{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Main where
import System.Exit
import System.Environment
import System.Console.CmdArgs
import System.Directory 
import Data.Time.Calendar
import Boogie.ProofObs
import Boogie.AST
import Boogie.Util
import Boogie.Position
import qualified Boogie.Parser as Parser (program)
import Boogie.TypeChecker
import FOOL.AST
import FOOL.PrettyAST
import FOOL.TPTP
import ToTPTP
import Pretty
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Data.Maybe (catMaybes)
import qualified Text.PrettyPrint.ANSI.Leijen as L

programName = "BLT"
versionName = "alpha release 0.1"
releaseDate = fromGregorian 2017 4 1 

data Format = BPL | TPTP
            deriving (Data, Typeable, Show, Eq)


main = do
  res <- cmdArgsRun $ mode
  case res of
    Typecheck file -> runOnFile (\p ctx -> print "TypeChecked") file
    Split file toF -> runOnFile (splitCommand file toF) file
    Prove file format proverLocation _ -> runOnFile (proveCommand file False) file
    Filter file -> runOnFile (filtering file) file
    Translate file toF useTup -> runOnFile (transCommand file toF useTup) file

data CLAs =
  Typecheck {
  -- | input file
  file :: String
  } |
  Split {
  -- | input 
  file :: String,
  toFile :: Bool 
  } |
  Filter {
  file :: String
  } | 
  Prove {
  -- | input
  file :: String,
  proofFormat :: Format,
  proverLocation :: String,
  -- | Experimental features
  conditionalLetIns :: Bool
  } |
  Translate {
  file :: String,
  toFile :: Bool,
  useTuple :: Bool
  }
  
  deriving (Data, Typeable, Show, Eq)


typecheck = Typecheck {
  file         = ""        &= typFile &= argPos 0
  } &= help "Parse & Typecheck Boogie program (No split or Prove)" 

split = Split {
  file         = ""        &= typFile &= argPos 0,
  toFile       = False     &= help "Write output of split to files (Default: False)"
  }

filter = Filter {  file         = ""        &= typFile &= argPos 0 }

translate = Translate {
  file         = ""        &= typFile &= argPos 0,
  toFile       = False     &= help "Write output of split to files (Default: False)",
  useTuple      = False     &= help "Use tuple translation or not (Default: False)"
  } &= auto &= help "Translate input Boogie program into TPTP format" 

prove = Prove {
  file = ""  &= typFile &= argPos 0,
  proofFormat = BPL     &= help "in which format we prove? (Default: BPL)", 
  proverLocation = "vampire" &= help "where is your vampire",
  Main.conditionalLetIns = False  &= help "[X] conditional Let-In (Default: False)"
  }

mode = cmdArgsMode $ modes [typecheck, Main.filter, split, translate] &= 
  help "Boogie Less triggers" &= 
  program programName &= 
  summary (programName ++ " v_" ++ versionName ++ ", " ++ showGregorian releaseDate)


runOnFile :: (Program -> Context -> IO()) -> String -> IO()
runOnFile command file = do
  parseResult <- parseFromFile Parser.program file
  case parseResult of
    Left parseErr -> (printErr $ errorDoc $ text (show parseErr)) >> exitFailure
    Right p -> case typeCheckProgram p of
      Left typeErrs -> (printErr $ errorDoc $ typeErrorsDoc typeErrs) >> exitFailure
      Right context -> command p context


printDoc d = putDoc d >> putStr "\n"
printErr d = putDoc (L.red d) >> putStr "\n"

writeToFile :: Task -> IO ()
writeToFile (prog, name) = writeFile ("./" ++ name ++ ".bpl") (show $ pretty prog)

writeToFile' :: String -> Int -> String -> IO()
writeToFile' f index s = writeFile ("./" ++ f ++ "." ++ show index ++ ".tptp") s

splitCommand :: String -> Bool -> Program -> Context -> IO ()
splitCommand file toF prog ctx = do
  let proofOb = splitBoogie (prog, ctx)
      transSt = map (\task -> toWP task ctx (OPT False)) (obligations proofOb)
    in
    case toF of
      False -> do
        print proofOb
      True  -> do
        outputDir $ file ++ "_output"
        mapM_ writeToFile (obligations proofOb)
  where outputDir f = do
          createDirectoryIfMissing False f
          setCurrentDirectory f 

proveCommand :: String -> Bool -> Program -> Context -> IO ()
proveCommand file toF prog ctx = do
  let proofOb = splitBoogie (prog, ctx)
      transSt = map (\task -> toWP task ctx (OPT False)) (obligations proofOb) --[(prog, "prog")] 
    in
    case toF of
      False -> do
        -- mapM_ (\t -> print $ pretty (FOOL.TPTP.TPTP $ tptp t) <+> "\n") transSt 
        -- mapM_ (\t -> print $ pretty (currentConjecture t) <+> "\n ===") transSt
        mapM_ (\t -> print $ (header t) $+$ pretty (stich t) $+$ "%%-- end") transSt
          where header t = "%%-- " <+> (pretty ((snd . task) t))
      True  -> do
        outputDir $ file ++ "_output"
        mapM_ writeToFile (obligations proofOb)
  where outputDir f = do
          createDirectoryIfMissing False f
          setCurrentDirectory f 

transCommand :: String -> Bool -> Bool -> Program -> Context -> IO()
transCommand file toF useTup prog ctx = do
  let proofOb = splitBoogie (prog, ctx)
      transSt = if useTup
                then map (\task -> toTPTP task ctx (OPT False)) (obligations proofOb)
                else map (\task -> toWP task ctx (OPT False)) (obligations proofOb)
    in
    case toF of
      False -> do
        mapM_ (\t -> print $ (header t) $+$ pretty (stich t) $+$ "%%-- end") transSt
          where header t = "%%--" <+> (pretty ((snd . task) t))
      True  -> do
        mapM_ (\(t, index) -> (writeToFile' file index) (tptp t)) (zip transSt [1..])
          where header t = "%%--" <+> (pretty ((snd . task) t))
                tptp t = show $ (header t) $+$ (pretty (stich t)) $+$ "%%-- end"
        
{- filtering Boogies -}

filtering :: String -> Program -> Context -> IO ()
filtering file prog@(Program decls) ctx = do
  if not $ null gotos
    then do
    putStrLn $ color blue $ "Found Gotos: " ++ file
    exitFailure
    else if and (map (containsTypeVar . node) decls)
         then do (putStrLn $ color blue $ "Found TypeVar: " ++ file) >> exitFailure
         else do print $ pretty prog -- putStrLn $ color green $ file ++ " Cleared "
  where stmts = (bareStmts . bodies') prog
        gotos = concatMap containsGOTO stmts 

containsGOTO :: BareStatement -> [BareStatement]
containsGOTO stmt = case stmt of
  (Goto _) -> [stmt]
  otherwise -> []

bareStmts :: [Body] -> [BareStatement]
bareStmts bodies = concatMap (\block -> map (\ls -> (node . snd . node) ls) block) blocks
  where blocks = map snd bodies
        

bodies' (Program decls) = foldr f [] decls'
  where decls' = map node decls
        f dec ls = case dec of
          (ProcedureDecl _ _ _ _ _ (Just b)) -> b : ls
          (ImplementationDecl _ _ _ _ bodies) -> bodies ++ ls
          otherwise -> ls


containsTypeVar :: BareDecl -> Bool
containsTypeVar bdecl = case bdecl of 
  TypeDecl newtypes -> not $ null $ Prelude.filter (\nt -> not $ null (tArgs nt)) newtypes
  FunctionDecl _ _ targs _ _ Nothing -> not $ null targs
  FunctionDecl _ _ targs _ _ (Just (Pos _p expr)) -> not $ null targs && exprContainsTypeVar expr
  AxiomDecl (Pos _p expr) -> exprContainsTypeVar expr
  ProcedureDecl _ targs _ _ _ _ -> not $ null targs
  ImplementationDecl _ targs _ _ _  -> not $ null targs
  otherwise -> False 

exprContainsTypeVar :: BareExpression -> Bool
exprContainsTypeVar bexpr = case bexpr of
  Boogie.AST.Quantified _ _ targs _ _ -> not $ null targs
  otherwise -> False 


--
-- * Terminal output colors
--

type Color = Int

color :: Color -> String -> String
color c s = fgcol c ++ s ++ normal

highlight, bold, underline, normal :: String
highlight = "\ESC[7m"
bold      = "\ESC[1m"
underline = "\ESC[4m"
normal    = "\ESC[0m"

fgcol, bgcol :: Color -> String
fgcol col = "\ESC[0" ++ show (30+col) ++ "m"
bgcol col = "\ESC[0" ++ show (40+col) ++ "m"

red, green, blue :: Color
red = 1
green = 2
blue = 4
