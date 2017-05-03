module Boogie.ProofObs where

import Boogie.AST
import Boogie.TypeChecker
import Boogie.Position
import Boogie.Util
import Pretty
import Control.Monad.State 
import qualified Data.Map as M

{- interface -}
splitBoogie :: (Program, Context) -> Obligation
splitBoogie (prog, ctx) = snd $ runState (poGen prog) initState
  where initState =  (Ob ctx [] [] "" (\_ -> gen (AxiomDecl $ gen tt)) [])

type PO a = State Obligation a 
type Task = (Program, String)

data Obligation = Ob {
  ctx    :: Context,
  shared :: [Decl],
  obligations :: [Task],
  -- local
  currentPid  :: Id,
  currentProcHeader :: Block -> Decl,
  currentProc :: Block
}

instance Show Obligation where 
  show ob = concatMap (\(prog, id) -> (show $ pretty prog) ++ "\n==== "++ id ++ " ====\n" )  $ obligations ob

addStmt :: LStatement -> PO()
addStmt lst =  modify $ \ob -> ob {currentProc = (currentProc ob) ++ [lst]}

addDecl :: Decl -> PO()
addDecl decl = modify $ \ob -> ob {shared = (shared ob) ++ [decl]}

setHeader :: (Block -> Decl) -> PO()
setHeader f = modify $ \ob -> ob {currentProcHeader = f}

setPid :: Id -> PO()
setPid pid = modify $ \ob -> ob {currentPid = pid}

poGen :: Program -> PO ()
poGen (Program decls) = do
  mapM_ goThrough decls 

goThrough ::  Decl -> PO ()
goThrough decl@(Pos pos d) = case d of
  TypeDecl _ -> addDecl decl 
  ConstantDecl _ _ _ _ _ -> addDecl decl
  FunctionDecl _ _ _ _ _ _ -> addDecl decl
  AxiomDecl _ -> addDecl decl
  VarDecl _ -> addDecl decl
  ProcedureDecl pid tArgs formals rets contracts (Nothing) -> do
    addDecl decl 
    return ()
  ProcedureDecl pid tArgs formals rets contracts (Just (locals, body)) -> do
    modify $ \ob -> ob{currentProc = []}    
    setPid pid
    setHeader (\block -> gen $ ProcedureDecl pid tArgs formals rets contracts (Just (locals, block)))
    -- addDecl decl -- we dont want the whole thing
    mapM_ checkBranch body
    if (not $ containReturn body) then newOb else return () -- implicit return at the end of body 
  ImplementationDecl pid tArgs formals rets bodies -> do
    setPid pid 
    mapM_ (multipleImps decl) bodies 

-- | [incomplete]
multipleImps :: Decl -> Body -> PO ()
multipleImps impDecl body = return ()

checkBranch :: LStatement -> PO ()
checkBranch lst@(Pos pos (lb, stmt)) = case node stmt of
  Return -> do
    newOb
  While c specs b -> do
    loopBeforeEntry (invariants specs)
    loopBodyAlone c (invariants specs) b
    mapM_ checkBranch b
    addStmt lst 
  If c thenB Nothing -> do
    mapM_ checkBranch' thenB -- if I see a return, create new proofOb without the If condition
    addStmt lst
  If c thenB (Just elseB) -> do
    mapM_ checkBranch' thenB
    mapM_ checkBranch' elseB    
    addStmt lst
  Call lhss pid args -> do
    priorCall pid
    addStmt lst 
    -- afterCall lst pid
  otherwise -> addStmt lst 

checkBranch' :: LStatement -> PO ()
checkBranch' lst@(Pos pos (lb, stmt)) = case node stmt of
  Return -> do
    newOb
  Call lhss pid args -> do
    priorCall pid
    -- afterCall lst pid
  otherwise -> return () 

containReturn :: Block -> Bool
containReturn block = and $ map f block
  where f (Pos pos (lb, stmt)) = case (node stmt) of
          Return -> True
          If _ thenB elseB -> case elseB of
            Nothing -> containReturn thenB
            Just elseB -> containReturn thenB || containReturn elseB
          While _ _ b -> containReturn b
          otherwise -> False
  
newOb = do
  currentProc <- gets currentProc
  header <- gets currentProcHeader
  currentPid <-  gets currentPid 
  shared <- gets shared
  let prog = Program (shared ++ [header currentProc]) in 
    modify $ \ob -> ob { obligations = (obligations ob) ++ [(prog, currentPid)] }

loopBeforeEntry :: [SpecClause] -> PO ()
loopBeforeEntry invs = do
  currentProc <- gets currentProc
  header <- gets currentProcHeader
  currentPid <-  gets currentPid 
  shared <- gets shared
  let prog = Program (shared ++ [dropEnsures $ header (currentProc ++ loopInvs)])
      loopInvs = map (\inv -> gen ([], (gen $ Predicate [] inv))) invs
    in 
    modify $ \ob -> ob { obligations = (obligations ob) ++ [(prog, currentPid ++ "_invariant_before_entry")] }
  
loopBodyAlone :: WildcardExpression -> [SpecClause] -> Block -> PO ()
loopBodyAlone c invs b = do
  header <- gets currentProcHeader
  currentPid <-  gets currentPid 
  shared <- gets shared
  let prog = Program (shared ++ [dropEnsures $ header ( cond ++ assumes ++ body  ++ loopInvs)])
      body = b
      loopInvs = map (\inv -> gen ([], (gen $ Predicate [] inv))) invs
      assumes =  map (\inv -> gen ([], (gen $ Predicate [] (SpecClause LoopInvariant True (specExpr inv))))) invs
      cond = case c of
        Wildcard -> []
        Expr ce -> [gen ([], (gen $ Predicate [] (SpecClause Precondition True (ce))))]
    in 
    modify $ \ob -> ob { obligations = (obligations ob) ++ [(prog, currentPid ++ "_loop_body")] }

priorCall :: Id -> PO ()
priorCall pid = do 
  currentProc <- gets currentProc
  ctx <- gets ctx 
  header <- gets currentProcHeader
  currentPid <-  gets currentPid 
  shared <- gets shared
  let prog = Program (shared ++ [dropEnsures $ header $ currentProc ++ ensures])
      ensures = case M.lookup pid (ctxProcedures ctx) of
        Nothing -> error $ "[ProofOb.priorCall] Failed to find PSig under: " ++ pid 
        Just psig -> map (\req -> gen ([], (gen $ Predicate [] req))) requires
          where requires = psigRequires psig 
    in 
    modify $ \ob -> ob { obligations = (obligations ob) ++ [(prog, currentPid ++ "_prior_call_" ++ pid)] }
                    
afterCall :: LStatement -> Id -> PO ()
afterCall lst pid  = do
  ctx <- gets ctx   
  currentProc <- gets currentProc
  shared <- gets shared  
  header <- gets currentProcHeader
  let prog = Program (shared ++ [dropEnsures $ header $ currentProc ++ assumptions])
      assumptions = case M.lookup pid (ctxProcedures ctx) of
          Nothing -> error $ "[ProofOb.priorCall] Failed to find PSig under: " ++ pid 
          Just psig -> map (\req -> gen ([], (gen $ Predicate [] req))) assumes
            where assumes = map (\(SpecClause Postcondition f e) -> (SpecClause Precondition True e)) (psigEnsures psig)
    in
    -- modify $ \ob -> ob { obligations = (obligations ob) ++ [(prog, pid)] } -- we dont create new proof ob after call 
    mapM_ addStmt assumptions

invariants :: [SpecClause] -> [SpecClause]
invariants specs = [ i | i@(SpecClause LoopInvariant _ _) <- specs ]

dropEnsures :: Decl -> Decl
dropEnsures (Pos pos (ProcedureDecl pid targs formals rets contracts b)) = (Pos pos (ProcedureDecl pid targs formals rets c' b))
  where c' = [ r | r@(Requires _ _) <- contracts] ++ [ m | m@(Modifies _ _) <- contracts]
