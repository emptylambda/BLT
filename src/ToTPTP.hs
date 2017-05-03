{-# LANGUAGE OverloadedStrings #-}

{-- KNOWN_ISSUEs
1. address multiple implementations!
   (resolved in proofObs instead)
--}

module ToTPTP where
import Control.Monad.State

import FOOL.AST
import qualified FOOL.AST as F
import FOOL.TransExpr
import FOOL.PrettyAST
import FOOL.TPTP
import Boogie.TypeChecker
import Boogie.AST 
import qualified Boogie.AST as B
import Boogie.Position
import Boogie.Util 
import Boogie.ProofObs
import qualified Data.Map as M
import Data.List (reverse , nub, sort, partition)
import Pretty 

{- external interface -}
toTPTP :: Task -> Context -> Options -> TransState
toTPTP task ctx options = snd $ runState (tptpGen task) initState
  where initState = TransState ctx task ([]) (BConst True) noPos [] options

toWP :: Task -> Context -> Options -> TransState
toWP task ctx options = snd $ runState (wpGen task) initState
  where initState = TransState ctx task ([]) (BConst True) noPos [] options

data Options = OPT {
  -- | Exp flags
  conditionalLetIns :: Bool 
  }

type TS a = State TransState a 

data TransState = TransState {
  ctx  :: Context,
  task :: Task,
  tptp :: [Sentence],
  currentConjecture :: FOOLTerm,
  pos   :: SourcePos,
  olds  :: [(B.Id, B.Type)],
  flags :: Options 
  }

stich :: TransState -> TPTP
stich s = TPTP $ (tptp s) ++ [conj]
  where conj = Conj (snd $ task s) (currentConjecture s) 

{- state-manipulating interfaces -}
setPos spos s = s {pos = spos}

updateContext f s = s {ToTPTP.ctx = f $ ToTPTP.ctx s}

addSentence :: Sentence -> TS ()
addSentence sen = modify $ \s -> s {tptp = (tptp s) ++ [sen]}

declareType name id t = do
  lpos <- gets (lineNo . pos) 
  addSentence $ TypeD (name ++ lpos) (F.TypedVar id t)

addAxiom name term = do
  lpos <- gets (lineNo . pos) 
  addSentence $ FOOL.TPTP.Axiom (name ++ lpos) term

expandConj :: (FOOLTerm -> FOOLTerm) -> TS ()
expandConj f = modify $ \s -> s {currentConjecture = f $ currentConjecture s}

registerHavoc :: (B.Id, B.Type) -> TS ()
registerHavoc (id, t) = do
  t <- resolveSynon t
  declareType "havoc_" id (transType t)

registerOld :: (B.Id, B.Type) -> TS ()
registerOld (id, t) = do
  t <- resolveSynon t
  declareType "old_" ("old_" ++ id) (transType t)
  modify $ \s -> s { olds = (id, t) : (olds s) } 

-- core functions 
-- | tptpGen models VC with Tuple updates 
tptpGen :: Task -> TS ()
tptpGen ((Program decls), taske_id) = do
  mapM_ frontDecl decls 
  mapM_ imperatives decls 
  assignOlds 

-- | wpGen models traditional VC Gen (weakest precond.)
wpGen  :: Task -> TS ()
wpGen ((Program decls), taske_id) = do
  mapM_ frontDecl decls 
  mapM_ imperativesWP decls
  assignOlds 

assignOlds :: TS ()
assignOlds = do
  os <- gets olds
  if null os
    then return ()
    else
    let lrs = zip lhss rhss 
        lhss = map (\(id, t) -> F.Var ("old_" ++ id)) os
        rhss = map (\(id, t) -> F.Var id) os
    in
      expandConj (Let lrs)

imperativesWP :: Decl -> TS ()
imperativesWP decl@(Pos pos d) = do
  modify $ setPos pos
  case d of
    ProcedureDecl pid targs formals rets contracts Nothing -> do
      return ()
    ProcedureDecl pid targs formals rets contracts (Just (localvars, block)) -> do
      mapM_ localvarTrans $ localvars ++ [rets]
      q <- gets currentConjecture
      q' <- wp (reverse $ map (snd . node) block) q
      modify $ \s -> s {currentConjecture = q'}
      -- forget localContext with globalContext 
      modify $ updateContext globalContext
    ImplementationDecl pid targs formals rets bodies -> do 
      return () 
    otherwise -> return () 


frontDecl :: Decl -> TS ()
frontDecl decl@(Pos pos d) = do
  modify $ setPos pos
  case d of
    -- | TypeDecl without `value` creates new types; TypeSynonyms are
    -- not of our interest in TPTP world, any variables with synonym
    -- types will be translated with their type resolved
    TypeDecl types -> mapM_ trans types 
      where trans t = case B.tValue t of
              Nothing -> declareType "ntypd_" (B.tId t) (I)
              Just r  -> return () 
              -- declareType "ntypd_" (B.tId t) (transType r)
    AxiomDecl e -> do
      e' <- transExpr' e -- transExpr' resolves typeSynon
      addAxiom "axmd_"  e' 
    ConstantDecl isU ids t _ _ -> do
      t <- resolveSynon t 
      mapM_ (\id -> declareType "const_" id (transType t)) ids 
    FunctionDecl _ fid targs formals rets b -> do
      formals' <- mapM (\(id, t) -> do
                           t <- resolveSynon t 
                           return (id, t)) formals
      declareType "func_" fid (FuncType (map (transType . snd) formals') (transType $ snd rets))
      case b of
        Nothing -> return ()
        Just body -> addAxiom (fid ++ "_fbdy_") term
          where term = F.Quantified F.Forall paras eq
                eq = Bin Equal (FunApp fid paras) imp
                imp = transExpr body 
                paras = map (\(t, i) -> translateParameters t i) (zip formals' [1..])
    VarDecl idtws -> mapM_ trans idtws -- not really using the "where" clause at the moment 
      where trans lvar = do
              t <- resolveSynon (B.itwType lvar)
              declareType "var_" (B.itwId lvar) (transType $ t)
    ProcedureDecl pid targs formals rets contracts b -> do
      frontDecl (Pos pos (VarDecl formals)) -- could improve by id; MAYBE move down to `imperatives`?
      -- frontDecl (Pos pos (VarDecl rets)) -- this is already move to imperatives
      handleContracts contracts       
    -- [FIXME] make sure Split handles bodies -> [body]
    ImplementationDecl pid targs formals rets bodies -> do 
      return () -- fill in 


handleContracts :: [Contract] -> TS ()
handleContracts contracts = do
  mapM_ axiomatize requires
  goal <- conjoin ensures
  updateEnsure goal 
  where requires = [c | c@(Requires _ _) <- contracts]
        ensures  = [c | c@(Ensures _ _) <- contracts]        

axiomatize :: Contract -> TS ()
axiomatize (Requires isFree e) = do 
  term <- transExpr' e
  addAxiom ("require_axiom") term

conjoin :: [Contract] -> TS FOOLTerm 
conjoin [] = return $ BConst True
conjoin [(Ensures isFree e)] = transExpr' e
conjoin ((Ensures isF e):cs) = do
  t <- conjoin cs
  return $ Bin F.And ((transExpr e)) t 
  

updateEnsure :: FOOLTerm -> TS ()
updateEnsure goal = do
  modify $ \s -> s {currentConjecture = goal}

imperatives :: Decl -> TS ()
imperatives decl@(Pos pos d) = do
  modify $ setPos pos
  case d of
    ProcedureDecl pid targs formals rets contracts Nothing -> do
      return ()
    ProcedureDecl pid targs formals rets contracts (Just (localvars, block)) -> do
      mapM_ localvarTrans $ localvars ++ [rets]
      mapM_ statementTrans (reverse block)
      -- forget localContext with globalContext 
      modify $ updateContext globalContext
    ImplementationDecl pid targs formals rets bodies -> do 
      return () 
    otherwise -> return () 


transAssign' :: [((B.Id, [[B.Expression]]), B.Expression)] -> TS [(FOOLTerm, FOOLTerm)]
transAssign' as = do
  vars' <- mapM (\(l, r) -> transExpr' r >>= \r' -> return ((F.Var (fst l)), r')) var_as
  maps' <- mapM (\(l, r) -> transArrayUpdate' l r >>= \r' -> return ((F.Var (fst l)), r')) map_as  
  return $ (vars' ++ maps')
  where (var_as, map_as) = partition (null . concat . snd . fst) as

transArrayUpdate' :: (B.Id, [[B.Expression]]) -> B.Expression -> TS FOOLTerm
transArrayUpdate' (id, index) value = do
  case concat index of
    [] -> error ""
    [i] -> do 
      index' <- transExpr' i
      value' <- transExpr' value
      return $ Store (F.Var id) index' value'
    i:is -> do
      index' <- transExpr' i      
      -- value' <- transExpr' value
      x <- transExpr' (gen (B.MapSelection (gen (B.Var id)) [i]))
      y <- transArrayUpdate' ((show (pretty x)), [is]) value  -- FIXME_LATTER dirty hacking with show 
      return $ Store (F.Var id) index' y

-- | extend context with localContext; notice this is extension
-- instead of replacement, use nestedContext instead of localContext
localvarTrans :: [IdTypeWhere] -> TS ()
localvarTrans idtws = do
  ctx <- gets ToTPTP.ctx
  modify $ \s -> s {ToTPTP.ctx = nestedContext bindings idts ctx }
  mapM_ localvarDecl idtws
  where bindings = M.fromList idts 
        idts = map (\i -> (itwId i, itwType i)) idtws 

localvarDecl :: IdTypeWhere -> TS ()
localvarDecl idtw = do
  t <- resolveSynon (itwType idtw)
  declareType "localvar_" id (transType t)
  where id = itwId idtw

statementTrans :: LStatement -> TS ()
statementTrans lst = do
  modify $ setPos pos
  case node st of
    Predicate _attr spec -> do
      q <- gets currentConjecture
      e' <- transExpr' $ specExpr spec 
      case specFree spec of
        True -> do
          expandConj (Bin Imply e')
        False -> do
          expandConj (Bin F.And e')

    Assign lhss rhss -> do
      q <- gets currentConjecture
      lrs <- transAssign' $ zip lhss rhss 
      expandConj (Let lrs)

    Havoc ids -> do
      ctx <- gets ToTPTP.ctx 
      q <- gets currentConjecture
      let idTypes = map (\id -> exprType ctx (gen (B.Var id))) ids
          lrs = transAssign $ zip lhss rhss
          lhss = zip ids (repeat [[]])
          idts = zip ids idTypes
          ids' = map (\(id, t) -> havocNaming pos id t) idts 
          rhss = map (\(id, t) -> havocWithType pos id t) idts in do
        expandConj (Let lrs)
        mapM_ registerHavoc (zip ids' idTypes)

    stmt@(B.Call lhss pid args) -> do
      ctx <- gets ToTPTP.ctx 
      q <- gets currentConjecture
      let lrs = [(modifiedTuple, rhsTuple)]
          rhsTuple = Tuple (map F.Var havocNames) 
          havocNames = (map (\(id, t) -> havocNaming pos id t) (zip modifies idTypes))
          modifies = nub $ checkStatement4Tuple ctx stmt lhss
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies 
          idts = zip modifies idTypes 
          ids' = map (\(id, t) -> havocNaming pos id t) idts                     
          modifiedTuple = Tuple (map F.Var modifies)
          -- in case of no postcondition associated with pid, just be BConst True => q 
          assumeCall = Bin Imply post'
          assumeCall' = Bin Imply (replaceNs (zip (pArgs) (argsNames)) posts)
          assumeCall'' = Bin Imply (replaceNs (zip (pRets ++ pArgs) (lhss ++ argsNames)) posts) -- take also lhss into account
          post' = replaceNs (zip modifies ids') posts
          pArgs = map (\idtw -> itwId idtw) (psigArgs psig)
          pRets = map (\idtw -> itwId idtw) (psigRets psig)
          argsNames = reverse $ takeArgName args 
          psig = case M.lookup pid (ctxProcedures ctx) of
            Nothing -> error $ "Called an unknown procedure: " ++ pid
            Just psig -> psig
          posts = case M.lookup pid (ctxProcedures ctx) of
            Nothing -> error $ "Called an unknown procedure: " ++ pid
            Just psig -> extractPostCondition $ psigContracts psig in do
        mapM_ registerHavoc (zip havocNames idTypes)        
        if (null modifies)
          then expandConj (\conj -> (assumeCall' conj))
          else expandConj (\conj -> (Let lrs (assumeCall'' conj)))
 
    While c spec b -> do
      ctx <- gets ToTPTP.ctx
      q <- gets currentConjecture
      when (c == B.Wildcard) wildCardCondition
      let lrs = [(modifiedTuple, rhsTuple)]
          modifies = nub $ findTuple ctx b
          modifiedTuple = Tuple (map F.Var modifies)
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies 
          havocNames = (map (\(id, t) -> havocNaming pos id t) (zip modifies idTypes))
          rhsTuple = Tuple (map F.Var havocNames) 
          assumeInv = Bin Imply invar q -- assume inv (second case) 
          invar = Bin F.And (Uni F.Not c') (loopInv spec) 
          c' = case c of
            B.Wildcard -> F.Var "wildbool"
            B.Expr ce -> transExpr ce
        in do 
        expandConj (Bin Imply invar)
        expandConj (Let lrs)
        mapM_ registerHavoc (zip havocNames idTypes)

    If c tb eb -> do
      ctx <- gets ToTPTP.ctx
      q <- gets currentConjecture
      when (c == B.Wildcard) wildCardCondition
      let c' = case c of
            B.Wildcard -> F.Var "wildbool"
            B.Expr c -> transExpr c in
        case eb of
          Nothing -> do 
            th <- (mapM sTrans tb)
            -- th <- (foldM (flip branchTrans) q) (reverse tb)
            let rhs = ITE c' (compose th modifiedTuple) modifiedTuple -- th modifiedTuple -- 
                modifies = nub $ findTuple ctx tb
                modifiedTuple = Tuple (map F.Var modifies)                
                lhs = [(modifiedTuple, rhs)] in
              expandConj (Let lhs)
          Just eb -> do
            th <- (mapM sTrans tb)
            el <- (mapM sTrans eb)
            let rhs = ITE c' (compose th modifiedTuple) (compose el modifiedTuple) -- not q in the compose 
                modifies = nub $ (findTuple ctx tb) ++ (findTuple ctx eb)
                modifiedTuple = Tuple (map F.Var modifies)                
                lhs = [(modifiedTuple, rhs)] in
              expandConj (Let lhs)
    otherwise -> return ()
    where st = (snd . node) lst
          pos = position st 

branchTrans :: LStatement -> FOOLTerm -> TS FOOLTerm
branchTrans lst q = do
  modify $ setPos pos
  case node st of
    Assign lhss rhss -> do
      return $ Let lrs q 
      where lrs = transAssign $ zip lhss rhss 
    Havoc ids -> do
      ctx <- gets ToTPTP.ctx 
      let idTypes = map (\id -> exprType ctx (gen (B.Var id))) ids
          lrs = transAssign $ zip lhss rhss
          lhss = zip ids (repeat [[]])
          idts = zip ids idTypes
          ids' = map (\(id, t) -> havocNaming pos id t) idts 
          rhss = map (\(id, t) -> havocWithType pos id t) idts in do
        return $ (Let lrs q)
    If c tb eb -> do
      ctx <- gets ToTPTP.ctx
      let c' = case c of
            B.Wildcard -> F.Var "wildbool"
            B.Expr c -> transExpr c in
        case eb of
          Nothing -> do 
            th <- (foldM (flip branchTrans) q tb)
            let rhs = ITE c' (th) modifiedTuple
                modifies = nub $ findTuple ctx tb
                modifiedTuple = Tuple (map F.Var modifies) in
              return $ rhs
          -- Just eb -> do
          --   th <- (mapM sTrans tb)
          --   el <- (mapM sTrans eb)
          --   let rhs = ITE c' (compose th modifiedTuple) (compose el modifiedTuple) -- not q in the compose 
          --       modifies = nub $ findTuple ctx tb
          --       modifiedTuple = Tuple (map F.Var modifies)                
          --       lhs = [(modifiedTuple, rhs)] in
          --     return $ (Let lhs)
    otherwise -> error ""
  where st = (snd . node) lst
        pos = position lst 

-- | translate statement and return the result, without modifing the state 
sTrans :: LStatement -> TS (FOOLTerm -> FOOLTerm)
sTrans lst = do
  modify $ setPos pos
  case node st of
    Predicate _attr spec -> do
      case specFree spec of
        True -> do
          -- expandConj (Bin Imply e)
          return id
        False -> do
          -- expandConj (Bin F.And e)
          return id
        where e = transExpr $ specExpr spec
    Assign lhss rhss -> do
      return $ Let lrs
      where lrs = transAssign $ zip lhss rhss 
    Havoc ids -> do
      ctx <- gets ToTPTP.ctx 
      let idTypes = map (\id -> exprType ctx (gen (B.Var id))) ids
          lrs = transAssign $ zip lhss rhss
          lhss = zip ids (repeat [[]])
          idts = zip ids idTypes
          ids' = map (\(id, t) -> havocNaming pos id t) idts 
          rhss = map (\(id, t) -> havocWithType pos id t) idts in do
        return $ (Let lrs)
    If c tb eb -> do
      ctx <- gets ToTPTP.ctx
      let c' = case c of
            B.Wildcard -> F.Var "wildbool"
            B.Expr c -> transExpr c in
        case eb of
          Nothing -> do 
            th <- (mapM sTrans tb)
            let rhs = \q -> ITE c' (compose th q) modifiedTuple
                modifies = nub $ findTuple ctx tb
                modifiedTuple = Tuple (map F.Var modifies) in
              return $ (rhs)
          Just eb -> do
            th <- (mapM sTrans tb)
            el <- (mapM sTrans eb)
            let rhs = ITE c' (compose th modifiedTuple) (compose el modifiedTuple) -- not q in the compose 
                modifies = nub $ findTuple ctx tb
                modifiedTuple = Tuple (map F.Var modifies)                
                lhs = [(modifiedTuple, rhs)] in
              return $ (Let lhs)
    -- [FIXME] Call
    Call lhss pid args -> do
      ctx <- gets ToTPTP.ctx
      let lrs = [(modifiedTuple, rhsTuple)]
          rhsTuple = Tuple (map F.Var havocNames) 
          ids' = map (\(id, t) -> havocNaming pos id t) idts                     
          idts = zip modifies idTypes 
          havocNames = (map (\(id, t) -> havocNaming pos id t) (zip modifies idTypes))
          modifies = nub $ checkStatement4Tuple ctx (node st) lhss
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies
          modifiedTuple = Tuple (map F.Var modifies)
          -- in case of no postcondition associated with pid, just be BConst True => q 
          argsTypes = map (\e -> exprType ctx e) args
          argsNames = reverse $ takeArgName args 
          assumeCall = Bin Imply post' --FIXME
          assumeCall' = Bin Imply (replaceNs (zip pArgs argsNames) posts)
          assumeCall'' = Bin Imply (replaceNs (zip (pRets ++ pArgs) (lhss ++ argsNames)) posts) -- take also lhss into account 
          pRets = map (\idtw -> itwId idtw) (psigRets psig)
          post' = replaceNs (zip modifies ids') posts
          pArgs = map (\idtw -> itwId idtw) (psigArgs psig)
          psig = case M.lookup pid (ctxProcedures ctx) of
            Nothing -> error $ "Called an unknown procedure: " ++ pid
            Just psig -> psig
          posts = extractPostCondition $ psigContracts psig  in do 
        mapM_ registerHavoc (zip ids' idTypes)
        expandConj assumeCall''
        return (\conj -> (Let lrs conj))
        -- if (null modifies)
        --   then return (\conj -> (assumeCall' conj))
        --   else return (\conj -> (Let lrs (assumeCall'' conj)))

    While c spec b -> do
      ctx <- gets ToTPTP.ctx
      q <- gets currentConjecture
      when (c == B.Wildcard) wildCardCondition
      let lrs = [(modifiedTuple, rhsTuple)]
          modifies = nub $ findTuple ctx b
          modifiedTuple = Tuple (map F.Var modifies)
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies 
          havocNames = (map (\(id, t) -> havocNaming pos id t) (zip modifies idTypes))
          rhsTuple = Tuple (map F.Var havocNames) 
          assumeInv = Bin Imply invar q -- assume inv (second case) 
          invar = Bin F.And (Uni F.Not c') (loopInv spec) 
          c' = case c of
            B.Wildcard -> F.Var "wildbool"
            B.Expr ce -> transExpr ce
        in do 
        mapM_ registerHavoc (zip havocNames idTypes)
        expandConj (Bin Imply invar)
        return $ \q -> Let lrs q

    otherwise -> error $ "[ToTPTP] sTrans : otherwise"  ++ (show $ pretty (node st))
  where st = (snd . node) lst
        pos = position lst 

takeArgName :: [B.Expression] -> [String]
takeArgName es = foldr (\(Pos pos e) ids -> case e of
                           B.Var id -> ids ++ [id]
                           otherwise -> ids 
                           ) [] es

replaceNs :: [(String, String)] -> FOOLTerm -> FOOLTerm
replaceNs fts term = foldr (\ft ter -> replaceNames ft ter) term fts

replaceNames :: (String, String) -> FOOLTerm -> FOOLTerm
replaceNames (from, to) term = case term of
  IConst _ -> term
  BConst _ -> term
  F.Var s -> if s == from then F.Var to else term
  F.TypedVar s t ->if s == from then F.TypedVar to t else term
  ITE c thn els -> ITE c' thn' els'
    where c' = replace c
          thn' = replace thn
          els' = replace els
  Tuple terms -> Tuple (map replace terms)
  FunApp fun terms -> FunApp fun (map replace terms)
  Store arr a b -> Store (replace arr) (replace a) (replace b)
  Select arr i -> Select (replace arr) (replace i)
  F.Bin op a b -> F.Bin op (replace a) (replace b)
  F.Uni op a -> F.Uni op (replace a)
  F.Quantified op vars term -> F.Quantified op (map replace vars) (replace term)
  Let lst term -> Let lst' (replace term)
    where lst' = map (\(a, b) -> (replace a, replace b)) lst 
  where replace = replaceNames (from, to)

translateParameters :: B.FArg -> Int -> FOOLTerm
translateParameters (Nothing, t) i = F.TypedVar ("para_" ++ show i) (transType t)
translateParameters (Just id, t) _ = F.TypedVar id (transType t)

-- | Types in the node can refer to TypeSynonyms; resolveSynon returns
-- the resolved type (addressing maps' type in TPTP)
resolveSynon :: B.Type -> TS B.Type
resolveSynon t = do
  case t of
    B.IdType tid _ -> do 
      ctx <- gets ToTPTP.ctx
      case (M.lookup tid (ctxTypeSynonyms ctx)) of
        Nothing -> return t
        Just (_formals, t') -> return t'
    otherwise -> return t 
      
-- | Stateful version of transExpr, for resolving typesyns
transExpr' :: Expression -> TS FOOLTerm
transExpr' e = case node e of
  B.Literal v -> return $ translateValue v
  B.Var id -> return $ F.Var id
  B.Application id exprs -> return $ FunApp id terms
    where terms = map transExpr exprs
  B.MapSelection m i -> case (reverse i) of
    [] -> error "Expression: MapSelect without index"
    [i] -> do
      i' <- transExpr' i
      m' <- transExpr' m
      return $ Select m' i' --(transExpr m) (transExpr i)
    (i:is) -> do
      i' <- transExpr' i
      s <- (transExpr' (Pos (position e) $ B.MapSelection m is))
      -- return $ Select (transExpr (Pos (position e) $ B.MapSelection m is)) (transExpr i)
      return $ Select s i'
  B.MapUpdate m ix rhs  -> case (reverse ix) of
    [] -> error "Expression: MapUpdate without index"
    [i] -> do
      m' <- transExpr' m
      rhs' <- transExpr' rhs
      i' <- transExpr' i      
      return $ Store m' i' rhs'
    (i:is) -> do
      m' <- transExpr' m
      rhs' <- transExpr' rhs
      i' <- transExpr' i
      let m'' = Pos (position e) (B.MapSelection m [i]) in 
        return $ Store m' i' (transExpr $ Pos (position e) $ B.MapUpdate m'' is rhs)
  B.IfExpr cond tb fb -> do 
    c' <- transExpr' cond
    tb' <- transExpr' tb
    fb' <- transExpr' fb          
    return $ ITE c' tb' fb'
  B.UnaryExpression unop e -> do
    e' <- transExpr' e 
    return $ Uni op' e' 
    where op' = translateUnOp unop
  B.BinaryExpression binop e1 e2 -> do 
    e1' <- transExpr' e1
    e2' <- transExpr' e2    
    return $ Bin op' e1' e2'
    where op' = translateBinOp binop
          e1' = transExpr e1
          e2' = transExpr e2
  B.Quantified f qop id bound_vars expr -> do
    bound_vars' <- mapM (\(id, t) -> resolveSynon t >>= \t' -> return (id, t')) bound_vars
    return $ transExpr $ Pos (position e) $ B.Quantified f qop id bound_vars' expr 

  -- In Boogie's two-state contexts, old(var) is always referring to
  -- the value of var before invocation of this procedure (a.k.a all
  -- the way back) 
  Old e' -> do
    ctx <- gets ToTPTP.ctx
    let typ = exprType ctx e' in
      case (node e') of
        B.Var id -> do
          registerOld (id, typ) 
          return $ F.Var ("old_" ++ id)
        otherwise -> do
          error "[ToTPTP] transExpr' old used on non-var expr" 
  otherwise -> do
    error "[ToTPTP] transExpr' case otherwise" 

loopInv :: [B.SpecClause] -> FOOLTerm
loopInv specs = case invs of
  [] -> BConst True -- No invariants 
  inv:invs -> foldr (\inv -> Bin F.And (transExpr (B.specExpr inv)))
    (transExpr (B.specExpr inv)) invs
  where isInv s = case B.specType s of
          B.LoopInvariant -> True
          _ -> False
        invs = filter isInv specs 


findTuple :: Context -> B.Block -> [B.Id]
findTuple ctx block = foldr (checkStatement4Tuple ctx) [] block'
  where block' = map B.stripToStatement block


checkStatement4Tuple :: Context -> B.BareStatement -> [B.Id] -> [B.Id]
checkStatement4Tuple ctx bst tup = case bst of
  B.Havoc ids -> ids ++ tup
  B.Assign ids _ -> ids' ++ tup
    where ids' = map fst ids
  B.While _ _ b -> (findTuple ctx b) ++ tup
  B.If _ tb (Just eb) -> (findTuple ctx tb ++ findTuple ctx eb) ++ tup 
  B.If _ tb Nothing ->  (findTuple ctx tb) ++ tup
  B.Call lhss pid args -> lhss ++ modifies ++ tup
    where modifies = case M.lookup pid (ctxProcedures ctx) of 
            Nothing -> error $ "Called an unknown procedure: " ++ pid
            Just psig -> findModifiesFromContracts $ psigContracts psig 
  _ -> tup 
  
-- | Procedures can only modify (global variables) as stated in their contract
-- along with their local variables and their return variables
-- Hence in a havoc_procedure_modifies tuple, we only need to find the variables stated in the contract 
findModifiesFromContracts :: [B.Contract] -> [B.Id]
findModifiesFromContracts contracts = foldr f [] contracts
  where f contract ids = case contract of
          B.Modifies _ mods -> ids ++ mods
          _ -> ids 

wildCardCondition :: TS ()
wildCardCondition = declareType "wildCondition" "wildbool" Boolean

extractPostCondition :: [B.Contract] -> FOOLTerm
extractPostCondition [] = BConst True
extractPostCondition (c:cs) = case c of
  B.Ensures free e -> Bin F.And (transExpr e) $ extractPostCondition cs
  _ -> extractPostCondition cs 

{- naming stuffs -}
havocWithType :: SourcePos -> String -> B.Type -> B.Expression
havocWithType pos varId t = attachPos pos (B.Var name)
  where name = havocNaming pos varId t

havocNaming :: SourcePos -> String -> B.Type -> String 
havocNaming pos varId t@(B.MapType _ _ _) = "hv_" ++ l ++ "_" ++ varId ++ "_" ++ mapType t
  where l = lineNo pos
havocNaming pos varId t = "hv_" ++ l ++ "_" ++ varId ++ "_" ++ show t
  where l = lineNo pos

mapType :: B.Type -> String
mapType (B.MapType _ domains range) = concatMap (\t -> show t ++ "_") domains ++ "_" ++ show range


compose :: [a -> a] -> a -> a 
compose = foldr (.) id 

-- | weakest precondition 
wp_s :: Statement -> FOOLTerm -> TS FOOLTerm
wp_s (Pos pos stmt) q = do
  case stmt of
    Predicate _attr spec -> do
      e <- transExpr' $ specExpr spec
      case specFree spec of
        True ->  return $ Bin Imply e q
        False -> return $ Bin F.And e q
    Assign lhss rhss -> do
      lrs <- transAssign' $ zip lhss rhss       
      return $ Let lrs q 
    Havoc ids -> do
      ctx <- gets ToTPTP.ctx
      let idTypes = map (\id -> exprType ctx (gen (B.Var id))) ids
          lrs = transAssign $ zip lhss rhss
          lhss = zip ids (repeat [[]])
          idts = zip ids idTypes
          ids' = map (\(id, t) -> havocNaming pos id t) idts 
          rhss = map (\(id, t) -> havocWithType pos id t) idts
        in do
        mapM_ registerHavoc (zip ids' idTypes)
        return $ Let lrs q 
    If c tb eb -> do
      ctx <- gets ToTPTP.ctx
      c' <-  case c of
        B.Wildcard -> return $ F.Var "wildbool"
        B.Expr c -> transExpr' c
      case eb of
        Nothing -> do
          tb' <- wp (reverse $ map (snd . node) tb) q
          return $ ITE c' tb' q
        Just eb -> do
          tb' <- wp (reverse $ map (snd . node) tb) q
          eb' <- wp (reverse $ map (snd . node) eb) q            
          return $ ITE c' tb' eb'
    While c spec b -> do
      ctx <- gets ToTPTP.ctx
      c'  <- case c of
        B.Wildcard -> return $ F.Var "wildbool"
        B.Expr c -> transExpr' c
      let lrs = transAssign $ zip lhss rhss
          lhss = zip modifies (repeat [[]])
          idts = zip modifies idTypes 
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies
          ids' = map (\(id, t) -> havocNaming pos id t) idts           
          rhss = map (\(id, t) -> havocWithType pos id t) idts
          modifies = nub $ findTuple ctx b          
          assumeInv = Bin Imply invar q -- assume inv (second case) 
          invar = Bin F.And (Uni F.Not c') (loopInv spec) 
        in do
        mapM_ registerHavoc (zip ids' idTypes)
        return $ Let lrs assumeInv
    Call lhss pid args -> do
      ctx <- gets ToTPTP.ctx
      let modifies = nub $ checkStatement4Tuple ctx stmt lhss
          lrs = transAssign $ zip lhss' rhss
          lhss' = zip modifies (repeat [[]])
          idts = zip modifies idTypes 
          idTypes = map (\id -> exprType ctx (gen (B.Var id))) modifies
          ids' = map (\(id, t) -> havocNaming pos id t) idts                     
          rhss = map (\(id, t) -> havocWithType pos id t) idts
          post' = replaceNs (zip modifies ids') posts
          assumeCall = Bin Imply post' q
          -- in case of no postcondition associated with pid, just be BConst True => q 
          posts = case M.lookup pid (ctxProcedures ctx) of
            Nothing -> error $ "Called an unknown procedure: " ++ pid
            Just psig -> extractPostCondition $ psigContracts psig 
        in do 
        mapM_ registerHavoc (zip ids' idTypes)
        return $ Let lrs assumeCall 
    otherwise -> error "otherwise"

wp' :: [Statement] -> FOOLTerm -> TS FOOLTerm
wp' stmts q = foldM (flip wp_s) q stmts'
  where stmts' = reverse stmts 

wp :: [Statement] -> FOOLTerm -> TS FOOLTerm
wp stmts q = case stmts' of
  [] -> return q
  s:ss -> do 
    q' <- wp_s s q
    wp ss q'
  where stmts' = stmts
  
