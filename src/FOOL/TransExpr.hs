-- | Expression level of translation 
module FOOL.TransExpr where

import Boogie.Position
import Boogie.TypeChecker
import Boogie.Util 
import qualified Boogie.AST as B
import FOOL.AST 
import Data.List (partition)
import Data.Data (toConstr)
import Data.Char (toLower)

{- Unary Ops -}
translateUnOp :: B.UnOp -> UOp
translateUnOp B.Neg = Neg
translateUnOp B.Not = Not

{- Binary Ops -}
translateBinOp :: B.BinOp -> BOp
translateBinOp B.Plus = Add
translateBinOp B.Minus = Subtract
translateBinOp B.Times = Multiply
translateBinOp B.Gt = Greater
translateBinOp B.Geq = Geq
translateBinOp B.Ls = Less
translateBinOp B.Leq = Leq
translateBinOp B.And = And
translateBinOp B.Or = Or
translateBinOp B.Implies = Imply
translateBinOp B.Explies = Exply
translateBinOp B.Equiv = Iff
translateBinOp B.Eq = Equal
translateBinOp B.Neq = Neq
translateBinOp B.Div = Div 
translateBinOp B.Mod = error "[FOOL.TransExpr]: translateBinOp Mod" 
translateBinOp op = error $ "[FOOL.TransExpr]: translateBinOp Missing Op" ++ (show $ toConstr op)

{- Quantifier Ops-}
translateQOp :: B.QOp -> QOp
translateQOp B.Forall = Forall
translateQOp B.Exists = Exists
translateQOp B.Lambda = error "[FOOL.TransExpr]: translateQOp Lambda"


translateValue v = case v of
  B.IntValue i -> IConst i 
  B.BoolValue b -> BConst b
  B.CustomValue t r -> error "Value: CustomValue with ref" 
  B.Reference t r -> error "Value: Map ref" 


transExpr :: B.Expression -> FOOLTerm
transExpr e = case node e of
  B.Literal v -> translateValue v
  B.Var id -> Var id
  B.Application id exprs -> FunApp id terms
    where terms = map transExpr exprs
  B.MapSelection m i -> case (reverse i) of
    [] -> error "Expression: MapSelect without index"
    [i] -> Select (transExpr m) (transExpr i)
    (i:is) -> Select (transExpr (Pos (position e) $ B.MapSelection m is)) (transExpr i)
  B.MapUpdate m ix rhs  -> case (reverse ix) of
    [] -> error "Expression: MapUpdate without index"
    [i] -> Store m' i' rhs'
      where m' = transExpr m
            rhs' = transExpr rhs
            i' = transExpr i
    (i:is) -> Store m' i' (transExpr $ Pos (position e) $ B.MapUpdate m'' is rhs)
      where i' = transExpr i
            m' = transExpr m
            m'' = Pos (position e) (B.MapSelection m [i])
  B.IfExpr cond tb fb -> ITE c' tb' fb'
    where c' = transExpr cond
          tb' = transExpr tb
          fb' = transExpr fb          
  B.UnaryExpression unop e -> Uni op' (transExpr e)
    where op' = translateUnOp unop
  B.BinaryExpression binop e1 e2 -> Bin op' e1' e2'
    where op' = translateBinOp binop
          e1' = transExpr e1
          e2' = transExpr e2
  B.Quantified tri qop _typVars boundvars e -> Quantified op' qvars e'
   where op' = translateQOp qop
         qvars = map (\(id, t) -> TypedVar id (transType t)) boundvars
         e' =  transExpr e -- Leaving upper-casing to pretty printer 
  _ -> error $ "TransExpr Err: " ++ show e 

transAssign :: [((B.Id, [[B.Expression]]), B.Expression)] -> [(FOOLTerm, FOOLTerm)]
transAssign as = zip (map fst all) (map snd all)
  where (var_as, map_as) = partition (null . concat . snd . fst) as
        vars = map (\(l, r) -> (,) (Var (fst l)) (transExpr r)) var_as
        maps = map (\(l, r) -> (,) (Var (fst l)) (transArrayUpdate l r)) map_as
        all = vars ++ maps

transArrayUpdate :: (B.Id, [[B.Expression]]) -> B.Expression -> FOOLTerm
transArrayUpdate (id, [[index]]) value = Store (Var id ) (transExpr index) (transExpr value)


transType :: B.Type -> Type
transType B.BoolType = Boolean
transType B.IntType = Integer
transType (B.MapType _fv ds r) = MapType index returns 
  where index = transType $ head ds
        returns = if (null $ tail ds)
                  then transType r
                  else transType (B.MapType _fv (tail ds) r)
transType (B.IdType id args) = TType (map toLower id)

