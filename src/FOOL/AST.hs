module FOOL.AST where

-- Simplified FOOL Terms 
data FOOLTerm = IConst Integer
              | BConst Bool
              | Var String
              | TypedVar String Type 
              | ITE FOOLTerm FOOLTerm FOOLTerm
              | Tuple [FOOLTerm]
              | FunApp String [FOOLTerm]
              | Store FOOLTerm FOOLTerm FOOLTerm
              | Select FOOLTerm FOOLTerm
              | Bin BOp FOOLTerm FOOLTerm
              | Uni UOp FOOLTerm
              | Quantified QOp [FOOLTerm] FOOLTerm 
              | Let [(FOOLTerm, FOOLTerm)] FOOLTerm -- for parallel assign
              deriving (Eq, Show)

instance Ord FOOLTerm where
  compare (TypedVar _ t1) (TypedVar _ t2) = compare t1 t2
  compare _ _ = EQ

data Type = I -- $i
          | TType String -- $tType
          | Boolean -- $o
          | Integer -- $int
          -- Both map and func are arrow type, but tptp distinguish them
          | MapType Type Type
          | FuncType [Type] Type 
          deriving (Eq, Show, Ord)


data BOp = And | Or | Imply | Iff | Xor | Exply
         | Greater | Less | Geq | Leq | Equal | Neq 
         | Add | Subtract | Multiply | Div 
  deriving (Show, Eq, Ord)

data UOp = Neg | Not 
  deriving (Show, Eq, Ord) 

data QOp = Forall | Exists
  deriving (Show, Eq, Ord)

