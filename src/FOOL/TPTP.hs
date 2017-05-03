module FOOL.TPTP where

import FOOL.AST

data TPTP = TPTP [Sentence]

data Sentence = TypeD Name FOOLTerm
              | Axiom Name FOOLTerm
              | Conj Name FOOLTerm 
  deriving (Eq) 

type Name = String 

{- misc -}
isOfType :: Name -> FOOLTerm -> Sentence
isOfType = TypeD
