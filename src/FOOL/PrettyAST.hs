{-# LANGUAGE OverloadedStrings #-}
module FOOL.PrettyAST where

import FOOL.AST
import FOOL.TPTP
import Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Char (toUpper, toLower) 
import Data.List (sort)

{- Pretty -}
instance Pretty QOp where
  pretty Forall = "!"
  pretty Exists = "?"

instance Pretty UOp where
  pretty Not = "~"
  pretty Neg = "$uminus"

instance Pretty BOp where
  pretty And =  "&"
  pretty Or =  "|"
  pretty Add =  "$sum"
  pretty Subtract =  "$difference"
  pretty Multiply =  "$product"
  pretty Imply =  "=>"
  pretty Exply =  "<="  
  pretty Iff =  "<=>"
  pretty Greater =  "$greater"
  pretty Geq =  "$greatereq"  
  pretty Less =  "$less"
  pretty Leq =  "$lesseq"
  pretty Equal =  "="
  pretty Neq  = "!="
  pretty Div = "$quotient_e"

class IsInfix a where
  isInFix :: a -> Bool

instance IsInfix UOp where
  isInFix _ = False 

instance IsInfix BOp where
  isInFix op = case op of
    And -> True
    Or -> True
    Imply -> True
    Iff -> True
    Equal -> True
    Neq -> True    
    _ -> False 

instance Pretty Type where
  pretty t = case t of
    Boolean -> "$o"
    Integer -> "$int"
    TType typ -> text typ 
    MapType ds r -> "$array" `funapp` (map pretty (ds : [r]))
    FuncType ds r -> ftyps <> " > " <> pretty r 
      where ftyps = condParens (length ds > 1) $ starSep $ map pretty ds
    I -> "$tType" -- I only appears as the type gets declared! so should be $tType

instance Pretty FOOLTerm where 
  pretty t = case t of
    IConst i -> (text . show) i
    BConst b -> if b then "$true" else "$false"
    Var id -> text id
    TypedVar id t -> text id <> text ": " <> pretty t 
    Tuple tuple -> "[" <> ttyps <> "]"
      where ttyps = commaSep $ map pretty tuple
    FunApp f args -> text f `funapp` (map pretty args)
    Uni op a -> pretty op <> (parens $ pretty a)
    -- parens $ pretty op <> (parens $ pretty a) -- over-parenthizing 
    Bin op a b -> if (isInFix op)
                     then parens $ hsep [pretty a , pretty op, pretty b]
                     else funapp (pretty op) [pretty a, pretty b]
    Quantified qop vs t -> pretty qop <> prettyVars <> text ": " <> quantifiedPretty qids t 
      where prettyVars = brackets $ commaSep (map (quantifiedPretty qids) vs)
            qids = map (\(TypedVar id t) -> id) vs 
    ITE c t f -> "$ite" `funappIndented` (map pretty [c, t, f])
    Select m i -> "$select" `funapp` [pretty m, pretty i]
    Store m i v -> "$store" `funapp` [pretty m, pretty i, pretty v]
    Let lrs inTerm -> "$let" <> parens (content <> ((", " PP.<$> pretty inTerm)))
      where content = delim $ map (\(l, r) -> pretty l <> " := " <> pretty r) lrs 
            -- zip-truncation is the only possible semantics 
            delim = align . vsep . punctuate ";"


funapp :: Doc -> [Doc] -> Doc
funapp f as = f <> parens (commaSep as) 

funappIndented :: Doc -> [Doc] -> Doc
funappIndented f as = f <> parens args
  where args = align $ (vsep . punctuate PP.comma) as 

toUpperName :: String -> Doc       
toUpperName =  text . map toUpper

quantifiedPretty :: [String] -> FOOLTerm -> Doc
quantifiedPretty qids term = case term of
  Var id -> if id `elem` qids
            then toUpperName id
            else text id 
  IConst i -> (text . show) i
  BConst b -> if b then "$true" else "$false"
  TypedVar id t -> toUpperName id <> text ": " <> pretty t 
  Tuple tuple -> "[" <> ttyps <> "]"
      where ttyps = commaSep $ map pretty' tuple
  FunApp fid args -> text fid `funapp` prettyArgs
      where prettyArgs = foldr f [] args
            f arg pargs = case arg of
              TypedVar id t -> pretty' (Var id) : pargs 
              _ -> pretty' arg : pargs 
  Uni op a -> pretty op <> (parens $ pretty' a)
  Bin op a b -> if (isInFix op)
                then parens $ hsep [pretty' a , pretty op, pretty' b]
                else funapp (pretty op) [pretty' a, pretty' b]
  Quantified qop vs t -> pretty qop <> prettyVars <> text ": " <> quantifiedPretty (qids ++ qids') t 
      where prettyVars = brackets $ commaSep (map pretty' vs)
            qids' = map (\(TypedVar id t) -> id) vs 
  ITE c t f -> "$ite" `funapp` (map pretty' [c, t, f])
  Select m i -> "$select" `funapp` [pretty' m, pretty' i]
  Store m i v -> "$store" `funapp` [pretty' m, pretty' i, pretty' v]
  Let lrs inTerm -> "$let" <> parens ((content lhss rhss) <> ((", " PP.<$> pretty' inTerm)))
      where content l r = delim $ map (\(l, r) -> pretty' l <> " := " <> pretty' r) (zip l r)
            -- zip-truncation is the only possible semantics 
            delim = align . vsep . punctuate ";"
            lhss = map fst lrs
            rhss = map snd lrs 
  where pretty' = quantifiedPretty qids 


{- TPTP -}
instance Pretty Sentence where
  pretty s = case s of
    TypeD des term -> commaSep [text' des, text "type", pretty term]
    Axiom des term -> commaSep [text' des, text "axiom", pretty term]
    Conj des term  -> commaSep [text' des, text "conjecture", pretty term]
    where text' s = text $ map toLower s 

instance Pretty TPTP where
  pretty (TPTP sens) = vsep $ map (tffWrapping . pretty) (sort sens)
  

-- Wrapping http://www.cs.miami.edu/~tptp/TPTP/Proposals/TFXTHX.html
thfWrapping :: Doc -> Doc
thfWrapping term = text "thf" <> parens term <> text "."
tfxWrapping term = text "tfx" <> parens term <> text "."
tffWrapping term = text "tff" <> parens term <> text "."



instance Ord Sentence where
  -- -- so $tType gets promoted 
  -- compare (TypeD _ term1) (TypeD _ term2) = compare term1 term2
  compare (TypeD _ _) _ = LT
  compare (Axiom _ _) (TypeD _ _) = GT   
  compare (Conj _ _)  _ = GT 
  compare _ _ = EQ
