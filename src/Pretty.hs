{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

-- | Wrapper around the pretty-printing libarary
module Pretty (
  -- * Interface
  Pretty (..),
  Doc,
  renderPretty,
  putDoc,
  -- * Basic documents  
  empty,
  isEmpty,
  text,
  int,
  integer,
  linebreak,
  semi,
  lbrace, rbrace, rangle, space, 
  -- * Combinators
  option,
  optionMaybe,  
  (<+>), ($+$), (<>),
  hcat,
  vcat,
  hsep,
  vsep,
  punctuate,
  tupled,
  -- * Enclosing
  commaSep,
  starSep, 
  parens,
  condParens,
  dquotes,
  brackets,
  braces,
  angles,
  spaces,
  sentence, 
  -- * Indentation
  nest,
  align,
  -- * Formatting
  errorDoc,
  auxDoc,
  internalError,
  plain,
  -- * Structures
  hMapDoc,
  vMapDoc
) where

import Text.PrettyPrint.ANSI.Leijen hiding ((<+>), (<$>), hsep, vsep)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import Data.Map (Map, (!))
import qualified Data.Map as M

infixr 5 $+$
infixr 6 <+>
  
-- | Is document empty?
isEmpty d = case renderCompact d of
  SEmpty -> True
  _ -> False
  
-- | Separate two documents by space if both are nonempty  
doc1 <+> doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<+> doc2
    
-- | Separate two documents by linebreak if both are nonempty    
doc1 $+$ doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<$> doc2

-- | Separate by spaces
hsep :: [Doc] -> Doc
hsep = foldr (<+>) empty    
-- | Separate by new lines
vsep :: [Doc] -> Doc
vsep = foldr ($+$) empty    
-- | Separate by commas
commaSep :: [Doc] -> Doc
commaSep = hsep . punctuate comma
-- | Separate by starts
starSep :: [Doc] -> Doc
starSep = hsep . punctuate (space <> "*")
-- | Enclose in spaces    
spaces d = space <> d <> space

-- | Conditionally enclose in parentheses  
condParens b doc = if b then parens doc else doc
      
-- | Conditionally produce a doc
option b doc = if b then doc else empty

-- | Convert a 'Just' value to doc
optionMaybe mVal toDoc = case mVal of
  Nothing -> empty
  Just val -> toDoc val
  
-- | Apply error formatting  
errorDoc doc = red doc

-- | Apply auxiliary text formatting
auxDoc doc = dullyellow doc

-- | Error with a message
internalError doc = error . show $ text "Internal interpreter error (consider submitting a bug report):" $+$ doc      
      
instance Eq Doc where
  d1 == d2 = show d1 == show d2
  
entryDoc keyDoc valDoc (k, v) = nest 2 $ (keyDoc k  <+> text "->") <+> valDoc v 
  
hMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc    
hMapDoc keyDoc valDoc m = brackets (commaSep (map (entryDoc keyDoc valDoc) (M.toList m)))  
  
vMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc  
vMapDoc keyDoc valDoc m = vsep $ map (entryDoc keyDoc valDoc) (M.toList m)  

sentence :: String -> String -> Doc -> Doc 
sentence s_k s_id d = text s_k <> parens (commaSep [text s_id, d]) <> text "."
