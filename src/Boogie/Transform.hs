-- | Collection of different transformation passes (Boogie -> Boogie)
module Boogie.Transform where 

import Boogie.AST 
import Boogie.Position
import Pretty 

---------- conceptualization ----------
transChain prog = mono_tguard prog >>= mono_targ

{- Polymorphism -}
mono_tguard :: Program -> Either TransformErr Program
mono_targ   :: Program -> Either TransformErr Program

{- Unstructured -}

{- Splitting -}


---------- Implementation ----------
mono_tguard prog = undefined 
mono_targ   prog = undefined 



-- an error during each transformation should result in direct error
-- reporting without continuation
data TransformErr = TransformErr SourcePos Doc 
