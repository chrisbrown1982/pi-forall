module Utils where


import GHC.Generics (Generic)
import Data.Generics (Data)
import Data.Typeable (Typeable)
import Generics.SYB hiding (Generic, Refl)
import Text.ParserCombinators.Parsec.Pos   

import Text.PrettyPrint.HughesPJ -- (render)
import Text.ParserCombinators.Parsec.Error 

import System.Exit (exitFailure,exitSuccess)

import Syntax

                      
-----------------------------------
-- positions
-----------------------------------

type SimpPos = (Int, Int)

defaultPos :: SourcePos
defaultPos = newPos "unknown location" 0 0

-----------------------------------
-- traversals for syntax selection
-----------------------------------
locToMatch :: (Data t)
            => SimpPos 
            -> t
            -> Maybe Match
locToMatch (row, col) t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` matchBind) t
  where
     matchBind m@(Match s bnd) 
       | sourceLine s == row && sourceColumn s == col = Just m
       | otherwise = Nothing

locToDecl :: (Data t)
            => SimpPos 
            -> t
            -> Maybe Decl
locToDecl (row, col) t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` declBind) t
  where
     declBind s@(Sig pos name term) 
       | sourceLine pos == row && sourceColumn pos == col = Just s
     declBind def@(Def pos name term)
       | sourceLine pos == row && sourceColumn pos == col = Just def
     declBind def@(RecDef pos name term)
       | sourceLine pos == row && sourceColumn pos == col = Just def
     declBind _  = Nothing

-- returns a top level type signature for a function

getTopLevelSig :: (Data t)
              =>  TName   -- the name of the function to find
              ->  t        -- the AST
              ->  Maybe Decl -- Maybe because there might not be a Sig
getTopLevelSig name t = 
   Generics.SYB.something (Nothing `Generics.SYB.mkQ` inSig) t
 where
   inSig s@(Sig pos sigName term)
    | name == sigName = Just s 
   inSig _ = Nothing


---------------------------------------------------
-- utilities for Names 
---------------------------------------------------
defToName :: Decl -> Maybe TName
defToName (Sig _ name _ ) = Just name
defToName (Def _ name _ ) = Just name
defToName (RecDef _ name _ ) = Just name
defToName (Data _ _ _) = Nothing
defToName (DataSig _ _) = Nothing