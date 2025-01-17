{- PiForall language, OPLSS -}

{-# LANGUAGE TypeSynonymInstances,ExistentialQuantification,FlexibleInstances, UndecidableInstances, ViewPatterns, DefaultSignatures, GeneralizedNewtypeDeriving, FlexibleContexts, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

-- | A Pretty Printer.
module PrettyPrint(Disp(..), D(..))  where

import Data.Typeable (Typeable)

import Utils
import Syntax
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

import Control.Monad.Identity
import Control.Monad.Reader
import Text.PrettyPrint as PP
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceName, sourceLine, sourceColumn)
import Text.ParserCombinators.Parsec.Error (ParseError)


#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,3,0)
-- ghc >= 7.10.3
#else
-- older ghc versions, but MIN_VERSION_GLASGOW_HASKELL defined
#endif
#else
-- MIN_VERSION_GLASGOW_HASKELL not even defined yet (ghc <= 7.8.x)
import Control.Applicative (Applicative(..), (<$>), (<*>))
#endif



import qualified Data.Set as S

-- | The 'Disp' class governs types which can be turned into 'Doc's
class Disp d where
  disp :: d -> Doc

  default disp :: (Display d) => d -> Doc
  disp = cleverDisp

-- This function tries to pretty-print terms using the lowest number in
-- the names of the variable (i.e. as close to what the user originally
-- wrote.)

cleverDisp :: (Display d) => d -> Doc
cleverDisp d =
  runReaderDispInfo (display d) initDI


instance Disp Term
instance Typeable a => Disp (Name a)
instance Disp Telescope
instance Disp Pattern
instance Disp Match


instance Disp String where
  disp = text
instance Disp Int where
  disp = text . show
instance Disp Integer where
  disp = text . show
instance Disp Double where
  disp = text . show
instance Disp Float where
  disp = text . show
instance Disp Char where
  disp = text . show
instance Disp Bool where
  disp = text . show
instance Disp a => Disp (Maybe a) where
  disp (Just a) = text "Just" <+> disp a
  disp Nothing = text "Nothing"
instance (Disp a, Disp b) => Disp (Either a b) where
  disp (Left a) = text "Left" <+> disp a
  disp (Right a) = text "Right" <+> disp a

instance Disp ParseError where
  disp = text . show
instance Disp SourcePos where
  disp p = text (sourceName p) PP.<> colon PP.<> int (sourceLine p) PP.<>
                colon PP.<> int (sourceColumn p) PP.<> colon

-- | Error message quoting
data D = DS String -- ^ String literal
       | forall a . Disp a => DD a -- ^ Displayable value

instance Disp D where
  disp (DS s) = text s
  disp (DD d) = nest 2 $ disp d
                -- might be a hack to do the nesting here???

instance Disp [D] where
  disp dl = sep $ map disp dl

instance Disp Epsilon where
  disp Erased = text "-"
  disp Runtime = text "+"

-------------------------------------------------------------------------
-- Modules and Decls
-------------------------------------------------------------------------

instance Disp Module where
  disp m = text "module" <+> disp (moduleName m) <+> text "where" $$
           vcat (map disp (moduleImports m)) $$
           disp (moduleEntries m)

instance Disp ModuleImport where
  disp (ModuleImport i) = text "import" <+> disp i

instance Disp [Decl] where
  disp = vcat . map disp

instance Disp Decl where

  disp (Def pos n term) = disp n <+> text "=" <+> disp term

  disp (RecDef pos n r) = disp (Def defaultPos n r)

  disp (Sig pos n ty) =
        disp n <+> text ":" <+> disp ty

  disp (Data n params constructors) =
    hang (text "data" <+> disp n <+> disp params
           <+> colon <+> text "Type"
           <+> text "where")
           2 (vcat $ map disp constructors)

  disp (DataSig t delta) =
        text "data" <+> disp t <+> disp delta <+> colon
    <+> text "Type"


instance Disp ConstructorDef where
  disp (ConstructorDef _ c Empty) = text c
  disp (ConstructorDef _ c tele)  = text c <+> text "of" <+> disp tele


-------------------------------------------------------------------------
-- The Display class
-------------------------------------------------------------------------
-- | The data structure for information about the display
--
data DispInfo = DI
  {
  showAnnots :: Bool,         -- ^ should we show the annotations?
  dispAvoid  :: S.Set AnyName   -- ^ names that have been used
  }


instance LFresh (ReaderDispInfo) where
  lfresh nm = do
      let s = name2String nm
      di <- ask;
      return $ head (filter (\x -> AnyName x `S.notMember` (dispAvoid di))
                      (map (makeName s) [0..]))
  getAvoids = dispAvoid <$> ask
  avoid names = local upd where
     upd di = di { dispAvoid =
                      (S.fromList names) `S.union` (dispAvoid di) }

-- | An empty 'DispInfo' context
initDI :: DispInfo
initDI = DI False S.empty

newtype ReaderDispInfo a = ReaderDispInfo (ReaderT DispInfo Identity a)
                         deriving (Functor, Applicative, Monad, MonadReader DispInfo)

runReaderDispInfo :: ReaderDispInfo a -> DispInfo -> a
runReaderDispInfo (ReaderDispInfo comp) = runReader comp

type M a = ReaderDispInfo a

-- | The 'Display' class is like the 'Disp' class. It qualifies
--   types that can be turned into 'Doc'.  The difference is that the
--   type might need the 'DispInfo' context to control the parameters
--   of pretty-printing

class (Alpha t) => Display t where
  -- | Convert a value to a 'Doc'.
  display  :: t -> M Doc

instance Display String where
  display = return . text
instance Display Int where
  display = return . text . show
instance Display Integer where
  display = return . text . show
instance Display Double where
  display = return . text . show
instance Display Float where
  display = return . text . show
instance Display Char where
  display = return . text . show
instance Display Bool where
  display = return . text . show

-------------------------------------------------------------------------
-------------------------------------------------------------------------

bindParens :: Epsilon -> Doc -> Doc
bindParens Runtime    d = d
bindParens Erased     d = brackets d

mandatoryBindParens :: Epsilon -> Doc -> Doc
mandatoryBindParens Runtime d = parens d
mandatoryBindParens Erased  d = brackets d


-- deciding whether to add parens to the func of an application
wrapf :: Term -> Doc -> Doc
wrapf f = case f of
  Var _         -> id
  App _ _       -> id
  ErasedApp _ _ -> id

  Paren _       -> id
  Pos _ a       -> wrapf a
  TrustMe _     -> id
  _             -> parens

-- deciding whether to add parens to the arg of an application
wraparg :: Term -> Doc -> Doc
wraparg x = case x of
  Var _       -> id
  Type        -> id
  TyUnit      -> id
  LitUnit     -> id
  TyBool      -> id
  LitBool b   -> id
  Sigma _     -> id
  TrustMe _   -> id
  TCon _ []   -> id
  (isNumeral -> Just x) -> id
  DCon _ [] _ -> id

  Refl _      -> id

  Pos _ a     -> wraparg a
  _           -> parens

instance Display Annot where
  display (Annot Nothing)  = return $ empty
  display (Annot (Just x)) = do
    st <- ask
    if (showAnnots st) then
         (text ":" <+>) <$> (display x)
      else return $ empty

instance Display Arg where
  display arg@(Arg ep t) = do
    st <- ask
    let annotParens = if showAnnots st
                      then mandatoryBindParens
                      else bindParens
    let wraparg (Arg ep x) = case x of
              Var _       -> bindParens ep
              TCon _ []   -> bindParens ep
              Type        -> bindParens ep
              TyUnit      -> bindParens ep
              LitUnit     -> bindParens ep
              TyBool      -> bindParens ep
              LitBool b   -> bindParens ep
              Sigma _     -> bindParens ep

              Pos _ a     -> wraparg (Arg ep a)

              DCon _ [] _ -> annotParens ep
              (isNumeral -> Just i) -> annotParens ep
              Prod _ _ _  -> annotParens ep
              TrustMe _   -> annotParens ep
              Refl _      -> annotParens ep

              _           -> mandatoryBindParens ep
    wraparg arg <$> display t




instance Display Term where
  display (Var n) = display n

  display (isNumeral -> Just i) = display i

  display (TCon n args) = do
    dn <- display n
    dargs <- mapM display args
    let wargs = zipWith wraparg args dargs
    return $ dn <+> hsep wargs

  display (DCon n args annot) = do
    dn     <- display n
    dargs  <- mapM display args
    dannot <- display annot
    return $ dn <+> hsep dargs <+> dannot


  display (Type) = return $ text "Type"

  display a@(Lam b) = do
    (binds, body) <- gatherBinders a
    return $ hang (text "\\" PP.<> sep binds <+> text ".") 2 body

  display (App f x) = do
     df <- display f
     dx <- display x
     return $ wrapf f df <+> wraparg x dx

  display (Pi bnd) = do
     lunbind bnd $ \((n,a), b) -> do
        da <- display (unembed a)
        dn <- display n
        db <- display b
        let lhs = if (n `elem` toListOf fv b) then
                parens (dn <+> colon <+> da)
              else
                wraparg (unembed a) da
        return $ lhs <+> text "->" <+> db

  display (Paren e) = do
     de <- display e
     return $ (parens de)

  display (Pos _ e) = display e

  display (Let bnd) = do

    lunbind bnd $ \ ((x,a) , b) -> do
     da <- display (unembed a)
     dx <- display x
     db <- display b
     return $  sep [text "let" <+> dx
                    <+> text "=" <+> da
                    <+> text "in",
                    db]

  display (Case scrut alts annot) = do
     dscrut <- display scrut
     dalts <- mapM display alts
     dannot <- display annot
     return $ text "case" <+> dscrut <+> text "of" $$
          (nest 2 $ vcat $ dalts) <+> dannot


  display (Subst a b annot) = do
      da  <- display a
      db  <- display b
      dat <- display annot
      return $ fsep [text "subst" <+> da,
                     text "by" <+> db,
                     dat]

  display (TyEq a b)   = do
      da <- display a
      db <- display b
      return $ da <+> text "=" <+> db
  display (Refl mty) = do
    da <- display mty
    return $ text "refl" <+> da

  display (Contra ty mty)  = do
     dty <- display ty
     da  <- display mty
     return $ text "contra" <+> dty <+> da


  display a@(ErasedLam b) = do
    (binds, body) <- gatherBinders a
    return $ hang (text "\\" PP.<> sep binds <+> text ".") 2 body

  display (ErasedApp f x) = do
     df <- display f
     dx <- display x
     return $ wrapf f df <+> brackets dx

  display (ErasedPi bnd) = do
     lunbind bnd $ \((n,a), b) -> do
        da <- display (unembed a)
        dn <- display n
        db <- display b
        let lhs = mandatoryBindParens Erased  $
              if (n `elem` toListOf fv b) then
                (dn <+> colon <+> da)
              else
                da
        return $ lhs <+> text "->" <+> db



  display (Ann a b)    = do
    da <- display a
    db <- display b
    return $ parens (da <+> text ":" <+> db)

  display (TrustMe ma)  = do
    da <- display ma
    return $ text "TRUSTME" <+> da

  display (Sigma bnd) =
    lunbind bnd $ \ ((x,unembed->tyA),tyB) -> do
      dx <- display x
      dA <- display tyA
      dB <- display tyB
      return $ text "{" <+> dx <+> text ":" <+> dA
        <+> text "|" <+> dB <+> text "}"
  display (Prod a b ann) = do
    da <- display a
    db <- display b
    dann <- display ann
    return $ parens (da <+> text "," <+> db) <+> dann

  display (Pcase a bnd ann) = do
    da <- display a
    dann <- display ann
    lunbind bnd $ \ ((x,y), body) -> do
      dx <- display x
      dy <- display y
      dbody <- display body
      return $ text "pcase" <+> da <+> text "of"
        <+> text "(" <+> dx <+> text "," <+> dy <+> text ")"
        <+> text "->" <+> dbody <+> dann

  display (TyBool) = return $ text "Bool"
  display (LitBool b) = return $ if b then text "True" else text "False"
  display (If a b c ann) = do
    da <- display a
    db <- display b
    dc <- display c
    dann <- display ann
    return $ text "if" <+> da <+> text "then" <+> db
                <+> text "else" <+> dc <+> dann

  display (TyUnit) = return $ text "One"
  display (LitUnit) = return $ text "tt"

instance Display Match where
  display (Match pos bd) =
    lunbind bd $ \ (pat, ubd) -> do
      dpat <- display pat
      dubd <- display ubd
      return $ hang (dpat <+> text "->") 2 dubd

instance Display Pattern where
  display (PatCon c []) = (display c)

  display (PatCon c args) =
      parens <$> ((<+>) <$> (display c) <*> (hsep <$> (mapM display args)))
  display (PatVar x) = display x

instance Display a => Display (a, Epsilon) where
  display (t, ep) = bindParens ep <$> display t

instance Disp Arg where
  disp (Arg ep t) = bindParens ep $ disp t

instance Display Telescope where
  display Empty = return empty
  display (Constraint t1 t2 tele) = do
      dt1 <- display t1
      dt2 <- display t2
      dtele <- display tele
      return $ brackets (dt1 <+> char '=' <+> dt2) <+> dtele
  display (Cons ep n ty tele) = do
      dn <- display n
      dty <- display ty
      dtele <- display tele
      return $ mandatoryBindParens ep (dn <+> colon <+> dty) <+> dtele


gatherBinders :: Term -> M ([Doc], Doc)
gatherBinders (Lam b) =
   lunbind b $ \((n,unembed->ma), body) -> do
      dn <- display n
      dt <- display ma
      let db = if isEmpty dt then dn else (parens (dn <+> dt))
      (rest, body) <- gatherBinders body
      return $ (db : rest, body)
gatherBinders (ErasedLam b) =
   lunbind b $ \((n,unembed->ma), body) -> do
      dn <- display n
      dt <- display ma
      (rest, body) <- gatherBinders body
      return $ ( brackets (dn <+> dt) : rest, body)

gatherBinders body = do
  db <- display body
  return ([], db)

-- Assumes that all terms were opened safely earlier.
instance Typeable a => Display (Name a) where
  display n = return $ (text . name2String) n

instance Disp [Term] where
  disp = vcat . map disp

instance Disp [(Name Term,Term)] where
  disp = vcat . map disp

instance Disp (TName,Term) where
  disp (n,t) = parens $ (disp n) PP.<> comma <+> disp t
