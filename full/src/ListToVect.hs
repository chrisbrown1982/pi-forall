{-# LANGUAGE ViewPatterns, TypeSynonymInstances, 
             ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, 
             TupleSections, FlexibleInstances, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module ListToVect where

import Modules (getModules)

import Environment
import TypeCheck
-- import Parser
import PrettyPrint
import Utils
import Syntax

import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error 
import Unbound.Generics.LocallyNameless
-- import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
-- import Unbound.Generics.LocallyNameless.TH (makeClosedAlpha)
-- import Unbound.Generics.LocallyNameless.Name
-- import Unbound.Generics.LocallyNameless.Bind

import Control.Monad.Except
import Control.Monad.Reader.Class

-- import System.Environment(getArgs)
import System.Exit (exitFailure)
import System.FilePath (splitFileName)

-- | Display a parse error to the user  
putParseError :: ParseError -> IO ()  
putParseError parseError = do
  putStrLn $ render $ disp $ errorPos parseError
  putStrLn $ show parseError
  
-- | Display a type error to the user  
putTypeError :: Disp d => d -> IO ()  
putTypeError typeError = do 
  putStrLn "Type Error:"
  putStrLn $ render $ disp typeError

exitWith :: Either a b -> (a -> IO ()) -> IO b
exitWith res f = 
  case res of 
    Left x -> f x >> exitFailure 
    Right y -> return y


-- parseAndTypeCheck :: String -> 
parseAndTypeCheck :: String -> IO Module
parseAndTypeCheck pathToMainFile = do
  let prefixes = currentDir : mainFilePrefix : []
      (mainFilePrefix, name) = splitFileName pathToMainFile
      currentDir = "" 
  putStrLn $ "processing " ++ name ++ "..."
  v <- runExceptT (getModules prefixes name)
  val <- v `exitWith` putParseError
  -- putStrLn $ show val 
  putStrLn "============================"
  putStrLn "type checking..."
  d <- runTcMonad emptyEnv (tcModules val)
  defs <- d `exitWith` putTypeError
  return (last defs)

listToVect :: String -> Int -> Int -> IO ()
listToVect pathToMainFile r c = do 
  m <- parseAndTypeCheck pathToMainFile
  let t = locToDecl (r,c) m
  case t of 
      Just d  -> do
                    let n = defToName d
                    case n of 
                      Nothing -> putStrLn $ "Couldn't find a name for the def"
                      Just name -> do
                           let sig = getTopLevelSig name m
                           sig' <- runTcMonad emptyEnv (refacSigListToVect sig)
                           sig'' <- sig' `exitWith` putTypeError
                           putStrLn (show (  sig'' ))
                           case sig'' of 
                             Nothing -> putStrLn "Error in generating type signature"
                             Just s -> putStrLn $ render $ disp s
      Nothing -> putStrLn $ "Invalid cursor position or identifier"

-- refacSigListToVect :: (MonadIO m, Fresh m) 
     --              => Maybe Decl -> m (Maybe Decl) 

--buildSig :: [Term] -> Term -> m Term
buildSig [] sig = return sig
buildSig (ErasedPi bnd : vs) sig = do
   ((x, unembed -> tyA), tyB) <- unbind bnd
   sig' <- buildSig vs (ErasedPi (bind (x, embed tyA) sig))
   return sig'


refacSigListToVect :: (Fresh m, MonadReader Env m, MonadIO m) => Maybe Decl -> m (Maybe Decl)
refacSigListToVect (Just s@(Sig pos name term)) = do
      (vars, term') <- refPiList [] term 
      newSig <- buildSig vars term'
      return (Just (Sig pos name newSig)) 
refacSigListToVect x = return x

-- refPiList :: (MonadIO m, Fresh m) => Term -> m Term 
-- returns a list of fresh variables to be added as explicits and the transformed type...
refPiList :: (Fresh m, MonadReader Env m, MonadIO m) => [Term] -> Term -> m ([Term],Term)
refPiList vars (ErasedPi bnd) = do
    ((x, unembed -> tyA), tyB) <- unbind bnd
   -- liftIO $ putStrLn $ (show tyB) 
    (vars',tyB') <- extendCtx (Sig defaultPos x tyA) $ refPiList vars tyB
    return (vars', ErasedPi (bind (x, embed tyA) tyB'))
refPiList vars (Pi bnd) = do
    ((x,unembed -> tyA), tyB) <- unbind bnd
    liftIO $ putStrLn $ show (tyA)
    (vars',tyA') <- refPiList vars tyA
    -- check if the tyB is the last type in the chain ... 
    -- if it is the last type, it shouldn't be another pi type.
    case tyB of 
     (TCon name terms) -> 
       if name == "List" then
         do
            n <- fresh (string2Name "n") 
            let n' = string2Name ((name2String n) ++ (show (name2Integer n)))
            return (vars',Pi (bind (x, embed tyA') (TCon "Sig" [TCon "Nat" [], Paren (Lam (bind (n',(embed (Annot (Just (TCon "Nat" []))))) (TCon "Vec" (terms ++ [Var n']))))])))
       else 
        do 
          (vars'', tyB') <- extendCtx (Sig defaultPos x tyA') $ refPiList vars' tyB
          return (vars'', Pi (bind (x, embed tyA') tyB'))
     _ -> 
        do 
          (vars'', tyB') <- extendCtx (Sig defaultPos x tyA') $ refPiList vars' tyB
          return (vars'', Pi (bind (x, embed tyA') tyB'))

-- remove this clause?

refPiList vars t@(TCon name terms)
  | name == "List" = do
                         n <- fresh (string2Name "n") 
                         let n' = string2Name ((name2String n) ++ (show (name2Integer n)))
                             newVar = ErasedPi (bind (n', (embed (TCon "Nat" []))) TyUnit)

                         return (newVar : vars, TCon "Vec" (terms ++ [Var n']))
                         -- return t
  | otherwise = return (vars,t)


refPiList vars t = do 
      liftIO $ putStrLn (">" ++ (show t) ++ "<")
      return (vars,t)
    