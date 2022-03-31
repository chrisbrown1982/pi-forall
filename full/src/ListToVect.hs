{-# LANGUAGE ViewPatterns, TypeSynonymInstances, 
             ExistentialQuantification, NamedFieldPuns, 
             ParallelListComp, FlexibleContexts, ScopedTypeVariables, 
             TupleSections, FlexibleInstances, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-matches #-}

module ListToVect where

import Modules (getModules)

import Environment
import TypeCheck
import Parser
import PrettyPrint
import Utils
import Syntax

import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error 
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)
import Unbound.Generics.LocallyNameless.TH (makeClosedAlpha)
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Bind

import Control.Monad.Except

import System.Environment(getArgs)
import System.Exit (exitFailure,exitSuccess)
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
parseAndTypeCheck pathToMainFile = do
  let prefixes = currentDir : mainFilePrefix : []
      (mainFilePrefix, name) = splitFileName pathToMainFile
      currentDir = "" 
  putStrLn $ "processing " ++ name ++ "..."
  v <- runExceptT (getModules prefixes name)
  val <- v `exitWith` putParseError
  putStrLn $ show val 
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
                    let name = defToName d
                    case name of 
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
refacSigListToVect (Just s@(Sig pos name term)) = do
      term' <- refPiList term 
      return (Just (Sig pos name term')) 
refacSigListToVect x = return x

-- refPiList :: (MonadIO m, Fresh m) => Term -> m Term 
refPiList (ErasedPi bnd) = do
    ((x, unembed -> tyA), tyB) <- unbind bnd
   -- liftIO $ putStrLn $ (show tyB) 
    tyB' <- extendCtx (Sig defaultPos x tyA) $ refPiList tyB
    return (ErasedPi (bind (x, embed tyA) tyB'))
refPiList (Pi bnd) = do
    ((x,unembed -> tyA), tyB) <- unbind bnd
    liftIO $ putStrLn $ show (tyA)
    case tyA of 
        (TCon name terms) -> 
             if name == "List"
                then do 
                    liftIO $ putStrLn "here"
                    n <- fresh (string2Name "n") 
                    tyB' <-extendCtxsGlobal [Sig defaultPos n (TCon "Nat" []), Sig defaultPos x tyA] $ refPiList tyB
                    return (Pi (bind (x, embed (TCon "Vec" (Var n : terms))) tyB'))
                else do 
                    tyA' <- refPiList tyA
                    tyB' <- extendCtx (Sig defaultPos x tyA') $ refPiList tyB
                    return (Pi (bind (x, embed tyA') tyB'))
        _ -> do
                    tyA' <- refPiList tyA
                    tyB' <- extendCtx (Sig defaultPos x tyA') $ refPiList tyB
                    return (Pi (bind (x, embed tyA') tyB'))
{-
   --  tyA' <- refPiList tyA
    tyB' <- extendCtxs [Sig defaultPos n (TCon "Nat" []), Sig defaultPos x tyA'] $ refPiList tyB
    return (Pi (bind (x, embed tyA') tyB'))
-}
refPiList t@(TCon name terms)
  | name == "List" = do
                         -- liftIO $ putStrLn name
                         n <- fresh (string2Name "n") 
                         t <-extendCtxsGlobal [Sig defaultPos n (TCon "Nat" [])] $ return (TCon "Vec" (Var n : terms))
                         return t
  | otherwise = return t
refPiList (Paren t) = do
    res <- refPiList t 
    return (Paren res)
refPiList t = do 
      liftIO $ putStrLn (">" ++ (show t) ++ "<")
      return t
    