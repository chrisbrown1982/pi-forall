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
                             Just (argSize, s) -> 
                               do
                                   putStrLn $ render $ disp s
                                   -- for now just assume position for declaration...
                                   dec' <- runTcMonad emptyEnv (refacDecListToVect argSize d)
                                   dec'' <- dec' `exitWith` putTypeError
                                   putStrLn $ render $ disp dec''

      Nothing -> putStrLn $ "Invalid cursor position or identifier"


generateNewNames 0 b = return b
generateNewNames count t@(ErasedLam bnd) = do
    ((x, unembed -> tyA), tyB) <- unbind bnd
    n <- fresh (string2Name "n") 
    body'' <- generateNewNames (count-1) (ErasedLam (bind (n,(embed (Annot (Just (TCon "Nat" []))))) t))
    return body''


transformNil (DCon "Nil" [] annot) = 
    (DCon "Prod" [Arg Runtime (DCon "Zero" [] (Annot Nothing)), Arg Runtime (DCon "Nil" [] (Annot Nothing))] (Annot Nothing))
transformNil x = x

transformCons q@(DCon "Cons" [Arg Runtime (App (Var x) (Var y)), Arg Runtime (App (App (ErasedApp (ErasedApp (Var map) (Var a)) (Var b)) (Var f)) (Var ys))] annot) = 

   Case t alts an

   -- (DCon "BOB" [Arg Runtime (App (Var x) (Var y)), Arg Runtime (App (App (ErasedApp (ErasedApp (Var map) (Var a)) (Var b)) (Var f)) (Var ys))] annot)
  where
    t = Paren (App (App (ErasedApp (ErasedApp (ErasedApp (Var map) (Var (string2Name "m"))) (Var a)) (Var b)) (Var f)) (Var ys))
    alts = [Match defaultPos bnd]
    bnd = bind (PatCon "Prod" [(PatVar (string2Name "s"), Runtime), (PatVar (string2Name "res"), Runtime)]) (DCon "Prod" [Arg Runtime (DCon "Succ" [Arg Runtime (Var (string2Name "s"))] (Annot Nothing)), Arg Runtime (DCon "Cons" [Arg Erased (Var (string2Name "s")), Arg Runtime (App (Var f) (Var y)), Arg Runtime (Var (string2Name "res"))] (Annot Nothing))   ] (Annot Nothing))
    an = Annot Nothing



  --  Case (Paren (App (App (ErasedApp (ErasedApp (ErasedApp (Var (string2Name "map")) )) ) ) (Var x)) (Var y)))) [Match defaultPos (<(PatCon "Prod" [(PatVar s,Runtime),(PatVar res,Runtime)])> DCon "Prod" [Arg Runtime (Paren (Pos "List.pi" (line 32, column 57) (DCon "Succ" [Arg Runtime (Var 0@0)] (Annot Nothing)))),Arg Runtime (Paren (Pos "List.pi" (line 32, column 66) 

  -- (DCon "Cons" [Arg Erased (Pos "List.pi" (line 32, column 72) (Var 0@0)),Arg Runtime (Paren (Pos "List.pi" (line 32, column 76) (App (Var 3@0) (Var 1@1)))),Arg Runtime (Var 0@1)] (Annot Nothing))))] (Annot Nothing))] (Annot Nothing))] (Annot Nothing)))))))))

transformAlts :: (Fresh m, Monad m) => [Match] -> m [Match]
transformAlts [] = return []
transformAlts ((Match pos bnd) : alts) = do
   (pat, body) <- unbind bnd

   case pat of 
      PatCon name pats -> do

          case name of 
            "Nil" -> do
                let newNil = transformNil body
                alts' <- transformAlts alts

                return (Match pos (bind (PatCon name pats) newNil) : alts')

            "Cons" -> do

                let newCons = transformCons body

                alts' <- transformAlts alts

                return (Match pos (bind (PatCon name ((PatVar (string2Name "m"), Erased):pats)) newCons) : alts')
 
      PatVar name -> do -- ignore? 
          alts' <- transformAlts alts
          return ((Match pos bnd) : alts')



transformBody :: Fresh m => Term -> m Term
transformBody (ErasedLam bnd) = do
   (((x, unembed -> tyA), body)) <- unbind bnd
   body' <- transformBody body 
   return (ErasedLam (bind (x,(embed tyA)) body'))

transformBody (Lam bnd) = do
   (((x, unembed -> tyA), body)) <- unbind bnd
   body' <- transformBody body 
   return (Lam (bind (x,(embed tyA)) body'))

transformBody (Case t alts annot) = do
   alts' <- transformAlts alts 
   return (Case t alts' annot)
   

refacDecListToVect :: (Fresh m, MonadReader Env m, MonadIO m) => Int -> Decl -> m Decl
refacDecListToVect argSize (RecDef pos name  body) = 
    do
       body' <- generateNewNames argSize body
       body'' <- transformBody body
       return (RecDef pos name (ErasedLam (bind ((string2Name "n5"),(embed (Annot (Just (TCon "Nat" []))))) body'')))

--buildSig :: [Term] -> Term -> m Term
buildSig :: Fresh m => [Term] -> Term -> m Term
buildSig [] sig = return sig
buildSig (ErasedPi bnd : vs) sig = do
   ((x, unembed -> tyA), tyB) <- unbind bnd
   sig' <- buildSig vs (ErasedPi (bind (x, embed tyA) sig))
   return sig'


refacSigListToVect :: (Fresh m, MonadReader Env m, MonadIO m) => Maybe Decl -> m (Maybe (Int, Decl))
refacSigListToVect (Just s@(Sig pos name term)) = do
      (vars, term') <- refPiList [] term 
      newSig <- buildSig vars term'
      return (Just (length vars, Sig pos name newSig))
refacSigListToVect x = return Nothing

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
    