module ListToVect where

import Modules (getModules)

import Environment
import TypeCheck
import Parser
import PrettyPrint
import Utils

import Text.PrettyPrint.HughesPJ (render)
import Text.ParserCombinators.Parsec.Error 

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
      Just m -> putStrLn $ show m 
      Nothing -> putStrLn $ "Invalid cursor position or identifier"