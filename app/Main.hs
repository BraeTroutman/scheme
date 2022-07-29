module Main where

import Lib
import System.Environment
import System.IO
import Control.Monad (liftM)

main :: IO ()
main = do
    (expr:_) <- getArgs
    evaled <- return $ liftM show $ readExpr expr >>= eval
    putStrLn $ extractValue $ trapError evaled

