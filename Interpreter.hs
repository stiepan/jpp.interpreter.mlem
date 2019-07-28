import System.IO ( stdin, stdout, stderr, hPutStrLn, hGetContents )
import System.Environment ( getArgs )

import LexMlem
import ParMlem
import SkelMlem
import PrintMlem
import ErrM
import AbsMlem
import AbsMlemBitter
import Aw ( check )
import Eval
import qualified AbsMlemBitterSweet

type ParseFun  = [Token] -> Err Program

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> hGetContents stdin >>= run pProgram
    fs -> mapM_ (runFile pProgram) fs

runFile :: ParseFun -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun -> String -> IO ()
run p s =
    case p (myLexer s) of
         Bad s -> do
            hPutStrLn stderr s
         Ok p@(ProgramP etree) -> do
            let tree = AbsMlemBitterSweet.t etree
            case check tree of
                Left error -> hPutStrLn stderr error
                Right t -> do
                    hPutStrLn stdout ((show t) ++ ":")
                    case (eval tree) of
                        Left error -> hPutStrLn stderr error
                        Right val -> hPutStrLn stdout (show val)
