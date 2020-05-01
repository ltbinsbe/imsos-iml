
module IML.Trans.ProMan where

import Prelude hiding (id, (.))

import IML.Grammar.Shared (MVar)
import IML.Grammar
import IML.Trans.Graphs

import Control.Category
import Control.Arrow
import Control.Monad.State

import Data.IORef

import System.IO

data Component a b = C { runComponent :: (a -> ProMan b) }

component :: (a -> ProMan b) -> Component a b
component = C

component_ :: (a -> b) -> Component a b
component_ = arr

componentMap :: Component a b -> Component [a] [b]
componentMap (C a2mb) = C $ (\as -> mapM a2mb as)

evalComponent :: ProOpts -> Component a b -> a -> b
evalComponent opts (C f) a = evalProMan opts (f a)

runWithDefaults :: ProMan a -> a
runWithDefaults pm = fst $ runProMan defaultOpts pm

runComponentIO :: ProOpts -> Component  a b -> a -> IO b
runComponentIO opts (C f) a = do
  forM (pm_warnings s) (hPutStrLn stderr)
  when (opt_csv opts) $ do
    forM_ (pm_csv_log s)
      (\strs -> mapM (\str -> putStr str >> putStr ",") strs >> putStrLn "")
  return b
  where (b, s) = runProMan opts (f a)
        print_lfactor ((f,r), (gs,ss)) = do
          print (f,r)
          sumRef <- newIORef 0
          forM gs $ \g -> do
            let g_nodes = length (nodes g)
            putStr ("nodes: " ++ show g_nodes ++ " ")
            modifyIORef sumRef (+g_nodes)
            putStrLn ("max-depth: " ++ show (maximum (map length (paths g))))
          let nr_ss = number_of_statements ss
          sum <- readIORef sumRef
--          putStrLn ("improvement: " ++ show sum ++ " - " ++ show nr_ss 
  --                    ++ " = " ++ show (sum - nr_ss))
          return ()
          where number_of_statements [] = 0
                number_of_statements [Branches ss] = sum (map number_of_statements ss)
                number_of_statements (x:xs) = 1 + number_of_statements xs

instance Category Component where
  id = C return 
  (C f2) . (C f1) = C op
    where op a = f1 a >>= f2

instance Arrow Component where  
  arr f = C op
    where op a = return (f a)
  first (C mf) = C op
    where op (b,d) = do
            c <- mf b
            return (c,d)

type ProMan a = State ProState a  

data ProState = ProState  { pm_seed     :: Int
                          , pm_opts     :: ProOpts
                          , pm_warnings :: [String]
                          , pm_csv_log  :: [[String]]
                          }

 
data ProOpts  = ProOpts   { opt_debug     :: Bool
                          , opt_csv       :: Bool
                          , opt_split_pm  :: Bool
                          , opt_no_hyphen :: Bool }

defaultOpts = ProOpts False False False False

runOptions :: [String] -> ProOpts
runOptions args = foldr op defaultOpts args
 where
  op "--debug"          o = o { opt_debug = True }
  op "--csv"            o = o { opt_csv = True }
  op "--split-pm"       o = o { opt_split_pm = True }
  op "--no-hyphen"      o = o { opt_no_hyphen = True }
  op _                  o = o 

whenOpt :: (ProOpts -> Bool) -> ProMan () -> ProMan ()
whenOpt pred m = gets (pred . pm_opts) >>= flip when m

boolOpt :: (ProOpts -> Bool) -> ProMan Bool
boolOpt pred = gets (pred . pm_opts)

-- | Raise a warning of any kind
warn :: String -> ProMan ()
warn str = modify (\s -> s { pm_warnings = str : pm_warnings s })

add_csv :: [String] -> ProMan()
add_csv ss = modify mod
  where mod s = s { pm_csv_log = pm_csv_log s ++ [ss] }

{-
refresh_var_name :: MVar -> ProMan MVar
refresh_var_name (MVar _ l mu) = do
  nm <- fresh_var_name 
  return (MVar nm l mu)
-}

fresh_id :: ProMan Int
fresh_id = do 
  i <- gets pm_seed
  modify (\m -> m { pm_seed = i+1} )
  return i

fresh_var_name :: ProMan String
fresh_var_name = do 
  i <- fresh_id
  return ("_X" ++ show i)

{-
-- | Generate a meta-variable matching a sequence of terms within given bounds
fresh_var :: Int -> Maybe Int -> ProMan MVar
fresh_var l mu = do
  nm <- fresh_var_name
  return (MVar nm l mu)
-}

-- | Generate a meta-variable matching exactly one term
fresh_var_ :: ProMan MVar
fresh_var_ = fresh_var_name
 
evalProMan :: ProOpts -> ProMan a -> a
evalProMan opts fa = fst (runProMan opts fa)

runProMan :: ProOpts -> ProMan a -> (a, ProState)
runProMan opts fa = runState fa (ProState 0 opts [] [])
