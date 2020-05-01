
module IML.Interpreter.HighInterpreter where

import IML.Grammar.Shared
import IML.Grammar.High
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Mixed
import IML.Grammar.Bindings
import IML.Interpreter.Types
import IML.Trans.ProMan
import IML.Trans.Unmix
import IML.Trans.RemoveRO
import IML.Trans.RelFlags
import IML.Printer (showQuery, showTerm)
import IML.Parser (iml_parse)
import IML.Lexer(iml_lexer)

import qualified Funcons.Operations (structVMcompare, traverseVM) 

import qualified Data.Map as M
import Data.List (sortBy, intercalate)
import Data.Function (on)
import Data.Tree
import Data.IORef 
import Control.Monad (guard, unless, when, foldM, join)
import Control.Arrow ((>>>), (***))

import System.Random.Shuffle
import System.IO.Unsafe
import System.IO

import Network.Socket

program2output :: [String] -> Component MixedProgram (IO ()) 
program2output opts = rules_from_flags >>> remove_read_only >>> tohigh >>>
  component_ (run opts)

run :: [String] -> HighProgram -> IO ()
run opts (Program spec qs) = do
  counter_ref <- newIORef 0
  env <- sem_interactions opts qs envEmpty counter_ref specf 
  -- code for running a server, reading additional files and execing their queries 
  when ("--server" `elem` opts) $ do
    sock <- socket AF_INET Stream 0
    setSocketOption sock ReuseAddr 1
    Network.Socket.bind sock (SockAddrInet 4242 (tupleToHostAddress (127,0,0,1)))
    listen sock 2
    queryLoop env counter_ref sock
  where specf = sem_spec spec
        queryLoop env ref sock = do
          putStrLn "--- AWAITING INPUT ---"
          conn <- accept sock
          env <- runConn env ref conn 
          queryLoop env ref sock
        runConn env ref (csock,_) = do
          handle <- socketToHandle csock ReadMode
          string <- hGetContents handle
          let Program _ qs = iml_parse (iml_lexer string)
          sem_interactions opts qs env ref specf 

sem_cond :: Either Premise SideCon -> Varf -> Specf -> State -> Maybe State 
sem_cond (Left prem) = sem_prem prem 
sem_cond (Right sc) = sem_sidecon sc 

sem_prem :: Premise -> Varf -> Specf -> State -> Maybe State
sem_prem (Prem ros ec@(TConf _ ents) r pc) varf spec (rec0, the0, trees) = do
  conf1 <- eval_conf rec0 (subs_conf the0 ec)
  tree  <- interpreter spec conf1 r
  let conf2@(lam2,rec2) = rhs (root tree)
  the1 <- match_conf varf conf2 pc spec the0
  return (rec2, the1, trees++[tree])

sem_sidecon :: SideCon -> Varf -> Specf -> State -> Maybe State
sem_sidecon sc varf spec@(_,_,_,css,_) state@(rec0, the0, trees) = case sc of
  SideOP es ps -> do
    ts <- eExprs (subs_expr the0 es)
    the1 <- matches varf ts ps spec rec0 the0
    return (rec0, the1, trees)
  Term k es -> do 
    ts <- eExprs (subs_expr the0 es)
    guard (checkIfTerminal css k ts)
    return state
  NonTerm k es -> do 
    ts <- eExprs (subs_expr the0 es)
    guard (not (checkIfTerminal css k ts))
    return state

checkIfTerminal :: ConsSet -> ConsSetKey -> [Term] -> Bool 
checkIfTerminal css r ts = not (null ts) && all (isVal css r) ts 

sem_seq :: [Specf -> State -> Maybe State] -> Specf -> State -> Maybe State
sem_seq cs spec state = foldl prop (Just state) cs
  where prop acc c = acc >>= c spec

sem_lhs :: [Term] {- closed -} -> PConf -> Varf -> Specf -> State -> Maybe State
sem_lhs lams p varf spec state@(rec0, the0, trees) = do
  the1 <- match_conf varf (lams, rec0) p spec the0
  return (rec0, the1, trees)

sem_rule :: Rule -> Specf -> Conf -> Maybe Deriv 
sem_rule (Rule _ (Concl _ pc@(PConf _ ents) rel ec) scs vds) spec conf0@(lams, rec) = 
  do  (rec1, the1, trees) <- branch spec (rec, envEmpty, [])
      conf1 <- eval_conf rec1 (subs_conf the1 ec)
      return (mkDeriv conf0 rel conf1 (map fst ents) trees)
  where branch = sem_seq (sem_lhs lams pc varf : (map (flip sem_cond varf) scs))
        varf = mkVarMap vds

sem_branches :: [Rule] -> Specf -> Conf -> Maybe Deriv
sem_branches rs spec cf = foldl backtrack Nothing rs
  where backtrack acc r = maybe (sem_rule r spec cf) Just acc
                             
interpreter :: Specf -> Conf -> RSymb -> Maybe Deriv 
interpreter spec@(tm,gr,_,css,_) (lam0, rec0) r 
  | any (\(e,t) -> checkIfTerminal css e t) (M.assocs rec0)
    || checkIfTerminal css r lam0 = Nothing  
  | otherwise = sem_branches branches spec (lam0, rec0)
  where branches = map snd $ 
                    sortBy (flip compare `on` fst) $ 
                    ((globOf r lam0 gr) ++) $ transOf r lam0 tm 

sem_query :: Query -> MetaEnv -> Specf -> Maybe (Deriv, MetaEnv)
sem_query (Query prem@(Prem ros ec@(TConf _ ents) r pc) vds) 
             the0 spec@(_,_,_,_,rec0) = do
  (rec1, the1, [tree]) <- sem_prem prem (mkVarMap vds) spec (rec0, the0, [])
  return (tree, the1)

sem_interactions :: [String] -> [Interaction] -> MetaEnv -> IORef Int -> Specf -> IO MetaEnv
sem_interactions opts as the0 counter_ref spec = do
  foldM (doA counter_ref) the0 as
  where doA ref the0 (DoQuery q)  = do_a_query opts spec ref the0 q
        doA ref _ (ResetEnv)      = unless silent (putStrLn "> RESET-BINDINGS") >> return envEmpty
        silent = "--silent" `elem` opts

do_a_query :: [String] -> Specf -> IORef Int -> MetaEnv -> Query -> IO MetaEnv
do_a_query opts spec ref the0 q@(Query (Prem _ _ _ (PConf ps es)) vds) = do
  modifyIORef ref (+1)
  case sem_query q the0 spec of 
    Just (tree, the1) -> do 
      counter <- readIORef ref
      when print_derivations $ 
        writeFile ("/tmp/iml-derivations" ++ show counter ++ ".txt")
          (drawTree (fmap showTrans tree))
      when (not silent) $ do  
        putStrLn (showQuery q ++ " SUCCESS " ++ show counter)
        let the1' = M.filterWithKey (\k v -> k `elem` bvars) the1
              where bvars = pvars ps ++ pvars (map snd es)
        when (not (null the1')) (putStrLn (showMap the1'))
      return the1
    Nothing -> putStrLn (showQuery q ++ " FAILED") >> return the0
  where showMap = show . map keyVal . M.toList
          where keyVal (k,v) = k ++ " |-> " ++ intercalate "," (map showTerm v)
        silent = "--silent" `elem` opts
        print_derivations = "--derivations" `elem` opts

-- pattern matching and substitution

matches :: Varf -> [Term] {- closed terms-} -> [Pattern] -> Specf -> Record -> MetaEnv -> Maybe MetaEnv
matches _ [] [] _ _ env = return env
matches _ _ [] _ _ _ = Nothing
matches varf [] (PAny:ps) _ _ env = Nothing
matches varf (t:ts) (PAny:ps) spec rec env = matches varf ts ps spec rec env
matches varf [] (PCons _ _:ps) _ _ env = Nothing
matches varf (t:ts) (p@(PCons _ _):ps) spec rec env = 
  match varf t p spec rec env >>= matches varf ts ps spec rec
matches varf [] (PVal _:ps) _ _ env = Nothing
matches varf (t:ts) (p@(PVal _):ps) spec rec env = match varf t p spec rec env >>= 
  matches varf ts ps spec rec
matches varf ts ((PVar x):ps) spec rec env = case M.lookup x varf of
  Nothing -> match_seqvar varf x ts ps 1 (Just 1) Longest [] spec rec env
  Just (VarDecl _ lb mub strat cds) -> match_seqvar varf x ts ps lb mub strat cds spec rec env

match_seqvar varf x ts ps lb mub strat cds spec rec env = case M.lookup x env of
  -- if already bound, check whether the bound sequence is a prefix of `ts`
  -- if so, continue matching the suffix to the remaining patterns `ps`
  -- otherwise: pattern-match fail
  Just cts | tsl == cts -> matches varf tsr ps spec rec env
           | otherwise  -> Nothing
    where (tsl,tsr) = splitAt (length cts) ts
  Nothing -> -- if not yet bound
    let attempt [] = Nothing
        attempt (c:cs) = case sem_seq (map (flip sem_cond varf) cds) spec (rec, env', []) of
          Nothing    -> attempt cs --side-cons failed
          Just (_,env'',_) -> case matches varf tsr ps spec rec env'' of --ignore premise results
            Nothing -> attempt cs --rest fails
            Just env''' -> return env'''
          where (tsl,tsr) = splitAt c ts 
                env' = env `envUnite` IML.Interpreter.Types.bind x tsl
        in attempt ord_choices  
    where choices = [lb .. (maybe seq_len (min seq_len) mub)]
            where seq_len = length ts 
          ord_choices = case strat of Shortest -> choices
                                      Longest  -> reverse choices
                                      Random   -> unsafePerformIO (shuffleM choices)

match :: Varf -> Term {-closed term-} -> Pattern -> Specf -> Record -> MetaEnv -> Maybe MetaEnv
match _ (TVar _) _ _ _ _ = error "match applied to non-closed term"
match varf t p spec rec env = case (t, p) of 
  (_, PAny)                                 -> return env
  (_, PVar x)                               -> matches varf [t] [PVar x] spec rec env
  (TCons cs1 ts, PCons cs2 ps)|cs1 == cs2   -> matches varf ts ps spec rec env
  (TVal v1, PVal v2)                        -> 
      join (Funcons.Operations.structVMcompare (\t p -> match varf t p spec rec env) (\t p -> matches varf t p spec rec env) v1 v2)
        >>= (return . (env `envUnite`)) --TODO grow environment in value match
  _                                         -> Nothing

match_conf :: Varf -> Conf -> PConf -> Specf -> MetaEnv -> Maybe MetaEnv
match_conf varf (ts, rec) (PConf ps ents) spec env0 = do
  env1  <- matches varf ts ps spec rec env0
  foldM op env1 [ (t, p) | (e, p) <- ents, M.member e rec, let t = rec M.! e ]
  where op env (t,p) = matches varf t p spec rec env

subs :: MetaEnv -> [Term] {- non-closed -} -> [Term] {- closed -}
subs gam ts = concatMap (subsFlatten gam) ts

subsFlatten :: MetaEnv -> Term -> [Term]
subsFlatten gam t = case t of 
        TVar v | Just t2 <- M.lookup v gam -> t2 
               | otherwise -> error ("substitution, unbound var: " ++ show v)
        TVal v -> map TVal $ Funcons.Operations.traverseVM (subsFlatten gam) ((:[]) . subs gam) v
        TCons cs ts -> [TCons cs (subs gam ts)]

subs_expr :: MetaEnv -> [Expr] -> [Expr] {- closed -}
subs_expr gam es = concatMap subsFlattenExpr es
  where subsFlattenExpr e = case e of
          ETerm t   -> map ETerm $ subsFlatten gam t
          VOP op es -> [VOP op $ subs_expr gam es]
                     
subs_conf :: MetaEnv -> TConf -> TConf 
subs_conf gam (TConf es ents) = 
  TConf (subs_expr gam es) (map (id *** (subs_expr gam)) ents)

