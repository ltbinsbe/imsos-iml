
module IML.CodeGen.DirectHaskellSupport (
  Term(..), TermCons, termApp, term2Expr, ioAppRes,
  TransF, SemF, tr_single, tr_many, 
  Exceptions, assert, evalBranches, evalExpr, coerceExpr, 
  Ents, entEmpty, entLookup, entInsert, entDelete, entNull, entFromList, entMember,
  unionWO, unionRW, unionRO,
  pmFail, substitute, substituteVal, 
  IML.CodeGen.DirectHaskellSupport.match, 
  IML.CodeGen.DirectHaskellSupport.matches, 
  )where

import Funcons.Operations
import Control.Monad.Identity

import Data.List (intercalate)
import Data.Maybe (isJust)
import qualified Data.Map as M

type TermCons   = [Term] -> Term
data Term       = Term String [Term] (Bool -> RSymb -> TransF)
                | Val Val
                | Var MVar
type TransF     = Ents -> Ents -> Exceptions (Term, Ents, Ents)
type SemF       = [Term] -> TransF

instance HasValues Term where
  project (Val v)  = Just v
  project _         = Nothing

  inject = Val

termApp ::      Term 
            ->  Bool  -- repetition? 
            ->  Bool  -- value reflexive?
            ->  RSymb -> TransF
termApp (Term _ _ t) rep _ rel ro rw = t rep rel ro rw
termApp (Val v) False False _ _ _ = ValStepExc v 
termApp (Val v) _ _ _ _ _  = return (Val v, entEmpty, entEmpty)
termApp (Var v) _ _ _ _ _  = CodeGenError "termApp var" 

term2Expr :: Term -> Exceptions (OpExpr Term)
term2Expr t@(Term _ _ _)  = NotAValExc t
term2Expr (Val v)         = return $ ValExpr v
term2Expr (Var v)         = CodeGenError "term2Expr var"

tr_single :: RSymb -> SemF -> [Term] -> TransF
tr_single _ = ($) 

tr_many :: RSymb -> SemF -> [Term] -> TransF
tr_many r semf args ro rw = case semf args ro rw of
  NoExc (Val t', rw', wo')  -> NoExc (Val t', rw', wo')
  NoExc (Term cs args t', rw', wo') -> 
    case t' True r ro (unionRW rw rw') of
      NoExc (t'', rw'', wo'') -> 
        NoExc (t'', unionRW rw' rw'', unionWO wo' wo'')
      _ -> NoExc (Term cs args t', rw', wo')
  ValStepExc v              -> NoExc (Val v, entEmpty, entEmpty) 
  failure                   -> failure 

ioAppRes :: Exceptions (Term, Ents, Ents) -> IO ()
ioAppRes e = putStrLn $ case e of
  NoExc (Val v, rw, wo) -> unlines [show v, show rw, show wo]
  NoExc (t2, rw, wo)    -> unlines ["a stuck term:", show t2, show rw, show wo]
  ValStepExc v          -> unlines ["attempt to transition a value:", show v]
  exc                   -> unlines [show exc]

type Env    = MetaEnv Term
type Val    = Values Term 
type RSymb  = String

type EID    = String
type Ents   = M.Map EID Val

entEmpty :: Ents
entEmpty = M.empty

entLookup :: EID -> Ents -> Maybe Val
entLookup = M.lookup

entInsert :: EID -> Val -> Ents -> Ents
entInsert = M.insert

entDelete :: EID -> Ents -> Ents
entDelete = M.delete

entNull :: Ents -> Bool
entNull = null

entMember :: EID -> Ents -> Bool 
entMember = M.member

entFromList :: [(EID, Val)] -> Ents
entFromList = M.fromList

unionWO :: Ents -> Ents -> Ents
unionWO = M.unionWith op
  where op (List ls) (List rs) = List (ls ++ rs)
        op _ _ = error "uniteWO, values not lists"

unionRW :: Ents -> Ents -> Ents
unionRW = M.unionWith op
  where op l r = r

unionRO :: Ents -> Ents -> Ents
unionRO = unionRW

--data Meta a = Meta (Exceptions a)

data Exceptions a = PatternExc String 
                  | ExprExc String {- expr -} String {- reason -}
                  | AssertExc String
                  | NoMoreBranches [Exceptions a]
                  | ValStepExc Val
                  | NotAValExc Term
                  | CodeGenError String
                  | NoExc a 

instance Show a => Show (Exceptions a) where
  show (PatternExc str) = "pattern match failed: " ++ str
  show (ExprExc expr str) = "could not evaluate expression " ++ expr ++ "\n" ++ str
  show (AssertExc str)  = "assertion failed: " ++ str
  show (NoMoreBranches es) = unlines ("no rule applicable:": concat (zipWith op [1..] es))
    where op i e = ["== attempt " ++ show i ++ " ==", show e]
  show (ValStepExc v)  = "attempting to step value: " ++ show v
  show (NotAValExc t)  = "attempting to coerce a term to an expression"
  show (NoExc a)       = show a
  show (CodeGenError err) = "error caused by code-generation, REPORT THIS: " ++ err 

instance Show Term where
  show (Var v) = show v
  show (Val v) = show v
  show (Term c cs _) | null cs = c 
                     | otherwise = c ++ "(" ++ intercalate "," (map show cs) ++ ")"

instance Functor Exceptions where
  fmap = (<$>)

instance Applicative Exceptions where
  pure = return
  (<*>) = ap

instance Monad Exceptions where
  return = NoExc 
  m >>= f = case m of
              NoExc a -> f a
              _       -> castException m              

castException :: Exceptions a -> Exceptions b
castException e = case e of
  PatternExc str    -> PatternExc str
  AssertExc str     -> AssertExc str
  NoMoreBranches s1 -> NoMoreBranches (map castException s1)
  ExprExc s1 s2     -> ExprExc s1 s2
  ValStepExc v      -> ValStepExc v
  NotAValExc t      -> NotAValExc t
  CodeGenError err  -> CodeGenError err
  NoExc a           -> error "castException: no exception" 

evalBranches :: [Exceptions a] -> Exceptions a
evalBranches alts = evalBranches' alts alts
  where 
    evalBranches' all []     = NoMoreBranches all
    evalBranches' all (x:xs) = case x of
      NoExc a -> NoExc a
      _       -> evalBranches' all xs

assert :: Bool -> String -> Exceptions ()
assert False = AssertExc 
assert True = const (NoExc ())

evalExpr :: OpExpr Term -> Exceptions Val
evalExpr expr = case eval expr of
  Error _ (SortErr str)   -> ExprExc expr' str
  Error _ (DomErr str)    -> ExprExc expr' str
  Error _ (ArityErr str)  -> ExprExc expr' str
  Error _ (Normal _)      -> ExprExc expr' "no further message"
  Success v               -> NoExc v
  where expr' = show expr

coerceExpr :: OpExpr Term -> Val
coerceExpr e = case evalExpr e of
  NoExc v -> v
  _       -> error ("could not coerce expression: " ++ show e)

-- pattern matching
pmFail :: String -> Exceptions a
pmFail = PatternExc

matches :: [Term] -> [VPattern Term] -> String -> Env -> Exceptions Env
matches ts ps str env0 = case Funcons.Operations.matches ps ts of
  Nothing   -> pmFail str
  Just env  -> return (env0 `envUnite` env)

match :: Term -> VPattern Term -> String -> Env -> Exceptions Env 
match t p str env0 = case Funcons.Operations.match p t of
  Nothing   -> pmFail str
  Just env  -> return (env0 `envUnite` env)

substitute :: Env -> Term -> Term
substitute gam t = case t of
  Var x -> maybe (error ("REPORT THIS: unbound var " ++ show x)) 
              id (termBinding gam x)
  Val v -> Val (subsVal True gam (substitute gam) v)
  Term nm ts f -> Term nm (concatMap (subss gam) ts) f

substituteVal :: Env -> Val -> Val
substituteVal gam = subsVal True gam (substitute gam) 
  
subss :: Env -> Term -> [Term]
subss gam t = case t of
  Var x -> maybe [t] id (termsBinding gam x)
  Val v -> map Val $ subsVals True gam (substitute gam) v
  _     -> [substitute gam t]

instance Ord Term where
  Val v1 `compare` Val v2 = v1 `compare` v2
  Val _ `compare` _ = LT
  _ `compare` Val _ = GT
  Var x1 `compare` Var x2 = x1 `compare` x2
  Var _ `compare` _ = LT
  _ `compare` Var _ = GT
  (Term n1 ts1 _) `compare` (Term n2 ts2 _) = (n1,ts1) `compare` (n2,ts2)


instance Eq Term where
  (Val v1) == (Val v2) = v1 == v2
  (Var x1) == (Var x2) = x1 == x2
  (Term x1 ts1 _) == (Term x2 ts2 _) = (x1,ts1) == (x2,ts2)
  _ == _ = False
