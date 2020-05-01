
module IML.Trans.Unmix where
 
import IML.Grammar.Low as LOW
import IML.Grammar.Mixed as Mixed
import IML.Grammar.Shared as Shared
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Bindings (get_eidss)
import IML.Trans.RemoveRO
import IML.Trans.ProMan
import IML.Trans.ToLower

import Control.Arrow ((>>>))
import Control.Monad (forM)

import Data.Set (toList)

-- | Transform a 'MixedProgram' into a 'HighProgram' simply by forgetting
-- the procedures in it (if any)
tohigh :: Component MixedProgram HighProgram
tohigh = remove_read_only >>> component_ program
  where program (Program (Spec decls) qs) = Program (Spec (forgetProc decls)) qs
        forgetProc :: [AnyDecls (Either Rule ProcDecl)] -> [AnyDecls Rule]
        forgetProc = concatMap op 
          where op (ARuleDecl (Left rule)) = [ARuleDecl rule]
                op (ARuleDecl (Right _))   = []
                op (AnEntDecl d)           = [AnEntDecl d]
                op (ATConsDecl d)          = [ATConsDecl d]
                op (ARelDecl r)            = [ARelDecl r]
                op (AVarDecl v)            = [AVarDecl v]

tolow :: Component MixedProgram Program
tolow = unmix

unmix :: Component MixedProgram Program
unmix = remove_read_only >>> component program
  where program :: MixedProgram -> ProMan Program
        program (Program (Spec decls) qs) = do
          decls' <- mergeTrans <$> genTrans decls 
          return (Program (Spec decls') qs)

genTrans :: [AnyDecls (Either Rule ProcDecl)] -> ProMan [AnyDecls ProcDecl]
genTrans ds = mapM (mapM op) ds
  where 
        op :: Either Rule ProcDecl -> ProMan ProcDecl 
        op (Left rule)  = tRule_ rule 
        op (Right d)    = cSRI d

mergeTrans :: [AnyDecls ProcDecl] -> [AnyDecls ProcDecl]
mergeTrans decls = 
  case foldr merge (Nothing,[]) decls of  (Nothing, acc)  -> acc
                                          (Just t, acc)   -> ARuleDecl t : acc
  where merge (ARuleDecl (Proc r f mc ss)) (mtd, acc) = 
          case mtd of 
            Nothing   -> (Just (Proc r f mc ss), acc)
            Just (Proc r2 f2 mc2 sss) 
              | r == r2, f == f2, mc == mc2 -> (Just (Proc r f mc (ss++sss)), acc)
              | otherwise -> (Just (Proc r f mc ss)
                             ,(ARuleDecl (Proc r2 f2 mc2 sss)):acc)
        merge odecl (mtd,acc) = 
          case mtd of Nothing -> (Nothing, cast odecl: acc)
                      Just td -> (Nothing, cast odecl: ARuleDecl td: acc)
          where cast (AnEntDecl e)  = AnEntDecl e
                cast (ARelDecl e)   = ARelDecl e
                cast (ATConsDecl e) = ATConsDecl e
                cast _ = error "pProgram cast"

-- | Computes the `StaticRuleInfo` for a particular procedure declaration
cSRI :: ProcDecl -> ProMan ProcDecl
cSRI (Proc prio rel mc sss) = do
  sss' <- forM sss $ \ss -> do 
    rid <- fresh_id
    let sinfo = SRI rid (toList $ get_eidss ss) 
    return (map (up sinfo) ss)
  return (Proc prio rel mc sss') 
  where up sinfo s = case s of 
          Branches sss      -> Branches (map (map (up sinfo)) sss)
          Commit i Nothing  -> Commit i (Just sinfo)
          _                 -> s

