module Alloc where

import Data.Maybe
import Data.List
import Data.Ord (comparing)
import Debug.Trace

import Types
import Examples

------------------------------------------------------
--
-- Part I
--
count :: Eq a => a -> [a] -> Int
count x
  = length . filter (== x)

degrees :: Eq a => Graph a -> [(a, Int)]
degrees (us, es)
  = [(u, count u us') | u <- us]
  where
    (us1, us2) = unzip es
    us'        = us1 ++ us2

neighbours :: Eq a => a -> Graph a -> [a]
neighbours u (_, es)
  = [v | (u', v) <- es, u' == u] ++ [v | (v, u') <- es, u' == u]

removeNode :: Eq a => a -> Graph a -> Graph a
removeNode u (us, es)
  = (filter (/= u) us, [e | e@(u1, u2) <- es, u1 /= u, u2 /= u])

------------------------------------------------------
--
-- Part II
--
colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph _ ([], [])
  = []
colourGraph maxc g
  | null availc = (n, 0) : cs
  | otherwise   = (n, head availc) : cs
  where
    (n, _) = minimumBy (comparing snd) (degrees g)
    g'     = removeNode n g
    cs     = colourGraph maxc g'
    availc = [1..maxc] \\ fmap (`lookUp` cs) (neighbours n g)

    

------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap cs
  = ("return", "return") : fmap changeMap cs
  where
    changeMap :: (Id, Int) -> (Id, Id)
    changeMap (i, 0)
      = (i, i)
    changeMap (i, n)
      = (i, 'R' : show n)


buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments vs idm
  = [Assign (lookUp v idm) (Var v) | v <- vs]

renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp (Const i) _
  = Const i
renameExp (Var i) idm
  = Var (lookUp i idm)
renameExp (Apply o e e') idm
  = Apply o (renameExp e idm) (renameExp e' idm)

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock b idm
  = filter redundantAssignment (fmap renameStatement b)
  where
    renameStatement :: Statement -> Statement
    renameStatement (Assign i e)
      = Assign (lookUp i idm) (renameExp e idm)
    renameStatement (If e b1 b2)
      = If (renameExp e idm) (renameBlock b1 idm) (renameBlock b2 idm)
    renameStatement (While e b)
      = While (renameExp e idm) (renameBlock b idm)
    redundantAssignment :: Statement -> Bool
    redundantAssignment (Assign i (Var i'))
      = i /= i'
    redundantAssignment _
      = True

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--
buildIG :: [[Id]] -> IG
buildIG idss
  = (nub (concat idss), nub (concat es))
  where
    es = [[(u, v) | u <- ids, v <- ids, u < v] | ids <- idss]

-----------------------------------------------------
--
-- Part V
--
liveVars :: CFG -> [[Id]]
liveVars cfg
  = fmap (liveVars' []) [0..length cfg - 1]
  where
    liveVars' :: [Int] -> Int -> [Id]
    liveVars' vis line
      | line `elem` vis = []
      | otherwise       = nub (us ++ (uSuccs \\ [ds]))
      where
        ((ds, us), succ) = cfg !! line
        uSuccs           = concatMap (liveVars' (line : vis)) succ


buildCFG :: Function -> CFG
buildCFG (_, _, b)
  = undefined
  where
    getVarIds :: Exp -> [Id]
    getVarIds (Var i)
      = [i]
    getVarIds (Const _)
      = []
    getVarIds (Apply _ e1 e2)
      = nub (getVarIds e1 ++ getVarIds e2)
    buildCFG' :: Block -> Int -> (Int, CFG)
    buildCFG' [] line
      = (line, [])
    buildCFG' (Assign i e : b) line
      | i == "return" = (nextAvail, ((i, getVarIds e), []) : cfg)
      | null cfg      = (nextAvail, ((i, getVarIds e), []) : cfg)
      | otherwise     = (nextAvail, ((i, getVarIds e), [line + 1]) : cfg)
      where
        (nextAvail, cfg) = buildCFG' b (line + 1)
    buildCFG' (If e b1 b2 : b) line
      = (nextAvail, ifLine : cfg1' ++ cfg2 ++ cfg)
      where
        (nextAvail1, cfg1) = buildCFG' b1 (line + 1)
        (nextAvail2, cfg2) = buildCFG' b2 nextAvail1
        (nextAvail, cfg)   = buildCFG' b nextAvail2
        (vars1, succ1)     = last cfg1
        cfg1Last'          = (vars1, nextAvail2 : succ1)
        cfg1'              = take (length cfg1 - 1) cfg1 ++ [cfg1Last']
        ifLine             = (("_", getVarIds e), [line + 1, nextAvail1]) 
    buildCFG' (While e b : b') line
      = (nextAvail', whileLine : cfg ++ cfg')
      where
        (nextAvail, cfg)   = buildCFG' b (line + 1)
        (nextAvail', cfg') = buildCFG' b' nextAvail
        whileLine          = (("_", getVarIds e), [line + 1, nextAvail'])

