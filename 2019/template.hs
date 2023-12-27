module SOL where

import Data.List
import Data.Maybe
import Data.Tuple (swap)

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp x
  = fromJust . lookup x

-- 3 marks
vars :: Formula -> [Id]
vars (Var i)
  = [i]
vars (Not f)
  = vars f
vars (And f f')
  = sort (nub (vars f ++ vars f'))
vars (Or f f')
  = sort (nub (vars f ++ vars f'))

-- 1 mark
idMap :: Formula -> IdMap
idMap f
  = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Or a b))
  = And (toNNF (Not a)) (toNNF (Not b))
toNNF (Not (And a b))
  = Or (toNNF (Not a)) (toNNF (Not b))
toNNF (Not (Not a))
  = toNNF a
toNNF (Not a)
  = Not (toNNF a)
toNNF (Or a b)
  = Or (toNNF a) (toNNF b)
toNNF (And a b)
  = And (toNNF a) (toNNF b)
toNNF (Var i)
  = Var i

-- 3 marks
toCNF :: Formula -> CNF
toCNF f
  = toCNF' (toNNF f)
  where
    toCNF' :: Formula -> CNF
    toCNF' (Or a b)
      = distribute (toCNF' a) (toCNF' b)
    toCNF' (And a b)
      = And (toCNF' a) (toCNF' b)
    toCNF' a
      = a


-- 4 marks
flatten :: CNF -> CNFRep
flatten f
  = flatten' f
  where
    idm = idMap f
    flatten' :: CNF -> CNFRep
    flatten' (And a b)
      = flatten' a ++ flatten' b
    flatten' (Var i)
      = [[lookUp i idm]]
    flatten' (Not (Var i))
      = [[negate (lookUp i idm)]]
    flatten' (Or a b)
      = [concat (flatten' a ++ flatten' b)]

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits cs
  | null ucs  = (cs, [])
  | otherwise = (cs'', ucs ++ ucs')
  where
    propUnits' :: Int -> CNFRep -> CNFRep
    propUnits' i cnf
      = [filter (/= -i) ls | ls <- cnf, i `notElem` ls]
    ucs  = [x | [x] <- cs]
    cs'  = foldr propUnits' cs ucs
    (cs'', ucs') = propUnits cs'


-- 4 marks
dp :: CNFRep -> [[Int]]
dp cs
  | null cs'      = [props]
  | [] `elem` cs' = []
  | otherwise     = fmap (props ++) sats1 ++ fmap (props ++) sats2
  where
    (cs', props)  = propUnits cs
    ((i : _) : _) = cs'
    sats1         = dp ([i] : cs')
    sats2         = dp ([-i] : cs')


--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = fmap (sort . fmap idToBool) sats
  where
    idm  = idMap f
    ridm = fmap swap idm
    nums = fmap snd idm
    cs   = flatten (toCNF f)
    fillMissing :: [Int] -> [Int] -> [[Int]]
    fillMissing [] ns
      = [ns]
    fillMissing (n:ns) ns'
      | n `elem` ns' || -n `elem` ns'
        = fillMissing ns ns'
      | otherwise
        = fillMissing ns (n:ns') ++ fillMissing ns (-n:ns')
    idToBool :: Int -> (Id, Bool)
    idToBool n
      | n > 0     = (lookUp n ridm, True)
      | otherwise = (lookUp (-n) ridm, False)
    sats = concatMap (fillMissing nums) (dp cs)



