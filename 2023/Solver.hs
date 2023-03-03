module Solver where

import Data.List
import Data.Char

import Types
import WordData
import Clues
import Examples

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp s
  = [toLower c | c <- s, c `notElem` punctuation]

split2 :: [a] -> [([a], [a])]
split2 xs
  = [splitAt i xs | i <- [1..length xs - 1]]

split3 :: [a] -> [([a], [a], [a])]
split3 xs
  = [(xs0, xs1', xs2) | (xs1, xs2) <- split2 xs, (xs0, xs1') <- split2 xs1] ++
    [(xs1, [], xs2) | (xs1, xs2) <- split2 xs]

uninsert :: [a] -> [([a], [a])]
uninsert xs
  = [(xs2, xs1 ++ xs3) | (xs1, xs2, xs3) <- split3 xs, not (null xs2)]

-- {- Uncomment these functions when you have defined the above.
split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs
-- -}

------------------------------------------------------
-- Part II

matches :: String -> ParseTree -> Bool
matches s (Synonym s')
  = s `elem` synonyms s'
matches s (Anagram _ s')
  = sort s == sort s'
matches s (Reversal _ t)
  = matches (reverse s) t
matches s (Insertion _ t1 t2)
  = any (\(s1, s2) -> matches s1 t1 && matches s2 t2) (uninsert s)
matches s (Charade _ t1 t2)
  = any (\(s1, s2) -> matches s1 t1 && matches s2 t2) (split2 s)
-- Pre: (words s') is not empty
matches s (HiddenWord _ s')
  | null ws   = s `elem` [w' | (_, w', _) <- split3 w, not (null w')]
  | otherwise = s `elem` hws
  where
    (w : ws)
      = words s'
    (ws', [w'])
      = splitAt (length ws - 1) ws
    hws
      = [w1 ++ concat ws' ++ w2 | (_, w1) <- split2 w, (w2, _) <- split2 w']



evaluate :: Parse -> Int -> [String]
evaluate (d, _, t) l
  = [s | s <- synonyms (unwords d), length s == l, matches s t]

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseCharade ws,
            parseHiddenWord ws]
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym ws
  | null (synonyms s) = []
  | otherwise         = [Synonym s]
  where
    s = unwords ws

parseOneArgument :: (Indicator -> b -> ParseTree)
                  -> [String]
                  -> ([String] -> [a])
                  -> (a -> b)
                  -> [String]
                  -> [ParseTree]
parseOneArgument comp inds expand process ws
  = [comp ind (process t) | (ind, arg) <- split2M ws
    , unwords ind `elem` inds
    , t <- expand arg]

parseAnagram :: [String] -> [ParseTree]
parseAnagram
  = parseOneArgument Anagram anagramIndicators (: []) concat
  -- = [Anagram ind (concat arg) | (ind, arg) <- split2M ws
  --   , unwords ind `elem` anagramIndicators]

parseReversal :: [String] -> [ParseTree]
parseReversal
  = parseOneArgument Reversal reversalIndicators parseWordplay id
  -- = [Reversal ind t | (ind, arg) <- split2M ws
  --   , unwords ind `elem` reversalIndicators
  --   , t <- parseWordplay arg]

parseHiddenWord :: [String] -> [ParseTree]
parseHiddenWord
  = parseOneArgument HiddenWord hiddenWordIndicators (: []) unwords

parseTwoArguments :: (Indicator -> ParseTree -> ParseTree -> ParseTree)
                  -> [String]
                  -> [String]
                  -> [String]
                  -> [ParseTree]
parseTwoArguments comp inds1 inds2 ws
  = [comp ind t t' | (arg, ind, arg') <- split3 ws
    , unwords ind `elem` inds1
    , t <- parseWordplay arg
    , t' <- parseWordplay arg'] ++
    [comp ind t' t | (arg, ind, arg') <- split3 ws
    , unwords ind `elem` inds2
    , t <- parseWordplay arg
    , t' <- parseWordplay arg']

parseInsertion :: [String] -> [ParseTree]
parseInsertion
  = parseTwoArguments Insertion insertionIndicators envelopeIndicators
  -- = [Insertion ind t t'
  -- | (arg, ind, arg') <- split3 ws, unwords ind `elem` insertionIndicators
  -- , t <- parseWordplay arg, t' <- parseWordplay arg']
  -- ++ [Insertion ind t' t
  -- | (arg, ind, arg') <- split3 ws, unwords ind `elem` envelopeIndicators
  -- , t <- parseWordplay arg, t' <- parseWordplay arg']

parseCharade :: [String] -> [ParseTree]
parseCharade
  = parseTwoArguments Charade beforeIndicators afterIndicators


-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText ws
  = [(d, l, t) | (d, l, wp) <- split3M ws
    , unwords l `elem` linkWords
    , (not . null . synonyms . unwords) d
    , t <- parseWordplay wp]

solve :: Clue -> [Solution]
solve c@(_, n)
  = [(c, p, soln) | p <- parseClue c, soln <- evaluate p n]


------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]


