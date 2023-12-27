module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes n
  | n < 16    = bitTable !! n
  | otherwise = countOnes (n `div` 16) + (bitTable !! (n `mod` 16))

countOnesFrom :: Int -> Int -> Int
countOnesFrom pos n = countOnes (n .&. mask)
  where
    mask = bit pos - 1

getIndex :: Int -> Int -> Int -> Int
getIndex n idx bs = mask .&. shiftR n (idx * bs)
  where
    mask = bit bs - 1

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace 0 (_:xs) x' = x' : xs
replace i (x:xs) x' = x : replace (i-1) xs x'

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 x' xs = x' : xs
insertAt i x' (x:xs) = x : insertAt (i-1) x' xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie f fs (Leaf ns) = fs ns
sumTrie f fs (Node bv sns) = sum (fmap (sumSubNode f fs) sns)

sumSubNode :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
sumSubNode f fs (Term n) = f n
sumSubNode f fs (SubTrie t) = sumTrie f fs t

{-
--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)
-}

member :: Int -> Hash -> Trie -> Int -> Bool
member = member' 0

member' :: Int -> Int -> Hash -> Trie -> Int -> Bool
member' l n h (Leaf ns) bs = n `elem` ns
member' l n h (Node bv sns) bs
  = testBit bv idx && 
    memberSn' l n h (sns !! countOnesFrom idx bv) bs
  where
    idx = getIndex h l bs

memberSn' :: Int -> Int -> Hash -> SubNode -> Int -> Bool
memberSn' l n h (Term n') bs   = n == n'
memberSn' l n h (SubTrie t) bs = member' (l+1) n h t bs

--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert = insert' 0

insert' :: Int -> HashFun -> Int -> Int -> Int -> Trie -> Trie
insert' l hf md bs v (Leaf vs) = Leaf (nub (v:vs))
insert' l hf md bs v (Node bv sns)
  | l == md - 1          = Leaf [v]
  | not (testBit bv idx) = Node (setBit bv idx) (insertAt snIdx (Term v) sns)
  | otherwise            = Node bv sns'
  where
    idx = getIndex (hf v) l bs
    snIdx = countOnesFrom idx bv
    sn' = replaceSubNode l hf md bs v (sns !! snIdx)
    sns' = replace snIdx sns sn'

replaceSubNode :: Int -> HashFun -> Int -> Int -> Int -> SubNode -> SubNode
replaceSubNode l hf md bs v (SubTrie t) = SubTrie (insert' (l+1) hf md bs v t)
replaceSubNode l hf md bs v (Term v')
  | v == v'   = Term v'
  | otherwise = SubTrie (foldr (insert' (l+1) hf md bs) empty [v, v'])

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hf md bs = foldr (insert hf md bs) empty
