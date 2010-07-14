
module SowsR (groupByR, groupByR') where

import Data.List(nub)

groupByR :: Eq e => 
            (a -> e) ->   -- decide each group
            ([a] -> b) -> -- fold function
            [a] ->        -- input set of record
            [b]           -- output set of record
groupByR tagger reducer = (map reducer) . (mkGrpL tagger)

groupByR' :: Eq e => 
            (a -> e) ->   -- decide each group
            ([a] -> b) -> -- fold function
            [a] ->        -- input set of record
            [(e,b)]       -- output set of group tag and record
groupByR' tagger reducer xs = zip tagL $ map reducer $ mkGrpL tagger xs
  where
    tagL = mkUniqTag tagger xs

mkGrpL :: Eq e => (a -> e) -> [a] -> [[a]]
mkGrpL _ [] = undefined
mkGrpL tagger xs = map mapper $ zip tagL $ repeat tagged
  where
    tagL = nub $ map tagger xs
    tagged = zip (map tagger xs) xs

mapper :: Eq e => (e,[(e,a)]) -> [a]
mapper (_,[]) = []
mapper (tag,xs) = map snd $ filter (\(tag',_) -> tag == tag') xs

mkUniqTag :: Eq e => (a -> e) -> [a] -> [e]
mkUniqTag tagger = nub . (map tagger)



-- Examples.

tagger1 :: Int -> Int
tagger1 x = x `mod` 3

xs1 :: [Int]
xs1 = [1,2,3,4,5,6,7]

tagL1 :: [Int]
tagL1 = nub $ map tagger1 xs1

tagged1 :: [(Int,Int)]
tagged1 = zip (map tagger1 xs1) xs1

ex1 = groupByR' tagger1 sum xs1
ex2 = groupByR' tagger1 length xs1
