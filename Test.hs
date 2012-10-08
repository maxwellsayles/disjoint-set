import Control.Category
import Control.Arrow hiding (left, right)
import Control.Monad (guard)
import Data.IntDisjointSet
import qualified Data.List as L
import Data.Maybe
import qualified Data.Set as S
import Prelude hiding ((.), id, lookup, elem)
import Test.HUnit
import Test.QuickCheck

type SlowIntDisjointSet = S.Set (S.Set Int)

empty' :: SlowIntDisjointSet
empty' = S.empty

{-
singleton' :: Int -> SlowIntDisjointSet
singleton' x = insert' x $ empty'
-}

insert' :: Int -> SlowIntDisjointSet -> SlowIntDisjointSet
insert' x sids
  | S.null $ findSet x sids = S.insert (S.singleton x) sids
  | otherwise = sids

insertList' :: [Int] -> SlowIntDisjointSet -> SlowIntDisjointSet
insertList' l sids = foldl (flip insert') sids l

union' :: Int -> Int -> SlowIntDisjointSet -> SlowIntDisjointSet
union' x y sids = S.insert (S.union xset yset) $ S.delete xset $ S.delete yset sids
  where xset = findSet x sids
        yset = findSet y sids

findSet :: Int -> SlowIntDisjointSet -> S.Set Int
findSet a sids = S.fold f S.empty sids
  where f e old
          | S.member a e = e
          | otherwise = old

getElements :: SlowIntDisjointSet -> S.Set Int
getElements sids = S.fold S.union S.empty sids

---------------------------------------------------------

newtype IntDisjointSets = IntDisjointSets (IntDisjointSet, SlowIntDisjointSet)
  deriving (Show)

applyNTimes :: Category cat => Int -> cat b b -> cat b b
applyNTimes n f = (foldr (.) id (replicate n f))

instance Arbitrary IntDisjointSets where
  arbitrary = sized f
    where f items = runKleisli (applyNTimes n $ Kleisli oneunion) starter
              where starter = IntDisjointSets (insertList [1..items] empty, insertList' [1..items] empty')
                    n = items - (floor $ sqrt (fromIntegral items :: Double))
                    oneunion (IntDisjointSets (ids, sids)) = do
                      x <- choose (1, items)
                      y <- choose (1, items)
                      return $ IntDisjointSets (union x y ids, union' x y sids)

---------------------------------------------------------

testRedundantInsert :: Test
testRedundantInsert = TestCase $ assertEqual "Inserting an element that's already inserted doesn't cause the number of sets to grow" 1 $
  disjointSetSize $ insert elem $ singleton elem
  where elem = 0

testRedundantInsertSize :: Test
testRedundantInsertSize = TestCase $ assertEqual "Inserting an element that's already inserted doesn't cause the number of sets to grow" 1 $
  size $ insert elem $ singleton elem
  where elem = 0

testInsertGrowsNumberOfSets :: Test
testInsertGrowsNumberOfSets = TestCase $ assertEqual "Inserting an element that hasn't already been inserted grows the number of sets by one" 2 $
  disjointSetSize $ insert 1 $ singleton 2

testInsertGrowsTotalSize :: Test
testInsertGrowsTotalSize = TestCase $ assertEqual "Inserting an element that hasn't already been inserted grows the total size by one" 2 $
  size $ insert 1 $ singleton 2

testInsertListSize :: [Int] -> Bool
testInsertListSize l = size (insertList l empty) == length (L.nub l)

testInsertListDisjointSetSize :: [Int] -> Bool
testInsertListDisjointSetSize l = disjointSetSize (insertList l empty) == length (L.nub l)

----------------------------------------------------------

testInsertConsistent :: IntDisjointSets -> Bool
testInsertConsistent (IntDisjointSets (ids, sids)) = all check $ S.toList $ getElements sids
  where check e = findSet e sids == findSet rep sids
          where rep = fromJust $ fst $ lookup e ids

testMembersGoToSameItem :: IntDisjointSets -> Bool
testMembersGoToSameItem (IntDisjointSets (ids, sids)) = all f $ S.toList sids
  where allTheSame [] = True
        allTheSame l = all (== head l) $ tail l
        f :: S.Set Int -> Bool
        f s = allTheSame $ L.map (fst . ((flip lookup) ids)) $ S.toList s

testSizesAreSame :: IntDisjointSets -> Bool
testSizesAreSame (IntDisjointSets (ids, sids)) = size ids == S.size (getElements sids)

testNumberOfSetsAreSame :: IntDisjointSets -> Bool
testNumberOfSetsAreSame (IntDisjointSets (ids, sids)) = disjointSetSize ids == S.size sids

------------------------------------------------------------

optimizeByNone :: IntDisjointSets -> IntDisjointSets
optimizeByNone = id

optimizeByLookup :: IntDisjointSets -> IntDisjointSets
optimizeByLookup (IntDisjointSets (ids, sids)) = IntDisjointSets (optimized, sids)
  where optimized = foldl (\ ids' e -> snd $ lookup e ids') ids $ S.toList $ getElements sids

optimizeByOptimize :: IntDisjointSets -> IntDisjointSets
optimizeByOptimize (IntDisjointSets (ids, sids)) = IntDisjointSets (optimize ids, sids)

optimizeByMap :: IntDisjointSets -> IntDisjointSets
optimizeByMap (IntDisjointSets (ids, sids)) = IntDisjointSets (Data.IntDisjointSet.map (+ 1) ids, S.map (S.map (+ 1)) sids)

optimizeByMerge :: IntDisjointSets -> IntDisjointSets
optimizeByMerge untouched@(IntDisjointSets (_, sids))
  | S.size sids == 1 = untouched
  | otherwise = IntDisjointSets (unsafeMerge left right, sids)
  where sets = S.toList $ sids
        (mergel, merger) = splitAt ((L.length sets) `div` 2) sets
        (left, right) = (f mergel, f merger)
          where f l = foldl g starter l
                  where starter = insertList (S.toList $ getElements $ S.fromList l) empty
                        g shallow s = foldl (\ accum e -> union (head l') e accum) shallow l'
                          where l' = S.toList s

--------------------------------------------------------------

testInsert :: Test
testInsert = TestList [ testRedundantInsert
                      , testRedundantInsertSize
                      , testInsertGrowsNumberOfSets
                      , testInsertGrowsTotalSize
                      ]

runQuickCheckAndGuard :: Test.QuickCheck.Testable prop => prop -> IO ()
runQuickCheckAndGuard f = do
  results <- quickCheckResult f
  guard $ check results
  where check (Success _ _ _) = True
        check (GaveUp _ _ _) = False
        check (Failure _ _ _ _ _ _ _) = False
        check (NoExpectedFailure _ _ _) = False

main :: IO ()
main = do
  results <- runTestTT $ TestList [testInsert]
  guard (errors results == 0 && failures results == 0)
  runQuickCheckAndGuard testInsertListSize
  runQuickCheckAndGuard testInsertListDisjointSetSize

  sequence_ [runQuickCheckAndGuard (x . y) | x <- [ testInsertConsistent
                                                  , testMembersGoToSameItem
                                                  , testSizesAreSame
                                                  , testNumberOfSetsAreSame
                                                  ],
                                             y <- [ optimizeByNone
                                                  , optimizeByNone
                                                  , optimizeByLookup
                                                  , optimizeByOptimize
                                                  , optimizeByMap
                                                  , optimizeByMerge
                                                  ]]
