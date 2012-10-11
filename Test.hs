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

{-|
This is a reference implementation of the IntDisjointSet, implemented as a set of sets.
The 'disjoint' property is enforced by the insert function.
-}
type SlowIntDisjointSet = S.Set (S.Set Int)

empty' :: SlowIntDisjointSet
empty' = S.empty

{-|
This function is never needed, so to keep -Wall happy, it's commented out.
-}
{-
singleton' :: Int -> SlowIntDisjointSet
singleton' x = insert' x $ empty'
-}

{-|
Try to find the set. If the set is empty, that means that the set doesn't exist, in
which case, we're all set to insert it. Inserting it just creates a set with 1 element
and adds it to the SlowIntDisjointSet. Otherwise, it does nothing.
-}
insert' :: Int -> SlowIntDisjointSet -> SlowIntDisjointSet
insert' x sids
  | S.null $ findSet x sids = S.insert (S.singleton x) sids
  | otherwise = sids

{-|
Folding insert' over a list
-}
insertList' :: [Int] -> SlowIntDisjointSet -> SlowIntDisjointSet
insertList' l sids = foldl (flip insert') sids l

{-|
Find the set that x is in, and the set that y is in. Delete those two sets from the
SlowIntDisjointSet. If x or y isn't found, its containing set will be empty, and delete
does nothing if the given element isn't in the set. Once you've deleted the two sets
from the SlowIntDisjointSet, insert the union of the two back in.
-}
union' :: Int -> Int -> SlowIntDisjointSet -> SlowIntDisjointSet
union' x y sids = S.insert (S.union xset yset) $ S.delete xset $ S.delete yset sids
  where xset = findSet x sids
        yset = findSet y sids

{-|
Iterate through all the constituent sets. If the given element is a member of the
curent set, set the accumulator equal to the current set. Otherwise, keep the
accumulator empty.
-}
findSet :: Int -> SlowIntDisjointSet -> S.Set Int
findSet a sids = S.fold f S.empty sids
  where f e old
          | S.member a e = e
          | otherwise = old

{-|
The union of all the constituent sets
-}
getElements :: SlowIntDisjointSet -> S.Set Int
getElements sids = S.fold S.union S.empty sids

{-|
This is the same as insertList', but operates on the real IntDisjointSet. It's just a
convenience function.
-}
insertList :: [Int] -> IntDisjointSet -> IntDisjointSet
insertList xs set = foldr insert set xs

---------------------------------------------------------

{-|
This type is used to join an instance of the real IntDisjointSet with an instance of the
reference implementation, so we can compare the instances.
-}
newtype IntDisjointSets = IntDisjointSets (IntDisjointSet, SlowIntDisjointSet)
  deriving (Show)

{-|
Convenience function.
applyNTimes 4 f = f . f . f . f
applyNTimes 5 f = f . f . f . f . f
-}
applyNTimes :: Category cat => Int -> cat b b -> cat b b
applyNTimes n f = (foldr (.) id (replicate n f))

{-|
Create random IntDisjointSets by following a procedure of random inserts and random
unions. Each of these operations is performed on both the IntDisjointSet and the
reference implementation. This way, we get mirror images of each other, so our tests
can compare properties of the two.
-}
instance Arbitrary IntDisjointSets where
  arbitrary = sized f
    where f items = runKleisli (applyNTimes n $ Kleisli oneunion) starter
                    -- First, insert 'items' elements into both *IntDisjointSets
              where starter = IntDisjointSets (insertList [1..items] empty,
                                               insertList' [1..items] empty')
                    -- This is the number of random unions to perform
                    n = items - (floor $ sqrt (fromIntegral items :: Double))
                    -- Perform a single random union. We can use the 'Gen' monad to get
                    -- randomness. Because the applyNTimes function works on any
                    -- category, we can use it on this with the Kleisli operator.
                    oneunion :: IntDisjointSets -> Gen IntDisjointSets
                    oneunion (IntDisjointSets (ids, sids)) = do
                      x <- choose (1, items)
                      y <- choose (1, items)
                      return $ IntDisjointSets (union x y ids, union' x y sids)

---------------------------------------------------------

testRedundantInsert :: Test
testRedundantInsert = TestCase $ assertEqual "Inserting an element that's already inserted doesn't cause the number of elements to grow" 1 $
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
testInsertGrowsTotalSize = TestCase $ assertEqual "Inserting an element that hasn't already been inserted grows the number of elements by one" 2 $
  size $ insert 1 $ singleton 2

{-|
Inserting n elements makes the IntDisjointSet have n constituent elements
-}
testInsertListSize :: [Int] -> Bool
testInsertListSize l = size (insertList l empty) == length (L.nub l)

{-|
Inserting n elements makes the IntDisjointSet have n constituent sets
-}
testInsertListDisjointSetSize :: [Int] -> Bool
testInsertListDisjointSetSize l = disjointSetSize (insertList l empty) ==
  length (L.nub l)

----------------------------------------------------------

{-|
For every item in the reference implementation, ask the IntDisjointSet for its
representative. Make sure that the item and the representative are in the same set in
the reference implementation
-}
testInsertConsistent :: IntDisjointSets -> Bool
testInsertConsistent (IntDisjointSets (ids, sids)) = all check $ S.toList $
  getElements sids
  where check e = findSet e sids == findSet rep sids
          where rep = fromJust $ fst $ lookup e ids

{-|
Do the following for each set in the reference implementation:
For each item in the set, ask the IntDisjointSet for its representative. Make sure all
the representatives in this set are the same
-}
testMembersGoToSameItem :: IntDisjointSets -> Bool
testMembersGoToSameItem (IntDisjointSets (ids, sids)) = all f $ S.toList sids
  where allTheSame [] = True
        allTheSame l = all (== head l) $ tail l
        f :: S.Set Int -> Bool
        f s = allTheSame $ L.map (fst . ((flip lookup) ids)) $ S.toList s

{-|
The number of elements should be the same in the two implementations
-}
testSizesAreSame :: IntDisjointSets -> Bool
testSizesAreSame (IntDisjointSets (ids, sids)) = size ids == S.size (getElements sids)

{-|
The number of sets should be the same in the two implementations
-}
testNumberOfSetsAreSame :: IntDisjointSets -> Bool
testNumberOfSetsAreSame (IntDisjointSets (ids, sids)) = disjointSetSize ids ==
  S.size sids

insertAndTest :: Int -> (Bool, IntDisjointSet) -> (Bool, IntDisjointSet)
insertAndTest x (_, set) =
  let set' = insert x set
  in  case lookup x set of
        -- x was already in set. The two sets should be unchanged.
        (Just _, _) -> (L.sort (fst (toList set)) == L.sort (fst (toList set')), set')
        -- x is new to the set. The sets should be unchanged except for entry x.
        (Nothing, _) -> let xs = fst $ toList set'
                   in  ((x,x) `L.elem` xs &&
                        L.sort (L.delete (x,x) xs) == L.sort (fst (toList set)), set')

testInsertAndTest :: [Int] -> Bool
testInsertAndTest l = all fst $ scanl (flip insertAndTest) (True, empty) l

unionAndTest :: (Int, Int) -> (Bool, IntDisjointSet) -> (Bool, IntDisjointSet)
unionAndTest (x', y') (_, set) = case (lookup x' set, lookup y' set) of
  -- Both elements are present, but they may be in the same set
  ((Just x, _), (Just y, _)) -> (if x == y then L.sort (fst (toList set)) ==
                                                L.sort (fst (toList unioned))
                                   else size unioned == size set &&
                                     disjointSetSize unioned == disjointSetSize set - 1,
                                 unioned)
  _ -> (True, set)
  where unioned = union x' y' set
  
testUnionAndTest :: (IntDisjointSets, [(Int, Int)]) -> Bool
testUnionAndTest (IntDisjointSets (ids, _), l) = all fst $ scanl (flip unionAndTest) (True, ids) l

------------------------------------------------------------

{-|
These functions shouldn't change the IntDisjointSet in a user-visible way. The idea is
to run the previous test suite on the output of these functions, and they should still
all pass. The idea is to show that these operations are transparent.
-}

{-|
Call lookup on an element with the IntDisjointSet. Disregard the element's
representative, but keep track of the partially-optimized IntDisjointSet. Fold this
across all the elements in the reference implementation.
-}
optimizeByLookup :: IntDisjointSets -> IntDisjointSets
optimizeByLookup (IntDisjointSets (ids, sids)) = IntDisjointSets (optimized, sids)
  where optimized = foldl (\ ids' e -> snd $ lookup e ids') ids $
          S.toList $ getElements sids

{-|
Map (+1) across the reference implementation and the IntDisjointSet.
-}
optimizeByMap :: IntDisjointSets -> IntDisjointSets
optimizeByMap (IntDisjointSets (ids, sids)) = IntDisjointSets
  (Data.IntDisjointSet.map (+ 1) ids, S.map (S.map (+ 1)) sids)

{-|
Disregard the input IntDisjointSet. Take the reference implementation and split it down
the middle into two groups of sets. Recreate these two groups of sets into two new
IntDisjointSets by inserting each element and then unioning the relevant sets together.
Then, merge the two IntDisjointSets together.
-}
optimizeByMerge :: IntDisjointSets -> IntDisjointSets
optimizeByMerge untouched@(IntDisjointSets (_, sids))
  | S.size sids == 1 = untouched
  | otherwise = IntDisjointSets (unsafeMerge left right, sids)
  where sets = S.toList $ sids
        (mergel, merger) = splitAt ((L.length sets) `div` 2) sets
        (left, right) = (f mergel, f merger)
          where f l = foldl g starter l
                  where starter = insertList (S.toList $ getElements $ S.fromList l)
                          empty
                        g shallow s = foldl (\ accum e -> union (head l') e accum)
                          shallow l'
                          where l' = S.toList s

--------------------------------------------------------------

{-|
All the HUnit-style functions that relate to the insert function
-}
testInsert :: Test
testInsert = TestList [ testRedundantInsert
                      , testRedundantInsertSize
                      , testInsertGrowsNumberOfSets
                      , testInsertGrowsTotalSize
                      ]

{-|
Run quickCheck, and make sure the result is acceptable. mzero for IO is to throw an
exception, which is unchecked and will cause the program to terminate with an error
code, which is what we want. There's probably a better way to do this, but I can't find
it.
-}
runQuickCheckAndGuard :: Test.QuickCheck.Testable prop => prop -> IO ()
runQuickCheckAndGuard f = do
  results <- quickCheckResult f
  guard $ check results
  where check (Success _ _ _) = True
        check (GaveUp _ _ _) = False
        check (Failure _ _ _ _ _ _ _) = False
        check (NoExpectedFailure _ _ _) = False

{-|
Run all the tests
-}
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
                                             y <- [ id
                                                  , optimizeByLookup
                                                  , optimizeByMap
                                                  , optimizeByMerge
                                                  ]]

  runQuickCheckAndGuard testInsertAndTest
  runQuickCheckAndGuard testUnionAndTest
