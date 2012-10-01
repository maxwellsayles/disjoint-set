{-# LANGUAGE BangPatterns #-}

module Data.IntDisjointSet (IntDisjointSet,
                            empty,
                            singleton,
                            insert,
                            unsafeInsert,
                            union,
                            lookup,
                            disjointSetSize,
                            size,
                            map) where

import Control.Arrow
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Maybe
import Prelude hiding (lookup, map)

{-|
Represents a disjoint set of integers.
-}
data IntDisjointSet = IntDisjointSet { parents :: IntMap Int,
                                       ranks   :: IntMap Int }

{-|
Create a disjoint set with no members.
Takes O(1).
-}
empty :: IntDisjointSet
empty = IntDisjointSet IntMap.empty IntMap.empty

{-|
Create a disjoint set with one member.
Takes O(1).
-}
singleton :: Int -> IntDisjointSet
singleton !x = let p = IntMap.singleton x x
                   r = IntMap.singleton x 0
               in  p `seq` r `seq` IntDisjointSet p r

{-|
Insert x into the disjoint set.
If it is already a member, then do nothing,
otherwise x has no equivalence relations.
Takes O(logn).
-}
insert :: Int -> IntDisjointSet -> IntDisjointSet
insert !x set@(IntDisjointSet p _)
  | IntMap.member x p = set
  | otherwise = unsafeInsert x set
                    
{-|
Insert x into the disjoint set such that there are no
equivalence relations with x.  x *must* not already be
in the set, since this sets the rank of the singleton
set {x} to rank 0. Takes O(logn).
-}
unsafeInsert :: Int -> IntDisjointSet -> IntDisjointSet
unsafeInsert !x (IntDisjointSet p r) =
  let p' = IntMap.insert x x p
      r' = IntMap.insert x 0 r
  in  p' `seq` r' `seq` IntDisjointSet p' r'

{-|
Create an equivalence relation between x and y.
Takes O(logn * \alpha(n))
where \alpha(n) is the extremely slowly growing
inverse Ackermann function.
-}
union :: Int -> Int -> IntDisjointSet -> IntDisjointSet
union !x !y set = flip execState set $ runMaybeT $ do
  repx <- MaybeT $ state $ lookup x
  repy <- MaybeT $ state $ lookup y
  guard $ repx /= repy
  (IntDisjointSet p r) <- get
  let rankx = r IntMap.! repx
  let ranky = r IntMap.! repy
  put $! case compare rankx ranky of
    LT -> let p' = IntMap.insert repx repy p
              r' = IntMap.delete repx r
          in  p' `seq` r' `seq` IntDisjointSet p' r'
    GT -> let p' = IntMap.insert repy repx p
              r' = IntMap.delete repy r
          in  p' `seq` r' `seq` IntDisjointSet p' r'
    EQ -> let p' = IntMap.insert repx repy p
              r' = IntMap.delete repx $! IntMap.insert repy (succ ranky) r
          in  p' `seq` r' `seq` IntDisjointSet p' r'

{-|
Find the set representative for this input.
This performs path compression and so is stateful.
Takes amortized O(logn * \alpha(n))
where \alpha(n) is the extremely slowly growing
inverse Ackermann function.
-}
lookup :: Int -> IntDisjointSet -> (Maybe Int, IntDisjointSet)
lookup !x set =
  case find x set of
    Nothing  -> (Nothing, set)
    Just rep -> let set' = compress x rep set
                in  set' `seq` (Just rep, set')

{-|
Return the number of disjoint sets.
Takes O(1).
-}
disjointSetSize :: IntDisjointSet -> Int
disjointSetSize = IntMap.size . ranks

{-|
Return the number of elements in all disjoint sets.
Takes O(1).
-}
size :: IntDisjointSet -> Int
size = IntMap.size . parents

{-|
Map each member to another Int.
The map function must be a bijection, i.e. 1-to-1 mapping.
-}
map :: (Int -> Int) -> IntDisjointSet -> IntDisjointSet
map f (IntDisjointSet p r) =
  let p' = IntMap.fromList $ List.map (f *** f) $ IntMap.toList p
      r' = IntMap.fromList $ List.map (first f) $ IntMap.toList r
  in  p' `seq` r' `seq` (IntDisjointSet p' r')

-- Find the set representative.
-- This traverses parents until the parent of y == y and returns y.
find :: Int -> IntDisjointSet -> Maybe Int
find !x (IntDisjointSet p _) =
  do x' <- IntMap.lookup x p
     return $! if x == x' then x' else find' x'
  where find' y = let y' = p IntMap.! y
                  in  if y == y' then y' else find' y'

-- Given a start node and its representative, compress
-- the path to the root.
compress :: Int -> Int -> IntDisjointSet -> IntDisjointSet
compress !x !rep set@(IntDisjointSet p r)
  | x == rep = set
  | otherwise = compress x' rep set'
    where x'   = p IntMap.! x
          set' = let p' = IntMap.insert x rep p
                 in  p' `seq` IntDisjointSet p' r
  
