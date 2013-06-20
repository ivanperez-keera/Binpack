-- Copyright (c) 2009, Bjoern B. Brandenburg <bbb [at] cs.unc.edu>
--
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * Neither the name of the copyright holder nor the names of any
--       contributors may be used to endorse or promote products derived from
--       this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
-- ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
-- LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
-- CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
-- SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
-- INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
-- CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
-- ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
-- POSSIBILITY OF SUCH DAMAGE.

-- | The implementation of 'Data.BinPack'. This module should not be imported
-- directly; all relevant functions are re-exported by 'Data.BinPack'.

module Data.BinPack.Internals where

import Data.List (sortBy
                 , maximumBy
                 , minimumBy
                 )

import Data.Ord (comparing)

----------------------------------------------
-- Some convenience type and function aliases.

-- | How to pre-process the input.
data OrderPolicy = AsGiven     -- ^ Don't modify item order.
                 | Decreasing  -- ^ Sort from largest to smallest.
                 | Increasing  -- ^ Sort from smallest to largest.
                   deriving (Show, Eq, Ord)

-- | A function that maps an item @b@ to its size @a@. The constraint @('Num'
-- a, 'Ord' a)@ has been omitted from the type, but is required by the exposed
-- functions.
type Measure a b = (b -> a)

-- | Given a 'Measure', an item @b@, a list of capacities @[a]@, and a list of
-- bins @['Bin' b]@, a placement heuristic returns @Just@ an updated lists of
-- capacities and bins if the item could be placed, and @Nothing@ otherwise.
type Placement a b = Measure a b -> b -> [Bin a b] ->
                                       Maybe [Bin a b]

order :: (Ord a) => OrderPolicy -> Order a b
order AsGiven    = const id
order Decreasing = decreasing
order Increasing = increasing

-- | Given a 'Measure' for @b@s and a list of items @[b]@, an 'Order' returns
-- a re-ordered version of the item list.
type Order a b = Measure a b -> [b] -> [b]

-- | Reorder items prior to processing. Items are placed into bins in the order
-- from largest to smallest.
decreasing :: (Ord a) => Order a b
decreasing size xs = sortBy decreasing' xs
    where
      decreasing' x y = if size x >= size y then LT else GT

-- | Reorder items prior to processing. Items are placed into bins in the order
-- from smallest to largest.
increasing :: (Ord a) => Order a b
increasing size xs = sortBy increasing' xs
    where
      increasing' x y = if size x <= size y then LT else GT

-----------------------
-- The Bin abstraction.

-- | A 'Bin' consists of the remaining capacity together with a list of items
--   already placed.
type Bin a b = (a, [b])

-- | Create an empty bin.
emptyBin :: (Num a, Ord a) =>
            a              -- ^ The initial capacity.
            -> Bin a b     -- ^ The empty bin.
emptyBin cap = (cap, [])

-- | Create multiple empty bins with uniform capacity.
emptyBins :: (Num a, Ord a) =>
             a              -- ^ The initial capacity.
          -> Int            -- ^ Number of bins.
          -> [Bin a b]
emptyBins cap = flip replicate $ emptyBin cap

-- | Try placing an item inside a 'Bin'.
tryAddItem :: (Num a, Ord a) =>
              a                -- ^ The item's size.
           -> b                -- ^ The item.
           -> Bin a b          -- ^ The bin.
           -> Maybe (Bin a b)  -- ^ 'Just' the updated bin with the item inside,
                               -- 'Nothing' if it does not fit.
tryAddItem s _ (c, _) | s > c = Nothing
tryAddItem s x (c, xs)        = Just (c - s, x:xs)

-- | Place an item inside a 'Bin'. Fails if there is insufficient capacity.
addItem ::  (Num a, Ord a) =>
              a                -- ^ The item's size.
           -> b                -- ^ The item.
           -> Bin a b          -- ^ The bin.
           -> Bin a b          -- ^ 'Just' the updated bin with the item inside,
                               -- 'Nothing' if it does not fit.
addItem s x b = case tryAddItem s x b of
                  Nothing -> error "Bin overflow."
                  Just b' -> b'

-- | Add a list of items to an existing bin. Fails if there is
--   insufficient capacity.
addItems :: (Ord a, Num a) =>
            Bin a b           -- ^ The bin that should be augmented.
         -> Measure a b       -- ^ A function to determine each item's size.
         -> [b]               -- ^ The items that are to be added.
         ->  Bin a b          -- ^ The resulting bin.
addItems (avail, obj) size xs =
    if req <= avail
       then (avail - req, xs ++ obj)
       else error "Data.BinPack.addItems: insufficient capacity."
    where
      req = sum . map size $ xs

-- | Turn a list of items into a pre-filled bin.
asBin :: (Ord a, Num a) => a -> Measure a b -> [b] -> Bin a b
asBin cap = addItems (emptyBin cap)

makeBin :: (Ord a, Num a) => Measure a b -> a -> b -> Bin a b
makeBin size cap x = asBin cap size [x]

-- | Get the items in a bin.
items :: Bin a b -> [b]
items = snd

-- |  Get the remaining capacity of a bin.
gap :: Bin a b -> a
gap = fst

--------------------------------------------
-- Some convenience list handling functions.

-- Like a map on a specific element.
update :: Int -> (a -> a) -> [a] -> [a]
update i f xs = pre ++ (f (head rst) : tail rst)
    where (pre, rst) = splitAt i xs

-- Insert an item into a bin and reduce the bin's capacity.
insertAt :: (Num a) => Int -> b -> a -> [Bin a b] -> [Bin a b]
insertAt i x s = update i (\ (c, xs) -> (c - s, x:xs))

-- Retrieve the first element from a list that satisfies
-- a given condition.
removeIf :: (a -> Bool) -> [a] -> Maybe (a, [a])
removeIf p lst = case break p lst of
                   (_, [])    -> Nothing
                   (pre, rst) -> Just (head rst, pre ++ tail rst)

---------------------------------
-- Simple bin packing heuristics.

-- generic X fit heuristic
xfit :: (Ord a, Num a) => ([(Int, a)] -> (Int, a)) -> Placement a b
xfit _   _    _    []   = Nothing
xfit choose size item bins =
    let
        s     = size item
        gaps  = filter (\(_, g) -> g >= s) . zip [0..] . map gap
    in
      case gaps bins of
        [] -> Nothing
        pl  -> let (i, _) = choose pl in Just (insertAt i item s bins)

bestfit, firstfit, lastfit, worstfit, almostWorstfit
    :: (Ord a, Num a) => Placement a b
bestfit        = xfit chooseBest
worstfit       = xfit chooseWorst
firstfit       = xfit head
lastfit        = xfit last
almostWorstfit = xfit chooseAlmostWorst

chooseBest, chooseWorst, chooseAlmostWorst :: (Ord a, Ord b) =>
                                              [(a, b)] -> (a, b)
chooseBest  = minimumBy (comparing snd `withTieBreakOn` fst)
chooseWorst = maximumBy (comparing snd `withReverseTieBreakOn` fst)
-- almost worst fit: choose the 2nd to worst-fitting bin
chooseAlmostWorst pl = case filter (/= worst) pl of
                         []   -> worst
                         rest -> chooseWorst rest
    where worst = chooseWorst pl


withReverseTieBreakOn, withTieBreakOn :: (Ord a, Ord b) =>
                                         (a -> a -> Ordering)
                                      -> (a -> b)
                                      -> a -> a
                                      -> Ordering
withTieBreakOn cmp key x y =
    case x `cmp` y of
      EQ   -> (key x) `compare` (key y)
      ord  -> ord

withReverseTieBreakOn cmp key x y =
    case x `cmp` y of
      EQ   -> (key y) `compare` (key x)
      ord  -> ord


--------------------------------------------
-- The actual bin-packing functions.

-- | 'minimize' traverses the list of items and
-- tries to place each in a bin.  If an item doesn't fit anymore, then a new
-- empty bin is created and the item is placed in that bin.
minimize :: (Num a, Ord a) => a -> Measure a b ->
            Placement a b -> [Bin a b] -> [b] -> [Bin a b]
minimize _   _    _   bins []       = bins
minimize cap size fit bins (x : xs) =
    case fit size x bins of
      Just bins' -> minimize cap size fit bins'  xs
      Nothing    -> minimize cap size fit bins'' xs
    where
      -- assumption: size x <= cap. Doesn't make much sense otherwise.
      -- concat at end is ugly, but required for first/last semantics
      bins'' = bins ++ [makeBin size cap x]


-- | Actual binpacking function. Tries to place each item in order.
binpack' :: (Num a, Ord a) =>
            (b -> [Bin a b] -> Maybe [Bin a b])  -- ^ Function to
                                                 -- place on item.
         -> [Bin a b]  -- ^ The bins.
         -> [b]        -- ^ Items yet to be placed.
         -> [b]        -- ^ Items that didn't fit anywhere (accumulator).
         -> ([Bin a b], [b])
binpack' _   bins []       misfits = (bins, misfits)
binpack' fit bins (x : xs) misfits =
    case fit x bins of
      Nothing    -> binpack' fit bins  xs (x : misfits)
      Just bins' -> binpack' fit bins' xs misfits
