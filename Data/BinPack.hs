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

{- |

This module implements a number of common bin-packing heuristics: 'FirstFit',
'LastFit', 'BestFit', 'WorstFit', and 'AlmostWorstFit'.  In addition, the
not-so-common, but analytically superior (in terms of worst-case behavior),
'ModifiedFirstFit' heuristic is also supported.  Further, the (slow)
'SumOfSquaresFit' heuristic, which has been considered in the context of online
bin-packing (Bender et al., 2008), is also supported.

Items can be packed in order of both 'Decreasing' and 'Increasing' size (and,
of course, in unmodified order; see 'AsGiven').


The module supports both the standard (textbook) minimization problem
(/"How many bins do I need to pack all items?"/; see 'minimizeBins' and
'countBins') and the more practical fitting problem
(/"I've got n bins; which items can I take?"/; see 'binpack').

The well-known heuristics are described online in many places and are not
further discussed here. For example, see
<http://www.cs.arizona.edu/icon/oddsends/bpack/bpack.htm> for an overview.  A
description of the 'ModifiedFirstFit' algorithm is harder to come by online,
hence a brief description and references are provided below.

Note that most published analysis assumes items to be sorted in some specific
(mostly 'Decreasing') order. This module does not enforce such assumptions,
rather, any ordering can be combined with any placement heuristic.

If unsure what to pick, then try 'FirstFit' 'Decreasing' or 'BestFit'
'Decreasing' as a default. Use 'WorstFit' 'Decreasing' (in combination with
'binpack') if you want a pre-determined number of bins filled evenly.

A short overview of the 'ModifiedFirstFit' heuristic follows. This overview is
based on the description given in (Yue and Zhang, 1995).

Let @lst@ denote the list of items to be bin-packed, let @x@ denote the size of
the smallest element in @lst@, and let @cap@ denote the capacity of one
bin. @lst@ is split into the four sub-lists, @lA@, @lB@, @lC@, @lD@.

[@lA@] All items strictly larger than @cap\/2@.

[@lB@] All items of size at most @cap\/2@ and strictly larger than @cap\/3@.

[@lC@] All items of size at most @cap\/3@ and strictly larger than @(cap - x)\/5@.

[@lD@] The rest, /i.e./, all items of size at most @(cap - x)\/5@.

Items are placed as follows:

 (1) Create a list of @length lA@ bins. Place each item in @lA@ into its own
     bin (while maintaining relative item order with respect to @lst@). Note:
     relevant published analysis assumes that @lst@ is sorted in order of
     'decreasing' size.

 (2) Take the list of bins created in Step 1 and reverse it.

 (3) Sequentially consider each bin @b@. If the two smallest items in @lC@ do
     NOT fit together into @b@ of if there a less than two items remaining in
     @lC@, then pack nothing into @b@ and move on to the next bin (if any).
     If they do fit together, then find the largest item @x1@ in @lC@ that
     would fit together with the smallest item in @lC@ into @b@. Remove @x1@
     from @lC@. Then find the largest item @x2@, @x2 \\= x1@, in @lC@ that will
     now fit into @b@ /together/ with @x1@. Remove @x1@ from @lC@. Place both
     @x1@ and @x2@ into @b@ and move on to the next item.

 (4) Reverse the list of bins again.

 (5) Use the 'FirstFit' heuristic to place all remaining items, /i.e./, @lB@,
     @lD@, and any remaining items of @lC@.

References:

 * D.S. Johnson and M.R. Garey (1985). A 71/60 Theorem for Bin-Packing.
   /Journal of Complexity/, 1:65-106.

 * M. Yue and L. Zhang (1995). A Simple Proof of the Inequality MFFD(L) <= 71/60
   OPT(L) + 1, L for the MFFD Bin-Packing Algorithm.
   /Acta Mathematicae Applicatae Sinica/, 11(3):318-330.

  * M.A. Bender, B. Bradley, G. Jagannathan, and K. Pillaipakkamnatt (2008).
	Sum-of-Squares Heuristics for Bin Packing and Memory Allocation.
	/ACM Journal of Experimental Algorithmics/, 12:1-19.
-}

module Data.BinPack (
                    -- * Types
                     PlacementPolicy(..)
                    , OrderPolicy (AsGiven, Increasing, Decreasing)
                    , Measure
                    -- * Feature Enumeration
                    -- $features
                    , allOrders
                    , allPlacements
                    , allHeuristics
                    -- * Bin Abstraction
                    -- $bin
                    , Bin
                    , emptyBin
                    , emptyBins
                    , asBin
                    , tryAddItem
                    , addItem
                    , addItems
                    , items
                    , gap
                    -- * Bin-Packing Functions
                    , minimizeBins
                    , countBins
                    , binpack
                    ) where


import Data.BinPack.Internals
import Data.BinPack.Internals.MFF (binpackMFF, minimizeMFF)
import Data.BinPack.Internals.SumOfSquares (sosfit, sosfitAnyFit)

-- | What placement heuristic should be used?
data PlacementPolicy = FirstFit           -- ^ Traverse bin list from 'head' to
                                          -- 'last' and place item in the first
                                          -- bin that has sufficient capacity.
                     | ModifiedFirstFit   -- ^ See above.
                     | LastFit            -- ^ Traverse bin list from 'last' to
                                          -- 'head' and place item in the first
                                          -- bin that has sufficient capacity.
                     | BestFit            -- ^ Place item in the bin with the
                                          -- most capacity.
                     | WorstFit           -- ^ Place item in the bin with the
                                          -- least (but sufficient) capacity.
                     | AlmostWorstFit     -- ^ Choose the 2nd to worst-fitting
                                          -- bin.
                     | SumOfSquaresFit    -- ^ Choose bin such that sum-of-squares
                                          -- heuristic is minimized.
                       deriving (Show, Eq, Ord)

-- $features
-- Lists of all supported heuristics. Useful for benchmarking and testing.

-- | The list of all possible 'PlacementPolicy' choices.
allPlacements :: [PlacementPolicy]
allPlacements = [FirstFit, ModifiedFirstFit, LastFit, BestFit
                , WorstFit, AlmostWorstFit, SumOfSquaresFit]

-- | The list of all possible 'OrderPolicy' choices.
allOrders :: [OrderPolicy]
allOrders = [Decreasing, Increasing, AsGiven]

-- | All supported ordering and placment choices.
allHeuristics :: [(PlacementPolicy, OrderPolicy)]
allHeuristics = [(p, o) | p <- allPlacements, o <- allOrders]

placement :: (Ord a, Num a) => PlacementPolicy -> Placement a b
placement WorstFit         = worstfit
placement BestFit          = bestfit
placement FirstFit         = firstfit
placement LastFit          = lastfit
placement AlmostWorstFit   = almostWorstfit
placement SumOfSquaresFit  = sosfitAnyFit
placement ModifiedFirstFit = error "Not a simple placment policy."


-- $bin
-- Conceptually, a bin is defined by its remaining capacity and the contained
-- items. Currently, it is just a tuple, but this may change in future
-- releases. Clients of this module should rely on the following accessor
-- functions.


{- | Bin-packing without a limit on the number of bins (minimization problem).
Assumption: The maximum item size is at most the size of one bin (this is not
checked).

Examples:

* Pack the words of the sentence /"Bin packing heuristics are a lot of fun!"/
  into bins of size 11, assuming the size of a word is its length.  The
  'Increasing' ordering yields a sub-optimal result that leaves a lot of empty
  space in the bins.

  > minimizeBins FirstFit Increasing length 11 (words "Bin packing heuristics are a lot of fun!")
  > ~~> [(2,["are","Bin","of","a"]),(4,["fun!","lot"]),(4,["packing"]),(1,["heuristics"])]


* Similarly, for 'Int'. Note that we use 'id' as a 'Measure' of the size of an 'Int'.

  > minimizeBins FirstFit Decreasing id 11 [3,7,10,3,1,3,2,4]
  > ~~> [(0,[1,10]),(0,[4,7]),(0,[2,3,3,3])]

-}

minimizeBins :: (Num a, Ord a) =>
                PlacementPolicy -- ^ How to order the items before placement.
             -> OrderPolicy     -- ^ The bin-packing heuristic to use.
             -> Measure a b     -- ^ How to size the items.
             -> a               -- ^ The size of one bin.
             -> [b]             -- ^ The items.
             -> [Bin a b]       -- ^ The result: a list of 'Bins'.
minimizeBins fitPol ordPol size capacity objects =
    case fitPol of
      -- special MFF: more complicated looping; no re-ordered items.
      ModifiedFirstFit -> minimizeMFF ordPol size capacity objects
      -- special SOS: not an any-fit heuristic.
      SumOfSquaresFit  -> minimize capacity size (sosfit capacity) [] items'
      -- everything else can be handled by minimize+placement.
      _                -> minimize capacity size (placement fitPol) [] items'
    where items' = order ordPol size objects



{- |
Wrapper around 'minimizeBins'; useful if only the number of required
bins is of interest. See 'minimizeBins' for a description of the arguments.

Examples:

* How many bins of size 11 characters each do we need to pack the words of the sentence
/"Bin packing heuristics are a lot of fun!"/?

  > countBins FirstFit Increasing length 11 (words "Bin packing heuristics are a lot of fun!")
  > ~~> 4

*  Similarly, for 'Int'. As before, we use 'id' as a 'Measure' for the size of an 'Int'.

  > countBins FirstFit Decreasing id 11 [3,7,10,3,1,3,2,4]
  > ~~> 3

-}
countBins :: (Num a, Ord a) =>
             PlacementPolicy -> OrderPolicy -> Measure a b -> a -> [b] -> Int
countBins fitPol ordPol size cap = length
                                   . minimizeBins fitPol ordPol size cap

{- | Bin-pack a list of items into a list of (possibly non-uniform) bins.  If
 an item cannot be placed, instead of creating a new bin, this version will
 return a list of items that could not be packed (if any).

Example: We have two empty bins, one of size 10 and one of size 12.
         Which words can we fit in there?

> binpack WorstFit Decreasing length [emptyBin 10, emptyBin 12]  (words "Bin packing heuristics are a lot of fun!")
> ~~> ([(0,["Bin","packing"]),(0,["of","heuristics"])],["a","lot","are","fun!"])

Both bins were filled completely, and the words /"are a lot fun!"/ coult not be
packed.  -}

binpack :: (Num a, Ord a)  =>
           PlacementPolicy     -- ^ The bin packing heuristic to use.
        -> OrderPolicy         -- ^ How to order the items before placement.
        -> Measure a b         -- ^ How to size the items.
        -> [Bin a b]           -- ^ The bins; may be non-uniform and pre-filled.
        -> [b]                 -- ^ The items.
        -> ([Bin a b], [b])    -- ^ The result; a list of bins
                               -- and a list of items that could not
                               -- be placed.
binpack fitPol ordPol size bins objects =
    let
        fit       = placement fitPol
        items'    = order ordPol size objects
    in
      case fitPol of
        ModifiedFirstFit -> binpackMFF ordPol size bins items'
        _ -> binpack' (fit size) bins items' []

