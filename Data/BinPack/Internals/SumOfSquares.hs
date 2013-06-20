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

-- | Sum-of-squares heuristic support.

module Data.BinPack.Internals.SumOfSquares where

import Data.List ( group
                 , sort
                 , minimumBy)

import Data.Ord (comparing)

import Data.BinPack.Internals

-- | Sum of squares metric. The sum of the square of the counts of each gap
--   size, ignoring empty and completely-packed bins.
sumOfSquares :: (Num a, Ord a) =>
                [Bin a b]  -- ^ The bins.
             -> Int        -- ^ Sum of the squared 'gapCount's.
sumOfSquares = sum
               . map sqrlen                   -- square heuristic
               . group . sort                 -- find bins with equal gaps
               . filter (/= 0)                -- ignore completely packed bins
               . map gap                      -- determine gap
               . filter (not . null . items)  -- ignore empty bins
    where sqrlen xs = length xs * length xs

-- | Pick a bin that minimizes the sum-of-squares heuristic.
sosfit' :: (Ord a, Num a) =>
           Measure a b -> b -> [Bin a b] -> Maybe (Int, [Bin a b])
sosfit' _    _    []   = Nothing
sosfit' size item bins =
    let
        s       = size item
        placed  = map (\(_,bs) -> (sumOfSquares bs, bs))
                  . map (\(i,_) -> (i, insertAt i item s bins))
                  . filter (\(_,b) -> gap b >= s)
                  . zip [0..]
        best    = minimumBy (comparing fst)
    in
      case placed bins of
        [] -> Nothing
        pl  -> Just $ best pl

-- | sosfit, but without the option of adding an additional bin.
sosfitAnyFit :: (Ord a, Num a) => Placement a b
sosfitAnyFit size item = fmap snd . sosfit' size item

-- | sofit, which may add a bin if it lowers the sum-of-squares heuristic.
sosfit :: (Ord a, Num a) => a -> Placement a b
sosfit cap size item bins = fmap testAppend . sosfit' size item $ bins
    where
        app = bins ++ [makeBin size cap item]
        sos = sumOfSquares app
        testAppend (sos', bins') = if sos' <= sos then bins' else app
