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

-- | Modified-first-fit heuristic support.

module Data.BinPack.Internals.MFF where

import Data.BinPack.Internals

import Data.List (partition)

minimizeMFF :: (Num a, Ord a) =>
               OrderPolicy -> Measure a b -> a -> [b] -> [Bin a b]
minimizeMFF ordPol size cap objects = minimize cap size firstfit gB' rest'
    where
      -- split in categories
      (lA, lC, rest)  = splitMFF cap size objects
      -- pack lA items
      bins           = map (makeBin size cap) lA
      -- pack lC items
      (gB', lC')      = packCs size [] (reverse bins) (increasing size lC)
      -- The rest that has yet to be packed.
      rest'           = order ordPol size $ lC' ++ rest

binpackMFF :: (Ord a, Num a) =>
              OrderPolicy -> Measure a b -> [Bin a b] -> [b] -> ([Bin a b], [b])
binpackMFF ordPol size bins objects = (bins''', rejA ++ rej)
    where
      (cap, _) = head bins -- We use the first bin as the representative bin; the
                           -- assumption is that they are all of the same size.
      (lA, lC, rest) = splitMFF cap size objects
      -- pack the lA items
      (bins', rejA)  = binpack' (firstfit size) bins lA []
      -- pack the lC items
      (bins'', rejC) = packCs size [] (reverse bins') (increasing size lC)
      -- The rest that still might fit.
      rest'          = order ordPol size $ rejC ++ rest
      -- pack the rest
      (bins''', rej)    = binpack' (firstfit size) bins'' rest' []


-- | Split items into the A,B,C,D groups of the MFF algorithm. Only A, C, and
-- | the rest are returned.
splitMFF :: (Num a, Ord a) => a -> Measure a b -> [b] -> ([b], [b], [b])
splitMFF cap size objects = (lA, lC, rest)
    where
      x            = minimum . map size $ objects
      (lA, items') = partition (\ i -> 2 * size i > cap) objects
      (lC, rest)   = partition (\ i -> 5 * size i > cap - x && 3 * size i <= cap) items'

packCs :: (Num a, Ord a) =>
          Measure a b         -- sizing function
       -> [Bin a b]           -- bins that we are done with
       -> [Bin a b]           -- bins yet to do
       -> [b]                 -- remainder of lC, sorted from largest to
                              -- smallest
       -> ([Bin a b], [b])    -- caps, bins, remainder (reversed)
packCs _ bins []    lC  = (bins, lC)
packCs _ bins bins2 []  = (bins ++ bins2, [])
packCs size bins ((c,b):bs) (s1:lC) =
    if null lC || size s1 + size s2 > c
      then packCs size ((c,b):bins) bs (s1:lC) -- there aren't two fitting items
      else -- approximate two largest items that fit
          let lC'             = reverse lC
              Just (x1, lC'') = removeIf (\i -> size i + size s1 <= c) lC'
          in case removeIf (\i -> size i + size x1 <= c) lC'' of
               Just (x2, lC''') ->
                   -- we can ignore s1 as something larger fits, too
                   let
                       bins' = (c - size x1 - size x2, (x2:x1:b)) : bins
                   in
                     packCs size bins' bs $ s1 : reverse lC'''
               Nothing ->
                   -- s1, the smallest item in lC, is the only that fits with x1
                   let
                       bins' = (c - size x1 - size s1, s1:x1:b) : bins
                   in
                     packCs size bins' bs $ reverse lC''
    where
      s2 = head lC

