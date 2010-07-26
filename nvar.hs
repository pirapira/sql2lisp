-- original header below. This file is modified by Yoichi Hirai

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Concurrent.SampleVar
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (concurrency)
--
-- Sample variables
--
-----------------------------------------------------------------------------

module NVar
       (
         -- * Nonblocking Variables
         NVar,         -- :: type _ =
 
         newNVar,      -- :: (a -> a -> a) -> a -> IO (NVar a)
         readNVar,     -- :: NVar a -> IO (a)
         writeNVar,    -- :: NVar a -> a -> IO ()

       ) where

import Prelude

import Control.Concurrent.MVar

-- |
-- NVar behaves differently than a normal 'MVar':
-- 
--  * Reading an NVar returns the current value. NVar is unchanged.
-- 
--  * Writing to an empty NVar fills it with a value.
--
--  * Writing to a filled 'NVar' makes NVar filled with
--    a value larger or equal to those already written and the newly written value.

data (Ord a) => NVar a = NVar (MVar a)

-- |Build a 'SampleVar' with an initial value.
newNVar :: (Ord a) => a -> IO (NVar a)
newNVar v = newMVar v >>= \mvar -> return $ NVar mvar

-- |Non-blocking read.
readNVar :: (Ord a) => NVar a -> IO a
readNVar (NVar svar) = do
--
-- filled => make empty and grab sample
-- not filled => try to grab value, empty when read val.
--
   val <- takeMVar svar
   putMVar svar val
   return val

-- |Write a value into the 'NVar' if the new value is larger.
writeNVar :: (Ord a) => NVar a -> a -> IO ()
writeNVar (NVar svar) v = do
--
-- filled => overwrite
-- not filled => fill, write val
--
   val <- takeMVar svar
   putMVar svar (max val v)
