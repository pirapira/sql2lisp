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

import System.IO.Unsafe

-- |
-- NVar behaves differently than a normal 'MVar':
-- 
--  * Reading an NVar returns the current value. NVar is unchanged.
-- 
--  * Writing to an empty NVar fills it with a value.
--
--  * Writing to a filled 'NVar' makes NVar filled with
--    a value larger or equal to those already written and the newly written value.

-- TODO: if join operation is there, it does not have to be (Ord)

data NVar a = NVar (MVar (Maybe a))

-- |Build a 'SampleVar' with an initial value.
newNVar :: IO (NVar a)
newNVar = newMVar Nothing >>= \mvar -> return $ NVar mvar

-- |Non-blocking read.
readNVar :: NVar a -> (Maybe a)
readNVar (NVar svar) = unsafePerformIO
    (do
      val <- takeMVar svar
      putMVar svar val
      return val)

-- |Write a value if empty. Otherwise, complain.
writeNVar :: NVar a -> a -> IO ()
writeNVar (NVar svar) v = do
--
-- filled => overwrite
-- not filled => fill, write val
--
   val <- takeMVar svar
   case val of
     Nothing -> putMVar svar (Just v)
     Just _ -> Prelude.error "attempt to write a value to full MVar"
