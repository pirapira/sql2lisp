--Protocol Description-----------------------------------------------------
-- 1. thread one and two waits for randomly long time up to 500 ms.
-- 2. each writes and reads the amount of time they waited for.
-- 3. either one should obtain both amount of time.

--Possible Outputs---------------------------------------------------------
-- There are three patterns

-- pattern 1
-- one: two waited for 115ms.
-- two: could not read.

-- pattern 2
-- one: could not read.
-- two: one waited for 115ms.

-- pattern 3
-- one: two waited for 320ms.
-- two: one waited for 115ms.



import System.Random
import Control.Concurrent


-- Aux Functions

randomDelay :: IO Int
randomDelay = getStdRandom (randomR (1,500)) >>= \wait -> threadDelay wait >> return wait

tryReadMVar :: MVar a -> IO (Maybe a)
tryReadMVar box = tryTakeMVar box >>= \taken ->
                case taken of
                  Nothing -> return ()
                  Just val -> putMVar box val >> return ()
                >> return taken

-- ThreadOne
threadOnePut :: MVar Int -> IO ()
threadOnePut oneWait = randomDelay >>= \wait -> putMVar oneWait wait

threadOneGet :: MVar Int -> IO ()
threadOneGet twoWait = tryReadMVar twoWait >>=
                       \wait ->
                           case wait of
                             Nothing -> putStrLn "one: could not read."
                             Just i  -> putStrLn $ "one: two waited for " ++ show i ++ "ms."

threadOne :: MVar Int -> MVar Int -> MVar () -> IO ()
threadOne = \oneWait twoWait oneFin ->
            threadOnePut oneWait >> threadOneGet twoWait >> putMVar oneFin ()

-- ThreadTwo
threadTwoPut :: MVar Int -> IO ()
threadTwoPut twoWait = randomDelay >>= \wait -> putMVar twoWait wait

threadTwoGet :: MVar Int -> IO ()
threadTwoGet oneWait = tryReadMVar oneWait >>=
                       \wait ->
                           case wait of
                             Nothing -> putStrLn "two: could not read."
                             Just i  -> putStrLn $ "two: one waited for " ++ show i ++ "ms."

threadTwo :: MVar Int -> MVar Int -> MVar () -> IO ()
threadTwo = \oneWait twoWait twoFin ->
            threadTwoPut twoWait >> threadTwoGet oneWait >> putMVar twoFin ()


-- Main
main :: IO ()
main = putStrLn "starting both threads..." >>
       newEmptyMVar >>= \oneWait ->
       newEmptyMVar >>= \twoWait ->
       newEmptyMVar >>= \oneFin ->
       newEmptyMVar >>= \twoFin ->
       forkIO (threadOne oneWait twoWait oneFin) >>
       forkIO (threadTwo oneWait twoWait twoFin) >>
       readMVar oneFin >>
       readMVar twoFin >>
       putStrLn "finish!"
