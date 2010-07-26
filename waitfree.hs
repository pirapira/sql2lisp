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

randomDelay :: IO Int
randomDelay = getStdRandom (randomR (1,500)) >>= \wait -> threadDelay wait >> return wait

tryReadMVar :: MVar a -> IO (Maybe a)
tryReadMVar box = tryTakeMVar box >>= \taken ->
                case taken of
                  Nothing -> return ()
                  Just val -> putMVar box val >> return ()
                >> return taken

threadPut :: MVar Int -> IO ()
threadPut oneWait = randomDelay >>= \wait -> putMVar oneWait wait

threadGet :: MVar Int -> String -> String -> IO ()
threadGet twoWait myName peerName = tryReadMVar twoWait >>=
                       \wait ->
                           case wait of
                             Nothing -> putStrLn $ myName ++ ": could not read."
                             Just i  -> putStrLn $ myName ++ ": " ++ peerName ++ " waited for " ++ show i ++ "ms."

thread :: MVar Int -> MVar Int -> MVar () -> String -> String -> IO ()
thread = \myWait peerWait oneFin myName peerName ->
            threadPut myWait >> threadGet peerWait myName peerName >> putMVar oneFin ()

-- Main
main :: IO ()
main = putStrLn "starting both threads..." >>
       newEmptyMVar >>= \oneWait ->
       newEmptyMVar >>= \twoWait ->
       newEmptyMVar >>= \oneFin ->
       newEmptyMVar >>= \twoFin ->
       forkIO (thread oneWait twoWait oneFin "one" "two") >>
       forkIO (thread twoWait oneWait twoFin "two" "one") >>
       readMVar oneFin >>
       readMVar twoFin >>
       putStrLn "finish!"
