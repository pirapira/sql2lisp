-- ghc --make -threaded waitfree.hs

--Protocol Description-----------------------------------------------------
-- 1. thread one and two waits for randomly long time up to 100 ms.
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
import NVar

randomDelay :: IO Int
randomDelay = getStdRandom (randomR (1,100)) >>= \wait -> threadDelay wait >> return wait

threadPut :: NVar Int -> IO ()
threadPut oneWait = randomDelay >>= \wait -> writeNVar oneWait wait

threadGet :: NVar Int -> String -> String -> IO ()
threadGet twoWait myName peerName = readNVar twoWait >>=
                       \wait ->
                           putStrLn $ myName ++ ": " ++ peerName ++ " halted for at least "
                                        ++ show wait ++ "ms."

thread :: NVar Int -> NVar Int -> MVar () -> String -> String -> IO ()
thread = \myWait peerWait oneFin myName peerName ->
            threadPut myWait >> threadGet peerWait myName peerName >> putMVar oneFin ()

-- Main
main :: IO ()
main = putStrLn "starting both threads..." >>
       newNVar 0 >>= \oneWait ->
       newNVar 0 >>= \twoWait ->
       newEmptyMVar >>= \oneFin ->
       newEmptyMVar >>= \twoFin ->
       forkIO (thread oneWait twoWait oneFin "one" "two") >>
       forkIO (thread twoWait oneWait twoFin "two" "one") >>
       takeMVar oneFin >>
       takeMVar twoFin >>
       putStrLn "finish!"
