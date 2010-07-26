--Problem--------------------------------------------------------
-- 1. thread one and two waits for randomly long time up to 500 ms.
-- 2. each writes and reads the amount of time they waited for.
-- 3. either one should obtain both amount of time.

--An Implementation--------------------------------------------------------
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
                             Nothing -> print "one: could not read"
                             Just i  -> print $ "one: two waited for " ++ show i

threadOne :: MVar Int -> MVar Int -> IO ()
threadOne = \oneWait twoWait ->
            threadOnePut oneWait >> threadOneGet twoWait

-- ThreadTwo
threadTwoPut :: MVar Int -> IO ()
threadTwoPut twoWait = randomDelay >>= \wait -> putMVar twoWait wait

threadTwoGet :: MVar Int -> IO ()
threadTwoGet oneWait = tryReadMVar oneWait >>=
                       \wait ->
                           case wait of
                             Nothing -> print "two: could not read"
                             Just i  -> print $ "two: one waited for " ++ show i

threadTwo :: MVar Int -> MVar Int -> IO ()
threadTwo = \oneWait twoWait ->
            threadTwoPut twoWait >> threadTwoGet oneWait


-- Main
main :: IO ()
main = newEmptyMVar >>= \oneWait ->
       newEmptyMVar >>= \twoWait ->
       newEmptyMVar >>= \oneFin ->
       newEmptyMVar >>= \twoFin ->
       forkIO (threadOne oneWait twoWait) >>
       forkIO (threadTwo oneWait twoWait) >>
       readMVar oneFin >>
       readMVar twoFin >>
       return ()

--What is Wrong with This--------------------------------------------------------

-- However, what it really does is 
-- main' = (hGetLine stdin) >>= \input ->
--         (\(x,y) -> putStr $ x ++ y)
--         (((\inp -> inp ++ inp  ) input,
--          ((\input -> reverse input))input)
-- with two parts executed in separate threads.




--First Goal---------------------------------------------------------------------

-- So, instead of writing the actual code, we should be able to write something like:

-- import System.IO

-- main'' = (hGetLine stdin) >>= \input ->
--        makeThread >>= \threadOne ->
--        makeThread >>= \threadTwo ->
--        (\(x,y) -> putStr $ x ++ y)
--        (threadOne (\input -> input ++ input) input,
--         threadTwo (\input -> reverse input) input)

-- The expressions threadOne and threadTwo are working as asynchronous RPC interface.



--Second Goal---------------------------------------------------------------------

-- The first goal is not satisfactory if it is implemented using two MVar's:
---- input MVar: used when RPC is called,
---- output MVar: used when RPC is returned.
-- We call this implementation "naive two MVar"

-- consider the following RPC.
-- (threadOne compute long list)
-- Assume the caller wants to consume the first elements of the computed long list.
-- The naive two MVar approach does not satisfy the caller's need for using
-- the first elements as soon as possible.

-- A clever implementation should satisfy
---- parallel execution of caller and caller
---- partial result passing
-- We want to support not only lists, but also all inductively defined data types.
