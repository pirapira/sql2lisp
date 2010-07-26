--Problem--------------------------------------------------------
-- 1. thread one and two waits for randomly long time up to 500 ms.
-- 2. each writes and reads the amount of time they waited for.
-- 3. either one should obtain both amount of time.

--An Implementation--------------------------------------------------------
import System.IO
import Control.Concurrent

-- ThreadOne
threadOneFirst :: MVar [Char] -> IO [Char]
threadOneFirst = \threadOneInput -> takeMVar threadOneInput

threadOneSecond :: MVar [Char] -> [Char] -> IO ()
threadOneSecond threadOneOutput str =
    putMVar threadOneOutput $ str ++ str

threadOne :: MVar[Char] -> MVar[Char] -> IO ()
threadOne inp outp = (threadOneFirst inp) >>= (threadOneSecond outp)

-- ThreadTwo
threadTwoFirst :: MVar[Char] -> IO [Char]
threadTwoFirst = takeMVar

threadTwoSecond :: MVar[Char] -> [Char] -> IO ()
threadTwoSecond threadTwoOutput str = putMVar threadTwoOutput $ reverse str

threadTwo :: MVar[Char] -> MVar[Char] -> IO ()
threadTwo = \input output -> (threadTwoFirst input) >>= (threadTwoSecond output)

-- Main
inputline :: IO [Char]
inputline = hGetLine stdin

feedThreadOne :: MVar[Char] -> [Char] -> IO [Char]
feedThreadOne threadOneInput input =  (putMVar threadOneInput input) >> return input

feedThreadTwo :: MVar[Char] -> [Char] -> IO ()
feedThreadTwo = putMVar

waitThreadOne :: MVar[Char] -> () -> IO [Char]
waitThreadOne = \threadOneOutput _ -> takeMVar threadOneOutput

waitThreadTwo :: MVar[Char] -> [Char] -> IO ([Char], [Char])
waitThreadTwo = \threadTwoOutput one -> (takeMVar threadTwoOutput) >>= \two -> (return (one, two))

output :: ([Char], [Char]) -> IO ()
output = \(x,y) -> putStr $ x ++ y

main :: IO ()
main = newEmptyMVar >>= \threadOneInput ->
       newEmptyMVar >>= \threadOneOutput ->
       newEmptyMVar >>= \threadTwoInput ->
       newEmptyMVar >>= \threadTwoOutput ->
       forkOS (threadOne threadOneInput threadOneOutput) >>
       forkOS (threadTwo threadTwoInput threadTwoOutput) >>
       inputline >>=
       (feedThreadOne threadOneInput) >>=
       (feedThreadTwo threadTwoInput) >>= 
       (waitThreadOne threadOneOutput) >>=
       (waitThreadTwo threadTwoOutput) >>= output

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
