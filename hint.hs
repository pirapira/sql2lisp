-- [Haskell-cafe] Information on B-Tree IO implemenations

-- Malcolm Wallace Malcolm.Wallace at cs.york.ac.uk 
-- Mon Nov 7 07:12:41 EST 2005
-- Previous message: [Haskell-cafe] Information on B-Tree IO implemenations
-- Next message: [Haskell-cafe] Information on B-Tree IO implemenations
-- Messages sorted by: [ date ] [ thread ] [ subject ] [ author ]
-- Scott Weeks <weeksie at twelvestone.com> writes:

-- > For a project that I'm working on I need to implement a B-Tree or 
-- > similar disk based data structure for storing large amounts of data. I 
-- > feel like I'm getting it and then I get hung up on disk IO operations 
-- > and trying to figure out how they should fit into the mix.

-- Here is a first-cut specification of a B-Tree:

--     data BTree k d = BTree Int [(k,[d])] [BTree k d]

-- where k = key and d = stored data.  Obviously this does not actually
-- store the B-Tree on file, it just gives a flavour of the intended
-- structure.

-- In order to store the data on file, we need to introduce an indirection
-- corresponding to a file pointer, on each of the child nodes.

--     data BTree k d = BTree Int [(k,[d])] [FilePtr (BTree k d)]

-- Then you need a serialisation routine to write any one node of the
-- tree out and read it back in.  And your tree-traversal routines
-- (lookup, insert, etc) need to be embedded in the IO monad, so they
-- can do the necessary file access.

-- Attached is an implementation of B-Trees (by Colin Runciman), which
-- uses nhc98's Binary class
--     http://haskell.org/nhc98/libs/Binary.html
-- for serialisation.  The type BinHandle corresponds to a file handle,
-- and Bin corresponds to a file pointer.  In this code, in fact we
-- managed to keep the lookup function pure, because the Binary interface
-- allows referentially-transparent I/O (getFAt), which may not be
-- possible in other serialisation libraries.  This facility however
-- depends on an invariant that the B-Tree can only be extended - there
-- is no operation to remove nodes or data.  However the insertion
-- routine clearly must use I/O to extend the tree.  I hope you can see
-- the pattern of how this I/O works.

-- Note also that the B-Tree structure is stored in BPages, separate
-- from the data values hanging off the tree, which are in DBlocks.

-- Hope this helps,
-- Regards,
--     Malcolm
-- -------------- next part --------------
module BTree(BPage, bpLookup, bpLookupPref, newPage, bpEmpty, bpInsert, bpKeys, bpStats) where

import Binary
import qualified Binary

order :: Int
order = 4

-- B-trees are constructed from linked pages, stored in binary form.
-- Invariants for a page (BPage n kds ptrs) are:
-- (1) n == length kds
-- (2) either ptrs == [] (if the page is a leaf)
--     or length ptrs == length kds + 1 
-- (3) the initial DBlock in kds contains a singleton list

data BPage k d = BPage Int [(k, DBlock d)] [Bin (BPage k d)] deriving Binary

data DBlock d = DBlock [d] (Maybe (Bin (DBlock d))) deriving Binary

bpEmpty = BPage 0 [] []

maxBP :: BPage String Int
maxBP = BPage (2*order)
              (map (const (maxKey, maxDB 1)) [1..2*order])
              (map toEnum [1..2*order+1])

maxBPsize :: Int
maxBPsize = sizeOf maxBP

maxKey :: String
maxKey = map (const ' ') [1..maxKlength]

maxKlength :: Int
maxKlength = 20

maxDB :: Int -> DBlock Int
maxDB n = DBlock (map (const 0) [1..n]) (Just (toEnum 0))

maxDBsize :: Int -> Int 
maxDBsize = sizeOf . maxDB

db2list :: Binary d => BinHandle -> DBlock d -> [d]
db2list bh (DBlock ds Nothing) = ds
db2list bh (DBlock ds (Just ptr)) = ds ++ db2list bh (getFAt bh ptr)

dbSizes :: [Int]
dbSizes = [3,5..]

bpLookup :: (Binary k, Binary d, Ord k) => BinHandle -> BPage k d -> k -> [d]
bpLookup bh (BPage _ kdbs []) key =
  look kdbs
  where
  look []           = []
  look ((k,db):kdbs) =
    case compare key k of
    LT -> []
    EQ -> db2list bh db
    GT -> look kdbs
bpLookup bh (BPage _ kdbs ptrs) key =
  look ptrs kdbs
  where
  look [ptr]    []           = bpLookup bh (getFAt bh ptr) key
  look (ptr:ptrs') ((k,db):kdbs) =
    case compare key k of
    LT -> bpLookup bh (getFAt bh ptr) key
    EQ -> db2list bh db
    GT -> look ptrs' kdbs

bpLookupPref :: (Binary k, Binary d, Ord k) =>
                BinHandle -> BPage [k] d -> [k] -> ([d]->[d]->[d]) -> [d]
bpLookupPref bh (BPage _ kdbs []) key join =
  look kdbs
  where
  look []           = []
  look ((k,db):kdbs) =
    case compare key k of
    LT -> if prefix key k then db2list bh db `join` look kdbs else []
    EQ -> db2list bh db `join` look kdbs
    GT -> look kdbs
bpLookupPref bh (BPage _ kdbs ptrs) key join =
  look ptrs kdbs
  where
  look [ptr]    []           = bpLookupPref bh (getFAt bh ptr) key join
  look (ptr:ptrs') ((k,db):kdbs) =
    case compare key k of
    LT -> (if prefix key k then db2list bh db `join` look ptrs' kdbs else []) `join`
          bpLookupPref bh (getFAt bh ptr) key join
    EQ -> db2list bh db `join` look ptrs' kdbs
    GT -> look ptrs' kdbs

prefix :: (Eq a) => [a] -> [a] -> Bool
prefix = pref (==)
  where
  pref eq [] _ = True
  pref eq _ [] = False
  pref eq (x:xs) (y:ys) = eq x y && pref eq xs ys

data PageInsertion k d = WholePage
                       | SplitPage (Bin (BPage k d)) (k, DBlock d) (Bin (BPage k d))

bpInsert :: (Binary k, Binary d, Ord k) =>
            BinHandle -> k -> d -> (Bin (BPage k d)) -> IO (Bin (BPage k d))
bpInsert bh key dat pagePtr =
  do
    bpi <- bpIns bh pagePtr key dat
    ( case bpi of
      WholePage -> return pagePtr
      SplitPage ptr1 kdb ptr2 -> newPage bh (BPage 1 [kdb] [ptr1, ptr2]) )

data PageChange = UnChanged | MoreData | NewKey

bpIns :: (Binary k, Binary d, Ord k) =>
         BinHandle -> (Bin (BPage k d)) -> k -> d -> IO (PageInsertion k d)
bpIns bh pagePtr key dat = 
  do
    (BPage n kdbs ptrs) <- getAt bh pagePtr
    (change,ptrs',kdbs') <- ins ptrs kdbs
    ( case change of
      UnChanged -> return WholePage
      MoreData  -> do
                     putAt bh pagePtr (BPage n kdbs' ptrs')
                     return WholePage
      NewKey    -> if n==2*order then
                     let ptrs1       = take (order+1) ptrs'
                         kdbs1       = take order kdbs'
                         ptrs2       = drop (order+1) ptrs'
                         (kdb:kdbs2) = drop order kdbs'
                     in
                       do
                         putAt bh pagePtr (BPage order kdbs1 ptrs1)
                         newPagePtr <- newPage bh (BPage order kdbs2 ptrs2)
                         return (SplitPage pagePtr kdb newPagePtr)
                    else
                      do
                        putAt bh pagePtr (BPage (n+1) kdbs' ptrs')
                        return WholePage )
  where
  ins [] = insLeaf
  ins ptrs = insFork ptrs
  insLeaf [] =
     return (NewKey, [], [(key,DBlock [dat] Nothing)]) 
  insLeaf kdbs@((k,db):kdbs') =
     case compare key k of
     GT -> do
             (change, _, kdbs'') <- insLeaf kdbs'
             return (change, [], (k,db):kdbs'')
     EQ -> do
             mdb' <- dbIns bh dat db
             ( case mdb' of
               Nothing -> return (UnChanged, [], kdbs)
               Just db' -> return (MoreData, [], (k,db'):kdbs') )
     LT -> return (NewKey, [], (key,DBlock [dat] Nothing):kdbs)
  insFork [ptr]  [] =
     do
       bpi <- bpIns bh ptr key dat
       ( case bpi of
         WholePage -> return (UnChanged, [ptr], [])
         SplitPage ptr1 kdb ptr2 -> return (NewKey, [ptr1, ptr2], [kdb]) ) 
  insFork ptrs@(ptr:ptrs') kdbs@((k,db):kdbs') =
     case compare key k of
     GT -> 
       do
         (change, ptrs'', kdbs'') <- insFork ptrs' kdbs'
         return (change, ptr:ptrs'', (k,db):kdbs'')
     EQ -> 
       do
         mdb' <- dbIns bh dat db
         ( case mdb' of
           Nothing -> return (UnChanged, ptrs, kdbs)
           Just db' -> return (MoreData, ptrs, (k,db'):kdbs') )
     LT -> 
       do
         bpi <- bpIns bh ptr key dat 
         ( case bpi of
           WholePage -> return (UnChanged, ptrs, kdbs)
           SplitPage ptr1 kdb ptr2 ->
	     return (NewKey, ptr1:ptr2:ptrs', kdb:kdbs) )
  insFork [] _ = error "missing page pointer"

-- If result is Nothing, then the initial DBlock is unchanged as
-- insertion has been performed in the chain of blocks it already points
-- to.  Otherwise the new value of the initial DBlock is returned, and
-- it is the *caller's* responsibility to write this back to file.

dbIns :: Binary d =>
           BinHandle -> d -> DBlock d -> IO (Maybe (DBlock d))
dbIns bh dat = dbIns' dbSizes
  where
  dbIns' (n1:n2:_) (DBlock ds Nothing) =
    if length ds < n1 then 
      return (Just (DBlock (ds++[dat]) Nothing))
    else
      do
        ptr <- newDBlock bh n2 (DBlock [dat] Nothing)
        return (Just (DBlock ds (Just ptr)))
  dbIns' (_:ns) (DBlock ds (Just ptr)) =
    do
      db <- getAt bh ptr
      mdb <- dbIns' ns db
      ( case mdb of
        Nothing -> return Nothing
        Just db' -> do
                      putAt bh ptr db'
                      return Nothing )

newDBlock :: (Binary d) => 
             BinHandle -> Int -> (DBlock d) -> IO (Bin (DBlock  d))
newDBlock bh n db =
  do
    end <- endBin bh
    writeDBlock bh end n db
    return end

writeDBlock :: (Binary d) => 
               BinHandle -> Bin (DBlock d) -> Int -> (DBlock d) -> IO ()
writeDBlock bh ptr n db =
  do
    putAt bh ptr db
    ptr' <- tellBin bh
    clearBits bh (maxDBsize n - (fromEnum ptr' - fromEnum ptr))
    return ()

newPage :: (Binary k, Binary d) =>
           BinHandle -> BPage k d -> IO (Bin (BPage k d))
newPage bh db =
  do
    end <- endBin bh
    writePage bh end db
    return end

writePage :: (Binary k, Binary d) =>
             BinHandle -> Bin (BPage k d) -> (BPage k d) -> IO ()
writePage bh ptr bp =
  do
    putAt bh ptr bp
    ptr' <- tellBin bh
    clearBits bh (maxBPsize - (fromEnum ptr' - fromEnum ptr))
    return ()

-- additional routines for statistics gathering

bpKeys :: (Binary k, Binary d) => BinHandle -> BPage k d -> [k]
bpKeys bh (BPage _ kdbs ptrs) =
  map fst kdbs ++ concat (map (bpKeys bh . getFAt bh) ptrs)

bpStats :: (Binary k, Binary d) => BinHandle -> BPage k d -> IO ()
bpStats bh bp =
  let h = bpHisto bh (bpAllKdbs bh bp) [] in
  do
    putStrLn (show (sum h) ++ " keys")
    putStrLn (show h)

bpAllKdbs :: (Binary k, Binary d) => BinHandle -> BPage k d -> [(k, DBlock d)]
bpAllKdbs bh (BPage _ kdbs ptrs) =
  kdbs ++ concat (map (bpAllKdbs bh . getFAt bh) ptrs)

bpHisto :: Binary d => BinHandle -> [(k, DBlock d)] -> [Int] -> [Int]
bpHisto bh [] h = h
bpHisto bh ((k,db):kdbs) h =
  tally (length (db2list bh db)) h (bpHisto bh kdbs)
  where
  tally 1 []     c = c [1]  
  tally 1 (t:ts) c = c (t+1:ts)
  tally n []     c = tally (n `div` 2) [] (c . (0:))
  tally n (t:ts) c = tally (n `div` 2) ts (c . (t:))
Previous message: [Haskell-cafe] Information on B-Tree IO implemenations
Next message: [Haskell-cafe] Information on B-Tree IO implemenations
Messages sorted by: [ date ] [ thread ] [ subject ] [ author ]
More information about the Haskell-Cafe mailing list