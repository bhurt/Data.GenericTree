{-# LANGUAGE Safe #-}

{-|
Module          : Data.GenericTree
Description     : A generic implementation of a binary tree
Copyright       : (c) Brian Hurt, 2014
License         : MIT
Maintainer      : bhurt42@gmail.com
Stability       : experimental
Portability     : safe

This library implements a generic binary tree- which is not a map or set
or similar, but can be used as the basis for such.  The library is not
designed to be used directly, but instead is designed to be used to
create a new library.

The generic tree is parameterized by only a single type variable, the
payload.  To implement a map, we declare the payload to be a tuple:

>    import Data.GenericTree
>
>    type MyMap k v = Tree (k,v)

This does introduce a slight inefficiency, as we are now paying for the
cost to box the tuple, but this is hard to avoid with generic code.
Also, this cost is offset with greater efficiency in the library (a more
memory-efficient encoding of leaf nodes saves a fair bit of memory), and
there is at least some vague hope that future compilers could specialize
this data structure, eliminating the inefficiency.

The library doesn't use type classes, so for example the type of search
is:

>    search :: (a -> Ordering) -> Tree a -> Maybe a

This allows the user to write code like:

>    find :: Ord k => MyMap k v -> k -> Maybe v
>    find m k =
>        case search ((compare k) . fst) m of
>            | Some (_,v) -> Some v
>            | Nothing -> Nothing

This allows the using code to define it's ordering function, without
having to play games with type classes.

Unfortunately, I can not unbox the tree datum type into the constructor,
as this is not always correct to do.  So, in the above example we pay
the memory overhead penalty of boxing the tuple for each element.  It
would be really nice if the Haskell compiler could optimize that, but
oh well.  Instead, we make up for that by having a more efficient
representation of the leaf nodes, saving us approximately the same amount
of memory.

-}
module Data.GenericTree(

    -- * Tree Type
    Tree,

    -- * Destructuring a Tree
    count,
    isEmpty,
    ith,
    firstElement,
    lastElement,
    view,

    -- * Constructing a Tree
    makeTree,
    empty,
    singleton,
    pair,
    triple,

    -- * Basic Operations
    appendElement,
    prependElement,
    search,
    insert,
    treeConcat,
    delete,
    removeFirst,
    removeLast,

    -- * Advanced tree construction

    -- | This section is based on ideas from the paper
    --   "Constructing Red-Black Trees" (1999) by Ralf Hinze
    --   (<http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.46.1458>).
    --  
    --   The paper shows how we construct balanced trees (in the paper,
    --   red-black trees, but here we do the obvious modification to
    --   work on weight-balanced trees) in O(N), not O(N*log(N)).  Both
    --   prepending (new elements are added to the head of the tree)
    --   and appending (new elements are added to the tail of the tree)
    --   versions are supplied.

    -- ** Fast Prepending
    Prepender,
    Digit,
    emptyPrepender,
    toPrepender,
    fromPrepender,
    prepending,

    -- ** Fast Appending
    Appender,
    Tigid,
    emptyAppender,
    toAppender,
    fromAppender,
    appending,

    -- * List Operations
    toList,
    fromList

) where

import qualified Data.List

{-|  The abstract tree type. -}
data Tree a =
    Branch !Int (Tree a) a (Tree a)
    | Empty
    | One a
    | Two a a
    | Three a a a

{-| Get the number of elements in the tree. -}
count :: Tree a -> Int
count (Branch w _ _ _) = w
count Empty = 0
count (One {}) = 1
count (Two {}) = 2
count (Three {}) = 3

{-| Return true if the tree is empty. -}
isEmpty :: Tree a -> Bool
isEmpty Empty = True
isEmpty _ = False

{-| Return a specific element from the tree.

Returns the ith element (0-based) from the tree, starting from the left-most
(minimum) element.  Useful for array-like behaviors.  Returns Nothing if
i is less than zero or if i is beyond the end of the tree.
-}
ith :: Tree a -> Int -> Maybe a
ith (One x) 0 = Just x
ith (Two x _) 0 = Just x
ith (Two _ y) 1 = Just y
ith (Three x _ _) 0 = Just x
ith (Three _ y _) 1 = Just y
ith (Three _ _ z) 2 = Just z
ith (Branch w l x r) i
    | (i < 0) || (i >= w) = Nothing
    | i < n = ith l i
    | i == n = Just x
    | otherwise = ith r (i - n - 1)
    where
        n = count l
ith _ _ = Nothing

firstElement :: Tree a -> Maybe a
firstElement Empty = Nothing
firstElement (One x) = Just x
firstElement (Two x _) = Just x
firstElement (Three x _ _) = Just x
firstElement (Branch _ l _ _) = firstElement l

lastElement :: Tree a -> Maybe a
lastElement Empty = Nothing
lastElement (One x) = Just x
lastElement (Two _ y) = Just y
lastElement (Three _ _ z) = Just z
lastElement (Branch _ _ _ r) = lastElement r

view :: (Tree a -> a -> Tree a -> b) -> b -> Tree a -> b
view f _ (Branch _ l x r) = f l x r
view f g Empty = g
view f _ (One x) = f Empty x Empty
view f _ (Two x y) = f Empty x (One y)
view f _ (Three x y z) = f (One x) y (One z)

empty :: Tree a
empty = Empty

singleton :: a -> Tree a
singleton = One

pair :: a -> a -> Tree a
pair = Two

triple :: a -> a -> a -> Tree a
triple = Three

branch :: Tree a -> a -> Tree a -> Tree a
branch l x r = Branch (1 + count l + count r) l x r

rotateRight :: Tree a -> a -> Tree a -> Tree a
rotateRight (Branch _ a m b) n c = branch a m $ branch b n c
rotateRight a x b = branch a x b

rotateLeft :: Tree a -> a -> Tree a -> Tree a
rotateLeft a m (Branch _ b n c) = branch (branch a m b) n c
rotateLeft a m b = branch a m b

maybeRotateLeft :: Tree a -> Tree a
maybeRotateLeft r@(Branch _ a m b)
    | count b > count a = rotateLeft a m b
maybeRotateLeft r = r

maybeRotateRight :: Tree a -> Tree a
maybeRotateRight r@(Branch _ a m b)
    | count a > count b = rotateRight a m b
maybeRotateRight r = r

appendElement :: Tree a -> a -> Tree a
appendElement Empty a = One a
appendElement (One a) b = Two a b
appendElement (Two a b) c = Three a b c
appendElement (Three a b c) d = Branch 4 (Two a b) c (One d)
appendElement (Branch _ l a r) b = makeTree l a (appendElement r b)

prependElement :: a -> Tree a -> Tree a
prependElement a Empty = One a
prependElement a (One b) = Two a b
prependElement a (Two b c) = Three a b c
prependElement a (Three b c d) = Branch 4 (Two a b) c (One d)
prependElement a (Branch _ l b r) = makeTree (prependElement a l) b r

makeTree :: Tree a -> a -> Tree a -> Tree a
makeTree Empty x Empty = One x
makeTree (One x) y Empty = Two x y
makeTree (One x) y (One z) = Three x y z
makeTree l@(One {}) y r@(Two {}) = Branch 4 l y r
makeTree (One x) y (Three z w v) = Branch 5 (Two x y) z (Two w v)
makeTree (Two x y) z Empty = Three x y z
makeTree l@(Two {}) z r@(One {}) = Branch 4 l z r
makeTree l@(Two {}) z r@(Two {}) = Branch 5 l z r
makeTree l@(Two {}) z r@(Three {}) = Branch 6 l z r
makeTree (Three x y z) w Empty = Branch 4 (Two x y) z (One w)
makeTree (Three x y z) w (One v) = Branch 5 (Two x y) z (Two w v)
makeTree l@(Three {}) w r@(Two {}) = Branch 6 l w r
makeTree l@(Three {}) w r@(Three {}) = Branch 7 l w r
makeTree Empty x (Branch _ l y r) = makeTree (prependElement x l) y r
makeTree (Branch _ l x r) y Empty = makeTree l x (appendElement r y)
makeTree l x r
    | lw > (2 * rw) = rotateRight (maybeRotateLeft l) x r
    | rw > (2 * lw) = rotateLeft l x (maybeRotateRight r)
    | otherwise = Branch (1 + lw + rw) l x r
    where
        lw = count l
        rw = count r

search :: (a -> Ordering) -> Tree a -> Maybe a
search _ Empty = Nothing
search f (One a) =
    case f a of
        LT -> Nothing
        EQ -> Just a
        GT -> Nothing
search f (Two a b) =
    case f a of
        LT -> Nothing
        EQ -> Just a
        GT ->
            case f b of
                LT -> Nothing
                EQ -> Just b
                GT -> Nothing
search f (Three a b c) =
    case f b of
        LT ->
            case f a of
                LT -> Nothing
                EQ -> Just a
                GT -> Nothing
        EQ -> Just b
        GT ->
            case f c of
                LT -> Nothing
                EQ -> Just c
                GT -> Nothing
search f (Branch _ l a r) =
    case f a of
        LT -> search f l
        EQ -> Just a
        GT -> search f r


insert :: (a -> a -> Ordering) -> a -> Tree a -> Tree a
insert _ x Empty = One x
insert f x (One a) =
    case f a x of
        LT -> Two a x
        EQ -> One x
        GT -> Two x a
insert f x (Two a b) =
    case f a x of
        LT ->
            case f b x of
                LT -> Three a b x
                EQ -> Two a x
                GT -> Three a x b
        EQ -> Two x b
        GT -> Three x a b
insert f x (Three a b c) =
    case f b x of
        LT ->
            case f c x of
                LT -> Branch 4 (Two a b) c (One x)
                EQ -> Three a b x
                GT -> Branch 4 (Two a b) x (One c)
        EQ -> Three a x c
        GT ->
            case f a x of
                LT -> Branch 4 (Two a x) b (One c)
                EQ -> Three x b c
                GT -> Branch 4 (Two x a) b (One c)
insert f x (Branch w l a r) =
    case f a x of
        LT -> makeTree l a (insert f x r)
        EQ -> Branch w l x r
        GT -> makeTree (insert f x l) a r


removeFirst :: Tree a -> Maybe (a, Tree a)
removeFirst Empty = Nothing
removeFirst (One x) = Just (x, Empty)
removeFirst (Two x y) = Just (x, One y)
removeFirst (Three x y z) = Just (x, Two y z)
removeFirst (Branch _ l x r) =
    case removeFirst l of
        Just (y, l') -> Just (y, makeTree l' x r)
        Nothing -> Just (x, r) -- should not happen

removeLast :: Tree a -> Maybe (Tree a, a)
removeLast Empty = Nothing
removeLast (One x) = Just (Empty, x)
removeLast (Two x y) = Just (One x, y)
removeLast (Three x y z) = Just (Two x y, z)
removeLast (Branch _ l x r) =
    case removeLast r of
        Just (r', z) -> Just (makeTree l x r', z)
        Nothing -> Just (l, x) -- should not happen

treeConcat :: Tree a -> Tree a -> Tree a
treeConcat Empty y = y
treeConcat x Empty = x
treeConcat (One a) (One b) = Two a b
treeConcat (One a) (Two b c) = Three a b c
treeConcat (One a) (Three b c d) = Branch 4 (One a) b (Two c d)
treeConcat (Two a b) (One c) = Three a b c
treeConcat (Two a b) r@(Two {}) = Branch 4 (One a) b r
treeConcat l@(Two {}) (Three c d e) = Branch 5 l c (Two d e)
treeConcat (Three a b c) (One d) = Branch 4 (One a) b (Two c d)
treeConcat (Three a b c) (Two d e) = Branch 5 (Two a b) c (Two d e)
treeConcat (Three a b c) r@(Three {}) = Branch 6 (Two a b) c r
treeConcat l r
    | count l > count r = appendLeft (maybeRotateLeft l)
    | otherwise = appendRight (maybeRotateRight r)
    where
        appendLeft (Branch _ ll lx lr) = makeTree ll lx (treeConcat lr r)
        appendLeft _ = error "Unreachable code reached."
        appendRight (Branch _ rl rx rr) = makeTree (treeConcat l rl) rx rr
        appendRight _ = error "Unreachable code reached."

delete :: (a -> Ordering) -> Tree a -> Tree a
delete _ Empty = Empty
delete f t@(One a) =
    case f a of
        LT -> t
        GT -> t
        EQ -> Empty
delete f t@(Two a b) =
    case f a of
        LT -> t
        EQ -> One b
        GT ->
            case f b of
                LT -> t
                EQ -> One a
                GT -> t
delete f t@(Three a b c) =
    case f b of
        LT ->
            case f a of
                LT -> t
                EQ -> Two b c
                GT -> t
        EQ -> Two a c
        GT ->
            case f c of
                LT -> t
                EQ -> Two a b
                GT -> t
delete f (Branch _ l x r) =
    case f x of
        LT -> makeTree (delete f l) x r
        EQ -> treeConcat l r
        GT -> makeTree l x (delete f r)

type Prepender a = [ Digit a ]

data Digit a =
    DOne a (Tree a)
    | DTwo a (Tree a) a (Tree a)

emptyPrepender :: Prepender a
emptyPrepender = []

toPrepender :: Tree a -> Prepender a
toPrepender tree = loop tree []
    where
        loop Empty p = p
        loop (Branch _ l x r) p = loop l (DOne x r : p)
        loop (One a) p = DOne a Empty : p
        loop (Two a b) p = DTwo a Empty b Empty : p
        loop (Three a b c) p = DTwo a Empty b (One c) : p

fromPrepender :: Prepender a -> Tree a
fromPrepender = Data.List.foldl' f Empty
    where
        f l (DOne x r) = makeTree l x r
        f l (DTwo x m y r) = makeTree (makeTree l x m) y r

prepending :: a -> Prepender a -> Prepender a
prepending x = loop x Empty
    where
        loop a l (DOne b r : p) = DTwo a l b r : p
        loop a l (DTwo b m c r : p) = DOne a l : loop b (makeTree m c r) p
        loop a l [] = [ DOne a l ]

type Appender a = [ Tigid a ]

data Tigid a =
    TEno (Tree a) a
    | TOwt (Tree a) a (Tree a) a

emptyAppender :: Appender a
emptyAppender = []

toAppender :: Tree a -> Appender a
toAppender = loop []
    where
        loop a Empty = a
        loop a (One x) = TEno Empty x : a
        loop a (Two x y) = TOwt Empty x Empty y : a
        loop a (Three x y z) = TOwt Empty x (One y) z : a
        loop a (Branch _ l x r) = loop (TEno l x : a) r

fromAppender :: Appender a -> Tree a
fromAppender = Data.List.foldl' f Empty
    where
        f r (TEno l x) = makeTree l x r
        f r (TOwt l x m y) = makeTree l x (makeTree m y r)

appending :: Appender a -> a -> Appender a
appending ap = loop ap Empty
    where
        loop [] l x = [ TEno l x ]
        loop (TEno l x : p) m y = TOwt l x m y : p
        loop (TOwt l x m y : p) r z = TEno r z : loop p (makeTree l x m) y


toList :: Tree a -> [a]
toList = loop []
    where
        loop t Empty = t
        loop t (One a) = a : t
        loop t (Two a b) = a : b : t
        loop t (Three a b c) = a : b : c : t
        loop t (Branch _ l x r) = loop (x : loop t r) l

fromList :: [a] -> Tree a
fromList = fromAppender . Data.List.foldl' appending emptyAppender
