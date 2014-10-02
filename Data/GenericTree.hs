module Data.GenericTree(
    Tree,
    view,
    makeTree,
    empty,
    singleton,
    pair,
    triple,
    appendElement,
    prependElement,
    search,
    insert,
    treeConcat,
    delete,
    Prepender,
    Digit,
    emptyPrepender,
    toPrepender,
    fromPrepender,
    prepending,
    Appender,
    Tigid,
    emptyAppender,
    toAppender,
    fromAppender,
    appending
) where

import qualified Data.List

data Tree a =
    Branch !Int (Tree a) a (Tree a)
    | Empty
    | One a
    | Two a a
    | Three a a a

empty :: Tree a
empty = Empty

singleton :: a -> Tree a
singleton = One

pair :: a -> a -> Tree a
pair = Two

triple :: a -> a -> a -> Tree a
triple = Three

view :: (Tree a -> a -> Tree a -> b) -> b -> Tree a -> b
view f _ (Branch _ l x r) = f l x r
view f g Empty = g
view f _ (One x) = f Empty x Empty
view f _ (Two x y) = f Empty x (One y)
view f _ (Three x y z) = f (One x) y (One z)

count :: Tree a -> Int
count (Branch w _ _ _) = w
count Empty = 0
count (One _) = 1
count (Two _ _) = 2
count (Three _ _ _) = 3

branch :: Tree a -> a -> Tree a -> Tree a
branch l x r = Branch (1 + count l + count r) l x r

rotateRight :: Tree a -> a -> Tree a -> Tree a
rotateRight (Branch _ a m b) n c = branch a m $ branch b n c
rotateRight a x b = branch a x b

rotateLeft :: Tree a -> a -> Tree a -> Tree a
rotateLeft a m (Branch _ b n c) = branch (branch a m b) n c
rotateLeft a m b = branch a m b

maybeRotateLeft :: Tree a -> Tree a
maybeRotateLeft r@(Branch _ a m b) =
    if (count b) > (count a) then
        rotateLeft a m b
    else
        r
maybeRotateLeft r = r

maybeRotateRight :: Tree a -> Tree a
maybeRotateRight r@(Branch _ a m b) =
    if (count a) > (count b) then
        rotateRight a m b
    else
        r
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
makeTree l@(One _) y r@(Two _ _) = Branch 4 l y r
makeTree (One x) y (Three z w v) = Branch 5 (Two x y) z (Two w v)
makeTree (Two x y) z Empty = Three x y z
makeTree l@(Two _ _) z r@(One _) = Branch 4 l z r
makeTree l@(Two _ _) z r@(Two _ _) = Branch 5 l z r
makeTree l@(Two _ _) z r@(Three _ _ _) = Branch 6 l z r
makeTree (Three x y z) w Empty = Branch 4 (Two x y) z (One w)
makeTree (Three x y z) w (One v) = Branch 5 (Two x y) z (Two w v)
makeTree l@(Three _ _ _) w r@(Two _ _) = Branch 6 l w r
makeTree l@(Three _ _ _) w r@(Three _ _ _) = Branch 7 l w r
makeTree Empty x (Branch _ l y r) = makeTree (prependElement x l) y r
makeTree (Branch _ l x r) y Empty = makeTree l x (appendElement r y)
makeTree l x r =
    if lw > (2 * rw) then
        rotateRight (maybeRotateLeft l) x r
    else if rw > (2 * lw) then
        rotateLeft l x (maybeRotateRight r)
    else
        Branch (1 + lw + rw) l x r
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
                GT -> BRanch 4 (Two x a) b (One c)
insert f x (Branch w l a r) =
    case f a x of
        LT -> makeTree l a (insert f x r)
        EQ -> Branch w l x r
        GT -> makeTree (insert f x l) a r


treeConcat :: Tree a -> Tree a -> Tree a
treeConcat Empty y = y
treeConcat x Empty = x
treeConcat (One a) (One b) = Two a b
treeConcat (One a) (Two b c) = Three a b c
treeConcat (One a) (Three b c d) = Branch 4 (One a) b (Two c d)
treeConcat (Two a b) (One c) = Three a b c
treeConcat (Two a b) r@(Two _ _) = Branch 4 (One a) b r
treeConcat l@(Two _ _) (Three c d e) = Branch 5 l c (Two d e)
treeConcat (Three a b c) (One d) = Branch 4 (One a) b (Two c d)
treeConcat (Three a b c) (Two d e) = Branch 5 (Two a b) c (Two d e)
treeConcat (Three a b c) r@(Three _ _ _) = Branch 6 (Two a b) c r
treeConcat l r =
    if (count l > count r) then
        appendLeft (maybeRotateLeft l)
    else
        appendRight (maybeRotateRight r)
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
        EQ -> append l r
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
    TOwt (Tree a) a (Tree a) a

emptyAppender :: Appender a
emptyAppender = []

toAppender :: Tree a -> Appender a
toAppender = loop []
    where
        loop a Empty = a
        loop a (One x) = TEno Empty x : a
        loop a (Two x y) = TOwt Empty x Empty y : a
        loop a (Three x y z) = TOwt Empty x (One y) z : a
        loop a (Branch l x r) = loop (TEno l x : a) r

fromAppender :: Appender a -> Tree a
fromAppender = Data.List.foldl' f Empty
    where
        f r (TEno l x) = makeBranch l x r
        f r (TOwt l x m y) = makeBranch l x (makeBranch m y r)

appending :: Appender a -> a -> Appender a
appending ap x = loop ap Empty x
    where
        loop [] l x = [ TEno l x ]
        loop (TEno l x : p) m y = TOwt l x m y : p
        loop (TOwn l x m y : p) r z = TEno r z : loop p (makeBranch l x m) y


