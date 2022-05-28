module Data.B23Tree


import Data.DPair

import Decidable.Equality

-- TODO: write split

||| 2-3 B-Tree
||| @depth leaf has depth 0, its parent has depth 1, ...
public export
data Tree : (depth: Nat) -> (k : Type) -> (v : k -> Type) -> Ord k -> Type where
  Leaf : (x : k) -> v x -> Tree Z k v o
  Branch2 : Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o
  Branch3 : Tree n k v o -> k -> Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o

branch4 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n k v o -> k -> Tree (S n) k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) k v o -> k -> Tree n k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) k v o -> k -> Tree (S n) k v o -> k -> Tree n k v o -> Tree (S (S n)) k v o
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

export
treeLookup : Ord k => (x : k) -> Tree n k v o -> Maybe (y : k ** v y) -- may also return an erased `So (x == y)`
treeLookup k (Leaf k' v) =
  if k == k' then
    Just (k' ** v)
  else
    Nothing
treeLookup k (Branch2 t1 k' t2) =
  if k <= k' then
    treeLookup k t1
  else
    treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    treeLookup k t1
  else if k <= k2 then
    treeLookup k t2
  else
    treeLookup k t3

treeInsert' : Ord k => (x : k) -> v x -> Tree n k v o -> Either (Tree n k v o) (Tree n k v o, k, Tree n k v o)
treeInsert' k v (Leaf k' v') =
  case compare k k' of
    LT => Right (Leaf k v, k, Leaf k' v')
    EQ => Left (Leaf k v)
    GT => Right (Leaf k' v', k', Leaf k v)
treeInsert' k v (Branch2 t1 k' t2) =
  if k <= k' then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsert' k v t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k v (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k <= k2 then
      case treeInsert' k v t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsert' k v t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

export
treeInsert : Ord k => (x : k) -> v x -> Tree n k v o -> Either (Tree n k v o) (Tree (S n) k v o)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

export
delType : Nat -> (k : Type) -> (v : k -> Type) -> Ord k -> Type
delType Z k v o = ()
delType (S n) k v o = Tree n k v o

export
treeDelete : Ord k => (n : Nat) -> k -> Tree n k v o -> Either (Tree n k v o) (delType n k v o)
treeDelete _ k (Leaf k' v) =
  if k == k' then
    Right ()
  else
    Left (Leaf k' v)
treeDelete (S Z) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete Z k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete (S Z) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k <= k2 then
    case treeDelete Z k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete Z k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete (S (S n)) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete (S (S n)) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k <= k2 then
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete (S n) k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

export
treeToList : Tree n k v o -> List (x : k ** v x)
treeToList = treeToList' (:: [])
  where
    -- explicit quantification to avoid conflation with {n} from treeToList
    treeToList' : {0 n : Nat} -> ((x : k ** v x) -> List (x : k ** v x)) -> Tree n k v o -> List (x : k ** v x)
    treeToList' cont (Leaf k v) = cont (k ** v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1
