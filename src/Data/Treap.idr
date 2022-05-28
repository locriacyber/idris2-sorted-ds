module Data.Treap

import Data.BinaryTree
import Data.So

%default total

-- export
-- data Treap : (k: Type) -> (o: Ord k) -> Type -> Type where
-- 	Empty : Treap k o v
-- 	M : BinaryTree k o v -> Treap k o v

-- export
-- empty : Treap k o v
-- empty = Empty

-- export
-- lookup : k -> {o: Ord k} -> Treap k o v -> Maybe v
-- lookup key Empty = Nothing
-- lookup key (M node) = BinaryTree.lookup key node

-- export
-- insert : Trie k v -> {o: Ord k} -> Treap k o v -> Treap k o v
-- insert kvpair Empty = M (Leaf kvpair)
-- insert kvpair (M tree) = M (BinaryTree.insert kvpair tree)
