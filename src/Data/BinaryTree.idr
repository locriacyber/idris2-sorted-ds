module Data.BinaryTree

import Data.So

%default total

public export
record Trie k v where
	constructor MkTrie
	key  : k
	value: v


mutual
	export
	record TreeData (k: Type) (o: Ord k) (v: Type) where
		constructor MkTreeData
		here: Trie k v
		left:   BinaryTree k o v
		right:  BinaryTree k o v

	public export
	data BinaryTree : (k: Type) -> Ord k -> (v: Type) -> Type where
		Empty : BinaryTree k o v
		NonEmpty :
			(data_: TreeData k o v) ->
			{auto 0 prf_order : ProofOfOrder data_} ->
			BinaryTree k o v
	
	ProofOfOrder' : {o: Ord k} -> BinaryTree k o v -> Trie k v -> BinaryTree k o v -> Type
	ProofOfOrder' Empty middle Empty = So True
	ProofOfOrder' (NonEmpty left) middle (NonEmpty right) = So (left.here.key < middle.key && middle.key < right.here.key)
	ProofOfOrder' Empty     middle (NonEmpty right) = So (middle.key    < right.here.key)
	ProofOfOrder' (NonEmpty left) middle Empty      = So (left.here.key < middle.key)

	export
	ProofOfOrder : {o: Ord k} -> TreeData k o v -> Type
	ProofOfOrder dat = ProofOfOrder' dat.left dat.here dat.right


export
lookup : k -> {o: Ord k} -> BinaryTree k o v -> Maybe v
lookup key Empty = Nothing
lookup key (NonEmpty (MkTreeData node left right)) = 
	let nodekey = node.key in
	case compare key nodekey of
		EQ => Just node.value
		LT => lookup key left
		GT => lookup key right

-- export
-- insert : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: Ord k} -> BinaryTree k o v -> m (BinaryTree k o v)
-- insert _ newkv tree with (compare newkv.key tree.trie.key)
-- 	insert resolvcoll newkv (Leaf leafkv) | EQ = pure $ Leaf (MkTrie leafkv.key !(resolvcoll leafkv.value newkv.value))
-- 	insert resolvcoll newkv (Leaf leafkv) | cmp_result = ?h2
-- 	-- insert resolvcoll newkv (Leaf leafkv) | cmp_result = ?h3
-- 	insert resolvcoll newkv (Branch leafkv left right) | cmp_result = ?h4
