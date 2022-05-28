module Data.BinaryTree

import Data.So

%default total
%prefix_record_projections off

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

	||| @prf proof or key ordering
	public export
	data BinaryTree : (k: Type) -> Ord k -> (v: Type) -> Type where
		Empty : BinaryTree k o v
		NonEmpty :
			(data_: TreeData k o v) ->
			{auto prf : ProofOfOrder data_} ->
			BinaryTree k o v
	
	ProofOfOrder' : {o: Ord k} -> BinaryTree k o v -> Trie k v -> BinaryTree k o v -> Type
	ProofOfOrder' Empty _ Empty =
		So (True && True)
	ProofOfOrder' (NonEmpty (MkTreeData (MkTrie left_key  _) _ _)) (MkTrie middle_key _) _ =
		So (left_key < middle_key)
	ProofOfOrder' _ (MkTrie middle_key _) (NonEmpty (MkTreeData (MkTrie right_key  _) _ _)) =
		So (middle_key < right_key)
	ProofOfOrder' (NonEmpty (MkTreeData (MkTrie left_key  _) _ _)) (MkTrie middle_key _) (NonEmpty (MkTreeData (MkTrie right_key  _) _ _)) =
		So (left_key < middle_key && middle_key < right_key)

		-- ) && (Proof_of_cmp (>) right middle_key)

		-- where
		-- 	||| proof of ordering
		-- 	Proof_of_cmp : (cmp: k -> k -> Bool) -> BinaryTree k o v -> k -> Bool
		-- 	Proof_of_cmp _ Empty _ = True
		-- 	Proof_of_cmp cmp (NonEmpty (MkTreeData (MkTrie left_key  _) _ _)) middle_key = cmp left_key middle_key


	export
	ProofOfOrder : {o: Ord k} -> TreeData k o v -> Type
	ProofOfOrder (MkTreeData here left right) = ProofOfOrder' left here right
	
	-- todo: make proof type easier to work with

||| lookup key in tree
||| return value assoc with key
export
lookup : k -> {o: Ord k} -> BinaryTree k o v -> Maybe v
lookup key Empty = Nothing
lookup key (NonEmpty (MkTreeData node left right)) = 
	let nodekey = node.key in
	case compare key nodekey of
		EQ => Just node.value
		LT => lookup key left
		GT => lookup key right


-- lemma_equal_key : (o: Ord k) -> So (here.key == there.key) -> ProofOfOrder' {o} left here right -> ProofOfOrder' {o} left there right

||| insert key-value pair into tree
||| @on_collision  custom key collision resolver
export
insert : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: Ord k} -> BinaryTree k o v -> m (BinaryTree k o v)
insert _ new_kv Empty = pure $ NonEmpty (MkTreeData new_kv Empty Empty)
insert resolvcoll new_kv (NonEmpty {prf} (MkTreeData here left right)) =
	case (compare new_kv.key here.key) of
		EQ => do
			new_value <- resolvcoll here.value new_kv.value
			let newtrie = (MkTrie here.key new_value)
			-- let 0 prf' = lemma_equal_key ?help prf
			-- let ()
			-- let prf_eq = (soToEq prf_left, soToEq prf_right)
			let prf' = ?hole_eq
			pure $ NonEmpty {prf=prf'} (MkTreeData newtrie left right)
		LT => do
			left' <- insert resolvcoll new_kv left
			let proof_left = ?hole_lt
			pure (NonEmpty {prf=proof_left} (MkTreeData here left' right))
		GT => do
			right' <- insert resolvcoll new_kv right
			let proof_right = ?hole_gt
			pure $ NonEmpty {prf=proof_right} (MkTreeData here left right')
	
-- insert _ new_kv tree with (compare new_kv.key tree.key)
-- 	insert resolvcoll new_kv (Leaf leafkv) | EQ = pure $ Leaf (MkTrie leafkv.key !(resolvcoll leafkv.value new_kv.value))
-- 	insert resolvcoll new_kv (Leaf leafkv) | cmp_result = ?h2
-- 	-- insert resolvcoll new_kv (Leaf leafkv) | cmp_result = ?h3
-- 	insert resolvcoll new_kv (Branch leafkv left right) | cmp_result = ?h4
