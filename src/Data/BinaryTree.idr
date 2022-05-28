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
			{auto prf : So (is_order_preserved data_)} ->
			BinaryTree k o v
	

	||| proof of ordering
	proof_of_cmp : (cmp: k -> k -> Bool) -> BinaryTree k o v -> k -> Bool
	proof_of_cmp _ Empty _ = True
	proof_of_cmp cmp (NonEmpty (MkTreeData (MkTrie left_key  _) _ _)) middle_key = cmp left_key middle_key


	is_order_preserved' : {o: Ord k} -> BinaryTree k o v -> k -> BinaryTree k o v -> Bool
	is_order_preserved' Empty _ Empty = True
	is_order_preserved' left  middle_key Empty =
		 (proof_of_cmp (<) left  middle_key)
	is_order_preserved' Empty middle_key right =
		 (proof_of_cmp (>) right middle_key)
	is_order_preserved' left  middle_key right =
		((proof_of_cmp (<) left  middle_key) && (proof_of_cmp (>) right middle_key))

	export
	is_order_preserved : {o: Ord k} -> TreeData k o v -> Bool
	is_order_preserved (MkTreeData middle left right) = is_order_preserved' left middle.key right
	
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


replace_value : v -> (old: Trie k v) -> (new: Trie k v ** old.key = new.key)
replace_value newvalue (MkTrie key value) = ((MkTrie key newvalue) ** Refl)


||| insert key-value pair into tree
||| @on_collision  custom key collision resolver
export
insert : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: Ord k} -> BinaryTree k o v -> m (BinaryTree k o v)
insert _ new_kv Empty = pure $ NonEmpty (MkTreeData new_kv Empty Empty)
insert resolvcoll new_kv (NonEmpty {prf} (MkTreeData here left right)) =
	case (compare new_kv.key here.key) of
		EQ => do
			new_value <- resolvcoll here.value new_kv.value
			let (newtrie ** eq_key) = replace_value new_value here
			let eqf = rewrite eq_key in Refl
			let eq  = soToEq prf
			let eq' = trans (sym eqf) eq
			pure $ NonEmpty {prf=eqToSo eq'} (MkTreeData newtrie left right)
		LT => do
			left' <- insert resolvcoll new_kv left
			let proof_left = ?hole_lt
			pure (NonEmpty {prf=proof_left} (MkTreeData here left' right))
		GT => do ?hole_gt
			-- right' <- insert resolvcoll new_kv right
			-- let proof_right = ?hole_gt
			-- pure $ NonEmpty {prf=proof_right} (MkTreeData here left right')
