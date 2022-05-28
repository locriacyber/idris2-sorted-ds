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
	proof_of_cmp : (cmp: k -> k -> Bool) -> TreeData k o v -> k -> Bool
	proof_of_cmp cmp treedata middle_key = cmp treedata.here.key middle_key


	is_order_oneside : (cmp: k -> k -> Bool) -> BinaryTree k o v -> k -> Bool
	is_order_oneside cmp Empty _ = True
	is_order_oneside cmp (NonEmpty side) middle_key = proof_of_cmp cmp side middle_key
	
	export
	is_order_preserved : {o: Ord k} -> TreeData k o v -> Bool
	is_order_preserved (MkTreeData middle left right) = 
		(is_order_oneside (<) left  middle.key) &&
		(is_order_oneside (>) right middle.key)
	
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


CheckedTreeData : (k : Type) -> Ord k -> Type -> Type
CheckedTreeData k o v = (data_: TreeData k o v ** So (is_order_preserved data_))

singleton_treedata : Trie k v -> CheckedTreeData k o v
singleton_treedata kv = (MkTreeData kv Empty Empty ** Oh)

singleton : Trie k v -> BinaryTree k o v
singleton kv = NonEmpty (singleton_treedata kv).fst


insert_treedata : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: Ord k} -> (old: CheckedTreeData k o v) -> m (new: CheckedTreeData k o v ** (old.fst.here.key = new.fst.here.key))
insert_treedata resolvcoll new_kv (treedata ** prf) = do
	let MkTreeData here left right = treedata
	case (compare new_kv.key here.key) of
		EQ => do
			new_value <- resolvcoll here.value new_kv.value
			let (newtrie ** eq_key) = replace_value new_value here
			let (so_left, so_right) = soAnd prf
			let eq_left = soToEq so_left
			let eq_right = soToEq so_right
			let eq_key_sym = sym eq_key
			let eq_left'  = trans (cong (is_order_oneside (<) left ) eq_key_sym) eq_left
			let eq_right' = trans (cong (is_order_oneside (>) right) eq_key_sym) eq_right
			let prf' = andSo (eqToSo eq_left', eqToSo eq_right')
			pure (((MkTreeData newtrie left right) ** prf') ** rewrite eq_key in Refl)
		LT => do
			-- let ((left' ** prf_left') ** prf_here') = do
			-- : (new_: CheckedTreeData k o v ** So (is_order_preserved' (NonEmpty {prf=?ho} new_.fst) here.key right))
			let (left' ** prf_left') : CheckedTreeData k o v = do
				case left of
					Empty => singleton_treedata new_kv
					(NonEmpty {prf=prf_left} left) => do ?helpme
					-- Empty => ((singleton_treedata new_kv) ** ?prf_here2)

				-- 	((left' ** prf_left') ** prf_eq) <- insert_treedata resolvcoll new_kv (assert_smaller treedata (left ** prf_left))
				-- 	let prf_here' = do
				-- 		case right of
				-- 			Empty => ?r_e
				-- 			NonEmpty _ => ?r_ne
					
				-- 	-- (left', prf_here')
				-- 	?haha
			-- let eqf = ?eqf0
			-- let eq' = trans (sym eqf) eq

			pure (((MkTreeData here (NonEmpty {prf=prf_left'} left') right) ** ?prf_here') ** Refl)
				
				--  (proof_of_cmp (<) left  middle_key)
			-- pure (((MkTreeData here (NonEmpty {prf=prf_left'} left') right) ** prf_here') ** ?hele)
		GT => do
			let (right' ** prf_right') : CheckedTreeData k o v = ?checked_right

			pure (((MkTreeData here left (NonEmpty {prf=prf_right'} right')) ** ?prf_here2') ** Refl)


||| insert key-value pair into tree
||| @on_collision  custom key collision resolver
export
insert : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: Ord k} -> BinaryTree k o v -> m (BinaryTree k o v)
insert _ new_kv Empty = pure $ singleton new_kv
insert resolvcoll new_kv (NonEmpty {prf} data_) = do
	((data_ ** prf') ** _) <- insert_treedata resolvcoll new_kv (data_ ** prf)
	pure $ NonEmpty data_
