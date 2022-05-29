module Data.BinaryTree

import Data.So
import Decidable.Order.Strict

%default total
%prefix_record_projections off

public export
record Trie k v where
	constructor MkTrie
	key  : k
	value: v


mutual
	export
	record TreeData (k: Type) {0 lt: _} (o: StrictOrdered k lt) (v: Type) where
		constructor MkTreeData
		here: Trie k v
		left:   BinaryTree k o v
		right:  BinaryTree k o v

	||| @prf proof or key ordering
	public export
	data BinaryTree : (k: Type) -> {0 lt: _} -> StrictOrdered k lt -> (v: Type) -> Type where
		Empty : BinaryTree k o v
		NonEmpty :
			(data_: TreeData k o v) ->
			{auto prf : is_order_preserved data_} ->
			BinaryTree k o v
	

	||| proof of ordering
	proof_of_cmp : (cmp: k -> k -> Type) -> TreeData k o v -> k -> Type
	proof_of_cmp cmp treedata middle_key = cmp treedata.here.key middle_key


	is_order_oneside : (cmp: k -> k -> Type) -> BinaryTree k o v -> k -> Type
	is_order_oneside cmp Empty _ = ()
	is_order_oneside cmp (NonEmpty side) middle_key = proof_of_cmp cmp side middle_key
	
	export
	is_order_preserved : {lt: _} -> {o: StrictOrdered k lt} -> TreeData k o v -> Type
	is_order_preserved (MkTreeData middle left right) = 
		(is_order_oneside lt left  middle.key,
		is_order_oneside (flip lt) right middle.key)
	
	-- todo: make proof type easier to work with

||| lookup key in tree
||| return value assoc with key
export
lookup : k -> {o: StrictOrdered k lt} -> BinaryTree k o v -> Maybe v
lookup key Empty = Nothing
lookup key (NonEmpty (MkTreeData node left right)) = 
	let nodekey = node.key in
	case order @{o} key nodekey of
		DecEQ _ => Just node.value
		DecLT _ => lookup key left
		DecGT _ => lookup key right


replace_value : v -> (old: Trie k v) -> (new: Trie k v ** old.key = new.key)
replace_value newvalue (MkTrie key value) = ((MkTrie key newvalue) ** Refl)


CheckedTreeData : (k : Type) -> {lt: _} -> StrictOrdered k lt -> Type -> Type
CheckedTreeData k o v = (data_: TreeData k o v ** is_order_preserved data_)

singleton_treedata : Trie k v -> CheckedTreeData k o v
singleton_treedata kv = (MkTreeData kv Empty Empty ** ((), ()))

singleton : Trie k v -> BinaryTree k o v
singleton kv = NonEmpty (singleton_treedata kv).fst


insert_treedata : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: StrictOrdered k lt} -> (old: CheckedTreeData k o v) -> m (new: CheckedTreeData k o v ** (old.fst.here.key = new.fst.here.key))
insert_treedata resolvcoll new_kv (treedata ** prf) = do
	let MkTreeData here left right = treedata
	let (prf_left, prf_right)  = prf
	case (order @{o} new_kv.key here.key) of
		DecEQ _ => do
			new_value <- resolvcoll here.value new_kv.value
			let (newtrie ** eq_key) = replace_value new_value here
			let prf_left'  = replace {p=is_order_oneside       lt  left } eq_key prf_left
			let prf_right' = replace {p=is_order_oneside (flip lt) right} eq_key prf_right
			let prf' = (prf_left', prf_right')
			pure (((MkTreeData newtrie left right) ** prf') ** rewrite eq_key in Refl)
		DecLT prf_inequal => do
			let modified_side : m (new_left: CheckedTreeData k o v ** (lt new_left.fst.here.key here.key)) = do
				case left of
					Empty => pure $ (singleton_treedata new_kv ** prf_inequal)
					(NonEmpty {prf=prf_left''} left) => do
						(left' ** prf_left_eq) <- insert_treedata resolvcoll new_kv (assert_smaller treedata (left ** prf_left''))
						let prf_left_inequal' = replace {p=(\x => lt x here.key)} prf_left_eq prf_left
						pure (left' ** prf_left_inequal')

			((left' ** prf_left') ** prf_left_inequal) <- modified_side
			let prf' = (prf_left_inequal, prf_right)
			pure (((MkTreeData here (NonEmpty {prf=prf_left'} left') right) ** prf') ** Refl)
		DecGT prf_inequal => do
			let modified_side : m (new_right: CheckedTreeData k o v ** (lt here.key new_right.fst.here.key)) = do
				case right of
					Empty => pure $ (singleton_treedata new_kv ** prf_inequal)
					(NonEmpty {prf=prf_right''} right) => do
						(right' ** prf_right_eq) <- insert_treedata resolvcoll new_kv (assert_smaller treedata (right ** prf_right''))
						let prf_right_inequal' = replace {p=(\x => lt here.key x)} prf_right_eq prf_right
						pure (right' ** prf_right_inequal')
			((right' ** prf_right') ** prf_right_inequal) <- modified_side
			let prf' = (prf_left, prf_right_inequal)
			pure (((MkTreeData here left (NonEmpty {prf=prf_right'} right')) ** prf') ** Refl)


||| insert key-value pair into tree
||| @on_collision  custom key collision resolver
export
insert : Monad m => (on_collision: (old: v) -> (new: v) -> m v) -> Trie k v -> {o: StrictOrdered k lt} -> BinaryTree k o v -> m (BinaryTree k o v)
insert _ new_kv Empty = pure $ singleton new_kv
insert resolvcoll new_kv (NonEmpty {prf} data_) = do
	((data_ ** prf') ** _) <- insert_treedata resolvcoll new_kv (data_ ** prf)
	pure $ NonEmpty data_
