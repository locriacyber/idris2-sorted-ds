module Data.Treap

import Data.So


export
record Trie k v where
	constructor MkTrie
	key  : k
	value: v

mutual
	export
	data Node : (k: Type) -> Ord k -> (v: Type) -> Type where
		Leaf : Trie k v -> Node k o v
		NotLeaf : {0 o : Ord k} ->
			(middle: Trie k v) -> (left: Node k o v) -> (right: Node k o v) ->
			So (left.trie.key < middle.key) => So (middle.key < right.trie.key) =>
			Node k o v

	export
	(.trie) : Node k _ v -> Trie k v
	(.trie) (Leaf v) = v
	(.trie) (NotLeaf v _ _) = v

export
(.children) : Node k o v -> Maybe (Node k o v, Node k o v)
(.children) (Leaf v) = Nothing
(.children) (NotLeaf v left right) = Just (left, right)

export
data Treap : (k: Type) -> (o: Ord k) -> Type -> Type where
	Empty : Treap k o v
	M : Node k o v -> Treap k o v

export
empty : Treap k o v
empty = Empty

lookup' : k -> {o: Ord k} -> Node k o v -> Maybe v
lookup' key node = case node.children of
	Nothing => Nothing
	Just (left, right) =>
		let nodekey = node.trie.key in
		case compare key nodekey of
			EQ => Just node.trie.value
			LT => lookup' key left
			GT => lookup' key right

export
lookup : k -> {o: Ord k} -> Treap k o v -> Maybe v
lookup key Empty = Nothing
lookup key (M node) = lookup' key node
