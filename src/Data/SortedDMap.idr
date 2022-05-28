module Data.SortedDMap

import Data.B23Tree

||| On key collision, which value to keep?
data CollisionResult = New | Old | Both

interface CollisionResolver (k: Type) (v: k -> Type) where
	conflicted : (key: k) -> (old: v key) -> (new: v key) -> CollisionResult

||| context for comparison and exchange
record Context (k: Type) (v: k -> Type) where
	constructor MkContext
	ord: Ord k
	coll: CollisionResolver k v


data SortedDMap : (k: Type) -> (v: k -> Type) -> Context k v -> Type where
  M : {k: Type} -> {v: _} -> (ctx: Context k v) -> (n:Nat) -> Tree n k v ctx.ord -> SortedDMap k v ctx

empty : {ctx: Context k v} -> SortedDMap k v ctx
empty {ctx} = M ctx 0 Leaf