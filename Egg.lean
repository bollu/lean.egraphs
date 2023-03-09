-- import Mathlib.Data.UnionFind
import Std.Data.RBMap
open Std
namespace UnionFind

structure Node where
  parentix : Nat -- parent index
  size : Nat -- size of subtree
deriving Inhabited, DecidableEq

structure UnionFind where
  data : Array Node
deriving Inhabited, DecidableEq

partial def UnionFind.find (uf: UnionFind) (ix: Nat) : UnionFind × Nat :=
  let node := uf.data[ix]!;
  if  node.parentix == ix then (uf, ix)
  else
    let (uf', parentix') := uf.find node.parentix
    let data := uf'.data.set! ix { node with parentix := parentix' }
    (UnionFind.mk data, parentix')

-- monad transformer for union find state
abbrev UnionFindT m α := StateT UnionFind m α

partial def UnionFind.inSameSet? (uf: UnionFind) (ix1 ix2 : Nat): UnionFind × Bool :=
  let (uf, parent1) := uf.find ix1
  let (uf, parent2) := uf.find ix2
  (uf, parent1 == parent2)

-- returns the index of the union'd representative
def UnionFind.union (uf: UnionFind) (ix1 ix2 : Nat)  : UnionFind × Nat :=
  let (uf, ix1) := uf.find ix1
  let (uf, ix2) := uf.find ix2
  if ix1 == ix2 then (uf, ix1)
  else
    let node1 := uf.data[ix1]!
    let node2 := uf.data[ix2]!
    -- attach smaller subtree to larger subtree.
    -- See that if we have (node1: * <- #) and (node2: @ ), then we should
    -- attach node2 to node1 to get (@ -> * <- #) to get height=2.
    -- If we do the reverse, then we get (@ <- * <- #) which has height=3, which is bad.
    let (smallix, largeix) :=
       if node1.size < node2.size
       then (ix1, ix2) else (ix2, ix1)
    let small := uf.data[smallix]!
    let large := uf.data[largeix]!
    let data := uf.data.set! smallix { small with parentix := largeix }
    let data := data.set! largeix { large with size := small.size + large.size }
    (UnionFind.mk data, largeix)

def UnionFind.push (uf: UnionFind) : UnionFind × Nat :=
  let data := uf.data
  let newix := data.size
  let node := { parentix := newix, size := 1 : Node }
  let data := data.push node
  (UnionFind.mk data, newix)

end UnionFind


namespace DSU

structure HashConser (α : Type) where
  hasher : Hashable α

-- def HashConser.create (n: Size) → HashConser α := sorry
-- def HashConser.hashcons (h: HashConser α) (a: α) : HashConsed α := sorry

-- https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf
structure HashConsed (α : Type) (hr: HashConser α) where
  node : α -- value
  tag : Int -- unique tag of value
  hkey : Int -- hash key of node

end DSU

namespace Egraph
-- index into an equivalence class.
structure ClassIx where
  ix : Nat
deriving DecidableEq, Inhabited


instance OrdClassIx : Ord ClassIx where
  compare cix1 cix2 := compare cix1.ix cix2.ix


structure Term (σ : Type) where
  head : σ
  args :  Array ClassIx

def listOrd [Ord α] : Ord (List α) where
  compare arr1 arr2 :=
    let rec go arr1 arr2 :=
      match arr1, arr2 with
      | [], [] => .eq
      | [], _ => .lt
      | _, [] => .gt
      | a :: as, b :: bs =>
        match compare a b with
        | .lt => .lt
        | .gt => .gt
        | .eq => go as bs
    go arr1 arr2




instance  OrdTerm [Ord σ] : Ord (Term σ) where
  compare t1 t2 :=
    have : Ord (List ClassIx) := listOrd
    lexOrd.compare (t1.head, t1.args.toList)  (t2.head, t2.args.toList)


structure Eclass (σ : Type) where
  nodes : Array (Term σ) -- nodes in the E-class
  -- parentix E-classes (??)
  parents : Array (Term σ × ClassIx)
deriving Inhabited

structure Egraph (σ : Type) [Ord σ] where
  uf : UnionFind.UnionFind  -- keeps track of unions of e-classes
  memo : RBMap (Term σ) ClassIx OrdTerm.compare -- maps term to equiv class ix
  classes : RBMap ClassIx (Eclass σ) OrdClassIx.compare -- maps class ix to the class itself.
  dirty_unions : Array ClassIx


-- monad transformer for union find state
abbrev EGraphT m σ α [Ordσ: Ord σ] := StateT (@Egraph σ Ordσ) (UnionFind.UnionFindT m) α

-- find the root e-class of the e-graph
def Egraph.findRoot [Ord σ] (god: Egraph σ) (ix: ClassIx) : Egraph σ × ClassIx :=
  let (uf, ix) := god.uf.find ix.ix
  ({god with uf := uf }, ClassIx.mk ix )

-- Check if two terms are in the same e-class
def Egraph.inSameClass? [Ord σ] (god: Egraph σ) (t1 t2 : Term σ) : Egraph σ × Bool :=
  let tix1 := god.memo.find! t1
  let tix2 := god.memo.find! t2
  let (uf, eq?) := god.uf.inSameSet? tix1.ix tix2.ix
  ({ god with uf := uf}, eq?)

-- Canonicalize a term by making its children point to the equiv. class representative
def Egraph.canonicalizeTerm [Ord σ] (god: Egraph σ) (t: Term σ) : Egraph σ × Term σ := Id.run do
  let mut args' := #[]
  let mut god := god
  for arg in t.args do
    let (god', arg') := god.findRoot arg
    args' := args'.push arg'
    god := god'
  (god, { t with args := args'})

-- Find the equivalence class this term belongs to, if it is in the Egraph.
def Egraph.findTermClass [Ord σ] (god : Egraph σ) (t : Term σ): Egraph σ × Option ClassIx :=
  let (god, t) := god.canonicalizeTerm t
  let ix? := god.memo.find? t
  (god, ix?)

-- add a parent to an E-class.
-- TODO: why do we need to know the parent term?
def Egraph.addEClassParent [Ord σ] (god : Egraph σ) (nodeix : ClassIx) (parentTerm : Term σ) (parentIx : ClassIx) : Egraph σ :=
  let node := god.classes.find! nodeix
  let node := { node with parents := node.parents.push (parentTerm, parentIx) }
  let classes := god.classes.insert nodeix node
  { god with classes := classes }

-- make a new equivalence class for the term `t`.
-- this does NOT check that `t` already exists, and is hence unsafe.
def Egraph.unsafeFreshEquivClass [Ord σ] (god: Egraph σ) (t: Term σ) : Egraph σ × ClassIx :=
    let (uf, tclassix) := god.uf.push
    let god := { god with uf := uf }
    let tclassix := ClassIx.mk tclassix
    let eclass := { nodes := #[t], parents := #[] : Eclass σ }
    let god := { god with classes := god.classes.insert tclassix eclass }
    (god, tclassix)

def Egraph.push_ [Ord σ] (god: Egraph σ) (t: Term σ) : Egraph σ × ClassIx :=
  match god.findTermClass t with
  | (god, .some ix) => (god, ix)
  | (god, .none) => Id.run do
      let (god, tclassix) := god.unsafeFreshEquivClass t
      let god := t.args.foldl (init := god) (Egraph.addEClassParent (parentTerm := t) (parentIx := tclassix))
      (god , tclassix)



def Egraph.traverse_ [Ord σ] (god: Egraph σ) (f: Egraph σ →  β → Egraph σ): (xs: List β) →  Egraph σ
| [] => god
| x :: xs =>
    let god := f god x
    god.traverse_ f xs

-- TODO: generalize to `Foldable β`
def Egraph.traverse [Ord σ] (god: Egraph σ) (f: Egraph σ →  β → Egraph σ × γ): (xs: List β) →  Egraph σ × List γ
| [] => (god, [])
| x :: xs =>
    let (god, y) := f god x
    let (god, ys) := god.traverse f xs
    (god, y :: ys)

def Egraph.union [Ord σ] (god: Egraph σ) (t1 t2 : ClassIx) : Egraph σ :=
  let (god, t1) := god.findRoot t1
  let (god, t2) := god.findRoot t2
  if t1 == t2 then god
  else
    let (uf, glompix) := god.uf.union t1.ix t2.ix
    let god := { god with uf := uf }
    let glompix := ClassIx.mk glompix -- equiv class index of the glomped equiv class.
    -- An invariant is that the EClass data should always keyed with the root of the union find
    -- in the e.classes datastructure
    let god := { god with dirty_unions := god.dirty_unions.push glompix }
    let (fromix, toix) :=
        if glompix == t1
        then (t2, t1)
        else if glompix == t2
        then (t1, t2)
        else panic s!"expected {t1.ix} or {t2.ix} to be equiv. class represnetative, but neither were representative!"

    let classfrom := god.classes.find! fromix
    let classto := god.classes.find! toix

    -- recanonicalize terms, since we have modified the eclasses by joining them.
    -- note that the canonicalization is shallow (only walks the term), not some kind of
    -- 'deep' canonicalization.
    -- Note that we must run the canonicalization on the full equiv. class, since changing from 'from' to 'to'
    -- might have wrecked pointers in some of the 'to' nodes?
    -- Why is it sufficient to edit only these? Why can't someone else be pointing to our data structure?
    let classto := { classto with nodes := classto.nodes ++ classfrom.nodes : Eclass σ }
    -- delete old nodes
    let god := god.traverse_ (xs := classto.nodes.toList) (fun god node => { god with memo := god.memo.erase node })
    -- canonicalize terms in nodes
    let (god, nodes') := god.traverse (xs := classto.nodes.toList) (fun god node => god.canonicalizeTerm node)
    let classto := { classto with nodes := nodes'.toArray  }
    -- add new nodes
    let god := god.traverse_ (xs := classto.nodes.toList) (fun god node => { god with memo := god.memo.insert node toix })
    -- fixup 'to' class
    let god := { god with classes := god.classes.insert toix classto :  Egraph σ }
    -- Delete 'from' from the set of classes
    let god := { god with classes := god.classes.erase fromix :  Egraph σ }
    god


def Egraph.repair [Ord σ] (god: Egraph σ) (ix: ClassIx): Egraph σ := Id.run do
  let mut god := god
  let cls := god.classes.find! ix
  for (term, termclsix) in cls.parents do
    god := { god with memo := god.memo.erase term }
    let (god', term) := god.canonicalizeTerm term
    god := god'
    let (uf, termclsroot) := (god.uf.find termclsix.ix)
    god :={ god with uf := uf, memo := god.memo.insert term (ClassIx.mk termclsroot) }
  god


partial def Egraph.rebuild [Ord σ] (god: Egraph σ): Egraph σ :=
  if god.dirty_unions.size == 0
  then god
  else Id.run do
    let mut god := god
    let (god', dirty_roots) := god.traverse (xs := god.dirty_unions.toList) (fun god node => god.findRoot node)
    god := god'
    dirty_roots.
    for cls in dirty_roots.size do
      god.repair xls








end Egraph




def hello := "world"
