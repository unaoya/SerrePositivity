module

public import SerrePositivity.EInfinity.Hammock.WeakUnionGluing

/-!
# 元の単射の像の比較の弱同値性

概要：単射を含む元の可換四角形は、始域の弱同値を元の像の比較へ移す。
方針：像への標準射が同型であることと、同じ元の四角形の自然性を使う。
規約：終域の比較の弱同値性は不要。比較は元の全体の射の制限。
使われ方：proper 図式の列部分集合の像の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory
open SerrePositivity.InfinityCategories

variable {A B A' B' : SSet.{u}} (p : A ⟶ B) (p' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
  (h : p ≫ b = a ≫ p')

include h

lemma mapsToRange : ∀ k, Set.MapsTo (b.app k) ((Subfunctor.range p).obj k)
    ((Subfunctor.range p').obj k) := by
  intro k x hx
  obtain ⟨σ, rfl⟩ := hx
  refine ⟨a.app k σ, ?_⟩
  exact (congrArg (fun η => η.app k σ) h).symm

def rangeMap : (Subfunctor.range p).toFunctor ⟶ (Subfunctor.range p').toFunctor :=
  mapSubcomplex b (mapsToRange p p' a b h)

lemma toRange_rangeMap : Subfunctor.toRange p ≫ rangeMap p p' a b h =
    a ≫ Subfunctor.toRange p' := by
  apply (cancel_mono (Subfunctor.range p').ι).1
  change (Subfunctor.toRange p ≫ mapSubcomplex b (mapsToRange p p' a b h)) ≫
    (Subfunctor.range p').ι = (a ≫ Subfunctor.toRange p') ≫ (Subfunctor.range p').ι
  rw [Category.assoc, mapSubcomplex_ι, ← Category.assoc, Subfunctor.toRange_ι,
    h, Category.assoc, Subfunctor.toRange_ι]

lemma weakRangeMap [Mono p] [Mono p'] (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (rangeMap p p' a b h) := by
  have ep := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange p))
  have ep' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (Subfunctor.toRange p'))
  have hp := ep.isWeakHomotopyEquivalence
  have hp' := ep'.isWeakHomotopyEquivalence
  apply hp.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Subfunctor.toRange p ≫ rangeMap p p' a b h)
  rw [toRange_rangeMap]
  exact ha.comp hp'

end SerrePositivity.EInfinity.Hammock
