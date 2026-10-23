module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeOverAnodyneRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullRestrictionPullback
public import SerrePositivity.InfinityCategories.F2.CoreTrivialFibration

/-!
概要：指定辺を覆う単射な同値による、元の指定辺保存 Hom の自明 Kan 制限。
方針：各指定辺が制限先で回収できるので頂点条件を反映し、元の相対 Hom の自明 Kan 性を移す。
規約：指定辺を覆う条件を明示し、spine の長辺が覆われるとは仮定しない。
使われ方：高次内ホーンでの元の cocartesian Hom の制限同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺を全て覆う制限は、元の指定辺保存条件を反映する。 -/
lemma markedCocartesianFunctorPredicate_reflect_of_markCover
    {E B : SSet.{u}} (q : E ⟶ B) {a b : Over B} (i : a ⟶ b)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e)
    (v : (relativeFunctorSpace q b.hom) _⦋0⦌)
    (hv : markedCocartesianFunctorPredicate q a.hom V
      ((relativeFunctorOverPre q i).app (Opposite.op ⦋0⦌) v)) :
    markedCocartesianFunctorPredicate q b.hom W v := by
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex q b.hom v
  rw [relativeFunctorOverPre_vertex, markedCocartesianFunctorPredicate_vertex] at hv
  rw [markedCocartesianFunctorPredicate_vertex]
  intro e he
  obtain ⟨d, hd, hde⟩ := hcover e he
  have h := hv d hd
  change IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) (i.left.app (Opposite.op ⦋1⦌) d)) at h
  rwa [hde] at h

/-- 指定辺を覆う同じ単射な同値による、指定辺保存 Hom の制限は自明 Kan。 -/
lemma markedCocartesianFunctorPre_trivialKanFibration_of_markCover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] (he : IsPrecompositionEquivalence i.left)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d ∈ W)
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e) :
    TrivialKanFibration (markedCocartesianFunctorPre q i V W hi) := by
  letI := relativeFunctorOverPre_trivialKanFibration_of_cocartesian q i he
  exact fullRestriction_trivialKanFibration _ _ _ _
    (markedCocartesianFunctorPre_ι q i V W hi)
    (markedCocartesianFunctorPredicate_reflect_of_markCover q i V W hcover)

/-- 同じ指定辺を覆う単射な同値による制限の core も自明 Kan。 -/
lemma core_markedCocartesianFunctorPre_trivialKanFibration_of_markCover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] (he : IsPrecompositionEquivalence i.left)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d ∈ W)
    (hcover : ∀ e ∈ W, ∃ d ∈ V, i.left.app (Opposite.op ⦋1⦌) d = e) :
    TrivialKanFibration (quasicategoryCoreMap (markedCocartesianFunctorPre q i V W hi)) := by
  letI := markedCocartesianFunctorPre_trivialKanFibration_of_markCover q i he V W hi hcover
  infer_instance

end SerrePositivity.InfinityCategories
