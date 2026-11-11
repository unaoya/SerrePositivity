module
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
概要：有限順序添字の局所余極限から、元の図式に厳密に等しい左 Kan 拡張を得る。
方針：非退化単体の単射性と左 comma の包含で局所添字の有限性を証明する。
規約：元の図式と native な左 Kan 添字を保持する。使われ方：安定性の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
lemma finitePosetNerve_hasDimensionLT (P : Type u) [PartialOrder P] [Fintype P] :
    (nerve P).HasDimensionLT (Fintype.card P) where
  degenerate_eq_top n hn := by
    ext s
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
    intro hs
    have hi := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s).mp hs
    have hc := Fintype.card_le_of_injective s.obj hi
    simp only [Fintype.card_fin] at hc
    omega

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
instance finitePosetNerve_finite (P : Type u) [PartialOrder P] [Finite P] :
    (nerve P).Finite := by
  let : Fintype P := Fintype.ofFinite P
  have := finitePosetNerve_hasDimensionLT P
  apply SSet.finite_of_hasDimensionLT (nerve P) (Fintype.card P)
  intro n hn
  apply Finite.of_injective (f := fun s : (nerve P).nonDegenerate n ↦ s.val.obj)
  intro s t h
  apply Subtype.ext
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Subsingleton.elim
  · intro i
    exact congrFun h i

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
