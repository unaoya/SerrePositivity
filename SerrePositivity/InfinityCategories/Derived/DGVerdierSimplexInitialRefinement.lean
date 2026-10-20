module
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Derived.DGOverVertexInitialDenominator

/-! # 任意次元の実分母 over 単体の閉始点細分

概要：追加閉射が実分母なら、全次数の閉始点細分は同じ実分母部分圏にとどまる。
方針：零頂点は二分母の実合成、正頂点は元の同じ頂点と照合する。
規約：零次元を含み、元の台の細分を保持。使われ方：高次実境界充填の新 apex。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x : D) {n : ℕ}
variable (σ : (dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((SSet.yonedaEquiv (roofPointSliceSimplex _ σ.val)).obj 0))

/-- 追加実閉分母による任意次元の同じ実分母 over 単体の閉始点細分。 -/
def dgVerdierSimplexInitialRefinement
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌ := by
  refine ⟨dgOverSimplexInitialRefinement A D _ σ.val q s, ?_⟩
  intro ν
  have hν : Function.Injective ν.toOrderHom :=
    fun (i j : Fin 1) _ => Subsingleton.elim i j
  by_cases h₀ : ν.toOrderHom 0 = 0
  · rw [dgOverSimplexInitialRefinement_pullback_fixed_zero _ ν σ.val hν h₀ q s]
    exact dgOverVertexInitialRefinement_mem A D P x _ q _ (σ.property ν)
      (dgClosedTargetTransport_mem A D P s _ hs)
  · have hz : ∀ i, ν.toOrderHom i ≠ 0 := by
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
      rw [hi]
      exact h₀
    rw [dgOverSimplexInitialRefinement_pullback_avoids_zero _ ν σ.val hν hz q s]
    exact σ.property ν

/-- 全部分圏内の細分の台は、同じ元の実 over 単体の同じ閉始点細分。 -/
lemma dgVerdierSimplexInitialRefinement_val
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgVerdierSimplexInitialRefinement A D P x σ q s hs).val =
      dgOverSimplexInitialRefinement A D _ σ.val q s := rfl

end SerrePositivity.InfinityCategories
