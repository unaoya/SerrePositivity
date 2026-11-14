module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverInitialRefinementAvoidingFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverVertexInitialDenominator

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D) {n : ℕ}
variable (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))

/-- 追加実閉分母による任意次元の同じ実分母 over 単体の閉始点細分。 -/
def dgVerdierSimplexInitialRefinement
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D _ σ.val q s, ?_⟩
  intro ν
  have hν : Function.Injective ν.toOrderHom :=
    fun (i j : Fin 1) _ => Subsingleton.elim i j
  by_cases h₀ : ν.toOrderHom 0 = 0
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_pullback_fixed_zero _ ν σ.val hν h₀ q s]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexInitialRefinement_mem A D P x _ q _ (σ.property ν)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s _ hs)
  · have hz : ∀ i, ν.toOrderHom i ≠ 0 := by
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
      rw [hi]
      exact h₀
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_pullback_avoids_zero _ ν σ.val hν hz q s]
    exact σ.property ν

/-- 全部分圏内の細分の台は、同じ元の実 over 単体の同じ閉始点細分。 -/
lemma dgVerdierSimplexInitialRefinement_val
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (dgVerdierSimplexInitialRefinement A D P x σ q s hs).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D _ σ.val q s := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
