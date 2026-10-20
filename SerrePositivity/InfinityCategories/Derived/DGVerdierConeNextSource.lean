module
public import SerrePositivity.InfinityCategories.Derived.TruncatedConeNextBoundary
public import SerrePositivity.InfinityCategories.Derived.DGVerdierConeRefinementData
public import SerrePositivity.InfinityCategories.Derived.DGVerdierBoundaryLastDenominator
public import SerrePositivity.InfinityCategories.Derived.DGOverBoundaryRefinedFaces

/-! # 有限次数錐の次次数境界の共通始対象

概要：次次数の全実境界ホーンの始対象は、元の同じ共通 apex の始対象である。
方針：正番号一面の回収対象と、既存の錐単体の始頂点の等式を使う。
規約：全ての対象を元の dg 圏で厳密に揃える。使われ方：次次数の有限同時原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (P : Set D) (x : D) {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet)} {N : ℕ}
variable (C : TruncatedJoinConeData f N)

/-- 次次数の全実境界ホーンの始対象は、元の同じ apex の始対象。 -/
lemma dgVerdierConeNextBoundary_source (σ : K _⦋N + 1⦌) :
    (HornData.knownData (dgVerdierBoundaryHorn A D P x (truncatedConeNextBoundary C σ))).obj 0 =
      dgVerdierSimplexSource A D P x C.apex := by
  have he : SSet.yonedaEquiv
      (boundary.ι (0 : Fin (N + 2)).succ ≫ truncatedConeNextBoundary C σ) =
        C.simplex N le_rfl (K.δ 0 σ) := by
    rw [truncatedConeNextBoundary_face_positive, Equiv.apply_symm_apply]
  exact (dgOverBoundaryFace_source _
    (truncatedConeNextBoundary C σ ≫ (dgVerdierOver A D P x).ι)
    (0 : Fin (N + 2)).succ (Fin.succ_ne_zero _)).trans
      ((congrArg (dgVerdierSimplexSource A D P x) he).trans
        (dgVerdierConeSimplex_source A D P x C N le_rfl (K.δ 0 σ)))

end SerrePositivity.InfinityCategories
