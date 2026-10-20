module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierBoundaryLastDenominator
public import SerrePositivity.InfinityCategories.Derived.DGOverBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralFiniteFillers

/-! # 任意次元の実分母 over 境界有限族の共通閉細分後の実単体

概要：境界ホーンの有限同時充填を、元の零面を保つ実 over 単体の有限族へ戻す。
方針：最後辺の分母性を自動供給し、一つの追加分母の全実充填を逆回収する。
規約：回収先の新 apex の実分母性は次工程。使われ方：高次錐の実単体の供給。
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
variable {P : Set D} {x source : D} {m : ℕ} {d : Fin m → ℕ}
variable (B : ∀ i, (∂Δ[d i + 1] : SSet.{max u v}) ⟶ (dgVerdierOver A D P x : SSet))
variable (T : DGGeneralLastHornFiniteRefinement P source
  (fun i => dgVerdierBoundaryHorn A D P x (B i)))

/-- 同じ一つの追加分母後に回収する、各次元の実 over 単体。 -/
def dgVerdierBoundaryRefinementOverSimplex (i : Fin m) :
    (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))) _⦋d i + 1⦌ :=
  dgOverBoundaryRefinedSimplex _ (B i ≫ (dgVerdierOver A D P x).ι)
    (T.residuals i).q (T.residuals i).s (T.filler i) (T.filler_fac i)

/-- 各回収単体の元の実単体は、同じ一つの追加分母による指定充填。 -/
lemma dgVerdierBoundaryRefinementOverSimplex_simplex (i : Fin m) :
    roofPointSliceSimplex _ (dgVerdierBoundaryRefinementOverSimplex A D B T i) = T.filler i :=
  dgOverBoundaryRefinedSimplex_simplex _ _ _ _ _ _

/-- 各回収単体の零面は、元の同じ指定境界零面を厳密に保つ。 -/
lemma dgVerdierBoundaryRefinementOverSimplex_face_zero (i : Fin m) :
    (sliceOver _).δ (0 : Fin (d i + 2)) (dgVerdierBoundaryRefinementOverSimplex A D B T i) =
      SSet.yonedaEquiv (boundary.ι (0 : Fin (d i + 2)) ≫ B i ≫ (dgVerdierOver A D P x).ι) :=
  dgOverBoundaryRefinedSimplex_face_zero _ _ _ _ _ _

/-- 各回収単体の全面を、同じ指定充填の各面で照合する。 -/
lemma dgVerdierBoundaryRefinementOverSimplex_face (i : Fin m) (j : Fin (d i + 2)) :
    roofPointSliceSimplex _ ((sliceOver _).δ j (dgVerdierBoundaryRefinementOverSimplex A D B T i)) =
      SSet.stdSimplex.δ j.castSucc ≫ T.filler i :=
  dgOverBoundaryRefinedSimplex_face _ _ _ _ _ _ j

/-- 実分母 over 境界有限族の残差には、一つの追加実分母後の同時原始元が存在する。 -/
theorem dgVerdierBoundaryFiniteRefinement_nonempty [IsDGPretriangulated A D]
    (hsource : ∀ i, (HornData.knownData (dgVerdierBoundaryHorn A D P x (B i))).obj 0 = source) :
    Nonempty (DGGeneralLastHornFiniteRefinement P source
      (fun i => dgVerdierBoundaryHorn A D P x (B i))) :=
  dgGeneralLastHornFiniteRefinement_nonempty P source _ hsource
    (fun i => dgVerdierBoundaryLastClosed_mem A D P x (B i))

/-- 共通始対象の実境界有限族は、一つの追加実分母後に全次元の実 over 単体を持つ。 -/
theorem dgVerdierBoundaryFinite_exists_refinedOverSimplexes [IsDGPretriangulated A D]
    (hsource : ∀ i, (HornData.knownData (dgVerdierBoundaryHorn A D P x (B i))).obj 0 = source) :
    ∃ T : DGGeneralLastHornFiniteRefinement P source
        (fun i => dgVerdierBoundaryHorn A D P x (B i)),
      ∀ i, ∃ U : (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm
          (Simplex.vertex x))) _⦋d i + 1⦌,
        roofPointSliceSimplex _ U = T.filler i ∧
        (sliceOver _).δ (0 : Fin (d i + 2)) U = SSet.yonedaEquiv
          (boundary.ι (0 : Fin (d i + 2)) ≫ B i ≫ (dgVerdierOver A D P x).ι) := by
  obtain ⟨T⟩ := dgVerdierBoundaryFiniteRefinement_nonempty A D B hsource
  exact ⟨T, fun i => ⟨dgVerdierBoundaryRefinementOverSimplex A D B T i,
    dgVerdierBoundaryRefinementOverSimplex_simplex A D B T i,
    dgVerdierBoundaryRefinementOverSimplex_face_zero A D B T i⟩⟩

end SerrePositivity.InfinityCategories
