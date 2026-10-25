module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryFacesOnly
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.FaceRightBasedAction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.UniversalBoundaryCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedFullEndColumnAction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundarySigns
/-!
概要：正位置の実正規化境界は、普遍 Hσ 係数の零次数作用に一致する。
方針：両側の面和を始点保存の自己写像へ移し、次元符号とホモトピー符号の偶奇を照合する。
規約：同じ実境界の全列について無条件の等式を与える。
使われ方：有限正規化段階と普遍係数の比較の帰納段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarNormalizationBoundary_coefficients_positive {n q a : ℕ}
    (hn : n = a + q) (s : I _⦋n + 1⦌) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n + 1, s⟩)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (dgCoherentBarUniversalBoundaryCoefficients R (n + 1) q) := by
  have hnative := dgCoherentBarNormalizationBoundary_restrict_faces R D F s q (by omega)
  have hcoeff := congrArg (dgCoherentBarBasedFullEndColumnAction R D F s)
    (dgCoherentBarUniversalBoundaryCoefficients_positive R hn)
  simp only [map_add (dgCoherentBarBasedFullEndColumnAction R D F s),
    map_sum (dgCoherentBarBasedFullEndColumnAction R D F s),
    map_zsmul (dgCoherentBarBasedFullEndColumnAction R D F s)] at hcoeff
  refine hnative.trans ((congrArg₂ (· + ·) ?_ ?_).trans hcoeff.symm)
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [dgCoherentBarFaceLeftTerm_based R D F s q i, smul_smul,
      dgCoherentBarBoundary_left_sign hn i.val]
    simp only [Units.smul_def, Units.val_mul, Int.coe_negOnePow_natCast, smul_smul]
    have hj : (⟨n + 1 - q, by omega⟩ : Fin (n + 2)) = ⟨a + 1, by omega⟩ := by
      apply Fin.ext
      change n + 1 - q = a + 1
      omega
    have hb := dgCoherentBarBasedFullEndColumnAction_basis R D F
      (SimplexCategory.δ i.succ ≫ SimplexCategory.σ ⟨a + 1, by omega⟩)
      (by
        change (SimplexCategory.σ (⟨a + 1, by omega⟩ : Fin (n + 2))).toOrderHom
          ((SimplexCategory.δ i.succ).toOrderHom 0) = 0
        have hd : (SimplexCategory.δ i.succ).toOrderHom 0 = 0 := by
          simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]
        rw [hd]
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
    rw [hb, hj]
  · apply Finset.sum_congr rfl
    intro i _
    rw [dgCoherentBarFaceRightTerm_based R D F s q (by omega) i, smul_smul,
      dgCoherentBarBoundary_right_sign hn i.val]
    simp only [Units.smul_def, Units.val_mul, Int.coe_negOnePow_natCast, smul_smul]
    have hj : (⟨n - q, by omega⟩ : Fin (n + 1)) = ⟨a, by omega⟩ := by
      apply Fin.ext
      change n - q = a
      omega
    have hb := dgCoherentBarBasedFullEndColumnAction_basis R D F
      (SimplexCategory.σ ⟨a, by omega⟩ ≫ SimplexCategory.δ i.succ)
      (by
        change (SimplexCategory.δ i.succ).toOrderHom
          ((SimplexCategory.σ (⟨a, by omega⟩ : Fin (n + 1))).toOrderHom 0) = 0
        have hs : (SimplexCategory.σ (⟨a, by omega⟩ : Fin (n + 1))).toOrderHom 0 = 0 := by
          simp [SimplexCategory.σ, Fin.predAboveOrderHom]
        rw [hs]
        simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]) s
    rw [hb, hj]

end SerrePositivity.InfinityCategories
