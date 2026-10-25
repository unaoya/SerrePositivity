module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryCoefficientPositive
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.LastBoundaryFacesOnly
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.VertexBoundary
/-!
概要：実正規化境界の全列は、全段階で普遍 Hσ 係数の零次数作用に一致する。
方針：正位置・最後・頂点・上方の四場合を、それぞれ既証の面式と零性に接続する。
規約：段階の安定化や有限段比較を仮定しない。
使われ方：実正規化の有限段と普遍 P 係数との帰納比較。
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

lemma dgCoherentBarNormalizationBoundary_coefficients_last {n : ℕ} (s : I _⦋n + 1⦌) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n + 1, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationBoundaryGraded R D F (n + 1)) =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (dgCoherentBarUniversalBoundaryCoefficients R (n + 1) (n + 1)) := by
  have hnative := dgCoherentBarNormalizationBoundary_restrict_last_faces R D F s
  have hcoeff := congrArg (dgCoherentBarBasedFullEndColumnAction R D F s)
    (dgCoherentBarUniversalBoundaryCoefficients_last R n)
  simp only [map_sum (dgCoherentBarBasedFullEndColumnAction R D F s),
    map_zsmul (dgCoherentBarBasedFullEndColumnAction R D F s)] at hcoeff
  refine hnative.trans (Eq.trans ?_ hcoeff.symm)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dgCoherentBarFaceLeftTerm_based R D F s (n + 1) i.succ, smul_smul]
  simp only [Fin.val_succ]
  rw [dgCoherentBarBoundary_last_sign n i.val]
  simp only [Units.smul_def, Int.coe_negOnePow_natCast]
  have hj : (⟨n + 1 - (n + 1), by omega⟩ : Fin (n + 2)) = 0 := by
    apply Fin.ext
    change n + 1 - (n + 1) = 0
    omega
  have hb := dgCoherentBarBasedFullEndColumnAction_basis R D F
    (SimplexCategory.δ i.succ.succ ≫ SimplexCategory.σ (0 : Fin (n + 2)))
    (by
      change (SimplexCategory.σ (0 : Fin (n + 2))).toOrderHom
        ((SimplexCategory.δ i.succ.succ).toOrderHom 0) = 0
      have hd : (SimplexCategory.δ i.succ.succ).toOrderHom 0 = 0 := by
        simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]
      rw [hd]
      simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s
  rw [hb, hj]

lemma dgCoherentBarNormalizationBoundary_coefficients_vertex (s : I _⦋0⦌) (q : ℕ) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨0, s⟩)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (dgCoherentBarUniversalBoundaryCoefficients R 0 q) := by
  rw [dgCoherentBarUniversalBoundaryCoefficients_vertex,
    map_zero (dgCoherentBarBasedFullEndColumnAction R D F s)]
  by_cases hq : q = 0
  · subst q
    exact dgCoherentBarNormalizationBoundary_restrict_vertex_zero R D F s
  · exact dgCoherentBarNormalizationBoundaryGraded_restrict_eq_zero R D F q ⟨0, s⟩
      (by change (0 : ℕ) < q; omega)

lemma dgCoherentBarNormalizationBoundary_coefficients (q : ℕ) (s : dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) =
    dgCoherentBarBasedFullEndColumnAction R D F s.2
      (dgCoherentBarUniversalBoundaryCoefficients R s.1 q) := by
  rcases s with ⟨n, s⟩
  cases n with
  | zero => exact dgCoherentBarNormalizationBoundary_coefficients_vertex R D F s q
  | succ n =>
    by_cases hq : q ≤ n
    · exact dgCoherentBarNormalizationBoundary_coefficients_positive R D F
        (show n = (n - q) + q by omega) s
    · by_cases hlast : q = n + 1
      · subst q
        exact dgCoherentBarNormalizationBoundary_coefficients_last R D F s
      · rw [dgCoherentBarUniversalBoundaryCoefficients_above R (by omega),
          map_zero (dgCoherentBarBasedFullEndColumnAction R D F s)]
        exact dgCoherentBarNormalizationBoundaryGraded_restrict_eq_zero R D F q ⟨n + 1, s⟩
          (by change n + 1 < q; omega)

end SerrePositivity.InfinityCategories
