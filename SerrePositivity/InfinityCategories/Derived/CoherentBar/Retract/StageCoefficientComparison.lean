module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BoundaryPostcomposeCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.StageCoefficientBase
/-!
概要：実 bar の全有限正規化段階は、普遍 P 係数の全 Hom の作用と一致する。
方針：零段を単位列で判定し、実境界の後合成比較と Mathlib の P_succ の係数再帰で帰納する。
規約：有限段比較を明示仮定に取らず、全段階・全列について証明する。
使われ方：安定作用素の係数比較と退化消去を経由した無条件の変形 retract。
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

lemma dgCoherentBarNormalizationStageGraded_restrict_succ_formula {n : ℕ}
    (s : I _⦋n⦌) (q : ℕ) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationStageGraded R D F (q + 1)) =
    Add.add (α := GradedHom R
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
        (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q))
      (compose R
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarNormalizationBoundaryGraded R D F q)
        ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
          (dgCoherentBarGraded R D F)).f 0
          (dgCoherentBarNormalizationStageGraded R D F q)) rfl) := by
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
    (dgCoherentBarGraded R D F)).f 0
      (compose R
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        ((unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val +
          dgCoherentBarNormalizationBoundaryGraded R D F q)
        (dgCoherentBarNormalizationStageGraded R D F q) rfl) = _
  rw [moduleHomRestriction_compose R D, compose_add_left, unit_compose]
  rfl

lemma dgCoherentBarNormalizationStageGraded_coefficients {n : ℕ} (s : I _⦋n⦌) (q : ℕ) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationStageGraded R D F q) =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (dgCoherentBarUniversalStageCoefficients R n q) := by
  induction q with
  | zero =>
    have hfull := dgCoherentBarBasedEndColumnAction_heq R D F s
      ((dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0))
    exact eq_of_heq ((dgCoherentBarStageCoefficientComparison_zero R D F s).trans hfull.symm)
  | succ q ih =>
    have hpost := dgCoherentBarNormalizationBoundary_postcompose_coefficients R D F s q
      (dgCoherentBarUniversalStageCoefficients R n q) (fun a ha =>
        dgCoherentBarUniversalStageCoefficients_based R n q a (Finsupp.mem_support_iff.mp ha))
    have hcomp := congrArg (fun z => compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationBoundaryGraded R D F q) z (show (0 : ℤ) + 0 = 0 from rfl)) ih
    have hrec := (dgCoherentBarNormalizationStageGraded_restrict_succ_formula R D F s q).trans
      (congrArg₂ (Add.add (α := GradedHom R
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) 0)) ih (hcomp.trans hpost))
    exact hrec.trans ((map_add (dgCoherentBarBasedFullEndColumnAction R D F s) _ _).symm.trans
      (congrArg (dgCoherentBarBasedFullEndColumnAction R D F s)
        (dgCoherentBarUniversalStageCoefficients_succ R n q)).symm)

lemma dgCoherentBarStageCoefficientComparison : DGCoherentBarStageCoefficientComparison R D F := by
  intro n s q
  exact (heq_of_eq (dgCoherentBarNormalizationStageGraded_coefficients R D F s q)).trans
    (dgCoherentBarBasedEndColumnAction_heq R D F s
      ((dgCoherentBarUniversalStageCoefficients R n q).subtypeDomain (fun a => a 0 = 0)))

end SerrePositivity.InfinityCategories
