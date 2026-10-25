module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.StageCoefficientCriterion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedIdentityColumn
/-!
概要：実正規化の零段階と普遍係数の零段階が一致する。
方針：恒等ラベルの単項係数へ自由加群を制限し、恒等単体写像の実単位列を使う。
規約：段階比較の基底だけを無条件に証明する。帰納段の比較は別に行う。
使われ方：DGCoherentBarStageCoefficientComparison の帰納証明の初期段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]

abbrev dgCoherentBarBasedUniversalIdentity (n : ℕ) : DGCoherentBarBasedLabel.{u} n n :=
  ⟨dgCoherentBarUniversalIdentity n, rfl⟩

lemma dgCoherentBarUniversalStageCoefficients_zero_based (n : ℕ) :
    (dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0) =
      Finsupp.single (dgCoherentBarBasedUniversalIdentity n) 1 := by
  classical
  change (Finsupp.single (dgCoherentBarUniversalIdentity n) (1 : R)).subtypeDomain _ = _
  ext a
  simp only [Finsupp.subtypeDomain_apply, Finsupp.single_apply, Subtype.ext_iff]

variable (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarStageCoefficientComparison_zero {n : ℕ} (s : I _⦋n⦌) :
    HEq ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F 0))
      (dgCoherentBarBasedColumnAction R D F n s
        ((dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0))) := by
  have hc := congrArg (dgCoherentBarBasedColumnAction R D F n s)
    (dgCoherentBarUniversalStageCoefficients_zero_based R n)
  have haction : dgCoherentBarBasedColumnAction R D F n s
        ((dgCoherentBarUniversalStageCoefficients R n 0).subtypeDomain (fun a => a 0 = 0)) =
      dgCoherentBarBasedColumn R D F (𝟙 ⦋n⦌) rfl s := by
    exact hc.trans (by
      simp only [dgCoherentBarBasedColumnAction, Finsupp.linearCombination_single, one_smul]
      rfl)
  exact ((heq_of_eq haction).trans (dgCoherentBarBasedIdentityColumn_heq R D F s)).symm

end SerrePositivity.InfinityCategories
