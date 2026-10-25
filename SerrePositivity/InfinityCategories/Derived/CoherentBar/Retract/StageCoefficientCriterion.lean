module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ProjectorCoefficientCriterion
/-!
概要：有限段階ごとの普遍係数比較が、安定作用素の係数比較を与える。
方針：Mathlib の P の安定化を恒等ラベルで評価し、実安定作用素の列の定義へ代入する。
規約：段階比較は明示仮定。無条件の比較証明は面作用の計算から別に供給する。
使われ方：有限和の比較から退化消去と修正包含へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan
variable (R : Type u) [CommRing R]

lemma dgCoherentBarUniversalStageCoefficients_last_eq (n : ℕ) :
    dgCoherentBarUniversalStageCoefficients R n (n + 1) =
      dgCoherentBarUniversalCoefficients R n := by
  have h := ConcreteCategory.congr_hom
    (P_is_eventually_constant (X := dgCoherentBarLabelModule R Δ[n]) (le_rfl : n ≤ n))
    (ModuleCat.freeMk (R := R) (dgCoherentBarUniversalIdentity n))
  have hs : dgCoherentBarUniversalStageCoefficients R n (n + 1) =
      dgCoherentBarUniversalStageCoefficients R n n := h
  exact hs.trans (dgCoherentBarUniversalCoefficients_eq_stage R n).symm

variable (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

abbrev DGCoherentBarStageCoefficientComparison : Prop :=
  ∀ {n : ℕ} (s : I _⦋n⦌) (q : ℕ),
    HEq ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationStageGraded R D F q))
      (dgCoherentBarBasedColumnAction R D F n s
        ((dgCoherentBarUniversalStageCoefficients R n q).subtypeDomain (fun a => a 0 = 0)))

lemma dgCoherentBarProjectorCoefficientComparison_of_stageCoefficientComparison
    (hstage : DGCoherentBarStageCoefficientComparison R D F) :
    DGCoherentBarProjectorCoefficientComparison R D F := by
  intro n s
  have hcoeff := congrArg (fun z : ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R =>
    dgCoherentBarBasedColumnAction R D F n s (z.subtypeDomain (fun a => a 0 = 0)))
    (dgCoherentBarUniversalStageCoefficients_last_eq R n)
  exact (heq_of_eq (dgCoherentBarNormalizationProjectorGraded_restrict R D F ⟨n, s⟩)).trans
    ((hstage s (n + 1)).trans (heq_of_eq hcoeff))

end SerrePositivity.InfinityCategories
