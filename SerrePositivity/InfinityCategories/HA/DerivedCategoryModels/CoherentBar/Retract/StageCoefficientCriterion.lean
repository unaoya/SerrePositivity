module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectorCoefficientCriterion
/-!
概要：有限段階ごとの普遍係数比較が、安定作用素の係数比較を与える。
方針：Mathlib の P の安定化を恒等ラベルで評価し、実安定作用素の列の定義へ代入する。
規約：段階比較は明示仮定。無条件の比較証明は面作用の計算から別に供給する。
使われ方：有限和の比較から退化消去と修正包含へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R]

lemma dgCoherentBarUniversalStageCoefficients_last_eq (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n (n + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalCoefficients R n := by
  have h := ConcreteCategory.congr_hom
    (P_is_eventually_constant (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R Δ[n]) (le_rfl : n ≤ n))
    (ModuleCat.freeMk (R := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalIdentity n))
  have hs : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n (n + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n n := h
  exact hs.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalCoefficients_eq_stage R n).symm

variable (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev DGCoherentBarStageCoefficientComparison : Prop :=
  ∀ {n : ℕ} (s : I _⦋n⦌) (q : ℕ),
    HEq ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStageGraded R D F q))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalStageCoefficients R n q).subtypeDomain (fun a => a 0 = 0)))

lemma dgCoherentBarProjectorCoefficientComparison_of_stageCoefficientComparison
    (hstage : DGCoherentBarStageCoefficientComparison R D F) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarProjectorCoefficientComparison R D F := by
  intro n s
  have hcoeff := congrArg (fun z : ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R =>
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s (z.subtypeDomain (fun a => a 0 = 0)))
    (dgCoherentBarUniversalStageCoefficients_last_eq R n)
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded_restrict R D F ⟨n, s⟩)).trans
    ((hstage s (n + 1)).trans (heq_of_eq hcoeff))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
