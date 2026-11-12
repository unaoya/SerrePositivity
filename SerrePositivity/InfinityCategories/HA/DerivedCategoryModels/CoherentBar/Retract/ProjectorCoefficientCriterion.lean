module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedUniversalColumn
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.CorrectedInclusion
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
/-!
概要：実安定作用素と普遍正規化係数の比較から、退化因子消去を導く判定を与える。
方針：実 Hom の普遍係数列の退化消滅へ、列ごとの異種等号と次数の等号を適用する。
規約：比較は明示仮定の補助入口。無条件の比較証明と変形 retract の完成を主張しない。
使われ方：段階作用素と P/PInfty の比較が完成した後、修正包含の既存降下へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev DGCoherentBarProjectorCoefficientComparison : Prop :=
  ∀ {n : ℕ} (s : I _⦋n⦌),
    HEq ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, s⟩)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R n))

lemma dgCoherentBarNormalizationKillsDegenerate_of_projectorCoefficientComparison
    (hcomp : DGCoherentBarProjectorCoefficientComparison R D F) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarNormalizationKillsDegenerate R D F := by
  rintro ⟨⟨n, s⟩, hs⟩
  have h := hcomp s
  have hz := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalColumn_zero_of_degenerate R D F s hs
  have hzero := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
    (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (x' := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (y' := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (k := 0) (l := (n : ℤ) - (n : ℤ)) rfl rfl (by omega)
  exact eq_of_heq (h.trans ((heq_of_eq hz).trans hzero.symm))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
