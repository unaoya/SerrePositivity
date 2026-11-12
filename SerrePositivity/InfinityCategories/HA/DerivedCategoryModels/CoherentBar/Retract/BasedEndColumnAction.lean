module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedUniversalColumn
/-!
概要：同じ単体次数の始点保存係数作用を、実 bar の零次数 Hom に固定する。
方針：既存の次数の線形同型で差の形の次数を零へ移す。
規約：移送前後の全 Hom の異種等号を保持し、線形性を保存する。
使われ方：実正規化段階の有限和を、同じ零次数 Hom で係数比較する。
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

abbrev dgCoherentBarEndDegreeTransport {n : ℕ} (s : I _⦋n⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D)
    (rfl : ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩) = _)
    (rfl : ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) = _)
    (sub_self (n : ℤ))

def dgCoherentBarBasedEndColumn {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) 0 :=
  dgCoherentBarEndDegreeTransport R D F s (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F f hf s)

def dgCoherentBarBasedEndColumnAction {n : ℕ} (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n →₀ R) →ₗ[R]
      GradedHom R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) 0 :=
  (dgCoherentBarEndDegreeTransport R D F s).toLinearMap.comp
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s)

lemma dgCoherentBarBasedEndColumn_heq {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) :
    HEq (dgCoherentBarBasedEndColumn R D F f hf s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F f hf s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

lemma dgCoherentBarBasedEndColumnAction_single {n : ℕ} (s : I _⦋n⦌)
    (a : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n) (r : R) :
    dgCoherentBarBasedEndColumnAction R D F s (Finsupp.single a r) =
      r • dgCoherentBarBasedEndColumn R D F (SSet.stdSimplex.objEquiv a.val) a.property s := by
  change dgCoherentBarEndDegreeTransport R D F s
    (Finsupp.linearCombination R _ (Finsupp.single a r)) = _
  rw [Finsupp.linearCombination_single, map_smul]
  rfl

lemma dgCoherentBarBasedEndColumnAction_heq {n : ℕ} (s : I _⦋n⦌)
    (z : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} n n →₀ R) :
    HEq (dgCoherentBarBasedEndColumnAction R D F s z)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

lemma dgCoherentBarBasedUniversalEndColumn_zero_of_degenerate {n : ℕ}
    (s : I _⦋n⦌) (hs : s ∈ I.degenerate n) :
    dgCoherentBarBasedEndColumnAction R D F s
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R n) = 0 := by
  change dgCoherentBarEndDegreeTransport R D F s
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumnAction R D F n s (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalCoefficients R n)) = 0
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedUniversalColumn_zero_of_degenerate R D F s hs, map_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
