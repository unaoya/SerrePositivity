module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedTargetProjection
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LastPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiEquation
/-!
概要：正規化実 bar を最後の対象とする余錐の単体データを構成する。
方針：D の Bianchi データの最後への全成分を、実正規化射影で後合成する。
規約：元の図式を先頭面に保持し、正規化加群の公開型を変更しない。
使われ方：native 余錐の全 HA 方程式と単体的自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

def dgCoherentBarNativeBianchiProjection {n : ℕ} (s : I _⦋n⦌) :
    GradedHom R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) 0 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F s).symm rfl rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetProjection R D F hMC)).val

lemma dgCoherentBarNativeBianchiProjection_heq {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarNativeBianchiProjection R D F hMC s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetProjection R D F hMC) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property

lemma dgCoherentBarNativeBianchiProjection_d {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.DifferentialGraded.differential R (dgCoherentBarNativeBianchiProjection R D F hMC s) =
    compose R (x := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s).obj (Fin.last (n + 1)))
      (z := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarNativeBianchiProjection R D F hMC s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiTheta R D F s) (add_zero 1) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F s
  have hρ := dgCoherentBarNativeBianchiProjection_heq R D F hMC s
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D)
    hx rfl rfl _ _ hρ
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hx rfl rfl rfl rfl _ _ _ _ hρ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiTheta_heq R D F s)
    (add_zero 1) (add_zero 1)
  exact eq_of_heq (hd.trans ((heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTargetProjection_d R D F hMC)).trans hc.symm))

def dgCoherentBarNativeSimplexData {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
    (dgCoherentBarNativeBianchiProjection R D F hMC s)

lemma dgCoherentBarNativeSimplexData_front {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplexData R D F hMC s).pullback Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData := by
  rw [dgCoherentBarNativeSimplexData, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData_front,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_front]

lemma dgCoherentBarNativeSimplexData_last_equation {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.differential R ((dgCoherentBarNativeSimplexData R D F hMC s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) =
    (dgCoherentBarNativeSimplexData R D F hMC s).rhs
      J a (Fin.last (n + 1)) k hJ ha hb hk :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData_equation_last (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
    (dgCoherentBarNativeBianchiProjection R D F hMC s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiTheta R D F s)
    (dgCoherentBarNativeBianchiProjection_d R D F hMC s) J a k hJ ha hb hk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_last_hom_d R D F s J a k hJ ha hb hk)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_rhs R D F s J a k hJ ha hb hk)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
