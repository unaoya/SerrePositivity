module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseParameterSum
/-!
概要：逆構成の標準面から回収した Hom の符号付き和を、実 Hom の微分先の次数で定義する。
方針：隣接する整数次数の算術輸送と合成の線形性を使う。
規約：次数の輸送を明示し、余錐の全標準面を含む。
使われ方：回収した高次 Hom の微分方程式を全 Hom の等式として公開する。
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
  (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)

def dgCoherentBarInverseBoundaryFaceHom {m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (a : Fin (m + 2)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (N) (-((m + 1 : ℕ) : ℤ) + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHom R D F hMC N f a)

def dgCoherentBarInverseBoundary {m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (N) (-((m + 1 : ℕ) : ℤ) + 1) :=
  ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
    dgCoherentBarInverseBoundaryFaceHom R D F hMC N f a

lemma dgCoherentBarInverseBoundary_columns {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (z := N)
      (dgCoherentBarInverseBoundary R D F hMC N f)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-((m + 1 : ℕ) : ℤ) + 1) = -((n + (m + 1) : ℕ) : ℤ) + 1 by omega) =
      ∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceColumn R D F hMC N f s a := by
  unfold dgCoherentBarInverseBoundary
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left]
  congr 1
  have hF := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
    (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHom R D F hMC N f a)
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
    (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
    (z := N)
    rfl rfl rfl rfl (show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega) rfl
    (p := -(n : ℤ)) (q := -((m + 1 : ℕ) : ℤ) + 1)
    (k := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ)) (q' := -(m : ℤ)) (k' := -((n + (m + 1) : ℕ) : ℤ) + 1)
    (dgCoherentBarInverseBoundaryFaceHom R D F hMC N f a)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFaceHom R D F hMC N f a)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) hF HEq.rfl (by omega) (by omega))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
