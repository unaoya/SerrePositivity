module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyExt
/-!
概要：任意の pinched 線形単体から、余錐族規約の全パラメーター係数を回収する。
方針：次数の符号を作用させ、線形削除方程式を余錐族の境界符号へ移す。
規約：任意の実 dg Hom に適用でき、余錐族の存在を先取りしない。
使われ方：工程Bの高次逆構成のパラメーター側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {x y : C}

def dgCoherentBarInverseParameterCoefficient {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) : GradedHom R x y k :=
  k.negOnePow • f.component J k hJ hk

lemma dgCoherentBarInverseParameterCoefficient_involution {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) :
    k.negOnePow • dgCoherentBarInverseParameterCoefficient f J k hJ hk =
      f.component J k hJ hk := by
  simp only [dgCoherentBarInverseParameterCoefficient, smul_smul,
    Int.units_mul_self, one_smul]

lemma dgCoherentBarInverseParameterCoefficient_differential {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (hc : 2 ≤ J.card) :
    _root_.SerrePositivity.DifferentialGraded.differential R (dgCoherentBarInverseParameterCoefficient f.val J k hJ hk) =
      ∑ j : J, ((J.filter (j.val < ·)).card : ℤ).negOnePow •
        dgCoherentBarInverseParameterCoefficient f.val (J.erase j.val) (k + 1)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hc j.val j.property)
          (by have := Finset.card_erase_add_one j.property; omega) := by
  unfold dgCoherentBarInverseParameterCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, f.property J k hJ hk]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
  rw [dite_eq_left hc, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add]
  congr 2
  omega

lemma dgCoherentBarInverseParameterCoefficient_closed_singleton {n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (hc : J.card = 1) :
    _root_.SerrePositivity.DifferentialGraded.differential R (dgCoherentBarInverseParameterCoefficient f.val J k hJ hk) = 0 := by
  unfold dgCoherentBarInverseParameterCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, f.property J k hJ hk]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, hc]

lemma dgCoherentBarInverseParameterCoefficient_pullback_inj {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    dgCoherentBarInverseParameterCoefficient (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f)
      J k hJ hk =
    dgCoherentBarInverseParameterCoefficient f (J.image α) k (hJ.image α)
      (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  unfold dgCoherentBarInverseParameterCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj α f J k hJ hk hi]

lemma dgCoherentBarInverseParameterCoefficient_pullback_not_inj {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty)
    (hk : k = 1 - (J.card : ℤ)) (hi : ¬Set.InjOn α (J : Set (Fin (m + 1)))) :
    dgCoherentBarInverseParameterCoefficient (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f)
      J k hJ hk = 0 := by
  unfold dgCoherentBarInverseParameterCoefficient
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj α f J k hJ hk hi,
    smul_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
