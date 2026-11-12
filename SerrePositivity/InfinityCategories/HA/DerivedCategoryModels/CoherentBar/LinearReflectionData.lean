module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionSigns
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedNaturality
/-!
概要：pinched Hom の線形成分族を、順序反転と濃度符号で反転する。
方針：既存の有限集合反転を成分の添字に用い、削除和を実全単射で移す。
規約：dg Hom の微分は変更せず、全整数次数の成分を保持する。
使われ方：左右の pinched Hom の全単体での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] {x y : C}

def dgCoherentBarLinearReflectionData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n :=
  fun i => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign i.val.1.card •
    f.component (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse i.val.1) i.val.2 (i.property.1.image Fin.rev)
      (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using i.property.2)

lemma dgCoherentBarLinearReflectionData_component {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (dgCoherentBarLinearReflectionData f).component J k hJ hk =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign J.card •
        f.component (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J) k (hJ.image Fin.rev) (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) := rfl

lemma dgCoherentBarLinearReflectionData_involution {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) :
    dgCoherentBarLinearReflectionData (dgCoherentBarLinearReflectionData f) = f := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgCoherentBarLinearReflectionData (dgCoherentBarLinearReflectionData f)).component
    J k hJ hk = f.component J k hJ hk
  simp only [dgCoherentBarLinearReflectionData_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse,
    smul_smul, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign_mul_self, one_smul]

lemma dgCoherentBarLinearReflectionData_rhs {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (dgCoherentBarLinearReflectionData f).rhs J k hk =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSign J.card •
        f.rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J) k (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) := by
  classical
  by_cases hJ : 2 ≤ J.card
  · have hRev : 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).card := by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hJ
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_left hJ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_left hRev, Finset.smul_sum]
    rw [← (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseElementEquiv J).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dgCoherentBarLinearReflectionData_component, smul_smul,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseElementEquiv, Equiv.coe_fn_mk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_erase]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflection_delete_sign J j.val j.property]
  · have hRev : ¬ 2 ≤ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J).card := by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hJ
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_right hJ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_right hRev, smul_zero]

def dgCoherentBarLinearReflectionSimplex {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n := by
  refine ⟨dgCoherentBarLinearReflectionData f.val, ?_⟩
  intro J k hJ hk
  rw [dgCoherentBarLinearReflectionData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul,
    f.equation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse J) k (hJ.image Fin.rev) (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk),
    dgCoherentBarLinearReflectionData_rhs]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
