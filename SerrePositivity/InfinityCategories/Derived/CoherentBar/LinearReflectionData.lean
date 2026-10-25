module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionSigns
public import SerrePositivity.InfinityCategories.DGNerve.PinchedNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DGNerveOppositeIndex
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C] {x y : C}

def dgCoherentBarLinearReflectionData {n : ℕ} (f : LinearData R x y n) : LinearData R x y n :=
  fun i => dgCoherentBarLinearReflectionSign i.val.1.card •
    f.component (reverse i.val.1) i.val.2 (i.property.1.image Fin.rev)
      (by simpa only [card_reverse] using i.property.2)

lemma dgCoherentBarLinearReflectionData_component {n : ℕ} (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (dgCoherentBarLinearReflectionData f).component J k hJ hk =
      dgCoherentBarLinearReflectionSign J.card •
        f.component (reverse J) k (hJ.image Fin.rev) (by simpa only [card_reverse] using hk) := rfl

lemma dgCoherentBarLinearReflectionData_involution {n : ℕ} (f : LinearData R x y n) :
    dgCoherentBarLinearReflectionData (dgCoherentBarLinearReflectionData f) = f := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgCoherentBarLinearReflectionData (dgCoherentBarLinearReflectionData f)).component
    J k hJ hk = f.component J k hJ hk
  simp only [dgCoherentBarLinearReflectionData_component, card_reverse, reverse_reverse,
    smul_smul, dgCoherentBarLinearReflectionSign_mul_self, one_smul]

lemma dgCoherentBarLinearReflectionData_rhs {n : ℕ} (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (dgCoherentBarLinearReflectionData f).rhs J k hk =
      dgCoherentBarLinearReflectionSign J.card •
        f.rhs (reverse J) k (by simpa only [card_reverse] using hk) := by
  classical
  by_cases hJ : 2 ≤ J.card
  · have hRev : 2 ≤ (reverse J).card := by simpa only [card_reverse] using hJ
    rw [LinearData.rhs, dite_eq_left hJ, LinearData.rhs, dite_eq_left hRev, Finset.smul_sum]
    rw [← (DGNerveOppositeData.reverseElementEquiv J).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dgCoherentBarLinearReflectionData_component, smul_smul,
      DGNerveOppositeData.reverseElementEquiv, Equiv.coe_fn_mk, reverse_erase]
    rw [dgCoherentBarLinearReflection_delete_sign J j.val j.property]
  · have hRev : ¬ 2 ≤ (reverse J).card := by simpa only [card_reverse] using hJ
    rw [LinearData.rhs, dite_eq_right hJ, LinearData.rhs, dite_eq_right hRev, smul_zero]

def dgCoherentBarLinearReflectionSimplex {n : ℕ} (f : LinearSimplex R x y n) :
    LinearSimplex R x y n := by
  refine ⟨dgCoherentBarLinearReflectionData f.val, ?_⟩
  intro J k hJ hk
  rw [dgCoherentBarLinearReflectionData_component, differential_units_smul,
    f.equation (reverse J) k (hJ.image Fin.rev) (by simpa only [card_reverse] using hk),
    dgCoherentBarLinearReflectionData_rhs]

end SerrePositivity.InfinityCategories
