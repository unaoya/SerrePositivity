module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BasedWeightMaps
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorFamilyWeights
public import SerrePositivity.EInfinity.BarrattEccles.Theory.UnitWordWeights
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition

/-!
# 有限入力族の係数と入力を分離する重み保存

## 概要
Berger–Moerdijk §1 の有限テンソル族の比較が、指定された入力の総重みを保つ。

## 方針
係数と入力の中間交換を、結合子と Koszul 組紐の重み保存へ帰着する。

## 規約
零入力の比較も指定された単位基底を使う。

## 使われ方
自由代数の Schur 演算の合成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A]
namespace ComplexWeightBasis

/-- The weight-zero tensor unit with its specified homogeneous basis. -/
abbrev unit : ComplexWeightBasis (𝟙_ (Complex A)) :=
  ⟨unitDegreeIndex, unitDegreeBasis, fun _ => 0⟩

/-- The weighted basis of a finite family of based complexes. -/
abbrev family (n : ℕ) {V : Fin n → Complex A} (b : ∀ j, ComplexWeightBasis (V j)) :
    ComplexWeightBasis (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V) :=
  ⟨familyGradedIndex n (fun j => (b j).index),
    familyGradedBasis n (fun j => (b j).basis),
    familyGradedWeight n (fun j => (b j).weight)⟩

lemma preserves_leftUnitor {K : Complex A} (b : ComplexWeightBasis K) :
    (unit.tensor b).Preserves b (λ_ K).hom :=
  leftUnitor_mem_basisWeightSpan b.basis b.weight

lemma preserves_leftUnitor_inv {K : Complex A} (b : ComplexWeightBasis K) :
    b.Preserves (unit.tensor b) (λ_ K).inv :=
  leftUnitor_inv_mem_basisWeightSpan b.basis b.weight

/-- Separating two varying tensor families preserves their total weight. -/
lemma preserves_familyTensorIso (n : ℕ) {V W : Fin n → Complex A}
    (b : ∀ j, ComplexWeightBasis (V j)) (c : ∀ j, ComplexWeightBasis (W j)) :
    (family n (fun j => (b j).tensor (c j))).Preserves
      ((family n b).tensor (family n c)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n V W).hom := by
  induction n with
  | zero => exact preserves_leftUnitor_inv unit
  | succ n ih =>
    have h₁ := (preserves_id ((b 0).tensor (c 0))).tensor
      (ih (fun j => b j.succ) (fun j => c j.succ))
    have h₂ := preserves_tensorμ (b 0) (c 0)
      (family n (fun j => b j.succ)) (family n (fun j => c j.succ))
    have h := h₁.comp h₂
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, Iso.trans_hom, whiskerLeftIso_hom,
      id_tensorHom] at h ⊢
    exact h

/-- The recursively chosen power basis weighted by the list of its inputs. -/
abbrev power {K : Complex A} (b : ComplexWeightBasis K) (n : ℕ) :
    ComplexWeightBasis (TensorPowers.power K n) :=
  ⟨powerGradedIndex b.index n, powerGradedBasis b.basis n,
    powerGradedWeightFamily b.weight n⟩

lemma power_zero {K : Complex A} (b : ComplexWeightBasis K) : b.power 0 = unit := rfl

lemma power_succ {K : Complex A} (b : ComplexWeightBasis K) (n : ℕ) :
    b.power (n + 1) = b.tensor (b.power n) := by
  dsimp only [power, tensor]
  rw [powerGradedWeightFamily_succ]
  rfl

/-- Transport of the power index preserves the specified weighted basis. -/
lemma preserves_power_eq {K : Complex A} (b : ComplexWeightBasis K)
    {m n : ℕ} (h : m = n) :
    (b.power m).Preserves (b.power n) (eqToHom (congrArg (TensorPowers.power K) h)) := by
  subst n
  exact preserves_id (b.power m)

/-- Concatenating two tensor words preserves the sum of their input weights. -/
lemma preserves_appendIso {K : Complex A} (b : ComplexWeightBasis K) (m n : ℕ) :
    ((b.power m).tensor (b.power n)).Preserves (b.power (m + n))
      (appendIso K m n).hom := by
  induction m with
  | zero =>
    change (unit.tensor (b.power n)).Preserves (b.power (0 + n))
      ((λ_ (TensorPowers.power K n)).hom ≫ _)
    exact (preserves_leftUnitor (b.power n)).comp
      (preserves_power_eq b (Nat.zero_add n).symm)
  | succ m ih =>
    have h₁ := preserves_associator b (b.power m) (b.power n)
    have h₂ := (preserves_id b).tensor ih
    have h₃ := preserves_power_eq b (Nat.succ_add m n).symm
    rw [power_succ] at h₃
    have h := (h₁.comp h₂).comp h₃
    rw [power_succ]
    simp only [appendIso, Iso.trans_hom, eqToIso.hom,
      whiskerLeftIso_hom, id_tensorHom] at h ⊢
    exact h

/-- A finite family of tensor words has the same total input bound after concatenation. -/
lemma preserves_powerFamilyIso {K : Complex A} (b : ComplexWeightBasis K)
    (n : ℕ) (s : Fin n → ℕ) :
    (family n (fun j => b.power (s j))).Preserves (b.power (∑ j, s j))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Fin.sum_univ_zero, eqToIso_refl, Iso.refl_hom]
    exact preserves_id unit
  | succ n ih =>
    have h₁ := (preserves_id (b.power (s 0))).tensor (ih (fun j => s j.succ))
    have h₂ := preserves_appendIso b (s 0) (∑ j : Fin n, s j.succ)
    have h₃ := preserves_power_eq b (Fin.sum_univ_succ s).symm
    have h := (h₁.comp h₂).comp h₃
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Iso.trans_hom, eqToIso.hom,
      whiskerLeftIso_hom, id_tensorHom] at h ⊢
    exact h

end ComplexWeightBasis
end SerrePositivity.EInfinity
