module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWeightedBasis

/-!
# Schur 演算の合成と入力の重み

## 概要
Berger–Moerdijk §1 の自由代数の演算で、内側の演算族を合成する生成射を扱う。

## 方針
係数と入力を分離し、係数の合成と入力の連結を別々に比較する。

## 規約
係数は重み零。内側の演算の arity は互いに異なってよい。

## 使われ方
自由代数とセル段の演算が入力の総重みを増やさないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory DifferentialGraded
open ComplexWeightBasis
open scoped BigOperators
variable {A : Type u} [CommRing A]

/-- The operation generator composes arbitrary coefficients without increasing input weights. -/
lemma preserves_schurOperationGenerator {K : Complex A} (b : ComplexWeightBasis K)
    (n : ℕ) (s : Fin n → ℕ) :
    ((arityWeightBasis n).tensor
      (family n (fun j => (arityWeightBasis (s j)).tensor (b.power (s j))))).Preserves
      (schurWeightBasis b) ((operad A).schurOperationGenerator K n s) := by
  let c := fun j => arityWeightBasis (A := A) (s j)
  let d := fun j => b.power (s j)
  have h₁ := (preserves_id (arityWeightBasis (A := A) n)).tensor
    (preserves_familyTensorIso n c d)
  have h₂ := preserves_associator_inv (arityWeightBasis (A := A) n)
    (family n c) (family n d)
  have h₃ := (preserves_to_arity ((arityWeightBasis n).tensor (family n c))
    (∑ j, s j) ((operad A).composition n s)).tensor (preserves_powerFamilyIso b n s)
  have h₄ := preserves_schurι b (∑ j, s j)
  have h := h₁.comp (h₂.comp (h₃.comp h₄))
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationGenerator, id_tensorHom] at h ⊢
  exact h

end SerrePositivity.EInfinity.BarrattEccles
