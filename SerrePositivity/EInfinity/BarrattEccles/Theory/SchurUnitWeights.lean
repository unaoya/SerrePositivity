module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWeightedBasis
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraEvaluation

/-!
# 自由生成元の包含と入力の重み

## 概要
Berger–Moerdijk §1 の自由代数の生成元包含は、指定された入力の重みを増やさない。

## 方針
一入力のテンソル冪、単位係数、Schur 生成射の比較を合成する。

## 規約
単位係数の重みは零である。

## 使われ方
実際のセル段の付加生成元の重み評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers
open ComplexWeightBasis
open scoped TensorProduct
variable {A : Type u} [CommRing A] {K : Complex A}

/-- The inverse one-power comparison inserts a weight-zero unit on the right. -/
lemma preserves_oneIso_inv (b : ComplexWeightBasis K) :
    b.Preserves (b.power 1) (oneIso K).inv := by
  rw [power_succ b 0, power_zero]
  intro i N x hx
  change (ρ_ K).inv.f i x ∈ _
  rw [complexRightUnitor_inv_apply]
  have h := tensorGradedInclusion_mem b.basis (unitDegreeBasis (A := A)) b.weight
    (fun _ => 0) i 0 i (by omega) N 0 hx
    (mem_basisWeightSpan_zero (unitDegreeBasis (A := A) 0) 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))
  simp only [Nat.add_zero] at h
  exact h

/-- The free generator inclusion preserves all original input weight bounds. -/
lemma preserves_schurUnit (b : ComplexWeightBasis K) :
    b.Preserves (schurWeightBasis b) ((operad A).schurUnit K) := by
  have h₁ := preserves_oneIso_inv b
  have h₂ := preserves_leftUnitor_inv (b.power 1)
  have h₃ := (preserves_to_arity ComplexWeightBasis.unit 1 (operad A).unit).tensor
    (preserves_id (b.power 1))
  have h₄ := preserves_schurι b 1
  have h := h₁.comp (h₂.comp (h₃.comp h₄))
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit, tensorHom_id] at h ⊢
  exact h

end SerrePositivity.EInfinity.BarrattEccles
