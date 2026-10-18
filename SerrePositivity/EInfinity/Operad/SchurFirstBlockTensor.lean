module

public import SerrePositivity.EInfinity.Operad.SchurOperationTensor
public import SerrePositivity.EInfinity.Operad.FirstBlockSubstitution
public import SerrePositivity.EInfinity.Operad.FirstBlockPowerAssembly
public import SerrePositivity.EInfinity.Operad.TensorNestedCoefficient

/-!
# Schur 演算の先頭ブロックでのテンソル射の結合則

概要：Berger–Moerdijk §1 の先頭への部分合成後の全合成と、内側・外側の二段の全合成を比較する。
方針：先頭の代入を係数と入力へ分離し、両側の結合則をテンソル射の整合性で合わせる。
規約：最終の Schur 生成射の手前で、総 arity の係数と入力を終域とする。
使われ方：自由代数の部分合成則を生成射上で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  tensorFamilyTensorIso tensorPowerFamilyIso

/-- 概要：内側の Schur 演算の係数と入力を合成して外側の先頭入力へ組み込む（Berger–Moerdijk §1）。
方針：先頭ブロックへの一般の代入に内側の演算のテンソル射を使う。
規約：後半の演算の係数と入力はそのまま保持する。
使われ方：二段の Schur 演算の内側の計算を表す。 -/
def schurFirstBlockInputs (P : Operad A) (K : Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.arity n ⊗ tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j)) ⟶
      tensorFamily (1 + m) (fun j => P.arity (firstBlockArities n m s j) ⊗
        power K (firstBlockArities n m s j)) :=
  firstBlockFamilySubstitution (P.arity n) (fun r => P.arity r ⊗ power K r) n m s
    (P.schurOperationTensor K n (fun j => s (j.castAdd m)))

/-- 概要：係数族への一般の先頭代入はオペラッドの既存の先頭代入に一致する（Berger–Moerdijk §1）。
方針：二つの定義の再結合射を同定する。
規約：係数の全合成以外の部分は入力族の分離と再結合のみ。
使われ方：一般のテンソル分離則へ係数の結合則を適用する。 -/
lemma firstBlockFamilySubstitution_arity (P : Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    firstBlockFamilySubstitution (P.arity n) P.arity n m s
      (P.composition n (fun j => s (j.castAdd m))) = P.firstBlockCompositionInputs n m s := by
  rfl

/-- 概要：内側の Schur 演算の先頭代入は係数の合成と入力の連結へ分離する（Berger–Moerdijk §1）。
方針：先頭代入のテンソル分離則に係数の全合成とテンソル冪の連結を代入する。
規約：外側の入力族は前半の総 arity を先頭に持つ。
使われ方：二段の演算へ係数側と入力側の結合則を独立に適用する。 -/
lemma schurFirstBlockInputs_tensor (P : Operad A) (K : Complex A) (n m : ℕ)
    (s : Fin (n + m) → ℕ) :
    P.schurFirstBlockInputs K n m s ≫
      (tensorFamilyTensorIso (1 + m) (fun j => P.arity (firstBlockArities n m s j))
        (fun j => power K (firstBlockArities n m s j))).hom =
    (P.arity n ◁ (tensorFamilyTensorIso (n + m)
      (fun j => P.arity (s j)) (fun j => power K (s j))).hom) ≫
      (α_ (P.arity n) (tensorFamily (n + m) (fun j => P.arity (s j)))
        (tensorFamily (n + m) (fun j => power K (s j)))).inv ≫
      (P.firstBlockCompositionInputs n m s ⊗ₘ
        firstBlockFamilyCollapse (power K) n m s
          (tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom) := by
  have h := firstBlockFamilySubstitution_tensor (P.arity n) P.arity (power K) n m s
    (P.composition n (fun j => s (j.castAdd m)))
    (tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom
  rw [P.firstBlockFamilySubstitution_arity] at h
  exact h

/-- 概要：先頭の部分合成後の全合成は二段の Schur 演算のテンソル射に一致する（Berger–Moerdijk §1）。
方針：先頭代入の分離則で二段の演算を分け、係数の結合則と入力の連結則を使う。
規約：最後に係数と入力の双方を元の総 arity へ移送する。
使われ方：自由代数の先頭での部分合成則を Schur 生成射へ送る。 -/
lemma schurOperationTensor_firstBlock_assoc (P : Operad A) (K : Complex A)
    (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷
      tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      P.schurOperationTensor K (n + m) s =
    (α_ (P.arity (1 + m)) (P.arity n)
      (tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j)))).hom ≫
      (P.arity (1 + m) ◁ P.schurFirstBlockInputs K n m s) ≫
      P.schurOperationTensor K (1 + m) (firstBlockArities n m s) ≫
      (eqToHom (congrArg P.arity (firstBlockArities_sum n m s)) ⊗ₘ
        eqToHom (congrArg (power K) (firstBlockArities_sum n m s))) := by
  rw [P.schurOperationTensor_firstBlock_coefficient]
  conv_rhs =>
    arg 2
    arg 2
    arg 1
    unfold schurOperationTensor
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, P.schurFirstBlockInputs_tensor]
  erw [reassoc_of% (tensorNestedCoefficient
    (tensorFamilyTensorIso (n + m) (fun j => P.arity (s j)) (fun j => power K (s j))).hom
    (P.firstBlockCompositionInputs n m s)
    (firstBlockFamilyCollapse (power K) n m s
      (tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom)
    (P.composition (1 + m) (firstBlockArities n m s))
    (tensorPowerFamilyIso K (1 + m) (firstBlockArities n m s)).hom)]
  rw [tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  have hp := tensorPowerFamilyIso_firstBlock K n m s
  change firstBlockFamilyCollapse (power K) n m s
    (tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom ≫
    (tensorPowerFamilyIso K (1 + m) (firstBlockArities n m s)).hom ≫
    eqToHom (congrArg (power K) (firstBlockArities_sum n m s)) = _ at hp
  rw [hp]

end SerrePositivity.EInfinity.Operad
