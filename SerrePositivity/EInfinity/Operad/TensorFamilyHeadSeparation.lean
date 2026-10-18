module

public import SerrePositivity.EInfinity.Operad.TensorFamilyHeadAssembly
public import SerrePositivity.EInfinity.Operad.TensorFamilyTensorSplitAt

/-!
# 先頭の組み込みと係数・入力の分離

概要：Berger–Moerdijk §1 の先頭ブロックの合成結果を係数列と入力列へ分ける。
方針：二ブロック再結合との両立を一入力の前半に適用し、単位因子を相殺する。
規約：先頭の係数と入力は既に一つのテンソル対へまとまっている。
使われ方：Schur 作用の生成射の先頭で二段の合成を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭のテンソル対の組み込みは係数列と入力列の独立な組み込みへ分かれる（Berger–Moerdijk §1）。
方針：二ブロック分離の逆射との両立を使い、一次の分離に付く右単位子を除く。
規約：後半の係数・入力の交換には既存の Koszul 対称性を使う。
使われ方：先頭で合成した Schur 生成射の係数と入力を独立に計算する。 -/
lemma tensorFamilyHeadAssembly_tensor (m : ℕ) (V W : Fin (1 + m) → Complex A) :
    tensorFamilyHeadAssembly m (fun j => V j ⊗ W j) ≫
      (tensorFamilyTensorIso (1 + m) V W).hom =
    ((V ((0 : Fin 1).castAdd m) ⊗ W ((0 : Fin 1).castAdd m)) ◁
      (tensorFamilyTensorIso m (fun j => V (j.natAdd 1)) (fun j => W (j.natAdd 1))).hom) ≫
      tensorμ (V ((0 : Fin 1).castAdd m)) (W ((0 : Fin 1).castAdd m))
        (tensorFamily m (fun j => V (j.natAdd 1)))
        (tensorFamily m (fun j => W (j.natAdd 1))) ≫
      (tensorFamilyHeadAssembly m V ⊗ₘ tensorFamilyHeadAssembly m W) := by
  unfold tensorFamilyHeadAssembly
  rw [Category.assoc, tensorFamilyTensorIso_splitAt_inv]
  rw [whiskerRight_comp_tensorHom_assoc]
  erw [tensorFamilyTensorIso_one_inv]
  rw [tensorHom_def']
  simp only [Category.assoc]
  erw [tensorμ_natural_left_assoc]
  rw [tensorHom_comp_tensorHom]

end SerrePositivity.EInfinity
