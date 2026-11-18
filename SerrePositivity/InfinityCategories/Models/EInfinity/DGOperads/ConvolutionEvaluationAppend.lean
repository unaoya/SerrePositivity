module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEquivariantEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerSeparationAppend

/-!
模型。文献の定義との比較は後で
# 反復評価とブロック連結

概要：Berger–Fresse §3.1 の反復評価は関数と評価点の二ブロックの連結に両立する。
方針：各ブロックの対を分離してから、連結の自然性へ帰着する。
規約：空ブロックを含み、全ての交換には Koszul 符号が含まれる。
使われ方：入力への演算の代入と出力への余演算の代入を評価で比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：反復評価は入力数の等式による移送を保つ（BF §3.1）。
方針：入力数の等式を消去して恒等射に帰着する。
規約：関数・評価点・出力を同じ等式で移す。
使われ方：二ブロックの長さの和の表示を交換する。 -/
@[reassoc]
lemma convolutionPowerEvaluation_index (H B : Complex A) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg (power (homComplex A H B)) h) ⊗ₘ
      eqToHom (congrArg (power H) h)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B m ≫ eqToHom (congrArg (power B) h) := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight,
    Category.id_comp, Category.comp_id]

/-- 概要：二ブロックを評価して連結する射は先に連結した評価に一致する（BF §3.1）。
方針：分離同型で前合成し、分離・評価の一致とテンソル冪の連結の自然性を使う。
規約：関数の前半・後半と評価点の前半・後半を tensorμ で対にする。
使われ方：部分合成の評価の比較を三ブロックへ分解する基底となる。 -/
@[reassoc]
lemma convolutionPowerEvaluation_append (H B : Complex A) (m n : ℕ) :
    tensorμ (power (homComplex A H B) m) (power (homComplex A H B) n)
        (power H m) (power H n) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n) ≫
      (appendIso B m n).hom =
    ((appendIso (homComplex A H B) m n).hom ⊗ₘ (appendIso H m n).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B (m + n) := by
  let q : (power (homComplex A H B) m ⊗ power H m) ⊗
      (power (homComplex A H B) n ⊗ power H n) ≅
      (power (homComplex A H B) m ⊗ power (homComplex A H B) n) ⊗
        (power H m ⊗ power H n) :=
    { hom := tensorμ _ _ _ _
      inv := tensorδ _ _ _ _
      hom_inv_id := tensorμ_tensorδ _ _ _ _
      inv_hom_id := tensorδ_tensorμ _ _ _ _ }
  apply (cancel_epi ((tensorIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (homComplex A H B) H m)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (homComplex A H B) H n)) ≪≫ q).hom).1
  simp only [Iso.trans_hom, tensorIso_hom, q, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSeparation_twice_assoc, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_append_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_separation]
  exact appendIso_naturality (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H B) m n


/-- 概要：反復評価の出力を二ブロックへ分ける射は入力の分割後の評価に一致（BF §3.1）。
方針：連結後の評価の公式に連結同型の逆射を合成して相殺する。
規約：二列を分割してから tensorμ で同じ位置のブロックを対にする。
使われ方：代入・余代入の定義に現れるブロック分割を評価へ通す。 -/
@[reassoc]
lemma convolutionPowerEvaluation_split (H B : Complex A) (m n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B (m + n) ≫ (appendIso B m n).inv =
    ((appendIso (homComplex A H B) m n).inv ⊗ₘ (appendIso H m n).inv) ≫
      tensorμ (power (homComplex A H B) m) (power (homComplex A H B) n)
        (power H m) (power H n) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H B n) := by
  apply (cancel_mono (appendIso B m n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_append, tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
