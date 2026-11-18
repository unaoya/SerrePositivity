module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationTensor

/-!
模型。文献の定義との比較は後で
# 末尾の入力を残した反復合成のテンソル射

概要：Berger–Moerdijk §1 の全合成の評価を、末尾に任意個の入力を残した形へ拡張する。
方針：指定した演算の係数と入力を分離し、係数の反復合成と入力の連結をテンソルする。
規約：前半 n 個の演算だけを代入し、末尾 k 個の入力はそのまま残す。
使われ方：全合成の評価の帰納法で、最後に代入した演算の入力を新しい末尾へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：未処理の末尾入力を残して、演算の係数と入力を同時に合成する射（Berger–Moerdijk §1）。
方針：前半の有限テンソル族の係数を集め、反復合成と末尾を含めた入力連結を適用する。
規約：末尾の入力は交換せず、指定した演算の全入力の後に置く。
使われ方：代数の評価の作用保存を n に関する帰納法で証明する対象となる。 -/
def iteratedOperationTensor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n k : ℕ) (s : Fin n → ℕ) :
    P.arity (n + k) ⊗
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j) ⊗ power K (s j)) ⊗ power K k) ⟶
      P.arity ((∑ j, s j) + k) ⊗ power K ((∑ j, s j) + k) :=
  (P.arity (n + k) ◁
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => P.arity (s j)) (fun j => power K (s j))).hom ▷
      power K k)) ≫
    (P.arity (n + k) ◁ (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j))) (power K k)).hom) ≫
    (α_ (P.arity (n + k)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j)) ⊗ power K k)).inv ≫
    (P.composeFirstInputs n k s ⊗ₘ
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom ▷ power K k) ≫ (appendIso K (∑ j, s j) k).hom))

/-- 概要：指定した演算族が空なら反復合成のテンソル射は空の入力と末尾の連結だけである（Berger–Moerdijk §1）。
方針：空の有限テンソル族の分離を展開し、単位子の整合性を適用する。
規約：未処理の末尾の入力数 k は任意とする。
使われ方：末尾を残した全合成の評価の帰納法の基底となる。 -/
lemma iteratedOperationTensor_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (k : ℕ)
    (s : Fin 0 → ℕ) :
    P.iteratedOperationTensor K 0 k s =
      P.arity (0 + k) ◁ (appendIso K 0 k).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.iteratedOperationTensor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.sum_univ_zero, eqToIso.hom, Iso.symm_hom,
    eqToHom_refl, Category.comp_id, id_whiskerRight, Category.id_comp]
  monoidal

/-- 概要：未処理の末尾が空なら反復合成のテンソル射は Schur 演算のテンソル射に戻る（Berger–Moerdijk §1）。
方針：末尾の零乗を右単位子で除き、係数と入力の合成へ単位子の自然性を適用する。
規約：指定した演算族の長さと各 arity は任意。
使われ方：末尾を残した評価の帰納法から通常の全合成の評価を取り出す。 -/
lemma iteratedOperationTensor_tail_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n : ℕ) (s : Fin n → ℕ) :
    P.iteratedOperationTensor K n 0 s =
      (P.arity n ◁ (ρ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j) ⊗ power K (s j)))).hom) ≫
        P.schurOperationTensor K n s := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.iteratedOperationTensor _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationTensor
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, eqToHom_refl, id_whiskerRight, Category.id_comp,
    Category.comp_id, appendIso_zero_right]
  monoidal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
