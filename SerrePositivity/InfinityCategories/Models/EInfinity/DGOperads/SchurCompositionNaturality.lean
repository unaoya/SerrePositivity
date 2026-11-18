module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorNaturality

/-!
模型。文献の定義との比較は後で
# Schur 合成の生成射の自然性

概要：Berger–Moerdijk §1 の自由代数の演算の生成射が底の複体射について自然であることを示す。
方針：係数と入力の分離、入力の連結、Schur 生成射のそれぞれの自然性を組み合わせる。
規約：係数のオペラッドを固定し、複体射は任意の chain map とする。
使われ方：自由代数関手の射が演算の作用を保つことを証明する。
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

/-- 概要：Schur 合成の生成射は底の chain map に関して自然である（Berger–Moerdijk §1）。
方針：テンソル分離の自然性、連結の自然性と Schur 生成射の自然性を順に適用する。
規約：arity の有限族は固定し、全ての入力に同じ chain map を適用する。
使われ方：自由代数の作用を構成した後、その関手性を生成射上で検証する。 -/
lemma schurOperationGenerator_naturality (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K L : Complex A} (f : K ⟶ L)
    (n : ℕ) (s : Fin n → ℕ) :
    (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => 𝟙 (P.arity (s i)) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f (s i))) ≫
      P.schurOperationGenerator L n s =
        P.schurOperationGenerator K n s ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f := by
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_naturality n
    (fun i => 𝟙 (P.arity (s i))) (fun i => _root_.SerrePositivity.TensorPowers.map f (s i))
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_id] at hc
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationGenerator, Category.assoc]
  rw [← whiskerLeft_comp_assoc, hc]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whiskerLeft_comp_tensorHom_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_naturality]
  rw [← tensorHom_comp_whiskerLeft_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
