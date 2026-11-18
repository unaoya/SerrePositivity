module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionFirstBlockFull

/-!
模型。文献の定義との比較は後で
# Schur 演算の係数と入力を合成したテンソル射

概要：Berger–Moerdijk §1 の自由代数の演算で、最終の Schur 生成射の直前の射を扱う。
方針：係数の全合成と入力の連結を一つのテンソル射にまとめる。
規約：終域は総 arity のオペラッド係数と底の入力のテンソル積。
使われ方：二段の演算の係数側と入力側を比較してから Schur 生成射を適用する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso

/-- 概要：Schur 生成射に入れる前の係数と入力の全合成射（Berger–Moerdijk §1）。
方針：係数と入力を分離し、係数の全合成と入力の連結をテンソルする。
規約：零入力の演算と空の入力族を含む。
使われ方：自由代数の部分合成則を最終の Schur 生成射の手前で証明する。 -/
def schurOperationTensor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    P.arity n ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j) ⊗ power K (s j)) ⟶
      P.arity (∑ j, s j) ⊗ power K (∑ j, s j) :=
  (P.arity n ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => P.arity (s j)) (fun j => power K (s j))).hom) ≫
    (α_ (P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j)))).inv ≫
    (P.composition n s ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom)

/-- 概要：Schur 演算の生成射は全合成のテンソル射と Schur 生成射の合成である（Berger–Moerdijk §1）。
方針：両辺の定義の合成の括弧付けを比較する。
規約：同じ arity 族を両辺で使う。
使われ方：テンソル射上の部分合成則を Schur 演算の生成射へ送る。 -/
lemma schurOperationGenerator_eq_tensor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) (s : Fin n → ℕ) :
    P.schurOperationGenerator K n s =
      P.schurOperationTensor K n s ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (∑ j, s j) := by
  rfl

/-- 概要：外側の係数射は係数と入力の分離を通して係数の全合成へ移せる（Berger–Moerdijk §1）。
方針：左の係数射を分離同型と結合子の自然性で移し、テンソル射の合成則を使う。
規約：係数射 f の始域は任意の複体でよい。
使われ方：外側の部分合成を先に行う計算へ係数側の結合則を適用する。 -/
lemma schurOperationTensor_coefficient_map (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ)
    (s : Fin n → ℕ) {C : Complex A} (f : C ⟶ P.arity n) :
    (f ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      P.schurOperationTensor K n s =
    (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => P.arity (s j)) (fun j => power K (s j))).hom) ≫
      (α_ C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j)))).inv ≫
      (((f ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫ P.composition n s) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationTensor
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    whiskerRight_comp_tensorHom]

/-- 概要：先頭で部分合成した Schur 演算の係数は内側と外側の二段の全合成で計算できる（Berger–Moerdijk §1）。
方針：係数射を全合成のテンソル射へ通し、先頭ブロックでの係数の結合則を適用する。
規約：入力の連結射を固定し、係数射だけを二段の全合成へ移す。
使われ方：入力側の先頭ブロックの連結則と合わせて部分合成則を証明する。 -/
lemma schurOperationTensor_firstBlock_coefficient (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      P.schurOperationTensor K (n + m) s =
    ((P.arity (1 + m) ⊗ P.arity n) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + m) (fun j => P.arity (s j)) (fun j => power K (s j))).hom) ≫
      (α_ (P.arity (1 + m) ⊗ P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => power K (s j)))).inv ≫
      (((α_ (P.arity (1 + m)) (P.arity n)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j)))).hom ≫
        (P.arity (1 + m) ◁ P.firstBlockCompositionInputs n m s) ≫
        P.composition (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s))) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + m) s).hom) := by
  erw [P.schurOperationTensor_coefficient_map K (n + m) s (P.composeAheadOfInputs m 0 n)]
  rw [P.composition_first_block_assoc]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
