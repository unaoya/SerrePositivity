module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurFirstBlockTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# Schur 生成射上の先頭ブロックの結合則

概要：Berger–Moerdijk §1 の先頭への部分合成と二段の全合成の一致を Schur 生成射へ送る。
方針：係数と入力のテンソル射の結合則の後へ Schur 生成射を合成し、arity の移送を相殺する。
規約：arity 零の演算と空の前半・後半を含む。
使われ方：Schur 作用の部分合成則を余極限の生成射上で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭の部分合成後の Schur 演算の生成射は二段の全合成に一致する（Berger–Moerdijk §1）。
方針：全合成のテンソル射の結合則に Schur 生成射を後置して arity の移送を相殺する。
規約：内側の全合成の結果をまとめた arity 族の先頭へ入れる。
使われ方：Schur 作用の先頭での部分合成則を生成射上へ移す。 -/
lemma schurOperationGenerator_firstBlock_assoc (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      P.schurOperationGenerator K (n + m) s =
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j)))).hom ≫
      (P.arity (1 + m) ◁ P.schurFirstBlockInputs K n m s) ≫
      P.schurOperationGenerator K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) := by
  rw [P.schurOperationGenerator_eq_tensor K (n + m) s,
    P.schurOperationGenerator_eq_tensor K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)]
  erw [reassoc_of% (P.schurOperationTensor_firstBlock_assoc K m n s)]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_index_eq P.sequence K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s)]

/-- 概要：Schur 入力の生成射上で先頭の部分合成は二段の作用に一致する（Berger–Moerdijk §1）。
方針：作用の生成射上の計算則で全合成へ移し、先頭ブロックの生成射の結合則を使う。
規約：内側の計算を schurFirstBlockInputs で表す。
使われ方：余極限の生成射で作用の部分合成則を検証する。 -/
lemma schurAction_firstBlock_generators (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      (P.arity (n + m) ◁ P.schurInputGenerator K (n + m) s) ≫
      P.schurAction K (n + m) =
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j) ⊗ power K (s j)))).hom ≫
      (P.arity (1 + m) ◁ (P.schurFirstBlockInputs K n m s ≫
        P.schurInputGenerator K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s))) ≫
      P.schurAction K (1 + m) := by
  rw [P.schurInputGenerator_action, P.schurOperationGenerator_firstBlock_assoc]
  rw [whiskerLeft_comp, Category.assoc, P.schurInputGenerator_action]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
