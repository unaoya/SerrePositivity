module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockGeneratorAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurFirstBlockComposition

/-!
模型。文献の定義との比較は後で
# 内側の Schur 演算の生成射を外側へ渡す

概要：Berger–Moerdijk §1 の先頭ブロックの二段の合成を内側の Schur 演算の生成射で記述する。
方針：先頭代入と生成射の両立に、内側の演算のテンソル射を代入する。
規約：後半は入力ごとの Schur 生成射のテンソルとして保持する。
使われ方：一般の入力テンソル冪に対する先頭の部分合成則へ接続する。
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

/-- 概要：先頭への内側の代入と外側の入力生成射は内側の演算の生成射を使って計算できる（Berger–Moerdijk §1）。
方針：先頭代入と入力生成射の自然性を適用し、全合成のテンソル射の後へ Schur 生成射を合成する。
規約：入力族を前半 n 個と後半 m 個へ分離する。
使われ方：二段の Schur 作用を内側の作用と残りの入力生成射で表す。 -/
lemma schurFirstBlockInputs_generator (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.schurFirstBlockInputs K n m s ≫
      P.schurInputGenerator K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s) =
    (P.arity n ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m
      (fun j => P.arity (s j) ⊗ power K (s j))).hom) ≫
      (α_ (P.arity n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m)) ⊗ power K (s (j.castAdd m))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n)) ⊗ power K (s (j.natAdd n))))).inv ≫
      (P.schurOperationGenerator K n (fun j => s (j.castAdd m)) ⊗ₘ
        P.schurInputGenerator K m (fun j => s (j.natAdd n))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) m := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilySubstitution_generator (P.arity n)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) (fun r => P.arity r ⊗ power K r)
    (fun r => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K r) n m s
    (P.schurOperationTensor K n (fun j => s (j.castAdd m)))
  rw [← P.schurOperationGenerator_eq_tensor] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
