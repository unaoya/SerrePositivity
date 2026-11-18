module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorMap
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# 先頭の演算を組み込んだ Schur 入力の生成射

概要：Berger–Moerdijk §1 の二段の全合成で、先頭の合成結果の生成射を外側の作用へ渡す。
方針：有限族の生成射の自然性を Schur 生成射へ適用し、作用の生成射上の計算則を使う。
規約：後半の入力族を一つのテンソル冪として保持する。
使われ方：Schur 作用の先頭での部分合成則を生成射上で検証する。
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

/-- 概要：先頭を組み込んだ入力生成射は先頭と後半へ独立に生成射を適用して計算できる（Berger–Moerdijk §1）。
方針：任意の有限族の生成射と先頭の組み込みの両立を Schur 生成射に適用する。
規約：先頭と後半の全ての arity は零を許す。
使われ方：内側の Schur 演算の生成射を外側の入力族へ組み込む。 -/
lemma schurInputGenerator_headAssembly (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m : ℕ)
    (s : Fin (1 + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m (fun j => P.arity (s j) ⊗ power K (s j)) ≫
      P.schurInputGenerator K (1 + m) s =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s ((0 : Fin 1).castAdd m)) ⊗ₘ
      P.schurInputGenerator K m (fun j => s (j.natAdd 1))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) m := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_headAssembly ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
    (fun r => P.arity r ⊗ power K r) (fun r => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K r) m s

/-- 概要：先頭と後半の Schur 生成射から外側の作用を計算する（Berger–Moerdijk §1）。
方針：先頭の組み込みの自然性を使い、作用の生成射上の式を適用する。
規約：外側の演算は 1+m 入力で、先頭に一つの Schur 生成射を置く。
使われ方：内側の全合成を先頭へ代入した二段の Schur 作用の計算に用いる。 -/
lemma schurAction_headAssembly (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m : ℕ)
    (s : Fin (1 + m) → ℕ) :
    (P.arity (1 + m) ◁
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s ((0 : Fin 1).castAdd m)) ⊗ₘ
        P.schurInputGenerator K m (fun j => s (j.natAdd 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) m)) ≫
      P.schurAction K (1 + m) =
    (P.arity (1 + m) ◁
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m (fun j => P.arity (s j) ⊗ power K (s j))) ≫
      P.schurOperationGenerator K (1 + m) s := by
  rw [← P.schurInputGenerator_headAssembly K m s, whiskerLeft_comp, Category.assoc,
    P.schurInputGenerator_action]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
