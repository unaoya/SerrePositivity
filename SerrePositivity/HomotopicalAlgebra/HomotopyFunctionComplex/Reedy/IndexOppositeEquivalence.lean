module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOpposite
public import Mathlib.CategoryTheory.Equivalence

/-!
# 反対圏を取ることで対応するReedy境界添字の圏同値を構成する

## 概要
反対圏を取ることで対応するReedy境界添字の圏同値を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0266][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0266
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Categorical opposite duality of Reedy boundary indices

The object correspondence is promoted to a fully faithful, essentially
surjective functor. The actual boundary source/target functors agree after
the equivalence. No limit or model-category assumptions are required.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

def matchingOpFunctor : MatchingIndex r.op (op j) ⥤ (LatchingIndex r j)ᵒᵖ where
  obj f := op (matchingOpObjEquiv r j f)
  map φ := Quiver.Hom.op (ObjectProperty.homMk (Over.homMk φ.hom.right.unop (by
    exact congrArg Quiver.Hom.unop (Under.w φ.hom))))
  map_id f := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp φ ψ := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

def matchingOpFullyFaithful : (matchingOpFunctor r j).FullyFaithful where
  preimage φ := ObjectProperty.homMk (Under.homMk φ.unop.hom.left.op (by
    exact congrArg Quiver.Hom.op (Over.w φ.unop.hom)))
  map_preimage φ := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    rfl

instance matchingOpFunctor_full : (matchingOpFunctor r j).Full :=
  (matchingOpFullyFaithful r j).full
instance matchingOpFunctor_faithful : (matchingOpFunctor r j).Faithful :=
  (matchingOpFullyFaithful r j).faithful
instance matchingOpFunctor_essSurj : (matchingOpFunctor r j).EssSurj where
  mem_essImage f := ⟨(matchingOpObjEquiv r j).symm f.unop,
    ⟨eqToIso (congrArg op ((matchingOpObjEquiv r j).apply_symm_apply f.unop))⟩⟩
instance matchingOpFunctor_isEquivalence : (matchingOpFunctor r j).IsEquivalence where

/-- 反対圏を取ることで対応するReedy境界添字の圏同値を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/
abbrev matchingOpEquivalence : MatchingIndex r.op (op j) ≌ (LatchingIndex r j)ᵒᵖ :=
  (matchingOpFunctor r j).asEquivalence

lemma matchingOpFunctor_target : matchingOpFunctor r j ⋙ (latchingSource r j).op =
    matchingTarget r.op (op j) := rfl

end SerrePositivity.Reedy
