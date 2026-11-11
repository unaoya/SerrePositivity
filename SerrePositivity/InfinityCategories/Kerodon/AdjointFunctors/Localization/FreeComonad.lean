module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeRelativeCategory
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# 自由相対圏の comonad

概要：Dwyer–Kan の自由単体的解像に使う同じ自由相対圏を comonad に束ねる。
方針：自由関手・列の合成・一文字の列への対角の厳密な全公理を使う。
規約：全次数の解像へ反復できる通常の圏上の実際の comonad。
使われ方：相対圏の単体的自由解像の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

open CategoryTheory

/-- 概要：自由相対圏を作る厳密な endofunctor（Dwyer–Kan）。
方針：元の矢の列の圏と、指定する矢だけからなる列の類を使う。
規約：同じ相対関手を列の全矢へ適用する。
使われ方：単体的解像の次数ごとの反復。 -/
def freeRelativeFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} where
  obj C :=
    { category := Cat.of (Paths C.category)
      weakEquivalences := C.weakEquivalences.paths
      isMultiplicative := inferInstanceAs (C.weakEquivalences.paths.IsMultiplicative) }
  map F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeMap F
  map_id C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeMap_id C.weakEquivalences)
  map_comp F G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeMap_comp F G)

/-- 概要：自由関手の余単位は列の合成の自然な相対関手（Dwyer–Kan）。
方針：同じ自由圏の余単位と全係数への自然性を使う。
規約：指定する矢の乗法性は束ねた元の相対圏が持つ。
使われ方：単体的解像の面と augmentation。 -/
def freeRelativeCounit : freeRelativeFunctor.{u} ⟶ 𝟭 _ where
  app C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit C.weakEquivalences
  naturality _ _ F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeCounit_naturality F)

/-- 概要：自由関手の対角は一文字の列への自然な相対関手（Dwyer–Kan）。
方針：同じ生成矢の列への対角と全係数への自然性を使う。
規約：比較は厳密な相対関手。
使われ方：単体的解像の退化写像。 -/
def freeRelativeDiagonal : freeRelativeFunctor.{u} ⟶ freeRelativeFunctor ⋙ freeRelativeFunctor where
  app C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeDiagonal C.weakEquivalences
  naturality _ _ F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeDiagonal_naturality F)

/-- 概要：自由相対圏は元の余単位と対角で comonad をなす（Dwyer–Kan）。
方針：余結合性と両余単位則を元の自由関手の厳密な等式で照合する。
規約：comonad の全公理を保持し、単体的局所化の普遍性は別に証明する。
使われ方：CAlg_R のための自由単体的解像の入力。 -/
def freeRelativeComonad : Comonad _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} where
  toFunctor := freeRelativeFunctor
  ε := freeRelativeCounit
  δ := freeRelativeDiagonal
  coassoc C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeDiagonal_coassoc C.weakEquivalences)
  left_counit C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeDiagonal_left_counit C.weakEquivalences)
  right_counit C := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeFunctor_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeDiagonal_right_counit C.weakEquivalences)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
