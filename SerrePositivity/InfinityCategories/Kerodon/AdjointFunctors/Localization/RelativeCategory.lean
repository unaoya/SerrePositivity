module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Dwyer–Kan 解像に使う相対圏の圏

概要：指定する矢の乗法的な類を持つ圏を相対圏として束ねる。
方針：同じ宇宙の圏と射の類、相対関手を Mathlib のデータで構成する。
規約：対象と Hom の宇宙を揃え、モデル構造や二つのうち三つの性質は要求しない。
使われ方：自由相対圏の comonad とその単体的解像。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

open CategoryTheory

/-- 概要：DK 解像に使う乗法的な指定矢の類を持つ相対圏（Dwyer–Kan）。
方針：通常の圏・指定する矢の類・乗法性を束ねる。
規約：対象と Hom は同じ宇宙、指定する矢は同型全体や飽和性を仮定しない。
使われ方：自由解像の全次数の係数圏。 -/
structure RelativeCategory where
  category : Cat.{u, u}
  weakEquivalences : MorphismProperty category
  isMultiplicative : weakEquivalences.IsMultiplicative

attribute [instance] RelativeCategory.isMultiplicative

/-- 概要：相対圏の射は指定する矢を保つ関手（Dwyer–Kan）。
方針：Mathlib の LocalizerMorphism の恒等射と合成を使う。
規約：相対関手のデータを変更しない。
使われ方：自由相対圏を厳密な endofunctor として構成する。 -/
instance relativeCategoryCategory : Category (RelativeCategory.{u}) where
  Hom C D := LocalizerMorphism C.weakEquivalences D.weakEquivalences
  id C := LocalizerMorphism.id C.weakEquivalences
  comp F G := F.comp G

/-- 概要：相対関手の等式は元の関手の等式で決まる（Dwyer–Kan）。
方針：指定する矢の保存は命題であることを使う。
規約：対象・射に関する元の関手の厳密な等式。
使われ方：自由相対圏の comonad の恒等式を照合する。 -/
@[ext]
lemma relativeFunctor_ext {C D : Type*} [Category C] [Category D]
    {W : MorphismProperty C} {V : MorphismProperty D} (F G : LocalizerMorphism W V)
    (h : F.functor = G.functor) : F = G := by
  cases F
  cases G
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
