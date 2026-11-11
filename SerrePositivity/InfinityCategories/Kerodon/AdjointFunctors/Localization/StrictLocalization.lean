module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# 相対圏の指定矢を反転する構成の厳密な関手性

概要：Dwyer–Kan の各自由次数での局所化を厳密な関手として構成する。
方針：元の Gabriel–Zisman の構成の lift と厳密な因子化・一意性を使う。
規約：局所化の対象と射は既存の構成そのもの。
使われ方：自由相対圏の単体的図式を次数ごとに局所化する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

noncomputable section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {V : MorphismProperty D}

/-- 概要：元の相対関手から構成的な局所化の射を得る（Dwyer–Kan）。
方針：元の各矢の像と指定矢の逆像を同じ構成の lift へ入力する。
規約：局所化の対象の選択を変更しない。
使われ方：各自由次数の局所化の単体作用素。 -/
def strictLocalizationMap (F : LocalizerMorphism W V) : W.Localization ⥤ V.Localization :=
  Localization.Construction.lift (F.functor ⋙ V.Q)
    (fun _ _ f hf => V.Q_inverts (F.functor.map f) (F.map f hf))

/-- 概要：局所化の射は元の相対関手で厳密に因子化（Dwyer–Kan）。
方針：構成的な lift の同じ因子化の等式を使う。
規約：自然同型だけでなく元の関手の等式。
使われ方：全単体恒等式の厳密な保存。 -/
lemma strictLocalizationMap_fac (F : LocalizerMorphism W V) :
    W.Q ⋙ strictLocalizationMap F = F.functor ⋙ V.Q :=
  Localization.Construction.fac _ _

/-- 概要：構成的な局所化の射は恒等関手を厳密に保つ（Dwyer–Kan）。
方針：元の構成の因子化と厳密な一意性を使う。
規約：指定した同じ局所化の構成。
使われ方：次数ごとの局所化を厳密な関手へ束ねる。 -/
lemma strictLocalizationMap_id (W : MorphismProperty C) :
    strictLocalizationMap (LocalizerMorphism.id W) = 𝟭 W.Localization := by
  apply Localization.Construction.uniq
  rw [strictLocalizationMap_fac]
  rfl

/-- 概要：構成的な局所化の射は合成を厳密に保つ（Dwyer–Kan）。
方針：元の因子化の等式を二回使い、同じ構成の一意性を適用する。
規約：局所化の比較同型による合成の選択を入れない。
使われ方：局所化後の単体作用素の全恒等式。 -/
lemma strictLocalizationMap_comp {E : Type*} [Category E] {U : MorphismProperty E}
    (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) :
    strictLocalizationMap (F.comp G) = strictLocalizationMap F ⋙ strictLocalizationMap G := by
  apply Localization.Construction.uniq
  rw [strictLocalizationMap_fac, ← Functor.assoc, strictLocalizationMap_fac,
    Functor.assoc, strictLocalizationMap_fac]
  rfl

/-- 概要：相対圏から各指定矢の構成的局所化への厳密な関手（Dwyer–Kan）。
方針：同じ局所化の射の恒等則・合成則を束ねる。
規約：対象と Hom の同じ宇宙を保つ。
使われ方：自由単体的解像の次数ごとの局所化。 -/
def strictLocalizationFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ Cat.{u, u} where
  obj C := Cat.of C.weakEquivalences.Localization
  map F := (strictLocalizationMap F).toCatHom
  map_id C := congrArg Functor.toCatHom (strictLocalizationMap_id C.weakEquivalences)
  map_comp F G := congrArg Functor.toCatHom (strictLocalizationMap_comp F G)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
