module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelCofibrantRelative

/-!
概要：任意モデル圏の全対象と元の弱同値を同じ宇宙の相対圏に束ねる。
方針：対象と Hom の宇宙だけを AsSmall で揃える。
規約：元のモデル構造と全対象・全射を保持する。
使われ方：全 C の指定局所化と cofibrant・bifibrant 中継との接続。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra
variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- 概要：全モデル圏の対象と射の宇宙を揃える。
方針：元の圏の AsSmall 表示を使う。
規約：対象を制限しない。使われ方：全 C の局所化の底の圏。 -/
abbrev modelCategorySmall := AsSmall.{max u v} C

/-- 概要：同じ全モデル圏の相対圏。
方針：元の弱同値を同じ宇宙表示に引き戻す。
規約：元の全弱同値。使われ方：全 C の hammock 局所化。 -/
def modelRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{max u v} where
  category := Cat.of (modelCategorySmall C)
  weakEquivalences := (weakEquivalences C).inverseImage AsSmall.down
  isMultiplicative := inferInstance

/-- 概要：元の対象を同じ全相対圏に送る。
方針：対象の宇宙だけを揃える。
規約：元の対象を保つ。使われ方：指定局所化頂点の回収。 -/
def modelRelativeObject (X : C) : (modelRelativeCategory C).category := AsSmall.up.obj X

/-- 概要：元の cofibrant 相対圏から全相対圏への実包含。
方針：元の全部分圏の包含の前後で宇宙を揃える。
規約：元の全射。使われ方：全 C の指定局所化への比較。 -/
def modelCofibrantToModel : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).category ⥤
    (modelRelativeCategory C).category := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantInclusion C ⋙ AsSmall.up

/-- 概要：同じ実包含は元の弱同値を保つ相対関手。
方針：元の包含と同じ逆像の条件を読む。
規約：元の包含自身。使われ方：実 hammock Hom の比較。 -/
def modelCofibrantToModelRelative : LocalizerMorphism
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantRelativeCategory C).weakEquivalences
    (modelRelativeCategory C).weakEquivalences :=
  ⟨modelCofibrantToModel C, fun _ _ _ hf => hf⟩

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
