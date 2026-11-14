module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelCofibrantDeformation
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelBifibrantHammockWeak

/-!
概要：指定第一分解の同じ cofibrant 置換は全 C の hammock Hom と弱比較する。
方針：元の両側の比較自然変換を相対逆の一般判定へ渡す。
規約：関手的第一分解はこの補助入口の明示入力に残し、主定理から隠さない。
使われ方：実 dg モデルで bifibrant 中継を全 C の Hom と比較する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories
variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

/-- 概要：元の cofibrant 包含の全 C の hammock Hom 射は弱同値。
方針：同じ二つの実余単位を相対逆の判定へ渡す。
規約：同じ元の包含自身。使われ方：全 C の指定局所化への Hom 比較。 -/
lemma modelCofibrantToModel_colimitMap_weak
    (X Y : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory C).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.Hammock.Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C) X Y) :=
  _root_.SerrePositivity.EInfinity.Hammock.RelativeEquivalence.colimitMap_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit_weak C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit_weak C) X Y

/-- 概要：同じ全 C からの cofibrant 置換の Hom 射も弱同値。
方針：同じ両余単位を逆順に使う。
規約：元の置換関手自身。使われ方：同じ Hom 比較の逆側。 -/
lemma modelToCofibrant_colimitMap_weak
    (X Y : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.Hammock.Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C) X Y) :=
  _root_.SerrePositivity.EInfinity.Hammock.RelativeEquivalence.colimitMap_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit_weak C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit_weak C) X Y

variable {C} (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の bifibrant 相対圏から全 C への同じ相対包含。
方針：同じ二つの元の包含を合成する。
規約：底の射は元の同じ射。使われ方：bifibrant frame と全モデルの hammock。 -/
def modelBifibrantToModelRelative : LocalizerMorphism
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C).weakEquivalences :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative.comp (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C)

include r in
/-- 概要：元の bifibrant 包含の全モデル hammock Hom 射は弱同値。
方針：同じ二つの包含の実 Hom 比較を合成する。
規約：同じ元の相対包含自身。使われ方：元の bifibrant frame の弱比較。 -/
lemma modelBifibrantToModel_colimitMap_weak
    (X Y : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.Hammock.Relative.colimitMap modelBifibrantToModelRelative X Y) := by
  rw [modelBifibrantToModelRelative, _root_.SerrePositivity.EInfinity.Hammock.Relative.colimitMap_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrant_colimitMap_weak r X Y).comp
    (modelCofibrantToModel_colimitMap_weak C _ _)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
