module

public import SerrePositivity.EInfinity.SimplicialLocalization.RelativeHammockNerveEquivalence
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelCofibrantHammockWeak

/-!
概要：同じ bifibrant・cofibrant・全圏の実 hammock 比較を全 coherent nerve の同値へ上げる。
方針：元の全 Hom の弱比較と同じ弱単位または余単位を使う。
規約：全圏との比較には第一の関手的分解を明示する。
使われ方：bifibrant 中継から指定された全圏の局所化へ戻る比較。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ bifibrant 化は全 hammock coherent nerve の同値を与える。
方針：元の全 Hom 弱比較と元の bifibrant 側の弱単位を代入する。
規約：同じ right frame の次数零。使われ方：bifibrant 中継への移行。 -/
lemma modelCofibrantToBifibrant_nerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeKanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r)) :=
  relativeKanHammockNerve_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r) _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantCofibrantUnit r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantCofibrantUnit_weak r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrant_colimitMap_weak r)

include r in
/-- 概要：同じ bifibrant 包含は全 hammock coherent nerve の同値を与える。
方針：元の全 Hom 弱比較と元の cofibrant 側の弱単位を使う。
規約：元の包含自身。使われ方：cofibrant 局所化への復帰。 -/
lemma modelBifibrantToCofibrant_nerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeKanHammockNerve
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative (C := C))) :=
  relativeKanHammockNerve_isQCatEquivalence
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrantRelative (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToBifibrantRelative r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantBifibrantUnit r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantBifibrantUnit_weak r)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantToCofibrant_colimitMap_weak r)

variable (C)
  [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)]

/-- 概要：元の cofibrant 包含は全圏の hammock coherent nerve と同値。
方針：同じ関手的置換と弱余単位を全 nerve の判定に渡す。
規約：第一の関手的分解を明示する。使われ方：全圏の指定局所化への復帰。 -/
lemma modelCofibrantToModel_nerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeKanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C)) :=
  relativeKanHammockNerve_isQCatEquivalence_of_counit
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantCounit_weak C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModel_colimitMap_weak C)

/-- 概要：元の全圏からの cofibrant 置換も全 hammock coherent nerve の同値。
方針：同じ包含を逆候補にし、元のもう一方の弱余単位を使う。
規約：同じ全図式比較。使われ方：全圏から cofibrant 模型への移行。 -/
lemma modelToCofibrant_nerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (relativeKanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C)) :=
  relativeKanHammockNerve_isQCatEquivalence_of_counit
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrantRelative C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelCofibrantToModelRelative C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.cofibrantModelSmallCounit_weak C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelToCofibrant_colimitMap_weak C)

end SerrePositivity.EInfinity.SimplicialLocalization
