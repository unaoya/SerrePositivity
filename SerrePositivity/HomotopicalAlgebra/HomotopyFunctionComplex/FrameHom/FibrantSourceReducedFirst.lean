module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPostcompose
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowRightReplacementOfFirst

/-!
概要：元の source frame から hammock への比較の第二分解入力を除く。
方針：弱な右脚の第一分解による特殊三本矢比較を代入する。
規約：同じ元の二列比較射と全単体を保持する。
使われ方：採用済みの第一関手的分解だけによる一般モデル圏の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 概要：元の source frame の二列比較を同じ hammock 余極限へ送る。
方針：同じ augmentation・全作用素・元の標準射を使う。
規約：定義上の同じ射。使われ方：bifibrant frame の包含像との照合。 -/
def resolutionLeftRoofColimitMap :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (weakEquivalences C) q.obj q.augmentation
    q.augmentation_weakEquivalence (fun f => q.homotopicallyConstant f) (Y := Y)

variable [IsFibrant Y]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include r cof in
/-- 概要：元の source frame の正規化された二列比較は第一分解だけで弱同値。
方針：同じ特殊三本矢の比較に第一分解による包含の反転性を合成する。
規約：第二分解を仮定しない。使われ方：元の全 frame 比較。 -/
lemma resolutionLeftRoofNerveMap_normalized_isWeakHomotopyEquivalence_of_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap q Y ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap_normalization]
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.nerveMap_localized_isIso X Y)
  simpa only [Category.assoc] using
    (((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpanNerveMap_isWeakHomotopyEquivalence_of_fibrant q Y r).comp
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.inclusion_isWeakHomotopyEquivalence_of_first cof X Y)).comp ht).comp
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowNormalization_isWeakHomotopyEquivalence X Y cof)

include r cof in
/-- 概要：元の source frame の同じ hammock 余極限への比較は弱同値。
方針：同じ reduced 比較と元の縮約同型を消去する。
規約：第一分解と指定 right frame のみ。使われ方：元の実屋根比較への復帰。 -/
lemma resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap q Y) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (weakEquivalences C) X Y).hom :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  apply hi.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap q Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (weakEquivalences C) X Y).hom)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofNerveMap_normalized_isWeakHomotopyEquivalence_of_first q Y r cof

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
