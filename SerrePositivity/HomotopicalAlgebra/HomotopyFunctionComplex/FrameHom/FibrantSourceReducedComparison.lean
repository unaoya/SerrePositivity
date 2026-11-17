module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanNormalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveULiftHom
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionLeftRoof
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowEquivalence
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowReducedWeakComparison

/-!
概要：fibrant 標的への元の source frame 比較を同じ reduced hammock へ接続する。
方針：全要素圏の宇宙同型、同じ三本矢の包含と正規化を合成する。
規約：元の二列の射と全単体作用素を保持する。
使われ方：bifibrant 部分圏での実 right Kan 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X) (Y : C)

/-- 概要：同じ全単体の Hom だけの持ち上げを AsSmall 表示へ送る実同型。
方針：両方を元の nerve の単体の持ち上げと同定する。
規約：同じ全単体を保つ。使われ方：元の比較射への弱同値性の輸送。 -/
def frameElementSmallIso :
    nerve (ULiftHom.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ≅
      nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom.iso _ ≪≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveAsSmall.iso _).symm

/-- 概要：宇宙同型の後の元の三本矢比較は同じ既存の比較射。
方針：全射列で up の後の down を評価する。
規約：実射の等式。使われ方：既存の二列正規化との接続。 -/
lemma frameElementSmallIso_comparison :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSmallIso q Y).hom ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanNormalization.comparisonNerveMap q Y =
        _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
          q.obj q.augmentation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q)
          (𝟙 Y) ((trivialCofibrations C).id_mem Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  rfl

variable [IsFibrant Y]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

include r in
/-- 概要：元の source frame の同じ三本矢比較射は弱ホモトピー同値。
方針：AsSmall 表示の弱比較を同じ実宇宙同型で前合成する。
規約：標的の fibrancy のみ。使われ方：元の二列比較の弱同値性。 -/
lemma frameElementSpanNerveMap_isWeakHomotopyEquivalence_of_fibrant :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameElementSpanNerveMap (trivialFibrations C) (trivialCofibrations C)
        q.obj q.augmentation (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionAugmentation_trivialFibration q)
        (𝟙 Y) ((trivialCofibrations C).id_mem Y)) := by
  rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSmallIso_comparison]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSmallIso q Y).hom
    (by infer_instance)).comp
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanNormalization.comparisonNerveMap_isWeakHomotopyEquivalence q Y r)

variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

include r cof fib in
/-- 概要：元の二列から reduced hammock への正規化された frame 比較は弱同値。
方針：同じ恒等右脚挿入の照合と三本矢の全比較を合成する。
規約：両関手的分解を明示し、単体集合のモデル構造は使わない。
使われ方：元の frame の全屋根比較の導来不変性。 -/
lemma resolutionLeftRoofNerveMap_normalized_isWeakHomotopyEquivalence_of_fibrant :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap q Y ≫
      graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionLeftRoofNerveMap_normalization]
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.nerveMap_localized_isIso X Y)
  simpa only [Category.assoc] using
    (((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpanNerveMap_isWeakHomotopyEquivalence_of_fibrant q Y r).comp
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialThreeArrowComparison.inclusion_isWeakHomotopyEquivalence cof fib X Y)).comp ht).comp
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowNormalization_isWeakHomotopyEquivalence X Y cof)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
