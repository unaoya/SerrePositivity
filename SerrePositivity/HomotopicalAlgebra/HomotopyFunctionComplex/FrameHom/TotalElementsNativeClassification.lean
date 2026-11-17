module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanElementsFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsClassification
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.NerveHomUniverseIso

/-!
概要：元の全係数と元の全要素圏のnative分類を、同じ単位とaugmentationで比較する。
方針：Homの持ち上げの全自然同型を外し、元の全要素augmentationの比較を合成する。
規約：底全体のFunctorIsoであり、固定始域のroofとの等式は別に確認する。
使われ方：全source frameの同じ係数からnativeな全分類への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ全要素nerveのHomの宇宙持ち上げを、全係数で自然に戻す。 -/
def totalElementsNerveCoefficientIso :
    simplicialElementsCatDiagram F ⋙ nerveFunctor ≅ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F :=
  NatIso.ofComponents (fun i => nerveHomUniverseIso (F.obj i).Elements)
    (fun {i _j} f => nerveHomUniverseIso_naturality (F.obj i).Elements (F.map f).mapElements)

/-- 同じ全nerveの宇宙比較を、Kan係数の全関手同型へ送る。 -/
def totalElementsNerveCoefficientKanIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (simplicialElementsCatDiagram F ⋙ nerveFunctor))
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F)) := by
  let e := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.totalElementsNerveCoefficientIso F
  have : ∀ i, Quasicategory ((simplicialElementsCatDiagram F ⋙ nerveFunctor).obj i) :=
    fun i => by
      change Quasicategory (nerve (ULiftHom.{u} (F.obj i).Elements))
      infer_instance
  have : ∀ i, Quasicategory ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elements)
      infer_instance
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (simplicialElementsCatDiagram F ⋙ nerveFunctor), trivial⟩)
    (G := ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsNerveDiagram F), trivial⟩)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap e.hom)
    (fun i => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyMap_isQCatEquivalence e.hom
      (fun i => (qCatEquivalenceOfIso (e.app i)).isQCatEquivalence.isWeakHomotopyEquivalence) i)

/-- 元の全係数を、同じ全要素圏の元の置換のnative全分類へつなぐ。 -/
def totalElementsNativeClassificationIso :
    FunctorIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyCoherent F)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.simplexElementsKanAugmentationIso F).symm.trans
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.totalElementsNerveCoefficientKanIso F).symm.trans
      (simplicialElementsNativeClassificationUnitIso F))
end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
