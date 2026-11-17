module
public import SerrePositivity.EInfinity.FrameHom.KanElementsFamily
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
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})

/-- 同じ全要素nerveのHomの宇宙持ち上げを、全係数で自然に戻す。 -/
def totalElementsNerveCoefficientIso :
    simplicialElementsCatDiagram F ⋙ nerveFunctor ≅ simplexElementsNerveDiagram F :=
  NatIso.ofComponents (fun i => nerveHomUniverseIso (F.obj i).Elements)
    (fun {i _j} f => nerveHomUniverseIso_naturality (F.obj i).Elements (F.map f).mapElements)

/-- 同じ全nerveの宇宙比較を、Kan係数の全関手同型へ送る。 -/
def totalElementsNerveCoefficientKanIso :
    FunctorIso (kanHomFamilyCoherent (simplicialElementsCatDiagram F ⋙ nerveFunctor))
      (kanHomFamilyCoherent (simplexElementsNerveDiagram F)) := by
  let e := totalElementsNerveCoefficientIso F
  have : ∀ i, Quasicategory ((simplicialElementsCatDiagram F ⋙ nerveFunctor).obj i) :=
    fun i => by
      change Quasicategory (nerve (ULiftHom.{u} (F.obj i).Elements))
      infer_instance
  have : ∀ i, Quasicategory ((simplexElementsNerveDiagram F).obj i) :=
    fun i => by
      change Quasicategory (nerve (F.obj i).Elements)
      infer_instance
  exact kanDiagramFunctorIsoOfPointwise
    (F := ⟨kanHomFamily (simplicialElementsCatDiagram F ⋙ nerveFunctor), trivial⟩)
    (G := ⟨kanHomFamily (simplexElementsNerveDiagram F), trivial⟩)
    (kanHomFamilyMap e.hom)
    (fun i => kanHomFamilyMap_isQCatEquivalence e.hom
      (fun i => (qCatEquivalenceOfIso (e.app i)).isQCatEquivalence.isWeakHomotopyEquivalence) i)

/-- 元の全係数を、同じ全要素圏の元の置換のnative全分類へつなぐ。 -/
def totalElementsNativeClassificationIso :
    FunctorIso (kanHomFamilyCoherent F)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom) :=
  (simplexElementsKanAugmentationIso F).symm.trans
    ((totalElementsNerveCoefficientKanIso F).symm.trans
      (simplicialElementsNativeClassificationUnitIso F))
end SerrePositivity.EInfinity.FrameHom
