module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKHomFamily
public import SerrePositivity.KST.Spectra.BousfieldKanEdgewiseEndLift

/-!
概要：元の円評価の BK 切断点を共通 edgewise 解像へ持ち上げ、反転した係数へ送る。
方針：右射影の自明 Kan fibration の切断を使い、左射影で反転した切断点を得る。
規約：右射影は元の恒等射の比較像を厳密に保つ。使われ方：実際の coherent な円評価錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleReflectedPointSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleReflectedPointHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の円 cotensor の恒等射の像を、共通解像へ持ち上げた点の射。 -/
def circleBKEdgewiseEndPointMap (Y : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :=
  circleBKEndPointMap Y ≫ edgewiseEndRightSection _

/-- 持ち上げた点の右射影は、元の恒等射の比較像そのもの。 -/
lemma circleBKEdgewiseEndPointMap_right (Y : OmegaSpectrum.{u}) :
    circleBKEdgewiseEndPointMap Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
          (cotensor PointedSimplicialSet.circle Y))) = circleBKEndPointMap Y := by
  rw [circleBKEdgewiseEndPointMap, Category.assoc, edgewiseEndRightSection_projection,
    Category.comp_id]

/-- 左射影で得られる、反転した元の Hom 係数の切断点の射。 -/
def circleBKReflectedEndPointMap (Y : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor) :=
  circleBKEdgewiseEndPointMap Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y)))

/-- 元の反転切断点の、共通解像の左射影による厳密な式。 -/
lemma circleBKEdgewiseEndPointMap_left (Y : OmegaSpectrum.{u}) :
    circleBKEdgewiseEndPointMap Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
          (cotensor PointedSimplicialSet.circle Y))) = circleBKReflectedEndPointMap Y := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
