module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitHomEndFamily

/-!
概要：元の共通解像の点と反転 end の点で固定した、全 Hom パラメータの前合成族。
方針：点を固定する族の自然性と、左右の end 射影・点の厳密な可換式を合成する。
規約：選んだ切断の源自然性を仮定しない。使われ方：左右射影を通した比較族の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance edgewiseFamiliesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I]

/-- 元の共通解像の点に前合成して得る、edgewise Hom 全体の比較族。 -/
def homotopyLimitEdgewiseEndFamily (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (mappingSpace X (homotopyLimit D)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (homotopyLimitEdgewiseEndPointMap D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (mappingSpace X (homotopyLimit D))) ≫
      edgewiseHomEndPrecomposition D X (homotopyLimit D)

/-- 元の反転 end の点に前合成して得る、反転 Hom 全体の比較族。 -/
def homotopyLimitReflectedEndFamily (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    (mappingSpace X (homotopyLimit D)).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X ⋙ SSet.opFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (homotopyLimitReflectedEndPointMap D)
    (mappingSpace X (homotopyLimit D)).op ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConeEndPrecomposition D X (homotopyLimit D)

/-- 共通解像の比較族を右射影すると、元の恒等射の像の比較族になる。 -/
lemma homotopyLimitEdgewiseEndFamily_right (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    homotopyLimitEdgewiseEndFamily D X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (mappingSpace X (homotopyLimit D)) ≫ homotopyLimitHomEndFamily D X := by
  dsimp only [homotopyLimitEdgewiseEndFamily, homotopyLimitHomEndFamily]
  rw [Category.assoc, ← edgewiseHomEndPrecomposition_right, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality, homotopyLimitEdgewiseEndPointMap_right, Category.assoc]
  rfl

/-- 共通解像の比較族を左射影すると、元の反転 end の点の比較族になる。 -/
lemma homotopyLimitEdgewiseEndFamily_left (D : I ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    homotopyLimitEdgewiseEndFamily D X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram D X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (mappingSpace X (homotopyLimit D)) ≫ homotopyLimitReflectedEndFamily D X := by
  dsimp only [homotopyLimitEdgewiseEndFamily, homotopyLimitReflectedEndFamily]
  rw [Category.assoc, ← edgewiseHomEndPrecomposition_left, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality, homotopyLimitEdgewiseEndPointMap_left, Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
