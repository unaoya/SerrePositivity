module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKReflectedPoints
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitReflectedFamilyEquivalence

/-!
概要：元の円評価の切断点から得る、共通解像と反転 Hom の全パラメーター比較族。
方針：左右の射影で元の非反転比較と可換にし、同値の二対三で反転比較へ移す。
規約：元の切断点と元の前合成作用を用いる。使われ方：cotensor を頂点とする実際の ∞ 極限錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleReflectedFamilySimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleReflectedFamilyHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance circleReflectedFamilyCoefficientKan (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X).obj i) :=
  mappingSpace_kanComplex X ((pointLoopDiagram Y).obj i)
local instance circleReflectedFamilyEdgewiseCoefficientKan (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor).obj i) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (mappingSpace X ((pointLoopDiagram Y).obj i))))
local instance circleReflectedFamilyOppositeCoefficientKan (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙ SSet.opFunctor).obj i) :=
  inferInstanceAs (KanComplex (mappingSpace X ((pointLoopDiagram Y).obj i)).op)
local instance circleReflectedFamilyEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _
local instance circleReflectedFamilyEdgewiseEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _
local instance circleReflectedFamilyOppositeEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙
      SSet.opFunctor)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 共通解像の元の切断点に、edgewise Hom の全パラメーターで前合成した族。 -/
def circleBKEdgewiseEndFamily (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (circleBKEdgewiseEndPointMap Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (mappingSpace X (cotensor PointedSimplicialSet.circle Y))) ≫
      edgewiseHomEndPrecomposition (pointLoopDiagram Y) X (cotensor PointedSimplicialSet.circle Y)

/-- 元の反転切断点に、反転 Hom の全パラメーターで前合成した族。 -/
def circleBKReflectedEndFamily (X Y : OmegaSpectrum.{u}) :
    (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ⋙ SSet.opFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (circleBKReflectedEndPointMap Y)
    (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedConeEndPrecomposition (pointLoopDiagram Y) X (cotensor PointedSimplicialSet.circle Y)

/-- 共通解像の比較族の右射影は、元の普遍評価による非反転比較へ厳密に可換。 -/
lemma circleBKEdgewiseEndFamily_right (X Y : OmegaSpectrum.{u}) :
    circleBKEdgewiseEndFamily X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseRight (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≫
        circleBKHomEndFamily X Y := by
  dsimp only [circleBKEdgewiseEndFamily, circleBKHomEndFamily]
  rw [Category.assoc, ← edgewiseHomEndPrecomposition_right, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality, circleBKEdgewiseEndPointMap_right, Category.assoc]
  rfl

/-- 共通解像の比較族の左射影は、同じ反転切断点の比較族へ厳密に可換。 -/
lemma circleBKEdgewiseEndFamily_left (X Y : OmegaSpectrum.{u}) :
    circleBKEdgewiseEndFamily X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≫
        circleBKReflectedEndFamily X Y := by
  dsimp only [circleBKEdgewiseEndFamily, circleBKReflectedEndFamily]
  rw [Category.assoc, ← edgewiseHomEndPrecomposition_left, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality, circleBKEdgewiseEndPointMap_left, Category.assoc]
  rfl

/-- 元の切断点から得た共通解像の全 Hom 比較族は、実際のホモトピー同値。 -/
lemma circleBKEdgewiseEndFamily_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (circleBKEdgewiseEndFamily X Y) := by
  have sourceTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (mappingSpace X (cotensor PointedSimplicialSet.circle Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration _
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (mappingSpace X (cotensor PointedSimplicialSet.circle Y)))
  have hs := hq.isSimplicialHomotopyEquivalence
  have h := hs.comp (circleBKHomEndFamily_homotopyEquivalence X Y)
  rw [← circleBKEdgewiseEndFamily_right] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanEdgewiseRight_homotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)).cancel_right h

/-- 元の反転切断点から得た全 Hom 比較族は、実際のホモトピー同値。 -/
lemma circleBKReflectedEndFamily_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (circleBKReflectedEndFamily X Y) := by
  have sourceTrivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (mappingSpace X (cotensor PointedSimplicialSet.circle Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_trivialKanFibration _
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (mappingSpace X (cotensor PointedSimplicialSet.circle Y)))
  have hs := hq.isSimplicialHomotopyEquivalence
  have h := (circleBKEdgewiseEndFamily_homotopyEquivalence X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanEdgewiseLeft_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X))
  rw [circleBKEdgewiseEndFamily_left] at h
  exact hs.cancel_left h

end SerrePositivity.KST.Spectra.OmegaSpectrum
