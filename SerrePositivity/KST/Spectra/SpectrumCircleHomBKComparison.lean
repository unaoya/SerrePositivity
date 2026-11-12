module

public import SerrePositivity.KST.Spectra.SpectrumPointLoopHomCoefficients
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：円 cotensor の元の Hom から、固定 cospan の元の Hom–BK end への比較。
方針：普遍評価、円の写像空間の BK 比較、中央固定の係数同型を合成する。
規約：この射の同値性だけでは元の円評価錐の極限性を主張しない。
使われ方：錐全体の比較族の制限と、実際の BF 比較辺を計算するための具体的な射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleHomBKSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleHomBKMappingKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance circleHomBKPointKan : KanComplex (Δ[0] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.isKanComplex
local instance circleHomBKZeroCoefficientKan (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    KanComplex ((loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).obj i) := by
  rcases i with ⟨i⟩
  cases i with
  | none => exact RawSpectrumMapping.pointedSpace_kanComplex X Y.toKanSequence
  | some i => cases i <;> change KanComplex (Δ[0] : SSet.{u}) <;> infer_instance
local instance circleHomBKZeroEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (loopCoefficient
      (RawSpectrumMapping.pointedSpace X Y.toKanSequence))) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _
local instance circleHomBKActualEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 零係数の end を、固定図式の元の Hom–BK end へ戻す厳密な同型。 -/
def pointLoopHomBKEndIso (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence)) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor _).mapIso (pointLoopHomCoefficientIso X Y).symm

/-- 係数の同型で元の BK end へ戻しても、中央射影は元の中央射影を保つ。 -/
@[reassoc]
lemma pointLoopHomBKEndIso_central (X Y : OmegaSpectrum.{u}) :
    (pointLoopHomBKEndIso X Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence))
          (AsSmall.up.obj .one) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap _ (pointLoopHomCoefficientIso X Y).inv ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π]
  change _ ≫ (ihom _).map (𝟙 (mappingSpace X Y)) = _
  simp

/-- 元の Hom の円の写像空間から、固定図式の元の Hom–BK end への指定した射。 -/
def pointLoopCircleHomComparison (X Y : OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).right ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) :=
  loopCircleBKComparison _ ≫ (pointLoopHomBKEndIso X Y).hom

/-- 指定した円の写像空間からの比較は、実際の単体的ホモトピー同値。 -/
lemma pointLoopCircleHomComparison_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (pointLoopCircleHomComparison X Y) :=
  (loopCircleBKComparison_homotopyEquivalence _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (pointLoopHomBKEndIso X Y).hom)

/-- 元の BF cotensor 比較を経由する、固定 Hom–BK end への実際の比較射。 -/
def circleCotensorHomBKComparison (X Y : OmegaSpectrum.{u}) :
    mappingSpace X (cotensor PointedSimplicialSet.circle Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) :=
  (cotensorMappingEquivalence X Y PointedSimplicialSet.circle).hom ≫
    pointLoopCircleHomComparison X Y

/-- cotensor の元の Hom から元の BK end への比較は、実際のホモトピー同値。 -/
lemma circleCotensorHomBKComparison_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (circleCotensorHomBKComparison X Y) :=
  (cotensorMappingComparison_homotopyEquivalence X Y PointedSimplicialSet.circle).comp
    (pointLoopCircleHomComparison_homotopyEquivalence X Y)

/-- 比較は、元の普遍評価への全 Hom 前合成を用いる射そのもの。 -/
lemma circleCotensorHomBKComparison_evaluation (X Y : OmegaSpectrum.{u}) :
    circleCotensorHomBKComparison X Y =
      (cotensorEvaluationPrecomposition X Y PointedSimplicialSet.circle).right ≫
        pointLoopCircleHomComparison X Y := by
  rw [cotensorEvaluationPrecomposition_eq, cotensorPointedMappingComparison_right]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
