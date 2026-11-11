module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKSection
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationUnderlying
public import SerrePositivity.KST.Spectra.WeightedParameterPointEvaluation
public import SerrePositivity.KST.Spectra.EdgewiseHomEndPrecomposition

/-!
概要：元の BK 切断点の全 Hom 前合成族は、元の円 cotensor–BK 比較射と厳密に一致する。
方針：中央での係数の作用を計算し、両端の終対象性で元の end 全体へ戻す。
規約：別の同値を選ばない。使われ方：反転した切断点と実際の coherent 錐の極限判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleHomFamilySimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の恒等射の BK 切断点を、全 Hom パラメーターで前合成した族。 -/
def circleBKHomEndFamily (X Y : OmegaSpectrum.{u}) :
    mappingSpace X (cotensor PointedSimplicialSet.circle Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (circleBKEndPointMap Y)
    (mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≫
      homEndPrecomposition (pointLoopDiagram Y) X (cotensor PointedSimplicialSet.circle Y)

/-- 切断点で固定した族の中央は、元の普遍評価への元の豊穣合成。 -/
lemma circleBKHomEndFamily_central_uncurry (X Y : OmegaSpectrum.{u}) :
    uncurry (circleBKHomEndFamily X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one)) =
      (β_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj (AsSmall.up.obj .one))
        (mappingSpace X (cotensor PointedSimplicialSet.circle Y))).hom ≫
      mappingSpace X (cotensor PointedSimplicialSet.circle Y) ◁
        (circleBKParameter.{u} ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right) ≫
      mappingComposition X (cotensor PointedSimplicialSet.circle Y) Y := by
  rw [circleBKHomEndFamily, homEndPrecomposition,
    weightedSectionsParameterMap_point_evaluation, circleBKEndPointMap_central]
  simp only [MonoidalClosed.curry', uncurry_curry, Iso.inv_hom_id_assoc]
  change ((circleBKParameter.{u} ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right) ▷
      mappingSpace X (cotensor PointedSimplicialSet.circle Y)) ≫
    (β_ (mappingSpace (cotensor PointedSimplicialSet.circle Y) Y)
      (mappingSpace X (cotensor PointedSimplicialSet.circle Y))).hom ≫
      mappingComposition X (cotensor PointedSimplicialSet.circle Y) Y = _
  erw [BraidedCategory.braiding_naturality_left_assoc]

/-- 恒等射の BK 切断点への前合成族は、元の円 cotensor 比較の指定した順射そのもの。 -/
lemma circleBKHomEndFamily_eq (X Y : OmegaSpectrum.{u}) :
    circleBKHomEndFamily X Y = circleCotensorHomBKComparison X Y := by
  apply pointLoopHomEnd_hom_ext X Y
  apply uncurry_injective
  rw [circleBKHomEndFamily_central_uncurry, circleCotensorHomBKComparison_uncurry,
    cotensorEvaluationPrecomposition_underlying]
  rw [BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp_assoc]

/-- 元の BK 切断点から得た全 Hom 前合成族は、実際の単体的ホモトピー同値。 -/
lemma circleBKHomEndFamily_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (circleBKHomEndFamily X Y) := by
  rw [circleBKHomEndFamily_eq]
  exact circleCotensorHomBKComparison_homotopyEquivalence X Y

end SerrePositivity.KST.Spectra.OmegaSpectrum
