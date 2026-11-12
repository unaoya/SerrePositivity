module

public import SerrePositivity.KST.Spectra.SpectrumCircleHomBKCentral
public import SerrePositivity.KST.Spectra.PointedUnitMappingFamily

/-!
概要：元の cotensor 恒等射の像として、固定 cospan の BK end の切断点を構成する。
方針：点つき単位の通常の成分を BF 恒等射に照合し、元の普遍評価の curry' を回収する。
規約：切断点と全パラメーターの族を元の比較射から取る。使われ方：円評価錐の weighted 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleEndPointSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 点つき恒等射の非基点側の成分は、元の BF 写像空間の恒等射を表す射。 -/
lemma rawPointedIdentity_underlying (X : OmegaSpectrum.{u}) :
    PointedSimplicialSet.unitUnderlyingHom (RawSpectrumMapping.pointedSpace X X.toKanSequence)
        (RawSpectrumMapping.pointedIdentity X) = mappingIdentity X := by
  apply (SSet.unitHomEquiv _).injective
  rw [PointedSimplicialSet.unitUnderlyingHom_vertex, RawSpectrumMapping.pointedIdentity,
    Equiv.apply_symm_apply]
  rfl

/-- 元の円の普遍評価が表す、円の基点付き写像空間の点の射。 -/
def circleEvaluationLoopPointMap (Y : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (RawSpectrumMapping.pointedSpace
      (cotensor PointedSimplicialSet.circle Y) Y.toKanSequence)).right :=
  PointedSimplicialSet.unitUnderlyingHom _
    (curry' (cotensorEvaluation PointedSimplicialSet.circle Y))

/-- 元の恒等射の cotensor 比較の像は、元の普遍評価の点そのもの。 -/
lemma circleEvaluationLoopPointMap_eq (Y : OmegaSpectrum.{u}) :
    circleEvaluationLoopPointMap Y = mappingIdentity (cotensor PointedSimplicialSet.circle Y) ≫
      (cotensorMappingEquivalence (cotensor PointedSimplicialSet.circle Y) Y
        PointedSimplicialSet.circle).hom := by
  rw [circleEvaluationLoopPointMap, curry'_cotensorEvaluation,
    PointedMapping.unitUnderlyingHom_post, rawPointedIdentity_underlying,
    cotensorPointedMappingComparison_right]

/-- 普遍評価の点の Hom の包含への像は、元の普遍評価の基礎射の curry'。 -/
lemma circleEvaluationLoopPointMap_ι (Y : OmegaSpectrum.{u}) :
    circleEvaluationLoopPointMap Y ≫ PointedObject.basedHomι PointedSimplicialSet.circle
        (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle Y)
          Y.toKanSequence) = curry' (cotensorEvaluation PointedSimplicialSet.circle Y).right :=
  PointedMapping.unitUnderlyingHom_curry'_ι _

/-- 元の cotensor の恒等射を元の Hom–BK 比較で送った、BK 切断点の射。 -/
def circleBKEndPointMap (Y : OmegaSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y)) :=
  mappingIdentity (cotensor PointedSimplicialSet.circle Y) ≫
    circleCotensorHomBKComparison (cotensor PointedSimplicialSet.circle Y) Y

/-- 同じ切断点を、元の BK end の実際の零単体として表示する。 -/
def circleBKEndPoint (Y : OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y))) _⦋0⦌ :=
  SSet.unitHomEquiv _ (circleBKEndPointMap Y)

/-- 切断点は、元の普遍評価の点に指定した円–BK 比較を作用させたもの。 -/
lemma circleBKEndPointMap_factor (Y : OmegaSpectrum.{u}) :
    circleBKEndPointMap Y = circleEvaluationLoopPointMap Y ≫
      pointLoopCircleHomComparison (cotensor PointedSimplicialSet.circle Y) Y := by
  rw [circleEvaluationLoopPointMap_eq, circleBKEndPointMap, circleCotensorHomBKComparison,
    Category.assoc]

/-- BK 切断点の中央は、元の普遍評価を指定した円パラメーターで制限した点。 -/
lemma circleBKEndPointMap_central (Y : OmegaSpectrum.{u}) :
    circleBKEndPointMap Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) (cotensor PointedSimplicialSet.circle Y))
          (AsSmall.up.obj .one) =
      curry' (circleBKParameter.{u} ≫
        (cotensorEvaluation PointedSimplicialSet.circle Y).right) := by
  rw [circleBKEndPointMap_factor, Category.assoc, pointLoopCircleHomComparison_central,
    ← Category.assoc, circleEvaluationLoopPointMap_ι]
  simp only [MonoidalClosed.curry']
  erw [curry_pre_app]
  rw [← Category.assoc, rightUnitor_naturality, Category.assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum
