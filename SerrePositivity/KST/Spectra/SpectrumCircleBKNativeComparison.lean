module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKReflectedFamilies
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeEndPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralHomHolimComparison

/-!
概要：元の円評価の反転 BK 点への前合成を、固定図式の coherent な切断へ送る比較族。
方針：実際の反転 Hom 比較族と、共有の反転 end の切断比較を合成する。
規約：選択した点・元の図式・全 Hom の族を保持する。使われ方：円 cotensor 錐の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleNativeComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleNativeComparisonHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance circleNativeComparisonCoefficientKan (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    KanComplex ((simplicialHomDiagram (pointLoopDiagram Y) X ⋙ SSet.opFunctor).obj i) :=
  inferInstanceAs (KanComplex (mappingSpace X ((pointLoopDiagram Y).obj i)).op)
local instance circleNativeComparisonEndKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram (pointLoopDiagram Y) X ⋙
      SSet.opFunctor)) := bousfieldKanHolim_kanComplex _

/-- 反転 Hom のパラメーターへ、元の反転 BK 切断点を添える射。 -/
def circleBKReflectedPointParameter (X Y : OmegaSpectrum.{u}) :
    (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op ⟶
      bousfieldKanHolim (simplicialHomDiagram (pointLoopDiagram Y)
        (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor) ⊗
          (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op :=
  ParameterPoint.family (circleBKReflectedEndPointMap Y)
    (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op

/-- 元の反転 Hom 全体から、元の固定図式上の coherent な切断への実際の比較族。 -/
def circleBKNativeConeComparison (X Y : OmegaSpectrum.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram (pointLoopDiagram Y))
        (coherentNerveVertex X) :=
  (SSet.uliftFunctor.{u + 1, u}).map (circleBKReflectedEndFamily X Y) ≫
    reflectedHomHolimConeComparison (pointLoopDiagram Y) X

/-- 元の点から構成した、coherent な切断への全 Hom 比較族は実際のホモトピー同値。 -/
lemma circleBKNativeConeComparison_homotopyEquivalence (X Y : OmegaSpectrum.{u}) :
    IsSimplicialHomotopyEquivalence (circleBKNativeConeComparison X Y) :=
  (DoldKanComparison.ulift_homotopyEquivalence.{u, u + 1}
    (circleBKReflectedEndFamily_homotopyEquivalence X Y)).comp
      (reflectedHomHolimConeComparison_cospan_homotopyEquivalence (pointLoopDiagram Y) X)

/-- 比較族の全 Hom 評価は、元の反転 BK 点に対する weighted な前合成そのもの。 -/
lemma circleBKNativeConeComparison_uncurry (X Y : OmegaSpectrum.{u}) :
    relativeFunctorUncurry (circleBKNativeConeComparison X Y) =
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)) ◁
        (SSet.uliftFunctor.{u + 1, u}).map (circleBKReflectedPointParameter X Y)) ≫
      (uliftTensorIso (nerve (AsSmall.{u} WalkingCospan))
        (bousfieldKanHolim (simplicialHomDiagram (pointLoopDiagram Y)
          (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor) ⊗
            (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((α_ (nerve (AsSmall.{u} WalkingCospan))
          (bousfieldKanHolim (simplicialHomDiagram (pointLoopDiagram Y)
            (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor))
          (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op).inv ≫
        (bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram (pointLoopDiagram Y)
          (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor) ▷
            (mappingSpace X (cotensor PointedSimplicialSet.circle Y)).op)) ≫
      (uliftTensorIso _ _).hom ≫
        weightedCoslicePrecompositionFamily (pointLoopDiagram Y) X
          (cotensor PointedSimplicialSet.circle Y) := by
  rw [circleBKNativeConeComparison, circleBKReflectedEndFamily,
    Functor.map_comp, Category.assoc, HomotopyLimits.relativeFunctorUncurry_parameter,
    reflectedHomHolimConeComparison_precomposition_uncurry,
    weightedCosliceEndPrecompositionEvaluation_eq_family]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
