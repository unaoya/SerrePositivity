module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsBaseChange
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.TargetReconstruction

/-!
概要：元の twisted arrow の復元を、全空間の終点パラメータ全体へ制限する。
方針：共同 Hom の底変換表示と、元の復元射の底変換を合成する。
規約：分類図式は同じ元の共同 Hom を制限したもの。各点ごとに選び直さない。
使われ方：密度の大域評価を c1 の相対写像空間へ移す前合成同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C)

local instance : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)

/-- 元の共同 Hom を、全ての指定終点へ制限した図式。 -/
def twistedElementsHomDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (C.op ⊗ E) ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (twistedElementsBaseMap p) ≫ twistedArrowHomInfinity C

/-- 同じ制限図式の unstraightening の厳密な底変換表示。 -/
def twistedElementsUnstraighteningIso : smallLeftUnstraightening (twistedElementsHomDiagram p) ≅
    pullback (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (twistedElementsBaseMap p) :=
  smallLeftUnstraighteningBaseChangeIso (twistedArrowHomInfinity C) (twistedElementsBaseMap p)

/-- 元の復元射を終点パラメータ全体で制限した比較。 -/
def twistedElementsReconstruction : pullback (edgewiseRight C) p ⟶
    smallLeftUnstraightening (twistedElementsHomDiagram p) :=
  (twistedElementsBaseChangeIso p).hom ≫
    fiberComparisonBaseChange (twistedArrowProjection C)
      (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
      (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))
      (twistedElementsBaseMap p) ≫ (twistedElementsUnstraighteningIso p).inv

/-- 元の共同射影を、同じ全パラメータにわたり厳密に保つ。 -/
lemma twistedElementsReconstruction_projection :
    twistedElementsReconstruction p ≫ smallLeftUnstraighteningProjection
      (twistedElementsHomDiagram p) = twistedElementsProjection p := by
  have h := (smallLeftUnstraighteningMap_isPullback
    (twistedElementsHomDiagram p) (twistedArrowHomInfinity C)
    (twistedElementsBaseMap p) rfl).isoPullback_inv_snd
  rw [twistedElementsReconstruction, Category.assoc, Category.assoc,
    show (twistedElementsUnstraighteningIso p).inv ≫
      smallLeftUnstraighteningProjection (twistedElementsHomDiagram p) = _ from h,
    fiberComparisonBaseChange_projection, twistedElementsBaseChangeIso_projection]

/-- 同じ復元射の全族の比較は、前合成同値。 -/
lemma twistedElementsReconstruction_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (twistedElementsReconstruction p) :=
  (isPrecompositionEquivalence_of_iso (twistedElementsBaseChangeIso p)).comp
    ((fiberComparisonBaseChange_isPrecompositionEquivalence (twistedArrowProjection C)
      (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
      (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))
      (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
        (twistedArrowProjection C)) (twistedElementsBaseMap p)).comp
      (isPrecompositionEquivalence_of_iso (twistedElementsUnstraighteningIso p).symm))

end SerrePositivity.InfinityCategories.F2.Ind
