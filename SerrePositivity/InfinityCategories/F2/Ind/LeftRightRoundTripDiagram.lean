module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionRightDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictCoherentNatTransComponent

/-!
概要：left/right 二重反転を、元の全通常図式上の自然な底上の比較として回収する。
方針：二重反転の標準同型の自然性を底上の射に移し、同じ成分の coherent 円柱を取る。
規約：個々の値の同値だけで代用せず、元の全添字の作用を保つ。
使われ方：共同 left 分類を、元の strict right 分類像へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ LeftFibrationObject B.op)

/-- 元の全添字を動かす、底上の二重反転から元の図式への同じ標準比較。 -/
def leftRightRoundTripDiagram :
    (F ⋙ leftFibrationOppositeRightOrdinary B) ⋙ rightFibrationOppositeOrdinary B ⟶ F where
  app i := Over.homMk (SSet.opFunctorCompOpFunctorIso.app (F.obj i).val.left).hom
    (rightFibrationOppositeRoundTrip_projection (F.obj i))
  naturality i j f := by
    apply Over.OverMorphism.ext
    exact SSet.opFunctorCompOpFunctorIso.hom.naturality (F.map f).left

/-- 同じ底上の二重反転比較を実現した、元の全図式上の関手同型。 -/
def leftRightRoundTripDiagramIso [Quasicategory B] :
    FunctorIso
      (HomotopyLimits.strictCoherentDiagram
        ((F ⋙ leftFibrationOppositeRightOrdinary B) ⋙ rightFibrationOppositeOrdinary B))
      (HomotopyLimits.strictCoherentDiagram F) := by
  apply F2.strictCoherentNatTransIso (leftRightRoundTripDiagram F)
  intro i
  exact leftFibrationInfinityEdge_isInvertible_of_precompositionEquivalence
    (((F ⋙ leftFibrationOppositeRightOrdinary B) ⋙ rightFibrationOppositeOrdinary B).obj i).val.hom
    (F.obj i).val.hom
    (SSet.opFunctorCompOpFunctorIso.app (F.obj i).val.left).hom
    (rightFibrationOppositeRoundTrip_projection (F.obj i))
    (isPrecompositionEquivalence_of_iso (SSet.opFunctorCompOpFunctorIso.app (F.obj i).val.left))

/-- 実際の反転写像で戻した right 図式は、元の left 図式そのものと全高次で同型。 -/
def leftRightOppositeDiagramIso [Quasicategory B] :
    FunctorIso
      (HomotopyLimits.strictCoherentDiagram (F ⋙ leftFibrationOppositeRightOrdinary B) ≫
        rightFibrationOppositeInfinityMap B)
      (HomotopyLimits.strictCoherentDiagram F) :=
  strictRightFibrationOppositeDiagramIso (F ⋙ leftFibrationOppositeRightOrdinary B) ≪≫
    leftRightRoundTripDiagramIso F

end SerrePositivity.InfinityCategories.F2.Ind
