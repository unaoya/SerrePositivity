module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightStraighteningFiberDiagram
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationFiberNative
public import SerrePositivity.InfinityCategories.F1.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.F1.KanDiagramNaturalTransformation

/-!
概要：right straightening で評価される反転 fiber 図式は、元の fiber 図式の反転と自然同型。
方針：実際の fiber 反転同型を各段に取り、元の底上の射に対する自然性を確認する。
規約：各段の頂点だけでなく、元の通常の全図式の射を保つ。
使われ方：証明済みの strict fiber 余極限を前層の評価余極限へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 元の各 fiber の反転と、反転した射影の同じ fiber の図式の自然同型。 -/
def rightFibrationOppositeFiberDiagramIso (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    rightFibrationFiberKanDiagram F b ⋙ kanObjectOpFunctor ≅
      rightFibrationOppositeFiberDiagram F (SSet.opObjEquiv.symm b) :=
  NatIso.ofComponents (fun i => {
    hom := (vertexFiberOpIso (F.obj i).val.hom b).hom
    inv := (vertexFiberOpIso (F.obj i).val.hom b).inv
    hom_inv_id := (vertexFiberOpIso (F.obj i).val.hom b).hom_inv_id
    inv_hom_id := (vertexFiberOpIso (F.obj i).val.hom b).inv_hom_id }) (by
    intro i j f
    change SSet.opFunctor.map ((rightFibrationFiberDiagram F b).map f) ≫
      (vertexFiberOpIso (F.obj j).val.hom b).hom =
        (vertexFiberOpIso (F.obj i).val.hom b).hom ≫
          (coherentEnrichedUnderlyingFunctor
            (leftFibrationFiberEvaluationEnriched (SSet.opObjEquiv.symm b))).map
              ((rightFibrationOppositeOrdinary B).map (F.map f))
    rw [leftFiberEvaluation_underlying_map]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl)

/-- 元の right straightening の全評価図式を、元の right fiber 図式の反転へ直接比較する。 -/
def strictRightStraighteningOriginalFiberDiagramIso (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) :
    FunctorIso
      (HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap B ≫
        evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm b)))
      (kanDiagramCoherentNerve (rightFibrationFiberKanDiagram F b ⋙ kanObjectOpFunctor)) := by
  let e := rightFibrationOppositeFiberDiagramIso F b
  have he := kanDiagramFunctorIsoOfPointwise
    (F := ⟨rightFibrationFiberKanDiagram F b ⋙ kanObjectOpFunctor, trivial⟩)
    (G := ⟨rightFibrationOppositeFiberDiagram F (SSet.opObjEquiv.symm b), trivial⟩)
    (Functor.whiskerRight e.hom kanObjectForget)
    (fun i => (qCatEquivalenceOfIso (vertexFiberOpIso (F.obj i).val.hom b)).isQCatEquivalence)
  exact strictRightStraighteningFiberDiagramIso F (SSet.opObjEquiv.symm b) ≪≫ he.symm

end SerrePositivity.InfinityCategories.F2.Ind
