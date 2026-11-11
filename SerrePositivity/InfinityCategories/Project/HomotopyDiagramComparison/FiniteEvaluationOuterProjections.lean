module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFunctorEvaluationModel
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentProductProjectionFiber

/-!
概要：元の有限評価錐の恒等・最初の射影と、元の tail への snd を厳密に照合する。
方針：元の射影変換の全一単体を元の豊穣二項積の辺へ戻す。
規約：元の反復 Kan 積と元の全射影を変更しない。
使われ方：後続脚の合成三角形のホモトピーの帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の Kan 射は、元の coherent 辺の全一単体で一意に決まる。 -/
lemma kanHom_eq_of_coherentNerveEdge_eq {K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {f g : K ⟶ L}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge) : f = g := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g := SSet.Edge.ext h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge] using congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom he

/-- 元の恒等変換の辺の評価は、元の値の恒等 Kan 射の辺そのもの。 -/
lemma coherentIdentityTransformationVertex_evaluation {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentIdentityTransformationVertex F)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)))).edge := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentIdentityTransformationVertex F) =
      SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _
  rw [he]
  have hid : (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) 1 :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm
  rw [hid, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)) =
      F.app (Opposite.op ⦋0⦌) b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).trans
    (congrArg (fun v ↦ (SSet.Edge.id v).edge) hv.symm)

/-- 元の二項 fst 変換の評価は、元の二値の Kan 積の fst の辺そのもの。 -/
lemma coherentBinaryFst_evaluation {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorEnrichedFst.val
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b),
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (G.app (Opposite.op ⦋0⦌) b)))).edge := by
  rcases b with ⟨b⟩
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex_edgeAt F G b
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductFstVertex F G)).edge = _ at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (F.app (Opposite.op ⦋0⦌) (ULift.up b)),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (G.app (Opposite.op ⦋0⦌) (ULift.up b))] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductFstHomotopy_component _ _)

/-- 元の二項 snd 変換の評価は、元の二値の Kan 積の snd の辺そのもの。 -/
lemma coherentBinarySnd_evaluation {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorEnrichedSnd.val
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b),
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (G.app (Opposite.op ⦋0⦌) b)))).edge := by
  rcases b with ⟨b⟩
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex_edgeAt F G b
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex F G)).edge = _ at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (F.app (Opposite.op ⦋0⦌) (ULift.up b)),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (G.app (Opposite.op ⦋0⦌) (ULift.up b))] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductSndHomotopy_component _ _)

/-- 元の零段の評価脚は、元の一因子の恒等射そのもの。 -/
lemma finiteFunctorEvaluationKanLeg_zero {B : SSet.{u}}
    (F : Fin 1 → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg 0 F b (Discrete.mk (ULift.up 0)) =
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues 0 F b 0)) := by
  apply kanHom_eq_of_coherentNerveEdge_eq
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_edge]
  exact coherentIdentityTransformationVertex_evaluation (F 0) b

/-- 元の後続段の最初の評価脚は、元の反復積の fst そのもの。 -/
lemma finiteFunctorEvaluationKanLeg_first (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up 0)) =
      fst (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b 0).obj
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj := by
  apply kanHom_eq_of_coherentNerveEdge_eq
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorEvaluationKanLeg_edge]
  have h := coherentBinaryFst_evaluation (F 0)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun i ↦ F i.succ)) b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct_vertex n (fun i ↦ F i.succ) b] at h
  exact h

/-- 元の tail への射影辺の評価は、元の反復 Kan 積の snd の辺そのもの。 -/
lemma finiteFunctorTailSnd_edge (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentSpaceTensorProductSndVertex (F 0)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun i ↦ F i.succ)))).edge =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject (n + 1)
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b) ⟶
              _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b) from
                snd (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues (n + 1) F b 0).obj
                  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n
                    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj)).edge := by
  have h := coherentBinarySnd_evaluation (F 0)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n (fun i ↦ F i.succ)) b
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct_vertex n (fun i ↦ F i.succ) b] at h
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
