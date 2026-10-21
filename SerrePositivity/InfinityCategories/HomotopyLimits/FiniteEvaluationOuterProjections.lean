module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFunctorEvaluationModel
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductProjectionFiber

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の Kan 射は、元の coherent 辺の全一単体で一意に決まる。 -/
lemma kanHom_eq_of_coherentNerveEdge_eq {K L : KanObject.{u}} {f g : K ⟶ L}
    (h : (coherentNerveEdge f).edge = (coherentNerveEdge g).edge) : f = g := by
  have he : coherentNerveEdge f = coherentNerveEdge g := SSet.Edge.ext h
  simpa only [coherentNerveEdgeToHom_edge] using congrArg coherentNerveEdgeToHom he

/-- 元の恒等変換の辺の評価は、元の値の恒等 Kan 射の辺そのもの。 -/
lemma coherentIdentityTransformationVertex_evaluation {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex (coherentIdentityTransformationVertex F)).edge =
        (coherentNerveEdge (𝟙 (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)))).edge := by
  have he : intervalMappingEdgeOfVertex (coherentIdentityTransformationVertex F) =
      SSet.Edge.id (functorVertex F) := (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _
  rw [he]
  have hid : (SSet.Edge.id (functorVertex F)).edge = PinchedHom.constant (functorVertex F) 1 :=
    (pinchedConstant_one _).symm
  rw [hid, pinchedConstant_map, evaluateFunctorAt_functorVertex, coherentNerveEdge_id]
  have hv : coherentNerveVertex (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)) =
      F.app (Opposite.op ⦋0⦌) b := coherentNerveVertex_object _
  exact (pinchedConstant_one _).trans
    (congrArg (fun v ↦ (SSet.Edge.id v).edge) hv.symm)

/-- 元の二項 fst 変換の評価は、元の二値の Kan 積の fst の辺そのもの。 -/
lemma coherentBinaryFst_evaluation {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex (coherentSpaceTensorProductFstVertex F G)).edge =
        (coherentNerveEdge (kanTensorEnrichedFst.val
          (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b),
            spaceInfinityObject (G.app (Opposite.op ⦋0⦌) b)))).edge := by
  rcases b with ⟨b⟩
  have h := coherentSpaceTensorProductFstVertex_edgeAt F G b
  change (evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (intervalMappingEdgeOfVertex (coherentSpaceTensorProductFstVertex F G)).edge = _ at h
  rw [← coherentNerveVertex_object (F.app (Opposite.op ⦋0⦌) (ULift.up b)),
    ← coherentNerveVertex_object (G.app (Opposite.op ⦋0⦌) (ULift.up b))] at h
  exact h.trans (spaceTensorProductFstHomotopy_component _ _)

/-- 元の二項 snd 変換の評価は、元の二値の Kan 積の snd の辺そのもの。 -/
lemma coherentBinarySnd_evaluation {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex F G)).edge =
        (coherentNerveEdge (kanTensorEnrichedSnd.val
          (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b),
            spaceInfinityObject (G.app (Opposite.op ⦋0⦌) b)))).edge := by
  rcases b with ⟨b⟩
  have h := coherentSpaceTensorProductSndVertex_edgeAt F G b
  change (evaluateFunctorAt (ULift.up b)).app (Opposite.op ⦋1⦌)
    (intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex F G)).edge = _ at h
  rw [← coherentNerveVertex_object (F.app (Opposite.op ⦋0⦌) (ULift.up b)),
    ← coherentNerveVertex_object (G.app (Opposite.op ⦋0⦌) (ULift.up b))] at h
  exact h.trans (spaceTensorProductSndHomotopy_component _ _)

/-- 元の零段の評価脚は、元の一因子の恒等射そのもの。 -/
lemma finiteFunctorEvaluationKanLeg_zero {B : SSet.{u}}
    (F : Fin 1 → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    finiteFunctorEvaluationKanLeg 0 F b (Discrete.mk (ULift.up 0)) =
      (𝟙 (finiteFunctorKanValues 0 F b 0)) := by
  apply kanHom_eq_of_coherentNerveEdge_eq
  rw [finiteFunctorEvaluationKanLeg_edge]
  exact coherentIdentityTransformationVertex_evaluation (F 0) b

/-- 元の後続段の最初の評価脚は、元の反復積の fst そのもの。 -/
lemma finiteFunctorEvaluationKanLeg_first (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    finiteFunctorEvaluationKanLeg (n + 1) F b (Discrete.mk (ULift.up 0)) =
      fst (finiteFunctorKanValues (n + 1) F b 0).obj
        (finiteKanProductObject n (finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj := by
  apply kanHom_eq_of_coherentNerveEdge_eq
  rw [finiteFunctorEvaluationKanLeg_edge]
  have h := coherentBinaryFst_evaluation (F 0)
    (finiteCoherentSpaceProduct n (fun i ↦ F i.succ)) b
  rw [finiteCoherentSpaceProduct_vertex n (fun i ↦ F i.succ) b] at h
  exact h

/-- 元の tail への射影辺の評価は、元の反復 Kan 積の snd の辺そのもの。 -/
lemma finiteFunctorTailSnd_edge (n : ℕ) {B : SSet.{u}}
    (F : Fin (n + 1 + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
      (intervalMappingEdgeOfVertex (coherentSpaceTensorProductSndVertex (F 0)
        (finiteCoherentSpaceProduct n (fun i ↦ F i.succ)))).edge =
          (coherentNerveEdge (show finiteKanProductObject (n + 1)
            (finiteFunctorKanValues (n + 1) F b) ⟶
              finiteKanProductObject n (finiteFunctorKanValues n (fun i ↦ F i.succ) b) from
                snd (finiteFunctorKanValues (n + 1) F b 0).obj
                  (finiteKanProductObject n
                    (finiteFunctorKanValues n (fun i ↦ F i.succ) b)).obj)).edge := by
  have h := coherentBinarySnd_evaluation (F 0)
    (finiteCoherentSpaceProduct n (fun i ↦ F i.succ)) b
  rw [finiteCoherentSpaceProduct_vertex n (fun i ↦ F i.succ) b] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
