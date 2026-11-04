module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningDiagramBaseChangeComponent
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeTranspose

/-! # 同じ実分類図式の底変換成分と共同底変換の成分の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B)

/-- 実図式の指定底頂点成分は、元の共同底変換の同じ対象・底頂点での二重評価。 -/
theorem leftStraighteningInfinityDiagram_baseChangeIso_heq_jointMap (d : D _⦋0⦌) :
    HEq (VertexIso.map (leftStraighteningInfinityDiagram_baseChangeIso p k)
      (evaluateFunctorAt (ULift.up d)))
      (VertexIso.map (leftStraighteningSectionJointDiagram_baseChangeIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up d) (leftFibrationInfinityVertex p))) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let P := (pre (U.map k)).app SpaceInfinity.{u}
  let e := leftStraighteningInfinityMap_baseChangeIso k
  let x := leftFibrationInfinityVertex p
  have hs : functorVertex (U.map k ≫ leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌) x :=
    congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have ht : functorVertex (leftStraighteningInfinityDiagram (pullback.snd p k)) =
      (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D).app
        (Opposite.op ⦋0⦌) x := by
    exact ((congrArg ((leftStraighteningInfinityMap D).app (Opposite.op ⦋0⦌))
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p))).trans
        (leftStraighteningInfinityDiagram_vertex (pullback.snd p k)).symm).symm
  have hm := F2.vertexIso_map_heq_of_heq
    (leftStraighteningInfinityDiagram_baseChangeIso p k) (e.app x) hs ht
    (leftStraighteningInfinityDiagram_baseChangeIso_heq_app p k)
    (evaluateFunctorAt (ULift.up d))
  have ha := F2.vertexIso_map_heq_of_heq (e.app x)
    (VertexIso.map e (evaluateFunctorAt x))
    (evaluateFunctorAt_functorVertex x _).symm
    (evaluateFunctorAt_functorVertex x _).symm
    (F2.functorIso_app_heq_evaluate e x) (evaluateFunctorAt (ULift.up d))
  exact hm.trans (ha.trans ((heq_of_eq (F2.vertexIso_map_comp e
    (evaluateFunctorAt x) (evaluateFunctorAt (ULift.up d)))).trans
      (leftStraighteningInfinityMap_baseChangeIso_doubleMap k (leftFibrationObjectOf p) d)))

end SerrePositivity.KST.Fibration
