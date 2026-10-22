module
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeVertex
public import SerrePositivity.KST.Fibration.DoubleEvaluationTranspose

/-! # 実分類写像の底変換は、同じ共同底変換の転置成分を保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 二重評価は底の前合成の同じ頂点を厳密に回収する。 -/
theorem doubleFunctorEvaluation_precomp_vertex {K L A Y : SSet.{u}}
    (F : K ⟶ (ihom A).obj Y) (q : L ⟶ K) (l : L _⦋0⦌) (a : A _⦋0⦌) :
    (doubleFunctorEvaluation (Y := Y) (q.app (Opposite.op ⦋0⦌) l) a).app
        (Opposite.op ⦋0⦌) (functorVertex F) =
      (doubleFunctorEvaluation (Y := Y) l a).app (Opposite.op ⦋0⦌)
        (functorVertex (q ≫ F)) := by
  rw [doubleFunctorEvaluation_vertex, doubleFunctorEvaluation_vertex]
  rfl

/-- 実分類写像の元の底変換同型は、同じ共同同型の転置の端点だけを変更する。 -/
theorem leftStraighteningInfinityMap_baseChangeIso_heq :
    HEq (leftStraighteningInfinityMap_baseChangeIso k)
      (leftStraighteningSectionJointDiagram_baseChangeIso k).transpose := by
  unfold leftStraighteningInfinityMap_baseChangeIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

/-- 実分類写像を対象・底頂点で評価すると、同じ共同底変換を逆順に評価した値。 -/
theorem leftStraighteningInfinityMap_baseChangeIso_doubleMap
    (X : LeftFibrationObject B) (d : D _⦋0⦌) :
    HEq (VertexIso.map (leftStraighteningInfinityMap_baseChangeIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (coherentNerveVertex X) (ULift.up d)))
      (VertexIso.map (leftStraighteningSectionJointDiagram_baseChangeIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up d) (coherentNerveVertex X))) := by
  let e := leftStraighteningSectionJointDiagram_baseChangeIso k
  let U := SSet.uliftFunctor.{u + 1, u}
  have hm := F2.vertexIso_map_heq_of_heq (leftStraighteningInfinityMap_baseChangeIso k)
    e.transpose
    (congrArg functorVertex
      (transposeFunctorFamily_comp (U.map k) (leftStraighteningSectionJointDiagram B)).symm)
    (congrArg functorVertex
      (transposeFunctorFamily_pre (leftStraighteningSectionJointDiagram D)
        (leftFibrationInfinityBaseChange k)).symm)
    (leftStraighteningInfinityMap_baseChangeIso_heq k)
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u}) (coherentNerveVertex X) (ULift.up d))
  exact hm.trans (functorIso_transpose_doubleMap e (ULift.up d) (coherentNerveVertex X))

/-- 大域共同同型の初頂点成分は、同じ全単体上の指定制限同型の成分と一致する。 -/
theorem leftStraighteningJointBaseChangeValueIso [Quasicategory D]
    (c : TransportSimplexCategory D) :
    functorIsoValue (leftStraighteningSectionJointDiagram_baseChangeIso k)
      (ULift.up ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌)
        (nerveVertex c))) =
      functorIsoValue (straighteningJointBaseChangeRestrictionIso k)
        (ULift.up (nerveVertex c)) := by
  apply Iso.ext
  exact leftStraighteningSectionJointDiagram_baseChangeIso_value k c

/-- 同じ大域二重成分は、同じ全単体上の元の制限同型の二重成分と一致する。 -/
theorem leftStraighteningJointBaseChangeDoubleMap [Quasicategory D]
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    HEq (VertexIso.map (leftStraighteningSectionJointDiagram_baseChangeIso k)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌)
          (nerveVertex c))) (coherentNerveVertex X)))
      (VertexIso.map (straighteningJointBaseChangeRestrictionIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
          (ULift.up (nerveVertex c)) (coherentNerveVertex X))) := by
  let e := leftStraighteningSectionJointDiagram_baseChangeIso k
  let a := ULift.up.{u + 1} ((transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌)
    (nerveVertex c))
  let r := straighteningJointBaseChangeRestrictionIso k
  let b := ULift.up.{u + 1} (nerveVertex c)
  let x := coherentNerveVertex X
  have h := congrArg (fun i => VertexIso.map i (evaluateFunctorAt x))
    (leftStraighteningJointBaseChangeValueIso k c)
  exact (functorIsoDoubleValue_heq_map e a x).symm.trans
    ((heq_of_eq h).trans (functorIsoDoubleValue_heq_map r b x))

end SerrePositivity.KST.Fibration
