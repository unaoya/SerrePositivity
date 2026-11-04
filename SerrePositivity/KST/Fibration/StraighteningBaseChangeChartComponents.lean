module
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeChartComponents
public import SerrePositivity.KST.Fibration.StraighteningSectionChart

/-! # 元の左右の底変換比較は、それぞれ同じ初頂点切断比較の指定成分 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 元の右側の指定比較は、同じ pullback 対象での初頂点切断比較。 -/
theorem straighteningBaseChangeRightChart_heq_firstVertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    HEq (straighteningBaseChangeRightChart k X c)
      (straighteningFirstVertexSectionChart (leftFibrationBaseChangeObject k X) c) := by
  let e := leftStraighteningSectionJointDiagram_restrictIso D
  let a := ULift.up.{u + 1} (nerveVertex c)
  let x := coherentNerveVertex X
  let H := leftFibrationInfinityBaseChange k
  have hr : HEq (straighteningBaseChangeRightChart k X c)
      (VertexIso.map (straighteningJointBaseChangeRightIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u}) a x)) := by
    unfold straighteningBaseChangeRightChart F2.isoNormalizeEndpoints
    exact F2.iso_endpoints_heq _ _ _
  have hm := functorIso_post_pre_doubleMap e H a x
  have hv := leftFibrationInfinityBaseChange_vertex k X
  have he := congrArg (fun z : (LeftFibrationInfinity D) _⦋0⦌ =>
    doubleFunctorEvaluation
      (K := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory D)))
      (Y := SpaceInfinity.{u}) a z) hv
  exact hr.trans (hm.trans ((F2.vertexIso_map_heq e he).trans
    (straighteningFirstVertexSectionChart_heq_doubleMap
      (leftFibrationBaseChangeObject k X) c).symm))

/-- 元の左側の指定比較は、像の同じ単体での初頂点切断比較。 -/
theorem straighteningBaseChangeLeftChart_heq_firstVertex
    (X : LeftFibrationObject B) (c : TransportSimplexCategory D) :
    HEq (straighteningBaseChangeLeftChart k X c)
      (straighteningFirstVertexSectionChart X ((transportSimplexFunctor k).obj c)) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  let e := leftStraighteningSectionJointDiagram_restrictIso B
  let a := ULift.up.{u + 1} (nerveVertex c)
  let x := coherentNerveVertex X
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  have hl : HEq (straighteningJointBaseChangeLeftIso k) (e.precomp t) := by
    unfold straighteningJointBaseChangeLeftIso
    exact prependEq_heq _ _
  have hm := F2.vertexIso_map_heq_of_heq (straighteningJointBaseChangeLeftIso k)
    (e.precomp t) (congrArg functorVertex hleft) rfl hl
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u}) a x)
  have hc : HEq (straighteningBaseChangeLeftChart k X c)
      (VertexIso.map (straighteningJointBaseChangeLeftIso k)
        (doubleFunctorEvaluation (Y := SpaceInfinity.{u}) a x)) := by
    unfold straighteningBaseChangeLeftChart F2.isoNormalizeEndpoints
    exact F2.iso_endpoints_heq _ _ _
  have hv : t.app (Opposite.op ⦋0⦌) a =
      ULift.up (nerveVertex ((transportSimplexFunctor k).obj c)) := rfl
  have he := congrArg (fun z : (U.obj (nerve (TransportSimplexCategory B))) _⦋0⦌ =>
    doubleFunctorEvaluation (A := LeftFibrationInfinity B) (Y := SpaceInfinity.{u}) z x) hv
  exact hc.trans (hm.trans ((functorIso_pre_doubleMap e t a x).trans
    ((F2.vertexIso_map_heq e he).trans
      (straighteningFirstVertexSectionChart_heq_doubleMap X
        ((transportSimplexFunctor k).obj c)).symm)))

end SerrePositivity.KST.Fibration
