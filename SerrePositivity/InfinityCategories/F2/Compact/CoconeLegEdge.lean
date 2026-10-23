module

public import SerrePositivity.InfinityCategories.F2.CoconeUnitCylinder
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.Stable.CoconeLeg

/-!
概要：元の余錐変換を各頂点で評価した辺は、元の指定余錐の同じ脚。
方針：元の全円柱の一点での値を、点の join 円柱の自然性で計算する。
規約：辺の類だけでなく元の全一単体の厳密な一致を保つ。
使われ方：元の fiber 写像の制限を、元の余錐脚による実輸送へ同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B X : SSet.{u}} {F : B ⟶ X}

/-- 元の余錐変換の同じ全辺を、元の底の指定頂点で評価する。 -/
def coconeTransportLeg (c : JoinCocone F) (b : B _⦋0⦌) :
    X.Edge (F.app (Opposite.op ⦋0⦌) b) c.vertex :=
  (functorEdgeAt (intervalMappingEdgeOfVertex (coconeTransformationVertex c)) b).ofEq rfl
    (pinchedConstant_zero c.vertex)

/-- 元の円柱を指定点で評価した辺は、元の指定余錐脚の全一単体そのもの。 -/
lemma coconeHomotopyLeg_edge (c : JoinCocone F) (b : B _⦋0⦌) :
    (simplicialHomotopyVertexEdge (coconeTransformationHomotopy c) b).edge =
      (c.leg (SSet.yonedaEquiv.symm b)).edge := by
  change (coconeTransformationHomotopy c).h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge,
      homotopyIntervalEdge.edge) = _
  rw [← pinchedConstant_one]
  rw [coconeTransformationHomotopy_h]
  apply congrArg (c.val.app (Opposite.op ⦋1⦌))
  let z := PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) 1
  have h := congrArg (fun q :
      ((Δ[0] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[0] ⟶ join B Δ[0] =>
        q.app (Opposite.op ⦋1⦌) ((z, homotopyIntervalEdge.edge), z))
    (joinCylinderMap_naturality (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u})))
  have sub (r : ℕ) : Subsingleton (Join.augObj (Δ[0] : SSet.{u}) r) := by
    cases r with
    | zero => exact inferInstanceAs (Subsingleton PUnit)
    | succ r =>
      constructor
      intro a b
      apply ULift.ext
      exact @Subsingleton.elim (⦋r⦌ ⟶ ⦋0⦌) inferInstance a.down b.down
  have hz : (joinCylinderMap (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋1⦌)
      ((z, homotopyIntervalEdge.edge), z) =
        (joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋1⦌)
          homotopyIntervalEdge.edge := by
    rw [joinCylinderMap_app]
    refine Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact (sub _).elim _ _
    · exact (sub _).elim _ _
  change (joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌)
      (((SSet.yonedaEquiv.symm b).app (Opposite.op ⦋1⦌) z,
        homotopyIntervalEdge.edge), z) =
    (joinMap (SSet.yonedaEquiv.symm b) (𝟙 Δ[0])).app (Opposite.op ⦋1⦌)
      ((joinCylinderMap (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋1⦌)
        ((z, homotopyIntervalEdge.edge), z)) at h
  rw [hz] at h
  have hb : (SSet.yonedaEquiv.symm b).app (Opposite.op ⦋1⦌) z =
      PinchedHom.constant b 1 := by
    rw [SSet.yonedaEquiv_symm_app]
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => B.map α.op b) (Subsingleton.elim _ _)
  rw [hb] at h
  have ht : homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    ext i
    fin_cases i <;> rfl
  change (joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌)
      ((PinchedHom.constant b 1, homotopyIntervalEdge.edge), _) = _
  rw [ht] at h ⊢
  convert h using 1
  · apply congrArg ((joinCylinderMap B Δ[0]).app (Opposite.op ⦋1⦌))
    refine Prod.ext ?_ ?_
    · rfl
    · exact (sub 2).elim _ _
  · apply congrArg ((joinMap (SSet.yonedaEquiv.symm b) (𝟙 (Δ[0] : SSet.{u}))).app
      (Opposite.op ⦋1⦌))
    apply congrArg ((joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋1⦌))
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    rfl

/-- 同じ変換の全評価辺も、元の余錐脚の全一単体を厳密に回収する。 -/
lemma coconeTransportLeg_edge (c : JoinCocone F) (b : B _⦋0⦌) :
    (coconeTransportLeg c b).edge = (c.leg (SSet.yonedaEquiv.symm b)).edge := by
  change (evaluateFunctorAt b).app (Opposite.op ⦋1⦌)
    (intervalMappingEdgeOfVertex (coconeTransformationVertex c)).edge = _
  exact (evaluateFunctorAt_edge
    (intervalMappingEdgeOfVertex (coconeTransformationVertex c)).toTruncated b).symm.trans
      (coconeHomotopyLeg_edge c b)

end SerrePositivity.InfinityCategories.F2.Compact
