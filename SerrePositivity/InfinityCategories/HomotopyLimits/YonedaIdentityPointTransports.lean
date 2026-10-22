module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.TwistedArrowPointedEdgeProjections

/-!
概要：元の Yoneda 恒等点の二方向の輸送を、同じ実際の fiber 内で比較する。
方針：元の Tw の二辺の共通終点と、それぞれの標準輸送点を比較して合成する。
規約：元の二つの底辺と恒等点を保持し、別の点や辺の代表を選ばない。
使われ方：Yoneda の第一変数の評価自然性と、P_Σ 内の有限余積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 二つの元の pointed 辺の共通終点を、同じ実際の fiber 内の点として保持する。 -/
def yonedaIdentityCommonFiberPoint {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (vertexFiber pointedSpaceProjection
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (twistedArrowPointedEdgeVertex f))) _⦋0⦌ :=
  ⟨twistedArrowPointedEdgeVertex f, (pinchedConstant_zero _).symm⟩

/-- 元の始点側の底辺を、元の Yoneda 恒等点の実際の fiber を始点として表示する。 -/
def yonedaIdentitySourceBaseEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      ((representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm
            (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))))
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (twistedArrowPointedEdgeVertex f)) := by
  let h := (twistedArrowPointedSourceEdge f).map pointedSpaceProjection
  exact ⟨h.edge, h.src_eq.trans
    ((canonicalYonedaPointedIdentity _).property.trans (pinchedConstant_zero _)), h.tgt_eq⟩

/-- 元の終点側の底辺を、元の Yoneda 恒等点の実際の fiber を始点として表示する。 -/
def yonedaIdentityTargetBaseEdge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    SSet.Edge
      ((representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm
            (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))))
      (pointedSpaceProjection.app (Opposite.op ⦋0⦌) (twistedArrowPointedEdgeVertex f)) := by
  let h := (twistedArrowPointedTargetEdge f).map pointedSpaceProjection
  exact ⟨h.edge, h.src_eq.trans
    ((canonicalYonedaPointedIdentity _).property.trans (pinchedConstant_zero _)), h.tgt_eq⟩

/-- 元の共通終点は、始点側の同じ恒等点を元の底辺で標準輸送した点と同型。 -/
def yonedaIdentitySourceTransportIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    VertexIso (yonedaIdentityCommonFiberPoint f)
      ((edgeTransport pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)).app
        (Opposite.op ⦋0⦌) (canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)))) :=
  leftFibrationEdge_pointVertexIso pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)
    (canonicalYonedaPointedIdentity _) (yonedaIdentityCommonFiberPoint f)
    (twistedArrowPointedSourceEdge f) rfl

/-- 元の共通終点は、終点側の同じ恒等点を元の反変辺で標準輸送した点と同型。 -/
def yonedaIdentityTargetTransportIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    VertexIso (yonedaIdentityCommonFiberPoint f)
      ((edgeTransport pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)).app
        (Opposite.op ⦋0⦌) (canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))) :=
  leftFibrationEdge_pointVertexIso pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)
    (canonicalYonedaPointedIdentity _) (yonedaIdentityCommonFiberPoint f)
    (twistedArrowPointedTargetEdge f) rfl

/-- 元の両恒等点の二方向の標準輸送点を、同じ実際の fiber 内で結ぶ。 -/
def yonedaIdentityPointTransportsIso {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    VertexIso
      ((edgeTransport pointedSpaceProjection (yonedaIdentitySourceBaseEdge f)).app
        (Opposite.op ⦋0⦌) (canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))
      ((edgeTransport pointedSpaceProjection (yonedaIdentityTargetBaseEdge f)).app
        (Opposite.op ⦋0⦌) (canonicalYonedaPointedIdentity
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)))) :=
  (yonedaIdentitySourceTransportIso f).symm ≪≫ yonedaIdentityTargetTransportIso f

/-- 始点側の標準輸送の底辺は、元の Yoneda の射を始点で評価した同じ一単体。 -/
lemma yonedaIdentitySourceBaseEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (yonedaIdentitySourceBaseEdge f).edge =
      (yonedaInfinityMap C ≫ evaluateFunctorAt
        (ULift.up (SSet.opObjEquiv.symm
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))).app
            (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)) :=
  twistedArrowPointedSourceEdge_projection f

/-- 終点側の標準輸送の底辺は、元の表現可能前層の反転辺の同じ一単体。 -/
lemma yonedaIdentityTargetBaseEdge_edge {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    (yonedaIdentityTargetBaseEdge f).edge =
      (representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋1⦌)
          (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) :=
  twistedArrowPointedTargetEdge_projection f

end SerrePositivity.InfinityCategories.HomotopyLimits
