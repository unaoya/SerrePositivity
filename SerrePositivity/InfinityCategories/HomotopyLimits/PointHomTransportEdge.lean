module

public import SerrePositivity.InfinityCategories.F2.PointHomTransportBase
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftHomEdgeTransport

/-!
概要：元の全 Hom 輸送の指定点を、元の始点と同じ実際の輸送辺として保持する。
方針：選択済み輸送円柱を指定点で評価し、底の標準区間比較を計算する。
規約：全 Hom の持ち上げを選び直さず、指定した底辺の全一単体を保持する。
使われ方：余錐の全作用の変換を native 単位と元の頂点辺の合成へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (d : E _⦋0⦌) (y : B _⦋0⦌)

/-- 元の輸送円柱の指定点の同じ辺を、元の始点・輸送先の端点表示で保持する。 -/
def pointHomTransportCylinderEdge
    (s : (pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y) _⦋0⦌) :
    SSet.Edge d ((leftFibrationPointHomFamily p d y).app (Opposite.op ⦋0⦌) s).val :=
  (simplicialHomotopyVertexEdge (F2.pointHomTransportCylinder p d y) s).ofEq
    (pinchedConstant_zero d) rfl

/-- 指定底辺の左 Hom の点から取った同じ輸送辺は、元の底辺の全一単体を被覆する。 -/
lemma pointHomTransportCylinderEdge_projection
    (e : SSet.Edge (p.app (Opposite.op ⦋0⦌) d) y) :
    p.app (Opposite.op ⦋1⦌)
      (pointHomTransportCylinderEdge p d y (leftHomEdgePoint e)).edge = e.edge := by
  let s := leftHomEdgePoint e
  have h : (SSet.yonedaEquiv.symm s ▷ (Δ[1] : SSet.{u})) ≫
      (F2.pointHomTransportCylinder p d y).h ≫ p =
        snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [F2.pointHomTransportCylinder_base, ← Category.assoc,
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← intervalMappingUncurry_precomp, SSet.yonedaEquiv_symm_comp]
    rw [show (pinchedHomLeftToIntervalMappingSpace (p.app (Opposite.op ⦋0⦌) d) y).app
      (Opposite.op ⦋0⦌) s = intervalMappingVertexOfEdge e from leftHomEdgePoint_interval e]
    rw [intervalMappingVertexOfEdge_uncurry, ← Category.assoc]
    rfl
  rw [SSet.yonedaEquiv_symm_zero] at h
  have hh := congrArg (fun f => f.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0)).edge, homotopyIntervalEdge.edge)) h
  have hi : homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  calc
    _ = (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋1⦌)
        homotopyIntervalEdge.edge := hh
    _ = e.edge := by
      rw [hi]
      change SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) = _
      rw [Category.id_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.HomotopyLimits
