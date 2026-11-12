module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialVertexHomEdge
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationTransportHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso

/-! # 自己引き戻しの第二射影の輸送と第一成分の Hom 表示

概要：第二成分を辺に沿って動かした fiber の輸送は、第一成分の Hom 表示で底へ送った辺との後合成になる。
方針：各頂点の輸送辺を第一射影へ送り、引き戻しの可換性でその底の辺を計算する。
規約：指定した始対象は動かさずに計算する。使われ方：ループ表示の基点変更の共役公式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：fiber 輸送の前後を全空間に含めると連結成分は同じになる。
方針：輸送の包含間の実際のホモトピーを π₀ に移す。
規約：射や空間の充填性は不要。使われ方：同じ自己引き戻しの成分を異なる基点の fiber で表す。 -/
lemma LeftFibrationFiberTransport.piZero_inclusion {E B : SSet.{u}} {p : E ⟶ B}
    {x y : B _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport p a) (b : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x)) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x) b =
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y) (SSet.mapπ₀ T.map b) := by
  simpa only [SSet.mapπ₀_comp_apply] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_eq_of_homotopy T.homotopy b

/-- 概要：自己引き戻しの第二射影の fiber の輸送は、第一成分の Hom 表示では底の辺との後合成。
方針：第一射影へ送った輸送辺の底への像を、第二射影の指定辺の像と引き戻しの可換性で照合する。
規約：r は left fibration、E と B は quasicategory、c は指定した始対象。
使われ方：異なる基点でのループ表示を比較する。 -/
lemma kernelPairFiberTransport_hom {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r] (c : E _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c)
    {e d : E _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj E) e d)
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (pullback.snd r r) a)
    (b : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd r r) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv r c hc (r.app (Opposite.op ⦋0⦌) d)
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r d).hom (SSet.mapπ₀ T.map b)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv r c hc (r.app (Opposite.op ⦋0⦌) e)
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).hom b) ≫
        SSet.Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map r)) := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective b
  simp only [SSet.mapπ₀_mk]
  let t := T.map.app (Opposite.op ⦋0⦌) s
  let se := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).hom.app (Opposite.op ⦋0⦌) s
  let td := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r d).hom.app (Opposite.op ⦋0⦌) t
  let v : SSet.Truncated.Edge (X := (truncation 2).obj E) se.val td.val :=
    (T.vertexEdge s).map ((truncation 2).map (pullback.fst r r))
  have H : r.app (Opposite.op ⦋1⦌)
      ((pullback.fst r r).app (Opposite.op ⦋1⦌) (T.vertexEdge s).edge) =
      r.app (Opposite.op ⦋1⦌)
        ((pullback.snd r r).app (Opposite.op ⦋1⦌) (T.vertexEdge s).edge) :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (pullback.condition (f := r) (g := r)) (Opposite.op ⦋1⦌))
      (T.vertexEdge s).edge
  have hv : r.app (Opposite.op ⦋1⦌) v.edge = (a.map ((truncation 2).map r)).edge :=
    H.trans (congrArg (r.app (Opposite.op ⦋1⦌)) (T.vertexEdge_over s))
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_edge r c hc se td v
    (a.map ((truncation 2).map r)) hv

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
