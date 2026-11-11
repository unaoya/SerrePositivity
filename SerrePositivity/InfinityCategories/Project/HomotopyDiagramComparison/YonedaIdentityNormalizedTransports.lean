module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaIdentityCommonBase

/-!
概要：元の両恒等点の輸送比較を、元の表現可能前層の同じ値の fiber で表示する。
方針：底の終点表示の等式で標準輸送を厳密に移し、既存の同じ比較を写す。
規約：底の辺の元の一単体を保ち、輸送を別の代表で選び直さない。
使われ方：元の Yoneda の脚の評価と反変輸送の自然性の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 同じ一単体の終点表示変更は、同じ標準輸送の終点 fiber の表示変更と一致する。 -/
lemma edgeTransport_target_congr {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b b' : B _⦋0⦌}
    (e : SSet.Edge a b) (e' : SSet.Edge a b') (h : b = b') (he : e.edge = e'.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e' := by
  subst b'
  have h' : e = e' := by
    cases e
    cases e'
    cases he
    rfl
  subst e'
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ終点表示変更により、二つの標準輸送点の元の同型を厳密に移す。 -/
def edgeTransportPointsIso_target_congr {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a c b b' : B _⦋0⦌} (h : b = b')
    (e : SSet.Edge a b) (e' : SSet.Edge a b') (he : e.edge = e'.edge)
    (d : SSet.Edge c b) (d' : SSet.Edge c b') (hd : d.edge = d'.edge)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) _⦋0⦌)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e).app (Opposite.op ⦋0⦌) v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p d).app (Opposite.op ⦋0⦌) w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e').app (Opposite.op ⦋0⦌) v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p d').app (Opposite.op ⦋0⦌) w) := by
  let k := eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)
  have hs := congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) v)
    (edgeTransport_target_congr p e e' h he)
  have ht := congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) w)
    (edgeTransport_target_congr p d d' h hd)
  have hmap := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hi k
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫ hmap ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

variable {C : SSet.{u}} [Quasicategory C] (f : (Δ[1] : SSet.{u}) ⟶ C)
local notation "x₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
local notation "y₀" => f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)
local notation "a₀" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity x₀) (Opposite.op ⦋0⦌)
  (ULift.up (SSet.opObjEquiv.symm x₀))
local notation "b₀" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y₀) (Opposite.op ⦋0⦌)
  (ULift.up (SSet.opObjEquiv.symm x₀))
local notation "c₀" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y₀) (Opposite.op ⦋0⦌)
  (ULift.up (SSet.opObjEquiv.symm y₀))

/-- 元の始点側の底辺を、元の表現可能前層の実際の値を終点として表示する。 -/
def yonedaIdentityNormalizedSourceEdge : SSet.Edge a₀ b₀ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentitySourceBaseEdge f).edge, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentitySourceBaseEdge f).src_eq,
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentitySourceBaseEdge f).tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityCommonFiber_base f)⟩

/-- 元の反変側の底辺を、同じ元の表現可能前層の実際の値を終点として表示する。 -/
def yonedaIdentityNormalizedTargetEdge : SSet.Edge c₀ b₀ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge f).edge, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge f).src_eq,
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge f).tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityCommonFiber_base f)⟩

/-- 始点側の元の恒等点の輸送を、元の y(x) の同じ fiber の点として表示する。 -/
def yonedaIdentityNormalizedSourcePoint : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection b₀) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentityNormalizedSourceEdge f)).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity x₀)

/-- 反変側の元の恒等点の輸送を、元の y(x) の同じ fiber の点として表示する。 -/
def yonedaIdentityNormalizedTargetPoint : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection b₀) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (yonedaIdentityNormalizedTargetEdge f)).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity y₀)

/-- 元の両恒等点の輸送点は、元の表現可能前層 y の x での同じ fiber 内で同型。 -/
def yonedaIdentityNormalizedTransportsIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection b₀)
      (yonedaIdentityNormalizedSourcePoint f) (yonedaIdentityNormalizedTargetPoint f) :=
  edgeTransportPointsIso_target_congr _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityCommonFiber_base f)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentitySourceBaseEdge f) (yonedaIdentityNormalizedSourceEdge f) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge f) (yonedaIdentityNormalizedTargetEdge f) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity x₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.canonicalYonedaPointedIdentity y₀)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityPointTransportsIso f)

/-- 始点側の表示変更は、元の Yoneda 評価辺の一単体を変えない。 -/
lemma yonedaIdentityNormalizedSourceEdge_edge :
    (yonedaIdentityNormalizedSourceEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (SSet.opObjEquiv.symm x₀))).app (Opposite.op ⦋1⦌)
          (ULift.up (SSet.yonedaEquiv f)) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentitySourceBaseEdge_edge f

/-- 反変側の表示変更も、元の表現可能前層の反転辺の一単体を変えない。 -/
lemma yonedaIdentityNormalizedTargetEdge_edge :
    (yonedaIdentityNormalizedTargetEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y₀).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaIdentityTargetBaseEdge_edge f

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
