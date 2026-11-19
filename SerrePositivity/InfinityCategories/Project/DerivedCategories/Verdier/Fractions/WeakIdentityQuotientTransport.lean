module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakIdentityQuotientPoint
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanFiberUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedRightFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-!
概要：既存の商上の指定恒等点を、元の値同型の同じ実辺で輸送する。
方針：元の一点からの射の正規化を coslice の実輸送点へ戻す。
規約：補助点への置換で既存指定点の条件を代用しない。全族写像の存在は未主張。
使われ方：K-B-S の既存 weakIdentityQuotientFiberPoint と元の Kan 恒等点の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：元の q(x) 値同型の同じ順射を表す実辺。
方針：元のホモトピー圏の射の代表を選ぶ。
規約：既存の指定値同型を変更しない。
使われ方：指定恒等点の実輸送。 -/
def weakIdentityQuotientValueEdge : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))) :=
  SSet.Edge.ofTruncated (Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueIso h x).hom))

/-- 概要：同じ実辺の類は元の値同型の指定順射。
方針：代表の選択の等式を読む。
規約：元の同型と点の射の正規化を保つ。
使われ方：実輸送の点の射の計算。 -/
theorem weakIdentityQuotientValueEdge_hom :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x).toTruncated =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueIso h x).hom :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueIso h x).hom)

/-- 概要：元の商上の指定恒等点を、同じ値比較の実輸送で運ぶ。
方針：既存の pointed-space 射影の edgeTransport を使う。
規約：元の指定点を始点とし、Kan 点を独立に選ばない。
使われ方：全族単位の恒等点比較。 -/
def weakIdentityQuotientTransportPoint :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x)).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x)

/-- 概要：同じ実輸送点の一点からの射は、元の同じ Kan 恒等点の射。
方針：実輸送の合成公式と元の値同型の正規化を使う。
規約：ホモトピー圏の点の射の計算であり、全族写像の自然性は未主張。
使われ方：同じ実 fiber 内の頂点同型の構成。 -/
theorem weakIdentityQuotientTransportPoint_hom :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientTransportPoint h x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityNativePointHom h x := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceTransportPointHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge_hom] at ht
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointHom h x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber_hom h x
  rw [hp] at ht
  exact ht.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointHom_normalized h x)

/-- 概要：同じ実輸送点は、元の Kan 恒等点の pointed 表示と同じ fiber 内で同型。
方針：元の一点からの射の一致を coslice fiber の実頂点同型に戻す。
規約：既存の指定恒等点に基づく比較。全空間だけの同型ではない。
使われ方：K-B-S の恒等点条件の値側の指定比較。 -/
def weakIdentityQuotientTransportPointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientTransportPoint h x)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberVertexIsoOfHomEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientTransportPoint_hom h x)

/-- 概要：元の Kan 恒等点の pointed 表示の既存値比較は、同じ Kan 恒等点を回収する。
方針：同じ右 Hom の比較の両逆と指定頂点比較を、充満忠実性で戻す。
規約：値比較の選択を新しい同値へ置き換えない。
使われ方：既存指定恒等点の同じ Kan 値における正規化。 -/
def weakIdentityKanPoint_valueIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))).hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)))
    (ULift.up.{u + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) := by
  let K := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)
  have hu := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedValueRightComparison_unitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K)).app s
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedRightFiberComparison_vertexIso K s
  have he := hu ≪≫ hv.symm
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedRightFiberComparison K).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K)).hom.app
          (Opposite.op ⦋0⦌) s))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedRightFiberComparison K).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x))) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedValueRightComparison_standard, s, Equiv.apply_symm_apply] using! he
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedRightFiberComparison_isQCatEquivalence K).isFullyFaithful.preimageVertexIso he'

/-- 概要：元の商上の指定恒等点の値を元の値同型で運ぶと、同じ Kan 恒等点になる。
方針：元の実辺の値自然性、同じ輸送点同型、既存値比較の点計算を合成する。
規約：元の指定点と全一単体を保持する。全族写像の存在は未主張。
使われ方：K-B-S の既存指定点と fiber 単位との照合の値側。 -/
def weakIdentityQuotientValue_normalizedIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x))).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x))
    (ULift.up.{u + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeTransportValueIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x)).app
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientTransportPointIso h x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))).hom ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_valueIso h x

/-- 概要：元の q(x) fiber の同じ値同型を、元の小さい Kan 図式値への実同値にする。
方針：小さい fiber 値同値と元の値比較辺の Kan 値を合成する。
規約：既存指定恒等点の正規化と同じ比較辺を使う。
使われ方：同じ小さい fiber 内の恒等点同型を反映する比較。 -/
def weakIdentityQuotientFiberValueEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) x))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).obj) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x) := by
    change IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x).toTruncated)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge_hom]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
    (q.hom.app (Opposite.op ⦋0⦌) x)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceInfinityEdgeValue_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x) he).choose

/-- 概要：元の小さい指定恒等点の値比較像は、元の同じ Kan 恒等点と同型。
方針：小さい fiber 点の厳密回収と既存値比較の正規化を、同じ宇宙へ降ろす。
規約：元の weakIdentityQuotientFiberPoint を補助点へ置換しない。
使われ方：K-B-S の恒等点条件を同じ fiber 内で反映する。 -/
def weakIdentityQuotientFiberValue_pointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let v := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientPointedFiber h x
  let m := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) (ULift.up b))).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValueEdge h x))
  have hrec := congrArg (m.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.smallUnstraighteningFiberPoint_recover F b v)
  have he : ULift.up.{u + 1}
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).hom.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x)) = m.app (Opposite.op ⦋0⦌) v := by
    exact hrec
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso (eqToIso (congrArg HomotopyCategory.mk he) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientValue_normalizedIso h x)

/-- 概要：元の両端 x 固定 span の全体を、元の q(x) fiber へ送る単位。
方針：同じ零単体添字の全 Kan 単位と、指定恒等点を保持する値同値の逆を使う。
規約：可変終点の全族写像ではなく、指定 x fiber 全体の射。
使われ方：K-B-S の既存指定恒等点を保持する fiber 制限の検証。 -/
def weakIdentityQuotientFiberUnit :
    fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) x) :=
  eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x).symm) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanFiberUnit i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).inv

/-- 概要：同じ全 fiber 単位の恒等 span 像は、元の Kan 恒等点の値逆像。
方針：元の指定 Kan 点の厳密計算を回収する。
規約：元の両端固定 span の恒等点を使う。
使われ方：既存の指定小さい fiber 点への同型。 -/
theorem weakIdentityQuotientFiberUnit_identity :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberUnit h x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).inv.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) := rfl

/-- 概要：同じ q(x) fiber の全単位は、元の Kan 置換単位を厳密な端点移送付きで回収する。
方針：値同値の余単位を元の全 Kan 単位で前合成し、同じ評価で後合成する。
規約：元の零単体添字への端点等式を明示し、点だけの回収で代用しない。
使われ方：既存指定恒等点を保つ fiber 全体の回収条件。 -/
def weakIdentityQuotientFiberUnit_recovery : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberUnit h x ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))
    (eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x).symm) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _) := by
  let a := eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x).symm)
  have e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x).invHomIso.precomp
    (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanFiberUnit i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberUnit, a, Category.assoc, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanFiberUnit_valueComparison] using! e

/-- 概要：同じ全 fiber 単位の恒等 span 像は、既存の指定恒等点と同じ小さい fiber 内で同型。
方針：指定値同値の余単位と元の指定点の値計算を、その充満忠実性で反映する。
規約：weakIdentityQuotientFiberPoint を標的とし、補助点への同型で代用しない。
使われ方：K-B-S の恒等 span 条件を満たす指定 fiber 制限。 -/
def weakIdentityQuotientFiberUnit_pointIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberUnit h x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberPoint h x) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValueEquivalence h x
  have hi := e.invHomIso.app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberValue_pointIso h x).symm
  have hr := e.isQCatEquivalence.isFullyFaithful.preimageVertexIso hi
  exact eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityQuotientFiberUnit_identity h x)) ≪≫ hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
