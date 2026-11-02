module

public import SerrePositivity.KST.Fibration.WeakIdentityQuotientPoint
public import SerrePositivity.KST.Fibration.WeakSpanKanFiberUnit
public import SerrePositivity.KST.Fibration.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedRightFiberVertices
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.F1.UniverseVertexIso

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：元の q(x) 値同型の同じ順射を表す実辺。
方針：元のホモトピー圏の射の代表を選ぶ。
規約：既存の指定値同型を変更しない。
使われ方：指定恒等点の実輸送。 -/
def weakIdentityQuotientValueEdge : SpaceInfinity.{u}.Edge
    ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
    (spaceInfinityVertex ((weakSpanKanDiagram i x).obj
      (transportSimplexIndex (n := ⦋0⦌) x))) :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective _ _
    (weakIdentityQuotientValueIso h x).hom))

/-- 概要：同じ実辺の類は元の値同型の指定順射。
方針：代表の選択の等式を読む。
規約：元の同型と点の射の正規化を保つ。
使われ方：実輸送の点の射の計算。 -/
theorem weakIdentityQuotientValueEdge_hom :
    Truncated.HomotopyCategory.homMk (weakIdentityQuotientValueEdge h x).toTruncated =
      (weakIdentityQuotientValueIso h x).hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _
    (weakIdentityQuotientValueIso h x).hom)

/-- 概要：元の商上の指定恒等点を、同じ値比較の実輸送で運ぶ。
方針：既存の pointed-space 射影の edgeTransport を使う。
規約：元の指定点を始点とし、Kan 点を独立に選ばない。
使われ方：全族単位の恒等点比較。 -/
def weakIdentityQuotientTransportPoint :=
  (edgeTransport pointedSpaceProjection (weakIdentityQuotientValueEdge h x)).app
    (Opposite.op ⦋0⦌) (weakIdentityQuotientPointedFiber h x)

/-- 概要：同じ実輸送点の一点からの射は、元の同じ Kan 恒等点の射。
方針：実輸送の合成公式と元の値同型の正規化を使う。
規約：ホモトピー圏の点の射の計算であり、全族写像の自然性は未主張。
使われ方：同じ実 fiber 内の頂点同型の構成。 -/
theorem weakIdentityQuotientTransportPoint_hom :
    cosliceFiberPointHom (weakIdentityQuotientTransportPoint h x) =
      weakIdentityNativePointHom h x := by
  have ht := cosliceTransportPointHom (weakIdentityQuotientValueEdge h x)
    (edgeTransport pointedSpaceProjection (weakIdentityQuotientValueEdge h x))
    (edgeTransport_isTransport pointedSpaceProjection (weakIdentityQuotientValueEdge h x))
    (weakIdentityQuotientPointedFiber h x)
  rw [weakIdentityQuotientValueEdge_hom] at ht
  have hp : cosliceFiberPointHom (weakIdentityQuotientPointedFiber h x) =
      weakIdentityQuotientPointHom h x := weakIdentityQuotientPointedFiber_hom h x
  rw [hp] at ht
  exact ht.symm.trans (weakIdentityQuotientPointHom_normalized h x)

/-- 概要：同じ実輸送点は、元の Kan 恒等点の pointed 表示と同じ fiber 内で同型。
方針：元の一点からの射の一致を coslice fiber の実頂点同型に戻す。
規約：既存の指定恒等点に基づく比較。全空間だけの同型ではない。
使われ方：K-B-S の恒等点条件の値側の指定比較。 -/
def weakIdentityQuotientTransportPointIso : VertexIso
    (weakIdentityQuotientTransportPoint h x)
    ((pointedSpaceFiberVertexEquiv ((weakSpanKanDiagram i x).obj
      (transportSimplexIndex (n := ⦋0⦌) x))).symm (weakIdentityKanPoint h x)) :=
  cosliceFiberVertexIsoOfHomEq (weakIdentityQuotientTransportPoint_hom h x)

/-- 概要：元の Kan 恒等点の pointed 表示の既存値比較は、同じ Kan 恒等点を回収する。
方針：同じ右 Hom の比較の両逆と指定頂点比較を、充満忠実性で戻す。
規約：値比較の選択を新しい同値へ置き換えない。
使われ方：既存指定恒等点の同じ Kan 値における正規化。 -/
def weakIdentityKanPoint_valueIso : VertexIso
    ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex ((weakSpanKanDiagram i x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)))).hom.app (Opposite.op ⦋0⦌)
      ((pointedSpaceFiberVertexEquiv ((weakSpanKanDiagram i x).obj
        (transportSimplexIndex (n := ⦋0⦌) x))).symm (weakIdentityKanPoint h x)))
    (ULift.up.{u + 1} (weakIdentityKanPoint h x)) := by
  let K := (weakSpanKanDiagram i x).obj (transportSimplexIndex (n := ⦋0⦌) x)
  let s := (pointedSpaceFiberVertexEquiv K).symm (weakIdentityKanPoint h x)
  have hu := (pointedValueRightComparison_unitIso (spaceInfinityVertex K)).app s
  have hv := pointedRightFiberComparison_vertexIso K s
  have he := hu ≪≫ hv.symm
  have he' : VertexIso
      ((pointedRightFiberComparison K).app (Opposite.op ⦋0⦌)
        ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom.app
          (Opposite.op ⦋0⦌) s))
      ((pointedRightFiberComparison K).app (Opposite.op ⦋0⦌)
        (ULift.up (weakIdentityKanPoint h x))) := by
    simpa only [pointedValueRightComparison_standard, s, Equiv.apply_symm_apply] using! he
  exact (pointedRightFiberComparison_isQCatEquivalence K).isFullyFaithful.preimageVertexIso he'

/-- 概要：元の商上の指定恒等点の値を元の値同型で運ぶと、同じ Kan 恒等点になる。
方針：元の実辺の値自然性、同じ輸送点同型、既存値比較の点計算を合成する。
規約：元の指定点と全一単体を保持する。全族写像の存在は未主張。
使われ方：K-B-S の既存指定点と fiber 単位との照合の値側。 -/
def weakIdentityQuotientValue_normalizedIso : VertexIso
    (((pointedSpaceFiberValueEquivalence
      ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (F2.spaceInfinityEdgeValue (weakIdentityQuotientValueEdge h x))).app
      (Opposite.op ⦋0⦌) (weakIdentityQuotientPointedFiber h x))
    (ULift.up.{u + 1} (weakIdentityKanPoint h x)) :=
  (F2.spaceInfinityEdgeTransportValueIso (weakIdentityQuotientValueEdge h x)).app
    (weakIdentityQuotientPointedFiber h x) ≪≫
    VertexIso.map (weakIdentityQuotientTransportPointIso h x)
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex ((weakSpanKanDiagram i x).obj
        (transportSimplexIndex (n := ⦋0⦌) x)))).hom ≪≫ weakIdentityKanPoint_valueIso h x

/-- 概要：元の q(x) fiber の同じ値同型を、元の小さい Kan 図式値への実同値にする。
方針：小さい fiber 値同値と元の値比較辺の Kan 値を合成する。
規約：既存指定恒等点の正規化と同じ比較辺を使う。
使われ方：同じ小さい fiber 内の恒等点同型を反映する比較。 -/
def weakIdentityQuotientFiberValueEquivalence :
    QCatEquivalence
      (vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) x))
      (((weakSpanKanDiagram i x).obj (transportSimplexIndex (n := ⦋0⦌) x)).obj) := by
  have he : IsInvertibleEdge (weakIdentityQuotientValueEdge h x) := by
    change IsIso (Truncated.HomotopyCategory.homMk (weakIdentityQuotientValueEdge h x).toTruncated)
    rw [weakIdentityQuotientValueEdge_hom]
    infer_instance
  exact (smallLeftUnstraighteningFiberValueEquivalence (weakSpanKanQuotientDiagram h x)
    (q.hom.app (Opposite.op ⦋0⦌) x)).trans
    (F2.Compact.spaceInfinityEdgeValue_isQCatEquivalence (weakIdentityQuotientValueEdge h x) he).choose

/-- 概要：元の小さい指定恒等点の値比較像は、元の同じ Kan 恒等点と同型。
方針：小さい fiber 点の厳密回収と既存値比較の正規化を、同じ宇宙へ降ろす。
規約：元の weakIdentityQuotientFiberPoint を補助点へ置換しない。
使われ方：K-B-S の恒等点条件を同じ fiber 内で反映する。 -/
def weakIdentityQuotientFiberValue_pointIso : VertexIso
    ((weakIdentityQuotientFiberValueEquivalence h x).hom.app (Opposite.op ⦋0⦌)
      (weakIdentityQuotientFiberPoint h x))
    (weakIdentityKanPoint h x) := by
  let F := weakSpanKanQuotientDiagram h x
  let b := q.hom.app (Opposite.op ⦋0⦌) x
  let v := weakIdentityQuotientPointedFiber h x
  let m := (pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) (ULift.up b))).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (F2.spaceInfinityEdgeValue (weakIdentityQuotientValueEdge h x))
  have hrec := congrArg (m.app (Opposite.op ⦋0⦌)) (smallUnstraighteningFiberPoint_recover F b v)
  have he : ULift.up.{u + 1}
      ((weakIdentityQuotientFiberValueEquivalence h x).hom.app (Opposite.op ⦋0⦌)
        (weakIdentityQuotientFiberPoint h x)) = m.app (Opposite.op ⦋0⦌) v := by
    exact hrec
  exact downVertexIso (eqToIso (congrArg HomotopyCategory.mk he) ≪≫
    weakIdentityQuotientValue_normalizedIso h x)

/-- 概要：元の両端 x 固定 span の全体を、元の q(x) fiber へ送る単位。
方針：同じ零単体添字の全 Kan 単位と、指定恒等点を保持する値同値の逆を使う。
規約：可変終点の全族写像ではなく、指定 x fiber 全体の射。
使われ方：K-B-S の既存指定恒等点を保持する fiber 制限の検証。 -/
def weakIdentityQuotientFiberUnit :
    fixedMarkedSpans B.obj (weakEquivalences i) x x ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) x) :=
  eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
    (transportSimplexFirstVertexMap_zeroIndex x).symm) ≫
      weakSpanKanFiberUnit i x (transportSimplexIndex (n := ⦋0⦌) x) ≫
        (weakIdentityQuotientFiberValueEquivalence h x).inv

/-- 概要：同じ全 fiber 単位の恒等 span 像は、元の Kan 恒等点の値逆像。
方針：元の指定 Kan 点の厳密計算を回収する。
規約：元の両端固定 span の恒等点を使う。
使われ方：既存の指定小さい fiber 点への同型。 -/
theorem weakIdentityQuotientFiberUnit_identity :
    (weakIdentityQuotientFiberUnit h x).app (Opposite.op ⦋0⦌) (weakIdentityFixedSpan h x) =
      (weakIdentityQuotientFiberValueEquivalence h x).inv.app (Opposite.op ⦋0⦌)
        (weakIdentityKanPoint h x) := rfl

/-- 概要：同じ q(x) fiber の全単位は、元の Kan 置換単位を厳密な端点移送付きで回収する。
方針：値同値の余単位を元の全 Kan 単位で前合成し、同じ評価で後合成する。
規約：元の零単体添字への端点等式を明示し、点だけの回収で代用しない。
使われ方：既存指定恒等点を保つ fiber 全体の回収条件。 -/
def weakIdentityQuotientFiberUnit_recovery : FunctorIso
    (weakIdentityQuotientFiberUnit h x ≫ (weakIdentityQuotientFiberValueEquivalence h x).hom ≫
      weakSpanKanValueComparison i x (transportSimplexIndex (n := ⦋0⦌) x))
    (eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
      (transportSimplexFirstVertexMap_zeroIndex x).symm) ≫ F2.continuousKanReplacementUnit.app _) := by
  let a := eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
    (transportSimplexFirstVertexMap_zeroIndex x).symm)
  have e := ((weakIdentityQuotientFiberValueEquivalence h x).invHomIso.precomp
    (a ≫ weakSpanKanFiberUnit i x (transportSimplexIndex (n := ⦋0⦌) x))).postcomp
      (weakSpanKanValueComparison i x (transportSimplexIndex (n := ⦋0⦌) x))
  simpa only [weakIdentityQuotientFiberUnit, a, Category.assoc, Category.comp_id,
    weakSpanKanFiberUnit_valueComparison] using! e

/-- 概要：同じ全 fiber 単位の恒等 span 像は、既存の指定恒等点と同じ小さい fiber 内で同型。
方針：指定値同値の余単位と元の指定点の値計算を、その充満忠実性で反映する。
規約：weakIdentityQuotientFiberPoint を標的とし、補助点への同型で代用しない。
使われ方：K-B-S の恒等 span 条件を満たす指定 fiber 制限。 -/
def weakIdentityQuotientFiberUnit_pointIso : VertexIso
    ((weakIdentityQuotientFiberUnit h x).app (Opposite.op ⦋0⦌) (weakIdentityFixedSpan h x))
    (weakIdentityQuotientFiberPoint h x) := by
  let e := weakIdentityQuotientFiberValueEquivalence h x
  have hi := e.invHomIso.app (weakIdentityKanPoint h x) ≪≫
    (weakIdentityQuotientFiberValue_pointIso h x).symm
  have hr := e.isQCatEquivalence.isFullyFaithful.preimageVertexIso hi
  exact eqToIso (congrArg HomotopyCategory.mk (weakIdentityQuotientFiberUnit_identity h x)) ≪≫ hr

end SerrePositivity.KST.Fibration
