module
public import SerrePositivity.KST.Fibration.VerdierFullSComparisonComponents

/-!
概要：同じ全 S• 比較と実下側読出しを合成する指定境界の実二単体を構成する。
方針：直接端と合成端の実恒等成分へ既存の単位合成二単体を適用する。
規約：元の二実辺を保持し、合成辺の実一単体を厳密回収する。
使われ方：K-6 c4 の境界を指定した全長 Hom 合成への実入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：同じ全 S• 比較の core 制限を再構成と同じ宇宙へ持ち上げる。
方針：元の全ホモトピーを同じ宇宙持ち上げへ送る。
規約：元の二つの全 path 族を保持する。
使われ方：実下側読出しへ続ける全長 Hom 比較。 -/
def verdierReadoutUpperComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    SSet.Homotopy
      ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
      ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplicialHomotopy.{u, u + 1} (verdierOriginalFullSCoreHomotopy d 0 1)

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)

private theorem nativeReadoutLeftUnitTriangle
    {a b c : (verdierNativeLongHomTarget d) _⦋0⦌}
    (l : (verdierNativeLongHomTarget d).Edge a b)
    (r : (verdierNativeLongHomTarget d).Edge b c) (hb : b = a)
    (hl : l.edge = (Truncated.Edge.id
      (X := (truncation 2).obj (verdierNativeLongHomTarget d)) a).edge) :
    ∃ e : (verdierNativeLongHomTarget d).Edge a c,
      ∃ _T : SSet.Edge.CompStruct l r e, e.edge = r.edge := by
  let e := r.ofEq hb rfl
  let t := SSet.Edge.CompStruct.idComp e
  exact ⟨e, t.ofEq (f₀₁ := l) (f₁₂ := r) (f₀₂ := e) hl.symm rfl rfl, rfl⟩

private theorem readoutDirectTriangle_at
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) _⦋0⦌)
    (hsame : ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 1)).app
      (Opposite.op ⦋0⦌) x =
      ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
        (Opposite.op ⦋0⦌) x)
    (hunit : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x).edge =
      (Truncated.Edge.id (X := (truncation 2).obj (verdierNativeLongHomTarget d))
        (((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
          (Opposite.op ⦋0⦌) x)).edge) :
    ∃ e : (verdierNativeLongHomTarget d).Edge
      (((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
        (Opposite.op ⦋0⦌) x)
      ((SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)).app (Opposite.op ⦋0⦌) x),
      ∃ _T : SSet.Edge.CompStruct
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL) x) e,
        e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
          (verdierLowerNativeReadoutHomotopy d L hL) x).edge := by
  exact nativeReadoutLeftUnitTriangle d _ _ hsame hunit


/-- 概要：直接端では同じ二実成分の合成を、元の下側読出し成分そのものへ指定できる。
方針：元の全 S• 比較の直接端成分が実恒等辺であることを単位二単体へ代入する。
規約：合成辺の実一単体を同じ読出し成分へ厳密に戻す。
使われ方：全境界合成二単体の直接端側の実指定面。 -/
theorem verdierReadoutDirectBoundaryTriangle_exists :
    let x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) _⦋0⦌ :=
      ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath)
    ∃ e : (verdierNativeLongHomTarget d).Edge
      (((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
        (Opposite.op ⦋0⦌) x)
      ((SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)).app (Opposite.op ⦋0⦌) x),
      ∃ _T : SSet.Edge.CompStruct
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL) x) e,
        e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
          (verdierLowerNativeReadoutHomotopy d L hL) x).edge := by
  have hbSmall : (verdierOriginalNativeHomFamily d 1).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath) =
      (verdierOriginalNativeHomFamily d 0).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleDirectPath) := by
    have h := verdierOriginalNativeHomFamily_same_direct d 1 0
    rw [coherentTriangleDirectVertexMap, SSet.yonedaEquiv_symm_comp,
      SSet.yonedaEquiv_symm_comp] at h
    exact SSet.yonedaEquiv.symm.injective h
  exact readoutDirectTriangle_at d L hL _ (congrArg ULift.up hbSmall)
    (verdierOriginalFullSCoreHomotopy_up_direct_edge d 0 1)

/-- 概要：合成端では同じ二実成分の合成を、元の全 S• 比較の成分そのものへ指定できる。
方針：実下側読出しの合成端成分が実恒等辺であることを単位二単体へ代入する。
規約：元の全時刻合成端条件に条件付き。新たな存在入力は取らない。
使われ方：全境界合成二単体の合成端側の実指定面。 -/
theorem verdierReadoutFullBoundaryTriangle_exists
    (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1]) :
    let x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) _⦋0⦌ :=
      ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)
    ∃ e : (verdierNativeLongHomTarget d).Edge
      (((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
        (Opposite.op ⦋0⦌) x)
      ((SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1)).app (Opposite.op ⦋0⦌) x),
      ∃ _T : SSet.Edge.CompStruct
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL) x) e,
        e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x).edge := by
  let x : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) _⦋0⦌ :=
    ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)
  let a := ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0)).app
    (Opposite.op ⦋0⦌) x
  let b := ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 1)).app
    (Opposite.op ⦋0⦌) x
  let c := (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
    (verdierNativeCompositePoint d 1)).app (Opposite.op ⦋0⦌) x
  let l : (verdierNativeLongHomTarget d).Edge a b :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierReadoutUpperComparison d) x
  let r : (verdierNativeLongHomTarget d).Edge b c :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierLowerNativeReadoutHomotopy d L hL) x
  have hc : c = verdierNativeCompositePoint d 1 := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := verdierNativeLongHomTarget d)
      (verdierNativeCompositePoint d 1) 0 = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _
  have hr : r.edge = (Truncated.Edge.id
      (X := (truncation 2).obj (verdierNativeLongHomTarget d)) c).edge :=
    (verdierLowerNativeReadoutHomotopy_full_edge d L hL hfull).trans
      (congrArg (fun v => (Truncated.Edge.id
        (X := (truncation 2).obj (verdierNativeLongHomTarget d)) v).edge) hc.symm)
  have hb : b = c :=
    r.src_eq.symm.trans ((congrArg ((verdierNativeLongHomTarget d).δ 1) hr).trans
      (Truncated.Edge.id (X := (truncation 2).obj (verdierNativeLongHomTarget d)) c).src_eq)
  let e : (verdierNativeLongHomTarget d).Edge a c := l.ofEq rfl hb
  let t := SSet.Edge.CompStruct.compId e
  have ht : SSet.Edge.CompStruct (X := verdierNativeLongHomTarget d) l r e :=
    t.ofEq (f₀₁ := l) (f₁₂ := r) (f₀₂ := e) rfl hr.symm rfl
  exact ⟨e, ht, rfl⟩

end SerrePositivity.KST.Fibration
