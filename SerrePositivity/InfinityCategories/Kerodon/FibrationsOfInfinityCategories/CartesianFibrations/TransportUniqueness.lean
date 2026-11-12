module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCosliceFiber

/-!
概要：同じ始点と基底の辺を持つ cocartesian な輸送の終点の一意性。
方針：持ち上げの可縮な空間から基底の終点の fiber への評価射を作る。
規約：同型を元の圏だけでなく、指定した基底の頂点上の厳密な fiber で得る。
使われ方：Kerodon §5.1.4（Tag 01U9）、B4 の比較錐の輸送の選択不変性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cocartesian な持ち上げの空間から基底の終点の fiber への評価。
方針：coslice の射影を、基底の固定条件を使って fiber へ持ち上げる。
規約：始点 a と基底の辺 s を固定する。
使われ方：輸送の終点の fiber 内での同型。 -/
def transportTarget {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceι a p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) (by
    have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a ≫ p =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro σ
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ σ.val ≫ p) =
        SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (σ.val ≫ p))
      rfl
    simp only [Category.assoc]
    rw [hw, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceι a p),
      ← Category.assoc]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：指定した基底上の cocartesian な coslice 頂点を選択の空間へ入れる。
方針：cocartesian 性による全部分複体と、基底の固定条件による fiber を順に取る。
規約：高次の全部分複体の条件は零単体で恒等写像に帰着する。
使われ方：実際の輸送の比較。 -/
def transportChoice {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌)
    (hσ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) σ = s)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p σ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s) _⦋0⦌ := by
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCoslice a p) _⦋0⦌ := ⟨σ, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, CategoryTheory.Functor.map_id_apply]
    exact hc⟩
  exact ⟨v, by change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app _ σ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant s 0
               rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact hσ⟩

/-- 概要：点の coslice の零単体は表す辺から決まる。
方針：標準区間との同型と Yoneda 同値の単射性を使う。
規約：端点条件の証明の表示を区別しない。
使われ方：輸送の基底の辺の一致から fiber 条件を得る。 -/
lemma F1B.Fibrations.pointCosliceVertexEdge_injective {E : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    {σ τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌}
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a σ).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a τ).edge) : σ = τ := by
  apply Subtype.ext
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  exact SSet.yonedaEquiv.injective h

/-- 概要：基底の辺に一致する cocartesian な辺を選択の空間へ入れる。
方針：辺を coslice の頂点に戻し、基底での一致と cocartesian 性を確認する。
規約：始点は a、基底の辺は s で指定する。
使われ方：比較錐の輸送の辺から可縮な選択空間への接続。 -/
def transportEdgeChoice {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hs : p.app (Opposite.op ⦋1⦌) e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge (a ≫ p) s).edge)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s) _⦋0⦌ :=
  transportChoice a p s (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e) (by
    apply F1B.Fibrations.pointCosliceVertexEdge_injective (a ≫ p)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge, hs]) (by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge a e)).2 he)

/-- 概要：辺から作った選択の評価の元の頂点は辺の終点。
方針：coslice に戻した辺の表示を終点で評価する。
規約：fiber の固定条件の証明には依存しない。
使われ方：選択空間の同型を具体的な比較錐に適用する。 -/
lemma transportEdgeChoice_target_val {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hs : p.app (Opposite.op ⦋1⦌) e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge (a ≫ p) s).edge)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    ((transportTarget a p s).app (Opposite.op ⦋0⦌)
      (transportEdgeChoice a p s e hs he)).val = y := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e) = y
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e)).tgt_eq
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge] at h
  exact h.symm.trans e.tgt_eq

/-- 概要：cocartesian な輸送の二つの選択は終点の厳密な fiber で同型。
方針：持ち上げの可縮な空間の頂点の一意性を評価射で移す。
規約：p の cocartesian fibration 性だけを要求する。
使われ方：B4 の輸送の選択不変性の一般部分。 -/
def transportTargetIso {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌)
    (t v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s))
      ((transportTarget a p s).app (Opposite.op ⦋0⦌) t)
      ((transportTarget a p s).app (Opposite.op ⦋0⦌) v) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceFiber_isContractibleKan a p s
  have := hc.kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex t) (hc.isTerminalVertex v))
    (transportTarget a p s)

/-- 概要：同じ始点と基底の辺を持つ二つの cocartesian な辺の終点は同じ fiber で同型。
方針：両辺を可縮な選択空間へ入れ、その終点の評価を使う。
規約：fiber の基点と両頂点を存在量化し、元の頂点との厳密な等式を保持する。
使われ方：指定自然変換に沿う比較錐の選択不変性。 -/
lemma exists_kanTransportEndVertexIso {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] {x y z : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x z)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p f)
    (hbase : p.app (Opposite.op ⦋1⦌) e.edge = p.app (Opposite.op ⦋1⦌) f.edge) :
    ∃ (b : B _⦋0⦌) (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌),
      v.val = y ∧ w.val = z ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v w) := by
  let a := SSet.yonedaEquiv.symm x
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y :=
    { edge := e.edge
      src_eq := e.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply x).symm
      tgt_eq := e.tgt_eq }
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) z :=
    { edge := f.edge
      src_eq := f.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply x).symm
      tgt_eq := f.tgt_eq }
  let eb : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (SSet.yonedaEquiv (a ≫ p)) (p.app (Opposite.op ⦋0⦌) y) :=
    { edge := p.app (Opposite.op ⦋1⦌) e.edge
      src_eq := (e'.map ((truncation 2).map p)).src_eq.trans
        (SSet.yonedaEquiv_comp a p).symm
      tgt_eq := (e.map ((truncation 2).map p)).tgt_eq }
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge (a ≫ p) eb
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e' :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (show e'.edge = e.edge from rfl)).2 he
  have hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p f' :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (show f'.edge = f.edge from rfl)).2 hf
  have hes : p.app (Opposite.op ⦋1⦌) e'.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge (a ≫ p) s).edge :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge (a ≫ p) eb).symm
  have hfs : p.app (Opposite.op ⦋1⦌) f'.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge (a ≫ p) s).edge := hbase.symm.trans hes
  let t := transportEdgeChoice a p s e' hes he'
  let v := transportEdgeChoice a p s f' hfs hf'
  refine ⟨_, (transportTarget a p s).app _ t, (transportTarget a p s).app _ v,
    transportEdgeChoice_target_val a p s e' hes he',
    transportEdgeChoice_target_val a p s f' hfs hf', ?_⟩
  exact ⟨transportTargetIso a p s t v⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
