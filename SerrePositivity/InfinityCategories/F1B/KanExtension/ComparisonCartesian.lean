module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.Definition
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TransportUniqueness
public import SerrePositivity.InfinityCategories.F1.CoconeRestrictionOppositeFibration
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Core.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左 Kan 比較余錐の輸送の cartesian 性と選択不変性。
方針：余錐の制限を反転し、cocartesian な持ち上げの終点の一意性を使う。
規約：指定した β を保持した固定図式上の余錐を比較する。
使われ方：Kerodon Proposition 5.3.7.5、Warning 7.3.1.4、Variant 7.3.1.5。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左比較余錐の輸送は余錐全体の関手圏の辺。
方針：時間を第二因子に移し、両端を指定して curry する。
規約：始点は比較余錐、終点は標準余錐。
使われ方：輸送の cartesian 性。 -/
def LeftKanCoconeTransport.edge {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D}
    {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    SSet.Truncated.Edge (X := (truncation 2).obj
      ((ihom (join (leftKanShape δ c) (Δ[0] : SSet.{u}))).obj D))
      (functorVertex t.cocone.val) (functorVertex (leftKanCanonicalCocone δ F c).val) :=
  functorEdgeOfSimplicialHomotopy {
    h := (β_ (join (leftKanShape δ c) (Δ[0] : SSet.{u})) Δ[1]).hom ≫ t.family
    h₀ := by
      rw [← Category.assoc]
      change prismEndpoint 0 _ ≫ t.family = _
      rfl
    h₁ := by
      rw [← Category.assoc]
      change prismEndpoint 1 _ ≫ t.family = _
      exact t.finish
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }

/-- 概要：左比較余錐の輸送は余錐の制限に対して cartesian。
方針：頂点固定式を一次単体で評価し、頂点で可逆な余錐の辺の判定を使う。
規約：標的のみ quasicategory を仮定する。
使われ方：反転した制限射への cocartesian な輸送としての接続。 -/
lemma LeftKanCoconeTransport.edge_cartesian {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    IsCartesianEdge (coconeRestriction (leftKanShape δ c) D) t.edge.edge := by
  apply isCartesianEdge_coconeRestriction_of_apex t.edge
  let z := (leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋0⦌)
    ((joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have heq : (t.edge.map ((truncation 2).map
      (coconeApexEvaluation (leftKanShape δ c) D))).edge = PinchedHom.constant z 1 := by
    let w : ((Δ[1] : SSet.{u}) ⊗ Δ[0]) _⦋1⦌ :=
      ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
        PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1⟩
    have hh := ConcreteCategory.congr_hom
      (NatTrans.congr_app t.fixedVertex (Opposite.op ⦋1⦌)) w
    change t.family.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 Δ[1]),
        (joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) =
      (leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋1⦌)
        ((joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
    rw [pinchedConstant_map, pinchedConstant_map] at hh
    exact hh
  have hi := isEquivalencePathVertex_const z
  unfold IsEquivalencePathVertex at hi
  rw [intervalFunctorVertexEdge_functorVertex] at hi
  exact (isInvertibleEdge_congr heq).2 hi

/-- 概要：左比較余錐の辺を反転すると cocartesian。
方針：cartesian 辺の反転による相対ホーン充填を使う。
規約：既存の二つの cocartesian 辺の表示をここで接続する。
使われ方：輸送の選択の可縮性の一般定理への入力。 -/
lemma LeftKanCoconeTransport.edge_op_cocartesian {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    HasCocartesianHornLifting (SSet.opFunctor.map (coconeRestriction (leftKanShape δ c) D))
      (edgeOp t.edge) := by
  intro n a b ha hw
  have sq : CommSq a (horn (n + 2) 0).ι
      (SSet.opFunctor.map (coconeRestriction (leftKanShape δ c) D)) b := ⟨hw⟩
  have := t.edge_cartesian.op n a b ha sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：同じ指定自然変換を輸送した二つの左比較余錐は固定図式上で反転同型。
方針：反転した制限射の cocartesian な輸送の一意性を fiber の反転同型で移す。
規約：同型は coconeFamily の反転内であり、頂点だけの同型ではない。
使われ方：余極限性の選択不変性。 -/
lemma LeftKanCoconeTransport.coconeFamily_opIso {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t s : LeftKanCoconeTransport δ F₀ F β c) :
    Nonempty (VertexIso (X := (coconeFamily (leftKanDiagram δ F₀ c)).op)
      (SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ t.cocone))
      (SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ s.cocone))) := by
  let J := leftKanShape δ c
  let T := join J (Δ[0] : SSet.{u})
  let p := coconeRestriction J D
  have hbase : p.app (Opposite.op ⦋1⦌) t.edge.edge =
      p.app (Opposite.op ⦋1⦌) s.edge.edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ t.family) ≫ p) =
      SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ s.family) ≫ p)
    congr 1
    apply uncurry_injective
    dsimp only [p, coconeRestriction]
    rw [uncurry_pre_app, uncurry_pre_app, uncurry_curry, uncurry_curry]
    have ht : (joinInl J (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫
        ((β_ T Δ[1]).hom ≫ t.family) =
        (β_ J Δ[1]).hom ≫ (Δ[1] ◁ joinInl J Δ[0]) ≫ t.family := rfl
    have hs : (joinInl J (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫
        ((β_ T Δ[1]).hom ≫ s.family) =
        (β_ J Δ[1]).hom ≫ (Δ[1] ◁ joinInl J Δ[0]) ≫ s.family := rfl
    rw [ht, hs, t.diagram, s.diagram]
  have hbaseOp : (SSet.opFunctor.map p).app (Opposite.op ⦋1⦌) (edgeOp t.edge).edge =
      (SSet.opFunctor.map p).app (Opposite.op ⦋1⦌) (edgeOp s.edge).edge :=
    congrArg SSet.opObjEquiv.symm hbase
  obtain ⟨b, v, w, hv, hw, ⟨e⟩⟩ := exists_kanTransportEndVertexIso
    (SSet.opFunctor.map p) (edgeOp t.edge) (edgeOp s.edge)
    t.edge_op_cocartesian s.edge_op_cocartesian hbaseOp
  have hb : b = SSet.opObjEquiv.symm (functorVertex (leftKanDiagram δ F₀ c)) := by
    have hp : (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌) v.val = b :=
      v.property.trans (pinchedConstant_zero b)
    calc
      b = (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌) v.val := hp.symm
      _ = (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (functorVertex t.cocone.val)) := congrArg _ hv
      _ = SSet.opObjEquiv.symm (functorVertex (leftKanDiagram δ F₀ c)) :=
        congrArg SSet.opObjEquiv.symm (congrArg functorVertex t.cocone.property)
  subst b
  let q := vertexFiberOpIso p (functorVertex (leftKanDiagram δ F₀ c))
  have hv' : q.inv.app (Opposite.op ⦋0⦌) v =
      SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ t.cocone) := by
    apply SSet.opObjEquiv.injective
    apply Subtype.ext
    exact congrArg SSet.opObjEquiv hv
  have hw' : q.inv.app (Opposite.op ⦋0⦌) w =
      SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ s.cocone) := by
    apply SSet.opObjEquiv.injective
    apply Subtype.ext
    exact congrArg SSet.opObjEquiv hw
  have e' := VertexIso.map e q.inv
  rw [hv', hw'] at e'
  exact ⟨e'⟩

/-- 概要：左 Kan 比較余錐の余極限性は輸送の選択に依存しない。
方針：固定図式上の余錐の始対象性を反転して同型に沿って移す。
規約：指定した β は同じである。
使われ方：Kerodon Warning 7.3.1.4 の左側の選択不変性。 -/
@[kerodon 02YB]
lemma LeftKanCoconeTransport.isColimitCone_iff {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t s : LeftKanCoconeTransport δ F₀ F β c) :
    IsColimitCone t.cocone ↔ IsColimitCone s.cocone := by
  obtain ⟨e⟩ := t.coconeFamily_opIso s
  rw [isColimitCone_iff_isInitialVertex_coconeFamily,
    isColimitCone_iff_isInitialVertex_coconeFamily,
    isInitialVertex_iff_isTerminalVertex_op, isInitialVertex_iff_isTerminalVertex_op]
  exact isTerminalVertex_iff_of_vertexIso e

/-- 概要：左 Kan 拡張条件は全ての輸送の比較余錐の余極限性と同値。
方針：選択不変性と輸送の存在を組み合わせる。
規約：標的 D の quasicategory 性を使う。
使われ方：比較余錐の合成の選択を条件から除く。 -/
lemma isLeftKanExtension_iff_forall_transport {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    IsLeftKanExtension δ F₀ F β ↔
      ∀ (c : C _⦋0⦌) (t : LeftKanCoconeTransport δ F₀ F β c), IsColimitCone t.cocone := by
  constructor
  · intro h c t
    obtain ⟨s, hs⟩ := h c
    exact (s.isColimitCone_iff t).1 hs
  · intro h c
    obtain ⟨t⟩ := leftKanCoconeTransport_nonempty δ F₀ F β c
    exact ⟨t, h c t⟩

end SerrePositivity.InfinityCategories
