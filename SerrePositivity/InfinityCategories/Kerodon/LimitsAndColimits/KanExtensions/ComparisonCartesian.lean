module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionOppositeFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左 Kan 比較余錐の輸送の cartesian 性と選択不変性。
方針：余錐の制限を反転し、cocartesian な持ち上げの終点の一意性を使う。
規約：指定した β を保持した固定図式上の余錐を比較する。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW）、Warning 7.3.1.4、Variant 7.3.1.5。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：左比較余錐の輸送は余錐全体の関手圏の辺。
方針：時間を第二因子に移し、両端を指定して curry する。
規約：始点は比較余錐、終点は標準余錐。
使われ方：輸送の cartesian 性。 -/
def LeftKanCoconeTransport.edge {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D}
    {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    SSet.Truncated.Edge (X := (truncation 2).obj
      ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}))).obj D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy {
    h := (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) Δ[1]).hom ≫ t.family
    h₀ := by
      rw [← Category.assoc]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ t.family = _
      rfl
    h₁ := by
      rw [← Category.assoc]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ t.family = _
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
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D) t.edge.edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isCartesianEdge_coconeRestriction_of_apex t.edge
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have heq : (t.edge.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeApexEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D))).edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1 := by
    let w : ((Δ[1] : SSet.{u}) ⊗ Δ[0]) _⦋1⦌ :=
      ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1⟩
    have hh := ConcreteCategory.congr_hom
      (NatTrans.congr_app t.fixedVertex (Opposite.op ⦋1⦌)) w
    change t.family.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 Δ[1]),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at hh
    exact hh
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const z
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr heq).2 hi

/-- 概要：左比較余錐の辺を反転すると cocartesian。
方針：cartesian 辺の反転による相対ホーン充填を使う。
規約：既存の二つの cocartesian 辺の表示をここで接続する。
使われ方：輸送の選択の可縮性の一般定理への入力。 -/
lemma LeftKanCoconeTransport.edge_op_cocartesian {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge) := by
  intro n a b ha hw
  have sq : CommSq a (horn (n + 2) 0).ι
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) D)) b := ⟨hw⟩
  have := t.edge_cartesian.op n a b ha sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：同じ指定自然変換を輸送した二つの左比較余錐は固定図式上で反転同型。
方針：反転した制限射の cocartesian な輸送の一意性を fiber の反転同型で移す。
規約：同型は coconeFamily の反転内であり、頂点だけの同型ではない。
使われ方：余極限性の選択不変性。 -/
lemma LeftKanCoconeTransport.coconeFamily_opIso {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)).op)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ t.cocone))
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ s.cocone))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J D
  have hbase : p.app (Opposite.op ⦋1⦌) t.edge.edge =
      p.app (Opposite.op ⦋1⦌) s.edge.edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ t.family) ≫ p) =
      SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ s.family) ≫ p)
    congr 1
    apply uncurry_injective
    dsimp only [p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction]
    rw [uncurry_pre_app, uncurry_pre_app, uncurry_curry, uncurry_curry]
    have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫
        ((β_ T Δ[1]).hom ≫ t.family) =
        (β_ J Δ[1]).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]) ≫ t.family := rfl
    have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫
        ((β_ T Δ[1]).hom ≫ s.family) =
        (β_ J Δ[1]).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]) ≫ s.family := rfl
    rw [ht, hs, t.diagram, s.diagram]
  have hbaseOp : (SSet.opFunctor.map p).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge).edge =
      (SSet.opFunctor.map p).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge).edge :=
    congrArg SSet.opObjEquiv.symm hbase
  obtain ⟨b, v, w, hv, hw, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanTransportEndVertexIso
    (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge)
    t.edge_op_cocartesian s.edge_op_cocartesian hbaseOp
  have hb : b = SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) := by
    have hp : (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌) v.val = b :=
      v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b)
    calc
      b = (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌) v.val := hp.symm
      _ = (SSet.opFunctor.map p).app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val)) := congrArg _ hv
      _ = SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)) :=
        congrArg SSet.opObjEquiv.symm (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.property)
  subst b
  let q := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c))
  have hv' : q.inv.app (Opposite.op ⦋0⦌) v =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ t.cocone) := by
    apply SSet.opObjEquiv.injective
    apply Subtype.ext
    exact congrArg SSet.opObjEquiv hv
  have hw' : q.inv.app (Opposite.op ⦋0⦌) w =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ s.cocone) := by
    apply SSet.opObjEquiv.injective
    apply Subtype.ext
    exact congrArg SSet.opObjEquiv hw
  have e' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e q.inv
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
    (t s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t.cocone ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone s.cocone := by
  obtain ⟨e⟩ := t.coconeFamily_opIso s
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_isInitialVertex_coconeFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_isInitialVertex_coconeFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_of_vertexIso e

/-- 概要：左 Kan 拡張条件は全ての輸送の比較余錐の余極限性と同値。
方針：選択不変性と輸送の存在を組み合わせる。
規約：標的 D の quasicategory 性を使う。
使われ方：比較余錐の合成の選択を条件から除く。 -/
lemma isLeftKanExtension_iff_forall_transport {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β ↔
      ∀ (c : C _⦋0⦌) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone t.cocone := by
  constructor
  · intro h c t
    obtain ⟨s, hs⟩ := h c
    exact (s.isColimitCone_iff t).1 hs
  · intro h c
    obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCoconeTransport_nonempty δ F₀ F β c
    exact ⟨t, h c t⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
