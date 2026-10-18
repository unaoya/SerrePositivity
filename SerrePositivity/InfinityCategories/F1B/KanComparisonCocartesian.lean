module

public import SerrePositivity.InfinityCategories.F1B.KanExtension
public import SerrePositivity.InfinityCategories.F1B.KanTransportUniqueness
public import SerrePositivity.InfinityCategories.Core.ConeRestrictionCocartesianFibration
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.Core.LimitConeFamily

/-!
概要：右 Kan 比較錐の輸送を錐の制限の cocartesian な辺にする。
方針：輸送を curry し、頂点固定条件から錐の頂点で可逆であることを示す。
規約：指定した自然変換の辺を全時間で保持する。
使われ方：Kerodon Proposition 5.3.7.5、右比較錐の選択不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右比較錐の輸送は錐全体の関手圏の辺を表す。
方針：族をその二つの端点とともに curry する。
規約：始点は標準錐、終点は比較錐。
使われ方：輸送の cocartesian 性。 -/
def RightKanConeTransport.edge {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D}
    {F : C ⟶ D} {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    SSet.Truncated.Edge (X := (truncation 2).obj
      ((ihom (join (Δ[0] : SSet.{u}) (rightKanShape δ c))).obj D))
      (functorVertex (rightKanCanonicalCone δ F c).val) (functorVertex t.cone.val) :=
  functorEdgeOfSimplicialHomotopy {
    h := t.family
    h₀ := t.start
    h₁ := rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨⟨x, hx⟩, i⟩
      exact False.elim hx }

/-- 概要：右比較錐の輸送は錐の制限に対して cocartesian。
方針：固定した頂点の辺は恒等辺なので、頂点で可逆な錐の辺の判定を使う。
規約：D は quasicategory、添字圏に充填性は要求しない。
使われ方：同じ自然変換に沿う二つの比較錐の比較。 -/
lemma RightKanConeTransport.edge_cocartesian {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t : RightKanConeTransport δ F₀ F α c) :
    HasCocartesianHornLifting (coneRestriction (rightKanShape δ c) D) t.edge := by
  apply hasCocartesianHornLifting_coneRestriction_of_apex
  let apex := (joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  let z := (rightKanCanonicalCone δ F c).val.app (Opposite.op ⦋0⦌) apex
  have heq : (t.edge.map ((truncation 2).map
      (coneApexEvaluation (rightKanShape δ c) D))).edge = PinchedHom.constant z 1 := by
    let w : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋1⦌ :=
      ⟨PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1,
        SSet.yonedaEquiv (𝟙 Δ[1])⟩
    have hh := ConcreteCategory.congr_hom
      (NatTrans.congr_app t.fixedVertex (Opposite.op ⦋1⦌)) w
    change t.family.app (Opposite.op ⦋1⦌)
      ((joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1),
          SSet.yonedaEquiv (𝟙 Δ[1])) =
      (rightKanCanonicalCone δ F c).val.app (Opposite.op ⦋1⦌)
        ((joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
    rw [pinchedConstant_map, pinchedConstant_map] at hh
    exact hh
  have hi := isEquivalencePathVertex_const z
  unfold IsEquivalencePathVertex at hi
  rw [intervalFunctorVertexEdge_functorVertex] at hi
  exact (isInvertibleEdge_congr heq).2 hi

/-- 概要：同じ指定自然変換を輸送した二つの右比較錐は同じ図式上で同型。
方針：錐の制限の cocartesian な持ち上げの終点の fiber 内の同型を使う。
規約：同型は coneFamily 内。頂点の hD での同型だけで代用しない。
使われ方：比較錐の選択不変性。 -/
lemma RightKanConeTransport.coneFamily_iso {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t s : RightKanConeTransport δ F₀ F α c) :
    Nonempty (VertexIso (X := coneFamily (rightKanDiagram δ F₀ c))
      (coneFamilyVertexEquiv _ t.cone) (coneFamilyVertexEquiv _ s.cone)) := by
  have hbase : (coneRestriction (rightKanShape δ c) D).app (Opposite.op ⦋1⦌) t.edge.edge =
      (coneRestriction (rightKanShape δ c) D).app (Opposite.op ⦋1⦌) s.edge.edge := by
    change SSet.yonedaEquiv (curry t.family ≫ (pre (joinInr Δ[0] _)).app D) =
      SSet.yonedaEquiv (curry s.family ≫ (pre (joinInr Δ[0] _)).app D)
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_pre_app, uncurry_curry, uncurry_curry, t.diagram, s.diagram]
  obtain ⟨b, v, w, hv, hw, ⟨e⟩⟩ := exists_kanTransportEndVertexIso
    (coneRestriction (rightKanShape δ c) D) t.edge s.edge
    t.edge_cocartesian s.edge_cocartesian hbase
  have hb : b = functorVertex (rightKanDiagram δ F₀ c) := by
    have hp : (coneRestriction (rightKanShape δ c) D).app (Opposite.op ⦋0⦌) v.val = b :=
      v.property.trans (pinchedConstant_zero b)
    calc
      b = (coneRestriction (rightKanShape δ c) D).app (Opposite.op ⦋0⦌) v.val := hp.symm
      _ = (coneRestriction (rightKanShape δ c) D).app (Opposite.op ⦋0⦌)
          (functorVertex t.cone.val) := congrArg _ hv
      _ = functorVertex (rightKanDiagram δ F₀ c) := congrArg functorVertex t.cone.property
  subst b
  have hv' : v = coneFamilyVertexEquiv _ t.cone := Subtype.ext hv
  have hw' : w = coneFamilyVertexEquiv _ s.cone := Subtype.ext hw
  rw [hv', hw'] at e
  exact ⟨e⟩

/-- 概要：右 Kan 比較錐の極限性は輸送の選択に依存しない。
方針：固定図式上の錐の模型で終対象性を同型に沿って移す。
規約：指定した α は同じである。α の h での変更は別の課題。
使われ方：Kerodon Warning 7.3.1.4 の比較錐の合成の選択不変性。 -/
lemma RightKanConeTransport.isLimitCone_iff {K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (t s : RightKanConeTransport δ F₀ F α c) : IsLimitCone t.cone ↔ IsLimitCone s.cone := by
  obtain ⟨e⟩ := t.coneFamily_iso s
  rw [isLimitCone_iff_isTerminalVertex_coneFamily,
    isLimitCone_iff_isTerminalVertex_coneFamily]
  exact isTerminalVertex_iff_of_vertexIso e

/-- 概要：右 Kan 拡張条件は全ての輸送の比較錐の極限性としても書ける。
方針：一つの輸送での極限性を選択不変性で全てへ移し、逆は輸送の存在を使う。
規約：輸送の存在は D の quasicategory 性から得る。
使われ方：比較錐の合成の選択を条件から除く。 -/
lemma isRightKanExtension_iff_forall_transport {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    IsRightKanExtension δ F₀ F α ↔
      ∀ (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ F α c), IsLimitCone t.cone := by
  constructor
  · intro h c t
    obtain ⟨s, hs⟩ := h c
    exact (s.isLimitCone_iff t).1 hs
  · intro h c
    obtain ⟨t⟩ := rightKanConeTransport_nonempty δ F₀ F α c
    exact ⟨t, h c t⟩

end SerrePositivity.InfinityCategories
