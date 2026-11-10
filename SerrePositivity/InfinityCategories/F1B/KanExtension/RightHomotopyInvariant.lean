module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.ComparisonCocartesian
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TransportEdgeHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定自然変換の h での等式による右 Kan 拡張条件の不変性。
方針：slice で制限した基底の辺の同じホモトピー類から、比較錐の同型を作る。
規約：固定図式上の錐の圏で同型を得る。
使われ方：Kerodon Remark 7.3.1.10、右 Kan 拡張を自然変換の類で扱うための接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：h で等しい指定自然変換の右比較錐は固定図式上で同型。
方針：辺の類の制限と、cocartesian な輸送の基底ホモトピー不変性を組み合わせる。
規約：比較錐の輸送はそれぞれ任意に選べる。
使われ方：右 Kan 拡張条件の h 不変性。 -/
lemma RightKanConeTransport.coneFamily_iso_of_homMk_eq
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α β : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
    (t : RightKanConeTransport δ F₀ F α c) (s : RightKanConeTransport δ F₀ F β c) :
    Nonempty (VertexIso (X := coneFamily (rightKanDiagram δ F₀ c))
      (coneFamilyVertexEquiv _ t.cone) (coneFamilyVertexEquiv _ s.cone)) := by
  let J := rightKanShape δ c
  let p := coneRestriction J D
  let a := SSet.yonedaEquiv.symm (functorVertex (rightKanCanonicalCone δ F c).val)
  let b := functorVertex (rightKanDiagram δ F₀ c)
  let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (functorVertex t.cone.val) :=
    { edge := t.edge.edge
      src_eq := t.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := t.edge.tgt_eq }
  let f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (functorVertex s.cone.val) :=
    { edge := s.edge.edge
      src_eq := s.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := s.edge.tgt_eq }
  have he : HasCocartesianHornLifting p e :=
    (hasCocartesianHornLifting_congr p (show e.edge = t.edge.edge from rfl)).2
      t.edge_cocartesian
  have hf : HasCocartesianHornLifting p f :=
    (hasCocartesianHornLifting_congr p (show f.edge = s.edge.edge from rfl)).2
      s.edge_cocartesian
  have hy : p.app (Opposite.op ⦋0⦌) (functorVertex t.cone.val) = b :=
    congrArg functorVertex t.cone.property
  have hz : p.app (Opposite.op ⦋0⦌) (functorVertex s.cone.val) = b :=
    congrArg functorVertex s.cone.property
  have htEdge : (SerrePositivity.InfinityCategories.transportBaseEdge a p b e hy).edge =
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp α (rightKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry t.family ≫ (pre (joinInr Δ[0] J)).app D) =
      SSet.yonedaEquiv (curry ((rightKanProjection δ c ▷ Δ[1]) ≫ α.h))
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, t.diagram]
  have hsEdge : (SerrePositivity.InfinityCategories.transportBaseEdge a p b f hz).edge =
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp β (rightKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry s.family ≫ (pre (joinInr Δ[0] J)).app D) =
      SSet.yonedaEquiv (curry ((rightKanProjection δ c ▷ Δ[1]) ≫ β.h))
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, s.diagram]
  have hlocal : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp α (rightKanProjection δ c))) =
      SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp β (rightKanProjection δ c))) := by
    rw [functorHomotopyPrecomp_hom, functorHomotopyPrecomp_hom, h]
  have hbase : SSet.Truncated.HomotopyCategory.homMk (SerrePositivity.InfinityCategories.transportBaseEdge a p b e hy) =
      SSet.Truncated.HomotopyCategory.homMk (SerrePositivity.InfinityCategories.transportBaseEdge a p b f hz) := by
    apply Arrow.mk_injective _ _
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ htEdge).trans
      ((congrArg Arrow.mk hlocal).trans
        (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hsEdge).symm)
  obtain ⟨v, w, hv, hw, ⟨i⟩⟩ :=
    exists_kanTransportEndVertexIso_of_homMk_eq a p b e f hy hz he hf hbase
  have hv' : v = coneFamilyVertexEquiv _ t.cone := Subtype.ext hv
  have hw' : w = coneFamilyVertexEquiv _ s.cone := Subtype.ext hw
  rw [hv', hw'] at i
  exact ⟨i⟩

/-- 概要：右 Kan 拡張条件は指定自然変換の h での類だけに依存する。
方針：輸送を選び、固定図式上の錐の同型によって極限性を移す。
規約：α と β は同じ両端を持つ。
使われ方：Kerodon Remark 7.3.1.10 の右側。 -/
@[kerodon 02YG]
lemma isRightKanExtension_iff_of_homMk_eq {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α β : SSet.Homotopy (δ ≫ F) F₀)
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) :
    IsRightKanExtension δ F₀ F α ↔ IsRightKanExtension δ F₀ F β := by
  suffices hforward : ∀ (α β : SSet.Homotopy (δ ≫ F) F₀),
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) →
      IsRightKanExtension δ F₀ F α → IsRightKanExtension δ F₀ F β from
    ⟨hforward α β h, hforward β α h.symm⟩
  intro α β hh hα c
  obtain ⟨t, ht⟩ := hα c
  obtain ⟨s⟩ := rightKanConeTransport_nonempty δ F₀ F β c
  obtain ⟨i⟩ := t.coneFamily_iso_of_homMk_eq hh s
  refine ⟨s, ?_⟩
  rw [isLimitCone_iff_isTerminalVertex_coneFamily] at ht ⊢
  exact ht.of_vertexIso i

end SerrePositivity.InfinityCategories
