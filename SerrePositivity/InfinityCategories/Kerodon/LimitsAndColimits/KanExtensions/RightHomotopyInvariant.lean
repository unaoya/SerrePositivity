module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportEdgeHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定自然変換の h での等式による右 Kan 拡張条件の不変性。
方針：slice で制限した基底の辺の同じホモトピー類から、比較錐の同型を作る。
規約：固定図式上の錐の圏で同型を得る。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG）、右 Kan 拡張を自然変換の類で扱うための接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：h で等しい指定自然変換の右比較錐は固定図式上で同型。
方針：辺の類の制限と、cocartesian な輸送の基底ホモトピー不変性を組み合わせる。
規約：比較錐の輸送はそれぞれ任意に選べる。
使われ方：右 Kan 拡張条件の h 不変性。 -/
lemma RightKanConeTransport.coneFamily_iso_of_homMk_eq
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α β : SSet.Homotopy (δ ≫ F) F₀} {c : C _⦋0⦌}
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F α c) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ F₀ F β c) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv _ t.cone) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv _ s.cone)) := by
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction J D
  let a := SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c).val)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c)
  let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cone.val) :=
    { edge := t.edge.edge
      src_eq := t.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := t.edge.tgt_eq }
  let f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cone.val) :=
    { edge := s.edge.edge
      src_eq := s.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := s.edge.tgt_eq }
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (show e.edge = t.edge.edge from rfl)).2
      t.edge_cocartesian
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (show f.edge = s.edge.edge from rfl)).2
      s.edge_cocartesian
  have hy : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cone.val) = b :=
    congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cone.property
  have hz : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cone.val) = b :=
    congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cone.property
  have htEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a p b e hy).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry t.family ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J)).app D) =
      SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ▷ Δ[1]) ≫ α.h))
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, t.diagram]
  have hsEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a p b f hz).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp β (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry s.family ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] J)).app D) =
      SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ▷ Δ[1]) ≫ β.h))
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry, s.diagram]
  have hlocal : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c))) =
      SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp β (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, h]
  have hbase : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a p b e hy) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a p b f hz) := by
    apply Arrow.mk_injective _ _
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ htEdge).trans
      ((congrArg Arrow.mk hlocal).trans
        (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hsEdge).symm)
  obtain ⟨v, w, hv, hw, ⟨i⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanTransportEndVertexIso_of_homMk_eq a p b e f hy hz he hf hbase
  have hv' : v = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv _ t.cone := Subtype.ext hv
  have hw' : w = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv _ s.cone := Subtype.ext hw
  rw [hv', hw'] at i
  exact ⟨i⟩

/-- 概要：右 Kan 拡張条件は指定自然変換の h での類だけに依存する。
方針：輸送を選び、固定図式上の錐の同型によって極限性を移す。
規約：α と β は同じ両端を持つ。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG） の右側。 -/
@[kerodon 02YG]
lemma isRightKanExtension_iff_of_homMk_eq {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α β : SSet.Homotopy (δ ≫ F) F₀)
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F β := by
  suffices hforward : ∀ (α β : SSet.Homotopy (δ ≫ F) F₀),
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F β from
    ⟨hforward α β h, hforward β α h.symm⟩
  intro α β hh hα c
  obtain ⟨t, ht⟩ := hα c
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanConeTransport_nonempty δ F₀ F β c
  obtain ⟨i⟩ := t.coneFamily_iso_of_homMk_eq hh s
  refine ⟨s, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_isTerminalVertex_coneFamily] at ht ⊢
  exact ht.of_vertexIso i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
