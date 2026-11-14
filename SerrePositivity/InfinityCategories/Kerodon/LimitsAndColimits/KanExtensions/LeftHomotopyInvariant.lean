module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportEdgeHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定自然変換の h での等式による左 Kan 拡張条件の不変性。
方針：余錐の制限の反転に、基底ホモトピーに沿う cocartesian 輸送の一意性を適用する。
規約：固定図式上の余錐の圏の反転で同型を得る。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG） の左側。

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

/-- 概要：h で等しい二辺を反転した辺も h で等しい。
方針：等式を左ホモトピーへ戻し、反転と左右ホモトピーの同値を使う。
規約：X は quasicategory。広い比較ファイルを import せず Core の API だけを使う。
使われ方：左比較余錐の基底の辺の類の反転。 -/
lemma kanHomMk_edgeOp_eq_of_eq {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : SSet.Truncated.HomotopyCategory.homMk e = SSet.Truncated.HomotopyCategory.homMk f) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f) := by
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk e =
      SSet.Truncated.HomotopyCategory₂.homMk f := by
    have hh := congrArg (fun m ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL e f := Quotient.exact h₂
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopic_path_eq _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopicL_edgeOp_iff e f).2 hh)

/-- 概要：h で等しい指定自然変換の左比較余錐は固定図式上で反転同型。
方針：制限した自然変換の反転の類を比較し、輸送の終点の fiber の同型を戻す。
規約：比較余錐の輸送はそれぞれ任意に選べる。
使われ方：左 Kan 拡張条件の h 不変性。 -/
lemma LeftKanCoconeTransport.coconeFamily_opIso_of_homMk_eq
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F α c) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ F₀ F β c) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)).op)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ t.cocone))
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ s.cocone))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u})
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction J D
  let po := SSet.opFunctor.map p
  let a := SSet.yonedaEquiv.symm
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c).val))
  let b := SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c))
  let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj D).op)
      (SSet.yonedaEquiv a) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val)) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge).src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge).tgt_eq }
  let f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj D).op)
      (SSet.yonedaEquiv a) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cocone.val)) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge).src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge).tgt_eq }
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting po e :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr po (show e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp t.edge).edge from rfl)).2
      t.edge_op_cocartesian
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting po f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr po (show f.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp s.edge).edge from rfl)).2
      s.edge_op_cocartesian
  have hy : po.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.val)) = b :=
    congrArg SSet.opObjEquiv.symm (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.cocone.property)
  have hz : po.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cocone.val)) = b :=
    congrArg SSet.opObjEquiv.symm (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.cocone.property)
  have htNative : p.app (Opposite.op ⦋1⦌) t.edge.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ t.family) ≫ p) =
      SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ Δ[1]) ≫ α.h))
    congr 1
    apply uncurry_injective
    dsimp only [p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction]
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    calc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ▷ Δ[1]) ≫ ((β_ T Δ[1]).hom ≫ t.family) =
          (β_ J Δ[1]).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]) ≫ t.family := rfl
      _ = (β_ J Δ[1]).hom ≫ (β_ Δ[1] J).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ Δ[1]) ≫ α.h := congrArg _ t.diagram
      _ = _ := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hsNative : p.app (Opposite.op ⦋1⦌) s.edge.edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp β (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ s.family) ≫ p) =
      SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ Δ[1]) ≫ β.h))
    congr 1
    apply uncurry_injective
    dsimp only [p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction]
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    calc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0] ▷ Δ[1]) ≫ ((β_ T Δ[1]).hom ≫ s.family) =
          (β_ J Δ[1]).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl J Δ[0]) ≫ s.family := rfl
      _ = (β_ J Δ[1]).hom ≫ (β_ Δ[1] J).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ Δ[1]) ≫ β.h := congrArg _ s.diagram
      _ = _ := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have htEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a po b e hy).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)))).edge :=
    congrArg SSet.opObjEquiv.symm htNative
  have hsEdge : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a po b f hz).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp β (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)))).edge :=
    congrArg SSet.opObjEquiv.symm hsNative
  have hlocal : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp α (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c))) =
      SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp β (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, h]
  have hlocalOp := kanHomMk_edgeOp_eq_of_eq _ _ hlocal
  have hbase : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a po b e hy) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseEdge a po b f hz) := by
    apply Arrow.mk_injective _ _
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ htEdge).trans
      ((congrArg Arrow.mk hlocalOp).trans
        (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hsEdge).symm)
  obtain ⟨v, w, hv, hw, ⟨i⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanTransportEndVertexIso_of_homMk_eq a po b e f hy hz he hf hbase
  let q := _root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c))
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
  have i' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map i q.inv
  rw [hv', hw'] at i'
  exact ⟨i'⟩

/-- 概要：左 Kan 拡張条件は指定自然変換の h での類だけに依存する。
方針：固定図式上の余錐の反転内の同型で終対象性を移す。
規約：α と β は同じ両端を持つ。
使われ方：Kerodon Remark 7.3.1.10（Tag 02YG） の左側。 -/
@[kerodon 02YG]
lemma isLeftKanExtension_iff_of_homMk_eq {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α β : SSet.Homotopy F₀ (δ ≫ F))
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β := by
  suffices hforward : ∀ (α β : SSet.Homotopy F₀ (δ ≫ F)),
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy α) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F α → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ F₀ F β from
    ⟨hforward α β h, hforward β α h.symm⟩
  intro α β hh hα c
  obtain ⟨t, ht⟩ := hα c
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCoconeTransport_nonempty δ F₀ F β c
  obtain ⟨i⟩ := t.coconeFamily_opIso_of_homMk_eq hh s
  refine ⟨s, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_isInitialVertex_coconeFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op] at ht ⊢
  exact ht.of_vertexIso i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
