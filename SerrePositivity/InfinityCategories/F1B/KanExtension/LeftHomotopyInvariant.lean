module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.ComparisonCartesian
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TransportEdgeHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.MappingSpaceLeft
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定自然変換の h での等式による左 Kan 拡張条件の不変性。
方針：余錐の制限の反転に、基底ホモトピーに沿う cocartesian 輸送の一意性を適用する。
規約：固定図式上の余錐の圏の反転で同型を得る。
使われ方：Kerodon Remark 7.3.1.10 の左側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：h で等しい二辺を反転した辺も h で等しい。
方針：等式を左ホモトピーへ戻し、反転と左右ホモトピーの同値を使う。
規約：X は quasicategory。広い比較ファイルを import せず Core の API だけを使う。
使われ方：左比較余錐の基底の辺の類の反転。 -/
lemma kanHomMk_edgeOp_eq_of_eq {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : SSet.Truncated.HomotopyCategory.homMk e = SSet.Truncated.HomotopyCategory.homMk f) :
    SSet.Truncated.HomotopyCategory.homMk (edgeOp e) =
      SSet.Truncated.HomotopyCategory.homMk (edgeOp f) := by
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk e =
      SSet.Truncated.HomotopyCategory₂.homMk f := by
    have hh := congrArg (fun m ↦ (pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL e f := Quotient.exact h₂
  exact homotopic_path_eq _ ((homotopicL_edgeOp_iff e f).2 hh)

/-- 概要：h で等しい指定自然変換の左比較余錐は固定図式上で反転同型。
方針：制限した自然変換の反転の類を比較し、輸送の終点の fiber の同型を戻す。
規約：比較余錐の輸送はそれぞれ任意に選べる。
使われ方：左 Kan 拡張条件の h 不変性。 -/
lemma LeftKanCoconeTransport.coconeFamily_opIso_of_homMk_eq
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    {α β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
    (t : LeftKanCoconeTransport δ F₀ F α c) (s : LeftKanCoconeTransport δ F₀ F β c) :
    Nonempty (VertexIso (X := (coconeFamily (leftKanDiagram δ F₀ c)).op)
      (SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ t.cocone))
      (SSet.opObjEquiv.symm (coconeFamilyVertexEquiv _ s.cocone))) := by
  let J := leftKanShape δ c
  let T := join J (Δ[0] : SSet.{u})
  let p := coconeRestriction J D
  let po := SSet.opFunctor.map p
  let a := SSet.yonedaEquiv.symm
    (SSet.opObjEquiv.symm (functorVertex (leftKanCanonicalCocone δ F c).val))
  let b := SSet.opObjEquiv.symm (functorVertex (leftKanDiagram δ F₀ c))
  let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj D).op)
      (SSet.yonedaEquiv a) (SSet.opObjEquiv.symm (functorVertex t.cocone.val)) :=
    { edge := (edgeOp t.edge).edge
      src_eq := (edgeOp t.edge).src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := (edgeOp t.edge).tgt_eq }
  let f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj D).op)
      (SSet.yonedaEquiv a) (SSet.opObjEquiv.symm (functorVertex s.cocone.val)) :=
    { edge := (edgeOp s.edge).edge
      src_eq := (edgeOp s.edge).src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := (edgeOp s.edge).tgt_eq }
  have he : HasCocartesianHornLifting po e :=
    (hasCocartesianHornLifting_congr po (show e.edge = (edgeOp t.edge).edge from rfl)).2
      t.edge_op_cocartesian
  have hf : HasCocartesianHornLifting po f :=
    (hasCocartesianHornLifting_congr po (show f.edge = (edgeOp s.edge).edge from rfl)).2
      s.edge_op_cocartesian
  have hy : po.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm (functorVertex t.cocone.val)) = b :=
    congrArg SSet.opObjEquiv.symm (congrArg functorVertex t.cocone.property)
  have hz : po.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm (functorVertex s.cocone.val)) = b :=
    congrArg SSet.opObjEquiv.symm (congrArg functorVertex s.cocone.property)
  have htNative : p.app (Opposite.op ⦋1⦌) t.edge.edge =
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp α (leftKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ t.family) ≫ p) =
      SSet.yonedaEquiv (curry ((leftKanProjection δ c ▷ Δ[1]) ≫ α.h))
    congr 1
    apply uncurry_injective
    dsimp only [p, coconeRestriction]
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    calc
      (joinInl J Δ[0] ▷ Δ[1]) ≫ ((β_ T Δ[1]).hom ≫ t.family) =
          (β_ J Δ[1]).hom ≫ (Δ[1] ◁ joinInl J Δ[0]) ≫ t.family := rfl
      _ = (β_ J Δ[1]).hom ≫ (β_ Δ[1] J).hom ≫
          (leftKanProjection δ c ▷ Δ[1]) ≫ α.h := congrArg _ t.diagram
      _ = _ := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hsNative : p.app (Opposite.op ⦋1⦌) s.edge.edge =
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp β (leftKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry ((β_ T Δ[1]).hom ≫ s.family) ≫ p) =
      SSet.yonedaEquiv (curry ((leftKanProjection δ c ▷ Δ[1]) ≫ β.h))
    congr 1
    apply uncurry_injective
    dsimp only [p, coconeRestriction]
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    calc
      (joinInl J Δ[0] ▷ Δ[1]) ≫ ((β_ T Δ[1]).hom ≫ s.family) =
          (β_ J Δ[1]).hom ≫ (Δ[1] ◁ joinInl J Δ[0]) ≫ s.family := rfl
      _ = (β_ J Δ[1]).hom ≫ (β_ Δ[1] J).hom ≫
          (leftKanProjection δ c ▷ Δ[1]) ≫ β.h := congrArg _ s.diagram
      _ = _ := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have htEdge : (SerrePositivity.InfinityCategories.transportBaseEdge a po b e hy).edge =
      (edgeOp (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp α (leftKanProjection δ c)))).edge :=
    congrArg SSet.opObjEquiv.symm htNative
  have hsEdge : (SerrePositivity.InfinityCategories.transportBaseEdge a po b f hz).edge =
      (edgeOp (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp β (leftKanProjection δ c)))).edge :=
    congrArg SSet.opObjEquiv.symm hsNative
  have hlocal : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp α (leftKanProjection δ c))) =
      SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp β (leftKanProjection δ c))) := by
    rw [functorHomotopyPrecomp_hom, functorHomotopyPrecomp_hom, h]
  have hlocalOp := kanHomMk_edgeOp_eq_of_eq _ _ hlocal
  have hbase : SSet.Truncated.HomotopyCategory.homMk (SerrePositivity.InfinityCategories.transportBaseEdge a po b e hy) =
      SSet.Truncated.HomotopyCategory.homMk (SerrePositivity.InfinityCategories.transportBaseEdge a po b f hz) := by
    apply Arrow.mk_injective _ _
    exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ htEdge).trans
      ((congrArg Arrow.mk hlocalOp).trans
        (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hsEdge).symm)
  obtain ⟨v, w, hv, hw, ⟨i⟩⟩ :=
    exists_kanTransportEndVertexIso_of_homMk_eq a po b e f hy hz he hf hbase
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
  have i' := VertexIso.map i q.inv
  rw [hv', hw'] at i'
  exact ⟨i'⟩

/-- 概要：左 Kan 拡張条件は指定自然変換の h での類だけに依存する。
方針：固定図式上の余錐の反転内の同型で終対象性を移す。
規約：α と β は同じ両端を持つ。
使われ方：Kerodon Remark 7.3.1.10 の左側。 -/
@[kerodon 02YG]
lemma isLeftKanExtension_iff_of_homMk_eq {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α β : SSet.Homotopy F₀ (δ ≫ F))
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) :
    IsLeftKanExtension δ F₀ F α ↔ IsLeftKanExtension δ F₀ F β := by
  suffices hforward : ∀ (α β : SSet.Homotopy F₀ (δ ≫ F)),
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β) →
      IsLeftKanExtension δ F₀ F α → IsLeftKanExtension δ F₀ F β from
    ⟨hforward α β h, hforward β α h.symm⟩
  intro α β hh hα c
  obtain ⟨t, ht⟩ := hα c
  obtain ⟨s⟩ := leftKanCoconeTransport_nonempty δ F₀ F β c
  obtain ⟨i⟩ := t.coconeFamily_opIso_of_homMk_eq hh s
  refine ⟨s, ?_⟩
  rw [isColimitCone_iff_isInitialVertex_coconeFamily,
    isInitialVertex_iff_isTerminalVertex_op] at ht ⊢
  exact ht.of_vertexIso i

end SerrePositivity.InfinityCategories
