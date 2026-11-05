module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierArrowLifting
public import SerrePositivity.KST.LocalizingInvariants.ConeLegTriangle
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.Stable.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Core.RightFibrationReflection
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport
public import SerrePositivity.KST.LocalizingInvariants.ExactFiniteLimitPreservation

/-!
概要：商で指定された有限錐を、同じ全錐比較と実分母付きの元の錐へ戻す。
方針：元の有限図式の極限に商錐を比較し、一つの実右分数を slice の最終ホーンへ戻す。
規約：商の指定錐を全図式で保持し、頂点比較の一次単体は同じ実分母の像と厳密一致する。
使われ方：零次の元の core 逆像商比較に対する有限錐の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement
end SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 同じ指定商錐への実 slice 可逆辺と、その頂点辺を与える元の実分母。 -/
structure VerdierQuotientConeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} (p : K ⟶ B.obj) (x : B.obj _⦋0⦌) (t : JoinCone (p ≫ q.hom)) where
  cone : JoinCone p
  denominator : Truncated.Edge (X := (truncation 2).obj B.obj) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.cone.vertex x
  denominator_mem : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.denominator.edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i
  comparison : Truncated.Edge (X := (truncation 2).obj (sliceOver (p ≫ q.hom)))
    (mapJoinCone q.hom _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.cone) t
  comparison_edge : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.comparison.map ((truncation 2).map
    (sliceOverProjection (p ≫ q.hom)))).edge = (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.denominator.map ((truncation 2).map q.hom)).edge
  isInvertible : IsInvertibleEdge (X := sliceOver (p ≫ q.hom)) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.comparison

/-- 元の有限図式上の指定商錐を、一つの元の実分母と同じ全比較辺で回収する。 -/
lemma exists_verdierQuotientConeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} [K.Finite] (p : K ⟶ B.obj) (x : B.obj _⦋0⦌)
    (t : JoinCone (p ≫ q.hom)) (hx : t.vertex = q.hom.app (Opposite.op ⦋0⦌) x) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement h p x t) := by
  let : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable B.obj
  obtain ⟨c, hc⟩ := HasFiniteLimits.hasLimit p
  have hqc := exactMap_map_isLimit_finite q c hc
  obtain ⟨e⟩ := hqc.nonempty_edge t
  let ep := e.map ((truncation 2).map (sliceOverProjection (p ≫ q.hom)))
  let f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) c.vertex) :=
    ⟨ep.edge, ep.src_eq.trans hx, ep.tgt_eq.trans (mapJoinCone_vertex q.hom c)⟩
  obtain ⟨y, s, g, hs, ⟨T⟩⟩ := verdierProjection_edge_fraction h f
  obtain ⟨F, hF₁, hFp⟩ := rightFibration_liftEdge_target (sliceOverProjection p) c g
  let σ := SSet.yonedaEquiv F
  let d : JoinCone p := (sliceOver p).δ 1 σ
  have hσ : (sliceOver p).δ 0 σ = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let u : Truncated.Edge (X := (truncation 2).obj (sliceOver p)) d c := ⟨σ, rfl, hσ⟩
  have hu : (u.map ((truncation 2).map (sliceOverProjection p))).edge = g.edge := by
    change (sliceOverProjection p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
    rw [← SSet.yonedaEquiv_comp, hFp]
    exact SSet.yonedaEquiv.apply_symm_apply g.edge
  have hd : d.vertex = y := by
    have hn := (sliceOverProjection p).naturality_apply (SimplexCategory.δ (1 : Fin 2)).op σ
    have hg := congrArg (fun z => B.obj.δ 1 z) hu
    exact hn.trans (hg.trans g.src_eq)
  let sd : Truncated.Edge (X := (truncation 2).obj B.obj) d.vertex x :=
    ⟨s.edge, s.src_eq.trans hd.symm, s.tgt_eq⟩
  let uq := u.map ((truncation 2).map (sliceOverPostcomp p q.hom))
  let r := sliceOverProjection (p ≫ q.hom)
  have huq : (uq.map ((truncation 2).map r)).edge = (g.map ((truncation 2).map q.hom)).edge := by
    change (sliceOverPostcomp p q.hom ≫ r).app (Opposite.op ⦋1⦌) u.edge = _
    rw [SerrePositivity.InfinityCategories.F1B.sliceOverPostcomp_projection]
    exact congrArg (q.hom.app (Opposite.op ⦋1⦌)) hu
  let b := ((SSet.Edge.ofTruncated (sd.map ((truncation 2).map q.hom))).ofEq
    (mapJoinCone_vertex q.hom d).symm hx.symm).toTruncated
  have Tb : Truncated.Edge.CompStruct b ep (uq.map ((truncation 2).map r)) :=
    ⟨T.simplex, T.d₂, T.d₀, T.d₁.trans huq.symm⟩
  obtain ⟨v, Tv, hv₂⟩ := derived_rightFibration_liftCompStruct r e uq b Tb
  have hv : (v.map ((truncation 2).map r)).edge = b.edge := by
    have hd₂ : (sliceOver (p ≫ q.hom)).δ 2 Tv.simplex = v.edge := Tv.d₂
    have hb₂ : C.obj.δ 2 Tb.simplex = b.edge := Tb.d₂
    calc
      _ = r.app (Opposite.op ⦋1⦌) ((sliceOver (p ≫ q.hom)).δ 2 Tv.simplex) :=
        congrArg (r.app (Opposite.op ⦋1⦌)) hd₂.symm
      _ = C.obj.δ 2 (r.app (Opposite.op ⦋2⦌) Tv.simplex) :=
        r.naturality_apply (SimplexCategory.δ (2 : Fin 3)).op Tv.simplex
      _ = C.obj.δ 2 Tb.simplex := congrArg (fun z => C.obj.δ 2 z) hv₂
      _ = _ := hb₂
  have hsd : sd.edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := hs
  have hb : IsInvertibleEdge b :=
    (isInvertibleEdge_congr (e := b) (f := sd.map ((truncation 2).map q.hom)) rfl).mpr
      ((_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.mem_weakEquivalences_iff_invertible h sd).mp hsd)
  have hvInv := derived_rightFibration_reflects_invertibleEdge r v
    ((isInvertibleEdge_congr hv).mpr hb)
  exact ⟨⟨d, sd, hsd, v, hv, hvInv⟩⟩

/-- 任意の商頂点を持つ同じ有限錐を、元の実錐へ slice 全体の同型を保って回収する。 -/
lemma exists_verdierQuotientConeIsoRefinement {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} [K.Finite] (p : K ⟶ B.obj) (t : JoinCone (p ≫ q.hom)) :
    ∃ c : JoinCone p, Nonempty (VertexIso (X := sliceOver (p ≫ q.hom))
      (mapJoinCone q.hom c) t) := by
  obtain ⟨x, ⟨e⟩⟩ := localization_isEssentiallySurjective q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)
    h.quotient t.vertex
  obtain ⟨b, hb⟩ := homotopyCategory_homMk_surjective
    (q.hom.app (Opposite.op ⦋0⦌) x) t.vertex e.hom
  have hbi : IsInvertibleEdge (X := C.obj) b := by
    change IsIso (Truncated.HomotopyCategory.homMk b)
    rw [hb]
    infer_instance
  let π := sliceOverProjection (p ≫ q.hom)
  obtain ⟨F, hF₁, hFπ⟩ := rightFibration_liftEdge_target π t b
  let σ := SSet.yonedaEquiv F
  let u : JoinCone (p ≫ q.hom) := (sliceOver (p ≫ q.hom)).δ 1 σ
  have hσ : (sliceOver (p ≫ q.hom)).δ 0 σ = t := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let w : Truncated.Edge (X := (truncation 2).obj (sliceOver (p ≫ q.hom))) u t :=
    ⟨σ, rfl, hσ⟩
  have hw : (w.map ((truncation 2).map π)).edge = b.edge := by
    change π.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
    rw [← SSet.yonedaEquiv_comp, hFπ]
    exact SSet.yonedaEquiv.apply_symm_apply b.edge
  have hu : u.vertex = q.hom.app (Opposite.op ⦋0⦌) x := by
    have hn := π.naturality_apply (SimplexCategory.δ (1 : Fin 2)).op σ
    have hg := congrArg (fun z => C.obj.δ 1 z) hw
    exact hn.trans (hg.trans b.src_eq)
  have hwi : IsIso (Truncated.HomotopyCategory.homMk w) :=
    derived_rightFibration_reflects_invertibleEdge π w ((isInvertibleEdge_congr hw).mpr hbi)
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierQuotientConeRefinement h p x u hu
  have hdi : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  exact ⟨d.cone, ⟨asIso (Truncated.HomotopyCategory.homMk d.comparison) ≪≫
    asIso (Truncated.HomotopyCategory.homMk w)⟩⟩

namespace VerdierQuotientConeRefinement
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {K : SSet.{u}} {p : K ⟶ B.obj} {x : B.obj _⦋0⦌}
  {t : JoinCone (p ≫ q.hom)} (d : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement h p x t)

/-- 同じ可逆な slice 比較辺から得る、指定した商錐全体への全関手同型。 -/
def iso : FunctorIso (d.cone.val ≫ q.hom) t.val := by
  have hv : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  exact coneFunctorIsoOfVertexIso (mapJoinCone q.hom d.cone) t
    (asIso (Truncated.HomotopyCategory.homMk d.comparison))

/-- 商で全辺が可逆な指定錐の回収錐も、商後の全辺が可逆。 -/
lemma invertsAllEdges (ht : InvertsEdges t.val Set.univ) :
    InvertsEdges (d.cone.val ≫ q.hom) Set.univ :=
  (invertsEdges_functorIso_iff d.iso Set.univ).mpr ht

/-- 同じ商錐比較と各実脚の合成は、選択済みの実二単体で保持される。 -/
def legTriangle (k : K _⦋0⦌) :
    Truncated.Edge.CompStruct
      (d.comparison.map ((truncation 2).map (sliceOverProjection (p ≫ q.hom))))
      (F2.nativeConeLeg t k) (F2.nativeConeLeg (mapJoinCone q.hom d.cone) k) :=
  coneLegComparisonTriangle d.comparison k

end VerdierQuotientConeRefinement
end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierQuotientConeIsoRefinement := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierQuotientConeRefinement := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierQuotientConeRefinement

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.comparison_edge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.comparison_edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.cone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.cone := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.cone

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.denominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.denominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.denominator_mem

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.invertsAllEdges

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.iso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.iso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.legTriangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.legTriangle := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.legTriangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierQuotientConeRefinement.mk.sizeOf_spec
