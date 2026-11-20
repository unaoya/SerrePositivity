module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.VerdierArrowLifting
public import SerrePositivity.KST.LocalizingInvariants.ConeLegTriangle
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 同じ指定商錐への実 slice 可逆辺と、その頂点辺を与える元の実分母。 -/
structure VerdierQuotientConeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} (p : K ⟶ B.obj) (x : B.obj _⦋0⦌) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom)) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p
  denominator : Truncated.Edge (X := (truncation 2).obj B.obj) cone.vertex x
  denominator_mem : denominator.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
  comparison : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom cone) t
  comparison_edge : (comparison.map ((truncation 2).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ q.hom)))).edge = (denominator.map ((truncation 2).map q.hom)).edge
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)) comparison

/-- 元の有限図式上の指定商錐を、一つの元の実分母と同じ全比較辺で回収する。 -/
lemma exists_verdierQuotientConeRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} [K.Finite] (p : K ⟶ B.obj) (x : B.obj _⦋0⦌)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom)) (hx : t.vertex = q.hom.app (Opposite.op ⦋0⦌) x) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement h p x t) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p
  have hqc := exactMap_map_isLimit_finite q c hc
  obtain ⟨e⟩ := hqc.nonempty_edge t
  let ep := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ q.hom)))
  let f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) c.vertex) :=
    ⟨ep.edge, ep.src_eq.trans hx, ep.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex q.hom c)⟩
  obtain ⟨y, s, g, hs, ⟨T⟩⟩ := verdierProjection_edge_fraction h f
  obtain ⟨F, hF₁, hFp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c g
  let σ := SSet.yonedaEquiv F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 σ
  have hσ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 σ = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let u : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) d c := ⟨σ, rfl, hσ⟩
  have hu : (u.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))).edge = g.edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
    rw [← SSet.yonedaEquiv_comp, hFp]
    exact SSet.yonedaEquiv.apply_symm_apply g.edge
  have hd : d.vertex = y := by
    have hn := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p).naturality_apply (SimplexCategory.δ (1 : Fin 2)).op σ
    have hg := congrArg (fun z => B.obj.δ 1 z) hu
    exact hn.trans (hg.trans g.src_eq)
  let sd : Truncated.Edge (X := (truncation 2).obj B.obj) d.vertex x :=
    ⟨s.edge, s.src_eq.trans hd.symm, s.tgt_eq⟩
  let uq := u.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q.hom))
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ q.hom)
  have huq : (uq.map ((truncation 2).map r)).edge = (g.map ((truncation 2).map q.hom)).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q.hom ≫ r).app (Opposite.op ⦋1⦌) u.edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]
    exact congrArg (q.hom.app (Opposite.op ⦋1⦌)) hu
  let b := ((SSet.Edge.ofTruncated (sd.map ((truncation 2).map q.hom))).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex q.hom d).symm hx.symm).toTruncated
  have Tb : Truncated.Edge.CompStruct b ep (uq.map ((truncation 2).map r)) :=
    ⟨T.simplex, T.d₂, T.d₀, T.d₁.trans huq.symm⟩
  obtain ⟨v, Tv, hv₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_liftCompStruct r e uq b Tb
  have hv : (v.map ((truncation 2).map r)).edge = b.edge := by
    have hd₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)).δ 2 Tv.simplex = v.edge := Tv.d₂
    have hb₂ : C.obj.δ 2 Tb.simplex = b.edge := Tb.d₂
    calc
      _ = r.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)).δ 2 Tv.simplex) :=
        congrArg (r.app (Opposite.op ⦋1⦌)) hd₂.symm
      _ = C.obj.δ 2 (r.app (Opposite.op ⦋2⦌) Tv.simplex) :=
        r.naturality_apply (SimplexCategory.δ (2 : Fin 3)).op Tv.simplex
      _ = C.obj.δ 2 Tb.simplex := congrArg (fun z => C.obj.δ 2 z) hv₂
      _ = _ := hb₂
  have hsd : sd.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := hs
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := b) (f := sd.map ((truncation 2).map q.hom)) rfl).mpr
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h sd).mp hsd)
  have hvInv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge r v
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hv).mpr hb)
  exact ⟨⟨d, sd, hsd, v, hv, hvInv⟩⟩

/-- 任意の商頂点を持つ同じ有限錐を、元の実錐へ slice 全体の同型を保って回収する。 -/
lemma exists_verdierQuotientConeIsoRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {K : SSet.{u}} [K.Finite] (p : K ⟶ B.obj) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) t) := by
  obtain ⟨x, ⟨e⟩⟩ := localization_isEssentiallySurjective q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    h.quotient t.vertex
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (q.hom.app (Opposite.op ⦋0⦌) x) t.vertex e.hom
  have hbi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) b := by
    change IsIso (Truncated.HomotopyCategory.homMk b)
    rw [hb]
    infer_instance
  let π := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ q.hom)
  obtain ⟨F, hF₁, hFπ⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target π t b
  let σ := SSet.yonedaEquiv F
  let u : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)).δ 1 σ
  have hσ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom)).δ 0 σ = t := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let w : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (p ≫ q.hom))) u t :=
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge π w ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hw).mpr hbi)
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeRefinement h p x u hu
  have hdi : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  exact ⟨d.cone, ⟨asIso (Truncated.HomotopyCategory.homMk d.comparison) ≪≫
    asIso (Truncated.HomotopyCategory.homMk w)⟩⟩

namespace VerdierQuotientConeRefinement

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {K : SSet.{u}} {p : K ⟶ B.obj} {x : B.obj _⦋0⦌}
  {t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q.hom)} (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement h p x t)

/-- 同じ可逆な slice 比較辺から得る、指定した商錐全体への全関手同型。 -/
def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.cone.val ≫ q.hom) t.val := by
  have hv : IsIso (Truncated.HomotopyCategory.homMk d.comparison) := d.isInvertible
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneFunctorIsoOfVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d.cone) t
    (asIso (Truncated.HomotopyCategory.homMk d.comparison))

/-- 商で全辺が可逆な指定錐の回収錐も、商後の全辺が可逆。 -/
lemma invertsAllEdges (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges t.val Set.univ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (d.cone.val ≫ q.hom) Set.univ :=
  (invertsEdges_functorIso_iff d.iso Set.univ).mpr ht

/-- 同じ商錐比較と各実脚の合成は、選択済みの実二単体で保持される。 -/
def legTriangle (k : K _⦋0⦌) :
    Truncated.Edge.CompStruct
      (d.comparison.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (p ≫ q.hom))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d.cone) k) :=
  coneLegComparisonTriangle d.comparison k

end VerdierQuotientConeRefinement
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
