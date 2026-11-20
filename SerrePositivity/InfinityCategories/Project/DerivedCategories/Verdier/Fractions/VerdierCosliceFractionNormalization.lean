module


public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.CosliceFractionTriangleNormalization
public import SerrePositivity.KST.LocalizingInvariants.VerdierArrowLifting
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierQuotientConeRefinement

/-!
概要：商 coslice の指定辺を、元の実右分数と同じ全三角形へ正規化する。
方針：商射影の実右分数を取り、同じ分母の可逆性を coslice の終点指定充填へ渡す。
規約：指定 coslice 辺・実分母・実分子・商二単体を全て保持する。
使われ方：有限線型図式の隣接二辺を、同じ商始点の錐として同時に扱う。
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
namespace SerrePositivity.KST.LocalizingInvariants.VerdierCosliceFractionNormalization
end SerrePositivity.KST.LocalizingInvariants.VerdierCosliceFractionNormalization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 同じ元の実右分数と、指定 coslice 後辺を保持する全三角形。 -/
structure VerdierCosliceFractionNormalization {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (_h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (a : (Δ[0] : SSet.{u}) ⟶ C.obj) {u v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)) u v)
    (x y : B.obj _⦋0⦌) where
  nativeSource : B.obj _⦋0⦌
  denominator : Truncated.Edge (X := (truncation 2).obj B.obj) nativeSource x
  numerator : Truncated.Edge (X := (truncation 2).obj B.obj) nativeSource y
  denominator_mem : denominator.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
  firstBase : Truncated.Edge (X := (truncation 2).obj C.obj)
    (q.hom.app (Opposite.op ⦋0⦌) nativeSource)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) u)
  diagonalBase : Truncated.Edge (X := (truncation 2).obj C.obj)
    (q.hom.app (Opposite.op ⦋0⦌) nativeSource)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) v)
  firstBase_edge : firstBase.edge = (denominator.map ((truncation 2).map q.hom)).edge
  diagonalBase_edge : diagonalBase.edge = (numerator.map ((truncation 2).map q.hom)).edge
  triangle : Truncated.Edge.CompStruct firstBase
    (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a))) diagonalBase
  lift : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.LeftFractionTriangleLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) e firstBase diagonalBase triangle

/-- 指定商 coslice 辺から、実右分数と同じ指定二単体の coslice 持ち上げを一括構成する。 -/
lemma exists_verdierCosliceFractionNormalization {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (a : (Δ[0] : SSet.{u}) ⟶ C.obj) {u v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)) u v)
    (x y : B.obj _⦋0⦌)
    (hu : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) u = q.hom.app (Opposite.op ⦋0⦌) x)
    (hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) v = q.hom.app (Opposite.op ⦋0⦌) y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h a e x y) := by
  let π := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a
  let ep := e.map ((truncation 2).map π)
  let f : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y) :=
    ⟨ep.edge, ep.src_eq.trans hu, ep.tgt_eq.trans hv⟩
  obtain ⟨z, s, g, hs, ⟨T⟩⟩ := verdierProjection_edge_fraction h f
  let b : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) z) (π.app (Opposite.op ⦋0⦌) u) :=
    ⟨(s.map ((truncation 2).map q.hom)).edge,
      (s.map ((truncation 2).map q.hom)).src_eq,
      (s.map ((truncation 2).map q.hom)).tgt_eq.trans hu.symm⟩
  let d : Truncated.Edge (X := (truncation 2).obj C.obj)
      (q.hom.app (Opposite.op ⦋0⦌) z) (π.app (Opposite.op ⦋0⦌) v) :=
    ⟨(g.map ((truncation 2).map q.hom)).edge,
      (g.map ((truncation 2).map q.hom)).src_eq,
      (g.map ((truncation 2).map q.hom)).tgt_eq.trans hv.symm⟩
  let t : Truncated.Edge.CompStruct b ep d := ⟨T.simplex, T.d₂, T.d₀, T.d₁⟩
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := C.obj) b :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := b) (f := s.map ((truncation 2).map q.hom)) rfl).mpr
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.mem_weakEquivalences_iff_invertible h s).mp hs)
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.exists_leftFractionTriangleLift π e b d t hb
  exact ⟨⟨z, s, g, hs, b, d, rfl, rfl, t, r⟩⟩

namespace VerdierCosliceFractionNormalization

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {a : (Δ[0] : SSet.{u}) ⟶ C.obj}
  {u v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌}
  {e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)) u v}
  {x y : B.obj _⦋0⦌} (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization h a e x y)

lemma first_native_image :
    (r.lift.first.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a))).edge =
      (r.denominator.map ((truncation 2).map q.hom)).edge :=
  r.lift.first_image.trans r.firstBase_edge

lemma diagonal_native_image :
    (r.lift.diagonal.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a))).edge =
      (r.numerator.map ((truncation 2).map q.hom)).edge :=
  r.lift.diagonal_image.trans r.diagonalBase_edge

/-- 同じ元の実分母と分子からなる有限 span。 -/
def nativeSpan : (horn 2 0 : SSet.{u}) ⟶ B.obj :=
  horn₂₀.isPushout.desc (SSet.yonedaEquiv.symm r.denominator.edge)
    (SSet.yonedaEquiv.symm r.numerator.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm
        (r.denominator.src_eq.trans r.numerator.src_eq.symm))

/-- 同じ二本の持ち上げ辺を、指定された元の coslice 内の有限全図式へ貼る。 -/
def spanLift : (horn 2 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a :=
  horn₂₀.isPushout.desc (SSet.yonedaEquiv.symm r.lift.first.edge)
    (SSet.yonedaEquiv.symm r.lift.diagonal.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm
        (r.lift.first.src_eq.trans r.lift.diagonal.src_eq.symm))

/-- 全有限図式の商像は、同じ実分母・分子の商像に厳密に一致する。 -/
lemma spanLift_projection : r.spanLift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a = r.nativeSpan ≫ q.hom := by
  apply horn₂₀.isPushout.hom_ext
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan, horn₂₀.isPushout.inl_desc]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact r.first_native_image
  · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.spanLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCosliceFractionNormalization.nativeSpan, horn₂₀.isPushout.inr_desc]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact r.diagonal_native_image

/-- 同じ coslice 図式が与える、元の有限実 span の指定商錐。 -/
def quotientCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (r.nativeSpan ≫ q.hom) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry r.spanLift,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection r.spanLift).trans r.spanLift_projection⟩

lemma quotientCone_vertex : r.quotientCone.vertex = SSet.yonedaEquiv a := by
  rw [r.quotientCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 0 : SSet.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry r.spanLift) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]

/-- 回収した同じ有限 span と指定商錐を、元の実錐へ全 slice 比較を保って戻す。 -/
lemma exists_nativeCone : ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r.nativeSpan,
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (r.nativeSpan ≫ q.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) r.quotientCone) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierQuotientConeIsoRefinement h r.nativeSpan r.quotientCone

end VerdierCosliceFractionNormalization

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
