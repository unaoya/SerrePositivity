module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductBoundary

/-! # 元の二脚の Cat^perf 局所化不変量値の実 pullback
概要：元の左端の値を頂点とし、元の完備化後の二脚を脚とする実極限錐を構成する。
方針：同じ元の実積と対角の pullback を、既存の全図式の貼り合わせで二脚へ移す。
規約：実商・冪等完備化・元の四射を保つ。使われ方：dg ⊙ と LT 主定理への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance valuePullbackSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 元の四つの実 BF 射を辺に持つ、同じ二脚の実正方形。 -/
def valuePullbackSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  BinaryProductCospanNormalized.square (d.valueCSource F) (d.valueDSource F)
    (d.valueCLeg F) (d.valueDLeg F) (d.valueCospan_comm F)
    (d.productCospanInputSquare hF) (d.productCospanInputSquare_isPullback hF)
    (d.productCospanInputSquare_top hF) (d.productCospanInputSquare_right hF)
    (d.productCospanInputSquare_left hF)

/-- 同じ元の二脚の正方形は、実 Sp の引き戻し。 -/
lemma valuePullbackSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.valuePullbackSquare hF) :=
  BinaryProductCospanNormalized.square_isPullback _ _ _ _ _ _ _ _ _ _

/-- 同じ下辺は元の C への値の実 BF 射。 -/
lemma valuePullbackSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ d.valuePullbackSquare hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueCSource F)).edge :=
  BinaryProductCospanNormalized.square_bottom _ _ _ _ _ _ _ _ _ _

/-- 同じ上辺は元の完備化後の D 脚の実 BF 射。 -/
lemma valuePullbackSquare_top : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ d.valuePullbackSquare hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueDLeg F)).edge :=
  BinaryProductCospanNormalized.square_top _ _ _ _ _ _ _ _ _ _

/-- 同じ左辺は元の D への値の実 BF 射。 -/
lemma valuePullbackSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ d.valuePullbackSquare hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueDSource F)).edge :=
  BinaryProductCospanNormalized.square_left _ _ _ _ _ _ _ _ _ _

/-- 同じ右辺は元の完備化後の C 脚の実 BF 射。 -/
lemma valuePullbackSquare_right : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ d.valuePullbackSquare hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueCLeg F)).edge :=
  BinaryProductCospanNormalized.square_right _ _ _ _ _ _ _ _ _ _

/-- 同じ正方形の左下は、元の左端の同じ BF 表示。 -/
lemma valuePullbackSquare_vertex00 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.valuePullbackSquare hF) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F (perfectStableVertex d.left d.left_complete)) :=
  NativeSquareRows.vertex00 _ _ (d.valuePullbackSquare_bottom hF)

/-- 元の完備化後の二脚を持つ、同じ実 cospan 図式。 -/
def valuePullbackCospan : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
  (d.valuePullbackSquare hF)

/-- 元の左端の値を頂点とする、元の二脚の実錐。 -/
def valuePullbackCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (d.valuePullbackCospan hF) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone
  (d.valuePullbackSquare hF)

/-- 同じ元の二脚の実錐は、実 Sp の極限錐。 -/
lemma valuePullbackCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (d.valuePullbackCone hF) :=
  d.valuePullbackSquare_isPullback hF

/-- 同じ極限錐の頂点は、元の左端の同じ BF 表示。 -/
lemma valuePullbackCone_vertex : (d.valuePullbackCone hF).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
  (perfectInvariantSpectrum F (perfectStableVertex d.left d.left_complete)) := by
  have hv := FiberModel.coneSquare_apex (d.valuePullbackCone hF)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (d.valuePullbackCone hF) = d.valuePullbackSquare hF := by
    simp only [valuePullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare, Iso.inv_hom_id_assoc]
  rw [hs] at hv
  exact hv.symm.trans (d.valuePullbackSquare_vertex00 hF)

/-- 同じ cospan の C 側は、元の完備化後の C 脚。 -/
lemma valuePullbackCospan_C : horn₂₂.ι₀₂ ≫ d.valuePullbackCospan hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueCLeg F)).edge := by
  rw [valuePullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge,
    d.valuePullbackSquare_right]

/-- 同じ cospan の D 側は、元の完備化後の D 脚。 -/
lemma valuePullbackCospan_D : horn₂₂.ι₁₂ ≫ d.valuePullbackCospan hF =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (d.valueDLeg F)).edge := by
  rw [valuePullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge,
    d.valuePullbackSquare_top]

/-- 元の左端の BF 表示の頂点は、同じ元の不変量値の頂点そのもの。 -/
lemma valuePullbackSquare_vertex_value : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.valuePullbackSquare hF) 0 0 =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex d.left d.left_complete) :=
  (d.valuePullbackSquare_vertex00 hF).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 同じ実 pullback 錐の頂点は、元の左端の同じ不変量値そのもの。 -/
lemma valuePullbackCone_vertex_value : (d.valuePullbackCone hF).vertex =
    F.app (Opposite.op ⦋0⦌) (perfectStableVertex d.left d.left_complete) :=
  (d.valuePullbackCone_vertex hF).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
