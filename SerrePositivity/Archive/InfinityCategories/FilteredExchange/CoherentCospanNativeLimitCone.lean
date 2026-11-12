module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeComparisonApex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport

/-!
概要：一般 coherent filtered 図式の各点の極限性から、元の余極限頂点で極限錐を構成。
方針：元の native 比較辺の可逆頂点円柱で、同じ native 二射の極限錐を輸送する。
規約：図式・元の頂点・比較辺・全錐の円柱を保持。使われ方：a7 の引き戻し交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}} [Quasicategory B] [IsFilteredInfinity B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
  (hc : ∀ b, IsLimitCone (coherentCospanConePointwiseCone F X Y Z C b))
local notation "f" => coherentCospanNativeLeftKanMap F X Y Z C
local notation "g" => coherentCospanNativeRightKanMap F X Y Z C

/-- 元の native 比較辺を頂点円柱として保持する、同じ native 二射上の全錐の輸送。 -/
def coherentCospanNativeLimitConeTransport :
    SpecifiedApexLimitConeTransport (intervalPullbackCone f g)
      (SSet.yonedaEquiv.symm (coherentDiagramTotalVertex F))
      (coherentCospanNativeComparisonApexPrism F X Y Z C) :=
  specifiedApexLimitConeTransport _ (intervalPullbackCone_isLimit f g) _ _
    (coherentCospanNativeComparisonApexPrism_zero F X Y Z C) (by
      rw [coherentCospanNativeComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change coherentNerveVertex (intervalPullbackKanObject f g) =
        (intervalPullbackCone f g).vertex
      rw [intervalPullbackCone_vertex, spaceInfinityVertex_eq_coherent])
    (coherentCospanNativeComparisonApexPrism_vertical_isInvertible F X Y Z C hc)

/-- 元の余極限頂点を持つ、元の native 値の二射上の錐。 -/
def coherentCospanNativeLimitCone : JoinCone
    (kanDiagramCoherentNerve (kanPullbackDiagram f g)) :=
  (coherentCospanNativeLimitConeTransport F X Y Z C hc).cone

/-- 各点の元の錐が極限なら、元の余極限頂点を持つこの錐も native な極限錐。 -/
lemma coherentCospanNativeLimitCone_isLimit :
    IsLimitCone (coherentCospanNativeLimitCone F X Y Z C hc) :=
  (coherentCospanNativeLimitConeTransport F X Y Z C hc).isLimit

/-- 輸送後の頂点の射は元の余極限頂点の指定射と厳密に一致。 -/
lemma coherentCospanNativeLimitCone_apex :
    joinInl _ _ ≫ (coherentCospanNativeLimitCone F X Y Z C hc).val =
      SSet.yonedaEquiv.symm (coherentDiagramTotalVertex F) :=
  (coherentCospanNativeLimitConeTransport F X Y Z C hc).apex_eq

/-- 輸送後の極限錐の頂点は元の coherent 図式の余極限頂点そのもの。 -/
lemma coherentCospanNativeLimitCone_vertex :
    (coherentCospanNativeLimitCone F X Y Z C hc).vertex = coherentDiagramTotalVertex F := by
  change SSet.yonedaEquiv (joinInl _ _ ≫
    (coherentCospanNativeLimitCone F X Y Z C hc).val) = _
  rw [coherentCospanNativeLimitCone_apex, SSet.yonedaEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
