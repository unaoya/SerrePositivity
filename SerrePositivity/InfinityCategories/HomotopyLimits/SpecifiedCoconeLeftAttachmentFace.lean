module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftBranchCommonInitial
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramNormalizedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialEdgeFamilyPrecomposition
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTotalPrecomposition

/-!
概要：元の左根辺三角形の実際の付加辺面を、同じ全 Hom パラメータで回収する。
方針：面と両端の初期 Hom を厳密に制限し、既存の枝初期族と同定する。
規約：元の三角形と実際の付加辺を保持。使われ方：枝終点の普遍前置との相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
private lemma targetCoordinate :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (2 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
  simpa using (stdSimplex.δ_comp_δ (n := 0) (i := (0 : Fin 2))
    (j := (1 : Fin 2)) (by decide))

attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "e" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "s" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "G" => specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
local notation "hG" => specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y
local notation "hs" => specifiedCoconeLeftRootedTriangle_first hp p c hc dB dC
local notation "b" => ConcreteCategory.hom
  (NatTrans.app (normalizedCoconeRestriction (i ≫ p) f rfl) (Opposite.op ⦋0⦌)) dB

/-- 元の左三角形の付加辺面全体にある、同じ全 Hom の族。 -/
def specifiedCoconeLeftAttachmentFaceFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder t := G ≫ normalizedCoconeRestriction s (stdSimplex.δ (2 : Fin 3)) hs
local notation "L" => specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y

/-- 同じ面の全族は、元の固定終点 y 上に留まる。 -/
lemma specifiedCoconeLeftAttachmentFaceFamily_fixed :
    (L ≫ sliceUnderProjection t) ≫ q = SSet.const y :=
  initialDiagramNormalizedRestriction_fixed q s (stdSimplex.δ (2 : Fin 3)) t hs y G hG
local notation "hL" => specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y

/-- 付加辺面の始点は、元の左根辺三角形の同じ初期 Hom 族である。 -/
lemma specifiedCoconeLeftAttachmentFaceFamily_source :
    initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL =
      specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y :=
  initialDiagramHomFamily_normalized_restrict q s (stdSimplex.δ (2 : Fin 3)) t hs y G hG
    c (stdSimplex.δ (1 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) rfl
    (SSet.Edge.δ_one_yonedaEquiv_symm e)
    (specifiedCoconeLeftRootedTriangle_initial hp p c hc dB dC)

/-- 付加辺面の終点は、元の左枝初期族を共通部分へ制限した同じ族である。 -/
lemma specifiedCoconeLeftAttachmentFaceFamily_target :
    initialDiagramHomFamily q b t (stdSimplex.δ (0 : Fin 2))
        (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL =
      specifiedCoconeLeftBranchCommonInitialFamily hp p c hc dB dC y := by
  have h := initialDiagramHomFamily_normalized_restrict q s (stdSimplex.δ (2 : Fin 3)) t hs
    y G hG b (stdSimplex.δ (0 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3))
    targetCoordinate
    (SSet.Edge.δ_zero_yonedaEquiv_symm e)
    (specifiedCoconeLeftRootedTriangle_middle hp p c hc dB dC)
  exact h.trans (specifiedCoconeLeftBranchCommonInitialFamily_triangle hp p c hc dB dC y).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
