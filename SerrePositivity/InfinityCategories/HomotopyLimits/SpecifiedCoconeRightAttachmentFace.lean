module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightBranchCommonInitial
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramNormalizedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialEdgeFamilyPrecomposition
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTotalPrecomposition

/-!
概要：元の右根辺四面体の実際の付加辺面を、同じ全 Hom パラメータで回収する。
方針：面と両端の初期 Hom を厳密に制限し、既存の枝初期族と同定する。
規約：元の四面体と実際の付加辺を保持。使われ方：枝終点の普遍前置との相対比較。
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
        (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) =
      stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) := by
  have h01 : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    simpa using (stdSimplex.δ_comp_δ (n := 0) (i := (0 : Fin 2))
      (j := (1 : Fin 2)) (by decide))
  have h03 : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.δ (3 : Fin 4) = stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    simpa using (stdSimplex.δ_comp_δ (n := 1) (i := (0 : Fin 3))
      (j := (2 : Fin 3)) (by decide))
  have h11 : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (2 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
    simpa using (stdSimplex.δ_comp_δ (n := 0) (i := (1 : Fin 2))
      (j := (1 : Fin 2)) (by decide))
  calc
    _ = stdSimplex.δ (1 : Fin 2) ≫
        (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) := by
      rw [← Category.assoc, h01, Category.assoc]
    _ = stdSimplex.δ (1 : Fin 2) ≫
        (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) :=
      congrArg (stdSimplex.δ (1 : Fin 2) ≫ ·) h03
    _ = _ := by rw [← Category.assoc, h11, Category.assoc]


attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "e" => colimitAttachmentRestrictionEdge c hc g (j ≫ p)
  (coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "s" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "G" => specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
local notation "hG" => specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y
local notation "hs" => specifiedCoconeRootedRightTetrahedron_firstEdge hp p c hc dB dC
local notation "b" => ConcreteCategory.hom
  (NatTrans.app (normalizedCoconeRestriction (j ≫ p) g
    (coconePushoutBoundary_eq hp p)) (Opposite.op ⦋0⦌)) dC

/-- 元の右四面体の付加辺面全体にある、同じ全 Hom の族。 -/
def specifiedCoconeRightAttachmentFaceFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      sliceUnder t :=
  G ≫ normalizedCoconeRestriction s (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) hs
local notation "L" => specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y

/-- 同じ面の全族は、元の固定終点 y 上に留まる。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_fixed :
    (L ≫ sliceUnderProjection t) ≫ q = SSet.const y :=
  initialDiagramNormalizedRestriction_fixed q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs y G hG
local notation "hL" => specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y

/-- 付加辺面の始点は、元の右根辺四面体の同じ初期 Hom 族である。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_source :
    initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL =
      specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y :=
  initialDiagramHomFamily_normalized_restrict q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs y G hG
    c (stdSimplex.δ (1 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4))) rfl
    (SSet.Edge.δ_one_yonedaEquiv_symm e)
    (specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC)

/-- 付加辺面の終点は、元の右枝初期族を共通部分へ制限した同じ族である。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_target :
    initialDiagramHomFamily q b t (stdSimplex.δ (0 : Fin 2))
        (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL =
      specifiedCoconeRightBranchCommonInitialFamily hp p c hc dB dC y := by
  have h := initialDiagramHomFamily_normalized_restrict q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs
    y G hG b (stdSimplex.δ (0 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫
      (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)))
    targetCoordinate
    (SSet.Edge.δ_zero_yonedaEquiv_symm e)
    (specifiedCoconeRootedRightTetrahedron_branchSource hp p c hc dB dC)
  exact h.trans (specifiedCoconeRightBranchCommonInitialFamily_tetrahedron hp p c hc dB dC y).symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
