module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightBranchCommonInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramNormalizedRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialEdgeFamilyPrecomposition
public import
  SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTotalPrecomposition

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
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


attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
local notation "hG" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y
local notation "hs" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_firstEdge hp p c hc dB dC
local notation "b" => ConcreteCategory.hom
  (NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (j ≫ p) g
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)) (Opposite.op ⦋0⦌)) dC

/-- 元の右四面体の付加辺面全体にある、同じ全 Hom の族。 -/
def specifiedCoconeRightAttachmentFaceFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder t :=
  G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction s (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) hs
local notation "L" => specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y

/-- 同じ面の全族は、元の固定終点 y 上に留まる。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_fixed :
    (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) ≫ q = SSet.const y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramNormalizedRestriction_fixed q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs y G hG
local notation "hL" => specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y

/-- 付加辺面の始点は、元の右根辺四面体の同じ初期 Hom 族である。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c t (stdSimplex.δ (1 : Fin 2))
        (SSet.Edge.δ_one_yonedaEquiv_symm e) y L hL =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_normalized_restrict q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs y G hG
    c (stdSimplex.δ (1 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫
      (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4))) rfl
    (SSet.Edge.δ_one_yonedaEquiv_symm e)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC)

/-- 付加辺面の終点は、元の右枝初期族を共通部分へ制限した同じ族である。 -/
lemma specifiedCoconeRightAttachmentFaceFamily_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q b t (stdSimplex.δ (0 : Fin 2))
        (SSet.Edge.δ_zero_yonedaEquiv_symm e) y L hL =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchCommonInitialFamily hp p c hc dB dC y := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_normalized_restrict q s
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) t hs
    y G hG b (stdSimplex.δ (0 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫
      (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)))
    targetCoordinate
    (SSet.Edge.δ_zero_yonedaEquiv_symm e)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_branchSource hp p c hc dB dC)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightBranchCommonInitialFamily_tetrahedron hp p c hc dB dC y).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
