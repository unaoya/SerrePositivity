module

public import SerrePositivity.InfinityCategories.F1.RightStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.PresheafRestrictionEquivalence

/-!
概要：元の right straightening の値の小さい left 復元を、元の反転全空間と比較する。
方針：共通解像の頂点比較で元の left 分類図式と比較し、既証の底上の復元射を合成する。
規約：分類値を元の前層の全単射で読み戻し、同じ底を厳密に保つ。
使われ方：元の right unstraightening と元の right fibration の全空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}}

/-- 元の right straightening の値を、元の前層の全単射で読んだ同じ図式。 -/
def rightStraighteningPresheafDiagram (p : RightFibrationObject B) :
    (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ SpaceInfinity.{u} :=
  (presheafInfinityObjectEquiv B).symm
    ((rightStraighteningInfinityMap B).app _ (coherentNerveVertex p))

/-- 同じ図式の前層頂点は元の分類値そのもの。 -/
lemma rightStraighteningPresheafDiagram_vertex (p : RightFibrationObject B) :
    functorVertex (rightStraighteningPresheafDiagram p) =
      (rightStraighteningInfinityMap B).app _ (coherentNerveVertex p) :=
  (presheafInfinityObjectEquiv B).apply_symm_apply _

/-- 反転した元の射影の left 分類図式と、元の right 分類値の同じ図式の関手同型。 -/
def rightStraighteningOppositeDiagramIso (p : RightFibrationObject B) :
    FunctorIso (leftStraighteningInfinityDiagram (SSet.opFunctor.map p.val.hom))
      (rightStraighteningPresheafDiagram p) := by
  have h := VertexIso.map (rightFibrationOppositeInfinityVertexIso p)
    (leftStraighteningInfinityMap B.op)
  change VertexIso
    ((rightStraighteningInfinityMap B).app _ (coherentNerveVertex p))
    ((leftStraighteningInfinityMap B.op).app _
      (leftFibrationInfinityVertex (SSet.opFunctor.map p.val.hom))) at h
  exact eqToIso (congrArg HomotopyCategory.mk
    (leftStraighteningInfinityDiagram_vertex (SSet.opFunctor.map p.val.hom))) ≪≫ h.symm ≪≫
      eqToIso (congrArg HomotopyCategory.mk (rightStraighteningPresheafDiagram_vertex p).symm)

variable [Quasicategory B]

/-- 元の反転全空間から、元の分類値の小さい left unstraightening への同じ底上の比較。 -/
def rightStraighteningLeftRecovery (p : RightFibrationObject B) :
    p.val.left.op ⟶ smallLeftUnstraightening (rightStraighteningPresheafDiagram p) :=
  leftStraighteningInfinityReconstruction (SSet.opFunctor.map p.val.hom) ≫
    smallLeftUnstraighteningComparisonOfFunctorIso (rightStraighteningOppositeDiagramIso p)

/-- 元の left 復元の比較は同じ反転射影を厳密に保つ。 -/
lemma rightStraighteningLeftRecovery_projection (p : RightFibrationObject B) :
    rightStraighteningLeftRecovery p ≫
      smallLeftUnstraighteningProjection (rightStraighteningPresheafDiagram p) =
        SSet.opFunctor.map p.val.hom := by
  rw [rightStraighteningLeftRecovery, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    leftStraighteningInfinityReconstruction_projection]

/-- 元の left 復元の同じ比較射は前合成同値。 -/
lemma rightStraighteningLeftRecovery_isPrecompositionEquivalence (p : RightFibrationObject B) :
    IsPrecompositionEquivalence (rightStraighteningLeftRecovery p) :=
  (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
    (SSet.opFunctor.map p.val.hom)).comp
      (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

end SerrePositivity.InfinityCategories.F2.Ind
