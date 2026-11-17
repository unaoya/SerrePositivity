module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofEndpointTransport
public import SerrePositivity.EInfinity.PowerOperation.NerveColumnRoofConjugation
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativePinched
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofColumn

/-! 元のroofの全局所化三角形を消去し、指定された同じnativeな両端へ全族を輸送する。 -/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.EInfinity.FrameHom
open SerrePositivity.EInfinity.SimplicialLocalization
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
attribute [local instance] jointRoofColumnLawModel jointRoofColumnLawFactorization
/-- 元のroofと同じ局所化三角形・指定両端の全族の照合。 -/
lemma strictBETotJointSourceRoofFrameAugmentation_inverted (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((strictBETotJointSourceRoofFrameAugmentation A P).app s)).map
      (strictBETotModelSource A)).toTruncated :=
  weakNerveEdges_inverts_arrows (modelRelativeCategory (operad A).Algebra)
    (strictBETotModelSource A) (strictBETotModelSource_isLocalization A).choose _
      (strictBETotJointSourceRoofFrameAugmentation_weak A P s)
/-- 元のroofと同じ局所化三角形・指定両端の全族の照合。 -/
lemma strictBETotJointSourceRoofNativePinchedComparison_column_roof (P : strictBETotJointHomIndex A) :
    Arrow.mk (intervalFamilyHom (strictBETotJointSourceRoofNativePinchedComparison A P ≫
      pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk ((NerveColumn.augmentationIso (strictBETotModelSource A)
      (strictBETotJointSourceRoofFrameDiagram A P)
      (strictBETotJointSourceRoofFrameAugmentation A P)
      (strictBETotJointSourceRoofFrameAugmentation_inverted A P)).inv ≫
      NerveColumn.hom (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameEvaluation A P)) := by
  let c := strictBETotJointRoofLocalizationComparison A P
  have hc := SerrePositivity.EInfinity.PowerOperation.nerveColumnRoofConjugation_arrow c.triangle
    (strictBETotJointSourceRoofFrameDiagram A P)
    (strictBETotJointSourceRoofFrameAugmentation A P)
    (RoofPrefix.postcomp_augmentation_invertible
      (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointSourceRoofFrameDiagram A P)
      (strictBETotJointSourceRoofFrameAugmentation A P)
      (strictBETotJointSourceRoofFrameAugmentation_weak A P) c.equivalence.hom)
    (strictBETotJointSourceRoofFrameAugmentation_inverted A P)
    (strictBETotJointSourceRoofFrameEvaluation A P)
    (strictBETotJointSourceRoofPinchedComparison A P ≫ pinchedHomMap c.equivalence.hom _ _)
    (strictBETotJointSourceRoofPinchedComparison_column_roof A P c.equivalence.hom)
  rw [functorIsoEvaluate_eq_app, functorIsoEvaluate_eq_app] at hc
  have ht := pinchedEndpointEquivalence_family
    (x' := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (strictBETotJointRoofSourceObject A P)))
    (y' := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (strictBETotJointRoofTargetObject A P)))
    (c.triangle.toNatIso.app (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofSourceObject A P))))
    (c.triangle.toNatIso.app (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofTargetObject A P))))
    (strictBETotJointSourceRoofPinchedComparison A P ≫ pinchedHomMap c.equivalence.hom _ _)
  rw [strictBETotJointSourceRoofNativePinchedComparison_normalization]
  have h := (congrArg Arrow.mk ht).trans hc
  simpa only [Category.assoc, c] using h
/-- 元のroofと同じ局所化三角形・指定両端の全族の照合。 -/
lemma strictBETotJointSourceRoofNormalizedPinchedComparison_interval_family (P : strictBETotJointHomIndex A) :
    let K := nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ
    intervalFamilyHom (strictBETotJointSourceRoofNormalizedPinchedComparison A P ≫
      pinchedHomToIntervalMappingSpace _ _) =
      constantFunctorHomMap K (strictBETotJointRoofProbeEndpointIso A P).inv ≫
        intervalFamilyHom (strictBETotJointSourceRoofNativePinchedComparison A P ≫
          pinchedHomToIntervalMappingSpace _ _) ≫
        constantFunctorHomMap K (strictBETotJointRoofTargetEndpointUnitIso A P).inv := by
  dsimp only
  unfold strictBETotJointSourceRoofNormalizedPinchedComparison
  exact pinchedEndpointEquivalence_family
    (x' := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
    (y' := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
    (strictBETotJointRoofProbeEndpointIso A P)
    (strictBETotJointRoofTargetEndpointUnitIso A P).symm
    (strictBETotJointSourceRoofNativePinchedComparison A P)

end SerrePositivity.EInfinity.BarrattEccles
end
