module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPinched
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotRightFrameCoherent

/-!
概要：同じroof比較を、元の指定局所化比較と二胞体で同じCAlg源へ送る。
方針：既存の同じcoherent局所化比較のpinchedEquivalenceをそのまま合成する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointSourceRoofNativePinchedModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceRoofNativePinchedFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

local instance jointRoofNativePinchedProbeCof (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X

/-- 元の固定始域の全Hom比較と同じ局所化比較・同じ二胞体を記録する。 -/
def strictBETotJointRoofLocalizationComparison (P : strictBETotJointHomIndex A) :
    FrameHom.CoherentLocalizationComparison
      (SimplicialLocalization.hammockLocalizationNerveMap
        (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A) :=
  (strictBETotRightFrameCoherentComparison A
    (framedLimitProbe A (AsSmall.down.obj P).1.unop)).2

/-- 元の同じroof比較を、元の同じ二胞体で指定されたCAlg源のpinched Homへ送る。 -/
def strictBETotJointSourceRoofNativePinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofTargetObject A P))) :=
  strictBETotJointSourceRoofPinchedComparison A P ≫
    ((strictBETotJointRoofLocalizationComparison A P).pinchedEquivalence
      (nerveVertex (strictBETotJointRoofSourceObject A P))
      (nerveVertex (strictBETotJointRoofTargetObject A P))).hom

/-- 同じroofから同じ指定局所化像のpinched Homへの実射は弱同値。 -/
theorem strictBETotJointSourceRoofNativePinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNativePinchedComparison A P) :=
  (strictBETotJointSourceRoofPinchedComparison_weak A P).comp
    (((strictBETotJointRoofLocalizationComparison A P).pinchedEquivalence
      (nerveVertex (strictBETotJointRoofSourceObject A P))
      (nerveVertex (strictBETotJointRoofTargetObject A P))).isQCatEquivalence.isWeakHomotopyEquivalence)

/-- 実比較は元の同じ比較関手の作用と同じ二胞体の両端成分の共役そのもの。 -/
theorem strictBETotJointSourceRoofNativePinchedComparison_normalization
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofNativePinchedComparison A P =
      strictBETotJointSourceRoofPinchedComparison A P ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
          (strictBETotJointRoofLocalizationComparison A P).equivalence.hom _ _ ≫
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofSourceObject A P))))
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofTargetObject A P))))).hom :=
  congrArg (fun f => strictBETotJointSourceRoofPinchedComparison A P ≫ f)
    ((strictBETotJointRoofLocalizationComparison A P).pinchedEquivalence_hom
      (nerveVertex (strictBETotJointRoofSourceObject A P))
      (nerveVertex (strictBETotJointRoofTargetObject A P)))
end SerrePositivity.EInfinity.BarrattEccles
