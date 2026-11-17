module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofComparison
public import SerrePositivity.EInfinity.FrameHom.AsSmallHammockHomFamily
public import SerrePositivity.EInfinity.FrameHom.KanHomFamilyOpposite
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockPinchedSimplexValue

/-!
概要：元の同じroof比較を、同じ全モデル局所化頂点のpinched Homへ送る。
方針：元のAsSmall同型・同じEx∞単位・元の全単体のpinched比較を合成する。
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
local instance jointSourceRoofPinchedModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceRoofPinchedFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の同じ基準roof比較の始域を、同じ全モデル相対圏の対象として記録する。 -/
abbrev strictBETotJointRoofSourceObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category :=
  modelRelativeObject (operad A).Algebra (framedLimitProbe A (AsSmall.down.obj P).1.unop)

/-- 元の同じ右置換を、同じ全モデル相対圏の対象として記録する。 -/
abbrev strictBETotJointRoofTargetObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category :=
  modelRelativeObject (operad A).Algebra
    ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)

/-- 元の同じroof比較を、同じAsSmall同型とEx∞単位で元のKan hammock Homへ送る。 -/
def strictBETotJointSourceRoofKanComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      exInfinity.obj
        (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
          (modelRelativeCategory (operad A).Algebra).weakEquivalences
          (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P)) :=
  strictBETotJointSourceRoofComparison A P ≫
    (Hammock.AsSmallComparison.colimitIso (weakEquivalences (operad A).Algebra)
      (framedLimitProbe A (AsSmall.down.obj P).1.unop)
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)).hom ≫
        exInfinityUnit.app _

/-- 元の同じ実roof比較の弱同値性を、同じAsSmall同型とEx∞単位で移す。 -/
theorem strictBETotJointSourceRoofKanComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofKanComparison A P) := by
  have h₀ := strictBETotJointSourceRoofComparison_isWeakHomotopyEquivalence A P
  have h₁ := (isPrecompositionEquivalence_of_iso
    (Hammock.AsSmallComparison.colimitIso (weakEquivalences (operad A).Algebra)
      (framedLimitProbe A (AsSmall.down.obj P).1.unop)
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp (FrameHom.kanHomFamilyUnit_isWeakHomotopyEquivalence _))

/-- 元の全標的のAsSmall比較の同じ成分と、元のEx∞単位の厳密な三角形。 -/
theorem strictBETotJointSourceRoofKanComparison_unit (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofComparison A P ≫ exInfinityUnit.app _ ≫
      (FrameHom.asSmallKanHammockHomFamilyMap (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)).app
          (strictBETotJointRoofTargetObject A P) =
      strictBETotJointSourceRoofKanComparison A P := by
  exact congrArg (fun f => strictBETotJointSourceRoofComparison A P ≫ f)
    (exInfinityUnit.naturality
      (Hammock.AsSmallComparison.colimitIso (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)).hom).symm

/-- 元の基準roof比較を、同じhammock局所化頂点のpinched Homへ送る実射。 -/
def strictBETotJointSourceRoofPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofTargetObject A P))) :=
  strictBETotJointSourceRoofKanComparison A P ≫
    SimplicialLocalization.kanHammockHomPinchedMap (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P)

/-- 同じ元の基準roofから同じ局所化頂点のpinched Homへの実射は弱同値。 -/
theorem strictBETotJointSourceRoofPinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofPinchedComparison A P) :=
  (strictBETotJointSourceRoofKanComparison_weak A P).comp
    (SimplicialLocalization.kanHammockHomPinchedMap_weak
      (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P))

/-- 元の全単体の値は、同じ元のKan hammock Homのcoherent単体そのもの。 -/
theorem strictBETotJointSourceRoofPinchedComparison_app_val (P : strictBETotJointHomIndex A) :
    SimplicialLocalization.KanHammockPinchedValueFormula
      (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P)
      (strictBETotJointSourceRoofKanComparison A P) :=
  SimplicialLocalization.kanHammockHomPinchedMap_value_family
    (modelRelativeCategory (operad A).Algebra)
    (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P) _
end SerrePositivity.EInfinity.BarrattEccles
