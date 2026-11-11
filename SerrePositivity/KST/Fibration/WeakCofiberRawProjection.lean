module
public import SerrePositivity.KST.Fibration.WeakCofiberPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-! # 全相対 cofiber 図式の元の実底辺への充満忠実な射影 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の全相対 cofiber 図式から、元の全辺図式への実底辺の射影。 -/
def weakCofiberRawProjection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakCofiberModel q).carrier ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
    (kernelClosedPredicate q)).val ≫ cofiberProjection B.obj

/-- 全相対 cofiber の実底辺への射影は、元の写像空間で充満忠実。 -/
lemma weakCofiberRawProjection_fullyFaithful {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (weakCofiberRawProjection q) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (weakCofiberProjection q)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ (weakArrowPredicate q))
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (weakCofiberProjection_ι q)).mp hp

/-- 元の共通補完からの実底辺は、指定した元の実合成辺そのもの。 -/
lemma weakStringCofiberExact_rawProjection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    (weakStringCofiberExact q α).val ≫ weakCofiberRawProjection q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
        (pre (stdSimplex.map α)).app B.obj := by
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc]
  exact weakStringCofiberFamilyInput_projection q α

/-- 全相対 cofiber の後合成と、元の実底辺の後合成は厳密に可換。 -/
lemma weakCofiberPostExact_rawProjection {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakCofiberPostExact f q).val ≫ weakCofiberRawProjection q =
      weakCofiberRawProjection (f ≫ q : A ⟶ C) ≫ (ihom (Δ[1] : SSet.{u})).map f.hom := by
  exact (weakCofiberPostExact_projection f q).trans (Category.assoc _ _ _).symm

end SerrePositivity.KST.Fibration
