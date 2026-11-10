module

public import SerrePositivity.InfinityCategories.F2.Idempotent.SplittingCanonicalColimits
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalMapping
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の全強分裂図式から全 Idem 図式への制限は、inner かつ充満忠実。
方針：元の全標準局所余極限から、元の pinched 写像空間の前合成そのものを判定する。
規約：標的全体の冪等完備性を充満忠実性の入力に要求しない。
使われ方：指定した元の全 Idem 図式上の全分裂空間の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全強分裂図式を、元の全 Idem 包含へ前合成する制限そのもの。 -/
def strongSplittingRestriction (X : SSet.{u}) :
    (ihom SplitShape).obj X ⟶ (ihom IdemShape).obj X := (pre idemInclusion).app X

/-- 元の全図式の制限は、元の包含の単射性により inner fibration。 -/
instance strongSplittingRestriction_innerFibration (X : SSet.{u}) [Quasicategory X] :
    InnerFibration (strongSplittingRestriction X) :=
  inferInstanceAs (InnerFibration ((pre idemInclusion).app X))

/-- 元の制限は、元の全図式間の pinched 写像空間で充満忠実。 -/
@[kerodon 0402]
lemma strongSplittingRestriction_isFullyFaithful (X : SSet.{u}) [Quasicategory X] :
    IsFullyFaithful (strongSplittingRestriction X) := by
  intro x y
  obtain ⟨F, rfl⟩ := (functorVertexEquiv SplitShape X).surjective x
  obtain ⟨G, rfl⟩ := (functorVertexEquiv SplitShape X).surjective y
  exact F1B.kanLeftCanonical_pinchedHomMap_equivalence idemInclusion F
    (splittingCanonicalCocones_isColimit F) G

/-- 冪等完備なら、元の全 Idem 図式への元の制限そのものが自明 Kan fibration。 -/
@[kerodon 0402]
lemma strongSplittingRestriction_trivialKanFibration_of_complete (X : SSet.{u})
    [Quasicategory X] (hX : IsIdempotentComplete X) :
    TrivialKanFibration (strongSplittingRestriction X) := by
  apply (strongSplittingRestriction_isFullyFaithful X).trivialKanFibration_of_surjective
  intro x
  obtain ⟨d, rfl⟩ := (functorVertexEquiv IdemShape X).surjective x
  obtain ⟨s⟩ := hX d
  refine ⟨functorVertex s.val, ?_⟩
  change functorVertex (idemInclusion ≫ s.val) = functorVertex d
  rw [s.property]

end SerrePositivity.InfinityCategories.F2.Idempotent
