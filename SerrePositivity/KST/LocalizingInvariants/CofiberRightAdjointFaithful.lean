module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberRightAdjointFaithful

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointZero

/-!
概要：元の cofiber の右随伴を零始点矢印の族へ持ち上げ、充満忠実性を証明する。
方針：零始点矢印の終点評価の厳密切断と、その自明 Kan 性を使う。
規約：元の右随伴関手を保持。使われ方：Cone の可逆余単位と差の局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiberZeroSourceQuasicategory
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 元の右随伴を同じ矢印を保って零始点矢印の全部分圏に入れる。 -/
def cofiberRightAdjointZeroSource : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrows X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (cofiberRightAdjoint X)
    (cofiberRightAdjoint_source_zero X)

lemma cofiberRightAdjointZeroSource_inclusion :
    cofiberRightAdjointZeroSource X ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι =
      cofiberRightAdjoint X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma cofiberRightAdjointZeroSource_target :
    cofiberRightAdjointZeroSource X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X = 𝟙 X := by
  change cofiberRightAdjointZeroSource X ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _
  rw [← Category.assoc, cofiberRightAdjointZeroSource_inclusion, cofiberRightAdjoint_target]

/-- 元の cofiber の実右随伴は充満忠実である。 -/
lemma cofiberRightAdjoint_fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (cofiberRightAdjoint X) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (cofiberRightAdjointZeroSource X) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.fullyFaithful_of_relativeInitialSection (cofiberRightAdjointZeroSource_target X)
      (fun x => initialBoundary_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceArrowTarget X)
        ((cofiberRightAdjointZeroSource X).app (Opposite.op ⦋0⦌) x))
  have h := hs.comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow)
  rw [cofiberRightAdjointZeroSource_inclusion] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants
