module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexNervePushout

/-!
概要：単射への反転関手の制限は inner fibration。
方針：内部 Hom の制限と全部分複体の包含の合成から、単射の後合成を消去する。
規約：標的の quasicategory 性と底の単射性のみを仮定する。
使われ方：局所化比較の相対的なホーン充填性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 単射による後合成が inner fibration なら、元の射も inner fibration。 -/
lemma innerFibration_of_comp_mono {A B C : SSet.{u}} (p : A ⟶ B) (j : B ⟶ C)
    [Mono j] [InnerFibration (p ≫ j)] : InnerFibration p := by
  constructor
  intro X Y i hi
  have : HasLiftingProperty i (p ≫ j) := InnerFibration.mem (q := p ≫ j) i hi
  constructor
  intro a b sq
  have hs : CommSq a i (p ≫ j) (b ≫ j) := by
    constructor
    rw [← Category.assoc, sq.w, Category.assoc]
  refine CommSq.HasLift.mk' {
    l := hs.lift
    fac_left := hs.fac_left
    fac_right := ?_ }
  apply (cancel_mono j).mp
  rw [Category.assoc, hs.fac_right]

/-- 単射に沿う反転関手の制限は、指定された比較を保って内ホーンを充填する。 -/
instance transportSimplexInvertingRestriction_innerFibration {B D : SSet.{u}}
    (f : B ⟶ D) [Mono f] (E : SSet.{u}) [Quasicategory E] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction f E) := by
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B)).ι
  have hh : innerFibrations (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction f E ≫ j) := by
    rw [show j = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) E
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B)).ι from rfl, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction_ι]
    apply innerFibrations.comp_mem
    · change innerFibrations (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
        ((ihom (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D))).obj E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges D))).ι
      exact mem_innerFibrations _
    · exact mem_innerFibrations _
  have : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction f E ≫ j) := ⟨hh⟩
  exact innerFibration_of_comp_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingRestriction f E) j

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
