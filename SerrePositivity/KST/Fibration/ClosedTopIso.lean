module
public import SerrePositivity.KST.Fibration.KernelCofiberModel

/-! # 全頂点を持つ安定閉部分圏の元の完全同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全頂点の閉部分圏への恒等射の完全な持ち上げ。 -/
def closedTopLift (X : StableModel.{u}) : X ⟶ closedStableModel (ClosedStablePredicate.top X) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (𝟙 X.carrier) (fun _ => trivial), by
    apply preservesCofiberData_fullSubcomplex_of_comp (ClosedStablePredicate.top X).predicate
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact preservesCofiberData_id X.carrier⟩

/-- 全頂点への持ち上げを含めると元の恒等射を回収する。 -/
lemma closedTopLift_inclusion (X : StableModel.{u}) :
    closedTopLift X ≫ closedStableInclusion (ClosedStablePredicate.top X) = 𝟙 X :=
  Subtype.ext rfl

/-- 全頂点の安定閉部分圏は、元の全単体を保つ完全な同型。 -/
def closedTopExactIso (X : StableModel.{u}) :
    closedStableModel (ClosedStablePredicate.top X) ≅ X where
  hom := closedStableInclusion (ClosedStablePredicate.top X)
  inv := closedTopLift X
  hom_inv_id := by
    apply Subtype.ext
    have : Mono (closedStableInclusion (ClosedStablePredicate.top X)).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier
        (ClosedStablePredicate.top X).predicate).ι)
    apply (cancel_mono (closedStableInclusion (ClosedStablePredicate.top X)).val).1
    change ((closedStableInclusion (ClosedStablePredicate.top X) ≫ closedTopLift X) ≫
      closedStableInclusion (ClosedStablePredicate.top X)).val = _
    rw [Category.assoc, closedTopLift_inclusion, Category.comp_id]
    rfl
  inv_hom_id := closedTopLift_inclusion X

end SerrePositivity.KST.Fibration
