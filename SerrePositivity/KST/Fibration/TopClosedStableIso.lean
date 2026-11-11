module
public import SerrePositivity.KST.Fibration.WeakStringZeroEquivalence

/-! # 全頂点部分圏と元の安定な入力の選択を加えない厳密同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全頂点部分圏を元の安定な入力に戻す同型。順射は元の包含。 -/
def topClosedStableIso (X : StableModel.{u}) : closedStableModel (ClosedStablePredicate.top X) ≅ X
    where
  hom := closedStableInclusion (ClosedStablePredicate.top X)
  inv := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (𝟙 X.carrier) (fun _ => trivial), by
    apply preservesCofiberData_fullSubcomplex_of_comp (ClosedStablePredicate.top X).predicate
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact preservesCofiberData_id X.carrier⟩
  hom_inv_id := by
    apply Subtype.ext
    have : Mono (closedStableInclusion (ClosedStablePredicate.top X)).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier
        (ClosedStablePredicate.top X).predicate).ι)
    apply (cancel_mono (closedStableInclusion (ClosedStablePredicate.top X)).val).1
    change ((closedStableInclusion (ClosedStablePredicate.top X)).val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (𝟙 X.carrier) (fun _ => trivial)) ≫ _ = _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (ClosedStablePredicate.top X).predicate (𝟙 X.carrier)
        (fun _ => trivial) ≫ (closedStableInclusion (ClosedStablePredicate.top X)).val =
          𝟙 X.carrier := rfl
    rw [Category.assoc, he, Category.comp_id]
    rfl
  inv_hom_id := Subtype.ext rfl

end SerrePositivity.KST.Fibration
