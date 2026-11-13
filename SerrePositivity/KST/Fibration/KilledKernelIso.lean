module
public import SerrePositivity.KST.Fibration.VerdierKernelEquivalence

/-! # 全対象を零化する商の元の核と元の安定圏の厳密同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全対象を零化する実完全関手の核は、元の安定圏と包含そのもので厳密に同型。 -/
def killedKernelIso {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hr : ∀ a : A.obj _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (r.hom.app (Opposite.op ⦋0⦌) a)) :
    closedStableModel (kernelClosedPredicate r) ≅ sInputModel A where
  hom := closedStableInclusion (kernelClosedPredicate r)
  inv := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (kernelClosedPredicate r).predicate (𝟙 A.obj) hr, by
    apply preservesCofiberData_fullSubcomplex_of_comp (kernelClosedPredicate r).predicate
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact preservesCofiberData_id A.obj⟩
  hom_inv_id := by
    apply Subtype.ext
    have : Mono (closedStableInclusion (kernelClosedPredicate r)).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A.obj (kernelClosedPredicate r).predicate).ι)
    apply (cancel_mono (closedStableInclusion (kernelClosedPredicate r)).val).1
    change ((closedStableInclusion (kernelClosedPredicate r)).val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (kernelClosedPredicate r).predicate (𝟙 A.obj) hr) ≫ _ = _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (kernelClosedPredicate r).predicate (𝟙 A.obj) hr ≫
        (closedStableInclusion (kernelClosedPredicate r)).val = 𝟙 A.obj := rfl
    rw [Category.assoc, he]
    rfl
  inv_hom_id := Subtype.ext rfl

/-- Verdier 列の包含を通る合成の核は、元の包含側の安定圏そのものである。 -/
def verdierCompositeKernelIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    closedStableModel (kernelClosedPredicate (i ≫ q : A ⟶ C)) ≅ sInputModel A :=
  killedKernelIso (i ≫ q : A ⟶ C) h.kills_inclusion

end SerrePositivity.KST.Fibration
