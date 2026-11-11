module
public import SerrePositivity.KST.Fibration.KilledKernelIso
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryFunctor

/-! # 元の包含側の完全関手による核部分圏の後合成 -/

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

/-- 元の完全関手による合成した商の核から元の商の核への制限。 -/
def kernelPostExact {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    closedStableModel (kernelClosedPredicate (f ≫ q : A ⟶ C)) ⟶
      closedStableModel (kernelClosedPredicate q) :=
  closedStableMap (kernelClosedPredicate (f ≫ q : A ⟶ C)) (kernelClosedPredicate q)
    (sInputExactMap f) (fun _ hx => hx)

/-- 核への制限は、元の包含と同じ完全関手の厳密な可換四角形を保つ。 -/
lemma kernelPostExact_inclusion {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    kernelPostExact f q ≫ closedStableInclusion (kernelClosedPredicate q) =
      closedStableInclusion (kernelClosedPredicate (f ≫ q : A ⟶ C)) ≫ sInputExactMap f :=
  closedStableMap_inclusion _ _ _ _

/-- Verdier 包含の核への後合成は、元の包含側の圏への厳密同型と実核同値の合成。 -/
lemma kernelPostExact_verdier_factor
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    kernelPostExact i q = (verdierCompositeKernelIso h).hom ≫ verdierKernelExact h := by
  apply closedStableInclusion_cancel (kernelClosedPredicate q)
  rw [kernelPostExact_inclusion]
  apply Subtype.ext
  change _ = (verdierCompositeKernelIso h).hom.val ≫
    (verdierKernelExact h).val ≫ (closedStableInclusion (kernelClosedPredicate q)).val
  rw [verdierKernelExact_ι]
  rfl

end SerrePositivity.KST.Fibration
