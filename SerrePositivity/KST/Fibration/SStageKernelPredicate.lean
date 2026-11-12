module
public import SerrePositivity.KST.Fibration.SComponentExactness
public import SerrePositivity.KST.Fibration.KernelCofiberModel
public import SerrePositivity.KST.SConstruction.SClosedStableIso

/-! # 同じ S 後合成の実核と、元の核条件を持つ全 Ar 図式との一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の核の全 Ar 成分条件は、元の同じ S 後合成による零化と同値。 -/
theorem sStageKernelPredicate_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)
    (v : (sConstruction n B.obj) _⦋0⦌) :
    (sClosedPredicate n (kernelClosedPredicate q)).predicate v ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((sPostcomp n q.hom (exactMap_preservesSData q)).app
        (Opposite.op ⦋0⦌) v) := by
  rw [sConstruction_isZeroVertex_iff_components]
  apply forall_congr'
  intro a
  have he := congrArg (fun m : sConstruction n B.obj ⟶ C.obj =>
    m.app (Opposite.op ⦋0⦌) v)
    (sPostcomp_gapped_evaluate n q.hom (exactMap_preservesSData q) a)
  exact iff_of_eq (congrArg (fun z : C.obj _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) he.symm)

end SerrePositivity.KST.Fibration
