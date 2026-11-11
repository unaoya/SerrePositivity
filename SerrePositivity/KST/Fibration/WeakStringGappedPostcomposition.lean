module
public import SerrePositivity.KST.Fibration.WeakStringPostNaturality
public import SerrePositivity.KST.Fibration.WeakStringGappedVerticesEquiv
public import SerrePositivity.KST.Fibration.FamilyFlipPostcomposition

/-! # 元の gapped W 列と相対 S 単体の交換は包含側の完全関手を保つ -/

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

/-- 元の相対 S への実単体の交換は、元の包含側の完全関手と厳密に可換。 -/
lemma weakStringGappedRelativeMap_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n m : ℕ}
    (v : (sConstruction n (weakStringCategory (f ≫ q : A ⟶ C) ⦋m⦌)) _⦋0⦌) :
    weakStringGappedRelativeMap q
      (((sEndofunctor n).map (weakStringPostExact f q ⦋m⦌)).val.app (Opposite.op ⦋0⦌) v) =
      weakStringGappedRelativeMap (f ≫ q : A ⟶ C) v ≫ relativeSFunctorMap f q.hom n := by
  apply (cancel_mono (relativeSConstruction q.hom n).ι).1
  apply (cancel_mono (gappedSubcomplex n B.obj).ι).1
  simp only [Category.assoc, relativeSFunctorMap_ι, sPostcomp_ι,
    weakStringGappedRelativeMap_inclusion,
    weakStringGappedTranspose_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) B.obj
    (gappedDiagram ((sPostcompCofiber n (weakStringPostMap f q ⦋m⦌)
      (weakStringPostExact f q ⦋m⦌).property).app _ v) ≫ _) = _
  rw [gappedDiagram_sPostcompCofiber, Category.assoc, weakStringPostMap_ι,
    ← Category.assoc, familyFlip_postcomp]
  change _ = weakStringGappedRelativeMap (f ≫ q : A ⟶ C) v ≫
    (relativeSConstruction (f ≫ q : A ⟶ C).hom n).ι ≫
      (gappedSubcomplex n A.obj).ι ≫ (ihom (arNerve n)).map f.hom
  rw [weakStringGappedRelativeMap_inclusion_assoc, weakStringGappedTranspose_ι_assoc]
  rfl

end SerrePositivity.KST.Fibration
