module
public import SerrePositivity.KST.Fibration.WeakStringRealizationConstants
public import SerrePositivity.KST.Fibration.WeakStringGappedVerticesEquiv
public import SerrePositivity.KST.SConstruction.ConstantFamilySwap

/-! # 元の定数 W 列の gapped 交換と元の相対 S の定値単体の厳密照合 -/

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

/-- 元の定数 W 列を gapped 交換すると、元の同じ相対 S 頂点の定値単体を得る。 -/
lemma weakStringGappedRelativeMap_constant {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n m : ℕ) (v : (sConstruction n B.obj) _⦋0⦌) :
    weakStringGappedRelativeMap q
      ((objectSConstructionFunctor.map (weakStringConstantExact q ⦋m⦌)).app
        (Opposite.op ⦋n⦌) v) =
      (SSet.const ⟨v, relativeDiagram_vertex q.hom (sComponentEvaluation B.obj n) v⟩ :
        (Δ[m] : SSet.{u}) ⟶ (relativeSConstruction q.hom n : SSet.{u})) := by
  apply (cancel_mono (relativeSConstruction q.hom n).ι).1
  apply (cancel_mono (gappedSubcomplex n B.obj).ι).1
  rw [weakStringGappedRelativeMap_inclusion, weakStringGappedTranspose_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) B.obj
    (gappedDiagram ((objectSConstructionFunctor.map
      (weakStringConstantExact q ⦋m⦌)).app (Opposite.op ⦋n⦌) v) ≫ _) = _
  rw [gappedDiagram_objectSFunctor_map, Category.assoc, weakStringConstantExact_ι,
    flipConstantFamily]
  simp only [SSet.const_comp]
  congr 1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ B.obj).apply_symm_apply v.val

end SerrePositivity.KST.Fibration
