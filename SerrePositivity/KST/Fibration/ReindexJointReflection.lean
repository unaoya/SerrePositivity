module
public import SerrePositivity.KST.Fibration.JointReflection

/-! # 添字の全頂点を覆う二つの制限による実普遍性の共同反映 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全頂点を覆う二つの添字制限は、全図式圏の零対象と実押し出しを共同で反映する。 -/
lemma reindex_jointReflection {K L M : SSet.{u}} (i : L ⟶ K) (j : M ⟶ K)
    (hc : ∀ k : K _⦋0⦌, (∃ a, i.app (Opposite.op ⦋0⦌) a = k) ∨
      ∃ a, j.app (Opposite.op ⦋0⦌) a = k) (B : StableModel.{u}) :
    JointlyReflectsSData ((pre i).app B.carrier) ((pre j).app B.carrier) where
  zero v hi hj := by
    apply isZeroVertex_of_pointwise
    intro k
    obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := hc k
    · have h := isZeroVertex_evaluateFunctorAt hi a
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre i).app B.carrier ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app _ v) at h
      rwa [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
    · have h := isZeroVertex_evaluateFunctorAt hj a
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre j).app B.carrier ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app _ v) at h
      rwa [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
  pushout F hi hj := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
    intro k
    obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := hc k
    · have h := (evaluateFunctorAt_preservesSConstructionData (C := B.carrier) a).2 _ hi
      rwa [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
    · have h := (evaluateFunctorAt_preservesSConstructionData (C := B.carrier) a).2 _ hj
      rwa [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h

end SerrePositivity.KST.Fibration
