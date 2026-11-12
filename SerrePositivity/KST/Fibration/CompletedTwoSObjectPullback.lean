module
public import SerrePositivity.KST.Fibration.CompletedTwoJointReflection

/-! # 全 S_n 行の後の補完した二辺の元の object S 引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 任意の最内側 S_n 行の後も、元の同じ両射影の object S は厳密引き戻し。 -/
theorem completedTwo_sObjectS_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    IsPullback (objectSConstructionFunctor.map ((sEndofunctor n).map (completedTwoCofiber q)))
      (objectSConstructionFunctor.map ((sEndofunctor n).map (completedTwoFirst q)))
      (objectSConstructionFunctor.map ((sEndofunctor n).map (relativeCofiberSubobject
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q))))
      (objectSConstructionFunctor.map ((sEndofunctor n).map (weakArrowTargetTopExact q))) := by
  have hn := sConstruction_isPullback_of_gapped_reflection (completedTwo_isPullback q) n
    (completedTwo_isGapped_iff q)
  apply IsPullback.of_forall_isPullback_app
  intro m
  exact (sConstruction_isPullback_of_gapped_reflection hn m.unop.len
    (completedTwo_sJointReflection q n).isGapped_iff).map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

end SerrePositivity.KST.Fibration
