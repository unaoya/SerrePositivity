module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits

/-!
概要：元の左 Kan 標準余錐の普遍性から、任意の全係数制限の Hom 族の右 Kan 条件を得る。
方針：元の反転標準錐を共同 Hom で写し、元の係数の全評価で極限性を判定する。
規約：全係数を持つ元の関手圏値の族と、持ち上げた元の反対射を保持する。
使われ方：大きい係数前層への全自然変換空間族の右 Kan 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全標準余錐の普遍性は、任意の全係数制限を持つ元の Hom 族の右 Kan 条件を与える。 -/
lemma homCanonical_isRightKanExtension {K C D : SSet.{u}} [Quasicategory D]
    {A : SSet.{u + 1}} (δ : K ⟶ C) (F : C ⟶ D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj D)
    (h : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c)) :
    IsRightKanExtension ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ))
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
          (coyonedaInfinityMap D ≫ (pre f).app SpaceInfinity.{u})))
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
        (coyonedaInfinityMap D ≫ (pre f).app SpaceInfinity.{u}))
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
          (coyonedaInfinityMap D ≫ (pre f).app SpaceInfinity.{u})))) := by
  apply rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have hc := rightKanCanonicalCone_op_isLimit δ F (SSet.opObjEquiv c) (h (SSet.opObjEquiv c))
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at hc
  apply isLimitCone_of_pointwise
  intro a
  change IsLimitCone (mapJoinCone
    ((coyonedaInfinityMap D ≫ (pre f).app SpaceInfinity.{u}) ≫ evaluateFunctorAt a)
    (JoinCone.ulift.{u, u + 1}
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F) c)))
  rw [Category.assoc, evaluateFunctorAt_pre]
  change IsLimitCone (mapJoinCone
    (coyonedaInfinityMap D ≫ evaluateFunctorAt (ULift.up ((f.app (Opposite.op ⦋0⦌) a).down)))
    (JoinCone.ulift.{u, u + 1}
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F) c)))
  rw [coyonedaInfinityMap_evaluation]
  exact representablePresheafInfinity_isLimit _ hc _

end SerrePositivity.InfinityCategories.HomotopyLimits
