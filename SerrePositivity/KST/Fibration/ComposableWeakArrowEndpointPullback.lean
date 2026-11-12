module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowObjectPullback
public import SerrePositivity.KST.Fibration.WeakArrowEndpointExact
public import SerrePositivity.KST.Fibration.ClosedTopIso

/-! # 相対 cofiber の subobject と同じ値域での二つの W 辺の引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の W 辺の始点を K-1 の全頂点部分圏に値を持たせた完全関手。 -/
def weakArrowSourceTopExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  weakArrowSourceExact q ≫ closedTopLift (sInputModel B)

/-- 元の W 辺の終点を同じ全頂点部分圏に値を持たせた完全関手。 -/
def weakArrowTargetTopExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  weakArrowTargetExact q ≫ closedTopLift (sInputModel B)

/-- 相対 cofiber の底辺の始点は、全頂点部分圏値でも元の subobject 射と厳密に一致する。 -/
lemma weakCofiberProjection_sourceTop {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowCofiberEquivalence q).hom ≫ weakArrowSourceTopExact q =
      relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q) := by
  change _ ≫ (weakArrowSourceExact q ≫ (closedTopExactIso (sInputModel B)).inv) = _
  rw [← Category.assoc, weakCofiberProjection_source, Category.assoc]
  change _ ≫ ((closedTopExactIso (sInputModel B)).hom ≫
    (closedTopExactIso (sInputModel B)).inv) = _
  rw [Iso.hom_inv_id, Category.comp_id]

/-- 二つの W 辺の object S 引き戻しを、相対 subobject と同じ元の全頂点部分圏上に戻す。 -/
theorem composableWeakArrow_top_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (composableWeakFirstExact q).val (composableWeakNextExact q).val
      (weakArrowTargetTopExact q).val (weakArrowSourceTopExact q).val := by
  let e := stableModelForget.mapIso
    (ambientPointExactIso B ≪≫ (closedTopExactIso (sInputModel B)).symm)
  apply (composableWeakArrow_isPullback q).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · rfl
  · rfl

/-- 同じ全頂点部分圏上の引き戻しを元の object S でも保持する。 -/
theorem composableWeakArrow_objectS_top_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (objectSConstructionFunctor.map (composableWeakFirstExact q))
      (objectSConstructionFunctor.map (composableWeakNextExact q))
      (objectSConstructionFunctor.map (weakArrowTargetTopExact q))
      (objectSConstructionFunctor.map (weakArrowSourceTopExact q)) := by
  let e := objectSConstructionFunctor.mapIso
    (ambientPointExactIso B ≪≫ (closedTopExactIso (sInputModel B)).symm)
  apply (composableWeakArrow_objectS_isPullback q).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp
  · simp
  · change _ ≫ objectSConstructionFunctor.map _ = 𝟙 _ ≫ _
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  · change _ ≫ objectSConstructionFunctor.map _ = 𝟙 _ ≫ _
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    rfl

end SerrePositivity.KST.Fibration
