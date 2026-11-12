module
public import SerrePositivity.KST.Fibration.CompletedTwoSPullback
public import SerrePositivity.KST.SConstruction.ObjectSTrivialFibration

/-! # 第二辺の元の cofiber 選択による完全な切断 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の第二辺と既存の同じ cofiber 選択による厳密な切断。 -/
def completedTwoSectionMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (composableWeakArrowModel q).carrier ⟶ (completedTwoModel q).carrier :=
  pullback.lift ((composableWeakNextExact q ≫ (weakArrowCofiberEquivalence q).inv).val)
    (𝟙 _) (by
      change ((composableWeakNextExact q ≫ (weakArrowCofiberEquivalence q).inv) ≫
        (weakArrowCofiberEquivalence q).hom).val = _
      rw [Category.assoc, weakArrowCofiberEquivalence_inv_hom, Category.comp_id]
      rfl)

/-- 元の二辺への射影は同じ厳密な恒等射を回収する。 -/
lemma completedTwoSectionMap_forget {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoSectionMap q ≫ (completedTwoForget q).val = 𝟙 _ := pullback.lift_snd _ _ _

/-- 厳密な切断は元の補完を忘れる射影の普遍性の反映により完全。 -/
def completedTwoSection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakArrowModel q ⟶ completedTwoModel q :=
  ⟨completedTwoSectionMap q, by
    apply preservesCofiberData_of_trivialProjection (completedTwoForget q).val
    rw [completedTwoSectionMap_forget]
    exact preservesCofiberData_id _⟩

/-- 完全な切断も元の二辺を厳密に保つ。 -/
lemma completedTwoSection_forget {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoSection q ≫ completedTwoForget q = 𝟙 _ :=
  Subtype.ext (completedTwoSectionMap_forget q)

/-- 切断で得る相対 cofiber 図式は既存の第二 W 辺の同じ補完。 -/
lemma completedTwoSection_cofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoSection q ≫ completedTwoCofiber q =
      composableWeakNextExact q ≫ (weakArrowCofiberEquivalence q).inv :=
  Subtype.ext (pullback.lift_fst _ _ _)

/-- 切断は object S の後も局所化同型。一般の弱同値の基底変換は仮定しない。 -/
lemma completedTwoSection_objectS_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (completedTwoSection q))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map (objectSConstructionFunctor.map (completedTwoForget q))) :=
    objectS_map_localized_isIso_of_trivialKanFibration (completedTwoForget q)
  have h : IsIso (Q.map (objectSConstructionFunctor.map
      (completedTwoSection q ≫ completedTwoForget q))) := by
    rw [completedTwoSection_forget, CategoryTheory.Functor.map_id, Q.map_id]
    infer_instance
  rw [CategoryTheory.Functor.map_comp, Q.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

end SerrePositivity.KST.Fibration
