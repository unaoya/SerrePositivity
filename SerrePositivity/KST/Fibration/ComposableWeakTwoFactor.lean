module
public import SerrePositivity.KST.Fibration.ComposableWeakSingleStep
public import SerrePositivity.KST.Fibration.FinTwoProductIso
public import SerrePositivity.KST.Fibration.WeakArrowAdditivity

/-! # 二辺の有限積比較の第一辺の加法性と第二 cofiber による因子分解 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- Fin 2 積を二項積へ戻すと、元の初期頂点と同じ二つの cofiber を回収する。 -/
lemma composableWeakTwoComparison_normalize {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    composableWeakTwoComparison q r ≫ (𝟙 _ ⊗ₘ (finTwoProductIso
      ((multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)))).hom) =
        lift ((multiRealizationFunctor r).map (composableWeakInitialExact q))
          (lift ((multiRealizationFunctor r).map (composableWeakCofiberExact q 0))
            ((multiRealizationFunctor r).map (composableWeakCofiberExact q 1))) := by
  unfold composableWeakTwoComparison
  rw [lift_map, Category.comp_id, finTwoProductIso_lift]

/-- 元の第一 W 辺への射影と一辺の加法性は、同じ初期頂点と第一 cofiber の射対。 -/
lemma composableWeakFirst_additivity {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    (multiRealizationFunctor (r + 1)).map (composableWeakFirstExact q) ≫
      weakArrowMultiAdditivityMap q r =
        lift ((multiRealizationFunctor (r + 1)).map (composableWeakInitialExact q))
          ((multiRealizationFunctor (r + 1)).map (composableWeakCofiberExact q 0)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, weakArrowMultiAdditivityMap_fst, lift_fst,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · rw [Category.assoc, weakArrowMultiAdditivityMap_snd, lift_snd,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- 二辺の有限積比較は、元の第一辺・第二 cofiber の射対と一辺の加法性の合成。 -/
lemma composableWeakTwoComparison_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    composableWeakMultiStep q (r + 1) ≫ (weakArrowMultiAdditivityMap q r ⊗ₘ 𝟙 _) ≫
      (α_ _ _ _).hom = composableWeakTwoComparison q (r + 1) ≫
        (𝟙 _ ⊗ₘ (finTwoProductIso ((multiRealizationFunctor (r + 1)).obj
          (closedStableModel (kernelClosedPredicate q)))).hom) := by
  rw [composableWeakTwoComparison_normalize]
  unfold composableWeakMultiStep
  rw [← Category.assoc, lift_map, Category.comp_id, composableWeakFirst_additivity,
    lift_lift_associator_hom]

/-- 元の第一辺・第二 cofiber の射対の同値性は、元の二辺の有限積比較へ移る。 -/
lemma composableWeakTwoComparison_localized_isIso_of_step {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ)
    (h : IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakMultiStep q (r + 1)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (composableWeakTwoComparison q (r + 1))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have ha := weakArrowMultiAdditivityMap_localized_isIso q r
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso (weakArrowMultiAdditivityMap q r) ha
    ((multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q)))
  have he := congrArg Q.map (composableWeakTwoComparison_factor q r)
  have hi : IsIso (Q.map (composableWeakTwoComparison q (r + 1)) ≫
      Q.map (𝟙 _ ⊗ₘ (finTwoProductIso ((multiRealizationFunctor (r + 1)).obj
        (closedStableModel (kernelClosedPredicate q)))).hom)) := by
    rw [← Q.map_comp, ← he, Q.map_comp, Q.map_comp]
    change IsIso (Q.map (composableWeakMultiStep q (r + 1)) ≫
      Q.map (weakArrowMultiAdditivityMap q r ▷ _) ≫ Q.map (α_ _ _ _).hom)
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

end SerrePositivity.KST.Fibration
