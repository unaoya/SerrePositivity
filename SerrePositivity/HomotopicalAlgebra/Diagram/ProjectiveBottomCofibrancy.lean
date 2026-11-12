module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacementFactor

/-! # Relative cofibrancy at the bottom of a projectively cofibrant diagram

This works for every partially ordered index with a least element and
does not require continuity or a well-order. The bottom-value replacement
keeps the prescribed lifting component fixed.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel
variable {K : Type w} [PartialOrder K] [OrderBot K]
  {C : Type u} [Category.{v} C] [ModelCategory C]

open BottomReplacement in
lemma fromBottom_llp_of_projective (R : K ⥤ C)
    (hR : ((trivialFibrations C).functorCategory K).llp (initial.to R)) :
    ((trivialFibrations C).functorCategory K).llp (ContinuousLifts.fromBottom R) := by
  intro U V p hp
  constructor
  intro a b sq
  let c := based b
  let q := change a c p sq.w
  have hq : (trivialFibrations C).functorCategory K q := by
    intro k
    change trivialFibrations C (changeApp a c p k)
    by_cases hk : k = ⊥
    · simpa only [changeApp, dite_eq_left hk] using
        (trivialFibrations C).of_isIso ((botIso a k hk).hom ≫ (botIso c k hk).inv)
    · simpa only [changeApp, dite_eq_right hk] using
        (trivialFibrations C).comp_mem _ _
          ((trivialFibrations C).of_isIso (awayIso a k hk).hom)
          ((trivialFibrations C).comp_mem _ _ (hp k)
            ((trivialFibrations C).of_isIso (awayIso c k hk).inv))
  have := hR q hq
  have test : CommSq (initial.to (diagram a)) (initial.to R) q (factor b) :=
    ⟨initial.hom_ext _ _⟩
  let L := test.lift ≫ comparison a
  have hfac : L ≫ p = b := by
    calc
      _ = test.lift ≫ (comparison a ≫ p) := Category.assoc _ _ _
      _ = test.lift ≫ (q ≫ comparison c) :=
        congrArg (fun t => test.lift ≫ t) (comparison_change a c p sq.w)
      _ = (test.lift ≫ q) ≫ comparison c := (Category.assoc _ _ _).symm
      _ = factor b ≫ comparison c := congrArg (fun t => t ≫ comparison c) test.fac_right
      _ = b := factor_comparison b
  have hbase : test.lift.app ⊥ ≫ (botIso a ⊥ rfl).hom = 𝟙 (R.obj ⊥) := by
    calc
      _ = test.lift.app ⊥ ≫ (q.app ⊥ ≫ (botIso c ⊥ rfl).hom) :=
        congrArg (fun t => test.lift.app ⊥ ≫ t) (change_bot_comp a c p sq.w).symm
      _ = (test.lift.app ⊥ ≫ q.app ⊥) ≫ (botIso c ⊥ rfl).hom :=
        (Category.assoc _ _ _).symm
      _ = (factor b).app ⊥ ≫ (botIso c ⊥ rfl).hom :=
        congrArg (fun t => t ≫ (botIso c ⊥ rfl).hom) (congr_app test.fac_right ⊥)
      _ = 𝟙 (R.obj ⊥) := factor_bot_comp b
  have hL₀ : L.app ⊥ = a.app ⊥ := by
    change test.lift.app ⊥ ≫ (comparison a).app ⊥ = a.app ⊥
    calc
      _ = test.lift.app ⊥ ≫ ((botIso a ⊥ rfl).hom ≫ a.app ⊥) :=
        congrArg (fun t => test.lift.app ⊥ ≫ t) (comparison_bot a)
      _ = (test.lift.app ⊥ ≫ (botIso a ⊥ rfl).hom) ≫ a.app ⊥ :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 (R.obj ⊥) ≫ a.app ⊥ := congrArg (fun t => t ≫ a.app ⊥) hbase
      _ = a.app ⊥ := Category.id_comp _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := hfac }
  apply NatTrans.ext
  funext k
  change R.map (homOfLE bot_le) ≫ L.app k = a.app k
  calc
    _ = L.app ⊥ ≫ U.map (homOfLE bot_le) := L.naturality (homOfLE bot_le)
    _ = a.app ⊥ ≫ U.map (homOfLE bot_le) := congrArg (fun t => t ≫ U.map _) hL₀
    _ = a.app k := by
      have hn := a.naturality (homOfLE (bot_le : (⊥ : K) ≤ k))
      change 𝟙 (R.obj ⊥) ≫ a.app k = a.app ⊥ ≫ U.map (homOfLE bot_le) at hn
      exact hn.symm.trans (Category.id_comp _)

namespace Projective
variable [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma fromBottom_cofibration_of_isCofibrant (R : K ⥤ C)
    (hR : let := modelCategory K I J; IsCofibrant R) :
    let := modelCategory K I J; cofibrations (K ⥤ C) (ContinuousLifts.fromBottom R) := by
  let := modelCategory K I J
  have := hR
  have hc : cofibrations (K ⥤ C) (initial.to R) := mem_cofibrations _
  rw [← trivialFibrations_llp (K ⥤ C)] at hc
  have hi : ((trivialFibrations C).functorCategory K).llp (initial.to R) := by
    intro U V p hp
    exact hc p ⟨fun k => (hp k).1, fun k => (hp k).2⟩
  have h := fromBottom_llp_of_projective R hi
  change cofibrations (K ⥤ C) (ContinuousLifts.fromBottom R)
  rw [← trivialFibrations_llp (K ⥤ C)]
  intro U V p hp
  exact h p (fun k => ⟨hp.1 k, hp.2 k⟩)

end Projective
end SerrePositivity.DiagramModel
