module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousProjectiveCofibrancy

/-! # Relative projective cofibrancy of continuous cofibration diagrams

The natural map from the constant initial-stage diagram is projectively
cofibrant even when the initial object of the sequence is not cofibrant.
The lift keeps its prescribed bottom component throughout the induction.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.ContinuousLifts
section Base
variable {K : Type w} [Preorder K] [OrderBot K] {C : Type u} [Category.{v} C]

@[simps]
def fromBottom (D : K ⥤ C) : (Functor.const K).obj (D.obj ⊥) ⟶ D where
  app k := D.map (homOfLE bot_le)
  naturality i j f := by
    change 𝟙 (D.obj ⊥) ≫ D.map (homOfLE (bot_le : (⊥ : K) ≤ j)) =
      D.map (homOfLE (bot_le : (⊥ : K) ≤ i)) ≫ D.map f
    exact (Category.id_comp _).trans (D.map_comp (homOfLE bot_le) f)

lemma fromBottom_naturality {D E : K ⥤ C} (p : D ⟶ E) :
    fromBottom D ≫ p = (Functor.const K).map (p.app ⊥) ≫ fromBottom E := by
  apply NatTrans.ext
  funext k
  exact p.naturality (homOfLE (bot_le : (⊥ : K) ≤ k))

end Base

variable {K : Type w} [LinearOrder K] [OrderBot K] {C : Type u} [Category.{v} C]
  [SuccOrder K] [WellFoundedLT K] (D : K ⥤ C) [D.IsWellOrderContinuous]

lemma fromBottom_llp (Q : MorphismProperty C)
    (hstep : ∀ (k : K), ¬IsMax k → Q.llp (D.map (homOfLE (Order.le_succ k)))) :
    (Q.functorCategory K).llp (fromBottom D) := by
  intro U V p hp
  constructor
  intro a b sq
  have hs (k : K) (hk : ¬IsMax k) :
      HasLiftingProperty (D.map (homOfLE (Order.le_succ k))) (p.app (Order.succ k)) :=
    hstep k hk _ (hp (Order.succ k))
  have h₀ : a.app ⊥ ≫ p.app ⊥ = b.app ⊥ := by
    have h := congr_app sq.w ⊥
    change a.app ⊥ ≫ p.app ⊥ = D.map (homOfLE (bot_le : (⊥ : K) ≤ ⊥)) ≫ b.app ⊥ at h
    simpa only [homOfLE_refl, D.map_id, Category.id_comp] using h
  obtain ⟨l, hl, hbase⟩ := exists_lift_with_base p b hs (Partial.ofBot (a.app ⊥) h₀)
  change l.app ⊥ = a.app ⊥ at hbase
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := hl }
  apply NatTrans.ext
  funext k
  change D.map (homOfLE bot_le) ≫ l.app k = a.app k
  calc
    _ = l.app ⊥ ≫ U.map (homOfLE bot_le) := l.naturality (homOfLE bot_le)
    _ = a.app ⊥ ≫ U.map (homOfLE bot_le) := congrArg (fun t => t ≫ U.map _) hbase
    _ = a.app k := by
      have hn := a.naturality (homOfLE (bot_le : (⊥ : K) ≤ k))
      change 𝟙 (D.obj ⊥) ≫ a.app k = a.app ⊥ ≫ U.map (homOfLE bot_le) at hn
      exact hn.symm.trans (Category.id_comp _)

end SerrePositivity.DiagramModel.ContinuousLifts

namespace SerrePositivity.DiagramModel.Projective
variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma fromBottom_cofibration (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ (k : K), ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    let := modelCategory K I J; cofibrations (K ⥤ C) (ContinuousLifts.fromBottom D) := by
  have hs (k : K) (hk : ¬IsMax k) :
      (trivialFibrations C).llp (D.map (homOfLE (Order.le_succ k))) := by
    rw [trivialFibrations_llp C]
    exact hstep k hk
  have h := ContinuousLifts.fromBottom_llp D (trivialFibrations C) hs
  let := modelCategory K I J
  change cofibrations (K ⥤ C) (ContinuousLifts.fromBottom D)
  rw [← trivialFibrations_llp (K ⥤ C)]
  intro U V p hp
  exact h p (fun k => ⟨hp.1 k, hp.2 k⟩)

end SerrePositivity.DiagramModel.Projective
