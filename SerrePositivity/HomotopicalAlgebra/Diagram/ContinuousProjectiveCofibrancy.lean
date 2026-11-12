module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftInduction
public import SerrePositivity.HomotopicalAlgebra.Diagram.Projective

/-! # Projective cofibrancy of continuous transfinite cofibration diagrams

The categorical lifting theorem is stated for any right class Q. Its
model-category application gives actual projective cofibrancy for any
well-ordered index, not just natural-number sequences.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.ContinuousLifts
variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {C : Type u} [Category.{v} C] {D U V : J ⥤ C} {p : U ⟶ V} {b : D ⟶ V}

namespace Partial

def ofBot (l : D.obj ⊥ ⟶ U.obj ⊥) (hl : l ≫ p.app ⊥ = b.app ⊥) : Partial p b ⊥ where
  hom i hi := by
    obtain rfl : i = ⊥ := le_antisymm hi bot_le
    exact l
  naturality {i k} hik hk := by
    obtain rfl : k = ⊥ := le_antisymm hk bot_le
    obtain rfl : i = ⊥ := le_antisymm hik bot_le
    simp only [homOfLE_refl, D.map_id, U.map_id, Category.id_comp, Category.comp_id]
  fac i hi := by
    obtain rfl : i = ⊥ := le_antisymm hi bot_le
    exact hl

end Partial

variable [HasInitial C] [D.IsWellOrderContinuous]

lemma projective_llp (Q : MorphismProperty C)
    (hbot : Q.llp (initial.to (D.obj ⊥)))
    (hstep : ∀ (j : J), ¬IsMax j → Q.llp (D.map (homOfLE (Order.le_succ j)))) :
    (Q.functorCategory J).llp (initial.to D) := by
  intro U V p hp
  constructor
  intro a b sq
  have : HasLiftingProperty (initial.to (D.obj ⊥)) (p.app ⊥) := hbot _ (hp ⊥)
  have q₀ : CommSq (initial.to (U.obj ⊥)) (initial.to (D.obj ⊥)) (p.app ⊥) (b.app ⊥) :=
    ⟨initial.hom_ext _ _⟩
  have hs (j : J) (hj : ¬IsMax j) :
      HasLiftingProperty (D.map (homOfLE (Order.le_succ j))) (p.app (Order.succ j)) :=
    hstep j hj _ (hp (Order.succ j))
  obtain ⟨l, hl⟩ := exists_lift p b hs (Partial.ofBot q₀.lift q₀.fac_right)
  exact CommSq.HasLift.mk' {
    l := l
    fac_left := initial.hom_ext _ _
    fac_right := hl }

end SerrePositivity.DiagramModel.ContinuousLifts

namespace SerrePositivity.DiagramModel.Projective
variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma isCofibrant_of_continuous (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hbot : IsCofibrant (D.obj ⊥))
    (hstep : ∀ (k : K), ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    let := modelCategory K I J; IsCofibrant D := by
  have hb : (trivialFibrations C).llp (initial.to (D.obj ⊥)) := by
    rw [trivialFibrations_llp C]
    exact (cofibration_iff _).mp ((isCofibrant_iff _).mp hbot)
  have hs (k : K) (hk : ¬IsMax k) :
      (trivialFibrations C).llp (D.map (homOfLE (Order.le_succ k))) := by
    rw [trivialFibrations_llp C]
    exact hstep k hk
  have h := ContinuousLifts.projective_llp (trivialFibrations C) hb hs
  let := modelCategory K I J
  apply (isCofibrant_iff D).mpr
  constructor
  rw [← trivialFibrations_llp (K ⥤ C)]
  intro U V p hp
  exact h p (fun k => ⟨hp.1 k, hp.2 k⟩)

end SerrePositivity.DiagramModel.Projective
