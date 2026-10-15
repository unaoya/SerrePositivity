module

public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-! # The converse Whitehead theorem for model categories

A homotopy inverse of a fibration can be made into a strict section by a
cylinder lift. The fibration is then an actual retract of a map homotopic
to the identity. Only the ordinary model axioms are used.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]

lemma weakEquivalences_iff_of_leftHomotopy {X Y : C} {f g : X ⟶ Y}
    (h : LeftHomotopyRel f g) : weakEquivalences C f ↔ weakEquivalences C g := by
  obtain ⟨P, ⟨h⟩⟩ := h
  have h₀ := (weakEquivalences C).precomp_iff P.i₀ h.h (mem_weakEquivalences P.i₀)
  have h₁ := (weakEquivalences C).precomp_iff P.i₁ h.h (mem_weakEquivalences P.i₁)
  rw [h.h₀] at h₀
  rw [h.h₁] at h₁
  exact h₀.trans h₁.symm

/-- Cylinder lifting strictifies the right-inverse equation of a fibration. -/
lemma section_of_leftHomotopyInverse {X Y : C} [IsCofibrant Y]
    (p : X ⟶ Y) [Fibration p] (g : Y ⟶ X)
    (hg : LeftHomotopyRel (g ≫ p) (𝟙 Y)) :
    ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y ∧ LeftHomotopyRel g s := by
  obtain ⟨P, hP, ⟨h⟩⟩ := hg.exists_good_cylinder
  have := hP
  have sq : CommSq g P.i₀ p h.h := ⟨h.h₀.symm⟩
  refine ⟨P.i₁ ≫ sq.lift, ?_, ?_⟩
  · rw [Category.assoc, sq.fac_right, h.h₁]
  · exact (show P.LeftHomotopy g (P.i₁ ≫ sq.lift) from
      { h := sq.lift, h₀ := sq.fac_left }).leftHomotopyRel

lemma weakEquivalence_of_fibration_leftHomotopyInverse {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] [IsFibrant X]
    (p : X ⟶ Y) [Fibration p] (g : Y ⟶ X)
    (hX : LeftHomotopyRel (p ≫ g) (𝟙 X))
    (hY : LeftHomotopyRel (g ≫ p) (𝟙 Y)) : weakEquivalences C p := by
  obtain ⟨s, hs, hgs⟩ := section_of_leftHomotopyInverse p g hY
  have hps : LeftHomotopyRel (p ≫ s) (𝟙 X) := (hgs.precomp p).symm.trans hX
  have hw : weakEquivalences C (p ≫ s) :=
    (weakEquivalences_iff_of_leftHomotopy hps).mpr ((weakEquivalences C).id_mem X)
  have hr : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 X) s (by simp)
      r := Arrow.homMk (𝟙 X) p (by simp [Category.assoc, hs])
      retract := by ext <;> simp [hs] }
  exact (weakEquivalences C).of_retract hr hw

end SerrePositivity.Quillen
