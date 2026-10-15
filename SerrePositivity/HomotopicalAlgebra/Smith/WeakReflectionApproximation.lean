module

public import SerrePositivity.HomotopicalAlgebra.Smith.LocalPresentableCover

/-! # A presentable approximation through a weak reflection

Over an object whose image lies in P, a presentable stage can be enlarged so
that its image transition factors through the specified weak reflection.
-/

@[expose] public section
universe w v₁ v₂ u₁ u₂
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith

lemma exists_weakReflection_transition
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ]
    (F : C ⥤ D) [F.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    {P : ObjectProperty D} (r : PresentableWeakReflection P κ)
    {X : C} (hX : P (F.obj X)) (A : C) [IsCardinalPresentable A κ] (f : A ⟶ X) :
    ∃ (B : C) (_ : IsCardinalPresentable B κ) (i : A ⟶ B) (p : B ⟶ X)
      (u : r.R.obj (F.obj A) ⟶ F.obj B),
      i ≫ p = f ∧ r.unit.app (F.obj A) ≫ u = F.map i := by
  obtain ⟨J, _, _, ⟨pX⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  have := isFiltered_of_isCardinalFiltered J κ
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have hFX := isColimitOfPreserves F pX.isColimit
  have := r.preservesPresentable
  obtain ⟨g, hg⟩ := r.factor hX (F.map f)
  obtain ⟨j₀, i₀, hi₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ pX.isColimit f
  obtain ⟨j₁, u₀, hu₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hFX g
  let j := IsFiltered.max j₀ j₁
  let i := i₀ ≫ pX.diag.map (IsFiltered.leftToMax j₀ j₁)
  let u := u₀ ≫ F.map (pX.diag.map (IsFiltered.rightToMax j₀ j₁))
  have hi : i ≫ pX.ι.app j = f := by
    dsimp [i, j]
    rw [Category.assoc, pX.w]
    exact hi₀
  have hu : u ≫ F.map (pX.ι.app j) = g := by
    change u₀ ≫ F.map (pX.ι.app j₁) = g at hu₀
    dsimp [u, j]
    rw [Category.assoc, ← F.map_comp, pX.w]
    exact hu₀
  obtain ⟨k, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
    κ hFX (F.map i) (r.unit.app (F.obj A) ≫ u) (by
      change F.map i ≫ F.map (pX.ι.app j) =
        (r.unit.app (F.obj A) ≫ u) ≫ F.map (pX.ι.app j)
      rw [← F.map_comp, hi, Category.assoc, hu, hg])
  refine ⟨pX.diag.obj k, pX.prop_diag_obj k, i ≫ pX.diag.map a,
    pX.ι.app k, u ≫ F.map (pX.diag.map a), ?_, ?_⟩
  · rw [Category.assoc, pX.w]
    exact hi
  · change F.map i ≫ F.map (pX.diag.map a) =
      (r.unit.app (F.obj A) ≫ u) ≫ F.map (pX.diag.map a) at ha
    rw [F.map_comp, ← Category.assoc]
    exact ha.symm

end SerrePositivity.Smith
