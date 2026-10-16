module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation

/-! # The iterated generator presentation as the actual free-path categories

The object type stays the original C in all degrees, and the Hom universe
is max u v after an initial Hom-only lift. The degree categories agree
with the corresponding actual comonad powers.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorCategories
open FreeGeneratorDegeneracies
variable (C : Type u) [Category.{v} C]

def identity (n : ℕ) (X : C) : hom n X X := by
  cases n with
  | zero => exact ⟨𝟙 X⟩
  | succ n => exact @Quiver.Path.nil C (quiver n) X

def compose (n : ℕ) {X Y Z : C} (f : hom n X Y) (g : hom n Y Z) : hom n X Z := by
  cases n with
  | zero => exact ⟨f.down ≫ g.down⟩
  | succ n => exact @Quiver.Path.comp C (quiver n) X Y Z f g

@[instance_reducible] def category (n : ℕ) : Category.{max u v} C where
  Hom X Y := hom n X Y
  id X := identity C n X
  comp f g := compose C n f g
  id_comp f := by
    cases n with
    | zero => apply ULift.ext; exact Category.id_comp f.down
    | succ n =>
      let _ := quiver (V := C) n
      exact Quiver.Path.nil_comp f
  comp_id f := by
    cases n with
    | zero => apply ULift.ext; exact Category.comp_id f.down
    | succ n =>
      let _ := quiver (V := C) n
      exact Quiver.Path.comp_nil f
  assoc f g h := by
    cases n with
    | zero => apply ULift.ext; exact Category.assoc f.down g.down h.down
    | succ n =>
      let _ := quiver (V := C) n
      exact Quiver.Path.comp_assoc f g h

def degree (n : ℕ) : Cat.{max u v, u} := @Cat.of.{max u v, u} C (category C n)

lemma degree_zero : degree C 0 = FreePathResolutionPresentation.base C := rfl

lemma degree_succ (n : ℕ) :
    degree C (n + 1) = FreePathResolution.comonad.obj (degree C n) := rfl

lemma degree_power (n : ℕ) : degree C n =
    ComonadResolutionOperators.power FreePathResolution.comonad
      (FreePathResolutionPresentation.base C) n := by
  induction n with
  | zero => exact degree_zero C
  | succ n ih =>
    change degree C (n + 1) = FreePathResolution.comonad.obj _
    rw [← ih]
    exact degree_succ C n

def degeneracyFunctor (n : ℕ) (i : Fin (n + 1)) : degree C (n + 1) ⥤ degree C (n + 2) where
  obj X := X
  map p := QuiverPaths.mapPath (A := quiver n) (B := quiver (n + 1)) (degeneracy n i) p
  map_id _ := rfl
  map_comp p q := QuiverPaths.mapPath_concat
    (A := quiver n) (B := quiver (n + 1)) (degeneracy n i) p q

lemma degeneracyFunctor_generator (n : ℕ) (i : Fin (n + 1)) {X Y : C} (e : hom n X Y) :
    (degeneracyFunctor C n i).map (singleton n e) = singleton (n + 1) (degeneracy n i e) := rfl

lemma degeneracyFunctor_zero (n : ℕ) :
    degeneracyFunctor C n 0 = (FreePathResolution.comonad.δ.app (degree C n)).toFunctor := by
  refine Paths.ext_functor (V := degree C n) (F := degeneracyFunctor C n 0)
    (G := (FreePathResolution.comonad.δ.app (degree C n)).toFunctor) rfl ?_
  intro X Y e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change singleton (n + 1) (degeneracy n 0 e) =
    (FreePathResolution.duplicate (degree C n)).map e.toPath
  rw [FreePathResolution.duplicate_generator, degeneracy_zero]
  rfl

lemma degeneracyFunctor_succ (n : ℕ) (i : Fin (n + 1)) :
    degeneracyFunctor C (n + 1) i.succ =
      (FreePathResolution.comonad.map (degeneracyFunctor C n i).toCatHom).toFunctor := by
  refine Paths.ext_functor (V := degree C (n + 1))
    (F := degeneracyFunctor C (n + 1) i.succ)
    (G := (FreePathResolution.comonad.map (degeneracyFunctor C n i).toCatHom).toFunctor) rfl ?_
  intro X Y e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma degree_cast_succ (n : ℕ) : eqToHom (degree_power C (n + 1)) =
    FreePathResolution.comonad.map (eqToHom (degree_power C n)) :=
  (eqToHom_map (FreePathResolution.comonad.{u, v} :
    Cat.{max u v, u} ⥤ Cat.{max u v, u}) (degree_power C n)).symm

lemma degeneracy_comparison_zero (n : ℕ) :
    (degeneracyFunctor C n 0).toCatHom ≫ eqToHom (degree_power C (n + 2)) =
      eqToHom (degree_power C (n + 1)) ≫
        ComonadResolutionOperators.degeneracy FreePathResolution.comonad
          (FreePathResolutionPresentation.base C) n 0 := by
  have hz : (degeneracyFunctor C n 0).toCatHom =
      FreePathResolution.comonad.δ.app (degree C n) :=
    Cat.Hom.ext (degeneracyFunctor_zero C n)
  rw [hz, degree_cast_succ C (n + 1), degree_cast_succ C n,
    ComonadResolutionOperators.degeneracy_zero]
  exact (FreePathResolution.comonad.δ.naturality (eqToHom (degree_power C n))).symm

lemma degeneracy_comparison (n : ℕ) (i : Fin (n + 1)) :
    (degeneracyFunctor C n i).toCatHom ≫ eqToHom (degree_power C (n + 2)) =
      eqToHom (degree_power C (n + 1)) ≫
        ComonadResolutionOperators.degeneracy FreePathResolution.comonad
          (FreePathResolutionPresentation.base C) n i := by
  induction n with
  | zero => fin_cases i; exact degeneracy_comparison_zero C 0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact degeneracy_comparison_zero C (n + 1)
    | succ i =>
      have hs : (degeneracyFunctor C (n + 1) i.succ).toCatHom =
          FreePathResolution.comonad.map (degeneracyFunctor C n i).toCatHom :=
        Cat.Hom.ext (degeneracyFunctor_succ C n i)
      rw [hs, degree_cast_succ C (n + 2), ComonadResolutionOperators.degeneracy_succ]
      conv_rhs => rw [degree_cast_succ C (n + 1)]
      rw [← FreePathResolution.comonad.map_comp, ← FreePathResolution.comonad.map_comp, ih i]

lemma generator_image_intersection (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j)
    {X Y : C} (p q : hom (n + 1) X Y) :
    (degeneracyFunctor C (n + 1) i.castSucc).map (singleton (n + 1) p) =
      (degeneracyFunctor C (n + 1) j.succ).map (singleton (n + 1) q) ↔
        ∃ r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r := by
  rw [degeneracyFunctor_generator, degeneracyFunctor_generator]
  exact (singleton_injective (V := C) (n + 2)).eq_iff.trans
    (degeneracy_intersection_iff n i j h p q)

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorCategories
