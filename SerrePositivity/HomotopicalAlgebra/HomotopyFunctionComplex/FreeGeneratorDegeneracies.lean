module

public import SerrePositivity.CategoryTheory.Quiver.PathIntersections
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-! # All-degree degeneracies and their exact intersections for iterated free generators

The objects stay fixed and the arrows are iterated paths, starting with a
Hom-only universe lift. These are the generator-level insertion operations
needed for the all-degree relative free-resolution induction. The comparison
with the bundled categorical resolution is proved in `FreeGeneratorCategories`.
-/

@[expose] public section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorDegeneracies
open Quiver
variable {V : Type u} [Quiver.{v} V]

def hom : ℕ → V → V → Type (max u v)
  | 0, X, Y => ULift.{u} (X ⟶ Y)
  | n + 1, X, Y => @Path V ⟨hom n⟩ X Y

abbrev quiver (n : ℕ) : Quiver.{max u v} V := ⟨hom n⟩

def singleton (n : ℕ) {X Y : V} (e : hom n X Y) : hom (n + 1) X Y :=
  @Quiver.Hom.toPath V (quiver n) X Y e

def degeneracy : (n : ℕ) → Fin (n + 1) → {X Y : V} → hom n X Y → hom (n + 1) X Y
  | 0, _, _, _, e => singleton 0 e
  | n + 1, i, _, _, p => Fin.cases (singleton (n + 1) p)
      (fun j => QuiverPaths.mapPath (A := quiver n) (B := quiver (n + 1)) (degeneracy n j) p) i

lemma degeneracy_zero (n : ℕ) {X Y : V} (e : hom n X Y) :
    degeneracy n 0 e = singleton n e := by cases n <;> rfl

lemma degeneracy_succ (n : ℕ) (i : Fin (n + 1)) {X Y : V} (p : hom (n + 1) X Y) :
    degeneracy (n + 1) i.succ p =
      QuiverPaths.mapPath (A := quiver n) (B := quiver (n + 1)) (degeneracy n i) p := rfl

lemma singleton_injective (n : ℕ) {X Y : V} :
    Function.Injective (singleton (V := V) n (X := X) (Y := Y)) :=
  QuiverPaths.singleton_injective (A := quiver n)

lemma degeneracy_injective (n : ℕ) (i : Fin (n + 1)) {X Y : V} :
    Function.Injective (degeneracy n i (X := X) (Y := Y)) := by
  induction n generalizing X Y with
  | zero => exact singleton_injective 0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact singleton_injective (n + 1)
    | succ i =>
      exact QuiverPaths.mapPath_injective (A := quiver n) (B := quiver (n + 1))
        (degeneracy n i) (fun _ _ => ih i)

lemma degeneracy_singleton (n : ℕ) (i : Fin (n + 1)) {X Y : V} (e : hom n X Y) :
    degeneracy (n + 1) i.succ (singleton n e) = singleton (n + 1) (degeneracy n i e) := rfl

lemma degeneracy_degeneracy (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j)
    {X Y : V} (e : hom n X Y) :
    degeneracy (n + 1) i.castSucc (degeneracy n j e) =
      degeneracy (n + 1) j.succ (degeneracy n i e) := by
  induction n generalizing X Y with
  | zero => fin_cases i; fin_cases j; rfl
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rw [Fin.castSucc_zero, degeneracy_zero, degeneracy_zero, degeneracy_singleton]
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        have hij : i ≤ j := Fin.succ_le_succ_iff.mp h
        change QuiverPaths.mapPath (A := quiver (n + 1)) (B := quiver (n + 2))
          (degeneracy (n + 1) i.castSucc)
          (QuiverPaths.mapPath (A := quiver n) (B := quiver (n + 1)) (degeneracy n j) e) =
            QuiverPaths.mapPath (A := quiver (n + 1)) (B := quiver (n + 2))
              (degeneracy (n + 1) j.succ)
              (QuiverPaths.mapPath (A := quiver n) (B := quiver (n + 1)) (degeneracy n i) e)
        rw [QuiverPaths.mapPath_comp, QuiverPaths.mapPath_comp]
        exact QuiverPaths.mapPath_congr (A := quiver n) (B := quiver (n + 2))
          _ _ (fun d => ih i j hij d) e

lemma degeneracy_intersection (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j)
    {X Y : V} (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i.castSucc p = degeneracy (n + 1) j.succ q) :
    ∃ r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r := by
  induction n generalizing X Y with
  | zero =>
    fin_cases i; fin_cases j
    have hh : QuiverPaths.mapPath (A := quiver 0) (B := quiver 1)
        (degeneracy 0 0) q = singleton 1 p := hpq.symm
    obtain ⟨r, hr, hr'⟩ := QuiverPaths.mapPath_eq_singleton
      (A := quiver 0) (B := quiver 1) (degeneracy 0 0) q p hh
    exact ⟨r, hr'.symm, hr⟩
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      have hh : QuiverPaths.mapPath (A := quiver (n + 1)) (B := quiver (n + 2))
          (degeneracy (n + 1) j) q = singleton (n + 2) p := hpq.symm
      obtain ⟨r, hr, hr'⟩ := QuiverPaths.mapPath_eq_singleton (A := quiver (n + 1))
        (B := quiver (n + 2)) (degeneracy (n + 1) j) q p hh
      exact ⟨r, hr'.symm, hr⟩
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        have hij : i ≤ j := Fin.succ_le_succ_iff.mp h
        change QuiverPaths.mapPath (A := quiver (n + 1)) (B := quiver (n + 2))
          (degeneracy (n + 1) i.castSucc) p =
            QuiverPaths.mapPath (degeneracy (n + 1) j.succ) q at hpq
        obtain ⟨r, hr, hr'⟩ := QuiverPaths.mapPath_intersection
          (A := quiver (n + 1)) (B := quiver (n + 1))
          (D := quiver (n + 2)) (K := quiver n)
          (degeneracy (n + 1) i.castSucc) (degeneracy (n + 1) j.succ)
          (degeneracy n j) (degeneracy n i)
          (fun x y hxy => by
            obtain ⟨z, hz, hz'⟩ := ih i j hij x y hxy
            exact ⟨z, hz.symm, hz'.symm⟩) p q hpq
        exact ⟨r, hr.symm, hr'.symm⟩

lemma degeneracy_intersection_iff (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j)
    {X Y : V} (p q : hom (n + 1) X Y) :
    degeneracy (n + 1) i.castSucc p = degeneracy (n + 1) j.succ q ↔
      ∃ r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r := by
  refine ⟨degeneracy_intersection n i j h p q, ?_⟩
  rintro ⟨r, rfl, rfl⟩
  exact degeneracy_degeneracy n i j h r

lemma degeneracy_intersection_unique (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j)
    {X Y : V} (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i.castSucc p = degeneracy (n + 1) j.succ q) :
    ∃! r : hom n X Y, p = degeneracy n j r ∧ q = degeneracy n i r := by
  obtain ⟨r, hr, hr'⟩ := degeneracy_intersection n i j h p q hpq
  refine ⟨r, ⟨hr, hr'⟩, ?_⟩
  intro t ht
  apply degeneracy_injective n j
  exact ht.1.symm.trans hr

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorDegeneracies
