module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RetractChainFamily
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Actual finite products of the simplicial interval and their coordinate faces -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.ParameterCube
open RetractChainFamily

def obj (n : ℕ) : SSet.{v} where
  obj m := Fin n → interval.obj m
  map f := ↾fun x i => interval.map f (x i)
  map_id m := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact types_congr_hom (interval.map_id m) (x i)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact types_congr_hom (interval.map_comp f g) (x i)

def coordinate {n : ℕ} (i : Fin n) : obj n ⟶ interval where
  app _ := ↾fun x => x i
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def endpoint (ε : Bool) (T : SSet.{v}) : T ⟶ interval := if ε then one T else zero T

def face {n : ℕ} (j : Fin (n + 1)) (ε : Bool) : obj n ⟶ obj (n + 1) where
  app m := ↾fun x => Fin.insertNth j ((endpoint ε (obj n)).app m x) x
  naturality {m m'} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    funext k
    induction k using j.succAboveCases with
    | x =>
      change Fin.insertNth (α := fun _ => interval.obj m') j _ _ j =
        interval.map θ (Fin.insertNth (α := fun _ => interval.obj m) j _ _ j)
      simp only [Fin.insertNth_apply_same]
      convert types_congr_hom ((endpoint ε (obj n)).naturality θ) x using 1 <;> rfl
    | p k =>
      change Fin.insertNth (α := fun _ => interval.obj m') j _ _ (j.succAbove k) =
        interval.map θ (Fin.insertNth (α := fun _ => interval.obj m) j _ _ (j.succAbove k))
      simp only [Fin.insertNth_apply_succAbove]
      rfl

lemma face_coordinate_same {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    face j ε ≫ coordinate j = endpoint ε (obj n) := by
  ext m x
  change Fin.insertNth (α := fun _ => interval.obj m) j _ x j = _
  exact Fin.insertNth_apply_same _ _ _

lemma face_coordinate_other {n : ℕ} (j : Fin (n + 1)) (ε : Bool) (i : Fin n) :
    face j ε ≫ coordinate (j.succAbove i) = coordinate i := by
  ext m x
  change Fin.insertNth (α := fun _ => interval.obj m) j _ x (j.succAbove i) = _
  exact Fin.insertNth_apply_succAbove _ _ _ _

def coordinateOrZero (n k : ℕ) : obj n ⟶ interval :=
  if h : k < n then coordinate ⟨k, h⟩ else zero (obj n)

lemma coordinateOrZero_lt {n k : ℕ} (h : k < n) :
    coordinateOrZero n k = coordinate ⟨k, h⟩ := dite_eq_left h

lemma coordinateOrZero_last (n : ℕ) : coordinateOrZero n n = zero (obj n) :=
  dite_eq_right (Nat.lt_irrefl n)

end SerrePositivity.SimplicialModel.ParameterCube
