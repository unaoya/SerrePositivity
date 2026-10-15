module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Degree
public import Mathlib.Order.SuccPred.Nat

/-! # Coherent diagrams on all finite degree restrictions

Successive restriction isomorphisms determine comparison maps between any
two stages. Their cocycle law will permit gluing the diagrams without
replacing coherent extensions by unrelated objectwise choices.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) (C : Type u') [Category.{v'} C]

structure DiagramTower where
  stage : (n : ℕ) → Lower r n ⥤ C
  step (n : ℕ) : lowerMap r (Nat.le_succ n) ⋙ stage (n + 1) ≅ stage n

namespace DiagramTower
variable {r C} (T : DiagramTower r C)

def comparison : {n m : ℕ} → (h : n ≤ m) → lowerMap r h ⋙ T.stage m ≅ T.stage n
  | n, 0, h => by
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    exact Iso.refl _
  | n, m + 1, h => by
    by_cases hnm : n ≤ m
    · exact Functor.isoWhiskerLeft (lowerMap r hnm) (T.step m) ≪≫ comparison hnm
    · have hn : n = m + 1 := le_antisymm h (Nat.lt_of_not_ge hnm)
      subst n
      exact Iso.refl _

@[simp]
lemma comparison_refl (n : ℕ) : T.comparison (le_refl n) = Iso.refl (T.stage n) := by
  cases n <;> simp only [comparison, dite_eq_right (Nat.not_succ_le_self _)] <;> rfl

lemma comparison_succ {n m : ℕ} (h : n ≤ m) :
    T.comparison (h.trans (Nat.le_succ m)) =
      Functor.isoWhiskerLeft (lowerMap r h) (T.step m) ≪≫ T.comparison h := by
  simp only [comparison, dite_eq_left h]

abbrev comparisonAt {n m : ℕ} (h : n ≤ m) (j : J) (hj : r.deg j < n) :
    (T.stage m).obj ⟨j, lt_of_lt_of_le hj h⟩ ≅ (T.stage n).obj ⟨j, hj⟩ :=
  (T.comparison h).app ⟨j, hj⟩

@[simp]
lemma comparisonAt_refl (n : ℕ) (j : J) (hj : r.deg j < n) :
    T.comparisonAt (le_refl n) j hj = Iso.refl _ := by
  unfold comparisonAt
  rw [comparison_refl]
  rfl

lemma comparisonAt_succ {n m : ℕ} (h : n ≤ m) (j : J) (hj : r.deg j < n) :
    T.comparisonAt (h.trans (Nat.le_succ m)) j hj =
      (T.step m).app ⟨j, lt_of_lt_of_le hj h⟩ ≪≫ T.comparisonAt h j hj := by
  unfold comparisonAt
  rw [comparison_succ]
  rfl

@[reassoc]
lemma comparisonAt_naturality {n m : ℕ} (h : n ≤ m) {j k : J}
    (hj : r.deg j < n) (hk : r.deg k < n) (f : j ⟶ k) :
    (T.stage m).map (ObjectProperty.homMk f) ≫ (T.comparisonAt h k hk).hom =
      (T.comparisonAt h j hj).hom ≫ (T.stage n).map (ObjectProperty.homMk f) :=
  by
    have hh := (T.comparison h).hom.naturality
      (ObjectProperty.homMk f : (⟨j, hj⟩ : Lower r n) ⟶ ⟨k, hk⟩)
    exact hh

lemma comparisonAt_trans {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (j : J) (hj : r.deg j < n) :
    T.comparisonAt (hnm.trans hmk) j hj =
      T.comparisonAt hmk j (lt_of_lt_of_le hj hnm) ≪≫ T.comparisonAt hnm j hj := by
  induction k, hmk using Nat.le_induction with
  | base => simp only [comparisonAt_refl, Iso.refl_trans]
  | succ k hmk ih =>
    rw [T.comparisonAt_succ (hnm.trans hmk), T.comparisonAt_succ hmk, ih]
    exact (Iso.trans_assoc _ _ _).symm

end DiagramTower
end SerrePositivity.Reedy
