module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies
public import Lean.Elab.Tactic.Omega

/-! # Compatible values on the union of all free-generator degeneracy images

The pairwise double-degeneracy equations suffice to descend prescribed values
onto the entire union. No disjointness of degeneracy images is assumed.
-/

@[expose] public section
universe v u w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues
open FreeGeneratorDegeneracies
variable {V : Type u} [Quiver.{v} V] {X Y : V} (n : ℕ) {T : Sort w}
  (value : Fin (n + 2) → hom (n + 1) X Y → T)

/-- Agreement on all double-degeneracy overlaps, in their ordered presentation. -/
def Compatible : Prop := ∀ (i j : Fin (n + 1)), i ≤ j → ∀ r : hom n X Y,
  value i.castSucc (degeneracy n j r) = value j.succ (degeneracy n i r)

lemma values_agree_ordered (h : Compatible n value) (i j : Fin (n + 2)) (hij : i < j)
    (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i p = degeneracy (n + 1) j q) : value i p = value j q := by
  let a : Fin (n + 1) := ⟨i.val, by omega⟩
  let b : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have ha : a.castSucc = i := Fin.ext rfl
  have hb : b.succ = j := Fin.ext (by dsimp [b]; omega)
  have hab : a ≤ b := by change i.val ≤ j.val - 1; omega
  rw [← ha, ← hb] at hpq ⊢
  obtain ⟨r, rfl, rfl⟩ := degeneracy_intersection n a b hab p q hpq
  exact h a b hab r

lemma values_agree (h : Compatible n value) (i j : Fin (n + 2))
    (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i p = degeneracy (n + 1) j q) : value i p = value j q := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact values_agree_ordered n value h i j hij p q hpq
  · exact congrArg (value i) (degeneracy_injective (n + 1) i hpq)
  · exact (values_agree_ordered n value h j i hji q p hpq.symm).symm

/-- The entire union of the degeneracy images in the next generator degree. -/
def Fixed (e : hom (n + 2) X Y) : Prop :=
  ∃ i : Fin (n + 2), ∃ p : hom (n + 1) X Y, e = degeneracy (n + 1) i p

lemma fixed_degeneracy (i : Fin (n + 2)) (p : hom (n + 1) X Y) :
    Fixed n (degeneracy (n + 1) i p) := ⟨i, p, rfl⟩

/-- Pick any presentation; `desc_eq` proves independence from this choice. -/
def desc (e : hom (n + 2) X Y) (he : Fixed n e) : T :=
  value he.choose he.choose_spec.choose

lemma desc_eq (h : Compatible n value) (e : hom (n + 2) X Y) (he : Fixed n e)
    (i : Fin (n + 2)) (p : hom (n + 1) X Y) (hp : e = degeneracy (n + 1) i p) :
    desc n value e he = value i p := by
  exact values_agree n value h _ _ _ _ (he.choose_spec.choose_spec.symm.trans hp)

lemma desc_degeneracy (h : Compatible n value) (i : Fin (n + 2)) (p : hom (n + 1) X Y)
    (he : Fixed n (degeneracy (n + 1) i p)) :
    desc n value (degeneracy (n + 1) i p) he = value i p :=
  desc_eq n value h _ he i p rfl

lemma desc_restriction {U : Sort w'} (ρ : T → U) (boundary : hom (n + 2) X Y → U)
    (hρ : ∀ i p, ρ (value i p) = boundary (degeneracy (n + 1) i p))
    (e : hom (n + 2) X Y) (he : Fixed n e) :
    ρ (desc n value e he) = boundary e := by
  rw [desc, hρ, ← he.choose_spec.choose_spec]

lemma desc_unique (h : Compatible n value)
    (f : (e : hom (n + 2) X Y) → Fixed n e → T)
    (hf : ∀ i p he, f (degeneracy (n + 1) i p) he = value i p)
    (e : hom (n + 2) X Y) (he : Fixed n e) : f e he = desc n value e he := by
  obtain ⟨i, p, rfl⟩ := he
  exact (hf i p _).trans (desc_degeneracy n value h i p _).symm

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues
