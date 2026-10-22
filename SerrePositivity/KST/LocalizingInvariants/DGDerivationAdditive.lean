module

public import SerrePositivity.KST.LocalizingInvariants.DGDerivationSection

/-!
概要：同じ実 dg 双加群に値を持つ derivation の加算・負号・差を構成する。
方針：underlying chain map の演算が単位零性と Leibniz 則を保つことを示す。
規約：係数の底作用を固定する。使われ方：class 射と相対経路の補正。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory Preadditive MonoidalPreadditive
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.Derivation
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M : Bimod A A}

def zero : Derivation A M where
  hom := 0
  unit := by simp
  leibniz := by simp

def add (d e : Derivation A M) : Derivation A M where
  hom := d.hom + e.hom
  unit := by rw [comp_add, d.unit, e.unit, add_zero]
  leibniz := by
    simp only [comp_add, whiskerLeft_add, add_whiskerRight, add_comp, d.leibniz, e.leibniz]
    abel

def neg (d : Derivation A M) : Derivation A M where
  hom := -d.hom
  unit := by rw [comp_neg, d.unit, neg_zero]
  leibniz := by
    have hl : A.X ◁ (-d.hom) = -(A.X ◁ d.hom) := (tensorLeft A.X).map_neg
    have hr : (-d.hom) ▷ A.X = -(d.hom ▷ A.X) := (tensorRight A.X).map_neg
    simp only [comp_neg, hl, hr, neg_comp, d.leibniz, neg_add]

def sub (d e : Derivation A M) : Derivation A M := add d (neg e)

lemma add_hom (d e : Derivation A M) : (add d e).hom = d.hom + e.hom := rfl
lemma neg_hom (d : Derivation A M) : (neg d).hom = -d.hom := rfl
lemma sub_hom (d e : Derivation A M) : (sub d e).hom = d.hom - e.hom := by
  exact (sub_eq_add_neg d.hom e.hom).symm

lemma add_sub_cancel (d e : Derivation A M) : add (sub d e) e = d := by
  apply Derivation.ext
  change d.hom + -e.hom + e.hom = d.hom
  abel

lemma sub_self (d : Derivation A M) : sub d d = zero := by
  apply Derivation.ext
  change d.hom + -d.hom = 0
  abel

lemma sub_add_cancel (d e : Derivation A M) : add (sub d d) e = e := by
  apply Derivation.ext
  change d.hom + -d.hom + e.hom = e.hom
  abel

end SerrePositivity.KST.LocalizingInvariants.SquareZero.Derivation
