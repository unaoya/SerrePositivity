module

public import SerrePositivity.EInfinity.BarrattEccles.EquivariantBasis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Barratt–Eccles の arity の正則表現

## 概要
Berger–Fresse §1.1 の非退化単体の基底から、各 arity の次数成分の自由表現を得る。

## 方針
先頭置換を単位に正規化し、残りの置換を逆元で左正則表現の添字にする。

## 規約
置換作用を対角余不変で使う左作用に直す。

## 使われ方
セル代数の Schur 表示の次数ごとの基底。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory DifferentialGraded

variable (A : Type u) [CommRing A]

/-- Each normalized degree of an arity has its left symmetric-group representation. -/
def arityDegreeRepresentation (n q : ℕ) :
    Representation A (ULift.{u} (Equiv.Perm (Fin n))) ((complex A n).X (-(q : ℤ))) where
  toFun σ := ((complexRightAction A n σ.down⁻¹).f (-(q : ℤ))).hom
  map_one' := by
    change ((complexRightAction A n (1 : Equiv.Perm (Fin n))⁻¹).f (-(q : ℤ))).hom = _
    rw [inv_one, complexRightAction_one]
    rfl
  map_mul' σ τ := by
    change ((complexRightAction A n (σ.down * τ.down)⁻¹).f (-(q : ℤ))).hom = _
    rw [mul_inv_rev, complexRightAction_mul]
    rfl

/-- The free representation on the based nondegenerate simplices. -/
def arityDegreeFreeMap (n q : ℕ) :
    Rep.free A (ULift.{u} (Equiv.Perm (Fin n))) (ULift.{u} (BasedNondegenerate n q)) ⟶
      Rep.of (arityDegreeRepresentation A n q) :=
  Rep.freeLift A _ _ (fun x => equivariantBasis A n q (x, 1))

/-- The free representation map is the basis equivalence with the group coordinate inverted. -/
def arityDegreeFreeLinearEquiv (n q : ℕ) :
    (ULift.{u} (BasedNondegenerate n q) →₀ MonoidAlgebra A
      (ULift.{u} (Equiv.Perm (Fin n)))) ≃ₗ[A] ((complex A n).X (-(q : ℤ))) :=
  (Finsupp.basis (fun _ => MonoidAlgebra.basis _ A)).equiv (equivariantBasis A n q)
    { toFun := fun x => (x.1, x.2.down⁻¹)
      invFun := fun x => ⟨x.1, ULift.up x.2⁻¹⟩
      left_inv := by rintro ⟨x, ⟨σ⟩⟩; simp
      right_inv := by rintro ⟨x, σ⟩; simp }

lemma arityDegreeFreeMap_eq (n q : ℕ) :
    (arityDegreeFreeMap A n q).hom.toLinearMap =
      (arityDegreeFreeLinearEquiv A n q).toLinearMap := by
  apply (Finsupp.basis (fun _ => MonoidAlgebra.basis _ A)).ext
  rintro ⟨x, σ⟩
  rw [LinearEquiv.coe_coe, arityDegreeFreeLinearEquiv, Module.Basis.equiv_apply]
  simp only [Finsupp.coe_basis, MonoidAlgebra.basis_apply]
  change Representation.freeLift (arityDegreeRepresentation A n q)
    (fun x => equivariantBasis A n q (x, 1))
    (Finsupp.single x (MonoidAlgebra.single σ 1)) =
      equivariantBasis A n q (x, σ.down⁻¹)
  rw [Representation.freeLift_single_single, one_smul]
  change ((complexRightAction A n σ.down⁻¹).f (-(q : ℤ)))
    (equivariantBasis A n q (x, 1)) = _
  rw [equivariantBasis_rightAction, one_mul]

/-- The arity representation is free, with the specified based generators. -/
def arityDegreeFreeIso (n q : ℕ) :
    Rep.free A (ULift.{u} (Equiv.Perm (Fin n))) (ULift.{u} (BasedNondegenerate n q)) ≅
      Rep.of (arityDegreeRepresentation A n q) := by
  let f := arityDegreeFreeMap A n q
  let F := forget (Rep A (ULift.{u} (Equiv.Perm (Fin n))))
  haveI : IsIso (F.map f) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective f.hom.toLinearMap
    rw [show f.hom.toLinearMap = _ from arityDegreeFreeMap_eq A n q]
    exact (arityDegreeFreeLinearEquiv A n q).bijective
  letI : IsIso f := isIso_of_reflects_iso f F
  exact asIso f

/-- Coinvariants of the diagonal action are indexed by the based nondegenerate simplices. -/
def arityDegreeCoinvariantsTensorEquiv (n q : ℕ)
    (V : Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) :
    (V ⊗ Rep.of (arityDegreeRepresentation A n q)).ρ.Coinvariants ≃ₗ[A]
      (ULift.{u} (BasedNondegenerate n q) →₀ V) := by
  classical
  exact ((((Rep.coinvariantsTensor A _).obj V).mapIso
    (arityDegreeFreeIso A n q)).symm.toLinearEquiv).trans
    (Rep.coinvariantsTensorFreeLEquiv V (ULift.{u} (BasedNondegenerate n q)))

/-- The regular arity decomposition transports any basis of the other tensor factor. -/
def arityDegreeCoinvariantsTensorBasis (n q : ℕ)
    (V : Rep.{u} A (ULift.{u} (Equiv.Perm (Fin n)))) {I : Type u}
    (b : Module.Basis I A V) :
    Module.Basis (ULift.{u} (BasedNondegenerate n q) × I) A
      (V ⊗ Rep.of (arityDegreeRepresentation A n q)).ρ.Coinvariants := by
  classical
  exact ((Finsupp.basis (fun _ : ULift.{u} (BasedNondegenerate n q) => b)).map
    (arityDegreeCoinvariantsTensorEquiv A n q V).symm).reindex
      (Equiv.sigmaEquivProd _ _)

end SerrePositivity.EInfinity.BarrattEccles
