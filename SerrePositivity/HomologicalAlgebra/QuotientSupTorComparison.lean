module

public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Tor comparison for successive ordinary ideal quotients -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The usual double quotient equivalence is linear for the original restricted R-action. -/
def doubleQuotientModuleIso {R : Type u} [CommRing R] (I J : Ideal R) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))) ≅
        ModuleCat.of R (R ⧸ (I ⊔ J)) := by
  let S := (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
  let e := DoubleQuot.quotQuotEquivQuotSup I J
  exact (show ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)))) ≃ₗ[R]
      (R ⧸ (I ⊔ J)) from
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun r x => by
        change e (algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I r) * (show S from x)) =
          Ideal.Quotient.mk (I ⊔ J) r * e x
        rw [map_mul]
        rfl }).toModuleIso

/-- Compute Tor for a sum of ideals by successive quotienting, when the first step is acyclic. -/
def quotientSupTorAcyclicBaseChangeIso {R : Type u} [CommRing R] (I J : Ideal R)
    (M : ModuleCat.{u} R) (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M) (i : ℕ) :
    ((Tor (ModuleCat R) i).obj (ModuleCat.of R (R ⧸ (I ⊔ J)))).obj M ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (((Tor (ModuleCat (R ⧸ I)) i).obj
          (ModuleCat.of (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)))).obj
          ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M)) :=
  (((Tor (ModuleCat R) i).mapIso (doubleQuotientModuleIso I J)).app M).symm ≪≫
    torAcyclicBaseChangeIso (Ideal.Quotient.mk I) M hM _ i
end SerrePositivity
