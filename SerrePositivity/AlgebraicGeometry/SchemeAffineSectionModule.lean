module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeTensorLinear
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech

/-!
概要：構造射で束ねた切断環の加群と、実際の構造層の係数加群を比較する。
方針：構造射の切断の制限を追い、同じ元上のスカラー作用を照合する。
規約：この比較自体は開がアフィンであることを仮定しない。
使われ方：テンソル積の切断の同型を、実際の Čech 係数へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens)

/-- 構造射で定める局所のスカラーは、大域スカラーを制限した切断。 -/
theorem schemeAffineSectionAlgebra_scalar (r : R) :
    algebraMap R (schemeAffineSectionAlgebra iX U) r =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
        (schemeScalarHom X iX r) := by
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appLE ⊤ U (by simp)).hom r) = _
  have h : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appLE ⊤ U (by simp) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appTop ≫
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rfl
  exact congrArg (fun f : CommRingCat.of R ⟶ Γ(X, U) ↦ f.hom r) h

/-- 実際の構造層の係数加群と、構造射で束ねた切断環は同じ加群。 -/
def schemeAffineSectionModuleEquiv :
    ((schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars
      (schemeScalarHom X iX)).obj (op U)) ≃ₗ[R] schemeAffineSectionAlgebra iX U :=
  { AddEquiv.refl Γ(X, U) with
    map_smul' := by
      intro r x
      change @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance
          ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
            (schemeScalarHom X iX r)) x =
        @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance
          (algebraMap R (schemeAffineSectionAlgebra iX U) r) x
      exact congrArg (fun a : Γ(X, U) ↦
          @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance a x)
        (schemeAffineSectionAlgebra_scalar iX U r).symm }

end SerrePositivity.AlgebraicGeometry
