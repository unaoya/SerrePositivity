module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineSectionModule

/-!
概要：指定した大域スカラーから作る構造射と、元の構造層の係数加群を比較する。
方針：構造射から戻したスカラーが元と一致することを使う。
規約：構造層の切断環自体を置き換えない。
使われ方：Proj の元の大域スカラーで、実際の閉厚化の切断の商を扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] (X : Scheme.{u}) (φ : R →+* Γ(X, ⊤)) (U : X.Opens)

/-- 指定した大域スカラーと、それが定める構造射で束ねた切断代数の加群の同型。 -/
def schemeScalarMorphismSectionModuleEquiv :
    ((schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φ).obj (op U)) ≃ₗ[R]
      schemeAffineSectionAlgebra (schemeScalarMorphism X φ) U :=
  { AddEquiv.refl Γ(X, U) with
    map_smul' := by
      intro r x
      have hs : algebraMap R (schemeAffineSectionAlgebra (schemeScalarMorphism X φ) U) r =
          (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (φ r) := by
        simpa only [schemeScalarHom_scalarMorphism] using
          schemeAffineSectionAlgebra_scalar (schemeScalarMorphism X φ) U r
      change @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance
          ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (φ r)) x =
        @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance
          (algebraMap R (schemeAffineSectionAlgebra (schemeScalarMorphism X φ) U) r) x
      exact congrArg (fun a : Γ(X, U) ↦
        @HMul.hMul Γ(X, U) Γ(X, U) Γ(X, U) inferInstance a x) hs.symm }

/-- スカラーを指定した切断の比較は、元そのものを変えない。 -/
theorem schemeScalarMorphismSectionModuleEquiv_apply
    (x : (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φ).obj (op U)) :
    schemeScalarMorphismSectionModuleEquiv X φ U x = x := rfl

end SerrePositivity.AlgebraicGeometry
