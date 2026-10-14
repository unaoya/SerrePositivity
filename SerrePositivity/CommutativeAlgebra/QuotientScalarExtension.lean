module
public import SerrePositivity.CommutativeAlgebra.AdicFaithfulDescentAlgebra
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Scalar extension to a quotient ring and ordinary residue modules -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
variable {R : Type u} [CommRing R]

/-- Ordinary reduction is a functor to modules over the quotient ring. -/
def quotientModuleFunctor (I : Ideal R) : ModuleCat.{u} R ⥤ ModuleCat.{u} (R ⧸ I) where
  obj M := ModuleCat.of (R ⧸ I) (AdicReduction I M)
  map f := ModuleCat.ofHom (adicReductionMap I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The usual quotient-tensor comparison retains the quotient-ring scalar action. -/
def quotientScalarExtensionEquiv (I : Ideal R) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M) ≃ₗ[R ⧸ I] AdicReduction I M :=
  let eA : ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) (R ⧸ I))) ≃ₗ[R] R ⧸ I :=
    { toFun := fun a => a
      invFun := fun a => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rfl }
  let e := TensorProduct.congr eA (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul M I
  have he (r : R) (m : M) : e (Ideal.Quotient.mk I r ⊗ₜ[R, Ideal.Quotient.mk I] m) =
      (I • (⊤ : Submodule R M)).mkQ (r • m) := by
    simp [e, eA, TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  { e.toAddEquiv with
    map_smul' := by
      intro a x
      change e (a • x) = a • e x
      induction x using TensorProduct.inductionOn with
      | tmul b m =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
        erw [ModuleCat.ExtendScalars.smul_tmul, ← map_mul, he, he]
        change (I • (⊤ : Submodule R M)).mkQ ((r * s) • m) =
          (I • (⊤ : Submodule R M)).mkQ (r • (s • m))
        rw [mul_smul]
      | add x y hx hy => simp_all only [smul_add, map_add] }

@[simp]
lemma quotientScalarExtensionEquiv_mk_tmul (I : Ideal R) (M : ModuleCat.{u} R) (r : R) (m : M) :
    quotientScalarExtensionEquiv I M (Ideal.Quotient.mk I r ⊗ₜ[R, Ideal.Quotient.mk I] m) =
      (I • (⊤ : Submodule R M)).mkQ (r • m) :=
  by simp [quotientScalarExtensionEquiv, TensorProduct.quotTensorEquivQuotSMul_mk_tmul]

@[simp]
lemma quotientScalarExtensionEquiv_one_tmul (I : Ideal R) (M : ModuleCat.{u} R) (m : M) :
    quotientScalarExtensionEquiv I M ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] m) =
      (I • (⊤ : Submodule R M)).mkQ m :=
  by simpa only [map_one, one_smul] using quotientScalarExtensionEquiv_mk_tmul I M 1 m

/-- Scalar extension and reduction agree naturally, including their standard quotient maps. -/
def quotientScalarExtensionIso (I : Ideal R) :
    ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅ quotientModuleFunctor I := by
  refine NatIso.ofComponents (fun M => (quotientScalarExtensionEquiv I M).toModuleIso) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change quotientScalarExtensionEquiv I N
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f x) =
    adicReductionMap I f.hom (quotientScalarExtensionEquiv I M x)
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [ModuleCat.ExtendScalars.map_tmul, quotientScalarExtensionEquiv_mk_tmul,
      quotientScalarExtensionEquiv_mk_tmul, adicReductionMap_mkQ]
    rw [f.hom.map_smul]
  | add x y hx hy => simp_all only [map_add]

attribute [local instance] adicQuotientAlgebra

/-- For an algebra the module reduction is the actual quotient ring by the extended ideal. -/
def quotientAlgebraScalarExtensionEquiv (I : Ideal R) (S : Type u)
    [CommRing S] [Algebra R S] :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of R S)) ≃ₗ[R ⧸ I]
      S ⧸ I.map (algebraMap R S) :=
  quotientScalarExtensionEquiv I (ModuleCat.of R S) ≪≫ₗ adicReductionEquivAlgebraQuotient I S

@[simp]
lemma quotientAlgebraScalarExtensionEquiv_one_tmul (I : Ideal R) (S : Type u)
    [CommRing S] [Algebra R S] (s : S) :
    quotientAlgebraScalarExtensionEquiv I S ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] s) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) s := by
  change (adicReductionEquivAlgebraQuotient I S)
    (quotientScalarExtensionEquiv I (ModuleCat.of R S) _) = _
  erw [quotientScalarExtensionEquiv_one_tmul, adicReductionEquivAlgebraQuotient_mkQ]

/-- The algebra quotient computation is natural in the algebra map. -/
lemma quotientAlgebraScalarExtensionEquiv_naturality (I : Ideal R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (ModuleCat.ofHom f.toLinearMap) ≫
        (quotientAlgebraScalarExtensionEquiv I T).toModuleIso.hom =
      (quotientAlgebraScalarExtensionEquiv I S).toModuleIso.hom ≫
        ModuleCat.ofHom (adicAlgebraReductionMap I f) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  change quotientAlgebraScalarExtensionEquiv I T
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (ModuleCat.ofHom f.toLinearMap)
        ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] s)) =
    adicAlgebraReductionMap I f (quotientAlgebraScalarExtensionEquiv I S
      ((1 : R ⧸ I) ⊗ₜ[R, Ideal.Quotient.mk I] s))
  rw [ModuleCat.ExtendScalars.map_tmul, quotientAlgebraScalarExtensionEquiv_one_tmul,
    quotientAlgebraScalarExtensionEquiv_one_tmul, adicAlgebraReductionMap_mk]
  rfl

end SerrePositivity
