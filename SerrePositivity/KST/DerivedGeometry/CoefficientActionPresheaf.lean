module

public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorSectionAction

/-!
概要：H 作用を持つ構造層加群からテンソル係数環上の加群前層を構成する。
方針：各開のテンソル係数作用を、H 作用の自然性と局所スカラーの半線形性で貼り合わせる。
規約：基礎加法群の前層を変更しない。
使われ方：KST D4・T1′、Toën §3.2 の係数加群層化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：切断のテンソル係数作用は前層の制限に関して半線形。
方針：純テンソルで二つの作用の自然性を使い、テンソルの和について帰納する。
規約：同じ構造層加群の制限写像を保持する。
使われ方：KST D4・T1′、Toën §3.2 の係数加群前層。
-/
theorem coefficientTensorSectionEnd_restrict (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (t : (coefficientTensorPresheaf H a).obj U) (m : M.val.obj U) :
    M.val.map i (coefficientTensorSectionEnd H a M ρ hρ U.unop t m) =
      coefficientTensorSectionEnd H a M ρ hρ V.unop
        ((coefficientTensorPresheaf H a).map i t) (M.val.map i m) := by
  let (W : Opens X) := sectionAlgebra a W
  let (W : Opens X) := structureSectionModule M W
  change H ⊗[A] Γ(X, U.unop) at t
  induction t using TensorProduct.inductionOn with
  | tmul h r =>
    change M.val.map i (coefficientTensorSectionEnd H a M ρ hρ U.unop (h ⊗ₜ[A] r) m) =
      coefficientTensorSectionEnd H a M ρ hρ V.unop
        (h ⊗ₜ[A] (X.presheaf.map i r)) (M.val.map i m)
    rw [coefficientTensorSectionEnd_tmul_apply, coefficientTensorSectionEnd_tmul_apply,
      M.val.map_smul]
    exact congrArg (fun z : M.val.obj V => (X.presheaf.map i r) • z)
      (PresheafOfModules.naturality_apply (ρ h).asHom.val i m).symm
  | add t s ht hs =>
    simp only [map_add, LinearMap.add_apply, ht, hs]

/--
概要：H 作用を持つ構造層加群のテンソル係数前層。
方針：切断ごとのテンソル加群構造と半線形な制限の証明を束ねる。
規約：基礎加法群の前層とその制限を変更しない。
使われ方：KST D4・T1′、Toën §3.2 の層化前の係数作用。
-/
def coefficientActionPresheaf (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r) :
    PresheafOfModules.{u} (coefficientTensorPresheaf H a) := by
  letI (U : (Opens X)ᵒᵖ) :
      Module ((coefficientTensorPresheaf H a).obj U) (M.val.presheaf.obj U) :=
    coefficientTensorSectionModule H a M ρ hρ U.unop
  exact PresheafOfModules.ofPresheaf M.val.presheaf
    (fun {_ _} i r m => coefficientTensorSectionEnd_restrict H a M ρ hρ i r m)

/--
概要：構成したテンソル係数前層の基礎加法群の前層は元のもの。
方針：既存の前層からの加群構成の定義を読む。
規約：同型だけでなく同じ前層を保持する。
使われ方：KST D4、Toën §3.2 の基礎層を保持した層化。
-/
theorem coefficientActionPresheaf_underlying (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r) :
    (coefficientActionPresheaf H a M ρ hρ).presheaf = M.val.presheaf := rfl

end SerrePositivity.KST.DerivedGeometry
