module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionPDCompletionMap
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.IteratedPDH0Reflection

/-! # 実δ完全化逐次H0から正確なPD係数加群への比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ) (ModuleCat.of C H)
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d

/-- 実PD H0の制限加群は、元の標準合成係数射に沿う加群と同型。 -/
def deltaAlgebraPerfectionPDNativeModuleIso :
    letI := pdCompletionCommRing C p (κ d)
    M ≅ baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  let := pdCompletionAlgebra C p (κ d)
  let Mc : ModuleCat.{u} A := M
  let Nc : ModuleCat.{u} A := baseChangeScalarModule t
  let f : Mc →ₗ[A] Nc :=
    { toFun := (id : H → H)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change H at x
        change (κ a) • x = s (κ a) * x
        exact Algebra.smul_def (κ a) x }
  let g : Nc →ₗ[A] Mc :=
    { toFun := (id : H → H)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change H at x
        change s (κ a) * x = (κ a) • x
        exact (Algebra.smul_def (κ a) x).symm }
  let e : Mc ≃ₗ[A] Nc := LinearEquiv.ofLinearMap f g (by ext x; rfl) (by ext x; rfl)
  exact e.toModuleIso

/-- 元の実δ完全化逐次H0は、C上の実PD H0の同じ制限加群と同型。 -/
def deltaAlgebraPerfectionPDNativeH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj ≅ M :=
  deltaAlgebraPerfectionCompletionRestrictionH0Iso E j d ≪≫
    (ModuleCat.restrictScalars κ).mapIso
      (iteratedPDH0LinearEquiv C (κ (p : A)) (κ d) p (map_natCast κ p)).toModuleIso

/-- 元の実δ完全化逐次H0を、標準合成係数射A→C→PDの加群と同定する。 -/
def deltaAlgebraPerfectionPDH0Iso :
    letI := pdCompletionCommRing C p (κ d)
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj ≅
      baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  exact deltaAlgebraPerfectionPDNativeH0Iso E j d ≪≫ deltaAlgebraPerfectionPDNativeModuleIso E j d

end SerrePositivity.BhattScholze
