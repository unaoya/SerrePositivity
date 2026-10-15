module

public import SerrePositivity.BhattScholze.DeltaPDivisionSourcePrincipal
public import SerrePositivity.BhattScholze.DeltaPDivisionSourceColimitTor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # G7交換入力を明示した実自由δ射の導来分冪比較

PreservesColimitの仮定自体はここでは証明しない。G7の解消や無条件のB4完成とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D (p : A)
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "F₀" => deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 具体的なα:x↦pzとβ:x↦φ(y)の二つのTorを、既存の実導来対称性で比較する。 -/
def deltaPDivisionSourceTorSwapIso (n : ℕ) :
    (((Tor (ModuleCat.{u} P₀) n).obj Mβ).obj Mα) ≅
      (((Tor (ModuleCat.{u} P₀) n).obj Mα).obj Mβ) :=
  by
    let X : DerivedCategory.Minus (ModuleCat.{u} P₀) := boundedAboveDerivedSingleFunctor.obj Mβ
    let Y : DerivedCategory.Minus (ModuleCat.{u} P₀) := boundedAboveDerivedSingleFunctor.obj Mα
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) (-(n : ℤ))
    let es := boundedAboveDerivedTensorSymmetry (R := P₀) X Y
    let e₁ := ((boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mβ n).app Mα).symm
    let e₂ := H.mapIso (DerivedCategory.Minus.ι.mapIso es)
    let e₃ := (boundedAboveDerivedTensorModuleTorNatIso (R := P₀) Mα n).app Mβ
    exact e₁ ≪≫ e₂ ≪≫ e₃

/-- G7交換入力の下、実評価βに沿う終域Pの全高次Torは零。 -/
theorem deltaPDivisionSourceEval_torVanishing_of_preservesColimit
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    scalarExtensionTorVanishing β₀ Mα := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvalAlgebra (σ := σ) D y
      let : Subsingleton (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        deltaPDivisionSource_tor_subsingleton_of_preservesColimit D y hpA hg v hv hy i (hpres i)
      have hz : IsZero (((ModuleCat.extendScalars α₀).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso α₀ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars α₀).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso α₀ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact (deltaPDivisionSourceTorSwapIso D y (i + 1)).isZero_iff.mpr hzT

/-- 実評価βによる通常係数拡大は、指定した二つの作用による通常テンソルそのもの。 -/
def deltaPDivisionSourceEvalScalarEquiv :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ((ModuleCat.extendScalars β₀).obj Mα) ≃ₗ[A] (A ⊗[P₀] P₀) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  exact
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- G7交換入力の下で、実自由δ射の導来拡大が具体的表示環の次数零対象となる。 -/
def deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (PrincipalDPPresentation A y)) := by
  letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
  letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
  letI : Module P₀ P₀ := Algebra.toModule
  let e := (deltaPDivisionSourceEvalScalarEquiv (σ := σ) D y).trans
    (deltaPDivisionSourcePrincipalAlgEquiv D y hA hpA hg v hv hy).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mα
      (deltaPDivisionSourceEval_torVanishing_of_preservesColimit D y hpA hg v hv hy hpres) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- G7交換入力の下、実自由δ導来拡大をA→A/pで実導来還元する具体的比較。 -/
def deltaPDivisionSourceDerivedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      (deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 同じG7交換入力の下、実自由δ導来拡大のA上の実完備化のp還元を具体的表示環へ同定する。 -/
def deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- G7交換入力付きの実自由δ導来比較は、標準A導来完備化単位と両立する。 -/
theorem deltaPDivisionSourceDerivedCompletedModPIso_unit_of_preservesColimit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p P₀ → ℕ → P₀))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} α₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          ((boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mα))) ≫
      (deltaPDivisionSourceDerivedCompletedModPIso_of_preservesColimit
        D y hA hpA hg v hv hy hpres).hom =
        (deltaPDivisionSourceDerivedModPIso_of_preservesColimit
          D y hA hpA hg v hv hy hpres).hom := by
  let e := deltaPDivisionSourceDerivedPrincipalIso_of_preservesColimit
    D y hA hpA hg v hv hy hpres
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze
