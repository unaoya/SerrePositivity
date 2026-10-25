module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionSourceResidueTensor
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootResidueSourceColimitTor
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # G7入力に相対的な根添加の実残余導来評価比較

既存Tor対称性と標準導来添加写像を使う。係数側Koszul操作との比較や
実導来完備化後CFFは別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀

/-- G7交換入力の下、実評価βに沿う実残余終域の全高次Torは零。 -/
theorem deltaRootResidueSourceEval_torVanishing_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    scalarExtensionTorVanishing β₀ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₀ c₀
      let : Subsingleton (((ModuleCat.extendScalars ψ₀).leftDerived (i + 1)).obj Mβ) :=
        deltaRootResidueSource_tor_subsingleton_of_preservesColimit D d b hpA hg v hv i (hpres i)
      have hz : IsZero (((ModuleCat.extendScalars ψ₀).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₀ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₀).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₀ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

/-- 実評価による通常係数拡大と、標準残余源作用の通常テンソルとの係数同値。 -/
def deltaRootResidueSourceEvalScalarEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    ((ModuleCat.extendScalars β₀).obj Mψ) ≃ₗ[P₀] (P₀ ⊗[L₀] Q₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- G7入力の下で、実残余終域のβに沿う導来拡大は既存raw(p,d)商の次数零対象。 -/
def deltaRootResidueSourceDerivedIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange β₀).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
  letI : Module L₀ Q₀ := Algebra.toModule
  let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₀ Mψ
    (deltaRootResidueSourceEval_torVanishing_of_preservesColimit D d b hpA hg v hv hpres) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 導来比較の順射は、標準導来添加写像と具体的な残余商比較の合成そのもの。 -/
theorem deltaRootResidueSourceDerivedIso_hom_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E₀ c₀
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₀ (MvPolynomial.C d)
    letI : Module L₀ Q₀ := Algebra.toModule
    let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (deltaDivisionSourceResidueTensorAlgEquiv E₀ (MvPolynomial.C d) c₀).toLinearEquiv
    (deltaRootResidueSourceDerivedIso_of_preservesColimit D d b hpA hg v hv hpres).hom.hom =
      (boundedAboveDerivedBaseChangeModuleAugmentation β₀).app Mψ ≫
        (boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

end SerrePositivity.BhattScholze
