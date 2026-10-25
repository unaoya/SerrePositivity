module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceCanonicalPowerResidue
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-! # G4による具体的根添加源のghost単射入力

G10の標準還元の入口から独立のghost単射仮定を除く。
G7の具体的colimit交換入力は明示して保持する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ

/-- 元の係数環のp正則性から、実自由δ源上のghost単射をG4で供給する。 -/
theorem deltaRootSource_ghostMap_injective
    (hpA : Function.Injective (fun x : A => (p : A) * x)) :
    Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀) := by
  apply witt_ghostMap_injective_of_mul_prime_injective
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)

variable [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk J₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))))) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀

include hn in
/-- G7入力の下、ghost仮定なしでG10の標準還元の次数消滅を得る。 -/
theorem deltaRootSourceCanonicalPowerResidue_homology_isZero_of_p_regular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidue_homology_isZero_of_preservesColimit
    D d b n hn hpA hd (deltaRootSource_ghostMap_injective (σ := σ) hpA) v hv hpres i hi

include hn in
/-- G7入力の下、ghost仮定なしでG10の標準還元H0の忠実平坦性を得る。 -/
theorem deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_p_regular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_preservesColimit
    D d b n hn hpA hd (deltaRootSource_ghostMap_injective (σ := σ) hpA) v hv hpres

end SerrePositivity.BhattScholze
