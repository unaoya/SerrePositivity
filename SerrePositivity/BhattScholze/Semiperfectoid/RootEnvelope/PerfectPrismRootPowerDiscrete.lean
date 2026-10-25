module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.BoundedSupport.DeltaRootBoundedSupportTorInputs
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.BoundedSupport.PerfectPrismRootBoundedSupportPowerInputs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticPowerDerivedFlat
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticGeneratorPowerModP
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootSourceGeneratorPowerComplete
public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel

/-! # 完全prism上の任意根族の実生成元冪商の離散性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "B₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := B₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "r₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk I₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
variable (n : ℕ) (hn : 0 < n)
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ
include hP hn

/-- 元の実逐次源の生成元冪商は離散で、そのH0は有界p冪ねじれを持つ。 -/
theorem perfectPrismRootPower_pure_bounded_torsion :
    (Zₙ).obj.IsGE 0 ∧ (Zₙ).obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} Tₙ) 0).obj (Zₙ).obj,
          (p : Tₙ) ^ k • z = 0 → (p : Tₙ) ^ N • z = 0 := by
  obtain ⟨hc, ht, hz, hf⟩ := perfectPrismRootBoundedSupportPower_G9_inputs P hP b n hn
    (deltaRootBoundedSupport_preservesColimit D d b)
  exact DerivedCompletion.derived_pure_bounded_torsion_of_complete_flat_reduction
    (p : Tₙ) Zₙ hz hf ⟨n, ht⟩ hc

/-- 同じ具体的実冪商の非零次数のホモロジーは零。 -/
theorem perfectPrismRootPower_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Tₙ) i).obj (Zₙ).obj) := by
  obtain ⟨hGE, hLE, _⟩ := perfectPrismRootPower_pure_bounded_torsion P hP b n hn
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

end SerrePositivity.BhattScholze
