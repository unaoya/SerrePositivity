module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceRegularGhost
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits

/-! # G7による具体的根添加源の逐次Tor交換入力の解消 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
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

/-- G7を実際の有限評価源図式と標準剰余係数射へ適用する。 -/
theorem deltaRootSource_preservesSequentialTor (i : ℕ) :
    PreservesColimit F₀ ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)) := by
  let : PreservesColimitsOfShape ℕ
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)) :=
    torAlg_preservesSequentialColimits (R := L₀) (S := L₀ ⧸ J₀) ψ₀ (i + 1)
  infer_instance

include hn in
/-- G4・G7を供給し、外部交換入力なしでG10標準還元の次数消滅を得る。 -/
theorem deltaRootSourceCanonicalPowerResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidue_homology_isZero_of_p_regular D d b n hn hpA hd v hv
    (fun i => deltaRootSource_preservesSequentialTor D d b i) i hi

include hn in
/-- G4・G7を供給し、外部交換入力なしでG10標準還元H0の忠実平坦性を得る。 -/
theorem deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) :=
  deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_p_regular D d b n hn hpA hd v hv
    (fun i => deltaRootSource_preservesSequentialTor D d b i)

end SerrePositivity.BhattScholze
