module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootRawCoefficientBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul

/-! # 元の係数環上での根関係raw包の実p Koszul比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
attribute [local instance] deltaRootRawCoefficientAlgebra
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "R₀" => DeltaAdjoinDivision E (p : P) a
local notation "J₀" => Ideal.span {(p : R₀)}
local notation "Q₀" => R₀ ⧸ J₀

/-- 具体的raw包のp列を、元の係数環A上の短複体として取る。 -/
def deltaRootRawRelativeModPPresentation : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk ((p : A) • 𝟙 (ModuleCat.of A R₀))
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ A J₀).toLinearMap) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change Ideal.Quotient.mk J₀ ((p : A) • r) = 0
      rw [Algebra.smul_def, map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))))

/-- 正則入力では、この実p列は元のA加群の短完全列。 -/
theorem deltaRootRawRelativeModPPresentation_shortExact
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    (deltaRootRawRelativeModPPresentation D b).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro r hr
    change Ideal.Quotient.mk J₀ r = 0 at hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    refine ⟨s, ?_⟩
    change (p : A) • s = r
    rw [Algebra.smul_def, map_natCast]
    exact hs.symm
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro r s hrs
    apply hpB
    change (p : A) • r = (p : A) • s at hrs
    have hmul (t : R₀) : (p : A) • t = (p : R₀) * t := by
      rw [Algebra.smul_def, map_natCast]
    exact (hmul r).symm.trans (hrs.trans (hmul s))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    change Function.Surjective (Ideal.Quotient.mk J₀)
    exact Ideal.Quotient.mk_surjective)

/-- 実p列を元のA加群の次数零cochain複体へ送る。 -/
def deltaRootRawRelativeModPCochainPresentation :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (deltaRootRawRelativeModPPresentation D b).map
    (CochainComplex.singleFunctor (ModuleCat A) 0)

/-- 最初のcochain射は、元のAのpによるスカラー射そのもの。 -/
theorem deltaRootRawRelativeModPCochainPresentation_f :
    (deltaRootRawRelativeModPCochainPresentation D b).f =
      smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀)) := by
  change (CochainComplex.singleFunctor (ModuleCat A) 0).map
    ((p : A) • 𝟙 (ModuleCat.of A R₀)) = _
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- A上の実p Koszul coneから、実p商の次数零対象への標準添加写像。 -/
def deltaRootRawRelativeModPKoszulAugmentation :
    CochainComplex.mappingCone (smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀))) ⟶
      cochainSingleZero (ModuleCat.of A Q₀) :=
  eqToHom (congrArg (fun f : cochainSingleZero (ModuleCat.of A R₀) ⟶
      cochainSingleZero (ModuleCat.of A R₀) ↦ CochainComplex.mappingCone f)
        (deltaRootRawRelativeModPCochainPresentation_f D b).symm) ≫
    CochainComplex.mappingCone.descShortComplex (deltaRootRawRelativeModPCochainPresentation D b)

/-- 正則入力では、元のA上の実Koszul添加写像が擬同型となる。 -/
theorem deltaRootRawRelativeModPKoszulAugmentation_quasiIso
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    QuasiIso (deltaRootRawRelativeModPKoszulAugmentation D b) := by
  have hS : (deltaRootRawRelativeModPCochainPresentation D b).ShortExact :=
    (deltaRootRawRelativeModPPresentation_shortExact D b hpB).map_of_exact
      (CochainComplex.singleFunctor (ModuleCat A) 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  dsimp only [deltaRootRawRelativeModPKoszulAugmentation]
  infer_instance

/-- 元のA→A/pで実導来還元したraw包をAへ制限すると、実R/pの次数零対象になる。 -/
def deltaRootRawRelativeDerivedModPRestrictedIso
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)))).obj ≅
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Q₀)).obj := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  have hr : IsSMulRegular A (p : A) := hpA
  have := deltaRootRawRelativeModPKoszulAugmentation_quasiIso D b hpB
  exact restrictedDerivedQuotientKoszulIso (p : A) hr X ≪≫
    (DerivedCompletion.derivedScalarConeComparison A (p : A)).app
      (cochainSingleZero (ModuleCat.of A R₀)) ≪≫
    asIso (DerivedCategory.Q.map (deltaRootRawRelativeModPKoszulAugmentation D b))

end SerrePositivity.BhattScholze
