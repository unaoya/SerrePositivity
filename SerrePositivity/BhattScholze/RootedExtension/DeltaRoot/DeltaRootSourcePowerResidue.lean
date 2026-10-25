module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceIteratedCompletionResidue
public import SerrePositivity.BhattScholze.Prism.PrismaticPowerResidueDerived

/-! # 具体的逐次根添加対象の冪零剰余射による実還元

実A/(p,dⁿ)還元の後に実冪零剰余射を施した対象を計算する。
A/(p,dⁿ)上の離散性・平坦性自体はG10の別工程である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

/-- 実冪剰余の実冪零還元は、既存の標準係数作用付きraw商のsingle対象。 -/
def deltaRootSourcePowerResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Z₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm ≪≫
    deltaRootSourceIteratedPDResidueIso_of_preservesColimit D d b hpA hd hg v hv hpres

/-- 実冪剰余の実冪零還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourcePowerResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Z₀).obj) :=
  (deltaRootSourceIteratedPDResidue_homology_isZero_of_preservesColimit
    D d b hpA hd hg v hv hpres i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm))

/-- 実冪零還元のH0はA/(p,d)上忠実平坦。冪剰余環上の平坦性とは区別する。 -/
theorem deltaRootSourcePowerResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm)
  have := deltaRootSourceIteratedPDResidueH0_faithfullyFlat_of_preservesColimit
    D d b hpA hd hg v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze
