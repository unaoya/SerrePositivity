module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceCoefficientRightFactor
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceCoefficientResidue
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootFamilyResidueSourceDerived

/-! # 根添加の係数側実導来還元とraw残余商の比較

既存三因子の実導来対象を使い、有限根族の実残余評価比較へ接続する。
導来完備化やperfectionの後の完全忠実平坦性は含まない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)

/-- 有限根族について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。 -/
def deltaRootFamilySourceCoefficientResidueIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DeltaRootSourceCoefficientReduced D d b ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (deltaRootFamilyResidueSourceDerivedIso D d b s hpA v hv)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。 -/
def deltaRootFamilySourceCoefficientResidueHomologyZeroIso (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootFamilySourceCoefficientResidueIso D d b s hpA v hv))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。 -/
theorem deltaRootFamilySourceCoefficientResidue_homology_isZero (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootFamilySourceCoefficientResidueIso D d b s hpA v hv)))

end SerrePositivity.BhattScholze
