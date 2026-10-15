module

public import SerrePositivity.BhattScholze.DeltaRootSourcePDResidue
public import SerrePositivity.BhattScholze.PrismaticCoefficientCompletionReduction

/-! # 実根添加対象の逐次主元完備化後の(p,d)還元

既存の二つの主元完備化を逐次適用した具体的対象を扱う。
原典の(p,d)完備化・環H0候補との比較や離散性は別工程である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
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
local notation "X₀" => DeltaRootSourceCoefficientObject d D b
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 既存の実p完備化の後に既存の実d完備化を施した具体的根添加対象。 -/
abbrev DeltaRootSourceIteratedPDCompletion := (Cd).obj ((Cp).obj X₀)

/-- p,dが個別に正則なら、この逐次対象の実(p,d)還元は元の実還元と同型。 -/
def deltaRootSourceIteratedPDReductionIso
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b) ≅
      (boundedAboveDerivedBaseChange q₀).obj X₀ :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hpA hd X₀

omit [Unique σ] in
/-- 還元比較は、元の対象からの合成標準完備化単位の像の左逆となる。 -/
theorem deltaRootSourceIteratedPDReductionIso_unit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (deltaRootSourceIteratedPDReductionIso D d b hpA hd).hom = 𝟙 _ :=
  prismaticCoefficientIteratedCompletionPairIso_unit (p : A) d hpA hd X₀

/-- G7入力の下、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。 -/
def deltaRootSourceIteratedPDResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceIteratedPDReductionIso D d b hpA hd ≪≫
    deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres

/-- raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。 -/
theorem deltaRootSourceIteratedPDResidueIso_unit_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (deltaRootSourceIteratedPDResidueIso_of_preservesColimit D d b hpA hd hg v hv hpres).hom =
      (deltaRootSourceCoefficientPDResidueIso_of_preservesColimit D d b hpA hg v hv hpres).hom := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [deltaRootSourceIteratedPDResidueIso_of_preservesColimit, Iso.trans_hom]
  rw [← Category.assoc, deltaRootSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourceIteratedPDResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj) :=
  (deltaRootSourceCoefficientPDResidue_homology_isZero_of_preservesColimit
    D d b hpA hg v hv hpres i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (deltaRootSourceIteratedPDReductionIso D d b hpA hd)))

/-- 逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。 -/
theorem deltaRootSourceIteratedPDResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (DeltaRootSourceIteratedPDCompletion D d b)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj (DeltaRootSourceIteratedPDCompletion D d b)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceIteratedPDReductionIso D d b hpA hd))
  have := deltaRootSourceCoefficientPDResidueH0_faithfullyFlat_of_preservesColimit
    D d b hpA hg v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze
