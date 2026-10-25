module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceCoefficientModels

/-! # 実源の通常加群の係数商比較

既存の商加群・拡張イデアル・係数制限を使い、標準商像を保って比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => MvPolynomial (σ × ℕ) P₀
local notation "C₀" => algebraMap A L₀
variable (I : Ideal A)
local notation "J₀" => Ideal.map C₀ I
local notation "κ₀" => algebraMap (A ⧸ I) (L₀ ⧸ J₀)
attribute [local instance] adicQuotientAlgebra

/-- 二重多項式源の拡張イデアルによる作用部分加群は、元の係数イデアルの作用に一致する。 -/
theorem deltaRootSourceCoefficientIdeal_smul_restrict (M : ModuleCat.{u} L₀) :
    letI := Module.compHom M C₀
    letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    (J₀ • (⊤ : Submodule L₀ M)).restrictScalars A = I • (⊤ : Submodule A M) := by
  let := Module.compHom M C₀
  let : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.restrictScalars_map_smul_eq I ⊤

/-- Aへ制限してから係数商を取る操作と、Lで拡張イデアルの商を取る操作の標準同型。 -/
def deltaRootSourceCoefficientQuotientModuleIso (M : ModuleCat.{u} L₀) :
    (quotientModuleFunctor I).obj ((ModuleCat.restrictScalars C₀).obj M) ≅
      (ModuleCat.restrictScalars κ₀).obj ((quotientModuleFunctor J₀).obj M) := by
  letI := Module.compHom M C₀
  letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA := (Submodule.quotEquivOfEq _ _
    (deltaRootSourceCoefficientIdeal_smul_restrict I M).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv A (J₀ • (⊤ : Submodule L₀ M)))
  refine ModuleCat.isoMk eA.toAddEquiv.toAddCommGrpIso ?_
  intro s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  ext x
  exact (eA.map_smul a x).symm

/-- 標準商像を保つ通常係数商比較の公式。 -/
theorem deltaRootSourceCoefficientQuotientModuleIso_mk (M : ModuleCat.{u} L₀) (x : M) :
    (deltaRootSourceCoefficientQuotientModuleIso I M).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  rfl

/-- この係数商比較は実源加群の任意の射に自然。 -/
def deltaRootSourceCoefficientQuotientModuleNatIso :
    ModuleCat.restrictScalars C₀ ⋙ quotientModuleFunctor I ≅
      quotientModuleFunctor J₀ ⋙ ModuleCat.restrictScalars κ₀ := by
  refine NatIso.ofComponents (deltaRootSourceCoefficientQuotientModuleIso I) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (deltaRootSourceCoefficientQuotientModuleIso I N).hom
        (Submodule.Quotient.mk (f.hom x)) =
          ((ModuleCat.restrictScalars κ₀).map ((quotientModuleFunctor J₀).map f))
            ((deltaRootSourceCoefficientQuotientModuleIso I M).hom (Submodule.Quotient.mk x))
      rw [deltaRootSourceCoefficientQuotientModuleIso_mk,
        deltaRootSourceCoefficientQuotientModuleIso_mk]
      rfl

/-- 同じ通常商比較を、実際の通常係数拡大関手の自然同型として表す。 -/
def deltaRootSourceCoefficientScalarExtensionNatIso :
    ModuleCat.restrictScalars C₀ ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
      ModuleCat.extendScalars (Ideal.Quotient.mk J₀) ⋙ ModuleCat.restrictScalars κ₀ :=
  Functor.isoWhiskerLeft _ (quotientScalarExtensionIso I) ≪≫
    deltaRootSourceCoefficientQuotientModuleNatIso I ≪≫
      Functor.isoWhiskerRight (quotientScalarExtensionIso J₀).symm _

/-- 実源の任意の複体について、通常の係数商比較を項ごとに適用する。 -/
def deltaRootSourceCoefficientCochainSquareIso
    (K : CochainComplex (ModuleCat.{u} L₀) ℤ) :
    baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars κ₀).mapHomologicalComplex (.up ℤ)).obj
        (baseChange (Ideal.Quotient.mk J₀) K) :=
  (Functor.mapHomologicalComplexCompIso
    (deltaRootSourceCoefficientScalarExtensionNatIso I) (.up ℤ)).app K

attribute [local instance] HasDerivedCategory.standard

/-- 元の係数商への実導来還元は、実源商での還元を係数制限した対象と同型。
具体的源のA自由性から制限射影モデルを供給し、Tor仮定は追加しない。 -/
def deltaRootSourceCoefficientDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J₀)).obj X) :=
  ObjectProperty.isoMk _
    (deltaRootSourceCoefficientQuotientModelIso I X P ≪≫
      DerivedCategory.Q.mapIso (deltaRootSourceCoefficientCochainSquareIso I P.complex) ≪≫
        ((derivedRestrictScalarsFactors κ₀).app
          (baseChange (Ideal.Quotient.mk J₀) P.complex)).symm ≪≫
        (derivedRestrictScalars κ₀).mapIso
          (boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk J₀) X P).symm)

end SerrePositivity.BhattScholze
