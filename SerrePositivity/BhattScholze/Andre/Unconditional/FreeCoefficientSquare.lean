module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceCoefficientModels

/-!
# 自由な係数代数の実導来商正方形

## 概要
元の係数環 A 上自由な代数 S に対し、S 上の実導来対象の A/(I) 還元と
S/(IS) 還元の係数制限を比較する。

## 方針
射影加群の分裂表示を自由な係数制限で保ち、通常商の自然同型を射影モデルへ適用する。

## 規約
自由性は一般補題の明示的 instance であり、無限根自由 δ 源への適用では内部で供給する。

## 使われ方
BS Rem 7.15（著者版 p.62）の元の A 作用を保つ無条件の導来剰余比較。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [Module.Free A S]
local notation "L₀" => S
local notation "C₀" => algebraMap A S

/-- 自由な係数代数上の射影加群は、二重係数包含に沿う実係数制限でも射影的。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientRestrict_projective (M : ModuleCat.{u} L₀) [Projective M] :
    Projective ((ModuleCat.restrictScalars C₀).obj M) := by
  have : Module.Projective L₀ M := inferInstance
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := L₀) (P := M)).mp inferInstance
  let F := ModuleCat.restrictScalars C₀
  let Y := ModuleCat.of L₀ (M →₀ L₀)
  let i : M ⟶ Y := ModuleCat.ofHom s
  let r : Y ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination L₀ id)
  have hir : i ≫ r = 𝟙 M := ModuleCat.hom_ext hs
  let e : F.obj Y ≃ₗ[A] (M →₀ L₀) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (M →₀ L₀) at x
        apply Finsupp.ext
        intro m
        change (algebraMap A L₀ r) * x m = r • x m
        rw [Algebra.smul_def] }
  have : Module.Projective A (F.obj Y) := Module.Projective.of_equiv e.symm
  have hM : Module.Projective A (F.obj M) :=
    Module.Projective.of_split (F.map i).hom (F.map r).hom (by
      apply ModuleCat.hom_ext_iff.mp
      change F.map i ≫ F.map r = 𝟙 (F.obj M)
      rw [← F.map_comp, hir, F.map_id])
  exact ModuleCat.projective_of_categoryTheory_projective (F.obj M)

/-- 指定した実源射影モデルを、実A係数制限対象の射影モデルへ変換する。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientModel
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel (((boundedAboveDerivedRestrictScalars C₀).obj X).obj) where
  complex := ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := freeCoefficientRestrict_projective (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso C₀ X P).symm

/-- 元の係数環の任意イデアルでの実導来還元を、制限した具体的射影モデルで計算する。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X)).obj ≅
      DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (freeCoefficientModel X P)


variable (I : Ideal A)
local notation "J₀" => Ideal.map C₀ I
local notation "κ₀" => algebraMap (A ⧸ I) (L₀ ⧸ J₀)
attribute [local instance] adicQuotientAlgebra

omit [Module.Free A S] in
/-- 自由な係数代数の拡張イデアルによる作用部分加群は、元の係数イデアルの作用に一致する。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientIdeal_smul_restrict (M : ModuleCat.{u} L₀) :
    letI := Module.compHom M C₀
    letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    (J₀ • (⊤ : Submodule L₀ M)).restrictScalars A = I • (⊤ : Submodule A M) := by
  let := Module.compHom M C₀
  let : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.restrictScalars_map_smul_eq I ⊤

/-- Aへ制限してから係数商を取る操作と、Lで拡張イデアルの商を取る操作の標準同型。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModuleIso (M : ModuleCat.{u} L₀) :
    (quotientModuleFunctor I).obj ((ModuleCat.restrictScalars C₀).obj M) ≅
      (ModuleCat.restrictScalars κ₀).obj ((quotientModuleFunctor J₀).obj M) := by
  letI := Module.compHom M C₀
  letI : IsScalarTower A L₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA := (Submodule.quotEquivOfEq _ _
    (freeCoefficientIdeal_smul_restrict I M).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv A (J₀ • (⊤ : Submodule L₀ M)))
  refine ModuleCat.isoMk eA.toAddEquiv.toAddCommGrpIso ?_
  intro s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  ext x
  exact (eA.map_smul a x).symm

/-- 標準商像を保つ通常係数商比較の公式。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
theorem freeCoefficientQuotientModuleIso_mk (M : ModuleCat.{u} L₀) (x : M) :
    (freeCoefficientQuotientModuleIso I M).hom
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  rfl

/-- この係数商比較は実源加群の任意の射に自然。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientQuotientModuleNatIso :
    ModuleCat.restrictScalars C₀ ⋙ quotientModuleFunctor I ≅
      quotientModuleFunctor J₀ ⋙ ModuleCat.restrictScalars κ₀ := by
  refine NatIso.ofComponents (freeCoefficientQuotientModuleIso I) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (freeCoefficientQuotientModuleIso I N).hom
        (Submodule.Quotient.mk (f.hom x)) =
          ((ModuleCat.restrictScalars κ₀).map ((quotientModuleFunctor J₀).map f))
            ((freeCoefficientQuotientModuleIso I M).hom (Submodule.Quotient.mk x))
      rw [freeCoefficientQuotientModuleIso_mk,
        freeCoefficientQuotientModuleIso_mk]
      rfl

/-- 同じ通常商比較を、実際の通常係数拡大関手の自然同型として表す。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientScalarExtensionNatIso :
    ModuleCat.restrictScalars C₀ ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
      ModuleCat.extendScalars (Ideal.Quotient.mk J₀) ⋙ ModuleCat.restrictScalars κ₀ :=
  Functor.isoWhiskerLeft _ (quotientScalarExtensionIso I) ≪≫
    freeCoefficientQuotientModuleNatIso I ≪≫
      Functor.isoWhiskerRight (quotientScalarExtensionIso J₀).symm _

/-- 実源の任意の複体について、通常の係数商比較を項ごとに適用する。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientCochainSquareIso
    (K : CochainComplex (ModuleCat.{u} L₀) ℤ) :
    baseChange (Ideal.Quotient.mk I)
        (((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars κ₀).mapHomologicalComplex (.up ℤ)).obj
        (baseChange (Ideal.Quotient.mk J₀) K) :=
  (Functor.mapHomologicalComplexCompIso
    (freeCoefficientScalarExtensionNatIso I) (.up ℤ)).app K

attribute [local instance] HasDerivedCategory.standard

/-- 元の係数商への実導来還元は、実源商での還元を係数制限した対象と同型。
具体的係数代数のA自由性から制限射影モデルを供給し、Tor仮定は追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の無限根自由 δ 源の係数還元。 -/
def freeCoefficientDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J₀)).obj X) :=
  ObjectProperty.isoMk _
    (freeCoefficientQuotientModelIso I X P ≪≫
      DerivedCategory.Q.mapIso (freeCoefficientCochainSquareIso I P.complex) ≪≫
        ((derivedRestrictScalarsFactors κ₀).app
          (baseChange (Ideal.Quotient.mk J₀) P.complex)).symm ≪≫
        (derivedRestrictScalars κ₀).mapIso
          (boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk J₀) X P).symm)


end SerrePositivity.BhattScholze.Andre
