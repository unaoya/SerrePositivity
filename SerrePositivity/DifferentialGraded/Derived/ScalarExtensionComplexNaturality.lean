module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality

/-! # 非有界複体の underived 比較自然変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

omit φ [HasDerivedCategory (ModuleCat.{u} A')] in
def ringDerivedInverseComparison :
    DerivedCategory.Q ⋙ (ringDerivedEquivalence A).inverse ≅
      (ringModuleEquivalence A).inverse ⋙ moduleToDerived A PUnit.{1} :=
  Functor.isoWhiskerRight (ringModuleEquivalence A).counitIso.symm
      (DerivedCategory.Q ⋙ (ringDerivedEquivalence A).inverse) ≪≫
    Functor.isoWhiskerLeft (ringModuleEquivalence A).inverse
      (Functor.isoWhiskerRight (ringDerivedEquivalence_fac A).symm
        (ringDerivedEquivalence A).inverse) ≪≫
    Functor.isoWhiskerLeft ((ringModuleEquivalence A).inverse ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm

/-- 複体の主導来係数拡大から underived 係数拡大への自然変換。 -/
def complexDerivedExtensionAugmentation :
    DerivedCategory.Q ⋙ complexDerivedExtension φ ⟶ extension φ ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (ringDerivedInverseComparison (A := A)).hom
      (derivedExtension φ PUnit.{1} ⋙
        moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit) ≫
    Functor.whiskerLeft (ringModuleEquivalence A).inverse
      (Functor.whiskerRight (derivedExtensionAugmentation φ PUnit.{1})
        (moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit)) ≫
    (Functor.isoWhiskerLeft ((ringModuleEquivalence A).inverse ⋙ moduleExtension φ PUnit.{1})
      (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ PUnit.{1}) PUnit.unit))).hom ≫
    (Functor.isoWhiskerLeft (ringModuleEquivalence A).inverse
      (Functor.isoWhiskerRight (moduleExtensionEvaluationIso φ PUnit.{1} PUnit.unit)
        DerivedCategory.Q)).hom ≫
    (Functor.isoWhiskerRight (ringModuleEquivalence A).counitIso
      (extension φ ⋙ DerivedCategory.Q)).hom

lemma complexDerivedExtensionAugmentation_isIso (K : Complex A) (hK : complexKFlat A K) :
    IsIso ((complexDerivedExtensionAugmentation φ).app K) := by
  let M := (ringModuleEquivalence A).inverse.obj K
  have hM : moduleObjectwiseKFlat A PUnit.{1} (ForgetEnrichment.to (Complex A) M) := by
    intro x
    cases x
    exact complexKFlat_of_iso A ((ringModuleEquivalence A).counitIso.app K) hK
  have := derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ PUnit.{1} M
    (fun _ _ => complexKFlat_unit A) hM
  dsimp only [complexDerivedExtensionAugmentation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- K-flat な複体上で自然な underived 計算同型。 -/
def complexDerivedExtensionKFlatIso (K : Complex A) (hK : complexKFlat A K) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj K) := by
  have := complexDerivedExtensionAugmentation_isIso φ K hK
  exact asIso ((complexDerivedExtensionAugmentation φ).app K)

lemma complexDerivedExtensionKFlatIso_naturality {K L : Complex A}
    (hK : complexKFlat A K) (hL : complexKFlat A L) (f : K ⟶ L) :
    (complexDerivedExtension φ).map (DerivedCategory.Q.map f) ≫
        (complexDerivedExtensionKFlatIso φ L hL).hom =
      (complexDerivedExtensionKFlatIso φ K hK).hom ≫
        DerivedCategory.Q.map ((extension φ).map f) :=
  (complexDerivedExtensionAugmentation φ).naturality f

end SerrePositivity.DifferentialGraded.ScalarExtension
