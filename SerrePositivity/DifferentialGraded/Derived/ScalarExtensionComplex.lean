module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionKFlat

/-! # 非有界複体の導来係数拡大

一対象 dg 圏の主導来圏と既存の DerivedCategory の同値を通す。
有界性や係数環の flatness は要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory HomologicalComplex Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 任意の非有界複体に対する導来係数変更。 -/
def complexDerivedExtension : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} A') :=
  (ringDerivedEquivalence A).inverse ⋙ derivedExtension φ PUnit.{1} ⋙
    moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit

/-- 一対象加群の局所化と複体局所化の比較を逆向きに読む。 -/
def ringDerivedInverseComputation (M : ModuleCategory A PUnit.{1}) :
    (ringDerivedEquivalence A).inverse.obj
        (DerivedCategory.Q.obj ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M)) ≅
      (moduleToDerived A PUnit.{1}).obj M :=
  (ringDerivedEquivalence A).inverse.mapIso ((ringDerivedEquivalence_fac A).app M).symm ≪≫
    ((ringDerivedEquivalence A).unitIso.app ((moduleToDerived A PUnit.{1}).obj M)).symm

/-- 任意の射影加群解像度による非有界複体の計算。 -/
def complexDerivedExtensionComputation (K : Complex A)
    (P : ModuleProjectiveResolution A PUnit.{1}
      (ForgetEnrichment.of (Complex A) (ringModule A K))) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj
        ((ForgetEnrichment.to (Complex A) P.obj).obj (op PUnit.unit))) :=
  (derivedExtension φ PUnit.{1} ⋙
      moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit).mapIso
        (ringDerivedInverseComputation (ForgetEnrichment.of (Complex A) (ringModule A K))) ≪≫
    (moduleDerivedEvaluation A' (DGBaseChange φ PUnit.{1}) PUnit.unit).mapIso
      (derivedExtensionResolutionComputation φ PUnit.{1} P)

/-- A 上 K-flat な複体では、標準 semifree 解像度を外して計算できる。 -/
def complexDerivedExtensionKFlatComputation (K : Complex A) (hK : complexKFlat A K) :
    (complexDerivedExtension φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((extension φ).obj K) := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let P := moduleCanonicalProjectiveResolution A PUnit.{1} M
  have hP : moduleObjectwiseKFlat A PUnit.{1}
      (ForgetEnrichment.to (Complex A) P.obj) :=
    moduleSemifree_objectwiseKFlat A PUnit.{1} (fun _ _ => complexKFlat_unit A)
      (moduleResolutionCandidate_semifree A PUnit.{1} M)
  let f : (ForgetEnrichment.to (Complex A) P.obj).obj (op PUnit.unit) ⟶ K :=
    (moduleEvaluation A PUnit.{1} PUnit.unit).map P.π
  have : QuasiIso f := P.quasiIso PUnit.unit
  have : QuasiIso ((extension φ).map f) :=
    extension_quasiIso_of_kFlat_ends φ (hP PUnit.unit) hK f
  exact complexDerivedExtensionComputation φ K P ≪≫
    asIso (DerivedCategory.Q.map ((extension φ).map f))

end SerrePositivity.DifferentialGraded.ScalarExtension
