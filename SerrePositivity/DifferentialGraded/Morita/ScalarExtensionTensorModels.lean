module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensorCoherence

/-! # U16d：二変数に自然な係数変更モデルとU12f計算の接続

hPN（A上のbalanced tensorのK-flat性）とhP'（係数変更した右加群の相対K-flat性）を
モデルの条件として分けて保持する。主導来kernel作用との接続はその実装後に行う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarTensorKFlatModels : ObjectProperty (ModuleCategory A D × LeftModuleCategory A D) :=
  fun MN => complexKFlat A ((BalancedTensor.functor A D).obj MN) ∧
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) MN.1))

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

def scalarTensorModelSource :
    ModuleCategory A D × LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  BalancedTensor.functor A D ⋙ DerivedCategory.Q ⋙ complexDerivedExtension φ

def scalarTensorModelTarget :
    ModuleCategory A D × LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  (moduleExtension φ D).prod (leftModuleExtension φ D) ⋙
    BalancedTensor.functor A' (DGBaseChange φ D) ⋙ DerivedCategory.Q

def scalarTensorModelComparison : scalarTensorModelSource φ D ⟶ scalarTensorModelTarget φ D where
  app MN := derivedBalancedComparison φ D
    (ForgetEnrichment.to (Complex A) MN.1) (ForgetEnrichment.to (Complex A) MN.2)
  naturality _ _ fg := derivedBalancedComparison_naturality φ D fg.1 fg.2

/-- K-flatなモデルの充満部分圏では、両変数の全射に自然な同型となる。 -/
def scalarTensorModelBaseChangeIso :
    (scalarTensorKFlatModels φ D).ι ⋙ scalarTensorModelSource φ D ≅
      (scalarTensorKFlatModels φ D).ι ⋙ scalarTensorModelTarget φ D := by
  let α := Functor.whiskerLeft (scalarTensorKFlatModels φ D).ι (scalarTensorModelComparison φ D)
  have (X : (scalarTensorKFlatModels φ D).FullSubcategory) : IsIso (α.app X) :=
    derivedBalancedComparison_isIso φ D (ForgetEnrichment.to (Complex A) X.obj.1)
      (ForgetEnrichment.to (Complex A) X.obj.2) X.property.1
  letI := NatIso.isIso_of_isIso_app α
  exact asIso α

lemma scalarTensorModelBaseChangeIso_hom_app
    (X : (scalarTensorKFlatModels φ D).FullSubcategory) :
    (scalarTensorModelBaseChangeIso φ D).hom.app X =
      derivedBalancedComparison φ D (ForgetEnrichment.to (Complex A) X.obj.1)
        (ForgetEnrichment.to (Complex A) X.obj.2) := rfl

/-- U12fの実際の導来tensor比較を、自然な二変数モデルの比較と前後の計算同型で表す。 -/
lemma scalarTensorBaseChange_model_square {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : LeftModule A D)
    (hPN : complexKFlat A (BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) P.obj) N))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) P.obj))) :
    (derivedTensorBaseChange φ D P N hPN hP').hom =
      (complexDerivedExtension φ).map (moduleDerivedTensorRightResolutionComputation A D P N).hom ≫
        (scalarTensorModelBaseChangeIso φ D).hom.app
          ⟨(P.obj, ForgetEnrichment.of (Complex A) N), ⟨hPN, hP'⟩⟩ ≫
        (relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj P.obj)
          hP' (leftModule φ D N)).inv ≫
        (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D N)).map
          (derivedExtensionResolutionComputation φ D P).inv := by
  simp only [derivedTensorBaseChange, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    scalarTensorModelBaseChangeIso_hom_app, derivedBalancedComparison,
    complexDerivedExtensionKFlatIso, asIso_hom, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.Morita
