module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelProduct
public import SerrePositivity.DifferentialGraded.Derived.BimoduleModuleEquivalence

/-! # 任意可換環上の主導来kernelの係数変更

既存の積上の右加群との主導来同値と射影解像度関手を使う。
通常kernelの係数変更を任意の擬同型へ直接適用することはしない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 積上の指定射影解像度族で計算する、全主導来kernel射上の係数変更関手。 -/
def scalarKernelResolutionExtension
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    DerivedBimoduleCategory A E D ⥤
      DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (rightModuleBimoduleDerivedEquivalence A E D).inverse ⋙
    moduleDerivedResolutionFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
      scalarKernelProductHomotopyToDerived φ D E

/-- 標準semifree解像度による主導来kernelの非flatな係数変更。 -/
def scalarKernelDerivedExtension : DerivedBimoduleCategory A E D ⥤
    DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  scalarKernelResolutionExtension φ D E
    (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)

/-- 通常kernelでの計算を、全閉零kernel射に自然な同型として与える。 -/
def scalarKernelResolutionExtensionFacIso
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    bimoduleToDerived A E D ⋙ scalarKernelResolutionExtension φ D E R ≅
      (rightModuleBimoduleEquivalence A E D).inverse ⋙
        moduleResolutionHomotopyFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
          scalarKernelProductHomotopyToDerived φ D E :=
  Functor.isoWhiskerRight (rightModuleBimoduleDerived_inverse_fac A E D)
      (moduleDerivedResolutionFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
        scalarKernelProductHomotopyToDerived φ D E) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A E D).inverse
      (Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A
        (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R) (scalarKernelProductHomotopyToDerived φ D E))

/-- 元のkernelの積上の解像度を係数変更した、実際の主局所化の対象で計算する。 -/
def scalarKernelResolutionExtensionComputation
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M)
    (P : BimoduleCategory A E D) :
    (scalarKernelResolutionExtension φ D E R).obj ((bimoduleToDerived A E D).obj P) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj
          (R ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).obj)) :=
  (scalarKernelResolutionExtensionFacIso φ D E R).app P

/-- 解像度族の変更を全主導来kernel射に自然な同型で比較する。 -/
def scalarKernelResolutionExtensionIso
    (R S : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtension φ D E R ≅ scalarKernelResolutionExtension φ D E S :=
  Functor.isoWhiskerLeft (rightModuleBimoduleDerivedEquivalence A E D).inverse
    (Functor.isoWhiskerRight (moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S)
      (scalarKernelProductHomotopyToDerived φ D E))

lemma scalarKernelResolutionExtensionIso_self
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtensionIso φ D E R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (scalarKernelProductHomotopyToDerived φ D E).map
    ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R R).hom.app _) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (scalarKernelProductHomotopyToDerived φ D E).map_id _

lemma scalarKernelResolutionExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtensionIso φ D E R S ≪≫ scalarKernelResolutionExtensionIso φ D E S T =
      scalarKernelResolutionExtensionIso φ D E R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (scalarKernelProductHomotopyToDerived φ D E).map
      ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S).hom.app _) ≫
      (scalarKernelProductHomotopyToDerived φ D E).map
        ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ S T).hom.app _) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (scalarKernelProductHomotopyToDerived φ D E).map
    (NatTrans.congr_app (congrArg Iso.hom
      (moduleDerivedResolutionIso_trans A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S T)) _)

/-- 任意の証明付き積上射影解像度で、標準導来kernel係数変更を計算する。 -/
def scalarKernelDerivedExtensionResolutionComputation {P : BimoduleCategory A E D}
    (R : ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
      ((rightModuleBimoduleEquivalence A E D).inverse.obj P)) :
    (scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj
          ((rightModuleBimoduleEquivalence A E D).functor.obj R.obj)) := by
  let R₀ := moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
  exact scalarKernelResolutionExtensionComputation φ D E R₀ P ≪≫
    scalarKernelProductHomotopyMapIso φ D E
      (@asIso _ _ _ _ ((moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map
        ((R₀ ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).comparison R))
        ((R₀ ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).comparison_isIso_homotopy R))

end SerrePositivity.DifferentialGraded.Morita
