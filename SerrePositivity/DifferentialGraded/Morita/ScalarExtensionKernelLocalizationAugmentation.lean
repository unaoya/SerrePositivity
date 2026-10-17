module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalization

/-! # 主導来kernel係数変更から通常モデルへの自然な増大比較

比較射の構成と可逆性のモデル条件を分ける。
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

lemma scalarKernelProductHomotopyToDerived_map_closed
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f : M ⟶ N) :
    (scalarKernelProductHomotopyToDerived φ D E).map
        ((moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map f) =
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) :=
  rfl

/-- 任意の積上解像度族の増大を、通常kernelの全閉零射に自然に送る。 -/
def scalarKernelResolutionAugmentation
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    (rightModuleBimoduleEquivalence A E D).inverse ⋙
        moduleResolutionHomotopyFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
          scalarKernelProductHomotopyToDerived φ D E ⟶
      scalarKernelFunctor φ D E ⋙ bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) where
  app P := (scalarKernelFunctor φ D E ⋙
    bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
      ((rightModuleBimoduleEquivalence A E D).functor.map
          (R ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
        ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom)
  naturality {P Q} f := by
    let H := rightModuleBimoduleEquivalence A E D
    let G := scalarKernelFunctor φ D E ⋙
      bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)
    let F := H.functor ⋙ G
    have h := congrArg (scalarKernelProductHomotopyToDerived φ D E).map
      ((R (H.inverse.obj P)).lift_fac (R (H.inverse.obj Q)) (H.inverse.map f))
    simp only [CategoryTheory.Functor.map_comp,
      scalarKernelProductHomotopyToDerived_map_closed] at h
    have hn := congrArg G.map (H.counitIso.hom.naturality f)
    simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hn
    change F.map ((R (H.inverse.obj P)).lift (R (H.inverse.obj Q)) (H.inverse.map f)) ≫
        G.map (H.functor.map (R (H.inverse.obj Q)).π ≫ (H.counitIso.app Q).hom) =
      G.map (H.functor.map (R (H.inverse.obj P)).π ≫ (H.counitIso.app P).hom) ≫ G.map f
    simp only [CategoryTheory.Functor.map_comp]
    rw [← Category.assoc]
    erw [h]
    rw [Category.assoc]
    erw [hn]
    exact (Category.assoc _ _ _).symm

/-- 主導来kernel係数変更を通常kernelの係数変更へ比較する自然変換。 -/
def scalarKernelDerivedExtensionAugmentation :
    bimoduleToDerived A E D ⋙ scalarKernelDerivedExtension φ D E ⟶
      scalarKernelFunctor φ D E ⋙ bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (scalarKernelResolutionExtensionFacIso φ D E
      (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)).hom ≫
    scalarKernelResolutionAugmentation φ D E
      (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)

lemma scalarKernelDerivedExtensionAugmentation_app (P : BimoduleCategory A E D) :
    (scalarKernelDerivedExtensionAugmentation φ D E).app P =
      (scalarKernelResolutionExtensionComputation φ D E
        (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) P).hom ≫
        (scalarKernelFunctor φ D E ⋙
          bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
          ((rightModuleBimoduleEquivalence A E D).functor.map
              (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
                ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
            ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom) := rfl

/-- 比較の可逆性には、選んだ積上モデルの増大が係数変更後も擬同型となる条件を保持する。 -/
lemma scalarKernelDerivedExtensionAugmentation_isIso (P : BimoduleCategory A E D)
    (hπ : BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map
        ((rightModuleBimoduleEquivalence A E D).functor.map
            (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
              ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
          ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom))) :
    IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P) := by
  have := bimoduleToDerived_inverts A' (DGBaseChange φ E) (DGBaseChange φ D) _ hπ
  rw [scalarKernelDerivedExtensionAugmentation_app]
  change IsIso (_ ≫ (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map _)
  infer_instance

end SerrePositivity.DifferentialGraded.Morita
