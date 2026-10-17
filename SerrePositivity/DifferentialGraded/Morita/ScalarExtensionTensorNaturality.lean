module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionTensorModels
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor

/-! # U12f係数変更の計算同型と左因子の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma tensorResolutionComputation_left_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') (M : ModuleCategory A D) :
    ((moduleResolutionDerivedTensorLeftFunctor A D R).map g).app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D R
          (ForgetEnrichment.to (Complex A) N') M).hom =
      (moduleResolutionDerivedTensorComputation A D R
        (ForgetEnrichment.to (Complex A) N) M).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 (R M).obj) g) := by
  let η := BalancedTensor.rightTensorHomotopyLeftMap A D g
  let e := moduleDerivedResolutionComputation A D R M
  have hn := congrArg DerivedCategory.Qh.map (η.naturality e.hom)
  simp only [CategoryTheory.Functor.map_comp] at hn
  simp only [moduleResolutionDerivedTensorComputation, Iso.trans_hom,
    Functor.mapIso_hom, moduleTensorHomotopyComputation, eqToIso.hom,
    eqToHom_refl, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_map, Iso.app_hom]
  erw [Category.id_comp, Category.id_comp]
  change DerivedCategory.Qh.map (η.app _) ≫
      (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyFunctor A D
        (ForgetEnrichment.to (Complex A) N')).map e.hom) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
        ((BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) N')).obj (R M).obj)) =
    (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyFunctor A D
        (ForgetEnrichment.to (Complex A) N)).map e.hom) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
        ((BalancedTensor.rightTensorFunctor A D
          (ForgetEnrichment.to (Complex A) N)).obj (R M).obj)) ≫ _
  rw [← Category.assoc, ← hn, Category.assoc]
  dsimp [η]
  rw [BalancedTensor.rightTensorHomotopyLeftMap_app]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

lemma tensorProjectiveResolutionComputation_left_naturality
    {M : ModuleCategory A D} (R : ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    ((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M) ≫
        (moduleDerivedTensorRightResolutionComputation A D R
          (ForgetEnrichment.to (Complex A) N')).hom =
      (moduleDerivedTensorRightResolutionComputation A D R
        (ForgetEnrichment.to (Complex A) N)).hom ≫
          DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 R.obj) g) := by
  change ((moduleResolutionDerivedTensorLeftFunctor A D
    (moduleCanonicalProjectiveResolution A D)).map g).app _ ≫ _ = _
  simp only [moduleDerivedTensorRightResolutionComputation, Iso.trans_hom]
  rw [← Category.assoc,
    tensorResolutionComputation_left_naturality A D (moduleCanonicalProjectiveResolution A D) g M,
    Category.assoc, Category.assoc]
  congr 1
  simp only [moduleProjectiveResolutionTensorIso_hom, ← CategoryTheory.Functor.map_comp]
  congr 1
  change BalancedTensor.map A D (𝟙 _) g ≫
      BalancedTensor.map A D ((moduleCanonicalProjectiveResolution A D M).comparison R) (𝟙 N') =
    BalancedTensor.map A D ((moduleCanonicalProjectiveResolution A D M).comparison R) (𝟙 N) ≫
      BalancedTensor.map A D (𝟙 _) g
  simp only [← BalancedTensor.map_comp, Category.id_comp, Category.comp_id]

lemma relativeTensorComputation_left_naturality
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    ((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M) ≫
        (relativeKFlatTensorComputation D M hM (ForgetEnrichment.to (Complex A) N')).hom =
      (relativeKFlatTensorComputation D M hM (ForgetEnrichment.to (Complex A) N)).hom ≫
        DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 M) g) := by
  change ((moduleResolutionDerivedTensorLeftFunctor A D
    (moduleCanonicalProjectiveResolution A D)).map g).app _ ≫ _ = _
  simp only [relativeKFlatTensorComputation, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc,
    tensorResolutionComputation_left_naturality A D (moduleCanonicalProjectiveResolution A D) g M,
    Category.assoc, Category.assoc]
  congr 1
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  change BalancedTensor.map A D (𝟙 _) g ≫
      BalancedTensor.map A D (moduleCanonicalProjectiveResolution A D M).π (𝟙 N') =
    BalancedTensor.map A D (moduleCanonicalProjectiveResolution A D M).π (𝟙 N) ≫
      BalancedTensor.map A D (𝟙 M) g
  simp only [← BalancedTensor.map_comp, Category.id_comp, Category.comp_id]

private lemma conjugateIso_naturality {C : Type*} [Category* C]
    {X Y X₀ Y₀ U V U₀ V₀ : C}
    (c : X ≅ X₀) (c' : Y ≅ Y₀) (b : X₀ ≅ U₀) (b' : Y₀ ≅ V₀)
    (d : U ≅ U₀) (d' : V ≅ V₀)
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (g : U ⟶ V) (g₀ : U₀ ⟶ V₀)
    (hc : f ≫ c'.hom = c.hom ≫ f₀)
    (hb : f₀ ≫ b'.hom = b.hom ≫ g₀)
    (hd : g ≫ d'.hom = d.hom ≫ g₀) :
    f ≫ (c' ≪≫ b' ≪≫ d'.symm).hom = (c ≪≫ b ≪≫ d.symm).hom ≫ g := by
  apply (cancel_mono d'.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hc, hb, hd]
  simp only [Iso.inv_hom_id_assoc]

variable {A} {A' : Type u} [CommRing A'] (φ : A →+* A')
  [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

set_option maxHeartbeats 600000 in
-- 二つの係数環・三つの計算同型を結ぶ図式の型の照合に、既定値より多い展開が必要。
lemma scalarTensorBaseChange_left_naturality
    {M : ModuleCategory A D} (R : ModuleProjectiveResolution A D M)
    {N N' : LeftModuleCategory A D} (g : N ⟶ N')
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (ForgetEnrichment.to (Complex A) N)))
    (hPN' : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (ForgetEnrichment.to (Complex A) N')))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).map
        (((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M)) ≫
        (derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N') hPN' hP').hom =
      (derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N) hPN hP').hom ≫
        ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
          ((leftModuleExtension φ D).map g)).app
            ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) := by
  let c (L : LeftModuleCategory A D) := (complexDerivedExtension φ).mapIso
    (moduleDerivedTensorRightResolutionComputation A D R (ForgetEnrichment.to (Complex A) L))
  let d (L : LeftModuleCategory A D) :=
    (moduleDerivedTensorRight A' (DGBaseChange φ D)
      (leftModule φ D (ForgetEnrichment.to (Complex A) L))).mapIso
        (derivedExtensionResolutionComputation φ D R) ≪≫
      relativeKFlatTensorComputation (DGBaseChange φ D) ((moduleExtension φ D).obj R.obj)
        hP' (leftModule φ D (ForgetEnrichment.to (Complex A) L))
  let X : (scalarTensorKFlatModels φ D).FullSubcategory :=
    ⟨(R.obj, N), ⟨hPN, hP'⟩⟩
  let Y : (scalarTensorKFlatModels φ D).FullSubcategory :=
    ⟨(R.obj, N'), ⟨hPN', hP'⟩⟩
  let b := (scalarTensorModelBaseChangeIso φ D).app X
  let b' := (scalarTensorModelBaseChangeIso φ D).app Y
  have hc := congrArg (complexDerivedExtension φ).map
    (tensorProjectiveResolutionComputation_left_naturality A D R g)
  simp only [CategoryTheory.Functor.map_comp] at hc
  have hd : ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
          ((leftModuleExtension φ D).map g)).app
          ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) ≫ (d N').hom =
      (d N).hom ≫ DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
        (𝟙 ((moduleExtension φ D).obj R.obj)) ((leftModuleExtension φ D).map g)) := by
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom]
    have ht := ((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
      ((leftModuleExtension φ D).map g)).naturality
        (derivedExtensionResolutionComputation φ D R).hom
    rw [← Category.assoc]
    erw [← ht]
    rw [Category.assoc]
    erw [relativeTensorComputation_left_naturality A' (DGBaseChange φ D)
      ((moduleExtension φ D).obj R.obj) hP' ((leftModuleExtension φ D).map g)]
    exact (Category.assoc _ _ _).symm
  have hb := (scalarTensorModelBaseChangeIso φ D).hom.naturality
    (ObjectProperty.homMk (𝟙 R.obj, g) : X ⟶ Y)
  change (complexDerivedExtension φ).map (DerivedCategory.Q.map
      (BalancedTensor.map A D (𝟙 R.obj) g)) ≫ b'.hom =
    b.hom ≫ DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
      ((moduleExtension φ D).map (𝟙 R.obj)) ((leftModuleExtension φ D).map g)) at hb
  have hn : (derivedTensorBaseChange φ D R
      (ForgetEnrichment.to (Complex A) N) hPN hP').hom =
        ((c N) ≪≫ b ≪≫ (d N).symm).hom := by
    rw [scalarTensorBaseChange_model_square]
    simp only [c, b, d, X, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, ForgetEnrichment.of_to]
  have hn' : (derivedTensorBaseChange φ D R
      (ForgetEnrichment.to (Complex A) N') hPN' hP').hom =
        ((c N') ≪≫ b' ≪≫ (d N').symm).hom := by
    rw [scalarTensorBaseChange_model_square]
    simp only [c, b', d, Y, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, ForgetEnrichment.of_to]
  rw [hn, hn']
  refine conjugateIso_naturality (C := DerivedCategory (ModuleCat.{u} A'))
    (c N) (c N') b b' (d N) (d N')
    ((complexDerivedExtension φ).map
      (((moduleDerivedTensorLeftFunctor A D).map g).app ((moduleToDerived A D).obj M)))
    ((complexDerivedExtension φ).map
      (DerivedCategory.Q.map (BalancedTensor.map A D (𝟙 R.obj) g)))
    (((moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D)).map
      ((leftModuleExtension φ D).map g)).app
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)))
    (DerivedCategory.Q.map (BalancedTensor.map A' (DGBaseChange φ D)
      (𝟙 ((moduleExtension φ D).obj R.obj)) ((leftModuleExtension φ D).map g))) ?_ ?_ ?_
  · exact hc
  · erw [CategoryTheory.Functor.map_id] at hb
    exact hb
  · exact hd

/-- 指定解像度に対するhPNとhP'を両方保持する左因子のモデル条件。 -/
def scalarTensorLeftModels {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) : ObjectProperty (LeftModuleCategory A D) :=
  fun N => scalarTensorKFlatModels φ D (R.obj, N)

def scalarTensorBaseChangeLeftSource (M : ModuleCategory A D) :
    LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  moduleDerivedTensorLeftFunctor A D ⋙
    (CategoryTheory.evaluation (DerivedModuleCategory A D) (DerivedCategory (ModuleCat.{u} A))).obj
      ((moduleToDerived A D).obj M) ⋙ complexDerivedExtension φ

def scalarTensorBaseChangeLeftTarget (M : ModuleCategory A D) :
    LeftModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A') :=
  leftModuleExtension φ D ⋙ moduleDerivedTensorLeftFunctor A' (DGBaseChange φ D) ⋙
    (CategoryTheory.evaluation (DerivedModuleCategory A' (DGBaseChange φ D))
      (DerivedCategory (ModuleCat.{u} A'))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))

/-- U12fの実際の比較同型を、許容モデル上の全左因子射に自然に束ねる。 -/
def scalarTensorBaseChangeLeftIso {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (scalarTensorLeftModels D φ R).ι ⋙ scalarTensorBaseChangeLeftSource D φ M ≅
      (scalarTensorLeftModels D φ R).ι ⋙ scalarTensorBaseChangeLeftTarget D φ M :=
  NatIso.ofComponents
    (fun N => derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N.obj)
      N.property.1 N.property.2)
    (by
      intro N N' g
      exact scalarTensorBaseChange_left_naturality D φ R g.hom
        N.property.1 N'.property.1 N.property.2)

lemma scalarTensorBaseChangeLeftIso_app {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (N : (scalarTensorLeftModels D φ R).FullSubcategory) :
    (scalarTensorBaseChangeLeftIso D φ R).app N =
      derivedTensorBaseChange φ D R (ForgetEnrichment.to (Complex A) N.obj)
        N.property.1 N.property.2 := rfl

end SerrePositivity.DifferentialGraded.Morita
