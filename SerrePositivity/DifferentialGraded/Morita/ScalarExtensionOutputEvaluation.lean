module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedComparison
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplexNaturality

/-! # 出力加群と出力複体の導来係数変更をつなぐ計算モデル

評価した複体のK-flat性と、加群係数変更の増大の可逆性を分けて保持する。
指定モデルを持つ導来対象について、二つの導来係数変更の評価を実際の射で比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (E : Type v) [DGCategory A E] [Small.{u} E]
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]
  [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

/-- 加群側の係数変更の評価から、通常係数変更の評価への自然な増大。 -/
def scalarOutputModuleEvaluationAugmentation (e : E) :
    moduleToDerived A E ⋙ derivedExtension φ E ⋙
        moduleDerivedEvaluation A' (DGBaseChange φ E) e ⟶
      moduleEvaluation A E e ⋙ extension φ ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (derivedExtensionAugmentation φ E)
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e) ≫
    (Functor.isoWhiskerLeft (moduleExtension φ E)
      (eqToIso (moduleDerivedEvaluation_fac A' (DGBaseChange φ E) e))).hom ≫
    (Functor.isoWhiskerRight (moduleExtensionEvaluationIso φ E e) DerivedCategory.Q).hom

/-- 複体側の係数変更から同じ通常評価モデルへの自然な増大。 -/
def scalarOutputComplexEvaluationAugmentation (e : E) :
    moduleToDerived A E ⋙ moduleDerivedEvaluation A E e ⋙ complexDerivedExtension φ ⟶
      moduleEvaluation A E e ⋙ extension φ ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (eqToIso (moduleDerivedEvaluation_fac A E e))
      (complexDerivedExtension φ)).hom ≫
    Functor.whiskerLeft (moduleEvaluation A E e) (complexDerivedExtensionAugmentation φ)

omit [HasDerivedCategory (ModuleCat.{u} A)] in
lemma scalarOutputModuleEvaluationAugmentation_isIso (e : E) (N : ModuleCategory A E)
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    IsIso ((scalarOutputModuleEvaluationAugmentation φ E e).app N) := by
  let := hAug
  dsimp only [scalarOutputModuleEvaluationAugmentation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom]
  infer_instance

lemma scalarOutputComplexEvaluationAugmentation_isIso (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N)) :
    IsIso ((scalarOutputComplexEvaluationAugmentation φ E e).app N) := by
  have := complexDerivedExtensionAugmentation_isIso φ ((moduleEvaluation A E e).obj N) hN
  dsimp only [scalarOutputComplexEvaluationAugmentation, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- モデルの増大を反転し、出力加群の係数変更と評価複体の係数変更を比較する。 -/
def scalarOutputEvaluationModelIso (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj ((moduleToDerived A E).obj N)) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((derivedExtension φ E).obj ((moduleToDerived A E).obj N)) := by
  have := scalarOutputModuleEvaluationAugmentation_isIso φ E e N hAug
  have := scalarOutputComplexEvaluationAugmentation_isIso φ E e N hN
  exact asIso ((scalarOutputComplexEvaluationAugmentation φ E e).app N) ≪≫
    (asIso ((scalarOutputModuleEvaluationAugmentation φ E e).app N)).symm

/-- 比較は、加群と複体の実際の二つの増大を可換にする。 -/
lemma scalarOutputEvaluationModelIso_augmentation (e : E) (N : ModuleCategory A E)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (scalarOutputEvaluationModelIso φ E e N hN hAug).hom ≫
        (scalarOutputModuleEvaluationAugmentation φ E e).app N =
      (scalarOutputComplexEvaluationAugmentation φ E e).app N := by
  have := scalarOutputModuleEvaluationAugmentation_isIso φ E e N hAug
  simp only [scalarOutputEvaluationModelIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 条件を満たす出力モデル間の全閉零射についての自然性。 -/
lemma scalarOutputEvaluationModelIso_naturality (e : E) {N N' : ModuleCategory A E}
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hN' : complexKFlat A ((moduleEvaluation A E e).obj N'))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N))
    (hAug' : IsIso ((derivedExtensionAugmentation φ E).app N')) (f : N ⟶ N') :
    (complexDerivedExtension φ).map
        ((moduleDerivedEvaluation A E e).map ((moduleToDerived A E).map f)) ≫
        (scalarOutputEvaluationModelIso φ E e N' hN' hAug').hom =
      (scalarOutputEvaluationModelIso φ E e N hN hAug).hom ≫
        (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map
          ((derivedExtension φ E).map ((moduleToDerived A E).map f)) := by
  let β := scalarOutputModuleEvaluationAugmentation φ E e
  let γ := scalarOutputComplexEvaluationAugmentation φ E e
  have : IsIso (β.app N') := by
    let := hAug'
    dsimp only [β, scalarOutputModuleEvaluationAugmentation, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom]
    infer_instance
  apply (cancel_mono (β.app N')).1
  rw [Category.assoc, scalarOutputEvaluationModelIso_augmentation]
  have hn := β.naturality f
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [hn]
  rw [← Category.assoc, scalarOutputEvaluationModelIso_augmentation]
  exact γ.naturality f

/-- 出力dg圏の局所Hom K-flat性とモデルの各値のK-flat性による十分条件版。 -/
def scalarOutputEvaluationModelIso_ofObjectwiseKFlat
    (hE : localHomKFlat A E) (N : ModuleCategory A E)
    (hN : moduleObjectwiseKFlat A E (ForgetEnrichment.to (Complex A) N)) (e : E) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj ((moduleToDerived A E).obj N)) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((derivedExtension φ E).obj ((moduleToDerived A E).obj N)) :=
  scalarOutputEvaluationModelIso φ E e N (hN e)
    (derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ E N hE hN)

/-- 指定された計算モデルを持つ任意の主導来出力に、実際の比較を移す。 -/
def scalarOutputEvaluationIso (e : E) (X : DerivedModuleCategory A E)
    (N : ModuleCategory A E) (i : X ≅ (moduleToDerived A E).obj N)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (complexDerivedExtension φ).obj ((moduleDerivedEvaluation A E e).obj X) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj ((derivedExtension φ E).obj X) :=
  (complexDerivedExtension φ).mapIso ((moduleDerivedEvaluation A E e).mapIso i) ≪≫
    scalarOutputEvaluationModelIso φ E e N hN hAug ≪≫
    (derivedExtension φ E ⋙ moduleDerivedEvaluation A' (DGBaseChange φ E) e).mapIso i.symm

/-- モデルへの移送と評価比較の正方形。 -/
lemma scalarOutputEvaluationIso_model (e : E) (X : DerivedModuleCategory A E)
    (N : ModuleCategory A E) (i : X ≅ (moduleToDerived A E).obj N)
    (hN : complexKFlat A ((moduleEvaluation A E e).obj N))
    (hAug : IsIso ((derivedExtensionAugmentation φ E).app N)) :
    (scalarOutputEvaluationIso φ E e X N i hN hAug).hom ≫
        (moduleDerivedEvaluation A' (DGBaseChange φ E) e).map ((derivedExtension φ E).map i.hom) =
      (complexDerivedExtension φ).map ((moduleDerivedEvaluation A E e).map i.hom) ≫
        (scalarOutputEvaluationModelIso φ E e N hN hAug).hom := by
  simp only [scalarOutputEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.comp_map, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
