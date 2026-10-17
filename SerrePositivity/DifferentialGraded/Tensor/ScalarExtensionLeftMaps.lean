module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionBalancedNaturality
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps
public import SerrePositivity.DifferentialGraded.Tensor.Functor

/-! # 左 dg 加群圏の係数拡大と相対 tensor 双関手の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma leftExtension_family_naturality {M N : LeftModule A D}
    (a : ∀ x : D, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : DGBaseChange φ D) :
    (leftModule φ D M).map x y ≫
        homPostcompose ((leftModule φ D M).obj x) ((extension φ).map (a y)) =
      (leftModule φ D N).map x y ≫
        homPrecompose ((extension φ).map (a x)) ((leftModule φ D N).obj y) := by
  change ((extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y)) ≫
      homPostcompose ((extension φ).obj (M.obj x)) ((extension φ).map (a y)) =
    ((extension φ).map (N.map x y) ≫ homComparison φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((extension φ).map (a x)) ((extension φ).obj (N.obj y))
  rw [Category.assoc, ← homComparison_postcompose φ (M.obj x) (a y),
    ← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp,
    Category.assoc, homComparison_precompose φ (a x) (N.obj y)]
  exact (Category.assoc _ _ _).symm

variable [Small.{u} D]

lemma leftMorphism_hom_naturality {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    (ForgetEnrichment.to (Complex A) M).map x y ≫
        homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
          ((leftModuleEvaluation A D y).map f) =
      (ForgetEnrichment.to (Complex A) N).map x y ≫
        homPrecompose ((leftModuleEvaluation A D x).map f)
          ((ForgetEnrichment.to (Complex A) N).obj y) := by
  have h := closedTransApp_naturality A (leftModuleClosedHomEquiv A D M N f)
    (op (op x)) (op (op y))
  change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) at h
  simpa only [Category.id_comp] using h

def leftModuleExtensionMap {M N : LeftModuleCategory A D} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A') (leftModule φ D (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A') (leftModule φ D (ForgetEnrichment.to (Complex A) N)) :=
  leftModuleMorphismMk A' (DGBaseChange φ D)
    (fun x => (extension φ).map ((leftModuleEvaluation A D x).map f))
    (leftExtension_family_naturality φ D
      (fun x => (leftModuleEvaluation A D x).map f) (leftMorphism_hom_naturality D f))

@[simp]
lemma leftModuleExtensionMap_eval {M N : LeftModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) x).map (leftModuleExtensionMap φ D f) =
      (extension φ).map ((leftModuleEvaluation A D (show D from x)).map f) :=
  leftModuleMorphismMk_eval A' (DGBaseChange φ D) _ _ x

def leftModuleExtension : LeftModuleCategory A D ⥤ LeftModuleCategory A' (DGBaseChange φ D) where
  obj M := ForgetEnrichment.of (Complex A')
    (leftModule φ D (ForgetEnrichment.to (Complex A) M))
  map f := leftModuleExtensionMap φ D f
  map_id M := by
    apply leftModuleMorphism_ext
    intro x
    rw [leftModuleExtensionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply leftModuleMorphism_ext
    intro x
    rw [leftModuleExtensionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      leftModuleExtensionMap_eval, leftModuleExtensionMap_eval]

@[simp]
lemma leftModuleExtension_eval {M N : LeftModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) x).map ((leftModuleExtension φ D).map f) =
      (extension φ).map ((leftModuleEvaluation A D (show D from x)).map f) :=
  leftModuleExtensionMap_eval φ D f x

@[reassoc]
lemma balancedIso_module_naturality {M M' : ModuleCategory A D} {N N' : LeftModuleCategory A D}
    (f : M ⟶ M') (g : N ⟶ N') :
    (extension φ).map (BalancedTensor.map A D f g) ≫
        (balancedIso φ D (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N')).hom =
      (balancedIso φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N)).hom ≫
        BalancedTensor.map A' (DGBaseChange φ D)
          ((moduleExtension φ D).map f) ((leftModuleExtension φ D).map g) := by
  apply extendedBalanced_hom_ext φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  intro x
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.ι_map,
    CategoryTheory.Functor.map_comp, Category.assoc, balancedIso_ι,
    balancedIso_ι_assoc]
  erw [BalancedTensor.ι_map A' (DGBaseChange φ D) ((moduleExtension φ D).map f)
    ((leftModuleExtension φ D).map g) (show DGBaseChange φ D from x)]
  erw [moduleExtension_eval φ D f (show DGBaseChange φ D from x),
    leftModuleExtension_eval φ D g (show DGBaseChange φ D from x)]
  exact tensorIso_naturality_assoc φ ((moduleEvaluation A D x).map f)
    ((leftModuleEvaluation A D x).map g) _

end SerrePositivity.DifferentialGraded.ScalarExtension
