module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModule
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionNaturality
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # dg 加群圏上の係数拡大関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

instance smallDGBaseChange [Small.{u} D] : Small.{u} (DGBaseChange φ D) :=
  inferInstanceAs (Small.{u} D)

lemma rightModule_map (M : RightModule A D) (x y : (DGBaseChange φ D)ᵒᵖ) :
    (rightModule φ D M).map x y =
      (extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y) := by
  change (𝟙 _ ≫ (extension φ).map (M.map x y)) ≫ _ = _
  rw [Category.id_comp]
  rfl

lemma rightModule_family_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : (DGBaseChange φ D)ᵒᵖ) :
    (rightModule φ D M).map x y ≫
        homPostcompose ((rightModule φ D M).obj x) ((extension φ).map (a y)) =
      (rightModule φ D N).map x y ≫
        homPrecompose ((extension φ).map (a x)) ((rightModule φ D N).obj y) := by
  rw [rightModule_map, rightModule_map, Category.assoc]
  change (extension φ).map (M.map x y) ≫ homComparison φ (M.obj x) (M.obj y) ≫
      homPostcompose ((extension φ).obj (M.obj x)) ((extension φ).map (a y)) =
    ((extension φ).map (N.map x y) ≫ homComparison φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((extension φ).map (a x)) ((extension φ).obj (N.obj y))
  erw [← homComparison_postcompose φ (M.obj x) (a y)]
  rw [← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [homComparison_precompose φ (a x) (N.obj y)]
  exact (Category.assoc _ _ _).symm

variable [Small.{u} D]

/-- 全次数自然な射の各値を係数拡大し、実際の加群圏の射へ戻す。 -/
def moduleExtensionMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A') (rightModule φ D (ForgetEnrichment.to (Complex A) M)) ⟶
      ForgetEnrichment.of (Complex A') (rightModule φ D (ForgetEnrichment.to (Complex A) N)) :=
  moduleMorphismMk A' (DGBaseChange φ D)
    (fun x => (extension φ).map ((moduleEvaluation A D x.unop).map f))
    (rightModule_family_naturality φ D
      (closedTransApp A (moduleClosedHomEquiv A D M N f))
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

@[simp]
lemma moduleExtensionMap_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (moduleEvaluation A' (DGBaseChange φ D) x).map (moduleExtensionMap φ D f) =
      (extension φ).map ((moduleEvaluation A D (show D from x)).map f) :=
  moduleMorphismMk_eval A' (DGBaseChange φ D) _ _ x

/-- 係数拡大は加群の対象と全次数自然な射の両方に定義される。 -/
def moduleExtension : ModuleCategory A D ⥤ ModuleCategory A' (DGBaseChange φ D) where
  obj M := ForgetEnrichment.of (Complex A')
    (rightModule φ D (ForgetEnrichment.to (Complex A) M))
  map f := moduleExtensionMap φ D f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleExtensionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleExtensionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleExtensionMap_eval, moduleExtensionMap_eval]

@[simp]
lemma moduleExtension_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : DGBaseChange φ D) :
    (moduleEvaluation A' (DGBaseChange φ D) x).map ((moduleExtension φ D).map f) =
      (extension φ).map ((moduleEvaluation A D (show D from x)).map f) :=
  moduleExtensionMap_eval φ D f x

def moduleExtensionEvaluationIso (x : DGBaseChange φ D) :
    moduleExtension φ D ⋙ moduleEvaluation A' (DGBaseChange φ D) x ≅
      moduleEvaluation A D (show D from x) ⋙ extension φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp)

end SerrePositivity.DifferentialGraded.ScalarExtension
