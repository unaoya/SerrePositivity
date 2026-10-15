module
public import SerrePositivity.DifferentialGraded.Module.Free
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 固定複体とのtensorの加群変数での関手性と余極限保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma tensorModuleFamilyMap_naturality (K : Complex A) {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (tensorModule K M).map x y ≫ homPostcompose (K ⊗ M.obj x) (𝟙 K ⊗ₘ a y) =
      (tensorModule K N).map x y ≫ homPrecompose (𝟙 K ⊗ₘ a x) (K ⊗ N.obj y) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (((tensorModule K M).map x y).f p f).comp
      (Cochain.ofHom (𝟙 K ⊗ₘ a y)) (add_zero p) =
    (Cochain.ofHom (𝟙 K ⊗ₘ a x)).comp
      (((tensorModule K N).map x y).f p f) (zero_add p)
  apply Cochain.ext
  intro r n hr
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = r at hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro t v
  change (𝟙 K ⊗ₘ a y).f n (moduleAction A (tensorModule K M) f
      (ιTensorObj K (M.obj x) i j r hij (t ⊗ₜ[A] v)) hr) =
    moduleAction A (tensorModule K N) f
      ((𝟙 K ⊗ₘ a x).f r (ιTensorObj K (M.obj x) i j r hij (t ⊗ₜ[A] v))) hr
  rw [tensorModule_action K M x y p i j r (j + p) n hij rfl hr, tensorMap_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorMap_apply, tensorModule_action K N x y p i j r (j + p) n hij rfl hr]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  exact congrArg (fun z => (p * i).negOnePow.val •
    ιTensorObj K (N.obj y) i (j + p) n (by omega) (t ⊗ₜ[A] z))
      (closedFamily_action A a h x y p j (j + p) rfl f v)

abbrev moduleTensorLeftObj (K : Complex A) (M : ModuleCategory A D) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (tensorModule K (ForgetEnrichment.to (Complex A) M))

def moduleTensorLeftMap (K : Complex A) {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleTensorLeftObj A D K M ⟶ moduleTensorLeftObj A D K N :=
  moduleMorphismMk A D (fun x => 𝟙 K ⊗ₘ closedTransApp A (moduleClosedHomEquiv A D M N f) x)
    (tensorModuleFamilyMap_naturality A D K _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

@[simp] lemma moduleTensorLeftMap_eval (K : Complex A) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleTensorLeftMap A D K f) =
      𝟙 K ⊗ₘ (moduleEvaluation A D x).map f :=
  moduleMorphismMk_eval A D _ _ x

@[implicit_reducible]
def moduleTensorLeftFunctor (K : Complex A) : ModuleCategory A D ⥤ ModuleCategory A D where
  obj := moduleTensorLeftObj A D K
  map := moduleTensorLeftMap A D K
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleTensorLeftMap_eval, CategoryTheory.Functor.map_id,
      tensorHom_id, id_whiskerRight, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleTensorLeftMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, moduleTensorLeftMap_eval, moduleTensorLeftMap_eval]
    simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- 評価と左tensorの可換比較。 -/
def moduleTensorLeftEvaluationIso (K : Complex A) (x : D) :
    moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A D x ⋙ tensorLeft K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    change (moduleEvaluation A D x).map (moduleTensorLeftMap A D K f) ≫ 𝟙 _ =
      𝟙 _ ≫ K ◁ (moduleEvaluation A D x).map f
    rw [moduleTensorLeftMap_eval, Category.comp_id, Category.id_comp, id_tensorHom])

instance moduleTensorLeftPreservesColimit (K : Complex A) {J : Type w} [Category.{w'} J]
    [Small.{u} J] (F : J ⥤ ModuleCategory A D) :
    PreservesColimit F (moduleTensorLeftFunctor A D K) := by
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply moduleIsColimitOfEvaluations A D
  intro x
  let : PreservesColimit F (moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x) :=
    preservesColimit_of_natIso F (moduleTensorLeftEvaluationIso A D K x).symm
  exact isColimitOfPreserves (moduleTensorLeftFunctor A D K ⋙ moduleEvaluation A D x)
    (colimit.isColimit F)

end SerrePositivity.DifferentialGraded
