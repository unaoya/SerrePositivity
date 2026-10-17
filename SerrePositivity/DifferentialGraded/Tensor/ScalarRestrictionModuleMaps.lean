module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionModule
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionNaturality

/-! # dg 加群圏上の係数制限関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma rightRestriction_family_naturality {M N : RightModule A' (DGBaseChange φ D)}
    (a : ∀ x : (DGBaseChange φ D)ᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : (DGBaseChange φ D)ᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖ) :
    (rightRestriction φ D M).map x y ≫
        homPostcompose ((rightRestriction φ D M).obj x) ((restriction φ).map (a y)) =
      (rightRestriction φ D N).map x y ≫
        homPrecompose ((restriction φ).map (a x)) ((rightRestriction φ D N).obj y) := by
  rw [rightRestriction_map, rightRestriction_map]
  have hh : (restriction φ).map (M.map x y) ≫ restrictionHom φ (M.obj x) (M.obj y) ≫
      homPostcompose ((restriction φ).obj (M.obj x)) ((restriction φ).map (a y)) =
    ((restriction φ).map (N.map x y) ≫ restrictionHom φ (N.obj x) (N.obj y)) ≫
      homPrecompose ((restriction φ).map (a x)) ((restriction φ).obj (N.obj y)) := by
    erw [← restrictionHom_postcompose φ (M.obj x) (a y)]
    rw [← CategoryTheory.Functor.map_comp_assoc, h, CategoryTheory.Functor.map_comp,
      Category.assoc]
    erw [restrictionHom_precompose φ (a x) (N.obj y)]
    exact (Category.assoc _ _ _).symm
  have he := congrArg (fun t => (adjunction φ).unit.app (x ⟶[Complex A] y) ≫ t) hh
  simp only [Category.assoc] at he
  convert he using 1 <;> rfl

variable [Small.{u} D]

/-- 全次数自然な射の値を係数制限し、元の dg 圏上の射に戻す。 -/
def moduleRestrictionMap {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N) :
    ForgetEnrichment.of (Complex A) (rightRestriction φ D (ForgetEnrichment.to (Complex A') M)) ⟶
      ForgetEnrichment.of (Complex A) (rightRestriction φ D (ForgetEnrichment.to (Complex A') N)) :=
  moduleMorphismMk A D
    (fun x => (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x.unop).map f))
    (rightRestriction_family_naturality φ D
      (closedTransApp A' (moduleClosedHomEquiv A' (DGBaseChange φ D) M N f))
      (closedTransApp_naturality A' (moduleClosedHomEquiv A' (DGBaseChange φ D) M N f)))

@[simp]
lemma moduleRestrictionMap_eval {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N)
    (x : D) :
    (moduleEvaluation A D x).map (moduleRestrictionMap φ D f) =
      (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x).map f) :=
  moduleMorphismMk_eval A D _ _ x

/-- 係数変更の単位に沿った右 dg 加群の係数制限関手。 -/
def moduleRestriction : ModuleCategory A' (DGBaseChange φ D) ⥤ ModuleCategory A D where
  obj M := ForgetEnrichment.of (Complex A)
    (rightRestriction φ D (ForgetEnrichment.to (Complex A') M))
  map f := moduleRestrictionMap φ D f
  map_id M := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    rw [moduleRestrictionMap_eval, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleRestrictionMap_eval, moduleRestrictionMap_eval]

@[simp]
lemma moduleRestriction_eval {M N : ModuleCategory A' (DGBaseChange φ D)} (f : M ⟶ N)
    (x : D) :
    (moduleEvaluation A D x).map ((moduleRestriction φ D).map f) =
      (restriction φ).map ((moduleEvaluation A' (DGBaseChange φ D) x).map f) :=
  moduleRestrictionMap_eval φ D f x

def moduleRestrictionEvaluationIso (x : D) :
    moduleRestriction φ D ⋙ moduleEvaluation A D x ≅
      moduleEvaluation A' (DGBaseChange φ D) x ⋙ restriction φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)

end SerrePositivity.DifferentialGraded.ScalarExtension
