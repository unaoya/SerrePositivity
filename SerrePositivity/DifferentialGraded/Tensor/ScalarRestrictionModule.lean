module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionCategory

/-! # dg 加群の係数制限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

/-- opposite と係数拡大を交換する逆向きの dg 関手。 -/
def oppositeDGInverse :
    DGFunctor A' (DGBaseChange φ Dᵒᵖ) (DGBaseChange φ D)ᵒᵖ where
  obj x := op (show DGBaseChange φ D from x.unop)
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp x y z := by
    change ((tensorIso φ _ _).inv ≫ (extension φ).map
      ((β_ _ _).hom ≫ eComp (Complex A) (C := D) z.unop y.unop x.unop)) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (β_ _ _).hom ≫ (tensorIso φ _ _).inv ≫
          (extension φ).map (eComp (Complex A) (C := D) z.unop y.unop x.unop)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      CategoryTheory.Functor.map_comp]
    rw [tensorIso_braiding_assoc]

/-- 拡大後の左加群を、係数変更の単位に沿って制限する。 -/
def leftRestriction (M : LeftModule A' (DGBaseChange φ D)) : LeftModule A D :=
  (unitDGFunctor φ D).comp ((restrictDGFunctor φ M).comp (restrictionComplexDGFunctor φ))

/-- 拡大後の右加群を元の dg 圏上の右加群へ制限する。 -/
def rightRestriction (M : RightModule A' (DGBaseChange φ D)) : RightModule A D :=
  RightModule.ofFunctor (leftRestriction φ Dᵒᵖ ((oppositeDGInverse φ D).comp M.toFunctor))

lemma rightRestriction_obj (M : RightModule A' (DGBaseChange φ D)) (x : D) :
    (rightRestriction φ D M).obj (op x) = (restriction φ).obj (M.obj (op x)) := rfl

lemma leftRestriction_obj (M : LeftModule A' (DGBaseChange φ D)) (x : D) :
    (leftRestriction φ D M).obj x = (restriction φ).obj (M.obj x) := rfl

lemma rightRestriction_map (M : RightModule A' (DGBaseChange φ D)) (x y : Dᵒᵖ) :
    (rightRestriction φ D M).map x y = (adjunction φ).unit.app (x ⟶[Complex A] y) ≫
      (restriction φ).map (M.map x y) ≫ restrictionHom φ (M.obj x) (M.obj y) := by
  change (adjunction φ).unit.app _ ≫
    (restriction φ).map (𝟙 _ ≫ M.map x y) ≫ _ = _
  rw [Category.id_comp]
  rfl

lemma rightRestriction_action (M : RightModule A' (DGBaseChange φ D)) (x y : Dᵒᵖ)
    (p r n : ℤ) (h : r + p = n) (f : GradedHom A x y p) (m : (M.obj x).X r) :
    let := φ.toAlgebra
    moduleAction A (rightRestriction φ D M) (x := x) (y := y) f m h =
      moduleAction A' M (x := x) (y := y) ((1 : A') ⊗ₜ[A] f) m h := by
  let := φ.toAlgebra
  unfold moduleAction
  rw [rightRestriction_map]
  rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
