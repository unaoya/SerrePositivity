module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaHom

/-! # 代表加群を始域とする実際のHom係数変更比較の可逆性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite

def moduleHomEvaluateAt (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    [Small.{u} D] (B M : RightModule A D) (z : D) (η : 𝟙_ (Complex A) ⟶ B.obj (op z)) :
    moduleHom A D B M ⟶ M.obj (op z) :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ₘ η) ≫ uncurryRight (moduleHomπ A D B M z)

lemma moduleHomEvaluateAt_eqToIso (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    [Small.{u} D] (B M : RightModule A D) (z : D) (h : B = representable A z) :
    (eqToIso (congrArg (fun N => moduleHom A D N M) h)).hom ≫ (dgYonedaIso A z M).hom =
      moduleHomEvaluateAt A D B M z
        (eId (Complex A) z ≫
          eqToHom (congrArg (fun N : RightModule A D => N.obj (op z)) h.symm)) := by
  subst B
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (z : D) (M : RightModule A D)

lemma scalarModuleYonedaEvaluation_isIso : IsIso (scalarModuleYonedaEvaluation φ D z M) := by
  let e := eqToIso (congrArg (fun N => moduleHom A' (ScalarExtension.DGBaseChange φ D)
    N (ScalarExtension.rightModule φ D M)) (scalarRepresentable_eq φ D z)) ≪≫
      dgYonedaIso A' (show ScalarExtension.DGBaseChange φ D from z)
        (ScalarExtension.rightModule φ D M)
  have he := moduleHomEvaluateAt_eqToIso A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M)
    z (scalarRepresentable_eq φ D z)
  have he' : e.hom = scalarModuleYonedaEvaluation φ D z M := by
    change _ = moduleHomEvaluateAt A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M)
      z (eId (Complex A') (show ScalarExtension.DGBaseChange φ D from z))
    exact he
  rw [← he']
  infer_instance

/-- 代表加群を始域とする実際のHom比較は、任意の係数環準同型に対して可逆。 -/
lemma scalarModuleHom_representable_isIso :
    IsIso (scalarModuleHom φ D (representable A z) M) := by
  let := scalarModuleYonedaEvaluation_isIso φ D z M
  have : IsIso (scalarModuleHom φ D (representable A z) M ≫
      scalarModuleYonedaEvaluation φ D z M) := by
    rw [scalarModuleHom_yoneda_square]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (scalarModuleYonedaEvaluation φ D z M)

end SerrePositivity.DifferentialGraded
