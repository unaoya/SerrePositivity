module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom

/-! # 実際の係数変更加群圏へ向かうdg関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_identity (M : RightModule A D) :
    (ScalarExtension.unitIso φ).inv ≫
        (ScalarExtension.extension φ).map (moduleIdentity A D M) ≫ scalarModuleHom φ D M M =
      moduleIdentity A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.rightModule φ D M) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, scalarModuleHom_π,
    ← CategoryTheory.Functor.map_comp_assoc, moduleIdentity_π, moduleIdentity_π]
  exact ScalarExtension.homComparison_identity φ (M.obj (Opposite.op x))

lemma scalarModuleHom_composition (M N P : RightModule A D) :
    (ScalarExtension.tensorIso φ (moduleHom A D M N) (moduleHom A D N P)).inv ≫
        (ScalarExtension.extension φ).map (moduleComposition A D M N P) ≫
          scalarModuleHom φ D M P =
      (scalarModuleHom φ D M N ⊗ₘ scalarModuleHom φ D N P) ≫
        moduleComposition A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N)
          (ScalarExtension.rightModule φ D P) := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, scalarModuleHom_π, moduleComposition_π]
  rw [tensorHom_comp_tensorHom_assoc, scalarModuleHom_π, scalarModuleHom_π,
    ← tensorHom_comp_tensorHom_assoc]
  erw [← ScalarExtension.homComparison_composition φ (M.obj (Opposite.op x))
    (N.obj (Opposite.op x)) (P.obj (Opposite.op x))]
  rw [scalarTensorIso_inv_naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    moduleComposition_π]

/-- 移送したambient enrichmentから、実際のD係数変更加群圏への比較。 -/
def scalarModuleDGFunctor :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))
      (RightModule A' (ScalarExtension.DGBaseChange φ D)) where
  obj := ScalarExtension.rightModule φ D
  map M N := scalarModuleHom φ D M N
  map_id M := scalarModuleHom_identity φ D M
  map_comp M N P := scalarModuleHom_composition φ D M N P

end SerrePositivity.DifferentialGraded
