module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionModuleMaps
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionColimits

/-! # 実際の係数変更加群間のHomへ向かう全次数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
@[reassoc]
lemma scalarTensorIso_inv_naturality {K K' L L' : Complex A} (f : K ⟶ K') (g : L ⟶ L') :
    ((ScalarExtension.extension φ).map f ⊗ₘ (ScalarExtension.extension φ).map g) ≫
        (ScalarExtension.tensorIso φ K' L').inv =
      (ScalarExtension.tensorIso φ K L).inv ≫ (ScalarExtension.extension φ).map (f ⊗ₘ g) := by
  apply (cancel_epi (ScalarExtension.tensorIso φ K L).hom).1
  rw [Iso.hom_inv_id_assoc, ← ScalarExtension.tensorIso_naturality_assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (D : Type v) [DGCategory A D]

/-- パラメータ付き自然変換の各成分を、実際に係数変更した加群の間へ送る。 -/
lemma scalarModuleParamNaturality {M N : RightModule A D} {K : Complex A}
    (a : ModuleParamTrans A D K M N) (x y : Dᵒᵖ) :
    (β_ ((ScalarExtension.extension φ).obj K)
      ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))).hom ≫
      ((ScalarExtension.rightModule φ D M).map x y ⊗ₘ
        ((ScalarExtension.extension φ).map (a.app y) ≫
          ScalarExtension.homComparison φ (M.obj y) (N.obj y))) ≫
        enrichedComposition _ _ _ =
    (((ScalarExtension.extension φ).map (a.app x) ≫
        ScalarExtension.homComparison φ (M.obj x) (N.obj x)) ⊗ₘ
      (ScalarExtension.rightModule φ D N).map x y) ≫ enrichedComposition _ _ _ := by
  rw [ScalarExtension.rightModule_map, ScalarExtension.rightModule_map]
  change (β_ ((ScalarExtension.extension φ).obj K)
      ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))).hom ≫
    (((ScalarExtension.extension φ).map (M.map x y) ≫ ScalarExtension.homComparison φ _ _) ⊗ₘ
      ((ScalarExtension.extension φ).map (a.app y) ≫ ScalarExtension.homComparison φ _ _)) ≫
        enrichedComposition ((ScalarExtension.extension φ).obj (M.obj x))
          ((ScalarExtension.extension φ).obj (M.obj y))
          ((ScalarExtension.extension φ).obj (N.obj y)) =
    (((ScalarExtension.extension φ).map (a.app x) ≫ ScalarExtension.homComparison φ _ _) ⊗ₘ
      ((ScalarExtension.extension φ).map (N.map x y) ≫ ScalarExtension.homComparison φ _ _)) ≫
        enrichedComposition ((ScalarExtension.extension φ).obj (M.obj x))
          ((ScalarExtension.extension φ).obj (N.obj x))
          ((ScalarExtension.extension φ).obj (N.obj y))
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [← ScalarExtension.homComparison_composition,
    ← ScalarExtension.homComparison_composition]
  erw [scalarTensorIso_inv_naturality_assoc φ (M.map x y) (a.app y),
    scalarTensorIso_inv_naturality_assoc φ (a.app x) (N.map x y)]
  erw [ScalarExtension.tensorIso_braiding_assoc φ K (x ⟶[Complex A] y)]
  change (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
      (ScalarExtension.extension φ).map (β_ K (x ⟶[Complex A] y)).hom ≫
      (ScalarExtension.extension φ).map (M.map x y ⊗ₘ a.app y) ≫
      (ScalarExtension.extension φ).map (enrichedComposition (M.obj x) (M.obj y) (N.obj y)) ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y) =
    (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
      (ScalarExtension.extension φ).map (a.app x ⊗ₘ N.map x y) ≫
      (ScalarExtension.extension φ).map (enrichedComposition (M.obj x) (N.obj x) (N.obj y)) ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y)
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  exact congrArg (fun f => (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
    (ScalarExtension.extension φ).map f ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y)) (a.naturality x y)

end SerrePositivity.DifferentialGraded
