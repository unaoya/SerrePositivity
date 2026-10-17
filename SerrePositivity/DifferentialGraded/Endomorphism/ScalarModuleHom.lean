module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomNaturality

/-! # 係数変更した実際の加群間の全次数Hom比較

Hom endの係数変更から実際の係数変更加群間のHom endへの射を構成する。
有限性やflat性を仮定せず、この射の可逆性は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

def scalarModuleParamTrans {M N : RightModule A D} {K : Complex A}
    (a : ModuleParamTrans A D K M N) :
    ModuleParamTrans A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.extension φ).obj K)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) where
  app x := (ScalarExtension.extension φ).map (a.app x) ≫
    ScalarExtension.homComparison φ (M.obj x) (N.obj x)
  naturality x y := scalarModuleParamNaturality φ D a x y

variable [Small.{u} D]

def scalarModuleHom (M N : RightModule A D) :
    (ScalarExtension.extension φ).obj (moduleHom A D M N) ⟶
      moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) :=
  (moduleHomEquiv A' (ScalarExtension.DGBaseChange φ D) _ _ _).symm
    (scalarModuleParamTrans φ D
      ((moduleHomEquiv A D (moduleHom A D M N) M N) (𝟙 _)))

@[reassoc]
lemma scalarModuleHom_π (M N : RightModule A D) (x : D) :
    scalarModuleHom φ D M N ≫
        moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) x =
      (ScalarExtension.extension φ).map (moduleHomπ A D M N x) ≫
        ScalarExtension.homComparison φ (M.obj (op x)) (N.obj (op x)) := by
  rw [scalarModuleHom, moduleHomEquiv_symm_π]
  change (ScalarExtension.extension φ).map (𝟙 _ ≫ moduleHomπ A D M N x) ≫ _ = _
  rw [Category.id_comp]

end SerrePositivity.DifferentialGraded
