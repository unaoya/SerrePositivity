module
public import SerrePositivity.DifferentialGraded.Derived.RightTensor

/-! # 任意の証明付き射影解像度による導来tensor計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable {M : ModuleCategory A D}

def moduleProjectiveResolutionTensorIso (P Q : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj P.obj) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj Q.obj) := by
  have := BalancedTensor.rightTensor_projective_quasiIso A D L P.projective Q.projective
    (P.comparison Q) (P.comparison_quasiIso Q)
  exact asIso (DerivedCategory.Q.map
    ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)))

lemma moduleProjectiveResolutionTensorIso_hom (P Q : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    (moduleProjectiveResolutionTensorIso A D P Q L).hom =
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)) := rfl

lemma moduleProjectiveResolutionTensorIso_self (P : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) : moduleProjectiveResolutionTensorIso A D P P L = Iso.refl _ := by
  apply Iso.ext
  change DerivedCategory.Q.map
    ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison P)) = 𝟙 _
  have h := moduleTensorDerived_map_eq_of_homotopy_map_eq A D L
    (P.comparison_self.trans ((moduleToHomotopy A D).map_id P.obj).symm)
  simpa only [CategoryTheory.Functor.map_id] using h

lemma moduleProjectiveResolutionTensorIso_trans (P Q R : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    moduleProjectiveResolutionTensorIso A D P Q L ≪≫ moduleProjectiveResolutionTensorIso A D Q R L =
      moduleProjectiveResolutionTensorIso A D P R L := by
  apply Iso.ext
  change DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison Q)) ≫
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (Q.comparison R)) =
    DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map (P.comparison R))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact moduleTensorDerived_map_eq_of_homotopy_map_eq A D L
    (((moduleToHomotopy A D).map_comp (P.comparison Q) (Q.comparison R)).trans
      (P.comparison_comp Q R))

/-- 導来tensorの値は任意の射影的解像度で計算できる。 -/
def moduleDerivedTensorRightResolutionComputation (P : ModuleProjectiveResolution A D M)
    (L : LeftModule A D) :
    (moduleDerivedTensorRight A D L).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj P.obj) :=
  moduleResolutionDerivedTensorComputation A D (moduleCanonicalProjectiveResolution A D) L M ≪≫
    moduleProjectiveResolutionTensorIso A D (moduleCanonicalProjectiveResolution A D M) P L

end SerrePositivity.DifferentialGraded
