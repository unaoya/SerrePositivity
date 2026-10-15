module
public import SerrePositivity.DifferentialGraded.Module.TensorUnit
public import SerrePositivity.DifferentialGraded.Complexes.TensorCylinder
public import SerrePositivity.DifferentialGraded.Module.QuasiIso
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-! # 全 dg 自然な加群 cylinder とホモトピーの延長

単位複体の標準cylinderをtensorし、左単位比較で元の加群に接続する。
射影は任意可換環上でobjectwise準同型。モデル構造やflatnessを仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex HomotopicalAlgebra
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意加群の標準pre-cylinder。全作用はintervalとのtensorから得る。 -/
def modulePrecylinder (M : ModuleCategory A D) : Precylinder M where
  I := ForgetEnrichment.of (Complex A)
    (tensorModule (dgInterval A) (ForgetEnrichment.to (Complex A) M))
  i₀ := (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₀ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)
  i₁ := (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₁ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)
  π := tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
    (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom
  i₀_π := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleTensorUnitIso_inv_eval, moduleTensorUnitIso_hom_eval, tensorModuleMap_eval,
      Category.assoc, tensorHom_id]
    rw [← comp_whiskerRight_assoc, cylinder.ι₀_π, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id]
  i₁_π := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleTensorUnitIso_inv_eval, moduleTensorUnitIso_hom_eval, tensorModuleMap_eval,
      Category.assoc, tensorHom_id]
    rw [← comp_whiskerRight_assoc, cylinder.ι₁_π, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id]

/-- 標準cylinderの射影はobjectwise quasiIso。 -/
lemma modulePrecylinder_π_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A D (modulePrecylinder A D M).π := by
  intro x
  change QuasiIso ((moduleEvaluation A D x).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom))
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval]
  exact tensorIntervalProjection_quasiIso A _

/-- 全 dg 自然なホモトピーを加群cylinderからの射へ延長する。 -/
def moduleCylinderDesc {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).I ⟶ N :=
  moduleParamUncurry A D (cylinder.desc
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f)
    (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) g) h.some)

lemma moduleCylinderDesc_i₀ {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₀ ≫ moduleCylinderDesc A D f g h = f := by
  change ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₀ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)) ≫
      moduleParamUncurry A D (cylinder.desc _ _ h.some) = f
  rw [Category.assoc, moduleParamUncurry_precomp, cylinder.ι₀_desc, moduleParamUncurry_closed,
    Iso.inv_hom_id_assoc]

lemma moduleCylinderDesc_i₁ {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).i₁ ≫ moduleCylinderDesc A D f g h = g := by
  change ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).inv ≫
    tensorModuleMap (cylinder.ι₁ (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M)) ≫
      moduleParamUncurry A D (cylinder.desc _ _ h.some) = g
  rw [Category.assoc, moduleParamUncurry_precomp, cylinder.ι₁_desc, moduleParamUncurry_closed,
    Iso.inv_hom_id_assoc]

/-- Mathlib LeftHomotopy の具体的証人。 -/
def moduleCylinderLeftHomotopy {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (modulePrecylinder A D M).LeftHomotopy f g where
  h := moduleCylinderDesc A D f g h
  h₀ := moduleCylinderDesc_i₀ A D f g h
  h₁ := moduleCylinderDesc_i₁ A D f g h

end SerrePositivity.DifferentialGraded
