module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleFunctorFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseComposition
/-!
概要：任意の対象宇宙の加群値 dg 関手の全区間族を、元の共通宇宙 Hom 入力上で評価する。
方針：共通宇宙変更の三角形則で実関手の Hom 作用へ戻し、同じ join prism を前合成する。
規約：Small は基準 dg 圏だけに置き、関手の始域には仮定しない。
使われ方：元左右 Hom 複体上の導来二作用を正本標的の作用と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w e
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (E : Type e) [DGCategory R E]
lemma dgGluingModuleRawFunctorEvaluation (F : DGFunctor R E (RightModule R C)) (x y : E) :
    intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u,v,max w e} R C
      (complexPinchedMap.{u,max (u + 1) v} (F.map x y) ≫
        (pinchedComplexModelIso (F.obj x) (F.obj y)).inv)) =
    rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w e,max u v w e}).obj
        (complexPinchedSpace.{u,max u v w e} (homObject R E x y))) ≫
      pinchedHomUncurry
        ((dgGluingCommonComplexPinchedUniverseIso.{u,max u v w e,e,max (u + 1) v w e}
          (homObject R E x y)).hom ≫
          (dgGluingUniversePinchedComplexIso.{u,e,max (u + 1) v w e} R E x y).inv) ≫
      dgGluingUniverseNerveMap.{u,e,max (u + 1) v,max (u + 1) v w e} F ≫
        dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C := by
  let V := (dgGluingCommonComplexPinchedUniverseIso.{u,max u v w e,e,max (u + 1) v w e}
    (homObject R E x y)).hom
  let G := (((SSet.uliftFunctor.{max (u + 1) v w e,max u e}).map
      (complexPinchedMap.{u,e} (F.map x y)) ≫
    (dgGluingCommonComplexPinchedUniverseIso.{u,e,max (u + 1) v,max (u + 1) v w e}
      (homObject R (RightModule R C) (F.obj x) (F.obj y))).hom ≫
    (dgGluingUniversePinchedComplexIso.{u,max (u + 1) v,max (u + 1) v w e}
      R (RightModule R C) (F.obj x) (F.obj y)).inv) ≫
    pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C)
      (ULift.up (Simplex.vertex (F.obj x))) (ULift.up (Simplex.vertex (F.obj y))) ≫
      pinchedHomToIntervalMappingSpace _ _)
  have hg := dgGluingUniverseFunctorIntervalImage.{u,e,max (u + 1) v,max (u + 1) v w e}
    F x y (dgGluingUniverseModuleDerivedComparison.{u,v,max w e} R C)
  have hv : V ≫ G = dgGluingUniverseModuleDerivedFamilyInterval.{u,v,max w e} R C
      (complexPinchedMap.{u,max (u + 1) v} (F.map x y) ≫
        (pinchedComplexModelIso (F.obj x) (F.obj y)).inv) := by
    dsimp only [V, G]
    simp only [Category.assoc]
    rw [reassoc_of% dgGluingCommonComplexUniverse_map_triangle.{u,max u v w e,e,max (u + 1) v,max (u + 1) v w e}
      (homObject R E x y) (F.map x y)]
    exact (dgGluingUniverseModuleHomFamily.{u,v,max w e} R C (F.map x y)).symm
  rw [← hv, intervalMappingUncurry_precomp, hg]
  rw [reassoc_of% rightMappingSpacePrism_naturality V,
    ← reassoc_of% pinchedHomUncurry_precomp]
end SerrePositivity.InfinityCategories
