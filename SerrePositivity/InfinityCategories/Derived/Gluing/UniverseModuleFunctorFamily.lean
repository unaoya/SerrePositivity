module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorIntervalImage
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure

/-! 加群値 dg 関手の実 Hom 作用を、同じ Hom 鎖写像から作った導来全区間族へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleHomFamily {K : Complex R} {P Q : RightModule R C}
    (φ : K ⟶ homObject R (RightModule R C) P Q) :
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v} φ ≫ (pinchedComplexModelIso P Q).inv) =
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} φ) ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
          max (u + 1) v, max (u + 1) v w}
          (homObject R (RightModule R C) P Q)).hom) ≫
        (dgGluingUniversePinchedComplexIso.{u, max (u + 1) v, max (u + 1) v w}
          R (RightModule R C) P Q).inv ≫
        pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
          (ULift.up (Simplex.vertex P)) (ULift.up (Simplex.vertex Q)) ≫
        pinchedHomToIntervalMappingSpace _ _ := by
  have hu := dgGluingComplexPinchedUniverseIso_naturality.{u, max u v w, max (u + 1) v}
    φ
  change (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} φ) ≫
      (dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
        max (u + 1) v, max (u + 1) v w} _).hom = _ at hu
  rw [hu]
  dsimp only [dgGluingUniversePinchedComplexIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, dgGluingUniverseModuleDerivedComparison]
  have hn := uliftPinchedHomIso_naturality.{max (u + 1) v, max (u + 1) v w}
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (Simplex.vertex P) (Simplex.vertex Q)
  rw [Category.assoc, Category.assoc, ← reassoc_of% hn]
  simp only [dgGluingUniverseModuleDerivedFamilyInterval, Functor.map_comp, Category.assoc]
  rfl

variable (E : Type (max u v w)) [DGCategory R E]

lemma dgGluingUniverseModuleFunctorFamily (F : DGFunctor R E (RightModule R C)) (x y : E) :
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v} (F.map x y) ≫
          (pinchedComplexModelIso (F.obj x) (F.obj y)).inv) =
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (F.map x y)) ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, max u v w,
          max (u + 1) v, max (u + 1) v w}
          (homObject R (RightModule R C) (F.obj x) (F.obj y))).hom) ≫
        (dgGluingUniversePinchedComplexIso.{u, max (u + 1) v, max (u + 1) v w}
          R (RightModule R C) (F.obj x) (F.obj y)).inv ≫
        pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
          (ULift.up (Simplex.vertex (F.obj x))) (ULift.up (Simplex.vertex (F.obj y))) ≫
        pinchedHomToIntervalMappingSpace _ _ :=
  dgGluingUniverseModuleHomFamily R C (F.map x y)

end SerrePositivity.InfinityCategories
