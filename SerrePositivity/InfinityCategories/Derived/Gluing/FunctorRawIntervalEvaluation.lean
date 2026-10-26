module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedModelInverseNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
/-!
概要：任意 dg 関手の元 Hom 複体上の全区間評価は、同じ nerve の実作用に等しい。
方針：実 Hom 模型同型の自然性と同じ pinched 全 join 評価を合成する。
規約：全次数・全区間を保持する。使われ方：元 lax 標的の二脚の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C D : Type v} [DGCategory R C] [DGCategory R D]
lemma dgGluingFunctorRawIntervalEvaluation (F : DGFunctor R C D) (x y : C) :
    intervalMappingUncurry (complexPinchedMap.{u,v} (F.map x y) ≫
      (pinchedComplexModelIso (F.obj x) (F.obj y)).inv ≫
        pinchedHomToIntervalMappingSpace _ _) =
    rightMappingSpacePrism _ ≫ pinchedHomUncurry (pinchedComplexModelIso x y).inv ≫
      dgNerve.map F := by
  rw [← Category.assoc, dgGluingComplexPinchedModelInverse_naturality,
    ← dgFunctor_pinchedHomMap_eq]
  simp only [Category.assoc]
  rw [← Category.assoc]
  erw [dgGluingPinchedEndpointIso_interval_uncurry]
  rw [pinchedHomUncurry_postcomp]

end SerrePositivity.InfinityCategories
