module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison

/-! 元の dg 関手の実 Hom 作用を、端点輸送込みで同じ全 Hom 複体模型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x y : D)

def dgGluingFunctorHomModelMap :
    DGNerve.pinchedHom R D x y ⟶ complexPinchedSpace.{u, v} (homObject R E (F.obj x) (F.obj y)) :=
  pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y) ≫
    (pinchedEndpointIso (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y)).hom ≫
      (pinchedComplexModelIso (F.obj x) (F.obj y)).hom

lemma dgGluingFunctorHomModelMap_eq :
    dgGluingFunctorHomModelMap F x y =
      (pinchedComplexModelIso x y).hom ≫ complexPinchedMap.{u, v} (F.map x y) := by
  rw [dgGluingFunctorHomModelMap, ← Category.assoc, dgFunctor_pinchedHomMap_eq]
  exact pinchedComplexModelIso_naturality _

end SerrePositivity.InfinityCategories
