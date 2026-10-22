module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseFunctorHomAction

/-! 一般宇宙の実 dg 関手像を pinched 単体として回収し、元の全係数を保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D) {x y : C} {n : ℕ}

def dgGluingFunctorPinchedSimplex (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    (DGNerve.pinchedHom R D (F.obj x) (F.obj y)) _⦋n⦌ :=
  downPinchedSimplex (C := dgNerve R D) (n := n)
    ((pinchedEndpointIso (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F x)
      (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F y)).hom.app (Opposite.op ⦋n⦌)
      (pinchedSimplexMap (dgGluingUniverseNerveMap.{u, v, w, r} F) (uliftPinchedSimplex s)))

lemma dgGluingFunctorPinchedSimplex_val (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s).val = s.val.map F := by
  exact congrArg ULift.down (pinchedEndpointIso_hom_val
    (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F x)
    (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F y)
    (pinchedSimplexMap (dgGluingUniverseNerveMap.{u, v, w, r} F) (uliftPinchedSimplex s)))

lemma dgGluingFunctorPinchedSimplex_component (s : (DGNerve.pinchedHom R C x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (toLinearData (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s)).component J k hJ hk =
      (F.map x y).f k ((toLinearData s).component J k hJ hk) := by
  apply eq_of_heq
  have ht := toLinearData_component_heq (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s)
    J k hJ hk
  rw [dgGluingFunctorPinchedSimplex_val] at ht
  exact ht.trans (dgGluingFunctor_map_component_heq F (source_obj s (J.min' hJ))
    (target_obj s) k (toLinearData_component_heq s J k hJ hk).symm)

end SerrePositivity.InfinityCategories
