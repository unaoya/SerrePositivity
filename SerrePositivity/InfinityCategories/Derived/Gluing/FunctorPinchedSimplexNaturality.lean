module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplex

/-! 対象宇宙が異なる実 pinched 関手像の、元の全引き戻しに関する自然性。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D) {x y : C} {m n : ℕ}

lemma dgGluingFunctorPinchedSimplex_pullback (s : (DGNerve.pinchedHom R C x y) _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s).pullback α =
      dgGluingFunctorPinchedSimplex.{u, v, w, r} F (s.pullback α) := by
  apply InfinityCategories.PinchedHom.Simplex.ext
  change (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s).val.pullback
      (InfinityCategories.PinchedHom.extendOrderHom α.toOrderHom) =
    (dgGluingFunctorPinchedSimplex.{u, v, w, r} F (s.pullback α)).val
  rw [dgGluingFunctorPinchedSimplex_val, dgGluingFunctorPinchedSimplex_val]
  apply Simplex.ext
  exact (SimplexData.map_pullback s.val.toSimplexData F
    (InfinityCategories.PinchedHom.extendOrderHom α.toOrderHom)).symm

end SerrePositivity.InfinityCategories
