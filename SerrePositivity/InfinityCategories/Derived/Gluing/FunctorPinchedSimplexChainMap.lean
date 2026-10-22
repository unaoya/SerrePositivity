module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplexNaturality

/-! 共通対象宇宙での実 pinched 関手像は、既存の同じ Hom 鎖写像の作用そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C D : Type v}
  [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D)

lemma dgGluingFunctorPinchedSimplex_chainMap {x y : C} {n : ℕ}
    (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    dgGluingFunctorPinchedSimplex.{u, v, v, r} F s =
      pinchedHomChainMapSimplex (F.map x y) s := by
  apply (linearEquiv (F.obj x) (F.obj y) n).injective
  change toLinearSimplex (dgGluingFunctorPinchedSimplex.{u, v, v, r} F s) =
    toLinearSimplex (pinchedHomChainMapSimplex (F.map x y) s)
  rw [pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  exact dgGluingFunctorPinchedSimplex_component F s J k hJ hk

end SerrePositivity.InfinityCategories
