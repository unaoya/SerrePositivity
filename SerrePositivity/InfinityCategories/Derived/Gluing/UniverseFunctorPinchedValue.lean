module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorPinchedSimplex

/-! 一般宇宙の Hom 鎖作用から再構成した実 pinched 単体の台は、元の dg 関手像そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D) {x y : C}

lemma dgGluingUniverseFunctorPinchedValue {n : ℕ}
    (s : ((SSet.uliftFunctor.{max w r, max u v}).obj
      (DGNerve.pinchedHom R C x y)) _⦋n⦌) :
    ((dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)).app
      (Opposite.op ⦋n⦌) s).down.val = s.down.val.map F := by
  have he : ((dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)).app
      (Opposite.op ⦋n⦌) s).down = dgGluingFunctorPinchedSimplex.{u, v, w, r} F s.down := by
    apply (linearEquiv (F.obj x) (F.obj y) n).injective
    change toLinearSimplex ((dgGluingUniverseHomChainMap.{u, v, w, r}
      (F.map x y)).app (Opposite.op ⦋n⦌) s).down =
        toLinearSimplex (dgGluingFunctorPinchedSimplex.{u, v, w, r} F s.down)
    rw [dgGluingUniverseHomChainMap_linear.{u, v, w, r} (F.map x y) s]
    apply Subtype.ext
    funext i
    rcases i with ⟨⟨J, k⟩, hJ, hk⟩
    exact (dgGluingFunctorPinchedSimplex_component F s.down J k hJ hk).symm
  exact (congrArg InfinityCategories.PinchedHom.Simplex.val he).trans
    (dgGluingFunctorPinchedSimplex_val F s.down)

end SerrePositivity.InfinityCategories
