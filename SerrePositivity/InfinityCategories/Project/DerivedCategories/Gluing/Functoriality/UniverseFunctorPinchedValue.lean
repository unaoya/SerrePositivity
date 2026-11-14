module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.FunctorPinchedSimplex

/-! 一般宇宙の Hom 鎖作用から再構成した実 pinched 単体の台は、元の dg 関手像そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) {x y : C}

lemma dgGluingUniverseFunctorPinchedValue {n : ℕ}
    (s : ((SSet.uliftFunctor.{max w r, max u v}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y)) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)).app
      (Opposite.op ⦋n⦌) s).down.val = s.down.val.map F := by
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y)).app
      (Opposite.op ⦋n⦌) s).down = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex.{u, v, w, r} F s.down := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (F.obj x) (F.obj y) n).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r}
      (F.map x y)).app (Opposite.op ⦋n⦌) s).down =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex.{u, v, w, r} F s.down)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_linear.{u, v, w, r} (F.map x y) s]
    apply Subtype.ext
    funext i
    rcases i with ⟨⟨J, k⟩, hJ, hk⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex_component F s.down J k hJ hk).symm
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val he).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedSimplex_val F s.down)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
