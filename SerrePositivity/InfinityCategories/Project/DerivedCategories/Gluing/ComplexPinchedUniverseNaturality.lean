module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedUniverseIso

/-! 対象宇宙の変更は、元の同じ全鎖写像の pinched 空間作用と厳密に可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L : _root_.SerrePositivity.DifferentialGraded.Complex R}

lemma dgGluingComplexPinchedUniverseIso_naturality (φ : K ⟶ L) :
    (SSet.uliftFunctor.{max u v w, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, v, w} L).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, v, w} K).hom ≫
        (SSet.uliftFunctor.{max u v w, max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, w} φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, w} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, w} L) n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, v, w} L n.unop.len
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _ s.down)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, v, w} K n.unop.len s.down))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
