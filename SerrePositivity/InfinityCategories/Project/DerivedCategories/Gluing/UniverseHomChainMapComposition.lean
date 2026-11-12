module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseHomChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomChainMap

/-! 一般宇宙間の Hom 鎖写像の作用は、同じ対象宇宙内での前後合成を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} {D E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {x y : C} {x' y' : D} {x'' y'' : E}

lemma dgGluingUniverseHomChainMap_post
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y')
    (ψ : _root_.SerrePositivity.DifferentialGraded.homObject R D x' y' ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x'' y'') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} φ ≫
      (SSet.uliftFunctor.{max v r, max u w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ψ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} (φ ≫ ψ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x'' y'' n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex ψ
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} φ).app n s).down) = _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex ψ
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} φ).app n s).down) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (φ ≫ ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s.down)).toPinched)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_linear,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]
  apply Subtype.ext
  rfl

variable {T : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] {a b : T}

lemma dgGluingUniverseHomChainMap_pre
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R C x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T a b)
    (ψ : _root_.SerrePositivity.DifferentialGraded.homObject R T a b ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R D x' y') :
    (SSet.uliftFunctor.{max w r, max u v}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} ψ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, v, w, r} (φ ≫ ψ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x' y' n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap ψ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ s.down))).toPinched) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (φ ≫ ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s.down)).toPinched)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
