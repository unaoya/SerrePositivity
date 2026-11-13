module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Prisms.ComplexCochainPrismUniverseLinear
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexFamilies

/-! 同じ複体 cochain prism の全時間族は、canonical な対象宇宙変更と可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet

open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L : _root_.SerrePositivity.DifferentialGraded.Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingComplexCochainPrism_universe_naturality :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v, max u v w r} 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max u v, max u w, r} L).hom =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max u v, max u w, r} K).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u w, max u v w r} 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, w} f g h he) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, s⟩
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, max u w} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, max u w} L) n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} L n
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he).app (Opposite.op ⦋n⦌)
          (ULift.up β.down, s.down))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, w} f g h he).app (Opposite.op ⦋n⦌)
        (ULift.up β.down, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max u v, max u w} K n s.down))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainPrism_universe_linear.{u, v, w} f g h he s.down
    (stdSimplex.objEquiv β).toOrderHom

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
