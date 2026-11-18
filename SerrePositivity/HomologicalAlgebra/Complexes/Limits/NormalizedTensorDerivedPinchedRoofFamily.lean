module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDerivedPinchedRoof
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedAmbientVertices
/-! 概要：導来 pinched 全族と元の roof 族を同じ端点表示で比較する。
方針：同じ Arrow 等式を明示的な端点輸送で関手圏内の等式へ戻す。
規約：全 K を保持。使われ方：標準単位比較の全族の検出。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
private lemma arrow_transport_of_eq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) (g : x' ⟶ y')
    (h : Arrow.mk f = Arrow.mk g) : eqToHom hx.symm ≫ f ≫ eqToHom hy = g := by
  cases hx
  cases hy
  obtain ⟨_, _, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hh

lemma normalizedTensorDerivedPinchedFamily_eq_roof :
    let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
    let V := fun z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌ =>
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z))
    eqToHom (congrArg V (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A X)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedPinchedMap A X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
          ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
          ((_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))) ≫
      eqToHom (congrArg V (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A Y).symm) =
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A X Y := by
  let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
  let V := fun z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌ =>
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z))
  exact _root_.SerrePositivity.ComplexLimits.arrow_transport_of_eq
    (congrArg V (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A X).symm)
    (congrArg V (_root_.SerrePositivity.ComplexLimits.complexOrdinaryAmbient_vertex A Y).symm) _ _
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorDerivedPinchedFamily_arrow A X Y).trans
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily_arrow A X Y).symm)

end SerrePositivity.ComplexLimits
