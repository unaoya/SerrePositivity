module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullSubcategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroDiagramComparison

/-! # dg 商の指定部分圏上での整合的な零化

概要：商包含を指定充満部分圏に制限すると、零対象の定値 ∞ 関手と同型になる。
方針：全ての頂点の実零対象性から、関手 ∞ 圏の終対象性による比較を作る。
規約：全図式の可逆二胞体を与える。局所化普遍性は別工程。使われ方：β3 の Verdier 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 商包含の指定充満部分圏への制限。 -/
def dgQuotientNullFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion A D P).comp (DGQuotient.inclusion A D P))

/-- 制限した関手は二つの実際の包含関手の合成。 -/
lemma dgQuotientNullFunctor_eq_comp : dgQuotientNullFunctor A D P =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _

/-- 指定部分圏上の制限関手の値は全て実際の零頂点。 -/
lemma dgQuotientNullFunctor_pointwise_zero (k : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      ((dgQuotientNullFunctor A D P).app _ k) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective k
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledVertex_isZero A D P x

/-- 指定部分圏上の制限は、零対象の定値関手と関手 ∞ 圏で同型。 -/
def dgQuotientNullFunctorIsoZero (b : P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgQuotientNullFunctor A D P)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledZeroVertex A D P b).vertex) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramConstantIso _ (dgQuotientNullFunctor_pointwise_zero A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledZeroVertex A D P b)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
