module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCounitSpaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedMap
/-!
概要：実余単位の普遍写像を、元の dg nerve 射の実 pinched Hom 作用へ戻す。
方針：像の実端点を比較し、同じ全 Hom 鎖写像の自然性と後合成を合成する。
規約：元の全写像空間の射を保持する。使われ方：普遍矢印の comma 条件への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  {G : DGFunctor R C E} {y : E} (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E G y)
/-- 同じ普遍余単位の全 Hom 写像は、元の実 dg nerve 射の作用と同じ閉後合成。 -/
lemma DGUniversalCounit.pinchedMap_eq_native (x : C) : e.pinchedMap x =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex e.source) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex G x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex G e.source)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R E (x := G.obj x) e.counit := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
  exact e.pinchedMap_eq x
/-- 元の実 dg nerve 射の作用に同じ余単位を後合成する写像は全 Hom 空間の同値。 -/
lemma DGUniversalCounit.nativePinchedMap_isSimplicialHomotopyEquivalence (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex e.source) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex G x)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex G e.source)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R E (x := G.obj x) e.counit) := by
  rw [← e.pinchedMap_eq_native x]
  exact e.pinchedMap_isSimplicialHomotopyEquivalence x
end SerrePositivity.InfinityCategories.Project.DerivedCategories
