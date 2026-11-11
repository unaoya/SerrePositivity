module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapQuasiIso
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 一般 Hom 準同型な dg 関手の実充満忠実性

概要：全射性を要求しない Hom 準同型から dg nerve の実充満忠実性を得る。
方針：Hom 鎖写像の一般準同型不変性を、端点の厳密な輸送同型と合成する。
規約：対象の全射性も不要。使われ方：β3 の局所 Hom と β5 の準同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 一つの Hom 上の一般準同型は、その実 pinched 写像空間上の同値を与える。 -/
lemma dgFunctor_pinchedHomMap_quasiIso_equivalence (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x y : D)
    (hq : QuasiIso (F.map x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  let := hq
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x y) ≫ e.inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
    change _ = (_ ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence (F.map x y)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e.symm).isQCatEquivalence.isSimplicialHomotopyEquivalence

/-- 全射性を仮定しない Hom 準同型な dg 関手の native nerve は実充満忠実。 -/
theorem dgNerve_map_isFullyFaithful_of_quasiIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hq : HomQuasiIso F) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  intro x y
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  exact dgFunctor_pinchedHomMap_quasiIso_equivalence F x y (hq x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
