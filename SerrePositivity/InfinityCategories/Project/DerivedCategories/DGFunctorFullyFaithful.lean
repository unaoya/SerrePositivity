module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapTrivialFibration
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 全射 Hom 準同型な dg 関手の nerve の充満忠実性

概要：対象上全射性を仮定せず、全 Hom 上の全射準同型から充満忠実性を得る。
方針：写像空間の射を Hom 鎖写像の射と同定し、実際の全相対境界を充填する。
規約：充満忠実性は Core の実写像空間による定義。使われ方：β3 の前三角化との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 標準頂点間の実際の写像空間への作用は自明 Kan fibration。 -/
lemma dgFunctor_pinchedHomMap_trivialKanFibration (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : _root_.SerrePositivity.DifferentialGraded.HomQuasiIso F) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_trivialKanFibration (F.map x y) (hs x y) (hq x y)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x y) ≫ e.inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
    change _ = (_ ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  constructor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)

/-- 対象上全射性を要しない、全射 Hom 準同型な dg 関手の nerve の充満忠実性。 -/
lemma dgNerve_map_isFullyFaithful_of_surjective_quasiIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  intro x y
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  let := dgFunctor_pinchedHomMap_trivialKanFibration F hs hq x y
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

/-- Hom 複体上の同型を持つ dg 関手は実際の ∞ 写像空間で充満忠実。 -/
lemma dgNerve_map_isFullyFaithful_of_homIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    (hi : ∀ x y, IsIso (F.map x y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  apply dgNerve_map_isFullyFaithful_of_surjective_quasiIso F
  · intro x y i
    let := hi x y
    exact (ConcreteCategory.bijective_of_isIso ((F.map x y).f i)).2
  · intro x y
    let := hi x y
    infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
