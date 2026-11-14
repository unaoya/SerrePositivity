module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoCurryPresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeFunctorCurryIsoPresentation

/-!
概要：元の指定同型の curry の一点成分を、元の同じ係数への制限に同定する。
方針：全関手空間の curry と評価の厳密な交換を用いる。
規約：指定比較を保持。使われ方：全三角形の輸送比較の一点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 全関手空間の curry の一点評価は、同じ係数を固定する前合成。 -/
lemma functorSpaceCurryMap_evaluate {A B X : SSet.{u}} (l : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l =
      (pre (lift (𝟙 A) (SSet.const l))).app X := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    uncurry_natural_left, uncurry_curry]
  have hp : (A ◁ lift (SSet.const l) (𝟙 ((ihom (A ⊗ B)).obj X))) ≫
      (α_ A B ((ihom (A ⊗ B)).obj X)).inv =
      lift (𝟙 A) (SSet.const l) ▷ ((ihom (A ⊗ B)).obj X) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hp]
  exact (MonoidalClosed.uncurry_pre (lift (𝟙 A) (SSet.const l)) X).symm

/-- 元の指定同型の curry の一点成分は、同じ係数で制限した元の指定同型。 -/
lemma functorIso_curry_app_heq_precomp {A B X : SSet.{u}}
    [Quasicategory B] [Quasicategory X] {f g : A ⊗ B ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (l : B _⦋0⦌) :
    HEq (e.curry.app l) (e.precomp (lift (𝟙 A) (SSet.const l))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.vertexIso_map_heq_of_heq e.curry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex f).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex g).symm
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_curry_heq_map e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l)
  refine (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIso_app_heq_evaluate e.curry l).trans (h.trans ?_)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_comp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_heq e (functorSpaceCurryMap_evaluate l)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
