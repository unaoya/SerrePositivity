module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

public import SerrePositivity.KST.Spectra.D3LoopedSectionComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：全関手空間の curry 後の図式評価を、元の指定係数への制限へ戻す。
方針：curry の同じ全単体作用と評価の交換を使い、指定関手同型の値を保つ。
規約：成分を選び直さない。使われ方：二方向模型比較の始点・終点の指定値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 全関手空間の curry 後に図式の角を評価すると、同じ元の係数制限になる。 -/
lemma d3FunctorSpaceCurryMap_post_evaluate {A B X : SSet.{u}} (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫ (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) =
      (pre (lift (SSet.const a) (𝟙 B))).app X := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hp : lift (SSet.const a) (𝟙 (B ⊗ (ihom (A ⊗ B)).obj X)) ≫
      (α_ A B ((ihom (A ⊗ B)).obj X)).inv =
    lift (SSet.const a) (𝟙 B) ▷ ((ihom (A ⊗ B)).obj X) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hp]
  exact (MonoidalClosed.uncurry_pre (lift (SSet.const a) (𝟙 B)) X).symm

/-- 指定関手同型の curry 後の角評価は、同じ元の係数への制限そのもの。 -/
lemma d3FunctorIso_curry_postcomp_evaluate {A B X : SSet.{u}} [Quasicategory X]
    {f g : A ⊗ B ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (a : A _⦋0⦌) :
    HEq (e.curry.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a))
      (e.precomp (lift (SSet.const a) (𝟙 B))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.vertexIso_map_heq_of_heq e.curry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex f).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex g).symm
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_curry_heq_map e) ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a))
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
  refine h.trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_comp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_heq e (d3FunctorSpaceCurryMap_post_evaluate a)

end SerrePositivity.KST.Spectra
