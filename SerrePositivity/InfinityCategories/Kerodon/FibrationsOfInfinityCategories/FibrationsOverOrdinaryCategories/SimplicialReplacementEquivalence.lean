module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveMapComparison

/-!
概要：係数の対象ごとの同値による simplicial replacement の不変性。
方針：taut scaffold の自然性で weighted nerve の同値へ移す。
規約：係数は Kan 値の通常の図式とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な変換空間の前合成による同値不変性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：各対象で同値な係数の自然変換は replacement 間の前合成同値を誘導する。
方針：両側の taut scaffold を用い、weighted nerve の同値から二対三則で戻す。
規約：replacement 自体の quasicategory 性を仮定しない。
使われ方：Kerodon §5.3.4（Tag 036V）、Corollary 5.6.0.6（Tag 028T）、相対関手空間による図式の同値判定。 -/
lemma simplicialReplacementMap_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {F G : C ⥤ SSet.{u}}
    [∀ c, KanComplex (F.obj c)] [∀ c, KanComplex (G.obj c)]
    (η : F ⟶ G) (hη : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap η) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence G).cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_map]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence F).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_isPrecompositionEquivalence η hη)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
