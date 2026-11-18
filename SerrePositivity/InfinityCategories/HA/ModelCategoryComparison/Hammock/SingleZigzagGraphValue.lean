module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagNativeDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.NerveWeakTransport

/-!
# 元の単一列の graph と離散 Hom の弱同値

概要：同じ始終点の元の単一列を評価する。
方針：端点移送と離散圏の nerve の同型を使う。
規約：モデル構造を要求しない。
使われ方：DK5.7の単一列の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative] {X Y : C}
def _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y) :=
  nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.toDiscrete ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso (X ⟶ Y)).hom
lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue_app (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue.app n) σ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (σ.obj 0) := rfl
lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardZigzag.graphValue (W := W) (X := X) (Y := Y)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.nerveMap_equivalence_isWeakHomotopyEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.discreteEquivalence).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso (X ⟶ Y))).isWeakHomotopyEquivalence

def _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj ((⟨Y⟩ : WideSubcategory W) ⟶ ⟨X⟩) :=
  nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nativeDiscreteEquivalence.functor ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso _).hom
lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue_app (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue.app n) σ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (σ.obj 0)) := rfl
lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BackwardZigzag.graphValue (W := W) (X := X) (Y := Y)) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.nerveMap_equivalence_isWeakHomotopyEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nativeDiscreteEquivalence).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso _)).isWeakHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
