module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：任意の底変換に対する全単体の共同切断評価の自然性。
方針：標準単体の定義域の比較と切断の豊穣的な底変換を共同実現する。
規約：全 left fibrations と全高次パラメーターを一つの関手同型で扱う。
使われ方：実際の straightening の任意の底変換との両立。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 関手の族の同型を二変数交換して同じ全パラメーターで比較する。 -/
def FunctorIso.transpose {A I X : SSet.{u}} {F G : A ⟶ (ihom I).obj X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A I X).hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIso (transpose)


/-- 族の始域の前合成は転置後に内部 Hom の制限になる。 -/
lemma transposeFunctorFamily_comp {A A' I X : SSet.{u}}
    (i : A' ⟶ A) (F : A ⟶ (ihom I).obj X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (i ≫ F) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily F ≫ (pre i).app X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre i F

/-- 全添字と全対象で共同実現した切断の底変換同型。 -/
def relativeSectionDiagramInfinityBaseChangeIso {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity A ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)).app
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionDiagramInfinity (A ⋙ Over.map k)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeRealizationIso k A).transpose
  rw [transposeFunctorFamily_comp] at e
  exact e

/-- 全単体の定義域は底の射での合成と厳密に両立する。 -/
lemma transportSimplexDomainFunctor_baseChange {B D : SSet.{u}} (k : D ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D ⋙ Over.map k := by
  refine CategoryTheory.Functor.ext (fun s ↦ ?_) ?_
  · change Over.mk (SSet.yonedaEquiv.symm (k.app _ s.unop.objDown.val)) =
      Over.mk (SSet.yonedaEquiv.symm s.unop.objDown.val ≫ k)
    exact congrArg Over.mk (SSet.yonedaEquiv_symm_comp _ k).symm
  · intro s t f
    apply Over.OverMorphism.ext
    simp
    rfl

/-- 全単体の共同切断評価は任意の底変換と関手同型で両立する。 -/
def transportSimplexSectionInfinity_baseChangeIso {B D : SSet.{u}} (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity D ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_reindex, transportSimplexDomainFunctor_baseChange]
  exact relativeSectionDiagramInfinityBaseChangeIso k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor D)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
