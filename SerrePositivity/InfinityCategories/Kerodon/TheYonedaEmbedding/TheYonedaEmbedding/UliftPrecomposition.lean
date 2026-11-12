module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：持ち上げた射の持ち上げた標的への前合成を、元の前合成の宇宙移送として比較する。
方針：内部 Hom の厳密な宇宙同型の自然性を全単体で計算する。
規約：大きい宇宙の任意の標的への弱同値性は要求しない。
使われ方：元の小さい単位から全空間余錐の全 Hom の同値性を検証する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：前合成は内部 Hom の宇宙同型と厳密に可換。
方針：全単体の関手の評価を比較する。
規約：始域・標的の Kan 性は不要。使われ方：元の前合成同値の移送。 -/
lemma uliftFunctorSpaceIso_pre {A B Z : SSet.{u}} (f : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} B Z).hom ≫
      (pre ((SSet.uliftFunctor.{v, u}).map f)).app ((SSet.uliftFunctor.{v, u}).obj Z) =
    (SSet.uliftFunctor.{v, u}).map ((pre f).app Z) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} A Z).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 概要：元の前合成がホモトピー同値なら、持ち上げた標的への前合成も同値。
方針：宇宙の同型の自然性と実際のホモトピー同値の持ち上げを使う。
規約：標的は元の Kan 複体の持ち上げ。使われ方：小さい単位の前合成同値の移送。 -/
lemma ulift_pre_homotopyEquivalence {A B Z : SSet.{u}} [KanComplex Z] (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((pre f).app Z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre ((SSet.uliftFunctor.{v, u}).map f)).app ((SSet.uliftFunctor.{v, u}).obj Z)) := by
  have hA := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} A Z)).isQCatEquivalence
  have hB := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} B Z)).isQCatEquivalence
  apply hB.isSimplicialHomotopyEquivalence.cancel_left
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} B Z).hom ≫
    (pre ((SSet.uliftFunctor.{v, u}).map f)).app ((SSet.uliftFunctor.{v, u}).obj Z))
  rw [uliftFunctorSpaceIso_pre]
  exact hf.ulift.comp hA.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
