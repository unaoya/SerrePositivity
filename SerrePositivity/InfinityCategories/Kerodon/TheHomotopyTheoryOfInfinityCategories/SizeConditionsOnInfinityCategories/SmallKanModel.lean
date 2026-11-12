module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallPointWitnessContractible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplexFibers

/-!
概要：大きい Kan 複体が小さい Kan 模型を持つという、同値不変な小ささの条件。
方針：小さい Kan 複体の宇宙持ち上げとの実際の圏同値を使う。
規約：元の単体の集合が各次数で小さいことは要求しない。
使われ方：essentially small な fiber の相対表現への延長。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 大きい Kan 複体が、元の宇宙の Kan 複体と同値であるという条件。 -/
def HasSmallKanModel (X : SSet.{u + 1}) [Quasicategory X] : Prop :=
  ∃ K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K.obj) X)

/-- 小さい Kan 模型を持つという条件は、同じ大きい宇宙の圏同値で保たれる。 -/
lemma HasSmallKanModel.of_equivalence {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (h : HasSmallKanModel X) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    HasSmallKanModel Y := by
  obtain ⟨K, ⟨d⟩⟩ := h
  exact ⟨K, ⟨d.trans e⟩⟩

/-- 実際に各次数で小さい Kan 複体は、次数ごとの縮小から小さい Kan 模型を持つ。 -/
lemma hasSmallKanModel_of_small (X : SSet.{u + 1}) [KanComplex X]
    [∀ n, Small.{u} (X.obj n)] : HasSmallKanModel X := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} X
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} X
  have : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj K) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso e.symm
  have : KanComplex K := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.kanComplex_of_ulift.{u + 1, u} K
  exact ⟨⟨K, inferInstance⟩, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e⟩⟩

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 各頂点上の実際の Kan fiber が小さい Kan 模型を持つという条件。 -/
def HasEssentiallySmallFibers {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : Prop :=
  ∀ b, HasSmallKanModel (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)

/-- 既存の次数 fiber の小ささは、同値不変な fiber の小ささを含意する。 -/
lemma HasSmallSimplexFibers.essentiallySmall {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) :
    HasEssentiallySmallFibers p := by
  intro b
  have (n : SimplexCategoryᵒᵖ) : Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).obj n) :=
    hp n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n.unop.len)
  exact hasSmallKanModel_of_small _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
