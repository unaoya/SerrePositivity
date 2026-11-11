module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.InnerAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.TrivialKanFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TrivialFibrationCofinality

/-!
概要：小さい right cofinal map は宇宙を持ち上げても同じ写像として right cofinal。
方針：生成ホーンの移送で right anodyne 性を保ち、同じ因子分解の trivial Kan 後因子と合成する。
規約：大きい標的への cofinal 性を追加仮定にしない。
使われ方：小さい cofinal poset を宇宙 u+1 の前層図式へ適用する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ右ホーンの宇宙持ち上げは、同じ番号の生成射と同型。 -/
lemma rightHornInclusions_ulift : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.{u} ≤
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.{max u v}.inverseImage (SSet.uliftFunctor.{v, u}) := by
  intro X Y f hf
  obtain @⟨n, i, h0⟩ := hf
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornArrowIso.{v, u} (n + 1) i)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn i h0)

/-- 宇宙持ち上げは元の right anodyne 射を保つ。 -/
lemma rightAnodyneExtensions_ulift {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((SSet.uliftFunctor.{v, u}).map f) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.{u}.HasSmallObjectArgument.{u} := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightHornFamily_eq]
    infer_instance
  exact ModelGeneration.generatedLeft_map (SSet.uliftFunctor.{v, u})
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions rightHornInclusions_ulift f hf

/-- 元の小さい right cofinal map を持ち上げた同じ写像も right cofinal。 -/
lemma isRightCofinal_ulift {A B : SSet.{u}} (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal ((SSet.uliftFunctor.{v, u}).map f) := by
  obtain ⟨Z, j, p, hm, hj, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((SSet.uliftFunctor.{v, u}).map p) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.trivialKanFibration_uliftFunctor_map p
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ (rightAnodyneExtensions_ulift j hj)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration ((SSet.uliftFunctor.{v, u}).map p))
  rw [← CategoryTheory.Functor.map_comp, he] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
