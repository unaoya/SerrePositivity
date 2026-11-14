module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.FibrationTowerLimitCone

/-!
概要：可縮 Kan 複体の fibration 塔の厳密な極限は可縮 Kan。
方針：遷移の同値性から全境界充填を得て既存の塔の逐次持ち上げを使う。
規約：任意の厳密極限の可縮性は主張しない。
使われ方：骨格ごとの表現空間の可縮性から一般の底へ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：可縮 Kan 複体間の Kan fibration は trivial Kan fibration。
方針：終対象への二つの同値の二対三則を使う。
規約：始域と終域の可縮性をともに要求する。
使われ方：骨格逆系の遷移の全境界充填。 -/
lemma trivialKanFibration_of_fibration_of_contractible {X Y : SSet.{u}}
    (f : X ⟶ Y) [Fibration f] (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f := by
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (⊤_ SSet.{u}) :=
    fun n b ↦ ⟨terminal.from _, terminal.hom_ext _ _⟩
  have := hT.kanComplex
  have := hX.kanComplex
  have := hY.kanComplex
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration X).mp hX
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration Y).mp hY
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ≫ terminal.from Y) := by
    rw [show f ≫ terminal.from Y = terminal.from X from terminal.hom_ext _ _]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_isQCatEquivalence f
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (terminal.from Y)).cancel_right he)

/-- 概要：全境界充填を持つ遷移の塔の初段射影は全境界充填を持つ。
方針：既存の逐次持ち上げを各境界包含に適用する。
規約：初段の可縮性はまだ不要。
使われ方：塔の極限の可縮性の相対部分。 -/
lemma contractibleTower_projection_trivialKanFibration (X : ℕ → SSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (d n)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have : ∀ k, HasLiftingProperty (boundary n).ι (d k) :=
    fun k ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := d k)) (boundary n).ι inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_zero_hasLiftingProperty
    X d (boundary n).ι

/-- 概要：可縮な初段と全境界充填を持つ遷移の塔の具体的極限は可縮。
方針：初段で境界を充填し初段射影の持ち上げで極限へ戻す。
規約：逐次の整合条件を厳密に保持する。
使われ方：任意の極限錐への同型による可縮性の移送。 -/
lemma isContractibleKan_fibrationTowerLimit (X : ℕ → SSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (d n)]
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (X 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit X d) := by
  have := contractibleTower_projection_trivialKanFibration X d
  intro n b
  obtain ⟨F, hF⟩ := h0 n
    (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0)
  have sq : CommSq b (boundary n).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0) F := ⟨hF.symm⟩
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection X d 0))
    (boundary n).ι inferInstance
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可縮 Kan 複体の Kan fibration 塔の任意の厳密な極限は可縮。
方針：遷移を trivial Kan fibration に昇格し具体的な塔の極限から同型で移す。
規約：全ての遷移の fibration 性が必要。
使われ方：骨格上の表現空間の可縮性から大域の可縮性を導く。 -/
lemma isContractibleKan_of_fibrationTowerCone {D : ℕᵒᵖ ⥤ SSet.{u}} (c : Cone D)
    (hc : IsLimit c) (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (D.obj (Opposite.op n)))
    [∀ n, Fibration (D.map (homOfLE (Nat.le_succ n)).op)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan c.pt := by
  have : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (D.map (homOfLE (Nat.le_succ n)).op) :=
    fun n ↦ trivialKanFibration_of_fibration_of_contractible _ (h (n + 1)) (h n)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit D).conePointUniqueUpToIso hc)
    (isContractibleKan_fibrationTowerLimit (fun n ↦ D.obj (Opposite.op n))
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) (h 0))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
