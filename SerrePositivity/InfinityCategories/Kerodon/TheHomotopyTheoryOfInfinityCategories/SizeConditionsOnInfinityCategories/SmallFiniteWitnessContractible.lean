module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDimensionStep
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessFiniteDimension

/-!
概要：次数ごとに小さい全空間を持つ有限次元の底上の表現空間は可縮。
方針：底の次元の帰納法で標準単体・境界の局所入力を証明してセルの還元へ渡す。
規約：局所的な可縮性を追加仮定として残さない。
使われ方：任意の底の標準単体と境界上での可縮性の主入力。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：各次数で小さい全空間の有限次元の底上の表現空間は可縮 Kan。
方針：次元の帰納法と点・区間・内ホーンの局所段階を実際のセル帰納法へ適用する。
規約：表現の存在や境界の可縮性を追加仮定にしない。
使われ方：一般の底上の表現空間の可縮性へ進む。 -/
lemma smallFiniteTransportWitnessSpace_isContractibleKan (N : ℕ) :
    ∀ {E B : SSet.{u + 1}} [∀ m, Small.{u} (E.obj m)]
      (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [B.HasDimensionLT N],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  induction N with
  | zero =>
    intro E B hSmall p hp hdim
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_finiteDimension p 0
    · intro n hn
      omega
    · intro n hn
      omega
  | succ N ih =>
    intro E B hSmall p hp hdim
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_finiteDimension p (N + 1)
    · intro n hn σ
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst σ p))
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst σ p) :=
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst σ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
      have : ∀ m, Small.{u} ((pullback σ p).obj m) :=
        fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small σ p m
      obtain hlt | heq := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn)
      · have : (Δ[n] : SSet.{u + 1}).HasDimensionLT N :=
          (Δ[n] : SSet.{u + 1}).hasDimensionLT_of_le (n + 1) N (by omega)
        exact ih (pullback.fst σ p)
      · subst n
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.simplexTransportWitnessSpace_isContractibleKan_of_lowerDimension N ih
          (pullback.fst σ p)
    · intro n hn σ
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst (∂Δ[n].ι ≫ σ) p))
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst (∂Δ[n].ι ≫ σ) p) :=
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst _ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
      have : ∀ m, Small.{u} ((pullback (∂Δ[n].ι ≫ σ) p).obj m) :=
        fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small _ p m
      have : (boundary n : SSet.{u + 1}).HasDimensionLT N :=
        (boundary n : SSet.{u + 1}).hasDimensionLT_of_le n N (Nat.le_of_lt_succ hn)
      exact ih (pullback.fst (∂Δ[n].ι ≫ σ) p)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
