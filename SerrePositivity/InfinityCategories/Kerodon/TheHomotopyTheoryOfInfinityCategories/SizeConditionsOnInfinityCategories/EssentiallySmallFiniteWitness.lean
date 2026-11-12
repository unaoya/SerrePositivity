module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.EssentiallySmallSimplexWitness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessFiniteDimension

/-!
概要：essentially small fiber を持つ有限次元の底上の実際の表現空間は可縮 Kan。
方針：全ての標準単体と境界への底変換で同じ fiber 条件を保ち、次元で帰納する。
規約：底も全空間も次数ごとに小さい必要はない。
使われ方：任意の底と大きいパラメーターに対する相対表現の延長。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 有限次元の任意の底上の表現空間は、fiber の小さい Kan 模型だけから可縮になる。 -/
lemma essentiallySmallFiniteTransportWitnessSpace_isContractibleKan (N : ℕ) :
    ∀ {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [B.HasDimensionLT N],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p → _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  induction N with
  | zero =>
    intro E B p hp hdim hsmall
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_finiteDimension p 0
    · intro n hn
      omega
    · intro n hn
      omega
  | succ N ih =>
    intro E B p hp hdim hsmall
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_finiteDimension p (N + 1)
    · intro n hn σ
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst σ p))
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst σ p) :=
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst σ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
      have hs := hsmall.pullback_fst σ
      obtain hlt | heq := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn)
      · have : (Δ[n] : SSet.{u + 1}).HasDimensionLT N :=
          (Δ[n] : SSet.{u + 1}).hasDimensionLT_of_le (n + 1) N (by omega)
        exact ih (pullback.fst σ p) hs
      · subst n
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.essentiallySmallSimplexWitnessSpace_isContractibleKan_of_lowerDimension N ih
          (pullback.fst σ p) hs
    · intro n hn σ
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst (∂Δ[n].ι ≫ σ) p))
      have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst (∂Δ[n].ι ≫ σ) p) :=
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst _ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
      have : (boundary n : SSet.{u + 1}).HasDimensionLT N :=
        (boundary n : SSet.{u + 1}).hasDimensionLT_of_le n N (Nat.le_of_lt_succ hn)
      exact ih (pullback.fst (∂Δ[n].ι ≫ σ) p) (hsmall.pullback_fst (∂Δ[n].ι ≫ σ))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
