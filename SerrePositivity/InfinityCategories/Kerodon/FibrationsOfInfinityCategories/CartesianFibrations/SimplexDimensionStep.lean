module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SmallPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallPointWitnessContractible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalWitnessBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessInnerAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.WitnessPushoutContractible
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：低次元の底上の可縮性から標準単体上の可縮性を得る。
方針：点・区間・高次の内ホーンを分け既証明の相対充填を使う。
規約：全空間の小ささを全ての底変換で確認する。
使われ方：有限次元の底の可縮性の次元帰納法の局所段階。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

local instance simplexDimensionPullbackSndLF {E B D : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：次元 n 未満の底での可縮性は n 次元標準単体上の可縮性を与える。
方針：零次元は点、一次元は境界制限、二次元以上は内ホーン制限を使う。
規約：全空間は各次数で宇宙 u に小さい。
使われ方：セル帰納法に必要な最上次元の局所入力。 -/
lemma simplexTransportWitnessSpace_isContractibleKan_of_lowerDimension (n : ℕ)
    (ih : ∀ {E B : SSet.{u + 1}} [∀ m, Small.{u} (E.obj m)]
      (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [B.HasDimensionLT n],
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p))
    {E : SSet.{u + 1}} [∀ m, Small.{u} (E.obj m)]
    (p : E ⟶ (Δ[n] : SSet.{u + 1})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  rcases n with _ | n
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointTransportWitnessSpace_isContractibleKan p
  rcases n with _ | n
  · have : ∀ m, Small.{u} ((pullback p (boundary 1).ι).obj m) :=
      fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small p (boundary 1).ι m
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.intervalWitnessRestriction_trivialKanFibration p
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p (boundary 1).ι)
      (ih (pullback.snd p (boundary 1).ι))
  · let j : Fin (n + 3) := 1
    have : ∀ m, Small.{u} ((pullback p (horn (n + 2) j).ι).obj m) :=
      fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small p (horn (n + 2) j).ι m
    have hj : innerAnodyneExtensions (horn (n + 2) j).ι :=
      innerAnodyneExtensions.horn_ι (by
        change 0 < 1 % (n + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega) (by
        change 1 % (n + 3) < n + 2
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_trivialKanFibration_of_innerAnodyne p
      (horn (n + 2) j).ι hj
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_trivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p (horn (n + 2) j).ι)
      (ih (pullback.snd p (horn (n + 2) j).ι))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
