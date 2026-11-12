module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CellContractible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessEmptyBase
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessSkeletonContractible

/-!
概要：標準単体と境界上の表現空間の可縮性から任意の底上の可縮性を得る。
方針：実際のセル付加で有限骨格を帰納し fibration 塔の極限へ渡す。
規約：標準単体と境界の局所的な可縮性は明示した入力とする。
使われ方：標準単体・境界の次元帰納法の大域への接続。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：空部分複体から始めた相対骨格は通常の骨格の底上の対象。
方針：相対骨格の範囲の項が空であることを消去する。
規約：部分複体の包含も構造射として保持する。
使われ方：セル付加の帰納法を骨格の逆極限へ渡す。 -/
lemma transportRelativeSkeleton_empty_eq (B : SSet.{u + 1}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRelativeSkeleton (⊥ : B.Subcomplex).ι n = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSkeletonOver B).obj n := by
  change Over.mk (skeletonOfMono (⊥ : B.Subcomplex).ι n).ι = Over.mk (B.skeleton n).ι
  have h : skeletonOfMono (⊥ : B.Subcomplex).ι n = B.skeleton n := by
    simp [skeletonOfMono, Subfunctor.range_ι]
  exact congrArg (fun T : B.Subcomplex ↦ Over.mk T.ι) h

/-- 概要：標準単体と境界での可縮性は空から始めた各相対骨格上の可縮性を与える。
方針：空の初段から実際のセル付加の可縮性保存で帰納する。
規約：各セルの底への分類射を固定して適用する。
使われ方：全ての有限骨格の可縮性の構成。 -/
lemma transportWitnessRelativeSkeleton_empty_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (hs : ∀ n (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk σ))))
    (hb : ∀ n (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk (∂Δ[n].ι ≫ σ)))))
    (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRelativeSkeleton (⊥ : B.Subcomplex).ι n))) := by
  induction n with
  | zero =>
    have h : skeletonOfMono (⊥ : B.Subcomplex).ι 0 = ⊥ := by
      simp [skeletonOfMono_zero, Subfunctor.range_ι]
    have he := congrArg (fun T : B.Subcomplex ↦ Over.mk T.ι) h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
      (Opposite.op (Over.mk (skeletonOfMono (⊥ : B.Subcomplex).ι 0).ι)))
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessEmptyBase_isContractibleKan p
  | succ n ih =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessRelativeSkeletonSucc_isContractibleKan p (⊥ : B.Subcomplex).ι n ih
      (fun c ↦ hs n c.map) (fun c ↦ hb n c.map)

/-- 概要：全ての標準単体とその境界上の局所可縮性から元の表現空間の可縮性を得る。
方針：有限骨格のセル帰納法とその fibration 塔の極限を続ける。
規約：局所可縮性の入力を未証明の結論に置き換えない。
使われ方：一般の底上の可縮性を標準単体・境界の問題へ還元する。 -/
lemma transportWitnessSpace_isContractibleKan_of_simplexes_and_boundaries
    {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (hs : ∀ n (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk σ))))
    (hb : ∀ n (σ : (Δ[n] : SSet.{u + 1}) ⟶ B), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op (Over.mk (∂Δ[n].ι ≫ σ))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_skeleton p
  intro n
  rw [← transportRelativeSkeleton_empty_eq B n]
  exact transportWitnessRelativeSkeleton_empty_isContractibleKan p hs hb n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
