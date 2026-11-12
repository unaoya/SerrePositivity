module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessDescentLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：空の部分複体上の表現空間は可縮。
方針：底上の始対象を反変の極限保存で終対象へ写す。
規約：全空間の小ささや表現の非空性を仮定しない。
使われ方：骨格の帰納法の初段。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：空部分複体の包含は底上の圏の始対象。
方針：空部分複体からの射の一意性を底上の射へ持ち上げる。
規約：標準の初対象の選択には依存しない。
使われ方：表現空間の反変性で終対象を得る。 -/
def transportEmptyOver_isInitial (B : SSet.{u + 1}) :
    IsInitial (Over.mk (⊥ : B.Subcomplex).ι) := by
  refine IsInitial.ofUniqueHom (fun a ↦ Over.homMk (Subcomplex.isInitialBot.to a.left)
    (by apply Subcomplex.isInitialBot.hom_ext)) ?_
  intro a f
  apply Over.OverMorphism.ext
  exact Subcomplex.isInitialBot.hom_ext _ _

/-- 概要：単体集合の終対象は可縮 Kan。
方針：境界からの射と延長を終対象への射の一意性で同定する。
規約：全ての次元の境界を含む。
使われ方：空の底上の表現空間の可縮性。 -/
lemma isContractibleKan_of_isTerminal {K : SSet.{u}} (h : IsTerminal K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K := fun _ _ ↦ ⟨h.from _, h.hom_ext _ _⟩

/-- 概要：空部分複体における降下関手の表現空間は可縮 Kan。
方針：底上の始対象を反対にして極限保存で終対象へ写す。
規約：宇宙の小ささの追加条件はない。
使われ方：有限骨格の可縮性の帰納法の初期値。 -/
lemma transportWitnessEmptyBase_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj
      (Opposite.op (Over.mk (⊥ : B.Subcomplex).ι))) :=
  isContractibleKan_of_isTerminal
    ((transportEmptyOver_isInitial B).op.isTerminalObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
