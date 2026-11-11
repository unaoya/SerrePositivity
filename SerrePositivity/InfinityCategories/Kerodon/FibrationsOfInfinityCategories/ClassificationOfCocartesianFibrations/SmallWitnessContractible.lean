module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallFiniteWitnessContractible

/-!
概要：次数ごとに小さい全空間を持つ任意の底上の表現空間は可縮 Kan。
方針：標準単体と境界への底変換に有限次元の定理を適用しセル帰納法へ渡す。
規約：底の有限次元性や次数ごとの小ささは仮定しない。
使われ方：一般の境界固定延長と表現の選択独立性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：各次数で小さい全空間を持つ任意の left fibration の表現空間は可縮 Kan。
方針：有限次元の標準単体・境界での可縮性を実際のセル帰納法で大域へ貼る。
規約：表現の存在も底の小ささも追加仮定にしない。
使われ方：Kerodon Theorem 5.6.8.3（Tag 02SC） の全空間が次数ごとに小さい場合。 -/
lemma smallTransportWitnessSpace_isContractibleKan {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessSpace_isContractibleKan_of_simplexes_and_boundaries p
  · intro n σ
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst σ p))
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst σ p) :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst σ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
    have : ∀ m, Small.{u} ((pullback σ p).obj m) :=
      fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small σ p m
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.smallFiniteTransportWitnessSpace_isContractibleKan (n + 1) (pullback.fst σ p)
  · intro n σ
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.fst (∂Δ[n].ι ≫ σ) p))
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst (∂Δ[n].ι ≫ σ) p) :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst _ p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
    have : ∀ m, Small.{u} ((pullback (∂Δ[n].ι ≫ σ) p).obj m) :=
      fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small _ p m
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.smallFiniteTransportWitnessSpace_isContractibleKan n (pullback.fst (∂Δ[n].ι ≫ σ) p)

/-- 概要：各次数で小さい全空間を持つ left fibration は実際の表現を持つ。
方針：可縮な表現空間の頂点を実際の表現へ戻す。
規約：分類図式と全空間の写像を同時に構成する。
使われ方：相対境界延長を指定する前の絶対的な存在。 -/
lemma smallLeftTransportRepresentation_nonempty {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) := by
  obtain ⟨v⟩ := (smallTransportWitnessSpace_isContractibleKan p).nonempty
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertexEquiv p).symm v⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
