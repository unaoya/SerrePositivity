module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessPushout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessDescentFibrations
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ContractibleKanTower

/-!
概要：セルの貼り合わせで表現空間の可縮性を保つ判定。
方針：可縮な Kan 複体間の fibration を trivial Kan fibration として pullback する。
規約：貼り合わせの一方の脚の単射性を要求する。
使われ方：有限骨格の可縮性のセルによる帰納法。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-- 概要：trivial Kan fibration の可縮な終域から始域の可縮性を得る。
方針：終域で充填した境界を全境界の持ち上げで始域へ戻す。
規約：始域の Kan 性を追加の仮定にしない。
使われ方：pullback と塔の可縮性の移送。 -/
lemma isContractibleKan_of_trivialKanFibration {X Y : SSet.{u}}
    (f : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f] (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X := by
  intro n b
  obtain ⟨F, hF⟩ := hY n (b ≫ f)
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := f)) (boundary n).ι inferInstance
  have sq : CommSq b (boundary n).ι f F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可縮 Kan 複体の fibration を含む pullback は可縮。
方針：右辺を trivial Kan fibration に昇格して左辺へ底変換する。
規約：三つの入力空間の可縮性を全て必要とする。
使われ方：表現空間のセル貼り合わせ。 -/
lemma isContractibleKan_of_isPullback_of_fibration {W X Y Z : SSet.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : IsPullback f g h i) [Fibration h]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Y) (hZ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan W := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trivialKanFibration_of_fibration_of_contractible h hX hZ
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration g :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback sq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := h))⟩
  exact isContractibleKan_of_trivialKanFibration g hY

/-- 概要：単射に沿う底上の pushout で三つの表現空間が可縮なら貼り合わせ後も可縮。
方針：降下の pullback と単射の制限の fibration 性を組み合わせる。
規約：非空な頂点だけの貼り合わせに弱めない。
使われ方：境界と標準単体のセル付加による可縮性の帰納法。 -/
lemma transportWitnessPushout_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a x y z : Over B}
    {f : a ⟶ x} {g : a ⟶ y} {h : x ⟶ z} {i : y ⟶ z}
    (hs : IsPushout f g h i) [Mono f.left]
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op a)))
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op x)))
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor p).obj (Opposite.op z)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor_map_fibration p f
  exact isContractibleKan_of_isPullback_of_fibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessPullbackFunctor_map_pushout p hs) hx hy ha

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories
