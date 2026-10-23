module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessPushout
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessDescentFibrations
public import SerrePositivity.InfinityCategories.F1.Limits.ContractibleKanTower

/-!
概要：セルの貼り合わせで表現空間の可縮性を保つ判定。
方針：可縮な Kan 複体間の fibration を trivial Kan fibration として pullback する。
規約：貼り合わせの一方の脚の単射性を要求する。
使われ方：有限骨格の可縮性のセルによる帰納法。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration の可縮な終域から始域の可縮性を得る。
方針：終域で充填した境界を全境界の持ち上げで始域へ戻す。
規約：始域の Kan 性を追加の仮定にしない。
使われ方：pullback と塔の可縮性の移送。 -/
lemma isContractibleKan_of_trivialKanFibration {X Y : SSet.{u}}
    (f : X ⟶ Y) [TrivialKanFibration f] (hY : IsContractibleKan Y) :
    IsContractibleKan X := by
  intro n b
  obtain ⟨F, hF⟩ := hY n (b ≫ f)
  have := (TrivialKanFibration.mem (p := f)) (boundary n).ι inferInstance
  have sq : CommSq b (boundary n).ι f F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可縮 Kan 複体の fibration を含む pullback は可縮。
方針：右辺を trivial Kan fibration に昇格して左辺へ底変換する。
規約：三つの入力空間の可縮性を全て必要とする。
使われ方：表現空間のセル貼り合わせ。 -/
lemma isContractibleKan_of_isPullback_of_fibration {W X Y Z : SSet.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (sq : IsPullback f g h i) [Fibration h]
    (hX : IsContractibleKan X) (hY : IsContractibleKan Y) (hZ : IsContractibleKan Z) :
    IsContractibleKan W := by
  have := trivialKanFibration_of_fibration_of_contractible h hX hZ
  have : TrivialKanFibration g :=
    ⟨trivialKanFibrations.of_isPullback sq (TrivialKanFibration.mem (p := h))⟩
  exact isContractibleKan_of_trivialKanFibration g hY

/-- 概要：単射に沿う底上の pushout で三つの表現空間が可縮なら貼り合わせ後も可縮。
方針：降下の pullback と単射の制限の fibration 性を組み合わせる。
規約：非空な頂点だけの貼り合わせに弱めない。
使われ方：境界と標準単体のセル付加による可縮性の帰納法。 -/
lemma transportWitnessPushout_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] {a x y z : Over B}
    {f : a ⟶ x} {g : a ⟶ y} {h : x ⟶ z} {i : y ⟶ z}
    (hs : IsPushout f g h i) [Mono f.left]
    (ha : IsContractibleKan ((transportWitnessPullbackFunctor p).obj (Opposite.op a)))
    (hx : IsContractibleKan ((transportWitnessPullbackFunctor p).obj (Opposite.op x)))
    (hy : IsContractibleKan ((transportWitnessPullbackFunctor p).obj (Opposite.op y))) :
    IsContractibleKan ((transportWitnessPullbackFunctor p).obj (Opposite.op z)) := by
  have := transportWitnessPullbackFunctor_map_fibration p f
  exact isContractibleKan_of_isPullback_of_fibration
    (transportWitnessPullbackFunctor_map_pushout p hs) hx hy ha

end SerrePositivity.InfinityCategories
