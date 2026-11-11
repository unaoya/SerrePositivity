module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PullbackSimplex

/-!
概要：各次数で小さい二つの全空間の pullback は各次数で小さい。
方針：二射影で単体を積へ単射に符号化する。
規約：底の小ささや射影の充填性は不要。
使われ方：標準単体・境界・内ホーンへの底変換での宇宙の制御。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：二つの射の始域の指定次数が小さければ pullback の同じ次数も小さい。
方針：第一・第二射影の組の単射性を使う。
規約：共通の底は大きくてもよい。
使われ方：有限な標準単体への底変換の全空間の小ささ。 -/
lemma transportPullback_obj_small {X Y B : SSet.{u + 1}}
    (p : X ⟶ B) (q : Y ⟶ B) (n : SimplexCategoryᵒᵖ)
    [Small.{u} (X.obj n)] [Small.{u} (Y.obj n)] :
    Small.{u} ((pullback p q).obj n) := by
  rcases n with ⟨⟨n⟩⟩
  apply small_of_injective (f := fun x : (pullback p q) _⦋n⦌ ↦
    ((pullback.fst p q).app _ x, (pullback.snd p q).app _ x))
  intro x y h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_ext p q (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- 概要：単射の終域の指定次数が小さければ始域の同じ次数も小さい。
方針：単射の次数ごとの単射性を小ささへ移す。
規約：単体集合の宇宙は変更しない。
使われ方：任意の部分複体への底変換の小ささ。 -/
lemma transportSmall_obj_of_mono {X Y : SSet.{u + 1}} (f : X ⟶ Y) [Mono f]
    (n : SimplexCategoryᵒᵖ) [Small.{u} (Y.obj n)] : Small.{u} (X.obj n) :=
  small_of_injective ((mono_iff_injective (f.app n)).mp inferInstance)

/-- 概要：単射への底変換は全空間の各次数の小ささを保つ。
方針：底変換の全空間から元の全空間への射影が単射であることを使う。
規約：底変換先の小ささは不要。
使われ方：一般の部分複体への表現の制限を扱う。 -/
lemma transportPullback_obj_small_of_mono {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) [Mono g] (n : SimplexCategoryᵒᵖ)
    [Small.{u} (E.obj n)] : Small.{u} ((pullback p g).obj n) :=
  transportSmall_obj_of_mono (pullback.fst p g) n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
