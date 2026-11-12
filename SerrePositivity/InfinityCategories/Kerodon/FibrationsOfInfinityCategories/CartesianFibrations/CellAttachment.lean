module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.WitnessPushoutContractible
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
概要：単体集合の実際のセル付加の pushout を底上の圏へ持ち上げる。
方針：Mathlib の境界と標準単体の非交和を底への構造射付きで扱う。
規約：相対骨格を使い任意の開始部分にも適用する。
使われ方：有限骨格の表現空間の可縮性の帰納法。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SSet.relativeCellComplexOfMono
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：相対骨格を底上の対象として表示する。
方針：部分複体の包含を構造射とする。
規約：段数 n は次元が n 未満の骨格に対応する。
使われ方：セル付加の右辺の二対象。 -/
def transportRelativeSkeleton {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) : Over B :=
  Over.mk (skeletonOfMono i n).ι

/-- 概要：新しい標準単体の族を底上の対象として表示する。
方針：セル付加の底辺と次段の包含を合成する。
規約：セルの索引と非交和は Mathlib の実際のもの。
使われ方：セル付加の左下の対象。 -/
def transportCellSimplexes {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) : Over B :=
  Over.mk (b i n ≫ (skeletonOfMono i (n + 1)).ι)

/-- 概要：新しいセルの境界の族を底上の対象として表示する。
方針：境界の非交和から標準単体の非交和への射を構造射へ続ける。
規約：境界全体を同時に扱う。
使われ方：セル付加の共通部分の対象。 -/
def transportCellBoundaries {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) : Over B :=
  Over.mk (l i n ≫ (b i n ≫ (skeletonOfMono i (n + 1)).ι))

/-- 概要：セルの境界の包含を底上の射にする。
方針：境界から標準単体への非交和の包含を取る。
規約：基礎の射は単射。
使われ方：表現空間の制限の fibration 条件。 -/
def transportCellBoundaryInclusion {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    transportCellBoundaries i n ⟶ transportCellSimplexes i n :=
  Over.homMk (l i n) (by rfl)

/-- 概要：セル境界の付着写像を底上の射にする。
方針：Mathlib の付着写像とセル正方形の可換性を使う。
規約：底への射を厳密に保つ。
使われ方：セル付加の上辺。 -/
def transportCellAttachingMap {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    transportCellBoundaries i n ⟶ transportRelativeSkeleton i n :=
  Over.homMk (t i n) (by
    change t i n ≫ (skeletonOfMono i n).ι =
      l i n ≫ (b i n ≫ (skeletonOfMono i (n + 1)).ι)
    rw [← Category.assoc, ← w i n, Category.assoc]
    rfl)

/-- 概要：セル族の実現を次段の相対骨格への射にする。
方針：標準単体の非交和から次段への既存の射を取る。
規約：全てのセルを同時に実現する。
使われ方：セル付加の底辺。 -/
def transportCellRealization {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    transportCellSimplexes i n ⟶ transportRelativeSkeleton i (n + 1) :=
  Over.homMk (b i n) (by rfl)

/-- 概要：相対骨格の隣接段の包含を底上の射にする。
方針：Mathlib の相対骨格の包含を取る。
規約：基礎の射は単射。
使われ方：セル付加の右辺。 -/
def transportRelativeSkeletonStep {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    transportRelativeSkeleton i n ⟶ transportRelativeSkeleton i (n + 1) :=
  Over.homMk (r i n) (by rfl)

/-- 概要：実際のセル付加の正方形は底上の圏でも pushout。
方針：忘却後の Mathlib のセル付加の pushout を反映する。
規約：可換性も底上の射として厳密に満たす。
使われ方：表現空間の pushout 貼り合わせの入力。 -/
lemma transportCellAttachment_isPushout {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    IsPushout (transportCellBoundaryInclusion i n) (transportCellAttachingMap i n)
      (transportCellRealization i n) (transportRelativeSkeletonStep i n) := by
  apply IsPushout.of_map_of_faithful (Over.forget B)
  exact (isPushout i n).flip

/-- 概要：セル境界の底上の包含の基礎の射は単射。
方針：境界包含の非交和の単射性を回収する。
規約：セル族が空の場合も含む。
使われ方：表現空間の付着写像の fibration 条件。 -/
instance transportCellBoundaryInclusion_mono_left {A B : SSet.{u + 1}}
    (i : A ⟶ B) (n : ℕ) : Mono (transportCellBoundaryInclusion i n).left := by
  change Mono (l i n)
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
