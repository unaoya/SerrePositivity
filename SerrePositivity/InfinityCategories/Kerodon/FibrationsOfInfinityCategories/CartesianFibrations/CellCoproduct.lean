module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CellAttachment
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessCoproduct

/-!
概要：相対骨格の実際のセル族と境界族は底上の非交和。
方針：各セルの底への射を保持し基礎の単体集合の非交和の普遍性を反映する。
規約：セル族の索引と付着写像は Mathlib のものを用いる。
使われ方：各セルの表現空間の可縮性から族の可縮性を得る。

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

/-- 概要：各セルを底上の標準単体として表示する。
方針：セルの分類射を構造射とする。
規約：非退化な相対セルを添字とする。
使われ方：標準単体上の可縮性の適用対象。 -/
def transportCellSimplexFamily {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    Cell i n → Over B := fun c ↦ Over.mk c.map

/-- 概要：各セルの境界を底上の対象として表示する。
方針：境界包含をセルの分類射へ続ける。
規約：同じ相対セルの添字を使う。
使われ方：低次元の境界上の可縮性の適用対象。 -/
def transportCellBoundaryFamily {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    Cell i n → Over B := fun c ↦ Over.mk (∂Δ[n].ι ≫ c.map)

/-- 概要：実際のセル族を頂点とする底上の非交和の余錐。
方針：各標準単体の非交和への包含を底上に持ち上げる。
規約：底への射を厳密に保つ。
使われ方：各セルの表現を同時に束ねる。 -/
def transportCellSimplexCofan {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    Cofan (transportCellSimplexFamily i n) :=
  Cofan.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportCellSimplexes i n) (fun c ↦ Over.homMk c.ιSigmaStdSimplex (by
    change c.ιSigmaStdSimplex ≫ (b i n ≫ (skeletonOfMono i (n + 1)).ι) = c.map
    exact c.ι_b_ι))

/-- 概要：実際の境界族を頂点とする底上の非交和の余錐。
方針：境界の非交和の包含とセル付加の射影公式を使う。
規約：全境界を同じ索引で扱う。
使われ方：境界族の可縮性を得る。 -/
def transportCellBoundaryCofan {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    Cofan (transportCellBoundaryFamily i n) :=
  Cofan.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportCellBoundaries i n) (fun c ↦ Over.homMk c.ιSigmaBoundary (by
    change c.ιSigmaBoundary ≫ (l i n ≫ (b i n ≫ (skeletonOfMono i (n + 1)).ι)) =
      ∂Δ[n].ι ≫ c.map
    rw [← Category.assoc c.ιSigmaBoundary, c.ι_l, Category.assoc, c.ι_b_ι]))

/-- 概要：実際のセル族の底上の余錐は非交和。
方針：忘却後の標準単体の非交和の普遍性を反映する。
規約：底上の構造射の等式も保持する。
使われ方：抽象的な非交和の表現空間の定理へ接続する。 -/
def transportCellSimplexCofan_isColimit {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    IsColimit (transportCellSimplexCofan i n) := by
  apply isColimitOfIsColimitCofanMkObj (Over.forget B) (transportCellSimplexFamily i n)
  change IsColimit (Cofan.mk (sigmaStdSimplex i n)
    (fun c : Cell i n ↦ c.ιSigmaStdSimplex))
  exact coproductIsCoproduct _

/-- 概要：実際の境界族の底上の余錐は非交和。
方針：忘却後の境界の非交和の普遍性を反映する。
規約：セル族が空の場合も含む。
使われ方：各境界の表現空間の可縮性を族へ束ねる。 -/
def transportCellBoundaryCofan_isColimit {A B : SSet.{u + 1}} (i : A ⟶ B) (n : ℕ) :
    IsColimit (transportCellBoundaryCofan i n) := by
  apply isColimitOfIsColimitCofanMkObj (Over.forget B) (transportCellBoundaryFamily i n)
  change IsColimit (Cofan.mk (sigmaBoundary i n)
    (fun c : Cell i n ↦ c.ιSigmaBoundary))
  exact coproductIsCoproduct _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
