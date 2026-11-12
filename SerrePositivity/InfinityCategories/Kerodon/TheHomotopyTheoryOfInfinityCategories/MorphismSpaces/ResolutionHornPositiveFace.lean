module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHornHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaces

/-!
# 正の欠落面のホーンの変形は零頂点を除く面を通る

概要：i ≠ 0 のとき、頂点との最大値によるホーンの変形の終端は零頂点を使わない面を通る。
方針：最大値は i 以上なので零にはならず、この面自体は同じホーンに含まれる。
規約：ホーン内での縮約の第一段階の因子分解。縮約全体の完成とは区別する。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの解像の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：零頂点を使わない旗からなる解像の面。
方針：F1 の頂点集合で定まる面を使う。
規約：零次元の場合は空の面。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の正の欠落面のホーンの変形の受け皿。 -/
def resolutionPositiveFace (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace (Finset.univ.erase 0)

/-- 概要：i ≠ 0 のとき零頂点を除く面はホーンの旗の部分複体に含まれる。
方針：欠落頂点の証人に零を使う。
規約：指定された欠落面の番号と証人の頂点は異なる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面からホーンへの包含。 -/
lemma resolutionPositiveFace_le_horn {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    resolutionPositiveFace.{u} n ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i := by
  intro d F hF
  refine ⟨0, Ne.symm hi, fun h0 ↦ ?_⟩
  exact (Finset.mem_erase.mp (hF h0)).1 rfl

/-- 概要：正の頂点との最大値で移した旗の台は零を含まない。
方針：直接像の各点は i 以上であり、i が零でないことを使う。
規約：ホーンに属さない旗に対しても成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の変形の終端の面への持ち上げ。 -/
lemma resolutionUpperVertex_mem_positiveFace {n d : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    ULift.up (F.pushforward (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i)) ∈
      (resolutionPositiveFace.{u} n).obj (Opposite.op ⦋d⦌) := by
  intro k hk
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  intro he
  have h : i ≤ max i j := le_max_left _ _
  change max i j = 0 at he
  rw [he] at h
  exact hi (le_antisymm h (Fin.zero_le i))

/-- 概要：正の頂点を選んだホーンの変形の終端を零頂点を除く面へ送る射。
方針：直接像が零を使わないことにより全体の射を持ち上げる。
規約：包含後の値は既存の最大値の押し出しそのもの。
使われ方：HA 1.3.1.17 の相対的な縮約を面上の比較へ接続する。 -/
def resolutionHornToPositiveFace {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn.{u} i).toSSet ⟶ (resolutionPositiveFace n).toSSet :=
  SSet.Subcomplex.lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionUpperVertexMap i))
    (by
      intro d F hF
      obtain ⟨G, rfl⟩ := hF
      exact resolutionUpperVertex_mem_positiveFace.{u} i hi G.val.down)

/-- 概要：ホーンの最大値の自己写像は零頂点を除く面を通って因子分解する。
方針：包含を後合成して全体の解像の射として二つの持ち上げを比較する。
規約：実際の単体集合の射の等式であり、ホモトピー類だけの因子分解ではない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面を使う縮約の第一段階。 -/
lemma resolutionHornUpperMap_factor_positiveFace {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    resolutionHornToPositiveFace.{u} i hi ≫
        SSet.Subcomplex.homOfLE (resolutionPositiveFace_le_horn i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornUpperMap i := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι).1
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHornUpperMap_ι]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
