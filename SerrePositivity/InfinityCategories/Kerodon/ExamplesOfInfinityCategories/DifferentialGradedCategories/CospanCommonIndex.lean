module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanBoundaryUnknownZero

/-! # cospan の二セルの共通面の添字

概要：B/C の点を除いた共通面で、先頭の面の集合と大きいセルへの像を計算する。
方針：最初の末尾頂点を飛ばす埋め込みと、先頭 n+2 点の像を比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左右の先頭・D 成分の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：共通面の先頭の既知面の番号。
方針：先頭の n+2 点を一点追加の埋め込みで含める。
規約：HTT §1.2.13。使われ方：共通面でのデータの外延性。 -/
def cospanCommonFaces (n : ℕ) : Finset (Fin (n + 3)) :=
  Finset.univ.image (fun j : Fin (n + 2) => j.castSucc)

/-- 概要：共通面の既知面番号は n+2 より小さいもの。
方針：一点追加の埋め込みの像を値で特徴付ける。
規約：HTT §1.2.13。使われ方：共通面から元の境界面への添字の復元。 -/
lemma mem_cospanCommonFaces {n : ℕ} (j : Fin (n + 3)) :
    j ∈ cospanCommonFaces n ↔ j.val < n + 2 := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact i.isLt
  · intro h
    exact Finset.mem_image.mpr ⟨⟨j.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- 概要：共通面の既知面の集合は全ての頂点を覆う。
方針：零番目と一番目の面の少なくとも一方が指定頂点を避ける。
規約：HTT §1.2.13。使われ方：既知面から共通面の対象族を同定する。 -/
lemma cospanCommonFaces_covers (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (cospanCommonFaces n) := by
  intro k
  by_cases hk : k = 0
  · refine ⟨1, (mem_cospanCommonFaces _).mpr (by simp), ?_⟩
    rw [hk]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  · exact ⟨0, (mem_cospanCommonFaces _).mpr (by simp), Ne.symm hk⟩

/-- 概要：共通面から大きいセルへの包含は最初の末尾頂点を飛ばす順序写像。
方針：面の順序埋め込みを使う。
規約：HTT §1.2.13。使われ方：先頭と D の成分を二セルで比較する。 -/
def cospanCommonOrderHom (n : ℕ) : Fin (n + 3) →o Fin (n + 4) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n).succAboveOrderEmb.toOrderHom

/-- 概要：共通面の先頭集合の像は大きいセルの先頭集合。
方針：先頭の頂点では飛ばす点より前なので番号が変わらないことを使う。
規約：HTT §1.2.13。使われ方：共通面の未知成分も大きいセルの未知成分となること。 -/
lemma cospanCommonFaces_image (n : ℕ) :
    (cospanCommonFaces n).image (cospanCommonOrderHom n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
  rw [cospanCommonFaces, Finset.image_image, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces]
  apply congrArg (fun f => Finset.univ.image f)
  funext j
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n).succAbove j.castSucc = j.castAdd 2
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change j.val < n + 2; exact j.isLt)]
  rfl

/-- 概要：共通面と先頭の境界面を取る順序は可換。
方針：面の合成恒等式を有限順序集合の対応する添字に適用する。
規約：HTT §1.2.13。使われ方：二セルの共通面の既知の面の一致。 -/
lemma cospanCommon_face_commute (n : ℕ) (j : Fin (n + 2)) :
    (SSet.stdSimplex.δ j.castSucc : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2]) ≫
      SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) =
      SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc) ≫ SSet.stdSimplex.δ (j.castAdd 2) := by
  exact SSet.stdSimplex.δ_comp_δ (n := n + 1)
    (i := j.castSucc) (j := (Fin.last (n + 1)).castSucc) (by exact Fin.le_last j)

/-- 概要：共通面と境界面の可換性は対応する順序写像の合成でも成り立つ。
方針：単体圏の面の恒等式を順序写像として評価する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：単体データの二段の引き戻しの比較。 -/
lemma cospanCommon_orderHom_comp (n : ℕ) (j : Fin (n + 2)) :
    (cospanCommonOrderHom n).comp j.castSucc.succAboveOrderEmb.toOrderHom =
      (j.castAdd 2).succAboveOrderEmb.toOrderHom.comp
        ((Fin.last (n + 1)).castSucc).succAboveOrderEmb.toOrderHom := by
  exact congrArg SimplexCategory.Hom.toOrderHom
    (SimplexCategory.δ_comp_δ (n := n + 1)
      (i := j.castSucc) (j := (Fin.last (n + 1)).castSucc) (by exact Fin.le_last j))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
