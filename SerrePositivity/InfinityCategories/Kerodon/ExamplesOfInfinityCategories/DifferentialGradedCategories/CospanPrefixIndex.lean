module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData

/-! # cospan の標準セルの既知面の添字

概要：末尾の二頂点より前の全ての面を選び、既知集合と未知集合を判定する。
方針：先頭の頂点を二点追加する埋め込みの像として有限集合を定義する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の二セルでの四つずつの未知成分。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open scoped _root_.Simplicial

/-- 概要：末尾の二頂点を固定した標準セルの先頭の面の番号。
方針：先頭 n+2 点の二点追加による像を取る。
規約：HTT §1.2.13。使われ方：slice の n+1 次元の境界に対応する面集合。 -/
def cospanPrefixFaces (n : ℕ) : Finset (Fin (n + 4)) :=
  Finset.univ.image (fun j : Fin (n + 2) => j.castAdd 2)

/-- 概要：選んだ面の番号は n+2 より小さいものに限る。
方針：像の所属を有限順序集合の値で判定する。
規約：HTT §1.2.13。使われ方：面番号から元の境界面番号を復元する。 -/
lemma mem_cospanPrefixFaces {n : ℕ} (j : Fin (n + 4)) :
    j ∈ cospanPrefixFaces n ↔ j.val < n + 2 := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact i.isLt
  · intro h
    exact Finset.mem_image.mpr ⟨⟨j.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- 概要：選んだ大きい面の番号から、元の先頭の面の番号を回収する。
方針：値を変えず、所属条件から上界を得る。
規約：HTT §1.2.13。使われ方：二セルの面から境界面を指定する。 -/
def cospanPrefixFaceIndex {n : ℕ} (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    Fin (n + 2) := ⟨j.val, (mem_cospanPrefixFaces j).mp hj⟩

/-- 概要：回収した先頭の面番号を二点追加すると元の面番号に戻る。
方針：有限順序集合の値の等式を使う。
規約：HTT §1.2.13。使われ方：標準セルの面の可換性の適用。 -/
lemma cospanPrefixFaceIndex_castAdd {n : ℕ} (j : Fin (n + 4))
    (hj : j ∈ cospanPrefixFaces n) :
    (cospanPrefixFaceIndex j hj).castAdd 2 = j := Fin.ext rfl

/-- 概要：先頭の面の集合は全ての頂点を覆う。
方針：零番目の面と一番目の面の少なくとも一方が指定頂点を避ける。
規約：HTT §1.2.13。使われ方：対象族の成分回収の被覆条件。 -/
lemma cospanPrefixFaces_covers (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (cospanPrefixFaces n) := by
  intro k
  by_cases hk : k = 0
  · refine ⟨1, (mem_cospanPrefixFaces _).mpr (by simp), ?_⟩
    rw [hk]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  · exact ⟨0, (mem_cospanPrefixFaces _).mpr (by simp), Ne.symm hk⟩

/-- 概要：既知成分とは先頭の頂点を少なくとも一つ欠く成分。
方針：集合の包含の否定を存在条件に書き換える。
規約：HA Proposition 1.3.1.10。使われ方：未知四成分以外を recoverHom に渡す条件。 -/
lemma cospanPrefixFaces_known_iff {n : ℕ} (I : Finset (Fin (n + 4))) :
    (∃ j ∈ cospanPrefixFaces n, j ∉ I) ↔ ¬ cospanPrefixFaces n ⊆ I := by
  simp only [Finset.subset_iff, not_forall, exists_prop]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
