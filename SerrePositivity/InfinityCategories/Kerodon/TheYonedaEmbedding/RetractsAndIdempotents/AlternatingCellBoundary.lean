module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceInnerAnodyne

/-!
概要：元の交互列の単体を Ret の濾過へ貼るときの境界は inner anodyne。
方針：元の奇数頂点集合を指定面とし、その頂点 1 と 3 の間の頂点 2 を使用する。
規約：全ての m≥2 を同じ元の Δ²ᵐ と元の境界包含で扱う。
使われ方：HTT 4.4.5.6 の Ret(m−1) から Ret(m) への貼付け。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の交互列 Y→X→Y→…→X→Y の非分裂対象側の頂点集合。 -/
def alternatingSourceVertices (m : ℕ) : Finset (Fin (2 * m + 1)) :=
  Finset.univ.filter (fun i ↦ i.val % 2 = 1)

/-- 元の奇数頂点の面を含まない面全体の合併である、元の交互列セルの境界。 -/
def alternatingCellBoundary (m : ℕ) : (Δ[2 * m] : SSet.{u}).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex (alternatingSourceVertices m)

/-- 元の交互列のセルの境界から全単体への同じ包含は、全 m≥2 で inner anodyne。 -/
lemma alternatingCellBoundary_innerAnodyne (m : ℕ) (hm : 2 ≤ m) :
    innerAnodyneExtensions (alternatingCellBoundary.{u} m).ι := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex_innerAnodyne (alternatingSourceVertices m)
    (⟨2, by omega⟩ : Fin (2 * m + 1)) ⟨1, by omega⟩ ⟨3, by omega⟩
  · simp [alternatingSourceVertices]
  · simp [alternatingSourceVertices]
  · simp [alternatingSourceVertices]
  · change (1 : ℕ) < 2
    omega
  · change (2 : ℕ) < 3
    omega

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
