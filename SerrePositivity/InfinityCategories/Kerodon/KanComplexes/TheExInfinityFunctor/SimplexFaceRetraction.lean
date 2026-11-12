module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionNerveChains

/-!
# 余面の分裂と欠けた頂点を持つ面の復元

概要：余面の分裂を明示し、その余面に属する非空有限集合を逆像から復元する。
方針：隣接する余退化を分裂に選び、欠けた頂点以外の元の復元を有限集合へ広げる。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の実際の細分比較の補助。
使われ方：horn の面の nerve の単体を余面の細分から持ち上げる。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder
open scoped _root_.Simplicial

/--
概要：各余面の分裂となる隣接した余退化。
方針：最後の頂点なら最後の余退化、それ以外なら同じ番号の余退化を取る。
規約：余面の余域の次元は n+1、定義域は n。
使われ方：余面に含まれる頂点集合の逆像。
-/
def simplexFaceRetraction {n : ℕ} (j : Fin (n + 2)) : ⦋n + 1⦌ ⟶ ⦋n⦌ := by
  induction j using Fin.lastCases with
  | last => exact SimplexCategory.σ (Fin.last n)
  | cast j => exact SimplexCategory.σ j

/--
概要：選んだ余退化は余面の厳密な分裂である。
方針：最後の頂点の場合とそれ以外の場合に、単体恒等式を適用する。
規約：δ_j の後で分裂を適用すると恒等射。
使われ方：欠けた頂点以外の点の復元。
-/
theorem simplexFaceRetraction_section {n : ℕ} (j : Fin (n + 2)) :
    SimplexCategory.δ j ≫ simplexFaceRetraction j = 𝟙 ⦋n⦌ := by
  cases j using Fin.lastCases
  · simpa only [simplexFaceRetraction, Fin.lastCases_last, Fin.succ_last] using
      (SimplexCategory.δ_comp_σ_succ (i := Fin.last n))
  · simpa only [simplexFaceRetraction, Fin.lastCases_castSucc] using
      (SimplexCategory.δ_comp_σ_self (i := _))

/--
概要：欠けた頂点以外の頂点は、分裂で戻して余面で送ると元に戻る。
方針：余面の像が欠けた頂点の補集合であることと分裂の恒等式を使う。
規約：除外する頂点自身では復元を要求しない。
使われ方：余面の像に入る有限集合の復元。
-/
theorem simplexFaceRetraction_recover {n : ℕ} (j i : Fin (n + 2)) (hi : i ≠ j) :
    SimplexCategory.δ j (simplexFaceRetraction j i) = i := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hi
  change SimplexCategory.δ j a = i at ha
  rw [← ha]
  have h := congrArg (fun θ : ⦋n⦌ ⟶ ⦋n⦌ => θ a) (simplexFaceRetraction_section j)
  change simplexFaceRetraction j (SimplexCategory.δ j a) = a at h
  rw [h]

/--
概要：欠けた頂点を含まない非空の面は、余面の分裂による像から復元できる。
方針：有限集合の像の所属条件を使い、各頂点での復元を適用する。
規約：ULift した頂点を持つ標準細分の面の模型。
使われ方：細分された horn の比較の全射性。
-/
theorem simplexFaceRetraction_chain {n : ℕ} (j : Fin (n + 2))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 2)))) (hs : ULift.up j ∉ s.finset) :
    (s.map (SimplexCategory.toPartOrd.map (simplexFaceRetraction j)).hom).map
      (SimplexCategory.toPartOrd.map (SimplexCategory.δ j)).hom = s := by
  rw [finiteChainMap_comp]
  apply NonemptyFiniteChains.ext
  ext x
  simp only [NonemptyFiniteChains.mem_map_iff]
  have hrecover (a : ULift.{u} (Fin (n + 2))) (ha : a ∈ s.finset) :
      (SimplexCategory.toPartOrd.map (SimplexCategory.δ j)).hom
        ((SimplexCategory.toPartOrd.map (simplexFaceRetraction j)).hom a) = a := by
    apply ULift.ext
    apply simplexFaceRetraction_recover
    intro heq
    apply hs
    exact (show a = ULift.up j from ULift.ext heq) ▸ ha
  constructor
  · rintro ⟨a, ha, hx⟩
    have h : a = x := (hrecover a ha).symm.trans hx
    exact h ▸ ha
  · intro hx
    exact ⟨x, hx, hrecover x hx⟩

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
