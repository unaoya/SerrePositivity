module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanBoundaryZeroData

/-! # span の二セルの共通面の添字

概要：二番目の固定頂点を除いた共通面で、後続の面の集合と大きいセルへの像を計算する。
方針：一点を飛ばす埋め込みと後続 n+2 点の像を比較する。
規約：共通面の先頭は A。使われ方：D7 の左右の共通データの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：共通面の既知面の番号は最初の固定点以外の全点。
方針：可変頂点の添字を succ で含める。
規約：先頭一点が固定点 A。使われ方：共通面でのデータの外延性。 -/
def spanCommonFaces (n : ℕ) : Finset (Fin (n + 3)) :=
  Finset.univ.image (fun j : Fin (n + 2) => j.succ)

/-- 概要：共通面の既知面番号は一以上の値に限る。
方針：succ の像を自然数の値で特徴付ける。
規約：有限添字に上界を含む。使われ方：境界面への参照。 -/
lemma mem_spanCommonFaces {n : ℕ} (j : Fin (n + 3)) :
    j ∈ spanCommonFaces n ↔ 1 ≤ j.val := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    change 1 ≤ i.val + 1
    omega
  · intro h
    refine Finset.mem_image.mpr ⟨⟨j.val - 1, by have := j.isLt; omega⟩,
      Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    omega

/-- 概要：共通面の既知面は全頂点を覆う。
方針：一番目と二番目を除く面の少なくとも一方が指定頂点を避ける。
規約：n=0 も含む。使われ方：共通面の対象の回収。 -/
lemma spanCommonFaces_covers (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (spanCommonFaces n) := by
  intro k
  by_cases hk : k = (⟨1, by omega⟩ : Fin (n + 3))
  · refine ⟨⟨2, by omega⟩, (mem_spanCommonFaces _).mpr (by change 1 ≤ 2; decide), ?_⟩
    rw [hk]
    intro h
    have hv := congrArg Fin.val h
    change 2 = 1 at hv
    omega
  · exact ⟨⟨1, by omega⟩, (mem_spanCommonFaces _).mpr (by change 1 ≤ 1; decide), Ne.symm hk⟩

/-- 概要：共通面の包含は二番目の固定頂点を飛ばす。
方針：標準共通面の順序埋め込みを使う。
規約：先頭の固定点 A と全可変点を保つ。使われ方：左右の共通成分の比較。 -/
def spanCommonOrderHom (n : ℕ) : Fin (n + 3) →o Fin (n + 4) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.toOrderHom

/-- 概要：共通面の可変頂点集合の像は元のセルの可変頂点集合。
方針：飛ばす固定頂点より後の値は一だけ増えることを使う。
規約：厳密な有限集合の等式。使われ方：共通面の未知成分を元のセルで判定する。 -/
lemma spanCommonFaces_image (n : ℕ) :
    (spanCommonFaces n).image (spanCommonOrderHom n) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
  rw [spanCommonFaces, Finset.image_image, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces]
  apply congrArg (fun f => Finset.univ.image f)
  funext j
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAbove j.succ = j.succ.succ
  rw [Fin.succAbove_of_le_castSucc _ _ (by change 1 ≤ j.val + 1; omega)]

/-- 概要：共通面と可変境界面を取る順序は可換。
方針：固定頂点の面番号が可変面番号以下であることに面の合成恒等式を適用する。
規約：単体データの引き戻しと同じ順序。使われ方：共通面の既知面の比較。 -/
lemma spanCommon_face_commute (n : ℕ) (j : Fin (n + 2)) :
    (SSet.stdSimplex.δ j.succ : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2]) ≫
      SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)) =
      SSet.stdSimplex.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n) ≫ SSet.stdSimplex.δ j.succ.succ := by
  exact (SSet.stdSimplex.δ_comp_δ (n := n + 1)
    (i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n) (j := j.succ) (by change 1 ≤ j.val + 1; omega)).symm

/-- 概要：共通面と可変面の可換性は順序写像の合成でも成り立つ。
方針：単体圏の面恒等式を順序写像として評価する。
規約：全ての可変面。使われ方：二段のデータの引き戻しの比較。 -/
lemma spanCommon_orderHom_comp (n : ℕ) (j : Fin (n + 2)) :
    (spanCommonOrderHom n).comp j.succ.succAboveOrderEmb.toOrderHom =
      j.succ.succ.succAboveOrderEmb.toOrderHom.comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n).succAboveOrderEmb.toOrderHom := by
  exact congrArg SimplexCategory.Hom.toOrderHom
    (SimplexCategory.δ_comp_δ (n := n + 1)
      (i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace n) (j := j.succ) (by change 1 ≤ j.val + 1; omega)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
