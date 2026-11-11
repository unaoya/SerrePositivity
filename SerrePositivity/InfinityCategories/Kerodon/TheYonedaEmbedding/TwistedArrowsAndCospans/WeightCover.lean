module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.WeightExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseFaceDomainCoordinates

/-!
概要：twisted arrow の重みの延長領域を、左右の半分とホーンの各面の像で覆う。
方針：左半分を前半の頂点の面と同定し、既存の右半分と二頂点を欠く面の計算と合わせる。
規約：全体の次数は正。欠けるホーンの番号以外の面だけを含める。
使われ方：実際のホーンデータを、厳密な延長定理の領域上へ接合する。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 重みの左半分の標準表示は、右半分の補集合の頂点と順序同型。 -/
def edgewiseLeftVerticesOrderIso (n : ℕ) : Fin (n + 1) ≃o ↥((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ) where
  toFun i := ⟨⟨i.val, by omega⟩, by
    simp only [Finset.mem_compl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt]
    exact Nat.le_of_lt_succ i.isLt⟩
  invFun v := ⟨v.val.val, by
    have hn := v.property
    simp only [Finset.mem_compl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt] at hn
    omega⟩
  left_inv i := Fin.ext rfl
  right_inv v := Subtype.ext (Fin.ext rfl)
  map_rel_iff' := by intro i j; rfl

/-- 左半分の重みの像は、標準単体の前半の全面。 -/
lemma edgewiseWeightIso_inl_range (n : ℕ) :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso n).hom) =
      stdSimplex.face ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_inl, Subcomplex.range_comp, Subcomplex.range_eq_top,
    Subcomplex.image_top, Subcomplex.range_eq_ofSimplex]
  exact (stdSimplex.face_eq_ofSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ) n
    (edgewiseLeftVerticesOrderIso n)).symm

/-- 前半の全面を元の重みに戻すと左包含の像となる。 -/
lemma edgewiseWeightIso_left_face_preimage (n : ℕ) :
    (stdSimplex.face ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n)ᶜ)).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso.{u} n).hom =
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}).op Δ[n]) := by
  rw [← edgewiseWeightIso_inl_range, Subcomplex.range_comp, Subcomplex.preimage_image]

/-- 左ホーンの固定領域は、左右の半分と指定番号以外の面の像の和。 -/
lemma twistedArrowWeightDomain_eq_face_cover {n : ℕ} (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowWeightDomain.{u} (n + 1) i =
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n + 1] : SSet.{u}).op Δ[n + 1]) ⊔
        (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]) ⊔
          ⨆ j : {j : Fin (n + 2) // j ≠ i},
            Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ j.val))) := by
  change (stdSimplex.face ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices (n + 1))ᶜ)).preimage
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso (n + 1)).hom ⊔
      ((stdSimplex.face (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices (n + 1))).preimage
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso (n + 1)).hom ⊔
        (⨆ j : {j : Fin (n + 2) // j ≠ i}, stdSimplex.face
          ({_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex (n + 1) j.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex (n + 1) j.val}ᶜ)).preimage
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso (n + 1)).hom) = _
  rw [Subcomplex.preimage_iSup, edgewiseWeightIso_left_face_preimage,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_right_face_preimage]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightIso_pair_face_preimage]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
