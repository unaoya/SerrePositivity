module
public import SerrePositivity.InfinityCategories.Derived.SpanCommonBoundaryFaces
public import SerrePositivity.InfinityCategories.DGNerve.SelectedFaceExtensionality

/-! # 左右の零未知データの共通面の一致

概要：左右の境界の零未知データは A と可変部分からなる共通面へ制限すると等しい。
方針：既知面の一致、未知集合の像の包含、未知成分の零からデータの外延性を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左右の共通の対象・後続右辺・A 側右辺を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：共通面で後続を全て含む集合の像も元のセルの後続を全て含む。
方針：後続集合の像の公式と像の単調性を使う。
規約：HTT §1.2.13。使われ方：共通面の未知成分の零を元のセルから回収する。 -/
lemma spanCommon_image_contains_suffix {n : ℕ} (I : Finset (Fin (n + 3)))
    (hI : spanCommonFaces n ⊆ I) :
    spanSuffixFaces n ⊆ I.image (spanCommonOrderHom n) := by
  rw [← spanCommonFaces_image n]
  exact Finset.image_subset_image hI

/-- 概要：左右の零未知境界データは A と可変部分からなる共通面上で等しい。
方針：後続の既知面を共通の境界から比較し、未知成分は像の包含と元の零性で消す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残差の右辺の左右共通部分の同定。 -/
lemma spanBoundaryZeroData_common {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    (spanBoundaryLeftZeroData F).pullback (spanCommonOrderHom n) =
      (spanBoundaryRightZeroData F).pullback (spanCommonOrderHom n) := by
  have hi : Function.Injective (spanCommonOrderHom n) :=
    (spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective
  apply SimplexData.ext_of_selected_faces_zero_unknown (spanCommonFaces n)
    (spanCommonFaces_covers n)
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact spanBoundaryCommonData_face F i
  · intro I hI a b k hJ ha hb hk
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact spanBoundaryLeftZeroData_unknownHom F _
      (spanCommon_image_contains_suffix I hI) _ _ _ _ _ _ _
  · intro I hI a b k hJ ha hb hk
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact spanBoundaryRightZeroData_unknownHom F _
      (spanCommon_image_contains_suffix I hI) _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories
