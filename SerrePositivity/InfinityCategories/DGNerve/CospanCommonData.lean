module
public import SerrePositivity.InfinityCategories.DGNerve.CospanCommonBoundaryFaces
public import SerrePositivity.InfinityCategories.DGNerve.SelectedFaceExtensionality

/-! # 左右の零未知データの共通面の一致

概要：左右の境界の零未知データは先頭と D からなる共通面へ制限すると等しい。
方針：既知面の一致、未知集合の像の包含、未知成分の零からデータの外延性を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左右の共通の対象・先頭右辺・D 側右辺を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：共通面で先頭を全て含む集合の像も元のセルの先頭を全て含む。
方針：先頭集合の像の公式と像の単調性を使う。
規約：HTT §1.2.13。使われ方：共通面の未知成分の零を元のセルから回収する。 -/
lemma cospanCommon_image_contains_prefix {n : ℕ} (I : Finset (Fin (n + 3)))
    (hI : cospanCommonFaces n ⊆ I) :
    cospanPrefixFaces n ⊆ I.image (cospanCommonOrderHom n) := by
  rw [← cospanCommonFaces_image n]
  exact Finset.image_subset_image hI

/-- 概要：左右の零未知境界データは先頭と D からなる共通面上で等しい。
方針：先頭の既知面を共通の境界から比較し、未知成分は像の包含と元の零性で消す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残差の右辺の左右共通部分の同定。 -/
lemma cospanBoundaryZeroData_common {n : ℕ}
    (F : join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ dgNerve A D) :
    (cospanBoundaryLeftZeroData F).pullback (cospanCommonOrderHom n) =
      (cospanBoundaryRightZeroData F).pullback (cospanCommonOrderHom n) := by
  have hi : Function.Injective (cospanCommonOrderHom n) :=
    (cospanFirstTail n).succAboveOrderEmb.injective
  apply SimplexData.ext_of_selected_faces_zero_unknown (cospanCommonFaces n)
    (cospanCommonFaces_covers n)
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact cospanBoundaryCommonData_face F i
  · intro I hI a b k hJ ha hb hk
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact cospanBoundaryLeftZeroData_unknownHom F _
      (cospanCommon_image_contains_prefix I hI) _ _ _ _ _ _ _
  · intro I hI a b k hJ ha hb hk
    rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact cospanBoundaryRightZeroData_unknownHom F _
      (cospanCommon_image_contains_prefix I hI) _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.DGNerve
