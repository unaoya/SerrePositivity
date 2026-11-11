module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanCommonBoundaryFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceExtensionality

/-! # 左右の零未知データの共通面の一致

概要：左右の境界の零未知データは先頭と D からなる共通面へ制限すると等しい。
方針：既知面の一致、未知集合の像の包含、未知成分の零からデータの外延性を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左右の共通の対象・先頭右辺・D 側右辺を同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：共通面で先頭を全て含む集合の像も元のセルの先頭を全て含む。
方針：先頭集合の像の公式と像の単調性を使う。
規約：HTT §1.2.13。使われ方：共通面の未知成分の零を元のセルから回収する。 -/
lemma cospanCommon_image_contains_prefix {n : ℕ} (I : Finset (Fin (n + 3)))
    (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonFaces n ⊆ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonFaces_image n]
  exact Finset.image_subset_image hI

/-- 概要：左右の零未知境界データは先頭と D からなる共通面上で等しい。
方針：先頭の既知面を共通の境界から比較し、未知成分は像の包含と元の零性で消す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残差の右辺の左右共通部分の同定。 -/
lemma cospanBoundaryZeroData_common {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) := by
  have hi : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonOrderHom n) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n).succAboveOrderEmb.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ext_of_selected_faces_zero_unknown (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonFaces n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanCommonFaces_covers n)
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryCommonData_face F i
  · intro I hI a b k hJ ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData_unknownHom F _
      (cospanCommon_image_contains_prefix I hI) _ _ _ _ _ _ _
  · intro I hI a b k hJ ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData_unknownHom F _
      (cospanCommon_image_contains_prefix I hI) _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
