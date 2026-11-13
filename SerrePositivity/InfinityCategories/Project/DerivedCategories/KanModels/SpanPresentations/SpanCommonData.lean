module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanCommonBoundaryFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceExtensionality

/-! # 左右の零未知データの共通面の一致

概要：左右の境界の零未知データは A と可変部分からなる共通面へ制限すると等しい。
方針：既知面の一致、未知集合の像の包含、未知成分の零からデータの外延性を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：左右の共通の対象・後続右辺・A 側右辺を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：共通面で後続を全て含む集合の像も元のセルの後続を全て含む。
方針：後続集合の像の公式と像の単調性を使う。
規約：HTT §1.2.13。使われ方：共通面の未知成分の零を元のセルから回収する。 -/
lemma spanCommon_image_contains_suffix {n : ℕ} (I : Finset (Fin (n + 3)))
    (hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces n ⊆ I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I.image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces_image n]
  exact Finset.image_subset_image hI

/-- 概要：左右の零未知境界データは A と可変部分からなる共通面上で等しい。
方針：後続の既知面を共通の境界から比較し、未知成分は像の包含と元の零性で消す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：残差の右辺の左右共通部分の同定。 -/
lemma spanBoundaryZeroData_common {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) := by
  have hi : Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanJoinCommonFace (n + 1)).succAboveOrderEmb.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ext_of_selected_faces_zero_unknown (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces_covers n)
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryCommonData_face F i
  · intro I hI a b k hJ ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom F _
      (spanCommon_image_contains_suffix I hI) _ _ _ _ _ _ _
  · intro I hI a b k hJ ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi.injOn]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom F _
      (spanCommon_image_contains_suffix I hI) _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
