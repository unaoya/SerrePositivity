module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FaceRhsComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanCommonData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanResidualCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixIndex

/-! # 左右の後続・A 側の右辺の直接比較

概要：左右の零未知境界データで、後続と A 側の右辺は異種等号で一致する。
方針：これらの集合が二番目の固定点を含まないことと、共通面の一致を使う。
規約：任意の可換環・dg 圏。使われ方：D7 の共通の二残差を一つにまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左右の零未知データの後続右辺は異種等号で一致する。
方針：二番目の固定点を含まない後続集合に共通面の比較を適用する。
規約：全次元。使われ方：r₀ を左右で共有する。 -/
lemma spanBoundaryZeroData_suffixRhs_heq {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixRhs := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common F
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom] at hf
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixRhs
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_face_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) hf _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanPrefix_notMem_suffix _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) _ _ _ _ _ _ _

/-- 概要：左右の零未知データの A 側右辺は異種等号で一致する。
方針：二番目の固定点を含まない一点追加集合に共通面の比較を適用する。
規約：最初の固定点を追加する。使われ方：r_A を左右で共有する。 -/
lemma spanBoundaryZeroData_A_rhs_heq {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common F
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom] at hf
  have hn : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n ∉ insert (0 : Fin (n + 4)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanPrefix_notMem_suffix _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)⟩
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_face_pullback_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) hf _ hn _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
