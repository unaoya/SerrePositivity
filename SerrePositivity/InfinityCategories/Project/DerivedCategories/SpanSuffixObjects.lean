module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanCommonRhs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanIndexGeometry

/-! # 左右の span 境界データの共通の対象

概要：左右の零未知境界データは全可変頂点および最初の固定頂点で同じ対象を持つ。
方針：共通面への制限の等式を、その像にある頂点で評価する。
規約：可換環上の任意の dg 圏。使われ方：D7 の全残差を同じ終点への Hom に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左右の零未知データは全ての可変頂点で同じ対象を持つ。
方針：その頂点を共通面の像として書き、共通面の対象の一致を使う。
規約：実際の任意の境界。使われ方：残差の始点・終点の統一。 -/
lemma spanBoundaryZeroData_suffix_obj {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (k : Fin (n + 4)) (hk : k ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).obj k = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).obj k := by
  have hi : k ∈ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces n).image (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonFaces_image]
    exact hk
  obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hi
  simpa only [heq] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common_obj F i

/-- 概要：左右の零未知データは最初の固定頂点でも同じ対象を持つ。
方針：共通面の最初の頂点で対象の一致を評価する。
規約：この頂点は span の始点 A。使われ方：A 側の残差の比較。 -/
lemma spanBoundaryZeroData_zero_obj {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).obj 0 = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).obj 0 := by
  have h0 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanCommonOrderHom n 0 = 0 := rfl
  simpa only [h0] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_common_obj F 0

/-- 概要：左右の零未知データの余錐頂点の対象は同じ。
方針：余錐頂点が後続集合に属することを使う。
規約：可変因子の最初の頂点。使われ方：cofiber 対象から出る残差の比較。 -/
lemma spanBoundaryZeroData_apex_obj {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :=
  spanBoundaryZeroData_suffix_obj F _ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le _).mpr le_rfl)

/-- 概要：左右の零未知データの最後の対象は同じ。
方針：最後の頂点の後続集合への所属を使う。
規約：全ての未知成分の共通終点。使われ方：Hom 座標の値域の固定。 -/
lemma spanBoundaryZeroData_last_obj {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).obj (Fin.last (n + 3)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).obj (Fin.last (n + 3)) :=
  spanBoundaryZeroData_suffix_obj F _ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
