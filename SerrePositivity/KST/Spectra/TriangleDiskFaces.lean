module

public import SerrePositivity.KST.Spectra.TriangleDiskBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SquareTriangleOuterFaces

/-!
概要：相対三角形の外側の辺と正方形の境界の対応。
方針：ホーンの商の式と三角形分割の座標表示を使う。
規約：外側の面の添字は 0 と 2。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。相対三角形を貼った写像の境界条件。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：相対三角形の外側の辺は基点へ潰れる。
方針：外側の辺をホーンへ因子分解し、cofiber の基点条件を使う。
規約：欠けた面以外の任意の面を扱う。
使われ方：Goerss–Jardine I §7。正方形の四辺の定数性。 -/
@[reassoc]
theorem triangleDiskQuotient_outer_face (j : Fin 3) (hj : j ≠ 1) :
    stdSimplex.δ j ≫ triangleDiskQuotient.{u} =
      toUnit (Δ[1] : SSet.{u}) ≫ triangleDisk.{u}.hom := by
  rw [← horn.ι_ι (1 : Fin 3) j hj, Category.assoc,
    PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]

namespace SquareTriangles

/-- 概要：第一変数の終点の辺は下側の三角形の零番目の面。
方針：二つの座標射影で確認する。
規約：零次元のパラメータを第二座標への射影で除く。
使われ方：Kerodon §3.2.3（Tag 00W3）。境界との積の面での計算。 -/
theorem first_endpoint_zero : stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) =
    snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_face_zero]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [stdSimplex.δ_zero_eq_const]

/-- 概要：第一変数の始点の辺は上側の三角形の最後の面。
方針：二つの座標射影で確認する。
規約：始点の面の添字は 1。
使われ方：Kerodon §3.2.3（Tag 00W3）。正方形のもう一方の縦辺の計算。 -/
theorem first_endpoint_one : stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) =
    snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_last]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [stdSimplex.δ_one_eq_const]

/-- 概要：第二変数の終点の辺は上側の三角形の零番目の面。
方針：二つの座標射影で確認する。
規約：零次元のパラメータを第一座標への射影で除く。
使われ方：Kerodon §3.2.3（Tag 00W3）。正方形の上辺の計算。 -/
theorem second_endpoint_zero : (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2) =
    fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper_face_zero]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [stdSimplex.δ_zero_eq_const]

/-- 概要：第二変数の始点の辺は下側の三角形の最後の面。
方針：二つの座標射影で確認する。
規約：始点の面の添字は 1。
使われ方：Kerodon §3.2.3（Tag 00W3）。正方形の下辺の計算。 -/
theorem second_endpoint_one : (Δ[1] : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 2) =
    fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower_face_last]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [stdSimplex.δ_one_eq_const]

end SquareTriangles

end SerrePositivity.KST.Spectra
