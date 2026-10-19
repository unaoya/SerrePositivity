module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberSquare

/-! # 全 Hom end の実四角形の四頂点

概要：四角形データの実辺と四頂点を元の閉零射と実加群対象に同定する。
方針：二つの実二単体の面を評価する。
規約：零性や普遍性は仮定しない。使われ方：零角変更と関手同型の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D} (s : DGModuleSquareData A D W X Y Z)

/-- 下辺は元の閉零射の実辺。 -/
lemma square_bottom : squareBottomEdge ≫ s.square =
    SSet.yonedaEquiv.symm (dgModuleEdge A D s.bottom).edge := by
  rw [← cofiberSquareTriangle_bottomEdge, Category.assoc, square_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₂

/-- 左辺は元の閉零射の実辺。 -/
lemma square_left : squareLeftEdge ≫ s.square =
    SSet.yonedaEquiv.symm (dgModuleEdge A D s.left).edge := by
  rw [← cofiberSquareTriangle_leftEdge, Category.assoc, square_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (dgModuleCompStruct A D s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₂

/-- 右辺は元の閉零射の実辺。 -/
lemma square_right : squareRightEdge ≫ s.square =
    SSet.yonedaEquiv.symm (dgModuleEdge A D s.right).edge := by
  rw [← squareTriangle_rightEdge, Category.assoc, square_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (dgModuleCompStruct A D s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₀

/-- 始点の実頂点。 -/
lemma square_vertex00 : squareVertex s.square 0 0 =
    Simplex.vertex (ForgetEnrichment.to (Complex A) W) := by
  rw [← squareBottomEdge_source, square_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D s.bottom).src_eq

/-- 下辺終点の実頂点。 -/
lemma square_vertex10 : squareVertex s.square 1 0 =
    Simplex.vertex (ForgetEnrichment.to (Complex A) X) := by
  rw [← squareBottomEdge_target, square_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D s.bottom).tgt_eq

/-- 左上の実頂点。 -/
lemma square_vertex01 : squareVertex s.square 0 1 =
    Simplex.vertex (ForgetEnrichment.to (Complex A) Y) := by
  rw [← squareLeftEdge_target, square_left, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D s.left).tgt_eq

/-- 終点の実頂点。 -/
lemma square_vertex11 : squareVertex s.square 1 1 =
    Simplex.vertex (ForgetEnrichment.to (Complex A) Z) := by
  rw [← squareRightEdge_target, square_right, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D s.right).tgt_eq

end SerrePositivity.InfinityCategories.DGModuleSquareData
