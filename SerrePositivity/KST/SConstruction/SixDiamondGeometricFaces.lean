module
public import SerrePositivity.KST.SConstruction.SixDiamondGeometricPasting

/-! # 六対角面の実消去で元の十二面と共有円柱を厳密に回収する
概要：六つの実四面体と全三辺移送から、入力した全十二面と共有直接円柱を回収する。
方針：各四面体の保存面の式と、全三辺移送の全境界の式を使う。
規約：元の全二単体と全円柱の等号を保持し、辺の類の同定に弱めない。
使われ方：元の raw 十二面図式へ実消去を適用し、全高次 prism と接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {E : SSet.{u}} {v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : E _⦋0⦌}
  {s t : E.Edge v₀ v₁} {leftEdge generatedEdge : E.Edge v₁ v₂}
  {r : E.Edge v₂ v₃} {p : E.Edge v₀ v₄} {l : E.Edge v₄ v₂}
  {q : E.Edge v₄ v₅} {k₁ : E.Edge v₀ v₆} {k₂ : E.Edge v₆ v₅}
  {k₃ : E.Edge v₅ v₃} {a : E.Edge v₆ v₇} {e : E.Edge v₇ v₃} {b : E.Edge v₁ v₇}
  {DA : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond p q k₁ k₂} {DB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond a e k₂ k₃}
  {DI : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond l r q k₃} {DL : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond s leftEdge p l}
  {DR : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond t b k₁ a} {DF : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond b e generatedEdge r}
  {H : EndpointFixedEdgeCylinder s t}
  (D : SixDiamondGeometricPasting DA DB DI DL DR DF H)

/-- 元の左外側二部分面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.left_binary :
    stdSimplex.δ 3 ≫ SSet.yonedaEquiv.symm D.firstMove.simplex =
      SSet.yonedaEquiv.symm DL.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.firstMove.first_face]

/-- 元の交換第一面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.interchange_first :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.firstMove.simplex =
      SSet.yonedaEquiv.symm DI.first.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.firstMove.second_face]

/-- 元の前二射段面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.first_stage :
    stdSimplex.δ 3 ≫ SSet.yonedaEquiv.symm D.secondMove.simplex =
      SSet.yonedaEquiv.symm DA.first.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.secondMove.first_face]

/-- 元の交換第二面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.interchange_second :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.secondMove.simplex =
      SSet.yonedaEquiv.symm DI.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.secondMove.second_face]

/-- 元の前二射二部分面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.first_binary :
    stdSimplex.δ 3 ≫ SSet.yonedaEquiv.symm D.thirdMove.simplex =
      SSet.yonedaEquiv.symm DA.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.thirdMove.first_face]

/-- 元の後二射二部分面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.last_binary :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.thirdMove.simplex =
      SSet.yonedaEquiv.symm DB.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.thirdMove.second_face]

/-- 元の右外側二部分面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.right_binary :
    stdSimplex.δ 3 ≫ SSet.yonedaEquiv.symm D.fourthMove.simplex =
      SSet.yonedaEquiv.symm DR.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.fourthMove.first_face]

/-- 元の後二射段面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.last_stage :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.fourthMove.simplex =
      SSet.yonedaEquiv.symm DB.first.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.fourthMove.second_face]

/-- 元の右外側段面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.right_stage :
    stdSimplex.δ 3 ≫ SSet.yonedaEquiv.symm D.fifthMove.simplex =
      SSet.yonedaEquiv.symm DR.first.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.fifthMove.first_face]

/-- 元の第一 BF 面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.bf_first :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.fifthMove.simplex =
      SSet.yonedaEquiv.symm DF.first.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.fifthMove.second_face]

/-- 元の第二 BF 面全体を、同じ実四面体の指定面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.bf_second :
    stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm D.sixthMove.simplex =
      SSet.yonedaEquiv.symm DF.second.simplex := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, D.sixthMove.second_face]

/-- 元の左外側段面全体は、同じ全三辺移送の始端そのもの。 -/
lemma SixDiamondGeometricPasting.left_stage :
    SSet.ι₀ ≫ D.transportComparison.h = SSet.yonedaEquiv.symm DL.first.simplex :=
  D.transportComparison.h₀

/-- 元の共有直接円柱全体も、同じ全三辺移送の下面として厳密に回収する。 -/
lemma SixDiamondGeometricPasting.shared_direct :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫ D.transportComparison.h = H.homotopy.h := by
  rw [← SSet.boundary.ι_ι (2 : Fin 3), comp_whiskerRight, Category.assoc,
    D.transport_boundary, triangleBoundaryHomotopy_face]
  rfl

/-- 同じ終辺消去の全比較円柱は、同じ全三辺移送の対角側面そのもの。 -/
lemma SixDiamondGeometricPasting.suffix_comparison :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫ D.transportComparison.h =
      (triangleRightCancellationCylinder
        D.top.triangle D.sixthMove.left D.suffixChoice).homotopy.h := by
  rw [← SSet.boundary.ι_ι (1 : Fin 3), comp_whiskerRight, Category.assoc,
    D.transport_boundary, triangleBoundaryHomotopy_face]
  rfl

end SerrePositivity.KST.SConstruction
