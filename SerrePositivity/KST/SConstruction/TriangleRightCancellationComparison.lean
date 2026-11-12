module
public import SerrePositivity.KST.SConstruction.TriangleRightCancellation
public import SerrePositivity.KST.SConstruction.AnodyneFixedHomotopy
public import SerrePositivity.KST.SConstruction.BoundaryTensorHomExt
public import SerrePositivity.KST.SConstruction.AnodynePrescribedComparison

/-! # 元の全三面を固定する終辺消去の二選択の実高次比較
概要：二つの終辺消去四面体を、その全指定三面を全時刻固定して比較する。
方針：三次外ホーンの anodyne 性を相対ホモトピー延長へ使う。
規約：単なる比較辺の類の等号にせず、元の全四面体を両端に保持する。
使われ方：十二面の消去を高次 prism に沿って同時に選択するための実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {E : SSet.{u}} [KanComplex E] {x y z : E _⦋0⦌}
  {a d : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct d b c)
  (v w : (triangleRightCancellationChoices T U) _⦋0⦌)

/-- 元の全三面を固定する、二つの全終辺消去四面体の実比較データ。 -/
def triangleRightCancellationComparisonData :=
  anodyneFixedHomotopyData (horn 3 (3 : Fin 4)).ι
    (anodyneExtensions.horn_ι (3 : Fin 4))
    (triangleRightCancellationAt T U v) (triangleRightCancellationAt T U w)
    ((anodyneExtensionAt_fac _ _ v).trans (anodyneExtensionAt_fac _ _ w).symm)

/-- 元の全四面体を両端に持つ同じ実高次比較円柱。 -/
def triangleRightCancellationComparison : SSet.Homotopy
    (triangleRightCancellationAt T U v) (triangleRightCancellationAt T U w) :=
  (triangleRightCancellationComparisonData T U v w).val

/-- 元の三次外ホーン全体を全比較時刻で厳密に固定する。 -/
lemma triangleRightCancellationComparison_relative :
    ((horn 3 (3 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationComparison T U v w).h =
      fst (Λ[3, 3] : SSet.{u}) Δ[1] ≫ (horn 3 (3 : Fin 4)).ι ≫
        triangleRightCancellationAt T U v :=
  (triangleRightCancellationComparisonData T U v w).property

/-- 全指定三面は元の二合成面と退化面を全時刻でそのまま保持する。 -/
lemma triangleRightCancellationComparison_face (j : Fin 4) (hj : j ≠ 3) :
    (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationComparison T U v w).h =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫ triangleRightCancellationFaces T U j hj := by
  rw [← horn.ι_ι (3 : Fin 4) j hj, comp_whiskerRight, Category.assoc,
    triangleRightCancellationComparison_relative, whiskerRight_fst_assoc]
  rw [← Category.assoc (horn.ι (3 : Fin 4) j hj), horn.ι_ι,
    triangleRightCancellationAt_face T U v j hj]

/-- 同じ高次比較の第三面は、実比較三角形全体を両端に持つ同じ実円柱。 -/
def triangleRightCancellationTriangleComparison : SSet.Homotopy
    (SSet.yonedaEquiv.symm (triangleRightCancellationTriangle T U v).simplex)
    (SSet.yonedaEquiv.symm (triangleRightCancellationTriangle T U w).simplex) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (triangleRightCancellationComparison T U v w) (stdSimplex.δ 3))
    (triangleRightCancellationTriangle_face T U v)
    (triangleRightCancellationTriangle_face T U w).symm

/-- 元の比較三角形の全高次比較は、四面体比較の同じ全第三面。 -/
lemma triangleRightCancellationTriangleComparison_h :
    (triangleRightCancellationTriangleComparison T U v w).h =
      (stdSimplex.δ 3 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationComparison T U v w).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 同じ比較三角形の全三辺は、高次比較の全時刻で厳密に固定する。 -/
lemma triangleRightCancellationTriangleComparison_edge (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationTriangleComparison T U v w).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫
        SSet.yonedaEquiv.symm (triangleRightCancellationTriangle T U v).simplex := by
  have hi : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
  have he : stdSimplex.δ.{u} i ≫ stdSimplex.δ (3 : Fin 4) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ i.castSucc := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro k
    fin_cases i <;> fin_cases k <;> rfl
  rw [triangleRightCancellationTriangleComparison_h, ← Category.assoc,
    ← comp_whiskerRight, he, comp_whiskerRight, Category.assoc,
    triangleRightCancellationComparison_face T U v w i.castSucc hi,
    whiskerRight_fst_assoc, triangleRightCancellationTriangle_face]
  rw [← Category.assoc (stdSimplex.δ i), he, Category.assoc,
    triangleRightCancellationAt_face T U v i.castSucc hi]

/-- 高次比較は元の比較三角形の全境界を全時刻で厳密に固定する。 -/
lemma triangleRightCancellationTriangleComparison_boundary :
    ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationTriangleComparison T U v w).h =
      fst (∂Δ[2] : SSet.{u}) Δ[1] ≫ (SSet.boundary 2).ι ≫
        SSet.yonedaEquiv.symm (triangleRightCancellationTriangle T U v).simplex := by
  apply boundaryTensorHomExt
  intro i
  rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι,
    triangleRightCancellationTriangleComparison_edge, whiskerRight_fst_assoc,
    ← Category.assoc (SSet.boundary.ι i), SSet.boundary.ι_ι]

variable {B : SSet.{u}} (p : E ⟶ B) [Fibration p]
  (H : SSet.Homotopy (triangleRightCancellationAt T U v ≫ p)
    (triangleRightCancellationAt T U w ≫ p))
  (hr : ((horn 3 (3 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Λ[3, 3] : SSet.{u}) Δ[1] ≫ triangleRightCancellationHorn T U ≫ p)

/-- 元の全基底比較と全三面を同時に保持する、同じ二四面体の実高次比較。 -/
def triangleRightCancellationComparisonOverData :
    {K : SSet.Homotopy (triangleRightCancellationAt T U v) (triangleRightCancellationAt T U w) //
      K.h ≫ p = H.h ∧ ((horn 3 (3 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h =
        fst (Λ[3, 3] : SSet.{u}) Δ[1] ≫ triangleRightCancellationHorn T U} := by
  let C := familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (triangleRightCancellationHorn T U))
    (anodyneExtensionAt_fac _ _ v) (anodyneExtensionAt_fac _ _ w).symm
  have hC : C.h = fst (Λ[3, 3] : SSet.{u}) Δ[1] ≫ triangleRightCancellationHorn T U :=
    familyHomotopyEndpointTransport_h _ _ _
  let D := anodynePrescribedComparisonData (horn 3 (3 : Fin 4)).ι
    (anodyneExtensions.horn_ι (3 : Fin 4)) p _ _ H C
    (by rw [hC]; exact (Category.assoc _ _ _).trans hr.symm)
  exact ⟨D.val, D.property.1, D.property.2.trans hC⟩

omit [KanComplex E]

/-- 同じ持ち上げの全射影は、元の全基底比較円柱そのもの。 -/
lemma triangleRightCancellationComparisonOverData_projection :
    (triangleRightCancellationComparisonOverData T U v w p H hr).val.h ≫ p = H.h :=
  (triangleRightCancellationComparisonOverData T U v w p H hr).property.1

/-- 全三面は、同じ持ち上げの全比較時刻で厳密に固定する。 -/
lemma triangleRightCancellationComparisonOverData_relative :
    ((horn 3 (3 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleRightCancellationComparisonOverData T U v w p H hr).val.h =
      fst (Λ[3, 3] : SSet.{u}) Δ[1] ≫ triangleRightCancellationHorn T U :=
  (triangleRightCancellationComparisonOverData T U v w p H hr).property.2

end SerrePositivity.KST.SConstruction
