module
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellation
public import SerrePositivity.KST.SConstruction.AnodyneFixedHomotopy
public import SerrePositivity.KST.SConstruction.BoundaryTensorHomExt
public import SerrePositivity.KST.SConstruction.AnodynePrescribedComparison

/-! # 元の全三面を固定する始辺消去の二選択の実高次比較
概要：二つの始辺消去四面体を、その全指定三面を全時刻固定して比較する。
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
  {a : E.Edge x y} {b d : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct a d c)
  (v w : (triangleLeftCancellationChoices T U) _⦋0⦌)

/-- 元の全三面を固定する、二つの全始辺消去四面体の実比較データ。 -/
def triangleLeftCancellationComparisonData :=
  anodyneFixedHomotopyData (horn 3 (0 : Fin 4)).ι
    (anodyneExtensions.horn_ι (0 : Fin 4))
    (triangleLeftCancellationAt T U v) (triangleLeftCancellationAt T U w)
    ((anodyneExtensionAt_fac _ _ v).trans (anodyneExtensionAt_fac _ _ w).symm)

/-- 元の全四面体を両端に持つ同じ実高次比較円柱。 -/
def triangleLeftCancellationComparison : SSet.Homotopy
    (triangleLeftCancellationAt T U v) (triangleLeftCancellationAt T U w) :=
  (triangleLeftCancellationComparisonData T U v w).val

/-- 元の三次外ホーン全体を全比較時刻で厳密に固定する。 -/
lemma triangleLeftCancellationComparison_relative :
    ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationComparison T U v w).h =
      fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ (horn 3 (0 : Fin 4)).ι ≫
        triangleLeftCancellationAt T U v :=
  (triangleLeftCancellationComparisonData T U v w).property

/-- 全指定三面は元の二合成面と退化面を全時刻でそのまま保持する。 -/
lemma triangleLeftCancellationComparison_face (j : Fin 4) (hj : j ≠ 0) :
    (stdSimplex.δ j ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationComparison T U v w).h =
      fst (Δ[2] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationFaces T U j hj := by
  rw [← horn.ι_ι (0 : Fin 4) j hj, comp_whiskerRight, Category.assoc,
    triangleLeftCancellationComparison_relative, whiskerRight_fst_assoc]
  rw [← Category.assoc (horn.ι (0 : Fin 4) j hj), horn.ι_ι,
    triangleLeftCancellationAt_face T U v j hj]

/-- 同じ高次比較の零面は、実比較三角形全体を両端に持つ同じ実円柱。 -/
def triangleLeftCancellationTriangleComparison : SSet.Homotopy
    (SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex)
    (SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U w).simplex) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (triangleLeftCancellationComparison T U v w) (stdSimplex.δ 0))
    (triangleLeftCancellationTriangle_face T U v)
    (triangleLeftCancellationTriangle_face T U w).symm

/-- 元の比較三角形の全高次比較は、四面体比較の同じ全零面。 -/
lemma triangleLeftCancellationTriangleComparison_h :
    (triangleLeftCancellationTriangleComparison T U v w).h =
      (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationComparison T U v w).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 同じ比較三角形の全三辺は、高次比較の全時刻で厳密に固定する。 -/
lemma triangleLeftCancellationTriangleComparison_edge (i : Fin 3) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationTriangleComparison T U v w).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ stdSimplex.δ i ≫
        SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex := by
  have he : stdSimplex.δ.{u} i ≫ stdSimplex.δ (0 : Fin 4) =
      stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ i.succ := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro k
    fin_cases i <;> fin_cases k <;> rfl
  rw [triangleLeftCancellationTriangleComparison_h, ← Category.assoc,
    ← comp_whiskerRight, he, comp_whiskerRight, Category.assoc,
    triangleLeftCancellationComparison_face T U v w i.succ (Fin.succ_ne_zero i),
    whiskerRight_fst_assoc, triangleLeftCancellationTriangle_face]
  rw [← Category.assoc (stdSimplex.δ i), he, Category.assoc,
    triangleLeftCancellationAt_face T U v i.succ (Fin.succ_ne_zero i)]

/-- 高次比較は元の比較三角形の全境界を全時刻で厳密に固定する。 -/
lemma triangleLeftCancellationTriangleComparison_boundary :
    ((SSet.boundary 2).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationTriangleComparison T U v w).h =
      fst (∂Δ[2] : SSet.{u}) Δ[1] ≫ (SSet.boundary 2).ι ≫
        SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex := by
  apply boundaryTensorHomExt
  intro i
  rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι,
    triangleLeftCancellationTriangleComparison_edge, whiskerRight_fst_assoc,
    ← Category.assoc (SSet.boundary.ι i), SSet.boundary.ι_ι]

variable {B : SSet.{u}} (p : E ⟶ B) [Fibration p]
  (H : SSet.Homotopy (triangleLeftCancellationAt T U v ≫ p)
    (triangleLeftCancellationAt T U w ≫ p))
  (hr : ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U ≫ p)

/-- 元の全基底比較と全三面を同時に保持する、同じ二四面体の実高次比較。 -/
def triangleLeftCancellationComparisonOverData :
    {K : SSet.Homotopy (triangleLeftCancellationAt T U v) (triangleLeftCancellationAt T U w) //
      K.h ≫ p = H.h ∧ ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫ K.h =
        fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U} := by
  let C := familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (triangleLeftCancellationHorn T U))
    (anodyneExtensionAt_fac _ _ v) (anodyneExtensionAt_fac _ _ w).symm
  have hC : C.h = fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U :=
    familyHomotopyEndpointTransport_h _ _ _
  let D := anodynePrescribedComparisonData (horn 3 (0 : Fin 4)).ι
    (anodyneExtensions.horn_ι (0 : Fin 4)) p _ _ H C
    (by rw [hC]; exact (Category.assoc _ _ _).trans hr.symm)
  exact ⟨D.val, D.property.1, D.property.2.trans hC⟩

omit [KanComplex E]

/-- 同じ持ち上げの全射影は、元の全基底比較円柱そのもの。 -/
lemma triangleLeftCancellationComparisonOverData_projection :
    (triangleLeftCancellationComparisonOverData T U v w p H hr).val.h ≫ p = H.h :=
  (triangleLeftCancellationComparisonOverData T U v w p H hr).property.1

/-- 全三面は、同じ持ち上げの全比較時刻で厳密に固定する。 -/
lemma triangleLeftCancellationComparisonOverData_relative :
    ((horn 3 (0 : Fin 4)).ι ▷ (Δ[1] : SSet.{u})) ≫
        (triangleLeftCancellationComparisonOverData T U v w p H hr).val.h =
      fst (Λ[3, 0] : SSet.{u}) Δ[1] ≫ triangleLeftCancellationHorn T U :=
  (triangleLeftCancellationComparisonOverData T U v w p H hr).property.2

end SerrePositivity.KST.SConstruction
