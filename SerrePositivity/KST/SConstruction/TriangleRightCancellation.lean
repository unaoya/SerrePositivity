module
public import SerrePositivity.KST.SConstruction.TriangleRightCancellationHorn
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders

/-! # 元の二面と実四面体を保持する端点固定の終辺消去
概要：選択した同じ外ホーン四面体の残る面から、両端固定比較円柱を構成する。
方針：残る面の三辺を単体恒等式で回収し、同じ実比較面を円柱へ移す。
規約：二つの元の全合成面・退化面・比較面を同じ四面体に保持する。
使われ方：高次 prism と相対的に選択できる、十二面の共通終辺の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a d : E.Edge x y} {b : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct d b c)
  (v : (triangleRightCancellationChoices T U) _⦋0⦌)

/-- 元の二合成面を保持する同じ全四面体の残る実比較面。 -/
def triangleRightCancellationTriangle : SSet.Edge.CompStruct a (SSet.Edge.id y) d := by
  let σ := SSet.yonedaEquiv (triangleRightCancellationAt T U v)
  have h₀ : E.δ 0 σ = (SSet.Edge.CompStruct.idComp b).simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleRightCancellationAt_face T U v 0 (by decide)]
    simp [triangleRightCancellationFaces]
  have h₁ : E.δ 1 σ = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleRightCancellationAt_face T U v 1 (by decide)]
    simp [triangleRightCancellationFaces]
  have h₂ : E.δ 2 σ = T.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleRightCancellationAt_face T U v 2 (by decide)]
    simp [triangleRightCancellationFaces]
  refine SSet.Edge.CompStruct.mk (E.δ 3 σ) ?_ ?_ ?_
  · have he := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 1) (i := 2)) σ
    exact (he.symm.trans (congrArg (E.δ 2) h₂)).trans T.d₂
  · exact ((E.δ_comp_δ_apply (i := (0 : Fin 3)) (j := 2) (by decide) σ).trans
      (congrArg (E.δ 2) h₀)).trans (SSet.Edge.CompStruct.idComp b).d₂
  · exact ((E.δ_comp_δ_apply (i := (1 : Fin 3)) (j := 2) (by decide) σ).trans
      (congrArg (E.δ 2) h₁)).trans U.d₂

/-- 比較面は元の同じ全四面体の第三面そのもの。 -/
lemma triangleRightCancellationTriangle_face :
    SSet.yonedaEquiv.symm (triangleRightCancellationTriangle T U v).simplex =
      stdSimplex.δ 3 ≫ triangleRightCancellationAt T U v := by
  change SSet.yonedaEquiv.symm
    (E.δ 3 (SSet.yonedaEquiv (triangleRightCancellationAt T U v))) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, Equiv.symm_apply_apply]

/-- 元の比較面全体を下面に保持する全端点固定実円柱。 -/
def triangleRightCancellationCylinder : EndpointFixedEdgeCylinder a d :=
  ⟨endpointFixedTriangleHomotopy (triangleRightCancellationTriangle T U v),
    endpointFixedTriangleHomotopy_relative (triangleRightCancellationTriangle T U v)⟩

/-- 同じ比較円柱の下面は、元の全四面体の同じ比較面を厳密に回収する。 -/
lemma triangleRightCancellationCylinder_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ (triangleRightCancellationCylinder T U v).homotopy.h =
      stdSimplex.δ 3 ≫ triangleRightCancellationAt T U v :=
  (endpointFixedTriangleHomotopy_triangle _).trans (triangleRightCancellationTriangle_face T U v)

end SerrePositivity.KST.SConstruction
