module
public import SerrePositivity.KST.SConstruction.TriangleLeftCancellationHorn
public import SerrePositivity.KST.SConstruction.EndpointFixedEdgeCylinders

/-! # 元の二面と実四面体を保持する端点固定の始辺消去
概要：選択した同じ外ホーン四面体の残る面から、両端固定比較円柱を構成する。
方針：残る面の三辺を単体恒等式で回収し、退化面と同じ対角に沿って正方形へ貼る。
規約：二つの元の全合成面・退化面・比較面を同じ四面体に保持する。
使われ方：高次 prism と相対的に選択できる、十二面の共通始辺の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {E : SSet.{u}} {x y z : E _⦋0⦌}
  {a : E.Edge x y} {b d : E.Edge y z} {c : E.Edge x z}
  (T : SSet.Edge.CompStruct a b c) (U : SSet.Edge.CompStruct a d c)
  (v : (triangleLeftCancellationChoices T U) _⦋0⦌)

/-- 元の二合成面を保持する同じ全四面体の残る実比較面。 -/
def triangleLeftCancellationTriangle : SSet.Edge.CompStruct (SSet.Edge.id y) d b := by
  let σ := SSet.yonedaEquiv (triangleLeftCancellationAt T U v)
  have h₁ : E.δ 1 σ = U.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleLeftCancellationAt_face T U v 1 (by decide)]
    simp only [triangleLeftCancellationFaces, Matrix.cons_val_one, Matrix.cons_val_zero,
      Equiv.apply_symm_apply]
  have h₂ : E.δ 2 σ = T.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleLeftCancellationAt_face T U v 2 (by decide)]
    simp [triangleLeftCancellationFaces]
  have h₃ : E.δ 3 σ = (SSet.Edge.CompStruct.compId a).simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, triangleLeftCancellationAt_face T U v 3 (by decide)]
    simp [triangleLeftCancellationFaces]
  refine SSet.Edge.CompStruct.mk (E.δ 0 σ) ?_ ?_ ?_
  · exact ((E.δ_comp_δ_apply (i := (0 : Fin 3)) (j := 2) (by decide) σ).symm.trans
      (congrArg (E.δ 0) h₃)).trans (SSet.Edge.CompStruct.compId a).d₀
  · have he := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self E (n := 1) (i := 0)) σ
    exact (he.trans (congrArg (E.δ 0) h₁)).trans U.d₀
  · exact ((E.δ_comp_δ_apply (i := (0 : Fin 3)) (j := 1) (by decide) σ).symm.trans
      (congrArg (E.δ 0) h₂)).trans T.d₀

/-- 比較面は元の同じ全四面体の零面そのもの。 -/
lemma triangleLeftCancellationTriangle_face :
    SSet.yonedaEquiv.symm (triangleLeftCancellationTriangle T U v).simplex =
      stdSimplex.δ 0 ≫ triangleLeftCancellationAt T U v := by
  change SSet.yonedaEquiv.symm
    (E.δ 0 (SSet.yonedaEquiv (triangleLeftCancellationAt T U v))) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, Equiv.symm_apply_apply]

/-- 元の比較面と同じ対角の退化面を持つ、両端固定の正方形データ。 -/
def triangleLeftCancellationTransport : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport b (SSet.Edge.id y) d :=
  ⟨b, SSet.Edge.id z, triangleLeftCancellationTriangle T U v,
    SSet.Edge.CompStruct.compId b⟩

/-- 元の比較面全体を上面に持つ全端点固定実円柱。 -/
def triangleLeftCancellationCylinder : EndpointFixedEdgeCylinder b d where
  homotopy :=
    { h := ThreeEdgeTransport.square (triangleLeftCancellationTransport T U v)
      h₀ := ThreeEdgeTransport.square_zero _
      h₁ := ThreeEdgeTransport.square_one _
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro q
        exact False.elim q.1.property }
  relative := by
    let R := triangleLeftCancellationTransport T U v
    have hs : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        ThreeEdgeTransport.square R = SSet.const y := by
      rw [ThreeEdgeTransport.square_start, mappingIdentityEdge_map, SSet.comp_const]
    have ht : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
        ThreeEdgeTransport.square R = SSet.const z := by
      rw [ThreeEdgeTransport.square_finish]
      change snd (Δ[0] : SSet.{u}) Δ[1] ≫
        SSet.yonedaEquiv.symm (SSet.Edge.id z).edge = _
      rw [mappingIdentityEdge_map, SSet.comp_const]
    change ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫ ThreeEdgeTransport.square R = _
    let hc := mapIsColimitOfPreservesOfIsColimit (tensorRight (Δ[1] : SSet.{u}))
      _ _ HomotopyFunctionComplex.BoundaryOne.isColimit
    apply hc.hom_ext
    rintro ⟨i⟩
    cases i
    · change (SSet.boundary.ι (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _ =
        (SSet.boundary.ι (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι, hs,
        whiskerRight_fst_assoc, ← Category.assoc (SSet.boundary.ι (1 : Fin 2)),
        SSet.boundary.ι_ι, SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    · change (SSet.boundary.ι (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _ =
        (SSet.boundary.ι (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _
      rw [← Category.assoc, ← comp_whiskerRight, SSet.boundary.ι_ι, ht,
        whiskerRight_fst_assoc, ← Category.assoc (SSet.boundary.ι (0 : Fin 2)),
        SSet.boundary.ι_ι, SSet.Edge.δ_zero_yonedaEquiv_symm,
        SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 同じ比較円柱の上面は、元の全四面体の同じ比較面を厳密に回収する。 -/
lemma triangleLeftCancellationCylinder_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ (triangleLeftCancellationCylinder T U v).homotopy.h =
      stdSimplex.δ 0 ≫ triangleLeftCancellationAt T U v := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ ThreeEdgeTransport.square _ = _
  rw [ThreeEdgeTransport.square_upper]
  exact triangleLeftCancellationTriangle_face T U v

end SerrePositivity.KST.SConstruction
