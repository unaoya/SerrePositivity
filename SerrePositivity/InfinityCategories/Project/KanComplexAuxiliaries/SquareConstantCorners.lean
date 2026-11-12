module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：下辺が基点付き loop、上辺・右辺が定値なら、正方形の四隅は同じ基点である。
方針：元の三つの辺の等式を零単体で評価し、共通の右上頂点を介して照合する。
規約：定値の値を仮定せず同定する。使われ方：円評価の Hom ホモトピーの端点固定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.IntervalSquare
end SerrePositivity.KST.Spectra.IntervalSquare
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.IntervalSquare

/-- 定値区間写像の頂点での値は、指定した元の零単体。 -/
lemma const_vertex {Y : SSet.{u}} (y : Y _⦋0⦌) (i : Fin 2) :
    (SSet.const (X := (Δ[1] : SSet.{u})) y).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = y := by
  simp only [SSet.const_app, SimplexCategory.const_eq_id]
  change Y.map (𝟙 (Opposite.op ⦋0⦌)) y = y
  exact ConcreteCategory.congr_hom (Y.map_id (Opposite.op ⦋0⦌)) y

/-- 定値区間写像の一頂点の値を指定すると、その定値写像そのものを同定できる。 -/
lemma constant_of_vertex {Y : SSet.{u}} {x : Y _⦋0⦌} {f : (Δ[1] : SSet.{u}) ⟶ Y}
    (h : ∃ y, f = SSet.const y)
    (hx : f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = x) :
    f = SSet.const x := by
  obtain ⟨y, rfl⟩ := h
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at hx
  subst x
  rfl

/-- 元の loop と二つの定値辺から、全ての隅を元の loop の基点へ厳密同定する。 -/
lemma corners_of_bottom_loop {Y : SSet.{u}} {x : Y _⦋0⦌} (e : Y.Edge x x)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y)
    (hb : lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ Q = SSet.yonedaEquiv.symm e.edge)
    (hr : ∃ y, lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u})) ≫ Q = SSet.const y)
    (ht : ∃ y, lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ Q = SSet.const y)
    (i j : Fin 2) :
    Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) = x := by
  have h00 := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Y ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) hb
  have h10 := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Y ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1)) hb
  change Q.app _ (stdSimplex.obj₀Equiv.symm 0,
    (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)).app _
      (stdSimplex.obj₀Equiv.symm 0)) = _ at h00
  change Q.app _ (stdSimplex.obj₀Equiv.symm 1,
    (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 0)).app _
      (stdSimplex.obj₀Equiv.symm 1)) = _ at h10
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] at h00 h10
  have hv0 : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  have hv1 : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by decide
  simp only [SSet.yonedaEquiv_symm_app, hv0] at h00
  simp only [SSet.yonedaEquiv_symm_app, hv1] at h10
  replace h00 := h00.trans e.src_eq
  replace h10 := h10.trans e.tgt_eq
  obtain ⟨r, hr⟩ := hr
  obtain ⟨t, ht⟩ := ht
  have rcorner (k : Fin 2) := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Y ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm k)) hr
  have tcorner (k : Fin 2) := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ Y ↦
    f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm k)) ht
  have hr' (k : Fin 2) : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm k) = r := by
    have h := rcorner k
    change Q.app _ ((SSet.const (X := (Δ[1] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 1)).app _ (stdSimplex.obj₀Equiv.symm k),
      stdSimplex.obj₀Equiv.symm k) = _ at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] using h
  have ht' (k : Fin 2) : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm 1) = t := by
    have h := tcorner k
    change Q.app _ (stdSimplex.obj₀Equiv.symm k,
      (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 1)).app _
        (stdSimplex.obj₀Equiv.symm k)) = _ at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex] using h
  have h11 : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) = x :=
    (hr' 1).trans ((hr' 0).symm.trans h10)
  have h01 : Q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1) = x :=
    (ht' 0).trans ((ht' 1).symm.trans h11)
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.const_vertex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.constant_of_vertex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_of_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.corners_of_bottom_loop := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.corners_of_bottom_loop
