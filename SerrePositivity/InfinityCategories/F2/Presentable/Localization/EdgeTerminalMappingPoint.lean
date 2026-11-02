module

public import SerrePositivity.InfinityCategories.Stable.EdgeTerminalCocone
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.F1.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap

/-!
概要：固定辺の終点への恒等余錐を、同じ指定終点の余錐空間の基点として保持する。
方針：既存の退化二単体の終点余錐を使い、両端の制限を元の辺と恒等辺に計算する。
規約：切断の選択は使わず、元の辺の一次単体を保持する。
使われ方：HTT 5.5.5.13 の二つの fiber の指定基点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ C)

/-- 元の終点余錐の頂点は、元の辺の終点そのもの。 -/
lemma edgeTerminalCocone_vertex :
    (edgeTerminalCocone g).vertex = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) := by
  have h := congrArg (fun F : join (Δ[0] : SSet.{u}) Δ[0] ⟶ C ↦
    SSet.yonedaEquiv (joinInr Δ[0] Δ[0] ≫ F)) (edgeTerminalCocone_restrict_val g)
  change ((edgeTerminalCocone g).restrict (stdSimplex.δ (0 : Fin 2))).vertex = _ at h
  rw [JoinCocone.vertex_restrict, SSet.comp_const, ← SSet.yonedaEquiv_symm_zero,
    Equiv.apply_symm_apply] at h
  exact h

/-- 元の終点への恒等余錐は、元の指定終点を持つ余錐空間の基点。 -/
def edgeTerminalMappingPoint :
    (coconeMappingSpace g (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))) _⦋0⦌ :=
  ⟨edgeTerminalCocone g, by
    change (edgeTerminalCocone g).vertex = PinchedHom.constant _ 0
    rw [pinchedConstant_zero, edgeTerminalCocone_vertex]⟩

/-- 基点を終点側へ制限すると、元の同じ恒等余錐の定値写像となる。 -/
lemma edgeTerminalMappingPoint_target_val :
    (((cosliceRestrictionFiberMap g (stdSimplex.δ (0 : Fin 2))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))).app _
        (edgeTerminalMappingPoint g)).val).val =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g)) :=
  edgeTerminalCocone_restrict_val g

/-- 基点を始点側へ制限すると、元の辺そのものを表す余錐の射となる。 -/
lemma edgeTerminalMappingPoint_source_val :
    (((cosliceRestrictionFiberMap g (stdSimplex.δ (1 : Fin 2))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))).app _
        (edgeTerminalMappingPoint g)).val).val = (joinStdSimplexIso 0 0).hom ≫ g := by
  have h : (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.σ 1 = 𝟙 Δ[1] := by
    apply SSet.yonedaEquiv.injective
    decide
  change joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
    ((joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g) = _
  rw [← Category.assoc, joinStdSimplexIso_one_vertex]
  change ((joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (1 : Fin 3)) ≫
    stdSimplex.σ 1 ≫ g = _
  rw [Category.assoc, ← Category.assoc (stdSimplex.δ (1 : Fin 3)), h, Category.id_comp]

/-- 元の終点を等号で指定しても、同じ恒等余錐を基点として保持する。 -/
def edgeTerminalMappingPointAt (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (coconeMappingSpace g y) _⦋0⦌ :=
  ⟨edgeTerminalCocone g, by
    change (edgeTerminalCocone g).vertex = PinchedHom.constant y 0
    rw [pinchedConstant_zero, edgeTerminalCocone_vertex, hy]⟩

/-- 終点の表示を変えても、終点側への制限は同じ指定恒等余錐である。 -/
lemma edgeTerminalMappingPointAt_target_val (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (((cosliceRestrictionFiberMap g (stdSimplex.δ (0 : Fin 2)) y).app _
      (edgeTerminalMappingPointAt g y hy)).val).val = SSet.const y := by
  change ((edgeTerminalCocone g).restrict (stdSimplex.δ (0 : Fin 2))).val = _
  rw [edgeTerminalCocone_restrict_val, hy]

/-- 終点の表示を変えても、始点側の制限は元の辺そのもの。 -/
lemma edgeTerminalMappingPointAt_source_val (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (((cosliceRestrictionFiberMap g (stdSimplex.δ (1 : Fin 2)) y).app _
      (edgeTerminalMappingPointAt g y hy)).val).val = (joinStdSimplexIso 0 0).hom ≫ g :=
  edgeTerminalMappingPoint_source_val g

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
