module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EdgeTerminalCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EdgeCosliceIntervalMap

/-!
概要：固定辺の終点への恒等余錐を、同じ指定終点の余錐空間の基点として保持する。
方針：既存の退化二単体の終点余錐を使い、両端の制限を元の辺と恒等辺に計算する。
規約：切断の選択は使わず、元の辺の一次単体を保持する。
使われ方：HTT 5.5.5.13 の二つの fiber の指定基点。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ C)

/-- 元の終点余錐の頂点は、元の辺の終点そのもの。 -/
lemma edgeTerminalCocone_vertex :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).vertex = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) := by
  have h := congrArg (fun F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0] ⟶ C ↦
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0] ≫ F)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_restrict_val g)
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).restrict (stdSimplex.δ (0 : Fin 2))).vertex = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, SSet.comp_const, ← SSet.yonedaEquiv_symm_zero,
    Equiv.apply_symm_apply] at h
  exact h

/-- 元の終点への恒等余錐は、元の指定終点を持つ余錐空間の基点。 -/
def edgeTerminalMappingPoint :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace g (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g, by
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _ 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, edgeTerminalCocone_vertex]⟩

/-- 基点を終点側へ制限すると、元の同じ恒等余錐の定値写像となる。 -/
lemma edgeTerminalMappingPoint_target_val :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap g (stdSimplex.δ (0 : Fin 2))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))).app _
        (edgeTerminalMappingPoint g)).val).val =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_restrict_val g

/-- 基点を始点側へ制限すると、元の辺そのものを表す余錐の射となる。 -/
lemma edgeTerminalMappingPoint_source_val :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap g (stdSimplex.δ (1 : Fin 2))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g))).app _
        (edgeTerminalMappingPoint g)).val).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ g := by
  have h : (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.σ 1 = 𝟙 Δ[1] := by
    apply SSet.yonedaEquiv.injective
    decide
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (1 : Fin 3)) ≫
    stdSimplex.σ 1 ≫ g = _
  rw [Category.assoc, ← Category.assoc (stdSimplex.δ (1 : Fin 3)), h, Category.id_comp]

/-- 元の終点を等号で指定しても、同じ恒等余錐を基点として保持する。 -/
def edgeTerminalMappingPointAt (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace g y) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g, by
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, edgeTerminalCocone_vertex, hy]⟩

/-- 終点の表示を変えても、終点側への制限は同じ指定恒等余錐である。 -/
lemma edgeTerminalMappingPointAt_target_val (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap g (stdSimplex.δ (0 : Fin 2)) y).app _
      (edgeTerminalMappingPointAt g y hy)).val).val = SSet.const y := by
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).restrict (stdSimplex.δ (0 : Fin 2))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_restrict_val, hy]

/-- 終点の表示を変えても、始点側の制限は元の辺そのもの。 -/
lemma edgeTerminalMappingPointAt_source_val (y : C _⦋0⦌)
    (hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) = y) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap g (stdSimplex.δ (1 : Fin 2)) y).app _
      (edgeTerminalMappingPointAt g y hy)).val).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ g :=
  edgeTerminalMappingPoint_source_val g

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
