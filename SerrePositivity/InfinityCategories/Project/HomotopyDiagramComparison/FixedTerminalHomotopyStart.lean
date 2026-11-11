module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedTerminalHomotopyFamily

/-!
概要：同じ根辺円柱上に延長した全余錐族の時間零の端面を元の族と照合する。
方針：join の uncurry と正方形の同じ頂点・射影の等式で底と終端を計算する。
規約：全パラメータを保持する。使われ方：相対 coslice 比較による左端面の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 時間零の空間終端は、空間終端上の時間零と同じ正方形の頂点。 -/
lemma terminalPrism_initialVertex :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ SSet.ι₀ =
      stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 時間零の包含を空間へ戻すと恒等射。 -/
lemma initialTime_fst :
    (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫ fst Δ[1] Δ[1] = 𝟙 Δ[1] := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 終端上の時間零を空間へ戻すと元の終端包含。 -/
lemma initialVertex_terminalPrism_fst :
    ((stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) ≫ fst Δ[1] Δ[1] = stdSimplex.δ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)
  (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W)
local notation "U" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily H z hz q hq a

/-- 同じ延長族の時間零の端面。 -/
def fixedTerminalHomotopyStartFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder W :=
  U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction H.h SSet.ι₀ H.h₀

/-- 時間零の端面の底は、元の全族の底と厳密に一致する。 -/
lemma fixedTerminalHomotopyStartFamily_base :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp W q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (W ≫ q)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, fixedTerminalHomotopyStartFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_base, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry,
    ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, initialTime_fst,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 時間零の端面の終端係数も、元の全族と厳密に一致する。 -/
lemma fixedTerminalHomotopyStartFamily_terminal :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective (stdSimplex.δ (0 : Fin 2) ≫ W)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, fixedTerminalHomotopyStartFamily,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.comp_id, terminalPrism_initialVertex]
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) (𝟙 T) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) (𝟙 T)
      from by simpa only [Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (stdSimplex.δ (1 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1]) (𝟙 T) (𝟙 T)),
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_terminal,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.normalizedCoconeRestriction_uncurry, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.comp_id, ← Category.assoc, initialVertex_terminalPrism_fst,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict]

/-- 時間零の端面は元の可変終点の全族も保持する。 -/
lemma fixedTerminalHomotopyStartFamily_projection :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W := by
  rw [fixedTerminalHomotopyStartFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedTerminalHomotopyFamily_projection]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
