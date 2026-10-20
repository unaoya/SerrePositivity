module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedTerminalHomotopyStart
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation

/-!
概要：同じ根辺円柱上の全余錐族を、時間一の実際の右端面へ制限する。
方針：正方形の頂点・射影を照合し、底と終端係数を元の族へ戻す。
規約：図式と全パラメータを保持する。使われ方：元の右四面体族との相対比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 時間一の空間終端は、空間終端上の時間一と同じ正方形の頂点。 -/
lemma terminalPrism_finalVertex :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ SSet.ι₁ =
      stdSimplex.δ (0 : Fin 2) ≫ prismEndpoint 1 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 時間一の包含も空間射影の切断。 -/
lemma finalTime_fst :
    (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫ fst Δ[1] Δ[1] = 𝟙 Δ[1] := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)

include hz in
/-- 元の二つの辺の終端図式は、同じ固定頂点として厳密に一致する。 -/
lemma fixedTerminalHomotopy_end_terminal_diagram :
    stdSimplex.δ (0 : Fin 2) ≫ W = stdSimplex.δ (0 : Fin 2) ≫ V := by
  calc
    _ = (stdSimplex.δ (0 : Fin 2) ≫ SSet.ι₀) ≫ H.h := by rw [Category.assoc, H.h₀]
    _ = stdSimplex.δ (1 : Fin 2) ≫ (prismEndpoint 1 Δ[1] ≫ H.h) := by
      rw [terminalPrism_initialVertex, Category.assoc]
    _ = SSet.const z := by rw [hz, SSet.comp_const]
    _ = stdSimplex.δ (0 : Fin 2) ≫ (prismEndpoint 1 Δ[1] ≫ H.h) := by
      rw [hz, SSet.comp_const]
    _ = (stdSimplex.δ (0 : Fin 2) ≫ SSet.ι₁) ≫ H.h := by
      rw [terminalPrism_finalVertex, Category.assoc]
    _ = _ := by rw [Category.assoc, H.h₁]

variable (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)

include hq in
omit [InnerFibration q] in
/-- 同じ根辺円柱の二端の底の図式は、厳密に一致する。 -/
lemma fixedTerminalHomotopy_end_base_diagram : W ≫ q = V ≫ q := by
  calc
    _ = (SSet.ι₁ ≫ fst Δ[1] Δ[1]) ≫ (W ≫ q) := by rw [finalTime_fst, Category.id_comp]
    _ = SSet.ι₁ ≫ (H.h ≫ q) := by rw [Category.assoc, hq]
    _ = _ := by rw [← Category.assoc, H.h₁]

variable (a : T ⟶ sliceUnder W)
local notation "U" => fixedTerminalHomotopyFamily H z hz q hq a

/-- 同じ延長族の時間一の実際の端面。 -/
def fixedTerminalHomotopyEndFamily : T ⟶ sliceUnder V :=
  U ≫ normalizedCoconeRestriction H.h SSet.ι₁ H.h₁

/-- 時間一の端面の底も、元の族の底の同じ表示変更である。 -/
lemma fixedTerminalHomotopyEndFamily_base :
    fixedTerminalHomotopyEndFamily H z hz q hq a ≫ sliceUnderPostcomp V q =
      (a ≫ sliceUnderPostcomp W q) ≫
        eqToHom (congrArg sliceUnder (fixedTerminalHomotopy_end_base_diagram H q hq)) := by
  apply sliceUnderUncurry_injective (V ≫ q)
  rw [sliceUnderUncurry_postcomp, fixedTerminalHomotopyEndFamily,
    normalizedCoconeRestriction_uncurry, Category.assoc, ← sliceUnderUncurry_postcomp,
    fixedTerminalHomotopyFamily_base, normalizedCoconeRestriction_uncurry,
    ← Category.assoc, ← joinMap_comp, Category.comp_id, finalTime_fst,
    joinMap_id, Category.id_comp,
    sliceUnderUncurry_eqToHom (fixedTerminalHomotopy_end_base_diagram H q hq)]

/-- 時間一の端面の終端係数は、元の全族と同じ固定頂点の表示変更である。 -/
lemma fixedTerminalHomotopyEndFamily_terminal :
    fixedTerminalHomotopyEndFamily H z hz q hq a ≫
        sliceUnderRestrict V (stdSimplex.δ (0 : Fin 2)) =
      a ≫ normalizedCoconeRestriction W (stdSimplex.δ (0 : Fin 2))
        (fixedTerminalHomotopy_end_terminal_diagram H z hz) := by
  apply sliceUnderUncurry_injective (stdSimplex.δ (0 : Fin 2) ≫ V)
  rw [sliceUnderUncurry_restrict, fixedTerminalHomotopyEndFamily,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, terminalPrism_finalVertex]
  rw [show joinMap (stdSimplex.δ (0 : Fin 2) ≫ prismEndpoint 1 Δ[1]) (𝟙 T) =
      joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T) ≫ joinMap (prismEndpoint 1 Δ[1]) (𝟙 T)
      from by simpa only [Category.id_comp] using
        (joinMap_comp (stdSimplex.δ (0 : Fin 2)) (prismEndpoint 1 Δ[1]) (𝟙 T) (𝟙 T)),
    Category.assoc, ← sliceUnderUncurry_restrict, fixedTerminalHomotopyFamily_terminal,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, ← Category.assoc, ← terminalPrism_finalVertex,
    Category.assoc, finalTime_fst, Category.comp_id, normalizedCoconeRestriction_uncurry]

/-- 時間一の端面も元の可変終点の全族を保つ。 -/
lemma fixedTerminalHomotopyEndFamily_projection :
    fixedTerminalHomotopyEndFamily H z hz q hq a ≫ sliceUnderProjection V =
      a ≫ sliceUnderProjection W := by
  rw [fixedTerminalHomotopyEndFamily, Category.assoc,
    normalizedCoconeRestriction_projection, fixedTerminalHomotopyFamily_projection]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
