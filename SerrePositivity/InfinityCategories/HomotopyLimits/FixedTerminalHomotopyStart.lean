module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedTerminalHomotopyFamily

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 時間零の空間終端は、空間終端上の時間零と同じ正方形の頂点。 -/
lemma terminalPrism_initialVertex :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ SSet.ι₀ =
      stdSimplex.δ (1 : Fin 2) ≫ prismEndpoint 1 Δ[1] := by
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
      prismEndpoint 1 Δ[1]) ≫ fst Δ[1] Δ[1] = stdSimplex.δ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)
  (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)
  (a : T ⟶ sliceUnder W)
local notation "U" => fixedTerminalHomotopyFamily H z hz q hq a

/-- 同じ延長族の時間零の端面。 -/
def fixedTerminalHomotopyStartFamily : T ⟶ sliceUnder W :=
  U ≫ normalizedCoconeRestriction H.h SSet.ι₀ H.h₀

/-- 時間零の端面の底は、元の全族の底と厳密に一致する。 -/
lemma fixedTerminalHomotopyStartFamily_base :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫ sliceUnderPostcomp W q =
      a ≫ sliceUnderPostcomp W q := by
  apply sliceUnderUncurry_injective (W ≫ q)
  rw [sliceUnderUncurry_postcomp, fixedTerminalHomotopyStartFamily,
    normalizedCoconeRestriction_uncurry, Category.assoc, ← sliceUnderUncurry_postcomp,
    fixedTerminalHomotopyFamily_base, normalizedCoconeRestriction_uncurry,
    ← Category.assoc, ← joinMap_comp, Category.comp_id, initialTime_fst,
    joinMap_id, Category.id_comp]

/-- 時間零の端面の終端係数も、元の全族と厳密に一致する。 -/
lemma fixedTerminalHomotopyStartFamily_terminal :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫
        sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) =
      a ≫ sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) := by
  apply sliceUnderUncurry_injective (stdSimplex.δ (0 : Fin 2) ≫ W)
  rw [sliceUnderUncurry_restrict, fixedTerminalHomotopyStartFamily,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, terminalPrism_initialVertex]
  rw [show joinMap (stdSimplex.δ (1 : Fin 2) ≫ prismEndpoint 1 Δ[1]) (𝟙 T) =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫ joinMap (prismEndpoint 1 Δ[1]) (𝟙 T)
      from by simpa only [Category.id_comp] using
        (joinMap_comp (stdSimplex.δ (1 : Fin 2)) (prismEndpoint 1 Δ[1]) (𝟙 T) (𝟙 T)),
    Category.assoc, ← sliceUnderUncurry_restrict, fixedTerminalHomotopyFamily_terminal,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, ← joinMap_comp,
    Category.comp_id, ← Category.assoc, initialVertex_terminalPrism_fst,
    sliceUnderUncurry_restrict]

/-- 時間零の端面は元の可変終点の全族も保持する。 -/
lemma fixedTerminalHomotopyStartFamily_projection :
    fixedTerminalHomotopyStartFamily H z hz q hq a ≫ sliceUnderProjection W =
      a ≫ sliceUnderProjection W := by
  rw [fixedTerminalHomotopyStartFamily, Category.assoc,
    normalizedCoconeRestriction_projection, fixedTerminalHomotopyFamily_projection]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
