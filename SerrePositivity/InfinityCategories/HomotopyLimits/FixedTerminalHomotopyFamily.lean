module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRetractCosliceFamily
public import SerrePositivity.InfinityCategories.F1.PrismEndpointRightAnodyne
public import SerrePositivity.InfinityCategories.F1.MappingCylinderOverMono

/-!
概要：終点を固定した同じ根辺円柱へ、元の全余錐族を延長する。
方針：終端包含の right anodyne 性と相対 coslice の充填を使う。
規約：底と終点係数の全族を厳密に保つ。使われ方：指定余極限の全 Hom 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 空間の終端を時刻零へ移す二つの包含は、同じ正方形の頂点である。 -/
lemma terminalPrism_initialTime :
    (prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[1]) ≫ SSet.ι₀ =
      (SSet.const (stdSimplex.obj₀Equiv.symm 0) : Δ[1] ⟶ Δ[1]) ≫
        prismEndpoint 1 Δ[1] := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

variable {E B T : SSet.{u}} {W V : (Δ[1] : SSet.{u}) ⟶ E}
  (H : SSet.Homotopy W V) (z : E _⦋0⦌)
  (hz : prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ H.h = SSet.const z)

include hz in
/-- 終点固定の円柱は、元の辺と同じ終端図式を厳密に持つ。 -/
lemma fixedTerminalHomotopyFamily_terminal_diagram :
    (prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[1]) ≫ W =
      prismEndpoint 1 Δ[1] ≫ H.h := by
  calc
    _ = (prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1]) ≫ (SSet.ι₀ ≫ H.h) :=
      congrArg (fun k ↦ (prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1]) ≫ k) H.h₀.symm
    _ = _ := by
      rw [← Category.assoc, terminalPrism_initialTime, Category.assoc, hz,
        SSet.comp_const]

variable (q : E ⟶ B) [InnerFibration q]
  (hq : fst (Δ[1] : SSet.{u}) Δ[1] ≫ (W ≫ q) = H.h ≫ q)
  (a : T ⟶ sliceUnder W)

/-- 底と終点係数を保つ、同じ円柱上の全パラメータの余錐族。 -/
def fixedTerminalHomotopyFamily : T ⟶ sliceUnder H.h :=
  relativeRetractCosliceFamily q H.h W (fst Δ[1] Δ[1]) (prismEndpoint 1 Δ[1])
    (prismEndpoint_one_rightAnodyne Δ[1]) hq
    (fixedTerminalHomotopyFamily_terminal_diagram H z hz) a

/-- 終端の全係数は、元の族の同じ終端への引き戻しである。 -/
lemma fixedTerminalHomotopyFamily_terminal :
    fixedTerminalHomotopyFamily H z hz q hq a ≫
        sliceUnderRestrict H.h (prismEndpoint 1 Δ[1]) =
      a ≫ normalizedCoconeRestriction W (prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1])
        (fixedTerminalHomotopyFamily_terminal_diagram H z hz) :=
  relativeRetractCosliceFamily_terminal _ _ _ _ _ _ _ _ _

/-- 底は元の全余錐族の時間に依存しない引き戻しである。 -/
lemma fixedTerminalHomotopyFamily_base :
    fixedTerminalHomotopyFamily H z hz q hq a ≫ sliceUnderPostcomp H.h q =
      (a ≫ sliceUnderPostcomp W q) ≫
        normalizedCoconeRestriction (W ≫ q) (fst Δ[1] Δ[1]) hq :=
  relativeRetractCosliceFamily_base _ _ _ _ _ _ _ _ _

/-- 可変終点も元の E 内の全族のまま保つ。 -/
lemma fixedTerminalHomotopyFamily_projection :
    fixedTerminalHomotopyFamily H z hz q hq a ≫ sliceUnderProjection H.h =
      a ≫ sliceUnderProjection W :=
  relativeRetractCosliceFamily_projection _ _ _ _ _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
