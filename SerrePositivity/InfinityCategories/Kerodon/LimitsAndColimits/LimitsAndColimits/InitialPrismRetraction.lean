module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FixedTerminalHomotopyStart

/-!
概要：正方形の初期側の時間辺と、空間方向の点への収縮を照合する。
方針：標準区間の端点と射影を同じ単体上で計算する。
規約：時間は第二因子。使われ方：元の根辺円柱の始点固定を余錐族へ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 点の円柱の初期端を含めると、空間の初期側の時間辺になる。 -/
lemma initialPrismRetraction_vertex :
    lift (stdSimplex.σ (0 : Fin 1) : (Δ[1] : SSet.{u}) ⟶ Δ[0]) (𝟙 Δ[1]) ≫
        (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
  rw [stdSimplex.δ_one_eq_const]
  rfl

/-- 初期側の時間辺を空間へ射影すると、初期頂点への同じ収縮になる。 -/
lemma initialPrismRetraction_fst :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ fst Δ[1] Δ[1] =
      stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 標準区間の両端はいずれも点への射影の切断である。 -/
lemma intervalRetraction_endpoint (i : Fin 2) :
    (stdSimplex.δ i : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ stdSimplex.σ (0 : Fin 1) = 𝟙 Δ[0] := by
  apply SSet.yonedaEquiv.injective
  fin_cases i <;> decide

/-- 初期側の時間零は、時間零の端面の初期頂点と同じ正方形の頂点。 -/
lemma initialPrismRetraction_zero :
    (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] =
      stdSimplex.δ (1 : Fin 2) ≫ SSet.ι₀ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 初期側の時間一も、時間一の端面の初期頂点と同じ正方形の頂点。 -/
lemma initialPrismRetraction_one :
    (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] =
      stdSimplex.δ (1 : Fin 2) ≫ SSet.ι₁ := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
