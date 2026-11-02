module

public import SerrePositivity.InfinityCategories.Core.RelativeInternalHomTrivialFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationInitialSpan

/-!
概要：始対象 Hom の終点評価を固定した族を、任意の単射パラメータ境界から延長する。
方針：評価の自明 Kan 性を、元の境界族と係数を保つテンソル境界に適用する。
規約：族のパラメータに充填性は不要。境界の射と底の評価を厳密に保持する。
使われ方：制限比較の評価固定円柱と三角形全体の族の高次比較を充填する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 任意の単射境界上の中間 Hom の族を、同じ評価のまま全パラメータへ延長できる。 -/
lemma exists_initialEvaluationFamily_of_mono {E B T K L : SSet.{u}}
    (q : E ⟶ B) (c : E _⦋0⦌) (hc : IsInitialVertex c) (y : B _⦋0⦌)
    (v : T ⟶ vertexFiber q y) (k : K ⟶ L) [Mono k]
    (W : T ⊗ K ⟶ leftFibrationInitialTotal q c y)
    (hW : W ≫ leftFibrationInitialEvaluation q c y = fst T K ≫ v) :
    ∃ U : T ⊗ L ⟶ leftFibrationInitialTotal q c y,
      U ≫ leftFibrationInitialEvaluation q c y = fst T L ≫ v ∧ (T ◁ k) ≫ U = W := by
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  have : Mono (T ◁ k) := (tensorLeft T).map_mono k
  have := TrivialKanFibration.mem (p := leftFibrationInitialEvaluation q c y)
    (T ◁ k) (inferInstance : Mono (T ◁ k))
  let sq : CommSq W (T ◁ k) (leftFibrationInitialEvaluation q c y) (fst T L ≫ v) :=
    ⟨by rw [hW, ← Category.assoc, whiskerLeft_fst]⟩
  exact ⟨sq.lift, sq.fac_right, sq.fac_left⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
