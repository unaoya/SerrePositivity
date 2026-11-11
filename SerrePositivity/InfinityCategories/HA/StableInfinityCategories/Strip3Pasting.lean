module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Grid22Pasting

/-!
概要：同じ三面の長方形から外側の押し出し性を得る。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def strip3Part {X : SSet.{u}} (F : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 4) :
    (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X := (stdSimplex.δ i ▷ Δ[1]) ≫ F

def strip3Square {X : SSet.{u}} (F : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 4)
    (j : Fin 3) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (strip3Part F i) j

lemma strip3Square_left_long {X : SSet.{u}}
    (F : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶ X) : strip3Square F 1 2 = strip3Square F 3 1 := by
  have h : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.δ (1 : Fin 4) = stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    decide
  change ((stdSimplex.δ (2 : Fin 3) ▷ Δ[1]) ≫
      (stdSimplex.δ (1 : Fin 4) ▷ Δ[1])) ≫ F =
    ((stdSimplex.δ (1 : Fin 3) ▷ Δ[1]) ≫ (stdSimplex.δ (3 : Fin 4) ▷ Δ[1])) ≫ F
  rw [← comp_whiskerRight, ← comp_whiskerRight, h]

lemma strip3Square_right_last {X : SSet.{u}}
    (F : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶ X) : strip3Square F 1 0 = strip3Square F 0 0 := by
  have h : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      stdSimplex.δ (1 : Fin 4) = stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    decide
  change ((stdSimplex.δ (0 : Fin 3) ▷ Δ[1]) ≫
      (stdSimplex.δ (1 : Fin 4) ▷ Δ[1])) ≫ F =
    ((stdSimplex.δ (0 : Fin 3) ▷ Δ[1]) ≫ (stdSimplex.δ (0 : Fin 4) ▷ Δ[1])) ≫ F
  rw [← comp_whiskerRight, ← comp_whiskerRight, h]

lemma isPushoutSquare_strip3_outer {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[3] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (h01 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 3 2))
    (h12 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 3 0))
    (h23 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 0 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 1 1) := by
  have hfirst := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting (strip3Part F 3) h01 h12
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting (strip3Part F 1)
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 1 2)
    rw [strip3Square_left_long]
    exact hfirst
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (strip3Square F 1 0)
    rw [strip3Square_right_last]
    exact h23

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
