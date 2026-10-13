module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import SerrePositivity.CommutativeAlgebra.AdicCompletionFlat
public import SerrePositivity.CommutativeAlgebra.AdicCompletionRegular
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 根の塔と完備化上の正則元

未完備の根の塔の平坦性を基底環へ制限し、共通の主イデアル完備化の正則性を
根の塔へ適用する。一般の正則性は AdicCompletionRegular に置き、旧 import の互換性を保つ。
Noether 基底上では、加群版と環版の完備化の比較を使い、完備化した塔も基底上平坦と示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 未完備の根の塔は基底環上平坦。零段の有限自由性と塔の各段上の平坦性を合成する。 -/
theorem flat_tower_over_base : Module.Flat A (Tower A t p) := by
  let := towerStage_free A t p 0
  let := flat_tower A t p 0
  exact Module.Flat.trans A (TowerStage A t p 0) (Tower A t p)

/-- 基底環上で `p` が正則なら、完備化した根の塔上でも `p` は正則。
未完備の塔の平坦性と、主イデアル完備化上の正則性保存を用いる。 -/
theorem isSMulRegular_p_completedTower (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (CompletedTower A t p) (p : CompletedTower A t p) := by
  let := flat_tower_over_base A t p
  have ht : IsSMulRegular (Tower A t p) (p : Tower A t p) := by
    simpa using hp.of_flat (S := Tower A t p)
  simpa using isSMulRegular_adicCompletion_span_singleton (Tower A t p) (p : Tower A t p) ht

/-- Noether 基底上では、p 進完備化した根の塔も基底環上平坦。
未完備塔自身の Noether 性は要求しない。 -/
theorem flat_completedTower_over_base [IsNoetherianRing A] :
    Module.Flat A (CompletedTower A t p) := by
  let := flat_tower_over_base A t p
  have hf := flat_adicCompletion_algebra_of_flat (S := Tower A t p) (Ideal.span {(p : A)})
  have hI : (Ideal.span {(p : A)}).map (algebraMap A (Tower A t p)) =
      Ideal.span {(p : Tower A t p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hf
  exact hf

/-- Noether基底では、完備塔は任意の有限段A_n上でも平坦。
有限段のNoether性と、未完備塔の各段上の平坦性を使う。 -/
theorem flat_completedTower_over_stage [IsNoetherianRing A] (n : ℕ) :
    Module.Flat (TowerStage A t p n) (CompletedTower A t p) := by
  let := towerStage_finite A t p n
  let : IsNoetherianRing (TowerStage A t p n) :=
    IsNoetherianRing.of_finite A (TowerStage A t p n)
  let := flat_tower A t p n
  have hf := flat_adicCompletion_algebra_of_flat (S := Tower A t p)
    (Ideal.span {(p : TowerStage A t p n)})
  have hI : (Ideal.span {(p : TowerStage A t p n)}).map
      (algebraMap (TowerStage A t p n) (Tower A t p)) = Ideal.span {(p : Tower A t p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [hI] at hf
  exact hf

end Section2
end SerrePositivity
