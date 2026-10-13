module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedTensorEvaluation
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 有限段のイデアルを完備塔へ拡張した商の長さ

完備塔上の商を、有限段の商のテンソル積と実際の代数同型で同定する。
有限段の商が有限長なら、正規化長さはその通常長さを段の階数で割った値となる。
完備塔の Noether 性や perfectoid 性の引用は使わない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

/-- 有限段の完備塔上の作用を、商とテンソル積の代数構造と同じ加群構造で固定する。 -/
local instance completedQuotientStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

include hp in
/-- 有限段のイデアルを完備塔へ拡張した商の正規化長さは、有限段の通常商長さを
段の階数で割った値。零商も含み、イデアルの追加の性質は有限長性から必要な分だけ導く。 -/
theorem completedNormalizedLength_quotient_eq_length (n : ℕ) (I : Ideal (TowerStage A t p n))
    (hIquot : IsFiniteLength (TowerStage A t p n) (TowerStage A t p n ⧸ I)) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ I.map (algebraMap (TowerStage A t p n) (CompletedTower A t p))) =
      (Module.length (TowerStage A t p n) (TowerStage A t p n ⧸ I) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  rw [(completedNormalizedLength A t p ht).len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (CompletedTower A t p) I).toLinearEquiv]
  exact completedNormalizedLength_tensor_eq_length A t p ht hp n _ hIquot

end SerrePositivity.RootTowerLength
