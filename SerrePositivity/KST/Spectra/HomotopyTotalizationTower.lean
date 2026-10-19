module

public import SerrePositivity.KST.Spectra.HomotopyTotalizationEvaluation

/-!
概要：任意の余単体 Ω 図式の Reedy 置換した部分 Tot の具体的な Kan fibration の塔。
方針：構成済みの段の Reedy 条件を一般の部分 Tot の Kan 性と制限の fibration 性へ渡す。
規約：各宣言の条件は構成から証明する。元の図式への追加条件は不要。
使われ方：Goerss–Jardine VIII §1。既存 homotopy Tot の Milnor 比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 置換した図式の一つのスペクトル次数の点つき係数。 -/
abbrev coefficients (X : CosimplicialObject OmegaSpectrum.{u}) (k : ℕ) :=
  diagram X ⋙ KanSequence.levelEvaluation k

/-- 置換後の通常 Tot は実際に Kan。 -/
lemma totalization_kanComplex (X : CosimplicialObject OmegaSpectrum.{u}) (k : ℕ) :
    KanComplex (PointedTotalization.obj (coefficients X k)).right :=
  PointedTotalization.kanComplex (coefficients X k)
    ((CosimplicialHornFibration.terminal_iff _).mp (reedy X k))

/-- 置換後の部分 Tot の各段は実際に Kan。 -/
lemma stage_kanComplex (X : CosimplicialObject OmegaSpectrum.{u}) (k n : ℕ) :
    KanComplex (PartialTotalizationTower.stage (coefficients X k) n).right :=
  PartialTotalizationTower.stage_kanComplex (coefficients X k) (reedy X k) n

/-- 置換後の部分 Tot の隣接制限は実際の Kan fibration。 -/
lemma step_fibration (X : CosimplicialObject OmegaSpectrum.{u}) (k n : ℕ) :
    Fibration (PartialTotalizationTower.step (coefficients X k) n).right :=
  PartialTotalizationTower.map_fibration (coefficients X k) (reedy X k) (Nat.le_succ n)

end
end SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
