module

public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.KST.NonConnective.DGKappaSwindleInfinity

/-!
概要：同じ非可算正則 κ と、各段の同じ I・P を保持する反復 dg 懸垂。
方針：未供給の dg 小模型の供給を明示引数とし、実 Drinfeld 商を再帰的に反復する。
規約：κ を段ごとに変更せず、供給の存在や K の消滅を仮定しない。
使われ方：BGT Def. 9.6 の非連結化列の厳密 dg 対象。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]

/-- 一つの厳密 dg 入力に対し、同じ κ の cone 模型と Perf 比較を対で保持する。 -/
structure DGSuspensionStageInput (κ : Cardinal.{u})
    (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) where
  /-- 同じ入力の κ-compact dg cone。 -/
  cone : DGKappaConeInput R A κ
  /-- 同じ cone 内の perfect 安定閉包と元の Perf との比較。 -/
  perfect : DGKappaPerfectInput R A cone

/-- 各段の dg 小模型を供給する未構成の関数の型。κ は全段で固定。 -/
abbrev DGSuspensionStageProvider (κ : Cardinal.{u}) :=
  (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) → DGSuspensionStageInput R κ A

/-- 実平坦 Drinfeld 商を反復した同じ厳密 dg K 入力。 -/
def dgSuspensionIteration {κ : Cardinal.{u}} (s : DGSuspensionStageProvider.{u, v} R κ)
    (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) :
    ℕ → SConstruction.PerfDGInput.{u, max (u + 1) v} R
  | 0 => A
  | n + 1 =>
    dgKappaSuspensionKInput R (dgSuspensionIteration s A n) (s (dgSuspensionIteration s A n)).cone

/-- 反復の各段で使う同じ I・P の対。別の存在選択で取り直さない。 -/
def dgSuspensionIterationStage {κ : Cardinal.{u}}
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    DGSuspensionStageInput R κ (dgSuspensionIteration R s A n) :=
  s (dgSuspensionIteration R s A n)

/-- 初期段は元の厳密 dg 入力そのもの。 -/
lemma dgSuspensionIteration_zero {κ : Cardinal.{u}}
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) :
    dgSuspensionIteration R s A 0 = A := rfl

/-- 次段は同じ段の同じ I を使った実懸垂。 -/
lemma dgSuspensionIteration_succ {κ : Cardinal.{u}}
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (A : SConstruction.PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    dgSuspensionIteration R s A (n + 1) =
      dgKappaSuspensionKInput R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone := rfl

end SerrePositivity.KST.NonConnective
