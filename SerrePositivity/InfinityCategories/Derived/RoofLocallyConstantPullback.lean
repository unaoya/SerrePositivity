module
public import SerrePositivity.InfinityCategories.Derived.RoofRightFibrationKan
public import SerrePositivity.InfinityCategories.F1.Categories.CoreKan
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # 全辺を反転する基底変換による屋根の局所定値性

概要：全ての辺を可逆にする写像で右ファイブレーションを引き戻すと、左にもなる。
方針：基底写像を Kan な core へ因子化し、その上の全ホーン充填を基底変換する。
規約：モデル構造は使わない。使われ方：商側の実屋根の射影の左右ファイブレーション性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 全辺を反転する写像による右ファイブレーションの基底変換は左にもなる。 -/
lemma roofRightFibration_pullback_leftFibration_of_inverts {E X Y : SSet.{u}}
    [Quasicategory Y] (p : E ⟶ Y) [RightFibration p] (f : X ⟶ Y)
    (hf : ∀ s : X _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s))) :
    LeftFibration (pullback.snd p f) := by
  let g := quasicategoryCoreLift f hf
  let i := (quasicategoryCore Y).ι
  let q := pullback.snd p i
  have : RightFibration q := rightFibration_pullback_snd p i
  have : KanComplex (pullback p i) := roofRightFibration_kanComplex q
  have : LeftFibration q := roofRightFibration_leftFibration_of_kan q
  have : LeftFibration (pullback.snd q g) :=
    ⟨leftFibrations.pullback_snd q g (LeftFibration.mem (p := q))⟩
  let e := pullbackLeftPullbackSndIso p i g
  have h : leftFibrations (e.inv ≫ pullback.snd q g) :=
    leftFibrations.comp_mem _ _ (leftFibrations.of_isIso e.inv) LeftFibration.mem
  rw [pullbackLeftPullbackSndIso_inv_snd_snd] at h
  have hg : g ≫ i = f := quasicategoryCoreLift_ι f hf
  exact Eq.mp (congrArg (fun k : X ⟶ Y => LeftFibration (pullback.snd p k)) hg) ⟨h⟩

end SerrePositivity.InfinityCategories
