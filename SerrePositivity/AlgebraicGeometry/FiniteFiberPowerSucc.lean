module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：有限ファイバー冪の先頭と末尾への実際の射は Cartesian 四角形を与える。
方針：既存の有限 wide pullback の普遍性を二つの射へ分ける。
規約：元の射影と基底への射を保つ。
使われ方：既存の Čech nerve の正次数の各項に Segre の表示を帰納する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {X S : C} (f : X ⟶ S) (n : ℕ)
local notation "arr" m => (fun _ : Fin (m + 1) ↦ f)

/-- n+2 個の冪は、末尾の n+1 個と先頭の一個の S 上の pullback。 -/
theorem isPullback_finiteFiberPowerSucc :
    let t := WidePullback.lift (WidePullback.base (arr (n + 1)))
      (fun i : Fin (n + 1) ↦ WidePullback.π (arr (n + 1)) i.succ)
      (fun i ↦ WidePullback.π_arrow (arr (n + 1)) i.succ)
    IsPullback t (WidePullback.π (arr (n + 1)) 0) (WidePullback.base (arr n)) f := by
  dsimp only
  have h : WidePullback.lift (WidePullback.base (arr (n + 1)))
      (fun i : Fin (n + 1) ↦ WidePullback.π (arr (n + 1)) i.succ)
      (fun i ↦ WidePullback.π_arrow (arr (n + 1)) i.succ) ≫
        WidePullback.base (arr n) = WidePullback.π (arr (n + 1)) 0 ≫ f := by
    simp only [WidePullback.lift_base, WidePullback.π_arrow]
  refine ⟨⟨h⟩, ⟨PullbackCone.IsLimit.mk h ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine WidePullback.lift (c.fst ≫ WidePullback.base (arr n))
      (Fin.cases c.snd (fun i ↦ c.fst ≫ WidePullback.π (arr n) i)) ?_
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact c.condition.symm
    · simp only [Fin.cases_succ, Category.assoc, WidePullback.π_arrow]
  · intro c
    apply WidePullback.hom_ext
    · intro i
      simp only [Category.assoc, WidePullback.lift_π, Fin.cases_succ]
    · simp only [Category.assoc, WidePullback.lift_base]
  · intro c
    simp only [WidePullback.lift_π, Fin.cases_zero]
  · intro c m hm ht
    apply WidePullback.hom_ext
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [WidePullback.lift_π, Fin.cases_zero] using ht
      · have hc := congrArg (fun l ↦ l ≫ WidePullback.π (arr n) j) hm
        simpa only [Category.assoc, WidePullback.lift_π, Fin.cases_succ] using hc
    · have hc := congrArg (fun l ↦ l ≫ WidePullback.base (arr n)) hm
      simpa only [Category.assoc, WidePullback.lift_base] using hc

end SerrePositivity.AlgebraicGeometry
