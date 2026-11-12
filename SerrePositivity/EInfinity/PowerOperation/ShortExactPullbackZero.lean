module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 短完全列の核を零対象との引き戻しとして保持する

DAG XIII §2.2 の Γ の cone 比較で用いる一般の補助。
指定された二射と零対象への実際の零射を変えない。［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe v u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma shortExact_isPullback_zero {S : ShortComplex C} (hS : S.ShortExact)
    (Z : C) (hZ : IsZero Z) :
    IsPullback S.f (0 : S.X₁ ⟶ Z) S.g (0 : Z ⟶ S.X₃) := by
  have hc : S.f ≫ S.g = (0 : S.X₁ ⟶ Z) ≫ (0 : Z ⟶ S.X₃) := by
    rw [S.zero, zero_comp]
  let l (s : PullbackCone S.g (0 : Z ⟶ S.X₃)) :=
    KernelFork.IsLimit.lift' hS.fIsKernel s.fst (by simpa using s.condition)
  refine IsPullback.of_isLimit (c := PullbackCone.mk S.f (0 : S.X₁ ⟶ Z) hc) ?_
  refine PullbackCone.IsLimit.mk hc (fun s => (l s).1) (fun s => (l s).2) ?_ ?_
  · intro s
    exact hZ.eq_of_tgt _ _
  · intro s m hm _hn
    apply Fork.IsLimit.hom_ext hS.fIsKernel
    exact hm.trans (l s).2.symm

end SerrePositivity.EInfinity.PowerOperation
