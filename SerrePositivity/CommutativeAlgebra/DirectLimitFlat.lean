module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # 有向直極限の平坦性

有限個の元を一つの段へ持ち上げ、零関係が後続段で成立することを使って、
Mathlibの平坦性の方程式判定を適用する。環・局所性・Noether性は不要。
-/

public section
namespace SerrePositivity

variable {R ι : Type*} [CommRing R] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (T h) (M i) (M j)]
variable [∀ i j (h : i ≤ j), LinearMapClass (T h) R (M i) (M j)]
variable (f : ∀ i j (h : i ≤ j), T h) [DirectedSystem M (f · · ·)]

/-- 直極限の有限個の元には、共通の段での代表元が存在する。 -/
theorem directLimit_exists_representatives {n : ℕ} (x : Fin n → DirectLimit M f) :
    ∃ i, ∃ y : Fin n → M i, ∀ a, DirectLimit.Module.of R ι M f i (y a) = x a := by
  classical
  induction n with
  | zero =>
    exact ⟨Classical.arbitrary ι, Fin.elim0, fun a ↦ Fin.elim0 a⟩
  | succ n ih =>
    obtain ⟨i, y, hy⟩ := ih (fun a ↦ x a.castSucc)
    obtain ⟨j, z, hz⟩ := DirectLimit.exists_eq_mk f (x (Fin.last n))
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, Fin.lastCases (f j k hjk z) (fun a ↦ f i k hik (y a)), ?_⟩
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simp only [Fin.lastCases_last, DirectLimit.Module.of_f]
      with_unfolding_all exact hz.symm
    · simpa only [Fin.lastCases_castSucc, DirectLimit.Module.of_f] using hy b

/-- 有向直極限の各段が平坦なら、直極限も平坦である。
遷移写像の単射性・有限生成性は要求しない。 -/
theorem directLimit_flat [∀ i, Module.Flat R (M i)] : Module.Flat R (DirectLimit M f) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n c x hx
  obtain ⟨i, y, hy⟩ := directLimit_exists_representatives M f x
  have hzero : DirectLimit.Module.of R ι M f i (∑ a, c a • y a) = 0 := by
    simpa only [map_sum, map_smul, hy] using hx
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero (f := f) ⟨i, ∑ a, c a • y a⟩).mp hzero
  have hrel : ∑ a, c a • f i j hij (y a) = 0 := by
    simpa only [map_sum, map_smul] using hj
  obtain ⟨k, A, z, hz, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, A, fun b ↦ DirectLimit.Module.of R ι M f j (z b), ?_, hA⟩
  intro a
  have h := congrArg (DirectLimit.Module.of R ι M f j) (hz a)
  simpa only [map_sum, map_smul, DirectLimit.Module.of_f, hy] using h

end SerrePositivity
