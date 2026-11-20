module

public import SerrePositivity.AlgebraicGeometry.MittagLefflerUniformStage

/-!
概要：KST §5、Stacks 05DP・059X の有限自由列の双対遷移像の安定化。
方針：双対像の商の族へ一様な後続段階の補題を適用し、合成による像の単調減少と合わせる。
規約：元の加群の Mittag–Leffler 性と実際の有限自由列の評価条件を入力する。
使われ方：可算生成平坦 Mittag–Leffler 加群の射影性への逆系の入力。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：加群列の遷移の双対像は終段階を進めると単調に減少する。
方針：遷移の合成式を双対の前合成として読む。
規約：KST §5、Stacks 05DP・059X、加群の有限性は不要。
使われ方：一様な双対像の包含を後続段階での等号へ強める。
-/
theorem linearSequence_dual_range_antitone
    (R : Type u) [CommRing R] (F : ℕ → Type u)
    [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    (a : ∀ n, F n →ₗ[R] F (n + 1)) (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    LinearMap.range (linearSequenceMap R F a n k (hnm.trans hmk)).dualMap ≤
      LinearMap.range (linearSequenceMap R F a n m hnm).dualMap := by
  rintro _ ⟨φ, rfl⟩
  refine ⟨(linearSequenceMap R F a m k hmk).dualMap φ, ?_⟩
  ext x
  simp only [LinearMap.dualMap_apply]
  exact congrArg φ (DirectedSystem.map_map' (linearSequenceMap R F a) hnm hmk x)

/--
概要：Mittag–Leffler 加群を表す有限自由列では、各初段からの双対遷移像が有限後続段階で安定する。
方針：全後続双対像による商を試験族とし、一様な像の包含と単調減少から等号を得る。
規約：KST §5、Stacks 05DP・059X、試験族の自然数添字は ULift で宇宙を揃える。
使われ方：全射への持ち上げを逆系の安定化から組み立てる。
-/
theorem exists_stable_dual_ranges_of_mittagLeffler
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Type u) [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    {σ : ℕ → Type v} [∀ n, Finite (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
    (a : ∀ n, F n →ₗ[R] F (n + 1)) (q : ∀ n, F n →ₗ[R] M)
    (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M)
    (n : ℕ) :
    ∃ (k : ℕ) (hk : n ≤ k), ∀ (ℓ : ℕ) (hkℓ : k ≤ ℓ),
      LinearMap.range (linearSequenceMap R F a n ℓ (hk.trans hkℓ)).dualMap =
        LinearMap.range (linearSequenceMap R F a n k hk).dualMap := by
  let (m : ℕ) : Fintype (σ m) := Fintype.ofFinite (σ m)
  let J := ULift.{u} ℕ
  let L (j : J) : Submodule R (Module.Dual R (F n)) :=
    LinearMap.range (linearSequenceMap R F a n (n + j.down) (Nat.le_add_right n j.down)).dualMap
  have hL (j : J) : (q n).rTensor (Module.Dual R (F n) ⧸ L j)
      (basisMappedCoevaluationTensor (b n) (L j).mkQ) = 0 := by
    let f := linearSequenceMap R F a n (n + j.down) (Nat.le_add_right n j.down)
    have hkill : f.rTensor (Module.Dual R (F n) ⧸ L j)
        (basisMappedCoevaluationTensor (b n) (L j).mkQ) = 0 := by
      apply (basisMappedCoevaluationTensor_rTensor_eq_zero_iff
        (b n) (b (n + j.down)) f (L j).mkQ).mpr
      rw [Submodule.ker_mkQ]
    have heval : (q (n + j.down)).comp f = q n := by
      ext x
      exact linearSequenceMap_eval R F a q hq n (n + j.down) (Nat.le_add_right n j.down) x
    rw [← heval, LinearMap.rTensor_comp_apply, hkill, map_zero]
  obtain ⟨k, hk, hinc⟩ := exists_stage_dual_range_le_iInf_of_mittagLeffler
    F b a q hq hker hcover hM n L hL
  refine ⟨k, hk, fun ℓ hkℓ => le_antisymm ?_ ?_⟩
  · exact linearSequence_dual_range_antitone R F a n k ℓ hk hkℓ
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hk.trans hkℓ)
    subst ℓ
    exact hinc.trans (iInf_le L (⟨t⟩ : J))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
