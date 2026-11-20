module

public import SerrePositivity.AlgebraicGeometry.CompatibleReductionSection
public import SerrePositivity.AlgebraicGeometry.ProjectivePowerReduction

/-!
概要：KST §5、Stacks 05D3 の各冪剰余で整合する右逆の列。
方針：零段階から始め、各正の冪剰余の射影性と整合する持ち上げの一段を反復する。
規約：平坦性と最初の剰余の射影性を使い、Noether 性を要求しない。
使われ方：各段の右逆から完備化の線形右逆を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：平坦な終域の最初の剰余が射影的なら、全ての冪剰余に整合する右逆を選べる。
方針：零段階は零加群の右逆とし、正の段階の射影性で整合する持ち上げを反復する。
規約：KST §5、Stacks 05D3, Lemma 10.97.9、元の全射の始域は任意。
使われ方：完備化の分裂を定める各段の線形写像。
-/
theorem exists_compatible_power_reduction_sections
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (I : Ideal R)
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    ∃ s : ∀ n : ℕ, (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
        (F ⧸ (I ^ n • (⊤ : Submodule R F))),
      (∀ n, ((π.reduceModIdeal (I ^ n)).restrictScalars R).comp (s n) = LinearMap.id) ∧
      ∀ n, (AdicCompletion.transitionMap I F (Nat.le_succ n)).comp (s (n + 1)) =
        (s n).comp (AdicCompletion.transitionMap I M (Nat.le_succ n)) := by
  let S (n : ℕ) := {s : (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
      (F ⧸ (I ^ n • (⊤ : Submodule R F))) //
    ((π.reduceModIdeal (I ^ n)).restrictScalars R).comp s = LinearMap.id}
  have h0 : ((π.reduceModIdeal (I ^ 0)).restrictScalars R).comp
      (0 : (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) →ₗ[R]
        (F ⧸ (I ^ 0 • (⊤ : Submodule R F)))) = LinearMap.id := by
    have hsub : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
      simpa only [pow_zero, one_smul] using
        (inferInstance : Subsingleton (M ⧸ (⊤ : Submodule R M)))
    let := hsub
    exact Subsingleton.elim _ _
  let s0 : S 0 := ⟨0, h0⟩
  have hstep (n : ℕ) (s : S n) : ∃ t : S (n + 1),
      (AdicCompletion.transitionMap I F (Nat.le_succ n)).comp t.val =
        s.val.comp (AdicCompletion.transitionMap I M (Nat.le_succ n)) := by
    let := projective_powerQuotientModule (M := M) I (n + 1) (Nat.succ_ne_zero n)
    obtain ⟨t, ht, hcompat⟩ := exists_compatible_reduction_section π hπ (I ^ n) (I ^ (n + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ n)) s.val s.property
    exact ⟨⟨t, ht⟩, hcompat⟩
  choose next hnext using hstep
  let a : ∀ n, S n := fun n => Nat.rec s0 (fun n s => next n s) n
  refine ⟨fun n => (a n).val, fun n => (a n).property, ?_⟩
  intro n
  exact hnext n (a n)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
