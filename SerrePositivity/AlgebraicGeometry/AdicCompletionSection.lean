module

public import SerrePositivity.AlgebraicGeometry.CompatiblePowerSections

/-!
概要：KST §5、Stacks 05D3, Lemma 10.97.9 の完備化された全射の実際の線形右逆。
方針：各冪剰余で整合する右逆を完備化の普遍性で持ち上げ、各座標で右逆の式を確認する。
規約：終域の平坦性と最初の剰余の射影性だけを要求する。
使われ方：自由完備化の Mittag–Leffler 性を一般の平坦加群の完備化へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：各冪剰余で整合する右逆から、完備化された写像の実際の線形右逆を構成する。
方針：一段ずつの整合性を全ての遷移へ広げ、完備化の普遍性を適用する。
規約：KST §5、Stacks 05D3、各段の右逆と隣接整合性を明示した入力とする。
使われ方：平坦な終域の最初の剰余の射影性による完備化の分裂。
-/
theorem exists_adicCompletion_section_of_compatible_sections
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (I : Ideal R)
    (s : ∀ n : ℕ, (M ⧸ (I ^ n • (⊤ : Submodule R M))) →ₗ[R]
      (F ⧸ (I ^ n • (⊤ : Submodule R F))))
    (hs : ∀ n, ((π.reduceModIdeal (I ^ n)).restrictScalars R).comp (s n) = LinearMap.id)
    (hnext : ∀ n, (AdicCompletion.transitionMap I F (Nat.le_succ n)).comp (s (n + 1)) =
      (s n).comp (AdicCompletion.transitionMap I M (Nat.le_succ n))) :
    ∃ σ : AdicCompletion I M →ₗ[R] AdicCompletion I F,
      ((AdicCompletion.map I π).restrictScalars R).comp σ = LinearMap.id := by
  let f (n : ℕ) := (s n).comp (AdicCompletion.eval I M n)
  have hfnext (n : ℕ) :
      (AdicCompletion.transitionMap I F (Nat.le_succ n)).comp (f (n + 1)) = f n := by
    dsimp only [f]
    rw [← LinearMap.comp_assoc, hnext, LinearMap.comp_assoc,
      AdicCompletion.transitionMap_comp_eval]
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (AdicCompletion.transitionMap I F hmn).comp (f n) = f m := by
    apply LinearMap.ext
    intro x
    symm
    refine Submodule.eq_factor_of_eq_factor_succ
      (fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h))
      (fun n => f n x) ?_ hmn
    intro k
    exact (congrArg (fun g => g x) (hfnext k)).symm
  let σ := AdicCompletion.lift I f hf
  refine ⟨σ, ?_⟩
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  change π.reduceModIdeal (I ^ n) (s n (x.val n)) = x.val n
  exact congrArg (fun g => g (x.val n)) (hs n)

/--
概要：平坦な終域の最初の剰余が射影的なら、任意の全射の完備化は分裂する。
方針：各冪剰余の整合的な右逆の存在と、その完備化上への持ち上げを合成する。
規約：KST §5、Stacks 05D3, Lemma 10.97.9、Noether 性も有限性も不要。
使われ方：Stacks 05DK の平坦加群の完備化を自由完備化の直和因子にする。
-/
theorem exists_adicCompletion_section_of_flat_of_projective_reduction
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (I : Ideal R)
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    ∃ σ : AdicCompletion I M →ₗ[R] AdicCompletion I F,
      ((AdicCompletion.map I π).restrictScalars R).comp σ = LinearMap.id := by
  obtain ⟨s, hs, hnext⟩ := exists_compatible_power_reduction_sections π hπ I
  exact exists_adicCompletion_section_of_compatible_sections π I s hs hnext

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
