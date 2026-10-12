module

public import SerrePositivity.CommutativeAlgebra.HomologyLength
public import SerrePositivity.CommutativeAlgebra.TorFiniteLength
public import SerrePositivity.Inputs.IntersectionTheory

/-!
# 交点重複度の左右の加法性

`chi` の定義を保ったまま、各変数の短完全列について加法性を証明する。
Noether 環上の有限生成加群では、中央のテンソル積の有限長性から両端の有限長性が従い、
各 Tor も有限長となる。高次 Tor の消滅を仮定すれば、長完全列の長さの交代和から結論を得る。

第2変数では左導来関手の長完全列、第1変数では固定した第2変数の射影分解と平坦性から
作った長完全列を使う。Tor の対称性や連結射の自然性は、この数値の等式には不要である。

最後に正則局所環へ適用する。一般論の引用は `regularResolution`（有界有限自由分解の存在）
だけで、加法性そのものを仮定するクラスは使わない。
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory TensorProduct

universe u

namespace SerrePositivity

variable {R : Type u} [CommRing R]

section noetherian

variable [IsNoetherianRing R]

/-- Noether 環上で、関係する Tor が高次で消えるときの交点重複度の第2変数に関する加法性。
中央のテンソル積の有限長性から両端の有限長性を台で判定し、Tor の長完全列の交代和を取る。 -/
theorem chi_add_right_of_eventually
    (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M ⊗[R] N₂) ≠ ⊤)
    (z₁ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₁))
    (z₂ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₂))
    (z₃ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₃)) :
    chi R M N₂ = chi R M N₁ + chi R M N₃ := by
  have h₂ := Module.length_ne_top_iff.mp h
  have h₁ : IsFiniteLength R (M ⊗[R] N₁) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨hp.1, Or.inl hp.2⟩)
  have h₃ : IsFiniteLength R (M ⊗[R] N₃) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨hp.1, Or.inr hp.2⟩)
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact M f g hf hg he
  exact lengthEuler_finsum_longExact
    (fun i => ModuleCat.of R (TorModule R i M N₁))
    (fun i => ModuleCat.of R (TorModule R i M N₂))
    (fun i => ModuleCat.of R (TorModule R i M N₃))
    α β δ hab hbd hda hb
    (isFiniteLength_torModule M N₁ h₁) (isFiniteLength_torModule M N₂ h₂)
    (isFiniteLength_torModule M N₃ h₃) z₁ z₂ z₃

/-- Noether 環上で、関係する Tor が高次で消えるときの交点重複度の第1変数に関する加法性。
固定した第2変数の分解から作った長完全列に、長さの交代和の一般定理を適用する。 -/
theorem chi_add_left_of_eventually
    (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M₂ ⊗[R] N) ≠ ⊤)
    (z₁ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₁ N))
    (z₂ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₂ N))
    (z₃ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₃ N)) :
    chi R M₂ N = chi R M₁ N + chi R M₃ N := by
  have h₂ := Module.length_ne_top_iff.mp h
  have h₁ : IsFiniteLength R (M₁ ⊗[R] N) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨Or.inl hp.1, hp.2⟩)
  have h₃ : IsFiniteLength R (M₃ ⊗[R] N) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨Or.inr hp.1, hp.2⟩)
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact_left N f g hf hg he
  exact lengthEuler_finsum_longExact
    (fun i => ModuleCat.of R (TorModule R i M₁ N))
    (fun i => ModuleCat.of R (TorModule R i M₂ N))
    (fun i => ModuleCat.of R (TorModule R i M₃ N))
    α β δ hab hbd hda hb
    (isFiniteLength_torModule M₁ N h₁) (isFiniteLength_torModule M₂ N h₂)
    (isFiniteLength_torModule M₃ N h₃) z₁ z₂ z₃

end noetherian

section regular

variable [IsRegularLocalRing R]
/-- 有限生成な第2変数の有界有限自由分解から、高次 Tor の消滅を得る。
分解の存在だけを `regularResolution` から受け取り、消滅自体は一般の左導来関手の定理による。
第1変数には有限生成性を要求しない。 -/
theorem torModule_eventually_subsingleton (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N) := by
  obtain ⟨F, ⟨hF⟩, ⟨a, b, hb⟩, _, _⟩ := regularResolution R N
  obtain ⟨n, hn⟩ := isZero_leftDerived_eventually_of_resolution
    (tensorLeft (ModuleCat.of R M)) hF a (fun i hi => hb i (Or.inl hi))
  exact ⟨n, fun i hi => ModuleCat.subsingleton_of_isZero (hn i hi)⟩

/-- 正則局所環上の交点重複度は第2変数の短完全列について加法的である。
中央のテンソル積は有限長とし、有界有限自由分解の存在から高次消滅を供給する。 -/
theorem chi_add_right
    (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M ⊗[R] N₂) ≠ ⊤) :
    chi R M N₂ = chi R M N₁ + chi R M N₃ :=
  chi_add_right_of_eventually M N₁ N₂ N₃ f g hf hg he h
    (torModule_eventually_subsingleton M N₁) (torModule_eventually_subsingleton M N₂)
    (torModule_eventually_subsingleton M N₃)

/-- 正則局所環上の交点重複度は第1変数の短完全列について加法的である。
中央のテンソル積は有限長とし、有界有限自由分解の存在から高次消滅を供給する。 -/
theorem chi_add_left
    (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M₂ ⊗[R] N) ≠ ⊤) :
    chi R M₂ N = chi R M₁ N + chi R M₃ N :=
  chi_add_left_of_eventually M₁ M₂ M₃ N f g hf hg he h
    (torModule_eventually_subsingleton M₁ N) (torModule_eventually_subsingleton M₂ N)
    (torModule_eventually_subsingleton M₃ N)

end regular

end SerrePositivity
