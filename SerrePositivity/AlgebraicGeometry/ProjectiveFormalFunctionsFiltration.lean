module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule
public import SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsBounds

/-!
概要：有限な Rees 加群からの全射を使い、像のフィルトレーションの I 進評価を得る。
方針：有限生成性を Mathlib の安定性の同値に渡し、安定な各段の表示を使う。
規約：ここでは像のフィルトレーションと Rees 全射を入力とする。
使われ方：次数ごとの Čech コホモロジーの直和との比較の後、形式関数の核の評価へ渡す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R H E : Type*} [CommRing R] [IsNoetherianRing R]
variable [AddCommGroup H] [Module R H] [Module.Finite R H]
variable {I : Ideal R} (F : I.Filtration H)
variable [AddCommGroup E] [Module (reesAlgebra I) E] [Module.Finite (reesAlgebra I) E]

/-- Čech 版の核の評価に渡す、像のフィルトレーションの一様な I 進評価。
原典は Stacks 30.20.4(1) の Hⁱ の核の評価。この補題は像の Rees 全射を入力とする。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem cechFormalFunctions_filtration_bound_of_finiteReesImage
    (u : E →ₗ[reesAlgebra I] F.submodule) (hu : Function.Surjective u) :
    ∃ c : ℕ, ∀ n, c ≤ n → F.N n ≤ I ^ (n - c) • (⊤ : Submodule R H) := by
  letI : Module.Finite (reesAlgebra I) F.submodule := Module.Finite.of_surjective u hu
  have hstable : F.Stable :=
    (F.submodule_fg_iff_stable (fun n ↦ IsNoetherian.noetherian (F.N n))).mp
      (Module.Finite.iff_fg.mp inferInstance)
  obtain ⟨c, hc⟩ := hstable.exists_pow_smul_eq_of_ge
  refine ⟨c, ?_⟩
  intro n hn
  rw [hc n hn]
  exact Submodule.smul_mono le_rfl le_top

end SerrePositivity.AlgebraicGeometry
