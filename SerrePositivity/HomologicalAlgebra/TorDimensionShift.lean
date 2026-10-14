module

public import SerrePositivity.HomologicalAlgebra.LocalFlatnessCriterion

/-! # 第2変数の次元シフト

## 概要

短完全列 `0 → V₁ → V₂ → V₃ → 0` と固定した `M` について、Tor の長完全列から

- `Tor_{n+1}(M, V₂) = Tor_{n+2}(M, V₂) = 0` なら `Tor_{n+2}(M, V₃) ≅ Tor_{n+1}(M, V₁)`、
- `Tor_1(M, V₂) = 0` なら `Tor_1(M, V₃) ≅ ker(M ⊗ V₁ → M ⊗ V₂)`、

を取り出す。また有限個の直積について Tor の消滅を移す。

## 使われ方

`formalization-plans/serre-equal-characteristic.md` の K8。二つの環の Tor を、自由加群による
表示に沿って同時に次元シフトして比べる。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace SerrePositivity

variable {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]

section les

variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
  [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
  (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
  (hg : Function.Surjective g) (hfg : Function.Exact f g)

include hf hg hfg in
/-- 短完全列の両端で `Tor_n(M, -)` が消えれば、中央でも消える。 -/
theorem torModule_subsingleton_of_exact (n : ℕ)
    (h₁ : Subsingleton (TorModule A n M V₁)) (h₃ : Subsingleton (TorModule A n M V₃)) :
    Subsingleton (TorModule A n M V₂) := by
  obtain ⟨α, β, _, hαβ, _, _, _⟩ := torModule_longExact M f g hf hg hfg
  have hx : ∀ z : TorModule A n M V₂, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := ((hαβ n) z).mp (Subsingleton.elim _ _)
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y ↦ by rw [hx x, hx y]⟩

include hf hg hfg in
/-- **高次の次元シフト**：`Tor_{n+1}(M, V₂) = Tor_{n+2}(M, V₂) = 0` なら
`Tor_{n+2}(M, V₃) ≅ Tor_{n+1}(M, V₁)`（連結射）。 -/
theorem nonempty_torModule_succ_equiv (n : ℕ)
    (h₂ : Subsingleton (TorModule A (n + 2) M V₂))
    (h₂' : Subsingleton (TorModule A (n + 1) M V₂)) :
    Nonempty (TorModule A (n + 2) M V₃ ≃ₗ[A] TorModule A (n + 1) M V₁) := by
  obtain ⟨α, β, δ, _, hβδ, hδα, _⟩ := torModule_longExact M f g hf hg hfg
  refine ⟨LinearEquiv.ofBijective (δ (n + 1)) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := ((hβδ (n + 1)) z).mp hz
    rw [@Subsingleton.elim _ h₂ w 0, map_zero]
  · intro w
    exact ((hδα (n + 1)) w).mp (@Subsingleton.elim _ h₂' _ _)

include hf hg hfg in
/-- **一次の次元シフト**：`Tor_1(M, V₂) = 0` なら `Tor_1(M, V₃) ≅ ker(M ⊗ V₁ → M ⊗ V₂)`。
連結射は単射で、像は零次の射の核。零次の射は自然な同一視で `M ⊗ f` に移る。 -/
theorem nonempty_torModule_one_equiv_ker (h₂ : Subsingleton (TorModule A 1 M V₂)) :
    Nonempty (TorModule A 1 M V₃ ≃ₗ[A] LinearMap.ker (f.lTensor M)) := by
  let G := (tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  let α₀ := (LeftDerivedLES.α G f 0).hom
  let δ₀ := (LeftDerivedLES.δ G f g hf hg hfg 0).hom
  have hβδ := LeftDerivedLES.exact_βδ G f g hf hg hfg 0
  have hδα := LeftDerivedLES.exact_δα G f g hf hg hfg 0
  have hδinj : Function.Injective δ₀ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (hβδ z).mp hz
    rw [@Subsingleton.elim _ h₂ w 0]
    exact (LeftDerivedLES.β G f g hf hg hfg (0 + 1)).hom.map_zero
  have hrange : LinearMap.range δ₀ = LinearMap.ker α₀ := by
    ext w
    exact (hδα w).symm
  -- 零次の射とテンソル積の自然な同一視
  have hα : α₀ = (LeftDerivedLES.α G f 0).hom := rfl
  rw [LeftDerivedLES.α_eq_map] at hα
  let e := G.leftDerivedZeroIsoSelf
  have hnat := e.hom.naturality (ModuleCat.ofHom f)
  let e₁ := (e.app (ModuleCat.of A V₁)).toLinearEquiv
  let e₂ := (e.app (ModuleCat.of A V₂)).toLinearEquiv
  have hG' : (G.map (ModuleCat.ofHom f)).hom =
      (e.hom.app (ModuleCat.of A V₂)).hom ∘ₗ
        ((G.leftDerived 0).map (ModuleCat.ofHom f)).hom ∘ₗ
          (e.inv.app (ModuleCat.of A V₁)).hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, Category.assoc, hnat]
    simp
  have hG : f.lTensor M = e₂.toLinearMap ∘ₗ α₀ ∘ₗ e₁.symm.toLinearMap := by
    rw [hα]
    exact hG'
  have hker : LinearMap.ker (f.lTensor M) = (LinearMap.ker α₀).map e₁.toLinearMap := by
    rw [hG, LinearEquiv.ker_comp, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.symm_symm]
  refine ⟨(LinearEquiv.ofInjective δ₀ hδinj).trans
    ((LinearEquiv.ofEq _ _ hrange).trans
      ((Submodule.equivMapOfInjective e₁.toLinearMap e₁.injective _).trans
        (LinearEquiv.ofEq _ _ hker.symm)))⟩

end les

/-- 有限個の直積への Tor の消滅の移送：`Tor_n(M, V) = 0` なら `Tor_n(M, V^m) = 0`。 -/
theorem torModule_pi_subsingleton (V : Type u) [AddCommGroup V] [Module A V] (n : ℕ)
    (h : Subsingleton (TorModule A n M V)) :
    ∀ m : ℕ, Subsingleton (TorModule A n M (Fin m → V)) := by
  intro m
  induction m with
  | zero => exact torModule_subsingleton_right_of_subsingleton M _ n
  | succ m ih =>
    let f : V →ₗ[A] (Fin (m + 1) → V) := LinearMap.single A (fun _ ↦ V) 0
    let g : (Fin (m + 1) → V) →ₗ[A] (Fin m → V) := LinearMap.funLeft A V Fin.succ
    have hf : Function.Injective f := fun a b h ↦ by
      simpa [f] using congrFun h 0
    have hg : Function.Surjective g := LinearMap.funLeft_surjective_of_injective _ _ _
      (Fin.succ_injective m)
    have hfg : Function.Exact f g := by
      intro w
      constructor
      · intro hw
        refine ⟨w 0, funext fun i ↦ ?_⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [f]
        · have := congrFun hw j
          simp only [g, LinearMap.funLeft_apply, Pi.zero_apply] at this
          simp [f, this, Fin.succ_ne_zero]
      · rintro ⟨v, rfl⟩
        funext j
        simp [f, g, Fin.succ_ne_zero]
    exact torModule_subsingleton_of_exact M f g hf hg hfg n h ih

end SerrePositivity
