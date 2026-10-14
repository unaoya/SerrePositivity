module

public import SerrePositivity.BhattScholze.CompatibleRootIdealTensor
public import SerrePositivity.HomologicalAlgebra.TorNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedTensor

/-! # B4-5：根イデアル商と被約終域のTor独立性

共通Tor長完全列と零次の自然性を、根イデアルの平坦性とテンソル単射性へ適用する。
一般の完全環のTor独立性・完備底変換の比較は別工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory MonoidalCategory
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [IsReduced R]

/-- 根イデアル商と被約なR-代数の正のTorはすべて零。
正則性・Noether性・通常の終域の平坦性は仮定しない。 -/
theorem compatibleRootQuotient_tor_subsingleton
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C] [IsReduced C]
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i (R ⧸ compatibleRootIdeal ρ) C) := by
  let K := compatibleRootIdeal ρ
  let : Module.Flat R K := compatibleRootIdeal_flat ρ hρ
  have he : Function.Exact K.subtype K.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  obtain ⟨α, β, δ, _, hβδ, hδα, _, hαstd, _⟩ := torModule_longExact_left_with_maps
    C K.subtype K.mkQ (fun x y h ↦ Subtype.ext h) (Submodule.mkQ_surjective K) he
  have hTensor : Function.Injective (K.subtype.rTensor C) := by
    intro x y h
    apply compatibleRootIdealTensorMap_injective ρ hρ C
    change (TensorProduct.lid R C) (K.subtype.rTensor C x) =
      (TensorProduct.lid R C) (K.subtype.rTensor C y)
    rw [h]
  have hn : ∀ x, torModuleZeroEquiv R R C (α 0 x) =
      K.subtype.rTensor C (torModuleZeroEquiv R K C x) := by
    intro x
    rw [hαstd 0]
    have h := torZeroIso_naturality_left (ModuleCat.ofHom K.subtype) (ModuleCat.of R C)
    have hx := congrArg (fun f ↦ f.hom x) h
    exact hx
  have hαinj : Function.Injective (α 0) := by
    intro x y h
    apply (torModuleZeroEquiv R K C).injective
    apply hTensor
    rw [← hn x, ← hn y, h]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  apply subsingleton_of_forall_eq 0
  intro x
  have hδx : δ j x = 0 := by
    cases j with
    | zero =>
      apply hαinj
      rw [map_zero]
      exact (hδα 0 (δ 0 x)).mpr ⟨x, rfl⟩
    | succ j =>
      let := torModule_subsingleton_of_flat (R := R) K C j
      exact Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (hβδ j x).mp hδx
  let := torModule_subsingleton_of_flat (R := R) R C j
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- 根イデアル商の被約終域との実導来テンソルは次数0に集中する。 -/
theorem compatibleRootQuotient_derivedTensor_concentrated
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C] [IsReduced C] :
    IsConcentratedInDegreeZero (derivedTensor R (R ⧸ compatibleRootIdeal ρ) C) :=
  (isConcentratedInDegreeZero_derivedTensor_iff (R := R) _ _).mpr
    (fun i hi ↦ compatibleRootQuotient_tor_subsingleton ρ hρ C i hi)

end SerrePositivity.BhattScholze
