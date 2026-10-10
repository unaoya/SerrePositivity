module

public import SerrePositivity.PerfectComplex.NormalizedLength

/-!
# 正規化長さの係数制限

## 概要

環準同型 `f : Λ →+* C` と `Λ` 上の正規化長さ `lam : NormalizedLength Λ J` から、`C` 加群を
`f` で `Λ` 加群とみて測る正規化長さ `lam.comap f J' h : NormalizedLength C J'` を作る。
`h : J.map f ≤ J'` は、`J'` 冪ねじれの `C` 加群が `Λ` 加群として `J` 冪ねじれであることを
保証する（加法性の定義域の対応）。

論文 Theorem 2.5 の「`C_D` 加群の正規化長さ `λ_D` は、塔 `Λ` の長さ `λ_∞` の係数制限で定める」
（`λ_D = λ_∞`）を定義として書くために使う（`Paper/Section2/Theorem2_5.lean`）。

## 内容

- `IsPowTorsion.comap`：`J.map f ≤ J'` のとき `J'` 冪ねじれの `C` 加群は `Λ` 加群として
  `J` 冪ねじれ（同じ冪で消える）。
- `NormalizedLength.comap` と `comap_len`（値は変わらない）。
-/

@[expose] public section

universe u

open scoped ENNReal

namespace SerrePositivity

variable {Λ C : Type u} [CommRing Λ] [CommRing C] (f : Λ →+* C) {J : Ideal Λ} {J' : Ideal C}

/-- `J.map f ≤ J'` なら、`J'` のある冪で消える `C` 加群 `M` は、`f` で `Λ` 加群とみると
`J` の同じ冪で消える。 -/
lemma IsPowTorsion.comap (h : J.map f ≤ J') (M : Type u) [AddCommGroup M] [Module C M]
    (hM : IsPowTorsion J' M) :
    letI := Module.compHom M f
    IsPowTorsion J M := by
  let := Module.compHom M f
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, fun x a ↦ ?_⟩
  have ha : f a ∈ J' ^ n := by
    have : f a ∈ (J ^ n).map f := Ideal.mem_map_of_mem f a.2
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono h n this
  exact hn (a := ⟨f a, ha⟩)

namespace NormalizedLength

/-- 正規化長さの係数制限：`C` 加群 `M` を `f : Λ →+* C` で `Λ` 加群とみて `lam` で測る。
加法性の定義域は `J.map f ≤ J'` をみたす `J'` 冪ねじれ加群。 -/
def comap (lam : NormalizedLength Λ J) (J' : Ideal C) (h : J.map f ≤ J') :
    NormalizedLength C J' where
  len M _ _ := letI := Module.compHom M f; lam.len M
  len_eq_zero_of_subsingleton M _ _ _ := by
    let := Module.compHom M f
    exact lam.len_eq_zero_of_subsingleton M
  len_congr M N _ _ _ _ e := by
    let := Module.compHom M f
    let := Module.compHom N f
    exact lam.len_congr M N
      { e with map_smul' := fun a x ↦ e.map_smul (f a) x }
  len_add_of_exact M₁ M₂ M₃ _ _ _ _ _ _ g₁ g₂ h₁ h₂ hex hM₂ := by
    let := Module.compHom M₁ f
    let := Module.compHom M₂ f
    let := Module.compHom M₃ f
    exact lam.len_add_of_exact M₁ M₂ M₃
      { g₁ with map_smul' := fun a x ↦ g₁.map_smul (f a) x }
      { g₂ with map_smul' := fun a x ↦ g₂.map_smul (f a) x }
      h₁ h₂ hex (IsPowTorsion.comap f h M₂ hM₂)

/-- `comap` は値を変えない：`C` 加群 `M` の長さは、`Λ` 加群とみた `M` の `lam` での長さ。 -/
@[simp] lemma comap_len (lam : NormalizedLength Λ J) (J' : Ideal C) (h : J.map f ≤ J')
    (M : Type u) [AddCommGroup M] [Module C M] :
    (lam.comap f J' h).len M = (letI := Module.compHom M f; lam.len M) := rfl

end NormalizedLength

end SerrePositivity
