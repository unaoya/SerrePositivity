module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.Algebra.Group.Hom.Basic

/-!
概要：群の二つの完全な五項列に対する五項補題。
方針：核と像の等式を使い、乗法と逆元で図式を追う。
規約：群の可換性を仮定しない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。fiber の正次数の π_* 比較。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

/-- 概要：完全な群の五項列の可換図式では外側の四射の全単射性から中央も全単射。
方針：単射性は核を左へ戻し、全射性は右への像を持ち上げた差を連結射で補う。
規約：全て乗法記法で、群の可換性を要求しない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。ホモトピー fiber の比較。 -/
theorem group_five_lemma
    {A B C D E A' B' C' D' E' : Type u}
    [Group A] [Group B] [Group C] [Group D] [Group E]
    [Group A'] [Group B'] [Group C'] [Group D'] [Group E']
    (d₁ : A →* B) (d₂ : B →* C) (d₃ : C →* D) (d₄ : D →* E)
    (d₁' : A' →* B') (d₂' : B' →* C') (d₃' : C' →* D') (d₄' : D' →* E')
    (f₁ : A →* A') (f₂ : B →* B') (f₃ : C →* C') (f₄ : D →* D') (f₅ : E →* E')
    (h₁ : ∀ a, f₂ (d₁ a) = d₁' (f₁ a))
    (h₂ : ∀ b, f₃ (d₂ b) = d₂' (f₂ b))
    (h₃ : ∀ c, f₄ (d₃ c) = d₃' (f₃ c))
    (h₄ : ∀ d, f₅ (d₄ d) = d₄' (f₄ d))
    (ex₁ : ∀ b, d₂ b = 1 ↔ ∃ a, d₁ a = b)
    (ex₂ : ∀ c, d₃ c = 1 ↔ ∃ b, d₂ b = c)
    (ex₃ : ∀ d, d₄ d = 1 ↔ ∃ c, d₃ c = d)
    (ex₁' : ∀ b, d₂' b = 1 ↔ ∃ a, d₁' a = b)
    (ex₂' : ∀ c, d₃' c = 1 ↔ ∃ b, d₂' b = c)
    (ex₃' : ∀ d, d₄' d = 1 ↔ ∃ c, d₃' c = d)
    (hf₁ : Function.Bijective f₁) (hf₂ : Function.Bijective f₂)
    (hf₄ : Function.Bijective f₄) (hf₅ : Function.Bijective f₅) :
    Function.Bijective f₃ := by
  constructor
  · apply (injective_iff_map_eq_one f₃).2
    intro c hc
    have hd : d₃ c = 1 := hf₄.injective (by rw [h₃, hc, map_one, map_one])
    obtain ⟨b, hb⟩ := (ex₂ c).1 hd
    have hdb : d₂' (f₂ b) = 1 := by rw [← h₂, hb, hc]
    obtain ⟨a', ha'⟩ := (ex₁' (f₂ b)).1 hdb
    obtain ⟨a, ha⟩ := hf₁.surjective a'
    have hda : d₁ a = b := hf₂.injective (by rw [h₁, ha, ha'])
    rw [← hb, ← hda]
    exact (ex₁ (d₁ a)).2 ⟨a, rfl⟩
  · intro c'
    obtain ⟨d, hd⟩ := hf₄.surjective (d₃' c')
    have hzero' : d₄' (d₃' c') = 1 := (ex₃' (d₃' c')).2 ⟨c', rfl⟩
    have hzero : d₄ d = 1 := hf₅.injective (by rw [h₄, hd, hzero', map_one])
    obtain ⟨c, hc⟩ := (ex₃ d).1 hzero
    have hker : d₃' (c' * (f₃ c)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h₃, hc, hd, mul_inv_cancel]
    obtain ⟨b', hb'⟩ := (ex₂' (c' * (f₃ c)⁻¹)).1 hker
    obtain ⟨b, hb⟩ := hf₂.surjective b'
    refine ⟨d₂ b * c, ?_⟩
    rw [map_mul, h₂, hb, hb', inv_mul_cancel_right]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.group_five_lemma := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_five_lemma
