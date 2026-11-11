module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.GroupFiveLemma

/-!
概要：最後の項が基点付き集合でよい群の五項補題。
方針：中央の群で乗法と逆元を使い、最後の項では基点保存と単射性だけを使う。
規約：最後の項や最後の写像に群構造・準同型性を要求しない。
使われ方：Goerss–Jardine I §§7–8、Sp の引き戻しの基本群を含む全空間の比較。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：群から基点付き集合へ続く完全な五項列の比較で中央の群の全単射性を得る。
方針：単射性は核を左へ戻し、全射性は右の基点への像を使って差を補う。
規約：最後の写像は基点付き集合への関数でよく、外側に必要な全射・単射だけを仮定する。
使われ方：Goerss–Jardine I §§7–8、π₁ から fiber の π₀ へ続く長完全列の比較。 -/
lemma group_pointed_five_lemma
    {A B C D E A' B' C' D' E' : Type u}
    [Group A] [Group B] [Group C] [Group D]
    [Group A'] [Group B'] [Group C'] [Group D']
    (e : E) (e' : E')
    (d₁ : A →* B) (d₂ : B →* C) (d₃ : C →* D) (d₄ : D → E)
    (d₁' : A' →* B') (d₂' : B' →* C') (d₃' : C' →* D') (d₄' : D' → E')
    (f₁ : A →* A') (f₂ : B →* B') (f₃ : C →* C') (f₄ : D →* D') (f₅ : E → E')
    (h₁ : ∀ a, f₂ (d₁ a) = d₁' (f₁ a))
    (h₂ : ∀ b, f₃ (d₂ b) = d₂' (f₂ b))
    (h₃ : ∀ c, f₄ (d₃ c) = d₃' (f₃ c))
    (h₄ : ∀ d, f₅ (d₄ d) = d₄' (f₄ d)) (h₅ : f₅ e = e')
    (ex₁ : ∀ b, d₂ b = 1 ↔ ∃ a, d₁ a = b)
    (ex₂ : ∀ c, d₃ c = 1 ↔ ∃ b, d₂ b = c)
    (ex₃ : ∀ d, d₄ d = e ↔ ∃ c, d₃ c = d)
    (ex₁' : ∀ b, d₂' b = 1 ↔ ∃ a, d₁' a = b)
    (ex₂' : ∀ c, d₃' c = 1 ↔ ∃ b, d₂' b = c)
    (ex₃' : ∀ d, d₄' d = e' ↔ ∃ c, d₃' c = d)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Bijective f₂)
    (hf₄ : Function.Bijective f₄) (hf₅ : Function.Injective f₅) :
    Function.Bijective f₃ := by
  constructor
  · apply (injective_iff_map_eq_one f₃).2
    intro c hc
    have hd : d₃ c = 1 := hf₄.injective (by rw [h₃, hc, map_one, map_one])
    obtain ⟨b, hb⟩ := (ex₂ c).1 hd
    have hdb : d₂' (f₂ b) = 1 := by rw [← h₂, hb, hc]
    obtain ⟨a', ha'⟩ := (ex₁' (f₂ b)).1 hdb
    obtain ⟨a, ha⟩ := hf₁ a'
    have hda : d₁ a = b := hf₂.injective (by rw [h₁, ha, ha'])
    rw [← hb, ← hda]
    exact (ex₁ (d₁ a)).2 ⟨a, rfl⟩
  · intro c'
    obtain ⟨d, hd⟩ := hf₄.surjective (d₃' c')
    have hzero' : d₄' (d₃' c') = e' := (ex₃' (d₃' c')).2 ⟨c', rfl⟩
    have hzero : d₄ d = e := hf₅ (by rw [h₄, hd, hzero', h₅])
    obtain ⟨c, hc⟩ := (ex₃ d).1 hzero
    have hker : d₃' (c' * (f₃ c)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h₃, hc, hd, mul_inv_cancel]
    obtain ⟨b', hb'⟩ := (ex₂' (c' * (f₃ c)⁻¹)).1 hker
    obtain ⟨b, hb⟩ := hf₂.surjective b'
    refine ⟨d₂ b * c, ?_⟩
    rw [map_mul, h₂, hb, hb', inv_mul_cancel_right]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
