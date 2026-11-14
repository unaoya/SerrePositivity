module

public import Mathlib.Logic.Function.Basic

/-!
概要：共通の比較対象を経由して四角形の持ち上げ可能性を移す。
方針：下側の元を共通対象に戻し、右下の単射性で一致を反映する。
規約：各辺の可換性を明示した写像の等式で受け取る。
使われ方：導手の四角形から、指定された中心の完全な四角形への移送。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry

/-- 共通対象からの単射・全射と右下の単射を通じて、四角形の持ち上げを移す。 -/
theorem squareLift_transport
    {A B C₀ C₁ C₂ D₁ D₂ : Type*}
    (f : A → B) (g₀ : A → C₀) (g₁ : A → C₁) (g₂ : A → C₂)
    (h₁ : B → D₁) (h₂ : B → D₂) (k₁ : C₁ → D₁) (k₂ : C₂ → D₂)
    (u : C₀ → C₁) (v : C₀ → C₂) (w : D₁ → D₂)
    (hu : Function.Injective u) (hv : Function.Surjective v) (hw : Function.Injective w)
    (hg₁ : ∀ a, g₁ a = u (g₀ a)) (hg₂ : ∀ a, g₂ a = v (g₀ a))
    (hh : ∀ b, w (h₁ b) = h₂ b) (hk : ∀ c, w (k₁ (u c)) = k₂ (v c))
    (hlift : ∀ b c, h₁ b = k₁ c → ∃ a, f a = b ∧ g₁ a = c)
    (b : B) (c : C₂) (he : h₂ b = k₂ c) :
    ∃ a, f a = b ∧ g₂ a = c := by
  obtain ⟨c₀, hc₀⟩ := hv c
  have he₁ : h₁ b = k₁ (u c₀) := hw (by rw [hh, hk, hc₀]; exact he)
  obtain ⟨a, ha, ha₁⟩ := hlift b (u c₀) he₁
  have ha₀ : g₀ a = c₀ := hu (by rw [← hg₁]; exact ha₁)
  exact ⟨a, ha, by rw [hg₂, ha₀, hc₀]⟩

end SerrePositivity.AlgebraicGeometry
