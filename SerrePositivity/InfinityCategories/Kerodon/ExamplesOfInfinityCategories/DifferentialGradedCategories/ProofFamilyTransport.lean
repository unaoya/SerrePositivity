module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 証明だけを引数とする射族の移送

概要：四つの証明引数を取る射族は、添字の等式に沿って移して評価しても元の評価に一致する。
方針：添字の等式を消去し、証明の一意性を使う。
規約：HA Construction 1.3.1.6 の端点・次数指定。使われ方：有限集合の切断の同定後の成分評価。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：四つの証明引数を取る射族の移送後の値は、移送前の任意の有効な証明での値に等しい。
方針：添字の等式を消去し、全ての証明引数を証明の一意性で同定する。
規約：HA Construction 1.3.1.6。使われ方：部分集合を同定した成分族の依存型の移送を取り除く。 -/
lemma eqRec_proofFamily_apply {ι : Sort v} {i j : ι} {T : Sort u}
    (P₁ : ι → Prop) (P₂ : ∀ t, P₁ t → Prop)
    (P₃ : ∀ t (p₁ : P₁ t), P₂ t p₁ → Prop)
    (P₄ : ∀ t (p₁ : P₁ t) (p₂ : P₂ t p₁), P₃ t p₁ p₂ → Prop)
    (f : ∀ (p₁ : P₁ i) (p₂ : P₂ i p₁) (p₃ : P₃ i p₁ p₂), P₄ i p₁ p₂ p₃ → T)
    (h : i = j) (q₁ : P₁ j) (q₂ : P₂ j q₁) (q₃ : P₃ j q₁ q₂) (q₄ : P₄ j q₁ q₂ q₃)
    (p₁ : P₁ i) (p₂ : P₂ i p₁) (p₃ : P₃ i p₁ p₂) (p₄ : P₄ i p₁ p₂ p₃) :
    (Eq.rec (motive := fun t _ => ∀ (a : P₁ t) (b : P₂ t a) (c : P₃ t a b), P₄ t a b c → T)
      f h) q₁ q₂ q₃ q₄ = f p₁ p₂ p₃ p₄ := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
