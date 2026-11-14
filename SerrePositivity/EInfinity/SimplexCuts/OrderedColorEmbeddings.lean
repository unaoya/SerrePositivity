module

public import SerrePositivity.EInfinity.SimplexCuts.Signs
public import SerrePositivity.EInfinity.SimplexCuts.VertexLists

/-!
# 元の色の順序を保つ番号の変更

Berger–Fresse §2.2.4・§2.2.6、M14 L12a、報告 §329。
残り色を順序単射で元の色へ戻しても、同じ整数符号と全頂点列を保つ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 色の単射は、同じraw語の全区切りを保つ（BF §1.2.3）。 -/
lemma caesura_comp_injective {l r R : ℕ} (v : Fin l → Fin r) (φ : Fin r → Fin R)
    (hφ : Function.Injective φ) (i : Fin l) :
    Surjection.Caesura (φ ∘ v) i ↔ Surjection.Caesura v i := by
  simp only [Surjection.Caesura, Function.comp_apply, hφ.eq_iff]

/-- 色の単射は元の全区間の重みを保つ（BF §2.2.4）。 -/
lemma intervalLength_comp_injective {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ)
    (i : Fin (m + 1)) : intervalLength s (φ ∘ v) i = intervalLength s v i := by
  simp only [intervalLength, caesura_comp_injective v φ hφ]

/-- 色の順序単射は元の整数符号を厳密に保つ（BF §2.2.4）。 -/
lemma cutSign_comp_strictMono {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : StrictMono φ) :
    cutSign s (φ ∘ v) = cutSign s v := by
  simp only [cutSign, permutationExponent, positionExponent, Function.comp_apply,
    hφ.lt_iff_lt, intervalLength_comp_injective s v φ hφ.injective,
    caesura_comp_injective v φ hφ.injective]

/-- 色の単射は元の色ごとの全頂点列を保つ（BF §2.2.6）。 -/
lemma verticesList_comp_injective {m q r R : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (φ : Fin r → Fin R) (hφ : Function.Injective φ)
    (c : Fin r) : verticesList s (φ ∘ v) (φ c) = verticesList s v c := by
  have hc : colorPositions s (φ ∘ v) (φ c) = colorPositions s v c := by
    unfold colorPositions
    apply Finset.filter_congr
    intro j _
    exact hφ.eq_iff
  simp only [verticesList, hc]

end SerrePositivity.EInfinity.SimplexCuts
