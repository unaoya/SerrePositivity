module

public import SerrePositivity.BhattScholze.Andre.PrimeAdicCompletionUniversal
public import SerrePositivity.BhattScholze.Andre.PowerRootEquationQuotient

/-!
# André A1-a：方程式商の p 完備化の普遍性

## 概要

通常の方程式商 R[Y^(1/p^∞)]/(f) の p 完備化から p 完備環への射は、
係数射と f を消す互換根列で一意に決まる。BS Rem 7.15（著者版 p.62）の入力比較。

## 方針

通常の商の普遍性と p 完備化の環射の普遍性を続けて使う。
原典の記述を補う具体的な通常の商と完備化による経路。

## 規約

ここで完備化するのは通常の方程式商。完備多項式環を f で割る順序との交換は別工程。
源の p 正則性・モニック性・正次数は要求しない。

## 使われ方

完備入力環からの試験射を根データで扱う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "S" => PowerRootEquationQuotient p hp f
local notation "C" => AdicCompletion (Ideal.span {(p : S)}) S
local notation "j" => algebraMap S C
local notation "c" => powerRootEquationQuotientCoeff p hp f
local notation "r" => powerRootEquationQuotientRoot p hp f

/-- 概要：方程式商の p 完備化からの射は係数と互換な方程式の根列で一意に定まる。
方針：通常の商からの一意な射を p 完備化へ一意に延長する。
規約：完備化前の入力根の自然像を全て保存する。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力環からの試験射。 -/
theorem existsUnique_powerRootEquationCompletionHom (k : R →+* B)
    (ρ : ℕ → B) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (hf : f.eval₂ k (ρ 0) = 0) :
    ∃! F : C →+* B, (F.comp j).comp c = k ∧ ∀ n, F (j (r n)) = ρ n := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_powerRootEquationQuotientHom p hp f k ρ hρ hf
  obtain ⟨F, hF, hu⟩ := existsUnique_primeAdicCompletionHom S p g
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · rw [hF]
    exact hg.1
  · intro n
    exact (RingHom.congr_fun hF (r n)).trans (hg.2 n)
  · intro K hK
    exact hu K (hgu (K.comp j) ⟨hK.1, hK.2⟩)

end SerrePositivity.BhattScholze.Andre
