module

public import SerrePositivity.KST.ProExcision.FilteredTowers
public import SerrePositivity.KST.ProExcision.SpectralSequencePageFunctor

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Koszul 頁複体とホモロジーの塔

概要：各頁の複体関手に Koszul スペクトル対象の塔を写す。
方針：対象・項・遷移を既存の頁模型へ比較し、ホモロジーの pro-零性補題を適用する。
規約：次頁とのホモロジー同型の遷移自然性は別途証明する。
使われ方：KST Lemma 4.10 の E₂ からの消滅伝播。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：Koszul 冪の実際の遷移から作る各頁の複体の塔。
方針：スペクトル対象の塔に各頁複体の関手を適用する。
規約：r≥2 は Mathlib の頁番号。使われ方：KST Lemma 4.10 の頁の微分と可換な遷移。 -/
def koszulPageComplexTower {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r) :
    Tower (HomologicalComplex (ModuleCat.{u} R)
      (ComplexShape.spectralSequenceFin (e + 1) (r, 1 - r))) :=
  (koszulSpectralTower z K).map
    (spectralSequencePageFunctor (Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1)) r hr)

/-- 概要：頁複体の塔の各段は、既存の Koszul 冪のスペクトル系列の実際の頁。
方針：頁複体関手の対象比較と既存の Koszul スペクトル対象を使う。
規約：第 n 段は z_i^n。使われ方：KST Lemma 4.10 の既存頁計算との一致。 -/
theorem koszulPageComplexTower_obj {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r) (n : ℕ) :
    (koszulPageComplexTower z K r hr).obj n =
      (koszulFilteredSpectralSequence (fun i ↦ z i ^ n) K).page r hr :=
  spectralSequencePageFunctor_obj (Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1))
    r hr (koszulFilteredSpectralObject (fun i ↦ z i ^ n) K)

/-- 概要：頁複体の塔の指定位置の項は既存の E 模型の項の塔に一致。
方針：頁複体関手の成分と E 関手の定義を比較する。
規約：対象だけでなく遷移も同じ。使われ方：KST Lemma 4.10 の項の pro-零性の移送。 -/
theorem koszulPageComplexTower_eval_eq {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × Fin (e + 1)) :
    (koszulPageComplexTower z K r hr).map (eval _ _ pq) = koszulPageETower z K r hr pq := by
  rfl

/-- 概要：Koszul 冪の各頁複体の指定位置のホモロジーの塔。
方針：実際の頁複体射のホモロジーを取る。
規約：次頁の項の塔とはここでは同一視しない。使われ方：KST Lemma 4.10 の頁間比較。 -/
def koszulPageHomologyTower {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × Fin (e + 1)) : Tower (ModuleCat.{u} R) :=
  (koszulPageComplexTower z K r hr).map (homologyFunctor _ _ pq)

/-- 概要：頁の指定位置の項が pro-零なら、その位置の頁ホモロジーも pro-零。
方針：項の塔と E 模型の同一性を用い、複体の項からホモロジーへの零性保存を適用する。
規約：遷移の微分との可換性は構成済み。使われ方：KST Lemma 4.10 の消滅伝播。 -/
theorem koszulPageHomologyTower_isProZero_of_terms {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × Fin (e + 1)) (h : IsProZero (koszulPageETower z K r hr pq)) :
    IsProZero (koszulPageHomologyTower z K r hr pq) :=
  homology_proZero_of_component (koszulPageComplexTower z K r hr) pq h

end SerrePositivity.KST.ProExcision
