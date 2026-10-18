module

public import SerrePositivity.KST.ProExcision.FilteredSpectralMaps

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 有限テンソル濾過と Koszul 頁の塔

概要：Koszul 冪の実際の遷移を濾過とスペクトル対象へ写し、頁の項の塔を構成する。
方針：構成済みの関手を合成し、各段では既存の頁計算と同型にする。
規約：頁の遷移はスペクトル対象の射から定義し、仮定として供給しない。
使われ方：KST Lemma 4.10 の pro-スペクトル系列の実装。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：複体の項濾過を右テンソルし有限添字へ制限する関手。
方針：切り詰め濾過関手と関手圏の前後合成を使う。
規約：係数複体 K は固定。使われ方：KST Lemma 4.10 の Koszul 冪の有限濾過の塔。 -/
def finiteTensorFiltrationFunctor (e : ℕ) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      (Fin (e + 2) ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :=
  truncationFiltrationFunctor ⋙
    (Functor.whiskeringRight ℤ (CochainComplex (ModuleCat.{u} R) ℤ)
      (CochainComplex (ModuleCat.{u} R) ℤ)).obj (tensorRight K) ⋙
    (Functor.whiskeringLeft (Fin (e + 2)) ℤ (CochainComplex (ModuleCat.{u} R) ℤ)).obj
      (koszulFiltrationIndex e)

/-- 概要：複体から有限テンソル濾過のホモロジースペクトル対象を得る関手。
方針：有限テンソル濾過関手と、δ と可換なホモロジースペクトル対象関手を合成する。
規約：任意の複体射を許す。使われ方：KST Lemma 4.10 の冪遷移の持ち上げ。 -/
def finiteTensorSpectralFunctor (e : ℕ) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      Abelian.SpectralObject (ModuleCat.{u} R) (Fin (e + 2)) :=
  finiteTensorFiltrationFunctor e K ⋙ filteredHomologySpectralFunctor (Fin (e + 2))

/-- 概要：Koszul 冪の実際の遷移から作る有限ホモロジースペクトル対象の塔。
方針：Koszul 複体の塔に有限テンソルスペクトル対象関手を適用する。
規約：K は固定、冪指数は塔の添字。使われ方：KST Lemma 4.10 の定数係数複体の場合。 -/
def koszulSpectralTower {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    Tower (Abelian.SpectralObject (ModuleCat.{u} R) (Fin (e + 2))) :=
  (koszulTower z).map (finiteTensorSpectralFunctor e K)

/-- 概要：Koszul スペクトル対象の塔の各段は既存の有限濾過のスペクトル対象。
方針：関手合成の対象部分を展開する。
規約：第 n 段の生成元は z_i^n。使われ方：KST Lemma 4.10 の既存頁計算との接続。 -/
theorem koszulSpectralTower_obj {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (koszulSpectralTower z K).obj n = koszulFilteredSpectralObject (fun i ↦ z i ^ n) K := by
  rfl

/-- 概要：Koszul スペクトル対象の塔の各頁の項を実際の射の塔として構成する。
方針：有限行の頁データで指定される三区間の E 関手を塔へ適用する。
規約：r は Mathlib の頁番号、r≥2。使われ方：KST Lemma 4.10 の E₂ から上の pro-零性。 -/
def koszulPageETower {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × Fin (e + 1)) : Tower (ModuleCat.{u} R) :=
  let data := Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1)
  let n := data.deg pq
  (koszulSpectralTower z K).map
    (spectralPageFunctor
      (homOfLE (data.le₀₁' r hr pq rfl rfl))
      (homOfLE (data.le₁₂' pq rfl rfl))
      (homOfLE (data.le₂₃' r hr pq rfl rfl))
      (n - 1) n (n + 1) (by omega) rfl)

/-- 概要：頁の項の塔の第 n 段は、実際の n 乗 Koszul 濾過の頁の項と同型。
方針：有限行のスペクトル系列の標準 E 表示を使う。
規約：段ごとの同型を明示する。遷移との自然性は別途検証する。
使われ方：KST Lemma 4.10 の頁計算と実際の塔の比較。 -/
def koszulPageTowerLevelIso {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℤ × Fin (e + 1)) (n : ℕ) :
    ((koszulFilteredSpectralSequence (fun i ↦ z i ^ n) K).page r hr).X pq ≅
      (koszulPageETower z K r hr pq).obj n :=
  (koszulFilteredSpectralObject (fun i ↦ z i ^ n) K).spectralSequencePageXIso
    (Abelian.SpectralObject.coreE₂CohomologicalFin (e + 1)) r hr pq _ _ _ _
      rfl rfl rfl rfl _ _ _ rfl

end SerrePositivity.KST.ProExcision
