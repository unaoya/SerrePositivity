module

public import SerrePositivity.KST.ProExcision.SpectralObjectCyclesMaps

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# スペクトル対象から各頁の複体への関手

概要：固定した頁データに対し、スペクトル対象の射を頁の複体射へ持ち上げる。
方針：三区間の頁関手と微分の自然変換を、添字変更の自然同型で結ぶ。
規約：Mathlib の実際の pageX・pageD と比較する。
使われ方：KST Lemma 4.10 の頁複体とそのホモロジーの塔。
-/

universe u v w w' k

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} [Category.{w'} I]

/-- 概要：五つの区間から定まる頁の微分を自然変換として構成する。
方針：各スペクトル対象の実際の d を使い、頁の射との可換性を適用する。
規約：源と標的は対応する三区間の頁関手。
使われ方：KST Lemma 4.10 の各頁の複体射の構成。 -/
def spectralDifferentialNatTrans
    {i₀ i₁ i₂ i₃ i₄ i₅ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) (h₃ : n₂ + 1 = n₃) :
    spectralPageFunctor (C := C) f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂ ⟶
      spectralPageFunctor f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃ where
  app X := X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃
  naturality {_ _} φ := spectralPageMap_d φ f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃

variable {J : Type w} [Preorder J] {κ : Type k}
variable {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- 概要：頁データの指定位置の項をスペクトル対象に関する関手にする。
方針：標準の四添字と三つの連続次数で頁関手を評価する。
規約：Mathlib の pageX と同じ模型。使われ方：KST Lemma 4.10 の頁複体関手の項。 -/
def spectralSequenceTermFunctor
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) : Abelian.SpectralObject C J ⥤ C :=
  spectralPageFunctor (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq)) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
      (by omega) rfl

/-- 概要：指定位置の頁関手を、等しい四添字と次数の任意表示へ自然に移す。
方針：添字と次数の等式で置換し恒等の自然同型を使う。
規約：対象ごとの同型ではなく自然同型として構成する。
使われ方：KST Lemma 4.10 の頁微分の添字整合性。 -/
def spectralSequenceTermFunctorIso
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : J) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    spectralSequenceTermFunctor (C := C) data r hr pq ≅
      spectralPageFunctor (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂)) (homOfLE (data.le₂₃' r hr pq h₂ h₃))
        n₀ n₁ n₂ hn₁ hn₂ := by
  obtain rfl : n₀ = n₁ - 1 := by omega
  subst h hn₂ h₀ h₁ h₂ h₃
  exact Iso.refl _

/-- 概要：頁関手の添字変更の自然同型は Mathlib の pageXIso と同じ対象成分を持つ。
方針：添字と次数を正規化し、両方の恒等同型を比較する。
規約：Mathlib の E 表示を変えない。使われ方：KST Lemma 4.10 の実際の頁微分との比較。 -/
theorem spectralSequenceTermFunctorIso_app
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : J) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (X : Abelian.SpectralObject C J) :
    (spectralSequenceTermFunctorIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃
      n₀ n₁ n₂ h hn₁ hn₂).app X =
      Abelian.SpectralObject.SpectralSequence.pageXIso X data r hr pq
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂ := by
  obtain rfl : n₀ = n₁ - 1 := by omega
  subst h hn₂ h₀ h₁ h₂ h₃
  rfl

/-- 概要：固定した頁データの二位置の微分を自然変換にする。
方針：微分が許される位置では五区間の微分と添字変更同型を合成し、他では零とする。
規約：Mathlib の pageD と同じ場合分け。使われ方：KST Lemma 4.10 の頁複体関手。 -/
def spectralSequencePageDNatTrans
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    spectralSequenceTermFunctor (C := C) data r hr pq ⟶
      spectralSequenceTermFunctor data r hr pq' := by
  classical
  exact if hpq : (c r).Rel pq pq' then
    spectralDifferentialNatTrans
      (homOfLE (data.le₀₁ r pq'))
      (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
      (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2)
      (by omega) rfl (by omega) ≫
    (spectralSequenceTermFunctorIso data r hr pq'
      (data.i₀ r pq') (data.i₁ pq') (data.i₀ r pq) (data.i₁ pq)
      rfl rfl (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq)
      (data.deg pq) (data.deg pq + 1) (data.deg pq + 2)
      (data.hc r pq pq' hpq) rfl (by omega)).inv
  else 0

/-- 概要：頁微分の自然変換の各成分は Mathlib の実際の pageD。
方針：位置の微分関係で場合分けし、添字変更同型の対象成分を比較する。
規約：零微分の位置も含める。使われ方：KST Lemma 4.10 の既存頁複体との同定。 -/
theorem spectralSequencePageDNatTrans_app
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (X : Abelian.SpectralObject C J) :
    (spectralSequencePageDNatTrans data r hr pq pq').app X =
      Abelian.SpectralObject.SpectralSequence.pageD X data r pq pq' hr := by
  classical
  by_cases hpq : (c r).Rel pq pq'
  · simp only [spectralSequencePageDNatTrans, dite_eq_left hpq, NatTrans.comp_app,
      spectralDifferentialNatTrans, ← Iso.app_inv, spectralSequenceTermFunctorIso_app,
      Abelian.SpectralObject.SpectralSequence.pageD]
  · simp [spectralSequencePageDNatTrans, Abelian.SpectralObject.SpectralSequence.pageD, hpq]

/-- 概要：固定した頁の複体をスペクトル対象に関する関手にする。
方針：項は三区間の頁関手、微分の可換性は微分自然変換から得る。
規約：対象部分は Mathlib の実際の page。使われ方：KST Lemma 4.10 の頁複体とホモロジーの塔。 -/
def spectralSequencePageFunctor
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    Abelian.SpectralObject C J ⥤ HomologicalComplex C (c r) where
  obj X := Abelian.SpectralObject.SpectralSequence.page X data r hr
  map φ :=
    { f := fun pq ↦ (spectralSequenceTermFunctor data r hr pq).map φ
      comm' := by
        intro pq pq' _
        have h := (spectralSequencePageDNatTrans data r hr pq pq').naturality φ
        rw [spectralSequencePageDNatTrans_app, spectralSequencePageDNatTrans_app] at h
        exact h }
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext pq
    exact (spectralSequenceTermFunctor data r hr pq).map_id X
  map_comp φ ψ := by
    apply HomologicalComplex.Hom.ext
    funext pq
    exact (spectralSequenceTermFunctor data r hr pq).map_comp φ ψ

unseal Abelian.SpectralObject.spectralSequence in
/-- 概要：頁複体関手の対象は、既存スペクトル系列の実際の頁に一致する。
方針：スペクトル系列の定義を局所的に展開して比較する。
規約：頁が存在するという Mathlib の条件を受け取る。
使われ方：KST Lemma 4.10 の頁関手と既存スペクトル系列の接続。 -/
theorem spectralSequencePageFunctor_obj
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (X : Abelian.SpectralObject C J) [X.HasSpectralSequence data] :
    (spectralSequencePageFunctor data r hr).obj X = (X.spectralSequence data).page r hr := by
  rfl

end SerrePositivity.KST.ProExcision
