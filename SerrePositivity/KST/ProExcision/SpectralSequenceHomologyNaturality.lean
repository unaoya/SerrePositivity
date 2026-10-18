module

public import SerrePositivity.KST.ProExcision.SpectralSequencePageFunctor
public import SerrePositivity.KST.ProExcision.SpectralPageIntervalNaturality

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 頁ホモロジーと次頁の同型の自然性

概要：頁間ホモロジー同型の自然性に必要な核模型と二つの自然変換を構成する。
方針：核模型と全射を区間の両端変更の自然変換として扱う。公開 homologyData との接続は依存側の kernel エラーにより未実装。
規約：Mathlib の実際の homologyData と homologyIso を比較する。
使われ方：KST Lemma 4.10 の次頁への pro-零性の移送。
-/

universe u v w k

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type w} [Preorder J] {κ : Type k}
variable {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- 概要：頁ホモロジーの核を表す三区間の頁関手。
方針：左端だけを次頁の位置へ移し、右端は元の頁に保つ。
規約：r' は r+1。使われ方：KST Lemma 4.10 の頁ホモロジー模型の自然性。 -/
def spectralSequencePageKernelFunctor
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    Abelian.SpectralObject C J ⥤ C :=
  spectralPageFunctor (homOfLE (data.le₀₁' r' (by omega) pq rfl rfl))
    (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl

/-- 概要：頁の核模型から元の頁への包含を自然変換として構成する。
方針：左端を変える標準射の自然性を適用する。
規約：元の頁の標準 E 表示を使う。使われ方：KST Lemma 4.10 の核模型の包含の自然性。 -/
def spectralSequencePageKernelInclusion
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    spectralSequencePageKernelFunctor (C := C) data r r' hrr' hr pq ⟶
      spectralSequenceTermFunctor data r hr pq where
  app X := X.mapFourδ₁Toδ₀' (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq)
    (data.i₂ pq) (data.i₃ r pq) (data.i₀_le' hrr' hr pq rfl rfl)
    (data.le₀₁ r pq) (data.le₁₂ pq) (data.le₂₃ r pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl
  naturality {_ _} φ := spectralPageMap_fourδ₁Toδ₀ φ _ _ _ _ _
    (data.i₀_le' hrr' hr pq rfl rfl) (data.le₀₁ r pq) (data.le₁₂ pq) (data.le₂₃ r pq)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl

/-- 概要：頁の核模型から次頁の項への全射を自然変換として構成する。
方針：右端を次頁まで拡げる標準射の自然性を適用する。
規約：対象は実際の次頁の E 模型。使われ方：KST Lemma 4.10 の頁ホモロジー模型の射影の自然性。 -/
def spectralSequencePageKernelProjection
    (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    spectralSequencePageKernelFunctor (C := C) data r r' hrr' hr pq ⟶
      spectralSequenceTermFunctor data r' (by omega) pq where
  app X := X.mapFourδ₄Toδ₃' (data.i₀ r' pq) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq) (data.i₃ r' pq) (data.le₀₁' r' (by omega) pq rfl rfl)
    (data.le₁₂ pq) (data.le₂₃ r pq) (data.le₃₃' hrr' hr pq rfl rfl)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl
  naturality {_ _} φ := spectralPageMap_fourδ₄Toδ₃ φ _ _ _ _ _
    (data.le₀₁' r' (by omega) pq rfl rfl) (data.le₁₂ pq) (data.le₂₃ r pq)
    (data.le₃₃' hrr' hr pq rfl rfl)
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (by omega) rfl

end SerrePositivity.KST.ProExcision
