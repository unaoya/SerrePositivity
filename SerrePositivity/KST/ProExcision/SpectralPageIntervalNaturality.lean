module

public import SerrePositivity.KST.ProExcision.SpectralObjectCyclesMaps

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 頁の区間変更とスペクトル対象の射

概要：頁を定める区間図式の変更は、スペクトル対象の射に自然である。
方針：短複体の各成分で区間ホモロジーの自然変換を評価し、ホモロジーを取る。
規約：頁の微分の自然性とは別に、区間の両端の変更を比較する。
使われ方：KST Lemma 4.10 の頁ホモロジーと次頁の比較の自然性。
-/

universe u v w w'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} [Category.{w'} I]
variable {X Y : Abelian.SpectralObject C I}

/-- 概要：頁を定義する短複体の区間変更は、スペクトル対象の射と可換。
方針：三つの成分で次数別自然変換の自然性を使う。
規約：四頂点の任意の可換図式を許す。使われ方：KST Lemma 4.10 の頁間比較の自然性。 -/
theorem spectralShortComplexMap_interval
    (φ : X ⟶ Y) {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : I}
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂) (g₃ : b₂ ⟶ b₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (spectralShortComplexFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ ≫
      Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ h₁ h₂ =
      X.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ h₁ h₂ ≫
        (spectralShortComplexFunctor g₁ g₂ g₃ n₀ n₁ n₂ h₁ h₂).map φ := by
  apply ShortComplex.Hom.ext
  · exact ((φ.hom n₀).naturality (homMk₁ (F := mk₁ f₃) (G := mk₁ g₃) (α.app 2) (α.app 3) (naturality' α 2 3))).symm
  · exact ((φ.hom n₁).naturality (homMk₁ (F := mk₁ f₂) (G := mk₁ g₂) (α.app 1) (α.app 2) (naturality' α 1 2))).symm
  · exact ((φ.hom n₂).naturality (homMk₁ (F := mk₁ f₁) (G := mk₁ g₁) (α.app 0) (α.app 1) (naturality' α 0 1))).symm

/-- 概要：三区間の頁の区間変更は、スペクトル対象の射が誘導する頁の射と可換。
方針：短複体上の可換四角形にホモロジー関手を適用する。
規約：恒等を含む四頂点の図式変更。使われ方：KST Lemma 4.10 の頁ホモロジー同型の自然性。 -/
theorem spectralPageMap_interval
    (φ : X ⟶ Y) {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : I}
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂) (g₃ : b₂ ⟶ b₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (spectralPageFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ ≫
      Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ h₁ h₂ =
      X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ h₁ h₂ ≫
        (spectralPageFunctor g₁ g₂ g₃ n₀ n₁ n₂ h₁ h₂).map φ := by
  have h := congrArg (fun f ↦ ShortComplex.homologyMap f)
    (spectralShortComplexMap_interval φ f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ h₁ h₂)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact h

/-- 概要：明示した核・ホモロジー模型上の二つの可換四角形から、標準ホモロジー射との比較を得る。
方針：左ホモロジー写像データを構成し、包含で相殺して境界の四角形も導く。
規約：模型は Mathlib の LeftHomologyData。使われ方：KST Lemma 4.10 の頁ホモロジー同型の自然性。 -/
theorem leftHomologyModelMap_comm
    {S T : ShortComplex C} (f : S ⟶ T)
    (hS : S.LeftHomologyData) (hT : T.LeftHomologyData)
    (k : hS.K ⟶ hT.K) (m : hS.H ⟶ hT.H)
    (hi : k ≫ hT.i = hS.i ≫ f.τ₂) (hπ : hS.π ≫ m = k ≫ hT.π) :
    ShortComplex.homologyMap f ≫ hT.homologyIso.hom = hS.homologyIso.hom ≫ m := by
  let γ : ShortComplex.LeftHomologyMapData f hS hT :=
    { φK := k
      φH := m
      commi := hi
      commπ := hπ
      commf' := by
        apply (cancel_mono hT.i).mp
        rw [Category.assoc, hi, ← Category.assoc, hS.f'_i,
          Category.assoc, hT.f'_i, f.comm₁₂] }
  exact γ.homologyMap_comm

/-- 概要：頁の左端を変える標準射はスペクトル対象の射に自然。
方針：四頂点の標準区間図式に頁の区間変更の自然性を適用する。
規約：指数は前順序集合。使われ方：KST Lemma 4.10 の頁ホモロジーの核模型。 -/
theorem spectralPageMap_fourδ₁Toδ₀
    {J : Type w} [Preorder J] {X Y : Abelian.SpectralObject C J} (φ : X ⟶ Y)
    (i₀ i₁ i₂ i₃ i₄ : J) (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂)
    (h₂₃ : i₂ ≤ i₃) (h₃₄ : i₃ ≤ i₄)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (spectralPageFunctor (homOfLE (h₀₁.trans h₁₂)) (homOfLE h₂₃) (homOfLE h₃₄)
        n₀ n₁ n₂ hn₁ hn₂).map φ ≫
      Y.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄ n₀ n₁ n₂ hn₁ hn₂ =
      X.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
        (spectralPageFunctor (homOfLE h₁₂) (homOfLE h₂₃) (homOfLE h₃₄)
          n₀ n₁ n₂ hn₁ hn₂).map φ :=
  spectralPageMap_interval φ _ _ _ _ _ _
    (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄) n₀ n₁ n₂ hn₁ hn₂

/-- 概要：頁の右端を変える標準射はスペクトル対象の射に自然。
方針：右端を拡げる四頂点の図式に頁の区間変更の自然性を適用する。
規約：指数は前順序集合。使われ方：KST Lemma 4.10 の頁ホモロジー模型の全射。 -/
theorem spectralPageMap_fourδ₄Toδ₃
    {J : Type w} [Preorder J] {X Y : Abelian.SpectralObject C J} (φ : X ⟶ Y)
    (i₀ i₁ i₂ i₃ i₄ : J) (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂)
    (h₂₃ : i₂ ≤ i₃) (h₃₄ : i₃ ≤ i₄)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (spectralPageFunctor (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        n₀ n₁ n₂ hn₁ hn₂).map φ ≫
      Y.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄ n₀ n₁ n₂ hn₁ hn₂ =
      X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
        (spectralPageFunctor (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE (h₂₃.trans h₃₄))
          n₀ n₁ n₂ hn₁ hn₂).map φ :=
  spectralPageMap_interval φ _ _ _ _ _ _
    (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ h₀₁ h₁₂ h₂₃ h₃₄) n₀ n₁ n₂ hn₁ hn₂

end SerrePositivity.KST.ProExcision
