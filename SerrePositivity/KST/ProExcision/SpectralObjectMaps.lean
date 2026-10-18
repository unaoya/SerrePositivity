module

public import SerrePositivity.KST.ProExcision.KoszulCoefficientRow

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# スペクトル対象の射と頁の関手性

概要：スペクトル対象の射から、三つの区間で定まる頁の射を構成する。
方針：二つの連結写像からなる短複体の関手を作り、そのホモロジーを取る。
規約：恒等射と合成の保存を関手の法則として持つ。
使われ方：KST Lemma 4.10 の Koszul 冪遷移と頁の塔。
-/

universe u v w w'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 概要：短複体の射の中央成分が零なら誘導ホモロジー射も零。
方針：サイクルへの単射とホモロジーへの全射で比較する。
規約：外側二成分に零性を要求しない。使われ方：KST Lemma 4.10 の頁の pro-零性保存。 -/
theorem shortComplex_homologyMap_zero_of_middle
    {S T : ShortComplex C} (f : S ⟶ T) (hf : f.τ₂ = 0) :
    ShortComplex.homologyMap f = 0 := by
  have hc : ShortComplex.cyclesMap f = 0 := by
    apply (cancel_mono T.iCycles).mp
    rw [ShortComplex.cyclesMap_i, hf, comp_zero, zero_comp]
  apply (cancel_epi S.homologyπ).mp
  rw [ShortComplex.homologyπ_naturality, hc, zero_comp, comp_zero]

variable {I : Type w} [Category.{w'} I]

/-- 概要：二つの連結写像からなる短複体をスペクトル対象の関手として構成する。
方針：各成分にスペクトル対象の射の次数別自然変換を評価する。
規約：三つの区間と三つの連続次数を固定する。
使われ方：KST Lemma 4.10 の頁の射と塔の合成則。 -/
def spectralShortComplexFunctor
    {i₀ i₁ i₂ i₃ : I} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    Abelian.SpectralObject C I ⥤ ShortComplex C where
  obj X := X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂
  map φ :=
    { τ₁ := (φ.hom n₀).app (ComposableArrows.mk₁ f₃)
      τ₂ := (φ.hom n₁).app (ComposableArrows.mk₁ f₂)
      τ₃ := (φ.hom n₂).app (ComposableArrows.mk₁ f₁)
      comm₁₂ := (φ.comm n₀ n₁ h₁ f₂ f₃).symm
      comm₂₃ := (φ.comm n₁ n₂ h₂ f₁ f₂).symm }
  map_id X := by ext <;> rfl
  map_comp φ ψ := by ext <;> rfl

/-- 概要：三つの区間で定まる頁を、スペクトル対象に関する関手にする。
方針：連結写像の短複体関手にホモロジー関手を後合成する。
規約：Mathlib の E と同じホモロジー模型。
使われ方：KST Lemma 4.10 の各頁の遷移を実際の射から構成する。 -/
def spectralPageFunctor
    {i₀ i₁ i₂ i₃ : I} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    Abelian.SpectralObject C I ⥤ C :=
  spectralShortComplexFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ ⋙ ShortComplex.homologyFunctor C

/-- 概要：中央区間の次数別射が零なら、対応する頁の射も零。
方針：頁を定義する短複体の中央成分へ零性の一般補題を適用する。
規約：像の対象の零性ではなく、実際の遷移射の零性。
使われ方：KST Lemma 4.10 の塔の eventual 零化。 -/
theorem spectralPageFunctor_map_zero
    {i₀ i₁ i₂ i₃ : I} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂)
    {X Y : Abelian.SpectralObject C I} (φ : X ⟶ Y)
    (hφ : (φ.hom n₁).app (ComposableArrows.mk₁ f₂) = 0) :
    (spectralPageFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ = 0 :=
  shortComplex_homologyMap_zero_of_middle
    ((spectralShortComplexFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ) hφ

/-- 概要：関手間の自然変換を、有限個の合成可能な射の図式の間へ持ち上げる。
方針：各図式に左 whisker を適用し、各頂点の自然性を使う。
規約：任意の図式長 n。使われ方：KST Lemma 4.10 の濾過間の射とスペクトル対象の比較。 -/
def composableArrowsMapNatTrans
    {A : Type u} [Category A] {B : Type v} [Category B]
    {F G : A ⥤ B} (α : F ⟶ G) (n : ℕ) :
    F.mapComposableArrows n ⟶ G.mapComposableArrows n where
  app D := Functor.whiskerLeft D α
  naturality D E f := by
    ext p
    exact α.naturality (f.app p)

/-- 概要：合成可能図式への自然変換の持ち上げは恒等射を保つ。
方針：図式の各頂点で比較する。
規約：図式長は固定。使われ方：KST Lemma 4.10 の塔の恒等遷移。 -/
theorem composableArrowsMapNatTrans_id
    {A : Type u} [Category A] {B : Type v} [Category B] (F : A ⥤ B) (n : ℕ) :
    composableArrowsMapNatTrans (𝟙 F) n = 𝟙 (F.mapComposableArrows n) := by
  ext D p
  rfl

/-- 概要：合成可能図式への自然変換の持ち上げは合成を保つ。
方針：図式の各頂点で二つの自然変換の合成を評価する。
規約：順序を変えずに合成する。使われ方：KST Lemma 4.10 の塔の遷移合成則。 -/
theorem composableArrowsMapNatTrans_comp
    {A : Type u} [Category A] {B : Type v} [Category B]
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    composableArrowsMapNatTrans (α ≫ β) n =
      composableArrowsMapNatTrans α n ≫ composableArrowsMapNatTrans β n := by
  ext D p
  rfl

end SerrePositivity.KST.ProExcision
