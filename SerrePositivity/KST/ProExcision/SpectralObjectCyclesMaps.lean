module

public import SerrePositivity.KST.ProExcision.SpectralObjectMaps

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# スペクトル対象の射とサイクル・商・頁

概要：スペクトル対象の射を連結写像の核と余核へ誘導し、頁の標準射との可換性を証明する。
方針：核・余核の普遍性と短複体のホモロジー写像の自然性を使う。
規約：既存の頁の E 模型と標準の πE・ιE を使用する。
使われ方：KST Lemma 4.10 の頁の微分の自然性。
-/

universe u v w w'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} [Category.{w'} I]
variable {X Y : Abelian.SpectralObject C I}

/-- 概要：スペクトル対象の射が連結写像の核へ誘導する射。
方針：中央区間の自然変換を核へ制限し、δ との可換性を使う。
規約：核は Mathlib の標準 cycles。使われ方：KST Lemma 4.10 の頁微分の自然性。 -/
def spectralCyclesMap (φ : X ⟶ Y) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.cycles f g n ⟶ Y.cycles f g n :=
  kernel.lift _ (X.iCycles f g n ≫ (φ.hom n).app (mk₁ g)) (by
    rw [Category.assoc, ← φ.comm n (n + 1) rfl f g, ← Category.assoc,
      X.iCycles_δ f g n (n + 1) rfl, zero_comp])

/-- 概要：核上の誘導射は核の包含と可換。
方針：核の普遍性の標準等式を使う。
規約：中央区間の自然変換を右辺に置く。使われ方：KST Lemma 4.10 のサイクル比較。 -/
theorem spectralCyclesMap_iCycles (φ : X ⟶ Y)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    spectralCyclesMap φ f g n ≫ Y.iCycles f g n =
      X.iCycles f g n ≫ (φ.hom n).app (mk₁ g) := by
  exact kernel.lift_ι _ _ _

/-- 概要：スペクトル対象の射が連結写像の余核へ誘導する射。
方針：中央区間の自然変換を余核へ降ろし、δ との可換性を使う。
規約：余核は Mathlib の標準 opcycles。使われ方：KST Lemma 4.10 の頁微分の自然性。 -/
def spectralOpcyclesMap (φ : X ⟶ Y) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.opcycles f g n ⟶ Y.opcycles f g n :=
  cokernel.desc _ ((φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n) (by
    rw [← Category.assoc, φ.comm (n - 1) n (by omega) f g, Category.assoc,
      Y.δ_pOpcycles f g (n - 1) n (by omega), comp_zero])

/-- 概要：余核上の誘導射は余核への射影と可換。
方針：余核の普遍性の標準等式を使う。
規約：左辺は元の射影に誘導射を合成する。使われ方：KST Lemma 4.10 の商比較。 -/
theorem spectralOpcyclesMap_pOpcycles (φ : X ⟶ Y)
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    X.pOpcycles f g n ≫ spectralOpcyclesMap φ f g n =
      (φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n := by
  exact cokernel.π_desc _ _ _

/-- 概要：スペクトル対象の核上の射と、頁を定義する短複体のサイクル射は標準同型で一致。
方針：短複体のサイクル包含で相殺し、二つの包含の自然性を使う。
規約：三つの連続次数を固定する。使われ方：KST Lemma 4.10 の πE の自然性。 -/
theorem spectralCyclesMap_cyclesIso_inv
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    spectralCyclesMap φ f₁ f₂ n₁ ≫ (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).inv =
      (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).inv ≫
        ShortComplex.cyclesMap ((spectralShortComplexFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ) := by
  apply (cancel_mono (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).iCycles).mp
  erw [Category.assoc, Y.cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂,
    spectralCyclesMap_iCycles, Category.assoc, ShortComplex.cyclesMap_i,
    ← Category.assoc, X.cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂]
  rfl

/-- 概要：スペクトル対象の射が誘導する頁の射は、cycles からの標準射 πE と可換。
方針：標準サイクル同型の比較と短複体のホモロジー全射の自然性を合成する。
規約：頁の射は spectralPageFunctor から得る。使われ方：KST Lemma 4.10 の微分自然性。 -/
theorem spectralPageMap_πE
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    spectralCyclesMap φ f₁ f₂ n₁ ≫ Y.πE f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ =
      X.πE f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ ≫
        (spectralPageFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ := by
  change spectralCyclesMap φ f₁ f₂ n₁ ≫
      ((Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).inv ≫ _) =
    ((X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).inv ≫ _) ≫ _
  erw [← Category.assoc, spectralCyclesMap_cyclesIso_inv, Category.assoc,
    ← ShortComplex.homologyπ_naturality, ← Category.assoc]
  rfl

/-- 概要：短複体の opcycles 上の射とスペクトル対象の余核上の射は標準同型で一致。
方針：短複体の余核射影で相殺し、二つの射影の自然性を使う。
規約：三つの連続次数を固定する。使われ方：KST Lemma 4.10 の ιE の自然性。 -/
theorem spectralOpcyclesMap_opcyclesIso_hom
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom ≫ spectralOpcyclesMap φ f₂ f₃ n₁ =
      ShortComplex.opcyclesMap ((spectralShortComplexFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ) ≫
        (Y.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).hom := by
  apply (cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).pOpcycles).mp
  erw [← Category.assoc, X.p_opcyclesIso_hom f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂,
    spectralOpcyclesMap_pOpcycles, ← Category.assoc, ShortComplex.p_opcyclesMap,
    Category.assoc, Y.p_opcyclesIso_hom f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂]
  rfl

/-- 概要：スペクトル対象の射が誘導する頁の射は、opcycles への標準射 ιE と可換。
方針：短複体のホモロジー単射の自然性と標準余核同型の比較を合成する。
規約：頁の射は spectralPageFunctor から得る。使われ方：KST Lemma 4.10 の微分自然性。 -/
theorem spectralPageMap_ιE
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ n₂ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) :
    (spectralPageFunctor f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).map φ ≫
      Y.ιE f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂ ≫ spectralOpcyclesMap φ f₂ f₃ n₁ := by
  change ShortComplex.homologyMap _ ≫
      ((Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).homologyι ≫ _) =
    ((X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ h₁ h₂).homologyι ≫ _) ≫ _
  erw [← Category.assoc, ShortComplex.homologyι_naturality, Category.assoc,
    ← spectralOpcyclesMap_opcyclesIso_hom, ← Category.assoc]

/-- 概要：スペクトル対象の射は合成区間から cycles への標準全射と可換。
方針：cycles の包含で相殺し、区間ホモロジーの自然変換の自然性を使う。
規約：合成区間は f≫g と固定する。使われ方：KST Lemma 4.10 の Ψ の自然性。 -/
theorem spectralCyclesMap_toCycles
    (φ : X ⟶ Y) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ) :
    (φ.hom n).app (mk₁ (f ≫ g)) ≫ Y.toCycles f g (f ≫ g) rfl n =
      X.toCycles f g (f ≫ g) rfl n ≫ spectralCyclesMap φ f g n := by
  apply (cancel_mono (Y.iCycles f g n)).mp
  erw [Category.assoc, Y.toCycles_i f g (f ≫ g) rfl n,
    Category.assoc, spectralCyclesMap_iCycles, ← Category.assoc,
    X.toCycles_i f g (f ≫ g) rfl n]
  exact ((φ.hom n).naturality (twoδ₁Toδ₀ f g (f ≫ g) rfl)).symm

/-- 概要：頁の微分を核・余核で表す標準射 Ψ はスペクトル対象の射に自然。
方針：合成区間から cycles への全射で相殺し、δ と余核射影の自然性を使う。
規約：三つの合成可能な射と隣接二次数。使われ方：KST Lemma 4.10 の頁微分の自然性。 -/
theorem spectralΨMap_naturality
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    spectralCyclesMap φ f₂ f₃ n₀ ≫ Y.Ψ f₁ f₂ f₃ n₀ n₁ h =
      X.Ψ f₁ f₂ f₃ n₀ n₁ h ≫ spectralOpcyclesMap φ f₁ f₂ n₁ := by
  apply (cancel_epi (X.toCycles f₂ f₃ (f₂ ≫ f₃) rfl n₀)).mp
  calc
    _ = (φ.hom n₀).app (mk₁ (f₂ ≫ f₃)) ≫
        Y.toCycles f₂ f₃ (f₂ ≫ f₃) rfl n₀ ≫ Y.Ψ f₁ f₂ f₃ n₀ n₁ h := by
      erw [← Category.assoc, ← spectralCyclesMap_toCycles, Category.assoc]
    _ = (φ.hom n₀).app (mk₁ (f₂ ≫ f₃)) ≫
        Y.δ f₁ (f₂ ≫ f₃) n₀ n₁ h ≫ Y.pOpcycles f₁ f₂ n₁ := by
      rw [Y.toCycles_Ψ f₁ f₂ f₃ (f₂ ≫ f₃) rfl n₀ n₁ h]
    _ = X.δ f₁ (f₂ ≫ f₃) n₀ n₁ h ≫
        (φ.hom n₁).app (mk₁ f₁) ≫ Y.pOpcycles f₁ f₂ n₁ := by
      rw [← Category.assoc, ← φ.comm n₀ n₁ h f₁ (f₂ ≫ f₃), Category.assoc]
    _ = X.δ f₁ (f₂ ≫ f₃) n₀ n₁ h ≫
        X.pOpcycles f₁ f₂ n₁ ≫ spectralOpcyclesMap φ f₁ f₂ n₁ := by
      rw [← spectralOpcyclesMap_pOpcycles]
    _ = _ := by
      rw [← Category.assoc, ← X.toCycles_Ψ f₁ f₂ f₃ (f₂ ≫ f₃) rfl n₀ n₁ h,
        Category.assoc]

/-- 概要：スペクトル対象の射から得る頁の射は、実際の頁微分と可換。
方針：源の標準全射 πE と標的の標準単射 ιE で相殺し、微分の Ψ 表示の自然性へ帰着する。
規約：五つの合成可能区間と四つの連続次数。使われ方：KST Lemma 4.10 の頁複体の塔。 -/
theorem spectralPageMap_d
    (φ : X ⟶ Y) {i₀ i₁ i₂ i₃ i₄ i₅ : I}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ) (h₁ : n₀ + 1 = n₁) (h₂ : n₁ + 1 = n₂) (h₃ : n₂ + 1 = n₃) :
    (spectralPageFunctor f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂).map φ ≫
      Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃ =
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃ ≫
        (spectralPageFunctor f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃).map φ := by
  let πX := X.πE f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂
  let πY := Y.πE f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂
  let ιX := X.ιE f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃
  let ιY := Y.ιE f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃
  let mS := (spectralPageFunctor f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂).map φ
  let mT := (spectralPageFunctor f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃).map φ
  let dX := X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃
  let dY := Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃
  let cφ := spectralCyclesMap φ f₃ f₄ n₁
  let oφ := spectralOpcyclesMap φ f₂ f₃ n₂
  let ΨX := X.Ψ f₂ f₃ f₄ n₁ n₂ h₂
  let ΨY := Y.Ψ f₂ f₃ f₄ n₁ n₂ h₂
  have hπ : cφ ≫ πY = πX ≫ mS := spectralPageMap_πE φ f₃ f₄ f₅ n₀ n₁ n₂ h₁ h₂
  have hι : mT ≫ ιY = ιX ≫ oφ := spectralPageMap_ιE φ f₁ f₂ f₃ n₁ n₂ n₃ h₂ h₃
  have hX : πX ≫ dX ≫ ιX = ΨX := X.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃
  have hY : πY ≫ dY ≫ ιY = ΨY := Y.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ h₁ h₂ h₃
  apply (cancel_epi πX).mp
  apply (cancel_mono ιY).mp
  change (πX ≫ (mS ≫ dY)) ≫ ιY = (πX ≫ (dX ≫ mT)) ≫ ιY
  calc
    _ = (πX ≫ mS) ≫ (dY ≫ ιY) := by simp only [Category.assoc]
    _ = (cφ ≫ πY) ≫ (dY ≫ ιY) := congrArg (fun f ↦ f ≫ (dY ≫ ιY)) hπ.symm
    _ = cφ ≫ (πY ≫ dY ≫ ιY) := by simp only [Category.assoc]
    _ = cφ ≫ ΨY := congrArg (fun f ↦ cφ ≫ f) hY
    _ = ΨX ≫ oφ := spectralΨMap_naturality φ f₂ f₃ f₄ n₁ n₂ h₂
    _ = (πX ≫ dX ≫ ιX) ≫ oφ := congrArg (fun f ↦ f ≫ oφ) hX.symm
    _ = πX ≫ dX ≫ (ιX ≫ oφ) := by simp only [Category.assoc]
    _ = πX ≫ dX ≫ (mT ≫ ιY) := congrArg (fun f ↦ πX ≫ dX ≫ f) hι.symm
    _ = _ := by simp only [Category.assoc]

end SerrePositivity.KST.ProExcision
