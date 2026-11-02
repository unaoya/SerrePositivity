-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite（仮。原典 Def 8.7 の affine 版、Lemma 8.8 の affine 版）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.1・§10、単位 A6-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
-- 本ファイルは drafts/A5/WeaklyInitialAndDescent.lean（`rootClosure`）、drafts/A5/SemiperfectoidCase.lean（`universalPerfectoidRing`）、drafts/A0/PrismaticSite.lean（`cutoff`）を import する。

/-!
# arc site（BS 著者版 Def 8.7 の affine 版、Lemma 8.8 の affine 版）

## 概要
κ-small の p 完備環の圏 affCompl_κ（affine の p 進形式スキーム）の opposite に、[BM18, Def 1.2]・原典 Def 8.7 の有限族の形で arc 被覆を定め、
生成される Grothendieck 位相を arc 位相とする。perfectoid 環の充満部分圏 affPerfd_κ に誘導位相を入れ（原典の Perfd ⊂ fSch の affine 版）、
Lemma 8.8 の affine 版「任意の p 完備環は perfectoid による arc 被覆をもつ」を affPerfd_κ が cover-dense であることとして述べる。

## 方針
被覆の条件：有限族 {R → R_i} が arc 被覆 ⇔ 任意の p 完備な階数 1 の付値環 V（Type u）と R → V に対し、或る i と忠実平坦な拡大 V ⊂ W
（同じ種類の付値環）と R_i → W があって R → R_i → W = R → V → W。界面の `ArcOutside` と同じ V の条件（`ValuationRing`・`ringKrullDim = 1`・
p 進完備）。位相は A0 の `flatTopology` と同じ sInf の形（D22）。coverage（底変換で安定）は完備テンソルが p 完備環（perfectoid なら perfectoid）であること。

## 規約
κ は使う環の濃度を超えるように取る（κ^{ℵ₀} = κ、A5 の D47）。V・W は site の対象ではなく Type u の試験対象。非 affine は定義しない（D53）。

## 使われ方
A6-2（Prop 8.10）、A6-3（集合の層の等式）、A6-4（Cor 8.12）、A8（Thm 10.11）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.DerivedCompletion

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

/-! ## 台の圏 -/

/-- 概要：p 完備な階数 1 の付値環（試験対象）：整域・付値環・Krull 次元 1・p 進完備。
方針：界面の `ArcOutside` と同じ条件を構造にまとめる。
規約：Type u。
使われ方：arc 被覆の定義。 -/
structure IsRankOneCompleteValuationRing (V : Type u) [CommRing V] : Prop where
  isDomain : IsDomain V
  valuationRing : ValuationRing V
  krullDim_eq_one : ringKrullDim V = 1
  adicComplete : IsAdicComplete (Ideal.span {(p : V)}) V

/-- 概要：κ-small の p 完備環の圏（affine の p 進形式スキーム）。
方針：`CommRingCat.{u}` の充満部分圏（導来 p 完備、濃度 ≤ κ）の `SmallModel`（要確認：A0 の `PrismOverSmall` と同じ道具）。
規約：対象の濃度 ≤ κ。
使われ方：arc site の台。 -/
def AffCompl : Type u := sorry

instance : Category.{u} (AffCompl p κ) := sorry

/-- 概要：κ-small の perfectoid 環の充満部分圏 affPerfd_κ ⊂ affCompl_κ。
方針：`IsIntegralPerfectoid` の `ObjectProperty.FullSubcategory`。
規約：—
使われ方：Prop 8.10、F_T。 -/
def AffPerfd : Type u := sorry

instance : Category.{u} (AffPerfd p κ) := sorry

/-- 概要：包含関手 affPerfd_κ ⥤ affCompl_κ（充満忠実）。 -/
def affPerfdInclusion : AffPerfd p κ ⥤ AffCompl p κ := sorry

/-! ## arc 被覆と arc 位相 -/

/-- 概要：有限族 {R → R_i} が arc 被覆（[BM18, Def 1.2]、Def 8.7 の affine 版）。
方針：∀ V（`IsRankOneCompleteValuationRing`）、∀ R → V、∃ i W（同じ種類）、V → W 忠実平坦、∃ R_i → W、両立。
規約：族の添字は `Finite`。単射の場合は族 = 一点。
使われ方：`arcTopology`、Prop 8.10、Cor 8.12 の二つの被覆。 -/
def IsArcCoverFamily {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, R →+* B i) : Prop :=
  ∀ (V : Type u) [CommRing V], IsRankOneCompleteValuationRing p V → ∀ k : R →+* V,
    ∃ (i : ι) (W : Type u) (_ : CommRing W), IsRankOneCompleteValuationRing p W ∧
      ∃ (e : V →+* W), e.Flat ∧ Function.Injective e ∧ -- 要確認：忠実平坦の述べ方（局所単射なら忠実平坦）
        ∃ l : B i →+* W, l.comp (f i) = e.comp k

/-- 概要：arc 位相：有限 arc 被覆族の生成 sieve を含む Grothendieck 位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`Sieve.generate (Presieve.ofArrows …)`。
規約：affCompl_κ の opposite の上。
使われ方：以下。 -/
def arcTopology : GrothendieckTopology (AffCompl p κ)ᵒᵖ := sorry

/-- 概要：affPerfd_κ への誘導位相（`affPerfdInclusion` による引き戻し、Mathlib `GrothendieckTopology` の `inducedTopology`）。
方針：Mathlib の dense subsite の道具。
規約：原典 "Perfd ⊂ fSch with the induced topology" の affine 版。
使われ方：Prop 8.10、Cor 8.12。 -/
def arcTopologyPerfd : GrothendieckTopology (AffPerfd p κ)ᵒᵖ := sorry

/-! ## coverage -/

/-- 概要：arc 被覆族は底変換で安定：R → R′ と {R → R_i} に対し {R′ → R_i ⊗̂_R R′}（p 完備テンソル）も arc 被覆族。
方針：R′ → V は R → V を与え、持ち上げ R_i → W と R′ → V → W から R_i ⊗̂_R R′ → W（W は p 完備）。
規約：完備テンソルは `CompletedTensor`（perfectoid なら perfectoid）。
使われ方：生成系の補題（S1 `isSheaf_toGrothendieck_iff`）を使うための coverage 条件。 -/
theorem isArcCoverFamily_baseChange : True := by trivial

/-- 概要：合成・有限族の合併・有限積への置き換え（{R → R_i} と R → ∏R_i は同じ位相を生成）。 -/
theorem isArcCoverFamily_comp : True := by trivial
theorem isArcCoverFamily_prod_iff : True := by trivial

/-- 概要：単射 arc 被覆 R → S の生成 sieve の層条件は、完備テンソル冪の Čech 余脈体の Tot の条件（S3 `CechNerveData`：affCompl_κ の余積は完備テンソル）。
方針：S1 の生成系の補題と S3。
規約：—
使われ方：Prop 8.10 の帰着。 -/
theorem isSheaf_arc_iff_cech : True := by trivial

/-! ## Lemma 8.8 の affine 版：affPerfd_κ は cover-dense -/

/-- 概要：任意の p 完備環 S は perfectoid による arc 被覆 S → S̃_perfd をもつ（S̃ は A5-4 の `rootClosure`、S̃_perfd は A5-2 の普遍 perfectoid 環）。
方針：S → V は S̃ → V に延び（`rootClosure_extends`）、V を perfectoid な p 完備階数 1 付値環 W に忠実平坦に埋めて（G-A6-3
`exists_perfectoid_valuation_extension`）S̃ → W、普遍性で S̃_perfd → W。
規約：濃度 ≤ κ。
使われ方：cover-dense。 -/
theorem exists_perfectoid_arcCover : True := by trivial

/-- 概要：G-A6-3：p 完備な階数 1 の付値環 V は、perfectoid な p 完備階数 1 の付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。
方針：Mathlib の付値の整拡大への延長（要確認）、絶対整閉な p 完備付値環は perfectoid（p 乗根の存在で Frobenius 全射、ker θ は主イデアル）。
規約：—
使われ方：上、Prop 8.10 の §3.1 の 2。 -/
theorem exists_perfectoid_valuation_extension : True := by trivial

/-- 概要：affPerfd_κ ⥤ affCompl_κ は arc 位相について cover-dense（Mathlib `Functor.IsCoverDense`）。
方針：`exists_perfectoid_arcCover`。
規約：Mathlib の 1 圏の道具。これで集合の層の圏同値 `IsCoverDense.sheafEquiv`（G-A6-8）が使える。
使われ方：A6-3。 -/
theorem affPerfdInclusion_isCoverDense : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
