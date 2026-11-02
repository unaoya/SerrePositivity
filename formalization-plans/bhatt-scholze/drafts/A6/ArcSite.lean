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
証明は前段 G-A6-11（R₀ := ℤ_p[p^{1/p^∞}]^∧ 上へ移す被覆 S → S₀）の後に A5-4 の根添加（W9-II-16：A5-4 の semiperfectoid 性は perfectoid 基底を要し、
全 p 完備環に直接は当てられない。ℤ_p の反例は a6-design §2.1）。

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
      ∃ (e : V →+* W), e.FaithfullyFlat ∧ -- 原典 Def 8.7 の「忠実平坦な拡大」そのもの（W9-II-10：「平坦かつ単射」は弱すぎる。
        -- 標数 p の A = F_p[t^{1/p^∞}] で {A → A[1/t], A → F_p} が被覆になり O の Čech 降下が破綻する。付値環の局所単射で代える場合は同値を証明する）
        ∃ l : B i →+* W, l.comp (f i) = e.comp k

/-- 概要：arc 位相：有限 arc 被覆族の生成 sieve を含む Grothendieck 位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`Sieve.generate (Presieve.ofArrows …)`。
規約：affCompl_κ の opposite の上。
使われ方：以下。 -/
def arcTopology : GrothendieckTopology (AffCompl p κ)ᵒᵖ := sorry

/-- 概要：affPerfd_κ への誘導位相（`affPerfdInclusion.op` による引き戻し、Mathlib `Functor.inducedTopology`。包含は site の opposite の向きで渡す、W9-II-25）。
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

/-! ## Lemma 8.8 の affine 版：affPerfd_κ は cover-dense

W9-II-16：A5-4 の `rootClosure_isSemiperfectoid` は `hR : IsIntegralPerfectoid R p` と `Algebra R S` を仮定する（G-A5-14 は θ の核に R 由来の
distinguished 元を使う）。全 p 完備環 S にそのまま当てることはできない（S = ℤ_p：基底なしの根添加 C_∞ は ℤ_p へ retraction をもち、perfectoid 環から
ℤ_p への環準同型はないので semiperfectoid でない）。そこで前段 G-A6-11 を置く。 -/

/-- 概要：G-A6-11：perfectoid 基底 R₀ := ℤ_p[p^{1/p^∞}]^∧（Type u）。
方針：ℤ_p[X_n : n]/(X_0 − p, X_{n+1}^p − X_n) の p 進完備化。perfectoid 性は既存の例があれば使う（要確認）。
規約：固定。E3 の R とは無関係（全 p 完備環を対象とするため）。
使われ方：`baseExtension`。 -/
def perfectoidBaseRing : Type u := sorry
instance : CommRing (perfectoidBaseRing p) := sorry
theorem perfectoidBaseRing_isPerfectoid : IsIntegralPerfectoid (perfectoidBaseRing p) p := by sorry

/-- 概要：G-A6-11：前段 S₀ := completionRing(S ⊗_{ℤ_p} R₀)（p 完備な R₀ 代数）と単位 S → S₀。
方針：`completionRing`（H⁰(LΛ_p)、既存）と `Algebra.TensorProduct`。
規約：#S₀ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ（`baseExtension_cardinal_le`）。
使われ方：`exists_perfectoid_arcCover`。 -/
def baseExtension (S : Type u) [CommRing S] : Type u := sorry
instance (S : Type u) [CommRing S] : CommRing (baseExtension p S) := sorry
instance (S : Type u) [CommRing S] : Algebra (perfectoidBaseRing p) (baseExtension p S) := sorry
def baseExtensionUnit (S : Type u) [CommRing S] : S →+* baseExtension p S := sorry
theorem baseExtension_cardinal_le : True := by trivial

/-- 概要：記録：S → S₀ は p 完備忠実平坦（ℤ_p → R₀ が p 完備忠実平坦：R₀ は p ねじれなしで R₀/p ≠ 0）。原典 Lemma 8.8 の証明の
「semiperfectoid な p 完備忠実平坦被覆」は S → S̃₀（S₀ の R₀ 上の `rootClosure`）がそれにあたる。
方針：記録のみ。E3 には下の arc 被覆性だけ要る。
規約：—
使われ方：なし（原典との対応の記録）。 -/
theorem baseExtensionUnit_pCompletelyFaithfullyFlat : True := by trivial

/-- 概要：G-A6-3：p 完備な階数 1 の付値環 V は、perfectoid な p 完備階数 1 の付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。
W には p の両立する p 冪根の列がある（絶対整閉包から来る）ので、環準同型 R₀ → W が取れる。
方針：Mathlib の付値の整拡大への延長（要確認）、絶対整閉な p 完備付値環は perfectoid（p 乗根の存在で Frobenius 全射、ker θ は主イデアル）。
規約：—
使われ方：下（W を**先に**取る）、Prop 8.10 の §3.1 の 2。 -/
theorem exists_perfectoid_valuation_extension : True := by trivial
theorem perfectoidBaseRing_toValuationExtension : True := by trivial -- R₀ → W（p の p 冪根の選択）

/-- 概要：S → V（試験付値環）は S₀ → W に延びる：W を G-A6-3 で取り、R₀ → W と S → V → W から S ⊗_{ℤ_p} R₀ → W、W は p 完備なので S₀ → W。
方針：`completionRing` の普遍性（p 完備な標的）。
規約：—
使われ方：`exists_perfectoid_arcCover`。 -/
theorem exists_baseExtension_lift : True := by trivial

/-- 概要：Lemma 8.8（affine 版）：任意の p 完備環 S は perfectoid による arc 被覆 S → S₀ → S̃₀ → (S̃₀)_perfd をもつ
（S̃₀ は S₀ の R₀ 上の A5-4 `rootClosure`、(S̃₀)_perfd は A5-2 の普遍 perfectoid 環）。
方針（W9-II-16 で訂正）：S → V に対し**先に** perfectoid な W（`exists_perfectoid_valuation_extension`）を取り、`exists_baseExtension_lift` で S₀ → W、
`rootClosure_extends`（標的は perfectoid）で S̃₀ → W、S̃₀ は R₀ 上 semiperfectoid（`rootClosure_isSemiperfectoid`、基底 R₀ で仮定が満たされる）
なので普遍性で (S̃₀)_perfd → W。旧方針「S̃ → V に延びてから W に替える」は `rootClosure_extends` の標的の仮定と順序が合わなかった。
規約：濃度 ≤ κ（S₀・S̃₀・(S̃₀)_perfd とも (#S + ℵ₀)^{ℵ₀} 以下）。未証明の E3・A7 の普遍性は使わない。
使われ方：cover-dense。 -/
theorem exists_perfectoid_arcCover : True := by trivial

/-- 概要：affPerfd_κ ⥤ affCompl_κ は arc 位相について cover-dense（Mathlib `Functor.IsCoverDense`）。
方針：`exists_perfectoid_arcCover`（前段 G-A6-11 つき。global な affCompl_κ を維持する、W9-II-16）。
規約：Mathlib の 1 圏の道具。これで集合の層の圏同値 `Functor.sheafInducedTopologyEquivOfIsCoverDense`（= `IsDenseSubsite.sheafEquiv`、G-A6-8。W9-II-25 で名前を訂正）が使える。
使われ方：A6-3。 -/
theorem affPerfdInclusion_isCoverDense : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
