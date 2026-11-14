-- 1 圏の arc site と Lemma 8.8 の affine 版は本体の ArcSite に移した。
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.1・§10、単位 A6-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Site.ArcSite
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationExtension
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
-- W9-III-08（致命・配置）：現行の CompletedTensor は IntegralExistence 経由で消去対象の Inputs/PerfectoidizationInterface を import する。2a の取り込み後に
-- Fontaine による完備テンソルの芯を E3 非依存のモジュール（仮称 CompletedTensorCore）へ切り出し、本ファイルはそれだけを import する（a9-design §7、調整役へ依頼）。
-- perfectoid 環の有限積が perfectoid であることは E3 を使う `isIntegralPerfectoid_finPi` ではなく直接証明（G-A6-12）。
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.MvPolynomial.Basic
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits
-- 相対 Čech の部分は drafts/Sheaves/{SheafCondition,CechConerveLimit}.lean の S1・S3 を import する。
-- 本ファイルは drafts/A5/RootAdjunction.lean（`rootClosure`・`rootClosure_extends`）、drafts/A5/WeaklyInitialAndDescent.lean（`rootClosure_isSemiperfectoid`）、drafts/A5/SemiperfectoidCase.lean（`universalPerfectoidRing`）、
-- drafts/A0/PrismaticSite.lean（`cutoff`）を import する（W9-III-14 で所在を RootAdjunction に揃えた）。

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
open scoped TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.DerivedCompletion

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

section ArcCech

open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.Sheaves
open SSet

/-- 小さい模型の射 f が一点族として arc 被覆である条件。 -/
def IsSingletonArcCover {R S : AffCompl p κ} (f : R ⟶ S) : Prop :=
  IsArcCoverFamily p (fun _ : PUnit.{u + 1} => (affComplForget p κ).obj S)
    (fun _ => ((affComplForget p κ).map f).hom)

/-- op R における f.op 一射の presieve。 -/
def arcSinglePresieve {R S : AffCompl p κ} (f : R ⟶ S) : Presieve (Opposite.op R) :=
  Presieve.ofArrows (fun _ : Unit => Opposite.op S) (fun _ => f.op)

/-- 一射が生成する sieve Q。 -/
abbrev arcSingleSieve {R S : AffCompl p κ} (f : R ⟶ S) : Sieve (Opposite.op R) :=
  Sieve.generate (arcSinglePresieve p κ f)

/-- 𝒟 = sieveCategory Q の対象 U は生成射 f.op 自身。 -/
def arcSieveGenerator {R S : AffCompl p κ} (f : R ⟶ S) : sieveCategory (arcSingleSieve p κ f) :=
  ⟨Over.mk f.op, Sieve.le_generate (arcSinglePresieve p κ f) _ _ (Presieve.ofArrows.mk ())⟩

theorem arcSieveGenerator_weaklyTerminal {R S : AffCompl p κ} (f : R ⟶ S) :
    Sheaves.IsWeaklyTerminal (arcSieveGenerator p κ f) := by
  sorry -- Q の各射の f.op による因子分解が、𝒟 の U への射を与える

-- §2.1 の cutoff。有限の相対テンソルと可算完備化の台を模型内に収める。
variable [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]

/-- 𝒟 での U の有限冪を相対完備テンソル冪で実現する Čech データ。
各次数の射影、Fan の IsLimit、射影と単体的構造射の整合を含む。 -/
def arcSieveCechData {R S : AffCompl p κ} (f : R ⟶ S) :
    Sheaves.CechNerveData (arcSieveGenerator p κ f) := by
  have hbound := hκ.out
  sorry -- R 上の (n+1) 重テンソルの completionRing とその射影は Q の対象で、完備化の普遍性から積を与える

/-- 概要：(1) 個々の単射 arc 被覆 f : R → S について、その生成 sieve Q := `Sieve.generate (Presieve.ofArrows (fun _ : Unit => op S) (fun _ => f.op))` の層条件
（S1 の `restrictionCone F Q` が極限錐）は、**相対** Čech 余脈体 S^{⊗̂_R (•+1)} の Tot の条件と同値。
方針（BS-D1 の D1-01 で確定、11-03）：S3 の `CechNerveData` は全 site ではなく **sieve の圏 𝒟 := sieveCategory Q** の中で取る。U := f.op は 𝒟 で弱終
（Q の射は f.op を経由する）、𝒟 の U の (n+1) 乗は op R 上のファイバー積＝完備テンソル冪 op(completionRing (S ⊗_R ⋯ ⊗_R S))（κ-small で Q に属する）。
全 site の絶対積 S ⊗̂_{ℤ_p} S ではない（R = S = F_p[t] の恒等被覆で両者は異なる）。S1 の `restriction F Q` は 𝒟 上の前層なので、S3 の
`isLimitCone_iff_restrict_cech` をそのまま当てる。A5 の完全 site（Perfd_{S/}、最初から相対）とはここが違う。
規約：F は (AffCompl p κ)ᵒᵖ 上の任意の E 値前層。
使われ方：(2)、Prop 8.10 の帰着。 -/
theorem isSheaf_generateSieve_iff_cech {R S : AffCompl p κ} (f : R ⟶ S)
    (hf : IsSingletonArcCover p κ f) {E : SSet.{u + 1}} [Quasicategory E]
    (F : Presheaf (AffCompl p κ)ᵒᵖ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (restrictionCone F (arcSingleSieve p κ f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (restrictionCone F (arcSingleSieve p κ f))
        (cechShape (arcSieveCechData p κ f))) := by
  sorry -- restriction F Q とその錐に、U の弱終性と相対 Čech データで S3 の isLimitCone_iff_restrict_cech を適用

/-- 概要：一点 arc 被覆の coverage K₁（D1-01 の (2) の入力。**D1-02：K₁ が生成する位相は `arcTopology` より粗い**——k × k → k の二つの射影の族は有限 arc 被覆だが、
その生成 sieve は一点 arc 被覆を一つも含まない。よって `arcTopology = K₁.toGrothendieck` は偽で、(2) は下の形に直す）。
方針：被覆 presieve は一点 arc 被覆 f の `arcSinglePresieve`。pullback は `isArcCoverFamily_baseChange` の一点族。
規約：—
使われ方：`arcTopology_eq_sup`、`isSheaf_arc_iff_cech`。 -/
def arcCoverage : Coverage (AffCompl p κ)ᵒᵖ where
  coverings X := { T | ∃ (S : AffCompl p κ) (f : X.unop ⟶ S),
    IsSingletonArcCover p κ f ∧ T = arcSinglePresieve p κ f }
  pullback := by
    have hbound := hκ.out
    sorry -- isArcCoverFamily_baseChange の一点族を模型へ移し、相対完備テンソルの二つの脚で FactorsThruAlong を与える

/-- 概要：有限族の coverage K_fam（`arcTopology` の定義そのもの）。
方針：被覆 presieve は有限 arc 被覆族 {R → B_i} の `Presieve.ofArrows`。pullback は `isArcCoverFamily_baseChange`。
規約：空族を含む（零環の上の空族は arc 被覆：零環から非零の付値環への環準同型はない）。
使われ方：`arcTopology_eq_toGrothendieck_family`。 -/
def arcFamilyCoverage : Coverage (AffCompl p κ)ᵒᵖ where
  coverings X := { T | ∃ (ι : Type u) (hι : Finite ι) (B : ι → AffCompl p κ)
    (f : ∀ i, X.unop ⟶ B i),
    letI : Finite ι := hι
    IsArcCoverFamily p (fun i => (affComplForget p κ).obj (B i))
      (fun i => ((affComplForget p κ).map (f i)).hom) ∧
    T = Presieve.ofArrows (fun i => Opposite.op (B i)) (fun i => (f i).op) }
  pullback := by
    have hbound := hκ.out
    sorry -- 各 f_i を相対完備テンソルで底変換し、isArcCoverFamily_baseChange と二脚から FactorsThruAlong を得る

/-- 概要：`arcTopology = K_fam.toGrothendieck`（sInf の定義と `Coverage.toGrothendieck` の定義から。D1-02 の訂正：一点族 K₁ ではなく有限族 K_fam）。 -/
theorem arcTopology_eq_toGrothendieck_family : arcTopology p κ = (arcFamilyCoverage p κ).toGrothendieck := by
  sorry -- 両辺とも「全ての有限 arc 被覆族の生成 sieve を含む最小の位相」

/-- 概要：extensive coverage K_ext：有限積 ∏_j R_j の射影の族 {∏_j R_j → R_i}_i（空積＝零環の空族を含む）。
方針：`Presieve.ofArrows` の射影。pullback は底変換で有限積が有限積に写ること（完備テンソルは有限積と可換）。
規約：Mathlib の `FinitaryPreExtensive`・`Presieve.Extensive`（Sites/Coherent/ExtensiveSheaves）の形に合わせる。
使われ方：`arcTopology_eq_sup`。 -/
def extensiveCoverage : Coverage (AffCompl p κ)ᵒᵖ where
  coverings X := { T | ∃ (ι : Type u) (_ : Finite ι) (B : ι → AffCompl p κ)
    (π : ∀ i, X.unop ⟶ B i), Nonempty (Limits.IsLimit (Limits.Fan.mk X.unop π)) ∧
    T = Presieve.ofArrows (fun i => Opposite.op (B i)) (fun i => (π i).op) }
  pullback := by
    have hbound := hκ.out
    sorry -- 底変換した環は像の直交冪等元で再び有限積に分かれ、各因子は完備環の直和因子

/-- 概要：有限積の射影の族は arc 被覆族（付値環は非零整域なので ∏R_j → V は一つの射影を通る。空積：零環から V への射はない）。
方針：冪等元の像は 0 か 1。
規約：—
使われ方：K_ext ≤ arcTopology。 -/
theorem isArcCoverFamily_projections {ι : Type u} [Finite ι]
    (R : ι → Type u) [∀ i, CommRing (R i)] :
    IsArcCoverFamily p R (fun i => Pi.evalRingHom R i) := by
  sorry -- 付値環への射は一因子で持ち上がる。空積から非零付値環への射は存在しない

/-- 概要：`arcTopology = K₁.toGrothendieck ⊔ K_ext.toGrothendieck`（D1-02 の修復）。
方針：≤：有限族 {R → R_i} は一点被覆 R → ∏R_i（`isArcCoverFamily_prod_iff`）と射影の族 {∏R_i → R_j}（K_ext）の合成なので、右辺で被覆。
≥：一点 arc 被覆は一点族として arc 被覆、射影の族は `isArcCoverFamily_projections` で arc 被覆。
規約：Mathlib の `GrothendieckTopology` の完備束の ⊔。
使われ方：`isSheaf_arc_iff_cech`。 -/
theorem arcTopology_eq_sup :
    arcTopology p κ = (arcCoverage p κ).toGrothendieck ⊔ (extensiveCoverage p κ).toGrothendieck := by
  sorry -- 有限族を積への一点被覆と射影族に分解し、逆向きには両生成系の arc 被覆性を使う

/-- 概要：F が有限積を保つ：AffCompl の有限積 ∏_i R_i（環の有限積、空積は零環）について F(∏ R_i) → ∏ F(R_i) が同値（空積なら F(0) が終対象）。
方針：E の積の錐が極限錐であること（`IsLimitCone`）で述べる。
規約：O（CAlg_ℤ 値：環の積は CAlg の積）と Hom(T, −)（集合値）はこれを満たす（ArcSheafProperty で主張）。
使われ方：`isSheaf_arc_iff_cech`。 -/
def PreservesFiniteRingProducts {E : SSet.{u + 1}} [Quasicategory E]
    (F : Presheaf (AffCompl p κ)ᵒᵖ E) : Prop :=
  ∀ (ι : Type u) [Finite ι] (B : ι → AffCompl p κ) (c : Limits.Fan B),
    Nonempty (Limits.IsLimit c) → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone
      ((SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone ((opOp (AffCompl p κ)).mapCone c))).postcomp F)

/-- 概要：S1 の一般補題（**基盤待ち**、S1-E）：extensive coverage の層 ⇔ 有限積を保つ（Mathlib `isSheaf_iff_preservesFiniteProducts` の ∞ 版、
`FinitaryPreExtensive` な site で）。
方針：HTT 6.2.2 の系（有限余積の Čech 脈体は定数、交叉は始対象）。置き場所は drafts/Sheaves/SheafCondition（S1）。
規約：—
使われ方：`isSheaf_arc_iff_cech`。 -/
theorem isSheaf_extensive_iff_preservesFiniteProducts {E : SSet.{u + 1}} [Quasicategory E] (F : Presheaf (AffCompl p κ)ᵒᵖ E) :
    IsSheaf (extensiveCoverage p κ).toGrothendieck F ↔ PreservesFiniteRingProducts p κ F := by
  sorry -- S1 の補題（基盤待ち）

/-- 概要：(2)（D1-02 で訂正）：F が arc 層 ⇔ F は有限積を保ち、かつ任意の一点 arc 被覆 f について (1) の相対 Čech 条件。
方針：`arcTopology_eq_sup` で位相を分け、⊔ の層 ⇔ 両方の層（被覆篩の和集合が生成）；K_ext 側は `isSheaf_extensive_iff_preservesFiniteProducts`、
K₁ 側は S1 の `isSheaf_toGrothendieck_iff` と (1)。**一点被覆だけでは足りない**（二点集合に値を取る定数前層が反例：全ての一点 Čech 条件を満たすが
零環の空族の条件 F(0) ≃ * を満たさない）。
規約：任意の E 値前層について述べる。O と Hom(T, −) は有限積を保つので、それらについては一点被覆の Čech 条件だけでよい（Prop 8.10 の帰着はこの形）。
使われ方：Prop 8.10（O、CAlg_ℤ 値）、Hom(T, −) の層性（集合値）。 -/
theorem isSheaf_arc_iff_cech {E : SSet.{u + 1}} [Quasicategory E] (F : Presheaf (AffCompl p κ)ᵒᵖ E) :
    IsSheaf (arcTopology p κ) F ↔
      PreservesFiniteRingProducts p κ F ∧
        ∀ {R S : AffCompl p κ} (f : R ⟶ S), IsSingletonArcCover p κ f →
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (restrictionCone F (arcSingleSieve p κ f))
            (cechShape (arcSieveCechData p κ f))) := by
  sorry -- arcTopology_eq_sup、⊔ の層条件、isSheaf_extensive_iff_preservesFiniteProducts、isSheaf_toGrothendieck_iff、isSheaf_generateSieve_iff_cech

end ArcCech

/-! ## Lemma 8.8 の affine 版：affPerfd_κ は cover-dense

W9-II-16：A5-4 の `rootClosure_isSemiperfectoid` は `hR : IsIntegralPerfectoid R p` と `Algebra R S` を仮定する（G-A5-14 は θ の核に R 由来の
distinguished 元を使う）。全 p 完備環 S にそのまま当てることはできない（S = ℤ_p：基底なしの根添加 C_∞ は ℤ_p へ retraction をもち、perfectoid 環から
ℤ_p への環準同型はないので semiperfectoid でない）。そこで前段 G-A6-11 を置く。 -/

/-- 概要：記録：S → S₀ は p 完備忠実平坦（ℤ_p → R₀ が p 完備忠実平坦：R₀ は p ねじれなしで R₀/p ≠ 0）。原典 Lemma 8.8 の証明の
「semiperfectoid な p 完備忠実平坦被覆」は S → S̃₀（S₀ の R₀ 上の `rootClosure`）がそれにあたる。
方針：記録のみ。E3 には下の arc 被覆性だけ要る。
規約：—
使われ方：なし（原典との対応の記録）。 -/
theorem baseExtensionUnit_pCompletelyFaithfullyFlat (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    letI := (baseExtensionUnit p S hS).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) (baseExtension p S hS) := by
  sorry -- ℤ_p → R₀ の p 完全忠実平坦性を S へ完備底変換し、上の単位射による S 加群として読む

end SerrePositivity.BhattScholze.Perfectoidization.Derived
