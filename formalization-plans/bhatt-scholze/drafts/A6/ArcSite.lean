-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite（仮。原典 Def 8.7 の affine 版、Lemma 8.8 の affine 版）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.1・§10、単位 A6-1。基準コミット 972bb7f53。ビルドしない。
module

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
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
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

/-! ## 台の圏 -/

/-- 概要：p 完備な階数 1 の付値環（試験対象）：整域・付値環・Krull 次元 1・p 進完備。
方針：界面の `ArcOutside` と同じ条件を構造にまとめる。
規約：Type u。
使われ方：arc 被覆の定義。 -/
structure IsRankOneCompleteValuationRing (V : Type u) [CommRing V] : Prop where
  isDomain : IsDomain V
  valuationRing : @ValuationRing V _ isDomain
  krullDim_eq_one : ringKrullDim V = 1
  adicComplete : IsAdicComplete (Ideal.span {(p : V)}) V

/-- 導来 p 完備性と濃度を併記する、環の圏上の対象条件。 -/
def affComplProperty : ObjectProperty CommRingCat.{u} := fun S =>
  IsModuleComplete S (p : S) (ModuleCat.of S S) ∧ Cardinal.mk S ≤ κ

/-- 小さい模型を取る前の充満部分圏。 -/
abbrev AffComplLarge := (affComplProperty p κ).FullSubcategory

instance affComplLarge_essentiallySmall : EssentiallySmall.{u} (AffComplLarge p κ) := by
  sorry -- 濃度 κ の固定した台の部分集合に環構造を移し、小さい同値な圏を作る

/-- 概要：κ-small の p 完備環の圏（affine の p 進形式スキーム）。
方針：`CommRingCat.{u}` の充満部分圏（導来 p 完備、濃度 ≤ κ）の `SmallModel`（A0 の `PrismOverSmall` と同じ道具。`EssentiallySmall.{u}` を上で供給）。
規約：対象の濃度 ≤ κ。
使われ方：arc site の台。 -/
abbrev AffCompl : Type u := SmallModel (AffComplLarge p κ)

instance : Category.{u} (AffCompl p κ) := inferInstance

/-- 小さい模型から元の環への忘却。射の環準同型もこの関手で取り出す。 -/
def affComplForget : AffCompl p κ ⥤ CommRingCat.{u} :=
  (equivSmallModel (AffComplLarge p κ)).inverse ⋙ (affComplProperty p κ).ι

/-- 小さい p 完備環の圏内での perfectoid 条件。 -/
def affPerfdProperty : ObjectProperty (AffCompl p κ) := fun S =>
  IsIntegralPerfectoid ((affComplForget p κ).obj S) p

/-- 概要：κ-small の perfectoid 環の充満部分圏 affPerfd_κ ⊂ affCompl_κ。
方針：`IsIntegralPerfectoid` の `ObjectProperty.FullSubcategory`。
規約：—
使われ方：Prop 8.10、F_T。 -/
abbrev AffPerfd : Type u := (affPerfdProperty p κ).FullSubcategory

instance : Category.{u} (AffPerfd p κ) := inferInstance

/-- 概要：包含関手 affPerfd_κ ⥤ affCompl_κ（充満忠実）。 -/
def affPerfdInclusion : AffPerfd p κ ⥤ AffCompl p κ :=
  (affPerfdProperty p κ).ι

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
def arcTopology : GrothendieckTopology (AffCompl p κ)ᵒᵖ :=
  sInf { J | ∀ (ι : Type u) [Finite ι] (R : AffCompl p κ)
    (B : ι → AffCompl p κ) (f : ∀ i, R ⟶ B i),
    IsArcCoverFamily p (fun i => (affComplForget p κ).obj (B i))
      (fun i => ((affComplForget p κ).map (f i)).hom) →
    Sieve.generate (Presieve.ofArrows (fun i => Opposite.op (B i))
      (fun i => (f i).op)) ∈ J (Opposite.op R) }

/-- 概要：affPerfd_κ への誘導位相（`affPerfdInclusion.op` による引き戻し、Mathlib `Functor.inducedTopology`。包含は site の opposite の向きで渡す、W9-II-25）。
定義の本体は `(affPerfdInclusion p κ).op.inducedTopology (arcTopology p κ)`。
Mathlib `Sites/InducedTopology.lean` の定義には cover-dense の仮定は不要（比較定理の仮定とは区別）。
方針：Mathlib の dense subsite の道具。
規約：原典 "Perfd ⊂ fSch with the induced topology" の affine 版。
使われ方：Prop 8.10、Cor 8.12。 -/
def arcTopologyPerfd : GrothendieckTopology (AffPerfd p κ)ᵒᵖ :=
  (affPerfdInclusion p κ).op.inducedTopology (arcTopology p κ)

/-! ## coverage -/

/-- 概要：arc 被覆族は底変換で安定：R → R′ と {R → R_i} に対し {R′ → R_i ⊗̂_R R′}（p 完備テンソル）も arc 被覆族。
方針：R′ → V は R → V を与え、持ち上げ R_i → W と R′ → V → W から R_i ⊗̂_R R′ → W（W は p 完備）。
規約：完備テンソルは `CompletedTensor`（perfectoid なら perfectoid）。
使われ方：生成系の補題（S1 `isSheaf_toGrothendieck_iff`）を使うための coverage 条件。 -/
theorem isArcCoverFamily_baseChange
    {R R' : Type u} [CommRing R] [CommRing R']
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, R →+* B i) (g : R →+* R')
    (hR : IsModuleComplete R (p : R) (ModuleCat.of R R))
    (hR' : IsModuleComplete R' (p : R') (ModuleCat.of R' R'))
    (hB : ∀ i, IsModuleComplete (B i) (p : B i) (ModuleCat.of (B i) (B i)))
    (hf : IsArcCoverFamily p B f) :
    letI : Algebra R R' := g.toAlgebra
    letI : ∀ i, Algebra R (B i) := fun i => (f i).toAlgebra
    IsArcCoverFamily p
      (fun i => completionRing p (CommRingCat.of (B i ⊗[R] R')))
      (fun i => (completionUnit p (CommRingCat.of (B i ⊗[R] R'))).hom.comp
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] B i ⊗[R] R').toRingHom) := by
  sorry -- R' → V を R に制限して持ち上げ、テンソルと完備化の普遍性で W へ延ばす

/-- 概要：合成・有限族の合併・有限積への置き換え（{R → R_i} と R → ∏R_i は同じ位相を生成）。 -/
theorem isArcCoverFamily_comp
    {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i)
    (J : ι → Type u) [∀ i, Finite (J i)]
    (C : ∀ i, J i → Type u) [∀ i j, CommRing (C i j)]
    (g : ∀ i j, B i →+* C i j)
    (hf : IsArcCoverFamily p B f)
    (hg : ∀ i, IsArcCoverFamily p (C i) (g i)) :
    IsArcCoverFamily p (fun ij : Sigma J => C ij.1 ij.2)
      (fun ij => (g ij.1 ij.2).comp (f ij.1)) := by
  sorry -- V → W → W' の二段の持ち上げと忠実平坦射の合成、有限添字の Sigma

theorem isArcCoverFamily_prod_iff
    {R : Type u} [CommRing R] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i) :
    IsArcCoverFamily p B f ↔
      IsArcCoverFamily p (fun _ : PUnit.{u + 1} => ∀ i, B i)
        (fun _ => RingHom.pi f) := by
  sorry -- 付値環は非零整域なので有限積からの射は一因子を通る（空積の場合も含む）

section ArcCech

open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.Sheaves
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
    IsWeaklyTerminal (arcSieveGenerator p κ f) := by
  sorry -- Q の各射の f.op による因子分解が、𝒟 の U への射を与える

-- §2.1 の cutoff。有限の相対テンソルと可算完備化の台を模型内に収める。
variable [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]

/-- 𝒟 での U の有限冪を相対完備テンソル冪で実現する Čech データ。
各次数の射影、Fan の IsLimit、射影と単体的構造射の整合を含む。 -/
def arcSieveCechData {R S : AffCompl p κ} (f : R ⟶ S) :
    CechNerveData (arcSieveGenerator p κ f) := by
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
    IsLimitCone (restrictionCone F (arcSingleSieve p κ f)) ↔
      IsLimitCone (restrictJoinCone (restrictionCone F (arcSingleSieve p κ f))
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
    Nonempty (Limits.IsLimit c) → IsLimitCone
      ((SerrePositivity.InfinityCategories.JoinCone.ulift.{u, u + 1}
        (F1B.nerveCone ((opOp (AffCompl p κ)).mapCone c))).postcomp F)

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
          IsLimitCone (restrictJoinCone (restrictionCone F (arcSingleSieve p κ f))
            (cechShape (arcSieveCechData p κ f))) := by
  sorry -- arcTopology_eq_sup、⊔ の層条件、isSheaf_extensive_iff_preservesFiniteProducts、isSheaf_toGrothendieck_iff、isSheaf_generateSieve_iff_cech

end ArcCech

/-! ## Lemma 8.8 の affine 版：affPerfd_κ は cover-dense

W9-II-16：A5-4 の `rootClosure_isSemiperfectoid` は `hR : IsIntegralPerfectoid R p` と `Algebra R S` を仮定する（G-A5-14 は θ の核に R 由来の
distinguished 元を使う）。全 p 完備環 S にそのまま当てることはできない（S = ℤ_p：基底なしの根添加 C_∞ は ℤ_p へ retraction をもち、perfectoid 環から
ℤ_p への環準同型はないので semiperfectoid でない）。そこで前段 G-A6-11 を置く。 -/

/-- R₀ の完備化前の表示。X₀ = p と X_{n+1}^p = X_n を課す。 -/
abbrev arcRootPolynomial := MvPolynomial ℕ (ULift.{u} (PadicInt p))

def arcRootIdeal : Ideal (arcRootPolynomial.{u} p) :=
  Ideal.span (insert (MvPolynomial.X 0 - (p : arcRootPolynomial.{u} p))
    (Set.range (fun n : ℕ => MvPolynomial.X (n + 1) ^ p - MvPolynomial.X n)))

abbrev arcRootQuotient := arcRootPolynomial.{u} p ⧸ arcRootIdeal p

/-- 概要：G-A6-11：perfectoid 基底 R₀ := ℤ_p[p^{1/p^∞}]^∧（Type u）。
方針：ℤ_p[X_n : n]/(X_0 − p, X_{n+1}^p − X_n) の p 進完備化。perfectoid 性はこの表示の p 完備化について示す。
規約：固定。E3 の R とは無関係（全 p 完備環を対象とするため）。
使われ方：`baseExtension`。 -/
abbrev perfectoidBaseRing : Type u :=
  (completionRing p (CommRingCat.of (arcRootQuotient.{u} p)) : Type u)

/-- R₀ の指定した根。X₀ の像は p。 -/
def perfectoidBaseRoot (n : ℕ) : perfectoidBaseRing.{u} p :=
  (completionUnit p (CommRingCat.of (arcRootQuotient.{u} p))).hom
    (Ideal.Quotient.mk (arcRootIdeal p) (MvPolynomial.X n))

instance : Algebra (PadicInt p) (perfectoidBaseRing.{u} p) :=
  ((completionUnit p (CommRingCat.of (arcRootQuotient.{u} p))).hom.comp
    ((Ideal.Quotient.mk (arcRootIdeal p)).comp
      ((MvPolynomial.C : ULift.{u} (PadicInt p) →+* arcRootPolynomial.{u} p).comp
        ULift.ringEquiv.symm.toRingHom))).toAlgebra

theorem perfectoidBaseRing_isPerfectoid : IsIntegralPerfectoid (perfectoidBaseRing.{u} p) p := by
  sorry -- 根の塔の p 完備化を a6-design §8.8 の完全 prism の商と同定する

/-- 導来 p 完備な離散環の標準 ℤ_p 作用。完備性の証拠を明示して使う。 -/
def arcPadicIntMap (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : PadicInt p →+* S := by
  sorry -- 整数の単位射を completion_existsUnique で延ばす。ℤ の導来 p 完備化は ℤ_p

/-- 完備化する直前の S ⊗_{ℤ_p} R₀。 -/
def arcBaseTensor (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : CommRingCat.{u} := by
  letI := (arcPadicIntMap p S hS).toAlgebra
  exact CommRingCat.of (S ⊗[PadicInt p] perfectoidBaseRing.{u} p)

/-- 概要：G-A6-11：前段 S₀ := completionRing(S ⊗_{ℤ_p} R₀)（p 完備な R₀ 代数）と単位 S → S₀。
方針：`completionRing`（H⁰(LΛ_p)、既存）と `Algebra.TensorProduct`。
規約：#S₀ ≤ (#S + ℵ₀)^{ℵ₀} ≤ κ（`baseExtension_cardinal_le`）。
使われ方：`exists_perfectoid_arcCover`。 -/
abbrev baseExtension (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : Type u :=
  (completionRing p (arcBaseTensor p S hS) : Type u)

instance (S : Type u) [CommRing S] (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    Algebra (perfectoidBaseRing.{u} p) (baseExtension p S hS) := by
  letI := (arcPadicIntMap p S hS).toAlgebra
  exact ((completionUnit p (arcBaseTensor p S hS)).hom.comp
    (Algebra.TensorProduct.includeRight : perfectoidBaseRing.{u} p →ₐ[PadicInt p]
      S ⊗[PadicInt p] perfectoidBaseRing.{u} p).toRingHom).toAlgebra

def baseExtensionUnit (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) : S →+* baseExtension p S hS := by
  letI := (arcPadicIntMap p S hS).toAlgebra
  exact (completionUnit p (arcBaseTensor p S hS)).hom.comp
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[PadicInt p] perfectoidBaseRing.{u} p)

theorem baseExtension_cardinal_le (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    Cardinal.mk (baseExtension p S hS) ≤ (Cardinal.mk S + Cardinal.aleph0) ^ Cardinal.aleph0 := by
  sorry -- R₀ の濃度は連続体以下、テンソルは有限和、最後の完備化は可算個のデータで評価する

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

/-- 概要：G-A6-3：p 完備な階数 1 の付値環 V は、perfectoid な p 完備階数 1 の付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。
W には p の両立する p 冪根の列がある（絶対整閉包から来る）ので、環準同型 R₀ → W が取れる。
方針：Mathlib の付値の整拡大への延長（要確認）、絶対整閉な p 完備付値環は perfectoid（p 乗根の存在で Frobenius 全射、ker θ は主イデアル）。
規約：—
使われ方：下（W を**先に**取る）、Prop 8.10 の §3.1 の 2。 -/
theorem exists_perfectoid_valuation_extension (V : CommRingCat.{u})
    (hV : IsRankOneCompleteValuationRing p V) :
    ∃ (W : CommRingCat.{u}) (e : V →+* W), IsRankOneCompleteValuationRing p W ∧
      IsIntegralPerfectoid W p ∧ e.FaithfullyFlat ∧
      ∃ ρ : ℕ → W, ρ 0 = (p : W) ∧ ∀ n, ρ (n + 1) ^ p = ρ n := by
  sorry -- 絶対整閉包で両立根を選んで p 完備化する。付値環の局所拡大は忠実平坦

theorem perfectoidBaseRing_toValuationExtension (W : CommRingCat.{u})
    (hW : IsRankOneCompleteValuationRing p W) (ρ : ℕ → W)
    (hzero : ρ 0 = (p : W)) (hpow : ∀ n, ρ (n + 1) ^ p = ρ n) :
    ∃ b : perfectoidBaseRing.{u} p →+* W, ∀ n, b (perfectoidBaseRoot p n) = ρ n := by
  sorry -- X_n ↦ ρ n は表示の二種類の関係を殺し、W の p 完備性で R₀ に延びる

/-- 概要：S → V（試験付値環）は S₀ → W に延びる：W を G-A6-3 で取り、R₀ → W と S → V → W から S ⊗_{ℤ_p} R₀ → W、W は p 完備なので S₀ → W。
方針：`completionRing` の普遍性（p 完備な標的）。
規約：—
使われ方：`exists_perfectoid_arcCover`。 -/
theorem exists_baseExtension_lift_of_map (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (V W : CommRingCat.{u}) (hV : IsRankOneCompleteValuationRing p V)
    (hW : IsRankOneCompleteValuationRing p W) (k : S →+* V) (e : V →+* W)
    (he : e.FaithfullyFlat) (b : perfectoidBaseRing.{u} p →+* W) :
    ∃ l : baseExtension p S hS →+* W,
      l.comp (baseExtensionUnit p S hS) = e.comp k ∧
      l.comp (algebraMap (perfectoidBaseRing.{u} p) (baseExtension p S hS)) = b := by
  sorry -- 二つの脚は ℤ_p 上一致するのでテンソルから射を作り、completion_existsUnique で延ばす

/-- W と b を G-A6-3 で選んだ後、同じ e に沿って S → V を延長する。 -/
theorem exists_baseExtension_lift (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S))
    (V : CommRingCat.{u}) (hV : IsRankOneCompleteValuationRing p V) (k : S →+* V) :
    ∃ (W : CommRingCat.{u}) (e : V →+* W) (l : baseExtension p S hS →+* W),
      IsRankOneCompleteValuationRing p W ∧ IsIntegralPerfectoid W p ∧ e.FaithfullyFlat ∧
      l.comp (baseExtensionUnit p S hS) = e.comp k := by
  sorry -- exists_perfectoid_valuation_extension の根を b に移し、exists_baseExtension_lift_of_map を同じ W に適用

/-- 概要：Lemma 8.8（affine 版）：任意の p 完備環 S は perfectoid による arc 被覆 S → S₀ → S̃₀ → (S̃₀)_perfd をもつ
（S̃₀ は S₀ の R₀ 上の A5-4 `rootClosure`、(S̃₀)_perfd は A5-2 の普遍 perfectoid 環）。
方針（W9-II-16 で訂正）：S → V に対し**先に** perfectoid な W（`exists_perfectoid_valuation_extension`）を取り、`exists_baseExtension_lift` で S₀ → W、
`rootClosure_extends`（標的は perfectoid）で S̃₀ → W、S̃₀ は R₀ 上 semiperfectoid（`rootClosure_isSemiperfectoid`、基底 R₀ で仮定が満たされる）
なので普遍性で (S̃₀)_perfd → W。旧方針「S̃ → V に延びてから W に替える」は `rootClosure_extends` の標的の仮定と順序が合わなかった。
規約：濃度 ≤ κ（S₀・S̃₀・(S̃₀)_perfd とも (#S + ℵ₀)^{ℵ₀} 以下）。未証明の E3・A7 の普遍性は使わない。
使われ方：cover-dense。 -/
theorem exists_perfectoid_arcCover (S : Type u) [CommRing S]
    (hS : IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (T : CommRingCat.{u}) (g : baseExtension p S hS →+* T),
      IsIntegralPerfectoid T p ∧ Cardinal.mk T ≤ (Cardinal.mk S + Cardinal.aleph0) ^ Cardinal.aleph0 ∧
      IsArcCoverFamily p (fun _ : PUnit.{u + 1} => (T : Type u))
        (fun _ => g.comp (baseExtensionUnit p S hS)) := by
  -- S₀ に R₀ 上の rootClosure を施し、その semiperfectoid 性と Cor 7.3 で T と g を取る。
  -- 各 S → V に対し上の拡大 W を先に選び、指定根で R₀ → W、二脚の持ち上げで S₀ → W を得る。
  sorry -- rootClosure_extends と普遍 perfectoid 環の普遍性で同じ W へ延長。濃度は根添加と商の評価

/-- 概要：affPerfd_κ ⥤ affCompl_κ は arc 位相について cover-dense（Mathlib `Functor.IsCoverDense`）。
方針：`exists_perfectoid_arcCover`（前段 G-A6-11 つき。global な affCompl_κ を維持する、W9-II-16）。
規約：Mathlib の 1 圏の道具。これで集合の層の圏同値 `Functor.sheafInducedTopologyEquivOfIsCoverDense`（= `IsDenseSubsite.sheafEquiv`、G-A6-8。W9-II-25 で名前を訂正）が使える。
使われ方：A6-3。 -/
theorem affPerfdInclusion_isCoverDense [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    (affPerfdInclusion p κ).op.IsCoverDense (arcTopology p κ) := by
  apply Functor.isCoverDense_of_generate_singleton_functor_π_mem
  intro X
  sorry -- exists_perfectoid_arcCover の T は hκ で ≤κ。模型に移し、同型で運んだ一点被覆の生成 sieve を arcTopology に入れる

end SerrePositivity.BhattScholze.Perfectoidization.Derived
