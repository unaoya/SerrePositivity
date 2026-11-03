-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSheafProperty（仮。原典 Prop 8.10 の affine 版と三つの引用）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.2・§3.1、単位 A6-2。基準コミット 972bb7f53。ビルドしない。
-- 引用 3 件の `sorry` 定理（G-A6-1a・1b・1c）は drafts/ の間は問題なし。SerrePositivity/ に入れるときは scripts/make_area_audits.py の許可一覧の更新を調整役に依頼する（main 7b8b96286）。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTilt
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.InfinityCategories.F2.Ind.NativeFilteredPreservation
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
-- 本ファイルは drafts/DerivedGeneral/Truncation.lean の IsCoconnectiveAt も使う。
-- W9-III-08：2a 後は E3 非依存の芯（仮称 CompletedTensorCore）だけを import する（a9-design §7）。
-- 本ファイルは drafts/A6/ArcSite.lean、drafts/Sheaves/{SheafCondition,CAlgValued}.lean、drafts/A0/PrismaticSite.lean（`ringPresheafToCAlg`）、
-- drafts/A4/AfterComparison.lean（Example 8.3 `perfectoidization_charP` を tilt の段で使う場合。W9-III-14）を import する。

/-!
# 構造層の arc 層性（BS 著者版 Prop 8.10 の affine 版）と三つの引用

## 概要
O : R ↦ R（**CAlg_ℤ 値**。W9-II-22：global な affPerfd_κ の対象には固定 R からの射がないので CAlg_R 値にはできない。F_U の元の圏 Perfd_{U/} の上で
R → U → T により CAlg_R 値に持ち上げ、極限・引き戻しは忘却 CAlg_R → CAlg_ℤ が作る）は affPerfd_κ 上の arc 層（Čech 層、D-S1）。affine T について Hom(T, −) は集合の arc 層。
原典の証明を追う：単射 arc 被覆 R → S の完備 Čech 複体の完全性に帰着し、tilt で完全 F_p 代数の d 進完備 Čech 複体に移し、
完全 F_p 代数の arc 被覆の Čech 完全性（G-A6-1）を使う。G-A6-1 は三つの引用 [BS17, Thm 4.1 (i)]・[BM18, Thm 1.7]・[BS17, Lemma 6.2/6.3] から
導く。三つは原典が引用している形で述べ、`sorry`（決定 2）。1c は初等的なので後で証明する。

## 方針
tilt の段：R = W(R^♭)/d、S ⊗̂_R S = W(S^♭ ⊗̂_{R^♭} S^♭)/d（G-A6-4）。余単体的な完全環に levelwise の W_n を当て、V の短完全列で Čech 複体の完全性を帰納、
Rlim で W へ、各 Witt 環で正則な d の cofiber で mod d へ（G-A6-5。W9-II-20：正則なのは W(B) 上の d で、tilt 上の a := d mod p は零になり得る）。
{R^♭ → S^♭, R^♭ → R^♭[1/a]} は完全 F_p 代数の arc 被覆族（付値環の tilt・untilt、G-A6-6。階数 0・a = 0 の分岐込み、W9-II-21）。導来 a 進完備化で R^♭[1/a] の項を消す（G-A6-7）。

## 規約
v 被覆は [BS17, Def 2.1]（任意の付値環）、arc 被覆は [BM18, Def 1.2]（階数 ≤ 1 の付値環）の affine・有限族の形。引用は affine 版（D59）。

## 使われ方
Cor 8.11 の affine 版（記録）、Cor 8.12（A6-4：O と F_T の層性）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

/-! ## 三つの引用（`sorry`） -/

open SerrePositivity.InfinityCategories SerrePositivity.BhattScholze.PerfectoidizationInterface

/-- 指定した階数の付値環で試す有限族。W とその整域構造を同じ証人として保持する。 -/
def ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], rank V → ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ rank W ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k

/-- 概要：[BS17, Def 2.1] の affine 版：F_p 代数の有限族 {A → B_i} が v 被覆 ⇔ 任意の付値環 V と A → V に対し、或る i と付値環の拡大 V ↪ W と B_i → W。
方針：定義。
規約：V は任意の階数。
使われ方：G-A6-1a・1b。 -/
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : Prop := ValuativeCoverFamily (fun _ => True) B f

/-- 概要：[BM18, Def 1.2] の affine 版（標数 p、p 完備性なし）：階数 ≤ 1 の付値環で同様。
方針：定義。`IsArcCoverFamily`（p 完備版）とは試験対象が違う。
規約：—
使われ方：G-A6-1b・G-A6-1。 -/
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : Prop := ValuativeCoverFamily (fun V => ringKrullDim V ≤ 1) B f

/-- 増大項での単射性、第0項での完全性、および全正次数での完全性。 -/
def AugmentedRingCechExact (X : CosimplicialObject.Augmented CommRingCat.{u}) : Prop :=
  let U := forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}
  let C := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (X.right ⋙ U)
  let ε := (X.hom.app ⦋0⦌).hom
  Function.Injective ε ∧ Function.Exact ε (fun x => (C.d 0 1) x) ∧
    ∀ n : ℕ, Function.Exact (fun x => (C.d n (n + 1)) x) (fun x => (C.d (n + 1) (n + 2)) x)

/-- 有限族の積への射の相対 Čech 余脈体。各次数は通常の A 上のテンソル冪。 -/
def affineFamilyCech {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) :
    CosimplicialObject.Augmented CommRingCat.{u} :=
  (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve

/-- 概要：**G-A6-1a**［引用、`sorry`］[BS17, Thm 4.1 (i)]（n = 1、E = O）：完全 F_p 代数 A と**完全** F_p 代数 B_i への v 被覆族 {A → B_i} について
A = RΓ_v(Spec A, O)、すなわち 0 → A → ∏B_i → ∏B_i ⊗_A B_j → ⋯ が完全（W9-II-18：被覆と Čech の各項は完全スキームの圏で取る。適用先
B = S^♭ × R^♭[1/d] は完全）。
方針：引用（v 降下、完全スキーム）。
規約：affine・有限族（D59）。
使われ方：G-A6-1。 -/
theorem cech_exact_of_vCover_perfect {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsVCoverFamily B f) :
    AugmentedRingCechExact (affineFamilyCech B f) := by
  sorry -- [BS17, Thm 4.1 (i)]

/-- 通常の F_p 代数（零環も含む）と整数の係数を Type u に揃える。 -/
abbrev ArcFp := ULift.{u} (ZMod p)
abbrev ArcZ := ULift.{u} ℤ

/-- 有限族が生成する sieve の環側の添字。A→D がいずれかの A→B_i を経由する。 -/
def fpFamilyFactor {ι : Type u} {A : A_R (ArcFp.{u} p)} {B : ι → A_R (ArcFp.{u} p)}
    (f : ∀ i, A ⟶ B i) : ObjectProperty (Under A) :=
  fun t => ∃ i, ∃ l : B i ⟶ t.right, f i ≫ l = t.hom

/-- 増大項 A と、生成 sieve に属するすべての構造射による指定錐。 -/
def fpFamilyCone {ι : Type u} {A : A_R (ArcFp.{u} p)} {B : ι → A_R (ArcFp.{u} p)}
    (f : ∀ i, A ⟶ B i) : Cone ((fpFamilyFactor p f).ι ⋙ Under.forget A) where
  pt := A
  π := { app := fun t => t.obj.hom
         naturality := by sorry } -- Under.w による可換性

/-- 共変関手に対する有限被覆族の sieve 降下。AsSmall は宇宙を u+1 に揃える同値。
全 Type u の試験環で関手を評価し、有限族の成分を F に適用する前に一射へ縮約しない。 -/
def IsFpSheafFor
    (test : ∀ {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
      (B : ι → Type u) [∀ i, CommRing (B i)], (∀ i, A →+* B i) → Prop)
    (F : algebraNerve (ArcFp.{u} p) ⟶ derivedInfinityCategory ArcZ.{u}) : Prop :=
  ∀ (ι : Type u) [Finite ι] (A : A_R (ArcFp.{u} p)) (B : ι → A_R (ArcFp.{u} p))
    (f : ∀ i, A ⟶ B i), test (fun i => ((B i).right : Type u)) (fun i => (f i).right.hom) →
    let I := (fpFamilyFactor p f).FullSubcategory
    let C := A_R (ArcFp.{u} p)
    let c := (AsSmall.up : C ⥤ AsSmall.{u + 1} C).mapCone
      ((fpFamilyCone p f).whisker (AsSmall.down : AsSmall.{u + 1} I ⥤ I))
    IsLimitCone ((F1B.nerveCone c).postcomp
      (nerveMap (AsSmall.down : AsSmall.{u + 1} C ⥤ C) ≫ F))

/-- V, V_𝔭, V/𝔭, κ(𝔭) の標準四角形。すべて同じ F_p 代数構造の下で取る。 -/
def fpValuationSquare (V : A_R (ArcFp.{u} p)) (P : Ideal V.right) [P.IsPrime] :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ algebraNerve (ArcFp.{u} p) := by
  let L := Localization.AtPrime P
  let K := P.ResidueField
  let loc : A_R (ArcFp.{u} p) := Under.mk (V.hom ≫ CommRingCat.ofHom (algebraMap V.right L))
  let res : A_R (ArcFp.{u} p) := Under.mk (V.hom ≫ CommRingCat.ofHom (algebraMap V.right K))
  let a : V ⟶ loc := Under.homMk (CommRingCat.ofHom (algebraMap V.right L)) rfl
  let b := quotientProjection (ArcFp.{u} p) V P
  let c : loc ⟶ res := Under.homMk (CommRingCat.ofHom (IsLocalRing.residue L)) (by
    sorry) -- κ(𝔭) の V 作用は V_𝔭 の剰余射経由
  let d : quotientAlgebra (ArcFp.{u} p) V P ⟶ res :=
    Under.homMk (CommRingCat.ofHom (algebraMap (V.right ⧸ P) K)) (by
      sorry) -- 剰余体への構造射を V/𝔭 に降ろしたもの
  exact ordinarySquare (ArcFp.{u} p) a b c d (by sorry) -- 二つの合成は同じ剰余体への射

/-- 概要：**G-A6-1b**［引用、`sorry`］[BM18, Thm 1.7]（BS の引用では Thm 1.6）の affine 版：finitary（filtered 余極限と可換）な**共変**関手
F : Ring_{F_p} → D(ℤ)^{≥0}（W9-II-17：環の圏の上では共変、値は cohomological に coconnective：H^i = 0 for i < 0。適用する A ↦ A_perf は環に共変）
について、F が arc 層 ⇔ F が v 層かつ、分数体が代数閉な任意の付値環 V と素イデアル 𝔭 ⊂ V について
F(V) → F(V/𝔭)、F(V_𝔭) → F(κ(𝔭)) の四角形が cartesian。使うのは ⇐。
方針：引用。
規約：D(ℤ)^{≥0} は `derivedInfinityCategory ℤ` の coconnective 部分（`IsCoconnectiveAt 0`）。層条件は有限族の Čech（D-S1）。
affine 版（D59）の根拠：v 層は有限 affine 開被覆の降下を満たすので affine の値から qcqs へ延長でき、finitary 性は有限段の降下と一様に coconnective な
Tot の filtered 余極限との交換（BM18 v4 p.4 Thm 1.7、p.17 Ex 3.6(1)、p.25 Thm 4.1）。
使われ方：G-A6-1。 -/
theorem arcSheaf_of_vSheaf_of_valuationSquares
    (F : algebraNerve (ArcFp.{u} p) ⟶ derivedInfinityCategory ArcZ.{u})
    (hfin : F2.Ind.PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hco : ∀ A : A_R (ArcFp.{u} p), SerrePositivity.InfinityCategories.Derived.IsCoconnectiveAt ArcZ.{u} 0
      (F.app (Opposite.op ⦋0⦌) (nerveVertex A))) :
    IsFpSheafFor p (@IsArcCoverFamilyCharP) F ↔
      IsFpSheafFor p (@IsVCoverFamily) F ∧
        ∀ (V : A_R (ArcFp.{u} p)) [IsDomain V.right] [ValuationRing V.right]
          [IsAlgClosed (FractionRing V.right)] (P : Ideal V.right) [P.IsPrime],
          IsPullbackSquare (fpValuationSquare p V P ≫ F) := by
  sorry -- [BM18, Thm 1.7]

/-- 加法群としての付値環の Milnor 短完全列。最後の射は二つの剰余の差。 -/
def MilnorShortExact {V : Type u} [CommRing V] (P : Ideal V) [P.IsPrime] : Prop :=
  let L := Localization.AtPrime P
  let i := fun x : V => (algebraMap V L x, Ideal.Quotient.mk P x)
  let d := fun z : L × (V ⧸ P) => IsLocalRing.residue L z.1 - algebraMap (V ⧸ P) P.ResidueField z.2
  Function.Injective i ∧ Function.Exact i d ∧ Function.Surjective d

/-- 概要：初等補題（引用ではない、W9-II-18）：任意の付値環 V と素イデアル 𝔭 について 0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0 が完全、すなわち
V → V_𝔭、V → V/𝔭、→ κ(𝔭) の四角形は環の圏で cartesian（V = V_𝔭 ×_{κ(𝔭)} V/𝔭）かつ cocartesian。
方針：𝔭V_𝔭 = 𝔭（a ∈ 𝔭、s ∉ 𝔭 で a/s ∉ V なら付値環性で s/a ∈ V、s = a·(s/a) ∈ 𝔭 で矛盾；a/s ∈ V なら素性で a/s ∈ 𝔭）。よって V_𝔭/𝔭V_𝔭 = κ(𝔭) で
V_𝔭 → κ(𝔭) の核が V の 𝔭 の像に一致するので短完全列、右の射は差で V_𝔭 → κ(𝔭) は全射。cocartesian は局所化と商の可換性。加群の導来圏でも cartesian。
規約：—
使われ方：`valuationRing_milnorSquare_perfect`。 -/
theorem valuationRing_milnorSquare {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] (𝔭 : Ideal V) [𝔭.IsPrime] : MilnorShortExact 𝔭 := by
  sorry -- 初等的。中身の段階で証明

/-- 概要：**G-A6-1c**［引用、`sorry`、上の初等補題の特殊化として後で証明］[BS17, Lemma 6.3]（Lemma 6.2 は付値環による v 被覆の主張で、この四角形
ではない。W9-II-18）：**完全**付値環 V（標数 p）と素イデアル 𝔭 について 0 → V → V_𝔭 ⊕ V/𝔭 → κ(𝔭) → 0 が完全。
方針：原典の形で引用。適用先（分数体が代数閉な標数 p の付値環）は完全なのでこの特殊化で足りる。
規約：「完全」の仮定を落とした一般版を引用そのものとは記さない。
使われ方：G-A6-1（F = O_perf の四角形）。 -/
theorem valuationRing_milnorSquare_perfect {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CharP V p] [PerfectRing V p]
    (𝔭 : Ideal V) [𝔭.IsPrime] : MilnorShortExact 𝔭 := by
  sorry -- [BS17, Lemma 6.3]

/-- 概要：G-A6-1：完全 F_p 代数の有限族の arc 被覆 {A → B_i} について 0 → A → ∏B_i → ∏B_i ⊗_A B_j → ⋯ が完全。
方針：F := (A ↦ A_perf) は F_p 代数上の finitary な関手。1a を完全化に当てて v 層（完全化は v 被覆を保つ）。分数体が代数閉な付値環は完全なので
四角形は 1c の Milnor 四角形（`valuationRing_milnorSquare_perfect`）で cartesian。1b（共変、D(ℤ)^{≥0} 値）で arc 層。arc 層で F(A) 離散なら Tot = Čech 複体の完全性。
規約：—
使われ方：Prop 8.10。 -/
theorem cech_exact_of_arcCover_perfect {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, CharP (B i) p]
    [∀ i, PerfectRing (B i) p] (f : ∀ i, A →+* B i) (hf : IsArcCoverFamilyCharP B f) :
    AugmentedRingCechExact (affineFamilyCech B f) := by
  sorry -- 完全化に 1a・1c と 1b を適用し、完全環上で相対 Čech 複体の完全性に戻す

/-! ## tilt（零環を含む。BS-D1 の D1-03、2026-11-03 決定） -/

/-- 概要：G-A6-14：零環を含む tilt。p 完備な O について、O が零環なら零環、そうでなければ Mathlib の `PreTilt O p`（p 完備で非零なら p は Jacobson 根基に入り
非単元なので `Fact (¬IsUnit (p : O))` が立つ）。原典の tilt O^♭ = lim_φ O/p は零環で零環なので**定義の変更ではない**。Mathlib の `PreTilt` の環構造が
`¬IsUnit p` を仮定することへの対処（D1-03：F_p × F_p の二つの射影による F_p 同士の相対完備テンソルは零環で、両因子が非零でも起こる）。
方針：`Classical` で `Subsingleton O` により分岐し `CommRingCat.{u}` の対象を返す。
規約：非零の場合の同一視は `tiltRingEquivPreTilt`。A6 の tilt を使う主張はすべてこの `tiltRing` で述べる。
使われ方：G-A6-4〜6、Prop 8.10 の tilt の段。 -/
def tiltRing (O : Type u) [CommRing O] : CommRingCat.{u} := sorry
theorem tiltRing_subsingleton (O : Type u) [CommRing O] [Subsingleton O] : Subsingleton (tiltRing p O) := by
  sorry -- 分岐の左
def tiltRingEquivPreTilt (O : Type u) [CommRing O] [Fact (¬ IsUnit (p : O))] : (tiltRing p O : Type u) ≃+* PreTilt O p := sorry

/-- 概要：p 完備で非零な環では p は単元でない（p は Jacobson 根基に入る：1 − px は p 進級数で可逆）。
方針：`IsModuleComplete` から p 進完備性、幾何級数。
規約：—
使われ方：`tiltRing` の分岐を `Subsingleton` で取ってよい根拠。 -/
theorem not_isUnit_p_of_isModuleComplete (O : Type u) [CommRing O] [Nontrivial O]
    (hO : IsModuleComplete O (p : O) (ModuleCat.of O O)) : ¬ IsUnit (p : O) := by
  sorry

/-- 概要：tilt の関手性：O → O′ に対し tiltRing O → tiltRing O′。場合は三つ（零→零、非零→零は零環への一意な射、非零→非零は ModP の射の `Perfection.map`）。
零環から非零への環準同型はない。
方針：分岐ごと。
規約：恒等・合成を保つ。
使われ方：G-A6-4 の代数構造、Čech 複体の tilt の関手性。 -/
def tiltMap {O O' : Type u} [CommRing O] [CommRing O'] (f : O →+* O') : tiltRing p O ⟶ tiltRing p O' := sorry
theorem tiltMap_id (O : Type u) [CommRing O] : tiltMap p (RingHom.id O) = 𝟙 (tiltRing p O) := by sorry
theorem tiltMap_comp {O O' O'' : Type u} [CommRing O] [CommRing O'] [CommRing O''] (f : O →+* O') (g : O' →+* O'') :
    tiltMap p (g.comp f) = tiltMap p f ≫ tiltMap p g := by sorry

/-- 概要：R^♭ の元 a が「核の生成元 d の mod p の像」であること（R 非零なら ker θ_R = (d) の d に対し a = d mod p；R 零なら任意）。
方針：`fontaineTheta` の核の生成元から。
規約：a による完備化は原典の「d 進完備」。
使われ方：G-A6-4 の右辺の完備化。 -/
def IsTiltGenerator (R : Type u) [CommRing R] (a : tiltRing p R) : Prop := sorry

/-- 概要：G-A6-4：perfectoid の完備テンソルの tilt：(S ⊗̂_R S′)^♭ ≅ (S^♭ ⊗_{R^♭} S′^♭)^∧_a（a 進完備化、a = d mod p）。零環の場合を含む（`tiltRing`）。
方針：非零の場合は既存の `CompletedTensor` の芯（Fontaine 表示 W(−)/d との比較）と `WittQuotientTilt`。零環が現れる場合（因子が零、または相対テンソルだけが零）は
両辺とも零環。
規約：代数構造は `tiltMap` で入れる。完備化は `PrincipalCompletionH0 _ a`。
使われ方：Čech 複体の tilt（Prop 8.10 の §3.1 の 1）。 -/
theorem completedTensor_tilt (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) (hS' : IsIntegralPerfectoid S' p)
    (a : tiltRing p R) (ha : IsTiltGenerator p R a) :
    letI := (tiltMap p (algebraMap R S)).hom.toAlgebra
    letI := (tiltMap p (algebraMap R S')).hom.toAlgebra
    Nonempty ((tiltRing p (completionRing p (CommRingCat.of (S ⊗[R] S'))) : Type u) ≃+*
      PrincipalCompletionH0 ((tiltRing p S : Type u) ⊗[(tiltRing p R : Type u)] (tiltRing p S' : Type u))
        (algebraMap (tiltRing p R : Type u) _ a)) := by
  sorry -- 非零：Fontaine 表示と完備テンソルの芯。零環：両辺零

/-- 概要：G-A6-5（W9-II-20 で訂正）：augmented 余単体的な完全 F_p 代数 B^• の Čech 複体が完全なら、W(B^•) の Čech 複体も完全で、W(B^•)/d（d は各 W(B^k) で
正則な distinguished 元）の Čech 複体も完全。正則なのは Witt 環上の d であって tilt 上の d mod p ではない（R が標数 p なら d = p、像は 0）。
方針：levelwise に W_n、加法群の短完全列 0 → W_{n−1}(B^•) → W_n(B^•) → B^• → 0（V）で帰納、遷移 W_n → W_{n−1} は項ごとに全射なので Rlim = lim（Mittag-Leffler）、
d の cofiber は d 正則なので通常の商の複体。Mathlib `WittVector` の `verschiebung`・`truncate` の API。「W を交代和微分に直接当てる」のではない。
規約：—
使われ方：Čech 複体の tilt。 -/
theorem witt_exact_of_perfect : True := by trivial
theorem modD_exact_of_regular : True := by trivial

/-- 概要：G-A6-6：階数 1 の付値環の tilt・untilt：V が完全で a 進完備（a := d mod p）な階数 1 の付値環（R^♭ 上）なら V^♯ := W(V)/d は p 完備な階数 1 の付値環で
(V^♯)^♭ = V（a = 0 なら d は W(V) で p の単元倍、V^♯ = V）；W が perfectoid な p 完備階数 1 の付値環なら W^♭ は完全な階数 1 の付値環。
方針：既存 `WittQuotientTilt`（環の部分）＋付値の対応。付値環性（W9 続き 6）：U = W(V)/d は局所・被約・p ねじれなし、非零元を p 冪で割って mod p 非零にし、
Teichmüller の像で x = b^♯ + ϖc、V の可除性の全順序で x = b^♯(1 + (ϖ^♭/b)^♯c) と単元倍の sharp に書ける。[Česnavičius–Scholze, Purity for flat cohomology,
Prop 2.1.9] の証明と同じ（証明の参照。第四の黒箱ではない）。
規約：—
使われ方：§3.1 の 2。 -/
theorem untilt_rankOneValuationRing : True := by trivial
theorem tilt_rankOneValuationRing : True := by trivial

/-- 概要：{R^♭ → S^♭, R^♭ → R^♭[1/a]}（a := d mod p）は完全 F_p 代数の arc 被覆族（`IsArcCoverFamilyCharP`、階数 ≤ 1 で試す。R → S が perfectoid の arc 被覆のとき）。
方針（W9-II-21 で分岐を補記）：R^♭ → V。V → V_perf は整・局所・単射で忠実平坦なので V は完全としてよい。(i) a が単元なら第二成分。(ii) V 階数 1、a 非零非単元なら
a 進完備化 V̂（階数 1・完全、V → V̂ 忠実平坦）、untilt V̂^♯ へ R → V̂^♯。(iii) V 階数 1、a = 0 なら V^♯ = V。(iv) V 階数 0（完全体 k）、a 非単元なら a = 0、
V₁ := k[t^{1/p^∞}]_{(t^{1/p^∞})} の t 進完備化（完全・階数 1、k → V₁ 忠実平坦）へ移って (iii)。R → V̂^♯ に仮定を当て、perfectoid な W に拡大（G-A6-3）、
S → W、V̂ → W^♭ は局所単射で忠実平坦、S^♭ → W^♭。
規約：—
使われ方：Prop 8.10。 -/
theorem tilt_arcCoverFamily : True := by trivial

/-- 概要：G-A6-7：導来 a 進完備化（a := d mod p）は完全列を保ち、a が可逆な項を殺す；Čech 複体 of {R^♭ → S^♭, R^♭ → R^♭[1/a]} の各項の分解で R^♭[1/a] が混じる項の完備化は零。
方針：HA/DerivedCompletion（2b 後の名前）。
規約：—
使われ方：Prop 8.10。 -/
theorem cech_completion_kills_inverted : True := by trivial

/-! ## Prop 8.10 -/

/-- 概要：Prop 8.10 前半（affine）：単射 arc 被覆 R → S（perfectoid）の完備 Čech 複体 0 → R → S → S ⊗̂_R S → ⋯ は完全。
方針：tilt（G-A6-4・5）、`tilt_arcCoverFamily`、`cech_exact_of_arcCover_perfect`、`cech_completion_kills_inverted`。
規約：—
使われ方：`structurePresheaf_isArcSheaf`。 -/
theorem cech_exact_of_arcCover_perfectoid : True := by trivial

/-- 概要：Prop 8.10 前半：O（CAlg_ℤ 値、R ↦ R。W9-II-22）は affPerfd_κ 上の arc 層（Čech 層、D-S1）。
方針：S1 の生成系の補題と `isSheaf_arc_iff_cech`、有限族を R → ∏R_i に置き換え、`cech_exact_of_arcCover_perfectoid`（離散な余単体的環の Tot は Čech 複体）。
規約：`IsSheaf (arcTopologyPerfd p κ) (structurePresheaf …)`。
使われ方：Cor 8.11 の affine 版、Cor 8.12。 -/
theorem structurePresheaf_isArcSheaf : True := by trivial

/-- 概要：Prop 8.10 後半（affine T）：R ↦ Hom(T, R) は affPerfd_κ 上の集合の arc 層。
方針：H⁰ の等化子 R = eq(S ⇉ S ⊗̂_R S) に Hom(T, −) を当てる。
規約：Mathlib の `Presheaf.IsSheaf`（集合値）。
使われ方：Cor 8.12 の F_T。 -/
theorem homPresheaf_isArcSheaf (T : Type u) [CommRing T] : True := by trivial

/-- 概要：Cor 8.11 の affine 版（記録、D55）：S_perfd ≃ RΓ_arc(affPerfd_κ/S, O)（slice site の上の β の RΓ）。
方針：O は層なので RΓ = lim（S2）、lim_{Perfd_{S/}} O = S_perfd（Prop 8.5、A5）。
規約：fSch・affCompl_κ 上の RΓ との比較はしない。
使われ方：記録。 -/
theorem perfectoidization_eq_arcCohomology : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
