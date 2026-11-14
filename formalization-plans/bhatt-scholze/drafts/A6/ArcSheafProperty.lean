-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Arc.ArcSheafProperty（仮。原典 Prop 8.10 の affine 版と三つの引用）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §2.2・§3.1、単位 A6-2。基準コミット efa846fe8。型検査対象（5∞-0）。
-- 引用 3 件の `sorry` 定理（G-A6-1a・1b・1c）は drafts/ の間は問題なし。SerrePositivity/ に入れるときは scripts/make_area_audits.py の許可一覧の更新を調整役に依頼する（main 7b8b96286）。
module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationExtension
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationUntilt
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationMilnor
public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTilt
public import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
-- Cor 8.11 は drafts/A5/{PerfectSiteComparison,InterfaceLimitCone}.lean と drafts/Sheaves/GlobalSections.lean を使う。
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
open scoped Simplicial TensorProduct

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

variable (p : ℕ) [Fact p.Prime] (κ : Cardinal.{u})

/-! ## 三つの引用（`sorry`） -/

open SerrePositivity.InfinityCategories SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories.Sheaves

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
    (F : algebraNerve (ArcFp.{u} p) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory ArcZ.{u}) : Prop :=
  ∀ (ι : Type u) [Finite ι] (A : A_R (ArcFp.{u} p)) (B : ι → A_R (ArcFp.{u} p))
    (f : ∀ i, A ⟶ B i), test (fun i => ((B i).right : Type u)) (fun i => (f i).right.hom) →
    let I := (fpFamilyFactor p f).FullSubcategory
    let C := A_R (ArcFp.{u} p)
    let c := (AsSmall.up : C ⥤ AsSmall.{u + 1} C).mapCone
      ((fpFamilyCone p f).whisker (AsSmall.down : AsSmall.{u + 1} I ⥤ I))
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone c).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (AsSmall.down : AsSmall.{u + 1} C ⥤ C) ≫ F))

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
    (F : algebraNerve (ArcFp.{u} p) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory ArcZ.{u})
    (hfin : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hco : ∀ A : A_R (ArcFp.{u} p), SerrePositivity.InfinityCategories.Derived.IsCoconnectiveAt ArcZ.{u} 0
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A))) :
    IsFpSheafFor p (@IsArcCoverFamilyCharP) F ↔
      IsFpSheafFor p (@IsVCoverFamily) F ∧
        ∀ (V : A_R (ArcFp.{u} p)) [IsDomain V.right] [ValuationRing V.right]
          [IsAlgClosed (FractionRing V.right)] (P : Ideal V.right) [P.IsPrime],
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (fpValuationSquare p V P ≫ F) := by
  sorry -- [BM18, Thm 1.7]

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

theorem tiltRing_subsingleton (O : Type u) [CommRing O] [Subsingleton O] : Subsingleton (tiltRing p O) := by
  sorry -- 分岐の左

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
    let T := (tiltRing p S : Type u) ⊗[(tiltRing p R : Type u)] (tiltRing p S' : Type u)
    let b : T := algebraMap (tiltRing p R : Type u) T a
    letI := principalCompletionCommRing T b
    Nonempty ((tiltRing p (completionRing p (CommRingCat.of (S ⊗[R] S'))) : Type u) ≃+*
      PrincipalCompletionH0 T b) := by
  sorry -- 非零：Fontaine 表示と完備テンソルの芯。零環：両辺零

/-- 増大項を含む全次数で完全 F_p 代数。p = 0 の形は零環にも適用できる。 -/
def IsPerfectFpDiagram (B : CosimplicialObject.Augmented CommRingCat.{u}) : Prop :=
  ((p : B.left) = 0 ∧ PerfectRing B.left p) ∧
    ∀ k : SimplexCategory, (p : B.right.obj k) = 0 ∧ PerfectRing (B.right.obj k) p

def arcWittFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (WittVector p A)
  map f := CommRingCat.ofHom (WittVector.map f.hom)
  map_id := by sorry -- 各 Witt 係数で恒等
  map_comp := by sorry -- map_coeff で合成を比較

def arcTruncatedWittFunctor (n : ℕ) : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (TruncatedWittVector p n A)
  map f := CommRingCat.ofHom {
    toFun := fun x => TruncatedWittVector.mk p (fun i => f.hom (x.coeff i))
    map_one' := by sorry -- truncate の全射性と WittVector.map の単位保存
    map_mul' := by sorry -- WittVector.truncate と係数写像の可換性
    map_zero' := by sorry -- 零の係数はすべて零
    map_add' := by sorry } -- WittVector.truncate と係数写像の可換性
  map_id := by sorry -- 係数ごと
  map_comp := by sorry -- 係数ごと

/-- 増大射を構造射として全次数を B.left 上に置く。 -/
def augmentedOverBase (B : CosimplicialObject.Augmented CommRingCat.{u}) :
    CosimplicialObject.Augmented (Under B.left) where
  left := Under.mk (𝟙 B.left)
  right := {
    obj := fun k => Under.mk (B.hom.app k)
    map := fun g => Under.homMk (B.right.map g) (by sorry) -- 増大射の自然性
    map_id := by sorry -- Under の射は環の射で決まる
    map_comp := by sorry } -- 同じく B.right.map_comp
  hom := {
    app := fun k => Under.homMk (B.hom.app k) (by simp)
    naturality := by sorry } -- B.hom.naturality

/-- A 上の各環における d の像で割る。射は構造射との可換性による商への降下。 -/
def quotientByBaseElement (A : CommRingCat.{u}) (d : A) : Under A ⥤ CommRingCat.{u} where
  obj T := CommRingCat.of (T.right ⧸ Ideal.span {T.hom.hom d})
  map {T U} f := CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {U.hom.hom d}) f.right.hom
    (by sorry)) -- Under.w によって生成元の像が一致
  map_id := by sorry -- 商写像の全射性
  map_comp := by sorry -- 商写像の全射性

/-- 概要：G-A6-5（W9-II-20 で訂正）：augmented 余単体的な完全 F_p 代数 B^• の Čech 複体が完全なら、W(B^•) の Čech 複体も完全で、W(B^•)/d（d は各 W(B^k) で
正則な distinguished 元）の Čech 複体も完全。正則なのは Witt 環上の d であって tilt 上の d mod p ではない（R が標数 p なら d = p、像は 0）。
方針：levelwise に W_n、加法群の短完全列 0 → W_{n−1}(B^•) → W_n(B^•) → B^• → 0（V）で帰納、遷移 W_n → W_{n−1} は項ごとに全射なので Rlim = lim（Mittag-Leffler）、
d の cofiber は d 正則なので通常の商の複体。Mathlib `WittVector` の `verschiebung`・`truncate` の API。「W を交代和微分に直接当てる」のではない。
規約：—
使われ方：Čech 複体の tilt。 -/
theorem witt_exact_of_perfect (B : CosimplicialObject.Augmented CommRingCat.{u})
    (hB : IsPerfectFpDiagram p B) (hex : AugmentedRingCechExact B) :
    (∀ n : ℕ, AugmentedRingCechExact
      ((CosimplicialObject.Augmented.whiskeringObj _ _ (arcTruncatedWittFunctor p n)).obj B)) ∧
    AugmentedRingCechExact
      ((CosimplicialObject.Augmented.whiskeringObj _ _ (arcWittFunctor p)).obj B) := by
  sorry -- V の短完全列で n に帰納し、項ごとに全射な切断塔の Rlim を取る

theorem modD_exact_of_regular (B : CosimplicialObject.Augmented CommRingCat.{u})
    (hB : IsPerfectFpDiagram p B) (hex : AugmentedRingCechExact B)
    (d : WittVector p B.left) (hd : IsUnit (d.coeff 1)) (hreg : IsLeftRegular d)
    (hregTerm : ∀ k : SimplexCategory, IsLeftRegular (WittVector.map (B.hom.app k).hom d)) :
    let W := (CosimplicialObject.Augmented.whiskeringObj _ _ (arcWittFunctor p)).obj B
    AugmentedRingCechExact
      ((CosimplicialObject.Augmented.whiskeringObj _ _ (quotientByBaseElement W.left d)).obj
        (augmentedOverBase W)) := by
  sorry -- witt_exact_of_perfect と d の乗法の短完全列。項ごとの正則性により cofiber は通常の商

/-- 二成分を同一の有限添字で表す。 -/
def tiltArcTarget (R S : Type u) [CommRing R] [CommRing S] (a : tiltRing p R) :
    ULift.{u} Bool → CommRingCat.{u} := fun i =>
  Bool.rec (tiltRing p S) (CommRingCat.of (Localization.Away a)) i.down

def tiltArcArrow {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (a : tiltRing p R)
    (i : ULift.{u} Bool) : (tiltRing p R : Type u) →+* tiltArcTarget p R S a i := by
  obtain ⟨b⟩ := i
  cases b
  · exact (tiltMap p f).hom
  · exact algebraMap _ (Localization.Away a)

/-- 概要：{R^♭ → S^♭, R^♭ → R^♭[1/a]}（a := d mod p）は完全 F_p 代数の arc 被覆族（`IsArcCoverFamilyCharP`、階数 ≤ 1 で試す。R → S が perfectoid の arc 被覆のとき）。
方針（W9-II-21 で分岐を補記）：R^♭ → V。V → V_perf は整・局所・単射で忠実平坦なので V は完全としてよい。(i) a が単元なら第二成分。(ii) V 階数 1、a 非零非単元なら
a 進完備化 V̂（階数 1・完全、V → V̂ 忠実平坦）、untilt V̂^♯ へ R → V̂^♯。(iii) V 階数 1、a = 0 なら V^♯ = V。(iv) V 階数 0（完全体 k）、a 非単元なら a = 0、
V₁ := k[t^{1/p^∞}]_{(t^{1/p^∞})} の t 進完備化（完全・階数 1、k → V₁ 忠実平坦）へ移って (iii)。R → V̂^♯ に仮定を当て、perfectoid な W に拡大（G-A6-3）、
S → W、V̂ → W^♭ は局所単射で忠実平坦、S^♭ → W^♭。
規約：—
使われ方：Prop 8.10。 -/
theorem tilt_arcCoverFamily {R S : Type u} [CommRing R] [CommRing S]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) (f : R →+* S)
    (hf : IsArcCoverFamily p (fun _ : PUnit.{u + 1} => S) (fun _ => f))
    (a : tiltRing p R) (ha : IsTiltGenerator p R a) :
    IsArcCoverFamilyCharP (fun i => (tiltArcTarget p R S a i : Type u)) (tiltArcArrow p f a) := by
  sorry -- 完全化後、単元は局所化、階数 0 の非単元は arcValuation_extendField。階数 1 の非零非単元は
        -- arcValuation_completeAt、零は V 自身を untilt。hf と G-A6-3 で得た拡大を tiltMap で戻す

/-- A→T 上で a の像について導来完備化した H⁰ と、その標準射。 -/
def arcPrincipalH0 {A : CommRingCat.{u}} (a : A) (T : Under A) : CommRingCat.{u} := by
  letI := principalCompletionCommRing T.right (T.hom.hom a)
  exact CommRingCat.of (PrincipalCompletionH0 T.right (T.hom.hom a))

def arcPrincipalUnit {A : CommRingCat.{u}} (a : A) (T : Under A) : T.right ⟶ arcPrincipalH0 a T := by
  letI := principalCompletionCommRing T.right (T.hom.hom a)
  exact CommRingCat.ofHom (principalCompletionUnitRingHom T.right (T.hom.hom a))

def arcPrincipalFunctor {A : CommRingCat.{u}} (a : A) : Under A ⥤ CommRingCat.{u} where
  obj := arcPrincipalH0 a
  map {T U} f := by
    letI := principalCompletionCommRing T.right (T.hom.hom a)
    letI := principalCompletionCommRing U.right (U.hom.hom a)
    exact CommRingCat.ofHom (R := PrincipalCompletionH0 T.right (T.hom.hom a))
      (S := arcPrincipalH0 a U) (Classical.choose
    (principalCompletion_existsUnique_ringHom T.right (T.hom.hom a) (arcPrincipalH0 a U)
      (f.right ≫ arcPrincipalUnit a U).hom
      (by sorry))) -- U の完備化は a の像について完備。Under.w で T の作用に制限
  map_id := by sorry -- 標準射上で一致する延長の一意性
  map_comp := by sorry -- 合成も同じ標準射を延長する

/-- 概要：G-A6-7：導来 a 進完備化（a := d mod p）は完全列を保ち、a が可逆な項を殺す；Čech 複体 of {R^♭ → S^♭, R^♭ → R^♭[1/a]} の各項の分解で R^♭[1/a] が混じる項の完備化は零。
方針：HA/DerivedCompletion（2b 後の名前）。
規約：—
使われ方：Prop 8.10。 -/
theorem cech_completion_kills_inverted [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) (hA : (p : A) = 0) (hB : (p : B) = 0)
    [PerfectRing A p] [PerfectRing B p]
    (hex : AugmentedRingCechExact ((Arrow.mk (CommRingCat.ofHom
      (f.prod (algebraMap A (Localization.Away a))))).augmentedCechConerve)) :
    (let X := (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve
     AugmentedRingCechExact ((CosimplicialObject.Augmented.whiskeringObj _ _
       (arcPrincipalFunctor (A := CommRingCat.of A) a)).obj (augmentedOverBase X))) ∧
    (∀ (T : Under (CommRingCat.of A)), IsUnit (T.hom.hom a) →
      ∀ n : ℤ, IsZero ((koszulCompletionComplex T.right
        (fun _ : Fin 1 => T.hom.hom a)).homology n)) := by
  sorry -- 完全な増大複体を導来完備化する。有限積分解の混合項では a が可逆で Koszul 塔は零。
        -- 完全 F_p 代数のテンソル冪は被約で a 冪ねじれは a で消え、各項の完備化は H⁰ に集中する

/-! ## Prop 8.10 -/

/-- 概要：Prop 8.10 前半（affine）：単射 arc 被覆 R → S（perfectoid）の完備 Čech 複体 0 → R → S → S ⊗̂_R S → ⋯ は完全。
方針：tilt（G-A6-4・5）、`tilt_arcCoverFamily`、`cech_exact_of_arcCover_perfect`、`cech_completion_kills_inverted`。
規約：—
使われ方：`structurePresheaf_isArcSheaf`。 -/
theorem cech_exact_of_arcCover_perfectoid {R S : Type u} [CommRing R] [CommRing S]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p) (f : R →+* S)
    (hf : IsArcCoverFamily p (fun _ : PUnit.{u + 1} => S) (fun _ => f)) :
    AugmentedRingCechExact ((CosimplicialObject.Augmented.whiskeringObj _ _ (ringCompletionFunctor p)).obj
      (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve) := by
  sorry -- 相対テンソル冪の tilt は completedTensor_tilt。一点族 R♭ → S♭ × R♭[1/a] に
        -- cech_exact_of_arcCover_perfect、G-A6-7、G-A6-5。零の積環は別扱いで、完備な R,S は単位で戻す

open SerrePositivity.EInfinity

/-- site の opposite を戻し、包含に沿って環とその射を読む。 -/
def arcPerfdRingFunctor : ((AffPerfd p κ)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  unopUnop (AffPerfd p κ) ⋙ affPerfdInclusion p κ ⋙ affComplForget p κ

/-- ℤ の標準射を備えた環値の図式。 -/
def arcIntegerAlgebras : ((AffPerfd p κ)ᵒᵖ)ᵒᵖ ⥤ Under (CommRingCat.of ArcZ.{u}) where
  obj T := Under.mk (CommRingCat.ofHom
    ((Int.castRingHom ((arcPerfdRingFunctor p κ).obj T)).comp ULift.ringEquiv.toRingHom))
  map f := Under.homMk ((arcPerfdRingFunctor p κ).map f) (by sorry) -- 整数上の構造射との可換性
  map_id := by sorry -- 環への忘却は忠実
  map_comp := by sorry -- 同じく環の射の合成で判定

def structurePresheaf : Sheaves.Presheaf (AffPerfd p κ)ᵒᵖ (E.CAlg ArcZ.{u}) :=
  ringPresheafToCAlg (E := E) ArcZ.{u} (arcIntegerAlgebras p κ)

def homPresheaf (T : Type u) [CommRing T] : ((AffPerfd p κ)ᵒᵖ)ᵒᵖ ⥤ Type u where
  obj D := T →+* (arcPerfdRingFunctor p κ).obj D
  map f := ↾fun l => ((arcPerfdRingFunctor p κ).map f).hom.comp l
  map_id := by sorry -- 環準同型の恒等射
  map_comp := by sorry -- 環準同型の合成の結合則

/-- 集合値の通常の前層を nerve 値に読み、S1 の有限積条件に渡す。 -/
def arcSetNerve {C : Type u} [SmallCategory C] (F : Cᵒᵖ ⥤ Type u) :
    Sheaves.Presheaf C (nerve (Type u)) where
  app _ := ↾fun x => (F.mapComposableArrows _).obj x.down
  naturality := by sorry -- 単体射での制限と F による後合成は可換

/-- ArcSite の PreservesFiniteRingProducts を包含に沿って制限した条件。
環側の錐が AffCompl で積かどうかを調べ、F は AffPerfd の対象と射にだけ適用する。
G-A6-12 により有限積（空積も含む）は AffPerfd にあり、この検査でその全てを覆う。 -/
def PreservesFiniteRingProductsOnPerfd {E : SSet.{u + 1}} [Quasicategory E]
    (F : Sheaves.Presheaf (AffPerfd p κ)ᵒᵖ E) : Prop :=
  ∀ (ι : Type u) [Finite ι] (B : ι → AffPerfd p κ) (c : Fan B),
    Nonempty (IsLimit ((affPerfdInclusion p κ).mapCone c)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone ((opOp (AffPerfd p κ)).mapCone c))).postcomp F)

theorem structurePresheaf_preservesFiniteRingProducts
    [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    PreservesFiniteRingProductsOnPerfd p κ (structurePresheaf (E := E) p κ) := by
  sorry -- G-A6-12 と離散環の有限積は CAlg_ℤ の積であること（零環は終対象）

theorem homPresheaf_preservesFiniteRingProducts
    [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] (T : Type u) [CommRing T] :
    PreservesFiniteRingProductsOnPerfd p κ (arcSetNerve (homPresheaf p κ T)) := by
  sorry -- 有限積環への射は各射影との合成の族に一意に対応する

/-- 概要：Prop 8.10 前半：O（CAlg_ℤ 値、R ↦ R。W9-II-22）は affPerfd_κ 上の arc 層（Čech 層、D-S1）。
方針：S1 の生成系の補題と `isSheaf_arc_iff_cech`、有限族を R → ∏R_i に置き換え、`cech_exact_of_arcCover_perfectoid`（離散な余単体的環の Tot は Čech 複体）。
規約：`IsSheaf (arcTopologyPerfd p κ) (structurePresheaf …)`。
使われ方：Cor 8.11 の affine 版、Cor 8.12。 -/
theorem structurePresheaf_isArcSheaf [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)] :
    Sheaves.IsSheaf (arcTopologyPerfd p κ) (structurePresheaf (E := E) p κ) := by
  have hbound := hκ.out
  sorry -- isSheaf_arc_iff_cech の二つの生成系を cover-dense な包含に沿い制限する。
        -- G-A6-12 と G-A6-4 で積・相対 Čech 項は Perfd にある。積は上の補題、
        -- 一点被覆は cech_exact_of_arcCover_perfectoid と CAlg_ℤ の忘却による極限判定

/-- 概要：Prop 8.10 後半（affine T）：R ↦ Hom(T, R) は affPerfd_κ 上の集合の arc 層。
方針：H⁰ の等化子 R = eq(S ⇉ S ⊗̂_R S) に Hom(T, −) を当てる。
規約：Mathlib の `Presieve.IsSheaf`（集合値）。
使われ方：Cor 8.12 の F_T。 -/
theorem homPresheaf_isArcSheaf [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    (T : Type u) [CommRing T] :
    Presieve.IsSheaf (arcTopologyPerfd p κ) (homPresheaf p κ T) := by
  have hbound := hκ.out
  sorry -- 一点被覆の H⁰ の等化子に Hom(T,−) を適用し、有限射影族には上の積保存を使う

/-- affPerfd_κ/S の環側。S は p 完備でよく、各対象が S→T を持つ。 -/
abbrev ArcPerfdUnder (S : AffCompl p κ) := StructuredArrow S (affPerfdInclusion p κ)

/-- slice の被覆は、S からの射を忘れた標的上の arc 被覆。 -/
def arcPerfdSliceTopology (S : AffCompl p κ) : GrothendieckTopology (ArcPerfdUnder p κ S)ᵒᵖ where
  sieves X := {Q | Q.functorPushforward (StructuredArrow.proj S (affPerfdInclusion p κ)).op ∈
    arcTopologyPerfd p κ (Opposite.op X.unop.right)}
  top_mem' := by sorry -- 各標的上の恒等射を持つ
  pullback_stable' := by sorry -- T→T′ には S→T→T′ を指定して一意に引き戻す
  transitive' := by sorry -- 同じ射の持ち上げで標的の位相の局所性に帰着

/-- slice 上の O を R→S→T で CAlg_R に持ち上げる。 -/
def arcSliceAlgebras (R : Type u) [CommRing R] (S : AffCompl p κ)
    (r : CommRingCat.of R ⟶ (affComplForget p κ).obj S) : ArcPerfdUnder p κ S ⥤ A_R R where
  obj X := Under.mk (r ≫ (affComplForget p κ).map X.hom)
  map f := Under.homMk ((affComplForget p κ).map ((affPerfdInclusion p κ).map f.right))
    (by sorry) -- StructuredArrow.w と r の前合成
  map_id := by sorry -- 忘却後は恒等射
  map_comp := by sorry -- 忘却後は環の射の合成

/-- 概要：Cor 8.11 の affine 版（記録、D55）：S_perfd ≃ RΓ_arc(affPerfd_κ/S, O)（slice site の上の β の RΓ）。
方針：O は層なので RΓ = lim（S2）、lim_{Perfd_{S/}} O = S_perfd（Prop 8.5、A5）。
規約：fSch・affCompl_κ 上の RΓ との比較はしない。
使われ方：記録。 -/
theorem perfectoidization_eq_arcCohomology
    [Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (hsize : Cardinal.mk R ≤ κ)
    (S : AffCompl p κ) (r : CommRingCat.of R ⟶ (affComplForget p κ).obj S)
    (hJ : Sheafification (arcPerfdSliceTopology p κ S) (E.CAlg R))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg R)) :
    let O := ringPresheafToCAlg (E := E) R
      (unopUnop (ArcPerfdUnder p κ S) ⋙ arcSliceAlgebras p κ R S r)
    ∃ e : SSet.Edge (perfectoidizationCone (E := E) p R (Under.mk r)).vertex
      (derivedGlobalSections (arcPerfdSliceTopology p κ S) hJ hE O),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated := by
  sorry -- S は p 完備なので A5 の指定錐の頂点は S_perfd。perfectoidization_isLimit の κ 版と
        -- structurePresheaf_isArcSheaf の slice への制限、S2 の derivedGlobalSections_of_isSheaf で両極限を比較

end SerrePositivity.BhattScholze.Perfectoidization.Derived
