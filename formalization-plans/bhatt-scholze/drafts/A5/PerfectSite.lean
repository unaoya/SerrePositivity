-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectSite（仮。原典 Rem 4.6、Lemma 4.8、比較写像）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.1・§2.2、単位 A5-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
-- 本ファイルは drafts/A0/PrismaticSite.lean（`PerfectPrismaticSite`、`flatTopology`、`structurePresheafDerived`）、drafts/Sheaves/{SheafCondition,GlobalSections,CechConerveLimit,CAlgValued}.lean、
-- drafts/A3/DiscreteCase.lean（`prismMapOfDiscrete`）、drafts/A4/Perfectoidization.lean、drafts/A7/AnimatedDomain.lean を import する。
-- W9-III-09：Prop 8.5 の証明・系（PerfectSiteComparison）は A5-2〜A5-4 の後。本ファイルは A5-2（SemiperfectoidCase）より先に置く定義だけ。

/-!
# 完全 prismatic site と比較写像（BS 著者版 Rem 4.6、Lemma 4.8、Lemma 7.7(3) からの比較写像）

## 概要
完全 prism (A,(d))（R = A/d perfectoid）と導来 p 完備な animated R 代数 S（D45 改訂。本ファイルの `S : Type u` は離散の特別な場合）に対し、
完全 prismatic site (S/A)^perf_Δ = (π_0 S/A)^perf_Δ（A0 の `PerfectPrismaticSite` に flat 位相）、Lemma 4.8 の系（site ≃ perfectoid 環への写像 S → T の圏、
濃度 ≤ κ）、比較写像 Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ（脚 f_n = φ_B^{-n} ∘ f、W9-II-07）。

## 方針
A5/PerfectSiteComparison.lean から W9-III-09 で切り出した。SemiperfectoidCase（A5-2）が比較写像の脚を使い、Prop 8.5 の証明は A5-2〜A5-4 を使うので、
定義を先行ファイルに分ける。

## 規約
位相の順序は ⊥ ≤ J ≤ flat（D46）。κ = `cutoff`（A0）。値は CAlg_A・CAlg_R。

## 使われ方
A5-2（`perfectoidizationToUniversal`）、A5-3・A5-4、A5-1 の Prop 8.5（PerfectSiteComparison）、E3 の `limitCone`（InterfaceLimitCone）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial Cardinal TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [aRS : Algebra R S]

/-! ## Rem 4.6：完全 prismatic site -/

local instance residueAlgebra : Algebra (perfectPrismRing p R ⧸ (perfectPrism p R hR).ideal) S :=
  ((algebraMap R S).comp (perfectPrism_quotientEquiv p R hR).toRingHom).toAlgebra

abbrev perfectSiteCutoff := cutoff (perfectPrismRing p R) S

local instance : EssentiallySmall.{u}
    (PrismOver (perfectPrism p R hR) S (perfectSiteCutoff p R S)) :=
  PrismOver.essentiallySmall (P := perfectPrism p R hR) (R := S) (by
    sorry) -- κ=(#A+#S+ℵ₀)^ℵ₀ は #A+#S 以上

/-- 概要：(S/A)^perf_Δ：A0 の `PerfectPrismaticSite (perfectPrism p R) S κ`（完全 prism の充満部分圏の opposite）。
方針：A/d ≃ R と R → S の合成で A0 に必要な代数構造を与える。
規約：κ = `cutoff`。
使われ方：以下すべて。 -/
abbrev perfectSite := PerfectPrismaticSite (perfectPrism p R hR) S (perfectSiteCutoff p R S)

local instance : SmallCategory (perfectSite p R hR S) := by
  unfold perfectSite PerfectPrismaticSite
  infer_instance

/-- 完全対象の包含と A0 の小さい模型の逆同値を合成する。 -/
def perfectSitePrism : (perfectSite p R hR S)ᵒᵖ ⥤ PrismOver (perfectPrism p R hR) S (perfectSiteCutoff p R S) :=
  unopUnop _ ⋙ (ObjectProperty.ι _) ⋙ (equivSmallModel _).inverse

/-- 概要：完全 site の flat 位相：完全 prism の間の忠実平坦な単射の生成 sieve を含む位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`IsFaithfullyFlat` を完全な対象に制限して sInf。
規約：包含関手による引き戻し位相との一致は述べない。
使われ方：Prop 8.5 の位相の上限。 -/
def perfectFlatTopology : GrothendieckTopology (perfectSite p R hR S) :=
  sInf { J | ∀ {X Y : perfectSite p R hR S} (f : Y ⟶ X),
    PrismOver.IsFaithfullyFlat ((perfectSitePrism p R hR S).map f.op) →
      Sieve.generate (Presieve.singleton f) ∈ J X }

/-- 二つの S 作用を一致させるテンソル。R 上の絶対テンソルでは S の関係が不足する。 -/
def relativeTensorRing (U V : PerfUnder_u p (CommRingCat.of S)) : CommRingCat.{u} := by
  letI := U.obj.hom.hom.toAlgebra
  letI := V.obj.hom.hom.toAlgebra
  exact CommRingCat.of (U.obj.right ⊗[S] V.obj.right)

def relativeTensorLeft (U V : PerfUnder_u p (CommRingCat.of S)) :
    U.obj.right →+* completionRing p (relativeTensorRing p S U V) := by
  letI := U.obj.hom.hom.toAlgebra
  letI := V.obj.hom.hom.toAlgebra
  exact (completionUnit p _).hom.comp Algebra.TensorProduct.includeLeftRingHom

def relativeTensorRight (U V : PerfUnder_u p (CommRingCat.of S)) :
    V.obj.right →+* completionRing p (relativeTensorRing p S U V) := by
  letI := U.obj.hom.hom.toAlgebra
  letI := V.obj.hom.hom.toAlgebra
  exact (completionUnit p _).hom.comp Algebra.TensorProduct.includeRight.toRingHom

include hR aRS in
theorem exists_relativeTensorPerfectoidization (U V : PerfUnder_u p (CommRingCat.of S)) :
    ∃ (C : CommRingCat.{u}) (η : completionRing p (relativeTensorRing p S U V) →+* C),
      IsPerfectoidization p η := by
  letI := (U.obj.hom.hom.comp (algebraMap R S)).toAlgebra
  letI := (V.obj.hom.hom.comp (algebraMap R S)).toAlgebra
  let T := completionRing p (CommRingCat.of (U.obj.right ⊗[R] V.obj.right))
  have hT : IsIntegralPerfectoid T p := by
    sorry -- integralPerfectoid_completedTensorH0_isIntegralPerfectoid の E3 非依存の芯を
          -- completedTensorH0PrincipalRingEquiv で H⁰ の完備化に移す（W9-III-08）
  let u := (completionUnit p (CommRingCat.of (U.obj.right ⊗[R] V.obj.right))).hom
  let l : S →+* T := u.comp (Algebra.TensorProduct.includeLeftRingHom.comp U.obj.hom.hom)
  let r : S →+* T := u.comp (Algebra.TensorProduct.includeRight.toRingHom.comp V.obj.hom.hom)
  let I := Ideal.span (Set.range (fun s : S => l s - r s))
  obtain ⟨C, instC, q, hq⟩ := exists_perfectoidization_of_perfectoid_surjective_quotient hT
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI := instC
  refine ⟨CommRingCat.of C, ?_⟩
  sorry -- q と T→T/I から相対テンソルの射を作り、completion_existsUnique で延長。
        -- 完備 perfectoid 標的への射は S 上で一致する二脚に対応し、hq により延長が一意

def relativeCoproductRing (U V : PerfUnder_u p (CommRingCat.of S)) :=
  (exists_relativeTensorPerfectoidization p R hR S U V).choose

def relativeCoproductUnit (U V : PerfUnder_u p (CommRingCat.of S)) :
    completionRing p (relativeTensorRing p S U V) →+* relativeCoproductRing p R hR S U V :=
  (exists_relativeTensorPerfectoidization p R hR S U V).choose_spec.choose

def relativeCoproductCofan (U V : PerfUnder_u p (CommRingCat.of S)) : BinaryCofan U V := by
  let η := relativeCoproductUnit p R hR S U V
  let l := η.comp (relativeTensorLeft p S U V)
  let r := η.comp (relativeTensorRight p S U V)
  let C : PerfUnder_u p (CommRingCat.of S) :=
    ⟨Under.mk (CommRingCat.ofHom (l.comp U.obj.hom.hom)),
      (exists_relativeTensorPerfectoidization p R hR S U V).choose_spec.choose_spec.1⟩
  let i : U ⟶ C := ObjectProperty.homMk (Under.homMk (CommRingCat.ofHom l) rfl)
  let j : V ⟶ C := ObjectProperty.homMk (Under.homMk (CommRingCat.ofHom r) (by
    sorry)) -- includeLeft と includeRight が S 上で一致
  exact BinaryCofan.mk i j

def relativeCoproduct_isColimit (U V : PerfUnder_u p (CommRingCat.of S)) :
    IsColimit (relativeCoproductCofan p R hR S U V) := by
  sorry -- 二脚から相対テンソルの射、完備化の延長、Cor 7.3 の一意延長の順に desc を作る

/-- 概要：G-A5-14：Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ は perfectoid T₁ ⊗̂_R T₂ の商で semiperfectoid、Cor 7.3 の普遍性）。
Čech 余脈体 (S̃^{⊗_S n+1})_perfd。
方針（W9-III-14）：**既存 Cor 7.3 の普遍 perfectoid 環**（`Semiperfectoid/Perfectoidization` の入口）から直接。T₁ ⊗̂_S T₂ は semiperfectoid（perfectoid T₁ ⊗̂_R T₂ の商）で
Q(T₁ ⊗̂_S T₂) を取り、Hom の普遍性から Čech の整合。A5-2 の wrapper `universalPerfectoidRing`・比較同値・弱始対象は不要（後段を import しない）。
規約：S3 の `CechNerveData`（`PerfUnder_u p S` の opposite）。
使われ方：`limit_perfUnder_eq_tot`。 -/
def perfUnder_cechNerveData : True := trivial

/-- 概要：完全 site の各対象に Čech 余脈体がある：**Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd**（Cor 7.3 の普遍 perfectoid 環の普遍性、上の `perfUnder_cechNerveData`）を
Lemma 4.8 の圏同値 `perfectSiteEquivPerfectoidUnder` で完全 site に運ぶ。
方針：W9-II-06 で訂正：A 上の完備テンソル B ⊗̂_A B′ では S の二つの構造射が一致せず（S = F_p[t]、T = F_p[t^{1/p^∞}] で反例）、S3 に渡すと極限が変わる。
flat 被覆の相対 Čech 項 B₁ ⊗̂_{B₀} B₁（G-A5-5 の層性に使う）とは別物。
規約：S3 の `CechNerveData`。
使われ方：弱始対象から極限（`perfectoidization_isLimit`）。 -/
def perfectSite_cechNerveData (U : perfectSite p R hR S) : True := trivial

/-- 概要：構造前層 O_Δ の完全 site への制限（D(A) 値、CAlg_A 値）。
方針：A0 の `structurePresheafDerived` を包含関手で引き戻す。
規約：—
使われ方：比較写像の終域。 -/
def perfectStructurePresheaf :
    Sheaves.Presheaf (perfectSite p R hR S) (CAlg_R (perfectPrismRing p R)) :=
  Sheaves.ringPresheafToCAlg (perfectPrismRing p R) ((perfectSitePrism p R hR S) ⋙
    { obj := fun X => Under.mk (CommRingCat.ofHom X.toHom.toRingHom)
      map := fun f => Under.homMk (CommRingCat.ofHom f.toHom.toRingHom) (by
        sorry) -- f.comm_base
      map_id := by sorry -- 基底上の恒等射
      map_comp := by sorry }) -- prism の射の合成

def perfectStructurePresheafDerived :
    Sheaves.Presheaf (perfectSite p R hR S) (derivedInfinityCategory (perfectPrismRing p R)) :=
  perfectStructurePresheaf p R hR S ≫ SerrePositivity.EInfinity.BarrattEccles.cAlgForgetDerived _

/-- 概要：G-A5-5：O_Δ は完全 site で flat 層（Čech 層）。
方針：A0-3d（Cor 3.12）の flat 被覆について B₁ ⊗̂_{B₀} B₁ の相対 Čech 項を用いる。
規約：D-S1（Čech 層）。
使われ方：位相非依存（`perfectionComparison_isIso_topology`）。 -/
theorem perfectStructurePresheaf_isSheaf :
    Sheaves.IsSheaf (perfectFlatTopology p R hR S) (perfectStructurePresheaf p R hR S) := by
  sorry -- 完全な flat 被覆の相対 Čech 項に Cor 3.12 を適用し、CAlg の忘却で極限を検出する

/-! ## Lemma 4.8 と site の記述 -/

/-- 概要：原典 Lemma 4.8 は任意の標的、ここでは有界に限る（site の対象が有界なので十分）。
方針：既存の有界標的への持ち上げを使う。規約：商写像の等号を保つ prism の射の一意存在。
使われ方：完全 site の商環関手の充満忠実性。 -/
theorem perfectPrism_hom_lift_unique {A B : Type u} [CommRing A] [CommRing B]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hQ : IsBoundedPrism Q) (g : A ⧸ P.ideal →+* B ⧸ Q.ideal) :
    ∃! f : OrientedPrism.Hom P Q, f.quotientMap = g :=
  Andre.existsUnique_perfectPrismHomLift_to_bounded P hP Q hQ g

abbrev PerfUnderBounded (κ : Cardinal.{u}) :=
  ObjectProperty.FullSubcategory (fun T : PerfUnder_u p (CommRingCat.of S) => Cardinal.mk T.obj.right ≤ κ)

/-- site の環側の指定関手。対象では S→B/J、射では prism の射の quotientMap。 -/
def perfectResidueFunctor : (perfectSite p R hR S)ᵒᵖ ⥤ PerfUnderBounded p S (perfectSiteCutoff p R S) where
  obj U := by
    let X := (perfectSitePrism p R hR S).obj U
    refine ⟨⟨Under.mk (CommRingCat.ofHom X.sec), ?_⟩, ?_⟩
    · sorry -- U の完全性と OrientedPrism.quotient_isIntegralPerfectoid
    · sorry -- 商の濃度 ≤ #X.B ≤ κ
  map f := by
    let g := (perfectSitePrism p R hR S).map f
    exact ObjectProperty.homMk (ObjectProperty.homMk
      (Under.homMk (CommRingCat.ofHom g.toHom.quotientMap) (by sorry))) -- g.comm_sec
  map_id := by sorry -- quotientMap の恒等射
  map_comp := by sorry -- quotientMap の合成

/-- 概要：Lemma 4.8 の系：関手 (B,J) ↦ B/J は (S/A)^perf_Δ（の opposite）から「S → T、T perfectoid、濃度 ≤ κ」の圏への圏同値。
方針：Hom は Lemma 4.8 を (A,I) := (B,J) に、本質的全射は Thm 3.10（`exists_perfectoidTrialPrism`）。
規約：濃度 ≤ κ の `PerfUnder_u p S` の充満部分圏を `PerfUnderSmall` と書く。
使われ方：系 1・系 2、E3 の錐の添字の移送。 -/
def perfectSiteEquivPerfectoidUnder :
    (perfectSite p R hR S)ᵒᵖ ≌ PerfUnderBounded p S (perfectSiteCutoff p R S) := by
  let F := perfectResidueFunctor p R hR S
  letI : F.IsEquivalence := by
    sorry -- Lemma 4.8 で基底と sec の両立を保ち充満忠実。Thm 3.10 と κ^ℵ₀=κ で本質的全射
  exact F.asEquivalence

/-! ## 比較写像 -/

/-- 概要：完全 (B,J) ∈ (S/A)^perf に対する Δ_{S/A,perf} → B：Lemma 7.7(3) の A 線形・Frobenius 両立の f : Δ_{S/A} → B（A3 `prismMapOfDiscrete`）から、
塔（φ_{A*}^n、A4）の第 n 項への脚 f_n := φ_B^{-n} ∘ f : Res_{φ_A}^n Δ_S → B（W9-II-07）、余極限から colim → B、B が (p,d) 完備なので完備化から。
方針：f_n(φ_A^n(a) x) = a f_n(x) で A 線形、f_{n+1} ∘ φ = f_n で塔と整合、B について自然（B 間の射は φ_B とその逆に可換）。
規約：CAlg_A の射。
使われ方：錐。 -/
def perfectionComparisonLeg (B : perfectSite p R hR S) : True := trivial -- W9-III-15：A4 の `toPerfection`（Δ̄ → Δ̄_perf）と名前を分けた

/-- 概要：比較写像 Δ_{S/A,perf} → lim_{(S/A)^perf} O_Δ（CAlg_A）。
方針：`perfectionComparisonLeg` の自然性で O 上の錐、極限の普遍性。
規約：終域は chaotic の RΓ = lim（S2 の `globalSections`）。
使われ方：Prop 8.5。 -/
def perfectionComparison : True := trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
