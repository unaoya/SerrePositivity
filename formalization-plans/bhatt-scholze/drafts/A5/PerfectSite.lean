-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Descent.PerfectSite（仮。原典 Rem 4.6、Lemma 4.8、比較写像）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.1・§2.2、単位 A5-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
-- 本ファイルは drafts/A0/PrismaticSite.lean（`PerfectPrismaticSite`、`flatTopology`、`structurePresheafDerived`）、drafts/Sheaves/{SheafCondition,GlobalSections,CechConerveLimit,CAlgValued}.lean、
-- drafts/A3/DiscreteCase.lean（`prismMapOfDiscrete`）、drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A7/AnimatedDomain.lean を import する。
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

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

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
  PrismOver.essentiallySmall

/-- 概要：(S/A)^perf_Δ：A0 の `PerfectPrismaticSite (perfectPrism p R) S κ`（完全 prism の充満部分圏の opposite）。
方針：A/d ≃ R と R → S の合成で A0 に必要な代数構造を与える。
規約：κ = `cutoff`。
使われ方：以下すべて。 -/
abbrev perfectSite (hR : IsIntegralPerfectoid R p := by assumption) : Type u :=
  PerfectPrismaticSite (perfectPrism p R hR) S (perfectSiteCutoff p R S)

instance : SmallCategory (perfectSite p R S hR) := by
  unfold perfectSite PerfectPrismaticSite
  infer_instance

/-- 完全対象の包含と A0 の小さい模型の逆同値を合成する。 -/
def perfectSitePrism : (perfectSite p R S hR)ᵒᵖ ⥤ PrismOver (perfectPrism p R hR) S (perfectSiteCutoff p R S) :=
  unopUnop _ ⋙ (ObjectProperty.ι _) ⋙ (equivSmallModel _).inverse

/-- 概要：完全 site の flat 位相：完全 prism の間の一つの (p,d) 完全忠実平坦射が生成する sieve を含む位相の sInf（A0 の `flatTopology` と同じ形）。
方針：`IsFaithfullyFlat` を完全な対象に制限して sInf。
規約：包含関手による引き戻し位相との一致は述べない。
使われ方：Prop 8.5 の位相の上限。 -/
def perfectFlatTopology (hR : IsIntegralPerfectoid R p := by assumption) : GrothendieckTopology (perfectSite p R S hR) :=
  sInf { J | ∀ {X Y : perfectSite p R S hR} (f : Y ⟶ X),
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

/-- 第 n 項は S 上の U の n+1 個の余積。弱始性は余積の構成に使わない。 -/
def perfPower (U : PerfUnder_u p (CommRingCat.of S)) (n : ℕ) : PerfUnder_u p (CommRingCat.of S) :=
  Nat.rec U (fun _ W => (relativeCoproductCofan p R hR S W U).pt) n

def perfPowerInj (U : PerfUnder_u p (CommRingCat.of S)) (n : ℕ) :
    Fin (n + 1) → (U ⟶ perfPower p R hR S U n) :=
  Nat.rec (motive := fun j => Fin (j + 1) → (U ⟶ perfPower p R hR S U j))
    (fun _ => 𝟙 U)
    (fun j ih i => Fin.lastCases
      (relativeCoproductCofan p R hR S (perfPower p R hR S U j) U).inr
      (fun k => ih k ≫ (relativeCoproductCofan p R hR S (perfPower p R hR S U j) U).inl) i) n

def perfPowerIsColimit (U : PerfUnder_u p (CommRingCat.of S)) (n : ℕ) :
    IsColimit (Cofan.mk (perfPower p R hR S U n) (perfPowerInj p R hR S U n)) := by
  induction n with
  | zero => sorry -- 単項余積の脚は恒等射
  | succ n ih =>
    have h := relativeCoproduct_isColimit p R hR S (perfPower p R hR S U n) U
    sorry -- h の左右への降下と ih を合成し、n+2 本の指定脚で一意性を得る

def perfPowerCosimplicial (U : PerfUnder_u p (CommRingCat.of S)) :
    CosimplicialObject (PerfUnder_u p (CommRingCat.of S)) where
  obj n := perfPower p R hR S U n.len
  map {m n} θ := (perfPowerIsColimit p R hR S U m.len).desc
    (Cofan.mk _ (fun i : Fin (m.len+1) => perfPowerInj p R hR S U n.len (θ.toOrderHom i)))
  map_id := by sorry -- 恒等添字の余積射は恒等射
  map_comp := by sorry -- 各脚で添字写像の合成を確認

/-- 概要：G-A5-14：Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（T₁ ⊗̂_S T₂ は perfectoid T₁ ⊗̂_R T₂ の商で semiperfectoid、Cor 7.3 の普遍性）。
Čech 余脈体 (S̃^{⊗_S n+1})_perfd。
方針（W9-III-14）：**既存 Cor 7.3 の普遍 perfectoid 環**（`Semiperfectoid/Perfectoidization` の入口）から直接。T₁ ⊗̂_S T₂ は semiperfectoid（perfectoid T₁ ⊗̂_R T₂ の商）で
Q(T₁ ⊗̂_S T₂) を取り、Hom の普遍性から Čech の整合。A5-2 の wrapper `universalPerfectoidRing`・比較同値・弱始対象は不要（後段を import しない）。
規約：D3-02 の大きい版 `CechNerveDataLarge`。全 Perfd_{S/} の opposite で積を取る。
使われ方：`limit_perfUnder_eq_tot`。 -/
def perfUnder_cechNerveData (U : (PerfUnder_u p (CommRingCat.of S))ᵒᵖ) :
    Sheaves.CechNerveDataLarge U where
  obj := (perfPowerCosimplicial p R hR S U.unop).op
  proj n i := (perfPowerInj p R hR S U.unop n i).op
  isLimit n := by
    have hc := perfPowerIsColimit p R hR S U.unop n
    sorry -- 同じ標準脚の余積を opposite に移して Fan の極限を得る
  proj_map := by
    sorry -- 余積からの desc の第 i 脚への制限は第 θ(i) 脚、op で射影の等式

/-- 概要：構造前層 O_Δ の完全 site への制限（D(A) 値、CAlg_A 値）。
方針：A0 の `structurePresheafDerived` を包含関手で引き戻す。
規約：—
使われ方：比較写像の終域。 -/
def perfectStructurePresheaf :
    Sheaves.Presheaf (perfectSite p R S hR) (E.CAlg (perfectPrismRing p R)) :=
  Sheaves.ringPresheafToCAlg (E := E) (perfectPrismRing p R) ((perfectSitePrism p R hR S) ⋙
    { obj := fun X => Under.mk (CommRingCat.ofHom X.toHom.toRingHom)
      map := fun f => Under.homMk (CommRingCat.ofHom f.toHom.toRingHom) (by
        sorry) -- f.comm_base
      map_id := by sorry -- 基底上の恒等射
      map_comp := by sorry }) -- prism の射の合成

def perfectStructurePresheafDerived :
    Sheaves.Presheaf (perfectSite p R S hR) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory (perfectPrismRing p R)) :=
  perfectStructurePresheaf (E := E) p R hR S ≫ E.forget _

/-- 忘却後は A0 の structurePresheafDerived の完全対象への制限。 -/
def perfectStructureRestriction :
    let i : perfectSite p R S hR ⥤ PrismaticSite (perfectPrism p R hR) S (perfectSiteCutoff p R S) :=
      (ObjectProperty.ι _).op
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (perfectStructurePresheafDerived (E := E) p R hR S)
      ((SSet.uliftFunctor.{u+1,u}).map (nerveMap i.op) ≫
        structurePresheafDerived (perfectPrism p R hR) S (perfectSiteCutoff p R S)) := by
  sorry -- 同じ A 上の環の関手を離散埋め込みで送り、algebraEmbeddingForgetIso を前合成する

/-- 概要：G-A5-5：O_Δ は完全 site で flat 層（Čech 層）。
方針：A0-3d（Cor 3.12）の flat 被覆について B₁ ⊗̂_{B₀} B₁ の相対 Čech 項を用いる。
規約：D-S1（Čech 層）。
使われ方：位相非依存（`perfectionComparison_isIso_topology`）。 -/
theorem perfectStructurePresheaf_isSheaf :
    Sheaves.IsSheaf (perfectFlatTopology p R S hR) (perfectStructurePresheaf (E := E) p R hR S) := by
  sorry -- 完全な flat 被覆の相対 Čech 項に Cor 3.12 を適用し、CAlg の忘却で極限を検出する

/-! ## Lemma 4.8 と site の記述 -/

/-- 概要：原典 Lemma 4.8 は任意の標的、ここでは有界に限る（site の対象が有界なので十分）。
方針：既存の有界標的への持ち上げを使う。規約：商写像の等号を保つ prism の射の一意存在。
使われ方：完全 site の商環関手の充満忠実性。 -/
theorem perfectPrism_hom_lift_unique {A B : Type u} [CommRing A] [CommRing B]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (Q : OrientedPrism p B)
    (hQ : IsBoundedPrism Q) (g : A ⧸ P.ideal →+* B ⧸ Q.ideal) :
    ∃! f : OrientedPrism.Hom P Q, f.quotientMap = g :=
  _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded P hP Q hQ g

abbrev PerfUnderBounded (κ : Cardinal.{u}) :=
  ObjectProperty.FullSubcategory (fun T : PerfUnder_u p (CommRingCat.of S) => Cardinal.mk T.obj.right ≤ κ)

theorem perfPower_small (U : PerfUnderBounded p S (perfectSiteCutoff p R S)) (n : ℕ) :
    Cardinal.mk (perfPower p R hR S U.obj n).obj.right ≤ perfectSiteCutoff p R S := by
  sorry -- S 上の代数的テンソル、可算完備化と Cor 7.3 の商を反復する。κ^ℵ₀=κ

def boundedPerfPowers (U : PerfUnderBounded p S (perfectSiteCutoff p R S)) :
    CosimplicialObject (PerfUnderBounded p S (perfectSiteCutoff p R S)) where
  obj n := ⟨(perfPowerCosimplicial p R hR S U.obj).obj n, perfPower_small p R hR S U n.len⟩
  map θ := ObjectProperty.homMk ((perfPowerCosimplicial p R hR S U.obj).map θ)
  map_id := by sorry -- 充満部分圏の包含は忠実
  map_comp := by sorry -- 同じく包含で確認

/-- site の環側の指定関手。対象では S→B/J、射では prism の射の quotientMap。 -/
def perfectResidueFunctor : (perfectSite p R S hR)ᵒᵖ ⥤ PerfUnderBounded p S (perfectSiteCutoff p R S) where
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
規約：濃度 ≤ κ の充満部分圏は `PerfUnderBounded`。
使われ方：系 1・系 2、E3 の錐の添字の移送。 -/
def perfectSiteEquivPerfectoidUnder :
    (perfectSite p R S hR)ᵒᵖ ≌ PerfUnderBounded p S (perfectSiteCutoff p R S) := by
  let F := perfectResidueFunctor p R hR S
  letI : F.IsEquivalence := by
    sorry -- Lemma 4.8 で基底と sec の両立を保ち充満忠実。Thm 3.10 と κ^ℵ₀=κ で本質的全射
  exact F.asEquivalence

/-- 概要：完全 site の各対象に Čech 余脈体がある：**Perfd_{S/} の余積 (T₁ ⊗̂_S T₂)_perfd**（Cor 7.3 の普遍 perfectoid 環の普遍性、上の `perfUnder_cechNerveData`）を
Lemma 4.8 の圏同値 `perfectSiteEquivPerfectoidUnder` で完全 site に運ぶ。
方針：W9-II-06 で訂正：A 上の完備テンソル B ⊗̂_A B′ では S の二つの構造射が一致せず（S = F_p[t]、T = F_p[t^{1/p^∞}] で反例）、S3 に渡すと極限が変わる。
flat 被覆の相対 Čech 項 B₁ ⊗̂_{B₀} B₁（G-A5-5 の層性に使う）とは別物。
規約：S3 の `CechNerveData`。
使われ方：弱始対象から極限（`perfectoidization_isLimit`）。 -/
def perfectSite_cechNerveData (U : perfectSite p R S hR) : Sheaves.CechNerveData U := by
  let E := perfectSiteEquivPerfectoidUnder p R hR S
  let T := E.functor.obj (Opposite.op U)
  let X := boundedPerfPowers p R hR S T
  let proj (n : ℕ) (i : Fin (n+1)) : (E.inverse.obj (X.obj ⦋n⦌)).unop ⟶ U :=
    ((E.unitIso.app (Opposite.op U)).hom ≫
      E.inverse.map (ObjectProperty.homMk (perfPowerInj p R hR S T.obj n i))).unop
  exact {
    obj := (X ⋙ E.inverse).leftOp
    proj := proj
    isLimit := fun n => by
      have hc := perfPowerIsColimit p R hR S T.obj n
      sorry -- 有界充満部分圏での同じ余積を E の逆で送り、opposite で指定射影の積を得る
    proj_map := by sorry -- perfPowerCosimplicial の desc は第 i 脚を第 θ(i) 脚へ送る
  }

/-! ## 比較写像 -/

open SerrePositivity.EInfinity.Perfectoidization

abbrev perfectTestAlgebra (U : (perfectSite p R S hR)ᵒᵖ) : A_R (perfectPrismRing p R) :=
  Under.mk (CommRingCat.ofHom ((perfectSitePrism p R hR S).obj U).toHom.toRingHom)

abbrev testValue (U : (perfectSite p R S hR)ᵒᵖ) :=
  (E.discrete (perfectPrismRing p R)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (perfectTestAlgebra p R hR S U))

def perfectStructureFiber (U : (perfectSite p R S hR)ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((perfectStructurePresheaf (E := E) p R hR S).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))) (testValue (E := E) p R hR S U) := by
  sorry -- ringPresheafToCAlg の評価は指定された離散 A 代数の埋め込み

abbrev baseRes := cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift

/-- 離散 A 代数の係数制限は構造射を φ_A と合成する。 -/
def discreteRestrictionIso (U : A_R (perfectPrismRing p R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((E.discrete (perfectPrismRing p R)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (CommRingCat.ofHom (U.hom.hom.comp (perfectPrism p R hR).deltaStructure.frobeniusLift)))))
      ((baseRes (E := E) p R hR).app _ ((E.discrete (perfectPrismRing p R)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))) := by
  sorry -- 要確認：ScalarRestriction へ。離散代数の埋め込みと cAlgRestrictScalars の標準比較

def testFrobenius (U : (perfectSite p R S hR)ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (testValue (E := E) p R hR S U) ((baseRes (E := E) p R hR).app _ (testValue (E := E) p R hR S U)) := by
  let X := (perfectSitePrism p R hR S).obj U
  let B := perfectTestAlgebra p R hR S U
  let twist : A_R (perfectPrismRing p R) := Under.mk
    (CommRingCat.ofHom (B.hom.hom.comp (perfectPrism p R hR).deltaStructure.frobeniusLift))
  let φ : B ⟶ twist := Under.homMk (CommRingCat.ofHom X.Q.deltaStructure.frobeniusLift)
    (by sorry) -- toHom は Frobenius と両立する
  haveI : IsIso φ := by sorry -- 完全な X.Q の Frobenius は全単射
  exact (algebraNerveIso _ (asIso φ)).map (E.discrete _) ≪≫ discreteRestrictionIso (E := E) p R hR B

abbrev deltaValue := (discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))

/-- 同じ錐の射影としての評価と Frobenius との整合。完全 site に制限した錐の極限性は仮定しない。 -/
structure PrismaticEvaluationData where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (perfectStructurePresheaf (E := E) p R hR S)
  vertexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (deltaValue (E := E) p R hR S) cone.vertex
  leg (U : (perfectSite p R S hR)ᵒᵖ) : SSet.Edge (deltaValue (E := E) p R hR S) (testValue (E := E) p R hR S U)
  is_projection (U : (perfectSite p R S hR)ᵒᵖ) :
    SSet.Truncated.HomotopyCategory.homMk (leg U).toTruncated =
      vertexIso.hom ≫ SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg cone (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))) ≫
        (perfectStructureFiber (E := E) p R hR S U).hom
  frobenius (U : (perfectSite p R S hR)ᵒᵖ) :
    SSet.Truncated.HomotopyCategory.homMk (leg U).toTruncated ≫ (testFrobenius (E := E) p R hR S U).hom =
      SSet.Truncated.HomotopyCategory.homMk (discreteDeltaFrobenius (E := E) p R hR (ofAlgebra R S)).toTruncated ≫
        (hoFunctor.map (baseRes (E := E) p R hR)).toFunctor.map (SSet.Truncated.HomotopyCategory.homMk (leg U).toTruncated)

/-- A0 の O_Δ を CAlg 値にして S2 の大域切断の B での射影を取る。
多項式分解では各段の射影を A2 の余極限で合わせる。animated 入力では対象を π₀S の site で読む。
A3 の離散性の仮定の下で H⁰ を取ると prismMapOfDiscrete に一致する。 -/
def prismaticEvaluation : PrismaticEvaluationData (E := E) p R hR S := by
  sorry -- A0/S2 の CAlg 値 RΓ の射影待ち（prismaticCohomologyCAlg が True のため）。
        -- Frobenius 両立は structurePresheafFrobenius の自然性

/-- Res^n B → B：完全標的の Frobenius の逆を正の係数制限で反復する。 -/
def inverseTestFrobenius (U : (perfectSite p R S hR)ᵒᵖ) (n : ℕ) :
    (HomotopyCategory.mk ((iterateRestriction (baseRes (E := E) p R hR) n).app _ (testValue (E := E) p R hR S U)) :
      hoFunctor.obj (E.CAlg (perfectPrismRing p R))) ⟶ HomotopyCategory.mk (testValue (E := E) p R hR S U) := by
  induction n with
  | zero => exact 𝟙 _
  | succ n ih =>
    exact (hoFunctor.map (iterateRestriction (baseRes (E := E) p R hR) n)).toFunctor.map
      (testFrobenius (E := E) p R hR S U).inv ≫ ih

def evaluationStage (U : (perfectSite p R S hR)ᵒᵖ) (n : ℕ) :=
  (hoFunctor.map (iterateRestriction (baseRes (E := E) p R hR) n)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk ((prismaticEvaluation (E := E) p R hR S).leg U).toTruncated) ≫
  inverseTestFrobenius (E := E) p R hR S U n

def towerToPerfection (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) (n : ℕ) :
    (HomotopyCategory.mk ((iterateRestriction (baseRes (E := E) p R hR) n).app _ (deltaValue (E := E) p R hR S)) :
      hoFunctor.obj (E.CAlg (perfectPrismRing p R))) ⟶ HomotopyCategory.mk (prismaticPerfection (E := E) p R hR S hS) := by
  let c := (directTowerColimit (E := E) p R hR (ofAlgebra R S)).1
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n))
  exact eqToHom (by sorry) ≫ SSet.Truncated.HomotopyCategory.homMk l.toTruncated ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (prismCAlgCompletionUnit (E := E) (p := p) (perfectPrism p R hR)) c.vertex
    -- restrictionSequence の第 n 頂点は Resⁿ Δ_S

/-- 一つの整合した錐を選び、全試験対象と全段で脚を指定する。 -/
structure PerfectionEvaluationData (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) where
  cone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (perfectStructurePresheaf (E := E) p R hR S)
  vertexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (prismaticPerfection (E := E) p R hR S hS) cone.vertex
  leg (U : (perfectSite p R S hR)ᵒᵖ) : SSet.Edge (prismaticPerfection (E := E) p R hR S hS) (testValue (E := E) p R hR S U)
  is_projection (U : (perfectSite p R S hR)ᵒᵖ) :
    vertexIso.hom ≫ SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg cone (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))) ≫
      (perfectStructureFiber (E := E) p R hR S U).hom = SSet.Truncated.HomotopyCategory.homMk (leg U).toTruncated
  stage (U : (perfectSite p R S hR)ᵒᵖ) (n : ℕ) :
    towerToPerfection (E := E) p R hR S hS n ≫ SSet.Truncated.HomotopyCategory.homMk (leg U).toTruncated =
      evaluationStage (E := E) p R hR S U n

def perfectionComparisonCone (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    PerfectionEvaluationData (E := E) p R hR S hS := by
  sorry -- prismaticEvaluation の錐と φ_B の逆から、試験対象について自然な塔の余錐を作る。
        -- 余極限の普遍性、B の (p,d) 完備性による延長を関手の段で適用する

/-- 第 n 段で φ_B^{-n} ∘ Resⁿ(f) を誘導する、同じ錐の指定された脚。 -/
def perfectionComparisonLeg (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (U : (perfectSite p R S hR)ᵒᵖ) :
    { e : SSet.Edge (prismaticPerfection (E := E) p R hR S hS) (testValue (E := E) p R hR S U) //
      ∀ n, towerToPerfection (E := E) p R hR S hS n ≫ SSet.Truncated.HomotopyCategory.homMk e.toTruncated =
        evaluationStage (E := E) p R hR S U n } :=
  let c := perfectionComparisonCone (E := E) p R hR S hS
  ⟨c.leg U, c.stage U⟩

/-- 小さい模型上の構造前層の極限。 -/
theorem perfectStructure_hasLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (perfectStructurePresheaf (E := E) p R hR S) :=
  Sheaves.hasLimit_presheaf (by sorry) _ -- G12：CAlg_A は presentable

/-- 比較の終域は chaotic 位相での O_Δ の大域切断。 -/
def perfectionComparison (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    (HomotopyCategory.mk (prismaticPerfection (E := E) p R hR S hS) : hoFunctor.obj (E.CAlg (perfectPrismRing p R))) ⟶
      HomotopyCategory.mk (Sheaves.globalSections (perfectStructurePresheaf (E := E) p R hR S) (perfectStructure_hasLimit (E := E) p R hR S)) := by
  let c := perfectionComparisonCone (E := E) p R hR S hS
  let l := Sheaves.globalSectionsCone (perfectStructurePresheaf (E := E) p R hR S) (perfectStructure_hasLimit (E := E) p R hR S)
  let lift : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (perfectStructurePresheaf (E := E) p R hR S)).Edge c.cone l := by
    sorry -- l は錐の圏で終対象
  exact c.vertexIso.hom ≫ SSet.Truncated.HomotopyCategory.homMk (lift.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _)).toTruncated

end SerrePositivity.BhattScholze.Perfectoidization.Derived
