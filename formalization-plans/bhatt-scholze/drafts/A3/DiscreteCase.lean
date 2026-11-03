-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Discrete（仮。原典 Lemma 7.7・7.8）
-- 設計書：formalization-plans/bhatt-scholze/a3-design.md §2.1、単位 A3-1・A3-2。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
-- 本ファイルは drafts/A2/{DerivedPrismaticCohomology,HodgeTateFiltration}.lean、drafts/A0/{PrismaticSite,PrismaticEnvelope}.lean、
-- drafts/DerivedGeneral/Truncation.lean、drafts/Sheaves/GlobalSections.lean を import する。

/-!
# 導来 prismatic コホモロジーが離散な場合（BS 著者版 Lemma 7.7、Lemma 7.8）

## 概要
Δ_{R/A}（A2）が次数 0 に集中するとき：(1) φ_R は δ-A 構造に持ち上がる（本書では特別な場合：p ねじれなし、または envelope と同一視できる場合。D36）、
(2) (Δ_R, dΔ_R) は (A,(d)) 上の prism で R → Δ_R/dΔ_R をもつ、(3) R 上の任意の prism (B, dB) へ Δ_R → B があり（弱始対象）、
(R/A)_Δ は始対象をもち、それは Δ_R の冪等自己準同型の retract（Lemma 7.8）。

## 方針
(3) の射は、R の多項式分解 R_• → R（A2 の Kan 延長）について Δ_{R_k} = lim_{(R_k/A)_Δ} O_Δ（RΓ ＝ site 上の極限、S2 と Cor 3.12）の、
対象 (B, R_k → R → B/dB) への脚を取り、k について余極限で得る。Lemma 7.8 は圏論。δ 射であることは (1) の場合に envelope の普遍性か
p ねじれなしの一意性で。

## 規約
「離散」は U(Δ_R) が D(A) で次数 0 に集中すること（DerivedGeneral/Truncation の述語）。Δ_R と書いたら H⁰ の可換環（CAlg 値なので環）。
(1) の一般形（W₂ の導来版）は述べない（D36）。

## 使われ方
Ex 7.9・Prop 7.10（A3-3・A3-4）、Lemma 8.4・Cor 8.14（A4・A7：H⁰(Δ_perf) の完全 δ 構造）、Thm 10.11（A8）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.EInfinity.BarrattEccles SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## Lemma 7.8（圏論） -/

/-- 概要：Lemma 7.8：冪等完備な圏 C と対象 X、恒等関手が射影 C_{X\} → C を経由する関手 F : C → C_{X\} があれば、F(X) : X → X は冪等で、
その retract X′ は C の始対象。
方針：原典の証明：F(X) = e は冪等、X′ = retract、F(X′) = (X → X′) は全射（epi）、F 忠実で Hom(X′, Y) ↪ Hom_{C_{X\}}(X → X′, X → Y) は高々一点、
X′ → X → Y で少なくとも一点。
規約：Mathlib の `IsIdempotentComplete`、`Limits.IsInitial`。
使われ方：(R/A)_Δ の始対象。 -/
theorem initial_of_retraction_idempotent {C : Type v} [Category.{u} C] [IsIdempotentComplete C] (X : C)
    (F : C ⥤ Under X) (hF : F ⋙ Under.forget X = 𝟭 C) :
    ∃ (X' : C) (r : X ⟶ X') (s : X' ⟶ X), s ≫ r = 𝟙 X' ∧
      r ≫ s = (F.obj X).hom ≫ eqToHom (congrArg (fun H : C ⥤ C => H.obj X) hF) ∧
      Nonempty (Limits.IsInitial X') := by
  sorry -- F(X) の冪等射を分裂させ、自然な脚で存在と一意性を示す

/-- 概要：(R/A)_Δ（環の側 `PrismOver P R κ`）は冪等完備：prism の冪等 δ 自己準同型の像は prism。
方針：retract は導来 (p,d) 完備性・δ 構造・d の正則性・R からの写像を保つ。
規約：濃度 ≤ κ も保つ（部分環）。
使われ方：Lemma 7.8 の適用。 -/
theorem prismOver_isIdempotentComplete (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u}) :
    IsIdempotentComplete (PrismOver P R κ) := by
  sorry -- 冪等射の像に δ、完備性、正則性、有界性と構造射を制限する

/-! ## 離散な Δ_R -/

variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-- 概要：原典 Lemma 7.7 の仮定：Δ̄_{R/A} = Δ_R ⊗^L A/d が次数 0 に集中（W9-I-33）。
方針：DerivedGeneral/Truncation の `IsConnectiveAt 0 ∧ IsCoconnectiveAt 0` を Δ̄_R に。
規約：離散 R について（`derivedPrismaticCohomologyDiscrete`）。
使われ方：以下の仮定の入口。 -/
abbrev discreteInput := (discreteToAnimated _).app _ (nerveVertex (ofAlgebra (A ⧸ P.ideal) R))
abbrev discreteDeltaAlgebra := derivedPrismaticCohomology_h0_ring P hP (discreteInput P R)

def IsDiscreteHodgeTate : Prop :=
  let x := (reducedDelta P hP ≫ cAlgForgetDerived _).app _ (discreteInput P R)
  Derived.IsConnectiveAt _ 0 x ∧ Derived.IsCoconnectiveAt _ 0 x

/-- 概要：Δ_{R/A} が離散で d が正則。`IsDiscreteHodgeTate` から従う（Δ_R は導来 d 完備で mod d が離散 ⇒ d 進 Nakayama で離散、Δ_R[d] = H⁻¹(Δ̄_R) = 0）。
方針：DerivedGeneral の導来 Nakayama。
規約：—
使われ方：以下。 -/
def IsDiscretePrismatic : Prop :=
  let x := (derivedPrismaticCohomologyDerived P hP).app _ (discreteInput P R)
  let d := (discreteDeltaAlgebra P hP R).hom.hom P.generator
  Derived.IsConnectiveAt A 0 x ∧ Derived.IsCoconnectiveAt A 0 x ∧ Function.Injective (fun y => d * y)

theorem isDiscretePrismatic_of_hodgeTate (h : IsDiscreteHodgeTate P hP R) :
    IsDiscretePrismatic P hP R := by
  sorry -- d 完備な Δ の導来 mod d が離散。Nakayama と H⁻¹(mod d)=H⁰(Δ)[d]

abbrev discretePrismaticRing (_ : IsDiscretePrismatic P hP R) : Type u :=
  (discreteDeltaAlgebra P hP R).right

abbrev discreteBase := (discreteDeltaAlgebra P hP R).hom.hom
instance discreteBaseAlgebra : Algebra A (discreteDeltaAlgebra P hP R).right := (discreteBase P hP R).toAlgebra

/-- 離散な Δ とその H⁰ の標準同型。 -/
def discreteDeltaIso (h : IsDiscretePrismatic P hP R) :
    VertexIso ((deltaUnderlying P hP).app _ (discreteInput P R))
      ((algebraEmbedding A).app _ (nerveVertex (discreteDeltaAlgebra P hP R))) := by
  sorry -- 離散 E∞ 代数の H⁰ への切り捨て

/-- 概要：Frobenius φ_R : Δ_R → Δ_R（環の自己準同型、φ_A 半線形）。
方針：A2 の `derivedPrismaticFrobenius` の H⁰。
規約：—
使われ方：δ 構造。 -/
def discreteFrobeniusData (h : IsDiscretePrismatic P hP R) :
    let C := discreteDeltaAlgebra P hP R
    let φ := P.deltaStructure.frobeniusLift
    let twist : A_R A := Under.mk (CommRingCat.ofHom (C.hom.hom.comp φ))
    { f : C ⟶ twist //
      let v := discreteDeltaIso P hP R h
      v.hom ≫ HomotopyCategory.homMk ((nerve.edgeMk f).map (algebraEmbedding A)) ≫
        (cAlgRestrictScalars_algebraEmbedding φ C).hom =
        HomotopyCategory.homMk (discreteFrobeniusComponent P hP (ofAlgebra _ R)) ≫
          (v.map (cAlgRestrictScalars φ)).hom } := by
  sorry -- 離散代数の間で A2 の Frobenius 成分を読む。制限後の離散埋め込みは M13

def discretePrismaticFrobenius (h : IsDiscretePrismatic P hP R) :=
  (discreteFrobeniusData P hP R h).val.right.hom

theorem discreteFrobenius_mod_p (h : IsDiscretePrismatic P hP R)
    (hp : Function.Injective (fun x : discretePrismaticRing P hP R h => (p : discretePrismaticRing P hP R h) * x))
    (x : discretePrismaticRing P hP R h) :
    discretePrismaticFrobenius P hP R h x - x ^ p ∈ Ideal.span {(p : discretePrismaticRing P hP R h)} := by
  sorry -- 要確認：G-A3-9。A2 の φ modulo p と E∞ の Frobenius 演算を比較し π₀ を取る

/-- 概要：Lemma 7.7(1′)：Δ_R が離散で p ねじれなしなら、φ_R は mod p で Frobenius（A2 の φ と E∞ の Frobenius 演算の比較から）で、
Rem 2.2 により δ-A 構造が一意に定まる。
方針：p ねじれなし環の Frobenius 持ち上げから δ（G-A3-6）。mod p で Frobenius であることは **G-A3-9**（Δ_R/p の E∞-F_p 代数としての
Frobenius の π_0 への作用が x ↦ x^p。A4 の P⁰ の π_0 の部分を前倒し。A4 の結論は使わない、W9-I-34）。HT の gr 上の一致だけでは全体の一致は出ない。
規約：p ねじれなしの仮定つき。
使われ方：Lemma 8.4・Cor 8.14（H⁰(Δ_perf)）。 -/
theorem deltaStructure_of_discrete_pTorsionFree (h : IsDiscretePrismatic P hP R)
    (hp : Function.Injective (fun x : discretePrismaticRing P hP R h => (p : discretePrismaticRing P hP R h) * x)) :
    ∃! D : DeltaStructure p (discretePrismaticRing P hP R h), D.frobeniusLift = discretePrismaticFrobenius P hP R h ∧
      P.deltaStructure.IsDeltaHom D (discreteBase P hP R) := by
  obtain ⟨D, hD, unique⟩ := DeltaStructure.existsUnique_of_frobeniusLift hp
    (discretePrismaticFrobenius P hP R h) (fun x =>
      Ideal.mem_span_singleton.mp (discreteFrobenius_mod_p P hP R h hp x))
  refine ⟨D, ⟨hD, DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hp ?_⟩, fun E hE => unique E hE.1⟩
  sorry -- hD と discreteFrobeniusData の Under の三角から基底の Frobenius と可換

/-- 概要：Lemma 7.7(1″)：Δ_R が prismatic envelope（prism）と A 代数として同型で、同型が Frobenius と両立するなら、δ 構造は移送したもの。
方針：同型に沿う δ 構造の移送。
規約：Ex 7.9・Prop 7.10 で使う形。
使われ方：A3-3・A3-4。 -/
theorem deltaStructure_of_envelopeIso (h : IsDiscretePrismatic P hP R)
    {B C : Type u} [CommRing B] [CommRing C] (Q : OrientedPrism p B)
    (DC : DeltaStructure p C) (ι : A →+* C) (hι : P.deltaStructure.IsDeltaHom DC ι)
    (J : Ideal C) (hJ : ι P.generator ∈ J) (η : C →+* B)
    (hE : IsPrismaticEnvelope P DC ι hι J hJ Q η)
    (e : discretePrismaticRing P hP R h ≃+* B)
    (he : e.toRingHom.comp (discreteBase P hP R) = η.comp ι)
    (hφ : e.toRingHom.comp (discretePrismaticFrobenius P hP R h) =
      Q.deltaStructure.frobeniusLift.comp e.toRingHom) :
    ∃! D : DeltaStructure p (discretePrismaticRing P hP R h),
      D.IsDeltaHom Q.deltaStructure e.toRingHom ∧
      D.frobeniusLift = discretePrismaticFrobenius P hP R h ∧
      P.deltaStructure.IsDeltaHom D (discreteBase P hP R) := by
  refine ⟨Q.deltaStructure.comapEquiv e, ⟨Q.deltaStructure.comapEquiv_isDeltaHom e, ?_, ?_⟩, ?_⟩
  · sorry -- hφ と e の単射性
  · sorry -- he と hE.isDeltaHom.comp hι、逆同型も δ 射
  · sorry -- どちらの切断も e を通じて Q の切断に一致

/-- 概要：Lemma 7.7(2)：Δ_R が離散で δ 構造をもち、Δ̄_R = Δ_R/d も離散（d 正則）なら、(Δ_R, dΔ_R) は (A,(d)) 上の有界向き付き prism で、
R → Δ_R/dΔ_R（HT filtration の Fil_0 = 単位）をもつ。
方針：導来 (p,d) 完備性は値の圏から、d の正則性は Δ̄_R の離散性（Δ ⊗^L A/d の H⁻¹ = Δ_R[d] = 0）、p ∈ (d, φ(d)) は A から。
有界性：Δ̄_R の p 冪ねじれ（R が p ねじれ有界なら、Prop 7.10 の場合は平坦）。
規約：`OrientedPrism` と `PrismOver P R κ` の対象（濃度は要確認：Δ_R の濃度 ≤ κ）。有界性（`IsBoundedPrism`）は自動ではなく、
Δ̄_R の p 冪ねじれの有界性を別の仮定 `hbdd` で受ける（W9-I-33。Ex 7.9・Prop 7.10 では R の有界ねじれと p 完全平坦性から）。
使われ方：(3)。 -/
def discretePrism (h : IsDiscretePrismatic P hP R) (D : DeltaStructure p (discretePrismaticRing P hP R h))
    (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R)) : OrientedPrism p (discretePrismaticRing P hP R h) where
  deltaStructure := D
  generator := discreteBase P hP R P.generator
  generator_regular := h.2.2
  complete_p := by sorry -- 完備な Δ が離散なので H⁰ は導来 p 完備
  complete_generator := by sorry -- 同じく d 完備
  p_mem := by sorry -- P.p_mem の像。hD で φ と可換

def discretePrismBase (h : IsDiscretePrismatic P hP R) (D : DeltaStructure p (discretePrismaticRing P hP R h))
    (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R)) :
    OrientedPrism.Hom P (discretePrism P hP R h D hD) where
  toRingHom := discreteBase P hP R
  map_delta := hD
  ideal_le := by sorry -- 生成元を生成元に送る

/-- H⁰Δ/d とその A/d 作用。δ 構造を選ぶ前に HT の単位を指定できる。 -/
def discreteHTAlgebra : A_R (A ⧸ P.ideal) :=
  let J := Ideal.span {discreteBase P hP R P.generator}
  Under.mk (CommRingCat.ofHom (Ideal.quotientMap J (discreteBase P hP R) (by
    sorry))) -- d の像は J の生成元

def discreteHTIso (h : IsDiscretePrismatic P hP R) :
    VertexIso ((reducedDelta P hP).app _ (discreteInput P R))
      ((algebraEmbedding _).app _ (nerveVertex (discreteHTAlgebra P hP R))) := by
  sorry -- d は H⁰Δ で正則。discreteDeltaIso の mod d は次数零の通常の商

def discreteHTArrow (h : IsDiscretePrismatic P hP R) :
    { s : ofAlgebra (A ⧸ P.ideal) R ⟶ discreteHTAlgebra P hP R //
      HomotopyCategory.homMk ((nerve.edgeMk s).map (algebraEmbedding _)) =
        ((discreteRealizationIso _).app (nerveVertex (ofAlgebra _ R))).inv ≫
          functorHomEvaluate (hodgeTateUnitFromInput P hP) (discreteInput P R) ≫
          (discreteHTIso P hP R h).hom } := by
  sorry -- 離散埋め込みの充満忠実性で HT 単位を係数環の射へ戻す

def discreteHTMap (h : IsDiscretePrismatic P hP R)
    (D : DeltaStructure p (discretePrismaticRing P hP R h)) (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R)) :
    R →+* discretePrismaticRing P hP R h ⧸ (discretePrism P hP R h D hD).ideal :=
  (discreteHTArrow P hP R h).val.right.hom

def discretePrismOver (h : IsDiscretePrismatic P hP R) (D : DeltaStructure p (discretePrismaticRing P hP R h))
    (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R)) (κ : Cardinal.{u})
    (hb : IsBoundedPrism (discretePrism P hP R h D hD))
    (hs : Cardinal.mk (discretePrismaticRing P hP R h) ≤ κ) : PrismOver P R κ where
  B := discretePrismaticRing P hP R h
  Q := discretePrism P hP R h D hD
  bounded := hb
  toHom := discretePrismBase P hP R h D hD
  sec := discreteHTMap P hP R h D hD
  sec_comp := by sorry -- HT 単位の A/d 線形性
  small := hs

/-- 概要：Lemma 7.7(3) の射：任意の prism (B, dB) over (A,(d)) と R → B/dB に対し、A 代数の射 Δ_R → B。
方針：R の多項式分解 R_• → R（A2 の Kan 延長の bar 分解）、Δ_{R_k} = lim_{(R_k/A)_Δ} O_Δ（S2 の `derivedGlobalSections_of_isSheaf`、Cor 3.12）の
対象 (B, R_k → R → B/dB) への脚、k について両立（B は R からの写像で固定）、余極限 Δ_R = colim_k Δ_{R_k} で Δ_R → B。
規約：環の射（H⁰）、φ と可換（O_Δ の Frobenius の自然性）。δ 射であることは **標的 B が p ねじれなしのとき**（W9-I-34：p·(fδ(x) − δ(fx)) = 0 を B で消す）
に示す（D36 改訂案 §7.1）。E3 で要る標的（B_univ、Δ_{S′}・Δ_T、完全 prism）はすべて p ねじれなし。
使われ方：弱始性、Lemma 7.8。 -/
abbrev evaluationCutoff {A : Type u} (R : Type u) (κ : Cardinal.{u}) := max κ (Cardinal.mk A + Cardinal.mk R)

instance evaluationSiteSmall (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (PrismOver P R (evaluationCutoff (A := A) R κ)) :=
  PrismOver.essentiallySmall (le_max_right _ _)

def evaluationTest {κ : Cardinal.{u}} (Y : PrismOver P R κ) :
    (PrismaticSite P R (evaluationCutoff (A := A) R κ))ᵒᵖ :=
  let Y' := (prismOverCutoffInclusion P R (show κ ≤ evaluationCutoff (A := A) R κ from le_max_left _ _)).obj Y
  Opposite.op (Opposite.op ((equivSmallModel _).functor.obj Y'))

def evaluationTestIso {κ : Cardinal.{u}} (Y : PrismOver P R κ) :
    VertexIso ((testStructure P R (evaluationCutoff (A := A) R κ)).app _
      (ULift.up (nerveVertex (evaluationTest P R Y))))
      ((algebraEmbedding A).app _ (nerveVertex (Under.mk (CommRingCat.ofHom Y.toHom.toRingHom)))) := by
  sorry -- ringPresheafToCAlg の評価と equivSmallModel の unitIso の逆で Y に移す

def prismEvaluationArrow (h : IsDiscretePrismatic P hP R) {κ : Cardinal.{u}} (Y : PrismOver P R κ) :
    let c := discreteEvaluation P R (evaluationCutoff (A := A) R κ) hP
    let v := ULift.up (nerveVertex (evaluationTest P R Y))
    let B := Under.mk (CommRingCat.ofHom Y.toHom.toRingHom)
    { f : discreteDeltaAlgebra P hP R ⟶ B //
      HomotopyCategory.homMk ((nerve.edgeMk f).map (algebraEmbedding A)) =
        (discreteDeltaIso P hP R h).inv ≫ c.2.val.hom ≫
          Truncated.HomotopyCategory.homMk (F2.nativeConeLeg c.1 v) ≫ (evaluationTestIso P R Y).hom } := by
  sorry -- A2 の Y での脚を、離散代数の充満忠実性で環準同型に戻す

def prismMapOfDiscrete (h : IsDiscretePrismatic P hP R) {κ : Cardinal.{u}} (Y : PrismOver P R κ) :
    discretePrismaticRing P hP R h →+* Y.B :=
  (prismEvaluationArrow P hP R h Y).val.right.hom

theorem prismMapOfDiscrete_natural (h : IsDiscretePrismatic P hP R) {κ : Cardinal.{u}}
    {Y Z : PrismOver P R κ} (g : Y ⟶ Z) :
    g.toHom.toRingHom.comp (prismMapOfDiscrete P hP R h Y) = prismMapOfDiscrete P hP R h Z := by
  sorry -- 同じ discreteEvaluation の錐の脚。小さい模型への移送は g と可換

def NoPTorsion (p : ℕ) (B : Type u) [CommRing B] : Prop := Function.Injective (fun x : B => (p : B) * x)

/-- 概要：(3)：(Δ_R, dΔ_R) は (R/A)_Δ の **p ねじれなしの対象に対して**弱始（δ 構造が (1′)(1″) で与えられているとき。D36 改訂案）。
方針：`prismMapOfDiscrete` と、δ 射であること（標的の p ねじれなし）、R からの写像との両立（Fil_0 の自然性）。
規約：—
使われ方：Lemma 7.8 で始対象。 -/
theorem discrete_weaklyInitial (h : IsDiscretePrismatic P hP R) (D : DeltaStructure p (discretePrismaticRing P hP R h))
    (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R))
    (hφ : D.frobeniusLift = discretePrismaticFrobenius P hP R h) (κ : Cardinal.{u})
    (hb : IsBoundedPrism (discretePrism P hP R h D hD))
    (hs : Cardinal.mk (discretePrismaticRing P hP R h) ≤ κ)
    (Y : PrismOver P R κ) (hY : NoPTorsion p Y.B) :
    ∃ f : discretePrismOver P hP R h D hD κ hb hs ⟶ Y,
      f.toHom.toRingHom = prismMapOfDiscrete P hP R h Y := by
  sorry -- 評価脚に isDeltaHom_of_map_frobeniusLift を hY で適用。HT 単位の自然性で sec と両立

abbrev TorsionFreePrisms (κ : Cardinal.{u}) :=
  ObjectProperty.FullSubcategory (fun Y : PrismOver P R κ => NoPTorsion p Y.B)

/-- 概要：(R/A)_Δ の **p ねじれなしの prism の充満部分圏**（Δ_R 自身が p ねじれなしのとき、W9-I-40）は始対象をもち、それは (Δ_R, dΔ_R) の冪等自己準同型
（`prismMapOfDiscrete` を B := Δ_R 自身に適用）の retract。全 prism の中の始性は Ex 7.9・Prop 7.10 では envelope の押し出しの普遍性から別に得る
（`lciDerivedEnvelope_isEnvelope_of_discrete`）。
方針：Lemma 7.8（`initial_of_retraction_idempotent`）をその部分圏で、`prismOver_isIdempotentComplete`。
規約：原典の「we conjecture that (Δ_R, IΔ_R) is actually the initial object」：一般には主張しない。Ex 7.9・Prop 7.10 で冪等元が恒等であることを示す。
使われ方：Ex 7.9、Prop 7.10。 -/
theorem exists_initial_of_discrete (h : IsDiscretePrismatic P hP R) (D : DeltaStructure p (discretePrismaticRing P hP R h))
    (hD : P.deltaStructure.IsDeltaHom D (discreteBase P hP R))
    (hφ : D.frobeniusLift = discretePrismaticFrobenius P hP R h) (κ : Cardinal.{u})
    (hb : IsBoundedPrism (discretePrism P hP R h D hD))
    (hs : Cardinal.mk (discretePrismaticRing P hP R h) ≤ κ)
    (hp : NoPTorsion p (discretePrismaticRing P hP R h)) :
    let X : TorsionFreePrisms P R κ := ⟨discretePrismOver P hP R h D hD κ hb hs, hp⟩
    ∃ (I : TorsionFreePrisms P R κ) (r : X ⟶ I) (s : I ⟶ X),
      s ≫ r = 𝟙 I ∧ (r ≫ s).hom.toHom.toRingHom = prismMapOfDiscrete P hP R h X.obj ∧
        Nonempty (Limits.IsInitial I) := by
  sorry -- 評価脚は Y に自然ゆえ Under X への切断になる。p 正則性は retract に閉じる。
        -- 部分圏で initial_of_retraction_idempotent を適用し X 自身での評価を分裂

end SerrePositivity.BhattScholze.Prismatic
