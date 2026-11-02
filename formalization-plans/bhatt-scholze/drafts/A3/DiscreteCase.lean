-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Discrete（仮。原典 Lemma 7.7・7.8）
-- 設計書：formalization-plans/bhatt-scholze/a3-design.md §2.1、単位 A3-1・A3-2。基準コミット 972bb7f53。ビルドしない。
module

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
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## Lemma 7.8（圏論） -/

/-- 概要：Lemma 7.8：冪等完備な圏 C と対象 X、恒等関手が射影 C_{X\} → C を経由する関手 F : C → C_{X\} があれば、F(X) : X → X は冪等で、
その retract X′ は C の始対象。
方針：原典の証明：F(X) = e は冪等、X′ = retract、F(X′) = (X → X′) は全射（epi）、F 忠実で Hom(X′, Y) ↪ Hom_{C_{X\}}(X → X′, X → Y) は高々一点、
X′ → X → Y で少なくとも一点。
規約：Mathlib の `IsIdempotentComplete`、`Limits.IsInitial`。
使われ方：(R/A)_Δ の始対象。 -/
theorem initial_of_retraction_idempotent {C : Type u} [Category.{u} C] [IsIdempotentComplete C] (X : C)
    (F : C ⥤ Under X) (hF : F ⋙ Under.forget X = 𝟭 C) :
    ∃ (X' : C) (r : X ⟶ X') (s : X' ⟶ X), s ≫ r = 𝟙 X' ∧ Nonempty (Limits.IsInitial X') := by
  sorry

/-- 概要：(R/A)_Δ（環の側 `PrismOver P R κ`）は冪等完備：prism の冪等 δ 自己準同型の像は prism。
方針：retract は導来 (p,d) 完備性・δ 構造・d の正則性・R からの写像を保つ。
規約：濃度 ≤ κ も保つ（部分環）。
使われ方：Lemma 7.8 の適用。 -/
theorem prismOver_isIdempotentComplete (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R] (κ : Cardinal.{u}) :
    IsIdempotentComplete (PrismOver P R κ) := by
  sorry

/-! ## 離散な Δ_R -/

variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

/-- 概要：原典 Lemma 7.7 の仮定：Δ̄_{R/A} = Δ_R ⊗^L A/d が次数 0 に集中（W9-I-33）。
方針：DerivedGeneral/Truncation の `IsConnectiveAt 0 ∧ IsCoconnectiveAt 0` を Δ̄_R に。
規約：離散 R について（`derivedPrismaticCohomologyDiscrete`）。
使われ方：以下の仮定の入口。 -/
def IsDiscreteHodgeTate : Prop := sorry

/-- 概要：Δ_{R/A} が離散で d が正則。`IsDiscreteHodgeTate` から従う（Δ_R は導来 d 完備で mod d が離散 ⇒ d 進 Nakayama で離散、Δ_R[d] = H⁻¹(Δ̄_R) = 0）。
方針：DerivedGeneral の導来 Nakayama。
規約：—
使われ方：以下。 -/
def IsDiscretePrismatic : Prop := sorry
theorem isDiscretePrismatic_of_hodgeTate (h : IsDiscreteHodgeTate P R) : IsDiscretePrismatic P R := by sorry

/-- 概要：離散な Δ_R の H⁰ の可換環（CAlg 値なので環）。
方針：`derivedPrismaticCohomology_h0_ring`。
規約：A 代数。
使われ方：prism の台。 -/
def discretePrismaticRing (h : IsDiscretePrismatic P R) : Type u := sorry

instance (h : IsDiscretePrismatic P R) : CommRing (discretePrismaticRing P R h) := sorry

/-- 概要：Frobenius φ_R : Δ_R → Δ_R（環の自己準同型、φ_A 半線形）。
方針：A2 の `derivedPrismaticFrobenius` の H⁰。
規約：—
使われ方：δ 構造。 -/
def discretePrismaticFrobenius (h : IsDiscretePrismatic P R) :
    discretePrismaticRing P R h →+* discretePrismaticRing P R h := sorry

/-- 概要：Lemma 7.7(1′)：Δ_R が離散で p ねじれなしなら、φ_R は mod p で Frobenius（HT filtration の Fil_0 と gr の Frobenius から）で、
Rem 2.2 により δ-A 構造が一意に定まる。
方針：p ねじれなし環の Frobenius 持ち上げから δ（`Delta/Basic`。要確認：名前）。mod p で Frobenius であることは **G-A3-9**（Δ_R/p の E∞-F_p 代数としての
Frobenius の π_0 への作用が x ↦ x^p。A4 の P⁰ の π_0 の部分を前倒し。A4 の結論は使わない、W9-I-34）。HT の gr 上の一致だけでは全体の一致は出ない。
規約：p ねじれなしの仮定つき。
使われ方：Lemma 8.4・Cor 8.14（H⁰(Δ_perf)）。 -/
theorem deltaStructure_of_discrete_pTorsionFree (h : IsDiscretePrismatic P R)
    (hp : Function.Injective (fun x : discretePrismaticRing P R h => (p : discretePrismaticRing P R h) * x)) :
    ∃! D : DeltaStructure p (discretePrismaticRing P R h), D.frobeniusLift = discretePrismaticFrobenius P R h ∧
      True := by -- A → Δ_R が δ 射
  sorry

/-- 概要：Lemma 7.7(1″)：Δ_R が prismatic envelope（prism）と A 代数として同型で、同型が Frobenius と両立するなら、δ 構造は移送したもの。
方針：同型に沿う δ 構造の移送。
規約：Ex 7.9・Prop 7.10 で使う形。
使われ方：A3-3・A3-4。 -/
theorem deltaStructure_of_envelopeIso (h : IsDiscretePrismatic P R) : True := by trivial

/-- 概要：Lemma 7.7(2)：Δ_R が離散で δ 構造をもち、Δ̄_R = Δ_R/d も離散（d 正則）なら、(Δ_R, dΔ_R) は (A,(d)) 上の有界向き付き prism で、
R → Δ_R/dΔ_R（HT filtration の Fil_0 = 単位）をもつ。
方針：導来 (p,d) 完備性は値の圏から、d の正則性は Δ̄_R の離散性（Δ ⊗^L A/d の H⁻¹ = Δ_R[d] = 0）、p ∈ (d, φ(d)) は A から。
有界性：Δ̄_R の p 冪ねじれ（R が p ねじれ有界なら、Prop 7.10 の場合は平坦）。
規約：`OrientedPrism` と `PrismOver P R κ` の対象（濃度は要確認：Δ_R の濃度 ≤ κ）。有界性（`IsBoundedPrism`）は自動ではなく、
Δ̄_R の p 冪ねじれの有界性を別の仮定 `hbdd` で受ける（W9-I-33。Ex 7.9・Prop 7.10 では R の有界ねじれと p 完全平坦性から）。
使われ方：(3)。 -/
def discretePrism (h : IsDiscretePrismatic P R) (D : DeltaStructure p (discretePrismaticRing P R h)) (hD : True)
    (hbdd : True) : OrientedPrism p (discretePrismaticRing P R h) := sorry

/-- 概要：Lemma 7.7(3) の射：任意の prism (B, dB) over (A,(d)) と R → B/dB に対し、A 代数の射 Δ_R → B。
方針：R の多項式分解 R_• → R（A2 の Kan 延長の bar 分解）、Δ_{R_k} = lim_{(R_k/A)_Δ} O_Δ（S2 の `derivedGlobalSections_of_isSheaf`、Cor 3.12）の
対象 (B, R_k → R → B/dB) への脚、k について両立（B は R からの写像で固定）、余極限 Δ_R = colim_k Δ_{R_k} で Δ_R → B。
規約：環の射（H⁰）、φ と可換（O_Δ の Frobenius の自然性）。δ 射であることは **標的 B が p ねじれなしのとき**（W9-I-34：p·(fδ(x) − δ(fx)) = 0 を B で消す）
に示す（D36 改訂案 §7.1）。E3 で要る標的（B_univ、Δ_{S′}・Δ_T、完全 prism）はすべて p ねじれなし。
使われ方：弱始性、Lemma 7.8。 -/
def prismMapOfDiscrete (h : IsDiscretePrismatic P R) {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (f : OrientedPrism.Hom P Q) (s : R →+* B ⧸ Q.ideal) :
    discretePrismaticRing P R h →+* B := sorry

/-- 概要：(3)：(Δ_R, dΔ_R) は (R/A)_Δ の **p ねじれなしの対象に対して**弱始（δ 構造が (1′)(1″) で与えられているとき。D36 改訂案）。
方針：`prismMapOfDiscrete` と、δ 射であること（標的の p ねじれなし）、R からの写像との両立（Fil_0 の自然性）。
規約：—
使われ方：Lemma 7.8 で始対象。 -/
theorem discrete_weaklyInitial (h : IsDiscretePrismatic P R) : True := by trivial

/-- 概要：(R/A)_Δ は始対象をもち、それは (Δ_R, dΔ_R) の冪等自己準同型（`prismMapOfDiscrete` を B := Δ_R 自身に適用）の retract。
方針：Lemma 7.8（`initial_of_retraction_idempotent`）と `prismOver_isIdempotentComplete`。
規約：原典の「we conjecture that (Δ_R, IΔ_R) is actually the initial object」：一般には主張しない。Ex 7.9・Prop 7.10 で冪等元が恒等であることを示す。
使われ方：Ex 7.9、Prop 7.10。 -/
theorem exists_initial_of_discrete (h : IsDiscretePrismatic P R) : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
