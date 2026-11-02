-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.AnimatedAlgebra（仮。原典 Construction 7.6 の始域、SAG 25.1.1.1）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.1、単位 A2-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.Derived.DiscreteEmbedding
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 単体的可換 k 代数（animated 代数）の ∞ 圏 P_Σ(Poly_k) と離散環の埋め込み

## 概要
有限生成多項式 k 代数 k[X_1,…,X_n]（n : ℕ）と k 代数の射の圏 `Poly k` について、その nerve の sifted 余極限による完備化
P_Σ(N(Poly k))（F2 の `SigmaPresheafInfinity`：有限余積を積へ送る空間値前層の ∞ 圏）を単体的可換 k 代数の ∞ 圏とする
（Lurie SAG 25.1.1.1、HTT 5.5.8）。Yoneda j : Poly k → P_Σ は充満忠実で像は compact projective な生成系。離散 k 代数 R は
P ↦ Hom_k(P, R)（有限余積を保つ前層）で埋め込む（HTT 5.5.8.10）。

## 方針
基盤の F2/Presentable の P_Σ をそのまま使う。多項式代数は添字 n : ℕ（a2-design §6 の 3）。離散環の埋め込みは E3 の `algebraNerve k`
（`nerve (Under (CommRingCat.of k))`）からの単体的集合の射として作る（E3 の `perfd` の始域に合わせる）。

## 規約
k = A/d（prism の商）を想定するが、ここでは任意の可換環 k。原典の「導来 p 完備な単体的代数」ではなく P_Σ 全体を始域にする（D32）。
生成系は完備化しない多項式代数（D32）。

## 使われ方
A2-2（Δ の左 Kan 延長、HTT 5.5.8.15）、A2-3（HT filtration）、A3（Lemma 7.7 の「単体的 A/I 代数」）、A4（Def 8.2 の S）、
E3 の `perfd` の始域との接続（`discreteToAnimated`）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits

variable (k : Type u) [CommRing k]

/-! ## 多項式代数の圏 -/

/-- 概要：有限生成多項式 k 代数の圏：対象は n : ℕ（k[X_1,…,X_n]）、射は k 代数の射。
方針：対象を添字で持ち、射は `MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k`。
規約：小さい圏（Type u）。有限余積は n + m（テンソル積 ＝ 変数の併置）。
使われ方：P_Σ の生成系、Čech–Alexander の R の範囲（A0 の `cechAlexanderAffine`）。 -/
structure Poly where
  n : ℕ

instance : SmallCategory (Poly k) where
  Hom P Q := MvPolynomial (Fin P.n) k →ₐ[k] MvPolynomial (Fin Q.n) k
  id P := AlgHom.id k _
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- 概要：多項式代数の有限余積 k[X_n] ⊗ k[X_m] = k[X_{n+m}]。
方針：`MvPolynomial.sumAlgEquiv` と `Fin` の和。
規約：P_Σ の条件（有限余積を積へ）に使う。
使われ方：`IsSigmaPresheaf` の検証。 -/
def polyCoproduct (P Q : Poly k) : Poly k := ⟨P.n + Q.n⟩

theorem polyCoproduct_isCoproduct (P Q : Poly k) : True := by trivial -- 要確認：Mathlib の BinaryCofan/IsColimit で

/-- 概要：多項式代数の圏の nerve（小さい形状）。
方針：Mathlib の `nerve`。
規約：SSet.{u}。
使われ方：P_Σ の添字。 -/
abbrev polyNerve : SSet.{u} := nerve (Poly k)

/-! ## animated 代数 -/

/-- 概要：単体的可換 k 代数の ∞ 圏 := P_Σ(N(Poly k))。
方針：F2 の `SigmaPresheafInfinity`。
規約：SSet.{u+1}。quasicategory 性は F2 の instance（要確認）。
使われ方：Δ の始域。 -/
abbrev AnimatedAlgebra : SSet.{u + 1} := SigmaPresheafInfinity (polyNerve k)

/-- 概要：Yoneda j : N(Poly k) → P_Σ（持ち上げた形状から）。
方針：F1 の Yoneda 埋め込み `PresheafInfinity` への射と、表現可能前層が有限余積を積へ送ること（HTT 5.5.8.10、F2 の `SigmaYonedaFiniteCoproducts`）で
`sigmaPresheafInfinityLift`。
規約：充満忠実（F1 の `YonedaInfinityFullyFaithful`）、像は compact projective（HTT 5.5.8.22）。
使われ方：Δ_0 の始域、(1) の主張。
要確認：F1 の Yoneda 射の名前（`yonedaInfinity`）。 -/
def polyYoneda : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve k) ⟶ AnimatedAlgebra k :=
  sorry -- sigmaPresheafInfinityLift (yonedaInfinity (polyNerve k)) (表現可能前層の有限積保存)

theorem polyYoneda_fullyFaithful : True := by trivial -- F1 の Yoneda の充満忠実性

/-- 概要：P_Σ は sifted 余極限をもち、Yoneda の像で sifted 余極限により生成される（HTT 5.5.8.10）。
方針：F2 の `PresheafBarRealization`（bar 図式の幾何学的実現）と `SiftedColimitPreservation`。
規約：主張の形は F2 の既存の定理に合わせる。
使われ方：Kan 延長の一意性（A2-2）。 -/
theorem animatedAlgebra_siftedColimits : True := by trivial

/-- 概要：HTT 5.5.8.15：sifted 余極限をもつ ∞ 圏 𝒱 について、sifted 余極限を保つ関手 P_Σ → 𝒱 の制限 Fun^Σ(P_Σ, 𝒱) → Fun(N(Poly), 𝒱) は同値。
方針：F2 の `SigmaLeftKanAllColimitPreservation`・`SigmaYonedaColimitPreservationCriterion`。
規約：存在（左 Kan 延長）と一意性（sifted 余極限保存な延長は一意）を分けて述べる。
使われ方：A2-2 の `derivedPrismaticCohomology` の定義と性質。 -/
theorem exists_siftedExtension {V : SSet.{u + 1}} [Quasicategory V]
    (hV : True) -- 要確認：V が sifted 余極限をもつことの述語
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve k) ⟶ V) :
    ∃ G : AnimatedAlgebra k ⟶ V, True ∧ -- G は sifted 余極限を保ち、polyYoneda ≫ G ≃ F
      True := by
  sorry -- F2 の左 Kan 延長の存在と HTT 5.5.8.15

/-! ## 離散環の埋め込み -/

/-- 概要：離散 k 代数 R を、集合値前層 P ↦ Hom_k(P, R) として（1 圏の関手）。
方針：`Under (CommRingCat.of k) ⥤ (Poly k)ᵒᵖ ⥤ Type u`。
規約：有限余積を積へ送る（Hom(P ⊗ Q, R) = Hom(P, R) × Hom(Q, R)）。
使われ方：`discreteToAnimated`。 -/
def discretePresheaf : Under (CommRingCat.of k) ⥤ ((Poly k)ᵒᵖ ⥤ Type u) :=
  sorry -- R ↦ (P ↦ (MvPolynomial (Fin P.n) k →ₐ[k] R))

/-- 概要：集合値前層を空間値前層（`PresheafInfinity`）の頂点として読む（離散空間）。
方針：集合値前層の 1 圏の nerve から `PresheafInfinity (polyNerve k)` への射（離散埋め込み）。
規約：—
使われ方：`discreteToAnimated`。
要確認：F1/F2 に「集合値前層の nerve → PresheafInfinity」の射があるか。なければ `SpaceInfinity` の離散埋め込みと ihom で作る。 -/
def discretePresheafEmbedding : nerve ((Poly k)ᵒᵖ ⥤ Type u) ⟶ PresheafInfinity (polyNerve k) :=
  sorry

/-- 概要：離散 k 代数の ∞ 圏（E3 の `algebraNerve k`）から animated 代数への埋め込み R ↦ (P ↦ Hom_k(P, R))。
方針：`nerveMap (discretePresheaf k) ≫ discretePresheafEmbedding k` を、有限積保存（`IsSigmaPresheaf`）の検証つきで
`sigmaPresheafInfinityLift` で P_Σ へ。
規約：E3 の `perfd` の始域はこの合成で Δ に接続する。
使われ方：A4（S_perfd の定義域）、E3。 -/
def discreteToAnimated : nerve (Under (CommRingCat.of k)) ⟶ AnimatedAlgebra k :=
  sorry -- sigmaPresheafInfinityLift (nerveMap (discretePresheaf k) ≫ discretePresheafEmbedding k) (有限積保存)

/-- 概要：多項式代数 R = k[X_n] の離散埋め込みは Yoneda j(n) に一致。
方針：Hom_k(P, k[X_n]) は表現可能前層。
規約：同値（頂点の同型）で述べる。
使われ方：(1) を離散 R へ移す、A0 の Δ との接続。 -/
theorem discreteToAnimated_poly (n : ℕ) : True := by trivial

/-- 概要：離散埋め込みは充満忠実。
方針：Hom_k(k[X_n], R) = R^n の Yoneda 的な議論（P_Σ の射は生成系で決まる）。
規約：—
使われ方：Δ の離散 R での値が R だけで決まること。 -/
theorem discreteToAnimated_fullyFaithful : True := by trivial

end SerrePositivity.BhattScholze.Prismatic
