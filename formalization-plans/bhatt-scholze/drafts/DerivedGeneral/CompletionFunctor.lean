-- 将来の置き場所：InfinityCategories の Derived の上（調整役が判断。M12 と同じ扱い）。BS 固有ではない一般論。
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md G-A2-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.Derived.InfinityCategory
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 導来 (p,d) 完備化の ∞ 関手

## 概要
D(A) の導来 (p,d) 完備な対象のなす充満部分 ∞ 圏 D(A)_comp と、包含の左随伴（反射）としての完備化 X ↦ X^∧。
完備な対象の特徴づけ（Koszul 塔の極限、`IsModuleComplete` の D(A) 版）、完備化が完全であること、余極限の完備化、
完備化が ⊗^L A/(p^n,d^n) を変えないこと。

## 方針
複体の側の既存の導来完備化（HA/DerivedCompletion の `koszulCompletionObject`、`PDCompletionH0` など）を dg nerve で ∞ 関手にし、
反射であることを `IsReflectiveSubcategory`（F2/Presentable）の形で述べる。

## 規約
完備性は元 p, d（基底 prism の生成元）について。一般の有限生成イデアルは A0〜A2 では不要。

## 使われ方
A2-2（Kan 延長の値を (p,d) 完備化する）、A2-4（底変換・テンソルの完備化）、A4（Def 8.2 の Frobenius 余極限の完備化）、
Lemma 4.22（Tot と完備底変換）。2b の後に HA/DerivedCompletion の名前に合わせる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Derived

variable (A : Type u) [CommRing A] (p : ℕ) (d : A)

/-- 概要：D(A) の頂点が導来 (p,d) 完備であること。
方針：複体の表現について `IsModuleComplete`（p と d）。表現によらないことは別の補題。
規約：—
使われ方：完備な対象の部分圏。 -/
def IsDerivedComplete (x : (derivedInfinityCategory A) _⦋0⦌) : Prop := sorry

/-- 概要：完備な対象の充満部分 ∞ 圏 D(A)_comp。
方針：`fullSubcomplex`。
規約：安定（fiber・cofiber・shift で閉じる）、極限で閉じる。
使われ方：Δ の値の圏。 -/
def completeSubcomplex : (derivedInfinityCategory A).Subcomplex := sorry

/-- 概要：完備化 X ↦ X^∧ は包含の左随伴（反射）。
方針：複体の導来完備化（Koszul 塔の極限）を dg nerve で関手にし、単位 X → X^∧ と普遍性。
規約：`IsReflectiveSubcategory` の形。
使われ方：Kan 延長の値の完備化、A4 の余極限の完備化。 -/
theorem completion_isReflective : True := by trivial

def completion : derivedInfinityCategory A ⟶ derivedInfinityCategory A := sorry

/-- 概要：完備化は ⊗^L A/(p^n, d^n)（Koszul）を変えない：X^∧ ⊗^L Kos(p^n,d^n) ≃ X ⊗^L Kos(p^n,d^n)。
方針：複体の計算（HA/DerivedCompletion の CompletionQuotientBaseChange など）。
規約：—
使われ方：完全平坦性の移送（A0-3c）、導来 Nakayama。 -/
theorem completion_tensor_koszul : True := by trivial

/-- 概要：完備化は完全（fiber 列を保つ）。
方針：極限の交換。
規約：—
使われ方：HT filtration の完備化、Lemma 4.22。 -/
theorem completion_exact : True := by trivial

/-- 概要：D(A)_comp の余極限 ＝ D(A) の余極限の完備化（反射的部分圏の余極限）。
方針：左随伴は余極限を保つ。
規約：—
使われ方：A2-2 の sifted 余極限、A4 の Frobenius 余極限。 -/
theorem complete_colimit : True := by trivial

/-- 概要：完備底変換 (− ⊗^L_A B)^∧ : D(A)_comp → D(B)_comp と、prism の射に沿う関手性。
方針：テンソルの ∞ 関手（基盤）と完備化の合成。
規約：—
使われ方：Lemma 4.20・4.22、Construction 6.1、A2-4 (4)。 -/
def completedBaseChange : True := trivial

end SerrePositivity.InfinityCategories.Derived
