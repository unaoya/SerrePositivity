-- 将来の置き場所：SerrePositivity.InfinityCategories.Derived.ScalarRestriction（仮。DerivedGeneral 2 本と同じ M13、`InfinityCategories/Derived/`、段 G・W2b 後）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.1（Frobenius）、a4-design.md §2.1（塔 φ_{A*}^n、W9-II-01）。基準コミット 68ed1ec05。ビルドなし。
-- 2026-11-03（BS-D2 の質問への回答）：本体の `Derived/ScalarRestrictionNerve.lean` の `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数を制限する同型で、
-- D(T) → D(S) の関手ではない。必要なのは係数制限の ∞ 関手そのものなので、ここに基盤待ちの宣言として置く。
module

public import SerrePositivity.InfinityCategories.Derived.BaseChange
public import SerrePositivity.InfinityCategories.Derived.ScalarRestrictionNerve

/-!
# 係数制限の ∞ 関手 f_* : D(T) → D(S)（基盤待ち、M13）

## 概要
環準同型 f : S → T に沿う係数制限（忘却）の ∞ 関手 `derivedInfinityRestrictScalars f : derivedInfinityCategory T ⟶ derivedInfinityCategory S`。
既存の底変換 `derivedInfinityBaseChange f : D(S) ⟶ D(T)`（f^* = − ⊗^L_S T）の右随伴。

## 方針
dg 模型では T 複体を S 複体として読む忘却関手で、dg nerve との両立は本体 `dgNerveRestrictScalarsIso`（係数制限しても dg nerve は変わらない）。
∞ 関手としての構成と随伴は基盤側（M13、DerivedGeneral の完備化関手と同じ窓）。

## 規約
f は任意の環準同型。A0・A4 では f = φ_A（prism の Frobenius、一般には可逆でない）で φ_{A*} := `derivedInfinityRestrictScalars φ_A`。
塔 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯ は正の反復（W9-II-01。A 完全なら φ_{A*} ≃ (φ_A^{-1})^* だが、A0 の有界 prism では使わない）。

## 使われ方
A0 `prismaticCohomologyFrobenius`（Δ → φ_{A*}Δ）、A4 `frobeniusTower`・`prismaticPerfection`、A5 の比較写像の脚 f_n = φ_B^{-n} ∘ f : Res_φ^n Δ_S → B。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.InfinityCategories

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 概要：f に沿う係数制限の ∞ 関手 f_* : D(T) → D(S)。
方針：dg 模型の忘却関手の dg nerve（`dgNerveRestrictScalarsIso` で係数制限は nerve を変えない）を D(T) → D(S) の射に。
規約：基盤待ち（M13）。
使われ方：φ_{A*}。 -/
def derivedInfinityRestrictScalars : derivedInfinityCategory T ⟶ derivedInfinityCategory S := sorry -- 基盤待ち（M13）

/-- 概要：底変換と係数制限の随伴 f^* ⊣ f_*（Map(f^* X, Y) ≃ Map(X, f_* Y)）。
方針：dg 模型の tensor-hom 随伴を nerve に移す。主張の形（∞ 随伴の述語）は基盤の名前が決まってから。
規約：基盤待ち。
使われ方：φ_A 半線形な射 Δ → φ_{A*}Δ を f^*Δ → Δ と読み替える所（A4 の塔の余極限）。 -/
theorem derivedInfinityBaseChange_restrictScalars_adjunction : True := by trivial -- 基盤待ち（M13）

/-- 概要：合成との両立：(g ∘ f)_* ≃ f_* ∘ g_*、id_* ≃ id（反復 φ_{A*}^n に使う）。
方針：忘却関手の合成。
規約：可逆な辺で述べる（頂点の等号ではない）。
使われ方：A4 `frobeniusTower` の φ_{A*}^n。 -/
theorem derivedInfinityRestrictScalars_comp : True := by trivial -- 基盤待ち（M13）
theorem derivedInfinityRestrictScalars_id : True := by trivial -- 基盤待ち（M13）

end SerrePositivity.InfinityCategories
