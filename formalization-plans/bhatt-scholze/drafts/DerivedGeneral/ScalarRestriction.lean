-- 将来の置き場所：D 版は SerrePositivity.InfinityCategories.Derived.ScalarRestriction（仮。DerivedGeneral 2 本と同じ M13、`InfinityCategories/Derived/`、段 G・W2b 後）、
-- CAlg 版（`cAlgRestrictScalars` と忘却との比較）は EInfinity 側（M14 の隣、調整役）。11-03 に CAlg 版を追加（BS-D2 の指摘：A4 の塔は CAlg_A の中）。
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.1（Frobenius）、a4-design.md §2.1（塔 φ_{A*}^n、W9-II-01）。基準コミット 68ed1ec05。ビルドなし。
-- 2026-11-03（BS-D2 の質問への回答）：本体の `Derived/ScalarRestrictionNerve.lean` の `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数を制限する同型で、
-- D(T) → D(S) の関手ではない。必要なのは係数制限の ∞ 関手そのものなので、ここに基盤待ちの宣言として置く。
module

public import SerrePositivity.InfinityCategories.Derived.BaseChange
public import SerrePositivity.InfinityCategories.Derived.ScalarRestrictionNerve
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived

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
A0 `prismaticCohomologyFrobenius`（Δ → φ_{A*}Δ、D 版）、A4 `frobeniusTower`・`prismaticPerfection`（CAlg 版と忘却の比較）、A5 の比較写像の脚 f_n = φ_B^{-n} ∘ f : Res_φ^n Δ_S → B。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.InfinityCategories

open SerrePositivity.EInfinity

variable {S T : Type u} [CommRing S] [CommRing T]
-- 11-03（BS-D2 の指摘）：f は型に現れないので section 変数にせず、各宣言の明示引数にする。

/-- 概要：f に沿う係数制限の ∞ 関手 f_* : D(T) → D(S)。
方針：dg 模型の忘却関手の dg nerve（`dgNerveRestrictScalarsIso` で係数制限は nerve を変えない）を D(T) → D(S) の射に。
規約：基盤待ち（M13）。f は明示引数。
使われ方：φ_{A*}。 -/
def derivedInfinityRestrictScalars (f : S →+* T) : derivedInfinityCategory T ⟶ derivedInfinityCategory S := sorry -- 基盤待ち（M13）

/-- 概要：底変換と係数制限の随伴 f^* ⊣ f_*（Map(f^* X, Y) ≃ Map(X, f_* Y)）。
方針：dg 模型の tensor-hom 随伴を nerve に移す。主張の形（∞ 随伴の述語）は基盤の名前が決まってから。
規約：基盤待ち。
使われ方：φ_A 半線形な射 Δ → φ_{A*}Δ を f^*Δ → Δ と読み替える所（A4 の塔の余極限）。 -/
theorem derivedInfinityBaseChange_restrictScalars_adjunction (f : S →+* T) : True := by trivial -- 基盤待ち（M13）

/-- 概要：合成との両立：(g ∘ f)_* ≃ f_* ∘ g_*、id_* ≃ id（反復 φ_{A*}^n に使う）。
方針：忘却関手の合成。
規約：可逆な辺（`FunctorIso`）で述べる（頂点の等号ではない）。
使われ方：A4 `frobeniusTower` の φ_{A*}^n。 -/
def derivedInfinityRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    FunctorIso (derivedInfinityRestrictScalars (g.comp f))
      (derivedInfinityRestrictScalars g ≫ derivedInfinityRestrictScalars f) := sorry -- 基盤待ち（M13）
def derivedInfinityRestrictScalars_id : FunctorIso (derivedInfinityRestrictScalars (RingHom.id S)) (𝟙 _) := sorry -- 基盤待ち（M13）

/-! ## CAlg 版（A4 の塔は CAlg_A の中、D35）。置き場所は EInfinity 側（M14 の隣、調整役）。 -/

/-- 概要：f に沿う E∞ 代数の係数制限 f_* : CAlg(T) → CAlg(S)（T 代数を S 代数として読む）。
方針：Barratt–Eccles 代数の忘却（作用素は同じ、係数だけ制限）の nerve。
規約：基盤待ち（M13 の CAlg 版。置き場所は `EInfinity/`、調整役）。f は明示引数。
使われ方：A4 `frobeniusTower`（CAlg_A の図式 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯）、A5 の比較写像の脚。 -/
def cAlgRestrictScalars (f : S →+* T) : CAlg_R T ⟶ CAlg_R S := sorry -- 基盤待ち

/-- 概要：忘却との両立：U_S ∘ f_*^{CAlg} ≃ f_*^{D} ∘ U_T（`cAlgForgetDerived`）。
方針：どちらも台の複体の忘却。
規約：`FunctorIso`。
使われ方：A4 の塔の余極限を D(A) で計算してから CAlg に戻す所、Lemma 8.4 (a)。 -/
def cAlgRestrictScalars_forget (f : S →+* T) :
    FunctorIso (cAlgRestrictScalars f ≫ cAlgForgetDerived S)
      (cAlgForgetDerived T ≫ derivedInfinityRestrictScalars f) := sorry -- 基盤待ち

/-- 概要：CAlg 版の合成・恒等との両立（D 版と同じ形）。 -/
def cAlgRestrictScalars_comp {U : Type u} [CommRing U] (f : S →+* T) (g : T →+* U) :
    FunctorIso (cAlgRestrictScalars (g.comp f)) (cAlgRestrictScalars g ≫ cAlgRestrictScalars f) := sorry -- 基盤待ち
def cAlgRestrictScalars_id : FunctorIso (cAlgRestrictScalars (RingHom.id S)) (𝟙 _) := sorry -- 基盤待ち

end SerrePositivity.InfinityCategories
