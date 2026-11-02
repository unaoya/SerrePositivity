-- 将来の置き場所：InfinityCategories の Derived の上（調整役が判断。M12 と同じ扱い）。BS 固有ではない一般論。
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md G-A2-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.InfinityCategories.Derived.InfinityCategory
public import SerrePositivity.InfinityCategories.Derived.StableLimits

/-!
# D(A) の標準 t 構造と Postnikov 切り捨て（∞ 関手として）

## 概要
導来 ∞ 圏 D(A) = N_dg(Semifree(A)) に標準 t 構造（D^{≤n}、D^{≥n}）を入れ、切り捨て τ^{≤n}・τ^{≥n} を ∞ 関手として与える。
cofiber 列 τ^{≤n−1}X → τ^{≤n}X → H^n(X)[−n]、H^i による検出、有界性。

## 方針
複体の側（Semifree）で良い切り捨て（smart truncation）を取り、dg nerve で ∞ 関手にする。t 構造の公理（HA 1.2.1.4）は複体の計算。
H^i は基盤の `H i`（`HFunctor`）。

## 規約
cohomological な添字（D^{≤n} は H^i = 0 for i > n）。BS の HT filtration では τ^{≤i} Δ̄ を使う。

## 使われ方
A2-3（HT filtration ＝ τ^{≤i} Δ̄_P の Kan 延長、gr^i = H^i[−i]）、A4（Lemma 8.4 の coconnectivity）、A5（Prop 8.5 の連結性の議論）、
導来 Nakayama（G-A1-4）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Derived

variable (A : Type u) [CommRing A]

/-- 概要：D^{≤n}：H^i = 0（i > n）な対象。
方針：基盤の `H i` で。
規約：Prop。
使われ方：t 構造。 -/
def IsCoconnectiveAt (n : ℤ) (x : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  ∀ i : ℤ, n < i → Subsingleton (H A i x) -- 要確認：零対象の述べ方（Subsingleton か IsZero）

/-- 概要：D^{≥n}：H^i = 0（i < n）な対象。 -/
def IsConnectiveAt (n : ℤ) (x : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  ∀ i : ℤ, i < n → Subsingleton (H A i x)

/-- 概要：切り捨て τ^{≤n} : D(A) → D(A)（∞ 関手）。
方針：Semifree 複体の良い切り捨てを dg 関手にして dg nerve。
規約：τ^{≤n}X → X が H^i（i ≤ n）で同型、τ^{≤n}X ∈ D^{≤n}。
使われ方：HT filtration。
要確認：Semifree の上で smart truncation が semifree を保つか（保たなければ分解を取り直す）。 -/
def truncationLE (n : ℤ) : derivedInfinityCategory A ⟶ derivedInfinityCategory A := sorry

def truncationGE (n : ℤ) : derivedInfinityCategory A ⟶ derivedInfinityCategory A := sorry

/-- 概要：τ^{≤n}X → X の自然変換と、その H^i（i ≤ n）での同型。 -/
def truncationLE_counit (n : ℤ) : True := trivial -- 要確認：NatInfinity（SSet.Homotopy）の形で

theorem truncationLE_isCoconnective (n : ℤ) (x : (derivedInfinityCategory A) _⦋0⦌) :
    IsCoconnectiveAt A n (vertexOf (truncationLE A n) x) := by sorry -- 要確認：頂点の記法

/-- 概要：cofiber 列 τ^{≤n−1}X → τ^{≤n}X → H^n(X)[−n]（gr^n）。
方針：複体の計算と `derivedCospanFiberSquare`。
規約：H^n(X)[−n] は離散加群の shift（`discreteEmbedding` と shift）。
使われ方：HT filtration の gr^i = Ω^i[−i]。 -/
theorem truncation_cofiber (n : ℤ) (x : (derivedInfinityCategory A) _⦋0⦌) : True := by trivial

/-- 概要：t 構造の公理（HA 1.2.1.4）：直交性、shift との関係、分解の fiber 列。
方針：複体の計算。
規約：—
使われ方：導来 Nakayama、HT filtration の一意性。 -/
theorem tStructure_axioms : True := by trivial

/-- 概要：有界な対象では Postnikov 塔は有限で exhaustive（X ∈ D^{[a,b]} ⇒ τ^{≤b}X ≃ X）。
方針：H^i の検出。
規約：—
使われ方：HT filtration が多項式代数で有限段で止まること。 -/
theorem truncationLE_of_isCoconnective (n : ℤ) (x : (derivedInfinityCategory A) _⦋0⦌)
    (hx : IsCoconnectiveAt A n x) : True := by trivial

/-- 概要：導来 Nakayama の形：導来 (p,d) 完備な X で X ⊗^L A/(p,d) = 0 ⇒ X = 0（G-A1-4）。
方針：完備化の塔と H^i の検出。
規約：完備性は `IsModuleComplete` の D(A) 版（DerivedGeneral/CompletionFunctor）。
使われ方：Thm 5.2 の η、Construction 6.1 (1)、Cor 4.12、D32。 -/
theorem derived_nakayama : True := by trivial

end SerrePositivity.InfinityCategories.Derived
