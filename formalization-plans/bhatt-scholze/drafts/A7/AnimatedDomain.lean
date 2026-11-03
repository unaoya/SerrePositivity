-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.AnimatedDomain（仮。原典 Def 8.2 の定義域「導来 p 完備な animated R 代数」）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.1・§5（配置、W9-II-24）、単位 A7-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
-- 本ファイルは drafts/A2/AnimatedAlgebra.lean、drafts/DerivedGeneral/CompletionFunctor.lean だけを import する（A5 より先に置く）。

/-!
# animated 代数の定義域（G-A7-1、BS 著者版 Def 8.2 の定義域）

## 概要
`AnimatedAlgebra R`（A2-1 の P_Σ(Poly_R)）の底の D(R) 対象 `animatedForget`、導来 p 完備な animated R 代数の充満部分 ∞ 圏 `CompleteAnimatedAlgebra R`、
導来 p 完備化 `animatedCompletion`、離散な導来 p 完備環の埋め込みとの整合。

## 方針
W9-II-24 で A7/AnimatedPerfectoidization.lean から切り出した。D45 改訂後の A5（Prop 8.5 の animated 版、`perfectionComparison_isIso_animated`）が
この定義域を使うので、A5 より先に import できる独立ファイルにする。所有単位は A7-1 のまま。

## 規約
基底は Not 8.1 の完全 prism（R = A/d）。導来 p 完備性は底の D(R) 対象で判定する。

## 使われ方
A5-1（Prop 8.5 の animated 版）、A7-1（Def 8.2 の animated 版、Prop 8.13）、A7-2（X = S_perfd ⊗̂^L_S S_perfd）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## G-A7-1：底の加群、完備性、完備化 -/

/-- 概要：animated R 代数の底の D(R) 対象：Poly_R → D(R)（多項式環を離散加群として）の sifted 余極限を保つ延長。
方針：A2-1 の `exists_siftedExtension`（HTT 5.5.8.15）。
規約：`AnimatedAlgebra R ⟶ derivedInfinityCategory R`。
使われ方：導来 p 完備性の定義、A2-2 の Δ との整合（Δ の底）。 -/
def animatedForget : AnimatedAlgebra R ⟶ derivedInfinityCategory R := sorry

/-- 概要：導来 p 完備な animated R 代数の充満部分 ∞ 圏（原典 Def 8.2 の定義域）。
方針：`animatedForget` の像が `IsDerivedComplete`（DerivedGeneral/CompletionFunctor）であるような頂点の fullSubcomplex。
規約：`SSet` の部分複体。
使われ方：Def 8.2、Prop 8.13。 -/
def CompleteAnimatedAlgebra : SSet.{u + 1} := sorry

/-- 概要：animated R 代数の導来 p 完備化（反射的局所化、代数構造と両立）。
方針：D(R) の完備化（DerivedGeneral/CompletionFunctor）は対称モノイダルな局所化なので代数に持ち上がる（要確認：P_Σ 上の構成）。W9 続き 6 の補記：animated 圏での
構成も記す——単体的可換環としての導来 mod p^n の逆極限（π_0 の商の遷移が全射なので lim¹ は現れず animated 圏に留まる）、底の加群で完備性を判定し、完備対象への反射
という普遍性で特徴づける。
規約：`AnimatedAlgebra R ⟶ CompleteAnimatedAlgebra R` と単位。
使われ方：完備テンソル S_1 ⊗̂^L_{S_3} S_2。 -/
def animatedCompletion : True := trivial

/-- 概要：導来 p 完備な離散 R 代数は `discreteToAnimated`（A2-1）で `CompleteAnimatedAlgebra` に入る。
方針：離散環の底は離散加群。
規約：—
使われ方：離散版との一致。 -/
theorem discreteToAnimated_complete : True := by trivial

end SerrePositivity.BhattScholze.Perfectoidization.Derived
