# BS-D2 作業報告

## 第1部　A0 の Frobenius の標的で途中停止

開始時の HEAD は main `68ed1ec05`、作業ツリー・index は空。最初の `prismaticCohomologyFrobenius` の標的について、design-status §2 (A) と D2 指示書 §1 が指す既存宣言を調べた。必要な∞関手と既存宣言の型が異なるため、指示書 §0 の停止条件に従って `True` を残した。具体化した対象宣言は0件。A4 以降は未着手で、停止点1には未到達。

### 指定された名前と必要な型

環準同型 `f : S →+* T` に対し、必要なのは各 T 加群の作用を `s • m = f(s) • m` として読む導来スカラー制限、すなわち `derivedInfinityCategory T ⟶ derivedInfinityCategory S` である。A0 では `f = P.deltaStructure.frobeniusLift : A →+* A`。この関手を Δ の頂点で評価して初めて、Frobenius の標的 φ_{A*}Δ が決まる。

| 照合した宣言 | ソースで確認した型と役割 |
| --- | --- |
| `DGRestrictScalars`、`dgNerveRestrictScalarsIso`（InfinityCategories/Derived/ScalarRestrictionNerve.lean:24,128） | T 線形 dg 圏 D の Hom の係数を S に制限する。得られる同型は `dgNerve S (DGRestrictScalars f D) ≅ dgNerve T D` で、対象は同じ。D に `Semifree T` を入れても左辺の対象は T 上の semifree 複体である。 |
| `derivedInfinityCategory`、`derivedInfinityBaseChange`（InfinityCategories/Derived/InfinityCategory.lean:23、BaseChange.lean:22） | D(S) の模型は `dgNerve S (Semifree S)`。底変更は `derivedInfinityCategory S ⟶ derivedInfinityCategory T` で、係数拡大の dg 関手に上記の nerve 同型を合成して作る。 |
| `derivedRestrictScalars`、`derivedRestrictScalarsFactors`（HomologicalAlgebra/DerivedRestriction.lean:17,22） | 通常の導来圏の関手 `DerivedCategory (ModuleCat T) ⥤ DerivedCategory (ModuleCat S)` と、複体の各項での制限との比較。必要な作用と向きは持つが、∞圏の間の単体的集合の射はこの型から取り出せない。 |

S = T = A の場合にも区別は残る。例えば有界 prism (ℤ_p[[x]], (p)) で係数には恒等、x には x^p を施す Frobenius 持ち上げを取る。自由加群 A のスカラー制限は x の作用が x^p 倍となり、A 加群として 1, x, …, x^{p−1} を基底に持つ。dg nerve の係数制限同型はその自由加群を同じ対象に保つ。これは Frobenius 射そのものへの反例ではなく、二つの操作の違いである。

### 再開に要る仕様

導来スカラー制限 Res_f の∞圏での入口を指定する。例えば `Res_f : derivedInfinityCategory T ⟶ derivedInfinityCategory S` を `derivedInfinityBaseChange f` の右随伴として指定すれば、逆向きの関手とその意味が揃う。A0 の結論は Δ から `Res_f.app _ Δ` への辺となる。構成では S2 の `derivedGlobalSections_map` に O_Δ → Res_f O_Δ を渡し、標的の RΓ を Res_f Δ と比較する。A4 の CAlg 値の制限とその正の反復についても別途型を照合する。

今回は未発見名を Lean に仮置きした箇所は0件。調査は本体・drafts・Mathlib のソース検索のみで、Lean 実行・型検査・ビルドはしていない。
