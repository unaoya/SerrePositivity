# arxiv_formalization との共通基盤の検討課題

作成：2026-10-14。状態：検討課題の記録のみ。統合の作業は未着手で、どちらのリポジトリも相手を import していない。

対象は、K 理論の基盤として作った群論・モノイダル圏論の部分と、
[arxiv_formalization](https://github.com/unaoya/arxiv_formalization)（確認したコミット `761bc6b`）の対応する部分である。

## 1. 現状

### 移植済み：型 A の Coxeter 群

- 元：`ArxivFormalization/Coxeter/TypeA.lean`
- 先：[GroupTheory/Coxeter/TypeA.lean](../SerrePositivity/GroupTheory/Coxeter/TypeA.lean)
- 内容：型 A の Coxeter 群と `Equiv.Perm (Fin (n + 1))` の同型 `typeAEquivPerm`（単射性は挿入ソートの正規形による）。
- 使用先：[Monoidal/PermutationAction.lean](../SerrePositivity/CategoryTheory/Monoidal/PermutationAction.lean) が
  `CoxeterSystem.lift` とこの同型から、反復テンソルへの対称群作用 `Perm (Fin n) →* Aut (X^{⊗n})` を作る。
- 出典・SHA256・版差の修正・同期方針は [Coxeter/README.md](../SerrePositivity/GroupTheory/Coxeter/README.md)。

### 独立に作った、内容の重なる部分

| arxiv_formalization | SerrePositivity | 違い |
| --- | --- | --- |
| `KnotTheory/Monoidal/Power.lean`：`tensorPower X (n+1) = tensorPower X n ⊗ X` | [Monoidal/TensorPowers.lean](../SerrePositivity/CategoryTheory/Monoidal/TensorPowers.lean)：`power X (n+1) = X ⊗ power X n` | 括弧の向きが逆（右因子を足すか、左因子を足すか） |
| `KnotTheory/Braid/CategoricalAction.lean`：braided 圏で、隣接 braiding・遠隔可換性・Yang–Baxter から組み紐群作用 `BraidGroup n →* Aut (tensorPower X n)` | [Monoidal/AdjacentTranspositions.lean](../SerrePositivity/CategoryTheory/Monoidal/AdjacentTranspositions.lean)、[AdjacentBraid.lean](../SerrePositivity/CategoryTheory/Monoidal/AdjacentBraid.lean)、[PermutationAction.lean](../SerrePositivity/CategoryTheory/Monoidal/PermutationAction.lean)：対称モノイダル圏で、隣接交換の対合性・遠隔可換性・braid 関係から対称群作用 | 証明の骨格は同じ。数学的には、組み紐群作用が対称群を経由するという関係 |

`formalization-plans/k-theory.md` §26 の再利用調査は TypeA と FreeRibbon を扱い、
上の二つには言及していない。FreeRibbon は rigid・ribbon 構造を要求するため取り込んでいない。

### 対応物のない部分

`Monoidal/` の連結の整合性（`TensorPowerCoherence`、`TensorPowerBlock*`、`TensorPowerFirstCrossing*`）、
有限全単射圏への関手化（`PowerBijection*`）、モノイド上の加群
（`BalancedTensor*`、`FreeModule*`、`Module*`）、および `CategoryTheory/FiniteBijection*.lean` には、
arxiv_formalization 側に対応するものを確認していない。

## 2. 検討課題

1. **テンソル冪の括弧の向き。** どちらかに揃えるか、両者の間の比較同型を作るか。
   揃える場合、SerrePositivity 側は連結の整合性・ブロック置換・球面対称列が `power` の定義に依存しているので影響が大きい。
2. **組み紐群作用と対称群作用の一本化。** 対称モノイダル圏では組み紐群作用が
   `BraidGroup n → Perm (Fin n)` を経由することを示し、`categoricalAction` と `PermutationAction` を一つの理論にまとめるか。
3. **共通基盤の置き場所。** 群論（Coxeter）と一般のモノイダル圏論を、独立したパッケージ（または一方のリポジトリ）に置き、
   両方から依存する形にするか。Lean・Mathlib の版の違い（SerrePositivity は v4.35.0-rc4、arxiv_formalization の環境は確認時点で依存先が欠けていた）も合わせて考える。
4. **重複の確認範囲。** 今回は `MonoidalCategory`・`BraidedCategory`・`MonoidalClosed`・`Mod_` などの名前で探しただけで、
   arxiv_formalization の全体（KnotTheory の TemperleyLieb、FreeRibbon の Monoidal・Braided など）との網羅的な比較はしていない。

## 3. 進め方の原則

- 統合は数学的に独立した部分（群論・一般のモノイダル圏論）から行い、スペクトル・論文固有の部分は持ち込まない。
- 移植するときは、出典のコミット・SHA256・変更点を [Coxeter/README.md](../SerrePositivity/GroupTheory/Coxeter/README.md) と同じ形で記録する。
- 片方のリポジトリ全体を Lake の依存に追加する方針はとらない（k-theory.md §26 と同じ）。
