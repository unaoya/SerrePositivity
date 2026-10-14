# 外部引用5：交点重複度の消滅定理をサイクルで証明する計画

作成：2026-10-14。状態：計画のみ。実装は未着手。
対象の宣言は [Inputs/IntersectionTheory.lean](../SerrePositivity/Inputs/IntersectionTheory.lean) の
`Inputs.intersectionVanishing`（Roberts–Gillet–Soulé の消滅定理、論文 (5.1)）。

経路の候補は [4〜5の計画](intersection-inputs-4-5.md) の §3 で比較した。
この文書では **候補A（局所 Chern 指標と Riemann–Roch、つまりサイクルの経路）を優先する** と決め、その段階を定める。
候補B（支持つきK理論と Adams 作用素）は廃止せず、並行して試す余地を残す。

## 1. 主張と、今の引用の使われ方

正則局所環 `R` と有限生成加群 `M, N` について、`M ⊗_R N` が有限長で
`dim M + dim N < dim R` なら `χ^R(M, N) = 0`。混標数を含む。

利用先は二つ。主定理の帰着（Lemma 5.1、`IntersectionMultiplicity/Devissage`）と、
第一比較のランクの因子（Lemma 5.2、`IntersectionMultiplicity/FiniteExtension`）。
4番（Serre の等標数正値性）を対角線の議論で証明する場合にも、次元の和が小さい成分を消すのに使える。

## 2. 証明の骨格（Roberts）

`F_•`、`G_•` を `M`、`N` の有限自由分解とする。局所 Chern 指標 `ch(F_•)` は、
`Supp M` に台をもつ perfect 複体から定まる作用素で、Chow 群の次数を `i` だけ下げる。

\[
\mathrm{ch}_i(F)\colon A_k(X)_{\mathbb Q}\to A_{k-i}(\operatorname{Supp}M)_{\mathbb Q}.
\]

1. **局所 Riemann–Roch**：`χ(M, N) = deg(ch(F) ch(G) ∩ τ(R))`。
2. **正則なら Todd 類は自明**：`τ(R) = [Spec R]`。
3. **次元の勘定**：`ch_i(F) ∩ [R]` は `A_{d−i}(Supp M)` にあるので、0 でないには `d − i ≤ dim M`。
   同様に `d − j ≤ dim N`。閉点の `A_0` に落ちるには `i + j = d`。
   よって 0 でない項があれば `dim M + dim N ≥ d`。可換性 `ch(F) ch(G) = ch(G) ch(F)` を使う。

3 は短い。重いのは 1・2 と、局所 Chern 指標の構成である。
混標数を含めるため、`Spec R` を正則な基底上の有限型スキームとして扱う Fulton 第20章の枠組みを使う。

## 3. 段階

| 段 | 内容 | 原典 | 備考 |
| --- | --- | --- | --- |
| Z0 | 正則な基底上の有限型スキームの次元関数、サイクル、有理同値、Chow 群 `A_*(X)`、連接層のサイクル `[𝓕]_k` | Fulton 第1章、§20.1 | 別プロジェクトで作るサイクルの基盤と共有する。Mathlib の `AlgebraicGeometry.AlgebraicCycle`（局所有限な台の関数）と `Scheme.OrderOfVanishing`（余次元1の位数）を出発点にする |
| Z1 | 固有押し出し、平坦引き戻し、閉点の `A_0 = ℤ` と次数写像 | 第1章 | Z0 と同じく共有 |
| Z2 | ベクトル束の Chern 類・Segre 類（射影束）、`ℚ` 係数の Chern 指標 | 第2〜3章 | 共有の候補 |
| Z3 | 台つき perfect 複体の局所 Chern 指標（graph construction）。加法性、乗法性、可換性、台、次数のずれ | 第18章 §18.1、Roberts の本（*Multiplicities and Chern Classes in Local Algebra*）第11〜12章 | このプロジェクトに固有の中心部分 |
| Z4 | 局所 Riemann–Roch と、正則なら `τ(R) = [Spec R]` | 第18章、第20章 | 最も深い。まず名前つきの引用として置き、Z5 を先に完成させる |
| Z5 | 次元の勘定から `intersectionVanishing` を証明する | Roberts | Z3 の性質と Z4 があれば短い |

## 4. 進め方

1. Z0〜Z2 は別プロジェクトとインターフェースを先に合わせる。
   こちらでは、局所環の Spec と、その閉部分スキームに必要な範囲だけを使う。
   同じ定義を二つのプロジェクトで別々に作らない。
2. Z4 を名前つきの引用として先に置き、Z3 と Z5 を完成させる。
   この時点で `intersectionVanishing` は「Riemann–Roch の引用」に置き換わる。
   主定理の未証明入力の件数は変わらないが、引用の範囲は狭まる。
3. その後 Z4 を証明する。

## 5. 受入条件

- `Inputs.intersectionVanishing` の公開型を保ったまま、直接の `sorry` を除く。
- Z4 を引用として置く段階では、その引用の原典・番号・適用範囲を docstring に明記し、件数の台帳を更新する。
- 局所 Chern 指標の性質（Z3）は、引用ではなく証明で供給する。
- 利用先（`Devissage`、`FiniteExtension`）とその下流のビルドと公理監査が通る。

## 6. 参照

- W. Fulton, *Intersection Theory*（第1〜3章、第18章、第20章）。
- P. Roberts, *Multiplicities and Chern Classes in Local Algebra*（第11〜13章）。
- P. Roberts, *The vanishing of intersection multiplicities of perfect complexes*, Bull. AMS 13 (1985)。
- H. Gillet, C. Soulé, *Intersection theory using Adams operations*, Invent. Math. 90 (1987)（候補B）。
