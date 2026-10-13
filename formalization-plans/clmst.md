# CLMST とその準備の形式化計画

作成日：2026-10-13。状態：設計段階（原典の主張の書き写し前）。

対象とする版：Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz
multiplicity, and an application to local fundamental groups*, arXiv:2209.04046v4
（以下 CLMST）。準備として、Faltings の正規化長さ、perfectoid 塔、Bhatt–Scholze の perfectoid 化を含む。

## 1. 目的と二つの前提

最終目標は、本論文の定理2.5（混標数の長さ代数の二つの長さの性質、
`mixedPerfectoid_length_properties`）が依存している CLMST の結果を、
**CLMST 自身の形で**述べ直し、そこから本論文への接続を `sorry` なしで証明することである。
CLMST 全体（signature の理論、局所基本群への応用）は対象外とし、本論文で使う範囲に限る。

次の二つを前提とする。

1. **CLMST の形式化と、本論文への接続を分離する。**
   CLMST の層は本論文（`Paper/`）を import しない。接続は別の層に置く。
2. **引用は原典の形で述べて `sorry` にし、接続は形式化する。**
   CLMST の主張は、原典の番号・仮定・結論（almost の主張を含む）のまま名前付きの `sorry` 定理として置く。
   本論文で必要な形への変換（almost から λ へ、`n = 0` への特殊化、塔への制限、設定の変換）は証明する。

### 以前の方針からの変更

現在の `Inputs/CLMST.lean` の三つの引用は、本論文で使う形に特殊化された主張
（Prop 4.0.10 の N = 0 版、Notation 4.0.1 と Cor 4.0.4 を合わせた存在命題、Prop 4.0.14 の n = 0 版）
になっている。この計画では、これらを原典の形の引用に置き換え、
現在の三つの主張は接続層で証明される補題に格下げする。

## 2. 三層の構成

| 層 | 中身 | `sorry` の扱い | import してよいもの |
| --- | --- | --- | --- |
| L0 共通の土台 | 塔 `A_n`・`A^nc_∞`・`A_∞`、`IsIntegralPerfectoid`、`Perfectoidization`、Koszul、パラメータ系、重複度、`NormalizedLength` | なし（既存） | Mathlib、`CommutativeAlgebra/` |
| L1 CLMST 層（`SerrePositivity/CLMST/`、namespace `CLMST`） | CLMST の定義と、引用する主張を原典の形で述べたもの | 引用文は `sorry`。P/G のタグを付ける | L0 のみ。`Paper/` は import しない |
| L2 接続層（`SerrePositivity/Bridge/CLMSTToSerre.lean`） | L1 の主張から定理2.5の二つの長さの性質を導く | **`sorry` なし** | L0、L1、`Paper/Section2` |

`Paper/Section2/MixedLengthAlgebra.lean` はそのまま残し、依存先を `Inputs.CLMST` から L2 に変える。

この分離の利点は、**後で L1 の G の項目を証明しても、L2 と本論文の側は変わらない**ことである。
引用の在庫は「`CLMST/` と `BhattScholze/` の中の `sorry`」と一致し、grep と `#print axioms` で確かめられる。

## 3. L1：CLMST の層

### 3.1 設定（Notation 4.0.1）

`structure CLMST.Setup` にまとめる。

- `R`：完備局所整域、混標数 `(0, p)`、剰余体 `k` は完全体。
- `x = (p, x_2, …, x_d)`：`R` のパラメータ系。
- `A = W(k)[[x_2,…,x_d]] ⊆ R`、`R` は `A` 上有限。
- `0 ≠ g ∈ A`：`A[1/g] → R[1/g]` が有限エタールになる元。

**原典との差 (i)**：`A` は冪級数環そのものではなく、同型
`e : A ≃+* MvPowerSeries … (WittVector p k)` を持つ形で扱う。
字義どおりにすると、接続層で `Perfectoidization` などを `e` に沿って運ぶ必要があり重い。
数学的には同じなので、docstring の「原典との差」に記録する（§8 の決定事項 2）。

### 3.2 定義

| CLMST | Lean | 備考 |
| --- | --- | --- |
| Def 2.2.1（λ**、λ*、λ_∞） | `CLMST.normalizedLength`（`A^nc_∞` 加群で `m_A` 冪ねじれのもの） | 現在の `presentedLength`・`fgLength`・`towerLengthFun`（`Paper/Section2/TowerLength.lean`）を移す |
| §4 の `(g)_perfd` | `CLMST.perfdIdeal g := ker(A_∞ → (A_∞/g)_perfd)` | 現在の `perfectoidIdeal`（`CommutativeAlgebra/Perfectoidization.lean`）を移すか別名にする |
| almost zero、almost flat、almost faithful | `CLMST.AlmostZero`・`AlmostFlat`・`AlmostFaithful` | 「`(g)_perfd` で消える」と、Tor・テンソル積での定義 |
| `R^{A_∞}_perfd` | `CLMST.RPerfd S := (R ⊗_A A_∞)_perfd` | 現在の `MixedPerfectoid` と定義上一致させる |

Serre に要らない `I_∞`、`s_perfd`、`e_perfd`（Def 4.0.6、4.0.8）は今回は定義しない。

### 3.3 引用する主張（すべて `sorry`）

P：恒久的な引用として残す（perfectoid の重い入力）。
G：後で L1 の中で、P の項目と一般論から証明する候補。

| 番号 | 原典の形（要旨） | タグ | 後で証明するときの材料 |
| --- | --- | --- | --- |
| Prop 2.2.3 | λ_∞ は well-defined。有限生成なら λ*、有限表示なら λ** と一致する | G | Gabber–Ramero Lemma 14.5.74 |
| Prop 2.2.6 | (a) 短完全列で加法的。(b) 推移写像が単射、または全射で各値が有限のとき、帰納極限で連続 | G | Faltings Appendix 2、Gabber–Ramero Thm 14.5.75 |
| Ex 2.4.2(1) | `A_∞`（`A^nc_∞` の p 進完備化）は perfectoid | P | |
| Prop 2.4.7 | Thm 2.4.5 の設定で `S` の p^∞ 捩れが有界なら `S → S_perfd` は J-isogeny（各 `g ∈ J` で `g^N` が錐を殺す） | P | |
| Thm 4.0.3 | (a) 全ての `i > 0` と A 加群 `M` で `(g)_perfd · Tor_i^A(RPerfd, M) = 0`。(b) almost faithful | P | |
| Cor 4.0.4 | almost CM 性（正確な形は要確認） | G | Thm 4.0.3 と、局所コホモロジーと Koszul の比較 |
| Prop 4.0.10 | almost zero ⇒ λ_∞ = 0（正確な形は要確認） | G | Prop 2.2.x と `(g)_perfd` の構造 |
| Prop 4.0.14 | パラメータ商の正規化長さ = p^{-nd}·e（正確な形は要確認） | G | Prop 2.4.7、Prop 2.2.6、Euler 標数 |

Bhatt–Scholze の perfectoid 化の存在（Thm 10.11、Prop 8.5。現在の `Inputs/Perfectoidization.lean`）も、
同じ規律で `BhattScholze/` に置く（タグ P）。

**未確認**：Cor 4.0.4、Prop 4.0.10、Prop 4.0.14 の正確な仮定と結論は、まだ原典で確認できていない
（arXiv の PDF は Thm 4.0.3 の証明の途中までしか読めていない）。M0 で確定させる。

### 3.4 主張の書き方の規則

1. **仮定は原典のとおりに置き、本論文に合わせて特殊化しない。**
   一般の `n`、一般の加群 `M` も、本論文で `n = 0` しか使わなくてもそのまま書く。
2. **結論も原典の形で書く。** almost の主張は「`(g)_perfd` で消える」のまま書き、λ に言い換えない。
3. **原典との差は、Lean 上の慣習に限る。** それぞれ docstring に書く。
   - `A` を同型付きで扱う（§3.1 の (i)）。
   - 値域 ℝ ∪ {∞} を `ℝ≥0∞` にする。
   - 原典が暗黙に置く「derived p-complete」（Caution 2.4.4）を明示する。
   - `Perfectoidization` は具体的に選んだものを使う。
4. 各文の docstring には、番号、日本語の要旨、P/G、証明の出典を書く。
5. 名前は `CLMST.prop_4_0_10` のような番号の名前とし、必要なら内容を表す別名を付ける。
6. 新しい恒久的な `axiom` は入れない。class と axiom インスタンスの方式は、
   別プロジェクトとの共有が必要になったときに再検討する。

## 4. L2：接続層

| 補題 | 内容 | 重さ |
| --- | --- | --- |
| B1 設定の変換 | リポジトリの仮定 `(A, D, t, e, he, hres, hinj, …)` から `CLMST.Setup` を作る（`R := D`、`x := t`、`k := ResidueField D`） | 軽い。ただし g の存在が要る（注意 1） |
| B2 環の同一視 | `CLMST.RPerfd = MixedPerfectoid` | 定義上の一致にすれば `rfl` |
| B3 長さの同一視 | CLMST の λ_∞（`A^nc_∞` 上）と `completedTowerLength`・`towerLengthOn` の比較 | 中くらい。既存の `towerLengthOn_eq_completedTowerLength` を使う |
| B4 almost から λ へ | Prop 4.0.10 を特殊化して、現在の `clmst_length_eq_zero_of_perfectoidIdeal_annihilates` を出す | 軽い |
| B5 任意のパラメータ系での Koszul の almost 消滅 | Cor 4.0.4（または Thm 4.0.3）から、現在の `clmst_exists_perfectoidIdeal_annihilates_koszul` を出す | 原典の形しだい（注意 2） |
| B6 重複度 | Prop 4.0.14 を `n = 0` にし、CLMST の e とリポジトリの `HilbertSamuel.multiplicity` を同一視する | 軽いか中くらい |
| B7 冪ねじれ | `isPowTorsion_completedTower_koszul` | 証明済み |

B1〜B7 が揃えば、現在の `Inputs/CLMST.lean` の三つの定理は L2 の補題として `sorry` なしで証明され、
`Inputs/CLMST.lean` は消える。

### 注意

1. **g の取り方（B1）。** CLMST は g に「`A[1/g] → R[1/g]` が有限エタール」を課す。
   現在の存在命題は `g ≠ 0` だけを主張している。標数 0 では分離性が自動なので、generic étaleness から g は取れる。
   これは CLMST ではなく古典的な可換環論の事実で、証明するか、
   別の引用ファイル（`Inputs/GenericEtale.lean`）に置くかを決める。Mathlib の現状は未調査。
2. **B5 が接続層で一番の危険。**
   - Cor 4.0.4 が「D の任意のパラメータ系 y で `H_i(y; RPerfd)` が almost zero」という形なら、B5 は特殊化だけで済む。
   - 局所コホモロジーの形（`H^i_m` が almost zero、`i < d`）なら、Čech と Koszul の比較が接続層に入り、重くなる。
   - Thm 4.0.3 から直接出るのは、A のパラメータ x について `H_i(x;C) = Tor^A_i(A/(x), C)` が almost zero、ということまで。
     そこから任意の y へ移るところが問題になる。
   - 逃げ道：本論文の側が本当に「任意のパラメータ系 z」を必要としているかを下流で確かめる。
     特定の z で足りれば、B5 は軽くなる。

## 5. ファイル配置

```
CommutativeAlgebra/…                       (L0、既存)
CLMST/Tower.lean                           ← Paper/Section2/{Tower,TowerStage,CompletedTower} から移す
CLMST/NormalizedLength.lean                Def 2.2.1、Prop 2.2.3、Prop 2.2.6
CLMST/Setup.lean                           Notation 4.0.1
CLMST/Almost.lean                          (g)_perfd、AlmostZero・AlmostFlat・AlmostFaithful
CLMST/Perfectoid.lean                      Ex 2.4.2、Prop 2.4.7
CLMST/Section4/AlmostCM.lean               Thm 4.0.3、Cor 4.0.4
CLMST/Section4/Length.lean                 Prop 4.0.10、Prop 4.0.14
BhattScholze/Perfectoidization.lean        perfectoid 化の存在
Bridge/CLMSTToSerre.lean                   B1–B7
Paper/Section2/MixedLengthAlgebra.lean     依存先を Bridge に変えるだけ
```

L1 は `Paper/` を import しないので、塔の定義を `Paper/Section2` から移すリファクタが要る。
`Paper` 側には別名を残して、既存のコードを壊さない（§8 の決定事項 3）。

## 6. 依存関係

- L1 の中：Cor 4.0.4 ← Thm 4.0.3。Prop 4.0.10 ← Prop 2.2.x と `(g)_perfd`。Prop 4.0.14 ← Prop 2.4.7、Prop 2.2.6。
  Thm 4.0.3 ← Ex 2.4.2、Bhatt–Scholze。
- L2：B4 ← Prop 4.0.10。B5 ← Cor 4.0.4（または Thm 4.0.3）。B6 ← Prop 4.0.14。B1–B3 は定義だけに依存。
- 本論文：`mixedPerfectoid_length_properties` ← B1–B7 → 定理2.5。

## 7. マイルストーンと完了条件

| 段 | 作業 | 完了の条件 |
| --- | --- | --- |
| M0 書き写し | CLMST §2.2、§2.4、§4 の対象の主張を原典から書き写し、Lean の主張の草案と突き合わせる | 主張表の確定。B5 の重さがここで決まる |
| M1 リファクタ | 塔と λ_∞ の定義を `CLMST/` に移す。主張は変えない | `lake build` が通り、`sorry` の集合が変わらない |
| M2 L1 の主張 | 引用文を `sorry` で書く | ビルドが通る。各文に docstring（番号、要旨、P/G、出典、原典との差） |
| M3 L2 | B1〜B7 を書き、`Inputs/CLMST.lean` を消す | `CLMST/` と `BhattScholze/` の外に CLMST 由来の `sorry` がない。`#print axioms mixedPerfectoid_length_properties` の `sorryAx` が L1 経由だけ |
| M4（独立、後で） | G の項目を L1 の中で証明する | 接続層と本論文の側は変更しない |

各段で `lake build` と `#print axioms` を確かめる。`native_decide` は使わない。
途中で壊れた部分的な証明を残さない。

## 8. 決めること

1. **原典の入手。** CLMST の PDF を手元から添付するか、ブラウザで読む。
2. **A の書き方。** 同型付き（§3.1 の (i)、推奨）か、字義どおりの冪級数環か。
3. **塔の定義の置き場所。** `CLMST/` に移すか、`CommutativeAlgebra/` に置いて両方から使うか。
4. **「任意のパラメータ系 z」の必要性。** 本論文の下流が全ての z を使うか（B5 の重さに直結）。
5. **generic étaleness。** 証明するか、古典的な引用として置くか。

## 9. 次の具体的な作業

1. M0：原典から Def 2.2.1、Prop 2.2.3、Prop 2.2.6、Ex 2.4.2、Prop 2.4.7、Notation 4.0.1、
   Thm 4.0.3、Cor 4.0.4、Prop 4.0.10、Prop 4.0.14 を書き写し、Lean の主張の草案を付けた表を作る。
2. 決定事項 4 を、下流（定理2.5 以降で `mixedPerfectoid_length_properties` を使う箇所）を読んで確かめる。
3. M1 と M2 の形式化担当への指示文（完全な形）を作る。

## 10. 参照資料

- CLMST：arXiv:2209.04046v4。
- Gabber–Ramero, *Foundations for almost ring theory*（§14.5）。
- Faltings, *Almost étale extensions*, Astérisque 279 (2002), Appendix 2。
- Bhatt–Scholze, *Prisms and prismatic cohomology*（§8、§10）。
- Bhatt–Iyengar–Ma, arXiv:1803.03229（Lemma 4.1.2 の背景。今回は対象外）。
- 現在のコード：`Inputs/CLMST.lean`、`Paper/Section2/TowerLength.lean`、
  `Paper/Section2/MixedLengthAlgebra.lean`、`Inputs/PerfectoidTower.lean`、`Inputs/Perfectoidization.lean`。
