# CLMST とその準備の形式化計画

作成・更新日：2026-10-13。状態：原典照合・実装境界の詳細設計段階。
原典は `paper/refs/CLMST-2209.04046v4.pdf`（手元のみ）と
[同じ版の HTML](https://arxiv.org/html/2209.04046v4)。新しい Lean 実装はこの更新には含まない。

具体的な型の設計、共通基盤の抽出順、接続の受入条件は
[実装境界と作業単位](clmst-interfaces.md)にまとめる。

対象とする版：Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz
multiplicity, and an application to local fundamental groups*, arXiv:2209.04046v4
（以下 CLMST）。準備として、Faltings の正規化長さ、perfectoid 塔、Bhatt–Scholze の perfectoid 化を含む。

## 0. 実装の進捗（2026-10-13）

初回の共通層抽出を実装した。有限段・塔・有限表示降下・λ**／λ*／λ∞の数値定義、
完備化の環、任意の正規化長さの係数制限、Koszul の冪ねじれを論文非依存のモジュールに分けた。
既存の宣言名を保持し、旧 Paper モジュールから互換 import する。
数値関数には全射による λ* の単調性と、有限表示加群での λ*≤λ** の証明も追加した。

C1/C2 の仮定と利用先の [監査](clmst-length-audit.md)を作成した。
引用はまだ既存の二宣言に保持しており、原典の標準基底へ狭める変更は未実装。
等標数の表示情報の伝播など、必要な変更を監査に記録した。

有限整域拡大の分数体の分離性から、非零元を逆にして有限 étale にする一般定理も実装した。
最小多項式条件からの系と標数零の場合の系も証明した。
この定理の証明に新しい引用は追加していない。
原典の CLMST の引用の新配置、導来完備化と almost 同型のモデル、接続 B1〜B7 は後続段階である。
今回の抽出を、CLMST の原典結果そのものの証明や既存の未証明依存の解消とは数えない。

検証：全体ビルド3854ジョブ成功。`scripts/audit_axioms.lean` と
新しい `scripts/audit_clmst.lean` が成功し、共通層と finite étale の新規証明に
`sorryAx` 依存がないことを確認した。主定理に到達する未証明入力は従来どおり15件（文献13件と保留降下2件）で、増加していない。
新しい層から Paper への推移的 import がないこともソースで確認した。

### 続き：有限生成一致の解消と almost・導来完備性

C1 は `FiniteGeneration.lean` で証明し、旧宣言の直接の `sorry` を除いた。
Noether 局所基底、素数 p、座標の極大イデアル所属で足り、正則・完備・標準表示は不要。
有限表示の場合の λ**＝λ*＝λ∞ も証明した。必要な前提は HasSup・有限近似・perfection の利用先へ渡した。
C1 に関しては、当初検討した「標準冪級数表示を全入口へ伝播する」工程は不要になった。
C2 の加法性は依然引用であり、その一般性の監査は継続する。

almost zero と写像の核・余核による条件、冪等イデアル下での実際の almost 局所化圏、
冪ねじれの almost 同型から長さ一致への接続を証明した。
完備性は実導来圏の全次数の射の消滅で具体的に定義し、冪で消える複体・加群で確認した。
CLMST の長さの定義域にある加群の導来 p 完備性も接続した。
原典の perfectoid ideal の mod p^N での basic setup、導来完備化関手、
原典引用の新配置と全接続は未完成である。未証明依存は14件（文献12件と保留降下2件）に減った。

検証：全体ビルド3864ジョブ、新旧の公理監査が成功。
解説の引用一覧と README の件数も更新した。

### 続き：一般加法性と正規化長さの構成

`AdditivityFinite`、`AdditivityApproximation`、`AdditivityFinitelyGenerated` で、
Noether 局所基底・素数 p・座標の極大イデアル所属の下の一般加法性を証明した。
有限表示の有限段実現、有限生成分母での商の下限、有限表示冪ねじれ被覆、
有向な部分加群の上限を順に使い、C2 自体や旧 `towerLength` は使わない。
`RootTowerLength.normalizedLength` とその HasSup も、この証明から構成できた。

ここで「加法性の数学的証明」と「既存の本体から C2 引用を外すこと」を区別する。
新 API は正当な基底・座標の仮定を明示するが、旧 `towerLength` は任意の局所基底で作られている。
その型と利用先を切り替える移行は未実施であり、主定理に到達する旧 C2 引用はまだ残る。
新しい一般論・長さ構造には未証明依存がない。

perfectoid 化の普遍性から誘導射・恒等射・合成の法則と、主イデアルに対する kernel の単調性も整備した。
mod p^N の商環作用と raw almost 条件の一致、全加群の almost 圏から冪ねじれ部分圏への同型の移送を証明した。
この移送により、長さの比較の接続を部分圏内の同型だけへ制限しない。
`CLMST/Almost` と `AlmostLength` では actual な perfectoid ideal を使ってこの接続を具体化した。
mod p^N の像イデアルの冪等性と almost zero から長さ零の結果は、独立した入力として保持する。
選択された perfectoid 化を参照する結果の型には、既存の存在引用への依存が到達する。
新しい引用・公理は追加していない。

検証：全体ビルド3883ジョブ、公理監査と新モジュールの依存監査が成功。
証明した加法性、新しい正規化長さと HasSup は標準3公理のみで、C2 の引用に依存しない。
主定理に到達する未証明入力は引き続き14件。新しい層から Paper への推移的 import はない。

次の移行：旧 C2 と無条件の長さ構成の利用先を、新しい仮定つきの証明済み構成へ切り替える。
その後、原典の basic setup、almost 消滅・商の長さの引用を新しい層で述べ、具体的な適用へ接続する。

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
| L0 共通の土台 | 塔 `A_n`・`A^nc_∞`・`A_∞`、perfectoid の定義、Koszul、パラメータ系、重複度、三つの数値関数の定義 | 数値関数の定義と証明済み API。具体的な `NormalizedLength` の組立と perfectoid 化の選択の引用依存は別に管理 | Mathlib、論文非依存の一般層 |
| L1 CLMST 層（`SerrePositivity/CLMST/`、namespace `CLMST`） | CLMST の定義と、引用する主張を原典の形で述べたもの | 引用文は `sorry`。P/G のタグを付ける | L0 と Bhatt–Scholze の入力・構成。`Paper/` は import しない |
| L2 接続層（`SerrePositivity/Bridge/CLMSTToSerre.lean`） | L1 の主張から定理2.5の二つの長さの性質を導く | 直接の **`sorry` なし** | L0、L1。必要な長さ比較も先に共通層へ抽出し、最終的に `Paper/` を import しない |

`Paper/Section2/MixedLengthAlgebra.lean` はそのまま残し、依存先を `Inputs.CLMST` から L2 に変える。

この分離の利点は、**後で L1 の G の項目を証明しても、L2 と本論文の側は変わらない**ことである。
CLMST 由来の直接の `sorry` の所在と依存を記録する。
generic étaleness 等の古典的引用を採用する場合は別枠で記録し、CLMST の外に未証明依存がないとは言わない。
`#print axioms` は `sorryAx` の存在を示すが、引用名の内訳はソース・依存宣言の台帳でも確認する。

## 3. L1：CLMST の層

### 3.1 設定（Notation 4.0.1）

原典の Notation 4.0.1 を、具体的な環・写像・座標・元と明示的な仮定で表す。
最初の実装は section の引数で述べ、論文専用の結論を fields に詰めた `CLMST.Setup` は作らない。
将来データをまとめる場合も、局所環の表示等の数学的データに限り、
almost 消滅・長さ公式・未証明定理を構造の fields に入れない。

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
| Def 2.2.1（λ**、λ*、λ_∞） | 共通層の定義を `CLMST.normalizedLength` として参照 | 原典の A 上の長さと実装の A_n 上の長さの比較には、既存の `length_eq_of_common_residueField` と `residue_surjective_towerStage` を適用する。有限段公式・降下も既存。下限による λ** の定義と原典の選択による定義の対応を明記する |
| §4 での `A_∞` 加群の λ_∞ | `CLMST.normalizedLengthA∞`：`A_∞` 加群を `A^nc_∞` に制限して測る | 原典は §4 で `A_∞ - Mod_{m_A}` 上の λ_∞ を断りなく使う。制限で定めることを「原典との差」に書く（Lech §3.3 が同じ説明：`Λ/p^N ≅ A_∞/p^N`） |
| §4 の `(g)_perfd` | `CLMST.perfdIdeal g := ker(A_∞ → (A_∞/g)_perfd)` | 現在の `perfectoidIdeal`（`CommutativeAlgebra/Perfectoidization.lean`）を移すか別名にする |
| almost zero、almost flat、almost faithful | ideal による零化、Tor・テンソル積で定義 | 冪ねじれ加群での almost 同型と、導来 p 完備対象での almost 理論を区別する。単なる環の同型を要求しない |
| `R^{A_∞}_perfd` | 共通の選択を用い、実装は `(A_∞ ⊗_A R)_perfd` | 現在の `MixedPerfectoid` と順序を揃える。原典の `R ⊗_A A_∞` とはテンソル積の交換同型で対応し、作用の両立を示す |

Serre に要らない `I_∞` と `s_perfd` は今回定義しない。
`e_perfd`（Def 4.0.8）と Cor 4.0.18 は Lech との共有用の追加段階とし、
Serre の接続の最初の完了条件には含めない。

### 3.3 引用する主張（すべて `sorry`）

P：当面の深い外部入力として引用する。将来の証明を禁止する意味ではない。
G：後で L1 の中で、P の項目と一般論から証明する候補。

| 番号 | 原典の形（要旨） | タグ | 後で証明するときの材料 |
| --- | --- | --- | --- |
| Prop 2.2.3 | λ_∞ は well-defined。有限生成なら λ*、有限表示なら λ** と一致する | 証明済み | `RootTowerLength/FiniteGeneration` と既存の有限表示降下・有限段公式 |
| Prop 2.2.6 | (a) 短完全列で加法的。(b) 推移写像が単射、または全射で各値が有限のとき、帰納極限で連続 | G | Faltings Appendix 2、Gabber–Ramero Thm 14.5.75 |
| Ex 2.4.2(1) | `A_∞`（`A^nc_∞` の p 進完備化）は perfectoid | P | |
| Prop 2.4.7 | perfectoid R、有限生成 ideal J、有限・有限表示 R 代数 S、V(J) 外で有限 étale、S の p^∞ 捩れが有界。各 g∈J に対し錐への g^N 倍が D(R) で零 | P | 導来圏での零射とホモロジー零化を区別。S_perfd の存在と同定を先に構成 |
| Thm 4.0.3 | (a) 全ての `i > 0` と A 加群 `M` で `(g)_perfd · Tor_i^A(RPerfd, M) = 0`。(b) almost faithful | P | |
| Cor 4.0.4 | `i < d` で `(g)_perfd · H^i_m(RPerfd) = 0`。したがって `A_n ⊗_A R` の任意のパラメータ系 y で、`i > 0` について `(g)_perfd · H_i(y; RPerfd) = 0` | G | Thm 4.0.3、局所コホモロジーの Koszul による表示、Koszul と RΓ_m のスペクトル系列 |
| Prop 4.0.10 | `M, N ∈ A_∞ - Mod_{m_A}` で `M^a ≃ N^a`（`(g)_perfd` に関して）なら `λ_∞(M) = λ_∞(N)` | G | 加法性、巡回加群への帰着、g=p の場合の評価、一般 g の mod p Frobenius 比較と A/(p,g) の低次元長さ評価 |
| Prop 4.0.14 | `A_n ⊗_A R` のパラメータ系 y で `λ_∞(RPerfd/(y)) = p^{-nd} e(y, A_n ⊗_A R)`。特に `λ_∞(RPerfd/m_A RPerfd) = rank_A R` | G | Prop 2.4.7、Prop 2.2.6、Cor 4.0.4、Prop 4.0.10 |
| Def 4.0.8、Cor 4.0.18 | `e_perfd(J; R) := λ_∞(RPerfd/J RPerfd)`。m 準素な I で `e_perfd(I) ≤ e(I)`、パラメータ系で生成されれば等号 | G | Prop 4.0.14、極小 reduction（剰余体が有限のときは剰余体の拡大、Prop 4.0.17） |

Bhatt–Scholze の perfectoid 化の存在（Thm 10.11、Prop 8.5。現在の `Inputs/Perfectoidization.lean`）も、
同じ規律で `BhattScholze/` に置く（タグ P）。現在の有限・有限表示代数版は複数結果と完備化を合わせた系であり、
それを原典の定理そのものと呼ばない。古典的／導来的完備化の比較と普遍対象の一意性を接続に含める。
原典どおりの一般範囲で述べるのに必要な対象のモデルは、M0 で先に固定する。

Def 4.0.8 と Cor 4.0.18 は本論文では使わず、Lech の論文の Theorem 3.1 (3)（混標数の `λ(C/HC) ≤ e(H, D)`）で使う。
CLMST の層は Lech の論文の形式化と共有する（[Lech の計画](lech.md)）。

**確認状況（2026-10-13）**：上の表の主張は原典の該当箇所で確認した。
Lean の主張の草案との一字一句の突き合わせは M0 で行う。

### 3.4 主張の書き方の規則

1. **仮定は原典のとおりに置き、本論文に合わせて特殊化しない。**
   一般の `n`、一般の加群 `M` も、本論文で `n = 0` しか使わなくてもそのまま書く。
2. **結論も原典の形で書く。** almost の主張は「`(g)_perfd` で消える」のまま書き、λ に言い換えない。
3. **原典との差は、Lean 上の慣習に限る。** それぞれ docstring に書く。
   - `A` を同型付きで扱う（§3.1 の (i)）。
   - 値域 ℝ ∪ {∞} を `ℝ≥0∞` にする。
   - 原典が暗黙に置く「derived p-complete」（Caution 2.4.4）を明示する。
     `IsAdicComplete` と名前だけを取り替えて同一視しない。
   - `Perfectoidization` は具体的に選んだものを使う。
4. 各文の docstring には、番号、日本語の要旨、P/G、証明の出典を書く。
5. 名前は `CLMST.prop_4_0_10` のような番号の名前とし、必要なら内容を表す別名を付ける。
6. 新しい恒久的な `axiom` は入れない。class と axiom インスタンスの方式は、
   別プロジェクトとの共有が必要になったときに再検討する。

## 4. L2：接続層

| 補題 | 内容 | 重さ |
| --- | --- | --- |
| B1 設定の変換 | 具体的な環と座標の引数を合わせ、非零 g と有限 étale 条件を供給する | g の存在は独立の一般可換環論。定義の変換だけではない |
| B2 環の同一視 | `CLMST.RPerfd` と `MixedPerfectoid` を作用と両立して比較する | 同じ選択を参照すれば `rfl`。別々の普遍対象を選んだ場合は代数同型と自然性を証明 |
| B3 長さの同一視 | CLMST の λ_∞（`A^nc_∞` 上）と `completedTowerLength`・`towerLengthOn` の比較 | 中くらい。既存の `towerLengthOn_eq_completedTowerLength` を使う |
| B4 almost から λ へ | Prop 4.0.10 を `N = 0` にして、現在の `clmst_length_eq_zero_of_perfectoidIdeal_annihilates` を出す（`M^a ≃ 0` は「`(g)_perfd` で消える」こと） | 軽い。almost 同型の定義との整合だけ |
| B5 任意のパラメータ系での Koszul の almost 消滅 | Cor 4.0.4 の後半を `n = 0`（`A_0 ⊗_A R = R`）にして、現在の `clmst_exists_perfectoidIdeal_annihilates_koszul` を出す | 軽い（注意 2） |
| B6 重複度 | Prop 4.0.14 を `n = 0` にし、CLMST の e とリポジトリの `HilbertSamuel.multiplicity` を同一視する | 軽いか中くらい |
| B7 冪ねじれ | `isPowTorsion_completedTower_koszul` | 証明済み |

B1〜B7 が揃えば、現在の `Inputs/CLMST.lean` の三つの定理は L2 の補題として直接の `sorry` なしで証明する。
移行中は旧ファイルに互換 wrapper を残せる。実際の定義と証明の正本は新しい層に一つだけ置く。
ファイル削除そのものを完了条件にはしない。

### 注意

1. **g の取り方（B1）。** CLMST は g に「`A[1/g] → R[1/g]` が有限エタール」を課す。
   現在の存在命題は `g ≠ 0` だけを主張している。標数 0 では分離性が自動なので、generic étaleness から g は取れる。
   これは CLMST ではなく古典的な可換環論の事実で、証明するか、
   別の引用ファイルに置くかを決める。原則は一般可換環論として証明する。
   Mathlib に有限 étale・分離拡大・局所化の API はあるが、必要な存在定理の接続は追加調査する。
   有限 étale 条件の意味を定義してから引用するのであり、未知の述語を仮定に追加するだけでは済ませない。
2. **B5 は軽い。** Cor 4.0.4 は局所コホモロジーの almost 消滅に加えて、
   `A_n ⊗_A R` の任意のパラメータ系の Koszul ホモロジーの almost 消滅まで主張している（原典で確認）。
   `n = 0` で R の任意のパラメータ系になるので、接続層に Čech と Koszul の比較は入らない。
   その比較は、Cor 4.0.4 自身を L1 の中で証明するとき（M4）に要る。
   以前この点を接続層の最大の危険としていたが、原典の確認でなくなった。
3. **B4 の一般性。** 現行の長さ零の引用は、任意の非零 g に対して述べている。
   原典の Notation 4.0.1 の形を保った Prop 4.0.10 からは、必要なら R=A として適用する。
   実際の D が g の外で étale であるという新しい仮定を、旧定理へ不用意に足さない。
4. **一般 n。** `A_n ⊗_A R` は原典で局所環として扱われる。
   Lean ではその局所性・次元・剰余体と、n=0 の代数同型を明示してからパラメータ系を扱う。

## 5. ファイル配置

```
CommutativeAlgebra/RootTower/…             ← 有限段・塔・有限表示降下・完備化の共通部分
LengthAlgebra/RootTowerLength/…            ← λ**・λ*・λ∞ と係数制限
CLMST/NormalizedLength.lean                Def 2.2.1、Prop 2.2.3、Prop 2.2.6
CLMST/Notation.lean                        Notation 4.0.1 の具体的引数・作用
CLMST/Almost.lean                          (g)_perfd、AlmostZero・AlmostFlat・AlmostFaithful
CLMST/Perfectoid.lean                      Ex 2.4.2、Prop 2.4.7
CLMST/Section4/AlmostCM.lean               Thm 4.0.3、Cor 4.0.4
CLMST/Section4/Length.lean                 Prop 4.0.10、Prop 4.0.14
BhattScholze/Perfectoidization.lean        perfectoid 化の存在
Bridge/CLMSTToSerre.lean                   B1–B7
Paper/Section2/MixedLengthAlgebra.lean     依存先を Bridge に変えるだけ
```

L1 は推移的にも `Paper/` を import しない。
現在の `CompletedTower.lean` は、完備化の定義だけでなく長さ比較・Koszul の冪ねじれも含むため、
そのまま移動せず役割ごとに分割する。具体的な抽出順は [実装境界](clmst-interfaces.md) を参照。
共通の塔は等標数・Serre・Lech でも使うため CLMST 専用にはしない。
`Paper` 側には互換別名を残して、既存のコードを壊さない。
数値関数と `NormalizedLength` の組立を分け、後者が加法性の引用を必要とすることを表面化する。
既存 C1/C2 の仮定は原典の標準基底より広いので、M0 でその一般性と利用先を監査する。
その広い型を、根拠のないまま CLMST の原典引用として移さない。

## 6. 依存関係

- L1 の中：Cor 4.0.4 ← Thm 4.0.3、局所コホモロジー比較、有限フィルトレーション、冪ねじれ上の almost ideal の性質。
  Prop 4.0.10 ← Prop 2.2.x と `(g)_perfd`、巡回加群の長さ評価。
  Prop 4.0.14 ← Prop 2.4.7、Prop 2.2.6、Cor 4.0.4、Prop 4.0.10、パラメータの変更と Koszul Euler 公式。
  Thm 4.0.3 を後で証明する場合には Prop 2.4.9 と導来完備化・平坦性の比較等も調査する。
- L2：B4 ← Prop 4.0.10。B5 ← Cor 4.0.4。B6 ← Prop 4.0.14。
  B1 は generic étaleness、B2 は同じ選択または普遍性の比較、B3 は係数制限の比較に依存する。
- 本論文：`mixedPerfectoid_length_properties` ← B1–B7 → 定理2.5。

## 7. マイルストーンと完了条件

| 段 | 作業 | 完了の条件 |
| --- | --- | --- |
| M0 型・引用境界 | 原典照合を型の設計へ進め、導来完備化・almost 同型・general n・引用台帳を確定 | 完成形の数学的主張と必要 API が明示され、弱い別命題を原典の定理と呼ばない |
| M1 共通層の抽出 | 塔・長さ・完備化・perfectoid の選択を依存順に分割移動 | 推移的な Paper import がない。主張と未証明依存の内容が変わらずビルドが通る |
| M2 原典の引用 | 具体的に定義した対象について原典の主張を名前付きで引用 | 各文に番号・P/G・原典との差。新旧の引用対応を台帳で説明 |
| M3 Serre 接続 | B1〜B7と旧 wrapper を証明し、利用先を新しい層へ移す | 旧三定理に直接の sorry がなく、未証明依存が原典引用と明示した基礎結果へ到達する |
| M4-G1 | 有限段の長さ比較、Prop 2.2.3、必要な加法性と連続性を証明 | 引用12・13を対象とする範囲が明示され、自己依存がない |
| M4-G2 | almost と長さの接続、Cor 4.0.4、Prop 4.0.14の候補を順に証明 | 原典の一般性で達成した範囲と残る深い引用を記録 |
| M5 Lech 追加 | Def 4.0.8・Cor 4.0.18 と Lech への接続 | 極小 reduction 等の入力を別途明示。Serre 接続の区切りを拡大しない |

各段で `lake build` と `#print axioms` を確かめる。`native_decide` は使わない。
途中で壊れた部分的な証明を残さない。

## 8. 決めること

1. **原典の入手。** 済み（`paper/refs/CLMST-2209.04046v4.pdf`。`.gitignore` で除外し、commit しない）。
2. **A の書き方。** 同型付きの環と座標を採用する。原典との対応を証明する。
3. **塔の定義の置き場所。** 共通の `CommutativeAlgebra/RootTower/` と `LengthAlgebra/RootTowerLength/` に抽出する案を採用。
   正確なファイル名は抽出時に既存依存に合わせる。
4. **generic étaleness。** 一般可換環論として証明することを第一候補とし、不足 API を先に調査する。
5. **導来完備化と almost 同型。** 数学的意味は固定。具体的モデルと必要比較定理の型は M0 の残る設計課題。

## 9. 次の具体的な作業

1. [実装境界](clmst-interfaces.md)の T0：命題2.4.7の導来圏の零射、命題4.0.10の almost 同型、
   Bhatt–Scholze の原典引用と現在の有限代数版の比較について、具体的な型を確定する。
2. T1：`CompletedTower` の環の定義と長さ・Koszul の API を分け、有限段から順に共通層へ抽出する。
3. T2：定義を実装した上で原典引用を置き、T3 の接続を完了する。
4. G の証明と Lech 追加は、それぞれ独立した後続段階として扱う。

## 10. 参照資料

- CLMST：arXiv:2209.04046v4。
- Gabber–Ramero, *Foundations for almost ring theory*（§14.5）。
- Faltings, *Almost étale extensions*, Astérisque 279 (2002), Appendix 2。
- Bhatt–Scholze, *Prisms and prismatic cohomology*（§8、§10）。
- Bhatt–Iyengar–Ma, arXiv:1803.03229（Lemma 4.1.2 の背景。今回は対象外）。
- 現在のコード：`Inputs/CLMST.lean`、`Paper/Section2/TowerLength.lean`、
  `Paper/Section2/MixedLengthAlgebra.lean`、`Inputs/PerfectoidTower.lean`、`Inputs/Perfectoidization.lean`。
