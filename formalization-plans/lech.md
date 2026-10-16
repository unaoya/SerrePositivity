# Lech の重複度予想の形式化計画

作成日：2026-10-13。状態：設計段階。新しい Lean 実装はこの文書の作成には含まない。

対象とする版：OpenAI, *Lech's multiplicity conjecture*（openai/math、2026-09-23、
コミット `adc7f124`、[`paper/lech.pdf`](../paper/lech.pdf)、41 ページ）。
論文の内容の解説は [解説](../exposition/ja/lech-ja.tex)（PDF は `exposition/ja/lech-ja.pdf`）にあり、
この文書は形式化の方針だけを扱う。番号は論文のもの。

## 1. 目的と前提

最終目標は、論文の定理 1.1（平坦な局所準同型 `R → S` について `e(R) ≤ e(S)`）を、
Serre の論文と同じリポジトリで形式化することである。

[CLMST の計画](clmst.md)と同じ二つの前提を置く。

1. **外部の結果は、原典の形で述べた名前付きの `sorry` 定理として引用する。**
   仮定と結論は原典のまま書き、論文で使う形への変換は証明する。
2. **論文自身の議論（§2〜§8）は証明する。**
   論文の定理を一時的に `sorry` で置くことはあるが、それは「引用」ではなく「保留」として区別し、
   後の段階で必ず証明する（§6）。

### 以前の方針からの変更

2026-10-10 の調査メモ（`research/lech-overview.md`、`research/lech-section2-algebraic.md`。この文書と解説に移して削除）
では、最初の段階を「Lech §3.2 に沿って `LengthAlgebraConstruction` の等標数の `sorry` を埋める」としていた。
その後、等標数の長さ代数は直接の `sorry` なしに実装され、残る依存は Roberts の Frobenius 消滅（外部引用 6）だけになった。
Lech §3.2 も同じ Roberts の結果（Ma, Thm. 2.4 の形）を使うが、(3.7) で必要なのはパラメータ Koszul 複体の場合だけで、
Serre の形式化と同じ初等的な証明（`CommutativeAlgebra/ParameterKoszulGrowth.lean`）で足りる（2026-10-17 追記）。
一般の有限自由複体の形 (5.1) を使うのは、主定理 1.1 に不要な系 5.4 だけである。

## 2. 現在の入口

Lech に固有の Lean 宣言はまだない。Serre の形式化のうち再利用できるものは、解説の付録 B.2 の表にまとめた。要点は次のとおり。

| 部分 | 状況 |
| --- | --- |
| 長さの仮定と (2.1)、補題 2.2、補題 3.2 | `PerfectComplex/NormalizedLength`、`SupProperty`、`KoszulFinite`・`KoszulAcyclic`、`lambdaHomology_projective_vanishing`、`Section2.lemma_2_4_*` がほぼそのまま使える |
| 定理 3.1 (1)(2) | 標数 `p` は `perfectClosure_length_properties_of_higher_tendsto`（Roberts の引用に依存）、混標数は `mixedPerfectoid_length_properties`（CLMST の引用に依存） |
| 補題 4.1 | `Section2.lemma_2_1`（剰余体拡大の引用に依存）。重複度の保存は系として示す |
| Hilbert–Samuel 重複度 | `HilbertSamuel.multiplicity`、多項式性、パラメータの冪の公式、Koszul Euler 標数の公式は証明済み |
| §2.3〜2.6、Hilbert–Kunz、Dutta、Nagata、Cohen 分解、極小 reduction、結合公式、§6、§7 | なし |

## 3. 最終的に述べる主張

- **定理 1.1**：`R`、`S` を `0` でない Noether 局所環、`R → S` を平坦な局所準同型とすると
  `HilbertSamuel.multiplicity R (maximalIdeal R) R ≤ HilbertSamuel.multiplicity S (maximalIdeal S) S`。
  次元・剰余体・標数の仮定は置かない。
- 途中の主な主張：定理 2.1（一様な評価）、定理 3.1（長さ代数）、命題 4.3（補助環と複体）、
  定理 5.2（標数 `p`）、系 5.4（Dutta 重複度）、定理 6.3（混標数）、定理 7.4（剰余標数 0）。

定理 2.1 は、具体的な環によらない抽象的な定理として述べる：
可換環 `C`、`I = (z_1, …, z_h)`、仮定 (2.1) と余極限の安定性を満たす `λ`（`NormalizedLength` と同じ形）、
有限自由複体 `F` について結論を述べる。Serre の形式化の長さ代数の一般論と同じ層に置く。

## 4. 層の構成

| 層 | 中身 | `sorry` |
| --- | --- | --- |
| 共通の土台（既存） | 長さ代数の一般論、Koszul、Hilbert–Samuel 重複度、塔と正規化長さ | なし |
| 外部引用（原典の形） | 下の §5 の一覧。CLMST は `CLMST/`、Roberts は `Inputs/RobertsFrobenius` を共有 | 引用文だけ |
| Lech の一般論（`SerrePositivity/Lech/Estimate/`） | 定理 2.1 とその補題。次数付き Čech 複体、Rees 代数、(W) | (W) の引用だけ（当面） |
| Lech の組み立て（`SerrePositivity/Lech/`） | §3 (3)、§4〜§8 | なし（保留の段階を除く） |

## 5. 外部引用の一覧（候補）

原典との照合は M0 で行う。共有と書いたものは、他の計画の引用文をそのまま使う。

| 引用 | 原典 | 使う場所 | 備考 |
| --- | --- | --- | --- |
| CLMST Def. 2.2.1、Prop. 2.2.3、2.2.6、Cor. 4.0.4、Prop. 4.0.10、Def. 4.0.8、Cor. 4.0.18、Prop. 4.0.14 | CLMST v4 | §3.3 | 共有（[CLMST の計画](clmst.md)）。Cor. 4.0.18 は Lech だけが使う |
| Bhatt–Scholze の perfectoid 化 | BS §8、Thm. 10.11 | §3.3 | 共有 |
| Roberts の Frobenius ホモロジー評価 | Roberts、Ma Thm. 2.4 | (3.7)、(5.1) | (3.7) はパラメータ Koszul 複体の場合で、初等的な証明（`ParameterKoszulGrowth`）で足りる。一般形 `Inputs.frobenius_homology_length_tendsto_zero` は系 5.4 の (5.1) だけで使う |
| Cohen–Gabber の正規化 | Kurano–Shimomoto Thm. 1.1 | §3.2 | 共有（外部引用 2） |
| 剰余体拡大 | EGA／Stacks | 補題 4.1 | 共有（外部引用 1、`Section2.lemma_2_1` 経由） |
| Monsky の定理 | Monsky 1983 | Hilbert–Kunz 重複度の定義 | 極限の存在。定義を下極限・上極限で置けば引用を減らせる（§8） |
| Nagata の局所化定理 | Ma Thm. 2.1 の形 | 補題 4.2 | |
| Cohen 分解 | Avramov–Foxby–Herzog、Ma Thm. 3.1 | 命題 4.3 | |
| Hilbert–Kunz の等式 | Ma Lemma 4.2、§2.3 | 補題 5.1 | 完全交叉で余長に等しいことを含む |
| Hilbert–Kunz の結合公式 | Huneke Thm. 3.14 | 定理 5.2 | |
| Dutta 重複度の極限の存在と底変換不変性 | IMW §4.17 | 系 5.4 | |
| Hochster–Huneke の Frobenius ホモロジー評価 | BHM Thm. 5.2 | 系 5.4 | 系 5.4 は主定理には不要なので後回しにできる |
| Heitmann の整拡大版 Briançon–Skoda | Heitmann 1997、Heitmann–Ma Prop. 2.8 | 定理 6.3 | |
| excellence（有限性）、完備局所環の catenary 性 | 標準（Stacks） | 補題 6.2、定理 6.3、Remark 4.4 | Mathlib の現状を M0 で確認 |
| Artin 近似 | Artin 1969 Thm. 1.10、Cor. 2.1 | 補題 7.3 | |
| Eisenbud–Schreyer の束（(W) の形） | Eisenbud–Schreyer Thm. 6.1、論文の補題 2.6 | §2.5、§2.6 | 論文自身が証明している結果なので、M8 で証明する候補 |

## 6. マイルストーンと完了条件

| 段 | 作業 | 完了の条件 |
| --- | --- | --- |
| M0 引用の確定 | §5 の引用文の原典を集め（手元の参照用は `paper/refs/`、commit しない）、Lean の主張の草案と突き合わせる | 主張表の確定 |
| M1 主張の骨格 | 定理 1.1、定理 2.1、定理 3.1 (3)、命題 4.3、定理 5.2、6.3、7.4 の主張を Lean で書く。証明は `sorry`（保留）にして依存関係を固める | ビルドが通る。保留と引用が docstring で区別されている |
| M2 Hilbert–Kunz | Hilbert–Kunz 重複度を定義し、定理 3.1 (3) を示す（標数 `p` は (3.3)〜(3.5)、混標数は CLMST Cor. 4.0.18 から） | 定理 3.1 が引用だけに依存 |
| M3 帰着 | 補題 4.1（重複度の保存）、補題 4.2、命題 4.3 | 命題 4.3 が引用だけに依存 |
| M4 標数 `p` | 補題 5.1（引用から）と定理 5.2 | 標数 `p` の Lech が、定理 2.1（保留）と引用だけに依存 |
| M5 一様な評価 | 付録 A の書き直しに沿って、次数付き Čech 複体、Rees 代数、補題 2.3〜2.5、§2.6 を示す | 定理 2.1 が (W) の引用だけに依存。ここで標数 `p` の Lech が引用だけに依存する |
| M6 混標数 | 補題 6.1、6.2、定理 6.3 | 混標数の Lech が引用だけに依存 |
| M7 剰余標数 0 | 補題 7.1、7.2（符号化）、7.3（Artin 近似から）、定理 7.4、§8 の組み立て | 定理 1.1 が引用だけに依存 |
| M8（任意） | (W) を論文の補題 2.6 に沿って証明する（解説 付録 A.5 の (b) または (c)）。系 5.4 | (W) の引用が消える |

各段で `lake build` と `#print axioms` を確かめる。`native_decide` は使わない。
途中で壊れた部分的な証明を残さない。新しい恒久的な `axiom` は入れない。

完了の報告では、[全体像](overview.md) §8 と同じく次を分ける：
(1) 原典の主張を正確に述べた、(2) 引用からの接続を証明した、(3) 引用した結果そのものを証明した、
(4) 補助定理まで含めて未証明依存を解消した。保留の `sorry` を別の名前に移しただけでは進捗と数えない。

### M5 の部品

解説の付録 A の書き直しに沿って作る（2026-10-10 の設計メモから移した）。

| 部品 | 内容 | 依存 | 規模の見込み |
| --- | --- | --- | --- |
| 次数付き Čech 複体 | 定義、長完全列、有限フィルトレーション、余極限 | 局所化 | 中 |
| 多項式環の Čech コホモロジー | `A[Z]` の計算（`t ≥ 0`）、底変換 | Koszul の基盤、正則列 | 中 |
| Rees 代数 | `C[It]`、チャート `C[I/z_i]`、`Iℛ ≅ ℛ(1)`、`gr_I C` との関係 | Mathlib の `RingTheory.ReesAlgebra`（要確認） | 小〜中 |
| 補題 2.3 | `(C/I)[Z]` と `gr_I C` の比較（`O(t)` だけ） | 上の三つ、`SupProperty` | 小 |
| 補題 2.4 | ひねりの写像の消滅、有限性 | Čech 複体、零ホモトピーの基盤 | 中 |
| 補題 2.5 | 二つの塔の比較、ひねりでの不変性 | Čech 複体、補題 2.2、`LengthAlgebra/SerreQuotient` | 大 |
| (W) | 直線束の複体による補題 2.6 の書き換え | 引用（M5 の間） | 引用なら小 |
| §2.6 | 根の選び方、層ごとの数え上げ、Riemann 和 | 上の全て、初等的な実解析の評価 | 中 |

## 7. 依存関係と着手順

- M2〜M4 と M5 は独立に進められる。M4 は M5 の結論（定理 2.1）を保留のまま使う。
- M6 は M2（混標数の (3)）、M3、M5 に依存する。
- M7 は M4（標数 `p` の場合）と M3 に依存する。
- CLMST の計画の M3（接続層）が終わっていれば、定理 3.1 (1)(2) の混標数は CLMST の層の引用文から得られる。
  それまでは既存の `mixedPerfectoid_length_properties` を使う。

重い順の見込みは、M5（§2 の Čech の議論）、M7（符号化）、M6 と M2・M3（重複度の一般論：結合公式、極小 reduction、
Hilbert–Kunz）の順。M7 の符号化は論文が細部を簡潔に書いているので、M0 の後に紙の上で詰める。

## 8. 決めること

1. **Hilbert–Kunz 重複度の定義。** Monsky の定理を引用して極限で定義するか、下極限・上極限で定義して引用を避けるか。
   論文が使う等式（(3.5)、補題 5.1、結合公式）がどちらの定義で述べやすいか。
2. **保留の `sorry` の名前と置き場所。** 引用（`Inputs/`、`CLMST/`）と混ざらないように、例えば `Lech/Pending.lean` に集めるか。
3. **(W) を引用で置く期間。** M5 で引用にし、M8 で証明する案。論文自身の補題なので、恒久的な引用にはしない。
4. **系 5.4 の扱い。** 主定理には不要なので、M8 に回すか、M4 と一緒にやるか。

## 9. 形式化の前に紙の上で確かめること

解説の付録 A.6 にまとめた（補題 2.5 前半の塔の比較の正確な主張、Čech 複体の項の「共通の冪で消される」条件、
(W) を使った §2.6 の数え上げ）。そのほか：

- 補題 7.2 の各条件が有限個の多項式等式になることの細部。
- Mathlib の Rees 代数（`RingTheory.ReesAlgebra`）と対称式（`MvPolynomial.esymm`、対称式の基本定理）の現状（(W) の代数化に使う）。
- 定理 6.3 の Heitmann の適用で、冗長な生成元を含む生成系への当て方と、整域拡大の選び方の細部。

## 10. 次の具体的な作業

1. M0：§5 の引用の原典を集めて照合する。
2. M1：主張の骨格の形式化担当への指示文（完全な形）を作る。
3. 紙の上の確認（§9）を、M5 と M7 の前に済ませる。

## 11. 参照資料

- 論文：[`paper/lech.pdf`](../paper/lech.pdf)、出典は [`paper/SOURCE.md`](../paper/SOURCE.md)。
- 解説：[`exposition/ja/lech-ja.tex`](../exposition/ja/lech-ja.tex)。
- 共有する計画：[CLMST](clmst.md)、[全体像](overview.md)。
