# §4：t 構造の一般論の実装記録

2026-10-10。共有の計画ファイルと並行作業の編集を避けるため、今回の到達点を独立に記録する。
全体の必須範囲は [section-4-plan.md](section-4-plan.md) に従う。
**最新の入力境界は末尾の「定理4.7：降下を引用する方針での完成」を優先する。**
ユーザーの指示により、補題4.6と定理3.1の K₀ 帰結を一つの未証明入力へ切り出し、
その入力に相対的な定理4.7まで完成した。以下の途中経過は履歴として残す。

## 完了した部分

- `CategoryTheory/TStructureHeart.lean`：任意の t 構造の heart の有限積、アーベル性、冪等完備性。
  heart の表示に既存の `t.Heart H` を用いる。有限積やアーベル性を追加仮定にはしていない。
- `CategoryTheory/TStructureRetracts.lean`：次数の上下界の retract への保存、単一次数での冪等分裂。
- `CategoryTheory/TriangleIdempotent.lean`：完全三角形の冪等自己射について、両端の分裂を中央へ延長する。
  この補題には前三角圏の公理だけで十分で、八面体公理を追加していない。
- `CategoryTheory/BoundedTStructureIdempotent.lean`：有限な次数幅に関する帰納法による冪等分裂、
  `isIdempotentComplete_of_bounded_tStructure`、有界対象の充満部分圏の冪等完備性、
  Karoubi 包絡との同値。分裂後の対象も元の次数範囲に入る。

## 冪等完備性の証明経路

Karoubi 包絡に三角構造を延長する一般定理を先に作る経路は、この結果には不要だった。
元の圏の切り詰め三角形を直接使うことで、S1 の冪等完備性を独立に証明できる。
§4 の採用方針や目標を変更するものではなく、その前提の証明順を短縮した。

1. 完全三角形の両端で零となる自己射の中央成分は平方零。
   三角形に対する Hom の完全性から因子化して示す。
2. 三角形の冪等自己射の両端を分裂し、像の間の接続射を完全三角形に補完する。
   三角形の射の補完公理により、元の三角形との往復の射を取る。
3. 往復の射を冪等元と合成し、その像上に制限する。両端で恒等になる合成は、
   三角形の五項補題により同型になる。この逆射を使って retract に補正する。
4. 補正した射影と元の冪等元との差は、冪等かつ両端で零。
   手順1によって平方零でもあるので、差は零となる。
5. 対象の次数範囲を `[a,a+w+1]` とすると、切り詰め三角形の左端は `[a,a+w]`、
   右端は単一次数 `a+w+1` に入る。左端には帰納仮定、右端には heart の冪等分裂を適用する。
   切り詰めが関手なので、元の冪等元はこの三角形の冪等自己射を与える。

## 残る接続

- S1 のもう一つの主張である、Serre 条件を満たす部分圏による Verdier 商への有界 t 構造の降下。
  下記の構成により、残りは Serre 条件から分母の切り詰め条件を導く接続になった。
- S2 で A 側と T 側に共通して使う Karoubi 包絡の三角構造。
  今回の証明経路では先送りできたが、S2 全体から不要になったわけではない。
- 列の圏・ランク商の構成、支持部分圏の切り詰め安定性、有限 Postnikov 構成との接続。
  今回の一般定理だけでは、任意の `P_A^J` の対象の一様自由持ち上げはまだ得られない。

## 検証

`lake build SerrePositivity.CategoryTheory.BoundedTStructureIdempotent` 成功。
今回の二つの新規ファイルの全10宣言について `#print axioms` と主定理の型を監査済み。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` はない。

## 続き：局所化上の t 構造の構成

追加したファイルは次の三つ。

- `CategoryTheory/TExactTruncation.lean`：t 完全な三角関手 `F` について、`F.map f` が同型ならば
  `F.map ((t.truncLE n).map f)` も同型になる。切り詰め三角形の射の一意性を使う。
- `CategoryTheory/LocalizationTStructure.lean`：右分数表示をもつ三角的局所化 `L` に対して、
  `W.IsInvertedBy (t.truncLE 0 ⋙ L)` を仮定し、非正側・非負側の本質像から t 構造を構成する。
  局所化関手の t 完全性、有界性の降下、局所化後の冪等完備性まで証明した。
- `CategoryTheory/VerdierTStructure.lean`：標準的な Verdier 商 `P.trW.Localization` に適用する。
  `P.trW` が非正切り詰めで保たれるという明示的な仮定の下で、商の t 構造を構成し、
  有界な場合の Karoubi 包絡との同値と、元の圏の対象による実際の代表の存在を得る。

直交性の証明では、射の右分数表示 `X ← Z → Y` に対し、分母を
`τ≤0 Z → Z → X` に置き換える。`X ≤ 0` ならば、この新しい分母の像は同型になる。
一方 `Y ≥ 1` ならば新しい分子は元の圏で零であり、局所化した射も零になる。
各対象の切り詰め三角形は三角関手で移し、本質的全射性により局所化の全対象に移す。

一般の局所化に対して、次の必要十分条件も証明した。

```text
(∃ s : TStructure D, L.TExact t s)
  ↔ W.IsInvertedBy (t.truncLE 0 ⋙ L)
```

右辺は切り詰め後の分母が局所化で可逆になる条件である。
`VerdierTStructure.lean` の「切り詰めが `P.trW` 自体を保つ」という条件は、
この右辺を供給する十分条件として使っている。

**Serre 条件から右辺を導く証明はまだない。** 今回の構成にはその代わりの未証明定理を
入れておらず、仮定として明示している。従って S1 の Serre 条件による降下定理全体は未完了。
次は、切り詰めで安定な部分圏 `P` の heart が Serre 部分圏であることから、
錐が `P` に属する射の切り詰めについても、その錐が `P` に属することを示す。
境界次数で現れる核・余核が `P` に属することに Serre 条件を使う必要がある。

検証：`lake build SerrePositivity.CategoryTheory.VerdierTStructure` 成功、警告なし。
3ファイルの全18宣言の公理依存と、分母条件を含む公開定理の型を監査済み。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` はない。

## 続き：列の圏・支持つきランク商・一様分解（2026-10-10）

今回の依頼の目標は定理4.7まで。**現時点では定理4.7も M5a（命題4.5）も未完了**。
以下は目標に必要な基盤の実装であり、論文の主張を条件つきの定理に置き換えて完成とはしない。
追加課題の K₀ の明示計算には着手していない。

### 実装した内容

| 段階 | ファイル | 証明した内容 |
| --- | --- | --- |
| S2 | `Asymptotic/FreeSequence.lean` | ランク `O(s)` の標準自由列、任意の行列列を射とする加法圏、有限直和 |
| S2・S7 の準備 | `Asymptotic/FreeSequenceGenerator.lean` | `s n > 0` の下で、全項に共通の自然数倍によるランク上界と標準列の固定倍への retract |
| S2 | `CategoryTheory/BoundedHomotopy.lean`、`Asymptotic/SequenceComplex.lean` | 共通有界ホモトピー圏、各段の鎖写像・ホモトピーの組み戻し、各段のホモトピー圏の積への完全忠実性 |
| S2 | `Asymptotic/RankQuotient.lean` | 共通有界かつ各項のランク `o(s)` の複体による、冪等完備化前の Verdier 商、小さい複体の像の消滅 |
| S2 | `Asymptotic/FreeSequenceBaseChange.lean`、`RankQuotientBaseChange.lean` | 行列への係数変更、ランク商への降下、商関手との自然同型、シフト・三角構造との両立 |
| S2 | `CategoryTheory/TriangulatedK0.lean` | 実際の三角圏の対象を同型・完全三角形の関係で割る K₀、加法的評価の普遍性、三角関手による誘導写像 |
| S2・S3 | `Asymptotic/SequenceLinear.lean`、`CategoryTheory/ScalarSupport.lean` | 列・ホモトピー圏・商のスカラー作用、共通の正の冪による台、直和因子・シフト・三角形への安定性 |
| S3 | `CategoryTheory/ScalarSupportLocalization.lean`、`Asymptotic/SupportedRankQuotient.lean` | 支持つき小対象を経由する射の因子化、支持部分圏の商から全体の商への完全忠実性、商の支持対象の直和因子表示 |
| S4b の準備 | `Asymptotic/NormalizedLimit.lean`、`LengthFamilies.lean`、`EulerLimit.lean` | 正規化超極限の収束・加法性・非負性、短完全列の族に対する Serre 条件の数値部分、共通有限支持をもつ Euler 和と超極限の交換 |
| S4a の接続 | `Asymptotic/SequenceKoszulBounds.lean` | 自由列の実際の複体に対する Koszul ホモロジーの有限性、`O(s)`・`o(s)` 評価、超極限の消滅 |
| S5 の準備 | `Asymptotic/SequenceDerived.lean` | 共通有界自由列から各段の導来圏の積への完全忠実性 |
| S5 の heart 部分 | `Asymptotic/AssembleComplex.lean`、`SequenceResolution.lean`、`SequenceSupport.lean` | 各段の自由複体の組み戻し、有限長加群列の実際の自由列による分解、共通範囲 `[-d,0]` とランク公式、一様消去指数から列全体の台への接続 |

### 補題4.2に向けた到達点

一般の線形三角圏において、台をもつ対象への射を、スカラー作用の錐を反復して因子化した。
小部分圏を `B`、支持部分圏を `S` とすると、`B` の対象から `S` の対象への射は
`S ∩ B` の対象を経由する。Mathlib の `IsVerdierRightLocalizing` に接続して、
`S/(S ∩ B) → C/B` の完全忠実性を得た。

また、線形三角関手 `F` の像で台をもつ `F(X)` は、元の圏で台をもつ `Z` の像 `F(Z)` の
直和因子になる。射影の鎖写像への持ち上げは使っていない。ランク商への適用により、
`supportedRankQuotient_retract` は商で初めて台をもつ全対象を扱う。

ここで `C` は共通有界ホモトピー圏。論文の `D_S`・`P_S` との比較に必要な
Karoubi 包絡の三角構造と同値は未実装なので、**補題4.2全体の完成とは区別する**。
`SequenceKaroubi` は現時点では加法圏としての定義である。

### 一様持ち上げの到達点

`exists_sequence_resolution` は、長さ `O(s)` の有限長加群列 `M n` を、
`FreeSequence A s` 上の実際の複体 `F` に持ち上げる。各段の評価は `M n` の分解であり、
ランクは `length(M n) × rank(K^i)`、次数は剰余体の固定分解 `K` で決まる `[-d,0]`。
固定分解は明示的な入力で、正則性の引用をこの一般補題の内部に混ぜていない。

`sequence_resolution_supported` により、加群列を `z_j^N` が一様に消すなら、
複体列の台には共通指数 `N * (d + 1)` が使える。各段のホモトピーは任意に選べる。
ただし、有限 Postnikov 構成と商への t 構造の降下はまだ接続していないため、
任意の `X ∈ P_A^J` の一様自由持ち上げは未完了。

### 定理4.7までに残る主要な証明

1. S1：heart の Serre 条件から分母の切り詰め条件を導く。
2. S2・S3：Karoubi 包絡の三角構造と、現在のランク商・支持部分圏を論文の圏に同定する。
3. S4b：長さの加群列の圏・Serre 商と、支持つき Verdier 商上のホモロジー評価を構成する。
   数値の Serre 条件だけではこの構成は完了しない。命題4.3・公式(4.2)も残る。
4. S5・S6：有限 Postnikov 構成による全対象の持ち上げから命題4.5の両等式へ接続する。
5. S7：補題4.6の dg 商・生成元の自己準同型 dg 代数・perfect 圏の表示と、基底変更の両立。
   固定版 Mathlib の既存 API だけではこの表示を供給できず、独自の証明と構成が必要。
6. S7・S8：一般係数版の定理3.1の引用を正しい dg の対象に述べ、実際の評価と
   `conjSum_eq` を接続して定理4.7を得る。

この一覧の未完了部分を新たな `sorry`・公理や、結論と同等の仮定で置き換えていない。

### 検証用の入口

`Paper/Section4/Foundations.lean` に追加モジュールをまとめた。
`lake build SerrePositivity.Paper.Section4.Foundations` は全2909ジョブで成功、警告なし。
今回の20実装モジュールの全122個の名前付き定義・補題・定理を `#print axioms` で監査済み。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` はない。
加法圏、三角構造、完全忠実性など13項目のインスタンスも個別に監査済みで、
依存公理は同じ標準公理のみ。支持部分圏の商の包含関手の三角性も確認した。
ルート import、§2 のファイル、共有の計画ファイルは今回の編集対象にしていない。
ルート import と共有の計画ファイルの変更は、並行作業との接続時に行う。

## 続き：長さの Serre 商と Euler 評価（2026-10-10）

**定理4.7と命題4.5は引き続き未完了**。今回、上の残件3のうち、実際の長さの圏、
Serre 商、ホモロジー関手の降下、冪等完備化への加法関手の延長を実装した。

### 圏と評価の構成

- `ModuleSequence.lean`、`LengthBoundedSequence.lean`：一様なイデアル冪で消され、
  各段の長さが有限、長さの列が `O(s)` である加群列のアーベル圏。
  `ENNReal.toReal` の前に有限性を要求する。
- `LengthSerreQuotient.lean`、`LengthQuotientValue.lean`：正規化超極限の長さが零の
  Serre 部分圏、実際のアーベル商、完全な商関手、商上の非負・加法的な実数値の長さ。
  商の対象の長さが零であることと、対象が零であることの同値も証明した。
  Mathlib の `Abelian/SerreClass/Localization.lean` に商のアーベル性と完全性があり、
  これを利用した。一部の古い TODO に反して、この機能は固定版にも存在する。
- `SequenceHomologyBounds.lean`、`SequenceHomology.lean`、
  `SequenceHomologyLocalization.lean`：実際の支持つき自由列から上の長さの圏への
  ホモロジー関手、小さい複体の消滅、支持つき Verdier 商への降下とホモロジー性。
- `SupportedKaroubi.lean`：支持部分圏の商の Karoubi 包絡と、全体のランク商を
  Karoubi 完備化してから支持条件を課した部分圏との圏同値。
  ここでは**三角圏としての同値までは主張していない**。
- `CompletedHomology.lean`：ホモロジー評価の Karoubi 包絡への延長、
  形式的直和因子 `(X,p)` の値と `im H(p)` の同型、次数の有限支持。
- `RankEuler.lean`、`RankHomologyShift.lean`、`RankEulerAdditivity.lean`：
  有限な Euler 和、同型不変性、代表複体での各段の Euler 値の正規化超極限との一致、
  **冪等完備化前**の支持つきランク商での三角加法性と `K₀ → ℝ`。

一般論は `CategoryTheory/` の `KaroubiLinear`、`KaroubiFullyFaithful`、
`KaroubiScalarSupport`、`KaroubiImage`、`SerreSubcategory`、`SerreLength`、
`HomologicalLocalization`、`HomologicalEuler` に分離した。
加法的な長さの Serre 商への降下や、有界ホモロジー関手の Euler 和の三角加法性には、
今回の列の圏に固有の仮定はない。

以上の20モジュールを含む `lake build SerrePositivity.Paper.Section4.Foundations` は
全2945ジョブで成功、警告なし。新しい130個の名前付き宣言の公理依存を監査し、
`propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` はなかった。

### 依然として必要な接続

1. Serre heart の条件から、商への t 構造の降下に必要な分母の切り詰め条件を証明する。
2. Karoubi 包絡の三角構造、商と完備化の順序の比較、論文の圏との同定。
3. 冪等完備化後の三角加法性と `K₀` 評価、命題4.3全体と公式(4.2)への接続。
4. 有限 Postnikov 構成を組み合わせ、A 側の任意の対象を一様な自由列で表す。
   その後、有限版3.5bから命題4.5の通常・正規化両側の等式へ接続する。
5. 補題4.6の dg 表示と係数変更、一般係数版定理3.1の引用、定理4.7。

実装の中心に残る Koszul 有限性の入力は、次の追記の接続を利用する。
入力を構造体にまとめて未証明の結論を隠す方法は採っていない。

### 論文の長さの性質からの Koszul 有限性

`Paper/Section4/KoszulInputs.lean` に接続を追加した。
通常の長さでは Noether 性と Artin パラメータ商から全ての冪での有限性を証明した。
有限な基底変更にも適用できる。正規化長さでは (2.4) の正次数の消滅と
(2.6) の有限な第零商の値から、全ての正の冪・全整数次数の有限性を導く。
長さに用いるイデアルがパラメータの像の根基に入ることも証明した。
§2 の代数の存在証明は、この接続の入力を供給する別作業である。

### 続き：テンソル積と有限版3.5bからの比較

さらに次を実装した。

- `Asymptotic/FreeSequenceTensor.lean`：行列の係数変更と、各段の実際のテンソル積との
  自然同型。複体の微分と両立する同型も構成した。
- `Asymptotic/SequenceBaseChangeSupport.lean`：環準同型に沿ったスカラー作用の保存、
  共通の零ホモトピーによる台の保存、各段が有限版3.5の台つき完全複体になること。
- `Asymptotic/SupportedRankBaseChange.lean`：支持つきホモトピー圏の係数変更、
  小さいランクの商への降下、商関手との比較同型、シフト・三角構造との両立。
- `Asymptotic/EulerLimit.lean` に Euler 値の列の `O(s)` 評価を追加。
  `RankEulerComparison.lean` では、有限版の比較から超極限の比較を得て、
  **冪等完備化前の商の全対象と `K₀`** へ移す一般定理を証明した。
  商関手の本質的全射性により、この段階では代表複体に戻せる。
- `Paper/Section4/RepresentativeComparison.lean`：有限版3.5bを各段で適用して、
  通常・正規化の両側の超極限の階数倍公式を証明。
- `Paper/Section4/OrdinaryRankComparison.lean`：通常の長さの入力を有限長から供給した
  実際の `K₀` 評価と、有限版3.5bによる係数変更の階数倍公式。
- `Paper/Section4/NormalizedRankComparison.lean`：テンソル積の結合で有限版を
  `A → C` に読み替え、正規化評価の階数倍公式を `K₀` に接続。
  こちらは `A → C` の商関手についての等式であり、`A → T → C` の商関手の合成との
  自然同型まで証明したわけではない。

紙面の入力との境界も明示したままにしている。通常の比較には Koszul 分解、
剰余体の条件、有限版の Koszul Euler 値の階数公式を使う。
正規化の比較には有限版3.5の消滅・第零商の値・全ての冪の有限性を使う。
これらの入力の下で証明は閉じているが、定理4.7の設定を構成し終えたという意味ではない。

この先の主要な問題は、A 側の商に有界 t 構造を構成して、冪等完備化後の任意の対象にも
この代表による議論を適用できるようにすること。
T 側では Karoubi 包絡の三角構造と Euler 評価の三角加法性も必要。
補題4.6の dg 表示と定理3.1との接続も残るため、**命題4.5全体と定理4.7は未完了**。

検証：`lake build SerrePositivity.Paper.Section4.Foundations` は全3061ジョブで成功。
今回の追加ファイル自体の警告は解消した。依存先の既存入力ファイルの `sorry` 警告と
既存スタイル警告は残っているため、新規28モジュールの名前付き宣言と Euler 評価の追加補題、
計171宣言の `#print axioms` を別途監査した。依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` はない。
空白検査も成功。並行作業中の §2・可換環論・正規化長さの共有ファイルは編集していない。

## 続き：具体的な Serre 導来商と heart の持ち上げ（2026-10-10）

**定理4.7と命題4.5全体は未完了**。今回の t 構造は、長さで制限した加群列の
有界導来圏から作った商についてのもの。既存の支持つき自由列のランク商に
そのまま t 構造が入った、という主張ではない。

### Serre 商の完全性から分母の切り詰め条件を供給

- `CategoryTheory/ExactDerivedTStructure.lean`：アーベル圏の完全関手が誘導する
  導来関手の t 完全性を、片側有界な複体による表示から証明した。
  ホモロジーの比較同型、全ホモロジーによる零対象の判定も追加した。
- `CategoryTheory/TExactKernelQuotient.lean`：三角関手 `F` の核を定義し、
  核を錐にもつ射と `F` で可逆になる射との同値を証明した。
  t 完全性から分母の切り詰め保存が従うため、以前の `hτ` を追加仮定とせず、
  この核による商の t 構造を構成できる。有界性、冪等完備性、Karoubi 包絡の
  対象の元の圏による代表、標準商関手の t 完全性も接続した。
- `CategoryTheory/SerreDerivedQuotient.lean`：Serre 商関手の導来関手の核を、
  全ホモロジーが元の Serre 部分圏に属する条件と同定した。
  有界導来圏をこの核で割った商は有界 t 構造をもち、冪等完備になる。
  Karoubi 包絡の対象には実際に両側有界な複体による代表も選べる。
  **この Verdier 商と、アーベル Serre 商の導来圏との同値は主張していない。**

### 通常の o(s) と超極限の長さ零を区別した適用

- `Asymptotic/SmallLengthSerreQuotient.lean`：`atTop` における通常の長さの
  `o(s)` 条件が Serre 条件を満たすこと、実際のアーベル商と完全な商関手を構成。
  この商から超極限で長さ零の Serre 商への完全な比較関手と、商関手との自然同型も構成。
- `Asymptotic/SmallLengthDerivedQuotient.lean`：全ホモロジーの長さが通常の
  `o(s)` である対象による有界導来商、その有界 t 構造、冪等完備性を証明。
  こちらが通常の `o(s)` を用いるランク商との比較に向けたモデルになる。
- `Asymptotic/LengthDerivedQuotient.lean`：全ホモロジーの正規化超極限が零である
  対象による別の導来商にも、同じ構成を適用した。
  超極限の零条件と通常の `o(s)` の同値は使っていない。

### Postnikov 生成と実際の heart の自由分解

- `CategoryTheory/BoundedTStructureGeneration.lean`：heart を含む三角部分圏は
  全 t 有界対象を含むことを、有限な次数幅に関する切り詰め三角形の帰納法で証明。
  充満な三角関手の本質像にも適用できる。ただし、この一般補題自体が
  §4 の比較関手の充満性を与えるわけではない。
- `Asymptotic/OrdinaryHeartResolution.lean`：通常の長さを台のイデアルに制限し、
  実際の長さで制限された加群列の各対象に、一様に支持された自由分解を与えた。
  剰余体の固定した分解が `[-d,0]` にあるという入力の下で、分解の次数範囲も
  `[-d,0]`、各項の階数は加群の長さと固定分解の項の階数の積になる。
  第零ホモロジーは元の加群列に同型で、他のホモロジーは零。
  通常の長さが `o(s)` の対象には、各項のランクが `o(s)` の分解を与える。

### 残る接続と方針の境界

一般の有界 t 構造と Serre heart からの降下定理はまだ証明していない。
今回は完全な Serre 商関手がある導来圏の場合について、分母条件を実際に証明した。
これを使って S1 を回避するなら、支持つき自由列のランク商との比較関手と
必要な完全忠実性・本質的全射性を別途構成する必要がある。
元の計画は heart の有界導来圏との同値を要求しないため、今回のモデルを作っただけで
その同値があると仮定したり、元の S1・S5 が完了したと数えたりしない。

heart での持ち上げと小さい対象の持ち上げは具体的に接続したが、任意の対象についての
一様自由代表は未完了。Karoubi 三角構造、論文の圏との比較、補題4.6の dg 表示、
定理3.1から定理4.7への接続も引き続き残る。

検証：追加8モジュールを含む `lake build SerrePositivity.Paper.Section4.Foundations` は
全3074ジョブで成功。追加モジュール自体には警告なし。
既存依存先の警告とは別に、今回の66個の名前付き宣言の公理依存を監査し、
`propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なしと確認した。
新規ファイルの空白検査と `git diff --check` も成功。
ルート import、§2・可換環論の並行作業ファイル、共有の計画ノートは編集していない。

## 2026-10-10 追記：一様自由代表、支持つきランク商の t 構造、完備化後の数値比較

この追記は直前の「任意の対象の一様自由代表は未完了」という状態を更新する。
**現在構成しているランク商のモデルでは S5 の一様自由代表を証明した。**
通常・正規化の Euler 階数倍公式も、支持つきランク商の Karoubi 包絡の全対象に拡張した。
ただし、**論文の圏との三角的な同定を含む命題4.5全体と、定理4.7は未完了**。

### heart の有界導来圏との同値を使わない一様持ち上げ

- `CategoryTheory/FamilyTriangulatedImage.lean`：三角関手の族について、
  成分ごとの射を同時に持ち上げられれば、同時の代表をもつ対象の族は
  成分ごとの完全三角形による拡大で閉じる。
- `Asymptotic/SupportedDerivedImage.lean`：既存の `pointwiseDerived` の完全忠実性を
  支持部分圏に制限した。射の同時持ち上げと成分ごとの同型の引き戻しを構成。
- `CategoryTheory/DerivedPure.lean` と `Asymptotic/SupportedPureDerivedImage.lean`：
  単一次数の導来対象をそのホモロジーの single と比較し、以前の heart の
  一様自由分解を使って任意の一つの次数の族を持ち上げる。
- `Asymptotic/FamilyHomologyTruncation.lean`、`FamilyPostnikov.lean`、
  `SupportedUniformLift.lean`：共通の有限な次数幅についての Postnikov 帰納法。
  全次数のホモロジー列が一様冪ねじれ・有限長・長さ `O(s)` を満たす導来対象の族に、
  共通有界な支持つき自由列の同時の代表を与える。
- `Asymptotic/SmallSupportedUniformLift.lean`：同じ帰納法を小さいランクの三角部分圏で
  行い、全ホモロジーが通常の `o(s)` の場合には小さいランクの代表を選ぶ。

この構成は、支持部分圏と heart の有界導来圏との同値を仮定しない。
導来圏の無限積に三角構造を新設することも不要。
各段の導来圏への三角関手の族と、元の圏での錐の構成を使う。

### 小さい対象の判定と、実際のランク商への t 構造の降下

- `Asymptotic/RankSmallHomologyCriterion.lean`：
  `rankSmallBounded X ↔ ∀ q, smallLengthFamily ... (H^q X)` を証明。
  順向きは一様な Koszul 長さ評価、逆向きは小さいランクの Postnikov 持ち上げと
  導来評価の完全忠実性による。超極限での長さ零とは同一視していない。
- `CategoryTheory/FamilyTStructure.lean` と `Asymptotic/SupportedSequenceTStructure.lean`：
  各段の導来ホモロジーで次数条件を定め、切り詰め三角形の左端を一様に持ち上げ、
  その射の錐を元の圏で取る。支持つき自由列の圏の有界 t 構造と
  各段の評価の t 完全性を証明した。
- `Asymptotic/SmallRankHomologicalKernel.lean`：通常の `o(s)` による Serre 商への
  ホモロジー関手を構成し、小さいランク部分圏をその第零ホモロジー関手の
  全シフトの核と同定した。
- `CategoryTheory/HomologicalKernelTStructure.lean`：ホモロジー関手が
  `C^{≤-1}` と `C^{≥1}` で消えるなら、全シフトの核の分母が `τ≤0` で保たれることを
  長完全列から証明した。境界の内側では切り詰め包含射がホモロジーで同型、
  外側ではホモロジーが零となる。
- `Asymptotic/SupportedRankTStructure.lean`：この核の同定と分母保存を既存の
  Verdier 商の構成に適用した。A 側の支持つきランク商の有界 t 構造、
  冪等完備性、Karoubi 包絡の全対象の商前の代表を得た。

これにより、この具体的な A 側については未証明の切り詰め分母条件を入力にしていない。
任意の Serre heart に対する一般的な降下定理は依然として別問題だが、
今回の具体的な商にはホモロジー関手の核を直接使う構成で十分である。

### 冪等完備化後の自由代表と Euler 比較

- `Asymptotic/SupportedCompletedRepresentative.lean`：支持つきランク商の冪等完備性と
  既存の支持部分圏の圏同値を組み合わせた。全体のランク商を冪等完備化してから
  台を課した任意の対象にも、商の前に一様に台をもつ実際の共通有界自由複体列が
  同型な代表として存在する。直和因子としての表示だけに留まらない。
- `Paper/Section4/UniformRepresentative.lean`：極大イデアルの生成列の
  `IsKoszulResolution` から必要な固定剰余体分解を供給し、
  `uniform_free_representative_of_koszul` に接続した。Noether 性・極大イデアルの
  生成条件から Koszul 有限性も供給する。A の完備性は使わない。
- `Asymptotic/CompletedEulerComparison.lean`：始域の支持つきランク商が冪等完備なら、
  既存の有限版 Euler 比較を Karoubi 包絡の任意の対象へ拡張できることを証明。
  値域側が既に冪等完備であるという仮定は置かない。
- `Paper/Section4/CompletedRankComparison.lean`：A 側の冪等完備性を実際に供給し、
  `ordinaryCompletedSupportedEuler_changeRing` と
  `normalizedCompletedSupportedEuler_changeRing` を証明した。
  前者は A → T、後者は A → C の係数変更について、任意の形式的直和因子で
  評価が `rank_A(T)` 倍になるという等式である。

### 残る接続

1. 論文の `P_S = (D_S/N_S)^♮` は、ホモトピー圏をまず冪等完備化してから商を取る。
   現在の `CompletedSequenceRankQuotient` は有界自由列のホモトピー圏の商を
   冪等完備化したもの。この順序の交換と、Karoubi 包絡の三角構造との両立は未証明。
2. T 側を含む完備化後のホモロジーの三角的完全性、Euler の三角加法性と
   `K₀` への降下、公式 (4.2) の接続。今回の全対象の数値比較だけで代用しない。
3. 正規化側の A → C と A → T → C の商関手の自然同型。
   各段のテンソル積の結合による Euler 値の比較は既存のものを使った。
4. 補題4.6の dg 表示・基底変更・中心作用・群作用の同定、一般係数版定理3.1との接続、
   定理4.7および §5 向けの評価 API。

検証：追加18モジュールを含む `lake build SerrePositivity.Paper.Section4.Foundations` は
全3093ジョブで成功。追加モジュール自体に警告なし。今回の75個の名前付き宣言の
公理依存は `propext`・`Classical.choice`・`Quot.sound` のみで、`sorryAx` なし。
監査出力は `/tmp/serre-section4-uniform-axioms-20261010.out`。
追加ファイルの行長・空白検査と `git diff --check` も成功。
途中で並行作業中の `CommutativeAlgebra/FiniteLength.lean` の再構築が一時的に失敗したが、
同ファイルには手を加えず、並行作業側の修正後に集約ビルドを通した。
ルート import、§2・可換環論のファイル、共有の三つの §4 計画・議論ノートは編集していない。

## 2026-10-10 追記：三角構造・論文の圏との比較・K₀・公式 (4.2)

今回指定された「1番」に対応する接続を実装した。直前の「残る接続」の1〜3を更新する。
補題4.6の dg 表示と定理4.7は今回の完了範囲に含めない。

### 三角構造と論文の圏の定義

- `CategoryTheory/KaroubiShift.lean`、`KaroubiPretriangulated.lean`、
  `KaroubiTriangulated.lean`：Karoubi 包絡のシフト、完全三角形、八面体公理を構成。
  完全三角形は元の完全三角形の retract として定義する。
  三角形上の冪等射の補完と、補対象を加えた八面体からの retract を明示した。
  参考は [Balmer–Schlichting, Theorem 1.12](https://www.math.ucla.edu/~balmer/Pubfile/IdempCompl.pdf)。
- `KaroubiHomological.lean`、`KaroubiTriangulatedFunctor.lean`、
  `KaroubiExtensionOne.lean`：ホモロジー関手と三角関手の延長。
  abelian 圏での exactness の retract 保存から、完備化後もホモロジー関手になる。
- `VerdierKaroubi.lean`、`VerdierKaroubiLinear.lean`：
  `Kar(Kar(C)/thick(P)) ≌ Kar(C/P)` を線形三角同値として構成した。
- `Asymptotic/PaperRankQuotient.lean`：論文と同じ順序の
  `D_S = Kar(K^b)`、`N_S`、`P_S = Kar(D_S/N_S)` と支持部分圏を定義。
  `paperRankEquivalence` と `paperSupportedRankEquivalence` が計算モデルとの比較を与える。
- `CategoryTheory/BoundedHomotopyGeneration.lean` と
  `Asymptotic/PaperRankGenerators.lean`：小さいランクの有界複体を使う実装の零部分圏が、
  **次数零の小さい自由列**から生成する論文の厚い部分圏と一致することも証明した。
  `paperRankNull_eq_smallFreeEnvelope` がその等式。
  一般の加法圏で下端への射の核を構成し、次数ごとに分裂する三角形による有限帰納法を使う。

### 完備化後のホモロジー・Euler 評価・公式 (4.2)

- `CompletedEulerAdditivity.lean`、`CompletedHomologyLength.lean`、
  `SupportedKaroubiTriangulated.lean`、`CompletedRankEvaluation.lean`：
  T 側を含む全支持対象について、ホモロジー関手、非負で有限台の実数値、
  Euler の三角加法性と K₀ への降下を構成した。
- `SequenceKoszul.lean`、`SequenceKoszulSupport.lean`：実際の自由複体列の Koszul 構成と、
  各段の既存 Koszul 複体との同型、一様支持を構成した。
- `CompletedKoszulFormula.lean`、`CompletedComplexEvaluation.lean`、
  `PaperRankEvaluation.lean`：零となるスカラーの錐から二項係数の畳み込みを導き、
  論文の圏で公式 (4.2) を係数ごとの等式として証明した。
  元の複体列の一様支持は仮定しない。商で指定された冪が零になる条件を用いる。
- `CompletedBaseChangeSupport.lean`、`BaseChangeComparison.lean`：
  商の完備化で初めて成り立つ支持条件も係数変更で保たれることを証明。
  支持部分圏の商を使った係数変更と、全体の商の係数変更の制限を自然同型で比較した。
- `PaperBaseChangeEvaluation.lean`：T → C の後のホモロジーを測る関手、非負の係数、
  有限台、Euler の K₀ 評価を構成。正規化評価版の (4.2) も証明した。
  `paperBaseChangeBetti_koszul_tensor_formula` の右辺の長さは、論文どおり
  元の Koszul 複体をさらに C にテンソルした複体のホモロジーを使う。
  係数環の平坦性は仮定していない。

### K₀ 上の階数倍比較と二段階の係数変更

- `BaseChangeComposition.lean`：行列、共通有界ホモトピー圏、支持つき Verdier 商、
  Karoubi 包絡の各段で二段階の係数変更と直接の係数変更の自然同型を構成。
- `CompletedK0Comparison.lean`、`PaperBaseChange.lean`：全対象の数値比較を K₀ 上の
  準同型の等式へ移した。`paperSupportedChangeRingCompIso` と
  `paperSupportedChangeRingK0_comp` により、論文の圏でも二段階の係数変更と両立する。
- `Paper/Section4/PaperK0Comparison.lean`：
  `ordinaryPaperEulerK0_changeRing` と `normalizedPaperEulerK0_changeRing` を証明。
  既存の有限版3.5bの比較を用い、A 側の冪等完備性は Koszul 完全性から供給する。
  任意の対象に同じ結論を仮定する形にはしていない。

### 残る範囲と検証

§2の長さ代数の構成を、ここで明示した Koszul 消滅・有限性・商の長さの入力に
適用する最終的な接続は、並行作業の結果に合わせて行う。
一般の Serre heart の有界導来圏との同値は今回の構成には不要であり、引き続き主張しない。
主経路の次の課題は、補題4.6の dg 表示・中心作用・群作用・一般係数版定理3.1との接続、
定理4.7、§5向けの評価 API である。

`lake build SerrePositivity.Paper.Section4.Foundations` は全3146ジョブで成功。
今回追加・修正したモジュールに警告なし。既存の依存先の警告は残っている。
ルート import、§2・可換環論の並行作業ファイル、共有の三つの §4 計画・議論ノートは編集していない。
既存の `TriangleIdempotent.lean` は途中の名前の衝突後に復元し、今回の補完補題は
`TriangleIdempotentCompletion.lean` に分離した。従来の有界 t 構造の経路も集約ビルドで確認済み。

公理監査：集約モジュールから読み込まれる `Asymptotic`、`CategoryTheory`、`Paper/Section4` の
125モジュール・857宣言を確認し、依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
`sorryAx` と追加公理への依存なし。監査出力は `/tmp/serre-section4-item1-axioms.out`。
今回の47ファイルは行長・空白検査に通り、`git diff --check` も成功した。

## 定理4.7：降下を引用する方針での完成（2026-10-10）

### 方針変更と完了範囲

ユーザーの明示的な指示により、dg 理論の実装を後回しにした。
旧計画の「補題4.6を未証明引用へ移さない」という方針は、この点で変更する。
ただし補題4.6の dg 表示を形式化・証明したとは主張しない。
補題4.6と一般係数版定理3.1から必要となる、実際の支持圏の K₀ の降下だけを
`Section4.supportedRankK0_descent` という一つの名前付き `sorry` 定理として置いた。

その帰結は、不変な類 `y` に対して `n > 0` と A 側の類 `x` が存在し、
`n • y = baseChange(x)` となること。有限群の作用、幾何ファイバーの推移性、
スペクトルの全射性、正則局所環と正の剰余標数、正の基準ランクを明示している。
任意の圏や任意の作用に対する降下を仮定せず、長さ関数にも依存しない。

この入力に相対的に、`Section4.theorem_4_7_K0` と `Section4.theorem_4_7` を証明した。
後者は論文の支持圏の任意の対象について、実際の通常・正規化 Euler 評価の共役和の一致。
仮定 (4.1) から有限性を証明し、Koszul 完全性と階数公式は既存の正則局所環の結果で供給する。
C の非自明性も商の長さと階数の正値性から導き、追加仮定として残していない。
λ の G 不変性、C 上の G 作用、T の A 平坦性は仮定しない。

§4は§2の具体的な環や長さ関数の構成を使わない。§2の成果を§4へ適用する接続は
§5側の仕事で、§4単体の未完了項目には数えない。以前の記録で両者を混同した記述は訂正する。

### 追加した構成

- `Asymptotic/BaseChangeIdentity.lean`：自由列から論文の支持圏までの恒等係数変更。
- `Asymptotic/PaperTwist.lean`：パラメータの像の同定、係数拡大によるひねり、K₀ の群作用。
  群作用の単位元・積・加法の法則を証明済み。係数制限を使う有限版のひねりとは逆元の規約が異なる。
- `Paper/Section4/LengthHypotheses.lean`：(4.1) から全冪での有限性、スペクトルの全射性からの
  単射性、および商の長さからの C の非自明性。零乗の場合は単位元に台をもつ Koszul 複体を使う。
- `Paper/Section4/NormComparison.lean`：二段階の係数変更による正規化評価、A 側の像での一致、
  降下を引数としたノルム比較。`conjSum_eq` を使い、このファイルに `sorry` はない。
- `Paper/Section4/SupportedDescent.lean`：今回唯一追加した未証明入力。
- `Paper/Section4/Theorem4_7.lean`：§4の抽象的な仮定から、対象版と K₀ 版の定理4.7。
  `Foundations.lean` から読み込む。共有のルート import は変更していない。

### 検証と未証明依存

`lake build SerrePositivity.Paper.Section4.Foundations` は全3175ジョブで成功。
今回の追加ファイルの警告は、意図した `supportedRankK0_descent` の `sorry` のみ。
既存の依存先の警告は残る。ビルドログは `/tmp/serre-section4-theorem-final-build.log`。

集約モジュールの `Asymptotic`・`CategoryTheory`・`Paper/Section4` に属する
131モジュール・897宣言を公理監査した。`sorryAx` に依存するのは、明示した降下定理、
正則局所環から C の非自明性を供給する補題、定理4.7の対象版と K₀ 版の4宣言のみ。
それ以外の893宣言は `propext`・`Classical.choice`・`Quot.sound` のみ。

さらに定理4.7の証明と型の依存を追跡し、直接 `sorry` を含む到達先が次の二つだけであることを確認した。

1. `Section4.supportedRankK0_descent`：補題4.6と定理3.1の K₀ 帰結（今回追加）。
2. `isWeaklyRegular_of_span_eq_maximalIdeal`：正則パラメータの正則性（既存の入力）。

監査ソースは `/tmp/serre-section4-theorem-axioms.lean`、結果は同名の `.out`。
§2の存在定理・Roberts–Gillet–Soulé・有限版の降下定理への未証明依存はない。
並行作業中の§2・§5・可換環論・正規化長さの共有ファイル、共有の§4計画ファイルは編集していない。
