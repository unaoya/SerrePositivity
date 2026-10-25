# K-B2：K-6 b の相対構成と加法性

## 引き継ぎ

- 現在地：指定の foundations §6・§8、経路 §13 決定15・16、進捗の K-B、
  L3 冒頭工程(b)、L1 §6 を確認した。全長・全正反復の有限積比較を、
  **局所化圏値**の単体的自然同型へ束ね、元の後合成の有限積写像を回収する。
  単回の相対実現 fiber と、全正反復の核可縮性を明示入力とする fiber 接続を用意。
  K-6 b の完成・厳密 dg K の非負次数 π 同型は未主張。
- 残り：下記の設計案を本チャットの停止報告でユーザー経由の中継事項として提示する。
  全正反復の核側収縮、元の S• 境界・BF 比較との同じ図式の照合、
  K-B d の実比較の π 同型への接続は未完。
- 主要宣言（namespace `SerrePositivity.KST.Fibration.Relative`）：
  `finiteComparisonIso`、`finiteCoordinateDiagram`、`finiteComparisonNatIso`、
  `finiteCoordinatePostcomp`、`finiteCoordinatePostcomp_app`、
  `additivityFiberIsoOfKernelContractible`、
  `additivityFiberIsoOfKernelContractible_projection`、`singleAdditivityFiberIso`。
- 依存と提供：K-B の既存 WeakStringFinite*・WeakStringConstantPullback・
  WeakStringKernelDiagonalContraction・ContractibleBaseFiberComparison、
  K-S• の MultiRealization・相対加法性、Sp の FiberModel・SplitFiber は読み取り専用。
  既存の公開型は変更していない。所有外の証明はコピーしない。
- 未コミット：なし（所有新葉3本・集約・専用監査・本計画の6ファイルを同時保存）。
- 既知の問題：所有集約・専用監査は成功、import 閉包の欠落なし。
  局所化圏値の自然同型は SSet 値の対角実現へ直接渡せない。
  条件付きの全正反復 fiber を無条件の成果と数えない。
- 次の一手：設計案の採否後、全正反復の核側収縮を実図式の上で証明する。

## 1. 所有と制約

所有は `KST/Fibration/Relative/` の新規葉・`Relative/All`、
`scripts/audit_kst_fibration_relative.lean`、本計画（300行以内）。
KST/Fibration の既存葉（DGRelative* を含む）、NonConnective、SConstruction、
LocalizingInvariants、InfinityCategories は読み取り専用。
厳密 dg 入力に限定し、一般 BF 高次面整流・一般 StableInfinity の K 関手化を再開しない。
新規 sorry・公理・引用による証明代用、主経路の ModelCategory SSet 仮定を禁止。
自分の集約と監査だけをビルドし、根の全体ビルド・.lake 削除はしない。
コミットは `set -o pipefail` の下で自分のファイルだけ `git commit --only`。
実施記録はコミット本文。他セッションの変更を stage しない。

## 2. 三段目と当初見積り（初回報告済み）

1. 有限 W 列比較の全添字自然性と比較先の単体的構造（2〜4時間）。
2. 初期頂点・連続 cofiber の有限積比較を全次元・全正反復へ接続（4〜8時間）。
3. 相対 cofiber 加法性・左 fiber 同値を同じ比較へ接続（3〜6時間）。
4. 元の包含・射影を保つ相対 S• 実現 fiber 列（6〜12時間）。
5. 厳密 dg 入力への特殊化と K-B d の公開界面（3〜6時間）。
6. 所有集約・監査・禁止仮定検査、計画更新と限定コミット（1〜3時間）。

計19〜39時間。原典の既存経路は Waldhausen fibration、K-S• の McCarthy 型加法性、
K-B の Segal realization。原典の番号は L1 §6・L3 の正本に従う。
項目1〜2は局所化圏値の範囲のみ。SSet 値の全単体的有限積比較としては未完。

## 3. 設計案（未採用、ユーザー経由の中継が必要）

### 根拠

`kernelMultiAddition` は加法性比較の `anodyneQ` 像の逆を使う。
`weakStringFiniteComparison_innerFace_addition` は局所化後の等号。
`finiteCoordinateDiagram` は全長の元の有限比較の同型による共役であり、
全ての単体作用素の関手則と後合成を持つが、値域は
`SSet.anodyneExtensions.Localization`。
その自然同型を `simplicialDiagonalFunctor` や
`segalRealization_homotopyPullback` の入力にすることはできない。
個々の局所化等号を高次整合性のある SSet 図式と数えない。

一方、K-B の既存 `weakStringMultiPostcomp_homotopyPullback` は
**元の SSet 値図式**の全単体作用素の自然性四角形を扱う。
`weakStringConstantPostSquare_homotopyPullback h r` は全正反復の実四角形であり、
既存の有限加法性と Segal 実現を経由している。
これらは有限積座標を厳密な単体的対象へ整流せずに使用できる。

### 提案

実現の主経路を、有限積比較先の SSet 値への整流から、既存の元の W 列の
全単体的 homotopy-cartesian 性へ切り替える。
有限積比較は局所化圏値の補助として保持し、これを要求(1)の強い意味の完成とは数えない。
要求(1)をこの範囲へ変更してよいか、コーディネータの設計判断を求める。
認められない場合は、全 cofiber 選択を保持する SSet 値の比較図式の別構成が必要。
既存の公開型の変更は提案しない。

### 残る正確な入力

任意の `h : IsVerdierSequence i q` について次を証明する必要がある：

```lean
∀ r : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
  (terminal.from (iteratedRelativeSpace (i ≫ q) r)))
```

単回 r=0 は `weakStringKernelDiagonal_toPoint_localized_isIso h` で充足。
全 r は未証明。この入力から `additivityFiberIsoOfKernelContractible` が
元の反復実現と同じ実 fiber の同型を構成し、`_projection` が元の包含を回収する。
この接続だけでは Sp の構造写像との整合性や d の非負次数 π 同型は得られない。
その後、元の境界比較・厳密 dg BF 比較へ全図式を接続する（追加9〜18時間の暫定見積り）。

## 4. 検証

対象：`lake build SerrePositivity.KST.Fibration.Relative.All`。
監査：`lake env lean scripts/audit_kst_fibration_relative.lean`。
専用監査は所有モジュール由来の全宣言について標準三公理だけを許可し、
宣言型の ModelCategory 定数を拒否する。所有外の集約・監査は変更しない。
最終結果と実施記録は保存コミット本文に置く。
集約6,970 jobs、監査24宣言・3モジュールは成功。標準三公理のみで
宣言型の ModelCategory 検査も成功。repository import 閉包3,262モジュールに欠落なし。
ログ：`/tmp/kst-relative-build.log`、`/tmp/kst-relative-audit.log`。
