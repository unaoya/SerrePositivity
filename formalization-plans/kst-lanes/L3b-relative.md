# K-B2：K-6 b の相対構成と加法性

## 引き継ぎ

- 現在地：08:59 採用の設計で、相対 S• 実現の実 fiber 列と K-B d への供給境界を接続。
  元の W 列の SSet 値 homotopy-cartesian 性を主経路とし、局所化圏値の有限積比較は補助。
  単回版の実 fiber 同型は追加収縮入力なし。元の包含を回収する。
  c の商実現比較・指定全四角形同型から、元の単回全 S• 四角形の引き戻し性を得る。
  同じ未完備 dg native 列の実供給 BF 比較の非負次数 π 同型へ直接接続する。
  c の二入力の存在、無条件 K-6 c・d、完備化後の固定 K の Sp 引き戻し性は未主張。
- 残り：採用済みの「d の仮定の形」で K-6 b の供給界面は完了。
  他レーン側に残る入力は §3 の c の二比較。無条件 K-6 全体の完成ではない。
- 主要宣言（namespace `SerrePositivity.KST.Fibration.Relative`）：
  `finiteComparisonNatIso`、`finiteCoordinatePostcomp_app`、`singleAdditivityFiberIso`、
  `singleAdditivityFiberIso_projection`、
  `relativeRealizationInfinitySquare_isPullback`、`SingleRelativeComparison`、
  `SingleRelativeComparison.ofPositiveStages`、`SingleRelativeComparison.isPullback`、
  `dgKappaRelativeFiberComparison_nonnegative`、
  `dgKappaRelativeFiberComparison_nonnegative_of_positiveStages`。
- 依存と提供：K-B 既存の WeakStringFinite*・WeakStringConstantPullback・
  RelativeSKernelRealizationPullback・QuotientSKernelPositiveStages、
  K-S• の相対加法性・MultiRealization・実有限 BF 比較、Sp の実 fiber API、
  K-B の NonConnective/DGKappaSuppliedBFOneStage を読み取り専用で消費。
  既存の公開型は変更していない。所有外の検出証明をコピー・再実装しない。
- 未コミット：なし（新葉2本・所有既存葉1本・集約・専用監査・本計画を同時保存）。
- 既知の問題：全正反復の核収縮は補助の条件付き界面の入力として残るが、主経路は
  単回 S• と既存の第一正段検出を使い、この入力を必要としない。
  局所化圏値の自然同型は SSet 値の対角実現へ直接渡さない。
- 次の一手：二段目完了で停止。K-B は §3 の二比較を公開界面へ代入する。

## 1. 所有と制約

所有は `KST/Fibration/Relative/` の新規葉・`Relative/All`、
`scripts/audit_kst_fibration_relative.lean`、本計画（300行以内）。
既存 Fibration、NonConnective、SConstruction、LocalizingInvariants、InfinityCategories は読み取り専用。
厳密 dg 入力に限定。一般 BF 高次面整流・一般 StableInfinity の K 関手化を再開しない。
新規 sorry・公理・引用による証明代用、主経路の ModelCategory SSet 仮定を禁止。
自分の集約と監査だけをビルド。根の全体ビルド・.lake 削除はしない。
`set -o pipefail` の下で自分のファイルだけ `git commit --only`。
実施記録はコミット本文。他セッションの変更を stage しない。

## 2. 三段目（08:59 採用の修正）

1. [x] 有限 W 列比較の全添字自然性（局所化圏値の補助、完了）。
2. [x] 初期頂点・連続 cofiber の全次元・全正反復比較（局所化圏値の補助、完了）。
3. [x] 既存の相対加法性・左 fiber 比較・全 W 列の実核四角形を使用する主経路へ接続。
4. [x] 元の包含・射影を保持する単回相対実現の実 fiber 同型と native な全四角形。
5. [x] c の二比較から、d の同じ未完備 dg native 実 fiber 比較の非負次数 π 同型を供給。
6. [x] 所有集約・監査・禁止仮定検査、計画更新と限定コミット。

当初見積り19〜39時間。単回 S• と既存第一正段検出への接続により、
主経路で全正反復核収縮を別途証明する必要を除去した。
項目1〜2は採用された局所化圏値の補助。SSet 値の全単体的比較には数えない。

## 3. 採用済み設計と公開供給境界

**2026-10-26 08:59、ユーザー経由で採用**：
実現は K-B 既存の元の W 列の SSet 値 homotopy-cartesian 性から進める。
`weakStringMultiPostcomp_homotopyPullback`・`weakStringConstantPostSquare_homotopyPullback`
は有限加法性と Segal 実現を経由する。
`kernelMultiAddition`・内部面公式の局所化後等号から高次整合性を推論しない。
完成条件は相対実現 fiber 列（または d の仮定の形）と d がそのまま消費する界面。

### 相対実現の本体

`singleAdditivityFiberIso` は元の単回反復実現から、元の W 列包含の指定基点上の
実 homotopy fiber への同型。一般の `_projection` に既存の単回核収縮を代入すると
元の包含の実現射を回収する。
`relativeRealizationInfinitySquare_isPullback` は元の相対 S• 核四角形を
同じ全二胞体のまま Ex∞ coherent 四角形にし、その ∞ 引き戻し性を供給する。

### c が供給する二入力

任意の `d : VerdierDiagram` に対し `SingleRelativeComparison d` の内容は次の二つ：

1. 元の `relativeSimplicialQuotientMap d.projection` の対角実現の局所化可逆性。
2. 指定した元の単回全 S• 四角形から同じ商核四角形への `FunctorIso`。

`ofPositiveStages` は既存 `relativeSQuotientMap d.projection (n+1)` の全正段比較と
この同じ全関手同型を受ける。零段は既証の無条件比較で充足し、新たな仮定にしない。
`isPullback` は元の相対核四角形をこの二比較で移し、指定された全 S• 四角形の
引き戻し性を与える。二辺だけの比較や全長 Hom の一部から同型の存在を推論しない。

### d が直接消費する結論

`dgKappaRelativeFiberComparison_nonnegative R D I c j hj` は、
同じ `dgKappaNativeVerdierDiagram R D I` に対する上の二入力から、
K-B の既存 `dgKappaSuppliedBFFiberComparison R D I` の同じ π 関手作用の全単射性を返す。
`_of_positiveStages` は c4 の指定全図式同型と c5 の正段商比較を直接引数に取る。
既存 `DGKappaSuppliedBFOneStage` の第一正段検出を読み取り専用で消費する。
同じ未完備実列・供給 BF 四角形・実 canonical fiber・元の実比較を保持し、
ν 像が strict Verdier である追加条件や一般 BF 整流を入れない。

この結論は採用済みの「d の仮定の形」である。c4・c5 の二入力の存在は c の未完部分。
b の界面の完成を、無条件 K-6 全体や非連結 K の完成とは数えない。

## 4. 検証

対象：`lake build SerrePositivity.KST.Fibration.Relative.All`。
監査：`lake env lean scripts/audit_kst_fibration_relative.lean`。
専用監査は所有モジュール由来の全宣言（私有名を含む）を標準三公理だけに制限し、
宣言型の ModelCategory 定数を拒否。所有外の集約・監査は変更しない。
最終結果と実施記録は保存コミット本文へ。
以前の保存：8c5d3d99b（局所化圏値の補助・単回 fiber と条件付き全正反復界面）。
今回のログ：`/tmp/kst-relative-native-build.log`、`/tmp/kst-relative-native-audit.log`。
集約12,624 jobs、監査50宣言・5モジュールは成功。標準三公理のみ、ModelCategory 型仮定なし。
repository import 閉包8,818モジュールに欠落・循環なし。
