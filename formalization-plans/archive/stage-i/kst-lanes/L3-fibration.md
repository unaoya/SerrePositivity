# K-B レーン：K-6 fibration 定理（L3）

## 引き継ぎ（2026-10-27、K-6 完了・第 I 段分担を閉鎖）

- 所有：KST/Fibration/（Relative/ を含む）、Fibration.lean、audit_kst_fibration、本計画（300 行以内）。既存 ClosedStable* と K-B3 所有の NonConnective/ は編集しない。
- 主定理：`Relative.k6Fibration R D I : Relative.K6FibrationConclusions R D I`。実入力 R・D・I のみを固定し、hc5・hIso・hBF・hcofinal は取らない。e の隣接射出力は同じ Z を取る。
- c5：Sp の `712868615`、`VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso` を元の native Verdier 列へ特殊化し、`k6FibrationOfC5` に一回代入済み。n=0 を含み、別の局所化供給型へ包み直していない。
- c4：S-1 (a) `5640d0942` の `nativeTriangle_ext` を四有限端点へ実代入済み。`verdierCanonicalKernelSquareIso` は元の d のみから全四角形の FunctorIso を供給する。
- b：元の核実現と元の商射の指定 fiber 同型・核包含の射影公式、指定全 S• 四角形の引き戻しを無条件化した。S-1 (c) `69c370610` の無条件閉部分圏 S1 も消費済み。
- d：元の固定 K(D) から、同じ供給済み BF 右辺の Sp fiber への実比較が非負次数 π 同型。右辺・fiber 対象は主定理の `.quotient_edge`・`.fiber_target` で厳密照合する。
- e：K-S• の無条件 Thomason 共終性 `7397052d8` を同じ実 Yoneda 完備化比較へ代入済み。正次数 π 同型・零次単射・一回 loop 後の非負次数同型、および元の固定 K の実隣接構造射を供給する。零次全射性は要求しない。
- 境界（ユーザー確定）：K(C)→K(C/D) は供給済み BF 実現の右辺。旧固定 kSpectrumMap 右辺への Sp 射レベル比較・fiber 輸送は K-6 の範囲外。必要時は K-B3 が K-7 f で提起し、K-S• が所有する。
- 他レーン向け未送付依頼・設計提案：なし。公開名と閉鎖報告は計画とは別にユーザーへ渡す。
- 検証：Fibration・Relative.All の両集約と専用公理監査、外部利用側の型検査。結果・コミット provenance はコミット本文に記録する。
- 未コミット：閉鎖時に K-B 所有の変更だけを `git commit --only` で保存する。他レーンの staged・未追跡ファイルは取り込まない。
- 次の一手：なし。K-6 と K-B の第 I 段分担は完了として閉鎖する。K-7 本体・全入力自然性・逐次余極限・非連結化後の局所化性と登録は K-B3 が担当する。

## 公開界面（K-B3 向け）

共通接頭辞：`SerrePositivity.KST.Fibration.Relative`。
一葉 import：`SerrePositivity.KST.Fibration.Relative.ConnectiveFibration`。
主 Fibration 集約には NonConnective 非依存の `Relative.SuppliedRealization` を接続し、d・e の依存葉は Relative.All に集約する。

| 出力 | 公開名 | 消費する式・範囲 |
| --- | --- | --- |
| 無条件主定理 | `k6Fibration` | `k6Fibration R D I`。d・e を同じ実データで束ねた `K6FibrationConclusions` |
| d の非負次数 π 同型 | `k6Fibration_nonnegative` | `k6Fibration_nonnegative R D I j hj`。元の `dgKappaCanonicalFixedSourceFiberComparison` の piMap |
| e の K-7 隣接射 | `k6SuspensionStructureMap_nonnegative` | `k6SuspensionStructureMap_nonnegative R D I Z j hj`。hc5・hcofinal なし |
| e の実射 | `dgKappaCanonicalSuspensionStructureMap` | 同じ固定 K(D) から固定懸垂値の loop への元の BF 構造射 |
| 既存 K-7 列との照合 | `dgKappaCanonicalSuspensionStructureMap_eq` | 任意の既存 hcofinal 証明を用いた元の構造射との厳密等号。隣接射を選び直さない |
| 完備化比較 | `dgKappaCanonicalCompletion_positive`・`_zero_injective`・`dgKappaCanonicalCompletionLoop_nonnegative` | 同じ元の実 Yoneda 比較。零次全射性は含めない |
| b の二比較 | `SingleRelativeComparison.supplied` | 元の商実現比較の可逆性と指定全四角形の FunctorIso |
| b の実 fiber | `suppliedQuotientRealizationFiberIso`・`_projection` | 元の商射・指定基点・核包含の射影公式 |
| 元の全 S• 四角形 | `suppliedSingleS_isPullback` | 元の全二胞体を保つ native 引き戻し |
| BF 境界の照合 | `k6Fibration_fiberTarget`・`k6Fibration_quotientEdge` | 主定理の `.fiber_target`・`.quotient_edge` でも取得可能 |
| 保持する条件付き入口 | `k6FibrationOfC5`・`dgKappaCanonicalFixedSourceFiberComparison_nonnegative`・`dgKappaCanonicalSuspensionStructureMap_nonnegative` | 既存名・型を変更しない。新規消費側は無条件版を使う |

BF 中央対象は `dgKappaNativeBFFiniteOmegaSpectrum R D I (dgKappaNativeBFFiniteNativeObject R D I 1)`、商対象は同じ式の添字 3。
商射は `(dgKappaNativeCoherentBFArrow R D I 1).hom`。
指定 Sp fiber は `dgKappaSuppliedBFCanonicalFiberSquare R D I`、その頂点は同じ実極限錐 `dgKappaSuppliedBFKLimitCone R D I` の頂点と一致する。

## c5 の正本と実代入

正本 import：`SerrePositivity.KST.LocalizingInvariants.VerdierFirstRowSimplexLocalization`。
公開名：`SerrePositivity.KST.LocalizingInvariants.VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso`。
`h : VerdierSequence.{u}` に対する供給型は依頼どおり：

```lean
∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
  (relativeFirstRowSimplexQuotient h.projection n))
```

無条件主定理の代入は `k6FibrationOfC5 R D I` に、元の `dgKappaNativeVerdierDiagram R D I` の `toVerdierSequence` に対する上記実証明を一回渡す。
一般局所化の普遍性や H⁰ の比較から core 比較を推論せず、元の実射に対する Sp 正本の証明を消費する。

## 完成条件と採用範囲

- [x] a：元の実核と cofiber-W、二対三・押し出し・引き戻し・拡大安定性。
- [x] c1〜c3：全 Hom 座標、core S• の対角・実現・商核零化円柱を元の実入力へ照合。
- [x] c4：Ind-S (9)・(9b) と S-1 (a) を消費し、全共有対角・四有限端点・元の全四角形を照合。
- [x] c5：Sp の全次数実供給を元の標準単体商比較と主定理へ代入。
- [x] b：相対加法性から同じ実包含・商射・基点を持つ実 fiber 比較へ統合。
- [x] d：供給 BF 実現右辺の fiber への連結比較の非負次数 π 同型。
- [x] e：同じ実商の冪等完備化比較と、BGT §9 の K-7 入力となる元の固定 K 隣接射へ接続。

固定連結 K の Sp 引き戻し性や、完備化の π₀ 全射性は完成条件に含めない。
供給済み二頂点 Sp 比較は実スペクトル射から得ており、整数群の抽象同型だけから Sp 同型を作らない。
Ind-S (9) の正規化全族可逆比較と (9b) の同じ三面内の実充填を使う。元 t 自身への厳密全対角回収・厳密切断は要求しない。

## R 候補（削除・改名なし）

以下は無条件公開入口の確定により外部入力として不要になった旧条件付き API、または新主定理の import 閉包外にある旧分岐の整理候補。
「候補」は死んだコードの認定ではない。第 I 段後の停止窓で R が全消費側と宣言依存を確認し、公開名・型・既存証明を保って判断する。

| 候補葉（KST/Fibration/ 以下） | 理由・保持条件 |
| --- | --- |
| `Relative/ConnectiveFibrationTheorem` | hc5 付き外部入口は `Relative/ConnectiveFibration` で放電済み。ただし無条件主定理の証明核なので保持必須 |
| `Relative/FirstRowSimplexComparison`・`CanonicalComparison`・`CanonicalRealization` | c4/c5 を外部に要求する入口の整理候補。実座標・射影公式と証明内部の利用は保持 |
| `Relative/CanonicalSingleStageDetection`・`CanonicalFixedSourceFiber`・`CanonicalSuspensionInput` | hc5 付き外部入口を無条件公開葉から置換可能。元の実射と証明核は保持 |
| `VerdierMovingCanonicalSquareComparison` | 四有限端点を明示引数に取る入口は native 外延性で放電済み。現在も証明依存にあるため削除対象ではない |
| `VerdierFullSMovingSquarePrism`・`ZeroMiddleFullSReconstruction` | 旧上側全族・再構成供給を引数に取る入口。現在の import 閉包内であり、依存分離の調査だけを候補とする |
| `ZeroMiddleNormalizedFamily`・`ZeroMiddleReconstructedDiagonal` | 旧厳密回収仕様の葉。新しい無条件主定理の import 閉包外。旧仕様の利用者を確認してから整理 |
| `DGRelativePositiveDetection`・`DGRelativeComparisonFiberPi` | ν 像の Verdier 認証や全正段 Sp 検出を使う旧強条件分岐。新主定理の import 閉包外。一般補題の他消費側は別途確認 |

旧葉はすべて現状の公開名・型で保持し、集約からもこの閉鎖作業では除去しない。

## 原典と所有境界

Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。運用は foundations.md §8 と k-theory-kst-route.md §13（決定15・16）。
BGT §9 の FκA=(Indω A)κ、ΣκA=FκA/A、swindle、実逐次余極限、全入力射・filtered 交換・非連結局所化登録は K-B3 の分担。
K-B は同じ元の実列・実比較・完備化・隣接射の入力を供給した時点で閉鎖する。
