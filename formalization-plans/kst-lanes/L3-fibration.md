# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 完了。`IsVerdierSequence` の核条件から包含の本質像が安定閉包と一致すると証明。
  cofiber による W 所属と商の実辺の可逆性を同定し、実二単体の二対三性、実押し出し・
  引き戻しでの保存と反映、実 cofiber 列間のホモトピーに対する拡大安定性を証明済み。
- この工程は thick 性より弱い安定な本質像で成立する。商の冪等完備化や連結 K の
  fiber 性はまだ主張しない。拡大安定性の三角形の射は実ホモトピーから構成する。
- 工程 (b) の一般構成：`relativeDiagram` の全単体・W 辺判定・内ホーン充填・
  厳密な再添字・core 包含と商の選択独立性を証明済み。全評価が核に入ると条件は自動。
  `relativeSimplicialDiagram` を具体的 S• に接続済み。相対図式は商の関手圏の core の
  逆像であり、指定全部分図式圏への比較は元の core 上の商射と周囲への包含を回収する。
- 核に入る評価を持つ図式が零対象を持つなら、相対部分複体は弱可縮と証明済み。
- K-S• の固定界面（L1 §6）を受領し、全 gapped 図式を保持した具体的 wS•C を構成。
  全 Ar 成分での W 判定・全ての面退化・元の core からの包含を接続済み。
  wS•C → core S•(C/D) と包含側 wS•(D,qi) → wS•(C,q) を自然変換として構成し、
  元の core の射を回収する可換四角形を証明済み。核側の全相対 S_n は弱可縮。
  可換四角形の実現後の homotopy pullback 性・商比較の同値性はまだ主張しない。
- 商の核を K-1 の `ClosedStablePredicate` として束ね、E(C,C,ker q) を構成した。
  元の全 cofiber 図式で、この頂点条件と底辺の W 所属を同定済み。
  W 辺を対象とする全部分図式圏への元の cofiber 射影は trivial Kan fibration。
  全境界持ち上げから W 辺図式の安定性と完全な ∞ 圏同値を導き、元の射影を回収する。
  この同値の coherent な逆を通す正有限反復実現の加法性と両射影の式を証明済み。
  W 辺の列の単体的構造への自然性・実現後の fiber 比較は未完。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 6155 jobs・専用監査 22 モジュール 145 宣言が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
  所有 import 閉包 2523 モジュールは EInfinity を含まない。全体は再試行 23756 jobs で成功。

### 残り（依存順）
1. 構成した wS•C と加法性からの連結版 fibration 定理
   （Waldhausen 1985 1.6.4、BGT §7、暫定 40–80 時間）。
2. 必要な cofinality 条件の明示。K-S• の K-1（加法性）・K-2（homotopy fiber 比較）の
   宣言だけを入力にする（BGT §7–8、暫定 16–32 時間）。
3. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値）。K-5 の形と π 同値検出へ
   接続する（BGT §7–8、暫定 16–32 時間）。
4. 冪等完備化と非連結化への入力の整理（BGT §9、暫定 8–16 時間。K-7 本体は別工程）。

### 主要宣言（共通接頭辞 `SerrePositivity.KST.Fibration`）
- weakEquivalences、stableClosure_essentialImage、mem_weakEquivalences_iff、
  mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、
  weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- relativeDiagram、relativeDiagram_mem_edge_iff、relativeDiagram_mem_iff、
  relativeDiagram_quasicategory、relativeDiagramEvaluation、relativeDiagramMap、
  relativeDiagramMap_id、relativeDiagramMap_comp、relativeDiagramMap_evaluation、
  relativeDiagramCoreInclusion、relativeDiagramCoreInclusion_naturality、
  relativeDiagram_eq_of_verdier、relativeDiagram_eq_top_of_kernel、
  relativeSimplicialDiagram、relativeSimplicialDiagramInclusion、
  relativeSimplicialDiagramCoreInclusion。
- functorCore_mem_iff、relativeDiagram_eq_functorCore_preimage、
  relativeDiagramFunctorCoreMap、relativeDiagram_eq_fullFunctorCore_preimage、
  relativeDiagramFullFunctorCoreMap、relativeDiagramFullFunctorCoreMap_core、
  relativeDiagramFullFunctorCoreMap_ambient、relativeDiagram_kernel_isWeaklyContractible、
  fiberProjection_surjective_iff_boundary_trivial、connectiveFiber_projection_piZero_surjective。
- relativeSConstruction、relativeSConstruction_mem_edge_iff、relativeSimplicialSConstruction、
  relativeSimplicialSConstructionCoreInclusion、relativeSQuotientMap、relativeSQuotientMap_core、
  relativeSimplicialQuotientMap、relativeSKernel_eq_top、relativeSKernel_isWeaklyContractible、
  relativeSFunctorMap、relativeSimplicialFunctorMap、relativeSFunctorMap_core、coreSExactMap、
  relativeSimplicialKernelSquare。
- sInputModel、kernelClosedPredicate、weakCofiberModel、weakCofiberAdditivity_localized_isIso、
  weakCofiber_predicate_iff_weakEquivalence、fullPredicateMap_trivialKanFibration、
  weakArrowCategory、weakCofiberProjection、weakCofiberProjection_ι、
  weakCofiberProjection_trivialKanFibration、weakArrowCofiberEquivalence、
  weakArrowCofiberEquivalence_hom、weakArrowMultiAdditivityMap、
  weakArrowMultiAdditivityMap_localized_isIso、weakArrowMultiAdditivityMap_fst、
  weakArrowMultiAdditivityMap_snd。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-1・K-2）、`KST/LocalizingInvariants/`（K-5）、`KST/Spectra/`、`InfinityCategories/Derived/`（β3 の Verdier 列）。
- 提供先：K-7（非連結 K）、K-基盤 2（K が局所化不変量であること）。
- 工程 (a) の直接入力は K-5 の `VerdierSequence` と Stable の実 cofiber・八面体・
  基底変更・前三角構造。SConstruction と Spectra の直接 import はない。
- 工程 (b) は F1 の `CoreKan` と、K-S• の `StructureMapCofibers` を直接 import する。
  固定界面は L1 §6 の `Gapped`・全 Ar 評価・`sMap_gapped_evaluate`・
  `sPostcomp_gapped_evaluate`。依頼先は `01a151d3-f75d-7ef2-9d1f-908c85eb1be1`。
  K-1 の ClosedStablePredicate 版相対加法性は任意 W 辺版の定理ではないので、
  W の保存・相対比較を別に証明する。K-3 以降の移動中の界面には依存しない。
  追加固定界面は L1 §6 の `cofiberDiagrams`・`cofiberProjection`・
  `cofiberProjection_trivialKanFibration`。W 条件への制限と全境界持ち上げは K-F が証明した。
- 工程 (c) の必要条件は K-5 の `NativeFiberSequence` の整数長完全列を入力にする。
  Sp の IsStable は使わない。K-3 の具体的 K 関手・π₀ 比較は未接続。

### 未コミット
- なし（今回の W 辺図式と相対 cofiber 比較の6モジュール・集約・監査・本計画を含める）。

### 既知の問題
- 所有 import 閉包の破損なし。全体の共有ルートの一時的な olean 欠落は再試行で解消。
  K-6 全体・W 辺の有限列への比較の自然性・連結版の cofinality 条件は未完。

### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  構成した一つの W 辺の比較・加法性を、W 辺の全有限列とその面・退化へ拡張する。
  同じ cofiber の選択の coherent な比較を保ち、K-2 の単体積版 Quillen A に接続する。
  商比較の全写像空間を含む局所化・cofinality 条件も別に証明する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
