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
- 工程 (b) の準備：任意の評価族の商像が core に属する全単体から `relativeDiagram` を
  構成。実辺と全単体の成分ごとの W 判定、全頂点の保持、内ホーン充填を証明済み。
  評価を再添字する実射の恒等・合成・包含後の回収と core 評価との可換性も証明済み。
- 同じ包含の二つの Verdier 商に対する全部分複体の等号、core からの自然な包含、
  核に属する全評価で相対条件が自動的に成立することを証明済み。
  評価と再添字が可換な単体的図式に対して `relativeSimplicialDiagram` を構成した。
  この一般構成を下記の具体的 S• に接続済み。実現・fiber 比較は未完。
- 工程 (b) の商比較：関手 ∞ 圏の core の全単体を頂点評価で判定し、相対図式を
  後合成による core の逆像と同定。指定全部分図式圏への商の実射があるとき、
  その core への実比較を構成し、元の core 上の商射と周囲への包含を回収する。
  gapped 条件や局所化比較の存在を仮定・完成扱いするものではない。
- 核に入る評価を持つ図式が零対象を持つなら、相対部分複体は弱可縮と証明済み。
- K-S• の固定界面（L1 §6）を受領し、全 gapped 図式を保持した具体的 wS•C を構成。
  全 Ar 成分での W 判定・全ての面退化・元の core からの包含を接続済み。
  wS•C → core S•(C/D) と包含側 wS•(D,qi) → wS•(C,q) を自然変換として構成し、
  元の core の射を回収する可換四角形を証明済み。核側の全相対 S_n は弱可縮。
  可換四角形の実現後の homotopy pullback 性・商比較の同値性はまだ主張しない。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 5830 jobs・専用監査 16 モジュール 94 宣言・全体 23740 jobs が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。

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
- 工程 (c) の必要条件は K-5 の `NativeFiberSequence` の整数長完全列を入力にする。
  Sp の IsStable は使わない。K-3 の具体的 K 関手・π₀ 比較は未接続。

### 未コミット
- なし（今回の具体的相対 S• の5モジュール・集約・監査・本計画を同じ保存単位に含める）。

### 既知の問題
- 所有 import 閉包の破損なし。K-6 全体と連結版の cofinality 条件は未完。

### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  W 辺の列の図式と cofiber が核に属する相対 cofiber 図式の比較を構成し、
  W の保存を証明して K-1 の相対加法性・K-2 の単体積版 Quillen A に接続する。
  商比較の全写像空間を含む局所化・cofinality 条件も別に証明する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
