# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 完了。`IsVerdierSequence` の核条件から包含の本質像が安定閉包と一致すると証明。
  cofiber による W 所属と商の実辺の可逆性を同定し、実二単体の二対三性、実押し出し・
  引き戻しでの保存と反映、実 cofiber 列間のホモトピーに対する拡大安定性を証明済み。
- 工程 (a) は thick 性より弱い安定な本質像で成立。冪等完備化・fiber 性は未主張。
- 工程 (b)：相対図式の全単体・W 判定・内ホーン充填・再添字・core 包含を構成し、
  商の関手圏の core の逆像と同定。具体的 wS•C・商への自然変換・核の可換四角形へ接続済み。
  核側の全相対 S_n は弱可縮。実現後の homotopy pullback 性・商比較の同値性は未証明。
- W 辺と E(C,C,ker q) の元の射影は trivial Kan fibration で、完全な ∞ 圏同値を構成済み。
  K-1 により W 辺の正の全有限反復の二評価の加法性を証明。全有限 W 列の図式圏も安定。
  全ての面・退化は完全で、StableModel 値の単体的対象と各段の反復実現を構成済み。
- 全合成辺に共通の cofiber 補完を構成し、元の実四角形・始点・核値 cofiber を回収。
  補完と cofiber は全再添字と厳密に可換。退化辺の核値 cofiber 族は全関手圏で零対象。
  関手圏内の八面体族から E(ker q,B,ker q) 値の完全な比較関手を構成し、元の三辺と比較。
  K-1/K-2 の固定界面で、三辺の cofiber 実現射の全正有限反復加法性と再添字整合性を証明済み。
- 初期頂点と全連続辺の cofiber から、空列を含む有限 W 列の実現と積との比較を構成済み。
  各射影は元の評価を回収し、任意の制限後の頂点・実合成辺との厳密な対応も証明。
  一辺では同じ二成分が既存の加法性写像を回収し、全正有限反復で局所化同型。
  二辺以上の比較の同値性・全列の加法性比較の自然性・実現後の fiber 比較は未完。
- 二辺では、二短辺の W 条件が元の全二単体条件を反映することを証明し、内ホーン制限を
  trivial Kan fibration・完全な安定圏同値にした。標的は共有端点上の二つの W 辺図式圏の
  厳密な引き戻し。元の両短辺を回収し、元の二辺の有限比較をこの同値と同じ積比較に因子分解済み。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 7158 jobs・専用監査 60 モジュール 429 宣言が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
  所有 import 閉包 3441 モジュールは EInfinity を含まない。全体 23922 jobs で成功。

### 残り（依存順）
1. 構成した wS•C と加法性からの連結版 fibration 定理
   （Waldhausen 1985 1.6.4、BGT §7、暫定 40–80 時間）。
2. 必要な cofinality 条件の明示。K-S• の K-1（加法性）・K-2（homotopy fiber 比較）の
   宣言だけを入力にする（BGT §7–8、暫定 16–32 時間）。
3. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値）。K-5 の形と π 同値検出へ
   接続する（BGT §7–8、暫定 16–32 時間）。
4. 冪等完備化と非連結化への入力の整理（BGT §9、暫定 8–16 時間。K-7 本体は別工程）。

### 主要宣言（共通接頭辞 `SerrePositivity.KST.Fibration`）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、
  weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- relativeDiagram、relativeSimplicialDiagram、relativeDiagramFullFunctorCoreMap。
- relativeDiagram_kernel_isWeaklyContractible、connectiveFiber_projection_piZero_surjective。
- relativeSConstruction、relativeSConstruction_mem_edge_iff、relativeSimplicialSConstruction、
  relativeSimplicialQuotientMap、relativeSKernel_isWeaklyContractible、relativeSimplicialKernelSquare。
- kernelClosedPredicate、weakCofiberProjection_trivialKanFibration、weakArrowCofiberEquivalence、
  weakArrowMultiAdditivityMap_localized_isIso。
- weakStringCategory、weakStringCategory_isStable、weakStringStableSimplicial、
  weakStringMultiRealization、weakStringEdgeExact、weakStringCofiberExact_reindex。
- weakStringKernelCofiber、weakStringCofiberVertex_bottom、weakStringCofiberVertex_kernel。
- cofiberFamily_isCofiber、weakStringCofiberFamily_reindex、weakStringCofiberFamily_quotient、
  weakStringOctahedronFamily、weakStringOctahedronFamily_middle_kernel。
- cofiberFamilyUntranspose、weakStringOctahedronRelativeExact、weakStringOctahedronSourceExact_eq、
  weakStringOctahedronTargetExact_comparison。
- kernelRelativeMiddle、kernelMultiAddition_of_relativeFunctor、
  weakStringOctahedronMiddleExact_comparison、weakStringTriangleMultiAddition、
  weakStringTriangleMultiAddition_reindex、weakStringCofiberMultiPair_reindex、
  weakStringKernelCofiber_degenerate_isZeroVertex。
- weakStringVertexExact、weakStringVertexExact_reindex、weakStringCofiberSubobject_eq、
  weakStringFiniteComparison、weakStringFiniteComparison_cofiber、
  weakStringFiniteComparison_reindex_cofiber、weakStringFiniteComparison_one_localized_isIso。
- composableWeakArrow_isPullback、weakStringTwoHornEquivalence、
  weakStringTwoHorn_multiRealization_localized_isIso、weakStringFiniteComparison_two_factor、
  weakStringFiniteComparison_two_localized_isIso_iff。

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
  追加固定界面（L1 §6）：MultiRealizationFunctorIso の
  multiRealization_map_positive_localized_eq_of_functorIso（正の全反復、ModelCategory 引数なし）。
- 工程 (c) の必要条件は K-5 の `NativeFiberSequence` の整数長完全列を入力にする。
  Sp の IsStable は使わない。K-3 の具体的 K 関手・π₀ 比較は未接続。

### 未コミット
- なし（今回の二辺の内ホーン・厳密引き戻し・切断因子分解の7モジュール・集約・監査・本計画を含める）。

### 既知の問題
- 所有 import 閉包の破損なし。前回の共有ルートの intervalMinimum 同名衝突は他レーンで解消済み。
  K-6 全体・有限 W 列全体の加法性比較の自然性・連結版の cofinality 条件は未完。

### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  内ホーンの引き戻し模型上の積比較に、K-1 の単体左 fiber の quotient 同値を基底変換し K-2 を適用する。
  まず左 fiber の厳密基底変換と、対象の object S 図式がこの具体的引き戻しを保つことを証明する。
  二辺の積比較から全有限列へ進み、共通補完の再添字可換性を保持する。
  商比較の全写像空間を含む局所化・cofinality 条件も別に証明する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
