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
- 工程 (b)：`relativeDiagram` の全単体・W 判定・内ホーン充填・厳密な再添字・core 包含、
  商の選択独立性を証明し、商の関手圏の core の逆像と同定。具体的 S• へ接続済み。
- K-S• の固定界面（L1 §6）を受領し、全 gapped 図式を保持した具体的 wS•C を構成。
  全 Ar 成分での W 判定・全ての面退化・元の core からの包含を接続済み。
  wS•C → core S•(C/D) と包含側 wS•(D,qi) → wS•(C,q) を自然変換として構成し、
  元の core の射を回収する可換四角形を証明済み。核側の全相対 S_n は弱可縮。
  可換四角形の実現後の homotopy pullback 性・商比較の同値性はまだ主張しない。
- 商の核を K-1 の `ClosedStablePredicate` として束ね、E(C,C,ker q) を構成した。
  底辺の W 所属との同定と、元の cofiber 射影の trivial Kan fibration 性を証明。
  全境界持ち上げから W 辺図式の安定性と完全な ∞ 圏同値を導き、元の射影を回収。
  この同値の coherent な逆を通す正有限反復実現の加法性と両射影の式を証明済み。
  全有限 W 列を全高次自然変換込みの全部分図式圏で構成し、全合成辺で W 判定を証明。
  一辺の段との一致・全面退化・任意の列図式圏の安定性・制限の完全性を証明済み。
  `StableModel` 値の単体的対象と段ごとの反復 core S 実現へ束ねた。
  全合成辺の完全な抽出と、全列に共通の相対 cofiber 切断を構成済み。
  補完・核値 cofiber は全再添字と厳密に可換。実底辺の回収・核所属・零性判定も証明。
  全 cofiber 族を関手圏の実 cofiber 列へ転置し、再添字・元の核値完全関手を回収。
  関手圏で全二単体の八面体族を構成し、長辺・第二短辺の共通補完との全図式の自然同型、
  最後の比較列の三頂点の核値性を証明し、E(ker q,B,ker q) 値の完全関手を構成済み。
  元の実四角形の族を包含で回収し、始点は第一短辺の共通 cofiber と厳密に一致。
  cofiber 評価は第二短辺の共通 cofiber と核の実関手圏で自然同型。八面体の再添字比較は未完。
  核の相対 middle 完全関手と、K-1 の全正有限反復加法射・任意相対完全関手の因子分解を構成。
  八面体の middle と長辺の核値 cofiber の自然同型、比較列の全反復加法性も証明済み。
  K-S• 追加固定界面を受領し、元の三辺の cofiber 実現射の加法性を全正有限反復で証明。
  元の射対の全再添字との厳密な可換性と加法性の再添字整合性、退化辺の核値 cofiber 族の零性も証明。
  列全体の加法性比較の自然性・実現後の fiber 比較は未完。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 7146 jobs・専用監査 48 モジュール 349 宣言が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
  所有 import 閉包 3429 モジュールは EInfinity を含まない。全体 23888 jobs で成功。

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
- なし（今回の元の三辺の加法性・再添字・退化零性の3モジュール・集約・監査・本計画を含める）。

### 既知の問題
- 所有 import 閉包の破損なし。前回の共有ルートの intervalMinimum 同名衝突は他レーンで解消済み。
  K-6 全体・有限 W 列全体の加法性比較の自然性・連結版の cofinality 条件は未完。

### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  元の初期頂点評価と連続する全辺の共通 cofiber により、有限 W 列全体の積との比較を構成する。
  一辺の加法性と三辺の実現射の整合性を使い、全列の比較の同値性へ進む。
  共通補完の再添字可換性を保持して K-2 の単体積版 Quillen A に接続する。
  商比較の全写像空間を含む局所化・cofinality 条件も別に証明する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
