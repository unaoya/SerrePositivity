# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）
### 現在地
- 工程 (a) 完了。`IsVerdierSequence` の核条件から包含の本質像と安定閉包を同定。
  cofiber の W 条件と商の可逆性、実二対三・押し出し・引き戻し・ホモトピーに対する拡大安定性を証明。
- 工程 (a) は thick 性より弱い安定な本質像で成立。冪等完備化・fiber 性は未主張。
- 工程 (b)：相対図式の全単体・W 判定・内ホーン充填・再添字・core 包含を構成し、
  商の core の逆像と同定し、wS•C・商への自然変換・核の四角形へ接続。核側の全相対 S_n は弱可縮。
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
  全正有限長で全正有限反復の局所化同型を証明。全列の自然性・実現後の fiber 比較は未完。
- 二辺では、二短辺の W 条件が元の全二単体条件を反映することを証明し、内ホーン制限を
  trivial Kan fibration・完全な安定圏同値にした。標的は共有端点上の二つの W 辺図式圏の
  厳密な引き戻し。元の両短辺を回収し、元の二辺の有限比較をこの同値と同じ積比較に因子分解済み。
  単体左 fiber の厳密基底変換同型を構成し、K-2 の単体積版 Quillen A を基底変換後へ移した。
  零対象・実押し出しの両成分反映を証明し、全 S_n・元の object S でも厳密引き戻しとした。
  第二辺の全 cofiber 補完模型から元の二辺への射影は trivial Kan fibration。
  相対 K-1 の単体左 fiber を基底変換し K-2 により、第一 W 辺 × 第二核値 cofiber
  への比較を証明。一辺の加法性・Fin 2 積の両射影を保つ同型と合成し、二辺の比較に接続。
  両射影の共同反映を全 S_n へ移し、相対 cofiber 交換と厳密に照合。全行・全多重対角の
  自然な元の射対で帰納し、同じ有限積比較を全正有限反復へ拡張した。
- 全有限列の帰納の入力：先行 Δ[n+1] と最後の Δ[1] の元の零単体上の押し出しを構成。
  長い Δ[n+2] への包含は inner anodyne、全図式圏への制限は trivial Kan fibration。
  共有端点を先行単体の最終頂点と同定し、先行 W 列・最後の W 辺の安定な厳密引き戻しも構成。
  core 値図式の厳密貼合せ・内 anodyne 延長・同じ制限の全関手圏内の自然同型で W 条件を反映。
  W 制限後も trivial Kan fibration・完全な同値で、全正有限反復の局所化同型と両実成分の回収を証明。
  先行列・最後辺の共同反映と、任意の実 W 辺の全 cofiber 補完・同じ切断を構成。
  共有端点を既存の最終頂点評価と厳密に照合し、RelativePullback の全反復定理に接続。
  元の長い W 列 → 先行列 × 最後の核値 cofiber の射対は全正有限反復で局所化同型。
  先行包含を最後の標準面射、最後の実辺を連続辺の終端添字と厳密照合。
  Fin の終端追加の積同型・同じ全成分の帰納式により、全正有限長の有限比較の同値性を証明。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 7221 jobs・専用監査 121 モジュール 745 宣言が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
  所有 import 閉包 3504 モジュールは EInfinity を含まない。全体 24020 jobs で成功。
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
- relativeDiagram_kernel_isWeaklyContractible、connectiveFiber_projection_piZero_surjective。
- relativeSConstruction、relativeSConstruction_mem_edge_iff、relativeSimplicialSConstruction、
  relativeSimplicialQuotientMap、relativeSKernel_isWeaklyContractible、relativeSimplicialKernelSquare。
- weakCofiberProjection_trivialKanFibration、weakArrowMultiAdditivityMap_localized_isIso。
- weakStringFiniteComparison_reindex_cofiber、weakStringFiniteComparison_one_localized_isIso。
- weakStringFiniteComparison_two_factor、weakStringFiniteComparison_two_localized_isIso_iff。
- relativeCofiberBaseChange_localized_isIso、completedTwo_objectS_isPullback、
  composableWeakObjectStep_localized_isIso、composableWeakMultiStep_one_localized_isIso。
- RelativePullback.multiPair_localized_isIso、composableWeakMultiStep_localized_isIso、
  weakStringFiniteComparison_two_localized_isIso（全正有限反復、元の全成分を回収）。
- standardTail_isPushout、standardTailInclusion_innerAnodyne、standardTailEndpoint_eq_yoneda、
  tailWeak_isPullback、tailWeakPrefixExact、tailWeakEdgeExact。
- weakStringPredicate_iff_tail、weakStringTailEquivalence、
  weakStringTail_multiRealization_localized_isIso、weakStringTail_prefix_ambient。
- tailWeak_jointReflection、weakCofiberCompletionEquivalence、tailPrefixEndpointTop_eq、
  tailRelativePullback、weakStringTailMultiStep_localized_isIso（全長・全正有限反復）。
- weakStringTailMultiStep_canonical、weakStringFiniteComparison_factor、
  weakStringFiniteComparison_positive_localized_isIso（全正有限長・全正有限反復）。
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
  RelativeCofiberLeftFiber と RelativeFiberEquivalence の相対左 fiber・quotient 局所化同型も
  L1 §6 に固定済み（相対 fiber 内の ρ・θ に基づく）。K-F の基底変換と Quillen A へ接続した。
- 工程 (c) の必要条件は K-5 の `NativeFiberSequence` の整数長完全列を入力にする。
  Sp の IsStable は使わない。K-3 の具体的 K 関手・π₀ 比較は未接続。
### 未コミット
- なし（今回の標準面・連続辺照合・Fin 終端積同型・有限比較帰納の6モジュール等を含める）。
### 既知の問題
- 所有 import 閉包の破損なし。前回の共有ルートの intervalMinimum 同名衝突は他レーンで解消済み。
  K-6 全体・有限 W 列全体の加法性比較の自然性・連結版の cofinality 条件は未完。
### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  全正有限長の有限比較を用い、全ての面・退化で初期頂点と cofiber 群の変化を照合する。
  再添字整合性・商の写像空間・cofinality・実現後の fiber 比較へ進む。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
