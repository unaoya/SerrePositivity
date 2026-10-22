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
  関手圏内の八面体族を E(ker q,B,ker q) へ制限し、元の三辺の全正有限反復加法性を証明。
- 初期頂点と全連続辺の cofiber から、空列を含む有限 W 列の実現と積との比較を構成済み。
  各射影は元の評価を回収し、任意の制限後の頂点・実合成辺との厳密な対応も証明。
  一辺では同じ二成分が既存の加法性写像を回収し、全正有限反復で局所化同型。
  零長では初期頂点評価・空積を除く射が厳密同型。零長を含む全長で全正有限反復の局所化同型。
  有限積比較の全単体的な自然同値・実現後の fiber 比較は未完。
  全面・全退化の元の成分を照合。内部面の合成は隣接 cofiber の K-1 加法、
  第零面の初期成分は初期頂点と第一 cofiber の核の作用。退化の挿入 cofiber は全関手圏で零。
- 二辺の内ホーン制限は W 条件を反映し、trivial Kan fibration・完全な安定圏同値。
  元の両短辺を保つ安定な厳密引き戻しである。単体左 fiber・Quillen A を基底変換し、
  零・実押し出しの共同反映と S/cofiber 交換で全 S_n・全多重対角の同じ射対の同値性を証明。
- 先行 Δ[n+1] と最後の Δ[1] の零単体上の押し出しを構成。長い単体への包含は inner anodyne。
  core 値図式の厳密貼合せ・延長・全関手圏内の同型で W 条件を反映し、制限は trivial Kan fibration。
  共有端点を元の最終頂点と照合した安定な厳密引き戻しで、両成分は零・実押し出しを共同反映。
  全 cofiber 補完を持つ同じ模型・切断を RelativePullback の全反復定理へ接続。
  元の先行面・最後の連続辺・Fin 終端積を保つ帰納式により、全正有限長の有限比較も局所化同型。
- 元の S_n(W 列_m) の頂点と wS_n(B) の実 m 単体を、内部 Hom の交換で厳密に同定。
  全零対角・実押し出し・W 条件を保ち、両方向の全面・全退化で可換。object S(W 列) と
  相対 S の交換した二重単体集合・対角の厳密同型を構成。K-1 の各行の object/core 比較から、
  相対 S の対角 → W 列の core S 実現の対角の実際の比較射が局所化同型と証明。
  同じ単回反復実現 F₁ の対角へ自然な座標同型で接続。包含側の任意の完全関手による
  W 列の後合成は安定な入力の単体的自然変換で、実単体・二重単体・対角の交換と厳密に可換。
  相対 S の核側の写像を同じ W 列の core/単回反復実現へ運ぶ可換四角形を証明。
  零長同型の逆と元の退化で全定数 W 列を構成。全単体作用素・完全関手と厳密に可換で全頂点を回収。
  gapped 交換と object/core 比較を通し、元の core 包含が相対 S の実比較の後で同じ定数包含になる
  局所化等式を証明（core S・同じ F₁ の両模型）。fiber 性はこの照合からまだ未主張。
- 工程 (c) の必要条件：K-5 の実 Sp 長完全列により、右射影の全射性と接続射の
  自明性を同定。左項が連結なら元の零次射影は全射。cofinality の十分条件は未証明。
- 現在の対象ビルド 7255 jobs・専用監査 154 モジュール 906 宣言が成功。
  標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
  所有 import 閉包 3538 モジュールは EInfinity を含まない。全体 24126 jobs で成功。
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
- weakStringFiniteComparison_localized_isIso（零長を含む全長・全正有限反復）。
- weakStringFiniteComparison_innerFace_addition、weakStringKernelCofiber_degeneracy_inserted_zero。
- standardTail_isPushout、standardTailInclusion_innerAnodyne、standardTailEndpoint_eq_yoneda、
  tailWeak_isPullback、tailWeakPrefixExact、tailWeakEdgeExact。
- weakStringPredicate_iff_tail、weakStringTailEquivalence、
  weakStringTail_multiRealization_localized_isIso、weakStringTail_prefix_ambient。
- tailWeak_jointReflection、weakCofiberCompletionEquivalence、tailPrefixEndpointTop_eq、
  tailRelativePullback、weakStringTailMultiStep_localized_isIso（全長・全正有限反復）。
- weakRelativeMultiAction、weakStringVertexMultiAction、weakStringFiniteComparison_face_zero_action。
- weakStringObjectRelativeIso、weakStringObjectRelativeDiagonalIso、
  relativeSWeakStringCoreComparison_localized_isIso（元の実比較射）。
- relativeSWeakStringMultiComparison_square、relativeSWeakStringCoreComparison_square。
- weakStringConstantExact、weakStringStableConstant、
  relativeSWeakStringMultiComparison_coreInclusion、weakStringRealizationConstantDiagonal_postcomp。
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
- なし（今回の定数 W 列・元の core 包含の実照合・局所化での比較の8モジュール等を含める）。
### 既知の問題
- 所有 import 閉包の破損なし。前回の共有ルートの intervalMinimum 同名衝突は他レーンで解消済み。
  K-6 全体・有限 W 列全体の加法性比較の自然性・連結版の cofinality 条件は未完。
### 次の一手
- `relativeSimplicialKernelSquare` の実現後の homotopy pullback 性へ進む。
  元の core 包含・核側の写像を保つ比較で relativeSimplicialKernelSquare を W 列側へ移す。
  全長の加法性から homotopy fiber 性を証明する。有限積の自然性・商の写像空間・cofinality も未完。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
