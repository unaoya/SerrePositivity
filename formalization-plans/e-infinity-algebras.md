# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：γ1.5 完了。γ3b は任意の小圏で元の非反転 q_x の同値性・全導来 fiber の可縮性による両向き判定と、pinched Hom の直接 fiber 模型まで公開。
  γ3c は 𝒮 の小積・Sp の有限積（空積含む）、一脚 fibration の引き戻し、fibration の塔の実際の ∞ 極限を公開。
  𝒮 の小余積・任意の span・任意の列の ∞ 余極限も公開。
  通常の随伴と整合する単体的 Hom 同型からの極限保存と、豊穣右関手の coherent nerve による像との一致を証明。
  任意の coherent な極限錐にも適用できる。γ4 の具体例 `K × − ⊣ Map(K,−)` は通常の随伴・豊穣 Hom 同型・零単体を照合。
  両対象の anodyne Kan 置換を含む frame Hom の可換性を全単体で検証し、固定した Quillen 類の保存も公開。
  一般の小図式の重み付き coend、tensor と内部 Hom の普遍性、反転係数の end との自然な同型を構成。
  Kan 置換後の Hom 比較は全 Hom パラメータの豊穣合成を保ち、恒等射の普遍切断点から復元できる。
  実際の coherent な余錐を構成し、頂点を Kan 置換した反転 coend と同定。
  任意の coherent 錐全体の明示的な Hom の族を構成し、頂点評価・元の図式への制限を標準比較と厳密に照合。
  通常の任意の小圏上の Kan 値図式では、構成した反対錐の ∞ 極限性・元の native な余錐の ∞ 余極限性を無条件に証明。
  任意の coherent な図式の切断空間は、形状の押し出しの引き戻し・セル付加・相対骨格の塔の厳密な極限で表示。
  left fibration では塔の各値は Kan、制限は Kan fibration。図式の底上の通常の余極限についても一般化済み。
  部分余極限頂点を付加した実際の形状と図式、指定した余錐を頂点ごと保つ延長と余極限性の保存・反映を構成。
  全ての脚を含む coherent な比較と実際の頂点間の射を抽出し、部分余極限対象の Kan 値 span とその押し出し候補を構成。
  今回、始対象を持つ left fibration の fiber の Hom 表示を実際の辺で計算し、部分余錐の制限の π₀ の像を、
  付加で作った比較辺そのもののホモトピー類と同定。二重 coslice の比較辺の終点と頂点への射影も厳密に検証。
  共通部分で同じ連結成分にある部分余錐は、単射側を同じ成分内で直して厳密に貼れることを証明。
  span の余錐に沿う輸送後の部分余錐の連結成分の照合と、貼り合わせた余錐の普遍性は未完了。
  γ3c 全体・一般の γ4 は未完了。F2-lite 第 2 部の分担と工程は `infinity-core-F2.md` §3。
  詳細な実施記録はコミットメッセージを参照。
- **残り**（依存順・時間は再開後の概算）：
  1. γ3c：通常の小圏上の Kan 値図式の coend 余極限から、任意の coherent な図式への接続。HTT 4.2.4.1、Kerodon 7.5.4.6、20〜50時間。
  2. γ4：具体例を一般の simplicial Quillen 随伴の cofibrant-fibrant 置換・frame へ拡張する。HTT 5.2.4.6、8〜20時間。
  3. 2 と F1b の随伴 API から導来 ∞ 随伴の単位・余単位・整合性と一般の右導来関手の極限保存を構成する。HTT 5.2.4.6、Kerodon §6.2、12〜30時間。
  4. E2a-3・4 と γ2 の豊穣化の確定後、Alg_E と忘却関手へ適用する。HTT 1.1.5.10・4.2.4.1・5.2.4.6、16〜40時間。E2a の現状は下記参照。
- **主要宣言**（名前のみ。名前空間 SerrePositivity.InfinityCategories.HomotopyLimits）：
  `strictCoherentCone_isLimit_iff_general_comparisonFiber`、`strictConePinched_generalOriginalEnd_equivalence`、
  `spaceProductCone_isLimitCone`、`spacePullbackCone_isLimitCone`、`spaceTowerCone_isLimitCone`、
  `spaceArbitraryPushoutCocone_isColimitCone`、`spaceArbitrarySequentialColimitCocone_isColimitCone`、
  `SimplicialAdjunctionHomIso`、`strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso`、
  `kanTensorAdjunctionHomIso`、`kanInternalHom_map_isLimit`、`kanReplacedTensorFrameAdjunction_square`、
  `weightedColimitFunctor`、`weightedColimitHomNatIso`、`kanBousfieldKanColimitObject`、
  `kanBousfieldKanColimitHomComparison_homotopyEquivalence`、`weightedSectionsReflectedIso`、
  `reflectedWeightedColimitHomIso`、`bousfieldKanCoherentConeComparison_homotopyEquivalence`、
  `bousfieldKanCoherentCocone`、`bousfieldKanCoherentCocone_vertex`、
  `coherentCone_isLimit_iff_reflectedNativeComparison`、`coherentConeFamily_homotopy_over_apex`、
  `coherentCone_isLimit_of_family_lifts`、`bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts`、
  `weightedColimitHomComparison_enriched_naturality`、
  `kanReflectedBousfieldKanColimitHomComparison_of_point`、`bousfieldKanCoherentConePoint_of_end_point`、
  `reflectedWeightedHomPostcomposition_evaluation`、`weightedCoherentCoefficient_precomposition`、
  `weightedCoslicePrecompositionFamily`、`weightedCoherentConePrecompositionFamily_over`、
  `bousfieldKanWeightedNerveEvaluation_parameter_map`、`kanReflectedBousfieldKanEndPostcomposition_eq`、
  `bousfieldKanCoherentConeComparison_uncurry`、`coherentCosliceSourcePrecomposition`、
  `coherentCosliceSourcePrecomposition_weighted`、`coneIdentityCosliceSection`、
  `coherentConeSourceFamily`、`coherentConeSourceFamily_evaluation`、
  `bousfieldKanCoherentConeSourceFamily_restrict`、`bousfieldKanCoherentOppositeCone_isLimit`、
  `bousfieldKanCoherentCocone_isColimit`、`kanDiagramCoherentNerve_hasColimit`、
  `relativeFunctorOverPre_pushoutIso`、`relativeFunctorOverColimitCone_isLimit`、
  `skeletalSectionCone_isLimit`、`skeletalSectionDiagram_map_fibration`、`skeletalCellSectionCone_isLimit`、
  `colimitAttachedCocone`、`colimitAttachmentComparison_restrict`、`colimitAttachmentApexHom`、
  `coherentShapePushoutCocone`、`partialColimitApexSpan`、`partialColimitPushoutCocone_isColimit`、
  `leftFibrationInitialFiberPiZeroEquiv_edgeAt`、`coconeMappingSpacePiZeroEquiv_attachment`、
  `exists_cocone_glue_of_boundary_component`。
- **依存と提供**：Core・F1（coherent Hom、切断、edgewise、通常の豊穣関手）、F1b（trivial fibration 上の相対ホモトピー）、Stable、KST/Spectra、Simplicial の小対象分解を読み取り専用で使用。
  提供先は F2 の 𝒮、L9／K-Sp の Sp、E2b。集約は InfinityCategories/HomotopyLimits.lean、監査は scripts/audit_homotopy_limits.lean。
  型は Lean、運用規約は foundations.md §8。README に実施記録は追記しない。
- **未コミット**：今回の保存単位は InitialFiberEdgeVertex・InitialFiberEdgePiZero・CoconeComparisonEdge・CoconeComparisonPiZero・ColimitAttachmentPiZero・CoconeBoundaryRectification、集約・監査、本 N 節、F2 計画 §3。保存後は N 所有の変更なし。他レーンの変更は温存。
  root の迷子 RelativeFreePathBoundary は正しい場所に修正版がコミット済みの N 旧稿と確認し、削除済み。
- **既知の問題**：停止時の対象ビルド・監査に失敗なし。新規 sorry・追加公理・公開名衝突なし。監査の既存の重複1件を除去済み。
  今回の公開型に ModelCategory SSet や IsRightQuillen の追加仮定なし。SSet の充填性・cofibrancy は Mathlib の固定 Quillen 類を使用。root 全体は未検証。
  完全なモデル構造の存在を与える `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので主経路へ import しない。
  今回はその存在命題を使わず固定類の保存と Hom 比較を証明しており、一般のモデル圏からの導出を済ませたとは数えない。
  γ4 用の Hom 同型は y に全単体で自然、x の高次豊穣自然性は未要求。従って通常の Quillen 条件だけからの ∞ 随伴の完成とは数えない。
  Sp では指定した Hom の局所 Kan 性・Ω 条件・cofibrancy を保持。一般の図式と右導来関手の cf 置換・高次整合性は後続課題。
  依存が壊れたら回避せず停止する。他レーンの作業中変更はコミットしない。
- **次の一手**：span の余錐の脚に沿って輸送した部分余錐の、共通部分での連結成分の一致を証明する。
  最初に始対象から選んだ辺と輸送辺の `Edge.compStruct` に今回の評価式を適用し、Hom 表示で輸送が後合成になることを示す。
  `coconeMappingSpacePiZeroEquiv_attachment` で元の部分余錐の制限と比較辺の類は照合済み。
  `sliceUnderProjection` の left fibration 性で部分余錐を span の終点へ輸送し、
  `leftFibrationInitialFiberPiZeroEquiv_edgeAt` と span の余錐の合成三角形から、輸送後の両制限の π₀ の像の一致を示す。
  `exists_cocone_glue_of_boundary_component` へ渡せば、単射側を同じ成分に保ったまま、厳密に貼った元の図式の余錐を得る。
  その余極限性を付加による制限の同値と切断空間の押し出し表示で照合し、続いて骨格の無限段階を処理する。
  小さい `K` と `p : ulift K → SpaceInfinity` のセルの添字を u に戻すことも検証する。
  任意の coherent 図式の余極限性を閉じてから γ4、F2-lite 第 2 部へ進む。

### E2a（既存の引き継ぎ）

- **現在地**：E2a-0（Ch(A) の射影モデル構造）、E2a-1（オペラッド・自由代数随伴）、
  E2a-2（Barratt–Eccles オペラッド・augmentation）まで完了。
  E2a-3 は承認済みの Hopf オペラッド＋区間＋path object 経路で、工程 (1) が完了。
  一般の小さい単体集合の正規化 AW 対角の鎖写像・自然性・余結合性・左右余単位と、
  一般 shuffle 鎖写像の AW 余代数射性を検証し、整数模型へ移送済み。
  `partialComposition_diagonal_tensorμ` が既存 BE 部分合成の余積適合性を与える。
  arity ごとのテンソルオペラッド `Operad.hadamard` を、両単位則・内外等変性・
  入れ子と独立な代入の結合則を含めて構成。頂点の群状元公式から単位保存を証明し、
  `hopfDiagonal` を実際の E → E ⊗ E のオペラッド射に束ねた。
  `BarrattEccles.hopf` はこの対角、既存の E → Com、余結合性・左右余単位則を持つ。
  Σ_n 同変性は対称列の自然性に含まれ、余可換性は要求しない。
  工程 (2) は P-coalgebra・射の圏・忘却関手・オペラッド射に沿う制限を構成済み。
  `CoalgebraInterval` は実際の余代数・二端点・収縮・余演算の保存図式と、
  底の境界 cofibration・収縮の擬同型からなる。区間の制限も構成済み。
  convolution の反復評価とその両変数自然性、各 arity の演算 chain map は構成済み。
  底の Hom(H,B) の `prepathComplex`、定数射と両端点評価の自然性も検証済み。
  `convolutionAction_unit` と `convolutionAction_equivariance` で単位則・全置換の等変性を検証。
  `convolutionAction_post` で P 代数射の後合成が各演算を保つことも検証済み。
  反復評価の二ブロックの連結・分割との整合性と、先頭の代入・余代入の評価の一致を検証。
  `convolutionAction_insertion_zero_evaluation` は標準の代入射・余代入射での等式を与える。
  `Algebra.ofFirstComposition` は等変性と先頭の合成則から全位置の代数公理を構成する。
  convolution 自体の部分合成則、余代数射の前合成、端点・定数の代数射性は未完成。
  E2a-3 の工程 (2) の転送と工程 (3)・(4)、E2a-4・5、E2b・G1′ は未完成。
  現在地のコードと検証は本節と同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. convolution の部分合成則、余代数射の前合成、定数・端点の代数射性を証明し、
     全代数の functorial path object を構成。底の評価の fibration・定数射の擬同型、
     fibrations.llp ⊆ 弱同値、J-cell acyclicity、小対象性・極限余極限と転送の適用を閉じる。
     Berger–Moerdijk（BM）2003 命題 4.1・§4.6.3、BF §3.1、24〜60 時間。
  2. TR : E → χ のオペラッド射性を一般に証明し、χ の区間切断作用を Δ¹ に適用する。
     BF §1.3・§3.1 と McClure–Smith の区間切断作用、80〜200 時間。
     着手前にファイル数・主要補題の見積もりを計画に一段落で記す指示が未実施。
     Δ¹ の作用は必要次数 r ≤ n に特殊化してよい。TR 自体は一般に証明する。
  3. 具体区間を抽象界面へ代入して E2a-3 を完成。BM 命題 4.1、BF §3.1、8〜24 時間。
  4. E2a-4：右 Quillen、全対象 fibrant、底での homotopy 引き戻し、H⁰ の可換環構造、
     離散可換代数の E 代数化。BM 命題 4.1、BF §3.1、16〜40 時間。
  5. E2a-5：homotopy function complex と π₀ の Hom 比較。
     Hovey §5・Dwyer–Kan、既存 HomotopyFunctionComplex の具体的適用、12〜24 時間。
  6. E2b：CAlg_R := N^hc と U : CAlg_R → D(R)、離散対象と極限。
     HTT §1.1.5・§5.2.4、γ2・γ4 の適用、16〜40 時間。その後 G1′（界面の述べ直し）。
- **主要宣言**（名前のみ）：
  `SerrePositivity.EInfinity.projectiveModelCategory`、
  `SerrePositivity.EInfinity.Operad.freeAlgebraAdjunction`、
  `SerrePositivity.EInfinity.Operad.hadamard`、
  `SerrePositivity.EInfinity.Operad.Hopf`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation_quasiIso`、
  `SerrePositivity.EInfinity.BarrattEccles.complexContraction`、
  `SerrePositivity.EInfinity.BarrattEccles.equivariantBasis_rightAction`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal`、
  `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal`、
  `SerrePositivity.EInfinity.BarrattEccles.partialComposition_diagonal_tensorμ`、
  `SerrePositivity.EInfinity.BarrattEccles.hopfDiagonal`、
  `SerrePositivity.EInfinity.BarrattEccles.hopf`、
  `SerrePositivity.EInfinity.Operad.Coalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraHom`、
  `SerrePositivity.EInfinity.Operad.restrictCoalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict`、
  `SerrePositivity.EInfinity.Operad.convolutionAction`、
  `SerrePositivity.EInfinity.Operad.convolutionAction_unit`、
  `SerrePositivity.EInfinity.Operad.convolutionAction_equivariance`、
  `SerrePositivity.EInfinity.Operad.convolutionAction_post`、
  `SerrePositivity.EInfinity.Operad.Algebra.ofFirstComposition`、
  `SerrePositivity.EInfinity.Operad.convolutionAction_insertion_zero_evaluation`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathComplex`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constantNat`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationNat`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com、
  テンソルオペラッドと E の Hopf 構造、余代数区間の界面と底の prepath object。
  Alg_E のモデル構造・右 Quillen U・CAlg は未提供。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：対象ビルド成功（2746 jobs）、公理監査成功（5327 宣言、標準 3 公理のみ）。
  新規 sorry・追加公理・名前衝突はなく、540 モジュールの import 閉包に他レーンの未コミット依存はない。
  今回の宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：工程 (2) の convolution の部分合成則を証明する。
  `convolutionAction_insertion_zero_evaluation` により先頭代入の評価は余代入の組み立て。
  Hopf 対角の部分合成保存、`Coalgebra.comp_coaction` と `Algebra.comp_action` を
  この評価式へ接続して先頭の合成則を閉じ、`Algebra.ofFirstComposition` で代数へ束ねる。
  その後に余代数射の前合成・端点・定数射の保存則を証明し P 代数へ束ねる。
  `prepathComplex` は底の複体の三角形と関手性だけで、まだ代数の path object ではない。
  TR・具体区間には着手していない。

作成日：2026-10-18。状態：計画。ε の経路として E2（モデル圏）を採用（2026-10-18 決定）。
全体の正本は [infinity-categories.md](infinity-categories.md) §0・§5。

## 0. 位置づけ

G1 の界面（perfectoid 化とその性質の束）を述べる場である CAlg_R を、
Ch(R) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏で実現する。
三段で進める。

| 段 | 内容 | 使い先 |
| --- | --- | --- |
| E2a（モデル圏まで） | オペラッド・Barratt–Eccles・E∞-dg 代数・転送モデル構造・右 Quillen な忘却関手・homotopy function complex | 界面の欄を「Alg_E の homotopy 引き戻し」「homotopy 写像空間」で述べる。γ を待たずに G1 の CAlg 版へ昇格できる |
| E2b（∞ 圏化、γ） | Alg_E の cofibrant 対象の単体的豊穣化と coherent nerve、homotopy 極限 = ∞ 極限、Quillen 随伴 = ∞ 随伴 | 界面を Lurie の言葉（quasicategory の引き戻し）で述べる。K 理論の Sp と共有 |
| E2c（BS の続き用） | 余単体的 E∞-dg 代数の Tot と余単体的可換環への E∞ 作用（Berger–Fresse）、単体的可換環のモデル圏と多項式解像度 | BS §4・§7・§8 の構成 |

E1（∞ オペラッド）は採らない。後で HA の定理を文字どおり引用したくなった場合に、
E2b ≃ E1 の比較（HA 4.5.4.7 型の rectification）を任意項目として検討する。

## 1. 既存資産

- `HomotopicalAlgebra/`：Mathlib `ModelCategory` 上の Quillen 随伴（H1）、Under（H2）、
  転送（`Transfer/Recognition.lean`：生成類から Mathlib の `ModelCategory` を構成、acyclicity は明示仮定；
  `Transfer/Right.lean`：右随伴が fibration と弱同値を作る転送）、Smith の定理、
  Bousfield 局所化、Reedy、`HomotopyFunctionComplex/`（frame による導来写像空間）、
  `Monoidal/`（モノイダルモデル圏、monoid axiom）。
- `Spectra/SymmetricSequence/`：対称列と Day 畳み込み（オペラッドの合成積の素材）。
- `DifferentialGraded/Complexes/Cells.lean`：`complexSphere`・`complexDisk`（射影モデル構造の生成 cofibration）。
- `InfinityCategories/Derived/`：semifree の閉性（cone・fiber・直和・テンソル・底変更）。
- Mathlib：`SmallObject`、`CategoryWithCofibrations/Fibrations/WeakEquivalences`、`ModelCategory`。
- 未整備：Ch(A) の非有界射影モデル構造（Mathlib は `CochainComplex.Plus` の injective のみ）、
  オペラッド、対称群作用つき複体。

## 2. E2a の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| E2a-0 | Ch(A) の非有界射影モデル構造：弱同値 = 擬同型、fibration = 各次数全射、生成 cofibration `complexSphere (n+1) → complexDisk n`、生成 trivial cofibration `0 → complexDisk n`。`Transfer/Recognition.lean` で構成 | Hovey, Model Categories 2.3.11 |
| E2a-1 | Ch(A) 上の対称オペラッド：各 arity n の複体 P(n) と Σ_n 右作用、合成、単位。代数、代数の射、自由代数 Sym_P（⊕ (P(n) ⊗ A^{⊗n})_{Σ_n}）、自由 ⊣ 忘却 | Loday–Vallette、Berger–Moerdijk 2003 §1 |
| E2a-2 | Barratt–Eccles オペラッド E：EΣ_n（Σ_n の translation 亜群の nerve）の正規化鎖。各 arity が可縮、Σ-cofibrant（各 E(n) が Σ_n 上自由な次数ごとの基底を持つ）、E → Com | Barratt–Eccles 1974、Berger–Fresse 2004 §1 |
| E2a-3 | Alg_E の完全な転送モデル構造：弱同値・fibration は忘却で作る。AW 対角による E の Hopf 構造と E-coalgebra 区間の抽象界面から全代数の functorial path object を構成し、fibrations.llp ⊆ 弱同値、J-cell acyclicity、`Transfer.Right.rightTransfer` の適用を先に証明。TR : E → χ と区間切断作用で N_*(Δ¹) を界面に代入する。始域の cofibrancy は追加しない | Berger–Moerdijk 2003 命題 4.1・§4.6.3、Berger–Fresse 2004 §3.1（TR は §1.3）。Hinich 4.1.1 は使用しない（正標数で E は Σ-split でない） |
| E2a-4 | U : Alg_E → Ch(A) は右 Quillen、全対象 fibrant、homotopy 引き戻し・homotopy 極限は底で計算。E 代数の H⁰ が可換環であること、離散可換代数は E 代数（E → Com 経由） | 同上 |
| E2a-5 | homotopy function complex Map^h(A, B)（`HomotopyFunctionComplex/` の frame を Alg_E に適用）、π₀ Map^h = Ho(Alg_E) の Hom | Hovey §5、Dwyer–Kan |

## 3. E2b（γ）の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| γ1 | 局所 Kan な単体的圏の coherent nerve は quasicategory（Mathlib `SimplicialNerve` に対して） | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| γ2 | Alg_E の cofibrant 対象の単体的豊穣化（Hopf オペラッド E による B ⊗ N^*(Δ^•) 型、または Dwyer–Kan 単体的局所化）と CAlg_R := N^hc | Berger–Moerdijk 2006、Hinich、Dwyer–Kan |
| γ3 | homotopy 極限 = ∞ 極限、右 Quillen ⇒ ∞ 極限保存、Quillen 随伴 ⇒ ∞ 随伴 | HTT 4.2.4.1、5.2.4.6 |

γ2 の単体的豊穣化が E2b の最大のリスクである。E2a の完了時点で方式を決める。

## 4. 受入基準と記録

dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。
配置は `SerrePositivity/EInfinity/`（E2a）、namespace `SerrePositivity.EInfinity`。
集約ファイルをルートに 1 行で追加する。既存の `HomotopicalAlgebra/`・`Spectra/` は編集せず、
必要な一般補題は新規ファイルに置く。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/e-infinity-algebras-log.md](archive/e-infinity-algebras-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
