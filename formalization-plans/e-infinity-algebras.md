# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：γ1.5 完了。γ3b は任意の小圏で元の非反転 q_x の同値性・全導来 fiber の可縮性による両向き判定と、pinched Hom の直接 fiber 模型まで公開。
  γ3c の 𝒮 の小積・Sp の有限積（空積含む）、一脚 fibration の引き戻し、fibration の塔の実際の ∞ 極限を公開。𝒮 の小余積・任意の span・任意の列の ∞ 余極限も公開。
  通常の随伴と整合する自然な単体的 Hom 同型からの極限保存、豊穣右関手の coherent nerve による像との一致、同図式の全 coherent 極限錐への拡張まで公開。
  今回は Kan 複体の `K × − ⊣ Map(K,−)` の通常の随伴・豊穣 Hom 同型・零単体の一致と strict 図式の ∞ 極限保存を構成。
  両対象の anodyne Kan 置換（全対象 cofibrant）を代入し、`AdjunctionHom` の frame 同型との可換性を全単体で検証。
  固定した単射・anodyne・Kan fibration・trivial Kan fibration の保存も公開。γ3c 全体・一般の γ4 は未完了。
  一般の小図式の重み付き coend を実際に構成。通常の Hom 普遍性・図式の関手性・tensor による普遍性の保存と、
  coend の内部 Hom = 反変 Hom の重み付き end の同型（終域に自然、全単体）を公開。
  Bousfield–Kan 重みに特殊化し、Kan 置換した対象からの Hom と既存の反変豊穣 Hom の end のホモトピー同値を構成。
  重み付き end の反転を成分公式・係数自然性つきの厳密な同型として構成。反転重みの coend の反転 Hom から、
  `reflectedHomHolimConeComparison` の係数の end への同型を公開し、Kan 置換後の比較も同値と検証。
  一般の Kan 値図式の native な coherent 余錐を元の図式上に構成し、頂点が反転 coend の Kan 置換そのものと証明。
  豊穣 Hom の族・頂点評価・native な極限判定を任意の coherent 錐へ拡張。
  頂点評価を固定した持ち上げの相対ホモトピーと、制限後の関手同型を公開。
  構成済みの coend の錐の極限性を、頂点評価と制限を満たす実際の族の構成へ還元。
  coend の Hom 比較の豊穣自然性を全 Hom パラメータで証明し、恒等射の普遍切断点からの復元公式を構成。
  反転係数の end に作用を移し、Kan 置換後の既存の Hom 比較についても同じ公式を検証。
  その普遍切断点の像が構成済みの coherent 余錐の普遍点と一致することを証明。
  反転 end の同型の評価を各係数の実際の評価へ戻し、豊穣後合成の係数公式を証明。
  weighted nerve に全反転 Hom パラメータで前合成する射を構成し、path の最小点による係数の合成公式を検証。
  この射から実際の coslice の族・coherent 錐の全空間への族を構成し、底の図式を保つことを証明。
  これは元の図式上の族。構成済みの錐の図式全体上の族はまだ未構成で、余極限性は未証明。詳細はコミットメッセージを参照。
  F2-lite 第 2 部の分担と工程は `infinity-core-F2.md` §3 に記載。
- **残り**（依存順・時間は再開後の概算）：
  1. γ3c：𝒮 の一般の小さい余極限と任意の coherent な図式への接続。HTT 4.2.4.1、Kerodon 7.5.4.6、20〜50時間。
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
  `weightedCoslicePrecompositionFamily`、`weightedCoherentConePrecompositionFamily_over`。
- **依存と提供**：Core・F1（coherent Hom、切断、edgewise、通常の豊穣関手）、F1b（trivial fibration 上の相対ホモトピー）、Stable、KST/Spectra、Simplicial の小対象分解を読み取り専用で使用。
  提供先は F2 の 𝒮、L9／K-Sp の Sp、E2b。集約は InfinityCategories/HomotopyLimits.lean、監査は scripts/audit_homotopy_limits.lean。
  型は Lean、運用規約は foundations.md §8。README に実施記録は追記しない。
- **未コミット**：今回の保存単位は ReflectedWeightedSectionsEvaluation・ReflectedWeightedHomCoefficients・WeightedConePrecomposition・WeightedCoslicePrecomposition、集約・監査、本 N 節、F2 計画 §3。保存後は N 所有の変更なし。他レーンの変更は温存。
  root の迷子 RelativeFreePathBoundary は正しい場所に修正版がコミット済みの N 旧稿と確認し、削除済み。
- **既知の問題**：停止時の対象ビルド・監査に失敗なし。新規 sorry・追加公理・公開名衝突なし。監査の既存の重複1件を除去済み。
  今回の公開型に ModelCategory SSet や IsRightQuillen の追加仮定なし。SSet の充填性・cofibrancy は Mathlib の固定 Quillen 類を使用。root 全体は未検証。
  完全なモデル構造の存在を与える `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので主経路へ import しない。
  今回はその存在命題を使わず固定類の保存と Hom 比較を証明しており、一般のモデル圏からの導出を済ませたとは数えない。
  γ4 用の Hom 同型は y に全単体で自然、x の高次豊穣自然性は未要求。従って通常の Quillen 条件だけからの ∞ 随伴の完成とは数えない。
  Sp では指定した Hom の局所 Kan 性・Ω 条件・cofibrancy を保持。一般の図式と右導来関手の cf 置換・高次整合性は後続課題。
  依存が壊れたら回避せず停止する。他レーンの作業中変更はコミットしない。
- **次の一手**：end のパラメータ付き係数の射と weighted nerve の評価の可換式を証明する。
  `reflectedWeightedHomPostcomposition_evaluation` は end の係数での実際の合成を、
  `weightedCoherentCoefficient_precomposition` は cone simplex の path 座標での実際の合成を与える。
  両者を `bousfieldKanWeightedNerveEvaluation` で照合し、`reflectedHomHolimConeComparison` の全体での整合性へ進む。
  `weightedCoslicePrecompositionFamily` は元の図式上の族を既に与える。次に構成済みの錐の図式全体の族 `a` を延長し、
  頂点評価 `ha`・制限 `hr` を満たして `comparison_lifts` 判定へ渡す。
  必要なら `hr` は関手同型による比較へ弱める。同じ始域・終域を持つ同値性だけでは代用しない。
  その後、反対の極限錐から元の余極限性を戻し、任意の coherent 図式へ接続する。

### E2a（既存の引き継ぎ）

- **現在地**：E2a-0（Ch(A) の射影モデル構造）、E2a-1（オペラッド・自由代数随伴）、
  E2a-2（Barratt–Eccles オペラッド・augmentation）まで完了。
  E2a-3 は承認済みの Hopf オペラッド＋区間＋path object 経路の工程 (1) の途中。
  一般の小さい単体集合の正規化 AW 成分を自然数次数のテンソル複体への鎖写像
  `diagonal` に束ね、次数分割の有限和公式、成分との一致、自然性、余結合性、
  augmentation 鎖写像 `counit` と左右余単位・その自然性まで検証済み。
  自然なテンソル比較（結合子・左右単位子との適合性を含む）で整数模型へ移送し、
  実際の E(n) の `complexDiagonal`、余結合性・左右余単位・Σ_n 同変性と
  既存 augmentation との一致まで検証済み。一般の X,Y の正規化 shuffle 次数成分・生成元公式・
  自然性、前半・後半経路の構成と全単射、切断の符号公式を検証済み。
  有限和の添字替えから `diagonal_value` と加群射の等式 `component_diagonal` まで検証済み。
  一般 shuffle の微分可換性を零次数も含めて検証し、自然な鎖写像 `Shuffle.chainMap` を構成。
  複体上の余代数射性と Hopf オペラッド射は未完成。
  E2a-3 の転送モデル構造、E2a-4・5 は未完成。現在地のコードと検証は本節と
  同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. `Shuffle.chainMap` と `component_diagonal` をテンソル複体の包含・交換の成分公式へ接続し、
     複体上の AW 余代数射性を閉じる。負次数テンソル比較の braiding 適合性も接続する。
     Berger–Fresse（BF）2004 §1.1.3–§1.1.4、24〜60 時間。
  2. arity ごとのテンソルオペラッドと AW の自然性を使い、E → E ⊗ E の
     オペラッド射性・余結合性・余単位・Σ_n 同変性を閉じる。BF §1.1.4、16〜32 時間。
  3. E-coalgebra 区間の抽象 structure から全代数の functorial path object、
     fibrations.llp ⊆ 弱同値、J-cell acyclicity、小対象性・極限余極限と転送の適用を閉じる。
     Berger–Moerdijk（BM）2003 命題 4.1・§4.6.3、BF §3.1、24〜60 時間。
  4. TR : E → χ のオペラッド射性を一般に証明し、χ の区間切断作用を Δ¹ に適用する。
     BF §1.3・§3.1 と McClure–Smith の区間切断作用、80〜200 時間。
     着手前にファイル数・主要補題の見積もりを計画に一段落で記す指示が未実施。
     Δ¹ の作用は必要次数 r ≤ n に特殊化してよい。TR 自体は一般に証明する。
  5. 具体区間を抽象界面へ代入して E2a-3 を完成。BM 命題 4.1、BF §3.1、8〜24 時間。
  6. E2a-4：右 Quillen、全対象 fibrant、底での homotopy 引き戻し、H⁰ の可換環構造、
     離散可換代数の E 代数化。BM 命題 4.1、BF §3.1、16〜40 時間。
  7. E2a-5：homotopy function complex と π₀ の Hom 比較。
     Hovey §5・Dwyer–Kan、既存 HomotopyFunctionComplex の具体的適用、12〜24 時間。
- **主要宣言**（名前のみ）：
  `SerrePositivity.EInfinity.projectiveModelCategory`、
  `SerrePositivity.EInfinity.Operad.freeAlgebraAdjunction`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation_quasiIso`、
  `SerrePositivity.EInfinity.BarrattEccles.complexContraction`、
  `SerrePositivity.EInfinity.BarrattEccles.equivariantBasis_rightAction`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_generator`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_natural`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_coassoc`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_left_counit`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_right_counit`、
  `SerrePositivity.EInfinity.AlexanderWhitney.component_d`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonalDegree_eq_sum`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_projection`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_natural`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_coassoc`、
  `SerrePositivity.EInfinity.AlexanderWhitney.counit`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_left_counit`、
  `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_right_counit`、
  `SerrePositivity.EInfinity.AlexanderWhitney.counit_natural`、
  `SerrePositivity.EInfinity.NegativeTensor.comparison`、
  `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal`、
  `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_projection_generator`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_rightAction`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_coassoc`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_left_counit`、
  `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_right_counit`、
  `SerrePositivity.EInfinity.Shuffle.component`、
  `SerrePositivity.EInfinity.Shuffle.component_generators`、
  `SerrePositivity.EInfinity.Shuffle.chainMap`、
  `SerrePositivity.EInfinity.Shuffle.chainMap_natural`、
  `SerrePositivity.EInfinity.Shuffle.pathCutEquiv`、
  `SerrePositivity.EInfinity.Shuffle.pathCut_sign`、
  `SerrePositivity.EInfinity.Shuffle.diagonal_value`、
  `SerrePositivity.EInfinity.Shuffle.component_diagonal`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com。
  Alg_E のモデル構造、右 Quillen 忘却関手、E2b 用 CAlg はまだ提供していない。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：停止時の対象ビルドは成功（2683 jobs）、公理監査は成功
  （4731 宣言、標準 3 公理のみ）。新規 sorry・追加公理・名前衝突はない。
  今回の AW 宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：`Shuffle.component_diagonal` を `Shuffle.chainMap` の余代数射性へ束ねる。
  自然数鎖テンソルの `tensorμ` の斉次包含上の公式と Koszul 符号を証明し、
  二つの AW 対角の有限和を同じ切断座標で展開する。既存の BE 部分合成との接続、
  負次数比較の braiding 適合性を閉じる。まだ区間・path object には着手しない。

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
