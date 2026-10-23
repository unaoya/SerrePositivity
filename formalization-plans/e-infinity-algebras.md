# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：2026-10-23 コーディネータ停止指示による保存区切り。P-1 g は未完了。
  P_Σ の全部分 quasicategory・充満忠実な Yoneda 因子化・sifted 余極限閉性・sifted 密度生成は完了。
  sifted 保存関手からの元の Yoneda 制限そのものの全充満忠実性も完了。
  小さい sifted 余極限を持つ標的への左 Kan 延長存在、元の指定単位の可逆性・全関手同型による回収、全密度余錐像の余極限性まで保存済み。
  前層宇宙変更の全関手・評価／制限との厳密な可換性・小 coherent 余極限保存、全 Hom 錐による余極限判定を保存済み。
  全自然変換空間族と持ち上げた延長の全 Hom 族が、同じ元の Yoneda に沿う実際の右 Kan 延長であることも保存済み。
  前回保存 28b67dcb7 は共同 Yoneda Hom・共同評価の実 left fibration と元の全 twisted arrow からの二射まで。二射の延長・cofinality は未証明。
  **今回の区切り**：充満忠実な元の関手による twisted arrow・共同 Hom・全 Yoneda 制限の自然同型、左右 Kan 制限同型の持ち上げ、全余錐の形状置換の7モジュール21宣言。
  `mapUliftCocone_isColimit_of_quasicategoryShapes` は、小さい quasicategory 添字での保存を任意の小さい添字へ戻す。元の全余錐を厳密な制限で保持する。
  大域 Yoneda 評価・両右 Kan 族の比較本体は未検証で、下記7ファイルを集約・監査から外した。
  N-1 完了（F1b の任意 coherent 余極限定理を使用）。N の部分余極限経路は打ち切り。
  N-2（γ4）は adbdbd14c・963d9e3cf で完了、再監査不要。固定 SM7・豊穣随伴の元の Hom 同型・合成互換を明示した simplicial Quillen 随伴が対象。
  N-3 の指定 Tot・hG・fiber 適用は Sp の既存定理で達成。Sp 全体の安定性の完成とは扱わない。
  F2N-3 は F1b の a7 実証拠の受け渡しだけ残す。F2N-4(a)〜(e)（冪等完備化の普遍性・安定性・compact Ind 比較）は完了。
  N-4 の Bousfield 局所化の存在は P 所有。局所置換が与えられた場合の反射までが N の保存済み範囲。
- **残り**（依存順）：
  1. F1b の a7 公開後、`IndFiniteLimitExchangeInput.exchange` へ実証拠を渡す差し替えを1コミットで保存。HTT 5.3.4、提供後の一工程。
  2. 下記7ファイルを検証・修正し、大域 Yoneda 評価と両右 Kan 族の全自然比較を閉じる。HTT 5.5.8.14〜15、数時間〜（再ビルド時間を除く暫定）。
  3. 元の左 Kan 延長の任意小 sifted 余極限保存、元の制限の本質的全射性・全関手 ∞ 圏の同値。
  4. simplicial Ind 表示、filtered／geometric realization 版、Yoneda の有限余積保存と全余極限保存判定。HTT 5.5.8.14〜15(2)(3)、2〜4 合計30〜80時間（暫定）。
- **主要宣言**（型・全一覧は Lean と各集約・監査が正本）：
  N：`quillenCfDerivedAdjunctionWithComparisons_exists`、`sigmaPresheaf_siftedPresentation`、`sigmaPresheaf_sifted_induction`、
  `sigma_exists_densityLeftKanExtension_with_recovery`、`sigmaSiftedContinuousRestriction_isFullyFaithful`、`isColimitCone_iff_fullHomCone`、
  `presheafUniverseDiagram`、`presheafHomWeightDiagram`、`sigmaUniverseInclusion_isLeftKanExtension`、
  `sigmaHomWeightFamily_isRightKanExtension`、`sigmaLiftedHomFamily_isRightKanExtension`、`sigmaHomWeightFamily_restrictionIso`、
  `sigmaLiftedHomFamily_restrictionIso`、`homWeightEvaluationFamily_liftedIso`。
  今回：`twistedHomFunctorMap`、`twistedArrowFunctorComparison_isPrecompositionEquivalence`、`homInfinityJoint_fullyFaithfulIso`、
  `yonedaInfinityMap_fullyFaithfulRestrictionIso`、`leftKanReflRestrictionIso`、`rightKanReflRestrictionIso`、
  `isColimitCone_iff_restrict_mono_precomposition`、`exists_coconeExtension_of_mono_precomposition`、`mapUliftCocone_isColimit_of_quasicategoryShapes`。
  F2.Compact：`indYoneda_isKappaCompact`、`IsKappaCompact.retract_of_colimit`、`compactIndEquivalence`、`compactIndOmegaEquivalence`。
  F2.Idempotent：`IsIdempotentCompletion.pre_isQCatEquivalence`、`IsIdempotentCompletion.isStable`、`idem_isStable`。
- **依存と提供**：F1・F1B・F2/Ind・F2 集約・P（`F2/Presentable/`）は読み取り専用。`infinity-core-F2.md` も変更しない。
  accessible／presentable 定義は P の公開宣言を待つか入力にする。局所化の存在は P の担当。
  N 所有は `HomotopyLimits/`・既存 N 集約／監査、F2/Compact・F2/Idempotent と各独立集約／監査、本 N 節だけ。README は規約だけ。
- **未コミット**：以下はすべて `SerrePositivity/InfinityCategories/HomotopyLimits/` の `.lean`。未検証の作業中ファイルとして保持し、集約・監査には接続しない。
  `YonedaHomWeightColimits`：元の Yoneda Hom 係数関手の小 coherent 余極限保存、未検証。
  `PresheafElementsLeftKan`：小さい元の圏と全前層の左 Kan 添字・密度全余錐の比較、未検証。
  `PresheafDensityLeftKan`：全前層密度から左 Kan 条件を導く証明、未検証。最後に局所証拠 hcan を明示する形へ整理。
  `YonedaWeightLeftKan`：両関手の左 Kan 条件・制限同型・`yonedaHomWeightDiagram_universeIso`、未検証。
  `YonedaWeightFamilyComparison`：全係数への制限・転置による `yonedaHomWeightFamily_evaluationIso`、未検証。
  `SigmaHomWeightComparison`：両右 Kan 族の制限比較と `sigmaHomWeightFamily_liftedIso`、未検証。
  `PresheafUniverseArbitraryColimits`：検証済みの形状還元を前層宇宙変更へ適用、未検証。
- **既知の問題**：R の F1/PullbackFiber 一時変更は取消済み。所有 import 閉包に他レーン未保存変更がないことを確認して保存する。
  旧未検証対象 session93517 は停止準備で終了コード143にして終了。重複実行しない。新しいチャットで未検証対象を改めてビルドする。
  停止区切りの7対象4272 jobs、N 集約8634 jobs、全5529宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理なし。監査時の所有 import 閉包4990ファイルの SHA は不変。
  compact 独立集約7354 jobs・273宣言、冪等完備化独立集約6793 jobs・609宣言の既存監査は終了コード0、標準三公理のみ。
  `Inputs/Homotopy/KanQuillen.lean` は禁止 import。主経路に `ModelCategory SSet` を仮定しない。新しい sorry・公理・資源上限引き上げ・警告抑制は禁止。
  元の全図式・指定単位・全パラメータ自然性を保持し、点ごとの同値・未証明の存在入力で完成扱いしない。規約は `foundations.md` §8。
- **次の一手**：新しいチャットでは foundations.md §8 と本節を読む。N-2 を再監査せず、P-1 g を再開する。
  最初に `lake build SerrePositivity.InfinityCategories.HomotopyLimits.SigmaHomWeightComparison SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseArbitraryColimits` を実行し、上記7ファイルを検証・修正。
  両対象が通ってから集約・監査へ接続し、N 集約ビルド→全公理監査→所有分だけ保存。未検証のまま `/tmp/n-faithful-density-prepare.py` を実行して再接続しない。
  その後、元の任意小 sifted 図式の指定余錐像の保存へ進む。元の P_Σ 包含の余極限保存と前層宇宙変更の形状還元を使い、全 Hom 比較で延長の保存性を判定する。
  原典：[HTT §5.1.4・§5.3・5.5.8.14〜15](https://www.math.ias.edu/~lurie/papers/HTT.pdf)、[HA 1.1.3.7](https://www.math.ias.edu/~lurie/papers/HA.pdf)（既に本文照合済み）。

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
  単位則・全置換の等変性・代数射の後合成による全演算の保存を検証済み。
  `convolutionAction_comp` で全位置の部分合成則を閉じ、`convolutionAlgebra` を構成。
  前合成・後合成を代数射と `convolutionFunctor`・`convolutionPreNat` へ束ねた。
  `unitCoalgebra ε` は任意の augmentation の単位余代数。`convolutionUnitNatIso` は
  Hom(単位,B) ≅ B を自然な P 代数同型にする。区間の端点・収縮も余代数射に束ねた。
  `prepathAlgebra` は全代数の自己関手と自然な定数・両端点評価を持ち、底の既存の射と厳密に一致。
  `evaluationPair_projectiveFibration` は底の二端点評価の対が射影 fibration であることを示す。
  `constant_quasiIso` と `evaluation_quasiIso` は任意の値域で定数射・両評価の底の擬同型性を示す。
  単位の cofibrancy、端点の鎖ホモトピー逆、符号付き Hom 前合成の移送から導出済み。
  `Algebra.binaryProductIsLimit`・`terminalAlgebraIsTerminal` で積・終対象を底の複体に構成。
  `pathAlgebra` は全代数の good path object。忘却の逆像の弱同値・fibration は局所選択。
  `fibrations_llp_quasiIso` は retraction と逆合成の path から底の擬同型性を示す。
  自由像の `freeGeneratingTrivialCofibrations_cell_acyclicity` は任意の始域で成立。
  一般の極限余極限・自由像の小対象性・転送定理の適用は未完成。
  E2a-3 の工程 (2) の転送と工程 (3)・(4)、E2a-4・5、E2b・G1′ は未完成。
  現在地のコードと検証は本節と同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. 代数の積と終対象を底で構成し、忘却関手との比較から good functorial path object を完成。
     続いてこの path object から底のホモトピー同値性を示し、
     小対象性・一般の極限余極限と転送の適用を閉じる。J-cell acyclicity は構成済み。
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
  `SerrePositivity.EInfinity.Operad.Hopf`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.hopf`、
  `SerrePositivity.EInfinity.Operad.Coalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraHom`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict`、
  `SerrePositivity.EInfinity.Operad.convolutionAlgebra`、
  `SerrePositivity.EInfinity.Operad.convolutionFunctor`、
  `SerrePositivity.EInfinity.Operad.convolutionPreNat`、
  `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat`、
  `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso`、
  `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono`、
  `SerrePositivity.EInfinity.homPrecompose_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com、
  E の Hopf 構造、余代数区間の界面、全代数の good path object と J-cell acyclicity。
  Alg_E のモデル構造・右 Quillen U・CAlg は未提供。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：対象ビルド成功（2778 jobs）、公理監査成功（5600 宣言、標準 3 公理のみ）。
  新規 sorry・追加公理・名前衝突はなく、572 モジュールの import 閉包に他レーンの未コミット依存はない。
  今回の宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：工程 (2) の一般の極限余極限と自由像の小対象性を構成する。
  極限は `Algebra.ofJointlyMonicActions` と底の極限錐を使い、忘却が極限を作ることを示す。
  余極限は自由・忘却随伴の代数的表示、filtered 余極限とテンソル冪・coinvariant の保存を使う。
  自由像の I・J の小対象性を得て、`Transfer.Right.rightTransfer` へ
  `freeGeneratingTrivialCofibrations_cell_acyclicity` を渡す。TR・具体区間には未着手。

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
