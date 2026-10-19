# K-S• → K-基盤 1・2：∞-S• と局所化不変量

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-S• → K-基盤。L1c〜f の後、L3 は非連結 K を BGT (a) のみで（暫定 (b) は使わない）、続けて局所化不変量・Tamme・Land–Tamme（K-基盤 1・2）。

## 引き継ぎ（2026-10-19）

### 現在地
- K-L1（∞-S• 構成、連結 K）。L1a・L1b 完了。L1c・L1d 進行中、L1e–f 未完了。後続は L3・K-基盤 1・2（v2 の担当範囲）。
- 全 gapped S• と第一行制限そのものの trivial Kan fibration を証明済み。core・対角実現・Kan 置換・Ω、反復 S の段と単射な構造射への置換、零方向の境界比較を構成済み。
- Ω から既存の path homotopy fiber への全基点 π_* 同型は証明済み。直前の S 実現との比較は未証明。
- raw ρ の cofiber・gapped 性と、同じ C 内の選択を保つ `mcCarthyRho` を構成済み。面・退化、時刻零、subobject・quotient の strict 回収を証明済み。
- McCarthy の ρ・θ の二つの実ホモトピーと厳密な切断から、全 C 内の `cofiberLeftFiberQuotient_localized_isIso` を証明済み。θ の可変時刻の gapped 性は点ごとの可逆性で保証する。
- strict 左 fiber の二重単体解消と augmentation の局所化同型、反対圏のラベル付き射列による余積表示、対象ごとの局所化同型を解消の対角へ移す定理を証明済み。
- `simplicialProductQuillenA` を追加仮定なしで証明済み。恒等射の単体 fiber と固定係数の積を使い、元の射対との厳密な可換性も照合した。
- `objectSAdditivityMap_localized_isIso`、`coreSAdditivityMap_localized_isIso` を証明済み。同じ C 内の全 cofiber 図式の subobject・quotient を対象とする。相対版の単回 object/core 加法性も証明済み。相対版の全正有限反復と、両端を保つ完全関手に関する自然性も証明済み。
- `sCofiberIso`：S_n(cofiber C) ≅ cofiber(S_n C) の厳密な同型を証明済み。零角と押し出しを全 Ar 成分で判定し、全 gapped・全 cofiber の選択を保った二回の転置で逆律を得た。
- `sCofiberStableIso` は完全関手としての同型で、全ての角・subobject・quotient の評価と厳密に可換。
- `multiRealizationAdditivityMap_localized_isIso`：全ての正の有限反復 core S• 実現の加法性を証明済み。単回の座標同型を基底に、S/cofiber 交換・行ごとの加法性・対角・既存の自然な反復座標同型で帰納した。r=0 は主張しない。
- `cofiberEndofunctor` と各角の自然変換を構成し、加法性を完全関手について自然な `multiRealizationAdditivityLocalizedIso` に束ねた。S₂ の元の中央四角形の二つの区間への射対も正の反復実現で局所化同型。
- `ClosedStablePredicate` と `closedSubcategory_isStable`：零対象・押し出し・引き戻しに閉じた replete な頂点条件から、全部分圏の安定性と包含の完全性を証明済み。部分圏の安定性を入力の仮定には置いていない。
- `relativeCofiberStableModel`：評価による逆像条件の交わりとして相対 E(A,C,B) を構成済み。subobject・quotient は A/B への完全関手で、元の評価との包含後の厳密な等号を証明済み。相対 object/core 加法性への入力として接続済み。
- 相対左 fiber 内の切断・ρ・θ と両端を構成済み。ρ は相対 quotient を厳密に固定、θ は replete 性で B 所属を保つ。`relativeCofiberLeftFiberQuotient_localized_isIso` を二ホモトピーから証明済み。
- `relativeObjectSAdditivityMap_localized_isIso`・`relativeCoreSAdditivityMap_localized_isIso`：相対 Quillen A と自然な object/core 比較による単回加法性を証明済み。
- `sClosedStableIso`：S_n A を全 Ar 成分が A に入る S_n C の全部分圏と、全高次単体を保つ完全関手の同型で比較済み。
- `sRelativeCofiberStableIso`：S_n E(A,C,B) と E(S_n A,S_n C,S_n B) の交換同型、両評価との厳密な可換性を証明済み。相対の各 S_n 行、全正有限反復実現の元の射対の加法性まで接続済み。
- `RelativeStableModel`・`relativeCofiberFunctor`：両端を保つ完全関手の相対図式への作用と厳密な二評価の自然性を構成済み。`relativeMultiRealizationAdditivityLocalizedIso` は全正反復の元の射対を成分とする自然同型。
- `cutStableComparison`：任意の切断位置 k で S_n C 内の実際の cofiber 四角形への完全関手を構成。各角は min・恒等・定数 k・max による制限と全高次単体で厳密に一致し、中央評価は恒等関手を回収する。
- `arCutSquareMap_naturality`：切断位置も写す任意の単調写像（面・退化を含む）で添字の全単体の切断四角形が厳密に可換。正の反復実現後の二分割 Segal 同値も証明済み。
- `cutLeftSupport`・`cutRightSupport`：反対側の全区間成分の零性から閉じた安定部分圏を構成。切断の両端の所属、`cutRelativeComparison` の完全性と中央評価との厳密な切断を証明済み。
- `cutLeftIntervalEquivalence`・`cutRightIntervalEquivalence`：左右の支持部分圏と S_k C・S_(n−k) C の実際の同値を、完全な制限・延長と coherent な逆同型で構成済み。相対 E の中央評価とのもう一方の逆同型も `cutRelativeMiddle_comparisonIso` で証明済み。
- `cutRelativeEquivalence`：相対 E と S_n C の実際の同値を構成済み。二重 cofiber 格子の零番目の行・列の商を支持条件で消し、入力族の同型を射影の自明ファイブレーションと包含の充満忠実性で反映した。`cutRelativeSegalPair` は任意の実現関手の下で元の区間評価の射対と厳密に可換。
- `cutSegalMap_localized_isIso`：任意の切断位置の元の二区間制限が全正有限反復実現で局所化同型。完全な逆データの同値保存を各 S_n・対角で帰納し、相対加法性と厳密な射対の式を合成した。`cutSegalLocalizedIso` は完全関手について自然で、成分は元の Segal 射の像。
- `edgeSegalMap_localized_isIso`：全連続辺への元の評価を n 個の S₁ の積へ束ね、正の全反復実現で局所化同型を証明済み。射影の式と最初の辺での厳密な分解式を含む。
- `iteratedPathBoundary_headPreserving_homotopyPullback`：先頭頂点を保つ全単体作用素の経路境界の自然性四角形は homotopy pullback。元の二区間評価による `pathHeadSegalMap` で標準積四角形へ移した。先頭を飛ばす面は未証明。

### 残り（依存順、原典番号と時間見積もり）
- 以下は再開後の実装作業時間の粗い目安。未形式化の難所で増えるため納期ではない。
- 面の homotopy pullback 条件、S 実現と既存の homotopy fiber の比較、構造射との照合：HTT 5.1.2.2、
  L11 §11・Fiore–Pieper Theorem 4.35、16–40時間。L2 の実現定理に面条件を追加仮定で渡さない。
- 正の Ω 条件・delooping・負次数消滅と BF 連結スペクトル関手：BGT Definition 7.1、経路正本 §10-5、
  §13 決定2・5・12、L9c の BF 界面、16–48時間。
- π₀ K と TriangulatedK0(h C) の対象類を保つ自然同型：経路正本 §5 K0 界面欄6、L11 型草案 S1、16–40時間。
- dg 関手性・Morita 不変性：経路正本 §4 D1・§5 K1b、U16・A3e、8–24時間（依存 API の照合を含む）。
- L3・K-基盤 1・2 は §6・7 の依存順に続行。非連結化は F2-lite の Ind を待つ。

### 主要宣言（名前のみ）
- `sConstruction`、`simplicialSConstruction`、`firstRowRestriction_trivialKanFibration`、`firstRowEquivalence`
- `StableModel`、`PreservesCofiberData`、`sEndofunctor`、`multiRealizationFunctor`
- `kSpace`、`kKanSequence`、`monicKKanSequence`、`monicKKanSequenceProjection_piIsomorphism`
- `iteratedPathHomotopyFiber`、`iteratedPathLoopComparison_piIsomorphism`
- `objectToCoreSRealization_localized_isIso`、`objectCoreRowIso`、`cofiberStableSubobject`、`cofiberStableQuotient`
- `mcCarthyLambdaMu`、`mcCarthyLambdaNu`、`mcCarthySpan`、`mcCarthyRhoRaw_pre`、`mcCarthyRhoRaw_timeZero`
- `mcCarthyRhoRaw_isCofiber`、`mcCarthyRhoRaw_isGapped`、`mcCarthyRho`、`mcCarthyRho_isGapped`
- `mcCarthyRho_ι`、`mcCarthyRho_pre`、`mcCarthyRho_timeZero`、`pointwiseDiagramPushoutApex_postcompIso`
- `mcCarthyRho_source`、`mcCarthyRho_quotient`、`mcCarthyRhoFiberMap`、`mcCarthyRhoFiberHomotopy`
- `mcCarthyRhoFiberMap_quotient`、`mcCarthyRhoTerminal_parameter`、`mcCarthyRhoTerminal_source`
- `fixedSourceArrowsTarget_trivialKanFibration`、`zeroSourceThetaHomotopy`、`mcCarthyThetaFiberHomotopy`
- `mcCarthyFiber_retraction_localized`、`cofiberLeftFiberQuotient_localized_isIso`
- `simplexFiberDiagram`、`elementsResolution`、`fiberResolutionAugmentation_localized_isIso`
- `oppositeLabelledChainEquiv`、`elementsResolutionRowIso`、`elementsResolutionMap_diagonal_localized_isIso`
- `tensorElementsResolutionIso`、`identitySimplexFiberIso`、`simplicialProductQuillenA`
- `objectSAdditivityMap_localized_isIso`、`objectCoreAdditivity_commute`、`coreSAdditivityMap_localized_isIso`
- `sCofiberIso`、`sCofiberStableIso`、`sCofiberStableIso_subobject`、`sCofiberStableIso_quotient`
- `coreSRowAdditivityMap_localized_isIso`、`objectSRowAdditivityMap_localized_isIso`
- `multiRealizationAdditivityMap_localized_isIso`、`multiRealizationAdditivityLocalizedIso`
- `cofiberEndofunctor`、`cofiberEvaluationNat`、`sTwoRealizationAdditivityMap_localized_isIso`
- `ClosedStablePredicate`、`closedSubcategory_isStable`、`closedStableInclusion`
- `relativeCofiberStableModel`、`relativeCofiberSubobject`、`relativeCofiberQuotient`
- `objectSClosedIso`、`relativeCofiberLeftFiberLift`、`relativeMcCarthyRhoHomotopy`、`relativeMcCarthyThetaHomotopy`
- `relativeCofiberLeftFiberQuotient_localized_isIso`、`relativeCoreSAdditivityMap_localized_isIso`
- `sClosedStableIso`、`sRelativeCofiberStableIso`、`relativeMultiRealizationAdditivityLocalizedIso`、`cutStableComparison`、`cutRelativeEquivalence`、`cutRelativeSegalPair`、`cutLeftIntervalEquivalence`、`cutRightIntervalEquivalence`、`StableModelEquivalence`、`multiRealization_map_localized_isIso_of_equivalence`、`cutSegalMap_localized_isIso`、`cutSegalLocalizedIso`、`edgeSegalMap_localized_isIso`、`edgeSegalMap_projection`、`pathHeadSegalMap`、`iteratedPathBoundary_headPreserving_homotopyPullback`

### 依存と提供
- 所有は `SerrePositivity/KST/SConstruction/`、集約、監査スクリプト、本計画。namespace は同名。
- 読取専用：Core（F0、関手圏の点ごとの極限等）、Stable（α-S）、F1/F1B（core・充満包含）、
  Spectra（L9）、Comparison（L2）、HomotopicalAlgebra（具体的 Kan 置換・局所化・対角）。
- 提供：全 gapped S• と第一行の完全な比較、安定な入力の完全関手の圏、object/core 実現比較、ρ の cofiber・gapped 性、左 fiber 内の二ホモトピー、quotient 射の局所化同型、単体積版 Quillen A、全 cofiber 図式の object/core 単回実現の加法性、S/cofiber の厳密な交換同型、正の全有限反復実現の自然な加法性、S₂ の二区間への分解、閉じた全部分圏と相対 E(A,C,B) の安定性・完全な評価、相対 object/core 単回実現と全正有限反復 core S• 実現の加法性、S_n と全部分圏・相対図式の厳密な交換同型、相対入力に関する全正反復加法性の自然同型、切断の左右支持部分圏と短い区間の S 構成の実際の同値、左右支持の相対 E と S_n C の実際の同値、元の Segal 射対の厳密な比較式、全正有限反復実現による完全な同値の保存、任意の切断位置の元の Segal 射の自然な局所化同型、全連続辺への Segal 同値、先頭を保つ単体作用素の経路境界の homotopy pullback。
- K スペクトル・TriangulatedK0 比較・Morita 不変性は未提供。条件付きの段を完成品に数えない。
- 将来接続：L9 の Ω・π_*・BF、既存の実現比較（L2 は Auxiliary として凍結）、α-S の h C の三角構造、N の dg nerve、D の Perf。

### 未コミット
- 担当分は検証済み保存単位（新規5モジュール、集約、監査スクリプト、本計画）にコミット。未保存の担当差分なし。
- 他レーンの作業中の差分・未追跡ファイルは触れていない。

### 既知の問題
- 対象ビルド3590 jobs、公理監査2328宣言が成功。全体 lake build は今回再実行していない。
- 名前衝突の未解決例なし。Core・Stable・F1 等の公開名・型は本レーンで変更していない。
- SConstruction 内の明示的な `[ModelCategory SSet]` 引数は検索で見つからず。HA の具体的 instance と
  anodyne 局所化を利用。推移的依存を含む model instance 全体の棚卸しは別途必要。
- 2328宣言の監査は追加公理・sorry を検出しない状態。許可は propext・Classical.choice・Quot.sound のみ。
- raw ρ の型は Ar→Fun(正方形,C)。cofiber 値への持ち上げ・gapped 性・各角の strict 回収・左 fiber 条件は証明済み。二つの実ホモトピーと quotient 射の局所化同型まで証明済み。
- cofiber 図式の圏で任意に選んだ押し出しでは、subobject・quotient の strict な回収を結論できない。
- homotopy fiber 比較を既存の構造射と形式的に合成するだけでは正の Ω 条件の証明にならない。
- C×C と S₂C の ∞ 圏の同値は主張しない。加法性は S• と実現の後の定理。
- Git は既存の gc.log と unreachable loose objects の警告を出す。整理操作はしていない。

### 次の一手
- 先頭を飛ばす面、とくに δ₀ の経路境界の自然性四角形の homotopy pullback を証明する。先頭を保つ作用素（σ₀ を含む）は今回の定理を使う。正の実現の連結性は `multiDiagonalCoreSConstruction_isConnected` にある。δ₀ の可逆な fiber 輸送、または退化の既証の面四角形からの検出を、具体的な homotopy fiber の比較で証明する。未証明の全ての面条件を L2 に渡さない。
- 全ての面条件が揃ったら既存の実現比較へ接続し、S 実現と homotopy fiber・元の構造射との比較、正の Ω 条件・BF 連結 K スペクトルへ進む。これらと π₀・dg・L3・K-基盤は未完。
- 検証は対象ビルドと `lake env lean scripts/audit_kst_s_construction.lean`。他レーンは編集しない。

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md` §8 と経路正本 §13 決定16を優先。非連結化は BGT (a) のみ。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c | KSpace.lean | 各段の core、対角実現・Kan 置換・Ω、反復 S• と L9 BF スペクトルへの接続 |
| L1d | Additivity.lean | McCarthy 型ホモトピーによる実現後の加法性 |
| L1e | PiZero.lean | π₀ K(C) ≃+ TriangulatedK0(h C)、対象類と自然性 |
| L1f | DGApplication.lean | K(N_dg(Perf_dg D))、dg 関手性、Morita 不変性 |
| L3 | §6 | fibration 定理、BGT (a) の非連結化、局所化不変量 |
| K-基盤 2 | §7 | Tamme の分裂、dg 増強流の ⊙ と Land–Tamme 主定理 |

## 4. 設計と実装前の文言

### Ar と gapped

Ar[n] は Fin(n+1) の対 (i,j), i≤j の成分ごとの順序の圏。
単調写像 θ:[m]→[n] は (i,j)↦(θi,θj) を誘導する。
図式圏は ihom(N Ar[n],C)。gapped は全対角 F(i,i) が零対象であり、
i≤j≤k≤l に対する F(i,k)→F(i,l), F(j,k)→F(j,l) の全四角が pushout となる条件。
S_n はこの頂点条件による充満部分単体集合。順序写像による前合成は条件を保つため、
選択を含まず Δᵒᵖ 上の単体的対象を与える。退化する四角にも同じ pushout 条件を課す。

### §10-13：gapped と第一行

原典の結論は Gap([n],C)→Fun(Δ^{1,…,n},C) の ∞ 圏の同値である。
これだけから literal な trivial Kan fibration と結論しない。
要求された元の制限写像について、有限個の相対 cocartesian completion を積み上げ、
零対象と余極限錐の相対境界持ち上げ性から全境界に対する RLP を証明する。
n=0 は零対象の空間として別処理する。全 gapped 図式を保ち、第一行の選択模型に置換しない。
不足する相対拡張補題は本レーン内で証明する。設計変更が必要なら実装前に提案する。
Ar[n] と正方形の積から (0,i),(0,j),(i,i),(i,j) への自然な添字写像を用い、
gapped 図式の全 cofiber 四角形を一つの族として取り出す。
その族は右上角の評価で元の図式を厳密に回収するため、境界上の既存データを保持できる。
相対 cofiber 補完をこの Ar[n] パラメーターに適用する際は、第一行と対角での条件を同時に固定する。
得られる右上角の図式の全四角形が押し出しとなることは、余極限の普遍性と押し出しの貼り合わせから
別に証明する。単に各区間に cofiber を持つことだけで gapped 条件を結論しない。
点ごとの余極限・押し出しを関手 ∞ 圏へ移す向きは、相対始点境界充填と内部 Hom の交換で証明する。
正次元のパラメーター境界では全頂点が指定されているため、境界を厳密に保つ補完の gapped 性は
全部分複体の頂点条件から回収できる。零次元の gapped 性および出力の第一行の厳密な回収は別条件として残す。

### §10-11：加法性

E(A,C,B) の cofiber 列から subobject・quotient への射について、
|core S•E|→|core S•A|×|core S•B| が同値となることを証明する。
E≃A×B という ∞ 圏レベルの誤った主張にはしない。
Fiore–Pieper の McCarthy 型の経路を用い、普遍的 cocartesian completion の制限自明
ファイブレーションでパラメータ付き pushout を選び、単体ホモトピー、単体積版 Quillen A、
対角実現、object/core 比較を証明する。Waldhausen の元の証明からの経路変更を明記する。

### §10-12：最小 fibration 定理（後続 L3 の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と BGT §9 の非連結化を経由する。L11 では ∞ 版全体は未検証である。
今回の L1a–f の成果としてこの定理を完成扱いしない。

### K と界面

L9 の基点・Ω・π_* の座標に従う。BF 模型は単射 ΣX_n→X_(n+1) と、随伴の全基点 π_* 同型。
厳密な Ω 同型を要求しない。未着 API は明示的な入力として隔離し、証明済みの構成と区別する。
π₀ は一般 dg 圏の H⁰D でなく、小さい Perf の H⁰ の TriangulatedK0 と比較する。
S4 未着時は cofiber 列の像が distinguished triangle になる仮定を明記する。
相対 K は L9 のスペクトル fiber を優先し、次数ごとの kernel/cokernel から復元しない。
Kₙ の境界・比較同型は自然性と対象類の式を含む。宇宙は S1.1 に従い小さい模型にそろえる。

## 5. 検証・保存

各保存単位で `lake build SerrePositivity.KST.SConstruction` と
`lake env lean scripts/audit_kst_s_construction.lean` を実行する。
公開宣言を #check / #print axioms で監査し、許可するのは propext、Classical.choice、Quot.sound のみ。
全体ビルドは工程の区切りで行う。自分の import 閉包外の並行作業の失敗は記録して続ける。
自分の検証済みファイルだけを保存し、経緯はコミットメッセージに記す。

## 6. L3・K-基盤 1（L1c〜f の後）

- **担当境界**：K の fibration・局所化定理は本レーン。Drinfeld 商の dg nerve と ∞ 圏的 Verdier 商の比較・Verdier 列の供給は D レーン β3。H⁰ の普遍性だけで mapping 空間の比較を代用しない。
- **Ind を待つ間**：小さい安定 ∞ 圏の完全関手を基礎に、冪等完備性の述語、Cat^perf の対象・射、Verdier 列、半直交分解、Sp 値の局所化不変量の定義と分裂列の帰結を整える。Cat^perf の ∞ 圏としての構成・極限は α2b の Cat_∞ に接続する。冪等完備化の存在を未証明の仮定で完成扱いしない。
- **fibration**：W の2-out-of-3・pushout・extension 安定性、S• の相対構成と加法性から連結版を証明し、必要な cofinality を明示する（Waldhausen 1985 §1.6、BGT §7–9、80–160時間）。β3 の商との比較は到着後に接続する。
- **非連結化は BGT (a) のみ**：N の Ind・κ-compact・冪等完備化と α2b の F2-lite を待ち、BGT §9 の suspension と反復 colimit により定義する（80–160時間）。Schlichting 暫定版 (b)・Bass による定義は導入しない。
- **完了条件**：冪等完備 Verdier 列を fiber 列に送る非連結 K、Morita 不変性、filtered 余極限との可換、連結 K との比較を証明する。値域の ∞ 圏 Sp は Sp レーンの供給を使い、局所化不変量の構造体にモデル圏 instance を要求しない（BGT §8–9、40–100時間）。

## 7. K-基盤 2（dg 増強流）

- **Tamme**：完全関手の lax pullback、標準包含・射影、半直交分解と分裂列を構成し、任意の局所化不変量で分裂を証明する（Tamme 2018 §1、60–120時間）。Cat_∞ の極限は α2b、dg gluing との比較は D の β4 を読み取り専用で使う。
- **Land–Tamme の ⊙**：dg 代数の Milnor 四角形から Perf の lax pullback と対角像の Verdier 商を作り、生成元の dg 自己準同型代数として A′ ⊙_A B を構成する。D の β3・β4・β5（非可換 D(A)・相対テンソル・Morita）を使う（Land–Tamme 2019 §1–2、100–200時間）。E₁ 環スペクトル・HA §2–4 の構成には進まない。
- **主定理**：Tamme の分裂と上の Verdier 列から、B′ を ⊙ に置き換えた四角形を全ての局所化不変量が引き戻しに送ると証明する。dg の対象供給と ∞ 圏の形式的議論を接続する（Land–Tamme §2、60–120時間）。
- **pro 版**：Tor の pro 消滅から ⊙→B′ の比較を経て pro 切除へ。Tor の環論は L7 の入力を待つ（Land–Tamme §3、80–160時間）。第 II 段のスキーム応用は基盤 I-a・I-b が閉じるまで起動しない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L1-s-construction-log.md](archive/L1-s-construction-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
