# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v4（2026-10-26）**：K-7 は **K-B3 レーン**が引き継ぐ。本ファイルが K-7 の正本。所有は `KST/NonConnective/`・同名集約・専用監査・本計画。K-6 は K-B（L3）、Fibration・SConstruction・Spectra・InfinityCategories は読み取り専用。I・P・Z と全入力作用の実供給は D 正本を消費する。第 I 段の完成条件は I-4（K-6・K-7・局所化不変量登録）。

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-26、K-B3 再開）

### 引継元と到着入力
- 旧 K-B の最終実装：`71a031889`。D-8 の同じ実 I・P・Z の反復で、全四角形同型と標準単体商比較から各段の一回の S• fibration を導き、元の固定 K・SOA K と同じ候補の非負次数 π 比較へ接続した。両比較と共終性は条件付き。
- `DGSuspensionSuppliedBFTailComparison.lean` は未追跡ではなく `f5759f875` で保存済み。実逐次比較に対する元の全整数末尾表示の自然性・逆座標式を公開。`28032a24b` は十分後の段の π 単射・全射・完全性と移動後非負範囲から同じ候補への判定を保存した。
- D-8 の実 I・P・Z は `12d3aa16e` で消費済み。`DGSuspensionNativeActionInput` の全四角形族・Morita 比較・P 包含の全 native Hom 自然性は未供給。D の DGSuspensionNativeSquareModel は cb125356d で型のみ公開。b21e4906c の parameterExtension_postcomposition・_heq を同じ零角の選択収縮へ消費。本体と実評価 Morita・P 包含の全 native Hom 自然性は未供給で、K-7 c4 は明示入力を保持する。
- 残りの順序：K-6 の canonical c4・実共終性を代入済みの同じ実 BF 列で c5 を消費 → K-7 c4 の全入力作用・c5 の実自然性と d3・d4 の照合 → e の非連結化後の Verdier fiber・Morita・filtered 余極限 → f の固定 dg 相対局所化登録。固定 S・ν・K と採用済み入力境界は維持。
- 他レーンへの未送付の供給依頼・設計提案：なし。F1 外延性・Sp 有限線型図式比較は既依頼。K-S• 共終性は到着済み。新しい仕様変更は求めていない。
- 旧 K-B 停止時の未追跡ファイル：なし。当時の全 Lean 作業は保存済み。NonConnective 集約 15,793 ジョブ、専用監査 191 モジュール・2,140 宣言（標準三公理のみ）成功。
- 到着入力：`Cofinality.kSpectrumMap_cofinality`（7397052d8、指定完備化証拠のみ）と `SingleRelativeComparison.ofFirstRowSimplices`（8cd255949）を消費する。旧明示引数の入口は互換性のため保持し、新入口 `DGSuspensionThomasonSequence` では共終性を実証明で放電する。

### 現在地
- 今回の所有集約ビルドは 16,310 ジョブで成功。専用監査は 209 モジュール・2,369 宣言、標準三公理のみ、ModelCategory 型検査を含め成功。所有外は未編集。
- c5 の対象別定義：DGNonconnectiveK で dgNonconnectiveK・各実懸垂段・元の構造辺と隣接射・実 Sp 余錐と IsColimitCone・元の全整数 π 群余極限を公開。D-8 の同じ固定 κ と実 I・P・Z を使用し、K-7 c4・K-6 d・Sp 安定性の追加仮定なし。全入力上の関手は未完成。
- 到着 K-B 7bbc95274：dgKappaCanonicalSuspensionStructureMap_nonnegative と実際の公開名 dgKappaCanonicalSuspensionStructureMap_eq を消費。DGNonconnectiveKConnectiveComparison は c5 の標準単体商比較だけに条件付きで、同じ元の全一単体・隣接安定化・連結比較・全整数末尾表示を接続。K-6 c4 の全四角形比較と K-7 c4 の全入力作用を区別する。
- d4：DGKInputCompactNativeChoiceCoherence は I-2 e の同じ無条件生成同値から任意の逆射選択を全 native Hom 族上で比較し、恒等・三選択の合成・任意族への再制限・元の ν/Yoneda 全族への指定比較の自然性を証明。非可算 κ-cone と同じ Indω の比較、全入力高次合成と構造辺 β の自然性は別工程。
- d4 の Indω 全体への延長：DGKInputIndNativeFamily は元の全 native Hom 族を、同じ Yoneda 制限同値の実逆で filtered 余極限保存関手へ一括延長する。元の全 Yoneda 族との比較・任意全高次パラメータへの再制限等式を保持。DGKInputIndExtension は同じ制限の充満忠実性で保存延長を比較し、DGKInputIndEquivalence は指定 ν 同値を元の Indω 間の実同値へ延長する。
- d4・e の実射照合：DGKInputIndMorita は全 native 族から回収した元の dg 射が固定 ν 射の指定 Ind 延長と厳密一致すること、元の Morita 射の Ind 作用が実同値であることを証明。DGKInputIndNativeComposition は同じ実射の恒等・二項合成比較、DGKInputIndCompactNaturality は元の compact 包含との全 native Hom 自然性と任意族の再制限等式を供給。全高次合成整合・非可算 κ-cone 比較・各懸垂段の作用・構造辺 β の自然性・最終 K^{nc} の Morita/filtered 保存の完成は主張しない。
- 到着 K-B a8da9d086：DGNonconnectiveKFibrationTail は Relative.k6FibrationOfC5 の d を同じ D-8 実 I の全反復へ代入する。hc5 は元の標準単体商比較の型を明示引数に保持し、各段の .quotient_edge で元の BF 商射と実 fiber の右辺を厳密照合する。同じ実余錐の末尾脚と固定 K の復号比較により、任意整数 j と十分後の n に対して元の K^{nc} の π_j を同じ実 BF fiber の π_{j+n} と比較し、元の実余錐の脚を通ると同じ段の K-6 d の比較を回収する。同じ実辺を表す BF 段別射も構成し、群同型の順方向と π 作用の一致・非負次数全単射性を保持する。fiber の逐次作用・余極限性や一般 Verdier fiber 性は未完。
- e：DGKappaStrictQuotientComparison は対象宇宙 u+1 で strict 商辺と固定 ν の Perf 商辺の Yoneda 自然性、元の strict 入力・ν・K への厳密下降四角形と下降 K 射の π 同型を接続。D の全作用や固定 ν の Verdier 認証は要求しない。一般 v への拡張は K-S• 正本の宇宙境界に従う。
- e：DGNonconnectiveKMorita は指定実逐次比較が各実懸垂段の元の Morita K 射と可換なら、同じ非連結 K 比較の全整数 π 同型・実辺の可逆性を証明。SequentialCandidatePiColimitExchange は元の実注入を保ち、外側余錐の段別 π 余極限から同じ候補の π 余極限を得る。初期 Morita 射からの全段保存・実逐次作用、dg filtered 図式の段別保存と実 Sp filtered 余錐は未供給で、Morita・filtered 保存全体の完成とは数えない。
- D b21e4906c の部分供給：DGKappaNullParameterPostcomposition は元の核→懸垂の同じ選択収縮に全パラメータ・全次数の後合成延長を適用し、元の成分と商延長後の前合成作用を回収する。D-8 e 本体の存在は推論しない。
- b283c7f41 の到着入力消費は所有集約 16,061 ジョブでビルド成功、専用監査 195 モジュール・2,174 宣言で成功（標準三公理のみ、ModelCategory 型検査を含む）。所有外は未編集。
- `DGKappaThomasonCofinality` は同じ実商の正次数全単射・零次単射と完備化前 cone K 零性へ共終性を代入。`DGSuspensionThomasonSequence` は同じ実候補・実 Sp 余錐・固定 K と SOA K の連結比較・全整数末尾表示を保持する。c4・c5 は相対比較 c に保持し、D の型のみの公開から本体を推論しない。
- 工程 e：`SequentialCandidateMapThomason` は j+n>0 の末尾で正次数共終性を使い、同じ実候補比較の全整数 π 同型・実辺の可逆性を得る。`DGSuspensionThomasonComparison` は同じ反復列の native loop 座標と元の SOA 比較の逆を使ってこれを実候補へ代入する。実逐次比較 η・元の段別完備化射 f・指定座標での可換性は明示入力で、Verdier fiber・Morita・filtered 保存や e 全体の完成は主張しない。
- K-B3 再開時に二比較から同じ候補の全整数末尾表示・隣接射整合まで接続。所有集約ビルド成功（15,793 ジョブ）、専用監査成功（191 モジュール・2,143 宣言、標準三公理のみ・ModelCategory 型検査を含む）。旧入口の c4・c5・共終性は明示入力のまま。到着後の新入口は上記。
- 採用済み経路へ再開：K(TA)≃0 と連結版 fibration の元の実 fiber 比較を構造射・連結比較 d1〜d4 に使う。全段の Sp 引き戻し性は仮定しない。e の Verdier 列の Sp fiber 性と f の相対局所化登録は K^{nc} について非連結化後に証明する。
- 上流 import 閉包の復旧と両所有集約の再ビルドを確認。`DGKappaSplitPerfEvaluation` を検証し、集約・監査へ接続済み。元の全 native 関手族と同じ実四角形の全単体を、元の各 Perf ラベルの dg 作用へ照合し、同じ点ごとの零三角形を構成した。D-12 の公開判定により同じ二胞体の cofiber 普遍性を証明し、同じ cone の連結 K・固定 K の実 Sp 零頂点性まで接続済み。
- 工程 a 完了：任意の厳密な逐次 BF 列の実 Sp 余極限を K-7 内で構成。同じ `filteredOmegaSpectrum` を頂点とする `sequentialCandidateColimitCocone` の `IsColimitCone` と、実辺の全整数 π 作用・群余極限比較を接続済み。
- 工程 b の明示入力版完了：β5 の実半自由 D(D)・Perf と β3 の平坦分解後の Drinfeld 商を読み取り専用で使用。非可算正則 κ の dg 小模型を `DGKappaConeInput`、元の Perf との全関手比較を `DGKappaPerfectInput` として明示した。[未供給宣言の名前・型一覧](archive/L10-dg-kappa-inputs.md)。D-8 e（19:33、5bf80c07c）の `dgKappaPerfectInput` により P は任意の同じ I から実供給済み。D-8（2b085b584）の `dgKappaConeInput_unconditional`・`dgKappaPerfectInput_unconditional` を `DGKappaUnconditionalStageSupply` で同じ固定 κ の段供給と実反復対象へ接続済み。
- 工程 c 進行中：同じ κ と同じ供給 s を保つ反復 `dgSuspensionIteration` を構成。実 swindle を dg 関手圏の閉同型・元の native Kan Hom の実辺へ束ね、固定 `dgKInputK` の同じ二つの実 BF 自己射の全整数 π 作用の等号 `dgKappaSwindleFixedK_pi` まで接続した。同じ全 cofiber 族の完全性と三評価の実加法性を用い、同じ SOA 群比較を介して元の固定 K と連結 K の実 Sp 零頂点性を証明した。
- K-S• の既存の正反復実現の加法性から、同じ全零境界商 Kan 射対の局所化可逆性・全基点 π 同型を K-7 内で証明した。実標準軸の零関手・恒等関手の評価と群の二軸分解から一重境界商の中央項の正次数群上の加法公式を導き、元の同じ連結 BF K の全整数 π 上の加法性 `connectedKMiddle_additivity` へ移した。非負整数群と一重境界商の群の比較は元の射に自然。非連結 K の定義を一般安定入力へ拡張していない。同じ Perf 上の実分裂 cofiber 族と、その完全性・元の三評価へ接続済み。
- 同じ実二項 dg 直和の両注入・両射影を、全斉次自然変換と全 dg 関手 Hom end の実閉射に保持した。同じ Hom end 内の四合成・恒等分解を証明した。非 replete な I に実零加群そのものが入る証拠は、別の追加所属入力 `DGKappaZeroInput` として隔離し、その証拠に対する実零 dg 自己関手と閉関手圏での零対象性を構成した。I・P の型・存在を変更したり、その所属を前三角性から推論したりしない。[追加型](archive/L10-dg-kappa-inputs.md)。
- 零自己関手の各 Perf ラベルでの閉零対象性・native 零頂点性、全 native dg 関手パラメータの Perf 作用と固定関手の照合、非可逆閉射の実 Perf 自然変換、同じ注入・射影・零関手の二単体を貼った `dgKappaSplitPerfFamilySquare` まで構成。同じ上・下二胞体、四辺、全関手空間の実零角を回収し、`dgKappaSplitPerfZeroTriangle` に束ねた。各 Perf ラベルでの同じ閉注入・射影の四合成と恒等分解も接続済み。点ごとの cofiber 性・同じ全族の完全性・固定 K への加法性と swindle による実零頂点性は接続済み。
- 実 dg 加群の全 Hom end の余積普遍性から可算直和の chain map を構成し、単位・豊穣合成・射影性の保存を証明した。同じ cone 上の厳密 dg 自己関手 T と id ⊕ T を構成。swindle は入力に仮定せず、指定した閉 dg 射・両側逆・全斉次自然性・両向きの厳密自然変換と元の dg nerve 上の実関手同型まで構成した。T と id ⊕ T の native nerve は完全。
- 同じ入力の full dg cone の perfect 対象で零化する cell 分解後の実 Drinfeld 商を構成した。実商射影・安定性・β3 の実安定閉包からの Verdier 列と、固定 `PerfDGInput` への包装を保持する。元の β5 の Perf と安定閉包の同値 P は D-8 e が同じ I から構成し、その元の Perf の全頂点の零化も証明した。
- κ-compact 性は F2 の全共変 Hom による定義を使う。ordinary compact/perfect 比較では代用しない。小ささは選んだ代表系にだけ要求し、全加群圏には要求しない。可算直和の κ-compact 閉性は I の `countableClosed` に明示され、κ の記号だけから証明したとは扱わない。
- Ind I-2 e を固定 ν 値の Indω へ接続済み。交換を定理化した最終公開入口 `ind_stableCompactGeneration_unconditional`（15:21、f350dce62）を採用し、交換入力・有限全存在の追加仮定を除去した。K-B2 の f7d3f64a4 の SingleRelativeComparison を DGSuspensionRelativeComparison で消費し、同じ実構造射・実反復列の連結比較・SOA 比較の非負次数 π 同型へ接続した。旧入口は二比較と共終性を明示引数に保持し、新入口では到着した共終性を代入する。D 側の供給の仲介はコーディネータ。今回 D・Sp へ直接依頼していない。所有外のファイルは変更していない。
- NonConnective 集約・専用監査は実供給 BF 四角形・cone 零性・新 BF 構造辺と非負次数比較まで成功（191 モジュール・2140 宣言、標準三公理のみ、ModelCategory 宣言型検査を含む）。零 Perf 全族、分裂四角形の二胞体・四辺・零角、各ラベルの閉分裂関係を接続済み。点ごとの cofiber 性と同じ cone の K の実零頂点性は証明済み。採用経路の段別構造辺と連結比較は、実 fibration の非負次数比較と共終性を明示引数に取る条件付き利用側として対象ビルド成功。構造射の実供給と全入力自然性は未完。

### 残り（依存順）
1. 工程 c：構成した反復の対象別供給を、懸垂の全入力射に対する作用・整合性へ接続する。証明済みの同じ cone の連結 K の消滅を保持して、K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A) の構造射を作る（BGT Lem. 9.4・Def. 9.6、見積り未確定）。
2. 連結 K との比較と負次数の記述（BGT §9、Schlichting 2006、見積り未確定）。
3. 非連結化後の K^{nc} が Verdier 列を Sp fiber 列へ送ること、Morita 不変性、filtered 余極限との可換（K-6 と β3、BGT Thm. 9.8、Schlichting 2006 §7 Lem. 6、見積り未確定）。
4. 非連結化後の K^{nc} の Sp 相対版 `IsRelativeLocalizingInvariant` への登録（固定 dgKInputInfinity・dgKInputNu、元の dgKInputK は連結比較の始点のまま、K-5、見積り未確定）。
5. Ind の無条件安定性・compact 生成界面は接続済み。同じ非可算 κ の実 dg cone・I・P と元の全 native 作用を照合する（BGT §9.1、見積り未確定）。I・P・実零所属 Z は D 正本の同じ代表系から実供給して接続済み。全入力自然性は未完。

### 主要宣言
- `sequentialCandidateColimitCocone`、`sequentialCandidateColimitCocone_isColimit`、`sequentialCandidateColimitCocone_vertex`、`sequentialCandidatePiCoconeIsColimit`、`sequentialCandidateColimitHomotopyIso_ι`。
- `DGKappaConeInput`、`DGKappaPerfectInput`、`dgKappaConeDerivedComparison_isFullyFaithful`。
- `dgCountableSumFunctor`、`dgCountableSumHom_injection`、`dgCountableSumObj_projective`、`dgSumFamilyFunctor`。
- `dgKappaConeCountableSum`、`dgKappaSwindleSource`、`dgKappaSwindleStrictHom`、`dgKappaSwindleStrictInv`、`dgKappaSwindleComponentIso`、`dgKappaSwindleInfinityIso`、`dgKappaConeCountableSum_isExactFunctor`。
- `DGKappaSuspension`、`dgKappaSuspensionProjection`、`dgKappaSuspensionInfinity_isStable`、`dgKappaSuspension_isStableVerdierSequence`、`dgKappaSuspensionKInput`、`dgKappaSuspension_kills_perfect`。
- `DGSuspensionStageProvider`、`dgSuspensionIteration`、`dgSuspensionIterationStage`、`dgKappaSwindleClosedFunctorIso`、`dgKappaSwindleNativeInputEdge`、`dgKappaSwindleFixedK_pi`。
- `boundaryKanAdditivityMap_piIsomorphism`、`boundaryKanAdditivityGroup_injective`、`singleBoundary_constantZero`、`singleBoundaryMiddle_additivity`、`nonnegativeBoundaryEquiv_naturality`、`connectedKMiddle_additivity`。
- `dgKappaSplitHead`、`dgKappaSplitTail`、`dgKappaSplitHeadProjection`、`dgKappaSplitTailProjection`、`dgKappaSplit_decomposition`、`DGKappaZeroInput`、`dgKappaZeroFunctor_isZero`。
- `dgKappaZeroPerfAction_isZeroVertex`、`dgKappaFullPerfFamilyMap_vertex`、`dgKappaPerfClosedHomotopy`、`dgKappaSplitPerfFamilySquare`、`dgKappaZeroPerfAction_values`、`dgKappaZeroPerfFunctorVertex_isZero`、`dgKappaFullPerfZeroVertex_isZero`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供：厳密な逐次 BF 列の同じ BF 候補を頂点とする実 Sp 余極限・実辺の整数 π 比較。一般 coherent 列の整流を仮定してはいない。
- D-8 は同じ `objects := dgKappaClosedProjectiveObjects R D κ` の I 全フィールドと同じ P を供給済み。`DGKappaUnconditionalStageSupply` は非可算正則 κ の明示条件だけから全厳密 dg 段へ接続する。`DGKappaUnconditionalConeZero` は D 正本の実零加群所属を Z に代入し、同じ cone の連結 K・固定 K の実 Sp 零性と全段の実零所属を供給する。
- `DGSuspensionStageProvider` の対象別実供給は接続済み。全 native 入力射作用と整合性は未供給で、対象別の実 I・P・Z から推論しない。[宣言名と対応表](archive/L10-dg-kappa-inputs.md)。

### 公開界面の利用
- コーディネータ確認（10-24）：公開 `PresentedPerfectDGNativeLabel.lean` は読み取り専用 import が可能。`presentedPerfectDGNativeActionSimplex_label` と `presentedPerfectDGNativeAction_label_app` を利用し、全 native 分裂四角形の点ごとの評価を同じ閉ラベル作用へ照合する。供給依頼・分割は不要。禁止対象はコピーと他レーンの編集。

### 未コミット
- なし。今回の新規 7 葉・集約・専用監査・本計画は対象ビルドと公理監査を通して限定保存。所有外の未追跡ファイルは対象外。
- 保存注記：c2a7623c1 は共有 index の並行更新により K-B の Relative/All・ConnectiveFibrationTheorem・L3・audit_kst_fibration も併収した。K-B3 はこれらの内容を編集していない。コミット本文の所有ファイル限定という記述はこの点を訂正する。履歴・他レーンの内容は保持する。

### 既知の問題
- D-8 e は任意の I から P の完成した実値を供給した。`DGKappaPerfectSupply` は同じ I を保つ段入力・全段供給・実 Perf 同値・反復 BF 列へ代入し、既存の段供給の P を差し替えても元の反復 dg 対象が変わらないことを保持する。元の全高次懸垂作用を同じ全単体写像・頂点・実射・全一単体のまま移し、各段の全入力 K・native loop 族も厳密に保持する。`DGKappaPerfectSupplyComparison` は同じ実導来包含の充満忠実性から既存 P と実供給 P の全 native Perf 関手比較を戻し、元の包含同型を厳密に回収する。同じ I の P 選択比較は単位・合成則を満たす。元の厳密評価・実評価 Perf 同値・実構造射は P の選択に依存しない。`DGKappaResolvedKernelRepresentability` は同じ実評価 Morita 核と実供給 P から実小核上の全 perfect 加群の代表可能性・実核の dg 前三角性を証明する。`DGKappaResolvedKernelYoneda` はその前三角性と既存の native 冪等完備性を D 正本の Yoneda 完備化へ代入し、元の dg Yoneda 自身の native 同値を与える。対象ラベルの移送後も元の全単体写像を厳密回収する。`DGKappaResolvedYonedaEvaluation` は同じ実評価双加群への D 正本の tensor・Yoneda 比較と実出力分解を接続し、元の実 Perf Morita 作用を元の厳密評価へ全関手で照合する。任意の元の P の後の元の Yoneda は同じ実 Morita 逆作用と全関手同型で、指定余単位を厳密回収する。同じラベル評価で挟むと固定 ν の既存の実 Perf 同値へ戻る。`DGKappaSuspensionYonedaCompletion` は元の実平坦懸垂の dg 前三角性と、同じ元の dg Yoneda の native 冪等完備化性を D 正本から得る。完備化を同値・通常の局所化・K₀ 全射とは扱わない。実商と固定 ν の Perf 完備化の K 比較を分ける経路はユーザー採用済み（L3 末尾）。共終性は K-S• の Thomason 正本が到着済みで、`DGKappaThomasonCofinality` から同じ命題を実証明で代入する。旧明示入力版は保持する。`DGKappaSuspensionCofinality` は同じ実商の元の Yoneda 安定模型射・実 K 射に正次数同型と零次単射を代入し、同じ比較辺の一回 native loop の非負次数同型へ移す。`DGKappaConeCofinality` は元の実 Perf 評価を介して既存の同じ cone の K 零性を戻し、共終性の正次数単射・零次単射と負次数の連結性から完備化前の cone K の全整数群を自明とする。`DGKappaNativeConeResolution` は同じ cell 増大を含む native 同値で、この零性を D-9 の同じ実平坦源へ反映する。`DGKappaNativeKernelThick`・`DGKappaNativeVerdier` は同じ実核の本質像と商零化対象の一致を証明し、元の二射の Sp 認証と完備化前の全四角形提示を供給する。`DGKappaNativeFibration` は同じ相対 S• fiber 比較と包含射影を実列へ接続する。`DGKappaRawSuspensionCompletion` は始域を移さない同じ実商の元の Yoneda 完備化から、実評価・SOA 比較による固定 K への BF 射を作り、共終性に条件付きの正次数同型・零次単射・loop の非負次数比較を保持する。`DGKappaNativeKernelKComparison` は元の P を通る同じ実核への始点比較。`DGKappaNativeStructure` は同じ実 fibration 辺を前後の実比較で固定 K の構造辺へ戻し、その全一単体と非負次数 π 同型を保持する。`DGSuspensionNativeFibrationSequence` は段別に同じ構造辺を既存の native loop 列へ代入し、実 fibration の非負次数比較と共終性に条件付きで、移動後の非負範囲の隣接安定化と元の実 Sp 余錐への連結比較を得る。`DGSuspensionNativeFibrationTail` は同じ明示引数に条件付きで、任意整数 j の十分後の元の懸垂 K の π_(j+n) から同じ実候補の π_j への群同型を作り、元の実隣接構造射を通る表示が同じ実余錐の脚に戻ることを証明する。候補の負群消滅は主張しない。`DGKappaNativeConeZero` は同じ平坦 cone の native K の実零頂点性を保持する。実商 fiber への比較は既存の正段比較に条件付きで、固定 K の非負次数 fiber 比較・全入力自然性の完成は主張しない。有限 BF 比較の追加経路は採用済み。`DGKappaNativeBFSquare`・`DGKappaNativeBFZero`・`DGKappaNativeBFFiberComparison` は同じ未完備実列の四辺・全正段・実零角・元の実 fiber 比較を保持する。`DGKappaNativeBFOneStage` は第一正段だけで非負整数 π を検出し、`DGKappaNativeBFConnectiveStructure` は同じ実 fiber と実 cone の零性から元の実構造辺を供給する。任意の fibration 辺の追加入力は不要になる。`DGKappaNativeBFConnectiveKernel` は同じ指定全四角柱と正段商比較を代入する。`DGSuspensionNativeBFConnectiveSequence` は段別有限 BF と共終性・I・Z から同じ実列・候補・実 Sp 余極限余錐を構成し、一回の未完備 S• fibration に条件付きで元の連結固定 K・SOA K の非負次数比較、全整数の末尾表示と同じ実隣接射との整合を与える。全反復 S• 引き戻しを条件にした `DGKappaNativeBFLoopStructure`・`DGSuspensionNativeBFSequence` は補助経路で、連結主経路には要求しない。I・P・Z の実例は D 正本から接続済み。異なる dg 入力間の全自然性・反復整合は未供給。未供給型一覧はコーディネータの仲介用であり、K-7 からの直接メッセージ送信はしていない。
- b の Verdier 列の左項は選んだ perfect 対象の実安定閉包。元の β5 の Perf と同一視する際は P の全写像空間の同値と包含の全関手比較を必ず使う。ordinary 導来圏での `perfectCovers` だけからは推論しない。
- 同じ cone の K の消滅は接続済み。K-6 の canonical fiber 比較から固定 native loop への実構造比較は、下記の未供給の相対屋根入力に対して構成した。F2N-5・非連結 K 本体は未接続。一般の安定 ∞ 圏上の K は作らない。
- D-9 の native `IsStableVerdierSequence` と、固定 ν（Perf 値）の `IsVerdierSequence` は異なる証拠。前者の実供給から後者や Perf 零角の零性を無条件に推論しない。
- a の以前の end 持ち上げ余錐は保持するが、完成界面は `sequentialCandidateColimitCocone`。通常の Hom 極限性だけでは ∞ 余極限性の代用にならない。

### 次の一手
- Sp の c5 が到着したら DGNonconnectiveKConnectiveComparison の hrow へ同じ実商で代入する。D の全作用が届いたら、元の実構造辺との自然性から dgNonconnectiveKDiagram の全入力比較を組み立てる。Fibration・SConstruction・Sp・D は読み取り専用。
- c5：Sp の同じ実商の標準単体比較を `DGKappaSuppliedBFFirstRowSimplices` へ代入し、`DGSuspensionUnconditionalFirstRowComparison` で同じ D-8 実反復の連結比較へ渡す。旧入口は二比較を保持する。新入口では K-6 canonical c4・共終性を放電し、Sp の c5 だけを明示入力に残す。
- K-S•-S3 の実 BF 四角形・全正段比較・整数 π 可換性と実核・実商の二頂点 Sp 同型は消費済み。旧四対象固定 hBF 経路も条件付きで保持し、供給待ちとは扱わない。
- c1〜c3、同じ cone の連結 K・固定 K の実零性、D-8 の実 I・P・Z の消費は完了。c4 の全 native 作用・Morita 比較・P 包含の自然性は明示境界を維持し、D の実供給は主張しない。
- e：D の全作用から実逐次比較 η と元の段別射 f の保存・座標可換性を供給し、既存の完備化・Morita 消費先へ代入する。filtered は同じ反復の段別 π 保存と実 Sp filtered 余錐を供給して交換部分へ渡す。K-6 d は到着分を消費済みで c5 が残る。Sp の sp_isStable は未到着、同種 API は新設しない。f は全入力関手性・局所化性が揃ってから登録する。

### c5 の供給境界（採用済み、2026-10-25）
- I は cone の dg 小模型、P は元の Perf とその perfect 安定閉包の全関手比較を供給するが、固定 `dgKInputInfinity` 内の実相対 Verdier 四角形まではフィールドに含まない。同じ商は平坦分解を介する屋根であり、未供給の厳密 Cone→Σ 射を仮定しない。
- 採用：I・P の型を変えず、`DGKappaSuspensionRelativeRoofInput` を別の明示供給境界とする。実小 dg 核、同じ平坦 cone・同じ Σ を頂点とする固定 ν の `RelativeVerdierDiagram`、右辺が元の `dgKappaResolvedSuspensionInputMap` の全一単体である厳密一致を要求する。この型の存在は主張しない。
- D-9 の `resolvedDGQuotientFlatKernel` を `dgKappaResolvedKernelKInput` に包装し、元の包含・局所 Hom K-平坦性を保持した。同じ native Verdier 列の全頂点零化と D 正本の収縮取得を使い、Sp-6 の固定零化構成子へ接続した。指定収縮の追加仮定は不要。`dgKappaResolvedRelativeRoof` は固定 ν の元の二射の Verdier 証拠 `hV` と、実全対象商の Perf 零性 `hz` に条件付きで、同じ実核・包含・商辺を保持する。実全対象商の Perf 零性 `hz` は `dgKappaResolvedNullPerf_isZero` で実供給済み。残る固定 ν の Verdier 証拠 `hV` と、Perf 完備化・P の照合の存在は主張しない。一般商・局所化 API は新設しない。
- 条件付きの利用側は実装・検証済み。相対屋根入力だけから同じ核 K→固定 native loop K(Σ) の実 BF 射・元の全比較辺・実合成二胞体を得る。元の K 四角形の引き戻し性、入力の存在、P との照合、全入力射に自然な反復整合性、`K^{nc}` の完成は含めない。


### 仮定入力の一覧（refactoring-infinity.md §6 と同形式）

入力型そのものの定義行・import 行を除く一致行数。存在は主張しない。I・P とは別の明示供給境界。

| 名前 | 所在（SerrePositivity/ 以下） | 供給元 | 使用（一致行／ファイル） |
|---|---|---|---|
| `hBF : dgKappaNativeBFSquareComparison`（ユーザー採用、明示定理引数） | KST/NonConnective/DGKappaNativeBFSquare.lean | 旧四対象を固定する条件付き補助経路として保持。実 S3 は新 BF 四対象で供給済みであり、同じ型の存在を供給済みとは扱わない。主利用側 DGKappaSuppliedBF* は実 Φ と指定整数群同型との可換式を直接消費する | 集計対象外（定理引数） |
| `hcofinal`（旧明示入力を保持、新入口で実供給） | KST/NonConnective/DGKappaSuspensionCofinality.lean | K-S•：Thomason 正本の実証明。K-B3：DGKappaThomasonCofinality・同じ実候補の完備化比較へ代入 | 集計対象外（定理引数） |
| `DGKappaSuspensionRelativeRoofInput` | KST/NonConnective/DGKappaSuspensionRelativeRoofInput.lean:32 | 実小 dg 核・平坦屋根：D-9。固定 ν の相対 Verdier 四角形・Sp 接続：Sp-6。元の Perf・P との照合：K-B | 19／7 |
| `DGSuspensionNativeActionInput`（採用（03:55）） | KST/NonConnective/DGSuspensionNativeActionInput.lean:25 | D-8 e（供給仕様拡張を採用、未供給）：同じ実核・cone・零角・懸垂の全四角形族と、実評価 Morita 比較・元の P の包含の全 native Hom 自然性。K-B：固定 S・ν・K での照合。供給路：PerfDGInput 上の厳密 SSet 豊穣自己関手の coherentNerveMap。DGSuspensionNativeSquareModel は型のみ公開（cb125356d）。本体・Morita/P 自然性は未供給で c4 は明示入力を保持 | 43／5 |

| フィールド／照合 | 供給元 |
|---|---|
| `kernel` | D-9：実供給済みの同じ平坦商の実小 dg 核。K-B の `dgKappaResolvedKernelKInput` に接続 |
| `diagram` | D-9：平坦屋根・native Verdier 列を実供給。Sp-6：固定 ν の構成子を実供給。`hz` は K-B の同じ実全対象商の Perf 零性で解消。残る `hV` は固定 ν の Verdier 証拠 |
| `left_eq`・`middle_eq`・`right_eq` | D-9・Sp-6 の構成子から同じ指定三頂点を保持。実供給済み `hz` を代入でき、残る `hV` に条件付き |
| `quotient` | 同じ元の平坦商射の全一単体を `dgKappaResolvedRelativeRoof_quotient` が保持。実供給済み `hz` を代入でき、残る `hV` に条件付き |
| 元の Perf・P との全関手照合（構造のフィールドには未追加） | K-B：同じ分解増大を実核へ制限した準同値と native nerve 同値を構成。P の実比較を逆に通す `dgKappaPerfectResolvedComparison` は元の導来模型への全包含同型を保持する。I・P に条件付きで同じ実評価 Morita 核の ∞-Perf 同値と固定 ν 値間の完全な順逆同値を供給。native P と同じ厳密評価の合成は元の Perf の恒等に全関手同型。元の Perf 包含との照合・全入力自然性は未完 |


| `DGSuspensionNativeActionInput` の追加供給仕様（現行 Lean フィールドには未追加） | 供給元 |
|---|---|
| 同じ実核・cone・零角・懸垂の全四角形族。各 A への制限は `dgKappaResolvedConnectiveSquare R A (s A).cone` 全体と厳密一致 | D-8 e：厳密模型。K-B：固定 S 上への接続 |
| 同じ実評価 Morita 比較の全 native Hom 自然性 | D-8 e：同じ実評価族。K-B：固定 ν・K の比較へ移送 |
| 元の P の包含との全 native Hom 自然な比較 | D-8 e：元の包含族。K-B：元の P・Perf 包含への照合 |


### c4 の全高次作用の供給境界（採用（03:55））
- I・P と `DGSuspensionStageProvider` は対象別の供給であり、選んだ同じ cone に対する全 native Hom の作用を含まない。`DGSuspensionIterationMaps` の通常射に対する条件付き恒等・合成則だけを、固定 S 上の ∞ 関手の供給とは数えない。
- 採用：`DGSuspensionNativeActionInput` を別の明示境界とする。固定 `dgKInputInfinity` 上の全単体的自己射 `map`、同じ平坦懸垂との `vertex` 照合、元の各 dg 射の増大可換データ `data`、同じ実商射の全一単体との `edge` 照合を要求する。存在は主張せず、固定 S・ν・K や I・P の型を変えない。
- 利用側は検証済み：`DGSuspensionEnrichedAction.ofEnrichedHom` は明示全 Hom 族・豊穣単位合成則・元の実 dg 射との照合から指定供給路を実装する。対応する豊穣自己関手の coherentNerveMap が元の各頂点・辺を保持する。供給された同じ作用の全高次反復を作り、各頂点を既存の `dgSuspensionIteration`、元の各厳密 dg 辺を既存の `dgSuspensionIterationMap` と厳密照合する。通常射の厳密合成則を追加で仮定せず、`map` 自体が全高次整合性を保持する。
- 供給分担：K-B が全単体的作用と頂点・辺の照合を組み立てる。供給路は **PerfDGInput 上の厳密 SSet 豊穣自己関手の coherentNerveMap**。D-8 e の供給仕様は下記の全四角形族・実評価 Morita 比較・元の P の包含の全 native Hom 自然性へ拡張済み（型のみ公開、本体は未供給）。対象別の `covers` による代表選択から厳密・高次の自然性を推論しない。この境界は I・P・実相対屋根とは別であり、存在・実供給は主張しない。評価待ちで停止せず K-6 c4・c5 と K-7 d を進める。

### D-12 供給境界（採用済み）
- c2 の汎用 dg 加群の分裂 cofiber 判定は D 正本（D-12）。K-B は元のラベル作用・二胞体との照合と Perf への反映を担当する。K-B 内に一般 dg 加群の cofiber API を重ねない。
- D への依頼型：小 dg 圏上の右加群の閉射 a:M→N、r:N→M、b:P→N、p:N→P が a≫r=1、b≫p=1、a≫p=0、b≫r=0、r≫a+p≫b=1 を満たすとき、零角 Z（native 零頂点）、左辺・上辺・対角が零、上下の次数 −1 成分がともに零の同じ `DGModuleSquareData` の実四角形が `IsPushoutSquare`。
- 元の cone 射影の右逆は K-B で構成済み。逆順の全 dg 自然ホモトピーと同じ二胞体の余極限性は D-12 正本を利用し、通常 H⁰ の分裂で代用しない。

- `DGKappaSplitModuleSquareData` は同じ四辺・零対角・零の両原始元を持ち、上下の実二胞体と全四角形を元のラベル作用像へ厳密照合済み。実加群像で五つの分裂関係と零角を検証した。`DGKappaSplitCofiberInput` だけを明示入力とし、同じ Perf 四角形への反映と全単体的 `dgKappaSplitCofiberFamily` を構成する。D-12 の公開 `DGModuleSplitCofiber`（469b59c33）で `dgKappaSplitCofiberInput` を実供給し、追加 cofiber 仮定を除去した。`dgKappaConnectedK_isZeroVertex` と `dgKappaFixedK_isZeroVertex` は、同じ実 cofiber 族の完全性・三評価の加法性・`dgKappaSwindleFixedK_pi`・同じ SOA 群比較から、元の cone の連結 K と固定 K の実 Sp 零頂点性を与える。

### K-7 c の三段目（v3）
- [x] c1 `dgKappaZeroPerfAction_values` の修正・集約・監査への接続。
- [x] c2 実分裂四角形の辺・零角・点ごとの cofiber 性。
- [x] c3 加法性と swindle による同じ cone の連結 K の消滅。
- [ ] c4 反復懸垂の入力射作用と整合性。
- [ ] c5 構造射と逐次余極限による `K^{nc}` の構成。


### K-7 d の三段目（2026-10-25、c の供給待ちと並行）
- [x] d1 元の連結固定 K から、同じ実 Sp 余極限余錐の零段の脚による実比較射。
- [x] d2 元の native loop 反復と整数 π の次数移動を、同じ隣接遷移射へ照合。
- [ ] d3 非負次数の隣接安定化を証明し、同じ実比較射の非負整数 π 同型へ接続。
- [ ] d4 Ind I-2 e の公開結果との照合、選択比較と全入力の自然性。

- `DGSuspensionConnectedComparison` は元の連結固定 K から同じ実 Sp 余錐の零段の脚を実 BF 比較射として回収する。隣接遷移の非負次数安定化に条件付きで、元の比較射を順方向とする群同型を構成し、同じ SOA 比較からの実連結 K 比較も全単射となる。`DGSuspensionLoopStagePi` は同じ n 段の native loop 反復値の整数 π を元の n 回懸垂 K の j+n 次数へ同型で比較する。`DGSuspensionShiftedTransition` は同じ実隣接 BF 射をこの座標で読み、元の作用との厳密な可換性・全単射性の同値・同じ実余錐の連結比較への移送を保持する。`DGSuspensionPerfectStructurePi` は段別 I・P・Z と同じ実 fiber 比較の非負次数条件に対し、実評価 Perf 比較を代入した元の構造射の j+n 次数の全単射性を供給する。全非負 j・全段、および任意整数 j の n≥(-j).toNat の範囲を保持する。無条件の連結版 K-6・段別入力の実供給・全入力自然性と I-2 e との照合は未証明。
- `DGSuspensionNativeTransitionPi` は Sp 正本の自然同型を反復し、元の構造辺の全一単体に対する `dgSuspensionStructureLoopPi_naturality` と、同じ実隣接 BF 射の全単射性を元の辺の j+n 次数へ移す `dgSuspensionNativeSequenceMap_bijective_iff_structure` を供給する。既存の対象別次数座標との一致は主張せず、同じ BF 射を介して全単射性だけを移す。一般 Sp loop API は新設しない。
- `DGSuspensionPerfectTransitionPi` は同じ実評価 Perf 比較と元の実零角を代入し、段別 I・P・Z と連結版 K-6 の非負次数比較に条件付きで、全非負次数の実隣接安定化・同じ実余錐への連結比較・元の SOA 連結 K 比較を供給する。任意整数 j と n≥(-j).toNat では、同じ実余錐の n 段の脚が π_j 同型であり、候補の π_j を元の n 回懸垂 K の π_(j+n) から群同型で比較する。`dgSuspensionPerfectCandidate_tailPiEquiv_succ` は、この段別表示が元の実隣接構造射を経ても同じ実余錐の脚を与えることを証明する。負群の消滅・段別入力の存在・無条件 K-6・全入力自然性は主張しない。
- `DGKInputIndCompactGeneration` は元の固定 ν の冪等完備性から、同じ `Indω` の compact 生成同値・元の全 Yoneda への厳密包含式・compact 本質像・任意族の包含と逆射選択比較を供給する。`dgKInputStableCompactGeneration` は `UnconditionalStableCompactGeneration` の最終入口を使い、正本の全頂点の filtered 生成表示も保持する。交換・有限全存在の追加入力を除去した。同じ生成同値と包含・全入力族の選択比較を保持する。
- `DGKInputCompactNativeFamily` は元の `presentedPerfectDGNativeFamilyMap` の全 native Hom を宇宙移送し、同じ生成逆射・順射で compact 生成元間へ送る。同じ全族の包含後は元の ν 全族と元の Yoneda の合成へ厳密に戻り、元の各厳密 dg 射を同じ全族の頂点として回収する。固定二入力間の全パラメータ比較であり、全入力間の合成整合・構造辺 β の自然性・D-8 の実 κ-compact cone との比較は未完。`Indω` の通常 compact 生成と `(Indω C)^κ` の非可算 κ-compact cone を混同せず、d4 完了とは数えない。
- `DGKInputCompactNativeComposition` は元の ν の通常関手の恒等・厳密合成保存を同じ生成同値の単位・余単位へ代入し、既存の全 native Hom 族の各元の dg 射について恒等・合成の全関手同型を与える。`DGKInputCompactNativeLiftedComposition` は同じ元の全 native 合成を宇宙移送し、固定 ν 全族の厳密合成保存を全単体・全評価で証明する。`dgKInputCompactNativeFamilyMap_compIso` は元の中間生成同値の単位を全関手空間へ送り、compact 生成元間の全 native 入力の二項合成を元の合成入力の作用と関手同型で比較する。任意の同時パラメータ族への制限は `dgKInputCompactNativeFamilyMap_compParameterIso`、同じ比較自体の再制限自然性は `_precomp`。`DGKInputCompactNativeComparison` は同じ生成単位による全 native 作用の生成順射比較・元の全 Yoneda 包含後の比較を供給する。同じ比較の任意入力族への制限と再制限自然性、同じ順射を持つ別の生成逆射との全 native 作用比較も保持する。`DGKInputCompactGenerationAdjoint` は Mathlib の quasicategory 二圏の余単位正規化を使い、同じ生成順逆射と単位を厳密に保つ随伴同値・左右三角式・正規化した恒等 dg 作用比較を供給する。既存の二項合成単位と旧恒等比較は保持する。三項以上の全高次整合・全入力の β 自然性や実 cone 比較を完成したとは数えない。
- Sp 正本から供給済み（09:30、472ca0e29）の `SpectrumHo.nativeLoopPiIso` を d2 に代入済み。同じ実 loop／円 cotensor 比較との可換性は正本の `nativeLoopPiIso_circle_comparison` が保持する。d3 の無条件化は連結版 K-6 の証明に依存する。


### 採用済み供給仕様：D-8 e の全入力自然性（未供給）
- 現行 `DGSuspensionNativeActionInput` は Σ の全高次作用と元の各 dg 辺のデータを保持する。今回の実評価による固定 ν 比較・元の P との全包含比較は対象別であり、これらだけから構造辺 β の全入力自然性を結論しない。
- 採用：D の厳密模型の評価対象を、`((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity R) ⟶ dgKInputInfinity R` で表す同じ実核・cone・零角・懸垂の全四角形族へ広げる。各元の入力 A への制限は同じ `dgKappaResolvedConnectiveSquare R A (s A).cone` 全体と厳密に照合する。
- 併せて、今回の実評価 Morita 比較と元の P の包含を同じ全 native Hom に自然な比較として供給する。K-B はその像から固定 K の構造辺・実逐次図式の自然性を構成する。β の自然性や Sp 引き戻し性を追加入力にして完成扱いしない。
- `DGSuspensionNativeActionInput` の D-8 e 供給仕様として記録する。D の新型 DGSuspensionNativeSquareModel は全四角形・厳密豊穣懸垂成分を表すが、本体と Morita/P 自然性は未供給で仕様充足・完成とは数えない。I・P・固定 S・ν・K を変更せず、存在も主張しない。供給の仲介はコーディネータが行う。
- `DGSuspensionNativeSquareFamily` は同じ採用済み全族と元の各実四角形への厳密一致を受ける条件付き利用側。全 native 関手空間表示から元の全族・固定 K 像を厳密回収し、各角・包含・商辺と全反復段を元の同じ実四角形へ照合する。`DGSuspensionNativeActionInput.ofSquareFamily` は元の dg 射データ・辺照合を併せて受け、懸垂角を既存の全高次反復へ渡す。`DGSuspensionNativeStageFamily` は採用済みの明示全高次懸垂作用から各段の全入力 K・native loop 族を構成し、元の BF 頂点・全一単体・零段の固定 K・次段再帰を厳密回収する。入力射の厳密恒等・合成則の追加入力は使わないが、段間 β の自然性は含めない。全族・実評価 Morita 比較・P 包含の全入力自然性の供給は未完で、境界の完成とは数えない。

### c4 利用側の厳密性調査（D 緩和案の照合待ち、未採用）
- 現行 ActionInput が要求するのは全単体の `map : S ⟶ S`・元の対象の `vertex` 等号・実射データ・`edge` 等号。厳密豊穣自己関手そのもの、data の act_id/act_comp はフィールドにない。coherentNerveMap による厳密豊穣供給は一つの供給路であって唯一の消費可能形式ではない。ただし個々の可逆 2-cell だけでは全 SSet map の存在・全高次整合性は得られない。
- vertex の厳密性は iteration_vertex と StageFamily_vertex、SquareIterationFamily_at/KSquareIterationFamily_at の既存の同じ実反復対象・選択 cone への依存型照合で使用。現行の固定模型を保つ最小変更案では保持する。頂点も VertexIso に緩和する場合は全反復の対象比較・I/P/β・実余錐の輸送が別途必要で、辺だけの緩和の見積り外。
- edge の直接消費は iteration_edge（帰納段の rw）と StageFamily_edge、その供給口 ofSquareFamily の hedge。全単体 map と厳密 vertex があれば、同じ始終点を固定した指定可逆 2-cell/相対 arrow 比較へ置換可能と判断。単なる端点対象の VertexIso やホモトピー圏の等号だけでは代用しない。反復は map による比較の像と次段比較を合成し、固定 K と native loop へ送る。
- SquareFamily の curry/uncurry・全族回収・反復の定義と再帰式は edge に非依存。hF は各入力での「全四角形」等号（四頂点の等号より強い）であり、edge 緩和だけでは変えない。hF も緩める場合は全四角形の指定比較とその辺制限・境界整合が必要。点別の角/辺比較だけで二胞体を代用しない。
- DGKappaSuspensionInputLaws の id/comp/epsilon は形式的な MapData.id/comp に関する既証明の厳密則で、D の作用の厳密性を要求していないため変更不要。DGSuspensionIterationMaps の厳密通常関手入口だけは act_id/act_comp を要求し、ホモトピーまでの作用から従来の ⥤ を結論しない。native 反復はこの入口を使わない。
- 規模の暫定見積り：全 SSet map・厳密 vertex・端点固定比較が供給され、hF を保持するなら別入口/互換アダプタとして 3–4 葉・8–15 宣言程度。hF も比較へ緩和するなら追加で既存の約 7 個の全四角形回収定理を比較版へ変更。全 native パラメータ比較・単位/合成/高次整合を作る供給本体はこの数に含めない。D 案を受けて確定し、現時点では型変更しない。

### 採用済み設計：連結 K の fiber 条件の適用範囲
- 検証済みの帰結：全段で同じ実屋根・元の Perf との指定同値・元の相対 K 四角形の Sp 引き戻し性を仮定すると、`dgSuspensionRoofTransition_piIsomorphism` は全整数の隣接 π 同型を与える。同じ実余錐の零段の脚が全整数 π 同型・実可逆辺となり、同じ候補の全負整数 π が消える。供給の存在や一般の負群消滅を主張する定理ではない。
- 採用：既存の条件付き Sp fiber 定理は保持する。一般の K-7 の構造射・連結比較には、K(TA)≃0 と連結版 fibration による実 fiber との非負次数比較を使い、全段の Sp 引き戻し性は仮定しない。一般の Verdier 列の Sp fiber 性と相対局所化登録は K^{nc} について非連結化後に証明する。固定 S・ν・K、I・P と採用済み供給境界は変更しない。
- `DGKappaSuspensionConnectivePi` は指定 Perf 同値・零所属に条件付きで、元の実 fiber 比較の π 全単射性を同じ元の K(B) 構造射へ移す。零角には同じ実 null 商の Perf 零性を使い、ν の Verdier 証拠や Sp 引き戻し性を要求しない。非負次数条件自体は連結版 K-6 からの未供給入力。`DGKappaResolvedEvaluationKernel` は同じ実核の評価双加群を元の核包含・増大・実加群包含で構成し、I の列の射影性と全 Hom 準同型を保持する。`DGKappaResolvedEvaluationPerfect` は P の元の全包含比較を実主導来比較へ移し、各列の perfect 性と元の全 perfect 加群の回収を証明する。`DGKappaResolvedEvaluationMorita` は同じ評価核の Morita 三条件と元の主 Perf 作用に一致する同値を構成する。`DGKappaResolvedKernelComplete` は P に条件付きの同じ native 核の coherent 冪等完備性を保持する。`DGKappaResolvedEvaluationQuasiEquivalence` は同じ実評価を元の全 perfect dg 加群へ制限し、同じ全 Hom と P による回収から厳密 dg 準同値と実 nerve 同値を構成する。`DGKappaResolvedEvaluationInfinity` は D の小 Perf 代表・局所生成原始から両側 compact 生成を検証し、同じ実評価の全主導来同値と実 ∞-Perf 同値へ接続する。`DGKappaResolvedKernelPerfEquivalence` は同じ二つのラベル評価で固定 ν 値の完全な順逆同値を供給する。`DGSuspensionPerfectConnectiveSequence` は段別 I・P・Z に条件付きで追加 Perf 同値入力を除き、元の実列・Sp 余極限・連結 K からの実比較を保持する。`DGKappaResolvedEvaluationInclusion` は同じ厳密評価の元の実導来包含を回収し、native P と実評価の合成を恒等へ全関手同型で比較する。実 ∞-Perf Morita 作用と元の P・Perf 包含の照合は `DGKappaResolvedYonedaEvaluation` で同じ全関手比較へ接続済み。異なる dg 入力間の全自然性は未完。
- K-6 d は K(D)→fib_Sp(K(C)→K(C/D)) の非負次数 π 同型へ修正済み。固定連結 K の Sp 引き戻し性は主張しない。K-6 c4 の元の全二胞体・核円柱比較、c5 の商実現比較、実核接続を保持し、c4・c5 と d を継続する。

## 原典との照合・受入条件
- [BGT 2013 §9.1、Def. 9.1・Lem. 9.4・Prop. 9.5・Def. 9.6・Lem. 9.7](https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf) を基準とする。一般安定 ∞ 圏での構成は参照先の主張であり、本レーンでは厳密 dg 供給に限定する。
- cone は `(Indω C)^κ`。通常の compact 対象だけに置き換えない。非可算正則 κ のもとで可算余積と swindle `id ⊕ T ≃ T` を使い、同じ dg cone の連結 K が消えることを証明してから構造射を作る（Lem. 9.4）。可算直和の dg 作用と swindle は K-7 内で構成した。未供給の小模型と Perf 比較はコーディネータが仲介する。
- dg cone・懸垂の完全列保存（Prop. 9.5）と全入力射での整合性を、対象別の商の存在と区別する。`PerfDGInput` は小さい dg 圏を受け取るため、元の商の smallness の証拠と固定 K への入力を保持する。
- Lem. 9.7 は κ-filtered 余極限の保存。工程 5 の通常 filtered 余極限保存には別の証明が必要で、両者を同一視しない（BGT Thm. 9.8 の証明末尾は Schlichting 2006 §7 Lem. 6 を別に参照する）。
- 工程 1 の受入には、同じ BF 候補を頂点とする実 Sp cocone、その `IsColimitCone`、実 cocone の各辺と既存整数 π 比較の整合が必要。群の `IsColimit` のみでは未達。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。工程 1 の逐次実 cocone と ∞ 余極限性は K-7 所有で自前構成（10-23 コーディネータ指示）。

### 実逐次比較の候補への消費（工程 e の形式部分）
- `SequentialLevelColimitLaws` は元の段別余極限比較の厳密な恒等・合成を保持する。`SequentialCandidateMap` は元の BF 射影の hSp 同型で同じ比較を既存の候補へ渡し、hSp 関手則と元の射影下の可換性を認証する。BF 代表の厳密な関手性は主張しない。
- `SequentialCandidateMapPi` は元の実余極限の脚の hSp 可換性、同じ実注入の全整数 π の自然性、候補群の関手と各固定段の元の自然な注入を供給する。各段で π 同型な実逐次自然変換に条件付きで、同じ候補比較の π 同型・実 Sp 辺の可逆性を証明する。dg 入力からの実列比較の供給・全 native 自然性・Morita 不変性の完成・相対局所化登録は含めない。

### K-B-S2：Kan 列標的への相対 BF 分解
- `SequentialBFKanArrowStage`・`SequentialBFKanArrowFactorization` は源 `X : OmegaSpectrum`、標的 `Y : KanSequence`、元の射 `f : KanSequence.Hom X.toKanSequence Y` を使う。Stage は標的の Ω 条件を使わない。
- `sequentialBFKanArrowKanSequence`・`sequentialBFKanArrowKanProjection` は同じ実中間列と厳密射。`sequentialBFKanArrowKanSequence_omegaCondition f hY` は明示証明 `hY : Y.OmegaCondition` から Ω 条件を供給し、`sequentialBFKanArrowMiddle f hY` はその同じ実 BF 対象。
- `sequentialBFKanArrowLeft`・`sequentialBFKanArrowRight`・`sequentialBFKanArrow_fac` は左右の厳密射と各段の元の射の回収、`sequentialBFKanArrowRight_rlp` は全単射 RLP。標的の構造射の単射性は要求しない。
- `SequentialRelativeCofibration` の `sequentialBFKanArrowLeft_relativeLatching`・`sequentialBFKanArrowLeft_isRelativeCofibration` は同じ相対 latching 射と左因子の相対単射性を公開する。旧 Stage 構造体・既存名・型・再帰式 eq_1/eq_2 を保持し、sequentialBFArrowStage_toKanStage で各段を照合する。旧構成は `Y.toKanSequence`・`Y.toKanSequence_omega` への特殊化から導く。

### D-8 の無条件実入力の消費
- `DGKappaUnconditionalStageSupply`・`DGKappaUnconditionalConeZero` は同じ固定 κ の実 I・P・Z、同じ反復対象と各 cone の連結 K・固定 K の実零性を供給する。
- `DGSuspensionUnconditionalBFSequence` はそれらを採用済み実 BF 経路へ代入し、同じ構造辺・候補・実 Sp 余極限余錐と零段脚を保持する。共終性は明示引数で、一回の未完備 S• fibration に条件付きの非負次数 π 同型・全整数の末尾表示まで接続する。`DGSuspensionUnconditionalBFComparison` は同じ連結 SOA 比較の非負次数 π 同型と、元の隣接実構造射を通る全整数末尾表示の整合を接続する。全 native 自然性・非連結化後の局所化性と登録は未完。

### 実逐次比較の末尾判定
- `SequentialCandidateMapEventualPi` は、同じ厳密逐次比較について各次数で十分後の各段の単射・全射・全単射から同じ候補比較の判定を供給し、次数別末尾の全整数 π 同型から元の実 Sp 辺の可逆性へ渡す。元の実注入・遷移射を保持する。dg 入力上の比較や Morita 不変性自体の供給とは数えない。
- `SequentialCandidateMapExactPi` は、同じ厳密逐次比較対の十分後の段別の核・像一致を、元の同じ実候補比較の整数 π へ渡す。実注入と遷移を保持する。Sp fiber 四角形・dg Verdier 列の比較や局所化登録そのものは主張しない。
- `SequentialCandidateMapShiftedPi` は各段の移動後非負範囲 `0 ≤ j+n` の比較・核像一致を、同じ候補の全整数 π の比較・完全性へ渡す。次数移動の実際の loop 比較は Sp 正本を消費し、この群判定だけで Sp fiber 性を結論しない。

### 同じ実列の比較と商標準単体の受け渡し
- `DGSuspensionSuppliedBFTailComparison` は、明示された同じ実 BF 逐次比較について元の全整数末尾表示の自然性と逆座標式を保持する。共終性・二入力の一回の S• fibration に条件付きであり、全 native 入力作用の存在は追加しない。
- `DGKappaSuppliedBFFirstRowSimplices` は c4 の全四角形 `FunctorIso` と c5 の同じ実商の標準単体比較を直接受け、未完備全 S• 引き戻し・実 BF fiber の非負次数比較・同じ固定 K 構造射へ渡す。有限 F1 外延性と Sp 有限図式比較は未放電で、従来の条件付き上側ホモトピー経路も保持する。
- `DGSuspensionUnconditionalFirstRowComparison` は同じ二供給を D-8 の実 I・P・Z の全反復へ代入し、独立した `hS` を取らず元の固定 K・SOA K から同じ候補への非負次数比較を得る。`dgSuspensionUnconditionalFirstRow_tailPiEquiv`・`_succ` は同じ候補の全整数末尾表示と元の隣接構造射との整合にも二供給を直接渡す。二供給と共終性には条件付きで、完成印は動かさない。

### 到着した共終性・相対比較の消費（K-B3）
- `dgKappaFirstRowRelativeComparison` は K-B 正本 `ofFirstRowSimplices` で同じ実商の相対比較を構成する。元の全 S• 引き戻しと反復の入口もこの比較を消費する。
- `dgSuspensionThomasonCandidateMap_piIsomorphism_of_completion`・`_isInvertible_of_completion` は同じ実 BF 候補間で共終性を消費する。十分後の j+n>0 のみを使い、零次全射性や一般の負群消滅は主張しない。
