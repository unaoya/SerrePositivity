# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v3（2026-10-24）**：K-7 は **K-B レーン**に統合（正本は L3-fibration.md、本ファイルは K-7 の引き継ぎ）。I・P の実供給は D-8 として D が担当。

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 a 完了：任意の厳密な逐次 BF 列の実 Sp 余極限を K-7 内で構成。同じ `filteredOmegaSpectrum` を頂点とする `sequentialCandidateColimitCocone` の `IsColimitCone` と、実辺の全整数 π 作用・群余極限比較を接続済み。
- 工程 b の明示入力版完了：β5 の実半自由 D(D)・Perf と β3 の平坦分解後の Drinfeld 商を読み取り専用で使用。未供給の非可算正則 κ の dg 小模型を `DGKappaConeInput`、元の Perf との全関手比較を `DGKappaPerfectInput` として明示した。[未供給宣言の名前・型一覧](archive/L10-dg-kappa-inputs.md)。両入力の存在は未証明。
- 工程 c 進行中：同じ κ と同じ供給 s を保つ反復 `dgSuspensionIteration` を構成。実 swindle を dg 関手圏の閉同型・元の native Kan Hom の実辺へ束ね、固定 `dgKInputK` の同じ二つの実 BF 自己射の全整数 π 作用の等号 `dgKappaSwindleFixedK_pi` まで接続した。これだけで K の消滅とは扱わない。
- K-S• の既存の正反復実現の加法性から、同じ全零境界商 Kan 射対の局所化可逆性・全基点 π 同型を K-7 内で証明した。実標準軸の零関手・恒等関手の評価と群の二軸分解から一重境界商の中央項の正次数群上の加法公式を導き、元の同じ連結 BF K の全整数 π 上の加法性 `connectedKMiddle_additivity` へ移した。非負整数群と一重境界商の群の比較は元の射に自然。非連結 K の定義を一般安定入力へ拡張していない。同じ Perf 上の実分裂 cofiber 族への接続は構成中。
- 同じ実二項 dg 直和の両注入・両射影を、全斉次自然変換と全 dg 関手 Hom end の実閉射に保持した。同じ Hom end 内の四合成・恒等分解を証明した。非 replete な I に実零加群そのものが入る証拠は、別の追加所属入力 `DGKappaZeroInput` として隔離し、その証拠に対する実零 dg 自己関手と閉関手圏での零対象性を構成した。I・P の型・存在を変更したり、その所属を前三角性から推論したりしない。[追加型](archive/L10-dg-kappa-inputs.md)。
- 零自己関手の各 Perf ラベルでの閉零対象性・native 零頂点性、全 native dg 関手パラメータの Perf 作用と固定関手の照合、非可逆閉射の実 Perf 自然変換、同じ注入・射影・零関手の二単体を貼った `dgKappaSplitPerfFamilySquare` まで構成。四角形の cofiber 性と固定 K への加法性の適用は未証明。
- 実 dg 加群の全 Hom end の余積普遍性から可算直和の chain map を構成し、単位・豊穣合成・射影性の保存を証明した。同じ cone 上の厳密 dg 自己関手 T と id ⊕ T を構成。swindle は入力に仮定せず、指定した閉 dg 射・両側逆・全斉次自然性・両向きの厳密自然変換と元の dg nerve 上の実関手同型まで構成した。T と id ⊕ T の native nerve は完全。
- 同じ入力の full dg cone の perfect 対象で零化する cell 分解後の実 Drinfeld 商を構成した。実商射影・安定性・β3 の実安定閉包からの Verdier 列と、固定 `PerfDGInput` への包装を保持する。元の β5 の Perf と安定閉包の同値は P の明示入力で、その元の Perf の全頂点の零化も証明した。
- κ-compact 性は F2 の全共変 Hom による定義を使う。ordinary compact/perfect 比較では代用しない。小ささは選んだ代表系にだけ要求し、全加群圏には要求しない。可算直和の κ-compact 閉性は I の `countableClosed` に明示され、κ の記号だけから証明したとは扱わない。
- F1 の Ind 安定性・K-6 は入力せず、待機もしていない。D 側の供給の仲介はコーディネータ。今回 D・Sp へ直接依頼していない。所有外のファイルは変更していない。
- c の途中成果22モジュールは `390171436` に保存済み。今回の停止区切りは追加4モジュールを集約・監査に接続済み。対象 `lake build SerrePositivity.KST.NonConnective` 成功（11051 jobs）、専用監査成功（71モジュール・761宣言、許容三公理のみ）。所有警告・`sorry`・新規公理・上限引上げなし。c の消滅と構造射は未完。

### 残り（依存順）
1. 工程 c：構成した反復の対象別供給を、懸垂の全入力射に対する作用・整合性へ接続する。証明した S• 境界商の加法性と実 swindle を同じ Perf の実 cofiber 族で結び、同じ cone の連結 K の消滅を証明し、K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A) の構造射を作る（BGT Lem. 9.4・Def. 9.6、見積り未確定）。
2. 連結 K との比較と負次数の記述（BGT §9、Schlichting 2006、見積り未確定）。
3. Verdier 列を fiber 列へ送ること、Morita 不変性、filtered 余極限との可換（K-6 と β3、BGT Thm. 9.8、Schlichting 2006 §7 Lem. 6、見積り未確定）。
4. Sp の相対版 `IsRelativeLocalizingInvariant` への登録（固定 dgKInputInfinity・dgKInputNu・dgKInputK、K-5、見積り未確定）。
5. F1 完了後に同じ dg cone と Ind の安定性 F2N-5 を照合する（BGT §9.1、見積り未確定）。I・P の実供給も未完で、必要型一覧をコーディネータへ報告する。

### 主要宣言
- `sequentialCandidateColimitCocone`、`sequentialCandidateColimitCocone_isColimit`、`sequentialCandidateColimitCocone_vertex`、`sequentialCandidatePiCoconeIsColimit`、`sequentialCandidateColimitHomotopyIso_ι`。
- `DGKappaConeInput`、`DGKappaPerfectInput`、`dgKappaConeDerivedComparison_isFullyFaithful`。
- `dgCountableSumFunctor`、`dgCountableSumHom_injection`、`dgCountableSumObj_projective`、`dgSumFamilyFunctor`。
- `dgKappaConeCountableSum`、`dgKappaSwindleSource`、`dgKappaSwindleStrictHom`、`dgKappaSwindleStrictInv`、`dgKappaSwindleComponentIso`、`dgKappaSwindleInfinityIso`、`dgKappaConeCountableSum_isExactFunctor`。
- `DGKappaSuspension`、`dgKappaSuspensionProjection`、`dgKappaSuspensionInfinity_isStable`、`dgKappaSuspension_isStableVerdierSequence`、`dgKappaSuspensionKInput`、`dgKappaSuspension_kills_perfect`。
- `DGSuspensionStageProvider`、`dgSuspensionIteration`、`dgSuspensionIterationStage`、`dgKappaSwindleClosedFunctorIso`、`dgKappaSwindleNativeInputEdge`、`dgKappaSwindleFixedK_pi`。
- `boundaryKanAdditivityMap_piIsomorphism`、`boundaryKanAdditivityGroup_injective`、`singleBoundary_constantZero`、`singleBoundaryMiddle_additivity`、`nonnegativeBoundaryEquiv_naturality`、`connectedKMiddle_additivity`。
- `dgKappaSplitHead`、`dgKappaSplitTail`、`dgKappaSplitHeadProjection`、`dgKappaSplitTailProjection`、`dgKappaSplit_decomposition`、`DGKappaZeroInput`、`dgKappaZeroFunctor_isZero`。
- `dgKappaZeroPerfAction_isZeroVertex`、`dgKappaFullPerfFamilyMap_vertex`、`dgKappaPerfClosedHomotopy`、`dgKappaSplitPerfFamilySquare`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供：厳密な逐次 BF 列の同じ BF 候補を頂点とする実 Sp 余極限・実辺の整数 π 比較。一般 coherent 列の整流を仮定してはいない。
- D の09:57までの供給：候補 `objects := dgKappaClosedProjectiveObjects R D κ` に対する `small`・`projective`・`derivedFullyFaithful`、`countableClosed`・`binaryClosed`・`perfectCovers` の個別宣言あり。実零加群所属・shift/cone 閉性もあり、同じ候補に対する Z の材料となる。K-7 の I・P の実値には未接続。`uncountable`・`regular` は κ の明示条件。
- D の未供給：I の `kappaCompact`・`covers`・`pretriangulated`。前三角性は D の未統合試作にとどまり、本体供給として数えない。P の `comparison`・`isEquivalence`・`inclusion` も未供給。対象別反復供給 `DGSuspensionStageProvider` の存在・入力射作用と整合性は未証明。[宣言名と対応表](archive/L10-dg-kappa-inputs.md)。

### 未コミット
- `SerrePositivity/KST/NonConnective/DGKappaPerfZeroFamily.lean` を未追跡の作業ファイルとして残す。集約・専用監査から未接続。`dgKappaZeroPerfAction_values` の末尾で、`dgNerve.map` による頂点の像と `Simplex.vertex` の同一視が型不一致（旧ログ `/tmp/k7-c-native-split2.log`）。後続 `dgKappaZeroPerfFunctorVertex_isZero`・`dgKappaFullPerfZeroVertex_isZero` もファイル全体として未検証。`sorry` に置き換えない。
- 他の K-7 所有変更は停止コミットで保存する。共有作業木・共有 index の他レーンの変更は対象外。

### 既知の問題
- D は上記の個別フィールドを供給したが、I・P の完成した実値は未提供。両構造の存在、選択独立性・全入力射での反復の整合性は証明済みと扱わない。未供給型一覧はコーディネータの仲介用であり、K-7 からの直接メッセージ送信はしていない。
- b の Verdier 列の左項は選んだ perfect 対象の実安定閉包。元の β5 の Perf と同一視する際は P の全写像空間の同値と包含の全関手比較を必ず使う。ordinary 導来圏での `perfectCovers` だけからは推論しない。
- K-6・F2N-5・K の消滅・非連結 K 本体は未接続。必要時は対応する主張を明示入力に隔離し、提供後に差し替える。一般の安定 ∞ 圏上の K は作らない。
- a の以前の end 持ち上げ余錐は保持するが、完成界面は `sequentialCandidateColimitCocone`。通常の Hom 極限性だけでは ∞ 余極限性の代用にならない。

### 次の一手
- 新チャットが最初に証明する宣言は、未接続 `DGKappaPerfZeroFamily.lean` の `dgKappaZeroPerfAction_values`：同じ実零自己関手による `dgNerve.map (presentedPerfectDGAction …)` が元の Perf の全0単体を `IsZeroVertex` へ送ること。`dgNerve.vertexEquiv.symm` と `Simplex.vertex` の照合、および dg nerve 写像の頂点公式を明示して型不一致を解消する。その後、同ファイル全体を対象検査し、成功後にだけ集約・監査へ接続する。次に実分裂四角形の辺・零角・点ごとの cofiber 性を証明し、`connectedKMiddle_additivity` と `dgKappaSwindleFixedK_pi` を結ぶ。K-6・F2N-5・I・P の存在は完成扱いしない。工程 c→d→e→f は各工程の完了報告後も承認を待たず、停止せず続行する。このチャットはコーディネータの停止指示に従い再開しない。

## 原典との照合・受入条件
- [BGT 2013 §9.1、Def. 9.1・Lem. 9.4・Prop. 9.5・Def. 9.6・Lem. 9.7](https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf) を基準とする。一般安定 ∞ 圏での構成は参照先の主張であり、本レーンでは厳密 dg 供給に限定する。
- cone は `(Indω C)^κ`。通常の compact 対象だけに置き換えない。非可算正則 κ のもとで可算余積と swindle `id ⊕ T ≃ T` を使い、同じ dg cone の連結 K が消えることを証明してから構造射を作る（Lem. 9.4）。可算直和の dg 作用と swindle は K-7 内で構成した。未供給の小模型と Perf 比較はコーディネータが仲介する。
- dg cone・懸垂の完全列保存（Prop. 9.5）と全入力射での整合性を、対象別の商の存在と区別する。`PerfDGInput` は小さい dg 圏を受け取るため、元の商の smallness の証拠と固定 K への入力を保持する。
- Lem. 9.7 は κ-filtered 余極限の保存。工程 5 の通常 filtered 余極限保存には別の証明が必要で、両者を同一視しない（BGT Thm. 9.8 の証明末尾は Schlichting 2006 §7 Lem. 6 を別に参照する）。
- 工程 1 の受入には、同じ BF 候補を頂点とする実 Sp cocone、その `IsColimitCone`、実 cocone の各辺と既存整数 π 比較の整合が必要。群の `IsColimit` のみでは未達。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。工程 1 の逐次実 cocone と ∞ 余極限性は K-7 所有で自前構成（10-23 コーディネータ指示）。
