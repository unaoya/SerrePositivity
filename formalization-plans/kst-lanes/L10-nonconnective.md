# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v3（2026-10-24）**：K-7 は **K-B レーン**に統合（正本は L3-fibration.md、本ファイルは K-7 の引き継ぎ）。I・P の実供給は D-8 として D が担当。

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-24）

### 現在地
- 採用済み経路へ再開：K(TA)≃0 と連結版 fibration の元の実 fiber 比較を構造射・連結比較 d1〜d4 に使う。全段の Sp 引き戻し性は仮定しない。e の Verdier 列の Sp fiber 性と f の相対局所化登録は K^{nc} について非連結化後に証明する。
- 上流 import 閉包の復旧と両所有集約の再ビルドを確認。`DGKappaSplitPerfEvaluation` を検証し、集約・監査へ接続済み。元の全 native 関手族と同じ実四角形の全単体を、元の各 Perf ラベルの dg 作用へ照合し、同じ点ごとの零三角形を構成した。D-12 の公開判定により同じ二胞体の cofiber 普遍性を証明し、同じ cone の連結 K・固定 K の実 Sp 零頂点性まで接続済み。
- 工程 a 完了：任意の厳密な逐次 BF 列の実 Sp 余極限を K-7 内で構成。同じ `filteredOmegaSpectrum` を頂点とする `sequentialCandidateColimitCocone` の `IsColimitCone` と、実辺の全整数 π 作用・群余極限比較を接続済み。
- 工程 b の明示入力版完了：β5 の実半自由 D(D)・Perf と β3 の平坦分解後の Drinfeld 商を読み取り専用で使用。未供給の非可算正則 κ の dg 小模型を `DGKappaConeInput`、元の Perf との全関手比較を `DGKappaPerfectInput` として明示した。[未供給宣言の名前・型一覧](archive/L10-dg-kappa-inputs.md)。D-8 e（19:33、5bf80c07c）の `dgKappaPerfectInput` により P は任意の同じ I から実供給済み。I 自体の存在は未証明。
- 工程 c 進行中：同じ κ と同じ供給 s を保つ反復 `dgSuspensionIteration` を構成。実 swindle を dg 関手圏の閉同型・元の native Kan Hom の実辺へ束ね、固定 `dgKInputK` の同じ二つの実 BF 自己射の全整数 π 作用の等号 `dgKappaSwindleFixedK_pi` まで接続した。同じ全 cofiber 族の完全性と三評価の実加法性を用い、同じ SOA 群比較を介して元の固定 K と連結 K の実 Sp 零頂点性を証明した。
- K-S• の既存の正反復実現の加法性から、同じ全零境界商 Kan 射対の局所化可逆性・全基点 π 同型を K-7 内で証明した。実標準軸の零関手・恒等関手の評価と群の二軸分解から一重境界商の中央項の正次数群上の加法公式を導き、元の同じ連結 BF K の全整数 π 上の加法性 `connectedKMiddle_additivity` へ移した。非負整数群と一重境界商の群の比較は元の射に自然。非連結 K の定義を一般安定入力へ拡張していない。同じ Perf 上の実分裂 cofiber 族と、その完全性・元の三評価へ接続済み。
- 同じ実二項 dg 直和の両注入・両射影を、全斉次自然変換と全 dg 関手 Hom end の実閉射に保持した。同じ Hom end 内の四合成・恒等分解を証明した。非 replete な I に実零加群そのものが入る証拠は、別の追加所属入力 `DGKappaZeroInput` として隔離し、その証拠に対する実零 dg 自己関手と閉関手圏での零対象性を構成した。I・P の型・存在を変更したり、その所属を前三角性から推論したりしない。[追加型](archive/L10-dg-kappa-inputs.md)。
- 零自己関手の各 Perf ラベルでの閉零対象性・native 零頂点性、全 native dg 関手パラメータの Perf 作用と固定関手の照合、非可逆閉射の実 Perf 自然変換、同じ注入・射影・零関手の二単体を貼った `dgKappaSplitPerfFamilySquare` まで構成。同じ上・下二胞体、四辺、全関手空間の実零角を回収し、`dgKappaSplitPerfZeroTriangle` に束ねた。各 Perf ラベルでの同じ閉注入・射影の四合成と恒等分解も接続済み。点ごとの cofiber 性・同じ全族の完全性・固定 K への加法性と swindle による実零頂点性は接続済み。
- 実 dg 加群の全 Hom end の余積普遍性から可算直和の chain map を構成し、単位・豊穣合成・射影性の保存を証明した。同じ cone 上の厳密 dg 自己関手 T と id ⊕ T を構成。swindle は入力に仮定せず、指定した閉 dg 射・両側逆・全斉次自然性・両向きの厳密自然変換と元の dg nerve 上の実関手同型まで構成した。T と id ⊕ T の native nerve は完全。
- 同じ入力の full dg cone の perfect 対象で零化する cell 分解後の実 Drinfeld 商を構成した。実商射影・安定性・β3 の実安定閉包からの Verdier 列と、固定 `PerfDGInput` への包装を保持する。元の β5 の Perf と安定閉包の同値 P は D-8 e が同じ I から構成し、その元の Perf の全頂点の零化も証明した。
- κ-compact 性は F2 の全共変 Hom による定義を使う。ordinary compact/perfect 比較では代用しない。小ささは選んだ代表系にだけ要求し、全加群圏には要求しない。可算直和の κ-compact 閉性は I の `countableClosed` に明示され、κ の記号だけから証明したとは扱わない。
- Ind I-2 e を固定 ν 値の Indω へ接続済み。交換を定理化した最終公開入口 `ind_stableCompactGeneration_unconditional`（15:21、f350dce62）を採用し、交換入力・有限全存在の追加仮定を除去した。K-6 は引き続き未供給。D 側の供給の仲介はコーディネータ。今回 D・Sp へ直接依頼していない。所有外のファイルは変更していない。
- NonConnective 集約・専用監査は交換入力の除去まで成功（145 モジュール・1694 宣言、標準三公理のみ、ModelCategory 宣言型検査を含む）。零 Perf 全族、分裂四角形の二胞体・四辺・零角、各ラベルの閉分裂関係を接続済み。点ごとの cofiber 性と同じ cone の K の実零頂点性は証明済み。構造射は未完。

### 残り（依存順）
1. 工程 c：構成した反復の対象別供給を、懸垂の全入力射に対する作用・整合性へ接続する。証明済みの同じ cone の連結 K の消滅を保持して、K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A) の構造射を作る（BGT Lem. 9.4・Def. 9.6、見積り未確定）。
2. 連結 K との比較と負次数の記述（BGT §9、Schlichting 2006、見積り未確定）。
3. 非連結化後の K^{nc} が Verdier 列を Sp fiber 列へ送ること、Morita 不変性、filtered 余極限との可換（K-6 と β3、BGT Thm. 9.8、Schlichting 2006 §7 Lem. 6、見積り未確定）。
4. 非連結化後の K^{nc} の Sp 相対版 `IsRelativeLocalizingInvariant` への登録（固定 dgKInputInfinity・dgKInputNu、元の dgKInputK は連結比較の始点のまま、K-5、見積り未確定）。
5. Ind の無条件安定性・compact 生成界面は接続済み。同じ非可算 κ の実 dg cone・I・P と元の全 native 作用を照合する（BGT §9.1、見積り未確定）。P は任意の I に対して実供給済み。I の実供給と全入力自然性は未完。

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
- D の09:57までの供給：候補 `objects := dgKappaClosedProjectiveObjects R D κ` に対する `small`・`projective`・`derivedFullyFaithful`、`countableClosed`・`binaryClosed`・`perfectCovers` の個別宣言あり。実零加群所属・shift/cone 閉性もあり、同じ候補に対する Z の材料となる。K-7 の I・P の実値には未接続。`uncountable`・`regular` は κ の明示条件。
- D の未供給：I の `kappaCompact`・`covers`・`pretriangulated`。前三角性は D の未統合試作にとどまり、本体供給として数えない。P の `comparison`・`isEquivalence`・`inclusion` は D-8 e が任意の同じ I から実供給済み。対象別反復供給 `DGSuspensionStageProvider` の存在・入力射作用と整合性は未証明。[宣言名と対応表](archive/L10-dg-kappa-inputs.md)。

### 公開界面の利用
- コーディネータ確認（10-24）：公開 `PresentedPerfectDGNativeLabel.lean` は読み取り専用 import が可能。`presentedPerfectDGNativeActionSimplex_label` と `presentedPerfectDGNativeAction_label_app` を利用し、全 native 分裂四角形の点ごとの評価を同じ閉ラベル作用へ照合する。供給依頼・分割は不要。禁止対象はコピーと他レーンの編集。

### 未コミット
- なし。`DGKappaSplitPerfEvaluation.lean` の小さい curry 評価公式・直接零角の型は解決し、既定 heartbeats のまま検証・集約・監査への接続済み。

### 既知の問題
- D-8 e は任意の I から P の完成した実値を供給した。`DGKappaPerfectSupply` は同じ I を保つ段入力・全段供給・実 Perf 同値・反復 BF 列へ代入し、既存の段供給の P を差し替えても元の反復 dg 対象が変わらないことを保持する。元の全高次懸垂作用を同じ全単体写像・頂点・実射・全一単体のまま移し、各段の全入力 K・native loop 族も厳密に保持する。`DGKappaPerfectSupplyComparison` は同じ実導来包含の充満忠実性から既存 P と実供給 P の全 native Perf 関手比較を戻し、元の包含同型を厳密に回収する。同じ I の P 選択比較は単位・合成則を満たす。元の厳密評価・実評価 Perf 同値・実構造射は P の選択に依存しない。`DGKappaResolvedKernelRepresentability` は同じ実評価 Morita 核と実供給 P から実小核上の全 perfect 加群の代表可能性・実核の dg 前三角性を証明する。`DGKappaResolvedKernelYoneda` はその前三角性と既存の native 冪等完備性を D 正本の Yoneda 完備化へ代入し、元の dg Yoneda 自身の native 同値を与える。対象ラベルの移送後も元の全単体写像を厳密回収する。`DGKappaResolvedYonedaEvaluation` は同じ実評価双加群への D 正本の tensor・Yoneda 比較と実出力分解を接続し、元の実 Perf Morita 作用を元の厳密評価へ全関手で照合する。任意の元の P の後の元の Yoneda は同じ実 Morita 逆作用と全関手同型で、指定余単位を厳密回収する。同じラベル評価で挟むと固定 ν の既存の実 Perf 同値へ戻る。`DGKappaSuspensionYonedaCompletion` は元の実平坦懸垂の dg 前三角性と、同じ元の dg Yoneda の native 冪等完備化性を D 正本から得る。完備化を同値・通常の局所化・K₀ 全射とは扱わない。実商と固定 ν の Perf 完備化の K 比較を分ける経路はユーザー採用済み（L3 末尾）。共終性は K-S• へ依頼済みで、届くまでは同じ命題を明示仮定引数に取る。`DGKappaSuspensionCofinality` は同じ実商の元の Yoneda 安定模型射・実 K 射に正次数同型と零次単射を代入し、同じ比較辺の一回 native loop の非負次数同型へ移す。`DGKappaConeCofinality` は元の実 Perf 評価を介して既存の同じ cone の K 零性を戻し、共終性の正次数単射・零次単射と負次数の連結性から完備化前の cone K の全整数群を自明とする。`DGKappaNativeConeResolution` は同じ cell 増大を含む native 同値で、この零性を D-9 の同じ実平坦源へ反映する。`DGKappaNativeKernelThick`・`DGKappaNativeVerdier` は同じ実核の本質像と商零化対象の一致を証明し、元の二射の Sp 認証と完備化前の全四角形提示を供給する。`DGKappaNativeFibration` は同じ相対 S• fiber 比較と包含射影を実列へ接続する。実商 fiber への比較は既存の正段比較に条件付きで、固定 K の非負次数 fiber 比較・全入力自然性の完成は主張しない。I の実例と異なる dg 入力間の全自然性・反復整合は未供給。未供給型一覧はコーディネータの仲介用であり、K-7 からの直接メッセージ送信はしていない。
- b の Verdier 列の左項は選んだ perfect 対象の実安定閉包。元の β5 の Perf と同一視する際は P の全写像空間の同値と包含の全関手比較を必ず使う。ordinary 導来圏での `perfectCovers` だけからは推論しない。
- 同じ cone の K の消滅は接続済み。K-6 の canonical fiber 比較から固定 native loop への実構造比較は、下記の未供給の相対屋根入力に対して構成した。F2N-5・非連結 K 本体は未接続。一般の安定 ∞ 圏上の K は作らない。
- D-9 の native `IsStableVerdierSequence` と、固定 ν（Perf 値）の `IsVerdierSequence` は異なる証拠。前者の実供給から後者や Perf 零角の零性を無条件に推論しない。
- a の以前の end 持ち上げ余錐は保持するが、完成界面は `sequentialCandidateColimitCocone`。通常の Hom 極限性だけでは ∞ 余極限性の代用にならない。

### 次の一手
- c1〜c3 完了。元の全四角形を cofiber 図式の全部分圏へ全単体で持ち上げ、四評価を同じ dg 作用に回収して完全関手に束ねた。`connectedKMiddle_additivity` と `dgKappaSwindleFixedK_pi` は同じ SOA 群比較を介して接続し、実 Sp の零頂点性を得た。I・Z の存在は明示入力のまま。P は同じ I から D-8 e が構成する。
- c4：同じ平坦分解の増大と商包含を固定 dg K の厳密二脚として保持し、増大の K 像の可逆性・平坦 cone の K の零性を証明した。`DGKappaSuspensionMapData` から同じ懸垂入力射と K 屋根の両可換四角形を得る。D 正本の `comparisonFunctor` により、perfect を保つ cone 射を同じ増大可換な平坦射へ持ち上げる。同じ明示 `DGKappaSuspensionMapData` に対する懸垂入力射の恒等・合成・元の ε の保存は、D 正本の指定収縮付き商普遍性を特殊化して証明した（`DGKappaSuspensionInputLaws`）。同じ固定 K の実 spectrum 射にも厳密な恒等・合成を接続した（`DGKappaSuspensionKMapLaws`）。一般の商関手則を K-B 内に新設していない。`DGSuspensionIterationMaps` は明示射作用とその厳密恒等・合成則に条件付きで、元の入力射を同じ全反復段へ送り、同じ固定 K の実 BF 射の恒等・合成も保持する。canonical `comparisonFunctor` の恒等・合成、元の dg 入力射からの cone 作用と全整合性は未供給で、単独の増大可換四角形で代用しない。


- c5：一般経路の `DGKappaResolvedConnectiveSquare` は D-9 の同じ実核・分解 cone・懸垂・元の商辺を、Sp-6 の固定零化構成子で保持する。ν の Verdier 認証 `hV` は使わない。零角の Perf 零性から元の K 零角を得て、`DGConnectiveFiberComparison` の同じ実 fiber 比較を `DGKappaSuspensionConnectiveLoop` の loop 四角形へ送る。`DGKappaSuspensionConnectiveStructure` は元の全比較辺から native loop への実構造射を回収し、指定次数の全単射性を元の実 fiber 比較と同値にする。`DGKappaResolvedConnectiveMap` は指定された元の Perf と同じ実核の全関手同値に条件付きで、同じ SOA 比較から K(D) 始点へ戻す。`DGSuspensionConnectiveSequence` は同じ実構造射を持つ BF 列と、その同じ候補上の実 Sp 余極限を構成する。`DGKappaResolvedNullPerf` は同じ実零角の固定 ν 値の零性を証明し、零角の追加仮定を除去した。`DGSuspensionResolvedConnectiveSequence` はこの実供給を全段へ代入し、同じ BF 列・実 Sp 余極限・元の K(A) からの実余錐の脚を保持する。段別 I・P・Z、指定 Perf 同値の P 照合・全入力自然性・非負次数安定化の供給は未完。元の K 四角形の Sp 引き戻し性は入力しない。以前の明示相対屋根の利用側と条件付き Sp fiber 判定は保持する。


### c5 の供給境界（採用済み、2026-10-25）
- I は cone の dg 小模型、P は元の Perf とその perfect 安定閉包の全関手比較を供給するが、固定 `dgKInputInfinity` 内の実相対 Verdier 四角形まではフィールドに含まない。同じ商は平坦分解を介する屋根であり、未供給の厳密 Cone→Σ 射を仮定しない。
- 採用：I・P の型を変えず、`DGKappaSuspensionRelativeRoofInput` を別の明示供給境界とする。実小 dg 核、同じ平坦 cone・同じ Σ を頂点とする固定 ν の `RelativeVerdierDiagram`、右辺が元の `dgKappaResolvedSuspensionInputMap` の全一単体である厳密一致を要求する。この型の存在は主張しない。
- D-9 の `resolvedDGQuotientFlatKernel` を `dgKappaResolvedKernelKInput` に包装し、元の包含・局所 Hom K-平坦性を保持した。同じ native Verdier 列の全頂点零化と D 正本の収縮取得を使い、Sp-6 の固定零化構成子へ接続した。指定収縮の追加仮定は不要。`dgKappaResolvedRelativeRoof` は固定 ν の元の二射の Verdier 証拠 `hV` と、実全対象商の Perf 零性 `hz` に条件付きで、同じ実核・包含・商辺を保持する。実全対象商の Perf 零性 `hz` は `dgKappaResolvedNullPerf_isZero` で実供給済み。残る固定 ν の Verdier 証拠 `hV` と、Perf 完備化・P の照合の存在は主張しない。一般商・局所化 API は新設しない。
- 条件付きの利用側は実装・検証済み。相対屋根入力だけから同じ核 K→固定 native loop K(Σ) の実 BF 射・元の全比較辺・実合成二胞体を得る。元の K 四角形の引き戻し性、入力の存在、P との照合、全入力射に自然な反復整合性、`K^{nc}` の完成は含めない。


### 仮定入力の一覧（refactoring-infinity.md §6 と同形式）

入力型そのものの定義行・import 行を除く一致行数。存在は主張しない。I・P とは別の明示供給境界。

| 名前 | 所在（SerrePositivity/ 以下） | 供給元 | 使用（一致行／ファイル） |
|---|---|---|---|
| `hcofinal`（ユーザー採用、明示定理引数） | KST/NonConnective/DGKappaSuspensionCofinality.lean | K-S•：Yoneda 完備化の正次数 π 同型・零次 π 単射。K-B：同じ実商への代入・同じ cone の K 零性・実 fiber 比較への接続 | 集計対象外（定理引数） |
| `DGKappaSuspensionRelativeRoofInput` | KST/NonConnective/DGKappaSuspensionRelativeRoofInput.lean:32 | 実小 dg 核・平坦屋根：D-9。固定 ν の相対 Verdier 四角形・Sp 接続：Sp-6。元の Perf・P との照合：K-B | 19／7 |
| `DGSuspensionNativeActionInput`（採用（03:55）） | KST/NonConnective/DGSuspensionNativeActionInput.lean:25 | D-8 e（供給仕様拡張を採用、未供給）：同じ実核・cone・零角・懸垂の全四角形族と、実評価 Morita 比較・元の P の包含の全 native Hom 自然性。K-B：固定 S・ν・K での照合。供給路：PerfDGInput 上の厳密 SSet 豊穣自己関手の coherentNerveMap。D への伝達は c′ 試作の判定後 | 11／2 |

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
- 供給分担：K-B が全単体的作用と頂点・辺の照合を組み立てる。供給路は **PerfDGInput 上の厳密 SSet 豊穣自己関手の coherentNerveMap**。D-8 e の供給仕様は下記の全四角形族・実評価 Morita 比較・元の P の包含の全 native Hom 自然性へ拡張済み（未供給、c′ 試作判定後にコーディネータが伝達）。対象別の `covers` による代表選択から厳密・高次の自然性を推論しない。この境界は I・P・実相対屋根とは別であり、存在・実供給は主張しない。評価待ちで停止せず K-6 c4・c5 と K-7 d を進める。

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
- `DGSuspensionNativeActionInput` の D-8 e 供給仕様として記録する。現行 Lean 型は全四角形族をまだ表さず、仕様充足・完成とは数えない。I・P・固定 S・ν・K を変更せず、存在も主張しない。D への伝達はコーディネータが c′ 試作の判定（20:11）後に行う。
- `DGSuspensionNativeSquareFamily` は同じ採用済み全族と元の各実四角形への厳密一致を受ける条件付き利用側。全 native 関手空間表示から元の全族・固定 K 像を厳密回収し、各角・包含・商辺と全反復段を元の同じ実四角形へ照合する。`DGSuspensionNativeActionInput.ofSquareFamily` は元の dg 射データ・辺照合を併せて受け、懸垂角を既存の全高次反復へ渡す。`DGSuspensionNativeStageFamily` は採用済みの明示全高次懸垂作用から各段の全入力 K・native loop 族を構成し、元の BF 頂点・全一単体・零段の固定 K・次段再帰を厳密回収する。入力射の厳密恒等・合成則の追加入力は使わないが、段間 β の自然性は含めない。全族・実評価 Morita 比較・P 包含の全入力自然性の供給は未完で、境界の完成とは数えない。

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
