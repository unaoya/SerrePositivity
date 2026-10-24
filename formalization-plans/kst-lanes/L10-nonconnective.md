# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v3（2026-10-24）**：K-7 は **K-B レーン**に統合（正本は L3-fibration.md、本ファイルは K-7 の引き継ぎ）。I・P の実供給は D-8 として D が担当。

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-24）

### 現在地
- 上流 import 閉包の復旧と両所有集約の再ビルドを確認。`DGKappaSplitPerfEvaluation` を検証し、集約・監査へ接続済み。元の全 native 関手族と同じ実四角形の全単体を、元の各 Perf ラベルの dg 作用へ照合し、同じ点ごとの零三角形を構成した。D-12 の公開判定により同じ二胞体の cofiber 普遍性を証明し、同じ cone の連結 K・固定 K の実 Sp 零頂点性まで接続済み。
- 工程 a 完了：任意の厳密な逐次 BF 列の実 Sp 余極限を K-7 内で構成。同じ `filteredOmegaSpectrum` を頂点とする `sequentialCandidateColimitCocone` の `IsColimitCone` と、実辺の全整数 π 作用・群余極限比較を接続済み。
- 工程 b の明示入力版完了：β5 の実半自由 D(D)・Perf と β3 の平坦分解後の Drinfeld 商を読み取り専用で使用。未供給の非可算正則 κ の dg 小模型を `DGKappaConeInput`、元の Perf との全関手比較を `DGKappaPerfectInput` として明示した。[未供給宣言の名前・型一覧](archive/L10-dg-kappa-inputs.md)。両入力の存在は未証明。
- 工程 c 進行中：同じ κ と同じ供給 s を保つ反復 `dgSuspensionIteration` を構成。実 swindle を dg 関手圏の閉同型・元の native Kan Hom の実辺へ束ね、固定 `dgKInputK` の同じ二つの実 BF 自己射の全整数 π 作用の等号 `dgKappaSwindleFixedK_pi` まで接続した。同じ全 cofiber 族の完全性と三評価の実加法性を用い、同じ SOA 群比較を介して元の固定 K と連結 K の実 Sp 零頂点性を証明した。
- K-S• の既存の正反復実現の加法性から、同じ全零境界商 Kan 射対の局所化可逆性・全基点 π 同型を K-7 内で証明した。実標準軸の零関手・恒等関手の評価と群の二軸分解から一重境界商の中央項の正次数群上の加法公式を導き、元の同じ連結 BF K の全整数 π 上の加法性 `connectedKMiddle_additivity` へ移した。非負整数群と一重境界商の群の比較は元の射に自然。非連結 K の定義を一般安定入力へ拡張していない。同じ Perf 上の実分裂 cofiber 族と、その完全性・元の三評価へ接続済み。
- 同じ実二項 dg 直和の両注入・両射影を、全斉次自然変換と全 dg 関手 Hom end の実閉射に保持した。同じ Hom end 内の四合成・恒等分解を証明した。非 replete な I に実零加群そのものが入る証拠は、別の追加所属入力 `DGKappaZeroInput` として隔離し、その証拠に対する実零 dg 自己関手と閉関手圏での零対象性を構成した。I・P の型・存在を変更したり、その所属を前三角性から推論したりしない。[追加型](archive/L10-dg-kappa-inputs.md)。
- 零自己関手の各 Perf ラベルでの閉零対象性・native 零頂点性、全 native dg 関手パラメータの Perf 作用と固定関手の照合、非可逆閉射の実 Perf 自然変換、同じ注入・射影・零関手の二単体を貼った `dgKappaSplitPerfFamilySquare` まで構成。同じ上・下二胞体、四辺、全関手空間の実零角を回収し、`dgKappaSplitPerfZeroTriangle` に束ねた。各 Perf ラベルでの同じ閉注入・射影の四合成と恒等分解も接続済み。点ごとの cofiber 性・同じ全族の完全性・固定 K への加法性と swindle による実零頂点性は接続済み。
- 実 dg 加群の全 Hom end の余積普遍性から可算直和の chain map を構成し、単位・豊穣合成・射影性の保存を証明した。同じ cone 上の厳密 dg 自己関手 T と id ⊕ T を構成。swindle は入力に仮定せず、指定した閉 dg 射・両側逆・全斉次自然性・両向きの厳密自然変換と元の dg nerve 上の実関手同型まで構成した。T と id ⊕ T の native nerve は完全。
- 同じ入力の full dg cone の perfect 対象で零化する cell 分解後の実 Drinfeld 商を構成した。実商射影・安定性・β3 の実安定閉包からの Verdier 列と、固定 `PerfDGInput` への包装を保持する。元の β5 の Perf と安定閉包の同値は P の明示入力で、その元の Perf の全頂点の零化も証明した。
- κ-compact 性は F2 の全共変 Hom による定義を使う。ordinary compact/perfect 比較では代用しない。小ささは選んだ代表系にだけ要求し、全加群圏には要求しない。可算直和の κ-compact 閉性は I の `countableClosed` に明示され、κ の記号だけから証明したとは扱わない。
- F1 の Ind 安定性・K-6 は入力せず、待機もしていない。D 側の供給の仲介はコーディネータ。今回 D・Sp へ直接依頼していない。所有外のファイルは変更していない。
- NonConnective 集約・専用監査は成功（87 モジュール・933 宣言、標準三公理のみ、ModelCategory 宣言型検査を含む）。零 Perf 全族、分裂四角形の二胞体・四辺・零角、各ラベルの閉分裂関係を接続済み。点ごとの cofiber 性と同じ cone の K の実零頂点性は証明済み。構造射は未完。

### 残り（依存順）
1. 工程 c：構成した反復の対象別供給を、懸垂の全入力射に対する作用・整合性へ接続する。証明済みの同じ cone の連結 K の消滅を保持して、K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A) の構造射を作る（BGT Lem. 9.4・Def. 9.6、見積り未確定）。
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
- `dgKappaZeroPerfAction_isZeroVertex`、`dgKappaFullPerfFamilyMap_vertex`、`dgKappaPerfClosedHomotopy`、`dgKappaSplitPerfFamilySquare`、`dgKappaZeroPerfAction_values`、`dgKappaZeroPerfFunctorVertex_isZero`、`dgKappaFullPerfZeroVertex_isZero`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供：厳密な逐次 BF 列の同じ BF 候補を頂点とする実 Sp 余極限・実辺の整数 π 比較。一般 coherent 列の整流を仮定してはいない。
- D の09:57までの供給：候補 `objects := dgKappaClosedProjectiveObjects R D κ` に対する `small`・`projective`・`derivedFullyFaithful`、`countableClosed`・`binaryClosed`・`perfectCovers` の個別宣言あり。実零加群所属・shift/cone 閉性もあり、同じ候補に対する Z の材料となる。K-7 の I・P の実値には未接続。`uncountable`・`regular` は κ の明示条件。
- D の未供給：I の `kappaCompact`・`covers`・`pretriangulated`。前三角性は D の未統合試作にとどまり、本体供給として数えない。P の `comparison`・`isEquivalence`・`inclusion` も未供給。対象別反復供給 `DGSuspensionStageProvider` の存在・入力射作用と整合性は未証明。[宣言名と対応表](archive/L10-dg-kappa-inputs.md)。

### 公開界面の利用
- コーディネータ確認（10-24）：公開 `PresentedPerfectDGNativeLabel.lean` は読み取り専用 import が可能。`presentedPerfectDGNativeActionSimplex_label` と `presentedPerfectDGNativeAction_label_app` を利用し、全 native 分裂四角形の点ごとの評価を同じ閉ラベル作用へ照合する。供給依頼・分割は不要。禁止対象はコピーと他レーンの編集。

### 未コミット
- なし。`DGKappaSplitPerfEvaluation.lean` の小さい curry 評価公式・直接零角の型は解決し、既定 heartbeats のまま検証・集約・監査への接続済み。

### 既知の問題
- D は上記の個別フィールドを供給したが、I・P の完成した実値は未提供。両構造の存在、選択独立性・全入力射での反復の整合性は証明済みと扱わない。未供給型一覧はコーディネータの仲介用であり、K-7 からの直接メッセージ送信はしていない。
- b の Verdier 列の左項は選んだ perfect 対象の実安定閉包。元の β5 の Perf と同一視する際は P の全写像空間の同値と包含の全関手比較を必ず使う。ordinary 導来圏での `perfectCovers` だけからは推論しない。
- K-6・F2N-5・K の消滅・非連結 K 本体は未接続。必要時は対応する主張を明示入力に隔離し、提供後に差し替える。一般の安定 ∞ 圏上の K は作らない。
- a の以前の end 持ち上げ余錐は保持するが、完成界面は `sequentialCandidateColimitCocone`。通常の Hom 極限性だけでは ∞ 余極限性の代用にならない。

### 次の一手
- c1〜c3 完了。元の全四角形を cofiber 図式の全部分圏へ全単体で持ち上げ、四評価を同じ dg 作用に回収して完全関手に束ねた。`connectedKMiddle_additivity` と `dgKappaSwindleFixedK_pi` は同じ SOA 群比較を介して接続し、実 Sp の零頂点性を得た。I・P・Z の存在は明示入力のまま。
- c4：同じ平坦分解の増大と商包含を固定 dg K の厳密二脚として保持し、増大の K 像の可逆性・平坦 cone の K の零性を証明した。`DGKappaSuspensionMapData` から同じ懸垂入力射と K 屋根の両可換四角形を得る。D 正本の `comparisonFunctor` により、perfect を保つ cone 射を同じ増大可換な平坦射へ持ち上げる。同じ明示 `DGKappaSuspensionMapData` に対する懸垂入力射の恒等・合成・元の ε の保存は、D 正本の指定収縮付き商普遍性を特殊化して証明した（`DGKappaSuspensionInputLaws`）。同じ固定 K の実 spectrum 射にも厳密な恒等・合成を接続した（`DGKappaSuspensionKMapLaws`）。一般の商関手則を K-B 内に新設していない。canonical `comparisonFunctor` の恒等・合成、元の dg 入力射からの cone 作用と全整合性は未供給で、単独の増大可換四角形で代用しない。

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

## 原典との照合・受入条件
- [BGT 2013 §9.1、Def. 9.1・Lem. 9.4・Prop. 9.5・Def. 9.6・Lem. 9.7](https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf) を基準とする。一般安定 ∞ 圏での構成は参照先の主張であり、本レーンでは厳密 dg 供給に限定する。
- cone は `(Indω C)^κ`。通常の compact 対象だけに置き換えない。非可算正則 κ のもとで可算余積と swindle `id ⊕ T ≃ T` を使い、同じ dg cone の連結 K が消えることを証明してから構造射を作る（Lem. 9.4）。可算直和の dg 作用と swindle は K-7 内で構成した。未供給の小模型と Perf 比較はコーディネータが仲介する。
- dg cone・懸垂の完全列保存（Prop. 9.5）と全入力射での整合性を、対象別の商の存在と区別する。`PerfDGInput` は小さい dg 圏を受け取るため、元の商の smallness の証拠と固定 K への入力を保持する。
- Lem. 9.7 は κ-filtered 余極限の保存。工程 5 の通常 filtered 余極限保存には別の証明が必要で、両者を同一視しない（BGT Thm. 9.8 の証明末尾は Schlichting 2006 §7 Lem. 6 を別に参照する）。
- 工程 1 の受入には、同じ BF 候補を頂点とする実 Sp cocone、その `IsColimitCone`、実 cocone の各辺と既存整数 π 比較の整合が必要。群の `IsColimit` のみでは未達。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。工程 1 の逐次実 cocone と ∞ 余極限性は K-7 所有で自前構成（10-23 コーディネータ指示）。
