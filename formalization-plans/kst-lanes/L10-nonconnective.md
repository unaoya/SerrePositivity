# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 1 進行中。既存 `filteredOmegaSpectrum` と同じ BF 候補を頂点とする実 `sequentialCoherentCocone` と頂点の厳密な等号を K-7 内で構成した。反変 Raw Hom 図式の BF 射影が成分ごとに自明 Kan fibration であることを end 全体へ移し、段ごとの余極限注入の整合した点を持ち上げた。射影で元の点を厳密に回収する。反対圏の coherent 錐から元の図式・Sp に戻している。Spectra の変更なし。
- 段ごとの filtered Kan 余極限の構造射も単射であることを証明し、置換前の BF 対象・厳密余錐・通常の BF 圏の `IsColimit` を構成した。既存 BF 置換からこの対象への同じ射影は全整数 π 同型。
- 各スペクトル段の反変 Hom 錐の通常の極限性、全 Raw Hom 図式の段評価の自然変換、任意の厳密錐からの一段の普遍 Hom 族と各入力への制限式まで構成した。全スペクトルの Hom–end 比較とその同値性は未証明。
- 既存 `filteredSpectrumHomotopyIso`・`filteredSpectrumInjection` を再利用する群 cocone とその `IsColimit`、台集合の余極限性は保持する。実 coherent 余錐の各脚との整数 π 比較は未接続。
- 任意の下限以降での元の表示、後の段での等号・単位元判定、元ごとの消滅と候補の π の消滅の同値、安定範囲での注入の全単射性、全整数安定化を仮定した元の Sp 辺の可逆性を証明した。dg 懸垂列の安定化そのものは未証明。
- 対象・集約ビルド成功（5209 jobs）、専用監査成功（9 モジュール・87 宣言、許容三公理のみ）。所有ソースに `sorry`・`axiom`・`ModelCategory` 等の仮定なし。

### 残り（依存順）
1. Sp の逐次余極限：実 Sp cocone は K-7 内で構成済み。残りは同じ余錐の `IsColimitCone` と実際の脚への整数 π 比較（BF 1978 §2、HTT 4.2.4.1、BGT §9、見積り未確定）。通常の `IsColimit` や π 自然性だけでは代用しない。10-23 コーディネータ指示により K-7 が `NonConnective/` 内で証明する。Sp の既存 API は読み取り専用とし、Spectra 自体の変更が必要な場合に限り Sp に依頼する。
2. dg 懸垂：Σ(Perf A) := D(A) の κ-compact 対象の小さい充満 dg 模型を Perf(A) で割った Drinfeld 商（β3・β5）。κ は非可算正則。F1 の Ind と F2N-5（Ind の安定性）との照合。必要 dg API は D に依頼済み（提供見積り未確定）。
3. 非連結 K スペクトル K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A)（BGT Def. 9.6 相当）。K-3 の連結 K を入力とする。
4. 連結 K との比較：非負次数で K^{nc} ≃ K、負次数の記述（BGT 9.? と Schlichting）。
5. Verdier 列を fiber 列に送ること（K-6 と β3 の Verdier 列）、Morita 不変性、filtered 余極限との可換。
6. Sp の相対版 `IsRelativeLocalizingInvariant`（ν : S ⟶ StableInfinity、K-S• の固定界面）としての登録。

### 主要宣言
- `SequentialIndex`、`SpectrumSequence`、`sequentialSpectrum`、`sequentialInjection`。
- `sequentialPiCocone`、`sequentialPiCoconeIsColimit`、`sequentialPiUnderlyingIsColimit`。
- `sequentialPi_exists_late`、`sequentialPi_eq_iff`、`sequentialPi_eq_one_iff`、`sequentialPi_subsingleton_iff`、`sequentialPi_subsingleton_of_eventually`。
- `sequentialInjection_bijective_of_stable`、`sequentialInjection_bijective_on`、`sequentialInjection_isInvertible_of_stable`。

- `sequentialRawHomDiagram`、`sequentialRawInjectionCone`、`sequentialReflectedEndSectionData`、`sequentialReflectedBFInjectionPoint_projection`。
- `sequentialCoherentOppositeCone`、`sequentialCoherentCocone`、`sequentialCoherentCocone_vertex`。
- `sequentialKanSequence_sigma_mono`、`sequentialLevelColimitSpectrum`、`sequentialLevelColimitCocone`、`sequentialLevelColimitIsColimit`、`sequentialReplacementProjection_piIsomorphism`。
- `sequentialLevelHomIsLimit`、`sequentialRawHomEvaluation`、`sequentialHomLimitFamily`、`sequentialHomLimitFamily_fac`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供先：K-基盤 1・2 の完成形（K が局所化不変量）、第 II 段の pro 切除の適用。

### 未コミット
- なし（本レーンの集約・新規6モジュール・既存1モジュールの説明・専用監査・本計画を検証して保存）。共有作業木の他レーンの変更は対象外。

### 既知の問題
- 工程 1 は未完。実 cocone と ∞ 余極限性は K-7 の担当（10-23 コーディネータ指示）。`filteredSpectrumInjection` の選択は BF 射として厳密自然とは主張されていない。新しい実余錐は end 全体の持ち上げで構成した。π の群 cocone、通常の BF 余極限、実 Sp 余錐の ∞ 余極限性を同一視しない。
- K-6・F2N-5 と dg 懸垂は未接続。F1 の現状は零対象と有限 Yoneda 図式の比較までで、Ind の安定性・compact 比較は未証明。後続工程で必要な場合は明示の入力に隔離し、完成扱いしない。一般の安定 ∞ 圏上の K は作らない。
- D の `DGModuleCompactEquivalence` は通常の compact／perfect 比較であり、非可算 κ の compact 模型を供給しない。`ResolvedDGQuotientVerdierSequence` は小さい前三角 dg 圏と部分集合からの商を供給するが、κ-compact 模型自体・その小ささ・包含・反復の射作用は別に必要。D に依頼済み。

### 次の一手
- `sequentialHomLimitFamily` の構造射との整合性を示し、全 Raw Hom の厳密極限比較へ束ねる。次に逐次図式の homotopy Hom–end 比較とその同値性を実証し、実 `sequentialCoherentOppositeCone` の全パラメータの族を `coherentCone_isLimit_of_family_lifts` へ接続して双対化する。通常の Hom 極限が Kan であることだけから BK end との同値を結論しない。実余錐の各脚と同じ整数 π cocone の整合も照合する。

## 原典との照合・受入条件
- [BGT 2013 §9.1、Def. 9.1・Lem. 9.4・Prop. 9.5・Def. 9.6・Lem. 9.7](https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf) を基準とする。一般安定 ∞ 圏での構成は参照先の主張であり、本レーンでは厳密 dg 供給に限定する。
- cone は `(Indω C)^κ`。通常の compact 対象だけに置き換えない。非可算正則 κ のもとで可算余積と swindle `id ⊕ T ≃ T` を使い、同じ dg cone の連結 K が消えることを証明してから構造射を作る（Lem. 9.4）。D へは可算直和の dg 作用と加法性に渡す整合性も依頼した。
- dg cone・懸垂の完全列保存（Prop. 9.5）と全入力射での整合性を、対象別の商の存在と区別する。`PerfDGInput` は小さい dg 圏を受け取るため、元の商の smallness の証拠と固定 K への入力を保持する。
- Lem. 9.7 は κ-filtered 余極限の保存。工程 5 の通常 filtered 余極限保存には別の証明が必要で、両者を同一視しない（BGT Thm. 9.8 の証明末尾は Schlichting 2006 §7 Lem. 6 を別に参照する）。
- 工程 1 の受入には、同じ BF 候補を頂点とする実 Sp cocone、その `IsColimitCone`、実 cocone の各辺と既存整数 π 比較の整合が必要。群の `IsColimit` のみでは未達。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。工程 1 の逐次実 cocone と ∞ 余極限性は K-7 所有で自前構成（10-23 コーディネータ指示）。
