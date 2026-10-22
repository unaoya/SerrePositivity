# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 1 完了：K-7 内で任意の厳密な逐次 BF 列の実 Sp 余極限を構成した。元の列の段ごとの余極限の構造射が単射であることを証明し、実 BF 対象・厳密余錐・全反変 Raw Hom の通常極限を構成。通常の極限性だけから ∞ 余極限性を結論していない。
- 任意の BF 射を相対 latching 単射と段ごとの自明 Kan fibration に実分解し、相対 cofibrant な逐次置換列と元の列への全整数 π 同型な厳密比較自然変換を構成した。全 Raw Hom の前合成が実 Kan fibration であることを証明し、既存の塔の定理で置換列の ∞ 余極限性を判定。余錐全体の成分を保った関手同型で、元の段ごとの厳密余錐の `IsColimitCone` へ戻した。
- `sequentialCandidateColimitCocone` は既存 `filteredOmegaSpectrum` と同じ BF 候補を頂点とする実余錐。`IsColimitCone` と頂点の厳密な等号を保持する。元の BF 射影そのものを coslice の可逆辺として終点から持ち上げた。
- 同じ実余錐の各辺は、既存 `filteredSpectrumInjection` の辺と hSp で等しい。coherent Hom 比較の π₀ 単射性で、実辺から読み戻した BF 射の全整数 π 作用も一致することを証明。実辺の群 cocone の余極限性と既存 `filteredSpectrumHomotopyIso` の各注入の式を接続した。
- 元の下限以降での表示、後の段での等号・単位元判定、元ごとの消滅、安定範囲での全単射性も保持する。dg 懸垂列そのものの安定化は未証明。
- Spectra・SConstruction・LocalizingInvariants・Fibration・Derived・F2 の変更なし。追加 API の Sp への依頼なし。集約ビルド成功（5365 jobs）、専用監査成功（35 モジュール・310 宣言、許容三公理のみ）。所有ソースに `sorry`・`axiom`・`ModelCategory` 等の仮定なし。

### 残り（依存順）
1. dg 懸垂：Σ(Perf A) := D(A) の κ-compact 対象の小さい充満 dg 模型を Perf(A) で割った Drinfeld 商。κ は非可算正則。β3・β5 と F1 の Ind・F2N-5 との照合（BGT Def. 9.1・Lem. 9.4、必要 dg API は D に依頼済み、提供見積り未確定）。
2. K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A) の厳密 dg 入力での構成（BGT Def. 9.6、dg 懸垂の供給後、見積り未確定）。
3. 連結 K との比較と負次数の記述（BGT §9、Schlichting 2006、見積り未確定）。
4. Verdier 列を fiber 列へ送ること、Morita 不変性、filtered 余極限との可換（K-6 と β3、BGT Thm. 9.8、Schlichting 2006 §7 Lem. 6、見積り未確定）。
5. Sp の相対版 `IsRelativeLocalizingInvariant` への登録（固定 dgKInputInfinity・dgKInputNu・dgKInputK、K-5、見積り未確定）。

### 主要宣言
- `SequentialIndex`、`SpectrumSequence`、`sequentialSpectrum`、`sequentialInjection`。
- `sequentialCandidateColimitCocone`、`sequentialCandidateColimitCocone_isColimit`、`sequentialCandidateColimitCocone_vertex`。
- `sequentialCandidateColimitLeg`、`sequentialCandidateColimitLegHom`、`sequentialCandidateColimitLeg_hom_eq`、`sequentialCandidateColimitLeg_pi`。
- `sequentialCandidatePiCoconeIsColimit`、`sequentialCandidateColimitHomotopyIso_ι`。
- `sequentialSpColimitCocone_isColimit`、`sequentialLevelColimitIsColimit`、`sequentialLevelColimitHomotopyIso_ι`。
- `sequentialDiagramReplacementComparison_piIsomorphism`、`sequentialRawHomPre_fibration`、`sequentialRawHomIsLimit`。
- `sequentialPiCoconeIsColimit`、`sequentialPiUnderlyingIsColimit`、`sequentialPi_exists_late`、`sequentialPi_eq_iff`、`sequentialPi_eq_one_iff`。
- `sequentialPi_subsingleton_iff`、`sequentialPi_subsingleton_of_eventually`、`sequentialInjection_bijective_of_stable`、`sequentialInjection_bijective_on`、`sequentialInjection_isInvertible_of_stable`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供：厳密な逐次 BF 列の同じ BF 候補を頂点とする実 Sp 余極限・実辺の整数 π 比較。一般 coherent 列の整流を仮定してはいない。

### 未コミット
- なし（本レーンの工程 1 の全追加モジュール、集約、専用監査、本計画を検証して保存）。共有作業木の他レーンの変更は対象外。

### 既知の問題
- 以前の end の持ち上げによる `sequentialCoherentCocone` は保持するが、その余錐自体の普遍性は主経路に使わない。工程 1 の完成界面は `sequentialCandidateColimitCocone`。頂点は既存候補と同一で、実辺の π 比較もこちらで証明した。
- K-6・F2N-5 と dg 懸垂は未接続。必要時は明示の仮定入力に隔離し、提供後に差し替える。未証明の仮定を完成扱いせず、一般の安定 ∞ 圏上の K は作らない。
- D の `DGModuleCompactEquivalence` は通常の compact／perfect 比較であり、非可算 κ の compact 模型を供給しない。`ResolvedDGQuotientVerdierSequence` は小さい前三角 dg 圏と部分集合からの商を供給するが、κ-compact 模型自体・小ささ・包含・反復の射作用は別に必要。D に依頼済み。

### 次の一手
- D の供給を確認して、工程 2 の非可算正則 κ に対する dg cone と Drinfeld 懸垂の入力界面を組む。同じ small dg 模型・包含・可算直和と swindle・反復の射作用を保持し、通常の perfect 比較と取り違えない。F2N-5 と K-6 が未提供なら対応する主張を明示入力として管理する。

## 原典との照合・受入条件
- [BGT 2013 §9.1、Def. 9.1・Lem. 9.4・Prop. 9.5・Def. 9.6・Lem. 9.7](https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf) を基準とする。一般安定 ∞ 圏での構成は参照先の主張であり、本レーンでは厳密 dg 供給に限定する。
- cone は `(Indω C)^κ`。通常の compact 対象だけに置き換えない。非可算正則 κ のもとで可算余積と swindle `id ⊕ T ≃ T` を使い、同じ dg cone の連結 K が消えることを証明してから構造射を作る（Lem. 9.4）。D へは可算直和の dg 作用と加法性に渡す整合性も依頼した。
- dg cone・懸垂の完全列保存（Prop. 9.5）と全入力射での整合性を、対象別の商の存在と区別する。`PerfDGInput` は小さい dg 圏を受け取るため、元の商の smallness の証拠と固定 K への入力を保持する。
- Lem. 9.7 は κ-filtered 余極限の保存。工程 5 の通常 filtered 余極限保存には別の証明が必要で、両者を同一視しない（BGT Thm. 9.8 の証明末尾は Schlichting 2006 §7 Lem. 6 を別に参照する）。
- 工程 1 の受入には、同じ BF 候補を頂点とする実 Sp cocone、その `IsColimitCone`、実 cocone の各辺と既存整数 π 比較の整合が必要。群の `IsColimit` のみでは未達。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。工程 1 の逐次実 cocone と ∞ 余極限性は K-7 所有で自前構成（10-23 コーディネータ指示）。
