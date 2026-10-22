# K-7 レーン：非連結 K（dg 形、BGT §9）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §6 の K-7。K-S• の連結 K（厳密 dg 入力、K-3・K-4）、Sp の値域界面と相対版局所化不変量（K-5）、
> D の β3（Drinfeld 商）・β5（D(A)・Perf(A)）、K-F の K-6（fibration 定理）、F1 の Ind と F2N-5 を読み取り専用で使い、非連結 K を dg 入力で構成する。
> 一般の安定 ∞ 圏上の非連結 K は作らない（主経路は厳密 dg 入力限定）。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 1 進行中。Sp の既存 `filteredOmegaSpectrum`・`filteredSpectrumHomotopyIso`・`filteredSpectrumInjection` を再利用し、同じ宇宙の逐次 BF 候補を公開した。選択した注入の整数 π を脚とする群 cocone とその `IsColimit`、台集合の余極限性を構成した。
- 任意の下限以降での元の表示、後の段での等号・単位元判定、元ごとの消滅と候補の π の消滅の同値、安定範囲での注入の全単射性、全整数安定化を仮定した元の Sp 辺の可逆性を証明した。dg 懸垂列の安定化そのものは未証明。
- 対象・集約ビルド成功（5089 jobs）、専用監査成功（3 モジュール・21 宣言、許容三公理のみ）。所有ソースに `sorry`・`axiom`・`ModelCategory` 等の仮定なし。

### 残り（依存順）
1. Sp の逐次余極限：BF 対象候補と全整数 π の比較は既存 Sp API で供給済み。残りは同じ候補を頂点とする高次整合つき実 Sp cocone と `IsColimitCone`（BF 1978 §2・BGT §9、Sp 側の見積り未確定）。選択した厳密注入の π 自然性だけでは代用しない。Sp に依頼済み・受領確認済み、供給待ち。
2. dg 懸垂：Σ(Perf A) := D(A) の κ-compact 対象の充満 dg 部分圏を Perf(A) で割った Drinfeld 商（β3・β5）。F1 の Ind_κ と F2N-5（Ind の安定性）との照合。
3. 非連結 K スペクトル K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A)（BGT Def. 9.6 相当）。K-3 の連結 K を入力とする。
4. 連結 K との比較：非負次数で K^{nc} ≃ K、負次数の記述（BGT 9.? と Schlichting）。
5. Verdier 列を fiber 列に送ること（K-6 と β3 の Verdier 列）、Morita 不変性、filtered 余極限との可換。
6. Sp の相対版 `IsRelativeLocalizingInvariant`（ν : S ⟶ StableInfinity、K-S• の固定界面）としての登録。

### 主要宣言
- `SequentialIndex`、`SpectrumSequence`、`sequentialSpectrum`、`sequentialInjection`。
- `sequentialPiCocone`、`sequentialPiCoconeIsColimit`、`sequentialPiUnderlyingIsColimit`。
- `sequentialPi_exists_late`、`sequentialPi_eq_iff`、`sequentialPi_eq_one_iff`、`sequentialPi_subsingleton_iff`、`sequentialPi_subsingleton_of_eventually`。
- `sequentialInjection_bijective_of_stable`、`sequentialInjection_bijective_on`、`sequentialInjection_isInvertible_of_stable`。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-3・K-4、固定界面 ν・K）、`KST/LocalizingInvariants/`（K-5 相対版、K-8）、`KST/Spectra/`、`KST/Fibration/`（K-6）、`InfinityCategories/Derived/`（β3・β5）、`F2/Ind/`。
- 提供先：K-基盤 1・2 の完成形（K が局所化不変量）、第 II 段の pro 切除の適用。

### 未コミット
- なし（本レーンの集約・3モジュール・専用監査・本計画を検証して保存）。共有作業木の他レーンの変更は対象外。

### 既知の問題
- 工程 1 は未完。Sp の実 cocone と ∞ 余極限性は未提供。`filteredSpectrumInjection` の選択は BF 射として厳密自然とは主張されていない。π の群 cocone を Sp cocone と同一視しない。
- K-6・F2N-5 と dg 懸垂は未接続。後続工程で必要な場合は明示の入力に隔離し、完成扱いしない。一般の安定 ∞ 圏上の K は作らない。

### 次の一手
- Sp から同じ BF 候補を頂点とする実 cocone と `IsColimitCone` が提供されたら接続する。候補の変更があれば同じ整数 π と注入射の比較を照合する。供給までは工程 1 の完了を主張しない。

## 規約
- 配置 `SerrePositivity/KST/NonConnective/`、集約 `KST/NonConnective.lean`、監査 `scripts/audit_kst_nonconnective.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。Sp の IsStable は使わない（K-5 の fiber 列・π 同値検出）。商・分数・局所化の API は Sp 正本（10-22 19:50）。
