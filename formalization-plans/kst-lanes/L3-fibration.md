# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使い、Verdier 列 D → C → C/D に対する連結 K の fiber 列を証明する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）

### 現在地
- 未着手。計画の骨子のみ。

### 残り（依存順）
1. 設定：C 安定、D ⊂ C thick、W = {f | cofib f ∈ D}。W の 2-out-of-3・pushout・extension 安定性。入力は Sp の `IsVerdierSequence`。
2. S• の相対構成 S•(C, W) と加法性からの連結版 fibration 定理（Waldhausen 1985 1.6.4、BGT §7）。
3. 必要な cofinality 条件の明示。K-S• の K-1（加法性）・K-2（homotopy fiber 比較）の宣言だけを入力にする。
4. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値）。Sp の K-5 の `IsLocalizingInvariant` の形に合わせ、π 同値検出で結論する。
5. 冪等完備化と BGT §9 の非連結化への入力の整理（K-7 の前提の列挙）。

### 依存と提供
- 読み取り専用：`KST/SConstruction/`（K-1・K-2）、`KST/LocalizingInvariants/`（K-5）、`KST/Spectra/`、`InfinityCategories/Derived/`（β3 の Verdier 列）。
- 提供先：K-7（非連結 K）、K-基盤 2（K が局所化不変量であること）。

### 次の一手
- 工程 1。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。
