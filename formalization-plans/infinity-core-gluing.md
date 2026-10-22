# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-22）

### 現在地
- 未着手。計画の骨子のみ。

### 残り（依存順）
1. 双加群 M : Dᵒᵖ ⊗ C → Ch に沿う gluing 圏 C ×_M D（対象 (c, d, φ : M(d, c) の元)、Hom 複体、合成、微分）と pretriangulated 性。Kuznetsov–Lunts。
2. 半直交分解 ⟨C, D⟩：充満 dg 部分圏、射影、随伴、gluing 関手の回収。
3. dg nerve N_dg(C ×_M D) の二射影と構造変換 Δ¹ → N_dg(D) の比較。F2 の laxPullback（Fun(Δ¹,−) による）への比較写像。
4. 比較写像の充満忠実性・本質的全射性（F0 の判定）と ∞ 圏的普遍性。
5. 安定性・完全射影の供給。F2 の laxPullback_isStable、K-8b（Sp）の半直交分解との整合。
6. gluing 内の通常 pullback（lax pullback の中の cartesian 部分）と、その Verdier 商 ⊙ の dg 側の同定：β3 の Drinfeld 商を gluing dg 圏に適用し、Sp の K-8d8 が仮定入力に取る IsVerdierSequence を供給する（D と共同）。

### 依存と提供
- 読み取り専用：`InfinityCategories/Derived/`（β5 の D(A)、双加群、相対 tensor、Drinfeld 商 β3）、`InfinityCategories/F2/`（lax pullback、安定性）、`InfinityCategories/Core/`・`F1/`。
- 提供先：Sp（K-8 の ⊙ の同定）、K-F・K-S•（Verdier 列の具体例）。

### 次の一手
- 工程 1。β5 の主要宣言（infinity-core-stable.md）から双加群と相対 tensor の名前を拾い、gluing の Hom 複体を定義する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
