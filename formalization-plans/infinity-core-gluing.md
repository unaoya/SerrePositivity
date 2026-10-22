# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 進行中。任意の `Bimodule R C D` の閉次数零元を持つ対象、
  比較差 `gμ − νf` の実鎖写像、その mapping cocone としての全 Hom 複体を構成。
  二射影、全次数の微分式、任意パラメータ複体からの持ち上げ・比較の回収・一意性まで証明済み。
- Yoneda による同じ閉元の代表加群表示と、β5 の実 comma dg 圏の充満対象族を構成。
  この表示には単位・合成・結合律と右 dg 射影・左代表加群値 dg 射影がある。
  native Hom との鎖同型・合成移送と前三角性は未完であり、工程 (a) 完了とは数えない。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHom_d_comparison`・`dgGluingHom_ext`・`dgGluingHomLift_unique`
- `dgGluingAugmentation_value`・`DGGluingRepresentableCategory`
- `dgGluingRepresentableRight`・`dgGluingRepresentableLeftModule`

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
- native Hom と代表加群表示の Hom の鎖同型を、Yoneda の全次数評価と比較差の可換性から構成。
  単位・合成を native Hom へ移し、シフト・cone の表現可能性（KL Lemma 4.3）へ進む。

### 未コミット・既知の問題
- 初期5モジュール・集約のビルド成功（4484 jobs）、公理監査88宣言成功。許容三公理のみ。
  新規 sorry・axiom と主経路の `ModelCategory` 仮定なし。専有パスだけ保存する。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  双加群の添字の表記より、比較差と F2 の矢印方向を正本にする。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
