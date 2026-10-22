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
  全整数次数の作用を同定し、比較差の可換正方形から native Hom との鎖同型を構成。
- native Hom に単位・合成・結合律を移し、実 dg gluing 圏を構成した。
  元の Hom 射影による左右 dg 射影と、元の単位・合成の両成分との厳密な一致も完成。
- 元の第三 cochain と代表加群表示の第三 cochain の比較、および単位の第三成分が零であることを証明。
- 閉じた gluing 射の同じ第三成分から、全対象での比較ホモトピーと実 cone 係数を構成。
  cone の包含・次数別行列式・比較ホモトピー零の場合の既存 cone 写像との一致を検証した。
- 三項行列を全 Hom end 内に構成し、各対象での評価が実 cone 係数であることから閉性を証明。
  全 dg 自然な実加群射 `dgGluingConeMorphism` と、右包含との厳密な可換性まで完成。
  元の両圏の代表 cone への移送と gluing の Hom の標準 cone 比較は未完。
  前三角性は未完であり、工程 (a) 全体の完了とは数えない。工程 (b)〜(f) は未着手。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHom_d_comparison`・`dgGluingHom_ext`・`dgGluingHomLift_unique`
- `dgGluingAugmentation_value`・`DGGluingRepresentableCategory`
- `dgGluingRepresentableRight`・`dgGluingRepresentableLeftModule`
- `dgGluingHomRepresentableIso`・`dgGluingHomRepresentableIso_left`・`dgGluingHomRepresentableIso_right`
- `dgGluingDGCategory`・`dgGluingToComma`・`dgGluingLeft`・`dgGluingRight`
- `dgGluingLeft_comp_yoneda`・`dgGluingIdentity`・`dgGluingComposition`
- `dgGluingComposition_left`・`dgGluingComposition_right`
- `dgGluingHomComparison_yoneda`・`dgGluingIdentity_comparison`
- `dgGluingConeSquareMap`・`dgGluingConeSquareMatrix_eq`
- `dgGluingCommaClosedSquareHomotopy_equation`・`dgGluingConeCoefficient`
- `dgGluingCommaConeElement_closed`・`dgGluingCommaConeMorphism_eval`・`dgGluingConeMorphism`

### 残り（依存順）
1. (a) 残り：シフト・cone の表現可能性から `IsDGPretriangulated` を証明。KL §4.1 Lemma 4.3。見積り 1〜2 日。
2. (b) 半直交分解 ⟨C, D⟩：充満 dg 部分圏、射影、随伴、gluing 関手の回収。KL §4.2。見積り 1〜2 日。
3. (c) dg nerve の二射影と構造変換、F2 の laxPullback への比較写像。Tamme Definition 5。見積り 1〜2 日。
4. (d) 比較の充満忠実性・本質的全射性と全試験関手の ∞ 普遍性。Tamme Remark 6、F0 判定。見積り 2〜3 日。
5. (e) 安定性・完全射影と F2・K-8b の半直交分解との整合。Tamme Lemma 8。見積り 1 日。
6. (f) 通常 pullback と Verdier 商 ⊙ の dg 同定、Sp の K-8d8 への `IsVerdierSequence` の供給（D と共同）。
   Tamme §1、Drinfeld Thm 3.4、β3 の平坦商。見積り 2〜3 日。

### 依存と提供
- 読み取り専用：`InfinityCategories/Derived/`（β5 の D(A)、双加群、相対 tensor、Drinfeld 商 β3）、`InfinityCategories/F2/`（lax pullback、安定性）、`InfinityCategories/Core/`・`F1/`。
- 提供先：Sp（K-8 の ⊙ の同定）、K-F・K-S•（Verdier 列の具体例）。
- β5 の確認済み入口：`dgAlgebraDerivedInfinityCategory`（`DGAlgebraDerivedInfinity`）、
  `Bimodule`（`DifferentialGraded/Bimodule/Basic`）、`Morita.kernelTensor`（通常 tensor）、
  `dgKernelDerivedInfinity`（半自由入力・実出力分解を保つ導来 tensor）。

### 次の一手
- 閉射に対する `dgGluingConeMorphism` は、左代表加群の cone から右成分の双加群像の cone への実射。
  次は元の両圏の前三角性から代表 cone を選び、この実射を gluing 対象の閉元へ移す。
  β5 の通常 `Morita.kernelTensor`、`BimoduleTensor.rightUnitIso` と cone 保存を使い、
  右成分の cone と双加群像の cone の比較を構成する。導来圏の同型だけで K(D) の同型を代用しない。
  続いて gluing の Yoneda Hom と標準 cone の比較・シフトを構成し、
  `dgRepresentableHomotopyProperty` の三角的閉性（KL Lemma 4.3）へ接続する。

### 未コミット・既知の問題
- 18モジュール・集約のビルド成功（4500 jobs）、公理監査257宣言成功。所有モジュールに警告なし。
  許容三公理のみ。新規 sorry・axiom と主経路の `ModelCategory` 仮定なし。主要6署名も検査済み。
  今回の5モジュール・集約・監査・本計画を専有8パスだけで保存する。他レーンの差分は含めない。
  三項行列の計算は複体上の一般補題と加群評価へ分離し、既定の heartbeat 上限を保って検証した。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
