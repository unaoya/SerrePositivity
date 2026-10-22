# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 進行中。任意の `Bimodule R C D` の閉次数零元を持つ対象と、比較差 `gμ − νf` の mapping cocone としての実 Hom 複体を構成。
  二射影・第三 cochain・全次数の微分式、任意複体からの持ち上げと一意性を証明。
- Yoneda の全 Hom 同型で実 comma dg 圏から単位・合成・結合律を移し、native gluing の実 dg 圏を構成。
  左右 dg 射影、単位・合成の二成分、第三 cochain と代表表示との厳密な整合性を証明。
- 全 Hom end 内の三項行列から全 dg 自然な `dgGluingConeMorphism` を構成。
  通常 tensor–Yoneda の単位と実円錐保存を接続し、像の円錐と代表加群円錐の tensor 像の実加群同型を構成。
- 元の両圏の前三角性を明示入力に、K(C)・K(D) の円錐代表を選び、実閉射と全 dg 自然な逆ホモトピーを回収。
  移送した同じ比較閉元から `dgGluingConeObject` を構成。augmentation の厳密な回収・移送ホモトピーと両成分の K の比較を証明。
- `Cone(coconeSquareMap) ≅ Cocone(coneSquareMap)` の交換を全整数次数で構成。四成分は `(a,b,c,d) ↦ (a,c,−b,d)`。
  閉後合成の回収下辺・ホモトピーを元の双加群作用・第三成分と同定し、`dgGluingHomConeExplicitIso` と左右分解を構成。
- 左右の評価円錐・全 Yoneda Hom・tensor の列比較を揃え、`dgGluingHomConeKernelIso` で標準加群円錐への kernel comma Hom と同定。
  標準円錐→同じ代表対象の実閉 comma 射を構成。その実後合成は各試験対象でホモトピー同値。
- native/kernel Hom 同型は両射影・第三 cochain・単位・全整数次数の合成を保存する。
  `dgGluingToKernelComma` と直接表示の同じ比較関手を構成。native gluing の Small 性も証明。
- native 閉円錐包含と指定零 cochain を構成し、kernel・native・全 Yoneda Hom end の間で同じ cochain を保持。
  `dgGluingHomConeKernelIso_inl` は左包含を同じ指定境界元の全次数作用と同定。両成分は実加群円錐の左包含元、第三成分は零。
- `dgGluingConeModuleMap` は指定境界元による全 dg 自然な実加群円錐射。
  評価の両包含が点ごとの既存同値の順射と一致し、`dgGluingConeModuleMapEvaluation_eq` を証明。
  同じ加群射の準同型性を証明し、射影的加群間の準同型として K(Gluing) の同型を構成。
  `dgGluingChosenConeHomotopyRepresentable` は元の両圏の前三角性を明示入力に標準 Yoneda 円錐の全 dg 自然なホモトピー表現可能性を供給。
- 恒等射の円錐から零加群の表現可能性を回収し、K(Gluing) で零を表す実 gluing 対象と代表加群の同型を構成。
  表現可能対象の同型閉包の `ContainsZero`・[1] および全非負整数シフト閉性を証明。
- K の代表加群間の任意の射を元の閉 dg 射へ持ち上げ、任意の distinguished 三角形の最初の二対象から第三対象への閉性を証明。
  `dgGluingRepresentable_isTriangulatedClosed₃` は標準 Yoneda 円錐に限らない同型閉包の全円錐閉性。
- 元の C・D の任意整数シフト代表を選び、実閉射と逆ホモトピーまで供給。gluing 自体の負シフトの表現可能性は未完。
  負シフト閉性・全整数シフト閉性と前三角性への統合が残る。工程 (a) 全体の完了とは数えない。工程 (b)〜(f) は未着手。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHom_d_comparison`・`dgGluingHom_ext`・`dgGluingHomLift_unique`・`dgGluingAugmentation_value`
- `DGGluingRepresentableCategory`・`dgGluingRepresentableRight`・`dgGluingRepresentableLeftModule`
- `dgGluingHomRepresentableIso`・`dgGluingHomRepresentableIso_left`・`dgGluingHomRepresentableIso_right`
- `dgGluingDGCategory`・`dgGluingToComma`・`dgGluingLeft`・`dgGluingRight`
- `dgGluingLeft_comp_yoneda`・`dgGluingIdentity`・`dgGluingComposition`・`dgGluingHomComparison_yoneda`・`dgGluingIdentity_comparison`
- `dgGluingConeSquareMatrix_eq`・`dgGluingConeCoconeIso`・`dgGluingHomConeKernelIso_inl`
- `dgGluingComposition_comparison`・`dgGluingPostcomposition_comparison`・`dgGluingPostcomposition_fst`
- `dgGluingCommaClosedSquareHomotopy_equation`・`dgGluingConeCoefficient`
- `dgGluingCommaConeElement_closed`・`dgGluingCommaConeMorphism_eval`・`dgGluingConeMorphism`
- `dgGluingKernelConeIso`・`dgGluingKernelConeIso_inr`・`dgGluingCommaKernelConeIso`
- `dgGluingKernelColumnIso_hom_naturality`・`dgGluingKernelHomAction_yoneda`・`dgGluingKernelHomConeAction_inl`
- `dgGluingYonedaConeIso_canonical`・`dgGluingHomConeRightTensorTargetIso`・`dgGluingHomConeRightCoefficient_kernel_module`
- `DGGluingConeRepresentative`・`dgGluingChooseConeRepresentative`
- `dgGluingConeObject`・`dgGluingConeObject_augmentation`・`dgGluingConeObject_leftIso`・`dgGluingConeObject_rightIso`
- `dgGluingConeObject_augmentation_transport`・`dgGluingConeRightHomotopyIso`
- `dgGluingHomConeKernelIso`・`dgGluingKernelConeRepresentativeMap`・`dgGluingKernelConeRepresentativeMap_source_homotopy`
- `dgGluingCoconeExtract_isIso`・`dgGluingCommaPostHomotopy_isIso`・`dgGluingHomConeKernelRepresentativeEquiv`
- `dgGluingKernelHomIso`・`dgGluingKernelHomIso_identity`・`dgGluingHomConeNativeEquiv`
- `dgGluingCommaToKernel`・`dgGluingKernelHomIso_factorization`・`dgGluingToKernelComma`・`dgGluingKernelHomIso_composition`
- `dgGluingSmall`・`dgGluingKernelConeInr`・`dgGluingConeInr`・`dgGluingHomConeKernelIso_inr`
- `dgGluingConeNullCochain`・`dgGluingConeModuleNullElement_boundary`・`dgGluingConeModuleMap`・`dgGluingChosenConeModuleMap`
- `dgGluingConeModuleMapEvaluation_inl`・`dgGluingConeModuleMapEvaluation_inr_comparison`・`dgGluingConeNullElement_kernel`
- `dgGluingConeModuleMapEvaluation_eq`・`dgGluingConeModuleMap_quasiIso`・`dgGluingConeModuleHomotopyIso`
- `dgGluingConeHomotopyRepresentable`・`dgGluingChosenConeHomotopyRepresentable`
- `dgGluingZeroHomotopyRepresentable`・`dgGluingZeroObject`・`dgGluingZeroRepresentableIso`
- `dgGluingRepresentableProperty_shift_nat`・`dgGluingRepresentable_containsZero`・`dgGluingRepresentable_isTriangulatedClosed₃`
- `DGGluingShiftRepresentative`・`dgGluingChooseShiftRepresentative`・`dgGluingShiftRepresentativeHomInv_homotopy`

### 残り（依存順）
1. (a) 残り：負シフトの表現可能性、全整数シフトと三角的閉性を統合し `IsDGPretriangulated` を証明。KL §4.1 Lemma 4.3。見積り 1〜2 日。
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
- `DGGluingShiftRepresentative` の n = −1 と実閉射・逆ホモトピーを使い、標準 kernel comma 内の両加群シフトを代表対象へ移す。
  β5 の `dgModuleFunctorShiftIso`（`Endomorphism/ModuleShiftImage`）で通常 kernel のシフト比較を供給し、同じ augmentation を移送。
  gluing の負シフトの全 dg 自然な加群表現可能性を証明し、既存の零・非負シフト・全円錐閉性と合わせる。

### 未コミット・既知の問題
- 158モジュール・集約ビルド成功（5074 jobs）、公理監査2903宣言成功。許容三公理のみ。所有警告・新規 sorry・axiom・主経路 `ModelCategory` 仮定なし。
  公開28署名を検査済み。新規9モジュール、集約・監査・本計画の専有12パスだけを保存。他レーンの差分は含めない。
  前三角性は元の両圏について明示入力に取り、gluing の前三角性・安定性を仮定に追加していない。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
