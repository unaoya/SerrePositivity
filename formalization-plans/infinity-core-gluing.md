# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-22）

### 現在地
- 工程 (a) 進行中。任意の `Bimodule R C D` の閉次数零元を持つ対象、
  比較差 `gμ − νf` の実鎖写像、その mapping cocone としての全 Hom 複体を構成。
  二射影、全次数の微分式、任意複体からの持ち上げ・一意性、Yoneda 代表加群表示と実 comma dg 圏の充満対象族を構成。
  全整数次数の作用を同定し、比較差の可換正方形から native Hom との鎖同型を構成。
- native Hom に単位・合成・結合律を移し、実 dg gluing 圏を構成した。
  左右 dg 射影・単位・合成の両成分、第三 cochain の代表表示、閉射の比較ホモトピーと実 cone 係数の行列式を証明。
- 三項行列を全 Hom end 内に構成し、各対象での評価が実 cone 係数であることから閉性を証明。
  全 dg 自然な実加群射 `dgGluingConeMorphism` と、右包含との厳密な可換性まで完成。
- 通常 tensor–Yoneda の単位と実 cone 保存を接続し、双加群像の cone と代表加群 cone の tensor 像の
  実加群同型・包含の整合性を構成。前三角性から K(C)・K(D) の cone 代表を選び、実閉射と逆ホモトピーを回収。
- 元の両圏の前三角性を明示入力に、同じ cone 比較射を代表対象へ移した閉元から
  gluing の対象候補 `dgGluingConeObject` を構成。実 augmentation の厳密な回収と、両成分の K の cone 比較まで完成。
- 候補の augmentation と元の比較射の移送後の射を結ぶ全 dg 自然なホモトピーを証明。
  右移送は K(C) の同型であり、その射が同じ実代表射の tensor 像であることまで回収した。
- ホモトピー可換な正方形の cocone 写像を第三 cochain ごと構成し、
  `Cone(coconeSquareMap) ≅ Cocone(coneSquareMap)` を全整数次数で証明。
  四成分の交換は `(a,b,c,d) ↦ (a,c,−b,d)`。右包含は既存の厳密 cocone 写像と一致。
- 実 gluing 合成の第三 cochain を全 Hom tensor 上で回収し、閉射の実後合成の二射影と第三 cochain を同定。
  `dgGluingHomConeIso` により実 Hom 後合成の標準 cone を回収係数の mapping cocone と同定。
- 閉射の後合成の第三 cochain を二項に因子分解し、右包含への制限を元の像の射の作用と同定。
  右包含の Yoneda 比較との整合性を使い、`dgGluingHomConeBottom_action` で元の双加群作用まで回収。
- 左包含上の第二項を全次数の加群 Hom 後合成へ移し、回収ホモトピーを同じ閉射の第三成分の評価と同定。
  `dgGluingHomConeExplicitIso` は元の双加群作用・第三成分を明示した係数への、実 Hom 後合成の標準 cone の鎖同型。
- 直和写像の cone の実鎖同型と実包含を構成し、`dgGluingHomConeSplitIso` で左右 Hom cone を分離。
  分解後の係数は左右の制限の和。左の差写像・第三成分は負の左作用・負の同じ第三成分、右は右作用・第三成分零。
- 左の評価 cone を同じ加群 cone の全 Hom と同定し、左係数を `dgGluingConeMorphism` の実後合成の負と同定。
  右係数は、同じ右作用の厳密正方形の標準 cone 写像そのものと証明。D の Yoneda cone 加群からの全 Hom 同型も構成。
  tensor–Yoneda の列比較を全 Hom に拡張し、試験対象の augmentation と通常 tensor による右作用を構成。
  代表上で元の右作用を回収し、全次数合成との整合性・右 Hom cone から tensor 像への写像と両包含を証明。
  Yoneda 円錐同型を標準 Hom 円錐比較で回収し、右係数を同じ右 Yoneda 円錐への kernel 全 Hom 作用と同定。
  左右の標的同型を揃え、`dgGluingHomConeKernelIso` で実 Hom 円錐を標準加群円錐への加群 comma Hom と同定。
  augmentation の同じ全 dg 自然な境界から標準円錐→選んだ対象の実閉 comma 射を構成し、両成分の K の代表同型を回収。
  任意の加群 comma 試験対象からの実後合成はホモトピー同値。`dgGluingHomConeKernelRepresentativeEquiv` で元の Hom 円錐を同じ代表対象への kernel Hom に移す。
  native/kernel Hom の実鎖同型は両射影・第三 cochain・閉単位・全整数次数の合成を厳密に保存する。
  同じ二比較の合成 `dgGluingToKernelComma` を構成。`dgGluingHomConeNativeEquiv` は同じ円錐対象への点ごとの実ホモトピー同値。
  gluing の同じ係数宇宙での Small 性と、標準加群円錐への第三 cochain 零の kernel comma 包含を構成。
  `dgGluingHomConeKernelIso_inr` は元の Hom 円錐の右包含と同じ kernel 包含による後合成を厳密に同定。
  native 閉包含 `dgGluingConeInr` と全 dg 自然な Yoneda 加群射を構成。合成の指定零 cochain を native・kernel・Yoneda Hom end 間で保持。
  `dgGluingConeModuleMap` は指定境界元による実加群円錐→代表加群の dg 自然な射。元の両圏の前三角性を明示入力とする版も構成。
  評価の両包含を同定し、右包含では既存の点ごとの同値の順射との一致を証明。左評価は指定 native 境界元の全次数後合成と同定。
  円錐交換の左包含の第一・第三成分と負符号も証明。左包含での既存同値との一致、加群射の同値性、零・整数シフトの閉性は未完。
  前三角性は未完であり、工程 (a) 全体の完了とは数えない。工程 (b)〜(f) は未着手。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHom_d_comparison`・`dgGluingHom_ext`・`dgGluingHomLift_unique`・`dgGluingAugmentation_value`
- `DGGluingRepresentableCategory`・`dgGluingRepresentableRight`・`dgGluingRepresentableLeftModule`
- `dgGluingHomRepresentableIso`・`dgGluingHomRepresentableIso_left`・`dgGluingHomRepresentableIso_right`
- `dgGluingDGCategory`・`dgGluingToComma`・`dgGluingLeft`・`dgGluingRight`
- `dgGluingLeft_comp_yoneda`・`dgGluingIdentity`・`dgGluingComposition`・`dgGluingHomComparison_yoneda`・`dgGluingIdentity_comparison`
- `dgGluingConeSquareMatrix_eq`・`dgGluingConeCoconeIso`・`dgGluingCoconeExtractConeIso_inl_snd`
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

### 残り（依存順）
1. (a) 残り：零・シフト・cone の全 dg 自然な表現可能性から `IsDGPretriangulated` を証明。KL §4.1 Lemma 4.3。見積り 1〜2 日。
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
- 標準 kernel 円錐の左包含を、`dgGluingKernelConeNullElement` による全次数後合成と同定。
  指定 cochain を保持する `dgGluingConeModuleMap` の左評価を既存の点ごとの同値の順射へ接続し、円錐の両包含による一意性を使う。
  加群射の点ごとの準同型性から射影的加群間の K の同型へ接続し、零・整数シフトも構成する。
  任意の零ホモトピーの選び直しや点ごとの Hom 同値だけでは、全 dg 自然な円錐表現可能性完了とは数えない。

### 未コミット・既知の問題
- 117モジュール・集約のビルド成功（5033 jobs）、公理監査2287宣言成功。所有モジュールに警告なし。
  許容三公理のみ。新規 sorry・axiom・主経路の `ModelCategory` 仮定なし。今回の公開45署名を検査済み。
  新規14モジュール、集約・監査・本計画の専有17パスだけを保存。他レーンの差分は含めない。
  前三角性は元の両圏について明示入力に取り、gluing の前三角性・安定性を仮定に追加していない。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
