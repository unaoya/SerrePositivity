# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 (a) 完了。`DGGluingObject` の対象、比較差 `gμ − νf` の mapping cocone としての実 Hom 複体、全次数の微分・単位・合成・結合律を構成。
  native dg 圏、左右 dg 射影、実 comma・通常 kernel comma への比較関手を供給。native/kernel Hom 同型は全次数の合成・単位を保存。
- 元の C・D の前三角性を明示入力に、実 gluing 円錐・全整数シフト代表と全 dg 自然な Yoneda 加群比較を構成。augmentation・両成分の比較も同じ射に保持。
- `dgGluing_isDGPretriangulated` は代表加群の同型閉包の零・全整数シフト・任意 distinguished 円錐閉性から結論。点ごとの比較は全 dg 自然な加群射で実現。
- 工程 (b) の dg・H⁰・K の界面を構成済み。片側が H⁰ で零となる対象の実充満 dg 部分圏 `DGGluingCFactor`・`DGGluingDFactor` と両包含・制限射影を構成。
  元の前三角性からホモトピー零対象を選び、両制限射影の実対象での全射性を証明。厳密零対象・零 Hom の仮定は追加しない。
- C 因子への左 Hom 射影、D 因子からの右 Hom 射影は擬同型。両充満因子と元の C・D の dg 準同値を証明。
  `dgGluingFactors_semiorthogonal` は順序 ⟨D,C⟩ の実 Hom 複体の全次数 acyclic 性。
- 同じ制限射影を順関手とする両 H⁰ 同値と、その逆による C・D 切断関手を構成。切断後の射影は実余単位で恒等と自然同型。
  元の Hom 射影の全単射から、左射影 ⊣ C 切断、D 切断 ⊣ 右射影の実 H⁰ 随伴を構成。
  C 随伴の余単位と D 随伴の単位は同じ切断同型の順射・逆射で可逆。両切断の完全忠実性も供給。
- D 随伴の同じ余単位を実閉 gluing 射へ持ち上げ、その右成分が H⁰ で同型と証明。実円錐は C 因子に属する。
  左零成分を持つ始域の円錐の左成分を標的の左成分と H⁰ で同定し、C 因子同値で円錐を同じ C 切断へ同定。
- `dgGluingDecompositionTriangle` は各実対象 X について、D 切断→X→C 切断の代表加群を三対象に持つ K(Gluing) の distinguished 三角形。
  第一射は同じ D 随伴余単位の Yoneda 像。元の H⁰ に未導入の三角構造や ∞ 随伴を結論していない。
- C 因子上の制限 Hom 加群値 dg 関手と、両射影で制限した係数 M[-1] の dg 関手を構成。
  標準 bottom 包含は全因子対で擬同型。両 Hom 射影は零、第三成分は恒等。比較元零の仮定なし。
- comma の bottom 包含は全次数の前後合成を保存し、native 係数包含・Yoneda 同型を通して一致。元の反変 M 作用から C 因子上の全 dg 自然な擬同型を供給。
  D 変数の全 Hom 自然性を含む同じ成分の厳密 dg 自然変換を構成。元の gluing 関手 `dgGluingFunctor` は D→Mod(C), M[-1]。
- 工程 (c) の実比較を一般対象宇宙で構成済み。元の C・D・M・gluing の Hom は変えず、nerve の単体のみ共通宇宙へ ULift。
  二射影と元の augmentation の全 prism は面・退化と可換。native 加群 nerve と β5 の導来加群 ∞ 圏上の lax pullback 比較を供給。
  二射影・全矢印族を厳密に回収し、実頂点辺は元の augmentation の持ち上げ、その導来像そのもの。
  共通対象宇宙では、一般宇宙の native・導来構造変換が先の実全単体族の持ち上げに一致。
- 工程 (d) 進行中。始域の実写像空間を同じ mapping cocone Hom 複体の空間模型へ同定し、導来 lax pullback の実写像空間への比較射を構成。
  同じ比較射を F2 の厳密な写像空間引き戻しへ移し、両射影と端点輸送を保って元の矢印族・二射影の対の Hom 作用へ照合。
  元の比較の充満忠実性は、この具体的引き戻し比較が全対象対で実ホモトピー同値であることと同値。Kan 仮定は追加しない。
- 複体側では mapping cocone を、恒等 cocone の path 射影と元の差の厳密な引き戻しと証明。両射影・持ち上げ一意性・実収縮・次数別全射性を供給。
  任意複体の厳密な引き戻しを実 pinched 空間へ移す。同じ path 空間同型は両射影を保存し、零複体への実ホモトピー同値と空間模型での同値も供給。
  同じ恒等 cocone の分解用複体を二端点 path に用い、元の gluing Hom からの写像の始終点を νf・gμ、primitive を元の比較 cochain と厳密に同定。
  同じ二端点の厳密引き戻しを構成。次数別切断から端点対の Kan fibration を得て、元の Hom 空間模型を頂点とする ∞ 極限錐・両脚を供給。
  直和複体の実空間模型を直積へ厳密に同定。元の二作用の直積による引き戻し・∞ 極限錐を構成。係数の二端点 path を同じ係数空間内の通常区間族へ両端点を保って同値に移し、元の gluing Hom から通常 path 引き戻しへの実比較のホモトピー同値性を証明。共通宇宙と canonical な実導来係数 Hom へ移した同じ比較も同値。全区間族・左右射影と、νf・gμ の導来像である両端を回収。
  任意の次数別全射な鎖写像の相対 horn を指定最上位成分・削除方程式から充填。擬同型性なしの Kan fibration と、元の cocone 空間を頂点とする旧 path の ∞ 極限錐も供給。
  β5 の実半自由分解・係数の準同型 span・二 augmentation の厳密可換四角形を構成。同じ全比較 cochain の円柱・全空間ホモトピー・鎖ホモトピーを元の nerve Hom 作用へ照合。
  射影的入力なら半自由出力 Hom 射影は準同型。同じ切断から元の導来 Hom 作用の同値性を証明。代表加群の canonical な係数比較は、模型・端点同型を除き一般宇宙の元の作用を厳密に回収。
  元の一般宇宙の比較の本質的全射性を証明。任意の導来辺を閉加群射で表し、同じ augmentation の gluing 対象へ戻す。
  一般宇宙の nerve の全 Hom 作用・複体模型・前後合成を厳密に照合。実導来 lax 比較の二脚は、端点輸送込みで元の左右 Hom 鎖射影に一致。
  矢印圏の区間 Hom を共通対角の二合成三角形へ分け、厳密な往復同値・全パラメーターでの自然性・四辺の式を証明。
  始辺固定の合成対応・第二辺への trivial Kan fibration・同じ対角評価を構成。始辺固定／終辺固定の実三角形族の持ち上げは三辺を回収。
  矢印 Hom と両合成対応の対角引き戻しの厳密な同型を証明。逆は元の二三角形の持ち上げ。矢印 Hom 自体を頂点とする空間の ∞ 極限錐も供給。
  同じ実 lax Hom 比較をこの対角引き戻しへ移し、augmentation の導来二辺・両射影・元の全二三角形の回収を証明。
  全写像空間の比較同値性・全試験関手の普遍性は未完。(e)・(f) 未着手。

### 主要宣言
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingHomPrimitive_boundary`
- `dgGluingHomRepresentableIso`・`dgGluingHomRepresentableIso_left`・`dgGluingHomRepresentableIso_right`
- `dgGluingDGCategory`・`dgGluingToComma`・`dgGluingLeft`・`dgGluingRight`・`dgGluingComposition_comparison`
- `dgGluingConeObject`・`dgGluingChosenConeModuleMap`・`dgGluingConeModuleMap_quasiIso`
- `dgGluingChosenShiftModuleMap`・`dgGluingShiftModuleMap_quasiIso`・`dgGluing_isDGPretriangulated`
- `DGGluingCFactor`・`DGGluingDFactor`・`dgGluingFactorZeroObject`・`dgGluingFactors_semiorthogonal`
- `dgGluingCFactorProjection_quasiEquivalence`・`dgGluingDFactorProjection_quasiEquivalence`
- `dgGluingCProjectionAdjunction`・`dgGluingDProjectionAdjunction`・`dgGluingCSectionHomotopyFullyFaithful`・`dgGluingDSectionHomotopyFullyFaithful`
- `dgGluingDecompositionTriangle`・`dgGluingDecompositionTriangle_distinguished`・`dgGluingDecompositionTriangle_mor₁`
- `dgGluingFunctor`・`dgGluingCrossHomFunctor`・`dgGluingCrossCoefficientFunctor`・`dgGluingCrossHomCoefficientMap_quasiIso`
- `dgGluingCrossHomCoefficientMap_pre`・`dgGluingCrossHomCoefficientMap_post`・`dgGluingCrossHomCoefficientModuleMap_quasiIso`
- `dgGluingCrossHomCoefficientModuleMap_naturality`・`dgGluingCrossHomCoefficientComparison`・`dgGluingCrossHomCoefficientComparison_app`
- `dgGluingLeftNerve`・`dgGluingRightNerve`・`dgGluingAugmentationNerveHomotopy`・`dgGluingAugmentationNerveHomotopy_vertex_edge`
- `dgGluingNerveLaxComparison`・`dgGluingNerveLaxComparison_fst`・`dgGluingNerveLaxComparison_snd`・`dgGluingNerveLaxComparison_arrow`
- `dgGluingModuleDerivedComparison`・`dgGluingDerivedNerveLaxComparison`・`dgGluingDerivedAugmentationArrowFamily_postcompose`
- `dgGluingDerivedNerveLaxComparison_fst`・`dgGluingDerivedNerveLaxComparison_snd`・`dgGluingDerivedAugmentationHomotopy_vertex_edge`
- `dgGluingUniverseLeftNerve`・`dgGluingUniverseRightNerve`・`dgGluingUniverseAugmentationHomotopy_vertex_edge`
- `dgGluingUniverseDerivedNerveLaxComparison` と `_fst`・`_snd`・`_arrow`、`dgGluingUniverseDerivedAugmentationArrowFamily_postcompose`
- `dgGluingUniverseHomMappingIso`・`dgGluingLaxHomMappingComparison`・`dgGluingLaxHomMappingComparison_source`
- `dgGluingLaxHomPullbackComparison` と `_arrow_transport`・`_inputs_transport`、`dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff`
- `dgGluingHomTwoEndpointPath_isPullback`・`dgGluingHomTwoEndpointPath_primitive`・`dgGluingHomTwoEndpointPathSpaceCone_isLimit`・`dgGluingTwoEndpointPathSpaceCone_path`
- `dgGluingHomCoefficientPathPullbackComparison_equivalence`・`dgGluingDerivedHomCoefficientPathComparison_equivalence` と `_path`・`_inputs`、`dgGluingDerivedHomCoefficientIntervalPath_start`・`dgGluingDerivedHomCoefficientIntervalPath_end`
- `dgGluingPinchedChainMap_fibration`・`dgGluingCoconePathSpaceProjection_fibration`・`dgGluingCoconePathSpaceCone_isLimit` と `_path`・`_base`
- `dgGluingModuleDerivedHomMap_equivalence`・`dgGluingCanonicalCoefficientMappingComparison` と `_equivalence`・`_universe_action`
- `dgGluingUniverseLaxComparison_vertex_image`・`dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective`
- `dgGluingUniverseFunctorHomAction`・`dgGluingUniverseFunctorHomModelComparison_eq`・`dgGluingLaxHomLeftModelComparison_eq`・`dgGluingLaxHomRightModelComparison_eq`
- `dgGluingArrowHomTriangleEquiv`・`dgGluingArrowCompositionIso`・`dgGluingArrowHomCompositionCone_isLimit`・`dgGluingLaxHomArrowCompositionComparison`
- `dgGluingFirstFixedCompositionSecond_trivialKanFibration`・`dgGluingArrowCompositionIso_inv_first`・`dgGluingLaxHomArrowCompositionComparison_first_triangle`

### 残り（依存順）
1. (d) 実 Hom 複体模型からの写像空間比較を同値と証明し、比較の充満忠実性と全試験関手の ∞ 普遍性を供給。Tamme Remark 6、F0 判定。見積り 2〜3 日。
2. (e) 安定性・完全射影と F2・K-8b の半直交分解との整合。Tamme Lemma 8。見積り 1 日。
3. (f) 通常 pullback と Verdier 商 ⊙ の dg 同定、Sp の K-8d8 への `IsVerdierSequence` の供給（D と共同）。
   Tamme §1、Drinfeld Thm 3.4、β3 の平坦商。見積り 2〜3 日。

### 依存と提供
- 読み取り専用：`InfinityCategories/Derived/`（β5 の D(A)、双加群、相対 tensor、Drinfeld 商 β3）、`InfinityCategories/F2/`（lax pullback、安定性）、`InfinityCategories/Core/`・`F1/`。
- 提供先：Sp（K-8 の ⊙ の同定）、K-F・K-S•（Verdier 列の具体例）。
- β5 の確認済み入口：`dgAlgebraDerivedInfinityCategory`（`DGAlgebraDerivedInfinity`）、
  `Bimodule`（`DifferentialGraded/Bimodule/Basic`）、`Morita.kernelTensor`（通常 tensor）、
  `dgKernelDerivedInfinity`（半自由入力・実出力分解を保つ導来 tensor）。

### 次の一手
- `dgGluingLaxHomPullbackComparison` を正本とし、両輸送済み射影を保って同じ実ホモトピー逆を構成する。
  入力側の二脚は `dgGluingLaxHomLeftModelComparison_eq`・`dgGluingLaxHomRightModelComparison_eq` で元の左右鎖射影へ照合済み。
  次は `dgGluingDerivedHomCoefficientPathComparison` の実導来係数 Hom 内の path 模型と `dgGluingArrowHomCompositionCone` を、同じ augmentation prism の Hom 作用を保って比較する。
  canonical な係数移送の同値性・全区間族と端点は証明済み。元の augmentation prism の二三角形へ照合し、全引き戻し比較の同値性を充満忠実性の判定へ適用する。

### 未コミット・既知の問題
- 387モジュール・集約ビルド成功（7307 jobs）、公理監査4681宣言成功。許容三公理のみ。所有警告・新規 sorry・axiom・主経路 `ModelCategory` 仮定なし。
  公開32署名を検査済み。新規9モジュール、集約・監査・本計画の専有12パスだけを保存。他レーンの差分は含めない。
  前三角性は元の両圏について明示入力に取り、gluing の前三角性・安定性を仮定に追加していない。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
