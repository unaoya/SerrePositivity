# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §2 の β4、§6 の D2。D レーンの β5（D(A)、双加群、相対 tensor・Hom）と
> F1b の F2L-2〜4（Cat_∞ の lax pullback、安定性）を読み取り専用で使い、dg gluing の dg nerve が lax pullback であることを証明する。
> 用途は K-基盤 2（Tamme・Land–Tamme）の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-23）

### 現在地
- 2026-10-23 コーディネータ指示で停止。次のチャットは本引き継ぎから再開する。工程 (a) 完了。`DGGluingObject` の対象、比較差 `gμ − νf` の mapping cocone としての実 Hom 複体、全次数の微分・単位・合成・結合律を構成。
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
  元の νf・gμ を実加群 Hom の前後合成・AW 合成族へ厳密に照合。対象圏の小ささなしの閉前合成成分式を供給し、元の augmentation の全合成 prism・両端・射影を回収。β5 の実導来 Hom 作用で移した合成方程式と、同じ実三辺を持つ導来合成三角形も供給。
  同じ二三角形を実二単体族へ評価し、全三辺を保持して共通宇宙へ移送。canonical 係数比較への対角の一致を証明し、元の gluing Hom で制限した両対角を実係数 path の両端へ厳密に照合。同じ全区間族から対角間の実ホモトピーを構成。
  対角ホモトピーは主比較の両端を全時刻で固定。二三角形の固定辺は元の導来 augmentation と一致し、可変辺を同じ端点表示へ正規化。始辺固定・終辺固定の合成対応へ持ち上げ、同じ入力・二三角形・対角を回収。対角間 path の引き戻しへの実比較を構成し、元の全区間ホモトピーを評価で回収。
  左右の元 Hom 入力を保つ合成 fiber・trivial Kan 射影・具体的切断の同値、入力付き対角の Kan fibration、厳密→path 比較の同値性を供給。係数側の `dgGluingHomDerivedCompositionInputPathComparison` 自体は同値。元 lax Hom 比較も同じ厳密対角模型へ移し、両模型の入力 lift 間の元 Hom 入力固定ホモトピーと、三角形の全変形・共通対角からの二変形・三角形境界を構成。係数三角形は native 合成 prism による具体的なものへ置換済み。主係数 path は元 Hom の負 primitive からの明示 cochain prism に両端固定で正規化済み。実切断和の第二切断への縮退、全次数 Yoneda 比較、円柱 extension と基底固定条件、共通宇宙・canonical 導来区間 Hom への移送も検証済み。元 gluing prism の全相の実係数から単体的正規化族を再構成し、同じ明示 cochain 族と厳密一致、主係数対角族との両端固定比較を供給。任意 comma から標的恒等 comma への実 dg 関手と二標準閉射を構成し、その実前後合成は同じ二作用・primitive の明示 lift に厳密一致。標的 Small 不要の実正規化 slice 三角形と augmentation の全 cube を構成し、三方向の境界・元 pinched 区間族を回収。恒等 comma 移送は全切断補正・全 augmentation prism を厳密保存。共通対象宇宙の cube の一面は元 comma の augmentation、他面は元負 primitive の明示 lift に一致。二重・三重区間族の持ち上げは三方向の面と全パラメータを保存。元 C・D・M の宇宙を制限せず、実 gluing Hom→加群恒等 comma の同じ Hom 鎖写像から二 native cube を構成し、全方向の面・実正規化入力・元 primitive の Yoneda 像を保持。正本の β5 導来加群関手による二 native cube の後合成と、その端面の全二次元族も供給。前 cube の内側零面と後 cube の中間零面の厳密一致を、元加群・共通宇宙・実導来加群の三段で証明。一般宇宙の実恒等 comma 関手は、正本の元 augmentation 全時間族を厳密に回収。元 Hom の区間評価は全切断で同じ nerve 関手像となり、複体模型の往復を相殺して正本の矢印 Hom 全四角形を同定。cube の元 augmentation 面の二三角形は、元 Hom の模型同型で制限した正本 F2 二三角形に厳密一致。実正規化 Hom の二射影は元 gμ・νf の Yoneda 像、比較 cochain は元 primitive の同じ像。元負 primitive を Yoneda 逆で移した明示 cochain lift と厳密一致。後 cube の全正規化面は、この明示入力だけから作る cochain 四角形に一致し、実導来加群関手の後合成も保持。別途、同じ実正規化 Hom からの全 pinched prism は明示 cochain 族と一致し、Yoneda 同型により加群宇宙での元係数複体の明示族へ戻る。終端へ潰れる係数の primitive は単位・零で消え、相 β→β⊔t が全単体を変えないと証明。恒等 comma の元 augmentation 四角形は同じ pinched prism の全区間評価に厳密一致し、元 C・D・M の明示 cochain 四角形でも全時間等式を供給。実後 cube の正規化面は、同じ元 Hom の正規化 pinched prism の全区間評価に共通宇宙で一致し、β5 実導来加群関手の後合成も保持。異なる対象宇宙の cochain prism について、元入力の線形成分・二端・primitive の照合から全出力係数の照合を供給。canonical な複体宇宙変更と明示 cochain prism の全時間自然性を証明。加群側の入力は同じ正本 Hom 模型写像へ戻り、正規化 prism の係数像は元 Hom 模型で制限した既存の明示係数 prism に厳密一致。区間評価後の canonical 導来係数写像への照合・主係数 path・選択済み入力固定変形の整合性、指定三角形境界の充填は未完。
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
- `dgGluingLeftNerve`・`dgGluingRightNerve`・`dgGluingAugmentationNerveHomotopy`・`dgGluingAugmentationNerveHomotopy_vertex_edge`
- `dgGluingNerveLaxComparison`・`dgGluingNerveLaxComparison_fst`・`dgGluingNerveLaxComparison_snd`・`dgGluingNerveLaxComparison_arrow`
- `dgGluingUniverseLeftNerve`・`dgGluingUniverseRightNerve`・`dgGluingUniverseAugmentationHomotopy_vertex_edge`
- `dgGluingUniverseDerivedNerveLaxComparison` と `_fst`・`_snd`・`_arrow`、`dgGluingUniverseDerivedAugmentationArrowFamily_postcompose`
- `dgGluingUniverseHomMappingIso`・`dgGluingLaxHomMappingComparison`・`dgGluingLaxHomMappingComparison_source`
- `dgGluingLaxHomPullbackComparison` と `_arrow_transport`・`_inputs_transport`、`dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff`
- `dgGluingHomTwoEndpointPath_isPullback`・`dgGluingHomTwoEndpointPath_primitive`・`dgGluingHomTwoEndpointPathSpaceCone_isLimit`・`dgGluingTwoEndpointPathSpaceCone_path`
- `dgGluingHomCoefficientPathPullbackComparison_equivalence`・`dgGluingDerivedHomCoefficientPathComparison_equivalence` と `_path`・`_inputs`、`dgGluingDerivedHomCoefficientIntervalPath_start`・`dgGluingDerivedHomCoefficientIntervalPath_end`
- `dgGluingModuleDerivedHomMap_equivalence`・`dgGluingCanonicalCoefficientMappingComparison` と `_equivalence`・`_universe_action`
- `dgGluingUniverseLaxComparison_vertex_image`・`dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective`
- `dgGluingUniverseFunctorHomAction`・`dgGluingUniverseFunctorHomModelComparison_eq`・`dgGluingLaxHomLeftModelComparison_eq`・`dgGluingLaxHomRightModelComparison_eq`
- `dgGluingArrowHomTriangleEquiv`・`dgGluingArrowCompositionIso`・`dgGluingArrowHomCompositionCone_isLimit`・`dgGluingLaxHomArrowCompositionComparison`
- `dgGluingHomDerivedCoefficientDiagonalHomotopy_source`・`dgGluingHomDerivedCoefficientDiagonalHomotopy_target`・`dgGluingHomDerivedFirstComposition_triangle`・`dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate`・`dgGluingHomDerivedCompositionPathComparison`
- `dgGluingDerivedFirstCompositionInputSection_equivalence`・`dgGluingDerivedLastCompositionInputSection_equivalence`・`dgGluingHomDerivedCompositionInputPathComparison_raw`・`dgGluingHomDerivedCompositionInputPathComparison_forget`・`dgGluingDerivedCompositionInputStrictPathComparison_equivalence`・`dgGluingHomDerivedCompositionInputPathComparison_equivalence`・`dgGluingHomDerivedCompositionInputPathComparison_factor`・`dgGluingLaxHomInputStrictComparison`・`dgGluingLaxHomInputStrictComparison_forget`・`dgGluingLaxHomFirstInputHomotopy_over`・`dgGluingLaxHomDiagonalComparisonBoundary`・`dgGluingHomDerivedLeftCoefficientTriangle_canonical`・`dgGluingHomCoefficientDirectNormalization_exists`・`dgGluingHomCoefficientCylinderExtension_primitive`・`dgGluingNativePinchedPrismCorrectionSum_cylinder`・`dgGluingCochainAugmentationHomotopy`・`dgGluingHomCoefficientAugmentationPrism`・`dgGluingComplexCochainAugmentationPrism_post_zero`・`dgGluingAugmentationCylinderPrism_over`・`dgGluingAugmentationCylinderComparison_exists`・`dgGluingComplexCochainAugmentationPrism_post`・`dgGluingAugmentationCylinderPrism_extension`・`dgGluingHomCoefficientAugmentationNormalization_exists`・`dgGluingHomDerivedAugmentationNormalization_exists`・`dgGluingHomDerivedAugmentationIntervalNormalization_exists`・`dgGluingNativePrismNormalizedFamily_comparison`・`dgGluingNativePrismNormalizedPathComparison_exists`・`dgGluingNativeDerivedPrismPathComparison_exists`・`dgGluingCommaNormalizedHom_eq_cochainLift`・`dgGluingCommaImagePrismSimplex`・`dgGluingCommaImageAugmentationPrism`・`dgGluingCommaPreNormalizeCube_original_face`・`dgGluingCommaPostNormalizeCube_cochain_face`・`dgGluingNativePreNormalizeCube`・`dgGluingNativePostNormalizeCube`・`dgGluingNativeNormalizationCube_inner`・`dgGluingNativeNormalizationHomInput_normalized`・`dgGluingNativeNormalizedHom_primitive`・`dgGluingNativeDerivedPreNormalizeCube`・`dgGluingNativeDerivedPostNormalizeCube`・`dgGluingNativeDerivedNormalizationCube_shared_face`・`dgGluingNativeIdentityAugmentationPrism`・`dgGluingNativeArrowComparisonPrism_cube`・`dgGluingNativeNormalizationFirstTriangle_eq`・`dgGluingNativeNormalizationLastTriangle_eq`・`dgGluingNativeNormalizedHom_eq_cochainLift`・`dgGluingNativeDerivedPostNormalizeCube_cochain_face`・`dgGluingNativeModuleNormalizedPrism_coefficient`・`dgGluingIdentityCommaTerminalPhase_data`・`dgGluingIdentityCommaPrismInterval_square`・`dgGluingNativeModuleCochainSquare_interval`・`dgGluingNativeDerivedPostNormalizeCube_interval_face`・`dgGluingCochainPinchedInput_component`・`dgGluingCochainPrism_universe_component`・`dgGluingComplexCochainPrism_universe_naturality`・`dgGluingNativeCochainModelInput_universe`・`dgGluingNativeNormalizedPrism_coefficient_universe`・`dgGluingCommonComplexUniverse_hom_eq_inv`・`dgGluingPrismIntervalSquare_target`

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
- 最初に未接続 `CoefficientYonedaInverseChainMap.lean` の `change` を全宇宙・端点の型注釈または同型合成の有限展開で修正する（heartbeat 上限は増やさない）。次に依存する `NativeCanonicalCoefficientPrism.lean` を個別ビルドし、成功後だけ集約・監査へ接続する。`dgGluingCommonComplexUniverse_hom_eq_inv` は逆向き宇宙同型の実逆射との厳密一致、`dgGluingPrismIntervalSquare_target` は prism の後合成を区間評価の前合成へ移す式として検証済み。`dgGluingLaxHomPullbackComparison` を正本とし、両輸送済み射影を保って同じ実ホモトピー逆を構成する。
  入力側の二脚は `dgGluingLaxHomLeftModelComparison_eq`・`dgGluingLaxHomRightModelComparison_eq` で元の左右鎖射影へ照合済み。
  正本と係数模型は同じ入力付き模型へ移送済み。係数側の入力付き path 比較は同値だが、正本との全 path 比較は未完。元 Hom の負 primitive の明示 augmentation prism と主係数 path は、元 pinched Hom 上・canonical 導来区間 Hom 上で両端固定に比較済み。標的恒等 comma の実二標準閉射の合成から正規化三角形・三次元族を構成し、二作用 gμ・νf・primitive と全 cochain lift を保持。`dgGluingCommaImagePrismSimplex` は任意対象宇宙で元 augmentation 全単体を保持し、`dgGluingCommaImageAugmentationPrism` は共通対象宇宙で全写像の可換式。`dgGluingCommaPreNormalizeCube_original_face`・`dgGluingCommaPostNormalizeCube_cochain_face` は同じ元 Hom 族の元 augmentation 面と明示 lift 面を回収。`dgGluingNativePreNormalizeCube`・`dgGluingNativePostNormalizeCube` は元 C・D・M の異なる宇宙を保った共通宇宙の実族。`dgGluingNativeNormalizationCube_inner` 等が全方向の面、`dgGluingNativeNormalizationHomInput_normalized` が同じ正規化 Hom 入力、`dgGluingNativeNormalizedHom_primitive` が元 primitive の Yoneda 像を保持。`dgGluingNativeDerivedPreNormalizeCube`・`dgGluingNativeDerivedPostNormalizeCube` は正本の β5 実導来加群関手による同じ後合成。`dgGluingNativeDerivedNormalizationCube_shared_face` により、前後二 cube は同じ全二次元面で接続済み。`dgGluingNativeIdentityAugmentationPrism`・`dgGluingUniverseFunctorPinchedInterval` は正本の元 augmentation 全時間族と全 Hom 区間族を回収。`dgGluingNativeArrowComparisonPrism_cube` は cube 面を正本の矢印 Hom 全四角形へ、`dgGluingNativeNormalizationFirstTriangle_eq`・`dgGluingNativeNormalizationLastTriangle_eq` はその二三角形を元 F2 二三角形へ厳密照合。`dgGluingNativeNormalizedHom_eq_cochainLift` は元 Hom の実正規化と負 primitive の同じ明示 lift の一致。`dgGluingNativeDerivedPostNormalizeCube_cochain_face` は後 cube の全正規化面を元二作用・負 primitive の明示 cochain 四角形へ照合。`dgGluingNativeModuleNormalizedPrism_coefficient` は同じ正規化 Hom の全 pinched prism を Yoneda 同型で元係数複体の明示族へ戻す。`dgGluingIdentityCommaTerminalPhase_data` は `coherentPrismCut t` で終端へ潰した部分の相変更 β→β⊔t を全次数で相殺。`dgGluingIdentityCommaPrismInterval_square` は恒等 comma の元 augmentation 四角形と同じ pinched prism の全区間評価の厳密等式。`dgGluingNativeModuleCochainSquare_interval` は元 C・D・M の明示 cochain 四角形に同じ全時間等式を供給。`dgGluingNativeDerivedPostNormalizeCube_interval_face` は同じ正規化 Hom prism の全区間評価へ後 cube 面を共通宇宙で結合し、β5 実導来加群関手の後合成を保持。`dgGluingCochainPinchedInput_component`・`_source`・`_replacement`・`_primitive` は元複体の同じ入力係数に戻す全次数式。`dgGluingIdentityCommaPrism_component_post_compare` は異なる対象宇宙へ一般化済み。`dgGluingCochainPrism_universe_component` は同じ入力係数と二端・primitive の鎖写像に沿う照合から全出力係数を比較する。`dgGluingComplexCochainPrism_universe_naturality` は両係数複体の canonical 宇宙変更と全 cochain prism の可換式。`dgGluingNativeCochainModelInput_universe` は加群側模型の入力を同じ正本 `dgGluingNativeHomModelMap` へ戻す。`dgGluingNativeNormalizedPrism_coefficient_universe` は同じ入力上で正規化 prism の係数像を元 `dgGluingHomCoefficientAugmentationPrism` へ厳密照合。次は、Yoneda・単位 Hom による係数空間同型の逆と pinched→区間評価の可換式を使い、この全 prism 等式を `dgGluingNativeDerivedPostNormalizeCube_interval_face` の同じ実区間面へ評価する。既存の canonical 導来係数 Hom 写像と主係数 path の両端固定正規化を保持して接続する。対象宇宙の異なる二 pinched 模型を定義的に同じ写像とは扱わない。cube が与える実入力固定変形と既存の選択変形の二次元相対比較を、入力 fiber の自明 Kan 射影で保持する。`dgGluingLaxHomDiagonalComparisonBoundary` の指定境界を保持して充填し、正本へ同値性を移す。個別の入力固定ホモトピーだけから全 path 比較の一致を結論しない。
  元の両 Hom 入力・augmentation prism・二三角形を保持して正本の実 lax Hom 比較と `dgGluingHomDerivedCompositionInputPathComparison` を照合する。入力付き path 比較の同値性を正本の全引き戻し比較へ移し、充満忠実性の判定へ適用する。

### 未コミット・既知の問題
- 停止時検証：集約ビルド成功（8696 jobs）、701モジュール・6513宣言の公理監査成功。許容三公理のみ。所有警告・新規 sorry・axiom・主経路 `ModelCategory` 仮定なし。ログ `/tmp/d2-stop-aggregate.log`・`/tmp/d2-stop-audit.log`。前回基準 `4069912ce`。今回は検証済み新規2モジュール・集約・監査・本計画の所有5パスだけを保存。他レーン不変。
  未コミット（ともに `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約・監査未接続）：`CoefficientYonedaInverseChainMap.lean` は23行の `change` が既定200000 heartbeatsで型照合タイムアウト、`NativeCanonicalCoefficientPrism.lean` はその補題に依存し未ビルド。前者は Yoneda 空間同型の逆を単位 Hom 同型付き鎖写像へ、後者は正規化 prism の係数像を canonical 始域同型の逆へ同定する作業。
- β5 の `Bimodule` は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`。
  KL の (D₂ᵒᵖ ⊗ D₁)-dgm は右 dg 加群の規約。比較差は `gμ − νf` を保持する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/Derived/Gluing/`、集約 `Derived/Gluing.lean`、監査 `scripts/audit_derived_gluing.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts（categorical resolutions, gluing）、Drinfeld 2004。
