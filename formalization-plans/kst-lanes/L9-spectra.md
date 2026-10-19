# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-20）

### 現在地
- L9a・L9b・改訂 L9c・L9d・L9e 完了（10-19）。L9e は係数表示、符号・像を含む微分同定、Milnor 完全性・lim¹・有理 Shapiro 全射性、通常 Tot 比較まで検証済み。Sp-5：零対象、任意の小積・通常の小さい BF 図式の実際の ∞ 極限錐、全ての指定辺の fiber と loop 四角形は構成済み。`nativeTailEquivalence` は元の一段移動の実際の同値。全 Hom で自然な cotensor 普遍評価と自明 Kan fibration 性、整合写像の源射影の同値から `nativeCotensor` と coherent な評価の族を構成済み。零評価の因子分解三角形と円の生成辺を、関手 quasicategory の Λ[3,1] で貼って四角形の族を構成した。点ごとの全四頂点と固定 cospan（一点 → Y ← 一点）を厳密同定し、円の三角形が元の普遍評価 loop の coherent Hom 比較単体そのものであることも証明済み。同じ固定図式の BF 参照極限錐、そこへの実際の比較射 `circlePointLoopComparison`、底と両錐を保持する join 拡張、比較頂点のホモトピー類の選択独立性を構成済み。元の四角形の引き戻し性はこの比較辺の可逆性と同値。Hom–end の検査に向け、両端固定の中央 anodyne な重みの制限が自明 Kan fibration であることを証明し、二単体の共通重みを介してホーンを区間へ潰す元の end の射に実際のホモトピー逆を構成した。collapse の左辺は生成区間、右辺は終点での定値辺に厳密一致する。通常の cospan の BK 重みとホーン重みの自然同型、および指定した collapse による区間 end から元の BK end へのホモトピー同値も完成した。中央係数の Kan 性だけで成立し、係数の自然性と各射影公式を保持する。区間 end と標準の基点付き円の写像空間の厳密同型も完成した。逆の中央射影は元の区間から標準円への商に沿う制限そのもの。円の写像空間から零係数 cospan の元の BK end への指定した射 `loopCircleBKComparison` は Kan な標的で実際のホモトピー同値。スペクトル Hom 係数の cospan への同定と元の錐の比較辺の可逆性、loop の完全忠実性と高次自然性、安定性は未完。
- Sp の quasicategory 性・全整数次数の群・homotopy fiber の長完全列・有理 telescope とテンソル表示を構成済み。Sp-5：任意の小積に加え、任意の小さい通常の BF 図式で、元の homotopy limit を頂点とする実際の coherent 錐の ∞ 極限性まで完成した。元の BF Hom と元の BK end の同値の順射を保持し、係数・重み・全 Hom パラメータの合成自然性を証明。恒等射の像を edgewise 共通解像へ厳密に持ち上げ、左右射影の全パラメータの可換四角形から反転 end の比較族の実際のホモトピー同値性を得た。さらに錐全体の Hom の族の頂点評価と制限をその比較そのものへ照合し、γ3 の native 判定へ接続した。既存の hG・homotopy Tot についても、元の BF 対象を頂点とする ∞ 極限錐を公開済み（群の有限性・Reedy 条件は不要）。段ごとの全基点 π 同型の BF 射の Sp での可逆性、BF 置換単位と通常 Tot 比較の可逆性も証明済み。任意の coherent 図式への接続・基点の全整数 π による同値検出・loop の完全忠実性・安定性は未完。
- hG と homotopy Tot の段ごとの Kan 構成・BF 置換・比較射、自明作用の標準射の全整数次数 π の単射性、有理化後の有限群の自明作用では全単射性と標準射による群同型まで証明済み。
- Sp-4：通常 Tot と標準単体 end の点つき同型、BK end への標準比較、loop 交換との厳密可換性を証明済み。Reedy 条件下で通常 Tot の Ω 列・BF 模型から既存の `homotopyTotalization` への実際の BF 射と各段の全基点・全整数次数 π 同型を構成済み。任意の Ω 図式についても、各段の Reedy anodyne な単位に沿い loop 値へ随伴構造を延長して厳密な余単体 Ω 列を構成した。置換単位の BK 比較と BF の逆向きの射を合成し、Reedy 置換した通常 Tot から元の `homotopyTotalization` への実際の BF 射と同じ π 同型まで完了。
- Sp-4 の重みの比較：置換後の end 比較は実際のホモトピー同値。相対 corner の実際の latching 射を立方体で計算し、重みの相対 latching とパラメーターの pushout-product に arrow 同型で同定済み。Reedy anodyne な重みと単射パラメーターから corner の Reedy anodyne 性を証明し、重みの制限の全単射 RLP を構成済み。置換単位の制限の切断により、end の非空性を仮定せず置換前の全基点 π 同型へ移送済み。 Reedy 単射な重みと anodyne パラメーターの corner の Reedy anodyne 性も証明し、重みの Reedy 単射への end の制限が実際の Kan fibration であることを証明済み。点つき enriched end の基礎単体集合にも arrow 同型で移送済み。単射による部分複体骨格の逆像・像と骨格の共通部分の公式、骨格への制限の単射性も証明済み。
- 有理化各段の高次群係数で BG の通常の正規化 cochain の正次数 cohomology が消滅することを証明済み。
- 球面的境界の交代関係と充填判定、骨格の一段の厳密な延長と通常の cocycle 条件の同値、任意の cochain・cocycle の骨格の射による実現まで完了。
- 関数複体の π₀ の座標表示を Kan 充填で構成し、骨格 fiber の係数へ合成済み。相対商の fiber 頂点とセル単体から復元する頂点も厳密に一致する。
- 復元した頂点を含めると元の射に戻り、成分係数は既存 cochain と一致する。成分と正次数群の係数は同じセル球面への制限で計算され、正規化微分の交代式も保持する。
- 反復 loop 値の fiber の π₀ と元の fiber の全正次数群を比較し、既存係数表示との正符号の可換式を証明済み。
- 同じ境界の二つの零ホモトピーの差を、一つ高いホモトピー群の類として Kan 充填から構成済み。充填選択からの独立性、自然性、自己差の単位元、逆元、三つの差の合成則を証明済み。
- 実際の塔の微分の各セルの係数を、セル境界の連結射とその cofiber 単体・零ホモトピーで計算済み。
- loop 交換の頂点を円の射と標準区間の辺で厳密に照合済み。骨格 fiber の通常の零 loop 比較の包含は明示した逆辺の類と一致し、実際の成分微分の係数を次数二以上の正規化交代微分と (-1)^(セル次元) で計算済み。
- Kan fibration の下で同じ downstairs の類を持つ代表を、射影が指定した単体と厳密に一致する upstairs の代表へ調整済み。整合する類の族を厳密に整合する代表へ直し、極限の群から段ごとの群の逆極限への比較準同型の全射性を証明済み。
- 整合する類を Kan 充填で厳密に整合する球面代表に直し、一般の Kan fibration の塔の比較準同型の全射性を証明済み。零ホモトピーの差から非可換 lim¹ の障害を作り、代表独立性・twisted 作用・基点判定・全射性を証明した。三角形を保持する相対ホーン充填で単射性も証明し、核と lim¹ の基点を保つ全単射と Milnor 完全性を得た。Mittag–Leffler 条件から lim¹ 消滅と比較同型を証明済み。有理有限群 BG の骨格塔では像の安定化、lim¹ 消滅、初段の検出、通常の写像空間と全整数次数への移送まで完了。通常 Tot の有限骨格の重みの Reedy cofibrancy と包含の Reedy 単射性から、各段が Kan、遷移が fibration である実際の塔を構成した。通常 Tot と整合族の極限の基点を保つ同型と射影公式を使い、実際の骨格制限による比較の全射性、核と次次数 lim¹ の全単射、Milnor 単射の基点・像＝核、および比較の全単射性と lim¹ 消滅の同値まで移送済み。BF の全整数次数、および任意の元の `homotopyTotalization` の全整数次数でも、実際の部分 Tot の群への比較・座標公式・全射性・核と lim¹・境界の基点と像＝核・全単射判定・Mittag–Leffler による収束まで完了。有理有限群の標準比較の実際の homotopy fiber の全整数次数の群の消滅も長完全列から証明済み。
- 比較ホーンの fiber 内の終点を比較し、標準の接続準同型と loop 同型の反可換式を全正次数で証明済み。
- 標準の零次数接続写像とその厳密な正方形への自然性を構成し、正次数・零次数の塔の微分の loop 反可換式を証明済み。
- 骨格の零次数・π₀ の反可換式に加え、実際の成分微分のセルへの自然性と、入力を保持した相対商の射の代表を構成済み。
- path の収縮の終点を厳密に計算し、`loopZeroHomotopyEquiv` は通常の円の成分表示の逆元と証明済み。置換円の写像類・セル球面・骨格の各係数でもこの向きを照合済み。
- cochain 次数 d ≥ 1 の全高次数 r で、実際の群の `coefficientDifferential` は通常の正規化微分の (-1)^(d+2+r) 倍と証明済み。次数の標準同定を含む加法準同型の等式、および核・像の一致も証明済み。
- 検証：対象ビルド 6126 jobs、専用監査 966 モジュール・8708 宣言、標準三公理のみ。ともに終了コード 0。
- 全体ビルド：16709 jobs、終了コード 0。前回の F1B.olean の一時欠落は今回は再現せず。所有外ソースは変更していない。

### 残り（依存順）
- 以下は粗い実作業時間の見積もりであり、外部待ちと全体合流の時間を含めない。
- L9e の残項目なし。通常 Tot・BF 模型・元の homotopy Tot の全整数次数の Milnor 界面と、実際の有理標準比較の fiber の群の消滅まで検証済み。
  原典：Goerss–Jardine VII §4、VIII §§1–2、BF 1978 §2。∞ 極限性・安定性は以下の Sp-5。
- Sp-5：任意の小積・通常の小図式の homotopy end・元の hG/Tot の実際の ∞ 極限錐は完了。残りは任意の小さい coherent 図式への接続、全整数次数の基点での π 同型からの Sp の同値検出、loop の完全忠実性・一段移動との比較の高次自然性、Sp の安定性と局所化不変量の値域としての界面。
  これらは後続範囲であり、現段階の主張に含めない。
  原典：HTT Theorem 4.2.4.1、HA §1.4.2。γ3 完了後 16–40 時間。

### 主要宣言（共通接頭辞 `SerrePositivity.KST.Spectra`、以下は名前のみ）
- `KanHomotopyGroup`、`OmegaSpectrum`
- `Sp`
- `OmegaSpectrum.SmallProduct.obj`
- `OmegaSpectrum.SmallProduct.infinityCone_isLimit`、`OmegaSpectrum.CoherentPullback.hasLimit`
- `OmegaSpectrum.pointZeroVertex`、`OmegaSpectrum.sp_fiber_exists`、`OmegaSpectrum.loopSquare`、`OmegaSpectrum.cotensorMappingEquivalence`、`OmegaSpectrum.BasedLoop.circleVertexIso`、`OmegaSpectrum.deloopingVertexIso`、`OmegaSpectrum.nativeLoop`、`OmegaSpectrum.nativeTail`、`OmegaSpectrum.tailMapping_isPullback`、`OmegaSpectrum.tailMappingEquivalence`、`OmegaSpectrum.nativeTailEquivalence`、`RawSpectrumMapping.weightedDiagramEndIso`、`KanSequence.homotopyLimitWedge`、`KanSequence.isLimitOfLevelLimits`、`KanSequence.homotopyLimitWedge_isLimit`、`KanSequence.homotopyLimitEndIso`、`RawSpectrumMapping.isLimitOfLevelLimits`、`RawSpectrumMapping.homotopyLimitIso`、`OmegaSpectrum.homotopyLimitHomHolimEquivalence`、`RawSpectrumMapping.composition_assoc`、`RawSpectrumMapping.pointedComposition`、`RawSpectrumMapping.sourceCotensorNatIso`、`RawSpectrumMapping.homotopyLimitIso_pre`、`InternalHomExchange.composition`、`RawSpectrumMapping.cotensorComparison_composition`、`RawSpectrumMapping.weightedComposition`、`RawSpectrumMapping.homotopyLimitIso_composition`、`OmegaSpectrum.homotopyLimitPointedMappingComparison_composition`、`RawSpectrumMapping.weightedComposition_underlyingIso`、`OmegaSpectrum.homotopyLimitUnderlyingMappingComparison_composition`、`OmegaSpectrum.homotopyLimitHomHolimEquivalence_composition`、`edgewiseEndRightSection`、`OmegaSpectrum.homotopyLimitEdgewiseEndPoint_projection`、`OmegaSpectrum.homotopyLimitCoherentCone`、`OmegaSpectrum.homotopyLimitCoherentCone_cosliceSection`、`OmegaSpectrum.homotopyLimitReflectedEndFamily_homotopyEquivalence`、`OmegaSpectrum.homotopyLimitCoherentCone_isLimit`、`OmegaSpectrum.strictCoherentDiagram_hasLimit`、`homotopyFixedPointsInfinityCone_isLimit`、`homotopyTotalizationInfinityCone_isLimit`、`OmegaSpectrum.cotensorPointedMappingComparison`、`OmegaSpectrum.cotensorEvaluation`、`OmegaSpectrum.cotensorEvaluationPrecomposition_eq`、`OmegaSpectrum.CotensorCompatible.sourceMap_trivialKanFibration`、`OmegaSpectrum.CotensorCompatible.sourceInfinityEquivalence`、`OmegaSpectrum.nativeCotensor`、`OmegaSpectrum.nativeCotensor_sourceIso`、`OmegaSpectrum.nativeCotensorVertexIso`、`OmegaSpectrum.CotensorCompatible.gradedEvaluation`、`OmegaSpectrum.CotensorCompatible.evaluationCylinderInfinityMap`、`OmegaSpectrum.CotensorCompatible.evaluationCylinder_cross`、`OmegaSpectrum.CotensorCompatible.evaluationCylinderInfinityMap_restriction`、`OmegaSpectrum.CotensorCompatible.parameterEvaluation_basepoint`、`EnrichedParameterCylinder.nervePair`、`OmegaSpectrum.nativeCotensorEvaluationFamily`、`OmegaSpectrum.nativeCotensorEvaluationFamily_left`、`OmegaSpectrum.nativeCotensorEvaluationFamily_rightIso`、`OmegaSpectrum.nativeCotensorEvaluationFamily_restriction`、`OmegaSpectrum.functorZeroVertex`、`OmegaSpectrum.CotensorCompatible.zeroEvaluation_factorization`、`OmegaSpectrum.CotensorCompatible.zeroEvaluationTriangleFamily`、`OmegaSpectrum.nativeZeroEvaluationTriangleFamily`、`OmegaSpectrum.nativeZeroEvaluationTriangleFamily_middle_isZero`、`EnrichedParameterCylinder.parameterEdge`、`EnrichedParameterCylinder.nervePair_parameterEdge`、`OmegaSpectrum.CotensorCompatible.zeroEvaluationTriangleFamily_outer`、`OmegaSpectrum.nativeZeroEvaluationTriangleFamily_outer`、`circleGeneratingEdge`、`EnrichedParameterCylinder.parameterCompStruct`、`OmegaSpectrum.nativeCircleEvaluationTriangleFamily`、`OmegaSpectrum.circleEvaluationHorn`、`OmegaSpectrum.circleEvaluationTetrahedron`、`OmegaSpectrum.circleZeroCompanionTriangle`、`OmegaSpectrum.nativeCircleEvaluationSquareFamily`、`OmegaSpectrum.circleEvaluationFunctorSquare_zeroCorner_isZero`、`EnrichedParameterCylinder.fiberEnriched`、`EnrichedParameterCylinder.nervePair_fiber`、`OmegaSpectrum.CotensorCompatible.evaluationFiber_comparison`、`OmegaSpectrum.CotensorCompatible.circleEvaluationNerveFamily_fiber`、`OmegaSpectrum.circleEvaluationHomEdge`、`OmegaSpectrum.nativeCotensorInput`、`OmegaSpectrum.nativeCircleEvaluationTriangleFamily_fiber`、`OmegaSpectrum.nativeCircleEvaluationSquare`、`OmegaSpectrum.nativeCircleEvaluationSquare_cospan`、`OmegaSpectrum.nativeCirclePointLoopCone`、`OmegaSpectrum.pointLoopReferenceCone`、`OmegaSpectrum.pointLoopReferenceCone_isLimit`、`OmegaSpectrum.circlePointLoopComparison`、`OmegaSpectrum.circlePointLoopComparisonExtension`、`OmegaSpectrum.circlePointLoopComparisonEdge_ho_unique`、`OmegaSpectrum.nativeCircleEvaluationSquare_isPullback_iff_comparison`、`weightedSectionsPre_central_trivialKanFibration`、`loopIntervalWeight`、`loopHornWeight`、`loopHornCollapse`、`loopHornCollapseEnd_homotopyEquivalence`、`cospanBKWeightIso`、`cospanBKLoopEndComparison`、`cospanBKLoopEndComparison_homotopyEquivalence`、`loopIntervalEndCircleIso`、`loopIntervalEndCircleIso_inv_central`、`loopCircleBKComparison`、`loopCircleBKComparison_homotopyEquivalence`
- `OmegaSpectrum.homotopyGroupEquivAt`
- `OmegaSpectrum.homotopyFiberLongExact`
- `OmegaSpectrum.rationalization`
- `OmegaSpectrum.rationalizationTensorEquiv`
- `homotopyFixedPoints`
- `homotopyTotalization`
- `homotopyFixedPointsUnit_homotopyMap_injective`
- `SimplicialFunctionComplex.componentEquiv`
- `SkeletalCellAttachment.stageFiberComponentEquiv`
- `PointedFibrationTower.limitGroupEquivOfMittagLeffler`
- `HomotopyTotalizationMilnor.kernelLimOneEquiv`
- `HomotopyTotalizationMilnor.limOneBoundary_range`
- `PointedFibrationTower.kernelLimOneEquiv`
- `PointedFibrationTower.kernelObstruction`
- `PointedFibrationTower.limitGroupComparison`
- `HomotopyTotalizationMilnor.comparison_bijective_iff`
- `SkeletalCellAttachment.coefficientDifferential_all_alternating`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_eq`
- `TowerLimOne.subsingleton_of_mittagLeffler`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_ker`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_range`
- `RationalSkeletalTower.groupTower_isMittagLeffler`
- `SkeletalCellAttachment.coefficientDifferential`
- `RationalLevelNormalizedCochains.positive_cohomology_isZero`
- `rational_homotopyFixedPointsUnit_fiberGroup_subsingleton`
- `rational_homotopyFixedPointsUnit_homotopyMap_bijective`
- `rationalShapiroEquiv`
- `SpectrumMappingAcyclic.isInvertible_of_levelwise`
- `OmegaSpectrum.replacedOrdinaryTotalizationComparison_isInvertible`
- `PartialTotalizationTower.limitIso`
- `OmegaSpectrum.replacedOrdinaryTotalizationComparison_piIsomorphism`

### 依存と提供
- 読取専用：Mathlib の PtSimplex・RelStruct・MulStruct、pushout-product、骨格の相対セル分解、正規化鎖、群 cochain。
- 読取専用：既存 Spectra/ の点つき閉構造・cofiber、Comparison/BasedPathEndpoint の汎用評価式。安定モデル構造は借用しない。
- 読取専用：HomotopicalAlgebra/Simplicial/ のホーン充填・因子分解・AnodyneKanReplacement と一般の Reedy 因子分解。
- 読取専用：InfinityCategories/ の coherent nerve の γ1、Core の Kan 性、HomotopyLimits の Bousfield–Kan end。
- 提供：π_n と関手性・長完全列、BF 対象と Sp、整数 π、置換、有理化、hG/Tot の具体的な模型、骨格の障害計算。
- H_* は K-L2、pro 形式は K-L6、γ3 は N 所有。K 理論の主定理への合流は他レーンの仕事。

### 未コミット
- この保存単位の後、K-Sp 所有ファイルに未コミットなし。保存内容は最新の K-Sp コミットを参照。
- 共有ルート `SerrePositivity.lean` および他レーンの既存差分は触らず、今回のコミット対象にも含めない。

### 既知の問題
- 対象ビルド（6137 jobs）・公理監査（974 modules / 8805 declarations）は成功。全体ビルドも成功（16751 jobs）。初回は並行更新中の `EInfinity.olean` 欠落で失敗したが、その生成を確認して再実行した。前回の所有外 `KFixedSpanFamilies` timeout は今回再現しない。所有外ソースは変更しない。円評価の実際の錐の普遍評価 loop と固定図式を保持し、極限性を具体的な BF 比較辺の可逆性へ帰着済み。通常の BK 重みとホーン重みの自然同型、および指定した collapse による区間 end から元の BK end への比較のホモトピー同値まで完成。区間 end と標準の円の写像空間の厳密同型、および零係数 cospan の元の BK end への指定した射のホモトピー同値も完成。実際のスペクトル Hom 係数への同定と元の円評価の比較辺の可逆性は未完。
- 所有ソースの sorry・追加 axiom はなし。所有宣言の型に `HomotopicalAlgebra.ModelCategory` 定数がないことも Lean 環境を走査して確認済み。
- import 閉包に KanQuillen モジュールなし。`SSet.modelCategoryQuillen` 名前空間は Mathlib のホーン生成射・Fibration の既存 API に使うが、`ModelCategory SSet` は仮定しない。
- 公理監査は私有宣言・推移的な公理依存と、宣言型の ModelCategory 定数を検査する。
- BF cofibrant–fibrant 仕様を承認済み。構造射は単射、随伴は全基点 π_* 同型。厳密 Ω 同型は要求しない。
- 厳密 Ω 同型と厳密極限だけからの局所 Kan 性は未解決だったため改訂した。現仕様では単射の指数版・引き戻し・塔の RLP 閉性で証明する。
- Sp-3 は cohomology 消滅だけで仮定せず、実際の障害補正・lim¹ 消滅・写像空間の検出・BF 比較を通して証明済み。通常 Tot と元の homotopy Tot の全整数次数の Milnor 比較・lim¹ 収束判定も証明済み。通常の小図式の ∞ 極限性も完成。任意の coherent 図式への接続・安定性は未完。

### 次の一手
- Sp-5：具体的な残目標は `coherentNerveEdge (circlePointLoopComparison z)` の可逆性で、`nativeCircleEvaluationSquare_isPullback_iff_comparison` が元の四角形の極限性との同値を与える。通常の BK 重みとの自然同型 `cospanBKWeightIso` と、区間 end から元の BK end への指定した射 `cospanBKLoopEndComparison` の実際のホモトピー同値は完成。`loopIntervalEndCircleIso` と `loopCircleBKComparison_homotopyEquivalence` で標準の円の写像空間から零係数 cospan の元の BK end への指定した比較まで完成した。逆の中央射影は `loopIntervalEndCircleIso_inv_central` により標準円への元の商に沿う制限。次は `simplicialHomDiagram (pointLoopDiagram Y) X` の両端を `mappingPoint_isTerminal` で一点へ同定し、中央を元の Hom に固定したまま零係数 cospan と自然同型を作る。`loopHornCollapseEnd_homotopyEquivalence` は中央の Kan 性だけで成立し、指定した collapse の元の射を保持する。`loopHornCollapse_leftEdge/rightEdge` の式で生成 loop と定値辺の向きを照合できる。この比較を参照錐の Hom–end 比較と、`nativeCircleEvaluationTriangleFamily_fiber` の元の普遍評価へ合成して、実際の BF 比較辺の可逆性を検査する。`circlePointLoopComparisonExtension` は底・両錐・頂点の辺を保持し、別の比較錐の射を使っても頂点のホモトピー類は同じ。対象の loop 模型との同型や切断空間の終域の一致だけでは可逆性を主張しない。極限性の後に `nativeLoopDiagramFamilyIso` へ渡す。一段移動の高次自然性・loop の完全忠実性、任意の coherent 図式の極限、全整数 π 検出・安定性・局所化不変量の値域も残る。
- Sp-4 の任意の図式に対する主比較は `OmegaSpectrum.replacedOrdinaryTotalizationComparison`。Reedy 仮定なしで、実際に置換した通常 Tot の BF 模型から元の `homotopyTotalization` へ送る。各段・全整数次数 π 同型と元の比較辺の Sp の同値性に加え、元の homotopy Tot の ∞ 極限錐も完成した。Sp の安定性は別工程。
- 有限骨格の Reedy cofibrancy は、latching 図式の全ての射で骨格の所属を保存・反映し、その部分図式の余極限の包含を単射とする `CartesianSubfunctorColimit` から証明した。骨格間の latching 正方形は次数ごとの pullback とし、その pushout の比較を単射と証明済み。Mathlib の部分複体骨格と `SSet.sk` の同型や、骨格関手全体の余極限保存を仮定しない。`PartialTotalizationTower.limitIso_hom_projection` と `groupComparison_apply` が通常 Tot の元の制限を計算する。
- L9e 完了。Sp-5 は任意の小積・通常の小図式の ∞ 極限錐を構成済みで、任意の coherent 図式への接続・全整数 π による同値検出・安定性・局所化不変量の値域の界面は未完。共有 γ3 の現状は `e-infinity-algebras.md` 冒頭。∞ 極限性を π 同型だけから仮定しない。

## 範囲と所有

- 作業場所：`SerrePositivity/KST/Spectra/`、namespace `SerrePositivity.KST.Spectra`。
- 集約入口：`SerrePositivity/KST/Spectra.lean`、監査：`scripts/audit_kst_spectra.lean`。
- 共有ルート・他レーン・既存 Spectra/・HomotopicalAlgebra/・InfinityCategories/ は読むだけ。
- 既存の未コミット変更を保存し、他者の新規ファイルをコミットしない。
- 全体の正本は [foundations.md](../foundations.md)、K の正本は [経路](../k-theory-kst-route.md) §13。
- H_* と pro の旧レーンは凍結。γ3・γ4 は N 所有。K の合流は K-基盤レーンが担当する。

## 実装仕様

- Kan 複体の π_n は PtSimplex と RelStruct の商。零次数は pointed set、正次数は群、二以上は可換群。
- fiber と長完全列は実際の Kan fibration の充填から構成する。
- Sp は BF cofibrant–fibrant 型の Ω スペクトルの単体的圏の coherent nerve（γ-B）。
- 構造写像 ΣX_n → X_(n+1) は単射、随伴は全基点で π_* 同型。厳密な Ω 同型を要求しない。
- 写像空間は有限切断の Hom の fibration の塔の極限。指数・引き戻し・塔の相対 RLP で Kan 性を示す。
- π_j は十分高い段の π_(j+k)(X_k) と遷移同型で定義し、整数次数の自然性を保つ。
- 置換は写像柱・境界セル分解・AnodyneKanReplacement の実構成。
- 有理化は正整数の乗法の telescope と π_* のテンソル比較。
- Tot・hG は段ごとの Kan 模型。通常の Tot と BF 置換した homotopy Tot の比較を分ける。
- γ3 後に導来 Sp との比較と ∞ 極限性、続いて安定性と局所化不変量の値域を示す。
- cohomology 消滅だけから塔の収束や Shapiro 全射性を主張しない。
- coefficientDifferential の同定は零性だけでなく像と符号も比較する。

## 原典

| 対象 | 原典 |
| --- | --- |
| Kan、π_n、群の演算、fiber 長完全列 | Kerodon §§3.1–3.2、Goerss–Jardine I §§7–8 |
| セルの係数・正規化・塔の収束 | Goerss–Jardine III §2、VIII §§1–2 |
| 通常の Tot | Goerss–Jardine VII §4、VIII §1 |
| coherent nerve | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| BF 模型 | Bousfield–Friedlander 1978 §2、HTT A.3.3 |
| Sp と ∞ 極限の比較 | HTT 4.2.4.1、HA §1.4.2 |

原典の主張を公理や未証明の入力構造にしない。未確認の定理番号は節番号で示す。

## 検証と保存

- 保存単位ごとに `lake build SerrePositivity.KST.Spectra` と専用公理監査。
- 許容公理は `propext`・`Classical.choice`・`Quot.sound` のみ。私有宣言と推移的依存も監査。
- 主経路の宣言の型に `HomotopicalAlgebra.ModelCategory` がないことを Lean 環境走査で確認。
- `ModelCategory SSet`・cofibrant generation・Quillen bifunctor を主経路の仮定にしない。
- KanQuillen の import は不可。Mathlib のホーン生成射・Fibration API は使用する。
- 工程区切りで全体ビルド。自分の import 閉包の破損を他者の修正で迂回しない。
- `git diff --check`。コミットは所有ファイルだけを `git commit --only`。amend・rebase・reset はしない。
- 本文 300 行以内、引き継ぎ 100 行以内。実施記録はコミットメッセージ。
- 旧本文・型一覧は [archive/L9-spectra-log.md](../archive/L9-spectra-log.md) に保存。
