# SC-W1 段 2e：登録モジュールと宣言の一覧

停止点の数学コミット：`bf9767cdc`。段 2d の報告 `df035c08e` 以後に追加した本体 336 本。

以下はソースに明示した名前付きの数学宣言と、その docstring の先頭の主張。生成宣言と局所インスタンスはこの表と別に公理監査の対象に含む。各束の経緯と検証記録は [route](scheme-w1-2e-route.md)。

## AdicProjectionCompletionInverse

モジュール：`SerrePositivity.AlgebraicGeometry.AdicProjectionCompletionInverse`

| 宣言 | 主張 |
| --- | --- |
| `adicProjectionCompletionInverse` | 射影先の互換族から、元の加群の I 進完備化への線形写像。 |
| `adicProjectionCompletionInverse_left_inverse` | 互換族から戻す写像は、完備化からの標準写像の左逆。 |
| `adicProjectionCompletionInverse_right_inverse` | 互換族から戻す写像は、完備化からの標準写像の右逆。 |
| `adicProjectionCompletionLinearEquiv` | 核の一様評価と像への所属から得られる、I 進完備化と互換族の線形同型。 |

## AdicProjectionFactor

モジュール：`SerrePositivity.AlgebraicGeometry.AdicProjectionFactor`

| 宣言 | 主張 |
| --- | --- |
| `adicProjectionQuotientMap` | IⁿH を殺す射影を、通常の I 進剰余類上へ降ろす。 |
| `adicProjectionQuotientMap_transition` | 射影の互換性は、I 進剰余類からの写像にも降りる。 |
| `adicProjectionCompletionMap` | I 進完備化から、射影先の互換族への標準線形写像。 |

## AdicProjectionInverseComponents

モジュール：`SerrePositivity.AlgebraicGeometry.AdicProjectionInverseComponents`

| 宣言 | 主張 |
| --- | --- |
| `adicProjectionImageToQuotient` | 十分先の射影の像から、元の加群の Iⁿ による商への線形写像。 |
| `compatibleLinearFamiliesEvalToRange` | 互換族を、その成分が属する射影の像へ評価する線形写像。 |
| `adicProjectionCompatibleComponent` | 射影先の互換族を、第 n 番目の I 進剰余類へ戻す線形写像。 |
| `adicProjectionCompatibleComponent_eq_mk` | 互換族の十分先の成分を代表で書けば、戻した成分は同じ代表の剰余類。 |
| `adicProjectionCompatibleComponent_transition` | 戻した各 I 進剰余類は、通常の I 進遷移について互換。 |
| `compatibleLinearFamilies_mem_range_of_stable` | 遷移の像が十分先で射影の像に入れば、互換族の各成分も射影の像に入る。 |

## AdicProjectionNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.AdicProjectionNaturality`

| 宣言 | 主張 |
| --- | --- |
| `adicProjectionQuotientMap_naturality` | 射影の可換性は、I 進剰余類上へ降ろした射影にも成り立つ。 |
| `adicProjectionCompletionMap_naturality_apply` | 完備化から互換族への標準写像は、成分写像と可換。 |

## AdicProjectionSemilinearNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.AdicProjectionSemilinearNaturality`

| 宣言 | 主張 |
| --- | --- |
| `adicProjectionQuotientMap_semilinear_naturality` | 半線形な射影の可換式は、各イデアル冪による剰余類にも降りる。 |
| `adicProjectionCompletionMap_semilinear_naturality_apply` | 完備化から互換族への標準写像は、係数環を変える半線形写像と可換。 |

## AdicSemilinearMap

モジュール：`SerrePositivity.AlgebraicGeometry.AdicSemilinearMap`

| 宣言 | 主張 |
| --- | --- |
| `adicSemilinear_smul_top_le_comap` | イデアルの像の包含から、半線形写像は各イデアル冪の作用を保つ。 |
| `adicSemilinearQuotientMap` | 各イデアル冪による剰余類の間の半線形写像。 |
| `adicSemilinearQuotientMap_transition` | 剰余類の半線形写像は、通常の I 進・J 進遷移と可換。 |
| `adicSemilinearCompletionMap` | イデアル冪を保つ半線形写像が誘導する、Mathlib の完備化の間の半線形写像。 |

## AffineLocalizingCech

モジュール：`SerrePositivity.AlgebraicGeometry.AffineLocalizingCech`

| 宣言 | 主張 |
| --- | --- |
| `cechAwayFactorUnits` | 局所化先では、分母を割る元の冪も可逆に作用する。 |
| `cechSpecRestriction` | Spec の大域切断から標準開への制限。 |
| `cechBasicOpen_le_of_dvd` | 分母の整除に沿う標準開の包含。 |
| `specStandardCechDiagram` | 標準開の交叉上の切断を、積の標準開で表示する係数図式。 |
| `specStandardCechSectionIso` | 標準開の切断と大域切断の局所化の同型。 |
| `specStandardCechSectionIso_naturality` | 標準開の切断と局所化の比較は、交叉を狭める制限に自然。 |
| `specStandardCechDiagramIso` | 局所化を与える前層の、標準開係数図式との自然同型。 |
| `specStandardCech_zero_injective` | 局所化を与える前層の標準開被覆では、増大項からの写像は単射。 |
| `specStandardCech_exact` | 局所化を与える前層の標準開被覆の増大 Čech 完全性。 |
| `cechBasicOpen_denominator` | 分母の積の標準開は、各分母の標準開の有限交叉。 |
| `specStandardCechOpenDiagramIso` | 積の標準開による図式と、実際の有限交叉による図式の自然同型。 |
| `specStandardOpenCech_exact` | Spec の標準開被覆上の実際の切断の増大 Čech の完全性。 |

## AffineModuleCechDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.AffineModuleCechDiagram`

| 宣言 | 主張 |
| --- | --- |
| `affineModuleAwayRestrictionIso` | 二つの分母が互いに整除するときの局所化加群の同型。 |
| `affineCechDenominator` | 有限交叉を定める被覆元の積。 |
| `affineCechDenominator_dvd` | 添字を増やすと、交叉の分母は元の分母の倍数になる。 |
| `affineModuleCechDiagram` | アフィン標準被覆の各有限交叉での局所化加群の図式。 |
| `affineCechDenominator_insert_dvd` | 単元の被覆元を追加しても、交叉の分母は元の分母を割る。 |
| `affineModuleCechDiagram_map_insert_isIso` | 被覆元が単元なら、それを交叉へ追加する制限は同型。 |

## AffineModuleCechMap

モジュール：`SerrePositivity.AlgebraicGeometry.AffineModuleCechMap`

| 宣言 | 主張 |
| --- | --- |
| `affineModuleCechMap` | 加群写像が誘導する、各有限交叉の局所化加群の図式の射。 |
| `affineModuleCechMap_id` | 局所化した係数写像は恒等写像を保つ。 |
| `affineModuleCechMap_comp` | 局所化した係数写像は合成を保つ。 |

## AffineModuleCechUnit

モジュール：`SerrePositivity.AlgebraicGeometry.AffineModuleCechUnit`

| 宣言 | 主張 |
| --- | --- |
| `affineModuleCechUnitInsertionIsIso` | 単元の頂点の挿入は、係数図式のすべての成分で同型。 |
| `affineModuleCechUnit_zero_injective` | 単元の被覆元があれば、増大項からの写像は単射。 |
| `affineModuleCechUnit_cycle_boundary` | 単元の被覆元があれば、増大 Čech の各サイクルは境界。 |
| `affineModuleCechUnit_exact` | 単元の被覆元があれば、増大 Čech の連続する二つの余境界は完全。 |

## AffineModuleLocalizedCech

モジュール：`SerrePositivity.AlgebraicGeometry.AffineModuleLocalizedCech`

| 宣言 | 主張 |
| --- | --- |
| `affineModuleLocalizedCechInsertionIsIso` | 被覆元で局所化すれば、その頂点を交叉へ挿入する制限はすべて同型。 |
| `affineModuleCech_localized_zero_injective` | 各被覆元で局所化すると、増大項からの写像は単射。 |
| `affineModuleCech_localized_exact` | 各被覆元で局所化した、連続する Čech の余境界は完全。 |
| `affineModuleCech_zero_injective` | 単位イデアルを生成する元の標準被覆では、増大項の写像は単射。 |
| `affineModuleCech_exact` | 標準アフィン被覆の増大 Čech の完全性。 |

## AffineQuasicoherentStandardCech

モジュール：`SerrePositivity.AlgebraicGeometry.AffineQuasicoherentStandardCech`

| 宣言 | 主張 |
| --- | --- |
| `specQuasicoherent_isLocalizing` | 準連接層の標準開への制限は、その元での局所化。 |
| `specQuasicoherentStandardOpenCech_zero_injective` | 準連接層の標準開被覆の増大項の単射性。 |
| `specQuasicoherentStandardOpenCech_exact` | Spec 上の準連接層の標準開被覆の増大 Čech 完全性。 |

## CechAdditiveCoefficientComparison

モジュール：`SerrePositivity.AlgebraicGeometry.CechAdditiveCoefficientComparison`

| 宣言 | 主張 |
| --- | --- |
| `fullCechAdditiveCoefficientEquiv` | 各交叉の加法的な比較による Čech 項の加法群の同型。 |
| `fullCechAdditiveCoefficientEquiv_differential` | 係数の制限と可換な加法的比較は、Čech 微分と可換。 |
| `fullCechAdditiveCoefficientEquiv_zero_injective` | 加法的係数比較によって、増大項の単射性を移す。 |
| `fullCechAdditiveCoefficientEquiv_exact` | 加法的係数比較によって、増大 Čech の完全性を移す。 |

## CechCoefficientExactness

モジュール：`SerrePositivity.AlgebraicGeometry.CechCoefficientExactness`

| 宣言 | 主張 |
| --- | --- |
| `fullCechCoefficientEquiv` | 係数の自然同型による、増大項を含む各 Čech 項の同型。 |
| `fullCechCoefficientEquiv_toLinearMap` | 各項の同型は係数写像で与えられる。 |
| `fullCechCoefficientEquiv_differential` | 係数の自然同型は微分と可換。 |
| `fullCechCoefficientEquiv_zero_injective` | 自然同型に沿って増大項の微分の単射性を移す。 |
| `fullCechCoefficientEquiv_exact` | 自然同型に沿って増大 Čech の完全性を移す。 |

## CechDiagramTransport

モジュール：`SerrePositivity.AlgebraicGeometry.CechDiagramTransport`

| 宣言 | 主張 |
| --- | --- |
| `cechDiagramTransport` | 各段の同型に沿って、図式の遷移を移す。 |
| `cechDiagramTransportIso` | 各段の同型は、移した遷移も含めた図式全体の自然同型。 |

## CechHomologyCycleCriterion

モジュール：`SerrePositivity.AlgebraicGeometry.CechHomologyCycleCriterion`

| 宣言 | 主張 |
| --- | --- |
| `cechCyclesOf` | 元で与えたサイクルを、短複体の抽象的な cycles の元にする。 |
| `cechCyclesOf_value` | 元で与えたサイクルの値は、元の元に戻る。 |
| `cechCyclesValue_isCycle` | cycles の元の値は、微分で零になる。 |
| `cechHomologyCycleValue` | サイクルの H の類を opcycles に写すと、その値の類になる。 |
| `cechHomologyMapCycleValue` | 短複体の射の H 上の写像は、サイクルの値に元の射を適用する。 |
| `cechHomologyMap_surjective_of_cycles` | 目標の各サイクルが境界を除いて持ち上がれば、H の射は全射。 |
| `cechHomologyMap_injective_of_cycles` | 境界への写像を元の境界へ戻せれば、H の射は単射。 |
| `cechHomologyMap_isIso_of_cycles` | サイクルの持ち上げと境界の反映から、各次数の H の同型性を得る。 |

## CechLocalizationCochains

モジュール：`SerrePositivity.AlgebraicGeometry.CechLocalizationCochains`

| 宣言 | 主張 |
| --- | --- |
| `cechLocalizationFunctorAdditive` | 分数の局所化関手は加法的。 |
| `cechLocalizationCochainsEquiv` | 各 Čech 次数の局所化と、局所化した係数の Čech の項の比較。 |
| `cechLocalizationCochainsEquiv_mk` | Čech の各項の局所化比較は、各タプルの分母を保つ。 |
| `cechLocalizationCochainsEquiv_differential` | 各項の局所化比較は、増大項を含めて Čech の余境界と可換。 |
| `cechLocalizationComplexIso` | 有限被覆の全タプル Čech 複体と、実際の分数の局所化との同型。 |
| `cechLocalizationCochainsEquiv_naturality` | 各項の分数の比較は、係数図式の射に自然。 |
| `cechLocalizedCochainsDifferential` | 元の Čech の余境界を、分数の局所化の間の写像にする。 |
| `cechLocalizationCochainsEquiv_differential_apply` | 局所化した余境界の比較の、元ごとの式。 |
| `cechLocalizationCochains_exact_of_exact` | 局所化後の係数図式での完全性は、局所化した二つの余境界の完全性を与える。 |

## CechLocalizationPi

モジュール：`SerrePositivity.AlgebraicGeometry.CechLocalizationPi`

| 宣言 | 主張 |
| --- | --- |
| `cechLocalizationPiEquiv` | 有限積と局所化の線形同型。 |
| `cechLocalizationPiEquiv_mk` | 有限積との比較は、すべての成分で同じ分母を保つ。 |
| `cechLocalizationPiEquiv_projection` | 有限積との比較の各成分は、射影を局所化した写像である。 |

## CechLocalizedAwayRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.CechLocalizedAwayRestriction`

| 宣言 | 主張 |
| --- | --- |
| `cechLocalizedAwayRestriction` | 標準開の制限を、さらに外側の分母で局所化した写像。 |
| `cechLocalizedAwayRestriction_surjective` | 追加因子が外側で逆になるなら、局所化した制限は全射。 |
| `cechLocalizedAwayRestriction_injective` | 追加因子が外側で逆になるなら、局所化した制限は単射。 |
| `cechLocalizedAwayRestriction_isIso` | 追加因子を外側で逆にした標準開の制限は、実際の加群の同型。 |

## CechProductCoefficients

モジュール：`SerrePositivity.AlgebraicGeometry.CechProductCoefficients`

| 宣言 | 主張 |
| --- | --- |
| `fullCechProductCoefficientDiagram` | 係数図式の成分ごとの直積。 |
| `fullCechProductCochainsEquiv` | 係数の直積と Čech 項の直積の交換。 |
| `fullCechProductDifferential_apply` | 直積の交換は Čech 微分と成分ごとに可換。 |
| `fullCechProduct_zero_injective` | 各係数図式の増大項の微分が単射なら、直積の微分も単射。 |
| `fullCechProduct_exact` | 各係数図式の増大 Čech が完全なら、直積も完全。 |

## CechQuotientComparison

モジュール：`SerrePositivity.AlgebraicGeometry.CechQuotientComparison`

| 宣言 | 主張 |
| --- | --- |
| `cechQuotientComparison` | 同じ核を持つ二つの全射の、共通の元の加群から定まる比較。 |
| `cechQuotientComparison_projection` | 商の比較は、元の加群からの二つの射影と可換。 |

## CechRefinementCone

モジュール：`SerrePositivity.AlgebraicGeometry.CechRefinementCone`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementConeTerm` | 自然数で添字付けした cone の項。 |
| `cechRefinementConeDifferential` | 負一から移した cone の微分。 |
| `cechRefinementConeDifferential_squared` | この添字付けでも cone の微分の二乗は零。 |
| `cechRefinementCone` | 共通アフィン細分の射の完全性を測る、自然数添字の cone。 |

## CechRefinementConeDouble

モジュール：`SerrePositivity.AlgebraicGeometry.CechRefinementConeDouble`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementConeGrid` | 行の cone を並べた二重図式の項。 |
| `cechRefinementConeHorizontal` | 二重図式の水平方向は、各行の cone の微分。 |
| `cechRefinementConeVertical` | 二重図式の垂直方向は、二つの列方向の射の直積。 |
| `cechRefinementConeVertical_squared` | 列方向の二乗が零なら、cone の列方向の二乗も零。 |
| `cechRefinementConeGrid_commute` | 四角の可換性は、cone の二つの微分の可換性を与える。 |
| `cechRefinementConeGrid_colExact` | 元の二重図式の列が完全なら、cone の各列も完全。 |
| `cechRefinementConeGrid_zero_row_exact` | 正の行の cone と全ての列が完全なら、零番の行の cone も完全。 |
| `cechRefinementConeGrid_homologyMap_isIso` | B1 の二重図式の判定から得る、零番の行の Čech H の同型性。 |

## CechRefinementConeExactness

モジュール：`SerrePositivity.AlgebraicGeometry.CechRefinementConeExactness`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementCone_zero_kernel` | 増大項で恒等を誘導する射の cone は、第零項で核が零。 |
| `cechRefinementCone_cycle_boundary` | cone の正次数の各サイクルは境界。増大項を保つ二つの完全な列を用いる。 |

## CechRefinementConeHomology

モジュール：`SerrePositivity.AlgebraicGeometry.CechRefinementConeHomology`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementCone_quasiIsoAt` | 自然数添字の cone が完全なら、元の射は各次数で quasi-isomorphism。 |
| `cechRefinementCone_homologyMap_isIso` | cone の完全性が与える、元の複体の各次数の H の同型性。 |

## CechRefinementConeMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechRefinementConeMap`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementConeMapTerm` | cone の各項に可換四角の成分を適用する。 |
| `cechRefinementConeMapTerm_differential` | 可換四角の成分は cone の微分と可換。 |
| `cechRefinementConeMap` | 可換四角が誘導する cone の射。 |
| `cechRefinementConeMapTerm_comp` | cone の項への写像は合成を保つ。 |
| `cechRefinementConeMapTerm_id` | cone の項への恒等写像。 |
| `cechRefinementConeMapTerm_zero` | cone の項への零写像。 |

## CechTupleCarrier

モジュール：`SerrePositivity.AlgebraicGeometry.CechTupleCarrier`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleChainsOn_map` | 生成元の台の条件から、鎖の写像の台の条件を得る。 |
| `cechTupleChainsOn_single_mem` | 台を指定した生成元の所属。 |
| `cechTupleChainsOn_boundary` | 境界は指定した頂点集合を保つ。 |
| `cechTupleChainsOn_prepend` | 集合内の頂点の先頭追加は、その集合を保つ。 |
| `cechTupleChainsOn_reindex` | 再添字付けは、頂点集合の像へ鎖を送る。 |
| `cechTupleComparisonHomotopy_stable_carrier` | 鎖写像で保たれる一つの頂点集合は、比較ホモトピーでも保たれる。 |

## CechTupleContraction

モジュール：`SerrePositivity.AlgebraicGeometry.CechTupleContraction`

| 宣言 | 主張 |
| --- | --- |
| `CechTupleChains` | 長さ `k` のタプルを生成元とする自由整数加群。 |
| `cechTupleBoundary` | 各頂点の削除の交代和で定める境界。 |
| `cechTupleBoundary_squared` | 概要：全タプルの増大鎖の境界を二回適用すると零になる。 |
| `cechTuplePrepend` | 固定頂点を各タプルの先頭に付ける。 |
| `cechTupleBoundary_prepend` | 概要：正の長さのタプルで境界と先頭追加の反交換式を与える。 |
| `cechTupleComparisonHomotopy` | 概要：全タプルの恒等鎖写像と、増加タプルを経由する鎖写像 P の間のホモトピー候補。 |
| `cechTupleComparisonHomotopy_succ_single` | 概要：全タプルの恒等鎖写像と、増加タプルを経由する鎖写像 P の間のホモトピー候補。 |
| `cechTupleChainsOn` | すべての頂点が T に入るタプルで生成される部分鎖加群。 |
| `cechTupleComparisonHomotopy_mem_chainsOn` | 概要：ホモトピーの各項の頂点は、入力タプルの頂点集合に収まる。 |
| `cechTupleComparisonHomotopy_identity` | 概要：増大項で恒等な鎖写像 P に対し、帰納定義したホモトピーの方程式を示す。 |

## CechTupleRefinementHomotopy

モジュール：`SerrePositivity.AlgebraicGeometry.CechTupleRefinementHomotopy`

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementAmbient` | 直和添字の左側を一つ目の写像で右側へ移す。 |
| `cechRefinementProjection` | 直和添字を二つ目の写像により元の目標へ戻す。 |
| `cechTupleRefinementHomotopy` | 二つの再添字付けをつなぐ整数鎖のホモトピー。 |
| `cechTupleRefinementHomotopy_identity` | 再添字付けの比較ホモトピーの方程式。 |

## CechTupleRefinementSupport

モジュール：`SerrePositivity.AlgebraicGeometry.CechTupleRefinementSupport`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleRefinementHomotopy_carrier` | ホモトピーの値の頂点は、入力タプルの二つの像に含まれる。 |
| `cechTupleRefinementHomotopy_support` | ホモトピーの各出力タプルの台は、二つの像の和集合の中にある。 |

## CechTupleReindex

モジュール：`SerrePositivity.AlgebraicGeometry.CechTupleReindex`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleReindex` | 頂点の写像に沿う、タプルの整数鎖の再添字付け。 |
| `cechTupleReindex_single` | 再添字付けはタプルの生成元をそのまま写す。 |
| `cechTupleReindex_comp` | 再添字付けは合成を保つ。 |
| `cechTupleReindex_zero` | 長さ零の再添字付けは、添字の自己写像では恒等。 |
| `cechTupleReindex_boundary` | 頂点の再添字付けは増大境界と可換。 |

## CechZeroCochains

モジュール：`SerrePositivity.AlgebraicGeometry.CechZeroCochains`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleSupport_empty` | 空タプルの台は空集合。 |
| `fullCechZeroCochainsEquiv` | 長さ零の Čech 項と、係数図式の空集合の値の同型。 |
| `fullCechZeroCochainsEquiv_naturality` | 空交叉の係数との同定は、係数図式の射に自然。 |
| `fullCechZeroCochainsEquiv_exact` | 増大項を空交叉の係数へ置き換えても、増大 Čech の完全性は同じ。 |

## FrobeniusAdicControl

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusAdicControl`

| 宣言 | 主張 |
| --- | --- |
| `frobeniusIdeal_map_le_pow` | Frobenius による I の像は、通常のイデアル冪 Iᵖ に含まれる。 |
| `frobeniusIdeal_map_le_self` | Frobenius による I の像は、I 自身にも含まれる。 |
| `frobeniusSemilinear_ideal_power_control` | Frobenius 半線形写像は、Iⁿ 倍を I^(p*n) 倍に送る。 |
| `frobeniusSemilinearCompletionMap` | Frobenius 半線形写像が誘導する、I 進完備化の間の Frobenius 半線形写像。 |
| `frobeniusScalarSemilinearMap` | 基底環の実際の Frobenius を、Frobenius 半線形な加群写像として見る。 |

## FrobeniusAdicQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusAdicQuotient`

| 宣言 | 主張 |
| --- | --- |
| `frobeniusSemilinearShiftedQuotientMap` | Frobenius 半線形写像は、指数を p 倍する I 進商の写像を与える。 |
| `frobeniusSemilinearShiftedQuotientMap_transition` | 指数を p 倍する Frobenius 商写像は、I 進遷移と可換。 |
| `frobeniusSemilinearCompletionMap_of` | 完備化上の Frobenius 半線形写像は、元の加群からの写像を保つ。 |

## GradedOriginalProjCech

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjCech`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjCechOpen` | scalar の指定の前の、元の Proj の標準開。 |
| `gradedOriginalProjCechOpen_intersection` | 元の Proj の標準開の交叉は、変数の像の積での標準開。 |
| `gradedOriginalProjCechSectionLinearEquiv` | carrier の正規化前の実際の標準開へ、非空交叉の係数を移す線形同型。 |
| `gradedOriginalProjCechSectionLinearEquiv_naturality` | carrier の正規化前の切断への比較は、標準開を狭める射に自然。 |
| `gradedOriginalProjNativeCechComplexIso` | 共通の係数環上の標準開計算と、元の Proj の Čech 複体の同型。 |

## GradedOriginalProjCechDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechDiagram`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalRingDiagramModule` | 次数付き環の図式を、共通の多項式環上の加群の図式として扱う。 |
| `gradedOriginalRingDiagramMap` | 元の各段の grading の、環の遷移に沿う次数付き環の射。 |
| `gradedOriginalRingChartDiagram` | 共通基底上の次数零チャートの、遷移を含めた係数図式。 |
| `gradedOriginalProjNativeCechDiagram` | 各段で元の Proj の構造層を使う、実際の Čech 複体の図式。 |
| `gradedOriginalProjNativeCechDiagramIso` | 各段だけでなく、図式全体での次数零チャートと元の Proj の自然同型。 |
| `gradedOriginalProjNativeCechDiagram_map` | 移した図式の遷移は、元の Proj の実際の構造層の引き戻しそのもの。 |

## GradedOriginalProjCechMaps

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechMaps`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjCech_preimageOpen` | 元の grading の Proj の射は、同じ変数の標準開を引き戻す。 |
| `gradedOriginalProjNativeCechMap` | 元の二つの grading の間の、実際の構造層の Čech の引き戻し。 |
| `gradedOriginalProjCech_intersection_le` | 元の grading の標準開の交叉を引き戻す包含。 |
| `gradedOriginalProjNativeCechMap_apply` | 共通基底上での元の Proj の Čech の射は、実際の appLE の引き戻し。 |
| `gradedOriginalProjNativeCechComplexIso_apply` | 共通基底の加群の複体と元の Proj の切断の比較を、タプルごとに計算する。 |

## GradedOriginalProjCechNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechNaturality`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `gradedOriginalProjNativeCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |

## GradedOriginalProjCechScalarRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechScalarRestriction`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjCoefficientScalarIso` | 段の基底環での構造層の係数を制限すると、共通の基底環での係数と自然に同型。 |
| `gradedOriginalProjCechScalarRestrictionIso` | 段ごとの基底環の制限と、同じ実際の Proj の Čech 複体の比較。 |

## GradedOriginalProjFilteredHomology

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjFilteredHomology`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjNativeFilteredHomologyIso` | 各段と極限先の両方で、元の Proj の実際の構造層を使う filtered Čech H の比較。 |

## GradedOriginalProjFrobeniusEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjFrobeniusEvaluation`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalChartLinearEquiv_frobenius` | 共通基底のチャートの Frobenius は、元の grading の斉次局所化の p 乗と一致。 |
| `gradedOriginalProjNativeChart_frobenius` | 共通基底での計算を元の Proj の切断へ戻しても、Frobenius は実際の p 乗。 |

## GradedOriginalProjRingMapSections

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjRingMapSections`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |
| `gradedOriginalProjRingMapSections_apply` | 元の grading を使う実際の切断への、斉次分数ごとの自然性。 |

## GradedOriginalProjScalarNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjScalarNaturality`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalProjScalarNaturality_fraction` | 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 |
| `gradedOriginalScalarToGlobalSections_naturality` | Proj の引き戻しは、元の基底環の大域スカラーを保つ。 |

## GradedOriginalProjSections

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalProjSections`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalScalarToZero` | 基底環のスカラーは零次成分に属する。 |
| `gradedOriginalScalarToGlobalSections` | 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 |
| `gradedOriginalScalarToGlobalSections_restrict` | 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 |
| `gradedOriginalAway_scalar_mul` | 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 |
| `gradedOriginalProjAwaySectionLinearEquiv` | 正次数の標準開の構造層の環同型は、元の基底環上でも線形。 |
| `gradedOriginalProjAwaySectionLinearEquiv_pow` | 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 |
| `gradedOriginalScalarToGlobalSections_comp` | 共通の基底環の大域スカラーは、元の基底環を通る合成と一致する。 |

## GradedOriginalScalarRingMap

モジュール：`SerrePositivity.AlgebraicGeometry.GradedOriginalScalarRingMap`

| 宣言 | 主張 |
| --- | --- |
| `gradedOriginalScalarRingMap` | 異なる carrier の次数付き環の射を、共通の基底環の部分加群の次数の射に移す。 |
| `gradedScalarAwayIso_map` | 共通基底への正規化と、実際の斉次局所化の射は可換。 |
| `gradedOriginalScalarRingMap_denominator` | 元の grading の射は、標準開の分母を同じ変数の像の積へ送る。 |
| `gradedOriginalScalarRingMap_powers` | 元の grading の射で標準開の分母の冪を移す包含。 |
| `gradedOriginalChartLinearEquiv_map` | 共通基底の加群でのチャートの射を、元の grading の斉次局所化の射へ戻す。 |

## GradedScalarComponents

モジュール：`SerrePositivity.AlgebraicGeometry.GradedScalarComponents`

| 宣言 | 主張 |
| --- | --- |
| `gradedScalarComponents` | 元の次数の carrier を、指定した基底環上の部分加群として扱う。 |
| `mem_gradedScalarComponents` | scalar を指定し直しても、各次数の所属の条件は変わらない。 |
| `gradedScalarComponentsGradedRing` | scalar を指定し直した次数成分は、同じ分解を持つ次数付き環になる。 |
| `gradedScalarToOriginal` | scalar を指定した次数付き環から、元の次数付き環への恒等写像。 |
| `gradedOriginalToScalar` | 元の次数付き環から、scalar を指定した次数付き環への恒等写像。 |
| `gradedScalarAwayIso` | 同じ carrier を持つ二つの grading の斉次局所化は、環として自然に同型。 |
| `gradedScalarAwayIso_val` | 二つの grading の比較は、周囲の通常の局所化の値を保つ。 |
| `gradedScalarAwayIso_awayMap` | carrier の比較は、標準開を狭める斉次局所化の制限と可換。 |
| `gradedOriginalAwayModule` | generic な grading の斉次局所化の R 加群構造。通常の局所化への単射で移す。 |
| `gradedScalarAwayLinearEquiv` | 同じ grading の carrier の比較は、指定した基底環上でも線形。 |
| `gradedScalarComponentsGradedSMul` | 係数環を明示した carrier 上にも、同じ次数付き作用がある。 |
| `gradedSubmoduleScalarRestrictionMemClass` | 大きい基底環の部分加群は、共通の小さい基底環の作用でも閉じる。 |

## LinearCompatibleFamilies

モジュール：`SerrePositivity.AlgebraicGeometry.LinearCompatibleFamilies`

| 宣言 | 主張 |
| --- | --- |
| `compatibleLinearFamilies` | 線形な遷移写像に関する互換族の部分加群。 |
| `compatibleLinearFamiliesEval` | 互換族を第 n 成分で評価する線形写像。 |

## LinearCompatibleFamiliesEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesEquiv`

| 宣言 | 主張 |
| --- | --- |
| `compatibleLinearFamiliesEquiv_inverse_commute` | 互換な成分同型の逆写像も、逆向きに遷移と可換。 |
| `compatibleLinearFamiliesEquiv` | 成分ごとの互換な線形同型が誘導する、互換族の線形同型。 |

## LinearCompatibleFamiliesMap

モジュール：`SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesMap`

| 宣言 | 主張 |
| --- | --- |
| `compatibleLinearFamiliesMap` | 遷移と可換な成分写像が誘導する、互換族の間の線形写像。 |

## LinearMapZeroOnSpan

モジュール：`SerrePositivity.AlgebraicGeometry.LinearMapZeroOnSpan`

| 宣言 | 主張 |
| --- | --- |
| `linearMap_zero_on_span_of_smul_generators` | 生成元のすべての B 倍で零なら、R 線形写像はその B 生成部分加群で零。 |

## LinearRangeDescent

モジュール：`SerrePositivity.AlgebraicGeometry.LinearRangeDescent`

| 宣言 | 主張 |
| --- | --- |
| `linearRangeDescent` | ker f⊆ker g なら、g を f の像から降ろせる。 |

## ModuleCechScalarExtension

モジュール：`SerrePositivity.AlgebraicGeometry.ModuleCechScalarExtension`

| 宣言 | 主張 |
| --- | --- |
| `moduleCechScalarExtension` | スカラーを制限した係数への射の、図式に自然なテンソル積からの延長。 |
| `moduleCechScalarExtension_one_tmul` | 自然なテンソル積からの射は、1 と元の切断の純テンソルを引き戻す。 |

## OpenCoverCech

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCech`

| 宣言 | 主張 |
| --- | --- |
| `cechOpenIntersection` | 有限個の開集合の交叉。空交叉は全空間。 |
| `cechOpenIntersection_antitone` | 添字集合が増えると交叉は小さくなる。 |
| `openCoverCechDiagram` | 前層を、有限交叉上の切断の共変な係数図式と見る。 |
| `cechOpenIntersection_refinement` | タプルに沿う細分の包含。重複した添字も許す。 |
| `openCoverCechRefinementCochains` | 細分による全タプル Čech 項の制限。 |
| `openCoverCechRefinementCochains_apply` | 細分による制限の成分表示。 |
| `openCoverCechRefinementCochains_differential` | 細分の制限は余境界と可換。 |
| `openCoverCechRefinementMap` | 細分による Čech 複体の射。 |
| `openCoverCechCoefficientMap` | 係数前層の射が有限交叉の係数図式に誘導する射。 |
| `openCoverCechRefinementCochains_naturality` | 細分の制限は係数前層の自然変換に自然。 |
| `openCoverCechRefinementCochains_id` | 恒等細分は恒等写像を与える。 |
| `openCoverCechRefinementCochains_comp` | 二つの細分を続けた制限は、合成細分の制限。 |

## OpenCoverCechAcyclic

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechAcyclic`

| 宣言 | 主張 |
| --- | --- |
| `OpenCoverCechAcyclic` | 係数前層の増大 Čech の完全性を表す補助の述語。 |
| `openCoverCechCoefficientIso` | 係数前層の自然同型を有限交叉の係数図式へ移す。 |
| `openCoverCechAcyclic_of_iso` | 自然同型な係数前層へ、増大 Čech の完全性を移す。 |
| `openCoverCechAcyclic_of_cycles` | 増大項の核の消滅と、正長の各サイクルの前像から完全性を得る。 |
| `openCoverCechAcyclic_of_double_zero_row` | 二重 Čech の零番の行の完全性から、元の前層の Čech 完全性を得る。 |
| `openCoverIntersectionPresheafTopIso` | 全空間との交叉を取る前層は、元の前層と自然に同型。 |
| `openCoverCechDouble_zero_col_exact` | 元の前層の Čech 完全性から、二重図式の零番の列の完全性を得る。 |
| `openCoverCechAcyclic_of_refinement` | 細分の完全性と各交叉上の完全性から、元の被覆の増大 Čech 完全性を得る。 |

## OpenCoverCechAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechAugmentation`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechZeroEquiv` | 開被覆の空タプルの項と、大域切断の同型。 |
| `openCoverCechZeroEquiv_symm_apply` | 大域切断を空タプルの項へ戻すと、その交叉への制限になる。 |
| `openCoverCechAugmentation` | 大域切断から各被覆開の切断への対角の制限。 |
| `openCoverCechAugmentation_eq` | 対角の制限は、空タプルの項からの Čech 微分と一致。 |
| `openCoverCechAugmentation_squared` | 対角の制限のあとに Čech 微分を適用すると零。 |
| `openCoverCechAugmentation_injective` | 増大 Čech が完全なら、大域切断からの対角の制限は単射。 |
| `openCoverCechAugmentation_exact` | 増大 Čech の完全性は、大域切断からの対角の制限でも完全。 |
| `openCoverCechRefinement_augmentation` | 細分の写像は、共通の大域切断からの増大写像を保つ。 |

## OpenCoverCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechComparison`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechRefinementH` | 実際の細分写像が誘導する Čech H の射。 |
| `openCoverCechCoefficientH` | 係数前層の射が誘導する Čech H の射。 |
| `openCoverCechComparisonIso` | 共通細分を用いる、二つの被覆の Čech H の比較。 |
| `openCoverCechComparisonIso_naturality` | 共通細分による Čech H の比較は係数前層の射に自然。 |
| `openCoverCechRefinementH_eq` | 細分写像の選択を変えても、誘導される Čech H の射は同じ。 |
| `openCoverCechComparisonIso_choice` | 同じ共通細分への添字の選択によらず、被覆間の Čech H の比較は同じ。 |
| `openCoverCechComparisonIso_refine` | 共通細分をさらに細分しても、Čech H の被覆間の比較は変わらない。 |
| `openCoverCechComparisonIso_trans` | 一つの共通細分で作る三つの Čech H の比較は合成に整合する。 |

## OpenCoverCechDouble

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechDouble`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechDoubleTerm` | 二つの被覆の実際の増大 Čech の二重図式の項。 |
| `openCoverCechDoubleHorizontal` | 二重 Čech の水平方向の余境界。 |
| `openCoverCechDoubleVertical` | 二重 Čech の垂直方向の余境界。 |
| `openCoverCechDoubleHorizontal_squared` | 水平方向の微分の二乗は零。 |
| `openCoverCechDoubleVertical_squared` | 垂直方向の微分の二乗は零。 |
| `openCoverCechDouble_commute` | 二つの方向の Čech 微分は可換。 |
| `openCoverCechDouble_rowExact` | 細分の包含から、正次数の行の完全性を得る。 |
| `openCoverCechDouble_colExact` | 各水平交叉上の増大 Čech が完全なら、その直積である列も完全。 |
| `openCoverCechDouble_exact_zero_iff` | 二重 Čech に既存 B1 の零番の行・列の比較を適用する。 |

## OpenCoverCechEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechEvaluation`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechEvaluateAt` | タプルの整数鎖を、指定した開集合上の切断として評価する。 |
| `openCoverCechEvaluateAt_single` | 一つのタプルの評価は切断の制限。 |
| `openCoverCechEvaluateAt_restrict` | 台に現れる全タプルの交叉に入る開集合からは、更に制限できる。 |
| `openCoverCechEvaluateAt_boundary_single` | 境界の生成元の評価は、余境界のその生成元での評価。 |
| `openCoverCechEvaluateAt_boundary` | 台に現れる交叉が指定開集合を含めば、境界と余境界は評価で対応する。 |
| `openCoverCechEvaluateAt_naturality` | 指定開集合での評価は、係数前層の射に自然。 |

## OpenCoverCechFunctor

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechFunctor`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechDiagramFunctor` | 前層から有限交叉の係数図式への関手。 |
| `openCoverCechDiagramFunctorAdditive` | 有限交叉への制限は、係数の射の加法を保つ。 |
| `fullCechComplexFunctorAdditive` | 全タプル Čech 複体の係数関手は、射の加法を保つ。 |
| `openCoverCechFunctor` | 前層から被覆の通常の Čech 複体への関手。 |
| `openCoverCechFunctorAdditive` | 前層から Čech 複体への関手は加法的。 |

## OpenCoverCechRefinementConeExact

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementConeExact`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechRefinementCone_exact` | 共通増大項を保つ、二つの完全な Čech の細分写像の cone の完全性。 |

## OpenCoverCechRefinementHomology

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementHomology`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechRefinement_homologyMap_isIso` | 各交叉上の完全性から、細分の実際の Čech H の射は同型。 |

## OpenCoverCechRefinementHomotopy

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementHomotopy`

| 宣言 | 主張 |
| --- | --- |
| `cechOpenIntersection_refinement_union` | 細分の交叉は、二つの添字の像を合わせた交叉に含まれる。 |
| `openCoverCechRefinementHomotopy_support` | 比較ホモトピーに現れるタプルの交叉は、細分の交叉を含む。 |
| `openCoverCechRefinementHomotopyTerm` | 細分の二つの選択を比較する Čech の次数一低い成分。 |
| `openCoverCechRefinementHomotopyTerm_zero` | 長さ零での比較成分は零。 |
| `openCoverCechRefinementHomotopyTerm_boundary` | 比較鎖の境界への評価は、比較コチェインの余境界に対応する。 |
| `openCoverCechRefinementHomotopyTerm_identity` | 二つの細分写像は、制限付きの比較成分によるコチェインホモトピーで結ばれる。 |

## OpenCoverCechRefinementIndependence

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementIndependence`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechRefinementHomotopyComponent` | 細分比較の複体としてのホモトピーの成分。 |
| `openCoverCechRefinementHomotopyComponent_succ` | 連続する次数での比較ホモトピーの成分。 |
| `openCoverCechRefinementHomotopy` | 同じ細分の二つの添字の選択は、コチェイン写像としてホモトピック。 |
| `openCoverCechRefinement_homologyMap_eq` | Čech H 上の細分の射は、細分の添字の選択によらない。 |

## OpenCoverCechRefinementNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementNaturality`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechRefinementMap_naturality` | 細分の複体の射は係数前層の射に自然。 |
| `openCoverCechRefinementMap_id` | 恒等細分が誘導する複体の射は恒等。 |
| `openCoverCechRefinementMap_comp` | 細分の複体の射は細分の合成を保つ。 |
| `openCoverCechRefinement_homology_naturality` | 各次数の Čech H の細分比較は、係数前層の射に自然。 |

## OpenCoverCechResolution

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechResolution`

| 宣言 | 主張 |
| --- | --- |
| `openCoverIntersectionPresheaf` | 固定した開集合との交叉上の切断を取る前層。 |
| `openCoverIntersectionPresheafMap` | 固定する開集合を狭めるときの交叉前層の制限。 |
| `openCoverCechResolution` | 開被覆の増大 Čech の一つの項を前層にする。 |
| `openCoverCechResolutionDifferential` | 増大 Čech の余境界は開集合について自然。 |
| `openCoverCechResolutionDifferential_squared` | 前層としての増大 Čech の微分の二乗は零。 |

## OpenCoverCechResolutionRows

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechResolutionRows`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechResolutionRowIso` | 二重 Čech の一つの行の係数を、交叉上の係数図式の直積として表示する。 |
| `cechOpenIntersection_le_tuple_member` | 正長の交叉は、その中に現れる任意の一つの被覆開に含まれる。 |
| `openCoverCechResolutionRow_zero_injective` | 細分である二重 Čech の正次数の行では、増大項からの微分は単射。 |
| `openCoverCechResolutionRow_exact` | 細分である二重 Čech の正次数の行は、増大 Čech として完全。 |

## OpenCoverCechResolutionZero

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechResolutionZero`

| 宣言 | 主張 |
| --- | --- |
| `openCoverResolutionZeroIntersection` | 長さ零の被覆交叉を付けても、指定開集合は変わらない。 |
| `openCoverCechResolutionZeroComponentIso` | 増大 Čech 前層の零項と元の前層の、各開集合での同型。 |
| `openCoverCechResolutionZeroIso` | 増大 Čech 前層の零項は、開集合について自然に元の前層と同型。 |

## OpenCoverCechRestrictedCover

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechRestrictedCover`

| 宣言 | 主張 |
| --- | --- |
| `cechOpenRestrictedIntersection_eq` | 指定開集合との各交叉の等式を、有限交叉の等式へ移す。 |
| `openCoverCechRestrictedCoverIso` | 指定開集合内で同じ被覆の、有限交叉の係数図式の自然同型。 |
| `openCoverCechAcyclic_of_intersection_eq` | 指定開集合内で同じ被覆へ、増大 Čech の完全性を移す。 |
| `openCoverIntersectionPresheafNestedIso` | 二段階の交叉前層は、交叉した開集合の前層に自然に同型。 |
| `openCoverIntersectionPresheafNestedIsoOfLe` | 小さい開集合での交叉なら、先の大きい開集合の制限は冗長になる。 |

## OpenCoverCechScalarRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechScalarRestriction`

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechAcyclic_restrictScalars` | 係数環を制限しても、増大 Čech の完全性は保たれる。 |

## OpenCoverCechSplitIntersection

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverCechSplitIntersection`

| 宣言 | 主張 |
| --- | --- |
| `cechOpenIntersection_insert` | 頂点の挿入に対応する開集合の交叉。 |
| `openCoverCechSplitIntersection_isIso` | 交叉全体を含む頂点の挿入による、切断の制限は同型。 |
| `openCoverCechSplitIntersection_zero_injective` | 交叉全体を含む頂点がある場合、増大項の微分は単射。 |
| `openCoverCechSplitIntersection_exact` | 交叉全体を含む頂点がある前層の増大 Čech の完全性。 |

## ProjStandardOpen

モジュール：`SerrePositivity.AlgebraicGeometry.ProjStandardOpen`

| 宣言 | 主張 |
| --- | --- |
| `proj_basicOpen_finset_prod` | 概要：標準開の有限交叉を対応する元の積の標準開として表す。 |
| `projStandardProduct_degree` | 次数一の元の積の次数は、添字集合の濃度に等しい。 |
| `projStandardIntersectionIso` | 概要：次数一の標準開の非空有限交叉上の切断を、積での次数零局所化と同一視する。 |
| `projStandardAffineOpenCover` | 次数一の生成元に対応する標準開は Proj のアフィン開被覆をなす。 |
| `isAffineOpen_projStandardIntersection` | 次数一の標準開の非空有限交叉はアフィン開である。 |
| `projStandardProduct_factor` | 添字集合を広げた積を、元の積と新しい添字の積に分ける。 |
| `projStandardIntersectionRestriction` | 概要：添字集合を広げたときの次数零局所化の写像を与える。 |
| `projStandardIntersectionIso_naturality` | 概要：次数零局所化の写像は標準開の切断の制限と可換になる。 |
| `projStandardIntersectionRestriction_id` | 同じ標準開への次数零局所化の制限は恒等写像。 |
| `projStandardIntersectionRestriction_comp` | 添字集合を二度広げる制限は、一度に広げる制限と一致する。 |
| `projStandardLocalizationDiagram` | 非空有限交叉の添字に対する、次数零局所化と制限写像の図式。 |
| `projStandardOpenDiagram` | 非空有限交叉の添字を、Proj の開集合とその包含の逆向きの図式に送る。 |
| `projStandardLocalizationDiagramIso` | 概要：Proj の標準開の切断の図式を、各交叉における次数零局所化の図式と比較する。 |

## ProjectiveCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechComparison`

| 宣言 | 主張 |
| --- | --- |
| `CechTupleMapPreservesSupport` | 各生成元の像に現れるタプルの頂点が、元の頂点集合に収まること。 |
| `CechTupleMapPreservesSupport` | 頂点部分集合ごとの鎖加群を保つ線形写像は、生成元の頂点集合を保つ。 |
| `fullCechTranspose_add` | 転置は鎖写像の和を保つ。 |
| `fullCechTranspose_sub` | 転置は鎖写像の差を保つ。 |
| `fullCechTranspose_comp` | 頂点集合を保つ鎖写像の合成は、転置すると逆順になる。 |
| `fullCechTranspose_boundary` | 交代境界の転置は全タプル版の余境界。 |
| `cechTupleBoundary_preservesSupport` | 境界でタプルの頂点集合は増えない。 |
| `fullCechTransposedHomotopy_identity` | 概要：頂点集合を保つ比較ホモトピーは、制限写像付き Čech コチェイン上で同じ方程式を満たす。 |
| `cechTupleSortProject` | 重複するタプルを零にし、単射なタプルを符号付きの増加タプルへ送る。 |
| `cechTupleSupport_perm` | 添字の置換はタプルに現れる頂点集合を変えない。 |
| `cechTupleSortingPerm_comp` | タプルの置換を整列置換の前に合成すると、元の整列置換を得る。 |
| `cechTupleSortProject_single_perm` | 符号付き整列の値は、元のタプルの置換の符号だけ変わる。 |
| `cechTupleSortProject_mem_chainsOn` | 符号付き整列は、与えられた頂点集合内のタプル鎖を保つ。 |
| `cechTupleSortProject_single_of_strictMono` | 整列写像はすでに狭義増加なタプルを固定する。 |
| `cechTupleSortProject_zero` | 空タプルの生成する増大項では整列写像が恒等になる。 |
| `cechTupleSortProject_boundary_perm` | 整列した境界は、タプルの置換の符号に従って変わる。 |
| `cechTupleSortProject_boundary` | 概要：符号付き整列は全タプルの境界と可換になる。 |
| `fullCechTranspose_sortProject` | 符号付き整列の転置は、成分制限と符号付き延長の合成。 |
| `orderedCechExtendFull_comp_differential` | 符号付き延長は狭義増加版と全タプル版の余境界に可換。 |
| `fullCechRestrictOrdered_extendFull` | 符号付き延長を狭義増加タプルに制限すると、元のコチェインを得る。 |
| `orderedCechComplexExtendFull` | 符号付き延長をコチェイン写像にまとめる。 |
| `fullCechOrderHomotopyComponent` | 整列と恒等写像のホモトピーのコチェイン成分。 |
| `fullCechOrderHomotopy` | 符号付き延長と成分制限の合成を、全タプル版の恒等と比較する。 |
| `fullCechOrderedHomotopyEquiv` | 全タプル版から狭義増加版への成分制限はホモトピー同値。 |
| `fullCechOrderedHomologyIso` | 全タプル版と狭義増加版は各次数で同じコホモロジーを持つ。 |

## ProjectiveCechComparisonNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechComparisonNaturality`

| 宣言 | 主張 |
| --- | --- |
| `fullCechOrderedHomologyNatIso` | 有界版と全タプル版の Čech コホモロジー比較は、係数の自然変換と可換。 |

## ProjectiveCechComplex

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleSupport` | タプルに現れる添字の有限集合。 |
| `cechTupleSupport_comp_subset` | タプルの再添字付けで、その添字集合は増えない。 |
| `cechTupleSupport_face_subset` | 面の添字集合は元のタプルの添字集合に含まれる。 |
| `cechTupleSupport_cons` | タプルの先頭に付けた頂点が、添字集合に追加される。 |
| `cechTupleSupport_cons_contains_iff` | 概要：負の指数の台 N の外の頂点を先頭に追加しても、その単項式が現れる条件は変わらない。 |
| `projectiveMonomialCochains` | 一つの Laurent 単項式に対応する、指定の台を持つコチェインの部分加群。 |
| `projectiveMonomialDifferential` | 一つの Laurent 単項式に対応する余境界。 |
| `projectiveMonomialContraction` | 台の外の頂点を先頭に付けて評価する。 |
| `projectiveMonomialDifferential_apply` | 一つの単項式の余境界を、タプルの各面で評価する。 |
| `projectiveMonomialContraction_identity` | 概要：負の指数の台が全体より小さければ、全タプルの単項式コチェインは縮約する。 |
| `FullCechCochains` | 全タプルを添字とする Čech の項。 |
| `fullCechEvaluateAt` | 概要：整数係数のタプル鎖を、指定の交叉上でコチェインに評価する。 |
| `fullCechEvaluateAt_single` | 一つのタプル上の評価は、その成分の制限写像で与えられる。 |
| `fullCechEvaluateAt_restrict` | 概要：タプル鎖の評価は、各成分の頂点が入る交叉から、より小さい開への制限と可換。 |
| `fullCechTranspose` | タプル鎖の線形写像を制限写像付きコチェインへ転置する。 |
| `fullCechTranspose_id` | 恒等な鎖写像の転置は恒等写像。 |
| `fullCechDifferential` | 制限写像の交代和による全タプル版の余境界。 |
| `fullCechDifferential_apply` | 全タプル版の余境界の成分は、制限した面の値の交代和。 |
| `fullCechReindex` | 有限交叉上の係数を、タプルの添字写像で引き戻す。 |
| `fullCechCosimplicial` | 全タプル版の余単体加群。 |
| `fullCechDifferential_squared` | 通常の Čech 次数では全タプル版の余境界の二乗が零になる。 |
| `fullCechComplex` | 通常の全タプル Čech 複体。次数 q では長さ q + 1 のタプルを使う。 |
| `OrderedCechCochains` | 狭義増加タプルを添字とする Čech の項。 |
| `orderedCechDifferential` | 狭義増加タプルだけを使う余境界。 |
| `subsingleton_orderedCechCochains` | 狭義増加版は添字集合の濃度より長いタプルを持たない。 |
| `fullCechRestrictOrdered` | 全タプル版を狭義増加タプルの成分へ制限する。 |
| `fullCechRestrictOrdered_comp_differential` | 成分の制限は余境界と可換になる。 |
| `fullCechRestrictOrdered_surjective` | 狭義増加版への成分の制限は全射。 |
| `orderedCechDifferential_squared` | 通常の Čech 次数では狭義増加版の余境界の二乗が零になる。 |
| `orderedCechComplex` | 狭義増加タプルによる通常の Čech 複体。 |
| `fullCechComplexRestrictOrdered` | 全タプル版から狭義増加版への成分制限をコチェイン写像にまとめる。 |
| `isZero_orderedCechHomology` | 被覆の添字集合の濃度以上の次数で、狭義増加版のコホモロジーは消える。 |
| `cechTupleSupport_card` | 単射なタプルの添字集合の濃度はタプルの長さに等しい。 |
| `cechTupleSupportEquiv` | 単射なタプルを、その添字集合への全単射と見なす。 |
| `cechTupleSortingPerm` | 整列順の位置を元のタプルの位置に移す置換。 |
| `cechTupleSortingPerm_apply` | タプルを整列置換で引き戻すと、添字集合の増加列になる。 |
| `cechTupleSortingPerm_eq_one` | 既に狭義増加なタプルの整列置換は恒等である。 |
| `orderedCechExtendFull` | 狭義増加版の値を整列の符号付きで全タプルへ延長する。 |
| `cechPermDelete` | 置換から一つの位置とその像を除いて得られる置換。 |
| `cechPermDelete_apply` | 一つの位置を削除した置換は、削除する前の置換と残った位置で可換になる。 |
| `cechPermDelete_sign` | 削除した位置とその像の符号を、制限置換の符号に移す。 |

## ProjectiveCechDevissage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechDevissage`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFinite_of_shortExact_presentations` | 概要：有限性が分かっている対象による短完全表示を繰り返せば、各対象の射影 Čech コホモロジーが有限になる。 |

## ProjectiveCechDiagramInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechDiagramInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechDirectSumDiagramInclusion` | 各係数図式から、係数の直和の図式への包含。 |
| `projectiveCechDirectSumDiagramInclusion_complex` | 係数図式の包含が誘導する Čech 写像は、項ごとの直和からの既存の包含に一致。 |
| `projectiveCechDirectSumDiagramInclusion_homology` | 係数図式の包含についての Čech コホモロジーの直和比較の公式。 |

## ProjectiveCechDirectSumHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechDirectSumHomology`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechDirectSumComplex_d` | 項ごとの直和の余境界は、各複体の余境界の直和。 |
| `projectiveCechDirectSumShortComplexIso` | 直和の複体の三項を、三項の直和と比較する。 |
| `projectiveCechDirectSumHomologyIso` | 射影標準開の Čech 版のコホモロジーは、係数の直和と交換する。 |

## ProjectiveCechDirectSumInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechDirectSumInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechDirectSumComplexInclusion` | Čech 複体の各成分から項ごとの直和への包含。 |
| `projectiveCechDirectSumInclusion` | 係数の直和の Čech 複体への、各成分の包含。 |
| `projectiveCechDirectSumHomologyIso_inclusion` | Čech 版の直和コホモロジー比較は各成分の包含を保つ。 |

## ProjectiveCechFilteredCochains

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredCochains`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechCochainsFunctor` | 全タプル版 Čech の固定した長さの項を、係数図式の関手として扱う。 |
| `projectiveCoefficientColimit_exists_rep` | 係数図式の余極限の各交叉の切断は、一つの有限段の代表元を持つ。 |
| `projectiveCoefficientColimit_eq_iff` | 同じ段の係数が余極限で等しいことは、一つ先の段で等しいことと同値。 |
| `projectiveCechColimitCochainsMap_ι` | canonical な Čech 各項の余極限比較は、有限段のタプル成分をそのまま送る。 |
| `projectiveCechColimitCochainsMap_surjective` | 有限被覆の Čech 各項の filtered 余極限比較は全射。 |
| `projectiveCechColimitCochainsMap_injective` | 有限被覆の Čech 各項の filtered 余極限比較は単射。 |
| `projectiveCechCochainsFunctorPreservesFilteredColimits` | 有限被覆の全タプル Čech の各項は、filtered 余極限を保つ。 |

## ProjectiveCechFilteredComplex

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredComplex`

| 宣言 | 主張 |
| --- | --- |
| `projectiveFullCechFunctorPreservesFilteredColimits` | 有限被覆の全タプル Čech 複体は filtered 余極限を保つ。 |
| `projectiveCechFilteredComplexIso` | 有限被覆の Čech 複体と係数図式の filtered 余極限との canonical な比較。 |
| `projectiveCechFilteredHomologyIso` | 有限被覆の Čech H は、係数図式の filtered 余極限と交換する。 |

## ProjectiveCechFilteredNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFilteredComplexIso_naturality` | 有限被覆の Čech 複体と filtered 余極限の比較は、係数図式の射に自然。 |
| `projectiveCechFilteredHomologyIso_naturality` | 有限被覆の Čech H の filtered 余極限比較は、係数図式の射に自然。 |

## ProjectiveCechFiniteRetracts

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteRetracts`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechHomology_finite_of_finite_splitting` | 有限個の複体への射影と包含が恒等を分解すれば、有限性は元の複体にも戻る。 |

## ProjectiveCechFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `finite_projectiveCechNonnegativeExponents` | 全指数が非負で総次数が固定された単項式は有限個。 |
| `finite_projectiveCechNegativeExponents` | 全指数が負で総次数が固定された Laurent 単項式は有限個。 |
| `exists_projectiveCech_commonMonomialDenominator` | 概要：標準開で許される Laurent 単項式の分母を、チャートの積の一つの冪にそろえる。 |
| `projectiveCechFinite_of_bounded_of_exact` | 概要：コホモロジーの有界性と有限自由表示から、各次数の有限性を出す。 |

## ProjectiveCechFlatBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFlatBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFlatBaseChangeIso` | flat なテンソル底変換は、有限被覆の Čech コホモロジーと交換する。 |
| `projectiveCechFlatBaseChangeIso_naturality` | flat な Čech 底変換の比較は、係数図式の任意の射に自然。 |
| `projectiveCechFlatBaseChange_finite` | flat 底変換後の Čech コホモロジーは、元のコホモロジーの有限生成性を保つ。 |

## ProjectiveCechFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobenius`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedChartFrobenius` | 各標準開の実際の Frobenius は、捻り d の部分を捻り p*d の部分へ送る。 |
| `projectiveNatGradedChartFrobenius_val` | 各標準開の指定次数の Frobenius は、周囲の局所化環の p 乗の制限である。 |
| `projectiveNatGradedChartFrobeniusNatTrans` | 実際の標準開の Frobenius を、係数作用を制限した図式の射にする。 |
| `projectiveNatGradedCechFrobenius` | 実際の構造層の標準開から得た、Čech コホモロジーの Frobenius 半線形写像。 |

## ProjectiveCechFrobeniusAdic

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusAdic`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedCechFrobenius_ideal_power_control` | 実際の Čech Frobenius は、H の Iⁿ 倍を I^(p*n) 倍へ送る。 |
| `projectiveNatGradedCechFrobeniusAdicQuotientMap` | Čech H 自身の I 進商上の Frobenius。指数 n を p*n へ送る。 |
| `projectiveNatGradedCechFrobeniusAdicQuotientMap_transition` | 指数 n→p*n の Čech Frobenius は、I 進商の遷移と可換。 |
| `projectiveNatGradedCechFrobeniusAdicCompletionMap` | 実際の Čech Frobenius が誘導する、I 進完備化上の半線形写像。 |
| `projectiveNatGradedCechFrobeniusAdicCompletionMap_of` | 完備化上の Čech Frobenius は、元の H からの写像を保つ。 |

## ProjectiveCechFunctor

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor`

| 宣言 | 主張 |
| --- | --- |
| `fullCechCochainsMap` | 全タプル版の各項の係数を自然変換で移す。 |
| `fullCechCochainsMap_comp_differential` | 係数の自然変換は全タプル版の余境界と可換。 |
| `fullCechComplexMap` | 係数図式の自然変換が誘導する全タプル版 Čech のコチェイン写像。 |
| `fullCechComplexFunctor` | 全タプル Čech 複体を係数図式の関手とする。 |
| `orderedCechCochainsMap` | 狭義増加版の各項の係数を自然変換で移す。 |
| `orderedCechCochainsMap_comp_differential` | 係数の自然変換は狭義増加版の余境界と可換。 |
| `orderedCechComplexMap` | 係数図式の自然変換が誘導する狭義増加版 Čech のコチェイン写像。 |
| `orderedCechComplexFunctor` | 狭義増加 Čech 複体を係数図式の関手とする。 |
| `fullCechComplexRestrictOrderedNatTrans` | 狭義増加タプルでの成分射影は係数図式の自然変換と可換。 |
| `orderedCechComplex_shortExact` | 各交叉の係数列が短完全なら、狭義増加 Čech 複体の列も短完全。 |

## ProjectiveCechGradedLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projDenominator` | 局所化の分母としての f の冪。 |
| `projectiveGradedFraction` | 分子を V n に制限し、分母を fⁿ に固定した分数の線形写像。 |
| `projectiveGradedFraction_apply` | 分数写像は指定した分子と分母を持つ。 |
| `projectiveGradedAway` | 分母の指数すべてから、局所化の指定次数成分を作る。 |
| `mem_projectiveGradedAway_iff` | 概要：分子の族が f の作用で次の部分へ移るなら、成分の元は一つの斉次分数で表される。 |
| `projectiveGradedAwayMap` | 分子の部分加群を保つ写像が、局所化の指定次数成分に誘導する写像。 |
| `projectiveGradedAwayMap_fraction` | 指定次数の局所化写像は分子に元の写像を適用する。 |
| `projectiveGradedAwayMap_surjective` | 分子の各次数で全射なら、その局所化の指定次数成分でも全射になる。 |
| `projectiveGradedAwayMap_exact` | 概要：分子の各次数で完全な二つの写像は、局所化の指定次数成分でも完全になる。 |

## ProjectiveCechGradedRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction`

| 宣言 | 主張 |
| --- | --- |
| `isUnit_projectiveModuleAwayFactor` | f が g を割ると、g で局所化した加群では f の作用も可逆になる。 |
| `projectiveModuleAwayRestriction` | 分母の整除関係が誘導する局所化加群の制限。 |
| `projectiveModuleAwayRestriction_mk_one` | 分母の整除関係が誘導する局所化加群の制限。 |
| `projectiveModuleAwayRestriction_comp` | 制限写像の合成は、分母の整除関係の推移から得る制限写像。 |
| `projectiveModuleAwayRestriction_refl` | 同じ分母での制限写像は恒等。 |
| `projectiveModuleAwayRestriction_mk` | 制限は分子に追加因子の冪を掛け、分母を新しい分母の冪へ移す。 |
| `projectiveGradedAwayRestriction` | 分子の指定次数を保つとき、制限は局所化の指定次数成分にも降りる。 |
| `projectiveGradedAwayRestriction_val` | 次数成分の制限は通常の局所化加群の制限で与えられる。 |

## ProjectiveCechNonemptyComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechNonemptyComparison`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleSupport_nonempty` | 正の長さのタプルに現れる添字集合は非空。 |
| `fullCechNonemptyTermEquiv` | 非空有限交叉の係数の同型を、Čech の一つの項に移す。 |
| `fullCechNonemptyTermEquiv_differential` | 非空交叉での自然性は Čech の余境界との可換性を与える。 |
| `fullCechNonemptyComplexIso` | 非空有限交叉の自然同型が与える、通常の全タプル Čech 複体の同型。 |

## ProjectiveCechRestrictScalars

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalars`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechRestrictScalarsComplexIso` | Čech 複体の形成は、係数環の作用の制限と交換する。 |
| `projectiveCechRestrictScalarsHomologyIso` | Čech 版のコホモロジーは係数制限と交換する。 |

## ProjectiveCechRestrictScalarsNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalarsNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechRestrictScalarsComplexIso_naturality` | Čech 複体の係数制限の比較は、係数の自然変換と可換。 |
| `projectiveCechRestrictScalarsHomologyIso_naturality` | Čech 版のコホモロジーと係数制限の比較は、係数の自然変換に自然。 |

## ProjectiveCechScalarAction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechScalarAction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechComplexMap_smul` | Čech 複体への係数写像の構成は、スカラー倍を保つ。 |
| `projectiveCechHomologyMap_smul` | Čech 版のコホモロジー写像は、係数写像のスカラー倍を保つ。 |
| `projectiveCechHomologyMap_smul_id` | Čech 版のコホモロジーで、恒等係数写像のスカラー倍は元のスカラー作用を誘導する。 |

## ProjectiveCechSemilinearMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearMap`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSemilinearHomologyMap` | 係数制限として与えた図式の写像は、Čech コホモロジーの半線形写像を誘導する。 |

## ProjectiveCechSemilinearNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSemilinearHomologyMap_naturality` | 半線形な係数の可換四角形は、Čech H の同じ四角形を与える。 |

## ProjectiveCechSplitExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitExact`

| 宣言 | 主張 |
| --- | --- |
| `cechTupleBoundary_prepend_zero` | 長さ零のタプルでは、先頭を追加して境界を取ると元に戻る。 |
| `fullCechPrependVertex_zero_differential` | 長さ零の先頭挿入と余境界の合成は、頂点挿入による係数の制限。 |
| `fullCechAugmentedDifferential_squared` | 全タプルの余境界の二乗は、長さ零の増大項からも零となる。 |
| `fullCechSplitVertexContraction_zero_identity` | 増大項での縮約も、余境界との合成が恒等になる。 |
| `fullCechSplitVertexDifferential_zero_injective` | 固定頂点による縮約があれば、増大項からの余境界は単射。 |
| `fullCechSplitVertex_cycle_boundary` | 固定頂点による縮約があれば、正の長さの各 Čech サイクルは境界。 |

## ProjectiveCechSplitVertex

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitVertex`

| 宣言 | 主張 |
| --- | --- |
| `cechInsertVertexFunctor` | 有限集合に固定した頂点を挿入する関手。 |
| `fullCechInsertVertexMap` | 係数図式の制限による、頂点挿入の自然変換。 |
| `fullCechInsertVertexIso` | 各交叉で頂点挿入の制限が可逆なら、係数図式の自然同型になる。 |
| `fullCechPrependVertex` | タプルの先頭への挿入による、挿入後の係数での評価。 |
| `fullCechPrependVertex_naturality` | 先頭挿入の評価は、係数図式の射に自然。 |
| `fullCechSplitVertexContraction` | 挿入の制限の逆で係数を戻した、縮約の候補。 |
| `fullCechInsertTranspose` | 頂点挿入まで台を広げる鎖写像の転置。 |
| `fullCechInsertTranspose_comp_preserving_left` | 挿入まで広げる写像の前に、台を保つ写像を合成する場合の転置。 |
| `fullCechInsertTranspose_comp_preserving_right` | 台を保つ写像の前に、挿入まで広げる写像を合成する場合の転置。 |
| `fullCechInsertTranspose_add` | 挿入を許す転置は鎖写像の和を保つ。 |
| `fullCechInsertTranspose_id` | 恒等写像の挿入を許す転置は、挿入による係数の制限。 |
| `cechTuplePrepend_support_insert` | 先頭追加の像の台は、元の台にその頂点を追加した集合に収まる。 |
| `fullCechInsertTranspose_prepend` | 先頭追加を転置したものは、係数図式への先頭挿入の評価。 |
| `fullCechPrependVertex_identity` | 係数図式付きの先頭挿入と余境界の反交換式。同型性の仮定は不要。 |
| `fullCechSplitVertexContraction_identity` | 挿入の制限が同型なら、係数図式の全タプル Čech コチェインは縮約する。 |

## ProjectiveCechTensorBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechTensorBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechTensorCochainsIso` | Čech の各項の有限積と、実際のテンソル底変換との交換同型。 |
| `projectiveCechTensorCochainsIso_tmul` | 各項のテンソル比較は、純テンソルをタプルごとに評価する。 |
| `projectiveCechTensorCochainsIso_differential` | テンソル積と有限積の比較は、Čech の交代和の余境界と可換。 |
| `projectiveCechTensorComplexIso` | 有限被覆の全タプル Čech 複体は、実際のテンソル底変換と交換する。 |

## ProjectiveCechTensorNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechTensorNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechTensorCochainsIso_naturality` | Čech 各項のテンソル比較は、任意の係数図式の射に自然。 |
| `projectiveCechTensorComplexIso_naturality` | Čech 複体のテンソル比較は、係数図式の自然変換と可換。 |
| `projectiveCechTensorComplexNatIso` | Čech 複体とテンソル底変換の比較を、係数図式の圏上の自然同型にする。 |

## ProjectiveCoefficientChartTransport

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientChartTransport`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCoefficientChartIsoOfRestrictEq` | 指定した次数族との同定を、恒等の加群写像による標準開の同型にする。 |
| `projectiveCoefficientChartIsoOfRestrictEq_naturality` | 次数族の同定を含む比較も、次数を保つ加群の射に自然。 |

## ProjectiveCoefficientGradingCongr

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientGradingCongr`

| 宣言 | 主張 |
| --- | --- |
| `projectivePolynomialCoefficientChartIsoOfGradeEq` | 基底環上の次数を、等しい別の族で書いた係数比較の同型。 |
| `projectivePolynomialCoefficientChartIsoOfGradeEq_naturality` | 次数を等式で取り替えた係数比較も、次数を保つ加群写像に自然。 |

## ProjectiveDirectSumCech

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumCech`

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechDirectSumDiagram` | 各有限交叉上で係数の直和を取った図式。 |
| `projectiveCechDirectSumComplex` | 各 Čech 複体の項ごとの直和。 |
| `projectiveCechDirectSumTermLinearEquiv` | 直和と有限なタプルの積を交換する、各 Čech 項の同値。 |
| `projectiveCechDirectSumTermLinearEquiv_differential` | 各項の比較は、有限な面の交代和と可換。 |
| `projectiveCechDirectSumComplexIso` | 係数の直和の Čech 複体と、Čech 複体の項ごとの直和の同型。 |

## ProjectiveDirectSumFinitePi

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumFinitePi`

| 宣言 | 主張 |
| --- | --- |
| `projectiveDirectSumToFinitePi` | 直和の各元の座標を、座標ごとの直和へ送る。 |
| `projectiveFinitePiToDirectSum` | 各座標の直和を、有限個の座標包含の和でまとめる。 |
| `projectiveDirectSumFinitePiLinearEquiv` | 直和と有限積の交換。 |
| `projectiveDirectSumFinitePiLinearEquiv_apply` | 同値は、Rees 次数と Čech 項の座標を交換する。 |
| `projectiveDirectSumFinitePiLinearEquiv_naturality` | 有限積との比較は、各成分の係数写像に自然。 |

## ProjectiveDirectSumHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumHomology`

| 宣言 | 主張 |
| --- | --- |
| `projectiveDirectSumCofan` | 加群の外部直和を余錐にする。 |
| `projectiveDirectSumCofanIsColimit` | 外部直和の余錐の普遍性。 |
| `projectiveDirectSumColimitIso` | カテゴリーの余極限を外部直和と比較する。 |
| `projectiveDirectSumColimitIso_ι` | 余極限の比較は各成分の包含を保つ。 |
| `projectiveDirectSumColimitIso_naturality` | 成分ごとの写像の余極限は、比較の下で直和写像となる。 |
| `projectiveShortComplexDiagram` | 短複体の族を、離散図式の短複体としてまとめる。 |
| `projectiveDirectSumShortComplex` | 各項の直和を取った短複体。 |
| `projectiveDirectSumShortComplexIso` | 短複体の余極限を、各項の外部直和と比較する。 |
| `projectiveShortComplexDiagramHomologyIso` | 離散図式のコホモロジーの各成分を、元の短複体のコホモロジーと比較する。 |
| `projectiveDirectSumShortComplexHomologyIso` | 短複体の任意直和のコホモロジーは、各コホモロジーの直和。 |

## ProjectiveDirectSumHomologyInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumHomologyInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveColimitInclusion` | 評価から余極限への自然な包含。 |
| `projectiveDirectSumShortComplexInclusion` | 直和の短複体への各成分の包含。 |
| `projectiveShortComplexColimitInclusion_eq` | 短複体の比較は、余極限への包含を外部直和への包含へ送る。 |
| `projectiveDirectSumShortComplexHomologyIso_inclusion` | Čech 版の直和コホモロジー比較は、各成分の包含を保つ。 |
| `projectiveDirectSumShortComplexHomologyIso_naturality_component` | Čech 版の直和コホモロジー比較は、成分を別の次数へ送る写像にも自然。 |

## ProjectiveDirectSumSubmodule

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumSubmodule`

| 宣言 | 主張 |
| --- | --- |
| `projectiveDirectSumSubmodule` | 周囲の直和のうち、各成分が指定部分加群に入るもの。 |
| `mem_projectiveDirectSumSubmodule` | 直和の部分加群への所属は成分ごとに判定する。 |
| `projectiveDirectSumSubmodule_range` | 部分加群の包含の直和の像。 |
| `projectiveDirectSumSubmoduleLinearEquiv` | 部分加群の直和と、周囲の直和の成分ごとの部分加群の同値。 |
| `projectiveDirectSumSubmoduleLinearEquiv_val` | 部分加群の直和の比較は、周囲の直和への成分ごとの包含そのもの。 |

## ProjectiveFilteredHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomology`

| 宣言 | 主張 |
| --- | --- |
| `projectiveFilteredShortComplexDiagram` | 短複体の filtered 図式を、関手圏の一つの短複体にまとめる。 |
| `projectiveFilteredShortComplexHomologyDiagramIso` | 関手圏の短複体のコホモロジーは、有限段ごとのコホモロジーの図式と一致する。 |
| `projectiveFilteredShortComplexHomologyIso` | 短複体の filtered 余極限のコホモロジーは、各段のコホモロジーの余極限。 |
| `projectiveFilteredComplexShortComplexIso` | 複体の余極限の短複体と、各項の余極限を取った短複体との比較。 |
| `projectiveFilteredComplexHomologyIso` | 複体の filtered 余極限と各次数のコホモロジーとの同型。 |

## ProjectiveFilteredHomologyNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomologyNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveFilteredShortComplexHomologyDiagramIso_naturality` | 関手圏の短複体の H と各段の H の比較は、図式の射に自然。 |
| `projectiveFilteredShortComplexHomologyIso_naturality` | 短複体の filtered 余極限の H の比較は、図式の射に自然。 |
| `projectiveFilteredComplexShortComplexIso_naturality` | 複体の短複体と各項の余極限の比較は、図式の射に自然。 |
| `projectiveFilteredComplexShortComplexIso_inv_naturality` | 短複体の比較の逆向きも、図式の射に自然。 |
| `projectiveFilteredComplexHomologyIso_naturality` | 複体の filtered 余極限と各次数の H の比較は、図式の射に自然。 |

## ProjectiveFilteredSubmodule

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredSubmodule`

| 宣言 | 主張 |
| --- | --- |
| `projectiveFilteredSubmodule` | 余極限内の指定部分は、各段の部分加群の像の上限。 |
| `projectiveFilteredSubmodule_directed` | 遷移で保たれる部分加群の像は、有向族をなす。 |
| `mem_projectiveFilteredSubmodule_iff` | 余極限の指定部分の元は、一段の指定部分の代表元を持つ。 |
| `projectiveFilteredSubmoduleDiagram` | 各段の指定部分加群自身がなす filtered 図式。 |
| `projectiveFilteredSubmoduleInclusion` | 指定部分加群の包含を、図式の包含とする。 |
| `projectiveFilteredSubmoduleInclusionMono` | 指定部分加群の図式の包含は mono。 |
| `projectiveFilteredSubmoduleColimit_injective` | filtered 余極限の完全性により、指定部分加群の余極限からの包含は単射。 |
| `projectiveFilteredSubmoduleColimit_range` | 部分加群の余極限の像は、各有限段の像の有向上限そのもの。 |
| `projectiveFilteredSubmoduleColimitEquiv` | 指定部分加群の余極限を、余極限の中の具体的な部分加群と同定する。 |
| `projectiveFilteredSubmoduleColimitEquiv_val` | 部分加群の比較は、余極限内の同じ元を対応させる。 |

## ProjectiveFormalFunctionsBounds

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsBounds`

| 宣言 | 主張 |
| --- | --- |
| `formalFunctions_range_eq_of_kernel_killed` | 十分先の核が遷移写像で零になれば、厚化のコホモロジーの像が安定する。 |
| `formalFunctions_eventually_injective_of_kernel_bound` | 核の I 進評価と I の冪による零化から、十分厚い商への単射性が従う。 |

## ProjectiveFormalFunctionsFiltration

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFormalFunctionsFiltration`

| 宣言 | 主張 |
| --- | --- |
| `cechFormalFunctions_filtration_bound_of_finiteReesImage` | Čech 版の核の評価に渡す、像のフィルトレーションの一様な I 進評価。 |

## ProjectiveFreeCechFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFreeCechFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedFreePieceSMul` | 有限自由加群の各生成元に次数を指定すると、係数環の作用は次数を保つ。 |
| `projectiveFreeOrderedCechHomology_finite` | 有限個の多項式環の捻りからなる自由加群の狭義増加 Čech コホモロジーは有限生成。 |

## ProjectiveFrobeniusNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedFrobenius_map` | 実際の局所化の Frobenius は、代数の環準同型が誘導する局所化の射に自然。 |
| `projectiveNatGradedChartFrobeniusNatTrans_naturality` | 標準開の実際の Frobenius の自然変換は、次数を保つ代数の射と可換。 |
| `projectiveNatGradedCechFrobenius_naturality` | 実際の標準開の Čech Frobenius は、次数を保つ代数の射に自然。 |

## ProjectiveFullCechExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFullCechExact`

| 宣言 | 主張 |
| --- | --- |
| `fullCechComplexFunctor_preservesZeroMorphisms` | 全タプルの Čech 複体を作る関手は零射を保つ。 |
| `fullCechComplex_shortExact` | 各交叉の係数列が短完全なら、全タプル Čech 複体の列も短完全。 |

## ProjectiveFullGradedCechExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFullGradedCechExact`

| 宣言 | 主張 |
| --- | --- |
| `projectiveFullCech_shortExact` | 斉次な短完全列は標準開の Čech 複体でも短完全となる。 |

## ProjectiveGradedAwayColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayColimit`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayColimitDiagram` | 各有限段の指定次数の斉次局所化からなる filtered 図式。 |
| `projectiveGradedAwayColimitCocone` | 有限段の斉次局所化から、余極限の分子族の斉次局所化への canonical な余錐。 |
| `projectiveGradedAwayColimitMap` | 指定次数の局所化の colimit から、実際の余極限の分子族の局所化への比較射。 |
| `projectiveGradedAwayColimitMap_ι` | 比較射は、各有限段の分数をその段の射で移す。 |
| `projectiveGradedAwayColimitMap_surjective` | 各段の分母倍の条件の下で、斉次局所化の filtered colimit の比較は全射。 |
| `projectiveGradedAwayColimitMap_injective` | 分母倍での零化を有限段へ降ろすことで、斉次局所化の比較は単射となる。 |
| `projectiveGradedAwayColimitEquiv` | 実際の斉次局所化の filtered colimit と、余極限の分子族の斉次局所化との同型。 |
| `projectiveGradedAwayColimitEquiv_ι` | 斉次局所化の同型は、各有限段からの実際の分数の写像を保つ。 |

## ProjectiveGradedAwayColimitValues

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayColimitValues`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayColimitEquiv_ι_value` | 斉次局所化の余極限同型は、周囲の局所化では各有限段からの局所化写像。 |

## ProjectiveGradedAwayIdeal

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayIdeal`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedFraction_ideal_range` | 指数を固定した分数のイデアル倍の像は、元の像のイデアル倍。 |
| `projectiveGradedAway_ideal_smul` | 分子の各成分のイデアル倍を局所化すると、局所化の指定成分のイデアル倍になる。 |

## ProjectiveGradedAwayIdealRange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayIdealRange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayMap_range_ideal` | 分子ごとの像の等式は、斉次局所化の像を元の指定成分のイデアル倍にする。 |

## ProjectiveGradedCechExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedCechExact`

| 宣言 | 主張 |
| --- | --- |
| `projectiveOrderedCech_shortExact` | 斉次な短完全列は標準開の Čech 複体でも短完全となる。 |

## ProjectiveGradedChart

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLaurentDenominator_mem_polynomialGrade` | 標準開の分母の次数は反転する変数の個数。 |
| `projectiveGradedChart_mul_mem` | 追加の分母の冪を掛けると、新しい分母に対応する次数成分へ移る。 |
| `projectiveGradedModuleChartDiagram` | 次数付き加群の指定次数の標準開係数図式。 |
| `projectiveGradedChart_mul_denominator` | 分子と分母へ同じチャートの分母を掛けると、許された分子の次の次数へ移る。 |
| `projectiveGradedModuleChartMap` | 次数を保つ加群写像は標準開の斉次局所化の自然変換を与える。 |
| `projectivePolynomialGrade_mul_denominator` | 多項式環の次数成分は分母との積で次の成分へ移る。 |
| `projectiveLaurentGradeLinearEquiv_restrict` | Laurent の次数成分の基底による表示は、チャートの制限と可換。 |
| `projectiveLaurentGradedLocalizationLinearEquiv_val` | 同次局所化の比較を部分加群の外で見ると、通常の局所化の比較になる。 |
| `projectivePolynomialTwistChartIso` | 射影空間の捻りの標準開係数図式と Laurent 単項式図式は自然同型。 |

## ProjectiveGradedChartAdditive

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartAdditive`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedModuleChartMap_id` | 標準開の係数図式への写像は恒等写像を保つ。 |
| `projectiveGradedModuleChartMap_comp` | 標準開の係数図式への写像は合成を保つ。 |
| `projectiveGradedModuleChartMap_sum` | 標準開の係数図式への写像は有限和を保つ。 |

## ProjectiveGradedChartDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedModuleChartDirectSumIso` | 次数を対応させる直和の加群同値は、標準開の係数図式の同型を与える。 |
| `projectiveGradedModuleChartDirectSumCechHomologyIso` | 直和と同値な次数付き加群の標準開 Čech コホモロジーは、各成分の直和と同型。 |

## ProjectiveGradedChartDirectSumInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSumInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedModuleChartInclusion_mem` | 直和同値と各成分の包含の合成は、Proj 次数を保つ。 |
| `projectiveGradedModuleChartInclusion` | 各成分の包含を標準開の図式へ渡す。 |
| `projectiveGradedModuleChartDirectSumIso_inclusion` | 標準開の直和比較は、元の各成分の包含を係数図式の直和の包含へ写す。 |
| `projectiveGradedModuleChartDirectSumCechHomologyIso_inclusion` | 各成分の包含についての、標準開 Čech コホモロジー直和比較の公式。 |

## ProjectiveGradedChartScalarAction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartScalarAction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveBaseScalarLinearMap` | 基底環の係数による、係数環上線形な自己写像。 |
| `projectiveGradedAwayMap_baseScalar` | 指定次数の局所化で、基底係数の写像は既存のスカラー作用に一致。 |
| `projectiveGradedModuleChartMap_baseScalar` | 基底の係数による標準開の図式の自己写像は、恒等自然変換のスカラー倍。 |
| `projectiveGradedModuleCechHomologyMap_baseScalar` | 基底係数の自己写像が誘導する Čech コホモロジー写像は、既存のスカラー作用。 |

## ProjectiveGradedChartShift

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartShift`

| 宣言 | 主張 |
| --- | --- |
| `projectivePolynomialShiftSMul` | 多項式環の捻りに対する次数付き作用。 |
| `projectiveGradedChartShiftIso` | 加群の次数をずらすことは、標準開で取る次数をずらすことに対応する。 |
| `projectiveShiftedPolynomialOrderedCechHomology_finite` | 多項式環の次数をずらして得る標準開 Čech コホモロジーも有限生成。 |

## ProjectiveGradedColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimit`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedColimitGrade` | 余極限の次数成分。共通基底での部分加群の余極限の像を使う。 |
| `projectiveGradedColimitBaseInclusion` | 各段からの次数付き射の、基底上の線形写像。 |
| `mem_projectiveGradedColimitGrade_iff` | 余極限の次数成分の元は、一つの有限段の同じ次数の元で表される。 |
| `projectiveGradedColimitInclusion_preservesPiece` | 各有限段からの射は、同じ Proj 次数の成分を保つ。 |
| `projectiveGradedColimitGrade_step` | 有限段での分母倍の条件は、余極限の次数成分でも成り立つ。 |

## ProjectiveGradedColimitGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimitGrading`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedColimitGrade_bot` | 各段の零部分の余極限の像は零部分。 |
| `projectiveGradedColimitGrade_int` | 余極限の次数成分と、負の次数を零とする整数への延長は交換する。 |

## ProjectiveGradedColimitNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimitNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedColimitMap_preservesPiece` | 次数を保つ図式の射は、余極限の実際の次数成分も保つ。 |

## ProjectiveGradedDirectSumRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedDirectSumRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedLocalizedDirectSumLinearEquiv_component_val` | 斉次局所化の直和比較の各成分は、周囲の局所化の同じ成分。 |
| `projectiveDirectSumSubmodule_restriction_mem` | 追加因子が各分子を保つなら、直和の分子も保つ。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv_restriction` | 斉次局所化の直和比較は、分母を広げる制限写像に自然。 |

## ProjectiveGradedFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedOrderedCechHomology_finite` | 有限生成次数付き多項式加群の各標準開 Čech コホモロジーは係数環上有限生成。 |
| `projectiveGradedFullCechHomology_finite` | 有限生成次数付き多項式加群の全タプル Čech コホモロジーも係数環上有限生成。 |

## ProjectiveGradedFree

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedFree`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedPiPiece` | 有限積の次数成分を成分ごとに指定する。 |
| `projectiveGradedPiSingle` | 一つの成分だけに斉次元を置く加法写像。 |
| `projectiveGradedPiSingle_sum` | 各成分の斉次元を戻して足すと、元の有限積の元になる。 |
| `projectiveGradedPiDecomposition` | 有限積は各成分の次数分解を受け継ぐ。 |
| `projectiveGradedReindexDecomposition` | 次数の添字を全単射で取り替えても、次数分解が得られる。 |
| `projectiveGradedShiftDecomposition` | 整数次数を定数だけずらした分解。 |
| `projectiveGradedFreePiece` | 指定した次数の生成元に対応する、有限自由加群の次数成分。 |
| `projectiveGradedFreeDecomposition` | 有限個の捻りの積の、次数分解。 |
| `projectiveGradedFreeMap_mem` | 斉次生成元による自由表示の写像は、各次数を保つ。 |
| `projectiveGradedFreeMap_surjective` | 有限個の斉次生成元による自由表示は、生成の仮定から全射になる。 |

## ProjectiveGradedFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedFrobenius`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayFrobenius` | Frobenius は、分子の p 乗が対応する指定部分へ入る場合に斉次局所化へ降りる。 |
| `projectiveGradedAwayFrobenius_val` | 斉次局所化の Frobenius は、周囲の実際の局所化の Frobenius の制限。 |
| `projectiveNatGradingInt_pow_mem` | 自然数次数を整数へ零延長した後も、p 乗は Proj 次数を p 倍する。 |
| `projectiveNatGradingInt_chart_pow_mem` | 指定分母の n 冪の分子の p 乗は、p 倍の捻りと p*n 冪の分母に対応する。 |

## ProjectiveGradedIdealProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedIdealProjection`

| 宣言 | 主張 |
| --- | --- |
| `projectiveIdealGradeProjection_mem` | イデアル倍の元を次数 d に射影すると、次数 d の成分のイデアル倍に入る。 |
| `projectiveHomogeneous_mem_ideal_smul_iff` | 斉次元が全体のイデアル倍に入ることと、同じ次数成分のイデアル倍に入ることは同値。 |
| `reesAdicProjectiveSubmodule_eq_ideal_smul` | 拡大イデアルで書いた Rees の部分加群は、元の Iⁿ 倍の部分加群そのもの。 |

## ProjectiveGradedLocalizationCongr

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationCongr`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayCongr` | 分子の指定部分を対応させる線形同値は、斉次局所化の同値を与える。 |
| `projectiveGradedAwayCongr_val` | 斉次局所化の比較の値は、周囲の局所化の誘導写像の値。 |
| `projectiveGradedLocalizedDirectSumTransport` | 分子の次数を保つ直和との同値を、斉次局所化の直和比較へ移す。 |

## ProjectiveGradedLocalizationMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationMaps`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayMap_id` | 指定次数の局所化に誘導される写像は恒等写像を保つ。 |
| `projectiveGradedAwayMap_add` | 指定次数の局所化に誘導される写像は和を保つ。 |
| `projectiveGradedAwayMap_comp` | 指定次数の局所化に誘導される写像は合成を保つ。 |
| `projectiveGradedAwayMap_injective` | 単射な加群写像は、局所化の指定次数成分でも単射になる。 |

## ProjectiveGradedLocalizedDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizedDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedLocalizedDirectSum_map` | 局所化と直和の同値は、指定次数の分子からなる部分加群を対応させる。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv` | 指定次数の斉次局所化と、その各成分の斉次局所化の直和の線形同値。 |
| `projectiveGradedLocalizedDirectSumLinearEquiv_val` | 斉次局所化の直和比較は、周囲の加群の局所化比較に一致する。 |

## ProjectiveGradedPresentation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedPresentation`

| 宣言 | 主張 |
| --- | --- |
| `exists_finset_homogeneous_span_top` | 概要：有限生成の次数付き加群は、有限個の斉次元で生成される。 |
| `projectiveGradedMap_decompose` | 次数を保つ写像は、斉次成分を取る射影と可換になる。 |
| `projectiveGradedMap_exact_piece` | 次数を保つ完全列は、各次数の斉次成分でも完全。 |
| `projectiveGradedMap_surjective_piece` | 全射な次数付き写像は各次数成分でも全射。 |
| `projectiveGradedKernelPiece` | 次数を保つ写像の核の、元の加群の次数成分との交わり。 |
| `projectiveGradedKernelDecomposition` | 次数を保つ写像の核は、元の加群の次数分解を受け継ぐ。 |

## ProjectiveGradedScalarRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedScalarRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveModuleScalarRestrictionLinearEquiv` | 与えられた R 作用と、B から係数制限した R 作用との恒等同値。 |
| `projectiveGradedFraction_restrictScalars` | 斉次分数の線形写像は、係数制限と交換する。 |
| `projectiveGradedAway_restrictScalars` | 斉次局所化の部分加群は係数制限と交換する。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv` | 斉次局所化の係数制限の比較を、R 加群としての線形同値にする。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv_val` | 斉次局所化の係数制限の比較は、周囲の局所化の元を変えない。 |

## ProjectiveGradedTensorCoefficientChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedTensorCoefficientChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorCoefficientNumerator` | 分子族のテンソル像を、変更後の基底環 B 上の部分加群として扱う。 |
| `projectiveTensorCoefficientNumerator_restrict` | B 上の分子のテンソル像を R に制限すると、元の R 上のテンソル像になる。 |
| `projectiveGradedTensorCoefficientEquiv` | 局所化する環を変えた、指定分子族のテンソル比較。まず R 線形に構成する。 |
| `projectiveGradedTensorCoefficientEquiv_fraction` | 係数環の変更を含めた比較も、純テンソル分数の分子と分母の冪を保つ。 |
| `projectiveGradedTensorCoefficientEquiv_smul` | 分子族が分母倍で次へ移るなら、係数変更を含む比較は B の作用と可換。 |
| `projectiveGradedTensorCoefficientLinearEquiv` | flat な基底変更と斉次局所化の比較を、B 線形な同型にする。 |

## ProjectiveGradedTensorLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedTensorLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorNumerator` | 分子族の右テンソル像を、元の基底環上の部分加群として扱う。 |
| `projectiveTensorNumerator_fraction_mem` | 純テンソルの斉次分数は、テンソル像の分子族に属する。 |
| `projectiveGradedTensorLocalization_symm_tmul_mem` | 周囲の局所化の比較の逆は、元の指定次数部分の純テンソルを保つ。 |
| `projectiveGradedTensorLocalizationMap` | 右テンソル像の指定次数部分への、元の斉次局所化からの比較写像。 |
| `projectiveGradedTensorLocalizationMap_val` | 斉次局所化の比較写像の周囲での値は、通常の局所化比較の逆である。 |
| `projectiveGradedTensorLocalizationMap_injective` | flat な右テンソル積では、斉次局所化の比較写像は単射。 |
| `projectiveGradedTensorLocalizationMap_fraction` | 純テンソルの比較写像は、元の分数の分母を保つ。 |
| `projectiveGradedTensorLocalizationMap_surjective` | 指定次数の比較写像は全射。分子族のテンソル像の定義だけで成立する。 |
| `projectiveGradedTensorLocalizationEquiv` | flat な右テンソル積は、指定分子族の斉次局所化と交換する。 |

## ProjectiveGradedTransportInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedTransportInclusion_mem` | 各成分の包含と同値の合成は、分子の指定部分を保つ。 |
| `projectiveGradedLocalizedDirectSumTransport_inclusion` | 直和の斉次局所化比較は、各成分からの局所化した包含を直和の包含へ写す。 |

## ProjectiveGradedTransportRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedTransport_restriction_mem` | 各成分の分子が追加因子で移るなら、同値で対応する加群の分子も移る。 |
| `projectiveGradedLocalizedDirectSumTransport_restriction` | 斉次局所化の直和への移送は、標準開を狭める制限と可換。 |

## ProjectiveGradedTransportValues

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportValues`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedLocalizedDirectSumTransport_val` | 斉次成分の直和への移送は、周囲の局所化の二つの同値の合成に一致する。 |
| `projectiveGradedLocalizedDirectSumTransport_component_val` | 斉次成分の移送の各成分を、周囲の局所化で計算する。 |
| `projectiveGradedLocalizedDirectSumTransport_fraction` | 斉次分数の移送は、分子に逆の加群同値を適用し、同じ分母で各成分を割る。 |

## ProjectiveGradingFromVariables

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradingFromVariables`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGrading_X_pow_mem` | 変数の作用の反復は、冪の数だけ次数を上げる。 |
| `projectiveGrading_monomial_mem` | 単項式の作用は、指数の全和だけ次数を上げる。 |
| `projectiveGradedSMul_of_variables` | 標準変数の作用の次数だけから、多項式環の次数付き作用が得られる。 |

## ProjectiveHomogeneousAway

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousAway`

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousAwayModule` | 斉次局所化の係数環の作用は加群の公理を満たす。 |
| `projectiveSelfLocalizationLinearEquiv` | 通常の環局所化と、環を自己加群と見た加群局所化の比較。 |
| `projectiveSelfLocalizationLinearEquiv_mk` | 通常の局所化の比較は分子と分母を保つ。 |
| `projectiveHomogeneousAwayToModule` | 斉次局所化から通常の加群局所化への単射な線形写像。 |
| `projectiveHomogeneousAwayToModule_mk` | 斉次局所化の分数は、加群局所化でも同じ分数に写る。 |
| `projectiveHomogeneousAwayLinearEquiv` | 次数零の斉次局所化を、通常の局所化の中の斉次分数の部分加群と同一視する。 |
| `projectiveHomogeneousAwayToModule_restriction` | 斉次局所化から加群局所化への比較は、標準開を狭める写像と可換。 |

## ProjectiveHomogeneousChart

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChart`

| 宣言 | 主張 |
| --- | --- |
| `projectivePolynomialVariableImage_mem` | 多項式の変数の像は斉次代数の次数一の元。 |
| `projectivePolynomialDenominatorImage` | チャートの分母を斉次代数へ写すと、対応する標準開の元の積になる。 |
| `projectivePolynomialDenominatorImage_mem` | チャートの分母の像の次数は、チャートの添字集合の濃度。 |
| `projectiveHomogeneousChartLinearEquiv` | 整数次数零のチャートを、斉次代数の次数零局所化と線形同一視する。 |
| `projectiveHomogeneousChartDiagram` | 次数零の斉次局所化を、標準開の局所化加群の制限に沿う係数図式にする。 |
| `projectiveHomogeneousChartDiagramIso` | 標準開の多項式加群の図式と、次数零の斉次局所化の図式の自然同型。 |
| `projectiveHomogeneousChartFullCechHomology_finite` | 有限生成斉次代数の次数零の標準開 Čech コホモロジーは有限生成。 |

## ProjectiveHomogeneousChartFractions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartFractions`

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousChartLinearEquiv_fraction` | 次数零のチャートの線形同型は、分子と分母の冪を保つ。 |
| `projectiveHomogeneousChartLinearEquiv_fraction_reflect` | 斉次分数での表示から、元の多項式加群の局所化での表示を取り戻す。 |

## ProjectiveHomogeneousChartRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousChartLinearEquiv_toModule` | 次数零チャートの比較と通常の加群局所化への写像は可換。 |
| `projectiveHomogeneousChartRestrictionRingHom` | 標準開を狭めるときの次数零斉次局所化の環準同型。 |
| `projectiveHomogeneousChartDiagram_map` | 局所化加群から移したチャートの制限は、斉次局所化の環の制限と一致する。 |

## ProjectiveHomogeneousCoefficientLift

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousCoefficientLift`

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousComponent_map` | 多項式の次数成分を取る操作は、任意の係数変更と交換する。 |
| `projectiveHomogeneousCoefficientLift` | 全射な係数変更では、斉次多項式を同じ次数のまま持ち上げられる。 |

## ProjectiveHomogeneousRingChartMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingChartMap`

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousRingChartMap_denominator` | 多項式環上の写像は、標準開の分母の像を保つ。 |
| `projectiveHomogeneousRingChartMap_powers` | 標準開の分母の冪の部分モノイドは、係数環の写像で次の段へ移る。 |
| `projectiveHomogeneousRingChartMap_fraction` | 斉次局所化の写像は、分子に係数の写像を適用し分母の指数を保つ。 |
| `projectiveHomogeneousChartLinearEquiv_map` | 次数零の加群の写像は、実際の斉次局所化の環の写像と一致する。 |

## ProjectiveLaurentChart

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLaurentChart`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLaurentExponents` | 添字集合 T の変数にだけ負の指数を許す指数加法モノイド。 |
| `projectiveLaurentOfNatExponents` | 自然数指数の単項式を Laurent 指数に入れる。 |
| `projectiveLaurentOfNatExponents_injective` | 自然数指数の単項式を Laurent 指数に入れる。 |
| `projectiveLaurentExponentRestriction` | 大きい添字集合への制限で負の指数を許す変数が増える。 |
| `projectiveLaurentDegree` | Laurent 単項式の次数は全ての指数の和。 |
| `projectiveLaurentChartMap` | 多変数多項式を、負の指数を許したチャートの単項式代数へ送る。 |
| `projectiveLaurentChartMap_injective` | 多変数多項式を、負の指数を許したチャートの単項式代数へ送る。 |
| `projectiveLaurentDenominatorExponent` | 局所化する変数の積の指数。 |
| `projectiveLaurentInverseExponent` | 変数の積の逆単項式の指数。 |
| `isUnit_projectiveLaurentDenominator` | チャート内では、局所化する変数の積の単項式は単元になる。 |
| `projectiveLaurentChartMap_monomial` | 多項式の単項式は、自然数指数を整数指数と見なした Laurent 単項式へ移る。 |
| `projectiveLaurentDenominator` | チャートの変数の積。 |
| `projectiveLaurentChartMap_denominator` | チャートの変数の積を Laurent 単項式として評価する。 |
| `projectiveLaurentExponents_clearDenominator` | Laurent 単項式に分母の冪を掛けると、多項式の単項式になる。 |
| `projectiveLaurentChart_isLocalizationMap` | 概要：標準開の Laurent 単項式代数は、チャートの変数の積で多項式環を局所化したもの。 |
| `projectiveLaurentChartAlgebra` | 多項式環からの写像が与える、Laurent 単項式代数の多項式環代数構造。 |
| `projectiveLaurentLocalizationLinearEquiv` | 多項式の局所化加群と Laurent 単項式代数の線形同型。 |
| `projectiveLaurentLocalizationLinearEquiv_mk_mul` | Laurent 代数へ移した斉次分数に分母を掛けると、その分子に戻る。 |
| `projectivePolynomialDegree` | 多項式の自然数指数の和を、整数次数として取る。 |
| `projectiveLaurentOfNatExponents_degree` | Laurent 単項式として写しても、多項式の次数は変わらない。 |
| `projectiveLaurentDenominatorExponent_degree` | 変数の積の次数は変数の個数。 |
| `projectiveLaurentInverseExponent_degree` | 逆単項式の次数は、変数の積の次数の反対。 |
| `projectiveLaurentChartMap_mem_grade_iff` | Laurent 単項式への埋め込みは次数を保存し、次数成分への所属を反映する。 |
| `projectiveLaurentLocalizationLinearEquiv_mk_mem_grade_iff` | 分母の次数を加えた次数の分子は、指定次数の Laurent 成分とちょうど対応する。 |
| `projectiveLaurentGradedLocalizationLinearEquiv` | チャートで捻った局所化加群と同じ次数の Laurent 成分の線形同型。 |
| `ProjectiveLaurentDegreeExponents` | チャートで許される、指定次数の Laurent 指数。 |
| `projectiveLaurentGradeLinearEquiv` | 指定次数の Laurent 多項式は、その次数の単項式に有限台を持つ係数の族。 |
| `projectiveLaurentDegreeExponentRestriction` | チャートの制限は Laurent 単項式の指数と次数を保つ。 |
| `projectiveLaurentChartRestriction` | チャートを狭めるとき、Laurent 単項式代数は指数を保って制限される。 |
| `projectiveLaurentChartRestriction_map` | チャートを狭めるとき、Laurent 単項式代数は指数を保って制限される。 |
| `projectiveLaurentDenominator_sdiff` | 追加で反転する変数の積を掛けると、狭いチャートの分母になる。 |
| `projectiveLaurentLocalizationLinearEquiv_restriction_mk` | 分母を広げてから Laurent 単項式に移す写像は、チャートの制限と可換。 |
| `projectiveLaurentGradedChartDiagram` | 指定次数の Laurent 単項式による、標準開の有限交叉の加群図式。 |
| `projectiveLaurentNegativeSupport` | 指数が負になる変数の有限集合。 |
| `projectiveLaurentExponents_iff_negativeSupport_subset` | チャートに単項式が現れる条件は、負の指数の台が添字集合に含まれること。 |
| `ProjectiveLaurentGlobalExponents` | 指定次数の整数指数ベクトル。 |
| `projectiveLaurentDegreeExponentEmbedding` | チャートに現れる指定次数の指数を、全体の整数指数に入れる。 |
| `projectiveLaurentLiftExponent` | 台の条件を満たす全体の指数を、チャート上の指数と見なす。 |
| `projectiveLaurentDegreeExponentRestriction_injective` | チャートの指数の制限は単射。 |
| `projectiveLaurentRestriction_coeff` | 制限後に追加で現れる指数の係数は零。 |
| `ProjectiveLaurentCochains` | 各タプルの標準開に、指定次数の Laurent 係数を置いたコチェイン。 |
| `projectiveLaurentCechCoordinate` | 指定した単項式の係数を全タプル Čech コチェインから取り出す。 |
| `projectiveLaurentCechSingle` | 単項式コチェインを Laurent 単項式を基底とする Čech コチェインに入れる。 |
| `projectiveLaurentCechCoordinate_apply` | 単項式が現れる標準開では、その係数を座標として取り出す。 |
| `projectiveLaurentCechCoordinate_differential` | Čech の余境界は Laurent 単項式ごとの係数に作用する。 |
| `projectiveLaurentCech_ext` | Laurent Čech コチェインは単項式ごとの全係数で決まる。 |
| `projectiveLaurentCechSingle_apply` | 許される指数の単項式コチェインを、指定の係数を持つ単項式として評価する。 |
| `projectiveLaurentCechCoordinate_single_self` | 一つの単項式を入れて、その単項式の座標を取ると恒等写像になる。 |
| `projectiveLaurentCechCoordinate_single_of_ne` | 異なる単項式の座標は零。 |
| `projectiveLaurentCechSingle_differential` | 単項式コチェインの組み込みは余境界と可換。 |
| `projectiveLaurentCechMonomialSupport` | 全タプルの有限個のチャートに現れる単項式を一つの有限集合に集める。 |
| `projectiveLaurentCechCoordinate_eq_zero_of_notMem` | 全チャートの台に現れない指数では座標が零。 |
| `projectiveLaurentCech_eq_sum_coordinates` | 有限個の単項式の座標を足すと元の Čech コチェインになる。 |
| `projectiveLaurentSurvives` | 負の指数の台が空または全体である指数を残す。 |
| `projectiveLaurentCech_cycle_decomposition` | 概要：Laurent Čech コサイクルは、台が空または全体である単項式だけで表せる。 |
| `finite_projectiveLaurentSurvives` | 固定次数で、負の指数の台が空または全体である指数は有限個。 |
| `projectiveLaurentSurvivorSubmodule` | 台が空または全体である単項式だけを含むコチェインの部分加群。 |
| `projectiveLaurentSurvivorSubmodule_finite` | 生き残る指数に限った Čech の各項は、Noether 環上で有限生成。 |
| `projectiveLaurentCechHomology_finite` | 概要：指定次数の Laurent 単項式による Čech 複体のコホモロジーは有限生成。 |

## ProjectiveLocalizationMapRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizationMapRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedModuleMap_restriction` | 局所化した加群写像は、分母の整除から得られる制限と可換。 |
| `projectiveLocalizedModuleCongr_restriction` | 加群同値を局所化する比較も、標準開の制限に自然。 |
| `projectiveGradedAwayMap_restriction` | 指定次数の局所化の係数写像は、標準開の制限に自然。 |
| `projectiveGradedAwayCongr_restriction` | 分子を対応させる同値の斉次局所化も、標準開の制限に自然。 |

## ProjectiveLocalizedColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedColimit`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedModuleFunctor` | 実際の局所化された加群を、元の係数環上の関手として扱う。 |
| `projectiveLocalizedModuleTensorNatIso` | 実際の分数の局所化は、局所化環とのテンソル積に自然に一致する。 |
| `projectiveLocalizedModuleFunctorPreservesColimits` | 固定した環での実際の局所化は、任意の小さい余極限を保つ。 |
| `projectiveLocalizedColimitIso` | 実際の局所化と余極限の canonical な比較。 |
| `projectiveLocalizedColimitIso_fraction` | 局所化の余極限比較は、有限段からの分数の分子と分母を保つ。 |
| `projectiveLocalizedColimitIso_naturality` | 実際の局所化と余極限の比較は、加群図式の射に自然。 |

## ProjectiveLocalizedDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `projectiveSumLocalized_isLocalized` | 各成分を局所化した加群の直和も、恒等写像について局所化された加群である。 |
| `projectiveLocalizationToDirectSum` | 直和を局所化してから、各成分の局所化の直和へ送る。 |
| `projectiveDirectSumToLocalization` | 各成分の包含を局所化し、局所化の直和から直和の局所化へ送る。 |
| `projectiveDirectSumLocalization_left` | 各成分の包含を局所化し、局所化の直和から直和の局所化へ送る。 |
| `projectiveDirectSumLocalization_right` | 各成分の包含を局所化し、局所化の直和から直和の局所化へ送る。 |
| `projectiveLocalizedDirectSumLinearEquiv` | 局所化は外部直和と交換する。 |
| `projectiveLocalizedDirectSumLinearEquiv_mk_lof` | 比較は、分母一の各成分を同じ成分へ送る。 |
| `projectiveLocalizationToDirectSum_naturality` | 直和と局所化の比較は、係数の線形写像に自然。 |

## ProjectiveLocalizedDirectSumComponents

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumComponents`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizationToDirectSum_component` | 局所化と直和の比較は、各成分への射影に自然。 |
| `projectiveLocalizedDirectSumLinearEquiv_mk_component` | 任意の分母を持つ元の第 i 成分は、分子の第 i 成分を同じ分母で割ったもの。 |
| `projectiveLocalizedModuleCongr` | 係数加群の線形同値を局所化へ移す。 |
| `projectiveLocalizedModuleCongr_mk` | 加群の局所化の同値は分子に元の同値を適用する。 |

## ProjectiveLocalizedDirectSumRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedDirectSumLinearEquiv_restriction` | 局所化と直和の比較は、分母を広げる制限に自然。 |

## ProjectiveLocalizedFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedFrobenius`

| 宣言 | 主張 |
| --- | --- |
| `projectivePrimePowerRingHom` | p の像が零であれば、零環も含め p 乗は環準同型である。 |
| `projectivePrimePowerRingHom_eq_frobenius` | 通常の指数標数の Frobenius と、p が零であることから作った冪写像は一致する。 |
| `projectiveLocalized_primeCast_eq_zero` | 元の係数環で p が零なら、局所化でも p は零。空の標準開の場合も含む。 |
| `projectiveLocalizedFrobenius` | 実際の局所化環の Frobenius。局所化が零環でも定義できる。 |
| `projectiveLocalizedFrobenius_mk` | 局所化の Frobenius は、分子と分母を共に p 乗へ送る。 |
| `projectiveFrobeniusDenominator_pow` | 分母 fⁿ の p 乗は、同じ f の n*p 冪。 |
| `projectiveLocalizedFrobenius_fraction` | 標準開の Frobenius は、元の分母の指数を p 倍にする。 |
| `projectiveModuleAwayRestriction_pow` | 局所化の制限は、係数環の作用による分子の冪の計算と可換。 |
| `projectiveLocalizedFrobenius_restriction` | 実際の局所化の Frobenius は、標準開を狭める制限と可換。 |
| `projectiveLocalizedFrobeniusSemilinear` | 実際の局所化の Frobenius は、元の基底環の Frobenius について半線形。 |

## ProjectiveModuleScalarGradedLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarGradedLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveModuleScalarGradedAwayLinearEquiv` | 分子の各部分加群を指定した局所化も、係数環の変更で同一視できる。 |
| `projectiveModuleScalarGradedAwayLinearEquiv_val` | 斉次成分の比較も、通常の局所化の比較と同じ元を与える。 |

## ProjectiveModuleScalarLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveModuleScalarDenominator` | 分母の冪を係数環へ写す。 |
| `projectiveModuleScalarLocalizationLinearEquiv` | 係数環へ写した分母の局所化との線形同値。 |
| `projectiveModuleScalarLocalizationLinearEquiv_mk` | 局所化の比較は、分子を保ち、分母だけを係数環へ写す。 |
| `projectiveModuleScalarLocalizationLinearEquiv_mk_one` | 比較は分母一の分子を保つ。 |

## ProjectiveModuleScalarLocalizationRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalizationRestriction`

| 宣言 | 主張 |
| --- | --- |
| `projectiveModuleScalarLocalizationLinearEquiv_mk_pow` | 係数環の変更は、斉次分数で使う分母の冪をその像の同じ冪へ写す。 |
| `projectiveModuleScalarLocalizationLinearEquiv_restriction` | 係数環の変更は、分母を広げる局所化の制限と可換。 |
| `projectiveModuleScalarGradedRestriction_mem` | 分子を追加因子で移す条件は、係数環へ写した追加因子でも成り立つ。 |
| `projectiveModuleScalarGradedAwayLinearEquiv_restriction` | 斉次成分での係数環の変更も、標準開の制限に自然。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq` | 分母の像を別の指定された分母と同定して、係数環の変更を行う。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_fraction` | 指定した分母との同定を含む比較も、分子と分母の冪の表示を保つ。 |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_restriction` | 分母の像を標準分母と同定した係数環の変更は、標準開の制限にも自然。 |

## ProjectiveNatCechExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatCechExact`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatFullCech_shortExact` | 自然数次数を保つ短完全列は、全タプル標準開 Čech 複体でも短完全。 |

## ProjectiveNatChartColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimit`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartColimitDiagram` | 有限段の実際の標準開の係数図式を並べる filtered 図式。 |
| `projectiveNatChartColimitCocone` | 各有限段から、余極限の次数付き加群の実際の標準開への余錐。 |
| `projectiveNatChartColimitMap` | 標準開の図式全体で定義した canonical な filtered colimit 比較。 |
| `projectiveNatChartColimitNumerator` | 標準開の分子族の余極限は、余極限の次数成分から作った分子族に一致する。 |

## ProjectiveNatChartColimitComponent

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitComponent`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartColimitNumerator_map` | 次数を保つ有限段の写像は、標準開の分子族も保つ。 |
| `projectiveNatChartColimitNumerator_step` | 各有限段の標準開の分子族は、その標準開の分母倍で次の項へ移る。 |
| `projectiveNatChartColimitComponentDiagramIso` | 標準開の成分図式を、固定した分母の斉次局所化の図式と明示的に同定する。 |
| `projectiveNatChartColimitComponentEquiv` | 実際の標準開の有限交叉ごとの filtered colimit 比較は線形同型。 |
| `projectiveNatChartColimitComponentDiagramIso_ι` | 図式の明示的な同定は、各有限段からの標準の射を保つ。 |
| `projectiveNatChartColimitComponentEquiv_ι_val` | 各段の標準開からの写像と、成分ごとの余極限同型は同じ局所化分数を与える。 |

## ProjectiveNatChartColimitIso

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitIso`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartColimitMap_app_isIso` | 標準開の filtered colimit の canonical な比較射は各有限交叉で同型。 |
| `projectiveNatChartColimitIso` | 標準開間の制限写像を含め、図式全体の filtered colimit 比較は同型。 |
| `projectiveNatCechFilteredHomologyIso` | 実際の射影標準開の Čech H と filtered colimit の比較。 |

## ProjectiveNatChartColimitNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartColimitDiagramMap` | 次数を保つ図式の射が誘導する、標準開の filtered 図式の射。 |
| `projectiveNatChartColimitTargetMap` | 図式の射の余極限が誘導する、余極限の実際の標準開の射。 |
| `projectiveNatChartColimitMap_naturality` | 実際の標準開の比較射は、次数を保つ図式の射に自然。 |
| `projectiveNatCechFilteredHomologyIso_naturality` | 実際の射影標準開の Čech H の余極限比較は、次数を保つ図式の射に自然。 |

## ProjectiveNatChartColimitTarget

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitTarget`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartColimitTargetIso` | 指定された実際の極限の加群の標準開と、各有限段の標準開の filtered colimit の同型。 |
| `projectiveNatCechFilteredHomologyTargetIso` | 指定された実際の極限の係数での Čech H と、有限段の Čech H の余極限との比較。 |

## ProjectiveNatChartDirectSumInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartDirectSumInclusion`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedModuleChartInclusion` | 自然数次数で、各成分の包含を標準開の図式へ渡す。 |
| `projectiveNatGradedModuleChartDirectSumCechHomologyIso_inclusion` | 自然数次数の Čech 直和比較は各成分からの包含を保つ。 |

## ProjectiveNatChartExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatChartExact`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatChartMap_surjective` | 次数ごとに全射な加群の射は、各標準開の指定次数部分へも全射。 |
| `projectiveNatChartMap_exact` | 次数を保つ完全列は、各標準開の指定次数部分でも完全。 |

## ProjectiveNatCoefficientNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatCoefficientNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatCoefficientChartIso` | 自然数次数の係数比較を、次数成分の恒等写像を介して構成する。 |
| `projectiveNatCoefficientChartIso_naturality` | 自然数次数の係数比較は、次数を保つ加群の射に自然。 |
| `projectiveNatCoefficientCechIso` | 自然な標準開比較が誘導する Čech コホモロジーの係数比較。 |
| `projectiveNatCoefficientCechIso_naturality` | 自然数次数の Čech 係数比較は、次数を保つ加群写像に自然。 |

## ProjectiveNatGradedChartDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradingInt_directSum_mem_iff` | 自然数次数の直和の分子の対応は、負の次数を零に延ばしても成り立つ。 |
| `projectiveNatGradedSMul_of_directSumLinearEquiv` | 各成分の次数付き作用を、次数を対応させる直和の同値で全体へ移す。 |
| `projectiveNatGradedModuleChartDirectSumIso` | 自然数次数の直和の同値が誘導する標準開の係数図式の同型。 |
| `projectiveNatGradedModuleChartDirectSumCechHomologyIso` | 自然数次数の直和の同値が誘導する、Čech 版のコホモロジーの直和同型。 |

## ProjectiveNatGradedChartIso

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartIso`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedChartIso_inverse_mem` | 指定した次数の同型は、逆写像も同じ次数を保つ。 |
| `projectiveNatGradedChartIso` | 次数成分を保つ加群の同型が、標準開の係数図式に与える自然同型。 |

## ProjectiveNatGradedChartMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradingInt_map_mem` | 自然数次数を保つ写像は、負の成分を零に延ばした次数も保つ。 |
| `projectiveNatGradedModuleChartMap` | 自然数の Proj 次数を保つ写像が誘導する、標準開の係数図式の写像。 |
| `projectiveNatGradedModuleCechHomologyMap` | 次数を保つ写像が誘導する、標準開 Čech コホモロジーの写像。 |

## ProjectiveNatGradedChartMapLaws

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedModuleChartMap_id` | 自然数次数の標準開への写像は恒等写像を保つ。 |
| `projectiveNatGradedModuleChartMap_comp` | 自然数次数の標準開への写像は合成を保つ。 |
| `projectiveNatGradedModuleCechHomologyMap_comp` | 自然数次数の Čech コホモロジーへの写像も合成を保つ。 |
| `projectiveNatGradedModuleChartMap_baseScalar` | 自然数次数の標準開の図式では、基底係数の写像は恒等自然変換のスカラー倍。 |
| `projectiveNatGradedModuleCechHomologyMap_baseScalar` | 自然数次数の Čech コホモロジーで、基底係数の写像は既存のスカラー作用。 |

## ProjectiveNatGradedChartZero

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartZero`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLaurentDenominator_mem_natGrade` | 標準開の分母は、変数の個数の自然数次数に斉次。 |
| `projectiveNatGradedChartZero_mul_denominator` | 分母を一回掛けると、次数零の分子の指定部分は次の段へ移る。 |
| `projectiveNatGradedChartZero_submodule_eq` | 整数次数に延ばした次数零の分子は、元の自然数次数の分子と一致する。 |
| `projectiveNatGradedChartZeroLinearEquiv` | 自然数次数の標準開図式の次数零は、元の次数を持つ分子の局所化。 |

## ProjectiveNatGradedEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedEquiv`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedModuleChartIso` | 両方向で Proj 次数を保つ同型が誘導する、標準開の図式の同型。 |
| `projectiveNatGradedModuleCechHomologyIso` | 次数付き加群の同型が誘導する、標準開 Čech コホモロジーの同型。 |

## ProjectiveNatGradedFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedOrderedCechHomology_finite` | 自然数次数の有限生成多項式加群の狭義増加 Čech コホモロジーは有限生成。 |
| `projectiveNatGradedFullCechHomology_finite` | 自然数次数の有限生成多項式加群の全タプル Čech コホモロジーは有限生成。 |

## ProjectiveNatGradedTensorBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedTensorBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedTensorChartDiagram` | 各標準開の係数を実際に B とテンソル積した図式。 |
| `projectiveNatGradedTensorCechIso` | 標準開 Čech コホモロジーのテンソル積と、テンソル係数の Čech 計算との同型。 |
| `projectiveNatGradedTensorCechIso_naturality` | テンソル係数の標準開 Čech 比較は、次数を保つ加群写像に自然。 |
| `projectiveNatGradedTensorCechHomology_finite` | flat なテンソル係数の標準開 Čech コホモロジーは B 上有限生成。 |

## ProjectiveNatGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradingInt` | 自然数次数の加群を、負の次数では零として整数次数へ延ばす。 |
| `projectiveNatGradingInt_natCast` | 自然数次数の加群を、負の次数では零として整数次数へ延ばす。 |
| `projectiveNatGradingPieceMap` | 自然数次数の一つの成分を、整数次数の同じ成分に入れる。 |
| `projectiveNatGradingDirectSumMap` | 直和の自然数添字を整数へ埋める。 |
| `projectiveNatGradingIntDecomposition` | 負の成分を零にしても、元の加群の次数分解が得られる。 |
| `projectivePolynomialDegree_eq_natCast` | 整数としての多項式の次数は、自然数としての指数の次数の埋め込み。 |
| `projectivePolynomialGrade_natCast` | 自然数次数では、多項式の整数次数成分と標準的な斉次成分が一致する。 |
| `projectivePolynomialGrade_eq_bot_of_neg` | 負の次数の多項式は零。 |
| `projectiveNatGradingIntSMul` | 自然数次数の多項式作用は、零で延ばした整数次数の加群にも作用する。 |
| `projectiveNatGradedModuleChartDiagram` | 自然数次数の加群の標準開係数図式を、整数次数へ延ばして作る。 |

## ProjectiveNatPolynomialCoefficientChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatPolynomialCoefficientChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradingInt_restrictScalars` | 自然数次数を負の次数で零に延ばす操作は、係数制限と交換する。 |
| `projectiveNatPolynomialCoefficientChangeChartIso` | 自然数次数の標準開図式の係数環変更と係数制限の比較。 |
| `projectiveNatPolynomialCoefficientChangeCechHomologyIso` | 自然数次数の Čech コホモロジーについて、係数環変更と係数制限を比較する。 |

## ProjectiveNativeTensorCechBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNativeTensorCechBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNativeTensorCechIso` | 実際の基底変更後の標準開 Čech コホモロジーと、元のコホモロジーのテンソル積の同型。 |
| `projectiveNativeTensorCechIso_naturality` | 実際の標準開の Čech flat 底変換の比較は、次数を保つ加群写像に自然。 |
| `projectiveNativeTensorCechHomology_finite` | 実際の flat 底変換後の標準開 Čech コホモロジーは B 上有限生成。 |

## ProjectivePolynomialCoefficientChange

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientChange`

| 宣言 | 主張 |
| --- | --- |
| `projectivePolynomialCoefficientDenominator` | 多項式の係数変更は、標準開の変数の積を同じ変数の積へ写す。 |
| `projectiveGradedPolynomialCoefficientChangeLinearEquiv` | 標準開の係数変更と、B 加群から R 加群への係数制限を合成する。 |
| `projectiveGradedPolynomialCoefficientChangeChartIso` | 多項式の係数変更と係数制限による、標準開の係数図式の同型。 |
| `projectiveGradedPolynomialCoefficientChangeCechHomologyIso` | 多項式の係数変更による Čech コホモロジーと、B 上のコホモロジーの係数制限との同型。 |

## ProjectivePolynomialCoefficientMapNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientMapNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedPolynomialCoefficientChangeLinearEquiv_map` | 各標準開の係数環比較は、Proj 次数を保つ加群写像に自然。 |
| `projectiveGradedPolynomialCoefficientChangeChartIso_naturality` | 係数環比較の図式の同型は、Proj 次数を保つ加群写像に自然。 |
| `projectiveGradedPolynomialCoefficientChangeCechHomologyIso_naturality` | 多項式係数変更の Čech コホモロジー比較は、次数を保つ写像に自然。 |

## ProjectivePolynomialTwistFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePolynomialTwistFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `projectivePolynomialTwistFullCechHomology_finite` | 多項式環の捻りの全タプル Čech コホモロジーは有限生成。 |
| `projectivePolynomialTwistOrderedCechHomology_finite` | 多項式環の捻りの狭義増加 Čech コホモロジーは有限生成。 |

## ProjectiveProjAdicCech

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCech`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjAdicScheme` | Proj の指定した大域スカラーに沿う実際の I 進閉厚化。 |
| `projectiveProjAdicProjection` | Proj の実際の閉厚化からの射。 |
| `projectiveProjAdicCechComplex` | 実際の I 進閉厚化の逆像被覆の構造層の Čech 複体。 |
| `projectiveProjAdicCechComplexIso` | Rees の商の Čech 複体と canonical な実際の閉厚化の Čech 複体の同型。 |
| `projectiveProjAdicCechTransition` | 実際の厚化間のスキームの射が誘導する Čech の遷移。 |

## ProjectiveProjAdicCechHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCechHomology`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjAdicCechHomology` | 実際の閉厚化の標準開被覆による Čech コホモロジー。 |
| `projectiveProjAdicCechHomologyTransition` | 実際の厚化間の射が誘導する Čech コホモロジーの遷移。 |
| `projectiveProjAdicCechHomologyProjection` | 元の構造層から実際の閉厚化への Čech コホモロジーの射影。 |
| `projectiveProjSourceCechHomology` | 元の Proj の構造層の標準開 Čech コホモロジー。 |
| `projectiveProjSourceCechHomologyIso` | 元の Proj の標準開被覆の Čech H と、次数零の計算の同型。 |
| `projectiveProjAdicCechHomologyIso` | 実際の閉厚化の Čech H と、Rees の商による計算の同型。 |
| `projectiveProjAdicCechHomologyIso_transition` | 閉厚化の Čech H の比較は I 進遷移と可換。 |
| `projectiveProjAdicCechHomologyIso_projection` | 閉厚化の Čech H の比較は、元の構造層からの射影と可換。 |
| `projectiveProjAdicCechFamilies` | 実際の閉厚化の Čech コホモロジーの互換族。 |
| `projectiveProjAdicCechFamiliesEquiv` | Rees の商の互換族と、実際の閉厚化の Čech 互換族の線形同型。 |

## ProjectiveProjAdicCechProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjAdicCechProjection`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjAdicCechProjection` | 元の Proj の構造層の Čech 複体から、実際の閉厚化への引き戻し。 |
| `projectiveProjAdicCechProjection_transition` | 実際の閉厚化への射影は、厚化間の実際の Čech 遷移と可換。 |
| `projectiveProjAdicCechComplexIso_projection` | Rees の射影を実際の閉厚化へ移す複体の比較は、元の射影と可換。 |
| `projectiveProjAdicCechComplexIso_transition` | Rees の商と実際の閉厚化の Čech 複体の比較は、I 進遷移に自然。 |

## ProjectiveProjCechComplexIso

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechOpen` | Proj の変数に対応する実際の標準開の族。 |
| `projectiveProjCechOpen_intersection` | 変数の像の積の標準開は、Čech の有限交叉と一致する。 |
| `projectiveProjCechSectionLinearEquiv` | 非空交叉の斉次局所化と、構造層の実際の切断との R 線形同型。 |
| `projectiveProjCechSectionLinearEquiv_naturality` | 非空交叉の R 線形同型は、Čech の制限写像に自然。 |
| `projectiveProjNativeCechComplexIso` | 斉次局所化で計算した Čech 複体と、実際の標準開の構造層の Čech 複体の同型。 |

## ProjectiveProjCechFormalFunctions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjCechFormalFunctions`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechFormalFunctions` | 実際の Proj と閉厚化の構造層に対する Čech 版の形式関数の同型。 |
| `projectiveProjCechFormalFunctions_of_apply` | Čech 形式関数の同型は、元の切断のコホモロジーを実際の閉厚化へ制限する。 |

## ProjectiveProjClosedPullbackCoefficient

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjClosedPullbackCoefficient`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjPullbackCechPresheaf` | 元の基底のスカラーを実際に引き戻して、構造層の係数前層を作る。 |
| `projectiveProjClosedPullbackCoefficient` | 非空交叉の次数零加群の係数から、実際に引き戻した切断への線形写像。 |
| `projectiveProjClosedPullbackCoefficient_apply` | 係数の線形写像は、元の Proj の切断の実際の引き戻しそのもの。 |
| `projectiveProjClosedPullbackCoefficient_naturality` | 次数零加群から実際の切断への射は、非空交叉の制限に自然。 |
| `projectiveProjClosedPullbackCoefficient_surjective` | 閉厚化への係数の写像は、実際の切断へ全射。 |
| `projectiveProjClosedPullbackCoefficient_ker` | 閉厚化の実際の切断への係数の写像の核は、元の係数の J 倍。 |

## ProjectiveProjNativeCechEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechEvaluation`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeNatCechComplexIso_apply` | 実際の構造層への複体の比較は、各タプルで非空交叉の切断の同型。 |
| `projectiveProjNativeCech_intersection_le` | 標準開の交叉は、実際の Proj の射での対応する交叉の逆像に含まれる。 |
| `projectiveProjNativeCechMap_apply` | 実際の Proj の Čech の射は、タプルごとに構造層の appLE に等しい。 |

## ProjectiveProjNativeCechFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeNatCechComplexIso` | 指定次数の代数的な複体から、実際の Proj の標準開への比較。 |
| `projectiveProjNativeStandardCechHomology_finite` | 実際の Proj の構造層の標準開 Čech H の有限性。 |
| `projectiveProjNativeAffineCechHomology_finite` | 実際の Proj の構造層の、任意の有限アフィン被覆での Čech H の有限性。 |

## ProjectiveProjNativeCechMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechMaps`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeCech_preimageOpen` | 実際の Proj の標準開の逆像は、次の係数環での同じ標準開。 |
| `projectiveProjNativeCechMap` | Proj の実際の構造層を引き戻す、標準開の Čech の射。 |

## ProjectiveProjNativeCechNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `projectiveProjNativeNatCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |

## ProjectiveProjNativeFilteredHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeFilteredHomology`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeFilteredHomologyIso` | 実際の極限の Proj の構造層の Čech H と、各有限段の次数零 Čech H の余極限の比較。 |

## ProjectiveProjNativeFrobeniusEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeFrobeniusEvaluation`

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradedChartZeroFrobenius` | 捻り零の Frobenius は、同じ次数零チャートへの半線形写像。 |
| `projectiveNatGradedChartZeroFrobenius_val` | 捻り零の Frobenius の周囲の局所化への像。 |
| `projectiveHomogeneousChartLinearEquiv_frobenius` | 加群のチャートの Frobenius は、実際の斉次局所化の p 乗に一致する。 |
| `projectiveProjNativeChart_frobenius` | 分数の比較を実際の標準開の切断へ移しても Frobenius は p 乗に一致する。 |

## ProjectiveProjNativeNatCechSections

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeNatCechSections`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjNativeNatCechSectionEquiv` | 次数零加群で計算した標準開の非空交叉と、実際の切断の線形同型。 |
| `projectiveProjNativeNatCechSectionEquiv_naturality` | 元の次数零加群から実際の切断への比較は、非空交叉の制限に自然。 |
| `projectiveProjCechOpenIntersection_isAffineOpen` | 標準開の非空交叉は実際の Proj のアフィン開。 |

## ProjectiveProjRingMapSections

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjRingMapSections`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjRingMapSections_apply` | 斉次分数の係数の写像は、実際の Proj の構造層の引き戻しそのもの。 |

## ProjectiveProjRingMapSectionsOfEq

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjRingMapSectionsOfEq`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |

## ProjectiveProjScalarNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjScalarNaturality_fraction` | 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 |
| `projectiveScalarToGlobalSections_naturality` | Proj の引き戻しは、元の基底環の大域スカラーを保つ。 |

## ProjectiveProjScalarSections

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarToZero` | 基底環のスカラーは零次成分に属する。 |
| `projectiveScalarToGlobalSections` | 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 |
| `projectiveScalarToGlobalSections_restrict` | 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 |
| `projectiveHomogeneousAway_scalar_mul` | 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 |
| `projectiveProjAwaySectionLinearEquiv` | 正次数の標準開の構造層の環同型は、元の基底環上でも線形。 |
| `projectiveProjAwaySectionLinearEquiv_pow` | 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 |

## ProjectiveProjStandardSections

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjStandardSections`

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjStandardOpen_eq_intersection` | 変数の像の積に対応する標準開は、各変数の像の標準開の有限交叉。 |
| `projectiveProjStandardSectionIso` | Čech の非空有限交叉の係数環と、その上の構造層の切断の環同型。 |
| `projectivePolynomialDenominatorImage_factor` | 添字を増やすときの分母の像を、追加した変数の像で因数分解する。 |
| `projectiveProjStandardSectionIso_naturality` | 有限性を計算した係数の制限は、標準開上の構造層の切断の制限に対応する。 |
| `projectiveProjStandardAffineOpenCover` | 次数一の変数の像が irrelevant ideal を生成する場合の標準アフィン開被覆。 |

## ProjectiveRightTensorLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveRightTensorLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedModule_mk_add` | 同じ分母を持つ局所化の分数は、分子について加法的である。 |
| `projectiveRightTensorLocalizationEquiv` | 加群の実際の局所化と右テンソル積を交換する、P 線形な同型。 |
| `projectiveRightTensorLocalizationEquiv_mk_one` | 局所化と右テンソル積の比較は、分母一の純テンソルを保つ。 |
| `projectiveRightTensorLocalizationEquiv_mk` | 局所化と右テンソル積の比較は、純テンソルの分母を保つ。 |
| `projectiveRightTensorLocalizationEquiv_naturality` | 局所化と右テンソル積の比較は、P 線形な加群写像に自然。 |
| `projectiveRightTensorLocalizationEquiv_restriction` | 局所化と右テンソル積の比較は、標準開を狭める制限にも自然。 |

## ProjectiveRingQuotientGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveRingQuotientGrading`

| 宣言 | 主張 |
| --- | --- |
| `projectiveRingQuotientGrade` | 実際の商環の次数成分は、元の次数成分の商写像による像。 |
| `projectiveRingQuotientGradeGradedMonoid` | 環の商の次数成分は、単位と積を保つ。 |
| `projectiveRingQuotientGradeGradedSMul` | 商環の次数成分は、元の多項式環の次数付き作用を受け継ぐ。 |
| `projectiveRingQuotientProjection_preservesPiece` | 実際の商写像は、商環の次数成分へ元の次数成分を送る。 |
| `projectiveRingQuotient_primeCast_eq_zero` | p の像は、零環を許す実際の商環でも零。 |
| `projectiveRingQuotientCechFrobenius_naturality` | 実際の商環への射影と、標準開の Čech Frobenius は可換。 |

## ProjectiveScalarGradedLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarGradedLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarModuleAwayLinearEquiv` | 係数環と代数の二つの加群局所化を、同じ環局所化を経由して比較する。 |
| `projectiveScalarModuleAwayLinearEquiv_mk` | 係数環を変える局所化の比較は、分母の冪と分子を保つ。 |
| `projectiveScalarGradedAwayLinearEquiv` | 分子の各部分加群を指定した局所化も、係数環の変更で同一視できる。 |
| `projectiveScalarGradedAwayLinearEquiv_val` | 斉次成分の比較も、通常の局所化の比較と同じ元を与える。 |

## ProjectiveScalarGradedMapNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarGradedMapNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveModuleScalarGradedAwayLinearEquivOfEq_map` | 分母の同定を含む係数環比較は、分子の次数を保つ加群写像に自然。 |
| `projectiveGradedAwayScalarRestrictionLinearEquiv_map` | 斉次局所化の係数制限の比較は、分子の次数を保つ加群写像に自然。 |

## ProjectiveScalarLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarLocalization`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarLocalization_denominators` | 分母の冪を代数へ写すと、その像の冪全体になる。 |
| `projectiveScalarLocalizationLinearEquiv` | 係数環の加群としての局所化を、代数の元の像による環局所化と比較する。 |
| `projectiveScalarLocalizationLinearEquiv_mk` | 局所化の比較は、分子を保ち、分母だけを代数へ写す。 |

## ProjectiveScalarRestrictionComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionComparison`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarModuleAwayLinearEquiv_restriction` | 係数環を変える局所化の比較は、追加因子を反転する制限と可換。 |

## ProjectiveScalarRestrictionTransport

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionTransport`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarRestrictionTransportModule` | 係数制限した B 加群との R 線形同値に沿って、X に B の作用を移す。 |
| `projectiveScalarRestrictionTransport_scalarTower` | 移した B 作用は、もとの R 作用と両立する。 |
| `projectiveScalarRestrictionTransportLinearEquiv` | 移した作用を持つ加群との B 線形同値。 |
| `projectiveScalarRestrictionTransportLinearEquiv_apply` | 作用を移す前後で、比較同値の元への値は変わらない。 |
| `projectiveScalarRestrictionTransport_finite` | B 上有限な加群との比較に沿って移した作用について、X も B 上有限となる。 |
| `projectiveScalarRestrictionTransportModuleOfIso` | 係数制限した加群からの同型を用いて、終域の R 加群へ B 作用を移す。 |
| `projectiveScalarRestrictionTransportOfIso_scalarTower` | 同型を用いて移した B 作用は、終域の既存の R 作用と両立する。 |
| `projectiveScalarRestrictionTransportLinearEquivOfIso` | 同型を用いて移した作用に関する、B 線形な比較。 |
| `projectiveScalarRestrictionTransportOfIso_finite` | 係数制限した有限 B 加群との同型から、移した作用に関する有限性を得る。 |

## ProjectiveScalarRestrictionTransportComponent

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionTransportComponent`

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarRestrictionTransportOfIso_component_smul` | 比較で移した B 作用は、成分の写像の可換式に沿って成分を移す。 |

## ProjectiveTensorChartComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartComparison`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorPiece_int` | 負次数を零に延ばす操作は、次数成分のテンソル像と交換する。 |
| `projectiveTensorChartNumerator_eq` | 分母の冪ごとのテンソル像は、基底変更後の指定次数の分子と一致する。 |
| `projectiveTensorChartRightLinearEquiv` | 基底変更後の各標準開の指定次数部分と、元の標準開の右テンソル積との B 線形同型。 |
| `projectiveTensorChartLinearEquiv` | 基底変更後の各標準開の指定次数部分と、元の標準開の左テンソル積との B 線形同型。 |
| `projectiveTensorChartRightLinearEquiv_fraction` | 右テンソルによる標準開の比較は、指定次数の純テンソル分数を保つ。 |
| `projectiveTensorChartLinearEquiv_fraction` | 左テンソルによる標準開の比較も、指定次数の純テンソル分数を保つ。 |

## ProjectiveTensorChartDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartDiagram`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorChartLinearEquiv_restriction` | 各標準開のテンソル比較は、標準開を狭める制限と可換。 |
| `projectiveTensorChartComponentIso` | 環準同型から係数構造を固定した、各標準開の実際のテンソル比較。 |
| `projectiveTensorChartComponentIso_hom_tmul` | 各標準開の環準同型による比較は、左純テンソルの既存の比較と一致する。 |
| `projectiveTensorChartDiagramIso` | 元の標準開図式のテンソル底変換と、基底変更後の実際の標準開図式との自然同型。 |

## ProjectiveTensorChartNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorChartNaturality`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorChartLinearEquiv_map` | 各標準開の実際のテンソル比較は、次数を保つ加群写像に自然。 |
| `projectiveTensorChartDiagramIso_naturality` | 標準開図式の実際のテンソル比較は、次数を保つ加群写像の自然変換と可換。 |

## ProjectiveTensorGradedChart

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorGradedChart`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorGradedModuleChartDiagram` | 基底変更後の B[X] 加群の、指定次数の実際の標準開図式。 |
| `projectiveTensorPiece_injective` | flat な基底変更では、元の次数成分のテンソル積は全体のテンソル積に単射。 |
| `projectiveTensorPieceEquiv` | flat な基底変更後の次数成分は、元の次数成分のテンソル積と同型。 |
| `projectiveTensorPieceEquiv_tmul` | 次数成分の比較は、純テンソルの元を同じ元へ送る。 |
| `projectiveTensorGradedModuleChartMap` | 次数付き加群の射から、基底変更後の実際の標準開図式の射を得る。 |

## ProjectiveTensorGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorGrading`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorPiece` | 基底変更した次数成分は、元の次数成分のテンソル積の像。 |
| `projectiveTensorPiece_tmul_mem` | 元の次数成分の純テンソルは、基底変更後の同じ次数成分に入る。 |
| `projectiveTensorPiece_monomial_smul_mem` | 単項式の作用は、テンソル像で定めた次数を加える。 |
| `projectiveTensorPiece_gradedSMul` | 基底変更後の B[X] の斉次作用は、テンソル像の次数を保つ。 |
| `projectiveTensorPiece_map_mem` | 次数を保つ元の加群写像は、テンソル像の次数成分も保つ。 |

## ProjectiveTensorPolynomialModule

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveTensorPolynomialModule`

| 宣言 | 主張 |
| --- | --- |
| `projectiveTensorPolynomialModule` | 基底変更後の実際の多項式加群構造。 |
| `projectiveTensorPolynomial_map_smul` | 係数変更した多項式の作用は、元の多項式の作用と一致する。 |
| `projectiveTensorPolynomial_C_smul` | 定数多項式の作用は、右係数 B の作用に一致する。 |
| `projectiveTensorPolynomial_monomial_tmul` | 単項式の作用は、元の単項式の作用と右係数の乗法で計算できる。 |
| `projectiveTensorPolynomial_coefficient_scalarTower` | B[X] の作用は、右係数 B の作用を拡張する。 |
| `projectiveTensorPolynomial_base_scalarTower` | B[X] の作用は、元の基底 R の作用と両立する。 |
| `projectiveTensorPolynomial_polynomial_scalarTower` | 基底変更後の多項式作用は、元の R[X] の作用と両立する。 |
| `projectiveTensorPolynomialMap` | 元の多項式加群の射を、基底変更後の B[X] 線形な射へ送る。 |
| `projectiveTensorPolynomialMap_tmul` | 基底変更後の多項式加群の射は、純テンソルの元の因子だけに作用する。 |

## ReesAdicChartIdealRange

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicChartIdealRange`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveChartInclusion_range_ideal` | IⁿM から元の標準開の次数 d 成分への写像の像は、同じ成分の Iⁿ 倍。 |

## ReesAdicClosedChartQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicClosedChartQuotient`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedChart_exact` | Rees の閉厚化の列は、各標準開の指定次数部分でも完全。 |
| `reesAdicProjectiveClosedChartProjection_surjective` | 閉厚化への射影は、各標準開の指定次数部分へ全射。 |
| `reesAdicProjectiveClosedChartProjection_ker` | 閉厚化への指定次数の標準開の射の核は、元の成分の Iⁿ 倍。 |
| `reesAdicProjectiveClosedChartQuotientIso` | Rees の閉厚化の標準開は、元の標準開の指定次数成分の Iⁿ 倍による商。 |
| `reesAdicProjectiveClosedChartQuotientIso_mk` | 商の同型は、元の標準開の成分を元の Rees の射影で送る。 |

## ReesAdicDirectSumGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicDirectSumGrading`

| 宣言 | 主張 |
| --- | --- |
| `ReesAdicTotalModule` | 拡大イデアルによる I 進 Rees 加群の台。 |
| `reesAdicDirectSumPolynomialLinearEquiv` | 各 IⁿM の直和と Rees 加群の、多項式環上の線形同値。 |
| `reesAdicTotalBaseModule` | 基底環の作用は多項式環を経由させる。 |
| `reesAdicTotalBaseModule_scalarTower` | 基底作用と基底 Rees 環の作用の両立性。 |
| `reesAdicDirectSumLinearEquiv` | 基底環上でも線形な Rees 加群の直和比較。 |
| `reesAdicDirectSumLinearEquiv_coeff` | 比較同値は、直和の第 n 成分を Rees の第 n 係数へ送る。 |
| `reesAdicDirectSumProjectivePiece` | 直和の Proj 次数は各成分で判定する。 |
| `reesAdicDirectSumLinearEquiv_mem_iff` | Rees 加群との比較は、直和の Proj 次数を保つ。 |

## ReesAdicGradedLocalizedDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicGradedLocalizedDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicDirectSumPolynomialLinearEquiv_projective_mem` | Rees 同値の分子の次数は、各 IⁿM の同じ Proj 次数に対応する。 |
| `reesAdicGradedLocalizedDirectSumLinearEquiv` | 指定 Proj 次数の Rees 局所化と、各 IⁿM の同じ次数の局所化の直和の同値。 |

## ReesAdicIdealPiece

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicIdealPiece`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectivePiece_image_eq_ideal_smul` | Rees の IⁿM の自然数次数 d の像は、元の d 成分の Iⁿ 倍。 |
| `reesAdicProjectiveIntPiece_image_eq_ideal_smul` | 整数への零延長後も、Rees の次数成分の像は同じ Iⁿ 倍。 |

## ReesAdicLocalizedDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicLocalizedDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicLocalizedDirectSumLinearEquiv` | 任意の多項式の冪による局所化での、Rees 加群と次数成分の直和の比較。 |
| `reesAdicLocalizedDirectSumLinearEquiv_mk_component` | 比較は分母を保ち、分子をその Rees 次数成分へ送る。 |

## ReesAdicNativeClosedCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCech`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicNativeClosedPushedComplexIso` | Rees の商の Čech 複体と、実際の切断を押し出した係数の複体との同型。 |
| `reesAdicNativeClosedCechComplexIso` | Rees の商の Čech 複体と、実際の閉厚化の逆像被覆の Čech 複体との同型。 |
| `reesAdicNativeClosedCechHomologyIso` | Rees の商の H と、実際の閉厚化の構造層の Čech H の比較。 |
| `reesAdicNativeClosedPushedComplexIso_projection` | 元の係数からの Rees の射影は、実際の切断を引き戻す Čech の射と一致する。 |

## ReesAdicNativeClosedCoefficient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCoefficient`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicNativeClosedCoefficientIso` | 実際の閉厚化の切断と Rees の商の、非空交叉での canonical な係数同型。 |
| `reesAdicNativeClosedCoefficientIso_projection_apply` | 係数同型は、元の係数からの射影を実際の引き戻しへ送る。 |
| `reesAdicNativeClosedCoefficientIso_projection` | 非空交叉の同型は、元の係数からの射影と実際の引き戻しを同じ射にする。 |
| `reesAdicNativeClosedCoefficientIso_naturality` | 実際の閉厚化の切断への係数同型は、非空交叉の制限に自然。 |

## ReesAdicNativeClosedProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedProjection`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicNativeClosedCechComplexIso_projection` | Rees の射影と、実際の閉厚化への構造層の Čech の引き戻しとの一致。 |
| `reesAdicNativeClosedCechComplexIso_projection_refined` | 実際の引き戻しを恒等添字の細分として書いても、Rees の射影と一致する。 |

## ReesAdicProjectiveCechDegreeShift

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechDegreeShift`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveDegreeShiftChartMap` | a∈Iⁱ の作用が誘導する、Rees 次数 j と i+j の標準開係数図式間の写像。 |
| `reesAdicProjectiveDegreeShiftCechHomologyMap` | a∈Iⁱ の作用が誘導する、Rees 次数 j と i+j の Čech コホモロジー間の写像。 |

## ReesAdicProjectiveCechDirectSum

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechDirectSum`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveBaseGrade` | Rees 加群の Proj 次数を、元の基底環に制限したもの。 |
| `reesAdicProjectiveBaseGradedSMul` | 元の多項式環の作用も、Rees 加群の Proj 次数を保つ次数付き作用。 |
| `reesAdicProjectiveBaseChartDirectSumIso` | P 上の Rees 加群の標準開の係数図式と、各 IⁿM の係数図式の直和との同型。 |
| `reesAdicProjectiveBaseCechHomologyDirectSumIso` | P 上の Rees 加群の Čech コホモロジーと、各 IⁿM の同じコホモロジーの直和との R 線形同型。 |

## ReesAdicProjectiveCechTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechTarget` | 元の加群の、固定した Proj・Čech 次数のコホモロジーの対象。 |
| `reesAdicProjectiveCechToModule` | 各 IⁿM の Čech コホモロジーから、元の加群の同じコホモロジーへの写像。 |
| `reesAdicProjectiveCechTransition` | IⁱM→IʲM の遷移が誘導する Čech コホモロジーの写像。 |
| `reesAdicProjectiveCechCoefficientLift` | Iⁿ の係数の持ち上げが誘導する、Čech コホモロジーの写像。 |
| `reesAdicProjectiveCechToModule_transition` | Čech 遷移と元のコホモロジーへの包含は可換。 |
| `reesAdicProjectiveCechTransition_comp` | Čech 遷移の合成は、指数の合成に一致。 |
| `reesAdicProjectiveCechToModule_degreeShift` | Čech の次数移動を元のコホモロジーへ送ると、基底係数の作用になる。 |
| `reesAdicProjectiveCechToModule_coefficientLift` | 係数の持ち上げと包含は、元の Čech コホモロジーのスカラー作用を与える。 |
| `reesAdicProjectiveCechTransition_degreeShift_factor` | 十分 I 進的な係数による Čech 次数移動の遷移は、元のコホモロジーを経由。 |

## ReesAdicProjectiveClosedCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveClosedCech`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechInclusionChartMap` | IⁿM の包含から得られる、標準開の係数図式の写像。 |
| `reesAdicProjectiveClosedCechProjectionChartMap` | 実際の閉厚化の商への射影が誘導する、標準開の係数図式の写像。 |
| `reesAdicProjectiveClosedCech_shortExact` | 実際の I 進閉厚化の列は、標準開の全タプル Čech 複体でも短完全。 |
| `reesAdicProjectiveClosedCechShortComplex` | 実際の I 進閉厚化の全タプル Čech 複体からなる短複体。 |
| `reesAdicProjectiveClosedCechShortComplex_shortExact` | 実際の閉厚化から作った Čech の短複体は短完全。 |

## ReesAdicProjectiveDegreeShift

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveDegreeShift`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveDegreeShift_mem` | Iⁱ の元の作用は、IʲM の元を Iⁱ⁺ʲM に送る。 |
| `reesAdicProjectiveDegreeShift` | Iⁱ の元による、多項式環上線形な Rees 次数 i の写像。 |
| `reesAdicProjectiveDegreeShift_preservesPiece` | 基底環の係数による作用は、Proj 次数を保つ。 |

## ReesAdicProjectiveModuleMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveModuleMap`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveSubmoduleMap` | 多項式加群の写像を、実際の IⁿM の間の写像に制限する。 |
| `reesAdicProjectiveQuotientMap` | 多項式加群の写像を、実際の I 進閉厚化の商の間へ降ろす。 |
| `reesAdicProjectiveSubmoduleMap_inclusion` | IⁿM の包含と加群写像の四角形は可換。 |
| `reesAdicProjectiveQuotientMap_projection` | 閉厚化への射影と加群写像の四角形は可換。 |
| `reesAdicProjectiveQuotientMap_transition` | 加群写像からの商写像は、閉厚化の遷移と可換。 |
| `reesAdicProjectiveSubmoduleMap_preservesPiece` | IⁿM の間の写像は、元の写像が保つ Proj 次数を保つ。 |
| `reesAdicProjectiveQuotientMap_preservesPiece` | 閉厚化の商写像は、元の写像が保つ Proj 次数を保つ。 |

## ReesAdicProjectivePieces

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectivePieces`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveSubmodule` | 基底環へ制限した、拡大イデアルの n 乗の作用による部分加群。 |
| `reesAdicProjectiveSubmodule_isHomogeneous` | IⁿM は、元の Proj 次数について斉次。 |
| `reesAdicProjectivePiece` | IⁿM 内の Proj 次数成分。 |
| `reesAdicProjectivePieceDecomposition` | IⁿM の Proj 次数分解。 |
| `reesAdicProjectivePolynomialModule` | IⁿM の多項式環上の加群構造。 |
| `reesAdicProjectivePolynomialModule_scalarTower` | 制限した基底作用と、多項式作用の両立性。 |
| `reesAdicProjectivePieceGradedSMul` | 制限した Proj 次数は、元の多項式の標準次数の作用と両立する。 |
| `reesAdicProjectivePolynomialModule_finite` | 有限な多項式加群の各 IⁿM は、多項式環上有限生成。 |

## ReesAdicProjectiveQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveQuotient` | I 進閉厚化の実際の商加群 M/IⁿM。 |
| `reesAdicProjectiveQuotientPolynomialModule` | 同じ商加群の、多項式環上の加群構造。 |
| `reesAdicProjectiveQuotientPolynomialModule_scalarTower` | 商における基底作用と多項式作用の両立性。 |
| `reesAdicProjectiveQuotientProjection` | 閉厚化の商への、多項式環上線形な射影。 |
| `reesAdicProjectiveQuotientProjection_surjective` | 閉厚化の商への射影は全射。 |
| `reesAdicProjectiveToModule_quotientProjection_exact` | IⁿM の包含と、閉厚化の商への射影は完全。 |
| `reesAdicProjectiveQuotientPiece` | I 進閉厚化の商の Proj 次数成分。 |
| `reesAdicProjectiveQuotientPieceDecomposition` | I 進閉厚化の商は、元の Proj 次数の分解を受け継ぐ。 |
| `reesAdicProjectiveQuotientProjection_preservesPiece` | 商への射影は Proj 次数を保つ。 |
| `reesAdicProjectiveQuotientPieceGradedSMul` | 閉厚化の商の次数と、多項式の次数の作用は両立する。 |

## ReesAdicProjectiveQuotientTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveQuotientTransition` | 閉厚化の実際の商加群の間の、多項式環上線形な I 進遷移。 |
| `reesAdicProjectiveQuotientTransition_projection` | 商への射影は、閉厚化の I 進遷移と可換。 |
| `reesAdicProjectiveQuotientTransition_preservesPiece` | 閉厚化の商の遷移は、Proj 次数を保つ。 |

## ReesAdicProjectiveTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveToModule` | 各 IⁿM から元の加群への包含。 |
| `reesAdicProjectiveSubmodule_antitone` | I 進部分加群は、指数が大きいほど小さい。 |
| `reesAdicProjectiveTransition` | IⁱM から IʲM への遷移（j≤i）。 |
| `reesAdicProjectiveToModule_transition` | 遷移と元の加群への包含は可換。 |
| `reesAdicProjectiveTransition_comp` | 遷移の合成は遷移に一致。 |
| `reesAdicProjectiveToModule_degreeShift` | 次数移動後に元の加群へ含めると、基底係数のスカラー写像になる。 |
| `reesAdicProjectiveCoefficientLift` | Iⁿ の係数の作用は、元の加群から IⁿM への写像を与える。 |
| `reesAdicProjectiveToModule_coefficientLift` | 係数の持ち上げと包含の合成は、元の加群のスカラー作用。 |
| `reesAdicProjectiveTransition_degreeShift_factor` | 係数が Iⁿ に入れば、次数移動からの遷移は元の加群を経由する。 |
| `reesAdicProjectiveToModule_preservesPiece` | 元の加群への包含は Proj 次数を保つ。 |
| `reesAdicProjectiveTransition_preservesPiece` | 遷移は Proj 次数を保つ。 |
| `reesAdicProjectiveCoefficientLift_preservesPiece` | 係数の持ち上げは Proj 次数を保つ。 |

## ReesCechImageAssembly

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechImageAssembly`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechImageAssembleR` | 各段の Čech 像への写像を、像の Rees 加群への R 線形写像に組む。 |
| `reesAdicProjectiveCechImageAssembleR_lof` | 一つの Čech 成分は、その像を係数とする Rees 単項式に写る。 |
| `reesAdicProjectiveCechImageAssembleR_surjective` | 各段の像への全射を組んだ R 線形写像は全射。 |
| `reesAdicProjectiveCechImageAssembleR_monomial_lof` | Čech 像への直和写像は、単項式と各成分で Rees 作用と可換。 |
| `reesAdicProjectiveCechImageAssemble` | 各段の Čech 像への写像を組んだ Rees 線形写像。 |
| `reesAdicProjectiveCechImageAssemble_surjective` | Čech コホモロジーの直和から、像の Rees 加群への Rees 線形写像は全射。 |

## ReesCechImageBounds

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechImageBounds`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechImageRees_finite` | 各 IⁿM からの Čech 像の Rees 加群は有限生成。 |
| `reesAdicProjectiveCechImage_bound` | Čech 版の実際の像の一様な I 進評価。 |
| `reesAdicProjectiveCechImage_cofinal` | Čech 像のフィルトレーションと I 進フィルトレーションは互いに共終。 |

## ReesCechImageFiltration

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechImageFiltration`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechStage` | IⁿM の、固定した Proj・Čech 次数のコホモロジーの対象。 |
| `reesAdicProjectiveCechImage` | 各 IⁿM の Čech コホモロジーからの包含の像。 |
| `reesAdicProjectiveCechImage_antitone` | Čech コホモロジーの像は、I 進指数について減少する。 |
| `reesAdicProjectiveCechImage_pow_smul_le` | Iⁱ と第 j 段の Čech 像の積は、第 i+j 段の像に入る。 |
| `reesAdicProjectiveCechImage_contains_pow` | 通常の Iⁿ 倍は、第 n 段からの Čech 像に入る。 |
| `reesAdicProjectiveCechImageFiltration` | 各 IⁿM の Čech 像からなる、元のコホモロジーの実際の I フィルトレーション。 |
| `reesAdicProjectiveCechImageStageMap` | 各段の Čech コホモロジーを、その像へ制限した線形写像。 |
| `reesAdicProjectiveCechImageStageMap_surjective` | 像へ制限した各段の Čech 写像は全射。 |

## ReesCechKernel

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechKernel`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechKernel` | Čech 像への Rees 全射の核。各段の包含の核をまとめる。 |
| `reesAdicProjectiveCechKernel_mem_iff` | Rees 核への所属は、各成分が実際の Čech 包含で零になることと同値。 |
| `reesAdicProjectiveCechKernel_lof_mem_iff` | 一つの斉次成分の Rees 核への所属は、その Čech 包含での零化と同値。 |
| `reesAdicProjectiveCechKernelHomogeneous` | 各段の実際の Čech 核の元を、一つの直和成分に入れた集合。 |
| `reesAdicProjectiveCechKernel_span_homogeneous` | 実際の Čech 核の Rees 加群は、その斉次な核の元で生成される。 |
| `reesAdicProjectiveCechKernel_finite` | Čech 核の Rees 加群は有限生成。 |
| `reesAdicProjectiveCechKernel_finite_homogeneous_generators` | 実際の Čech 核には有限個の斉次生成元を選べる。 |

## ReesCechKernelTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechKernelTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechTransition_mem_kernel` | 各段の Čech 包含の核は、I 進遷移で保たれる。 |
| `reesAdicProjectiveCechTransition_degreeShift_zero` | 十分 I 進的な係数による次数移動は、Čech 核の元の遷移を零にする。 |
| `reesAdicProjectiveCechKernel_bounded_homogeneous_generators` | 実際の Čech 核は、次数に一様な上界のある有限個の斉次元で生成される。 |

## ReesCechKernelVanishing

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCechKernelVanishing`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechTransitionComponent` | 直和の第 l 成分を取り、そこから第 n 段へ遷移する R 線形写像。 |
| `reesAdicProjectiveCechTransitionComponent_monomial_kernel_zero` | 十分高い次数の成分の遷移は、低次数の斉次核の元の単項式倍で零。 |
| `reesAdicProjectiveCechTransitionComponent_smul_kernel_zero` | 同じ成分の遷移は、低次数の斉次核の元の任意の Rees 倍で零。 |
| `reesAdicProjectiveCechTransitionComponent_zero_of_span` | 低次数の斉次核で生成した Rees 部分加群では、十分先の成分の遷移は零。 |
| `reesAdicProjectiveCechKernel_transition_zero_of_bounded_generators` | 次数が c 以下の斉次核で生成されれば、c だけ遅らせた核の遷移は零。 |
| `reesAdicProjectiveCechKernel_transition_eventually_zero` | 実際の Čech 包含の核の遷移は、一様に遅らせれば零になる。 |

## ReesClosedCechCompletion

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechCompletion`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechCompatibleFamilies` | 実際の閉厚化の Čech コホモロジーの互換族の加群。 |
| `reesAdicProjectiveClosedCechProjection_pow_le_ker` | Iⁿ 倍は、実際の閉厚化への Čech 写像の核に入る。 |
| `reesAdicProjectiveClosedCechProjection_linear_compat` | 閉厚化への Čech 射影の互換性を、線形写像の合成として述べる。 |
| `reesAdicProjectiveClosedCechCompletionMap` | 元の Čech コホモロジーの完備化から、実際の閉厚化の互換族への標準写像。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | 核の評価を、n+c 段の核が Iⁿ 倍に入るという形にする。 |
| `reesAdicProjectiveClosedCechCompatibleFamilies_mem_range` | 閉厚化の Čech 互換族の各成分は、元のコホモロジーからの像に入る。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | 実際の射影 Čech コホモロジーの形式関数の線形同型。 |

## ReesClosedCechFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechFrobenius`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechFrobenius` | 実際の商環の Frobenius を、同じ閉厚化の Rees 表示の Čech H へ戻す。 |
| `reesAdicProjectiveClosedCechFrobenius_compare` | Rees 表示へ戻した閉厚化の Čech Frobenius は、環の商の表示の写像そのもの。 |
| `reesAdicProjectiveClosedCechFrobenius_projection` | 実際の閉厚化の Čech Frobenius は、以前からの閉厚化への射影と可換。 |
| `reesAdicProjectiveClosedCechFrobenius_transition` | 実際の閉厚化の Čech Frobenius は、以前からの I 進遷移と可換。 |

## ReesClosedCechFrobeniusCompletion

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechFrobeniusCompletion`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechFrobenius_linear_transition` | 閉厚化の Čech Frobenius と I 進遷移の可換式を、半線形写像の等式で述べる。 |
| `reesAdicProjectiveClosedCechFamiliesFrobenius` | 実際の閉厚化の互換族へ誘導した Čech Frobenius。 |
| `reesAdicProjectiveClosedCechFrobenius_linear_projection` | 閉厚化の Frobenius と元の H の Frobenius の射影の可換式。 |
| `reesAdicProjectiveClosedCechCompletionMap_frobenius` | 標準の完備化比較は、実際の閉厚化の互換族の Čech Frobenius と可換。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius` | 射影版の形式関数の同型は、実際の Čech Frobenius と可換。 |

## ReesClosedCechHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechHomology`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechHomology` | 実際の閉厚化 M/IⁿM の全タプル Čech コホモロジーの対象。 |
| `reesAdicProjectiveClosedCechProjection` | 実際の閉厚化への射影が誘導する Čech コホモロジーの写像。 |
| `reesAdicProjectiveClosedCechConnecting` | 実際の閉厚化の Čech 長完全列の連結写像。 |
| `reesAdicProjectiveClosedCech_exact_middle` | 元の加群の Čech コホモロジーにおける、閉厚化の長完全列の完全性。 |
| `reesAdicProjectiveClosedCech_exact_projection_connecting` | 閉厚化の Čech コホモロジーにおける、長完全列の完全性。 |
| `reesAdicProjectiveClosedCech_exact_connecting_inclusion` | 次の次数の Čech コホモロジーにおける、長完全列の完全性。 |
| `reesAdicProjectiveClosedCechProjection_ker_eq_image` | 実際の閉厚化への Čech 写像の核は、IⁿM の Čech 包含の像に等しい。 |
| `reesAdicProjectiveClosedCechProjection_kernel_bound` | 実際の閉厚化への Čech 写像の核の一様な I 進評価。 |

## ReesClosedCechInverseSystem

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechInverseSystem`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechTransitionChartMap_self` | 閉厚化の標準開の図式における、同じ段の遷移は恒等写像。 |
| `reesAdicProjectiveClosedCechTransitionChartMap_comp` | 閉厚化の標準開の図式における、遷移の合成則。 |
| `reesAdicProjectiveClosedCechTransition_self` | 閉厚化の Čech コホモロジーの同じ段の間の遷移は恒等写像。 |
| `reesAdicProjectiveClosedCechTransition_comp` | 閉厚化の Čech コホモロジーの遷移の合成則。 |
| `reesAdicProjectiveClosedCechInverseSystem` | 実際の閉厚化の Čech コホモロジーの逆系。 |

## ReesClosedCechModuleMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleMap`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechModuleChartMap` | 加群写像から得られる、実際の閉厚化の標準開図式の写像。 |
| `reesAdicProjectiveClosedCechModuleMap` | 加群写像が誘導する、実際の閉厚化の Čech コホモロジーの写像。 |
| `reesAdicProjectiveClosedCechModuleChartMap_projection` | 標準開の図式の商写像は、閉厚化への射影と可換。 |
| `reesAdicProjectiveClosedCechModuleChartMap_transition` | 標準開の図式の商写像は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechModuleMap_projection` | 実際の閉厚化の Čech 写像は、元の Čech コホモロジーからの射影と可換。 |
| `reesAdicProjectiveClosedCechModuleMap_transition` | 実際の閉厚化の Čech 写像は、I 進遷移と可換。 |

## ReesClosedCechModuleNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechModuleNatTrans` | 実際の次数付き加群写像が誘導する、閉厚化の Čech 逆系の間の自然変換。 |
| `reesAdicProjectiveClosedCechModuleFamiliesMap` | 実際の次数付き加群写像が誘導する、閉厚化の Čech 互換族の間の線形写像。 |
| `reesAdicProjectiveClosedCechCompletionMap_module_naturality` | 完備化からの標準 Čech 写像は、実際の次数付き加群写像と可換。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv_module_naturality` | Čech 形式関数の同型は、実際の次数付き加群写像に自然。 |

## ReesClosedCechStabilization

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechStabilization`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveClosedCechTransition_range_eq_of_kernel_killed` | 次の次数の Čech 核が遷移で零になれば、実際の閉厚化の像は元の像に一致。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | 実際の閉厚化の Čech コホモロジーの像は、一様に遅らせれば安定する。 |

## ReesClosedCechTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechTransitionChartMap` | IⁱM→IʲM の写像が誘導する、標準開の係数図式の遷移。 |
| `reesAdicProjectiveClosedCechTransitionChartMap` | 閉厚化の商の間の写像が誘導する、標準開の係数図式の遷移。 |
| `reesAdicProjectiveClosedCechShortComplexMap` | 閉厚化の Čech 短完全列の間の、I 進遷移による射。 |
| `reesAdicProjectiveClosedCechTransition` | 実際の閉厚化の Čech コホモロジーの間の I 進遷移。 |
| `reesAdicProjectiveClosedCechTransition_projection` | 閉厚化への Čech 射影は、I 進遷移と可換。 |
| `reesAdicProjectiveClosedCechTransition_connecting` | 閉厚化の Čech 連結写像は、I 進遷移と可換。 |

## ReesClosedCoefficientAdicFormalFunctions

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientAdicFormalFunctions`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientAdicCechIso` | M/JM の実際の I 進閉厚化の、商係数 Čech 計算との比較。 |
| `reesClosedCoefficientAdicCechIso_transition` | 閉厚化の商係数比較は、以前の実際の I 進 Čech 遷移と可換。 |
| `reesClosedCoefficientAdicCechFamiliesEquiv` | 閉厚化の実際の互換族を、R/J 上の Čech 計算の互換族へ送る同型。 |
| `reesClosedCoefficientAdicCechFamiliesMap` | 元の M の閉厚化の互換族から、商係数で表示した M/JM の互換族への写像。 |
| `reesClosedCoefficientAdicCechFormalFunctions` | M/JM の Čech 形式関数を、R/J 上の各閉厚化の計算を用いて表す同型。 |
| `reesClosedCoefficientAdicCechFormalFunctions_naturality` | 商係数で表した Čech 形式関数も、元の M からの閉厚化射影と可換。 |

## ReesClosedCoefficientAdicModuleNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientAdicModuleNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientAdicModuleFamiliesMap` | 実際の M/JM→N/JN が誘導する、商係数の I 進 Čech 互換族の写像。 |
| `reesClosedCoefficientAdicModuleCechMap` | 実際の M/JM→N/JN が各 I 進段で誘導する、商係数の Čech 写像。 |
| `reesClosedCoefficientAdicCechIso_module_naturality` | 実際の閉厚化の各 I 進段の係数比較は、任意の元の次数付き加群写像に自然。 |
| `reesClosedCoefficientAdicCechFamiliesEquiv_module_naturality` | 実際の閉厚化の I 進互換族の係数比較は、任意の元の次数付き加群写像に自然。 |
| `reesClosedCoefficientAdicCechFormalFunctions_module_naturality` | M/JM の商係数表示の Čech 形式関数は、任意の元の次数付き加群写像に自然。 |

## ReesClosedCoefficientCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientCech`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientChartIso` | 実際の閉厚化の R 上の標準開図式と、R/J 上の表示の係数制限の同型。 |
| `reesClosedCoefficientCechHomologyIso` | 閉厚化の Čech コホモロジーは、商環上の同じ標準開計算の係数制限と一致する。 |
| `reesClosedCoefficientCechHomology_finite` | 商環 R/J 上で表示した閉厚化の標準開 Čech コホモロジーは有限生成。 |

## ReesClosedCoefficientGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientGrading`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientPiece` | 閉厚化の次数成分を、商環上の部分加群として表したもの。 |
| `reesClosedCoefficientPiece_restrictScalars` | 商係数の次数成分を R へ制限すると、元の次数成分そのものになる。 |
| `reesClosedCoefficientPieceGradedSMul` | 商係数の斉次多項式作用は、閉厚化の Proj 次数を保つ。 |

## ReesClosedCoefficientModule

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientModule`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficient_torsion` | J は実際の閉厚化 M/JM を消す。 |
| `reesClosedCoefficientModule` | 閉厚化の商環 R/J 上の係数加群構造。 |
| `reesClosedCoefficient_mk_smul` | 商環の代表による作用は元の R 作用に一致する。 |
| `reesClosedCoefficient_scalarTower` | 係数制限は元の R 加群構造を回復する。 |
| `reesClosedPolynomialCoefficient_torsion` | 拡大イデアルも、閉厚化の元の多項式加群構造を消す。 |
| `reesClosedPolynomialCoefficientModule` | 閉厚化の (R/J)[X] 上の係数加群構造。 |
| `reesClosedPolynomialCoefficient_map_smul` | 多項式の係数を商へ写してから作用させても、元の作用と同じ。 |

## ReesClosedCoefficientModuleMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientModuleMap`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientModuleMap` | 実際の閉厚化の商写像を、商係数多項式環上の写像として表す。 |
| `reesClosedCoefficientModuleMap_restrictScalars` | 元の多項式環への係数制限で、既存の実際の商写像を回復する。 |
| `reesClosedCoefficientModuleMap_preservesPiece` | 商係数の閉厚化の射も、実際の商次数成分を保つ。 |

## ReesClosedCoefficientNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCoefficientNaturalChartIso` | 実際の閉厚化の標準開の、射に自然な商係数比較。 |
| `reesClosedCoefficientNaturalCechIso` | 実際の閉厚化の Čech コホモロジーの、射に自然な商係数比較。 |
| `reesClosedCoefficientModuleChartMap` | 次数付き加群の射が誘導する、商係数の閉厚化の標準開の射。 |
| `reesClosedCoefficientNaturalChartIso_naturality` | 商係数の標準開比較は、実際の閉厚化の加群写像と可換。 |
| `reesClosedCoefficientModuleCechMap` | 元の次数付き加群の射から得られる、商係数の閉厚化の Čech 写像。 |
| `reesClosedCoefficientNaturalCechIso_naturality` | 商係数の Čech 比較は、実際の閉厚化の加群写像と可換。 |

## ReesClosedCoefficientTower

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientTower`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedPolynomialCoefficient_scalarTower` | 多項式環の係数変更に関する作用の塔。 |
| `reesClosedPolynomialCoefficient_base_scalarTower` | 元の基底から商係数の多項式環への作用の塔。 |
| `reesClosedPolynomialCoefficient_quotient_scalarTower` | 商基底から商係数の多項式環への作用の塔。 |

## ReesClosedRingComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingComparison`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRing_submodule_eq` | Rees の閉厚化の部分加群は、A の拡大イデアルの係数制限。 |
| `reesClosedRingLinearEquiv` | Rees の商加群表示と、実際の環の閉厚化との R 線形同型。 |
| `reesClosedRingPolynomialEquiv` | 実際の環の商との比較は、元の多項式環の作用も保つ。 |
| `reesClosedRingPolynomialEquiv_mem_iff` | 閉厚化の二つの表示の比較は、各 Proj 次数を両方向で対応させる。 |
| `reesClosedRingChartIso` | Rees の閉厚化と環の閉厚化の実際の標準開図式の比較。 |
| `reesClosedRingCechIso` | Rees の閉厚化の Čech H と、実際の環の商の Čech H の比較。 |

## ReesClosedRingNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingPolynomialEquiv_projection` | 環の商の比較は、既存の Rees の商への射影を実際の環の射影へ送る。 |
| `reesClosedRingTransition` | 実際の環の閉厚化の間の遷移。係数の指数が下がる商射。 |
| `reesClosedRingPolynomialEquiv_transition` | Rees と環の商の比較は、厚化間の実際の遷移と可換。 |
| `reesClosedRingTransition_preservesPiece` | 環の閉厚化の遷移も、商の Proj 次数を保つ。 |
| `reesClosedRingProjectionChartMap` | 環の閉厚化への射影が誘導する実際の標準開図式の射。 |
| `reesClosedRingTransitionChartMap` | 環の閉厚化の遷移が誘導する実際の標準開図式の射。 |
| `reesClosedRingChartIso_projection` | 実際の標準開の環の商の比較は、既存の閉厚化への射影と可換。 |
| `reesClosedRingChartIso_transition` | 環の商の標準開の比較は、以前の閉厚化間の遷移と可換。 |
| `reesClosedRingCechIso_projection` | 環の商の Čech 比較は、以前の実際の閉厚化への射影と可換。 |
| `reesClosedRingCechIso_transition` | 環の商の Čech 比較は、既存の閉厚化の I 進遷移と可換。 |

## ReesClosedTensorChart

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedTensorChart`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedTensorPiece_mem_iff` | 商とのテンソル比較は、元の次数成分を両方向で対応させる。 |
| `reesClosedTensorChartIso` | R/J にテンソルした加群の標準開図式と、既存の閉厚化の商係数図式との自然同型。 |
| `reesClosedTensorCechIso` | R/J にテンソルした加群の実際の標準開と、閉厚化の商係数表示の Čech 比較。 |

## ReesClosedTensorComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedTensorComparison`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedTensor_submodule_eq` | 拡大イデアルで定義した一段目の閉厚化は、実際の JM による商。 |
| `reesClosedTensorEquiv` | 既存の閉厚化と右テンソルの比較。まず元の基底環上で線形に構成する。 |
| `reesClosedTensorEquiv_tmul_mk` | テンソルと閉厚化の比較は、商環の代表を元の係数の作用として計算する。 |
| `reesClosedTensorEquiv_smul` | 商係数の作用についても、テンソルと閉厚化の比較は線形。 |
| `reesClosedTensorCoefficientEquiv` | 既存の R/J 係数の閉厚化との、R/J 線形な同型。 |
| `reesClosedTensorCoefficientEquiv_tmul_one` | 閉厚化の比較は、元の加群からの射影を保つ。 |
| `reesClosedTensorEquiv_polynomial_smul` | 商とテンソルの比較は、元の多項式環の作用を保つ。 |
| `reesClosedTensorPolynomialEquiv` | 既存の閉厚化の多項式係数表示と、テンソルの多項式作用との同型。 |
| `reesClosedTensorPiece_map_eq` | 次数成分のテンソル像は、既存の R/J 係数の商次数成分に一致する。 |

## ReesClosedTensorNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedTensorNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedTensorEquiv_naturality` | テンソルと閉厚化の比較は、元の多項式加群の射と可換。 |
| `reesClosedTensorChartIso_naturality` | R/J による標準開の表示の同型は、次数を保つ加群写像に自然。 |
| `reesClosedTensorCechIso_naturality` | R/J の実際の閉厚化の Čech 比較は、次数を保つ加群写像に自然。 |

## ReesClosedThickeningFormalFunctions

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedThickeningFormalFunctions`

| 宣言 | 主張 |
| --- | --- |
| `reesIteratedClosedSumCechFamilies` | 一重の商 M/(JM+IⁿM) の Čech コホモロジーの互換族。 |
| `reesIteratedClosedCechFamiliesEquiv` | 二重閉厚化と一重の商の Čech 比較を、互換族の線形同型へまとめる。 |
| `reesClosedThickeningSumCechFamiliesMap` | 元の M の閉厚化の互換族を、一重の商の Čech 互換族へ送る。 |
| `reesClosedThickeningSumCechFormalFunctions` | M/JM の Čech コホモロジーの完備化を、M/(JM+IⁿM) の互換族と比較する同型。 |
| `reesClosedThickeningSumCechFormalFunctions_naturality` | 一重の商で表した閉厚化の Čech 形式関数も、元の M からの射影と可換。 |

## ReesClosedThickeningNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedThickeningNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesClosedThickeningCechHomologyMap` | M→M/JM が誘導する、元の標準開 Čech コホモロジーの写像。 |
| `reesClosedThickeningCechFamiliesMap` | M→M/JM が誘導する、I 進閉厚化の Čech 互換族の間の写像。 |
| `reesClosedThickeningCechCompletionMap_naturality` | 実際の M/JM への閉厚化は、完備化からの標準 Čech 写像と可換。 |
| `reesClosedThickeningCechCompletionLinearEquiv_naturality` | Čech 形式関数の同型は、実際の M/JM への閉厚化と可換。 |

## ReesCoefficientAdicCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCech`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicProjection` | 変更後の基底環上で見た、実際の I 進商への射影。 |
| `reesCoefficientAdicPiece` | I 進商の Proj 次数成分を、変更後の係数環上の部分加群として表す。 |
| `reesCoefficientAdicPiece_restrictScalars` | I 進商の次数成分は、係数制限で元の R 上の商次数成分に戻る。 |
| `reesCoefficientAdicPieceGradedSMul` | 変更後の多項式係数の作用は、I 進商の次数を保つ。 |
| `reesCoefficientAdicTransition_preservesPiece` | 実際の I 進遷移は、変更後の係数環で表した次数成分も保つ。 |
| `reesCoefficientAdicChartIso` | I 進商の標準開図式の、変更後の係数環への比較同型。 |
| `reesCoefficientAdicChartTransition` | 変更後の係数環上での、実際の I 進遷移の標準開写像。 |
| `reesCoefficientAdicChartIso_transition` | I 進商の係数比較は、実際の I 進遷移と可換。 |

## ReesCoefficientAdicCechTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCechTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicOriginalCechHomology` | 元の R 上で計算する、実際の I 進商の Čech コホモロジー。 |
| `reesCoefficientAdicOriginalCechTransition` | 元の R 上で計算する、実際の I 進遷移の Čech 写像。 |
| `reesCoefficientAdicRestrictedCechHomology` | 変更後の係数環上で計算した Čech コホモロジーの係数制限。 |
| `reesCoefficientAdicCechIso` | I 進商の Čech コホモロジーの係数比較。 |
| `reesCoefficientAdicRestrictedCechTransition` | 変更後の係数環上の I 進遷移が誘導する Čech 写像の係数制限。 |
| `reesCoefficientAdicCechIso_transition` | I 進商の Čech 係数比較は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicRestrictedCechFamilies` | 変更後の係数環で計算した I 進 Čech コホモロジーの互換族。 |
| `reesCoefficientAdicCechFamiliesEquiv` | 元の R 上の互換族と、変更後の係数環上の計算の互換族との同型。 |

## ReesCoefficientAdicFamiliesNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicFamiliesNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicOriginalCechFamiliesMap` | 元の R 上の I 進 Čech 互換族の、実際の加群写像が誘導する写像。 |
| `reesCoefficientAdicRestrictedCechFamiliesMap` | B 上で計算した I 進 Čech 互換族の、実際の加群写像が誘導する写像。 |
| `reesCoefficientAdicCechFamiliesEquiv_module_naturality` | I 進 Čech 互換族の係数比較は、実際の加群写像に自然。 |
| `reesCoefficientAdicCechFamiliesEquiv_module_naturality_linear` | 互換族の係数比較の自然性を、R 線形写像の可換な合成として述べる。 |
| `reesCoefficientAdicCechFamiliesEquiv_symm_module_naturality` | 互換族の係数比較の逆写像も、実際の加群写像に自然。 |

## ReesCoefficientAdicFormalFunctionsNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicFormalFunctionsNaturality`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicCompletionMap` | 完備化から実際の I 進 Čech 互換族への標準写像を、B 上の表示へ送る。 |
| `reesCoefficientAdicOriginalCechFamiliesMap_eq_native` | 元の R 上の実際の互換族写像は、既存の I 進 Čech 写像に一致する。 |
| `reesCoefficientAdicCompletionMap_module_naturality` | 商係数表示の完備化からの標準 Čech 写像は、任意の次数付き加群写像に自然。 |
| `reesCoefficientAdicFormalFunctions` | Čech 形式関数を、B 上で計算した実際の I 進閉厚化の互換族で表す同型。 |
| `reesCoefficientAdicFormalFunctions_toLinearMap` | 商係数表示の形式関数の順写像は、既存の標準 Čech 写像そのものである。 |
| `reesCoefficientAdicFormalFunctions_module_naturality` | 商係数表示の Čech 形式関数は、任意の次数付き加群写像に自然。 |

## ReesCoefficientAdicModuleCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicModuleCech`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicModuleChartMap` | 実際の加群写像から得られる、B 上の I 進商の標準開の写像。 |
| `reesCoefficientAdicOriginalModuleChartMap` | 元の R 上で計算する、実際の加群写像の I 進商の標準開の写像。 |
| `reesCoefficientAdicModuleChartMap_transition` | B 上の I 進標準開写像は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicOriginalModuleChartMap_transition` | R 上の I 進標準開写像も、実際の I 進遷移と可換。 |
| `reesCoefficientAdicChartIso_module_naturality` | 各 I 進段の標準開係数比較は、実際の加群写像に自然。 |
| `reesCoefficientAdicOriginalCechModuleMap` | 元の R 上での、実際の加群写像からの I 進 Čech コホモロジーの写像。 |
| `reesCoefficientAdicRestrictedCechModuleMap` | B 上の実際の加群写像からの I 進 Čech 写像の係数制限。 |
| `reesCoefficientAdicOriginalCechModuleMap_transition` | R 上の実際の I 進 Čech 写像は遷移と可換。 |
| `reesCoefficientAdicRestrictedCechModuleMap_transition` | B 上の実際の I 進 Čech 写像の係数制限も遷移と可換。 |
| `reesCoefficientAdicCechIso_module_naturality` | I 進 Čech コホモロジーの係数比較は、実際の加群写像に自然。 |

## ReesCoefficientAdicModuleMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicModuleMap`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicQuotientModuleMap` | 変更後の多項式環上で見た、実際の加群写像の I 進商への降下。 |
| `reesCoefficientAdicQuotientModuleMap_restrictScalars` | 商係数の I 進商の写像の係数制限は、元の実際の商写像である。 |
| `reesCoefficientAdicQuotientModuleMap_projection` | 商係数の I 進商の写像は、商への実際の射影と可換。 |
| `reesCoefficientAdicQuotientModuleMap_transition` | 商係数の I 進商の写像は、実際の I 進遷移と可換。 |
| `reesCoefficientAdicQuotientModuleMap_preservesPiece` | 商係数の I 進商の写像は、元の射が保つ Proj 次数を保つ。 |

## ReesCoefficientAdicQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicQuotient`

| 宣言 | 主張 |
| --- | --- |
| `reesCoefficientAdicPolynomial_surjective` | 全射な基底係数変更は、多項式環の係数変更も全射にする。 |
| `reesCoefficientAdicSubmodule` | 実際の IⁿM を、変更後の多項式環上の部分加群として表す。 |
| `reesCoefficientAdicSubmodule_eq` | 変更後の係数環で表した IⁿM は、I の拡大冪の作用そのものである。 |
| `reesCoefficientAdicSubmodule_eq_mappedIdeal` | 同じ部分加群は、変更後の基底のイデアル I B の冪による作用でもある。 |
| `reesCoefficientAdicQuotientPolynomialModule` | 同じ I 進商の、変更後の多項式環上の加群構造。 |
| `reesCoefficientAdicQuotientModule` | 同じ I 進商の、変更後の基底環上の加群構造。 |
| `reesCoefficientAdicQuotient_base_scalarTower` | 元の基底と変更後の基底の作用の塔。 |
| `reesCoefficientAdicQuotient_base_polynomial_scalarTower` | 元の基底と変更後の多項式環の作用の塔。 |
| `reesCoefficientAdicQuotient_polynomial_scalarTower` | 変更後の基底と変更後の多項式環の作用の塔。 |
| `reesCoefficientAdicQuotient_coefficient_scalarTower` | 二つの多項式環の作用の塔。 |
| `reesCoefficientAdicQuotientTransition` | 変更後の多項式環上で見た、実際の I 進遷移。 |
| `reesCoefficientAdicQuotientTransition_restrictScalars` | I 進遷移の係数制限は、以前の実際の遷移そのものである。 |

## ReesDirectSumLinearMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesDirectSumLinearMap`

| 宣言 | 主張 |
| --- | --- |
| `reesDirectSumLinearMap_smul_of_monomial_lof` | 単項式と各直和成分で作用と可換なら、すべての Rees 元の作用と可換。 |
| `reesDirectSumLinearMapOfMonomialLof` | 単項式と各成分での可換性から、同じ値の Rees 線形写像を作る。 |
| `reesDirectSumLinearMapOfMonomialLof_surjective` | Rees 線形にする前の写像が全射なら、そのまま全射。 |

## ReesExtendedFiltration

モジュール：`SerrePositivity.AlgebraicGeometry.ReesExtendedFiltration`

| 宣言 | 主張 |
| --- | --- |
| `reesExtendedAdic_restrictScalars` | 拡大イデアルの冪の作用を制限すると、基底のイデアルの冪の作用になる。 |
| `reesExtendedAdic_map_mem` | 基底環上の線形写像は、拡大イデアルによる I 進フィルトレーションを保つ。 |
| `reesExtendedAdic_decompose_mem` | Proj 次数の斉次成分への射影は、各 IⁿM を保つ。 |

## ReesExtendedModule

モジュール：`SerrePositivity.AlgebraicGeometry.ReesExtendedModule`

| 宣言 | 主張 |
| --- | --- |
| `reesExtendedModule` | 拡大イデアルの Rees 加群に、基底の Rees 環を作用させる。 |
| `reesExtendedPolynomialMap` | 係数ごとに基底環上の線形写像を適用する。 |
| `reesExtendedPolynomialMap_coeff` | 係数写像の値。 |
| `reesExtendedModule_smul_coeff` | 基底の Rees 環の作用は、基底環上の係数の畳み込みで計算できる。 |
| `reesExtendedMap` | 基底環上の線形写像は、拡大イデアルの Rees 加群の基底 Rees 線形写像を与える。 |
| `reesExtendedMap_coeff` | 拡大 Rees 加群上の写像は、各係数で元の写像を適用する。 |

## ReesExtendedMonomialAction

モジュール：`SerrePositivity.AlgebraicGeometry.ReesExtendedMonomialAction`

| 宣言 | 主張 |
| --- | --- |
| `reesMap_monomial` | Rees 代数の係数写像は、任意の次数の斉次単項式を保つ。 |
| `reesExtendedModule_monomial_smul_single` | 拡大 Rees 加群の次数 j の単項式に、基底 Rees 環の次数 i の単項式を掛ける。 |

## ReesFiltrationAdic

モジュール：`SerrePositivity.AlgebraicGeometry.ReesFiltrationAdic`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicMap` | 線形写像が I 進フィルトレーションから誘導する Rees 加群の写像。 |
| `reesAdicMap_surjective` | 全射な加群写像は、I 進 Rees 加群にも全射を与える。 |
| `reesKernelFiltration` | 元のフィルトレーションと写像の核との交叉。 |
| `reesKernelInclusion` | 核との交叉から、元の Rees 加群への包含。 |
| `reesKernelInclusion_injective` | 核との交叉から得る Rees 加群の包含は単射。 |
| `reesKernelInclusion_exact` | 核との交叉は、Rees 加群の写像の核を各次数で実現する。 |
| `reesKernelFiltration_stable` | Noether 環上の有限加群では、安定なフィルトレーションと核との交叉も安定。 |
| `reesKernelModule_finite` | 核との交叉の Rees 加群は、安定な場合に有限生成。 |

## ReesFiltrationExact

モジュール：`SerrePositivity.AlgebraicGeometry.ReesFiltrationExact`

| 宣言 | 主張 |
| --- | --- |
| `reesFiltrationMap_surjective` | 各次数で全射な写像は、Rees 加群でも全射。 |
| `reesFiltrationMap_exact` | 各次数で完全な二つの写像は、Rees 加群でも完全。 |

## ReesFiltrationGrade

モジュール：`SerrePositivity.AlgebraicGeometry.ReesFiltrationGrade`

| 宣言 | 主張 |
| --- | --- |
| `reesFiltrationGrade` | Rees 加群の一つの次数の斉次部分加群。 |
| `reesFiltrationProjection` | Rees 加群の係数を一つの次数の単項式へ戻す射影。 |
| `reesFiltrationCoeff_single` | 同じ次数の単項式の係数は元の元に戻る。 |
| `isInternal_reesFiltrationGrade` | 各次数の斉次部分加群は Rees 加群の内部直和を与える。 |
| `reesFiltrationGradeDecomposition` | Rees 加群の自然数次数の分解。 |
| `reesFiltrationGradeSMul` | Rees 環の斉次作用は、加群の自然数次数を加える。 |

## ReesFiltrationMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ReesFiltrationMaps`

| 宣言 | 主張 |
| --- | --- |
| `reesFiltrationMap` | フィルトレーションを保つ線形写像から得る Rees 環上の線形写像。 |
| `reesFiltrationMap_coeff` | Rees 加群の写像は係数ごとに元の写像を適用する。 |
| `reesFiltrationMap_single` | Rees 加群の写像は単項式と可換。 |
| `reesFiltrationMap_id` | 恒等写像が与える Rees 加群の写像。 |
| `reesFiltrationMap_comp` | Rees 加群の写像は合成を保つ。 |
| `reesFiltrationMap_assemble` | Rees 加群の写像と、次数成分の直和から足す写像の可換性。 |
| `reesFiltrationMap_injective` | 元の写像が単射なら、フィルトレーションを保つ Rees 加群の写像も単射。 |

## ReesFiltrationModule

モジュール：`SerrePositivity.AlgebraicGeometry.ReesFiltrationModule`

| 宣言 | 主張 |
| --- | --- |
| `reesFiltrationCoeff` | Rees 加群の一つの次数の係数を取り出す。 |
| `reesFiltrationSingle` | フィルトレーションの一つの成分を Rees 加群の単項式に入れる。 |
| `reesFiltrationSingle_coeff` | Rees 加群の単項式の係数。 |
| `reesFiltrationAssemble` | 各次数成分の直和から Rees 加群へ単項式を足し合わせる。 |
| `reesFiltrationAssemble_of` | 直和の一つの成分は、対応する単項式に写る。 |
| `reesFiltrationAssemble_coeff` | 直和から足した元の係数は、元の直和の同じ次数の成分。 |
| `reesFiltrationAssemble_injective` | Rees 加群の単項式表示は一意。 |
| `reesFiltration_sum_single` | Rees 加群の元は、その有限個の係数を持つ単項式の和に等しい。 |
| `reesFiltrationAssemble_surjective` | Rees 加群の各元は、その有限個の係数を持つ単項式の和。 |
| `reesFiltrationDirectSumLinearEquiv` | フィルトレーションの各次数の直和と、Mathlib の Rees 加群の線形同型。 |
| `reesFiltration_monomial_smul_single` | Rees 環の斉次単項式は、加群の次数をその指数だけ上げる。 |
| `reesFiltration_finite` | 安定なフィルトレーションの Rees 加群は Rees 環上有限生成。 |

## ReesIntegerCechAction

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIntegerCechAction`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveIntegerCoefficientChartIso` | 整数の Proj 次数を固定した、R と B 上の標準開の係数比較。 |
| `reesAdicProjectiveIntegerBaseScalarChartMap` | Rees 係数 b の作用が誘導する、R 上の標準開図式の自己写像。 |
| `reesAdicProjectiveIntegerCoefficientChartIso_scalar` | 整数次数の標準開係数比較は、実際の Rees 係数の作用と可換。 |
| `reesAdicProjectiveIntegerCoefficientCechHomologyIso` | R と B 上の整数次数の Rees の Čech コホモロジーの比較。 |
| `reesAdicProjectiveIntegerCoefficientCechHomologyIso_scalar` | Čech コホモロジーの係数比較も、実際の Rees スカラー作用と可換。 |
| `reesAdicProjectiveIntegerChartInclusion_monomial` | Rees 単項式と各次数の包含の可換式を、標準開の図式へ渡す。 |

## ReesIntegerCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIntegerCechComparison`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveIntegerBaseGrade` | B 上で整数次数へ延ばしてから R に係数制限した、Rees の Proj 次数。 |
| `reesAdicProjectiveIntegerBaseGrade_mem_iff` | 整数次数の対応は、図式の移送ではなく所属の命題として示す。 |
| `reesAdicProjectiveIntegerBaseChartDirectSumIso` | 整数次数の R 上の Rees 標準開図式と、各 IⁿM の図式の直和との比較。 |
| `reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso` | 整数次数の R 上の Rees Čech コホモロジーと、各 IⁿM の直和との比較。 |
| `reesAdicProjectiveIntegerCechHomologyDirectSumIso` | 同じ B 上の Čech コホモロジーを R へ制限し、各 IⁿM の直和へ比較する。 |

## ReesIntegerCechComponentAction

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIntegerCechComponentAction`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveIntegerCechObject` | B 上で整数次数へ延ばした Rees の標準開 Čech コホモロジー。 |
| `reesAdicProjectiveIntegerCechComponentMap` | 各 IⁿM の Čech コホモロジーから、Rees の B 上の計算を R に制限したものへの写像。 |
| `reesAdicProjectiveIntegerCechComponentMap_directSum` | Rees の各次数のコホモロジーからの写像は、直和比較で lof に移る。 |
| `reesAdicProjectiveIntegerCechComponentMap_monomial` | Rees 単項式は、各次数からの Čech 写像を次の次数からの写像へ移す。 |

## ReesIntegerCechGradedAction

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIntegerCechGradedAction`

| 宣言 | 主張 |
| --- | --- |
| `ReesIntegerCechDirectSum` | 各 IⁿM の同じ Proj・Čech 次数のコホモロジーの直和。 |
| `reesAdicCechIntegerDirectSumTransportedModule` | 自然な整数次数の比較に沿って、Čech コホモロジーの直和に Rees 作用を移す。 |
| `reesAdicCechIntegerDirectSumTransportedScalarTower` | 移した Rees 作用は、直和の既存の R 作用と両立する。 |
| `reesAdicCechIntegerDirectSumTransportedLinearEquiv` | 整数次数の比較に沿って移した作用に関する B 線形同値。 |
| `reesAdicCechIntegerDirectSum_monomial_smul_lof` | Rees 単項式の実際の Čech 作用は、直和の第 j 成分を第 i+j 成分へ送る。 |
| `reesAdicCechIntegerDirectSumPiece` | コホモロジーの直和の、第 n Rees 次数の部分加群。 |
| `reesAdicCechIntegerDirectSumGradedSMul` | 移した B 作用は、実際の Rees 次数の直和分解と両立する。 |
| `reesAdicProjectiveIntegerCechObject_finite` | B 上の整数次数の Rees Čech コホモロジーは B 上有限生成。 |
| `reesAdicCechIntegerDirectSumFinite` | 次数付き性を確認した Rees 作用について、Čech コホモロジーの直和は B 上有限。 |

## ReesIntegerCechInclusion

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIntegerCechInclusion`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveIntegerCoefficientInclusion` | 各 IⁿM から Rees 加群への、多項式環上線形な包含。 |
| `reesAdicProjectiveIntegerCoefficientInclusion_apply` | 上の包含は、Rees 加群の第 n 単項式を作る。 |
| `reesAdicProjectiveIntegerChartInclusion` | 各 IⁿM の包含が誘導する、整数次数の標準開図式の写像。 |
| `reesAdicProjectiveIntegerBaseChartDirectSumIso_inclusion` | Rees の標準開直和比較は、各次数の包含を係数図式の直和の包含へ送る。 |
| `reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso_inclusion` | Rees の Čech 直和比較は、各次数の包含をコホモロジーの直和の lof に送る。 |
| `reesAdicProjectiveIntegerCoefficientInclusion_monomial` | Rees 単項式の作用と各次数の包含が作る、多項式環上線形な可換式。 |

## ReesIteratedClosedCechTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIteratedClosedCechTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesIteratedClosedSumChartTransition` | 一重の商の遷移が誘導する、標準開の係数図式の写像。 |
| `reesIteratedClosedSumCechHomology` | 一重の商 M/(JM+IⁿM) の Čech コホモロジーの対象。 |
| `reesIteratedClosedSumCechTransition` | 一重の商の遷移が誘導する、Čech コホモロジーの写像。 |
| `reesIteratedClosedChartIso` | 二重閉厚化と一重の商の、標準開の係数図式の比較同型。 |
| `reesIteratedClosedChartIso_transition` | 二重閉厚化の標準開での比較は、実際の遷移と可換。 |
| `reesIteratedClosedCechHomologyIso_transition` | 二重閉厚化の Čech 比較は、実際の I 進遷移と可換。 |

## ReesIteratedClosedGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIteratedClosedGrading`

| 宣言 | 主張 |
| --- | --- |
| `reesIteratedClosedSumPiece` | 単一の商 M/(JM+IⁿM) における、元の Proj 次数成分の像。 |
| `reesIteratedClosedQuotientLinearEquiv_preservesPiece` | 二重閉厚化から単一の商への同型は、元の Proj 次数を保つ。 |
| `reesIteratedClosedQuotientLinearEquiv_symm_preservesPiece` | 単一の商から二重閉厚化への逆写像も、元の Proj 次数を保つ。 |
| `reesIteratedClosedSumPieceGradedSMul` | 単一の商の Proj 次数と、多項式の次数の作用は両立する。 |
| `reesIteratedClosedCechHomologyIso` | 二重閉厚化と M/(JM+IⁿM) の標準開 Čech コホモロジーの比較同型。 |

## ReesIteratedClosedQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIteratedClosedQuotient`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectivePolynomialSubmodule` | 多項式環上で見た、基底イデアルの拡大冪による部分加群。 |
| `reesIteratedClosedQuotient_submodule_image` | 全射 M→M/JM による IⁿM の像は、Iⁿ(M/JM) に等しい。 |
| `reesIteratedClosedQuotientLinearEquiv` | (M/JM)/Iⁿ(M/JM) と M/(JM+IⁿM) の、多項式環上線形な同型。 |

## ReesIteratedClosedSumDecomposition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIteratedClosedSumDecomposition`

| 宣言 | 主張 |
| --- | --- |
| `reesIteratedClosedSum_isHomogeneous` | 分母 JM+IⁿM は、元の Proj 次数について斉次。 |
| `reesIteratedClosedSumPieceDecomposition` | 一重の商の Proj 次数成分は、商加群の直和分解を与える。 |
| `reesIteratedClosedSumCechHomology_finite` | 一重の商 M/(JM+IⁿM) の標準開 Čech コホモロジーは有限生成。 |

## ReesIteratedClosedTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesIteratedClosedTransition`

| 宣言 | 主張 |
| --- | --- |
| `reesIteratedClosedSumTransition` | 一重の商 M/(JM+IⁱM) から M/(JM+IʲM) への遷移。 |
| `reesIteratedClosedQuotientLinearEquiv_transition` | 二重閉厚化から一重の商への同型は、実際の遷移と可換。 |
| `reesIteratedClosedSumTransition_preservesPiece` | 一重の商の遷移は、元の Proj 次数を保つ。 |

## ReesPolynomialBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.ReesPolynomialBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `reesPolynomialBaseChange` | 基底の Rees 環の係数と、元の多項式の変数を評価する環準同型。 |
| `reesPolynomialBaseChange_C` | Rees 係数の評価は既存の Rees 写像。 |
| `reesPolynomialBaseChange_X` | 元の変数は、拡大イデアルの Rees 環の定数部分へ送る。 |
| `reesPolynomialBaseChange_map` | 元の多項式の係数を基底の Rees 環へ写してから評価すると、定数部分に戻る。 |
| `reesPolynomialBaseChange_surjective` | 拡大イデアルの Rees 環は、基底の Rees 環と元の変数で生成される。 |
| `reesPolynomialBaseChange_module_finite` | 拡大イデアルの Rees 環上有限な加群は、基底の Rees 環上の多項式環でも有限。 |
| `reesPolynomialBaseChange_module_scalarTower` | Rees 係数の作用と、多項式環に沿う作用は両立する。 |
| `reesPolynomialCoefficientAlgebra` | 元の多項式環からの係数拡大を、基底 Rees 環上の多項式環の代数構造にする。 |
| `reesPolynomialBaseChange_source_scalarTower` | 元の多項式環の作用と、基底 Rees 環上の多項式作用も両立する。 |
| `reesAdicPolynomialModule_finite` | 有限生成多項式加群の I 進 Rees 加群は、基底の Rees 環上の多項式環で有限生成。 |

## ReesPolynomialCoefficientTowers

モジュール：`SerrePositivity.AlgebraicGeometry.ReesPolynomialCoefficientTowers`

| 宣言 | 主張 |
| --- | --- |
| `reesPolynomialCoefficientAlgebra_scalarTower` | P→B[X] の係数変更は、基底環 R からの代数構造と両立する。 |
| `reesPolynomialBaseChange_base_scalarTower` | 制限した B[X] 作用は、P を経由する基底環上の作用と両立する。 |

## ReesProjectiveCechTransportedModule

モジュール：`SerrePositivity.AlgebraicGeometry.ReesProjectiveCechTransportedModule`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCechObject` | B[X] 上の Rees 加群の標準開 Čech コホモロジーを B 加群としてまとめる。 |
| `reesAdicCechDirectSumTransportedModule` | Čech コホモロジーの直和へ、Rees 比較によって B 作用を移す。 |
| `reesAdicCechDirectSumTransportedScalarTower` | 移した Rees 作用は、直和の既存の R 作用と両立する。 |
| `reesAdicCechDirectSumTransportedLinearEquiv` | 移した作用に関して、直和と Rees の Čech コホモロジーは B 線形に同値。 |
| `reesAdicProjectiveCechObject_finite` | B[X] 上の Rees の Čech コホモロジーは B 上有限生成。 |
| `reesAdicCechDirectSumTransportedFinite` | 比較で移した作用について、各 IⁿM の Čech コホモロジーの直和は B 上有限生成。 |

## ReesProjectiveCoefficientComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesProjectiveCoefficientComparison`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveCoefficientChartIso` | P 上と B[X] 上の Rees 加群の標準開の図式を、R に係数制限して比較する。 |
| `reesAdicProjectiveCoefficientCechHomologyIso` | Rees 加群の二つの多項式環での Čech コホモロジーを R 上で比較する。 |
| `reesAdicProjectiveCechHomologyDirectSumIso` | B[X] 上の Rees 加群の Čech コホモロジーを R に制限したものと、各 IⁿM の直和との同型。 |

## ReesProjectiveFiniteness

モジュール：`SerrePositivity.AlgebraicGeometry.ReesProjectiveFiniteness`

| 宣言 | 主張 |
| --- | --- |
| `reesProjective_X_smul_coeff` | 多項式変数の作用は、Rees 係数ごとに元の変数を作用させる。 |
| `reesProjectivePolynomialGradedSMul` | 元の変数は Proj 次数を一つ上げ、基底 Rees 環上の次数付き作用を与える。 |
| `reesProjectiveFullCechHomology_finite` | Rees 加群の Proj 標準開の全タプル Čech コホモロジーは、基底 Rees 環上有限生成。 |

## ReesProjectiveGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ReesProjectiveGrading`

| 宣言 | 主張 |
| --- | --- |
| `reesProjectiveProjection` | 元の Proj 次数への射影を、拡大イデアルの Rees 加群へ持ち上げる。 |
| `reesProjectiveGrade` | 持ち上げた射影の像としての Proj 次数成分。 |
| `reesProjectiveProjection_coeff` | Proj 次数の射影は、各 Rees 係数の Proj 次数への射影。 |
| `mem_reesProjectiveGrade_iff` | Proj 次数の所属は、全ての Rees 係数の所属で判定する。 |
| `isInternal_reesProjectiveGrade` | 二つ目の、Proj 次数による内部直和。 |
| `reesProjectiveGradeDecomposition` | Rees 加群の Proj 次数分解。 |

## ReesQuotientTransitionLaws

モジュール：`SerrePositivity.AlgebraicGeometry.ReesQuotientTransitionLaws`

| 宣言 | 主張 |
| --- | --- |
| `reesAdicProjectiveQuotientTransition_self` | 閉厚化の同じ段の間の遷移は恒等写像。 |
| `reesAdicProjectiveQuotientTransition_comp` | 閉厚化の二つの遷移の合成は、直接の遷移に等しい。 |

## SchemeAdicBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAdicBaseChange`

| 宣言 | 主張 |
| --- | --- |
| `schemeAdicBaseChange` | 実際の Iⁿ による閉厚化。 |
| `schemeAdicBaseChangeProjection` | 閉厚化から元のスキームへの射。 |
| `schemeAdicBaseChangeStructure` | 閉厚化の商環上の構造射。 |
| `schemeAdicBaseChange_isPullback` | 定義した閉厚化は、実際に元の構造射の底変換。 |
| `schemeAdicBaseChangeTransition` | 小さい指数の閉厚化から大きい指数の閉厚化への canonical な射。 |
| `schemeAdicBaseChangeTransition_projection` | 閉厚化の遷移は、元のスキームへの射と可換。 |
| `schemeAdicBaseChangeTransition_structure` | 閉厚化の遷移は、基底の商環の射とも可換。 |
| `schemeAdicBaseChangeTransition_self` | 同じ指数の閉厚化の遷移は恒等射。 |
| `schemeAdicBaseChangeTransition_comp` | 閉厚化の遷移を二度合成すると、直接の遷移になる。 |

## SchemeAffineBaseChangeNativeSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeNativeSections`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffineBaseChangeNativeSectionsEquiv` | アフィン底変換の実際の切断の同型を、元の構造層の係数加群の間で述べる。 |
| `schemeAffineBaseChangeNativeSectionsEquiv_unit` | 実際の切断の同型は、1 と元の切断の純テンソルを構造層の引き戻しへ送る。 |

## SchemeAffineBaseChangeTensor

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeTensor`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffineSectionAlgebra` | 構造射を指定したアフィン開の切断を、基底環上の代数として束ねる。 |
| `schemeAffineBaseChangeSections_isPushout` | 実際のアフィン切断の正方形を、元の R と A を頂点に持つ pushout に移す。 |
| `schemeAffineBaseChangeTensorIso` | 実際の底変換のアフィン切断と、元の環上のテンソル積の環同型。 |
| `schemeAffineBaseChangeTensorIso_left` | テンソル積の左の写像は、底変換先の構造射が誘導する scalar の写像。 |
| `schemeAffineBaseChangeTensorIso_right` | テンソル積の右の写像は、元の構造層の実際の引き戻し。 |

## SchemeAffineBaseChangeTensorLinear

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeTensorLinear`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffineBaseChangeTensorIso_tmul` | 純テンソルの実際の切断への像は、scalar の像と切断の引き戻しの積。 |
| `schemeAffineBaseChangeSectionsLinearEquiv` | 実際のアフィン底変換の切断の比較は、底変換先の環上で線形。 |

## SchemeAffineClosedBaseChangeSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffineClosedBaseChangeSections`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffineClosedBaseChangeSectionIso` | 実際の閉厚化のアフィン切断は、元の切断の拡大イデアルによる商。 |
| `schemeAffineClosedBaseChangeSectionIso_projection` | 元の切断から商へ射影する写像は、実際の閉厚化への引き戻し。 |
| `schemeAffineClosedBaseChangeSections_surjective` | 実際の閉厚化のアフィン切断への引き戻しは全射。 |
| `schemeAffineClosedBaseChangeSections_ker` | 実際の閉厚化へのアフィン切断の射の核は、元の切断での拡大イデアル。 |

## SchemeAffinePullbackSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffinePullbackSections`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffinePullbackSectionIso` | アフィン交叉上の実際の切断は、三つの切断環の canonical な pushout と同型。 |
| `schemeAffinePullbackSectionIso_inl` | pushout の左の写像は、実際の構造層の引き戻し。 |
| `schemeAffinePullbackSectionIso_inr` | pushout の右の写像も、実際の構造層の引き戻し。 |
| `schemeAffinePullbackIntersection_isAffineOpen` | 同じ実際の底変換の交叉はアフィン開である。 |

## SchemeAffinePullbackSectionsNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffinePullbackSectionsNaturality`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffinePullbackSectionIso_naturality` | 底変換の canonical なアフィン切断の比較は、開集合を狭める制限に自然。 |

## SchemeAffineSectionModule

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAffineSectionModule`

| 宣言 | 主張 |
| --- | --- |
| `schemeAffineSectionAlgebra_scalar` | 構造射で定める局所のスカラーは、大域スカラーを制限した切断。 |
| `schemeAffineSectionModuleEquiv` | 実際の構造層の係数加群と、構造射で束ねた切断環は同じ加群。 |

## SchemeCechPreimage

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechPreimage`

| 宣言 | 主張 |
| --- | --- |
| `schemeCechPreimageCoefficientIso` | 逆像被覆の有限交叉と、押し出した前層の係数図式の自然同型。 |
| `schemeCechPreimageComplexIso` | 逆像被覆と押し出した前層の Čech 複体の自然な同型。 |
| `schemeCechPreimageRefinement_naturality` | 逆像被覆の比較は、細分の制限と可換。 |
| `schemeCechPullbackMap` | スキームの射に沿う係数の射から、逆像被覆への Čech の射を作る。 |
| `schemeCechPullbackMap_refinement` | 逆像被覆への Čech の射は、細分の制限と可換。 |
| `schemeCechPullback_homology_refinement` | 逆像被覆への Čech H の射は、細分の H の射と可換。 |

## SchemeCechPullbackComparison

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechPullbackComparison`

| 宣言 | 主張 |
| --- | --- |
| `schemeCechPullback_comparison_naturality` | 共通細分の Čech H の比較は、実際のスキームの引き戻しに自然。 |

## SchemeCommonAffineCechHomology

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechHomology`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCommonAffineCechHomologyIso` | 二つの有限アフィン被覆による、準連接層の Čech H の比較同型。 |

## SchemeCommonAffineCechIndependence

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechIndependence`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCechComparison_commonRefinement_independent` | 実際の準連接係数の二つの共通アフィン細分による Čech H の比較は同じ。 |

## SchemeCommonAffineCechScalarHomology

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarHomology`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCommonAffineCechScalarHomologyIso` | 二つの有限アフィン被覆による、準連接層の Čech H の比較同型。 |

## SchemeCommonAffineCechScalarIndependence

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarIndependence`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCechScalarComparison_commonRefinement_independent` | 実際の準連接係数の二つの共通アフィン細分による Čech H の比較は同じ。 |

## SchemeCommonAffineCover

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCover`

| 宣言 | 主張 |
| --- | --- |
| `schemeCommonOpenCover` | 二つの開被覆の交叉による共通細分。 |
| `schemeCommonOpenCover_iSup` | 二つの被覆の交叉も全空間を被覆する。 |
| `schemeCommonOpenCover_le_left` | 共通細分から最初の被覆への包含。 |
| `schemeCommonOpenCover_le_right` | 共通細分から二つ目の被覆への包含。 |
| `schemeCommonOpenCover_isAffineOpen` | アフィン対角のスキームでは、共通細分もアフィン開被覆。 |
| `cechOpenIntersection_isAffineOpen` | アフィン対角のスキームのアフィン開の非空有限交叉はアフィン。 |

## SchemeFiniteCommonCover

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeFiniteCommonCover`

| 宣言 | 主張 |
| --- | --- |
| `schemeFiniteCommonOpenCover` | Fin で添字付けした、有限の共通開被覆。 |
| `schemeFiniteCommonCoverLeft` | 有限の共通被覆から第一の被覆への添字。 |
| `schemeFiniteCommonCoverRight` | 有限の共通被覆から第二の被覆への添字。 |
| `schemeFiniteCommonOpenCover_iSup` | 有限共通被覆の全空間の被覆性。 |
| `schemeFiniteCommonOpenCover_le_left` | 有限共通被覆から第一の被覆への包含。 |
| `schemeFiniteCommonOpenCover_le_right` | 有限共通被覆から第二の被覆への包含。 |
| `schemeFiniteCommonOpenCover_isAffineOpen` | アフィン対角の下で、有限共通被覆の各開集合はアフィン。 |

## SchemeFinitePrincipalRefinement

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeFinitePrincipalRefinement`

| 宣言 | 主張 |
| --- | --- |
| `schemeFinitePrincipalRefinement` | アフィン開集合の任意の開被覆は、単位イデアルを生成する有限標準開被覆で細分できる。 |

## SchemeModuleAffineCech

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeModuleAffineCech`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCechPresheaf` | 構造層加群の切断を、大域の係数環上の前層として扱う。 |
| `schemeModuleAffineCechCoefficientEquiv` | アフィン開埋め込みの座標の切断と、元のスキームの切断の加法群の同型。 |
| `schemeModuleAffineCechCoefficientEquiv_naturality` | アフィン座標との加法的比較は、交叉を狭める制限に自然。 |
| `schemeModuleStandardOpenCech_exact` | アフィン開集合の標準開被覆上の、準連接層の増大 Čech 完全性。 |
| `schemeModuleStandardOpenCech_zero_injective` | アフィン開集合の標準開被覆における、準連接層の増大項の単射性。 |

## SchemeModuleAffineCoverCech

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeModuleAffineCoverCech`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleStandardOpenCech_acyclic` | アフィン標準開被覆の完全性を、増大項の単射性とともにまとめる。 |
| `schemeModuleStandardOpenCech_restrict` | アフィン標準開被覆の完全性は、小さいアフィン開への制限でも成り立つ。 |
| `schemeModuleAffineCoverCech_acyclic` | アフィン開集合をちょうど被覆するアフィン開被覆の増大 Čech 完全性。 |
| `schemeModuleAffineOpenCech_acyclic` | アフィン開と各被覆開との交叉がアフィンで、その開を被覆すれば、増大 Čech は完全。 |

## SchemeModuleCechRefinement

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeModuleCechRefinement`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCechRefinement_homologyMap_isIso` | 準連接層のアフィン開被覆の細分は、各次数の Čech H の同型を誘導する。 |

## SchemeModuleCechScalarRefinement

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeModuleCechScalarRefinement`

| 宣言 | 主張 |
| --- | --- |
| `schemeModuleCechScalarRefinement_homologyMap_isIso` | 準連接層のアフィン被覆の細分比較は、任意の基底環の作用に制限しても同型。 |

## SchemeOpenCoverCechIntersections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeOpenCoverCechIntersections`

| 宣言 | 主張 |
| --- | --- |
| `cechOpenIntersection_scheme_preimage` | スキームの逆像は Čech の有限交叉を保つ。 |
| `cechOpenIntersection_scheme_image_preimage` | 開埋め込みの像による交叉の表示。空交叉では像全体を与える。 |

## SchemeScalarMorphism

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism`

| 宣言 | 主張 |
| --- | --- |
| `schemeScalarMorphism` | 大域スカラーが定める、Spec R への構造射。 |
| `schemeScalarHom` | Spec R への構造射から得られる、大域スカラー。 |
| `schemeScalarMorphism_appTop` | 構造射に移した大域スカラーを、Γ–Spec の三角恒等式で回収する。 |
| `schemeScalarHom_scalarMorphism` | 構造射を経由しても、大域スカラーの環準同型は変わらない。 |
| `schemeScalarHom_naturality` | 実際の構造射の可換な正方形から、切断の引き戻しの scalar の整合性を得る。 |

## SchemeScalarMorphismSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeScalarMorphismSections`

| 宣言 | 主張 |
| --- | --- |
| `schemeScalarMorphismSectionModuleEquiv` | 指定した大域スカラーと、それが定める構造射で束ねた切断代数の加群の同型。 |
| `schemeScalarMorphismSectionModuleEquiv_apply` | スカラーを指定した切断の比較は、元そのものを変えない。 |

## SchemeStructureAffineCechPullbackComparison

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureAffineCechPullbackComparison`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureAffineCechPullback_comparison_naturality` | アフィン射の実際の引き戻しは、共通アフィン細分による Čech H の比較と可換。 |

## SchemeStructureCech

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCech`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureModule` | 構造層を、それ自身の上の階数一の加群として扱う。 |
| `schemeStructureModuleQuasicoherent` | 構造層加群は準連接。 |
| `schemeStructureCechPresheaf` | 構造層の切断を大域切断の環上で扱う、実際の係数前層。 |
| `schemeStructureCechPresheaf_smul` | 構造層の切断の大域スカラー作用は、制限した切断の乗法。 |
| `schemeStructureCechRefinement_homologyMap_isIso` | 構造層のアフィン被覆の細分は、実際の Čech H の同型を誘導する。 |

## SchemeStructureCechBaseChangeCoefficient

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechBaseChangeCoefficient`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechBaseChangePullbackCoefficient` | 基底環の変わる構造層の引き戻し。スカラー制限の合成を明示する。 |
| `schemeStructureCechBaseChangeDiagramRestriction` | 実際の基底変更から得る、逆像被覆の係数図式への射。 |
| `schemeStructureCechBaseChangeDiagramMap` | 実際の切断の引き戻しをテンソル積から延長した、自然な係数の射。 |

## SchemeStructureCechBaseChangeIso

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechBaseChangeIso`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechBaseChangeSectionIso` | アフィン交叉の切断の同型を、逆像被覆の対応する交叉まで輸送する。 |
| `schemeStructureCechBaseChangeDiagramMap_app` | 自然なテンソル積の射のアフィン交叉での成分は、実際の切断の同型。 |
| `schemeStructureCechBaseChangeDiagramMap_isIso` | 非空アフィン交叉において、実際の係数の底変換の射は同型。 |
| `schemeStructureCechBaseChangeComplexIso` | 実際の底変換の切断の Čech 複体は、係数をテンソル積にした Čech 複体と同型。 |

## SchemeStructureCechComparisonNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechComparisonNaturality`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCommonAffineCechCoefficient_naturality` | 二つのスカラー作用の間の実際の係数の射に対する、被覆比較の自然性。 |
| `schemeStructureCommonAffineCechFrobenius_naturality` | 実際の構造層の Frobenius は、共通アフィン細分による被覆比較と可換。 |

## SchemeStructureCechFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechFrobenius`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructurePrimeCast` | 基底の p = 0 は、空の開も含めすべての切断環へ移る。 |
| `schemeStructureCechFrobeniusCoefficient` | 構造層の切断の実際の Frobenius。基底のスカラー作用を p 乗でねじる。 |
| `schemeStructureCechFrobeniusCoefficient_apply` | 構造層の Frobenius の各開上の式は p 乗そのもの。 |

## SchemeStructureCechNativeTensor

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechNativeTensor`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechNativeTensorComplexIso` | 実際のアフィン被覆の逆像の Čech 複体と、元の Čech 複体のテンソル積の同型。 |
| `schemeStructureCechNativeTensorComplexIso_unit_apply` | 複体の比較は、1 と元の cochain の純テンソルを実際の切断の引き戻しへ送る。 |
| `schemeStructureCechNativeFlatBaseChangeIso` | 実際の底変換の構造層の Čech H と、flat なテンソル積の比較。 |

## SchemeStructureCechPullback

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullback`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechPullback_scalar` | 構造層の切断の引き戻しは、大域スカラーの引き戻しと整合する。 |
| `schemeStructureCechPullbackCoefficient` | 実際の構造層の引き戻しを、固定した基底環上の前層の射として扱う。 |
| `schemeStructureCechPullbackMap` | スキームの射の、構造層の Čech 複体上の実際の引き戻し。 |

## SchemeStructureCechPullbackComposition

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullbackComposition`

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechPullbackMap_eq_refined` | 同じ逆像被覆への恒等細分を合成しても、実際の引き戻しは変わらない。 |
| `schemeStructureCechRefinedPullbackMap_comp` | 同じ添字で細分した、構造層の実際の引き戻しはスキームの射の合成と可換。 |
| `schemeStructureCechPullbackScalar_comp` | 共通の元のスカラーを合成して引き戻すと、各段で引き戻したスカラーの合成になる。 |
| `schemeStructureCechPreimage_refinement` | 共通の射への可換な三角形は、逆像被覆の細分を与える。 |

## SchemeStructureCechRefinedPullback

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureCechRefinedPullback`

| 宣言 | 主張 |
| --- | --- |
| `schemeCechRefinedPullbackIntersection_le` | 逆像被覆の細分の有限交叉は、元の有限交叉の逆像に含まれる。 |
| `schemeStructureCechRefinedPullbackMap` | 逆像被覆への引き戻しと、さらに細分する写像の合成。 |
| `schemeStructureCechRefinedPullbackMap_apply` | 各タプルでの Čech の引き戻しは、実際の構造層の appLE そのもの。 |

## SemilinearCompatibleFamiliesMap

モジュール：`SerrePositivity.AlgebraicGeometry.SemilinearCompatibleFamiliesMap`

| 宣言 | 主張 |
| --- | --- |
| `compatibleSemilinearFamiliesMap` | 遷移と可換な半線形成分写像が誘導する、互換族の半線形写像。 |

## SurjectiveCoefficientQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.SurjectiveCoefficientQuotient`

| 宣言 | 主張 |
| --- | --- |
| `surjectiveCoefficientSubmodule` | 全射な係数変更では、小さい環の部分加群は大きい環でも閉じている。 |
| `surjectiveCoefficientSubmodule_restrictScalars` | 係数変更後の部分加群の制限は元の部分加群に一致する。 |
| `surjectiveCoefficientQuotientModule` | 元の商の型を保った、変更後の係数環上の加群構造。 |
| `surjectiveCoefficientQuotient_scalarTower` | 変更後の係数作用は、元の商の作用と両立する。 |
| `surjectiveCoefficientQuotientProjection` | 商への射影は変更後の係数環上でも線形。 |
| `surjectiveCoefficientQuotientProjection_apply` | 係数変更後の射影も、代表を同じ剰余類へ送る。 |

## TensorCoefficientAlgebraModule

モジュール：`SerrePositivity.AlgebraicGeometry.TensorCoefficientAlgebraModule`

| 宣言 | 主張 |
| --- | --- |
| `tensorRightCoefficient_smulCommClass` | 左因子の P 作用と右係数 B の作用は可換。 |
| `tensorRightCoefficientAlgebraModule` | 二つの可換な作用をまとめた、B⊗_R P 上の加群構造。 |
| `tensorRightCoefficientAlgebra_tmul_smul` | テンソル代数の純テンソルの作用は、元の二つの作用の合成。 |
| `tensorRightCoefficientAlgebra_tmul_tmul` | 二重の純テンソル上の作用は、元の P 作用と B の乗法で計算できる。 |
| `tensorRightCoefficientAlgebra_coefficient_scalarTower` | テンソル代数の作用は、右係数 B の作用を拡張する。 |
| `tensorRightCoefficientAlgebra_scalarTower` | テンソル代数の作用は、元の基底 R の作用と両立する。 |
| `tensorRightCoefficientAlgebraMap` | P 線形な写像は、係数変更後のテンソル代数上でも線形。 |

## TensorCoefficientRightModule

モジュール：`SerrePositivity.AlgebraicGeometry.TensorCoefficientRightModule`

| 宣言 | 主張 |
| --- | --- |
| `tensorRightCoefficientModule` | 右係数のテンソル積に、交換同型から B 加群構造を入れる。 |
| `tensorRightCoefficient_smul_tmul` | 係数 B の作用は、純テンソルの右因子への乗法で計算できる。 |
| `tensorRightCoefficient_scalarTower` | 右係数の B 作用は、元の R 作用と両立する。 |
| `tensorRightCoefficientComm` | テンソル積の交換同型は、右係数の B 加群構造について B 線形。 |
| `tensorRightCoefficientComm_tmul` | B 線形な交換同型の、純テンソル上の計算式。 |
| `tensorRightCoefficientMap` | 元の R 線形写像を、右係数テンソル積の B 線形写像として扱う。 |

