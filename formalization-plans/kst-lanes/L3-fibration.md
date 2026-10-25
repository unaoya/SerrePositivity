# K-F レーン：K-6 fibration 定理（L3）

> **v3（2026-10-24）**：K-F と K-7 は **K-B レーン**に統合。本ファイルが K-B の正本（K-6）、K-7 の引き継ぎは L10-nonconnective.md を併読。所有：KST/Fibration/、KST/NonConnective/。

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使う。**2026-10-25 採用の修正**：(d) は固定の厳密 dg 入力 S・ν:S→StableInfinity・連結 K:S→Sp に対し、K(D)→fib_Sp(K(C)→K(C/D)) が非負次数で π 同型となる連結版（連結スペクトラムでの引き戻し）とする。10-22 の「実 Sp fiber 四角形へ送る」は撤回。固定連結 K の Sp 引き戻し性は主張しない。既存の条件付き Sp fiber 定理は条件付きで保持する。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-24）
### 現在地
- 採用済みの連結版へ再開：K-6 d は元の実 fiber 比較の非負次数 π 同型。`DGConnectiveFiberComparison` は固定 dg 四角形と K 零角から同じ実 fiber 比較・全脚の二胞体・非負次数条件付き群同型を構成し、ν の Verdier 認証や Sp 引き戻し性を使わない。K-7 は同じ cone の K 零性から構造射・比較を作る。c4・c5 と K-7 d を継続する。
- `VerdierFullSLowerDeformation` は元の全下側二胞体から最大 path 二胞体への実三角柱・恒等縦辺・全関手同型を与える。`VerdierFullSLowerShortFaces` は二短辺の全時刻固定、`VerdierFullSLowerRelativeDeformation` は同じ内ホーンを固定した可縮 Kan 延長空間への実辺と元の全三角柱の回収を保持する。`VerdierFullSLowerMaximalFaces` は同じ変形の時刻一で二短辺を評価し、元の指定包含・商の同じ全一単体へ戻す。`VerdierFullSLowerKernelTriangle` は同じ最大 path 図式の全二胞体を元の実 Kan 包含・商の標準合成へ同定し、元の指定 Verdier 下側全二胞体から元の商核下側全二胞体への実関手同型を与える。`VerdierFullSLowerDeformationSource` は同じ全三角柱・最大化全二胞体・動く対角族を、元の Stable∞ 二胞体から同じ S• Kan 作用への像として厳密回収する。`VerdierLowerDeformationZeroHom` は同じ Stable∞ 三角柱の全次数・全時刻単体の長い Hom を元の零値部分空間へ持ち上げ、同じ全 Hom と全正反復 S• Kan 像を厳密回収する。`VerdierLowerDeformationFullSLongHom` はこの全族を元の全 S• 始域の native Kan Hom へ延長し、元の core 包含で全次数・全時刻の全 Hom を厳密回収する。二胞体では元の変形二胞体の全長 Hom 自身に一致する。`VerdierLowerDeformationFullSComposite` は指定した三頂点全体の合成 path と、その全 S• 作用の実合成端を全時刻で保持する。`VerdierLowerDeformationFullSNaturality` は同じ零値持ち上げと全 S• 延長の、全パラメータの単調な制限との厳密な可換性を与える。`VerdierFullSMovingSquarePrism` は元の動く対角を厳密に共有する上側全族に条件付きで、両全三角柱を回収する四角柱・四頂点の可逆性・同じ元の Verdier 四角形との全関手同型を構成する。終端を実全 S• 商核へ固定し、下側全二胞体の最大化との厳密一致を証明した。`verdierFullSMovingKernelSquareIso` は同じ実商核まで接続するが、上側全族自体は未供給で、存在入力を主経路へ追加しない。F1 正本への依頼：短辺・合成端を固定した全長 Hom のパラメータ付き族から、元の全二胞体の族を厳密回収する公開界面（コーディネータ経由）。
- `ZeroMiddleControlledTriangleInput` は元の全 S• Hom を core 包含で制限し、同じ二短辺の指定合成端を持つ実 fiber の点を構成する。元の指定 core 二胞体の全長 Hom と厳密に一致し、元の合成 path と仕様の全体 path の等号も回収する。`ZeroMiddleFixedHornComparison` は元の三面を固定する実充填空間の可縮 Kan 性・元の既存充填の指定点・構成済みの制御充填との fiber 内の同型と面 2 の上側全比較を供給する。制御充填の存在は主張しない。`VerdierLowerDeformationZeroHomFaces` は同じ零値長 Hom の持ち上げが全ての面・退化に厳密に自然であることを保持する。点ごとの零値条件を全三角柱の整合的な族へ接続するが、上側との同じ動く対角での貼り合わせは未証明。
- 上流 import 閉包は D の修正後に復旧確認済み。両所有集約を再ビルドして成功。K-6 c4 の全四角形比較と c5 の商実現比較を進める。
- 工程 (a) 完了。K-5 の実核条件から包含の本質像を同定し、cofiber-W と商の可逆性、二対三・pushout・pullback・ホモトピーに対する拡大安定性を証明。
- 工程 (b)：全相対 S_n・面退化・core 包含・商への射と核四角形を構成。元の全 Ar 評価・S 後合成の完全性と全成分の零対象検出を証明。
  同じ実 cofiber による相対辺判定と、全 n の二対三・pushout・pullback・拡大安定性を証明。元の S_n(D) 包含は全写像空間で充満忠実で実核像に一致し、同じ cofiber の像条件を回収。W 辺・相対 cofiber 射影は trivial Kan、全正反復の加法性へ接続済み。
- 有限 W 列の初期頂点・連続 cofiber 比較は、零長で厳密同型、全長・全正反復で局所化同型。
  全単体的有限積比較は未主張。元の相対 S と W 列 core S の対角・定数列・実押し出しを保持。
- 元の核包含を実核への完全同値へ制限し、K-2 Segal 実現で元の核四角形を homotopy pullback と証明。
  relativeSFibrationFiberIso は実 fiber と core S(D) の局所化同型で、同じ射影は元の包含の実現射。
  quotientSFibrationFiberIsoOfComparison は条件付き。元の S• 商核四角形を構成し、同じ商実現比較の可逆性を入力すれば homotopy pullback。通常の全錐比較と任意の Kan 四角形の橋渡しにより、同じ Ex∞ coherent 四角形は native な ∞ 引き戻し。元の四頂点・四辺を同じ Ex∞ Kan 値と元の射の coherent な一単体として回収し、同じ相対 S 核の角の終対象性も証明。一回の反復実現への全 Hom の座標読み替えは元の豊穣関手と等しい。指定 Verdier 四角形の包含・商辺と三頂点は厳密一致し、残る角は実終対象間の同型。零値完全関手の実 Kan Hom 部分空間は可縮で、任意の指定部分族を厳密に保つ延長と元の全正反復 S の全 Hom への図式比較を構成。零圏から・零圏への全 Hom の可縮性により、指定 Verdier 四角形は元の StableInfinity の零角付き四角形となる。指定 Verdier 上側二単体の全長 Hom を元の零値部分複体へ読み出し、同じ全長 Hom と元の全正反復 S 像で厳密照合。元の上下二単体の共有対角 δ₁ は厳密一致。下側の全長 Hom も零値族へ読み出し、全正反復 S 像で厳密回収。共有対角の同じ両端で読んだ両二胞体族は直接 path の像が同じ対角頂点で、全関手同型を構成。可縮な零値 Hom 空間への制限の実 fiber により、対角上の制限が元の恒等一単体となる全比較辺を構成。評価円柱は全時刻で共有対角を固定し、全正反復 S の全 Hom 作用後も固定条件を保つ。比較円柱の合成 path 側の実辺を評価し、元の指定両端で下側合成が包含・商の合成そのものと証明。元の上側零合成との全自然同値を、同じ比較円柱から回収。合成 path 上の全時刻評価も厳密一致。一つの零自己関手→恒等の実自然変換を全 S_n の全 Hom 作用へ送り、全ての面・退化に自然な実円柱を構成。核上の包含そのものを順射とする全単体的同型で相対核へ戻し、同じパラメータの対角円柱と一点への具体的収縮ホモトピーを構成。元の商比較へ全単体的円柱を送り、元の core S 包含・商の実合成に対する具体的零化ホモトピーを構成。零値後合成の全族を元の Kan Hom へ読み戻し、その全 S_n 作用が同じ商核円柱の包含後の像と厳密一致。指定下側二胞体の直接 path→合成 path 族と、実合成端を全時刻で固定した全比較辺・円柱を構成し、全正反復 S の全 Hom 作用後も固定。元の指定両端への対象座標の輸送後も同じ全収縮族を異種等号で照合。元の core 包含で制限した全単体的零化円柱の各段は、K-S• の同じ全 Kan Hom 族による core S_n 作用と厳密一致し、対角は元の零化円柱を回収。全図式 Hom の射影を用いて全入力族を全単体的円柱へ送り、対角が元の豊穣対角作用と厳密一致すると証明。全有限反復 core S• へ接続し、一回の native 図式と元の core S• の恒等成分の同型を介して、元の商核零化円柱が同じ実合成の全豊穣実現族の評価と厳密一致。core 制限・対角・Ex∞ を通る指定二胞体比較と全四角形比較は未証明。商実現比較の可逆性は未証明で、無条件 K-6(b) は未完。
- Ore・分母輸送・固定分数・可変終点 coslice の既存構成は保持し、新設は Sp 正本へ依頼する。
  全 span 族の評価・全単体被覆・W 反転・降下・同じ分数比較の回収を構成。一般比較同値・span 普遍性は未証明。
  tamme* の lax 専用仮定を一般 Verdier 商へ流用しない。H⁰ の普遍性で全写像空間を代用しない。
- 元の scaffold 埋め込み・二脚・相対三角・係数点と、native 表現の pointedMap の指定点を保持。
  豊穣実現・curry・転置・反転・strict transport の同じ指定成分を、元の点の作用と照合済み。
- 切断の底変換・under 実現・初頂点制限・反転・共通 Hom 解像の指定成分を、元の実図式と照合。
  同じ strict 持ち上げの恒等射評価は、第一射影により元の単体切断の初頂点を厳密に回収する。
- F1 の exists_leftCoherentTransport_directComparison は底上の同値だけで指定 scaffold 三角形を残さず、元の係数点との一致は推論しない。
- scaffoldNerveRepresentationIso は指定 scaffold 三角形を保持し、係数点を元の恒等射評価の同じ fiber 点の
  pointedMap 像へ送ると証明。scaffoldStraighteningRepresentationIso はその指定制限比較を Sp の前合成充満忠実性で戻す。
  新主経路の scaffoldPointedReconstruction は実射・射影・前合成同値・fiber 点計算を構成。
- 指定した全制限比較と降下後の同じ成分を厳密に照合。native 表現の制限点は第一射影した元の同じ fiber 点の像。
  元の単体切断の係数点を、新復元射による同じ初頂点 fiber 点の実像へ接続済み。
- 左右の底変換比較の端点等式と切断の全空間値を保持。初頂点 fiber 点は既存の実底変換像と厳密一致。
  任意の実 fiber 点を零単体切断で回収し、元の実図式の同じ指定成分に対する復元像の底変換自然性を証明。
- 新分類比較は、strict・cocartesian 切断の元の係数点を、実底変換した同じ fiber 点の新復元像へ送る。
  既存の coslice 点族は恒等錐で同じ実点を回収。新復元恒等点からの延長は新復元射と全写像空間で自然同型で、前合成同値。
- 既存の分数分類を新比較へ接続。元の恒等 span の strict Kan 比較像は、既存の固定分数評価を経由して
  同じ scaffold 復元恒等点へ送られる。元の coslice 合成は新復元射と全相対写像空間で自然同型で、無条件に前合成同値。
  元の比較に、商上の実右逆と全相対写像空間内の余単位を構成。同じ右逆を全 fiber へ制限し、余単位と本質的全射性を証明。
  同じ比較二胞体の成分の点の射の全射性を、元の strict Kan 比較成分の実本質的全射性へ移送。
  Sp 正本の `verdierFractionMappingComparison_isFullyFaithful`（d08ea0c53）を代入し、元の全 strict Kan 成分・全終点の分数比較の同値と元の商上の比較自体の可逆性を `WeakQuotientMappingEquivalence` で接続した。商実現比較は未完。
- 工程 (c)：中央・右 π の k 未満の消滅の下で、左 fiber の同じ消滅 ⇔ πₖ 射影全射を K-5 の実長完全列で証明。
  中央 πⱼ=0 なら右 πⱼ₊₁／射影像 ≃ 左 fiber πⱼ。代表元は元の接続射。零次余核の障害を明示。
- 固定 dg K の実頂点・実辺の整数 π 作用を同じ BF 射と可換に比較し、πⱼ 全射性の同値を証明。
  元の Verdier 商の三角圏 K₀ 作用は全射で、同じ射の代数的零次余核は零群。
  固定 ν の同じ dg 辺の K₀ 作用を実完全関手と照合し、ν 像が Verdier 列となる厳密 dg 列の全射性を証明。
  既存の厳密 dg K₀ 自然比較と固定頂点・辺の同定で、ν 像が Verdier となる同じ固定 K 商辺の実 π₀ 全射性を証明。
  任意の相対 Verdier 四角形の元の右辺を同じ dg 射として回収し、ν 像の商辺と照合。元の K 右辺の実 π₀ 全射性を証明。
  同じ相対 K 右辺を持つ実 Sp fiber 四角形を構成し、元の BF fiber との群同型で全負整数群の消滅を証明。K(D) との同定は未証明。
  ν(P) が零なら全反復 S・境界商の一点射が局所化可逆で、正段の整数 π 検出により固定 K(P) は零。任意の元の相対 K 四角形の零角を保持する。
- 工程 (d) は採用済みの連結相対形：同じ厳密 dg 入力 S 上の ν:S→StableInfinity、連結 K:S→Sp。元の実 fiber 比較の非負次数 π 同型を証明する。以下の Sp 引き戻し検出は追加仮定に条件付きの既存成果として保持する。
  元の零角・右辺を保持した canonical fiber と K(D) からの実比較辺、全脚の合成三角形を構成。元の四角形の引き戻し性 ⇔ 同じ比較辺の可逆性を証明。
  比較先を同じ dg 右射の BF fiber に比較し、両端の負次数消滅を証明。元の比較の非負次数 π が全単射なら元の K 四角形は引き戻し。非負次数の条件は未証明。
  固定 K の非負次数 π と一段 S• 境界商の π を自然に比較。元の core S•・対角実現・境界商の全 Hom を ν 後合成と照合し、指定 VerdierDiagram の境界商四角形と固定 K の各正段四角形を全高次単体で同定。元の反復実現から境界商への商射は全 Hom に自然で、同じ Ex∞ 商射を成分とする全図式同型を構成。基点忘却後の全正段で同じ Sp 辺の可逆性を検出し、元の実 fiber 錐の極限性も証明。元の相対 K 四角形が引き戻し ⇔ ν 像の元の全正反復 S• 実現の Ex∞ 四角形が引き戻し、まで証明。後者の無条件な引き戻し性は未証明。
- 工程 (e)：N の冪等完備化の普遍性・安定性・完全性と BGT §9 の入力境界を本文に整理。K-7 本体は別工程。
- Fibration 集約・専用監査は強化再構成命題の全族共有対角の厳密回収まで成功（660 モジュール・4413 宣言、標準三公理のみ、宣言型の ModelCategory 検査を含む）。K-6 c1〜c3 完了。全四角形比較と商実現比較は未証明。
### 残り（依存順）
1. 商実現比較を証明し、無条件の連結版 fibration 定理へ接続する（Waldhausen 1.6.4、BGT §7、40–80時間）。
2. 証明済みの任意の相対 Verdier 四角形の実 π₀ cofinality・fiber 連結性を、β3 の具体提示へ照合する（BGT §7–8、4–8時間）。
3. 証明済みの固定 K の相対零保存と元の四角形を保持し、K(D)→fib_Sp(K(C)→K(C/D)) の非負次数 π 同型へ接続する（BGT §7–8、16–32時間）。
4. 固定 dg 界面との接続後に、完備化と BGT §9 の非連結化への実入力を確定する（8–16時間、K-7 本体は別）。
### 主要宣言（共通接頭辞 SerrePositivity.KST.Fibration）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- verdierSStageKernelEquivalence_inclusion、verdierSPostcomp_fullyFaithful、verdierSPostcomp_kernel、relativeSConstruction_mem_edge_iff_cofiber_image。
- weakStringConstantPostSquare_homotopyPullback、relativeSKernelRealizationSquare_homotopyPullback、relativeSFibrationFiberIso、quotientSFibrationFiberIsoOfComparison、quotientSKernelInfinitySquare_isPullback、quotientSKernelInfinitySquare_right、quotientSKernelInfinitySquare_bottom、quotientSKernelInfinitySquare_corner_isTerminal、stableCoreSingleKanEnrichedFunctor_eq、stableMultiSingleKan_edge、quotientSKernelInfinitySquare_right_eq_verdierSingle、quotientSKernelInfinitySquare_bottom_eq_verdierSingle、quotientSKernelCornerIso_verdierSingle、zeroStableHomSpace_isContractibleKan、zeroStableHomFamily_extend、zeroStableHomMultiFamilyIso、verdierDiagramZeroTriangle、stableHomZeroVertex_iff_of_edge、coherentTriangleLongHom、verdierUpperTriangleZeroHomLift_recovery、verdierUpperTriangleZeroHomLift_multi_recovery、verdierTriangle_sharedDiagonal、verdierLowerTriangleZeroHomLift_multi_recovery、verdierNullHomFamily_direct、verdierNullHomFamilyIso、contractibleTargetRestriction_trivialKanFibration、FixedRestrictionFunctorEdge、verdierNullHomRelativeComparison、verdierNullHomRelativeMultiComparison、verdierNullHomComparisonPrism_diagonal、verdierLowerTriangle_first_arrow、verdierLowerTriangle_last_arrow、verdierNullCompositeOriginalMap_lower、verdierNullCompositeIso、verdierNullHomComparisonPrism_composite、exInfinityCommSqInfinitySquare_isPullback、strictCoherentCone_isLimit_iff_of_transformation、fractionKanQuotientDiagram_classificationIso、weakQuotientCosliceComparison、weakQuotientCosliceUnit_identity。
- weakSpanKanMappingComparison_value_equivalence_iff、weakIdentityKanMappingComparisonUnitIso、leftStraighteningCandidate_classificationIso_pointHom、leftCocartesianKanClassificationIso_pointHom。
- dgKPiComparison、dgKPiComparison_naturality、dgKPiMap_surjective_iff、dgKNativeSBoundaryPiEquiv_naturality、dgKNativePiMap_bijective_iff_sBoundary、dgRelativeVerdierSBoundaryFixedKSquareIso、dgRelativeKPositiveSquare_isPullback_iff、spectrumFiberSquare_evaluation_isPullback、spectrumEdge_isInvertible_of_positive_evaluation、dgRelativeK_isPullback_iff_sBoundary、stableBoundaryQuotientKanIso、verdierMultiBoundaryForget_isPullback_iff、spectrumEdge_isInvertible_of_positive_spaceEvaluation、dgRelativeK_isPullback_iff_multiRealization。
- dgKInputK_preservesRelativeZero、dgRelativeK_zero_corner、dgRelativeKZeroTriangle、dgRelativeFiberVertexComparison、dgRelativeK_isPullback_of_fiberComparison_pi_nonnegative。
- scaffoldNerveRepresentationIso_pointHom、scaffoldStraighteningRepresentationIso_pre、
  scaffoldPointedReconstruction、scaffoldPointedReconstruction_pointHom。
- scaffoldStraighteningGlobalChart_original_pointHom、firstVertexSectionFiberPoint_val、
  scaffoldPointedReconstruction_coefficient_pointHom。
- scaffoldBaseChangeCoefficientIso_pointHom、scaffoldBaseChangeCoefficientIso_heq_diagramValue、
  straighteningBaseChangeLeftChart_eq_firstVertex、straighteningBaseChangeRightChart_eq_firstVertex。
- baseChangeImageSectionFiberPoint_eq、vertexFiberZeroSection_firstVertex、
  scaffoldVertexBaseChangeIso_eq_diagramValue、scaffoldPointedReconstruction_baseChange_pointHom。
- scaffoldCocartesianBaseChangeClassificationIso_pointHom、coslicePointFamilyAt_recoveryIso、
  scaffoldCoslicePointExtension_reconstructionIso、scaffoldCoslicePointExtension_isPrecompositionEquivalence。
- weakIdentityNativeComparisonImage_scaffold_pointHom、weakCosliceComposite_scaffold_relativeIso、
  weakCosliceComposite_scaffold_functorIso、weakCosliceComposite_isPrecompositionEquivalence。
- verdierKZeroMap_surjective、verdierKZeroCofinalityObstruction_subsingleton、dgNuKZeroMap_surjective_of_verdier。
- dgKPiZeroMap_surjective_of_verdier、dgKBFHomotopyFiber_negative_subsingleton_of_verdier、
  dgKInputFiberSquare、dgRelativePiZeroMap_surjective、dgRelativeFiberSquare_negative_subsingleton。
- weakCosliceComparisonFiber_isEssentiallySurjective、weakSpanKanMappingComparison_value_isEssentiallySurjective、
  weakQuotientMappingComparison_isIso_of_fraction_fullyFaithful。
- relabelEnrichedObjects_uncurry、coreSingleSimplicialIso_diagonal_hom、coreSingleRealizationFamily_coordinates、quotientSKernelNullCylinder_coreRealization、stableCoreSingleKanFamily_coordinates、quotientSKernelNullCylinder_exInfinity、quotientSKernelNullCylinder_coreKan、verdierNullContractionCoreKanEvaluation_original_heq。
- relativeSKernelContractionCylinder、relativeSKernelDiagonalContraction、quotientSKernelNullHomotopy、quotientSKernelContractionImage_fullS、quotientSKernelNullNatTrans_app、quotientSKernelNullNatTrans_diagonal、stableMultiCoreFamilyCylinder_diagonal、quotientSKernelNullCylinder_native、verdierNullContractionComparison、verdierNullContractionFamily_original_heq。
- relativeSectionBaseChangeComponentIso_pointHom、relativeSectionBaseChangeComponentIso_heq_transportMap、
  leftStraighteningSectionJointDiagram_baseChangeIso_pre、leftStraighteningSectionJointDiagram_baseChangeIso_vertex。
- fiberGroup_lowerBound_iff_projection_surjective、connectiveFiber_iff_projection_piZero_surjective、
  fiberCofinalityObstructionEquiv、piZeroCofinalityObstructionEquiv_mk。
### 依存と提供
- 読み取り専用：KST/SConstruction、KST/LocalizingInvariants、KST/Spectra、InfinityCategories/Derived。
- K-S• の固定 K-1/K-2 は L1 §6：加法性、MultiRealizationFunctorIso の正反復、RelativeCofiberLeftFiber、
  RelativeFiberEquivalence と Quillen A。任意 W への制限・底変換・元の射影の照合は K-F が証明する。
- 相対 (d) の固定三点は K-S• の DGKFixedInterface・DGKFixedSConstruction を読み取り専用で使う。固定 ν・K の頂点・辺、厳密 dg の K₀ 自然比較・負次数消滅は提供済み。
- 商・分数・局所化は Sp 正本。一般分数比較の充満忠実性は Sp 正本から供給され、元の商上比較へ代入済み。厚い β3 列の実核接続・有限線型図式の局所化も依頼済み。
- Sp の IsStable は使わない。実 fiber 列・整数長完全列・π 同値検出を使う。提供先は K-7 と K-基盤 2。
### K-B-S：Sp-6 s4 への空間値全族単位（供給完了）
- 元の `markedSpanFamily` と同じ `weakSpanKanQuotientDiagram` を保持する。一般 Verdier 分数比較の充満忠実性は Sp 正本が消費・公開し、K-B は元の商上比較の可逆性へ代入済み。K-6 c5 の商実現比較自体は未完。

| 条件 | 同じ実全族に対する公開名 |
| --- | --- |
| 実全族写像 | `weakSpanKanQuotientFamilyMap`：元の marked span 全族から同じ商図式の小さい unstraightening への実射。 |
| 底 q の厳密保持 | `weakSpanKanQuotientFamilyMap_projection`。 |
| 元の各固定 fiber の実制限 | `weakSpanKanQuotientFamilyFixedFiber`・`weakSpanKanQuotientFamilyFixedFiber_ι`：包含後は元の固定 span 全族包含≫同じ実全族写像に厳密一致。 |
| 同じ全 fiber 単位の回収 | `weakSpanKanQuotientFamilyFixedFiber_recovery`：全ての元の終点 y で、元の固定 span 全体の Kan 置換単位を全関手同型で回収する。指定正規化は `weakSpanKanQuotientZeroValueComparison`、同じ射の同値性は `weakSpanKanQuotientZeroValueComparison_isQCatEquivalence`。 |
| 既存指定恒等点 | `weakSpanKanQuotientFamilyFixedFiber_identityIso`：元の `weakIdentityFixedSpan` の実像と既存 `weakIdentityQuotientFiberPoint` を同じ q(x) fiber 内で比較。補助点で代用しない。 |

- Ind-S (5) の正本 `CocartesianKanUnstraighteningUnit`・`CocartesianKanUnstraighteningUnitPoints` を読み取り専用で消費。同じ元の span 射影の単体圏引き戻し、`strictKanCompletion`、元の単位へ代入し、同じ存在証拠から実単位・厳密な底・全 fiber 回収を取り出す。`weakSpanKanUnstraighteningUnit_fixedFiberIso` は元の固定 span 座標で既存の全単位へ戻す。
- 相対初頂点降下は F1 正本 `relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization` を消費する。`weakSpanKanQuotientFamilyMapRestrictionIso` は同じ元の実単位を相対関手空間内で回収し、底を忘れた絶対同型で代用しない。追加の相対同値性や単位存在の入力は不要。
- `WeakSpanFixedSimplexCollapse` は元の固定 span の全単体の同時比較 prism と、元の span 座標・底の全時刻固定・両端の厳密回収を保持する。`weakSpanKanQuotientFamilyFixedFiberIso` は同じ商 fiber 内の相対比較と prism を元の初頂点局所化で戻す。
- `WeakSpanKanQuotientValueEdge`・`WeakSpanKanQuotientValueCancellation` は元の実 transport 辺と指定値比較辺を保持し、指定成分の逆関係を実三角形の Kan ホモトピーへ戻す。`weakSpanKanQuotientSimplexFiberValueRecovery` は同じ全 fiber 比較を元の小さい宇宙で正規化し、`weakSpanKanQuotientSimplexUnitFiber_recovery` は同じ実単位の商像から元の Kan 単位を回収する。
- `WeakSpanZeroSimplexFiber`・`WeakSpanKanQuotientZeroUnit` は同じ零単体の実 fiber 包含を元の全族持ち上げへ全単体で厳密照合する。`WeakIdentityQuotientValueCoordinates`・`WeakIdentityQuotientZeroValue` は元の恒等点の既存値比較と同じ零単体比較を全関手同型で照合し、同じ指定値比較の充満忠実性で実 fiber 内の恒等点比較を反映する。
- 既存の絶対降下・底厳密化と条件付き全族利用側は保持する。新しい供給は元の `IsVerdierSequence i q` の下で、単位や比較の存在入力を追加せず構成したもの。I・P・懸垂供給境界には変更なし。空間値に限定し、Cat∞ 値分類や一般局所化・商 API は追加しない。

### 採用済み設計：c4 の上側輸送で指定全長 Hom を保持する
- 現行 `zeroMiddleFullSKanTetrahedron` は三面を固定した内角充填を選び、始端上側はその未指定の面 2。`zeroMiddleFullSKanLongHom` は実構成済みだが、この選択された面の全長 Hom との厳密一致は充填条件に含まれない。短辺・共有対角の一致からこの一致を推論しない。
- 提案：F1 正本の、同じ短辺・合成端と指定全長 Hom を厳密回収するパラメータ付き二胞体構成を用いる。元の core 制限・指定 Verdier 二胞体を保つ中間対象輸送も同じ指定族へ照合し、既存の非指定充填の定理は保持する。必要な汎用構成はコーディネータ経由で Ind/F1 に依頼し、K-B にコピーしない。
- 制御した上側と既存の上側を比較する場合は、同じ元の三面を固定した充填空間内の比較を証明してから使う。`ZeroMiddleFixedHornFamilyComparison` は任意パラメータ族の同じ可縮 Kan fiber 内の比較を構成する。`ZeroMiddleFixedHornUpperBoundary` は同じ実相対ホモトピーを上側へ制限し、二短辺・共有対角を含む全境界の全時刻固定と、その同じホモトピーからの全族関手同型を回収する。F1・F1B 正本を消費し、再構成の存在は主張しない。指定族の実構成は未供給のまま証明目標とする。
- 利用側は `VerdierFullSMovingSquarePrism` に接続済み。終端を同じ全 S• 商核に固定した下側最大化の厳密一致と `verdierFullSMovingKernelSquareIso` まで検証済み。上側全族・全対角条件・縦辺の可逆性の実供給は未完で、c4 完了とは数えない。採用済み経路として続行する。汎用再構成と同じ三面を固定した充填空間内の比較は Ind-S (9) に依頼し、型をユーザー経由で中継する。
- `ZeroMiddleControlledFillerFamily` と `ZeroMiddleControlledPrismHomotopy` は、構成済みの同じ三面の充填族から、制御上側を始端・元の native 二胞体を終端とする実全族三角柱を構成する。共有対角を全時刻固定し、全辺の厳密回収から縦辺を元の同じ実可逆辺に照合する。同じホモトピーから全族関手同型を得る。制御充填の存在と指定全長 Hom の回収は主張せず、非指定充填も保持する。

### 未コミット
- 固定三面からの上側全境界回収と、同じ実列の第一行比較から固定 K 構造辺への接続を両集約へ接続済み。両専用監査成功。所有 Lean の未コミットなし。
### 既知の問題
- 一般分数比較の同値性と元の商上比較の可逆性は接続済み。有限線型図式の局所化、span 普遍性、商実現比較、厚い β3 列の Perf 核照合、相対連結版 K-6 は未完。
- 現在の条件付き fiber 同型や一般の群判定を、具体的 K の局所化性の証明とは数えない。
- D-9 の実小核と Sp-6 の固定零化構成子は K-B に接続済み。同じ実零角の Perf 零性は K-B で証明済み。固定 ν 上の Verdier 証拠と Perf 完備化・P 照合は別の条件。native Verdier 列だけから連結 K の Sp fiber 性を結論しない。
### 次の一手
- 全 Hom の対象座標読み替え、図式同型の対角と実現同型の逆射の一致、元の core S 対象上の商核円柱の全評価は接続済み。Ex∞ の全 Hom 作用と strength による同じ円柱像も接続済み。`verdierNullContractionCoreKanEvaluation` は、元の円柱像から指定下側二胞体の全 path 評価への二重パラメータ比較で、実合成端を全時刻固定する。始点は `verdierNullContractionCoreKanEvaluation_original_heq` で元の指定包含・商の円柱へ照合済み。内部 uncurry 後の全円柱の同じ可逆辺と実合成端上の恒等制限、上下二胞体の全評価の共有対角上の恒等制限も接続した。指定 Verdier 左辺から回収した同じ完全射で、相対 S 核から元の零角の core S• への実比較を構成し、左辺との厳密可換性・実現後と Ex∞ 後の厳密可換性・同じ比較の局所化可逆性・その実 coherent 辺の可逆性を接続した（`VerdierZeroCornerMap`）。元の零値関手の全族を全 S_n から core S_n へ持ち上げ、全ての面・退化に自然な図式 Hom の族へ束ねた。指定関手の実点では元の全 S• 射を厳密に回収し、零圏への指定射は既存の零角比較と一致する。元の商核上辺は同じ全 S• 零値作用で、元の全核円柱も同じ図式 Hom 族の全パラメータ評価と厳密一致する（`QuotientSKernelZeroFunctorMap`）。指定上側合成は元の左辺・上辺の実合成と厳密に一致し、元の零角比較を上辺へ送った全 S• 射も同じ合成の零値作用を厳密に回収する。全 S• の始域を保つ Ex∞ Hom の全作用を構成し、元の上下二胞体の共有対角上恒等の比較と核円柱の実合成端上恒等の比較を、全円柱の実可逆辺・全関手同型へ接続した。次はこれらの相対比較を、元の商核四角形と指定 Verdier 四角形の全関手同型へ束ねる。全零値族の全 S• 延長は、core 包含後に元の K-S• の全段・全実現・全 Ex∞ Hom 作用へ厳密に戻る。元の相対核円柱の全 Ex∞ 像も、同じ核包含同型を通る全 S• 作用と厳密一致する。全 S• の実 Kan 頂点の終対象性と、指定左辺から作った零角比較自体の可逆性・元の左辺と上辺への厳密な因子分解を証明した（`VerdierFullSZeroCornerKanMap`）。元の native 正反復 Kan 座標へ戻した後も、同じ零角比較の可逆性・指定左辺と上辺の厳密な因子分解を保持する。全 S• の全零値族を native 座標へ送り、元の実 core 包含で同じ全 native Hom 作用を厳密回収した。上下二胞体の全長 Hom の同じ延長は、元の指定二胞体の native 像へ対象座標の異種等号で照合し、共有対角と合成 path の元の実点を保持する。実比較辺の native 像と全円柱の固定部分・全関手同型、指定両端へ戻した同じ合成点と元の商核上辺も接続済み（`VerdierFullSNativeLongHom`、`VerdierFullSNativeComparison`、`VerdierFullSNativeCompositeCoordinates`）。`ZeroMiddleFullSKanTriangle` と `ZeroMiddleFullSKanComposite` は元の零中間二胞体に対し、実 core 包含 f、元の第一短辺の全 S• 比較 e（可逆）、元の第二短辺 r、第一短辺=f≫e、合成端=e≫r、元の native 二胞体の全長 Hom へ厳密に戻る全 S• 族を供給する。指定上側 Verdier 二胞体への適用は `ZeroMiddleVerdierCoordinates` で元の零角比較・指定合成端・同じ native 長 Hom へ照合済み。公開 `horn₃₂` の貼合せと `triangleMiddlePrism` に特殊化し、元の全二胞体を終端で厳密回収し対角を全時刻固定する実三角柱を構成した（`ZeroMiddleFullSKanHorn`・`ZeroMiddleFullSKanPrism`）。始端の第一短辺は同じ core 包含で、二つの側面は同じ厳密合成二胞体へ厳密に戻る。両端の縦辺は恒等、中間は同じ可逆比較 e の全一単体と一致し、元の三角柱の辺そのものの可逆性・全関手同型まで接続した（`ZeroMiddleFullSKanPrismIso`）。`VerdierFullSUpperPrism` は終端を元の指定四角形の native 上側全二胞体へ厳密照合する。一般中間対象輸送 API は新設していない。`VerdierFullSSquarePrism` はこの上側三角柱を元の下側二胞体を全時刻固定して貼り合わせ、指定した始端四角形から元の全 native Verdier 四角形への実四角柱を与える。上下二胞体の全制限は厳密に戻り、四頂点の縦辺の可逆性から指定全四角柱の辺そのものの可逆性・全関手同型・引き戻し性の両方向移送を得た（`VerdierFullSSquarePrismIso`）。`VerdierFullSTransportedKernelBoundary` は始端四角形の包含・商の全一単体と左下頂点を元の商核へ厳密照合する。`KanCommSqTriangles` と `QuotientSKernelTriangles` は元の商核の上下全二胞体を同じ四射の標準 coherent 合成二胞体へ厳密回収し、共有対角も元の包含・商の実合成の全一単体へ照合する。`QuotientSKernelFullSquare` は元の相対核の実同型で零角を同じ全 S• へ戻し、左辺・上辺を厳密回収する。`QuotientSKernelFullSquareIso` は同じ零角同型を cospan の通常同型と全錐変換に使い、元の全商核四角形から同じ全 S• 四角形への実関手同型と Space∞ 引き戻し性の両方向移送を構成する。指定 Verdier 側との上下二胞体・共有対角・核円柱の全比較は未完で、境界の一致だけでは代用しない。元の商射影の零段は無条件で局所化可逆と証明し、正の各段の同じ比較だけから実現比較を得る `relativeSQuotientRealization_localized_isIso_of_positive_stages` へ接続した。`QuotientSKernelPositiveStages` は正の各段の比較だけから、元の全 Ex∞ 商射の全写像空間の同値性と同じ coherent 核四角形の引き戻し性を得る条件付き利用側。正の段の入力は Sp 正本の供給待ちで、無条件の商実現比較は未証明。
- Sp 正本の分数比較の充満忠実性は供給済みで、`weakFractionMappingComparison_isQCatEquivalence`・`weakQuotientMappingComparison_isIso` へ代入済み。β3 の実核接続・有限線型図式の局所化と元の商実現比較を継続する。同種 API は新設しない。

### K-6 c の三段目（v3）
- [x] c1 `relabelEnrichedObjects` の全 Hom 座標読み替え。
- [x] c2 `coreSingleSimplicialIso` の対角と実現同型の逆射の照合。
- [x] c3 商核零化円柱の元の core S 実現対象への輸送。
- [ ] c4 Ex∞ 上で指定二胞体を保つ全四角形比較。
- [ ] c5 商実現比較と無条件の連結版への接続。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。

## 冪等完備化・K-7 への入力境界（工程 e）

原典：[BGT §9.1、定義 9.1・9.6](https://arxiv.org/pdf/1001.2282#page=57)。
FκA=(Indω A)κ と ΣκA=FκA/A の列、K(FκA) の消滅、完全列・κ-filtered 余極限の保存を使い、
非連結 K は colimₙ ΩⁿK(ΣκⁿA) で構成する。これらの構成・消滅・余極限の証明は K-7 側。

| 入力 | 検証した正本と K-F の境界 |
| --- | --- |
| 完備化前の商 | Sp の IsVerdierSequence・VerdierSequence。K-F の quotientSFibrationFiberIsoOfComparison は商実現比較の可逆性が未証明の条件付き界面。 |
| 完備化 | N の IsIdempotentCompletion は充満忠実性と retract 条件を保持。IsIdempotentCompletion.pre_isQCatEquivalence は全関手 ∞ 圏の普遍性。H⁰ では代用しない。 |
| 安定・完全性 | N の IsIdempotentCompletion.isStable・isExactFunctor、idem_isStable・idemYoneda_isExactFunctor を使う。元の Idem C は宇宙 u+1、idemYoneda の始域は ulift C。 |
| 零次 cofinality | 厳密 dg 入力の ν と K の指定比較へ接続する。完備化という条件だけでは π₀ 全射性を入力せず、実 K 比較で検査する。K-F の piZeroCofinalityObstructionEquiv は中央 π₋₁=0 の下で、元の射影の余核を左 fiber の π₋₁ と同定する。 |
| K-7 への提供 | 指定射影と点を保つ条件付き相対 S fiber 比較、零次障害・連結性判定。各 suspension 段階の実比較と構造写像の整合性が必要。非連結 K 自体とその局所化性は未構成。 |

### Ind-S (9)：指定全長 Hom の全族再構成の供給型（採用（06:29））
- (9)・(9b) はユーザー採用（06:29）、一括で Ind-S に発注済み。以下は F1 新規葉への仕様命題の型であり、主経路の新しい存在仮定ではない。`K` は任意の単体集合。二短辺 `f`・`g` も指定全族として固定し、全ホーン族 `a` はその標準 coherent 区間像を厳密に回収する。
- `c` は同じ全短辺族の元の豊穣合成。`L` は合成端を全入力で `c` に固定した全長 Hom 族の空間、`T` は同じ全ホーン `a` を固定した二胞体族の実延長空間。`encode`・`longHom` の厳密回収は全族を保持する。読出しは各指定入力点で元の全豊穣 Hom に一致する。
- K-B では元の全 S• Hom を core 包含で制限してから渡す。未制限の全 S• Hom は始域が異なる。末尾の比較は同じ三面 `b` を固定する実充填空間内で取り、制御充填を実際に構成してから既存充填と比較する。任意四面の可填性を境界一致だけから要求しない。
```lean
import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
import SerrePositivity.InfinityCategories.F1.Diagrams.CompositionTriangleFamily
import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
import SerrePositivity.InfinityCategories.Core.EquivalencePath
import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality
import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Supply specification only; no existence assumption in the main route.
def indS9ControlledTriangleFamilyRequest : Prop :=
  ∀ (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}),
    (horn₂₁.ι₀₁ ▷ K) ≫ a = (Δ[1] ◁ f) ≫
      intervalMappingUncurry (coherentHomIntervalComparison X Y) →
    (horn₂₁.ι₁₂ ▷ K) ≫ a = (Δ[1] ◁ g) ≫
      intervalMappingUncurry (coherentHomIntervalComparison Y Z) →
  let P := SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let p : P :=
    { I := Set.univ
      left := Set.mem_univ _
      right := Set.mem_univ _
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)
  let c := lift f g ≫ (HomotopyLimits.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  let L := vertexFiber ((ihom K).map
    (evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (functorVertex c)
  let T := vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u})
    (functorVertex a)
  ∃ (encode : L ⟶ T) (longHom : T ⟶ L),
    encode ≫ longHom = 𝟙 L ∧
    (∀ (t : T _⦋0⦌) (k : K _⦋0⦌),
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm t.val
      let s := SSet.yonedaEquiv ((functorVertexEquiv Δ[2] SpaceInfinity.{u}).symm
        ((curry Tt).app (Opposite.op ⦋0⦌) k))
      HEq (Lt.app (Opposite.op ⦋0⦌) k)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) ∧
    (∀ t : T _⦋0⦌,
      let direct : P :=
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm nt.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            intervalMappingUncurry (coherentHomIntervalComparison X Z)) ∧
    (∀ t : T _⦋0⦌, Nonempty (VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      let E := vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app SpaceInfinity.{u})
        (functorVertex b)
      IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (VertexIso old controlled))
```


### 採用経路：実商と Perf 完備化の K 比較を分ける（ユーザー採用）
- D-9 の `resolvedDGQuotientFlatKernel_isStableVerdierSequence` は完備化前の native 実商への列。固定 ν の `IsVerdierSequence` は Perf 完備化後の射に通常の `IsLocalization` を要求する。今回の実核・P・Morita 照合は、この追加認証を含まない。
- 採用：K-6 の完備化前の連結 fibration と、同じ実商の元の dg Yoneda 完備化の実 K 比較を分ける。K-7 の同じ cone について、後者の正次数 π 同型・零次 π 単射と構成済みの K 零性を使い、固定 K への実 fiber 比較の非負次数 π 同型を得る。K₀ 全射性・連結 K の Sp 引き戻し性は要求しない。
- 固定 S・ν・K と同じ I・採用済み供給境界は不変。既存の条件付き相対屋根と Sp fiber 定理も保持する。完備化前の商の局所化は D・Sp、K の cofinality は K-S• 正本とし、K-B に同種 API を重ねない。
- `DGKappaNativeKernelThick` は同じ実核の冪等完備性で D 正本の thick 核の retract 表示を戻し、完備化前の商の零化対象が元の実小核の本質像であることを証明する。`DGKappaNativeVerdier` は同じ包含・商辺を保つ Sp の完備化前の `IsVerdierSequence`・全四角形提示を供給する。固定 ν の完備化後の認証は使わない。`DGKappaRawSuspensionCompletion` は始域を移さない同じ実商の元の dg Yoneda を完備化として認証し、実 Perf 評価と SOA 比較で固定 K への実 BF 比較を保持する。正次数 π 同型・零次単射と一回 loop の非負次数同型は同じ `hcofinal` に条件付き。`DGKappaNativeKernelKComparison` は元の評価と同じ実供給 P による実核同値から、固定 K の始点を戻す。`DGKappaNativeFibration` はこの実列を元の相対 S• fiber 比較へ代入し、包含射影を厳密回収する。実商の fiber・Ex∞ 核四角形への接続は、既存の正段商比較 `hstage` に条件付きで、`DGKappaNativeSquareComparison` は同じ提示を動く共有対角の四角柱へ代入し、指定上側全族・全対角条件・縦辺可逆性と同じ正段比較に条件付きで、元の全 S• 四角形へ引き戻し性を移す。これらの実供給と無条件化・c4 の全二胞体比較は未完。
- 共終性はユーザーが K-S• へ依頼済み。供給までは下記命題を `hcofinal` という明示仮定引数に取って利用側を進め、供給後に同じ引数へ代入する。公理・証明済み成果として登録せず、新しい構造体の存在境界も加えない。`DGKappaSuspensionCofinality` は同じ実懸垂の元の Yoneda 安定模型射と実 K 射を保持する。
```lean
∀ (X Y : StableModel.{u}) (f : X ⟶ Y),
  F2.Idempotent.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective
      (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0)
```

### 採用済み：同じ未完備実列だけの有限 BF 四角形比較
- `kSpectrumMap` の射ごとの供給だけから、元の native 二胞体を持つ実 BF 四角形は回収しない。一般の BF 高次面整流は L1 のユーザー指示で中断済み。固定 `dgKInputK` を代入すると商が Perf 完備化後に戻る。
- ユーザー採用の有限 BF 比較は K-S•-S3 から実供給済み。同じ D-9 未完備実列の元二胞体を、新 BF 四対象・四辺上の実 Φ へ送り、各正段の全 S• 四角形比較と旧 K への指定整数群同型との可換性を保持する。`DGKappaSuppliedBF*` の主利用側は供給を直接消費し、hBF の存在引数を取らない。一般 StableInfinity の K 関手化は再開しない。
- [旧四対象固定型と範囲](archive/L3-raw-bf-square-proposal.md) の `DGKappaNativeBFBoundaryInput`・`DGKappaNativeBFSquare`・旧 hBF に条件付きの fiber・loop・固定 K 構造射の利用側は保持する。ただし実 S3 の BF 対象は旧四対象と厳密には等しくなく、旧 hBF の存在は主張しない。実供給側の構造辺から固定 K への戻しは末尾の二頂点比較の設計補足で扱う。c4・c5 と K-7 c5・d3 の印は未完。

### c5 の有限第一行比較の消費
- `RelativeFirstRow` は元の相対 gapped S_n を同じ商関手の相対第一行の厳密な逆像と認証し、第一行制限を底変換した trivial Kan fibration を構成する。`RelativeFirstRowQuotient` は元の商比較との厳密可換性と局所化可逆性の必要十分条件を保持する。
- `RelativeFirstRowRealization` は正段の残入力を `∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowQuotient q (n+1)))` に移し、同じ実現・Ex∞ 射・商核四角形へ条件付きで接続する。第一行の標準単体座標同型は同じ商後合成に厳密自然。同じ D-9 実列の `dgKappaNativeFullSSquare_isPullback_of_firstRows` と `dgKappaNativeBFFixedStructure_nonnegative_of_firstRows` まで接続。一般局所化から core 比較を推論せず、有限図式の Verdier 分数・core 比較は Sp 正本へユーザー経由で中継済み。
- `RelativeFirstRowSimplex` は同じ相対部分複体の標準単体座標への厳密な両側逆を供給する。`RelativeFirstRowSimplexQuotient` は元の商比較との厳密四角形を保持し、正段条件を `∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n))` と同値にする。この型から元の商実現への条件付き利用側まで接続済み。先の第一行型と同値な供給型として Sp へユーザー経由で補足した。新たな局所化存在入力は追加しない。

### Ind-S (9b)：同じ三面を保つ制御三単体の実構成（採用（06:29））
- ユーザー採用（06:29）。(9) と (9b) を一括で Ind-S に発注済み。元の二胞体・二つの厳密合成面・同じ長 Hom を保つ因子分解三単体族を使い、構成後に同じ固定三面 fiber 内で既存充填と比較する。[型・供給範囲](archive/L3-controlled-factorization-tetra-proposal.md)。(9b) は 77a33b4c9 の controlledFactorizationTetraFamily を ZeroMiddleNativeFactorization で代入済み。(9) は正規化後仕様の命題を明示引数に取り、存在は主張しない。全族 Hom 回収の既存要求は保持。今後の提案・依頼は要約と型のファイル・行を必ずユーザー経由で中継する。

### 採用済み供給命題の利用側

| 明示定理引数 | 型の正本（SerrePositivity/ 以下） | 供給元・回収内容 |
|---|---|---|
| `h9 : zeroMiddleControlledTriangleSupply` | KST/Fibration/ZeroMiddleReconstructionSupply.lean:32 | Ind-S (9)：指定二短辺・合成端・全族 encode/read の厳密切断・指定点の全 native Hom 回収・共有対角の全族厳密回収 |
| `h9b : zeroMiddleFactorizationTetraSupply` | KST/Fibration/ZeroMiddleReconstructionSupply.lean:97 | Ind-S (9b)：実供給済み（77a33b4c9）。ZeroMiddleNativeFactorization の zeroMiddleFactorizationTetraSupply_of_indS9b を代入 |

- (9) は採用済み命題の明示引数であり存在は主張しない。(9b) は実供給を代入する入口も接続。`ZeroMiddleFullSReconstruction`・`ZeroMiddleReconstructedFamily` は元の core 始域・全 S• 中間頂点と同じ短辺への再構成・実ホーン回収・同じ実入力への読戻しを保持する。`ZeroMiddleFactorizationTetra`・`ZeroMiddleFactorizationComparison` は同じ実因子分解族の三面・長 Hom を回収し、ホーン全体の回収後に既存充填との固定三面 fiber 内比較へ渡す。動く共有対角の貼り合わせと K-6 c4・c5、K-7 c5・d3 の無条件化は未完。

### 採用済み仕様補足：全族の共有対角の厳密回収
- ユーザー採用、Ind-S (9) へ中継済み。各 K 頂点の全 native Hom 回収から全時刻の式を推論せず、同じ encode/read の normalize(t)=encode(longHom(t)) に対する直接 path 評価の全族厳密回収式と、元 t との固定ホーン内の可逆比較を持つ強化命題を明示引数に取る。元 t 自身への厳密式は要求しない。`ZeroMiddleReconstructedDiagonal` は encode(ℓ) の正規化不変性から共有対角を Δ[1] ⊗ K 上で厳密回収する。`ZeroMiddleNormalizedFamily` は読出し保存・冪等性・固定ホーン内同型を介して元の族へ戻す。[型・範囲・採否の影響](archive/L3-whole-diagonal-recovery-proposal.md)。VerdierLowerReconstructionBoundary は元の実下側変形の二短辺と固定ホーン族の実入力点を厳密回収する。VerdierLowerNormalizedReconstruction は (9) に条件付きで、同じ実下側族との全関手同型・元の二短辺・正規化側の全対角・各入力点の全 native Hom 読出しと全時刻の実合成端を接続する。合成端は元の二つの実 Kan 射の厳密合成の定値族と一致する。ZeroMiddleControlledLongFamily は Ind の 218e5b449 を消費し、指定長 Hom 入力から全ホーン・各入力点の全 native Hom を保つ実上側族を (9) の仮定なしで構成する。全時刻対角の厳密回収とは区別する。VerdierNativeCompositeEdge は元の全長 Hom 比較の実合成端成分を core 制限と宇宙持ち上げへ送り、上側・下側の同じ実合成端間の可逆辺を保持する。本体へ新たな存在仮定は追加しない。

### K-S•-S3 の実供給と採用済み二頂点比較
- 実供給 `dgKappaNativeCoherentBFSquare` は新 BF 四対象を持ち、旧 K とは指定整数群同型を介して四辺の π 作用が可換。`DGKappaSuppliedBFSquare` は元の全 S• 比較と旧 K-cof の群作用を消費し、`DGKappaSuppliedBFZero`・`DGKappaSuppliedBFFiberComparison`・`DGKappaSuppliedBFOneStage` は hBF の存在仮定なしで零角・同じ実 fiber 比較・非負次数 π 比較へ接続する。`DGKappaSuppliedBFConeZero`・`DGKappaSuppliedBFConnectiveStructure` は同じ cone の零性から新 BF 上の実構造辺を作る。旧四対象を固定した hBF の条件付き定理は保持する。
- 二頂点比較は K-S• の 8b9bb13d2 で実供給済み。dgKappaNativeBFKernelQuotientVertexIso を代入し、DGKappaSuppliedBFFixedStructure で旧実核・実商の loop を経る固定 K 構造辺と非負次数 π 比較へ接続した。DGSuspensionSuppliedBFSequence は共終性・一回の S• fibration に条件付きで、二頂点比較の仮定なしに元の実余錐・連結比較・全整数末尾表示まで渡す。[型（28行）・範囲・採否の影響](archive/L3-supplied-bf-vertex-comparison.md)。二頂点比較は実スペクトル比較から構成し、整数群の抽象同型だけから Sp 同型を推論しない。
