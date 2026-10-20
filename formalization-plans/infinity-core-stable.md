# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-20）

### 現在地

- S1〜S7（D7）完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）、完全関手の CommShift・三角性を公開済み。
- D(S) の実零対象・全 fiber/cofiber・cospan の極限と span の余極限を構成。実境界の Q・A の二未知 cochain と微分式から coslice を充填し、cofiber の普遍性を証明済み。
- fiber/cofiber 比較の二脚・対角・ホモトピーと同値性、実 slice/coslice 比較辺を照合。同じ四角形の関手同型輸送から任意四角形の双カルテジアン判定と `derivedInfinityCategory_isStable` を証明済み。
- 通常の h D(S) と二切断の D3 を接続。実 suspension と複体シフトの自然同型・全整数 CommShift・実接続射の符号を照合し、標準 cofiber 列の D3 像を Mathlib の cone 三角形と同定済み。
- 全 distinguished triangle の標準 cofiber 表示から保存・反映・逆関手の三角性を証明。`derivedStableHomotopyEquivalenceIsTriangulated` は単位・余単位のシフト整合性も持つ。通常の導来圏から三角構造を引き戻して済ませていない。 D7 の入口：`Derived/StableTriangulatedEquivalence.lean`、`Derived/StableHomotopyTriangulated.lean`、`Derived/StandardCofiberTriangleImage.lean`。
- β3 の入口：`Derived/RoofPointBoundaryHorn.lean`・`Derived/DGOverBoundaryRefinedSimplex.lean`・`Derived/DGVerdierBoundaryOverFillers.lean`。商の実安定性・完全性・実分母の反転、全次数分数表示、境界固定の有限相対充填は完成。実 Verdier over 上の元・商屋根は右ファイブレーション、商側は左でもあり、fiber は pinched Hom と同型。固定商 Hom の実商屋根全空間への包含の right cofinality・弱同値、実屋根比較自体の π₀ 全射性、全係数細分 prism・商自然性・境界整合性と有限同時輸送まで証明済み。実屋根比較自体の弱同値性は未証明。有限頂点には `DGVerdierDiagramVertexCone` を供給済み。三次最後ホーンの二残差の原始元から一つの追加閉分母で有限辺族を同時充填し、全新 apex を同じ閉細分頂点へ同定した。各頂点に辺から独立な単一実脚を構成し、全辺錐の二脚をその同じ頂点脚と同定。`dgVerdierDiagramFiniteEdges_exists_vertexCone` は一つの頂点錐と指定有限辺族全ての合成二単体を供給する。実図式二単体と同じ頂点脚の三辺錐を六つの共通辺で照合して実 Λ[4,4] を組み立てた。`dgFourSimplexWithQ_rhs_top` は最上位 rhs を K+f34 Q へ分解し、実四次ホーンからの R・K は dR=0・dK=−f34 R を満たす。次数 −2 の実 Hom 後合成 cone の閉残差を構成し、その次数 −3 の原始元と Q（−2）・A（−3）の解の存在を双方向に接続した。解から実ホーン全体を延長し、全指定四面を保つ実分母 over 三単体へ回収する。`dgVerdierDiagramTriangleLastClosed_edge`・`_mem` は最後閉辺を元の実二単体の終頂点の実分母辺と厳密に同定する。`dgFourLastHornYonedaConeIso` は同じ指定残差を最後閉辺の Yoneda 加群 cone への Hom へ実鎖同型で移す。実分母性から導来有限 cell 性を供給し、`DGFourLastHornResidualRefinement` は追加実閉分母後の原始元と、その評価から Q・A の二微分式を供給する。`dgVerdierTriangleInitialDiagonal_edge` は全四次ホーンの対角辺 04 を同じ共通閉分母と同定する。`dgVerdierTrianglesResidualRefinement_nonempty` は同じ頂点錐の実二単体有限族に、一つの追加実閉分母と全残差原始元・Q・A を同時供給する。全新始対象と各輸送分母の実辺は厳密に共通。`dgSimplexInitialRefinement` は任意次数の実 dg 単体の閉始点細分を供給し、全微分方程式を保存する。順方向 Hom の線形写像の微分・合成・符号・和の保存から全 rhs の輸送を証明した。零始点の成分・rhs は同じ閉前合成、正始点では元の値と異種等号で一致する。`dgSimplexInitialRefinement_pullback_avoids_zero` は頂点零を避ける任意単射面を厳密に保存し、零面の保存も供給する。零を固定する任意順序単射の制限と閉始点細分の可換性、全正番号 coface との整合性を証明した。元の零面と細分した三面の六つの共通面を照合し、`dgFourLastHornSourceRefinement` を実 Λ[4,4] として構成した。全回収データが元の既知データの同じ始点細分と一致し、新 R・K は元の閉前合成、最後辺は元のままと証明した。`DGFourLastHornResidualRefinement.solution` は供給済みの Q・A を新ホーンの型付き二未知解へ移し、全指定四面を保つ実四単体を供給する。`dgFourLastHornFinite_exists_sourceRefinement_fillers`・`dgVerdierTriangles_exists_refinedFillers` は空族も含む有限族に一つの追加分母の実辺と全ホーンの実充填を同時供給し、元の零面を厳密に保存する。`dgVerdierDiagramRefinedOverThreeSimplex` は同じ充填から終点 x を固定した実 over 三単体を回収し、零面を元の図式二単体のまま、残る三面の四面体を元の指定閉始点細分のまま保つ。一次元で一般閉始点細分を閉射の合成と同定し、二つの正番号面との可換性から四面体の始点対角辺へ適用した。新 apex の構造辺を追加閉分母と元の共通分母の実合成へ同定し、同じ指定集合の実分母性を証明した。`fullSubcomplexSimplexApexLift` は零面と始頂点の所属から任意次元の同じ台を全部分複体へ持ち上げる。`dgVerdierDiagramRefinedThreeSimplex`・`DGVerdierFiniteTriangleRefinement.simplex` は空族も含む有限族の実分母 over 三単体を供給し、全零面を厳密に保存する。`DGVerdierFiniteTriangleRefinement.apex_eq` は全新始頂点を同じ一つの閉細分頂点へ厳密に同定する。`dgSimplexInitialRefinement_triangle` は一般二次細分と既存の三辺・三角 cochain による細分を厳密に同定する。`dgOverTwoSimplexInitialRefinement` は任意の実 over 二単体を同じ閉射で細分し、零面を保持、回収四面体を同じ一般閉始点細分へ同定する。新 apex の構造辺の合成表示と分母性から `dgVerdierTwoSimplexInitialRefinement` を実分母部分圏内に構成した。`dgVerdierDiagramRefinedThreeSimplex_face_cone`・`DGVerdierFiniteTriangleRefinement.simplex_face_cone` は全正番号面を同じ閉実辺で細分した元の指定辺錐へ厳密に同定する。細分は元の実二単体と追加閉実辺だけで決まり、`commonConeFace_eq` は元の辺錐が同じ二面が追加分母後にも厳密に同じことを証明する。`DGVerdierClosedVertexRefinement` は元の頂点錐と一つの追加閉分母だけから共通閉細分 apex・固定脚三角形・頂点ごとの単一実脚と新頂点錐を供給する。`dgOverTwoSimplexInitialRefinement_face_positive` は二つの脚面の回収三角形を、元の同じ脚面の閉始点細分へ同定する。`DGVerdierClosedVertexRefinement.edgeCone_face_positive` は元の任意の辺錐の同じ細分の二脚を、新頂点錐の同じ固定脚へ厳密に揃える。`edgeCompStruct` はその同じ実二単体から合成整合性を返す。`dgVerdierTriangles_exists_closedRefinedVertexCone` は有限二単体族の全実三単体の四面を、元の二単体と同じ新頂点脚の指定辺錐へ厳密に揃える。`dgVerdierDiagramFiniteTriangles_exists_vertexCone` は頂点・辺が有限な実図式の全辺錐と指定有限二単体族の三次整合性を同時供給する。`dgSimplexDataInitialRefinement_pullback_initial`・`dgSimplexInitialRefinement_pullback_initial` は零固定・正番号非零の一般順序写像に沿う可換性を、単射像・非単射零・潰れた二点の単位の三場合で証明する。`dgSimplexInitialRefinement_degeneracy_positive` は全次元の正番号基本退化との厳密可換性を供給する。over 辺の終点退化の四面体回収を照合し、`refine_degenerateLeg`・`identityEdgeCone_simplex` は元の標準単位辺錐の閉細分が新固定脚の同じ標準退化になることを証明する。`dgVerdierDiagramNormalizeEdgeCone` は任意の全辺錐を退化辺で標準単位錐を選ぶ族へ正規化し、同じ閉細分後もその単位選択を厳密に保つ。`dgVerdierDiagramFiniteTriangles_exists_unitalVertexCone` は有限頂点・辺の実図式の共通頂点錐・全辺錐・指定有限二単体族の全四面整合性に、この全退化辺の標準単位条件を同時供給する。`dgVerdierDegenerateTriangleCone_boundary` は退化図式二単体 σ0 e・σ1 e の標準実三単体を辺錐の σ1・σ2 として構成し、全四面を照合する。`dgVerdierDegenerateTriangleCone_overlap`・`_congr` は異なる退化表示の重なりを二重退化頂点へ戻し、単位条件と σσ 恒等式で標準値を厳密に一致させる。`dgVerdierNormalizeTriangleCone` は非退化の元の充填を保ちつつ退化の場合を標準値へ直し、全四面と二つの退化式を同時保存する。`DGVerdierDiagramTwoCone` は共通頂点錐・全辺錐・全二単体の実三単体を、全ての面・基本退化の厳密式で束ねる。`dgVerdierDiagramTwoCone_nonempty` は二次まで有限な実分母図式へその同じデータを供給する。`dgGeneralLastHornMissingResidual_closed` は全次元 n+2（n=0 も含む）の実最後外ホーンの欠面 rhs R の閉性を一般に証明する。欠面成分の零、次数 −n の Q の挿入による指定全面の保持、Q の微分式からの全真部分方程式と最上位 rhs の閉性を検証した。`DGGeneralLastHornSolution` は Q・A の二微分式を明示入力として受け、全指定面を厳密に保つ実 (n+2) 単体とホーン全体の延長を返す。対象族・欠面 Q・最上位 A は同じ入力のまま保持する。三次・四次の R と Q 挿入データを既存構成へ厳密に同定した。`dgLastHornLastCut_left/right/upper_card` は最後の左切断・右切断・符号指数を一般に同定する。`dgLastHornLastTerm_formula` は最後の寄与を削除成分の負と最後辺による欠面成分の後合成へ分解する。`dgGeneralLastHornQData_rhs_top` は左切断置換で変化する一寄与だけを計算し、全次元で最上位 rhs＝K＋最後辺∘Q を実際の符号付きで証明する。元の対象族の斉次 Hom を明示する `RhsWithQ`・`LastTermWithQ` で置換前後の加減算を型付けする。`dgGeneralLastHornSolutionOfCochains` はこの分解形の二微分式から同じ一般実充填を供給し、任意の解の A 微分も同じ形へ戻す。三次・四次の K と Q 後合成を既存の二未知微分式へ厳密に同定した。一般解の存在、dK と R の関係・残差 cone への接続、三次以上の退化を含む全高次有限共通錐、零次元の既存厳密屋根辺との一致、実比較の弱同値性、全 ∞ 関手圏の局所化普遍性・Verdier 列は未完。検証結果は保存コミットに記録する。 `dgGeneralLastHornKnown_leftCut`・`_rightCut`・`_erase` は全内部頂点の既知方程式を供給する。最後以外の Bianchi 寄与の消滅、最後左残差＝−R、右・削除残差＝0 と単位符号を照合し、`dgGeneralLastHornTopResidual_differential` により一般の dK＝−最後辺∘R を証明した。`dgGeneralLastHornFinalEdge_closed`・`dgGeneralLastHornPostcomposition` は実最後閉辺と元の Hom 後合成鎖写像を供給する。K のみを同じ端点の次数 −n へ線形輸送し、`dgGeneralLastHornConeResidual_closed` は R・K を持つ次数 −n の実 Hom cone 成分の閉性を全次元で証明する。 `dgComplexConePrimitive_fst_at`・`_snd_at` と `dgComplexConeElementMkAt_differential` は命題的な隣接次数を明示した二座標を供給する。`dgGeneralLastHornSolutionOfConePrimitive` は次数 −n−1 の cone 原始元から同じ実ホーンの型付き二未知解を回収し、逆の成分構成と微分も照合。`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary` は指定残差の境界性と解の存在を双方向に接続する。最後実閉辺の `dgGeneralLastHornYonedaConeIso` で同じ残差を Yoneda 加群 cone へ移し、閉性と境界性の同値を保つ。`DGGeneralLastHornResidualRefinement` とその存在定理は、最後実辺が指定分母なら、一つの追加実閉分母後の次数 −n−1 の原始元を供給する。cone 等式輸送・Yoneda 評価・前合成の二座標を照合し、`DGGeneralLastHornResidualRefinement.Q_differential`・`a_differential` は同じ追加閉分母による R と正規化 K の前合成を実際の Q・A の微分へ結ぶ。A の式は微分の終次数 −n で正規化されており、元の −n−1+1 への輸送は実細分ホーンへの接続時に戻す。 `dgSimplexDataInitialRefinement_equation` は任意の指定集合の方程式を保存する。`dgPartialSimplexHorn` は未知二集合以外の方程式を持つ全体データから、各面を実単体へ昇格して、次元の列挙なしで実ホーンを貼る。`dgGeneralLastHornSourceRefinement` は全次元の同じ閉始点細分ホーンを構成する。`dgGeneralLastHornSourceRefinement_knownData` は全指定面と未知二成分の零から、新ホーンの回収データ全体を元の同じ全体細分へ厳密に同定する。新始対象は q、正対象・最後辺は元のまま、R・K は同じ閉前合成と異種等号で照合。A 微分の次数を線形輸送で元へ戻し、`DGGeneralLastHornResidualRefinement.solution` と `dgGeneralLastHorn_exists_sourceRefinement_filler` は元の零面を厳密に保つ全実充填を供給する。`DGGeneralLastHornFiniteRefinement`・`dgGeneralLastHornFinite_exists_sourceRefinement_fillers` は空族も含み次元が異なってよい有限ホーン族に、一つの追加実閉分母と全充填を同時供給し、全新始対象・追加実辺を厳密に共通化する。`dgGeneralLastHornSourceRefinement_face_positive` は全正番号面を元の同じ指定面の閉始点細分へ厳密に同定する。 `roofPointSliceSimplex` は任意次元の over 単体を一つ上の実単体へ移し、全順序写像への自然性・終点固定・単射性を持つ。`roofPointExtend_coface` と `roofPointSliceSimplex_face` は全次数の面公式を次元列挙なしで供給する。`roofPointSliceSimplexOfFixed`・`roofPointSliceSimplexOfFace` は終点固定・指定零面から実 over 単体を回収し、全面と指定零面を照合する。`roofPointBoundaryHorn` は実境界写像を既存の `finalHornPointJoinIso` と `sliceOverUncurry` で実最後ホーンへ移し、全面・最後辺の厳密な公式を持つ。`dgGeneralLastHornFinalClosed_edge` は全次数の元の実ホーンの最後辺を回収閉射の実辺へ厳密に同定する。`dgVerdierBoundaryLastClosed_mem` は実分母部分圏への任意次元の境界に、その同じ最後閉辺の実分母性を供給する。`dgOverBoundaryRefinedSimplex` は一般の実細分ホーン充填を終点固定の over 単体へ戻し、元の境界零面を厳密に保ち、全正番号面を元の指定面の閉始点細分へ照合する。`dgVerdierBoundaryFinite_exists_refinedOverSimplexes` は共通始対象の任意次元の実分母境界有限族に、一つの追加実分母と全実 over 単体を同時供給する。新 apex の実分母性と、回収した全単体を同じ実分母部分圏へ上げる工程は未完。
- β3 の入口 F1B/Localization と archive/L4-derived-geometry-log.md §26〜27 を読了。商の nerve・包含・ε による恒等辺の零ホモトピー、指定収縮付き dg 関手の延長と射影の厳密一致を構成済み。
- 収縮対象に入る／出る Hom の全次数の閉元の原始元、Hom 複体の恒等写像の零ホモトピーと非輪状性を証明済み。始点側の次数符号も検証済み。
- 実際の pinched Hom の全境界から真部分集合の成分を回収し、削除右辺の閉性・最上位の原始元による置換で全境界を厳密に充填。零次元も含む `IsContractibleKan` を両方向で証明済み。
- 全面を選ぶ `SelectedFaceAssembly` を全境界へ接続。全真部分集合の方程式から Bianchi で最上位の右辺の閉性を得て、始点の収縮元で解き、全ての面を厳密に保って充填。一次元は零辺で直接充填した。
- 収縮元を持つ任意の dg 対象の実始対象性・零対象性、商包含の指定対象の実零化を公開済み。零対象性から収縮元を回収する逆向きも証明し、任意 dg 関手の `PreservesZeroVertices` を証明済み。
- 商包含の指定充満部分圏上の制限は零対象の定値関手と、関手 ∞ 圏の可逆二胞体で比較済み。任意形状の零図式の比較とその一意性も Stable に公開した。
- 指定対象を実零頂点へ送る dg 関手から、収縮データを回収して商からの dg 関手へ延長し、nerve の射影との厳密な一致を証明済み。全 ∞ 関手圏の普遍性は未証明。この段階の零化・延長は K-flat 性を要求しない。
- 全面の一致から最上位の右辺を同定する補題、全射 Hom 準同型に沿う境界・目標原始元の同時持ち上げを構成。全面を保つ実相対充填を、一次元・零次元も含めて証明済み。
- 対象上全射・全 Hom 上次数ごと全射な準同型の dg 関手の nerve は `TrivialKanFibration`。逆写像・可逆二胞体を持つ `QCatEquivalence` まで公開済み。
- 具体的な cell 分解の第一添加と余極限から増大の各次数全射性を証明し、増大の nerve の明示的 ∞ 圏同値に適用済み。一般部品は DifferentialGraded の公開 API を使用し、KST の import は追加していない。
- 平坦分解後の path 商の nerve、元の nerve からの関手、屋根の比較同型を構成。証明済み K-flat 条件を供給し、元の指定対象の零化・指定部分圏上の定値零関手との可逆二胞体も構成済み。
- 任意の固定 Hom 複体の鎖写像に沿う pinched 線形単体・実写像空間の射を構成。全射準同型なら、零次元を含む全相対境界充填から `TrivialKanFibration` とホモトピー同値を証明済み。
- 実際の `pinchedHomMap (dgNerve.map F)` を端点の等式による同型込みで線形写像と同定。対象上全射性を外した充満忠実性、Hom 複体同型の場合、dg 充満部分圏の包含への適用を公開済み。
- 任意対象族のラベル付き dg 充満像と評価への厳密な分解を構成。dg Yoneda の全 Hom 複体同型から、同一宇宙の代表加群の模型との明示的 ∞ 圏同値を証明済み。
- 自明 Kan fibration の始域・基底の両方向に実 fiber/cofiber を構成し、一般の ∞ 圏同値の安定性の同値不変性と完全性を証明。Yoneda 模型と具体的 cell 分解の安定性の比較、実関手・逆関手の完全性へ適用済み。
- 閉零圏の零対象の恒等成分の消滅から、dg nerve の実零頂点性を証明。全 Hom end を持つ `dgModuleNerve` と具体的零加群の実零対象性を公開済み。
- dg 加群の cone から出る Hom の全次数線形同値・行列微分・二残差からの原始元を構成。実辺・二単体・cone 四角形の四頂点・四辺・零角を照合済み。
- 実 coslice 境界の最初の余錐から対象・三辺・ホモトピーを回収し、全 Hom end の型付き残差を定義。Bianchi から全脚・二三角形の微分条件を証明し、Q・A の二未知成分と微分式へ接続済み。
- 始点・脚・最上位も含む左右の全方程式を証明し、全面と共通面を保って実単体を貼合せ。`dgModuleConeCocone_isColimit`・`dgModuleConeSquare_isPushout` を全 coslice 境界の直接充填で証明済み。
- 任意の辺を閉加群射へ戻し、入力辺を厳密に保つ `dgModuleCofiberSquare`・`dgModuleNerve_cofiber_exists` を構成済み。
- shifted cone の射影・零ホモトピー・実四角形を構成。fiber の逆 Hom 座標の微分 `(da, f a − db)` と実射影・零ホモトピーへの一致、二残差からの原始元を証明済み。
- 実 slice 境界の六残差から二未知成分を定義。左右の全方程式・全面・共通面を保って直接充填。`dgModuleFiberCone_isLimit`・`dgModuleFiberSquare_isPullback`・`dgModuleNerve_fiber_exists` が揃った。
- M→fiber(inr f) と双対の cone(projection f)→N の両実比較の代数的同値性を証明。両方向を比較三単体・join・curry により実 slice/coslice 辺へ昇格し、端点・射影・span/cospan を照合。`dgModuleConeSquare_isPullback`・`dgModuleFiberSquare_isPushout` により標準 cone/fiber 四角形は双方とも双カルテジアン。各辺の双カルテジアンな選択と、実四角形の関手同型による選択独立性から任意の零角の fiber iff cofiber と `dgModuleNerve_isStable` を証明済み。元の nerve の対象宇宙だけを上げた `dgYonedaModuleNerve` を安定な全加群 nerve への実写像として構成し、単体・頂点での作用と実写像空間での充満忠実性まで照合済み。K(D) の同型で閉じた三角的対象条件の零・全整数シフト・cone・fiber の閉性から、条件付き全加群の実 nerve の安定性を証明。表現可能対象の isoClosure による `IsDGPretriangulated` の下で `dgHomotopyRepresentableNerve_isStable` が完成。共通宇宙の元の dg 圏との明示的同値と両方向の完全性、元の nerve の ULift の安定性まで接続済み。元の小さい宇宙への安定性の降下も完成。実四角形の全写像の全単射、頂点・右辺・底辺の一致、引き戻し性・押し出し性の保存・反映から `fiberSquareOfULift`・`cofiberSquareOfULift` を構成。`isStable_of_ulift` と `dgNerve_isStable_of_pretriangulated` を公開した。

### 残り（依存順、時間は推定）

- β3：Drinfeld 商の dg nerve の局所化普遍性と Verdier 列。平坦分解後の商の安定性と商関手の完全性は完成。Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。残り 1〜2 万行、複数日。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b を読み取り専用で待つ。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`、`suspensionEquivalence`、`pretriangulated_ho`、`isTriangulated_ho`、`exactFunctor_isTriangulated`。
- `derivedInfinityCategory_hasZeroVertex`、`derivedInfinityCategory_fiber_exists`、`derivedInfinityCategory_cofiber_exists`。
- `cofiberBoundaryLiftQ`、`cofiberBoundaryLiftA`、`cofiberBoundaryLiftQ_differential`、`cofiberBoundaryLiftA_differential`。
- `standardCofiberCocone_isColimit`、`cofiberFiberLift_homotopyEquivalence`、`fiberCofiberDesc_homotopyEquivalence`。
- `derived_isPullbackSquare_iff_isPushoutSquare`、`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyBridge`、`derivedStableHomotopyEquivalence`、`derivedHomotopyHom_chainMap_surjective`。
- `derivedSuspensionShiftIso`、`derivedStableHomotopyEquivalenceCommShift`、`derivedStableHomotopyEquivalenceCommShift_one`。
- `semifreeCofiberConnectingToSuspension`、`derivedSemifreeCofiberConnecting_shift`、`derivedCofiberTriangle_mor₃`。
- `derivedStandardCofiberTriangleImageIso`、`derivedStandardCofiberTriangle_distinguished`。
- `derivedDistinguishedTriangle_standard_presentation`、`derivedStableHomotopyEquivalenceFunctorIsTriangulated`。
- `derivedStableHomotopyEquivalenceInverseCommShift`、`derivedStableHomotopyEquivalenceCommShiftCompatible`。
- `derivedStableHomotopyEquivalenceIsTriangulated`、`derivedStableHomotopyInverse_map_distinguished`。
- `dgNerve_contractingElement_id_homotopic_zero`、`dgNerve_contractingElement_id_eq_zeroEdge`。
- `dgQuotientNerve`、`dgQuotientNerveProjection`、`dgQuotientNerve_id_homotopic_zero`、`dgQuotientNerveExtension_projection`。
- `contractingTargetPrimitive_differential`、`contractingSourcePrimitive_differential`、`contractingTargetHomotopy`、`contractingSourceHomotopy`。
- `dgQuotientTargetPinchedHom_isContractibleKan`、`dgQuotientSourcePinchedHom_isContractibleKan`、`dgQuotientKilledVertex_isTerminal`。
- `dgNerve_isZeroVertex_iff_contractingElement`、`dgFunctorNerve_preservesZeroVertices`、`dgQuotientNerveProjection_kills`。
- `zeroDiagramFunctorIso`、`dgQuotientNullFunctorIsoZero`、`dgQuotient_exists_nerve_extension_of_zeroing`。
- `dgFunctor_relative_top_lift`、`dgFunctor_relative_simplex_lift`、`dgFunctor_relative_boundary_lift`。
- `dgNerve_map_trivialKanFibration_of_surjective_quasiIso`、`dgCellAugmentationNerve_trivialKanFibration`、`dgCellResolutionNerveEquivalence`。
- `resolvedDGQuotientNerve`、`resolvedDGQuotientFunctor`、`resolvedDGQuotientRoofIso`、`resolvedDGQuotient_localKFlat`。
- `pinchedHomChainMap_trivialKanFibration`、`pinchedHomChainMap_isSimplicialHomotopyEquivalence`、`dgFunctor_pinchedHomMap_eq`。
- `dgNerve_map_isFullyFaithful_of_surjective_quasiIso`、`dgNerve_map_isFullyFaithful_of_homIso`、`dgFullSubcategoryInclusionNerve_isFullyFaithful`。
- `dgYonedaRepresentableNerveEquivalence`、`representableDGYoneda_evaluation`、`IsQCatEquivalence.isStable_iff`、`isExactFunctor_of_isQCatEquivalence`。
- `dgYonedaRepresentableNerve_isStable_iff`、`dgCellResolutionNerve_isStable_iff`、`dgCellAugmentationNerve_isExactFunctor`。
- `dgNerve_isZeroVertex_of_closed_isZero`、`dgModuleNerveZeroVertex_isZero`、`dgModuleConeHomCoordinates`、`dgModuleConeDescElement_differential`。
- `dgModuleConeBoundaryRhsAB_differential`、`dgModuleConeBoundaryRhsAC_differential_zero`、`dgModuleConeBoundaryLiftQ_differential`、`dgModuleConeBoundaryLiftA_differential`。
- `dgModuleConeBoundaryLeftCandidate_suffix_equation`、`dgModuleConeBoundaryRightCandidate_suffix_equation`、`dgModuleConeBoundaryCandidate_common`。
- `dgModuleConeCocone_isColimit`、`dgModuleConeSquare_isPushout`、`dgModuleCofiberSquare`、`dgModuleNerve_cofiber_exists`。
- `dgModuleFiberCone_isLimit`、`dgModuleFiberSquare_isPullback`、`dgModuleFiberSquareOfMorphism`、`dgModuleNerve_fiber_exists`。
- `dgModuleCofiberFiberLift_isInvertible`、`dgModuleFiberCofiberDesc_isInvertible`、`dgModuleCofiberFiberComparisonSliceEdge_projection`、`dgModuleCofiberFiberComparisonSliceEdge_isInvertible`、`dgModuleConeSquare_isPullback`・`dgModuleFiberSquare_isPushout`・`dgModuleNerve_isStable`・`dgYonedaModuleNerve`・`dgYonedaModuleNerve_isFullyFaithful`・`dgModulePropertyNerve_isStable`・`dgHomotopyRepresentableNerve_isStable`・`dgRepleteYonedaNerveEquivalence`・`dgNerveULift_isStable_of_pretriangulated`・`uliftJoinIso`・`uliftSliceOverIso`・`uliftSliceUnderIso`。 `isTerminalVertex_iff_ulift`・`isInitialVertex_iff_ulift`・`hasZeroVertex_iff_ulift`・`isLimitCone_iff_ulift`・`isColimitCone_iff_ulift`・`hasLimit_iff_ulift`・`hasColimit_iff_ulift`。 `isPullbackSquare_iff_ulift`・`isPushoutSquare_iff_ulift`・`isStable_of_ulift`・`dgNerve_isStable_of_pretriangulated`。 `dgQuotient_isDGPretriangulated`・`dgQuotientNerve_isStable`・`isDGPretriangulated_of_quasiEquivalence`・`resolvedDGQuotientNerve_isStable`。 `dgModuleFunctorConeIso`・`dgModuleFunctorConeComparison_inl`・`dgModuleFunctorZeroIso`。 `DGModuleSquareData.postcomposeFunctorIso`・`DGModuleSquareData.map_square`・`dgModuleFunctorConeSquareModel_isPushout`・`dgModuleFunctorConeSquareModel_lower`・`dgModuleTriangleMiddleHomotopy_diagonal`。 `dgModuleFunctorConeSquare_isPushout`・`dgModuleFunctorNerve_preservesCofiber`・`dgModuleFunctorNerve_isExactFunctor`・`dgModuleExtensionRepresentableIso_naturality`。 `dgModuleExtensionYonedaCompositeIso`・`dgModulePropertyInclusion_isExactFunctor`・`dgPretriangulatedYoneda_reflectsPushoutSquare`・`isExactFunctor_of_ulift`・`dgPretriangulatedFunctor_isExactFunctor`・`dgQuotientNerveProjection_isExactFunctor`・`resolvedDGQuotientFunctor_isExactFunctor`。 `CofiberSquare.map`・`StableVertexClosure`・`inverts_stableVertexClosureEdges_iff_kills`・`dgVerdierEdges`・`resolvedDGQuotientFunctor_invertsVerdierEdges`・`resolvedDGQuotientLocalizationPrecomposition`。 `pinchedHomChainMap_quasiIso_equivalence`・`dgNerve_map_isFullyFaithful_of_quasiIso`・`dgQuasiEquivalenceNerveEquivalence`・`dgQuotient_pinchedHomMap_equivalence_into`・`dgQuotientRightLocalNerve_isFullyFaithful`。 `cofiberPushoutComparisonIso`・`StableVertexClosure.extension`・`cofiberStableEdges_twoOfThree`・`dgVerdierEdges_twoOfThree`・`dgVerdierEdges_pushout_iff`・`dgVerdierEdges_pullback_iff`。 `stableHoClosure_le_iff`・`cofiberStableEdges_iff_trW`・`cofiberStableEdges_commonDenominator`・`cofiberStableEdges_equalizeFinite`・`dgVerdierEdges_commonDenominator`・`dgVerdierEdges_equalizeFinite`。 `dgModule_stableVertexClosure_iff_finiteCell`・`dgModule_cofiberEdges_iff_trW`・`stableVertexClosure_image_iff`・`cofiberStableEdges_map_iff`・`dgLifted_stableVertexClosure_iff_finiteCell`・`dgPretriangulatedYoneda_cofiberEdges_iff`。 `stableVertexClosure_ulift_iff`・`cofiberStableEdges_ulift_iff`・`dgNative_stableVertexClosure_iff_finiteCell`・`dgHomotopyFiniteCell_iff_derivedFiniteCell`・`dgNative_stableVertexClosure_iff_derivedFiniteCell`・`dgVerdierEdges_mem_iff_derivedFiniteCell`。 `dgRepresentableDerivedMap_surjective`・`dgClosedEdge_map`・`dgClosedEdge_mem_iff_derived_trW`・`dgQuotient_exists_closedRoof`・`DGQuotientActualRoof`・`dgQuotient_exists_actualRoof`。 `dgRepresentableRestrictionMap_naturality`・`dgRestrictionRepresentableArrow_derived_eq_iff`・`dgClosedMappedEdge_closed`・`DGQuotientActualRoof.compositionSimplex`・`dgQuotientEdge_exists_fractionTriangle`。 `dgQuotientClosed_eq_iff_restriction`・`dgQuotientKernel_exists_closedDenominator`・`dgQuotientClosed_exists_cancelingDenominator`・`dgQuotientEdge_exists_cancelingTriangles`・`dgQuotientEdges_exists_cancelingTriangles`。 `dgDerivedDenominator_exists_closed`・`dgRepresentableDerivedEdgeMap_compStruct`・`dgModuleProjectiveDerived_zero_iff_primitive`・`dgQuotientShiftedKernel_exists_closedDenominator`・`dgQuotientFiniteShiftedKernel_exists_denominator`・`dgQuotientFiniteShifted_exists_primitives`・`dgQuotientShifted_exists_closedRoof`。 `dgModuleHomRightShift_primitive`・`dgModuleClosedRightShift_precompose_cycle`・`dgYoneda_exists_gradedPrimitive_iff`・`dgYonedaClosedRightShift`・`dgYonedaRightShift_exists_primitive`・`dgModuleHomRightShift_exists_primitive_iff`・`dgYonedaClosedRightShift_zero_iff_primitive`・`dgQuotientFiniteGraded_exists_primitives`。 `dgModuleShiftOut_naturality`・`dgModuleShiftIn_naturality`・`dgModuleClosedRightShift_postcompose_cycle`・`dgRestrictionGradedComparison_evaluation`・`dgRestrictionShiftedComparison_zero_iff_boundary`・`dgQuotientFiniteBoundary_exists_primitives`。 `dgModuleHomRightShift_unshift`・`dgYonedaClosedRightShift_surjective`・`dgRestrictionGradedLiftClosed`・`dgYonedaInverse_precompose_evaluation`・`dgModuleShiftedComparison_exists_primitive`・`dgRestrictionGradedLift_precompose_evaluation`・`dgQuotientGraded_exists_fraction`・`dgQuotientGraded_exists_actualFraction`。 `dgGradedPrecompose_d`・`dgFunctorGradedPrecompose_map`・`dgPrimitiveResidual_closed`・`dgPrimitiveCorrection_d`・`dgPrimitiveCorrection_residual`・`dgClosedVerdierDenominator_comp`・`dgQuotient_exists_relativePrimitive`・`dgRelativePrimitiveWitness_refine`・`dgQuotientFinite_exists_relativePrimitives`・`dgQuotientFinite_exists_actualRelativePrimitives`。 `dgClosedPrecomposition_f`・`dgClosedPrecomposition_comp`・`pinchedClosedPrecomposition`・`pinchedCompleteTop`・`dgQuotientFinite_exists_pinchedBoundaryFillers`・`pinchedBoundary_eq_of_proper_components`・`dgQuotientFinite_exists_actualBoundaryFillers`。 `pinchedMappedBoundaryComparison_proper`・`PinchedTopComparison`・`PinchedTopComparison.difference_full`・`dgQuotientFinite_exists_pinchedTopComparisons`・`pinchedBoundaryPrimitiveEdge_top`・`PinchedTopComparison.edge_zero`・`PinchedTopComparison.homotopy_zero`・`dgQuotientFinite_exists_pinchedVertexEdges`。 `PinchedTopComparison.difference_face_zero`・`pinchedNormalizedBoundary_rhs`・`PinchedTopComparison.normalized_primitive_equation`・`PinchedTopComparison.normalizedFiller_face`・`PinchedTopComparison.normalizedFiller_full`・`pinchedNormalizedPointed`・`PinchedTopComparison.normalizedRelStruct`。 `pinchedConeIntervalMap`・`pinchedSimplex_pullback_zero_of_avoids`・`PinchedTopComparison.normalizedPrism_boundary`・`pinchedPointwiseAdd`・`PinchedTopComparison.homotopy_boundary`・`PinchedRelativeHomotopy`・`dgQuotientFinite_exists_pinchedRelativeHomotopies`・`dgQuotientFinite_exists_actualRelativeHomotopies`。 `PinchedRelativeHomotopy.map`・`dgClosedPrecomposition_naturality`・`PinchedRelativeHomotopy.refineClosed`・`DGQuotientRelativeFiller`・`DGQuotientRelativeFiller.actual_boundary`・`DGQuotientRelativeFiller.refineClosed_comp_h`・`DGQuotientRelativeFiller.refineClosed_id_h`。 `dgClosedPinchedRepresentable`・`dgClosedVerdierRoofDiagram`・`dgClosedPinchedFunctorMap`・`dgQuotientRoofComparison`・`dgVerdierOver`・`dgClosedVerdierDenominatorVertex`・`dgClosedNerveOverMap_projection`・`dgClosedRoofSliceMap_projection`。 `ordinaryRoofVertexEdge`・`dgClosedNerveOverMap_edge`・`dgClosedNerveOverMap_vertex`・`dgClosedRoofVerdierMap`・`dgClosedRoofVerdierMap_ι`・`dgClosedRoofVerdierMap_source`・`dgClosedRoofVerdierMap_vertex`。
- `dgClosedRoofVerdierMap_vertex_surjective`・`dgVerdierOverSource_edge_mem`・`dgClosedRoofRefinement_mem`・`dgClosedPrecomposition_quasiIso_of_invertible`・`dgQuotientRoofDiagram_map_equivalence`・`dgQuotientRoofConstantComparison`・`dgQuotientRoofRefinement_relative_fillers`・`dgQuotientRoofRefinement_vertex_lifts`・`dgRoofReplacementComparison`・`dgRoofReplacementConstantComparison_isPrecompositionEquivalence`。
- `dgCommonRoofComparison_relative_fillers`・`dgCommonRoofComparison_vertex_lifts`・`roofReplacementTransportEdge`・`roofReplacementMap_piZero_surjective`・`dgRoofReplacementComparison_piZero_surjective`・`dgRoofCorrespondence`・`dgQuotientRoofCorrespondence`・`dgRoofCorrespondenceFiberIso`・`dgQuotientRoofCorrespondenceFiberIso`・`dgRoofCorrespondenceMap`・`dgRoofCorrespondenceMap_projection`。
- `dgRoofCorrespondenceFiberMap_comparison`・`dgRoofCorrespondenceFiberMap_conjugate`・`roofRightFibration_pullback_leftFibration_of_inverts`・`dgQuotientRoofCorrespondenceProjection_leftFibration`・`dgVerdierOverIdentityVertex_isTerminal`・`dgQuotientFixedHomRoofMap_isRightCofinal`・`dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence`・`dgFixedHomRoofMap_comparison`。
- `closedNerveInclusion_dgFunctor`・`dgStrictRoofNerveMap`・`dgStrictRoofRefinementEdge`・`dgStrictQuotientRoofRefinementEdge`・`dgRoofCorrespondenceMap_strictVertex`・`dgStrictMappedRoofVertex_rightInverse`・`dgStrictMappedRoofNerveMap_vertex_surjective`。
- `dgRoofCorrespondenceMap_piZero_surjective`・`dgClosedRoofRefinementPrism_projection`・`dgClosedRoofRefinementHomotopy`・`dgQuotientClosedRoofRefinementHomotopy`・`dgClosedRoofHomInclusion_comparison`・`dgClosedRoofRelativeHomotopy_projection`・`DGActualRoofRelativeFiller`・`DGActualRoofRelativeFiller.actual_boundary`・`dgQuotientRoofFinite_exists_relativeFillerData`・`dgClosedRoofRefinementPrism_comparison`・`dgRoofFillerTransport_boundary`・`DGActualRoofRelativeFiller.transport_boundary`・`roofLeftFibration_relativeFirstTriangle`・`DGActualRoofTransportedFiller`・`DGActualRoofTransportedFiller.homotopy_boundary`・`DGActualRoofTransportedFiller.homotopy_projection`・`dgQuotientRoofFinite_exists_transportedFillerData`・`dgVerdierOverFinite_exists_commonSource`・`DGVerdierDiagramVertexCone`・`dgVerdierDiagramVertexCone_nonempty`・`dgVerdierDiagramEdgeHorn`・`dgVerdierDiagramEdgeCompStructOfFiller`・`dgLastHornMissingResidual_closed`・`dgLastHornTopResidual_closed_of_Q`・`DGLastHornSolution`・`dgLastHornFinalClosed`・`dgVerdierDiagramEdgeCompStructOfCochains`・`dgLastHornFinalClosed_edge`・`dgVerdierDiagramLastClosed_mem`・`dgLastHornTopResidual_differential`・`dgLastHornConeResidual_closed`・`dgLastHornSolutionOfConePrimitive`・`dgLastHornSolution_nonempty_iff_coneResidual_boundary`・`dgLastHornYonedaConeIso`・`dgLastHornYonedaResidual_closed`・`dgFiniteCellGraded_exists_simultaneous_closedPrimitives`・`dgVerdierDiagramResidualRefinement_nonempty`・`dgLastHornPrecomposedResidual_fst`・`dgLastHornPrecomposedResidual_snd`・`DGLastHornResidualRefinement.Q_differential`・`DGLastHornResidualRefinement.a_differential`・`dgLastHornSourceRefinement`・`DGLastHornResidualRefinement.solution`・`dgLastHorn_exists_sourceRefinement_filler`・`dgVerdierDiagramEdge_exists_refinedFiller`・`dgVerdierDiagramRefinedOverTriangle_face0`・`DGVerdierDiagramEdgeRefinement.compStruct`・`dgVerdierDiagramEdgeRefinement_nonempty`・`dgVerdierDiagramHorn_source`・`dgVerdierDiagramHorn_target`・`dgVerdierFiniteEdgeRefinement_nonempty`・`DGVerdierFiniteEdgeRefinement.apex_eq`・`DGVerdierFiniteEdgeRefinement.refinedFace1_legTriangle`・`DGVerdierFiniteEdgeRefinement.refinedFace2_legTriangle`・`DGVerdierFiniteEdgeRefinement.vertexCone`・`DGVerdierFiniteEdgeRefinement.vertexConeCompStruct`・`dgVerdierDiagramFiniteEdges_exists_vertexCone`・`dgVerdierDiagramTriangleHorn`・`dgVerdierDiagramTriangleFiller_face_cone`・`dgFourLastHornMissingResidual_closed`・`dgFourLastHornQData_topRhs_closed`・`dgFourLastHornConeResidual_closed`・`dgFourLastHornSolution_nonempty_iff_coneResidual_boundary`・`dgVerdierDiagramTriangleLastClosed_mem`・`dgFourLastHornResidualRefinement_nonempty`・`DGFourLastHornResidualRefinement.Q_differential`・`DGFourLastHornResidualRefinement.a_differential`・`dgVerdierTrianglesResidualRefinement_nonempty`・`dgSimplexInitialRefinement`・`dgSimplexDataInitialRefinement_rhs`・`dgSimplexInitialRefinement_face_zero`・`dgSimplexInitialRefinement_pullback_fixed_zero`・`dgSimplexInitialRefinement_face_positive`・`dgFourLastHornSourceRefinement`・`dgFourLastHornSourceRefinement_knownData`・`DGFourLastHornResidualRefinement.solution`・`dgFourLastHornFinite_exists_sourceRefinement_fillers`・`dgVerdierTriangles_exists_refinedFillers`・`dgTetrahedronInitialRefinement_initialDiagonal`・`fullSubcomplexSimplexApexLift`・`dgVerdierDiagramRefinedOverThreeSimplex`・`dgVerdierDiagramRefinedThreeApex_comp`・`dgVerdierDiagramRefinedThreeApex_mem`・`dgVerdierDiagramRefinedThreeSimplex`・`DGVerdierFiniteTriangleRefinement.simplex`・`dgVerdierFiniteTriangleRefinement_nonempty`・`DGVerdierFiniteTriangleRefinement.apex_eq`・`dgSimplexInitialRefinement_triangle`・`dgOverTwoSimplexInitialRefinement`・`dgOverTwoSimplexInitialRefinement_apex_edge`・`dgVerdierTwoSimplexInitialRefinement`・`dgVerdierTwoSimplexInitialRefinement_congr`・`dgVerdierDiagramRefinedThreeSimplex_face_cone`・`DGVerdierFiniteTriangleRefinement.commonConeFace_eq`・`DGVerdierClosedVertexRefinement.vertexCone`・`dgOverTwoSimplexInitialRefinement_face_positive`・`DGVerdierClosedVertexRefinement.edgeCone_face_positive`・`DGVerdierClosedVertexRefinement.edgeCompStruct`・`dgVerdierTriangles_exists_closedRefinedVertexCone`・`dgVerdierDiagramFiniteTriangles_exists_vertexCone`・`dgSimplexInitialRefinement_pullback_initial`・`dgSimplexInitialRefinement_degeneracy_positive`・`roofPointSliceTetrahedron_degeneracy_one`・`DGVerdierClosedVertexRefinement.refine_degenerateLeg`・`dgVerdierDiagramIdentityEdgeCone`・`dgVerdierDiagramNormalizeEdgeCone_identity`・`dgVerdierDiagramFiniteTriangles_exists_unitalVertexCone`・`DGVerdierTriangleConeBoundary`・`dgVerdierDegenerateTriangleCone_boundary`・`dgVerdierDegenerateTriangleCone_congr`・`dgVerdierNormalizeTriangleCone_boundary`・`dgVerdierNormalizeTriangleCone_degeneracy`・`DGVerdierDiagramTwoCone`・`dgVerdierDiagramTwoCone_nonempty`・`dgGeneralLastHornMissingResidual_closed`・`dgGeneralLastHornMissingHom_zero`・`dgGeneralLastHornQData_properEquations`・`dgGeneralLastHornQData_topRhs_closed`・`DGGeneralLastHornSolution.fac`・`DGGeneralLastHornSolution.simplex_Q`・`DGGeneralLastHornSolution.simplex_A`・`dgGeneralLastHornMissingResidual_three`・`dgGeneralLastHornMissingResidual_four`・`dgLastHornLastTerm_formula`・`dgGeneralLastHornQData_rhs_top`・`dgGeneralLastHornSolutionOfCochains`・`DGGeneralLastHornSolution.differential_a_expanded`・`dgGeneralLastHornTopResidual_three`・`dgGeneralLastHornTopResidual_four`・`dgGeneralLastHornKnown_equation`・`dgGeneralLastHornResidualContribution_zero`・`dgGeneralLastHornLastResidualTerm`・`dgGeneralLastHornTopResidual_differential`・`dgGeneralLastHornFinalEdge_closed`・`dgGeneralLastHornPostcomposition_f`・`dgGeneralLastHornNormalizedK_differential`・`dgGeneralLastHornConeResidual_closed`・`dgGeneralLastHornSolutionOfConePrimitive`・`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary`・`dgGeneralLastHornYonedaConeIso`・`dgGeneralLastHornSolution_nonempty_iff_yonedaResidual_boundary`・`dgGeneralLastHornResidualRefinement_nonempty`・`dgGeneralLastHornPrecomposedResidual_fst`・`dgGeneralLastHornPrecomposedResidual_snd`・`DGGeneralLastHornResidualRefinement.Q_differential`・`DGGeneralLastHornResidualRefinement.a_differential`・`dgSimplexDataInitialRefinement_equation`・`dgPartialSimplexHorn_knownData_face`・`dgGeneralLastHornSourceRefinement_knownData`・`dgGeneralLastHornSourceRefinement_preserves_face_zero`・`dgGeneralLastHornSourceRefinement_missingResidual`・`dgGeneralLastHornSourceRefinement_topResidual`・`DGGeneralLastHornResidualRefinement.a_differential_original`・`DGGeneralLastHornResidualRefinement.solution`・`dgGeneralLastHorn_exists_sourceRefinement_filler`・`dgGeneralLastHornFiniteRefinement_nonempty`・`dgGeneralLastHornFinite_exists_sourceRefinement_fillers`・`dgGeneralLastHornSourceRefinement_face_positive`・`roofPointSliceSimplex_naturality`・`roofPointSliceSimplexOfFace_face_zero`・`roofPointBoundaryHorn_face`・`roofPointBoundaryHorn_lastEdge`・`dgGeneralLastHornFinalClosed_edge`・`dgVerdierBoundaryLastClosed_mem`・`dgOverBoundaryRefinedSimplex_face_positive`・`dgVerdierBoundaryFinite_exists_refinedOverSimplexes`。

### 依存と提供

- Core・F1・F1B・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。

### 未コミット

- 今回の所有ファイルだけを保存。自分の未コミットなし。他レーンの変更は取り込んでいない。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルド成功（7272 jobs）。公理監査は Derived 8902 宣言／968 モジュール、Stable 10017／1238。許容三公理のみ。今回の新規7モジュールは警告なし。主要宣言に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零化・平坦模型との比較、前三角性の cell 分解への反映、平坦分解後の商の実安定性と商関手の完全性は完成。全 ∞ 関手圏の局所化普遍性と Verdier 列は未完。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β3：全次元の境界 join ホーン、実最後辺の分母性、同時充填からの実 over 単体の回収まで完成。次は新 apex の実分母性を証明して、回収単体を同じ `dgVerdierOver` に戻す。最初に任意次元の `dgOverSimplexInitialRefinement` を作ると、全正番号面の照合にも再利用できる。`roofPointSliceSimplex a σ` の実 dg 単体を `dgSimplexInitialRefinement` で写し、正の最終頂点への単射制限の保存から終点固定を戻して `roofPointSliceSimplexOfFixed` に渡す（over の零次元も含む）。`RoofPointSliceSimplex.lean` の全順序写像への自然性と `dgSimplexInitialRefinement_pullback_fixed_zero` で新旧の任意始点零を含む辺を比較する。特に始頂点の構造辺は、閉追加射と元の構造閉射の実合成と同定し、`dgSimplexInitialRefinement_edge_comp`・`dgClosedVerdierDenominator_comp` から実分母性を供給する。回収した高次単体の正番号一面は、`dgOverBoundaryRefinedSimplex_face_positive` と `dgSimplexInitialRefinement_congr` により元の境界一面の同じ閉細分。始頂点はその面に含まれるので、その分母性を移して `fullSubcomplexSimplexApexLift` と元の境界零面から同じ全実分母単体を得る。追加射の終対象等式輸送は `dgClosedTargetTransport_edge` を使い、同じ実追加分母辺を保つ。有限族の全新 apex と共有面を同じ共通閉細分へ揃え、高次の標準退化と重なりも正規化する。実 join からの全単体写像、零次元の既存厳密屋根辺との一致、有限非退化単体帰納、厳密添字の filteredness・実添字への cofinality、実屋根比較の弱同値性、全標的の `F1B/Localization.IsLocalization`、Verdier 列、β5、β4 は未完。

作成日：2026-10-18。状態：S1〜S7（D7）完了。β3 に進む。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/StableTriangulatedEquivalence.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定、IsStable、実 suspension 由来の全整数シフト、標準 cofiber 三角形の像の同型、全 distinguished triangle の保存・反映、単位・余単位と整合する三角同値 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f を既提供とせず、S7 の coslice の直接充填で標準 cofiber の押し出し性を証明した。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。


## β3：Drinfeld 商と ∞ 圏的 Verdier 商

D7 の後に着手済み。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda 模型との同値、前三角 dg 圏と平坦分解後の商の実 dg nerve の安定性、商関手の完全性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、同じ宇宙の標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明する。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏の平坦分解後の商の実安定性と商関手の完全性は完成。
  零化する完全関手への前合成の同値、Verdier 列を構成する（見積もり 1〜2 万行）。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

β3 の後。L4 §26 の dg 圏分解と既存の dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、α2b の Cat_∞ の極限・lax pullback の実装を待って接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
