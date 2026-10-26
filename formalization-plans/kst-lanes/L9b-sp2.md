# Sp-2 — d3・s3・s5 専用計画

更新：2026-10-27。正本：L9-spectra.md。開始時の採用条件を以下へ転記する。

## 所有・禁止事項
- 所有：KST/Spectra/ の d3 新規葉、Spectra/D3All.lean、scripts/audit_kst_spectra_d3.lean、本計画（≤300行）。
- 既存 Spectra 葉、Spectra.lean、LocalizingInvariants、L9 は読み取り専用。
- Sp は c5 を担当。PointedUncurry*・PointedParametric* の未追跡4葉は接続せず保持する。
- nativeLoop 正本。evaluationPost・uncurry・d7 を再開せず、新仮定・sorry・追加 axiom・円交換因子の直接比較を導入しない。

## L9 転記：Sp-6

### Sp-6 の三段目（第二チャット）
- [x] s1. 固定 S・ν と商合成を照合し、源内の零化と ν 像の認証を分離する。
- [x] s2. S 内の実零化 2-cell を構成し、指定商合成と ν 像を回収する。
- [ ] s3. 二つの三角形を保つ具体的長方形と、K-B の DGKappaSuspensionRelativeRoofInput 用の固定 ν 上の相対 Verdier 接続を供給する。
- [x] s4. K-B-S c13c179e3 の実全族・厳密な底・元の Kan 単位回収・指定恒等点を適用し、元の verdierFractionMappingComparison_isFullyFaithful を追加仮定なしで公開。対象・集約・専用監査合格。
- [ ] s5. 集約ビルド・公理監査・仮定検査を通し、公開界面と引き継ぎを保存する。

### Sp-5 d3 の三段目（I-5、10-26 再開）
- [x] d3a. 実終対象と任意 coherent cospan の極限を有限極限生成定理へ接続する。
- [ ] d3b. nativeLoop と一段移動の全関手比較。採用済み：補助 AdjointLoopKanSequence を使い、①相対 BF 置換と全 Hom 自然性、②指定 loop 図式・厳密終点を保つ元の nativeLoop との全図式 FunctorIso、③既存 nativeTailEquivalence と合わせた hΩ の順。nativeLoop が正本。②は点ごとの π 同型と厳密自然性から組み、円交換因子を直接比較しない。①②を未供給の入力のまま完成扱いにしない。
- [ ] d3c. 元の nativeLoop の IsQCatEquivalence（hΩ）を証明する。
- [ ] d3d. D の isStable_of_loopEquivalence に実入力を代入し sp_isStable を公開する。
- [ ] d3e. 両集約・専用監査・仮定検査を通し、引き継ぎを保存する。


## L9 転記：採用済み自然性条件
- **採用済み d3b の自然性条件**：T(X) := adjointLoop (tail X.toKanSequence)、α_X := adjointLoopTailUnit。実分解 X → R(X) → T(X) の合成は各段で α_X に厳密一致する。AdjointLoopUnitRawHom が証明したのは α_X の後合成の全 Hom 比較（源の豊穣合成自然性、標的の通常射の自然性、実 π 同型）。接続済みの Compatible 系は元の射 f と置換射 g に i_X ≫ g = f ≫ i_Y を全パラメータで課す。この左因子の可換性だけから右射影 q の自然性・補助 T の全 Hom 作用・nativeLoop との比較を結論しない。FullCompatible 系は同じ全パラメータ族で左右条件を同時に保持し、元の射影の全単射 RLP・実豊穣合成・単位・元の Sp への同値・包含の全図式同型と各段の fullGradedProjection を供給する。指定 α は元の fac で回収する。nativeLoop との比較はこの成果に含めない。②は指定 loop 図式・厳密終点を保ち、点ごとの π 同型と厳密自然性から全図式 FunctorIso を組む。③は既存 nativeTailEquivalence と実 hΩ を D の一般定理へ代入する。①②を明示入力に残して完成扱いにせず、円交換因子の直接比較・evaluationPost・uncurry・d7 は再開しない。暫定見積りは①5〜8時間、②4〜7時間、③適用・集約監査1〜2時間（供給・閉包安定の待ち時間を除く、②の比較が主な不確定部分）。

## L9 転記：引き継ぎ時点
- **再開の第一工程**：d3a の sp_hasFiniteLimits は公開済み。d3b は採用済み。K-B-S2 bf29e6b53 の Kan 列標的の実相対分解を元の補助単位へ直接適用する（AdjointLoopRelativeBF）。Compatible 系・GradedInclusion・CoherentComparison の7葉は集約・監査へ接続済みで、元の全 Hom を回収する originalInfinityEquivalence と指定左因子を保つ inclusionFunctorIso を供給する。①の右射影 q を含む全 Hom 自然性も実構成済み。補助 loop の全パラメータ作用・制限可換性・単位の厳密自然性は AdjointLoopParameterHom。二変数 corner は許可に従い Sp の新葉で実構成し、RawSpectrumMapping.relativeCorner_rlp_monomorphisms／relativeCorner_trivialKanFibration と元の二射影・全段評価を供給する。同じ単位・右射影へ実適用した FullCompatible 系は、左右の条件を同時に保つ全 Hom の恒等・合成・結合律、元の Sp を回収する fullOriginalInfinityEquivalence、元の包含を成分とする fullInclusionFunctorIso、各段の実右射影を全 Hom 上で保つ fullGradedProjection を供給する。AdjointLoopRelativeNativeDiagram は元の native loop 図式族・厳密終点と成分候補を供給する。②の追加設計は事前採用済み、今回ユーザーへチャットで具体的仕様を再送：元の X→M_X→T_X（合成 η_X）と、厳密 tail 終点の実 loop 図式の BF 始点 L_X に X→L_X→T_X（合成 η_X）を構成する。後者の a_X の相対 cofibration と全パラメータ境界整合も証明対象。比較 c_X:L_X→M_X は a_X≫c_X=i_X、c_X≫q_X=r_X を保つ relativeCorner a_X q_X の指定境界 fiber から構成し、比較射を含む全 Hom の RLP・全単体整合を相対充填から証明する。L_X・a_X・r_X の存在や Hom 充填を明示入力に残さない。RLP・coherence を入力に残さず、nativeLoop 正本・厳密 tail 終点を保持し、円交換因子を直接比較しない。AdjointLoopRelativeDiagramResolution は図式側の基底を実装：終点評価の引き戻し fullLoopDiagramResolution、射影の実自明 Kan fibration、fullLoopDiagramResolutionEquivalence、元の指定族を厳密回収する切断、fullLoopDiagramResolutionNativeIso／SourceIso。これは比較射を追加する前の図式側の基底に限る。次は比較射を含む全 Hom の相対充填・合成整合の実証で、この射影の RLP を図式側の RLP だけから推論しない。比較射を自由な可逆辺として加えるだけでは選択空間の可縮性は保証されず、包含・右射影との境界を保つ充填が必要。現行 q の自然性だけから、任意の逆射と持ち上げを含む deloopingComparison の厳密自然性を結論しない。実 nativeLoop 比較・hΩ・sp_isStable は未提供。K-8 e の実 dg 塔・Tor 比較、s3 の三つの全図式比較は未供給、到着時は s3 最優先。

### Sp-6 s3 の接続口（採用済み、具体的入力の存在は未供給）
- 採用済み修正：固定 ν の Perf 商辺は strict Verdier 商でなく冪等完備化までの列。K-S• 正本 PerfectVerdierSequence（実 strict 商＋完備化）を使う。Sp の RelativePerfectVerdierDiagram.ofSquare／ofStableSquare、RelativePerfectVerdierRectangle.ofActualFaces と境界付き全源比較・全 ν 像比較で、Cat^perf 不変量の同じ制限の pullback を得る。ofStrict は元の四角形・長方形と恒等完備化を保ち、完備性を追加入力にしない。D-21 は K-S• の dgOdotMilnorCompletion／_isIdempotentCompletion に特殊化済み。実二面からの comparison_isPullback_of_actualFaces と、絶対 Cat^perf 長方形への comparison_isPullback_of_actualFaces_imageIso、同じ全比較成分を使う rectangleValueIso_of_imageIso／_triangle を提供。実長方形・全比較の一体化は未供給。新たな不変量条件や一般商 API は導入しない。
- 固定 S・ν・K を保ち、零角に A/A を使う。対象別 ε からの自然な収縮を構成せず、全対象商からの厳密延長を用いる。
- 具体的 S 長方形 F の実際の ν 像を、右面・外周の Verdier 証拠で認証する。独立に選択した絶対 Tamme 長方形との厳密等号 image_eq に代えて、指定境界を保つ全図式 FunctorIso を接続口に追加する。既存の厳密等号版は特殊化として保持する。
- 元の包含・商・四辺と二つの合成三角形を明示して保持する。始域回収は元入力への増大屋根と ν 像の指定同値で受け、S 内の source_vertex_eq を主経路で要求しない（17:53 採用、RelativePerfectVerdierSourceRoof で受ける）。旧等号版は特殊化として保持する。絶対 PerfectVerdierDiagram の認証から同じ実 ν 二面へ全比較を運び、同じ実 S 長方形の値で貼合せを消去する。辺の関手同型だけから全図式比較や S 内の厳密代表を推論しない。長方形と全図式比較の存在は未証明。
- K-B の DGKappaSuspensionRelativeRoofInput は現行の型で受けられる。I・P は変更せず、実核・指定収縮・Verdier 証拠・零角の Perf 値の零性の供給後に exists_dgFixedNullRelativeRoof を適用する。一般分数比較の充満忠実性は s4 で供給済み。


## Sp-2 工程
- [x] d3b②の対象別入力：実 loop 始点 L_X と X→L_X→T_X を構成。a_X の相対 cofibration と指定単位の厳密因子分解を証明。全 Hom の整合は下項。
- [x] relativeCorner a_X q_X の指定境界 fiber から対象別 c_X:L_X→M_X を構成し、a_X≫c_X=i_X、c_X≫q_X=r_X を保持。
- [ ] 比較射を含む全 Hom の RLP・恒等・合成・全単体整合を実証。図式側だけの RLP で代用しない。
- [ ] 指定 loop 図式と厳密 tail 終点を保つ nativeLoop への全図式 FunctorIso を構成。
- [ ] d3b③→d3c：nativeTailEquivalence と合わせて元の nativeLoop の hΩ。
- [ ] d3d：Stable/LoopEquivalenceStability.isStable_of_loopEquivalence へ代入し sp_isStable 公開。
- [ ] s3：K-S• d④③ の実右面・外周・上下二単体を保つ全長方形比較の三認証到着後、固定 ν の RelativePerfectVerdierDiagram／Rectangle に実代入。
- [ ] s5：専用集約・公理監査・型の仮定検査・引き継ぎ。

## 依存と報告
- d3d → K-B3 d3。K-S• d④③ → s3 → K-B3 e。
- 各段の公開名はユーザー経由で報告。他チャットへの送信は行わない。
- s3 の実供給が来たら優先して接続する。

## 今回の実装境界
- D3ComparisonResolution：具体的な相対 BF 右射影 q_X へ corner を適用し、指定二境界を持つ比較族の射影の実 RLP、全単射に沿う相対延長、比較選択 fiber の可縮性を証明する。
- 固定 BF 始点上の比較族の RLP を証明した。一般補助定理の入力を最終安定性の新仮定として公開しない。
- fullLoopDiagramResolution は元の指定図式を保持する既存基底として読み取り専用 import。比較射を含む解像の完成とは扱わない。

## 2026-10-27：点ごとの実分解まで
- [x] `loopSource`：元の `deloopingComparison` を所有正本の `sequentialBFArrowMiddle` で相対分解した BF 始点。
- [x] `loopSourceInclusion_relative`／`loopSourceInclusion_levelwise`：a_X の相対 cofibration と全段の全基点 π 同型。
- [x] `loopSourceToBasedLoop`／`loopSource_fac`：厳密 tail の実 loop 頂点への右脚と元の delooping 射の回収。
- [x] `loopSourceBasedLoopVertexIso`／`loopSourceNativeVertexIso`：同じ実 loop 四角形の始点と nativeLoop 正本への点ごとの比較。
- [x] `loopSourcePre_trivialKanFibration`／`exists_relative_loopSourceFamily`：a_X の全 Raw Hom 前合成の実自明 Kan fibration と相対延長。
- [x] `loopSourceProjection`／`loopSourceProjection_fac`：r_X:L_X→T_X を実構成し a_X≫r_X=η_X を各段で厳密回収。
- [x] `loopSourceComparison`／`loopSourceComparison_left`／`loopSourceComparison_right`：実 c_X:L_X→M_X と指定二境界。
- [x] `loopSourceProjection_levelwise`／`loopSourceComparison_levelwise`／`loopSourceComparison_isInvertible`、同じ指定二境界 fiber の `loopSourceComparisonFiber_isContractibleKan`。
- 全て点ごとの実構成。元の delooping 比較・切断・相対分解の任意の選択に全 Hom 自然性は主張しない。
- **次工程**：実 loop 図式と a_X,r_X,c_X を保持する動く始点の共通解像を構成し、その全 Hom の射影の RLP・恒等・合成・全単体整合を実証する。固定始点の corner／前合成の RLP のみから、この豊穣解像の RLP を結論しない。
- 実 loop 図式族と指定終点を保つ全図式 FunctorIso、hΩ、sp_isStable は依然未提供。d3b②・d3c・d3d を完了扱いにしない。
- s3：L1 正本では K-S• d④③ の共通長方形と三認証は未完。既存の独立した全比較を三認証の完成として接続しない。

## 保存時の検証
- `lake build SerrePositivity.KST.Spectra.D3All` 合格（5750 jobs）。
- `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：496 modules／5114 declarations、私有宣言を含み標準三公理のみ。宣言型の ModelCategory 仮定なし。
- 監査で PointedParametricUncurryAction／Pre、PointedUncurryActionTensor／Composition の未接続も検査。
- 本計画は300行以内。既存 Spectra 葉・Spectra.lean・L9・LocalizingInvariants への編集なし。
- 注意：r_X は相対左因子に沿う元の η_X の延長として選んだ実射であり、実 loop 図式の射影との全図式整合はまだ証明していない。点別の図式始点同型を全図式自然性に昇格しない。

## 2026-10-27：実 loop 錐と指定境界の全パラメータ充填
- [x] `D3LoopSourceCone`：`loopSourceConeLift` を固定 cospan の slice 内で実構成。`loopSourceConeLift_projection`／`loopSourceConeEdge_projection` は元の BF 右脚そのものの一次単体を回収。
- [x] `loopSourceConeIso`／`loopSourceCone_isLimit`：同じ錐比較の可逆性を右 fibration の反映で認証し、錐全体の指定同型から極限性を証明。
- [x] `loopSourceSquare`／`loopSourceSquare_vertex`：L_X を厳密な実始点とする loop 四角形。終点は同じ tail X。右辺・上辺は `loopSourceSquare_right`／`_top` で元の path 終点射・一点からの射を厳密回収。
- [x] `loopSourceSquareFunctorIso`：同じ固定 cospan 上の錐比較を、元の BasedLoop.square (tail X) への全四角形 FunctorIso に移す。X を動かす関手の自然同型ではない。
- [x] `D3LoopConeRelativeLifting`：`loopConeLiftCorner_trivialKanFibration`／`exists_relative_loopConeLift` は固定 cospan の上で、終端錐・全 apex 辺と既存の部分パラメータを同時に固定した実充填を供給。
- [x] `loopSourceConeBoundary_fst`／`_snd`：構成済みの同じ錐比較の終端制限と、同じ BF 右脚全体を厳密回収。`loopSourceConeChosenPoint` を含む `loopSourceConeChoiceSpace_isContractibleKan` を証明。
- [x] `D3ComparisonHomLifting`：異なる X,Y の a_X・q_Y へ適用した `loopComparisonHomCorner_trivialKanFibration` と、任意次元 n の `loopComparisonBoundaryCorner_trivialKanFibration` を証明。
- [x] `exists_relative_loopComparisonBoundary`／`loopComparisonBoundaryFiber_isContractibleKan`：比較 Hom の既存部分パラメータ・n 単体の全境界・元の左右境界を同時に保持。n=1 の相対自然性比較に加え高次境界も含む。
- **未完の接続**：実際の Hom の恒等・合成から指定境界を実構成し、実 loop 図式も保持する共通解像の全 Hom 射影 RLP と豊穣法則を実証する。上記の充填器を、共通解像の完成とは扱わない。
- 比較 c_X の相対 BF 分解と二段の corner 充填は下記の共通 BF 解像で実装した。実 loop 図式との合成整合は同じ解像上で別途証明する必要がある。
- s3 再確認：更新中の L1 正本でも、共通実 S 長方形・上下指定二単体・三認証は未完。D2 の三入力の供給と、共通長方形の三認証の完成を区別する。

### 今回の保存検証
- `lake build SerrePositivity.KST.Spectra.D3All` 合格（5756 jobs）。
- `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：499 modules／5179 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
- d3b② 全体、hΩ、sp_isStable は未完のまま。対象別の全四角形比較と比較 Hom の指定境界充填を、X 全体の nativeLoop 比較と取り違えない。

## 2026-10-27：比較射を含む共通 BF Hom
- `D3CompositeCorner`：二つの実相対左因子の合成に対する corner の全単射 RLP を、二段の実充填から証明。合成左因子の cofibration 性を新仮定にしない。
- `D3SpectrumCorner`：同じ corner の BF 豊穣 Hom 表示と射影・右射影の合成を一般 BF 変数の段階で検査。具体的置換対象上で Raw と BF の引き戻しを直接書き換えると kernel の巨大展開が生じるため、この一般補題を使用する。
- `commonRefinement`／`commonLoopInclusion`／`commonComparison`：元の c_X:L_X→M_X の相対 BF 分解。`commonComparison_fac` が同じ c_X を厳密回収。`commonComparison_rlp` は全段 RLP。
- `commonInclusion_comparison`／`commonLoopInclusion_projection`／`commonProjection_fac`：元の包含 i_X・元の右脚 r_X・元の単位 η_X を同じ分解で保持。
- `commonHom` は元の FullCompatible Hom の指定二境界への実引き戻し。`commonBaseMap_trivialKanFibration`／`commonOriginalMap_trivialKanFibration` は比較を含む元の全 Hom の実 RLP。
- `commonIdentity`／`commonComposition` と `commonIdentity_composition`／`commonComposition_identity`／`commonComposition_assoc` は同じ二境界を保つ厳密な単位・合成・結合律。`CommonObject` は局所 Kan な実単体的圏。
- `commonOriginalInfinityEquivalence`：比較射を含む同じ共通 BF 解像から元の Sp への実同値。
- `commonInclusionFunctorIso`／`commonComparisonFunctorIso`：二段包含と指定比較右脚を成分とする全図式同型。対象別の可逆性だけでなく、同じ全 Hom 上の厳密な豊穣自然性から構成。
- `common_right_projection`：同じ共通 Hom の右条件に元の q_Y を後合成し、元の補助標的への右射影の全パラメータ自然性を回収する。
- 上記の全対象・専用集約・専用監査は合格。結果は下記。
- **重要な未完**：CommonObject の Hom は包含・比較・元の q を保持する共通 BF Hom であり、実 loop 図式の族をまだ含まない。`commonComparisonFunctorIso` は nativeLoop との同型ではない。
- **次工程**：元の実 loop 四角形を共通対象上へ、指定終点と比較成分を保って移し、同じ全 Hom と全 loop 図式の整合を実証する。元の L_X の点別図式比較や上記 Hom 射影の RLP だけから、図式を追加した射影の RLP を推論しない。hΩ・sp_isStable は未提供。

### 共通 BF Hom の保存検証
- `lake build SerrePositivity.KST.Spectra.D3All` 合格（5766 jobs）。
- `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：509 modules／5344 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
- 所有新葉・集約・計画・専用監査だけを保存。既存 Spectra 葉・Spectra.lean・L9・LocalizingInvariants は編集していない。
- s3 は L1 正本を再確認し、共通 S 長方形と三認証が未完であることを確認。実供給が到着したら優先して接続する。

## 2026-10-27：共通 BF 左脚を保持する実 loop 四角形
- `d3_rightFibration_liftEdge_source`：指定可逆辺の同じ一次単体を、指定始端から右 fibration へ持ち上げる。逆辺の終端固定持ち上げに元の逆三角形の実充填を組み合わせ、元の辺への厳密な射影を回収。
- `commonLoopConeLift`／`commonLoopConeLift_projection`：元の固定 cospan の slice で、元の `loopSourceCone X` を始端に、同じ `commonLoopInclusion X` そのものを持ち上げる。
- `commonLoopConeIso`／`commonLoopCone_isLimit`：同じ実錐比較全体の可逆性から極限性を移す。`commonLoopCone_vertex` は apex が共通対象 N_X 自体であることを証明。
- `commonLoopSquare`／`commonLoopSquare_vertex`：N_X を厳密な実始点、元の tail X を厳密終点とする実 loop 四角形。`_right`／`_top` は元の cospan の二脚を保持。
- `commonLoopSquareInclusionIso`／`commonLoopSquareFunctorIso`：元の実 loop 四角形から共通四角形へ、さらに元の BasedLoop 四角形へ、固定 cospan を保つ全四角形の同型。
- `commonLoopSquareInterval`／`_source`／`_target`／`_sourceEdge`／`_boundary`：同じ比較辺の実区間族、両端の全四角形、始点成分の元の共通 BF 左脚、固定 cospan 三頂点の同じ定値区間を厳密回収。
- **未完**：上記は各 X の実図式と比較成分。CommonObject の同じ全 Hom に実 loop 図式の族を加え、その射影 RLP と恒等・合成整合を証明する工程は残る。これらの対象別 FunctorIso を nativeLoop との全関手自然同型とは数えない。hΩ・sp_isStable は未提供。
- s3：L1 の最新現在地でも、上下指定二単体・共通 S 長方形・三認証は未完。D2 三入力の無条件供給とは区別して待機。

### 共通実 loop 四角形の保存検証
- `lake build SerrePositivity.KST.Spectra.D3All` 合格（5774 jobs）。新規4葉に警告なし。
- `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：513 modules／5396 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
- 所有新葉4本・専用集約・専用監査・本計画だけを変更。本計画は300行以内。既存 Spectra 葉・Spectra.lean・L9・LocalizingInvariants は編集していない。
