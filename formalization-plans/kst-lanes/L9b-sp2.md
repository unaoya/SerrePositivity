# Sp-2 — d3 専用計画（s3・s5 は Sp-3 へ移管）

更新：2026-10-27。正本：L9-spectra.md。開始時の採用条件を以下へ転記する。

現担当：B（構造補正を保つ証拠または正しい補正を保つ BF 比較 → nativeLoop 全図式 FunctorIso）に専念。d3c・d3d は Sp-2b へ移管し、B の確定出力型をユーザー経由で渡す。D3* の WIP は保持。

## 所有・禁止事項
- 所有：KST/Spectra/ の d3 新規葉、Spectra/D3All.lean、scripts/audit_kst_spectra_d3.lean、本計画（≤300行）。
- 既存 Spectra 葉、Spectra.lean、LocalizingInvariants、L9 は読み取り専用。
- Sp は c5 を担当。PointedUncurry*・PointedParametric* の未追跡4葉は接続せず保持する。
- nativeLoop 正本。evaluationPost・uncurry・d7 を再開せず、新仮定・sorry・追加 axiom・円交換因子の直接比較を導入しない。

## L9 転記：Sp-6

### Sp-6 の三段目（第二チャット）
- [x] s1. 固定 S・ν と商合成を照合し、源内の零化と ν 像の認証を分離する。
- [x] s2. S 内の実零化 2-cell を構成し、指定商合成と ν 像を回収する。
- s3. **Sp-3 へ移管**。移管時の記録：二つの三角形を保つ具体的長方形と、K-B の DGKappaSuspensionRelativeRoofInput 用の固定 ν 上の相対 Verdier 接続を供給する。
- [x] s4. K-B-S c13c179e3 の実全族・厳密な底・元の Kan 単位回収・指定恒等点を適用し、元の verdierFractionMappingComparison_isFullyFaithful を追加仮定なしで公開。対象・集約・専用監査合格。
- s5. **Sp-3 へ移管**。移管時の記録：集約ビルド・公理監査・仮定検査を通し、公開界面と引き継ぎを保存する。

### Sp-5 d3 の三段目（I-5、10-26 再開）
- [x] d3a. 実終対象と任意 coherent cospan の極限を有限極限生成定理へ接続する。
- [ ] d3b. nativeLoop と一段移動の全関手比較。採用済み：補助 AdjointLoopKanSequence を使い、①相対 BF 置換と全 Hom 自然性、②指定 loop 図式・厳密終点を保つ元の nativeLoop との全図式 FunctorIso、③既存 nativeTailEquivalence と合わせた hΩ の順。nativeLoop が正本。②は点ごとの π 同型と厳密自然性から組み、円交換因子を直接比較しない。①②を未供給の入力のまま完成扱いにしない。
- d3c. **Sp-2b へ移管**。B の実出力を明示引数として、元の nativeLoop の IsQCatEquivalence（hΩ）を先行構成する。
- d3d. **Sp-2b へ移管**。D の isStable_of_loopEquivalence への代入と sp_isStable 公開を担当する。
- [ ] d3e. 両集約・専用監査・仮定検査を通し、引き継ぎを保存する。


## L9 転記：採用済み自然性条件
- **採用済み d3b の自然性条件**：T(X) := adjointLoop (tail X.toKanSequence)、α_X := adjointLoopTailUnit。実分解 X → R(X) → T(X) の合成は各段で α_X に厳密一致する。AdjointLoopUnitRawHom が証明したのは α_X の後合成の全 Hom 比較（源の豊穣合成自然性、標的の通常射の自然性、実 π 同型）。接続済みの Compatible 系は元の射 f と置換射 g に i_X ≫ g = f ≫ i_Y を全パラメータで課す。この左因子の可換性だけから右射影 q の自然性・補助 T の全 Hom 作用・nativeLoop との比較を結論しない。FullCompatible 系は同じ全パラメータ族で左右条件を同時に保持し、元の射影の全単射 RLP・実豊穣合成・単位・元の Sp への同値・包含の全図式同型と各段の fullGradedProjection を供給する。指定 α は元の fac で回収する。nativeLoop との比較はこの成果に含めない。②は指定 loop 図式・厳密終点を保ち、点ごとの π 同型と厳密自然性から全図式 FunctorIso を組む。③は既存 nativeTailEquivalence と実 hΩ を D の一般定理へ代入する。①②を明示入力に残して完成扱いにせず、円交換因子の直接比較・evaluationPost・uncurry・d7 は再開しない。暫定見積りは①5〜8時間、②4〜7時間、③適用・集約監査1〜2時間（供給・閉包安定の待ち時間を除く、②の比較が主な不確定部分）。

## L9 転記：引き継ぎ時点
- **再開の第一工程**：d3a の sp_hasFiniteLimits は公開済み。d3b は採用済み。K-B-S2 bf29e6b53 の Kan 列標的の実相対分解を元の補助単位へ直接適用する（AdjointLoopRelativeBF）。Compatible 系・GradedInclusion・CoherentComparison の7葉は集約・監査へ接続済みで、元の全 Hom を回収する originalInfinityEquivalence と指定左因子を保つ inclusionFunctorIso を供給する。①の右射影 q を含む全 Hom 自然性も実構成済み。補助 loop の全パラメータ作用・制限可換性・単位の厳密自然性は AdjointLoopParameterHom。二変数 corner は許可に従い Sp の新葉で実構成し、RawSpectrumMapping.relativeCorner_rlp_monomorphisms／relativeCorner_trivialKanFibration と元の二射影・全段評価を供給する。同じ単位・右射影へ実適用した FullCompatible 系は、左右の条件を同時に保つ全 Hom の恒等・合成・結合律、元の Sp を回収する fullOriginalInfinityEquivalence、元の包含を成分とする fullInclusionFunctorIso、各段の実右射影を全 Hom 上で保つ fullGradedProjection を供給する。AdjointLoopRelativeNativeDiagram は元の native loop 図式族・厳密終点と成分候補を供給する。②の追加設計は事前採用済み、今回ユーザーへチャットで具体的仕様を再送：元の X→M_X→T_X（合成 η_X）と、厳密 tail 終点の実 loop 図式の BF 始点 L_X に X→L_X→T_X（合成 η_X）を構成する。後者の a_X の相対 cofibration と全パラメータ境界整合も証明対象。比較 c_X:L_X→M_X は a_X≫c_X=i_X、c_X≫q_X=r_X を保つ relativeCorner a_X q_X の指定境界 fiber から構成し、比較射を含む全 Hom の RLP・全単体整合を相対充填から証明する。L_X・a_X・r_X の存在や Hom 充填を明示入力に残さない。RLP・coherence を入力に残さず、nativeLoop 正本・厳密 tail 終点を保持し、円交換因子を直接比較しない。AdjointLoopRelativeDiagramResolution は図式側の基底を実装：終点評価の引き戻し fullLoopDiagramResolution、射影の実自明 Kan fibration、fullLoopDiagramResolutionEquivalence、元の指定族を厳密回収する切断、fullLoopDiagramResolutionNativeIso／SourceIso。これは比較射を追加する前の図式側の基底に限る。次は比較射を含む全 Hom の相対充填・合成整合の実証で、この射影の RLP を図式側の RLP だけから推論しない。比較射を自由な可逆辺として加えるだけでは選択空間の可縮性は保証されず、包含・右射影との境界を保つ充填が必要。現行 q の自然性だけから、任意の逆射と持ち上げを含む deloopingComparison の厳密自然性を結論しない。実 nativeLoop 比較・hΩ・sp_isStable は未提供。K-8 e の実 dg 塔・Tor 比較、s3・s5 は Sp-3 へ移管。以後本計画の s3・s5 行は編集しない。

### Sp-6 s3 の接続口（Sp-3 へ移管・以下は移管時の記録、以後編集しない）
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
- d3c：**Sp-2b へ移管**。nativeTailEquivalence と B の実出力を合わせて元の nativeLoop の hΩ。
- d3d：**Sp-2b へ移管**。Stable/LoopEquivalenceStability.isStable_of_loopEquivalence へ代入し sp_isStable 公開。
- s3：**Sp-3 へ移管**。移管時の記録：K-S• d④③ の実右面・外周・上下二単体を保つ全長方形比較の三認証到着後、固定 ν の RelativePerfectVerdierDiagram／Rectangle に実代入。
- s5：**Sp-3 へ移管**。移管時の記録：専用集約・公理監査・型の仮定検査・引き継ぎ。

## 依存と報告
- d3d → K-B3 d3。s3・s5／K-S• d④③ → s3 → K-B3 e は **Sp-3 へ移管**。
- 各段の公開名はユーザー経由で報告。他チャットへの送信は行わない。
- s3・s5 は **Sp-3 へ移管**。新規葉・S3All・audit_kst_spectra_s3・L9c-sp3.md は Sp-3 所有。以後 s3・s5 行は編集しない。

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
- s3：**Sp-3 へ移管**。移管時の記録：L1 正本では K-S• d④③ の共通長方形と三認証は未完。既存の独立した全比較を三認証の完成として接続しない。

## 保存時の検証
- `lake build SerrePositivity.KST.Spectra.D3All` 合格（5750 jobs）。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：496 modules／5114 declarations、私有宣言を含み標準三公理のみ。宣言型の ModelCategory 仮定なし。
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
- s3：**Sp-3 へ移管**。移管時の再確認記録：更新中の L1 正本でも、共通実 S 長方形・上下指定二単体・三認証は未完。D2 の三入力の供給と、共通長方形の三認証の完成を区別する。

- **今回の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5756 jobs）。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：499 modules／5179 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
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

- **共通 BF Hom の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5766 jobs）。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：509 modules／5344 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。 所有新葉・集約・計画・専用監査だけを保存。既存 Spectra 葉・Spectra.lean・L9・LocalizingInvariants は編集していない。
- s3：**Sp-3 へ移管**。移管時の記録：L1 正本を再確認し、共通 S 長方形と三認証が未完であることを確認。以後の接続は Sp-3 が担当。
## 2026-10-27：共通 BF 左脚を保持する実 loop 四角形
- `d3_rightFibration_liftEdge_source`：指定可逆辺の同じ一次単体を、指定始端から右 fibration へ持ち上げる。逆辺の終端固定持ち上げに元の逆三角形の実充填を組み合わせ、元の辺への厳密な射影を回収。
- `commonLoopConeLift`／`commonLoopConeLift_projection`：元の固定 cospan の slice で、元の `loopSourceCone X` を始端に、同じ `commonLoopInclusion X` そのものを持ち上げる。
- `commonLoopConeIso`／`commonLoopCone_isLimit`：同じ実錐比較全体の可逆性から極限性を移す。`commonLoopCone_vertex` は apex が共通対象 N_X 自体であることを証明。
- `commonLoopSquare`／`commonLoopSquare_vertex`：N_X を厳密な実始点、元の tail X を厳密終点とする実 loop 四角形。`_right`／`_top` は元の cospan の二脚を保持。
- `commonLoopSquareInclusionIso`／`commonLoopSquareFunctorIso`：元の実 loop 四角形から共通四角形へ、さらに元の BasedLoop 四角形へ、固定 cospan を保つ全四角形の同型。
- `commonLoopSquareInterval`／`_source`／`_target`／`_sourceEdge`／`_boundary`：同じ比較辺の実区間族、両端の全四角形、始点成分の元の共通 BF 左脚、固定 cospan 三頂点の同じ定値区間を厳密回収。
- **未完**：上記は各 X の実図式と比較成分。CommonObject の同じ全 Hom に実 loop 図式の族を加え、その射影 RLP と恒等・合成整合を証明する工程は残る。これらの対象別 FunctorIso を nativeLoop との全関手自然同型とは数えない。hΩ・sp_isStable は未提供。
- s3：**Sp-3 へ移管**。移管時の記録：L1 の最新現在地でも、上下指定二単体・共通 S 長方形・三認証は未完。D2 三入力の無条件供給とは区別して待機。

- **共通実 loop 四角形の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5774 jobs）。新規4葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：513 modules／5396 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。 所有新葉4本・専用集約・専用監査・本計画だけを変更。本計画は300行以内。既存 Spectra 葉・Spectra.lean・L9・LocalizingInvariants は編集していない。
## 2026-10-27：同じ共通 BF 基底上の全実 loop 図式族
- `commonLoopDiagramResolution`：終点評価を `commonNativeLoopEndpoint` に沿って実引き戻し。`commonLoopDiagramProjection` は同じ共通 BF 全単体を回収し、その射影の全単射 RLP・実同値・fiber 可縮性を証明。
- `exists_relative_commonLoopDiagram`：元の BF 比較族と既存の部分 loop 図式を同時に保つ相対充填。厳密 tail 終点も回収する。ただし新部分の図式始点と refined 関手の全 Hom 一致は充填条件に含めていない。
- `commonLoopDiagramToFull`／`_projection`／`_family`：元の full 図式基底へ同じ元の図式と BF 比較を保って接続。`commonLoopDiagramInclusionIso`／`commonLoopDiagramComparisonIso` は同じ新基底上の元の包含・比較成分の全関手同型。
- `commonChosenLoopDiagramFamily`／`_target`／`_vertex`／`_square_vertex`：共通 BF 基底の全頂点で構成済みの同じ実四角形全体を固定し、離散全頂点の単射への終点評価の実 RLP から全図式族を構成。
- `commonChosenLoopDiagramSection`／`_projection`／`_family`：同じ指定族の実切断。共通 BF 比較の全単体を厳密回収する。
- `commonChosenLoopSource_refined_vertex`：記憶した図式の始点関手と元の共通 refined 関手は全頂点で厳密一致。全単体の等式・全関手同型は主張していない。
- `commonLoopDiagramSourceNativeIso`／`commonChosenLoopSourceNativeIso`：同じ厳密終点を保つ実図式族の始点と元の nativeLoop の全関手同型。**未完 B** は、ここから共通 refined 関手へつなぐ全 Hom 整合。始点の頂点一致と図式側 RLP だけでこの比較を推論しない。
- **A→B→C→D の残り**：実 loop 図式の始点作用と共通 BF 全 Hom の作用を、元の包含・比較・右射影を保って比較する。その全関手比較を nativeLoop へ接続し、nativeTailEquivalence から hΩ、D の一般定理から sp_isStable を実証する。hΩ・sp_isStable は未提供。

- **共通全図式族の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5777 jobs）。新規2葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：515 modules／5458 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
- D3 新葉2本・専用集約・専用監査・本計画のみを変更。既存読み取り専用領域への編集なし。
## 2026-10-27：共通右射影の各段の全関手比較
- `d3StageKanEnriched`／`d3Stage_vertex`：元の BF 全 Hom の段評価を、既存の点つき Kan 全部分圏への実豊穣関手へ束ねる。単位・合成を保持し、通常射の像は元の段射そのもの。
- `d3Stage_post`／`d3Stage_pre`：元の BF 全 Hom の前後合成と段評価の厳密交換。一般 BF 変数上で検査し、具体的な相対置換対象の巨大展開を避ける。
- `commonComparison_stage_whiskered`／`commonProjection_stage_whiskered`：元の比較右脚の全 Hom 正方形を段評価し、元の q の全 Hom 正方形と縦に合成。同じ commonProjection の右自然性を各段の厳密な豊穣正方形として回収。
- `commonStageGradedProjection`／`commonStageGradedProjection_component`／`commonStageProjectionFunctorIso`：元の共通右射影の段射そのものを成分とする実自然変換と全関手同型。成分の可逆性は同じ射の全基点 π 同型から認証。
- `d3Stage_loop_action`／`commonTargetStageKanEnriched_eq_loop`：補助標的の段作用と、元の次段評価に既存の pointedKanLoopInfinity を施した作用が全豊穣 Hom 上で一致。同じ閉合成の curry を照合し、円交換因子の直接比較は行わない。
- `commonStageLoopFunctorIso n`／`commonLoopDiagramStageLoopIso n`：共通 refined 関手の段と、元の次段の実点つき Kan loop を全関手比較。同じ実図式基底へ前合成しても元の BF 比較を保持。
- **残る B**：実 loop 図式の始点作用をこれらの段比較へ接続し、段をまたぐ構造との整合を同じ全 Hom 上で実証する。各段の関手同型だけから BF 全体の自然同型は結論しない。commonChosenLoopSource と commonRefinedEnriched の全関手比較・hΩ・sp_isStable は未提供。

- **共通段比較の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5810 jobs）。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：518 modules／5503 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。宣言型の ModelCategory 仮定なし、指定未追跡四葉は未接続。
- 既存の点つき Kan 圏・loop 圏は読み取り専用 import で再利用。所有新葉3本・集約・監査・本計画のみを変更。既存読み取り専用葉への編集なし。
## 2026-10-27：同じ全実 loop 図式族の段評価
- `d3StagePullbackInfinityCone_isLimit`：元の BF 引き戻し錐の全 coherent 段評価の極限性。上流の `spectrumPullbackCone_level_isLimit` と元の点つき Hom の極限保存から、同じ通常錐・同じ coherent 錐全体で実証。
- K 側の既存 fiber 段定理は固定 K の依存を経由するため import せず、Sp の上流の実 BF 錐から接続した。K-B3 が d3d を消費する向きを保つ。専用監査で KST.Fibration／LocalizingInvariants の下流 import を拒否する。
- `d3FiberCone_stage_isLimit`／`d3BasedLoopCone_stage_isLimit`／`commonLoopCone_stage_isLimit`：同じ cospan 上の極限錐の一意性と形状制限・後合成の厳密交換から、構成済み実 loop 錐そのものの段極限性を回収。
- `d3StagePoint_isZero`／`d3StageBasedPath_isZero`：元の一点の豊穣 Hom の終対象性と、元の BF path から一点への同じ段射を使い、実段四角形の両零角を認証。
- `commonLoopSquare_stage`／`_vertex`／`_right`／`_top`：同じ実共通四角形の段評価を実 LoopSquare に束ねる。始点は共通 BF 対象の同じ段、終点は元の厳密 tail の同じ段。二辺は元の path 終点射・一点からの段射そのものの一次単体。
- `commonChosenStageLoopDiagramFamily`／`_corner`／`_source`／`_target`：元の全実図式族を同じ全単体で段評価し、全頂点の実 loop 四角形の認証から loop 図式の全部分圏へ因子化。四角の全関手・始点・厳密終点を回収。
- `d3StageTail`／`commonChosenStageLoopDiagramFamily_target_next`：元の nativeTail の段評価と元の次段評価を全豊穣 Hom・全 coherent 単体で厳密照合。
- `commonChosenStageEndpointLoopIso`：元の右射影の全関手比較を、同じ実段図式族の厳密終点の通常点つき loop へ接続。成分・全 Hom の作用を選び直さない。
- **残る B**：同じ実段図式族の始点作用と、その厳密終点への pointedKanLoopInfinity の作用との全関手比較を実証し、段をまたぐ構造との整合を保って BF 全体へ接続する。各段の実 LoopSquare／全関手同型だけから BF 全体の自然同型は結論しない。hΩ・sp_isStable は未提供。

- **実全段図式族の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5815 jobs）。新規4葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：522 modules／5561 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉4本・集約・監査・本計画のみを変更。既存読み取り専用領域への編集なし。
## 2026-10-27：点つき Kan の実端点パラメータ全図式族
- `d3PointedKanIhom`／`d3PointedKanPre_whiskered`／`d3PointedKanPre`：元の任意パラメータの内部 Hom 作用と、その制限射の全 Hom 自然性を Kan 全部分圏へ束ねる。成分は同じ `prePointed` 射そのもの。
- `d3PointedKanPreFunctorIso`／`d3PointedKanEndpointLoopIso`：通常円と端点円の同じ表示同型から全関手同型を構成。円交換因子の直接比較は行わない。
- `d3PointedKanMixed_id`／`d3PointedKanPre_factorization`／`d3PointedKanMixed_comp`：同じ入力 Hom と逆向きパラメータ制限を同時に扱う混合 Hom の恒等・厳密合成則を実証。
- `D3EnrichedOrderedDiagram.functor`／`d3PointedKanParameterDiagram`：元の順序図式と全 Kan 入力を一つの実豊穣関手へ束ねる。単位・合成は一般豊穣変数上で証明済みの法則を元の実混合作用へ代入。
- `d3PointedKanSquarePair`／`d3PointedKanParameterSquare`／`_corner`：二つの実区間単体と同じ全 coherent 単体を pairing し、全四角形族を構成。四角の全関手は指定した同じ内部 Hom 作用に厳密一致。
- `d3EndpointParameter`／`d3EndpointParameterSquare`：元の端点包含・cofiber 商射・一点への射を持つ実四角パラメータ関手を供給し、上記の一般図式へ代入。四つの角の全関手を実証。終点はまだ内部 Hom(unit, -) であり、恒等関手への単位同型との接続は別工程。
- `commonChosenStageEndpointCircleIso`：元の共通 BF 右射影の段比較を、同じ実段 loop 図式終点の endpoint 円模型へ全関手比較。元の比較成分を選び直さない。
- **残る B**：構成した実全四角形族の loop 性と終点の単位同型を認証し、同じ実段 loop 図式始点との全関手比較へ接続する。さらに段をまたぐ BF 構造の整合が必要。現在の族を loopDiagrams への因子化とは数えず、hΩ・sp_isStable は未提供。

- **実端点パラメータ族の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（5821 jobs）。新規5葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：528 modules／5732 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉5本・集約・監査・本計画のみを変更。移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：実端点 loop 全図式と共通段始点の全関手比較
- `d3Mixed_identity`／`d3ParameterEvaluation`：混合 Hom の実恒等入力は同じ元のパラメータ制限射。通常の制限図式の恒等・合成も実証。
- `d3PointedKanParameterSquare_vertex`：構成済み全四角形族の各実頂点は、同じ通常パラメータ図式の coherent 表示に全単体で一致。対象別の四隅一致だけで図式全体を比較しない。
- `d3EndpointParameterSquare_zero_corner`／`_other_zero`：同じ全族の point Hom と通常 based path Hom を実零頂点として認証。BF path の段とは区別する。
- `d3PointedKanCofiberCone_hom_isLimit`／`_isLimit`／`d3PointedKanEndpointCone_isLimit`：元の cofiber 制限錐の点つき極限性と元の端点包含の単射性から、同じ Kan Hom 錐・同じ coherent 錐の極限性を認証。
- `D3StrictPullbackSquare.triangle_left`／`triangle_right`／`isPullback`：同じ strict 錐を cospan ホーン・四角形へ移し、その二つの実三角形を元の fst・snd と二辺の同じ合成射列で回収。
- `d3EndpointParameterSquare_eq_strict`／`_isPullback`／`_isLoop`：元の全族の四角形そのものを上記実錐の四角形と厳密比較し、実引き戻し性を回収。
- `d3PointedKanEndpointLoopDiagram`／`_corner`／`_sourceIso`：構成済み全 Hom と全単体を保って loopDiagrams へ因子化。始点は元の通常 pointedKanLoopInfinity と全関手同型。終点は同じ Hom(unit, -) 作用。
- `d3Closed_unit_action`／`d3PointedKanUnit_whiskered`／`d3PointedKanUnitFunctorIso`：同じ標準単位同型と元の内部 Hom 全作用の厳密豊穣自然性を抽象閉圏で証明し、Kan 全関手同型へ代入。円交換因子は比較していない。
- `d3LoopDiagramEvaluation_equivalenceLifting`：両零角・引き戻し性の全図式同型不変性から、終点評価の全パラメータ同値持ち上げ性を供給。安定性・loop 切断を仮定しない。
- `d3PointedKanLoopCorrection`／`d3PointedKanLoopSection`／`_target`／`_diagramIso`：同じ指定単位同型の path を全図式へ持ち上げ、厳密恒等終点を持つ実 loop 切断を構成。元の実端点図式との全関手同型を保持。
- `d3PointedKanLoopSection_sourceIso`／`d3PointedKanLoopEvaluation_trivial`：同じ厳密切断の始点作用と元の通常 loop の全関手同型、同じ終点評価の全単射 RLP を実証。
- `commonChosenStageSourceLoopIso n`：元の共通実段図式族の厳密終点を保って全図式比較し、同じ始点段作用を通常 loop 作用へ全関手比較。
- `commonChosenStageRefinedSourceIso n`：元の共通 BF 右射影による段自然同型と上記全図式比較を合成し、refined 段作用と実 loop 図式始点段作用を全関手比較。
- **残る B**：この段比較と、段をまたぐ元の BF 構造との整合を実証し、同じ比較を BF 全体の FunctorIso へ接続する。各段の全関手同型から BF 全体の自然同型を推論しない。hΩ・sp_isStable は未提供。
- **実端点 loop・共通段始点比較の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7767 jobs）。新規9葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：537 modules／5823 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉9本・集約・監査・本計画のみを変更。移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：元の BF 構造射による実 loop 全図式族の段間比較
- `commonInclusion_stage_whiskered`：同じ共通左包含の全 Hom 正方形を元の段評価で回収。
- `commonStructure_stage_whiskered`：共通左包含・共通右射影の実正方形を縦合成し、同じ元の構造随伴単位の全 Hom 正方形を回収。
- `d3StageStructure_raw`：元の全 Hom への実自明射影の切断を用いて消去し、元の構造随伴射の全 BF Hom 自然性を実証。相対対象の巨大展開を避け、同じ元の Hom を使う。
- `commonInclusion_structure`／`commonComparison_structure`／`commonProjection_structure`：元の列射の構造条件を随伴表示へ移し、指定包含・比較・右射影の段間の厳密正方形を回収。補助列の構造は元の定義だけを展開し、円交換因子を比較しない。
- `d3StageStructureGraded`／`_component`／`d3StageStructureFunctorIso`：元の BF 構造随伴単位そのものを成分とする、段評価から次段通常 loop 評価への実豊穣自然変換と全関手同型。成分の可逆性は元の Ω 条件から認証。
- `commonChosenStageStructureSquareIso`：この同じ構造同型を四角形の内部 Hom へ写し、元の全実図式族へ前合成。元の段族と、同じ次段族へ通常 loop を施した族との全四角形同型を構成。
- `commonChosenStageLoopImageSquareFamily_isLoop`／`commonChosenStageLoopImageFamily`：この同じ次段 loop 像の実零角・引き戻し性を、元の段との全図式同型から認証し、loopDiagrams へ因子化。
- `commonChosenStageStructureDiagramIso`：元の全部分複体包含の充満忠実性で、同じ四角形同型を実 loop 全図式の関手同型へ回収。
- **残る B**：前段の `commonChosenStageRefinedSourceIso n` と今回の指定構造同型・厳密右射影正方形との整合を実証し、同じ比較を BF 全体の FunctorIso へ接続する。構造同型と各段比較を別々に構成できただけでは、BF 全体の自然同型とは数えない。hΩ・sp_isStable は未提供。
- **元の構造射・実段間全図式比較の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7772 jobs）。新規4葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：541 modules／5861 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉4本・集約・監査・本計画のみを変更。移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：指定射影値を保持する実図式比較の構造自然性
- 段始点比較の内部の標準図式族・実 fiber 比較を `commonChosenStageCanonicalFamily`／`commonChosenStageCanonicalDiagramIso` として公開。既存の始点比較と構造同型の端点正規化を明示し、同じ指定比較を選び直さず照合可能にした。
- `commonChosenStageStructureDiagramIso_projection`／`commonChosenStageCanonicalDiagramIso_target`：同じ構造同型の周囲の四角形への射影は元の指定構造同型、同じ fiber 比較の終点射影は元の厳密等式の同型を回収。
- `commonChosenStageSourceLoopIso_diagram_triangle`／`commonChosenStageRefinedSourceIso_canonical_triangle`：既存の始点 loop 比較と refined／実始点比較を、同じ全図式始点比較・元の右射影の段同型へ指定値を保持して接続する三角形を実証。
- `d3FunctorPostcomposition_evaluate`／`d3FunctorIsoMapPost_evaluate_precomp`：全図式への同型の作用を頂点で評価すると、同じ元の同型への前合成を回収。全単体の厳密交換とホモトピー圏の関手性から指定値を同定。
- `commonChosenStageStructureDiagramIso_corner`／`_source`／`_target`：実全図式の構造同型を四角で評価し、実始点関手・厳密 nativeTail 終点関手に前合成した同じ BF 構造同型そのものとして回収。
- `d3LoopCanonicalDiagramIso_naturality`：元の実 fiber 内比較と、指定終点同型の充満忠実な逆像は、同じ指定全図式同型に厳密に自然。射影後の同型の指定値の回収から、全図式の正方形を反映して証明。
- `commonChosenStageCanonicalStructure_naturality`／`_source`：上記へ既存の BF 構造全図式同型を代入。同じ実段比較・指定構造同型・指定終点の持ち上げが全図式および始点評価で同じ構造正方形を満たす。
- **残る B**：次段 loop 像の図式からの比較と、次段図式比較を通常 loop で写した同じ値との整合を、元の右射影の構造正方形も保持して実証する。その整合から BF 全体の FunctorIso を構成する。今回の全図式正方形だけで BF 全体の自然同型を推論しない。hΩ・sp_isStable は未提供。
- **指定射影値・標準比較の構造自然性の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7842 jobs）。所有変更葉に新しい警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：546 modules／5902 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉5本・所有 D3 葉2本の端点表示整理・集約・監査・本計画のみを変更。移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：次段比較の loop 像と次段像の比較を全図式で接続
- `commonChosenStageLoopedCanonicalSquareFamily`／`_SquareIso`：元の次段の指定図式比較へ同じ通常 loop を後合成し、実次段像との同じ全四角形比較を保持。
- `commonChosenStageLoopedCanonicalSquareFamily_isLoop`／`_Family`／`_DiagramIso`：この同じ像の loop 性を元の実次段像との比較から認証し、実 loop 全図式へ因子化。通常 loop が任意の図式を保存するという新仮定は置かない。
- `commonChosenStageLoopedCanonicalFamily_corner`／`commonChosenStageLoopImageFamily_corner`：二つの全族の各角は元の同じ角へ通常 loop を施した作用に厳密一致。
- `commonChosenStageLoopedCanonicalDiagramIso_projection`／`_corner`／`_target`：充満忠実な逆像の指定値を回収し、各角で元の次段比較の同じ後合成、終点で元の厳密等式の同型を回収。
- `commonChosenStageLoopImageComparison`／`_target`：二つの標準模型を、元の厳密終点を共有する同じ実 fiber 内で比較し、同じ指定等式同型の射影を保持。
- `commonChosenStageLoopImageComparison_triangle`：実次段像からの標準比較は、元の次段比較の loop 像と、保持した標準模型間比較の合成に全図式で一致。終点射影の充満忠実性から反映して証明。
- `commonChosenStageLoopImageComparison_structure`／`_source`：元の BF 構造の自然性を、この同じ三角形へ接続。全図式と始点評価で同じ比較因子を保持。
- **残る B**：保持した標準模型間比較の始点成分を、元の右射影の構造正方形と接続し、refined／実始点比較を BF 全体の FunctorIso へ組む。比較因子を恒等と見なしたり、今回の全図式三角形だけから BF 全体の自然同型を推論しない。hΩ・sp_isStable は未提供。
- **次段 loop 像・標準模型間比較の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7845 jobs）。新規3葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：549 modules／5936 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉3本・集約・監査・本計画のみを変更。移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：指定右射影の構造正方形を全 Hom・全関手空間で認証
- `d3GradedPrecomp`／`d3GradedPostcomp`／`d3GradedComp`：元の単位パラメータの厳密豊穣変換を、全単体の自然性を保持して前後合成・縦合成する。`d3GradedOfEq_component_heq` と各 `_component` は端点正規化・合成で元の通常成分を回収。
- `commonStageLoopGradedProjection`／`commonRefinedStageStructureGraded`／`commonOriginalLoopStructureGraded`：同じ共通右射影、refined 構造、元の次段構造の通常 loop を、括弧と既証の豊穣関手等式だけで同じ端点へ束ねる。各 `_component` で元の指定射を回収。
- `commonProjectionStructureGraded_square`：`commonProjection_structure` を代入し、同じ二経路の厳密豊穣変換の等式を認証。既に全 Hom 自然性を持つ変換どうしを比較しており、点別同型から新たな自然性を推論していない。
- `d3GradedCompositionTriangleFamily`／`_first`／`_second`／`_outer`：既存三段豊穣円柱の同じ実合成三角形を作り、全対象・全高次単体で三辺を元の指定区間族として回収。
- `d3GradedComposition_compStruct`／`d3GradedHom_comp`／`d3GradedHom_functorIso`：同じ三角形を関手空間へ curry し、厳密縦合成の実現がホモトピー圏の合成を保つこと、元の関手同型の順射を回収することを実証。
- `commonProjectionStructureHom_square`：同じ指定右射影の構造正方形は、coherent な全関手空間の実射としても厳密に可換。
- **残る B**：今回の指定厳密変換の実現を、既存の段 FunctorIso の前後合成と同じ値として照合し、保持した模型間比較の始点成分をこの右射影の構造正方形へ接続する。その後 BF 全体の FunctorIso を構成する。hΩ・sp_isStable は未提供。
- **右射影の全 Hom 構造正方形・実合成三角形の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7851 jobs）。新規3葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：555 modules／6010 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉3本・集約・監査・本計画のみを変更。本計画の既存270行を保持し、移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：既存段 FunctorIso の指定値で右射影の構造正方形を回収
- `d3OrderedCylinderMap_family`／`d3GradedPrecomp_family`／`d3GradedPostcomp_family`：元の円柱の順序・Hom を保ち、厳密変換の前後合成の実現が同じ指定区間族の前後合成に全単体で一致。
- `d3GradedHom_precomp_heq`／`_postcomp_heq`／`d3GradedIso_precomp_postcomp_hom_heq`：同じ族を curry して指定辺の類を追跡し、元の関手同型の前後合成の順射を同じ厳密変換の実現として回収。等式だけの端点正規化も指定値を保持。
- `commonStageLoopFunctorIso`／`d3StageStructureFunctorIso` の端点正規化を明示。元の厳密変換からの指定同型を保持し、前後合成後の順射まで照合可能にした。
- `commonStageLoopFunctorIso_hom_heq`／`_postcomp_hom_heq`／`commonRefinedStageStructureIso_hom_heq`／`commonOriginalLoopStructureIso_hom_heq`：既存の段右射影・元の構造同型の同じ前後合成を、前工程の厳密変換の実現値として回収。
- `commonProjectionStructureIso_square`：四辺の端点表示だけを正規化し、元の既存段 FunctorIso そのものによる全関手空間の構造正方形を、`commonProjectionStructureHom_square` から認証。
- **残る B**：この指定右射影の構造正方形と、保持した模型間比較の始点成分を接続し、refined／実始点比較を BF 全体の FunctorIso へ組む。段の同型や今回の構造正方形だけから BF 全体の自然同型を推論しない。hΩ・sp_isStable は未提供。
- **既存段同型の指定値・全関手構造正方形の保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7854 jobs）。所有変更葉に新しい警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：558 modules／6056 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉3本・所有 D3 葉2本の端点表示整理・集約・監査・本計画のみを変更。本計画の既存284行を保持し、移管済み行と既存読み取り専用領域への編集なし。
## 2026-10-27：同じ既存段比較・模型間比較と右射影構造を一体で貼合せ
- `d3LoopCanonicalTransport_section`／`_source_naturality`：指定標準図式 transport は同じ終点同型の厳密切断への後合成に一致。標準始点表示との交換を全関手同型で保持。
- `d3StageStructureTailGraded_eq`／`d3StageStructureTailFunctorIso_eq`：元の同じ構造変換・構造同型は nativeTail 前合成で元の次段構造変換・同型を回収。全 Hom 自然性と指定順射を保持し、円交換因子は比較しない。
- `commonChosenStageStructureDiagramIso_target_next`／`commonChosenStageTargetLoopStructure_square`：実図式の厳密 tail 終点の構造を元の次段構造へ同定し、同じ右射影正方形へ接続。
- `commonChosenStageCanonicalUnit_structure`／`commonChosenStageCanonicalRefinedStructure_square`：同じ標準始点表示と実終点構造の交換を、元の右射影の指定端点で接続する全関手正方形を認証。
- `commonChosenStageRefinedSourceNormalized_triangle`／`_factorization`／`_pasting`：既存 refined／実始点比較を端点だけ正規化し、同じ BF 構造・次段比較の loop 像・保持した模型間比較の始点成分まで一体で貼合せ。段比較や比較因子を選び直さない。
- **残る B**：保持した模型間比較因子を含むこの指定段間貼合せから、BF 全体の全 Hom・全単体整合を持つ実 FunctorIso を構成する。模型比較を恒等と見なしたり、今回の段貼合せ式だけから BF 全体の自然同型を推論しない。hΩ・sp_isStable は未提供。
- **指定段比較・実 tail 終点構造・模型間比較の貼合せの保存検証**：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7863 jobs）。所有変更葉に新しい警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：562 modules／6101 declarations、私有宣言・推移的公理依存を含み標準三公理のみ。ModelCategory 仮定なし、指定未追跡四葉・下流 K 依存は未接続。 所有新葉4本・所有 D3 葉1本の端点表示整理・集約・監査・本計画のみを変更。計画は過去監査欄の所有確認4行を直前の監査行へ併記し、重複空行を整理して299行。移管済み行・移管節・既存読み取り専用領域への編集なし。
## 2026-10-27：指定段比較の構造整合に残る条件を厳密に特定
- `commonChosenStageLoopedCanonicalUnitIso`／`commonChosenStageLoopedRefinedSourceIso`：同じ既存次段比較・標準始点表示の通常 loop 像を、実図式の同じ角へ正規化。
- `commonChosenStageLoopedRefinedSource_triangle`：既存次段の三角形全体を loop で写し、指定右射影・始点表示を同じ値として回収。
- `commonChosenStageLoopModelCorrection`／`commonChosenStageRefinedSource_structure_iff`：既存 refined／実始点段比較の BF 構造可換性と、保持した模型比較から定まる補正同型の恒等性が同値。全関手同型の貼合せと可逆因子の消去で証明。
- **残る B**：この補正同型の恒等性は未証明。同じ段比較を BF 全体へ組むにはこれを実証するか、正しい補正を保持する比較構成が必要。判定定理で自然性を供給したとは扱わず、hΩ・sp_isStable は未提供。
- 保存検証：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7865 jobs）。新規二葉に警告なし。 `lake env lean scripts/audit_kst_spectra_d3.lean` 合格：564 modules／6119 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。 所有新葉二本・集約・監査・本計画のみを変更。過去節の空行を整理し298行。移管済み全行・凍結転記節を保持。
## 2026-10-27：模型補正を保つ実構造不一致の回収と、貼合せのみからの推論の排除
- `d3PastingRelations_structureCounterexample`：Bool の交換同型により、既証と同形の二つの貼合せが成立し、構造正方形と補正の恒等性は共に失敗する具体例を証明。一般の同型代数の反例であり、実 Sp の補正が非恒等という主張ではない。
- **次の実証対象**：実 loop 図式に由来する `commonChosenStageLoopedCanonicalUnitIso n ≪≫ (commonChosenStageLoopImageComparison n).postcomp (loopDiagramEvaluation PointedKanInfinity 0 0) = commonChosenStageCanonicalImageUnitIso n`。既存の貼合せ式だけを追加変形する経路では閉じない。実図式の追加証拠か、正しい補正を保つ BF 比較の構成が必要。A/B・hΩ・sp_isStable の完了とは数えない。
- `commonChosenStageRefinedSource_structure_defect`：実段比較の構造不一致は、同じ右射影で移した模型補正の逆を挿入した値に厳密一致。新仮定なし。補正を通常 loop 以前の段比較へ持ち上げる証拠と全段整合は未提供。
- 保存検証：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7867 jobs）。新規二葉に警告なし。 専用監査合格：566 modules／6127 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有5ファイルのみ変更。本計画300行、移管済み全行・凍結転記節は保持。
## 2026-10-27：実 loop 全図式の転置から nativeLoop の coherent な反転候補を構成
- `d3LoopDiagramTranspose`／`_corner`／`_comp_self`：全四角形の転置を実 loop 全図式へ制限。零角と引き戻し性を保持し、四隅の厳密交換と二回合成の恒等を全単体で証明。
- `d3LoopDiagramTransposeIso`／`_reverse`：厳密終点を固定した同じ指定比較と、その転置から戻した比較が全図式上で互いに逆。終点評価の充満忠実性で指定値を認証。
- `d3LoopDiagramReflection`／`_involution`／`_naturality`：始点評価の全関手自己同型、二回合成の恒等、任意の全図式同型との自然性を証明。円因子の直接比較や安定性仮定は使わない。
- `OmegaSpectrum.d3NativeLoopReflection`／`_involution`、`commonChosenLoopReflection_native_square`：元の実切断へ適用し、nativeLoop の全関手自己同型と共通実全図式との指定比較での交換を実構成。段ごとの自由な選択ではない。
- `d3LoopImageTransposeIso_projection`／`_eq`・`commonChosenStageReflectionImageIso_eq`：元の実全図式の指定転置比較の段像は、同じ実段図式の指定転置比較そのもの。周囲の全四角形では元の指定比較の同じ後合成を回収。任意関手の極限保存を仮定しない。
- **残る B**：全体反転と段転置比較の照合は得たが、保持した `commonChosenStageLoopModelCorrection` に必要な補正との一致・全段整合は未証明。BF 全体の比較が完成したとは扱わない。d3c・d3d は Sp-2b へ移管。
- 保存検証：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7872 jobs）。新規五葉に警告なし。
- 専用監査合格：571 modules／6176 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有8ファイルのみ変更。過去検証欄を併記して本計画300行、s3・s5 行を保持し d3c・d3d 移管を明記。
## 2026-10-27：Sp-2b への d3c・d3d 移管と B の受け渡し型
- `OmegaSpectrum.AdjointLoopRelativeBF.NativeLoopComparison := FunctorIso (coherentNerveMap commonRefinedEnriched) (commonNativeLoopEndpoint ≫ nativeLoop)`。Sp-2b の指定受取型に一致。ユーザー経由で報告済み。型名の公開は B の実値の供給ではない。
- `ChosenLoopSourceComparison := FunctorIso (coherentNerveMap commonRefinedEnriched) commonChosenLoopSource` から `nativeLoopComparisonOfChosenSource` が既存 `commonChosenLoopSourceNativeIso` と合成して同じ受取型へ送る。専用葉ビルド合格。元の全実 loop 図式と厳密 tail 終点は既存族に保持し、未証明の始点比較・構造補正は解決済みとしない。B 本体を継続する。

## 2026-10-27：実反転の始点・次段 loop 像・BF 構造の指定値を接続
- `d3LoopImageTransposeIso_corner`／`d3LoopReflectionImage_source`：元の実全図式の指定転置比較を各角まで回収し、同じ始点反転の後合成が像側の始点反転そのものとなることを証明。全パラメータの像だけを用いる。
- `commonChosenStageReflection_global`：nativeLoop と比較される元の共通全体反転を段評価した指定値は、実段図式の反転に厳密一致。
- `commonChosenStageImageReflection_loop`／`commonChosenStageReflection_structure`：同じ次段反転の通常 loop 像を元の実次段像で回収し、元の BF 構造射に対する全関手正方形を認証。`_involution` は同じ段反転の二回合成の恒等を供給。
- **残る B**：実反転候補の構造整合は得た。保持した `commonChosenStageLoopModelCorrection` と、この反転を用いた必要な補正との一致は未証明。その一致と比較射の全 Hom・全単体整合から B の実値を構成する。出力型や今回の反転の構造正方形を B の値として代用しない。d3c・d3d は Sp-2b 担当。
- 保存検証：`lake build SerrePositivity.KST.Spectra.D3All` 合格（7874 jobs）。新規二葉に警告なし。 専用監査合格：573 modules／6190 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有5ファイルのみ変更。過去検証欄を併記し本計画300行。移管済み全行・凍結転記節を保持。

## 2026-10-27：保持した模型比較の始域を全四角形として転置
- `commonChosenStageLoopReflectedComparison`：元の looped canonical 全図式の転置から、同じ canonical image 全図式への実比較を構成。指定転置比較の逆と保持した元の比較の合成であり、始点だけの自由な補正ではない。
- `_target_eq`／`_target`：転置後も元の実次段 loop 像と厳密終点が一致し、比較の終点成分は等式由来の指定同型。`_recover` は元の保持済み模型比較を全図式の合成から厳密回収。
- `_source`：転置済み比較の始点は、同じ全図式反転の逆と元の始点比較の合成そのもの。全関手空間で証明し、点ごとの成分の一致で代用しない。
- **残る B**：転置済み比較と元の looped unit・canonical image unit の整合は未証明。保持した模型補正と反転との一致、および BF 比較の全 Hom・全単体整合を引き続き実証する。今回の全図式候補を B の実値とは扱わない。
- 保存検証：D3All ビルド合格（7875 jobs）、新規葉に警告なし。専用監査合格：574 modules／6212 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有4ファイルのみ変更。過去検証見出し7行を本文へ併記し本計画300行、移管済み行・凍結転記節を保持。

## 2026-10-27：実反転を奇数段に保持する段比較と構造条件の接続
- `commonChosenStageLoopReflectedSourceIso`／`_eq`：転置済み全図式比較の始点を元の端点へ正規化し、元の反転の逆と保持した模型比較の合成を指定値として回収。
- `commonChosenStageRefinedSource_reflected_structure_iff`：転置模型の単位三角形と、同じ既存段比較に実次段像の反転を保持した構造正方形が同値。全図式反転の自然性と二回合成の恒等を既証貼合せへ実適用。
- `commonChosenStageAlternatingSourceIso`／`commonChosenStageAlternatingLoopSourceIso`：偶数段は同じ既存段比較、奇数段は同じ実反転を合成した全関手同型を構成。`_eq` は実際の次段比較の通常 loop 像を同じ実像上で回収。
- `commonChosenStageAlternatingSource_structure_iff`：構成した段比較と同じ次段比較の loop 像の構造可換性は、各段で転置模型の同じ単位三角形と同値。三角形そのもの、および BF 全体への全 Hom・全単体整合は未証明。判定定理を B の実値や新しい最終仮定として扱わない。
- 保存検証：D3All ビルド合格（7877 jobs）、新規二葉に警告なし。専用監査合格：576 modules／6232 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有5ファイルのみ変更。過去検証見出し7行を本文へ併記し本計画300行、移管済み行・凍結転記節を保持。

## 2026-10-27：二つの実端点四角形を全 Hom 上の四次元図式へ束ねる
- `d3TensorParameter`／`d3TensorParameterDiagram`：二つの実逆向き図式の制限射を同じ積順序上でテンソルし、元の全 Kan Hom と同時評価。`d3PointedKanParameterDiagram_reindex` は任意の単調な制限で指定全 Hom を厳密回収。
- `d3DoubleEndpointSquare`／`d3PointedKanBiParameterSquare_corner`：元の二つの端点四角形を全単体の実四次元図式族にし、16 個の角の全関手作用を同じテンソルパラメータの内部 Hom 作用として厳密回収。
- `d3PointedKanBiParameterSquare_left`／`_right`：一方の四角形を任意の角に固定した各二次元面は、元の実パラメータ図式の制限族に全 Hom・全単体で厳密一致。`d3DoubleEndpointTargetIso`／`LeftLoopIso`／`RightLoopIso` は外側の三角を元の恒等作用・通常 loop 作用へ全関手比較。
- **残る B**：二方向の基礎図式と外側境界までを構成。内側の極限認証・二方向 loop 表示と既存模型比較の全図式照合、および転置模型の単位三角形は未証明。四次元図式や外側境界の比較だけから単位整合・BF 全体比較を結論しない。円交換因子の直接比較・禁止枝の接続なし。
- 保存検証：D3All ビルド合格（7881 jobs）、新規四葉に警告なし。専用監査合格：580 modules／6284 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有7ファイルのみ変更。過去検証4組を併記し空行3行を整理して本計画300行、移管済み行・凍結転記節を保持。

## 2026-10-27：二方向の実面の極限・零角と実 loop 全図式族
- `d3ParameterSquare_isPullback`：同じ実パラメータ pushout と端点射の単射性から、反変写像空間の極限保存・全 Hom 錐・元の二三角形を通じ、同じ coherent 四角形の ∞ pullback 性を認証する。
- `d3DoubleEndpointSquare_left_isPullback`／`_right_isPullback`：元の端点 pushout の左右テンソル保存と実単射を代入し、二つの四角形方向の各4面を実認証。一般 pushout や fibration 性を未供給入力に残さない。
- `d3PointedKanTensorPoint_isZero`／`TensorPath_isZero`／`PointTensor_isZero`／`PathTensor_isZero`：通常閉圏の対象同型と既証の point・based path 零性から、同じ実テンソルパラメータの零角を認証。対象同型から全関手自然性は推論せず、円交換因子の直接比較も行わない。
- `d3DoubleEndpointLeftLoopFamily`／`d3DoubleEndpointRightLoopFamily`：同じ四次元全図式の各面を全 Hom・全単体の作用を変更せず loopDiagrams へ因子化。各 `_ι`／`_corner` は元の実面全体と元の各角の全関手作用を厳密回収。
- **残る B と申告**：既存の looped canonical／canonical image への指定単位を保つ全図式比較、保持した模型補正と必要な補正の一致、BF 比較の全 Hom・全単体整合が未完。残工数は粗く18〜40時間（模型照合3〜7、補正一致6〜12、BF 整合8〜18、接続監査1〜3）。経路不成立のリスクは中〜高。代替は実比較射・実 loop 図式・厳密終点を同時保持する共通解像の相対 Hom RLP から直接 B を組む経路（追加12〜24時間）。ユーザーへチャットで申告済み。
- 保存検証：D3All ビルド合格（7885 jobs）、新規四葉に警告なし。専用監査合格：584 modules／6345 declarations、標準三公理のみ。ModelCategory・指定未追跡四葉・下流 K 依存なし。所有7ファイルのみ変更。過去節間の空行8行を整理し本計画300行、移管済み行・凍結転記節を保持。
