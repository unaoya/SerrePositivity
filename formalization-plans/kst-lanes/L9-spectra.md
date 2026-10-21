# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-21）

### 現在地
- **K-8 再スコープ（コーディネータ決定）**：(a)〜(c) と、q ⊣ v（v 充満忠実）の場合の (d)③・④は完成。元の laxDifference ⊣ fromD∘v、商の全関手 ∞ 圏上の普遍性、局所化不変量の実 fiber 列・積比較・全整数長完全列を保存済み。d7（一般の Verdier 商の抽象構成）は今回の検証済み区切りで停止し、補助成果として保持する。任意辺集合の実 quasicategory 局所化と普遍性、商候補の pointed 性・真の核、普遍 Ore 族、分母上の元の span 輸送の亜群化の同値性まで検証済み。一般商の安定性・完全性、分数写像空間比較の同値性は未証明で、主経路では要求しない。B 案の商の供給は D の β3、gluing との比較は β4 に委ねる。d8 は IsVerdierSequence を仮定入力とする laxQuotientFiberTriangle の実 fiber 性、元の包含・商の辺、laxQuotientFiberMiddleIso による実積への中項比較と右辺・二軸の整合、全整数長完全列を検証済み。既存の充満忠実右随伴の場合との一致も証明済み。tammeProjectionEquivalence は元の両射影を順方向に持つ新しい実積同値で、第一・第二射影と両包含の整合を証明した。laxQuotientProjectionMiddleIso と ProjectionDifferenceHom はこの比較による元の包含・商・両射影を保つ界面。以前の比較との差は tammeProjectionCorrection で明示し、両軸と右辺の整合を保持する。laxQuotientProductMap は実積から E(Q) への BF 射で、laxQuotientProductFiberSquare は中項・右項が指定対象の実 fiber 四角形。その全図式から元の Verdier 像への同型と、E(A) と標準 homotopyFiber の実同値を構成した。右辺の区間関手同型と全四角形の比較は指定した中項・右項の成分を保持し、その自然性から元の包含と両 lax 射影の二脚を同時に回収した。laxQuotientProductInclusion は元の二脚を組にした実 BF 射で、左項・中項の同型を通した下辺の類に等しく、laxQuotientProductMap との合成は h Sp で零。入力安定圏の SuspensionExact.map は完全な実 ∞ 関手で、F3 の標準 suspension 自己同値と全関手同型により一致し、equivalence・inverseExactMap を持つ。一般商 Q の二脚 laxQuotientCLeg := fromC≫r≫Σ_Q⁻¹、laxQuotientDLeg := fromD≫r を明示し、差の C 軸は E(CLeg) の後の E(Σ_Q)、D 軸は E(DLeg) と証明した。r が元の cofiber 差の場合の二脚は元の p,q に全関手同型で戻る。suspension_pi_inv は E(Σ_Q)(a)=a⁻¹ を全整数 π で証明し、laxQuotientProductMap_pi_formula は元の一般商の実 BF 差の作用を C 脚の逆元と D 脚の積に同定する。元の包含の二脚は各整数 π で可換する。D 随伴余単位の cofiber 全族は cofiber_fromCIso により元の laxFst の後の C 包含と全関手同型となる。さらに元の cofiber 右辺 rightHom の第一射影を反転し、rightCompatibleFromCIso を構成した。rightCompatibleFromCIso_right は、この同型で元の右辺を写すと C 随伴の単位になることを全関手圏の射の等式として保持する。元の包含で制限して商へ写した cofiber を零終点 cofiber と比較し、laxQuotientLegsIso は元の二脚の全関手同型、valueMap_laxQuotientLegs_comm は値の h Sp の可換式を与える。LaxQuotientSquare.square は四辺が元の BF 射となる可換実現、cone は元の E(A) を頂点とする候補の実錐。h Sp の可換式から任意に選び直した正方形の極限性は従わず、商での元の cofiber 全図式比較は quotientDiagramComparison により構成し、底辺で恒等となること、右辺の自然性とその始点の恒等性を保持した。quotientOriginalRightImage_arrow はその右辺を元の指定右辺の像に同定し、quotientOriginalRightImage_unit は C 単位の像への合成式を保持する。quotientSelectedCIso_right は選択された cofiber の指定右辺が C 単位の像になる式を保持する。零終点 cofiber の全族を suspension 図式圏へ入れ、zeroTargetDiagramComparison は同じ始点で恒等となる全図式比較、laxQuotientRelativeLegsIso はこれと C 比較からの二脚の同型。exactMapPinchedPath・exactMapComparisonTriangle と指定二単体を保つ三次元の対角移送から LaxQuotientRelativeSquare.square を構成し、valueSquare はその E の像を同じ両三角形ごと保持する。始域の二辺は E(i≫fst), E(i≫snd) であり、元の BF 合成射との比較と元の product fiber との整合・実 pullback の極限性は未証明。これを完成後に pro 版へ進む。
- **K-5 抽象部分へ移行（ユーザー指示）**：安定 ∞ 圏・完全関手、抽象 Verdier 列、Sp 値の局所化不変量と基本補題を担当する。K-S• の SConstruction と D の Stable/・Drinfeld 商は読み取り専用。以下の K-5 節に界面と残工程を固定する。
- K-5：安定 ∞ 圏・完全関手の ∞ 圏、抽象 Verdier 列・四角形提示、Sp 値局所化不変量、その像の実 fiber 性と整数 π 同値検出は完成。BF fiber 四角形の下辺と元の包含の類、h Sp 上の π 関手と元の BF π の自然比較、任意の fiber 四角形の三対象と二辺の同時比較を構成済み。今回、任意の Sp fiber 四角形の全整数次数の接続射と三箇所の完全性を証明し、任意抽象 Verdier 列の元の値の群・包含・商への長完全列まで移送した。端の値の全整数 π 消滅から元の像の辺の同値性も得た。coherent な切断付き fiber 列の実 Sp 積同値も完成し、任意の fiber 四角形・抽象 Verdier 列の像へ移送した。実 ∞ 積錐、元の fiber・底から積因子への同値、元の包含・切断・射影との h Sp での整合性を全て保持する。K-5 の抽象部分は完成。
- K-5 の今回の検証：専用対象5687 jobs、59モジュール・719宣言の専用公理監査、全体19210 jobs が終了コード0。標準三公理のみ、宣言型の ModelCategory 検査と diff --check も成功。
- **優先順を変更（ユーザー指示）**：d1 整数次数による同値検出 → d2 値域界面の固定。IsStable は I-b 末尾へ延期。evaluationPost circle と逆関手経路は再開しない。停止中の4 WIP は保持する。
- L9a・L9b・改訂 L9c・L9d・L9e 完了。骨格の成分・高次係数表示、微分の符号と核・像、Milnor の全整数次数界面と lim¹、Mittag–Leffler 収束、有理有限群の標準 Shapiro 同型、通常 Tot・BF・元の homotopy Tot の比較まで完了。
- Sp の零対象、小積、任意の coherent cospan、通常の小圏上の BF 図式の ∞ 極限、元の hG/Tot の実際の ∞ 極限錐、任意射の fiber と整数 π の長完全列は完成。
- nativeTailEquivalence は完成。nativeLoop は全単体上の関手で、実 loop 四角形・円 cotensor との関手同型・対象ごとの tail との両合成の同型・本質的全射性は完成。nativeLoop の完全忠実性と ∞ 圏同値性は未証明。
- d1 の証明を完成：標準整数 π の同型性を任意段の標準基点へ移し、path fiber の任意基点での五項比較から点つき Kan 複体間の loop 射の全基点同型性を得て、構造随伴の厳密な自然性で各段の全基点へ戻した。PiIsomorphism と全段 KanPiIsomorphism の同値、元の BF 射と任意の Sp の一単体の可逆性を証明。対象・集約ビルドと専用監査まで成功。
- d2：下表を K-S• の K-5〜K-8 が使う Sp 値域界面の正本とする。提供済み行だけを無条件に使用し、未提供行を入力公理・追加 instance で埋めない。Sp の安定性・一般の完全関手 API は I-b 末尾まで要求しない。
- 今回の検証：対象・集約 6617 jobs、監査 1446 モジュール・13123 宣言、標準三公理のみ。ともに終了コード 0、宣言型の ModelCategory 検査も成功。全体 19003 jobs も終了コード 0。全体 diff --check も成功。

### 残り（依存順）
- K-8：d7 は補助成果として停止。d8 は安定 Q と IsVerdierSequence (i : A → laxCategory p q) (r : laxCategory p q → Q) を入力に、局所化不変量の像の実 fiber 列、中項 E(C)×E(D) への同定と E(A) ≃ E(C)×_{E(Q)}E(D) を構成する（Tamme Thm. 18、Land–Tamme §1–2）。Q と ⊙ の同定は β3・β4 後に行い、ここでは仮定のまま。続く pro 版は pro 値・pro 零性・pro fiber 列の最小形式と、Tor の pro 消滅から pro 切除への抽象的接続（foundations.md §1）。d8 の積を介した実 pullback 比較と pro 接続は未実装、暫定複数日・上限未見積もり。
- d1 完了：PiIsomorphism と全段・全基点 KanPiIsomorphism の同値と、任意の Sp の一単体の同値検出を検証済み。BF §2、Goerss–Jardine I §§7–8。
- d2 の宣言表固定は完了。未提供行の実装は今回の宣言表固定とは別の後続項目。任意 coherent 極限・全有限極限の一般界面は F1b/F2 の既存 HasColimit から Sp へ接続する（HTT 4.2.4.1、規模未再見積もり）。一般 γ4 の完成待ちや再実装へ戻らない。
- d3：IsStable は I-b 末尾。d1・d2 の固定と他の優先項目の消化後だけ、旧経路の六段階を再開する。HA §1.4.2、従前 24–48 時間以上（上限保証なし）。現時点では着手しない。

### 主要宣言：Sp 値域界面（共通接頭辞 SerrePositivity.KST.Spectra）

| 項目 | 宣言 | 型・範囲・状態 |
| --- | --- | --- |
| 値域 | Sp、sp_quasicategory | BF Ω スペクトルの coherent nerve。宇宙 u の BF 対象から SSet.{u+1}。提供済み |
| 零対象 | OmegaSpectrum.pointZeroVertex、OmegaSpectrum.sp_hasZeroVertex、OmegaSpectrum.functorZeroVertex | Sp と任意 Fun(K,Sp) の実零対象。提供済み |
| 小積（有限積を含む） | OmegaSpectrum.SmallProduct.obj、projection、infinityCone、infinityCone_isLimit | S : Type u の族、Discrete S の元の錐の IsLimitCone。提供済み |
| cospan・pullback | OmegaSpectrum.CoherentPullback.infinityCone、infinityCone_isLimit、hasLimit | p : horn 2 2 → Sp に HasLimit p。任意の coherent cospan。提供済み |
| 通常の一般小図式 | OmegaSpectrum.homotopyLimitCoherentCone、homotopyLimitCoherentCone_isLimit、strictCoherentDiagram_hasLimit | I : Type u、SmallCategory I、D : I ⥤ OmegaSpectrum に HasLimit (strictCoherentDiagram D)。提供済み。任意の coherent 図式と混同しない |
| fiber 列 | OmegaSpectrum.sp_fiber_exists、fiberSquare、homotopyFiber、homotopyFiberInclusion | 任意の Sp の辺の実 fiber 四角形、および実 BF 射の指定 fiber。提供済み |
| 整数 π と長完全列 | OmegaSpectrum.homotopyGroup、homotopyMap、homotopyGroupEquivAt、homotopyFiberBoundary、homotopyFiberLongExact | j : ℤ の可換群と実 BF 射への作用、全整数次数の三箇所の完全性。提供済み |
| 有限極限全体 | 予定 OmegaSpectrum.sp_hasFiniteLimits | HasFiniteLimits Sp（全有限 K : SSet.{u+1} と任意 p : K → Sp）。有限形状の小宇宙への縮小・錐の移送を含む一般の包装は未提供。提供済みの積・cospan を使用し、一般 coherent 図式の極限の接続後に供給する |
| 同値検出（d1） | OmegaSpectrum.PiIsomorphism.levelwise、piIsomorphism_iff_levelwise、isInvertible_of_piIsomorphism、spEdge_isInvertible_of_piIsomorphism | 標準整数 π 同型 ⇒ 各段の全基点 π 同型 ⇒ 元の Sp の辺の可逆性。対象・集約・専用監査成功、提供済み |
| tail の同値 | OmegaSpectrum.nativeTail、nativeTailEquivalence | 元の全単体上の関手を順方向に持つ QCatEquivalence Sp Sp。提供済み |
| Ω と tail の比較 | OmegaSpectrum.nativeLoop、nativeLoopCircleFunctorIso、nativeLoopTailVertexIso、nativeTailLoopVertexIso、nativeLoop_essentiallySurjective、予定 nativeLoopEquivalence・nativeLoopTailFunctorIso・nativeTailLoopFunctorIso | Ω の実関手と対象ごとの比較は提供済み。QCatEquivalence Sp Sp（hom = nativeLoop）と両合成から恒等関手への FunctorIso は未提供・I-b 末尾。K-5〜K-8 はその完成を先取りしない |
| 任意の coherent 図式の極限 | F2.hasColimit_coherentSpaceDiagram、F2.coherentDiagramTotalCocone_isColimit（InfinityCategories.F2 集約）、予定 OmegaSpectrum.coherentDiagram_hasLimit | F1b の空間値 HasColimit（B : SSet.{u}、ulift B → SpaceInfinity.{u}）を読み取り専用で使用。Sp の任意 D : ulift B → Sp の HasLimit への移送は未提供。空間の HasColimit だけを Sp の HasLimit と主張しない |
| 安定性 | 予定 sp_isStable | IsStable Sp は未提供。I-b 末尾の d3。K-5〜K-8 の現段階の前提にしない |

### 主要宣言：一般局所化・補助成果（共通接頭辞 KST.LocalizingInvariants）
- F1b の B2 が残した任意辺集合の一般局所化の存在を提供：edgeLocalization、edgeLocalizationMap、edgeLocalization_quasicategory、edgeLocalization_isLocalization、edgeLocalization_universal。元の単体集合と辺集合から同宇宙の実 quasicategory と全関手 ∞ 圏の局所化普遍性を構成する。
- 商候補：tammeQuotient、tammeQuotientMap、tammeQuotientComparisonIso、tammeQuotient_hasZeroVertex、tammeQuotientMap_kernel、tammeQuotientMap_invertedEdges。一般の安定性・完全性は提供しない。
- Ore 族：tammeLocalizingEdges_rightOre_pullback、tammeOreProjection_trivialKanFibration、exists_relative_tammeOreFamily、tammeOreFamilySpace_isContractibleKan、exists_tammeOreCartesianSpanLift。
- 分母上の補助比較：tammeDenominatorFixedSpanGroupoidEquivalence、tammeDenominatorSpanTransport_groupoidCompletion_isEquivalence。局所化後の写像空間との比較の同値性は未提供。
- d8 の提供済み界面：laxQuotientVerdierSequence、IsLocalizingInvariant.laxQuotientFiberTriangle・laxQuotientFiberTriangle_isFiber・laxQuotientFiberMiddleIso・laxQuotientFiberMiddleIso_right・laxQuotientDifferenceHom、laxQuotientConnecting と全整数三箇所の完全性、laxQuotientVerdierSequence_reflective と3つの値の整合式。Q と IsVerdierSequence は明示的な入力。実 pullback 比較は未提供。 追加：laxValueProjectionHom、IsLocalizingInvariant.tammeProjectionEquivalence（両射影・両包含を保持）、laxQuotientProjectionMiddleIso・laxQuotientProjectionDifferenceHom、tammeProjectionCorrection と対応する整合式。 laxQuotientProductMap・laxQuotientProductMap_right_comm、laxQuotientProductArrowIso_source/target、laxQuotientProductFiberSquare・laxQuotientProductFiberComparison・laxQuotientProductFiberEdge_right、laxQuotientProductFiber_middle_vertex/right_vertex・laxQuotientProductFiberLeftIso、laxQuotientHomotopyFiberValueIso。一般補題 exists_arrowFunctorIso_with_endpoints・exists_fiberSquare_right_transport。 laxQuotientProductFiberComparison_middle/right・laxQuotientProductFiberComparison_bottom・laxQuotientProductFiber_bottom_fst/snd、laxQuotientProductInclusion・laxQuotientProductFiber_bottom_map/right_map・laxQuotientProductInclusion_comp_map。 SuspensionExact.map・map_isExact・exactMap・exactNaturality・diagrams・canonicalIso・equivalence・inverseExactMap、cofiberZeroTargetIso・fromC_differenceIso、valueMap_fromC_difference/fromD_difference、laxQuotientCLeg・laxQuotientDLeg・laxQuotientCLeg_suspensionIso、laxQuotientProjectionDifferenceHom_shift_C/D、laxQuotientCLeg_cofiberIso・laxQuotientDLeg_cofiberIso と値の二脚の一致。 IdentityLax.diagonal・exactDiagonal・difference_diagonal_zero・productDiagonal_difference_zero、IsLocalizingInvariant.suspension_pi_inv・laxQuotientProductMap_pi_C/D・laxQuotientProductMap_pi_formula・laxQuotientLegs_pi_commute、CofiberFamily.familyExactComparison、LaxCounit.arrow・arrow_source/target・cofiber・cofiber_fstIso・counit_snd_isIso・cofiber_snd_zero、counit_postcompRight_isIso。 isInvertibleEdge_of_initialBoundaries/terminalBoundaries、LaxCounit.fromC_unit_component_isIso・cofiber_unitIso・cofiber_fromCIso、CofiberFamily.precompositionIso、LaxCounit.quotientArrow・quotientCofiberComparison・quotientCofiber_CIso・quotientCofiber_DSuspIso、laxQuotientLegsIso・valueMap_laxQuotientLegs_comm、LaxQuotientSquare.square・square_bottom/top/left/right・cospan・cone・cospan_C/D・cone_vertex（候補錐、極限性は未提供）。 arrowFamilyHomotopy・arrowFamilyHomotopy_roundTrip・arrowFamilyHomotopy_vertex_edge、CofiberFamily.rightArrow・rightHomotopy・rightHom・rightHomotopy_vertex_edge・rightHom_post_isIso_of_zeroSource、homPost_homPre_exchange・identityHom_exchange_comp、LaxCounit.rightHom・rightHom_fst_isIso・rightFstIso・rightCompatibleFromCIso・rightHom_unit_naturality・rightCompatibleFromCIso_right。 CofiberDiagrams.relativeComparison・relativeSquareComparison・relativeComparison_bottom_arrow・relativeComparison_right_naturality・relativeComparison_rightSource_arrow、arrowFamilyHom・arrowFamilyHom_precomp/postcomp・arrowFamilyHom_naturality、LaxCounit.quotientOriginalDiagrams・quotientOriginalDiagrams_bottom/squares/right/cofiber・quotientDiagramComparison・quotientDiagramComparison_bottom_arrow・quotientSquareComparison・quotientRightComparison_naturality・quotientRightSourceComparison_arrow・quotientCofiberRelativeIso・quotientOriginalRightImage・quotientOriginalCImage・quotientCUnitImage・quotientOriginalRightImage_unit・quotientSelectedCIso・quotientOriginalRightImage_arrow。 quotientSelectedRight・quotientSelectedRight_relative_arrow・quotientSelectedCIso_right、CofiberFamily.zeroTargetDiagrams・zeroTargetDiagramComparison・zeroTargetDiagramComparison_source_arrow・zeroTargetRelativeIso、laxQuotientRelativeLegsIso、exactMapCoreEdge・exactMapCoreEdge_hom・exactMapPinchedPath・exactMapComparisonTriangle、CompositionDiagonalTransport・compositionDiagonalTransport・CompositionDiagonalTransport.triangle、PathComparisonSquare.square・square_upper/lower、LaxQuotientRelativeSquare.square・square_bottom/right/left/top・square_upper/lower・valueSquare・valueSquare_bottom/right/left/top・valueSquare_upper/lower。

### 依存と提供
- Mathlib・既存 Spectra/・HomotopicalAlgebra/Simplicial/・InfinityCategories/ は読み取り専用。F2N-1 は中止し、F2・F1B には書き込まない。削除指定の旧3ファイルに未コミットの残存はない（2つは不存在、RelativeFunctorCurryIsoPointComparison は 17afc3366 で保存済みのため保持）。型の正本は Lean、運用は foundations.md §8。
- γ1 は coherent nerve の quasicategory 性、F0 は同値と極限の普遍性を供給。任意 coherent 図式の極限の次の入口は F1b/F2 の上記 HasColimit とする。
- K-S• の K-5（局所化不変量の定義）・K-6（Verdier 列の fiber 性）・K-7（BGT 非連結化）・K-8（Tamme・Land–Tamme）は上表の界面だけを使う。BF の符号・厳密化・evaluationPost の内部へ依存しない。K-7 に必要な一般 coherent 極限は未提供行の移送の完成後に消費する。
- 外部提供は零・実極限錐・実 fiber と整数長完全列・同値検出、および既存の有理化・Tot・hG・骨格障害計算。局所化不変量の定義・K の合流そのものは K-基盤所有。

### 未コミット
- 停止中の未追跡 WIP：PointedUncurryActionTensor.lean、PointedParametricUncurryAction.lean、PointedUncurryComposition.lean、PointedParametricUncurryPre.lean。集約・監査に接続しない。前二つは単体ビルド成功、Composition は失敗、Pre は未検証のまま保持。
- K-5 と K-8 の330モジュールを接続。今回の保存対象は FunctorHomArrowTransport・LaxCounitSelectedRightCompatibility・CofiberZeroTargetDiagrams・LaxQuotientRelativeLegComparison・ExactMapPinchedPath・CompositionDiagonalTransport・PathComparisonSquare・LaxQuotientRelativeSquare、端点輸送を明示した既存2ファイル、専用集約・監査・本計画。検証後に所有ファイルだけを保存し、停止中4 WIP と他レーンの差分は保持する。d7 は再開しない。

### 既知の問題
- LaxQuotientSquare.square と cone は四辺固定の可換実現であり、h Sp の可換式から選び直した候補。特定のこの錐が極限であるとは未証明で、四辺や整数 π の可換性だけからは従わない。元の cofiber・fiber 図式の二次の整合を保持した比較を構成し、必要なら候補の実現を置き換える。
- Sp の IsStable、Ω の完全忠実性・関手同値、任意の coherent 図式への極限の移送は未完。いずれも上表で未提供と明記し、存在を仮定する構造体で完成扱いにしない。
- **逆関手案の再評価（2026-10-21、今回の評価を1時間以内に記録）**：残る正確な旧経路の十分補題は、任意の BF 対象 X,Y に対し `A := sourceMap CirclePower.space X Y`、`e := tracedOriginalLoopModelMap X` と置いたときの `H : SSet.Homotopy (A ≫ signedEvaluationAt X Y e).right (kanAdjointTracedUnitFamily X Y A).right` の構成。これを evaluationPost_circle_piIsomorphism_of_raw_traced_homotopy に渡す。旧経路の残りは直下の6工程、従前の暫定見積もり24–48時間以上（上限保証なし）。代替の残りは①全有限形状・宇宙を含む HasFiniteLimits Sp の包装、②BF 置換後の厳密な豊穣 Ω と構造随伴の全 Hom 自然性、③両合成の FunctorIso と nativeLoop との比較から元の Ω の QCatEquivalence を組立、④一般安定性判定を Spectra 配下で自前証明、の4工程。①・③も未実装、②・④の上限は未見積もりで、総計は少なくとも複数日という暫定評価。②の入力を既存の対象ごとの同型で代用できない：ordinaryStructureAdjoint_comm_iff は二重随伴 b の `b ≫ swap = b` を要求し、ordinaryStructureAdjoint_comm_forces_swap_piZero はその等式と Ω 条件から円交換の π₀ 作用が恒等となることを証明する。Ω 条件が与える b の全基点 π 同型性だけでは、その交換不変性は得られない。また段ごとの内部 Hom 列には BF の構造射の単射性を回復する置換が入り、cotensorPost は選んだ持ち上げであって厳密な恒等・合成則を備えた豊穣関手として未提供。nativeLoop は loop 図式評価の切断から得た ∞ 関手で、厳密な BF 豊穣関手そのものではない。originalLoopModelMap_natural_component は各段の点つき写像空間の π₀ の自然性まで。随伴が直接与える候補の向きは id ⇒ Ω∘tail（交換・移送ができれば tail∘Ω にも同じ向き）で、要求の tail∘Ω ⇒ id は可逆化後に作る。移送には既存の StrictEnrichedTransformation.functorIso と homotopy_component が使えるため N への追加 API 要求はない。④の正確な目標は `[Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]`、`s : X ⟶ loopDiagrams X`、`hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X`、`hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)` から `IsStable X`。F3 の既存判定は有限余極限と双カルテジアン判定も入力するため使えない。[HA Cor. 1.4.2.27](https://www.math.ias.edu/~lurie/papers/HA.pdf) の原証明は Prop. 1.4.2.24 の spectrum-object 塔と Cor. 1.4.2.17 の安定性を経由し、これらの一般構成は既存 BF の tail 同値では代用できない。有限余極限・cofiber の存在と任意 ZeroTriangle の fiber/cofiber 同値を実際に導出する必要がある。Stable/ は編集せず、D 計画の既存要求は後の取り込み先として保持する。結論：提示された厳密自然変換の前提が未構成で、旧経路より短いとは判定できないため切り替えない。今回 evaluationPost の計算も再開しない。根拠となる OrdinaryLoopAdjointStructureCriterion・StrictEnrichedTransformationNerve の対象ビルドは2008 jobs・終了コード0、diff --check も成功。今回は計画のみの変更で Lean 宣言の追加はない。
- d3 の保留位置：①全族正方形の uncurry・評価への移送、②元の自然性・逆三角形との境界照合、③主構造正方形（左 kanAdjointTracedStructureInterval、右 tracedSourceUnitStructureInterval）、④SpecifiedCodifference、⑤標的単位との貼合せ、⑥自由 cotensor・相対 StrictInterval による raw 全 Hom H を evaluationPost_circle_piIsomorphism_of_raw_traced_homotopy に渡す。旧実入力 kanAdjointSignedReverseParametricSquare と全境界は保存済み。
- 所有ソースの sorry・追加 axiom・ModelCategory 仮定を禁ずる。公理監査は私有宣言・推移的依存・宣言型の ModelCategory 定数を検査する。KanQuillen は import しない。

### 次の一手
- K-8：次は LaxQuotientRelativeSquare.valueSquare を元の BF 合成射の二脚へ戻す。現在の始域の二辺は valueMap Φ (i≫laxFst), valueMap Φ (i≫laxSnd)。coherentNerveCompStruct i (laxFst/laxSnd) の E の像と BF の合成三角形を使い、比較道と三次元の充填証人を保って valueMap Φ i≫valueMap Φ (laxFst/laxSnd) へ移送する。任意の h Sp の可換式から選び直す旧 LaxQuotientSquare.square には戻らない。新 square は laxQuotientRelativeLegsIso から exactMapPinchedPath・exactMapComparisonTriangle を作り、compositionDiagonalTransport がその指定二単体を Λ³₁ の一面として保持して貼った実現である。この錐と元の laxQuotientProductFiberSquare の全図式の比較を構成し、suspension_pi_inv・laxQuotientProductMap_pi_formula と元の二脚から、実 pullback の普遍性を証明する。整数 π の可換性だけを coherent な比較の代用にしない。quotientSelectedCIso_right と零終点 suspension 全図式の始点の恒等式は提供済み。Sp の IsStable は要求しない。Q と ⊙ の構成・同定は D の β3・β4 後の合流。d7 は再開せず、d8 完成後に pro 値・pro 零性・pro fiber 列と Tor pro 消滅からの抽象 pro 切除へ進む。
- K-5 抽象部分は完成。K-S• が具体的 K 関手の局所化条件を接続する際は IsLocalizingInvariant.abstractFiberTriangle_isFiber・connecting・exact_left/middle/right・同値検出を使用する。切断付き列には IsLocalizingInvariant.splitEquivalence と splitLeftFactorIso・splitRightFactorIso、三つの splitEquivalence_inclusion/section/projection を使う。積は NativeSplit.productCone_isLimit の実 ∞ 極限錐であり、productCone_vertex は同値の始域をその頂点に同定する。Sp の IsStable・evaluationPost・Ω の関手同値は要求しない。
- 今回の d1・d2 は工程完了。整数次数による同値検出の証明・宣言表固定と対象・集約・監査・全体ビルドは成功。宣言表の未提供行まで完成したとは扱わない。
- 一般 coherent 極限の実装を再開する際の最初の工程は、F2.hasColimit_coherentSpaceDiagram から任意 D : ulift B → Sp の実錐の構成へ至る接続の設計・見積もり。空間の HasColimit から Sp の HasLimit は直接には従わず、その接続は未構成。既存の通常小図式の極限を再実装しない。
- d3 の再開条件は未成立：foundations.md では I-b の F1b-7・N-2・K-5〜K-8 等が未完。I-b 末尾までは evaluationPost circle・逆関手案・IsStable の実装へ戻らない。

## K-5：K-基盤 1 の抽象部分（2026-10-20）

- **分担**：本レーンは `KST/LocalizingInvariants/` と専用集約・監査を所有する。K-S• は SConstruction の構成・具体的 K 関手との接続を担当し、本レーンでは読み取り専用。F3 の IsStable・IsExactFunctor と D の β3 を変更しない。
- **対象・射**：StableCategory は小さい安定 quasicategory、ExactMap は F3 の完全関手。exactFunctors は内部 Hom の完全な頂点による充満部分 ∞ 圏。これを core 化した Hom の単体的圏の coherent nerve を構成する。冪等完備化は後続の Cat^perf 界面で別条件として扱う。
- **提供済み宣言**（共通接頭辞 `KST.LocalizingInvariants`）：StableCategory、ExactMap、exactFunctors、exactFunctorVertexEquiv、StableQCat、StableInfinity、stableInfinity_quasicategory、stableObject、stableVertex、stableArrowEquiv、IsVerdierSequence、VerdierSequence、IsVerdierSequence.universal、inverts_iff_kills_inclusion。
- **Verdier 列**：完全関手 i : A → B、q : B → C、i の充満忠実性、q の核と i の本質像の一致、cofiber が i の本質像に属する辺に関する q の局所化普遍性を要求する。D が Drinfeld 商を後から具体例として接続する。単なる核の一致を商の普遍性の代用にしない。
- **局所化不変量**：実際の Sp 値 ∞ 関手が Verdier 列を実 fiber 四角形に送る条件を定義する。Sp の IsStable は使わない。全整数 π の長完全列、同値検出、切断を持つ fiber 列の積分解を証明する。filtered 余極限保存等は必要な追加条件として区別する。
- **追加の提供済み宣言**：VerdierDiagram、IsZeroCategory、PreservesZeroCategories、IsLocalizingInvariant、LocalizingInvariant、IsLocalizingInvariant.fiberTriangle_isFiber、value、valueMap、valueHomotopyGroup、valueHomotopyMap、value_isInvertible_of_piIsomorphism、SplitFiber.section_map、SplitFiber.boundary_eq_one、SplitFiber.inclusion_injective、SplitFiber.groupEquiv。
- **今回の提供済み宣言**：zeroCategory、zeroCategory_isZero、toZeroCategory、fromZeroCategory、isExact_of_zero_values、verdierZeroCompositeIso、exactMapCoreVertexIso、stableArrow_homMk_eq_of_functorIso、exists_verdierSquare、VerdierSequence.presentation、VerdierSequence.presentation_sequence、IsLocalizingInvariant.abstractFiberTriangle、IsLocalizingInvariant.abstractFiberTriangle_isFiber、IsLocalizingInvariant.abstractFiberTriangle_bottom、IsLocalizingInvariant.abstractFiberTriangle_right、FiberDetection.piIsomorphism_of_fiberGroups、FiberDetection.piIsomorphism_iff_fiberGroups、FiberDetection.isInvertible_of_fiberGroups。
- **BF fiber の追加界面**（接頭辞 `FiberModel`）：obj、inclusion、comparison、comparison_inclusion、comparison_isInvertible、pointedCone_isLimit、infinityCone、infinityCone_isLimit、replacedCone、replacedCone_vertex、replacedConeComparison、replacedConeComparison_projection、homotopyFiberCone、homotopyFiberCone_isLimit、homotopyFiberCone_vertex、homotopyFiberSquare、homotopyFiberSquare_vertex。raw fiber の極限性は各段の実際の pointedFiber の普遍性から証明。置換後の図式上では、比較射上の slice の辺も保持する。
- **今回の追加界面**：StrictConeTransport.transport・apexEdge・diagramEdge、FiberModel.homotopyFiberTransport・homotopyFiberLeg_left_hom・homotopyFiberSquare_bottom_edge・homotopyFiberSquare_bottom_hom、SpectrumHo.component_eq_of_hom_eq・homotopyMap_eq_of_hom_eq・piFunctor・piComparison・piComparison_naturality、CoherentSplitFiber.section_map・boundary_eq_one・inclusion_injective・groupEquiv。錐の輸送には元の厳密自然変換の全 prism を使い、各脚を元の BF 射へ戻す。
- **全図式の比較界面**：FiberComparison.nonempty_functorIso・shortComplexIso・fiberShortComplexIso、FiberModel.fiberObjectIso・totalObjectIso・baseObjectIso・bottom_naturality・right_naturality。同じ右辺の fiber 四角形の比較に Sp の IsStable を使わず、三つの対象と両射への整合性を同時に保持する。
- **一般 fiber 長完全列**：SpectrumHo.edgeMap・edgeMap_edge・piMap_edge、FiberPi.fiberGroupIso・totalGroupIso・baseGroupIso・boundary・exact_fiber・exact_total・exact_base、NativeFiber.asFiberSquare・boundary・exact_fiber・exact_total・exact_base・isInvertible_of_fiberGroups。任意の Sp の辺を同じ一単体の BF 射に復号し、元の四角形の三対象・二辺を π 関手で写す。接続射と三箇所の完全性は元の BF 長完全列から群同型で移送した。
- **局所化不変量の値の長完全列**（接頭辞 IsLocalizingInvariant）：connecting・exact_left・exact_middle・exact_right、projection_bijective_of_leftGroups・inclusion_bijective_of_rightGroups、projection_isInvertible_of_leftGroups・inclusion_isInvertible_of_rightGroups。全て任意の抽象 Verdier 列と元の valueHomotopyGroup・valueHomotopyMap に対する主張で、像の fiber 性を追加仮定にしない。
- **Sp 積分解の完成界面**：Binary.hom_ext は両射影で一致する射の類の一致。Multiplication.map は対象ごとの実 BF 演算、SplitProduct.shear は整数 π 上で恒等な自己同値。SplitProduct.equivalence と equivalence_inclusion/section/projection は元の BF 包含・切断・射影との整合性を保持する。演算の標的自然性は使わず、shear の逆で射影を補正する。NativeSplit.productCone・productCone_isLimit・productCone_vertex・fiberIso・baseIso・equivalence と三つの整合式は任意の Sp fiber 四角形を扱う。IsLocalizingInvariant.splitLeftFactorIso・splitRightFactorIso・splitEquivalence と splitEquivalence_inclusion/section/projection は任意の抽象 Verdier 列の元の値・包含・商・指定切断へ適用する。積因子は元の fiber・底と同値な BF 表示で、その比較も明示する。
- **K-5 抽象部分は完成**：対象・完全関手の ∞ 圏、商の普遍性を含む Verdier 列、局所化不変量、全整数長完全列・同値検出・切断付き列の実 Sp 積分解を提供した。F3 と SConstruction は読み取り専用、Sp の IsStable は不使用。具体的 K 関手の局所化定理、D の Drinfeld 商の具体例、冪等完備化・filtered 余極限保存の追加条件はこの抽象部分の外。原典は HA §§1.1–1.3、BGT §§5・9。

## K-8：K-基盤 2 の抽象部分（2026-10-21）

- **分担と順序**：本レーンが `KST/LocalizingInvariants/` と専用集約・監査を所有する。(a) 二項半直交分解と切断付き Verdier 列、(b) F2 の元の lax pullback の半直交分解、(c) 局所化不変量の実 Sp 積分裂、(d) 通常 pullback と lax pullback の値の関係・差の項の順に進める。F2・F3・D の Stable/・K-S• の SConstruction は読み取り専用。⊙ の自己準同型環としての同定は β5・β4 の後、Cat^perf への接続は F1b-6 の後に K-7 と合わせる。
- **(a) の設計**：順序 ⟨A,B⟩ は Map(i A,j B) が可縮となる向き。完全包含 i,j、完全射影 r,q、実随伴 i ⊣ r と q ⊣ j、充満忠実性、q i の零化、q の核を i の本質像が尽くす生成条件を持つ admissible な表示を使う。選んだ右随伴の可逆余単位を明示し、商の普遍性は入力せず実関手 ∞ 圏上の局所化として導く。
- **現在の実装**：AdjointLocalization は可逆余単位の実随伴から局所化普遍性を導き、AdjointVerdier は cofiber が核に属する辺の反転と IsVerdierSequence を接続する。SemiorthogonalDecomposition は kernel・sectionIso・isVerdier・verdierSequence・semiorthogonal を提供。stableValueFunctor と value_section を経て semiorthogonalSplitEquivalence が K-5 の splitEquivalence へ接続する。今回までに (b) の実対象と (c) の元の値の積同値も接続済み。検証結果は下記。
- **(b) の完成界面**：ZeroArrowFamily.ofHomotopy・fromZero・toZero と LaxInclusion.fromD・fromC は元の全単体上の包含を構成する。fromD_fst/snd・fromC_fst/snd は一方が恒等・他方が零の厳密等式、exactFromD・exactFromC は完全包含。C 側も terminal_prism_extend_two_endpoints と lax_fst_terminalBoundary を実装し、RelativeTerminalAdjunction の相対終点充填の双対論から fromCAdjunction・fromC_fullyFaithful・fromCAdjunction_counit_isIso を得た。laxSemiorthogonal は元の D,C を因子とする SemiorthogonalDecomposition、laxVerdierSequence は D → lax → C の実切断付き Verdier 列。
- **(b) D 側の完成界面**：initial_prism_extend_two_endpoints は両端と境界を固定し、最初の頂点一つの始対象性から延長する。lax_snd_initialBoundary は第一成分とその像が始対象である任意の頂点の第二射影に対する相対始点境界充填を証明する。LaxInclusion.fromD_initialBoundary・fromD_mapping_equivalence・fromDAdjunction・fromDAdjunction_unit・fromD_fullyFaithful は元の D 包含と第二射影の実随伴と写像空間の充満忠実性。単位は fromD_snd の厳密等式から選ぶ。RelativeInitialVertexIso は二つの相対始対象の像の同型を元の圏へ持ち上げ、LaxInclusion.fst_kernel は零化と本質像の一致を証明する。Tamme の写像空間正方形をさらに包装する代わりに、既存 F1b の相対境界充填からの標準写像空間の同値を使った。
- **(c) の完成界面**：Binary.hoLift・hoMap・mapIso・swapIso と両軸・射影の整合式で、K-5 の補助因子を元の Φ(C), Φ(D) に同定する。IsLocalizingInvariant.tammeSplitEquivalence は要求の向き Φ(lax) ≃ Φ(C)×Φ(D)、tammeProductCone_isLimit は元の二因子の実 ∞ 積錐。tammeSplitComparison_C/D と projection は両包含・第一射影との h Sp の整合式。第二射影の整合式や Sp の IsStable を先取りしない。
- **(d) の到達点**：通常 pullback の安定性・完全包含、元の完全な差と核、target 評価・cofiber の随伴は完成。q ⊣ v（v 充満忠実）の場合は差の実右随伴・局所化・Verdier 普遍性と不変量の実 fiber 列・全整数長完全列を供給する。d7 の一般局所化・pointed 商候補・真の核・Ore・元の分母輸送の亜群化同値は「主要宣言」の補助界面として保持し、一般商の安定性・完全性・分数写像空間比較は未完のまま停止。d8 は安定 Q と IsVerdierSequence を入力に、実 product fiber、元の包含・両射影と右辺を保つ三対象の比較、全整数長完全列と reflective な場合の整合を提供する。完全な入力 suspension と逆 shift により一般商の二脚を明示し、cofiber 差の場合は元の p,q に戻る。E(Σ_Q) の整数 π の負号と差の二脚の π 公式も完成。LaxCounit.cofiber の両射影を計算し、cofiber_fromCIso と laxQuotientLegsIso により C 包含および一般商の二脚を全関手同型で比較する。値の四辺固定の候補正方形・E(A) を頂点とする実錐も存在する。rightCompatibleFromCIso_right は元の cofiber 右辺と C 単位の整合を全関手圏の射の等式で保持する。商での全 cofiber 図式比較は底辺で恒等となり、右辺の自然性・始点の恒等性と C 単位の像の合成式まで提供した。quotientSelectedCIso_right と始点固定の suspension 全図式比較を結び、元の比較道の指定二単体と三次元の証人を保つ LaxQuotientRelativeSquare.square、およびその同じ E の像まで提供した。元の BF 合成二脚への移送・実 product fiber との比較と実 pullback の極限性は未証明で、候補錐の任意の選択が極限になるとは主張しない。
- **残工程と見積もり**：d8 は安定 Q・元の lax pullback から Q への完全関手・IsVerdierSequence を仮定入力に、実 fiber 列と二軸の実 pullback 比較を完成する（Tamme Thm. 18、Land–Tamme §1–2）。その後、pro 値・pro 零性・pro fiber 列の最小形式と抽象 pro 切除へ進む。いずれも暫定複数日、上限未見積もり。D の β3・β4 による Q と ⊙ の同定は後の合流。d7 の一般商の構成は再開しない。
- **今回の検証**：選択された商 cofiber の C 単位整合、始点固定の suspension 比較、指定された比較道を保つ正方形と E の像は対象6777 jobs、330モジュール・2662宣言の専用公理監査、全体21208 jobs が終了コード0。標準三公理のみ、宣言型の ModelCategory 検査も成功。8新規ソースの各行は100文字以内、sorry・追加 axiom・KanQuillen import はなく、diff --check も成功。
- **原典**：[Tamme 2018 §1、Prop. 10–11・Cor. 12](https://arxiv.org/html/1703.03331)、[Land–Tamme 2019 §1–2](https://arxiv.org/html/1808.05559)、分数写像空間は [Nuiten §3・Cor. 3.14](https://www.math.univ-toulouse.fr/~jnuiten/Writing/Localizing.pdf)。一般の正方形に excision を無条件で課さず、差の項の商の存在・普遍性を証明せずに完成扱いしない。Sp の IsStable は全工程で使わない。

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
- 値域界面は上表で固定する。IsStable はユーザー指示により I-b 末尾へ延期する。
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
