# K-S• → K-基盤 1・2：∞-S• と局所化不変量

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-S• → K-基盤。L1c〜f の後、L3 は非連結 K を BGT (a) のみで（暫定 (b) は使わない）、続けて局所化不変量・Tamme・Land–Tamme（K-基盤 1・2）。

## 引き継ぎ（2026-10-20）

### 現在地
- K-L1（∞-S• 構成、連結 K）。L1a・L1b・L1e 完了。L1c・L1d 進行中、L1f 未完了。後続は L3・K-基盤 1・2（v2 の担当範囲）。
- 全 gapped S• と第一行制限そのものの trivial Kan fibration を証明済み。core・対角実現・Kan 置換・Ω、反復 S の段と単射な構造射への置換、零方向の境界比較を構成済み。
- Ω から既存の path homotopy fiber への全基点 π_* 同型は証明済み。前段の Kan 実現と同じ fiber は共通 Kan 模型からの全基点 π_* 同型で比較済み。元の構造射の随伴と零行 loop 射の照合は証明済み。終点固定 path による fiber 内の実ホモトピーは証明済み。元の円の loop 包含との厳密な分解と、元の随伴の全基点 π_* 同型まで証明済み。境界商の BF Ω スペクトルに加え、元の K 空間を零段とする `kOmegaSpectrum` を構成し、全負整数次数の消滅まで証明済み。
- raw ρ の cofiber・gapped 性と、同じ C 内の選択を保つ `mcCarthyRho` を構成済み。面・退化、時刻零、subobject・quotient の strict 回収を証明済み。
- McCarthy の ρ・θ の二つの実ホモトピーと厳密な切断から、全 C 内の `cofiberLeftFiberQuotient_localized_isIso` を証明済み。θ の可変時刻の gapped 性は点ごとの可逆性で保証する。
- strict 左 fiber の二重単体解消と augmentation の局所化同型、反対圏のラベル付き射列による余積表示、対象ごとの局所化同型を解消の対角へ移す定理を証明済み。
- `simplicialProductQuillenA` を追加仮定なしで証明済み。恒等射の単体 fiber と固定係数の積を使い、元の射対との厳密な可換性も照合した。
- `objectSAdditivityMap_localized_isIso`、`coreSAdditivityMap_localized_isIso` を証明済み。同じ C 内の全 cofiber 図式の subobject・quotient を対象とする。相対版の単回 object/core 加法性も証明済み。相対版の全正有限反復と、両端を保つ完全関手に関する自然性も証明済み。
- `sCofiberIso`：S_n(cofiber C) ≅ cofiber(S_n C) の厳密な同型を証明済み。零角と押し出しを全 Ar 成分で判定し、全 gapped・全 cofiber の選択を保った二回の転置で逆律を得た。
- `multiRealizationAdditivityMap_localized_isIso`：全ての正の有限反復 core S• 実現の加法性を証明済み。単回の座標同型を基底に、S/cofiber 交換・行ごとの加法性・対角・既存の自然な反復座標同型で帰納した。r=0 は主張しない。
- `cofiberEndofunctor` と各角の自然変換を構成し、加法性を完全関手について自然な `multiRealizationAdditivityLocalizedIso` に束ねた。S₂ の元の中央四角形の二つの区間への射対も正の反復実現で局所化同型。
- `ClosedStablePredicate` と `closedSubcategory_isStable`：零対象・押し出し・引き戻しに閉じた replete な頂点条件から、全部分圏の安定性と包含の完全性を証明済み。部分圏の安定性を入力の仮定には置いていない。
- `relativeCofiberStableModel`：評価による逆像条件の交わりとして相対 E(A,C,B) を構成済み。subobject・quotient は A/B への完全関手で、元の評価との包含後の厳密な等号を証明済み。相対 object/core 加法性への入力として接続済み。
- 相対左 fiber 内の切断・ρ・θ と両端を構成済み。ρ は相対 quotient を厳密に固定、θ は replete 性で B 所属を保つ。`relativeCofiberLeftFiberQuotient_localized_isIso` を二ホモトピーから証明済み。
- `sClosedStableIso`：S_n A を全 Ar 成分が A に入る S_n C の全部分圏と、全高次単体を保つ完全関手の同型で比較済み。
- `sRelativeCofiberStableIso`：S_n E(A,C,B) と E(S_n A,S_n C,S_n B) の交換同型、両評価との厳密な可換性を証明済み。相対の各 S_n 行、全正有限反復実現の元の射対の加法性まで接続済み。`RelativeStableModel`・`relativeCofiberFunctor`：両端を保つ完全関手の相対図式への作用と厳密な二評価の自然性を構成済み。`relativeMultiRealizationAdditivityLocalizedIso` は全正反復の元の射対を成分とする自然同型。
- `cutStableComparison`：任意の切断位置 k で S_n C 内の実際の cofiber 四角形への完全関手を構成。各角は min・恒等・定数 k・max による制限と全高次単体で厳密に一致し、中央評価は恒等関手を回収する。
- `arCutSquareMap_naturality`：切断位置も写す任意の単調写像（面・退化を含む）で添字の全単体の切断四角形が厳密に可換。正の反復実現後の二分割 Segal 同値も証明済み。
- `cutLeftSupport`・`cutRightSupport`：反対側の全区間成分の零性から閉じた安定部分圏を構成。切断の両端の所属、`cutRelativeComparison` の完全性と中央評価との厳密な切断を証明済み。
- `cutLeftIntervalEquivalence`・`cutRightIntervalEquivalence`：左右の支持部分圏と S_k C・S_(n−k) C の実際の同値を、完全な制限・延長と coherent な逆同型で構成済み。相対 E の中央評価とのもう一方の逆同型も `cutRelativeMiddle_comparisonIso` で証明済み。
- `cutRelativeEquivalence`：相対 E と S_n C の実際の同値を構成済み。二重 cofiber 格子の零番目の行・列の商を支持条件で消し、入力族の同型を射影の自明ファイブレーションと包含の充満忠実性で反映した。`cutRelativeSegalPair` は任意の実現関手の下で元の区間評価の射対と厳密に可換。
- `cutSegalMap_localized_isIso`：任意の切断位置の元の二区間制限が全正有限反復実現で局所化同型。完全な逆データの同値保存を各 S_n・対角で帰納し、相対加法性と厳密な射対の式を合成した。`cutSegalLocalizedIso` は完全関手について自然で、成分は元の Segal 射の像。
- `edgeSegalMap_localized_isIso`：全連続辺への元の評価を n 個の S₁ の積へ束ね、正の全反復実現で局所化同型を証明済み。射影の式と最初の辺での厳密な分解式を含む。
- `iteratedPathBoundary_homotopyPullback`：元の経路境界の全単体作用素の自然性四角形は正の全反復実現で homotopy pullback。δ₀ は σ₀ の面条件・厳密な退縮・正の実現の連結性から検出し、他の面・退化と合成して全作用素へ拡張した。
- `localized_isIso_of_connected_baseChange`：連結な Kan 基底上の二つの Kan fibration の間の射は、非空な任意の基底変換で局所化同型を検出できる。境界 RLP・全単体全射性・right properness から証明済み。
- `iteratedPathBoundary_realization_homotopyPullback`：証明済みの全ての面条件を既存の Segal 実現定理に適用し、各行と全対角の四角形の homotopy pullback 性まで接続済み。零行の既存 fiber との比較は次項。元の構造射の随伴と具体的 loop 射の照合は証明済み。
- `sInterchangeStableIso`：全 gapped 図式を保つ二重 S の厳密な交換と完全関手・両添字・評価の自然性を証明済み。全多次数で固定方向も動かす `multiMovingSCoreIso` は既存の巡回実現を回収する。独立な全零方向の境界と商の比較、座標置換の全零境界保存も証明済み。旧座標比較の全多単体的な自然性と対角での一致を証明し、標準の全零境界と既存の商上の `cyclicBoundaryIso` を構成済み。
- `sOneInnerOuterRealizationIso_comparison`：経路零行 F_r(S₁ X) と元の一方向実現の交換同型と、二つの元の前段比較の厳密な可換性を証明済み。固定方向も動かす自然性と `iteratedSRealizationCyclicIso` を構成し、`sOneInnerOuterRealizationIso_assembly` で元の区間族の厳密な可換性まで照合済み。全多次数の交換と自然性も構成し、源の既存の全零境界の対応、元の境界商の `sOneInnerOuterReducedIso` と前段比較の可換性まで証明済み。標的の標準境界商の巡回自己同型も構成済み。`simplicialPathDiagonalCylinder_zeroRow_boundary` は元の経路収縮の零行への制限と元の区間組み立ての厳密な等号。元の点つき経路商の基点固定収縮、既存の Kan 経路全空間への零行制限と両端・境界の回収、零段の全退化像の全時刻での基点固定まで証明済み。`zeroRowLoopComparison` を元の円の商と既存の点つき curry で構成し、評価で元の区間組み立てを厳密に回収済み。任意の零段頂点を使う点つき射と既存の Kan 単位への厳密な延長も構成済み。`zeroRowLoopComparison_assemblyAdjoint` と源の境界商上の同式で、元の `kanTargetAssemblyAdjointNat` と具体的 loop 射の厳密な一致を証明済み。`zeroRowReducedLoopComparison` は元の全零境界商へ降り、商射で元の loop 射を回収する。全零境界の定数 loop への像も厳密に証明済み。`zeroRowTerminalFiberHomotopy` は元の零行収縮の向きを保つ終点固定 fiber 内の実ホモトピー。全境界充填による path 空間の可縮性と元の homotopy pullback から、定数 path 比較・収縮境界 loop 型比較の両方の局所化同型まで証明済み。`terminalEndpointCircleIso` は元の円と元の区間商射を保つ同型。元の loop 包含は可縮な全空間に対して全基点 π_* 同型で、`zeroRowLoopComparison_terminalFactor` は収縮の fiber 比較への厳密な分解。`zeroRowKanLoopComparison_piIsomorphism`、元の任意の延長の `kanAssemblyAdjointAt_piIsomorphism`、`boundaryKanAssemblyAdjoint_piIsomorphism`、元の列・単射置換の Ω 条件、`boundaryOmegaSpectrum` まで証明済み。境界の段は r+1 重 S のまま。既存の `kKanSequence` は零段 Ω|S•|・正の段が反復 S なので、その Ω 条件と単射置換を用いる `kOmegaSpectrum` に接続済み。零段は境界商の K 空間と厳密に一致し、元の `kSpace` と全基点 π_* 同型。`kOmegaSpectrum_negative_subsingleton` は実際の全負整数次数の消滅。実際のスペクトルの射、整数 K 群の可換群への関手、任意段表示と零次数の元の K 空間の π₀ への自然同型まで証明済み。`objectKClass` は元の S₁ core 比較の π₀ 全単射の逆と元の零行 loop から作る実際の加法記法の BF K 類。任意の S₁ 補完の回収・選択非依存性、core の成分・可逆辺・h C の同型に関する不変性、任意の零対象の零性、完全関手の像の対象類との自然性まで証明済み。零次群から一重 S の元の基本群への群同型と、対象 loop の逆元の向きの式、元の S₂ の三辺と対象 loop の厳密な照合、任意の元の cofiber 正方形の `objectKClass_cofiber` を証明済み。h C の distinguished triangle 全体の加法性から `triangulatedKZeroMap : TriangulatedK0(h C) →+ π₀K(C)` と対象類の回収・完全関手に関する自然性まで構成済み。任意の Kan 値 anodyne 射について、元の辺と二単体の基本亜群から置換後のホモトピー圏への圏同値・辺／逆／合成による帰納法を証明済み。既存の基本群との単位・積・逆の同定から `kZeroGroupoidPresentation` を構成し、元の全零境界商の基本亜群の基点の自己射で実際の零次 K 群を表示済み。`kZeroGroupoidPresentation_objectKClass` は同じ置換前の object S₁ の辺の形式的な類の逆を回収する。元の全零境界商の頂点一意性と、内部 core の辺の対角像を同じ始点の object S₁ の辺へ帰着する実三角形を証明済み。元の全ての辺の帰着と基本亜群の帰納法から `triangulatedKZeroMap_surjective`（対象類による生成）まで証明済み。三角圏 K₀ 自身の退化辺・S₂ 関係から `objectTriangulatedFunctor` を構成し、元の object S と境界商の局所化同値・実ホモトピー・Kan 単位への厳密な延長で `kZeroToTriangulatedMap` を構成済み。元の対象 K 類の像を既存の Kan 辺で計算する式も証明済み。同じ零頂点を両対角に厳密に指定した S₁ 補完と閉じた辺の自然性から逆向き写像の対象類の回収を証明済み。K₀ の普遍性で左逆、既存の全射性で右逆を証明し、`triangulatedKZeroEquiv` と可換群値の `triangulatedKZeroNatIso`、元の K 空間の π₀ への `triangulatedKZeroPiZeroIso` を構成済み。スペクトル値の coherent 関手化は未完。
- `zeroRowPathFiberComparison_localized_isIso`：元の経路零行から既存の `iteratedPathHomotopyFiber` への定数 path による実際の比較と局所化同型を証明済み。Δ[0] の積を外した零列写像、商・Kan 比較の厳密な可換性、標的の零列の厳密な零化を含む。
- `exists_previousStage_pathFiber_comparison`：任意の零段基点の退化を基点にした零行の同じ Kan 模型から、前段の既存の全零境界 Kan 実現と既存 fiber へ全基点 π_* 同型を構成済み。Kan 単位に沿う延長は元の射を厳密に回収する。
- 比較逆・Kan 延長・合成構造射の全選択空間は可縮 Kan。元の全入力円柱と全離散頂点上の補正から、`boundaryAssemblyOriginalCoherentHomotopy` は元の固定随伴構造射の辺を全対象で厳密に回収する。元の loop の実 ∞ 関手 `pointedKanLoopInfinity`、その全単体の図式への作用、元の全入力変換そのものの Ω 同型を構成済み。`kKanCoherentLevelDiagram` は元の K の全段・段の射を回収する。豊穣 Hom の suspension/loop 同型の全単体での前後合成と、局所 Kan な有向 collage 内の合成・射影・元の suspension への評価を構成済み。元の固定交差射への全対象同時補正から、`boundaryAssemblyOriginalSuspensionHomotopy` は元の固定 suspension 構造射を全成分で厳密に回収する。零段は元の余単位を使い、`kKanOriginalSuspensionPrism` は零段を含む全段・全合成列・全頂点・両端と面・退化を保持する。`coherentTriangleMappingEdge` は元の三辺を保つ三角形から長辺→合成の豊穣 Hom の実辺を、局所 Kan 性なしで復号する。`kKanSuspensionMappingTriangles` は元の全段の square の共通対角射と二つの標準実三角形。`kKanSuspensionCompatibilityComposition` はその二辺と両逆三角形・合成三角形を保存し、`kKanSuspensionCompatibilityHomotopy` は全段の基点固定実適合ホモトピー。`monicKPrismCompatibilityEdge`・`monicKPrismCompatibilityHomotopy` は元の単射置換の射影による前合成で、既存の `monicKToRawLevelMap` の適合条件を回収する。一般の列の射に沿う移送を `sequenceCompatibilityEdge_precompose` に抽象化してカーネルの展開を抑える。境界固定の適合円柱を入力する `relativeSequenceFamilyRectification` は全段を相対厳密化し、実際の補正有限列を状態に保存、全区間の射影が元の指定区間そのものになる式を保持する。`relativeKFamilyRectificationData` は指定 BF 境界と元の未置換列への射影を厳密に保持する。`relativeKanSpanFamilyData` は全パラメータを関手空間の辺として扱い、指定境界の逆辺・合成辺と二つの実三角形を厳密に回収する。相対構成は一つの逆三角形と合成三角形を指定し、独立な両逆三角形の同時拡張は仮定しない。`relativeKanHomotopySpanComposite_restrict_constant` は境界の合成辺の恒等性から実円柱の境界定数性を導く。`relativeSequenceSpanRectification` と `relativeKSpanFamilyRectificationData` は全段の二円柱の族・境界の指定三角形・恒等性・元の BF 境界の射影の式を入力して、指定境界を保つ実 BF K 写像族へ接続する。`relativeEquivalenceFamilyRecovery` は同値の path 置換の全単射 RLP から、指定境界を厳密に保つ元の族と境界定数の実比較円柱を回収する。`relativeCoherentIntervalFamilyRecovery` は豊穣 Hom と固定端点の区間模型の比較へ適用し、`relativeLoopCollageSuspensionFamilyRecovery` は局所 Kan な collage と元の随伴同型を通して suspension の写像空間へ回収する（宇宙持ち上げ後）。`kKanPrismCutHomotopy` は元の全段の prism の各高次単体の全 Path 族を、元の豊穣 Hom 内の実合成へ結ぶ円柱。合成面の全時刻固定、入力列と各単体の面・退化の両方との可換性、端点 Path で以前の指定三角形の辺を回収する式まで証明済み。`fixedKanHomotopySpanBoundary` は定数境界の二円柱から実逆・合成三角形と恒等合成辺を退化で構成する。同じ豊穣単体の二つの切断は全 Path を共通パラメータとし、両切断点を通る共通面を固定する `coherentCutSpanComposite` へ接続済み。`kKanPrismCutSpanComposite` は上段に終わる元の prism の単体に追加の Kan 仮定なしで適用し、同じ元の豊穣作用の境界固定まで証明済み。`relativeKFixedSpanFamilyRectificationData` は全段で境界定数の二円柱と元の BF 境界・射影式から、境界三角形を内部で構成して実 BF K 写像族を与える。`kanSpanHorn` は別々の二三角形の復号辺を同じ外側ホーンへ貼り、`kanSpanPastingChoices` は元の二脚を厳密に固定する可縮 Kan 空間。普遍三角形族は両脚を全選択で回収し、指定三角形と辺は選択空間へ入れてそのまま回収する。`kKanSuspensionSpecifiedPastingVertex` は既存の prism 適合辺を変更しない指定頂点で、元の実ホモトピー、単射置換後の辺・実円柱も厳密に回収する。各入力射を固定した全選択の相対延長まで証明済み。`varyingKanSpanHornFamily` は与えられた二円柱が変化する全パラメータで両脚を貼り、元の円柱と全パラメータ制限を厳密に回収する。`relativeVaryingKanSpanTriangleFamily` は元の境界三角形族を保持して延長する。`relativeKanOuterSpanFamilyData` は一つの指定外側三角形と比較辺だけを保持し、逆辺の入力を要しない。同じ選択の `relativeKanOuterSpanTriangleFamily` は三面で元の二円柱・比較円柱を回収し、境界では指定実三角形族そのものを保持する。`relativeKanCoincidentSpanComposite` は二円柱が境界で一致すれば、個別の定数性なしで境界固定の合成を構成する。一般の列での厳密化と `relativeKCoincidentSpanFamilyRectificationData` は元の BF 境界・射影を厳密に保持する。`CoherentArrowString f` は元の射を長辺に持つ全有限合成列と両端固定の精密化の圏。元の射そのものの初対象性と実収縮、各高次精密化単体から最後の合成列内の native Path 単体を作る `coherentStringPathFlag` と全単体作用との整合性を証明済み。`coherentStringDiagramCell` は元の coherent 図式の全合成列を共通の元の頂点対象へ回収し、全再添字と厳密に可換。`coherentStringNativeMap` は元の Path 評価を元の射の両端に固定し、全精密化と厳密に可換。`coherentArrowNativeFamily` は高次 Path 評価を一つの native Hom の単体射へ束ね、元の全頂点 Path と初点の二端点 Path の回収、実収縮 `coherentArrowNativeContraction` まで証明済み。`coherentOrdinaryPrismIso` は prism の始域を通常積圏の nerve と厳密に同定し、`kKanOriginalPrismStringDiagram` は元の K 実円柱と全単体の prism を厳密に回収する。元の全段の prism から直接、全合成列の `kKanOriginalPrismNativeFamily` と実収縮を構成済み。`coherentLowerPrismStringFunctor`・`coherentUpperPrismStringFunctor` は同じ元の射の全合成列を上下の因子分解列へ送り、長辺・時刻・全精密化・恒等・合成を厳密に保つ。`coherentPrismLowerNativeContraction`・`coherentPrismUpperNativeContraction` は同じ元の収縮への前合成で、同じ長辺の値から始まる共通パラメータ上の二円柱。元の K prism への直接適用と頂点の全 Path 評価の回収まで構成済み。`coherentOrdinaryPrismSlice_source`・`coherentOrdinaryPrismSlice_target` により、上下の部分圏が元の円柱の全端点図式を厳密に回収する。`kKanOriginalPrismStringDiagram_bottom`・`kKanOriginalPrismStringDiagram_top` は元の suspension・次段の strict 図式に一致し、頂点と水平辺・縦辺も元の対象・段の射・構造射を回収する。`kKanOriginalPrismNativeHomIso` は元の suspension 写像空間への対象等式だけの同型。上下の実円柱を同じ Kan 標的へ移し、逆射で元の族・円柱を全時刻で回収済み。上下の全高次 Path 単体は縦辺との切断点を通り、`coherentLowerPrismPathFlag_mapping_comp`・`coherentUpperPrismPathFlag_mapping_comp` は元の豊穣作用を水平部分と縦辺の実合成へ厳密に分割する。上下の水平 Hom の全次数での定数性は、元の水平面の厳密な回収と外側面の Path 写像の全射性から証明済み。隣接縦区間の全 Path は唯一で、合成面上の全評価と両端への移送後の native 評価の定数性まで証明済み。`kKanOriginalPrismLowerNativeFamily_eq_const`・`kKanOriginalPrismUpperNativeFamily_eq_const` は全精密化パラメータの終点族を元の二辺の因子分解列の値の定数族へ厳密に回収する。元の suspension 写像空間内でも同じ定数族で、`kKanOriginalPrismLowerEndpointContraction`・`kKanOriginalPrismUpperEndpointContraction` は両端が定数の同じ実円柱。`coherentLowerPrismDirect_forward`・`coherentUpperPrismDirect_forward` と `kKanOriginalPrismLowerDirect_cell`・`kKanOriginalPrismUpperDirect_cell` は元の短い列を元の square の同じ二三角形へ厳密に同定する。`kKanOriginalPrismLowerEndpointVertex_composite`・`kKanOriginalPrismUpperEndpointVertex_composite` により、全パラメータの定数終点値は元の構造射・段の写像の明示的な二合成の頂点そのもの。上下の `CompositeContraction` はこの二合成を終点に持つ同じ元の実円柱で、指定頂点の成分も元の Path 包含辺の評価を厳密に回収する。`kKanOriginalPrismLowerCompositeContraction_boundary_leg`・`kKanOriginalPrismUpperCompositeContraction_boundary_leg` は指定頂点の二成分を既存の二三角形の復号辺そのものへ同定し、`kKanOriginalPrismSpanInitialVertex_diagonal` は共通初点を元の対角射へ戻す。`kKanOriginalPrismSpecifiedCompatibilityFamily` は追加入力なしで全精密化上の実適合族を供給し、指定頂点で元の `kKanSuspensionCompatibilityEdge` の同じ実区間を厳密に回収する。同じ選択の全三角形族は上下の元の二円柱と比較円柱を三面で回収し、指定頂点で既存の外側三角形全体を保持する。`monicKPrismSpecifiedCompatibilityFamily` は元の単射源の射影で前合成し、指定頂点で元の `monicKPrismCompatibilityEdge` の同じ実区間を回収する。三角形族の元の三面と指定境界の同じ前合成を保持済み。`monicKPrismRawLevelFamily` と `monicKPrismRawSequenceCompatibility` は既存 raw 写像空間の全段の型で具体的な入力を供給し、実円柱と指定境界を保持する。`FamilyHomotopyChain` は境界定数性なしの元の補正有限列を保存する。`exists_prescribedFamilyChain_lift_with_traces` と `prescribedFamilyChainLiftData` は、指定境界の補正列の射影 trace が元の区間の制限に一致すれば、同じ全区間の射影と境界 trace・終点を保持して持ち上げる。`canonicalTracedSequenceBoundaryData` は元の適合円柱から先に境界の全段の補正列・射影 trace を実構成する。`prescribedSequenceFamilyRectification` は同じ境界終点・全区間を固定して全段を厳密化する。`monicKPrismTracedBFFamily` は元の K prism の全精密化にこれを適用した BF 族で、先に選んだ同じ BF 境界・raw 射影・各段の評価を厳密に回収する。元の零段と実補正列も保存済み。`extendedTracedSequenceBoundaryData` は一回目の補正列を選び直さず次の境界へ渡す。`kIteratedTracedFamilyLiftData` は中間 BF 族と元の境界を厳密に保持して延長する。同じ raw 族の直接・段階的 BF 延長の境界固定比較と、指定した実比較円柱を保持する比較延長も構成済み。`monicKPrismTracedCompositionFamily` と `monicKPrismTracedRawComposition` は二本の全精密化族の実合成と同じ raw 射影。`monicKPrismTracedCompositeCorrectionChain` は各段の元の合成射からの実補正列で、前の補正の後合成と後ろの補正の前合成の二つの全 trace への厳密な分解を証明済み。指定頂点の二つの BF 境界の合成と、元の零段の厳密な回収も証明済み。`familyInterchangeSquare` は元の二円柱から四辺と任意の制限を保つ実正方形を作る。`monicKPrismCompatibilityInterchangeSquares` は前の全補正と後ろの元の適合円柱の交換正方形列で、隣接面の厳密な貼り合わせと水平二面の明示的な二合成への回収を証明済み。指定頂点では元の後続適合辺そのものを保持する。`monicKPrismCompositeFirstTrace_projection_squares` は前半補正の構造射での射影を、元の前の適合区間と同じ交換正方形列の零面へ分解する。`monicKPrismCompositeSecondTrace_projection` は後半射影を元の後続適合区間と前段の後半補正へ厳密分解する。`monicKPrismCompositeSecondCompatibilityTransport` は元の前の段族から補正済み段へ後続適合円柱を運ぶ実二次元補正列で、元の各交換正方形と全 trace を保存する。終点は後半射影の同じ先頭区間で、零段は厳密に元のまま。`monicKPrismTracedCompositeCorrectionChain_projection_trace` は前後を合わせた全射影 trace の分解。`trianglePrismTetrahedron` は元の合成二単体 prism の三つの三単体で、二つの共有面と前後・合成射の六三角形を厳密回収する。`kKanOriginalCompositionMappingSquare` は元の K prism の三つの正方形を同じ元の suspension Hom に表示し、共有区間を厳密に保持する。`coherentTriangleTrace_specified_edge` で Path 区間を既存の同じ復号辺へ同定し、外側の二区間は元の合成射の上側・下側の復号辺そのものと証明済み。`kKanOriginalCompositionMappingSquare_first_upper_post`・`first_lower_post`・`second_upper_pre`・`second_lower_pre` は残る四辺を元の復号辺と元の水平射の前後合成へ厳密に同定する。元の上下の三角形は strict 図式の同じ二単体で、その Path 区間は定数。`kKanOriginalCompositionMappingSquare_exterior_*_constant` は正方形の外側二辺そのものの全時刻の定数性を証明する。`threeSquareTrianglePasting` は二つの共有区間で三正方形を貼り、外側三ホーンに三つの指定三角形を同時に付ける複体。`kKanOriginalCompositionSpecifiedPasting` はその全セルを元の同じ suspension Hom へ写し、各正方形・指定三角形全体、元の三適合区間の実前後合成、外側二定数辺を厳密に回収する。`threeSquareCompatibilityDataOfMaps` は同じ共有二区間と定数外側二辺から六頂点・全境界を内部構成し、三正方形・三指定三角形全体を保持する。`kKanOriginalCompositionCompatibilityTriangle` は零段を含む全段で、入力二射の元の適合辺の実前後合成と合成射の元の適合辺を同じ三面に持つ実比較三角形。`monicKPrismOriginalCompositionTriangle` はその全二単体を単射源へ移し、三適合区間の同じ前合成を保持する。`CompositionStringParameters` は合成射と二入力射の独立な全合成列の積圏で、直通列点の包含の anodyne 性も証明済み。`relativeSpecifiedTriangleMap` は全三辺と指定部分の全二単体を固定して延長する。元の三円柱をこの積の全パラメータへ移し、指定点での元の全区間から定数端点を合わせた。`kKanCompositionNativeTriangle` はその元の三円柱を全三面に持ち、指定点で元の比較三角形全体を回収する。`monicKPrismCompositionNativeTriangle` は同じ全族を単射源に移し、三面と指定点の全二単体を保持する。`monicKPrismCompositionNativeTriangle_first_trace`・`_composite_trace`・`_second_trace` は全三面を保存済みの同じ raw 適合円柱へ厳密に照合する。第二面の補正始点は元の定数段族での実合成であり、`monicKPrismNativeSecondCompatibilityTransport` は同じ二次元補正全区間と順序を引き戻す。`monicKPrismNativeCompositeCorrectionChain_projection_trace` は補正全体の射影を元の第一面・交換零面列・補正後の第二適合円柱・前段の後半全区間へ厳密に分解する。零段の両補正列に区間はなく、元の族を回収する。`familyChainPasting` は全補正円柱を実 pushout で貼り、複体内の共有面と両端を `CylinderCellWalk` に保存する。`monicKPrismNativePastingMap` は元の全三角形と同じ全交換正方形を一つの実複体から写す。補正全セルは二時刻を交換した元の全正方形そのもので、両側の全 trace と隣接共有面を保持する。零段には補正セル自体がない。`monicKPrismNativePasting_projected_full_trace` と `_original_full_trace` は、次段補正の全射影と、元の合成適合円柱・前段補正全体の構造射の像を同じ複体の両側に表示する（共通末尾も保持）。この実複体から各段の端点固定比較円柱と構造適合の実二次元比較を取り出す工程、旧 BF 射との比較と入力の合成面の貼り合わせ、大きい全入力・高次射への接続は未完。

### 残り（依存順、原典番号と時間見積もり）
- 以下は再開後の実装作業時間の粗い目安。未形式化の難所で増えるため納期ではない。
- 完全関手について BF 連結 K の coherent スペクトル値関手化：BGT Definition 7.1、経路正本 §10-5、
  §13 決定2・5・12、L9c の BF 界面、16–48時間。
- dg 関手性・Morita 不変性：経路正本 §4 D1・§5 K1b、U16・A3e、8–24時間（依存 API の照合を含む）。
- L3・K-基盤 1・2 は §6・7 の依存順に続行。非連結化は F2-lite の Ind を待つ。

### 主要宣言（名前のみ）
- `sConstruction`、`simplicialSConstruction`、`firstRowRestriction_trivialKanFibration`、`firstRowEquivalence`
- `StableModel`、`PreservesCofiberData`、`sEndofunctor`、`multiRealizationFunctor`
- `kSpace`、`kKanSequence`、`monicKKanSequence`、`monicKKanSequenceProjection_piIsomorphism`
- `iteratedPathHomotopyFiber`、`iteratedPathLoopComparison_piIsomorphism`
- `objectToCoreSRealization_localized_isIso`、`objectCoreRowIso`、`cofiberStableSubobject`、`cofiberStableQuotient`
- `mcCarthyLambdaMu`、`mcCarthyLambdaNu`、`mcCarthySpan`、`mcCarthyRhoRaw_pre`、`mcCarthyRhoRaw_timeZero`
- `mcCarthyRhoRaw_isCofiber`、`mcCarthyRhoRaw_isGapped`、`mcCarthyRho`、`mcCarthyRho_isGapped`
- `mcCarthyRho_ι`、`mcCarthyRho_pre`、`mcCarthyRho_timeZero`、`pointwiseDiagramPushoutApex_postcompIso`
- `mcCarthyRho_source`、`mcCarthyRho_quotient`、`mcCarthyRhoFiberMap`、`mcCarthyRhoFiberHomotopy`
- `mcCarthyRhoFiberMap_quotient`、`mcCarthyRhoTerminal_parameter`、`mcCarthyRhoTerminal_source`
- `fixedSourceArrowsTarget_trivialKanFibration`、`zeroSourceThetaHomotopy`、`mcCarthyThetaFiberHomotopy`
- `mcCarthyFiber_retraction_localized`、`cofiberLeftFiberQuotient_localized_isIso`
- `simplexFiberDiagram`、`elementsResolution`、`fiberResolutionAugmentation_localized_isIso`
- `oppositeLabelledChainEquiv`、`elementsResolutionRowIso`、`elementsResolutionMap_diagonal_localized_isIso`
- `tensorElementsResolutionIso`、`identitySimplexFiberIso`、`simplicialProductQuillenA`
- `objectSAdditivityMap_localized_isIso`、`objectCoreAdditivity_commute`、`coreSAdditivityMap_localized_isIso`
- `sCofiberIso`、`sCofiberStableIso`、`sCofiberStableIso_subobject`、`sCofiberStableIso_quotient`
- `coreSRowAdditivityMap_localized_isIso`、`objectSRowAdditivityMap_localized_isIso`
- `multiRealizationAdditivityMap_localized_isIso`、`multiRealizationAdditivityLocalizedIso`
- `cofiberEndofunctor`、`cofiberEvaluationNat`、`sTwoRealizationAdditivityMap_localized_isIso`
- `ClosedStablePredicate`、`closedSubcategory_isStable`、`closedStableInclusion`
- `relativeCofiberStableModel`、`relativeCofiberSubobject`、`relativeCofiberQuotient`
- `objectSClosedIso`、`relativeCofiberLeftFiberLift`、`relativeMcCarthyRhoHomotopy`、`relativeMcCarthyThetaHomotopy`
- `relativeCofiberLeftFiberQuotient_localized_isIso`、`relativeCoreSAdditivityMap_localized_isIso`
- `sClosedStableIso`、`sRelativeCofiberStableIso`、`relativeMultiRealizationAdditivityLocalizedIso`、`cutStableComparison`、`cutRelativeEquivalence`、`cutRelativeSegalPair`、`cutLeftIntervalEquivalence`、`cutRightIntervalEquivalence`、`StableModelEquivalence`、`multiRealization_map_localized_isIso_of_equivalence`、`cutSegalMap_localized_isIso`、`cutSegalLocalizedIso`、`edgeSegalMap_localized_isIso`、`edgeSegalMap_projection`、`pathHeadSegalMap`、`iteratedPathBoundary_headPreserving_homotopyPullback`、`iteratedPathBoundary_homotopyPullback`、`iteratedPathBoundary_realization_homotopyPullback`、`localized_isIso_of_connected_baseChange`、`zeroRowPathFiberComparison_localized_isIso`、`zeroRowKanFiberComparison_piIsomorphism`、`zeroRowKanPreviousComparison_piIsomorphism`、`exists_previousStage_pathFiber_comparison`、`sInterchangeStableIso`、`diagonalFixedSInterchangeNatIso`、`sOneInnerOuterRealizationIso`、`sOneInnerOuterRealizationIso_comparison`、`diagonalFixedSInterchangeNatIso_index`、`iteratedSRealizationCyclicIso`、`sOneInnerOuterRealizationIso_assembly`、`multiFixedSEndofunctorIso`、`multiSOneSlideCoreIso`、`coordinateZeroBoundary_image_iso`、`sOneInnerOuterReducedIso`、`sOneInnerOuterReducedIso_comparison`、`multiFixedSEndofunctorIso_index`、`multiMovingSCoreIso`、`multiMovingSBoundaryIso`、`coordinateZeroBoundary_permutation`、`innerVariableSComparisonIso_outer_naturality`、`multiInnerSCoordinateNatIso`、`multiInnerSCoordinateCoreIso_realization`、`cyclicBoundaryIso`、`cyclicBoundaryIso_coordinate_quotient`、`simplicialPathDiagonalCylinder_zeroRow_boundary`、`reducedPathDiagonalBasedContraction`、`zeroRowPathContractionHomotopy`、`zeroRowPathContraction_boundary`、`zeroRowPathContraction_degeneracy`、`loopOfCylinder`、`loopOfCylinder_constant_parameter`、`zeroRowLoopComparison`、`zeroRowLoopComparison_assembly`、`zeroRowPointedLoopComparison`、`zeroRowKanLoopComparison`、`loop_interval_hom_ext`、`suspensionLoopEquiv_interval`、`kanTargetAssemblyAdjoint_interval`、`zeroRowLoopComparison_assemblyAdjoint`、`zeroRowReducedLoopComparison`、`zeroRowReducedLoopComparison_quotient`、`zeroRowLoopComparison_fatBoundary`、`terminalPathSpace`、`terminalPathStart`、`terminalPathSpace_isContractibleKan`、`terminalSuffixFamily`、`terminalFiberHomotopy`、`zeroRowTerminalFiberHomotopy`、`zeroRowTerminalLoopFiberComparison_localized_isIso`、`terminalEndpointCircleIso`、`loopToTerminalPathHomotopyFiber_piIsomorphism`、`zeroRowLoopComparison_terminalFactor`、`zeroRowKanLoopComparison_piIsomorphism`、`kanAssemblyAdjointAt_piIsomorphism`、`boundaryKanAssemblyAdjoint_piIsomorphism`、`boundaryKanSequence_omegaCondition`、`boundaryOmegaSpectrum`、`kKanSequence_omegaCondition`、`kOmegaSpectrum`、`kSpaceSpectrumComparison_piIsomorphism`、`kOmegaSpectrum_negative_subsingleton`、`kOmegaSpectrum_zeroGroupEquiv`、`kSpectrumMap`、`kHomotopyFunctor`、`kHomotopyStageIso`、`kHomotopyZeroPiZeroIso`、`coreSOnePiZeroEquiv`、`objectKPiZeroClass`、`objectKClass`、`objectKPiZeroClass_sOne`、`homotopyObjectKClass`、`homotopyObjectKClass_iso`、`objectKClass_of_isZero`、`zeroRowLoopComparison_naturality`、`objectKClass_naturality`、`kZeroFundamentalGroupEquiv`、`kZeroFundamentalGroupEquiv_objectKClass`、`objectBoundaryEdge_loop`、`objectKClass_sTwo`、`objectKClass_cofiber`、`homotopyObjectKClass_triangle`、`triangulatedKZeroMap`、`triangulatedKZeroMap_vertex`、`triangulatedKZeroMap_naturality`、`simplicialFundamentalGroupoid`、`fundamentalGroupoidEquivalence`、`kanAnodyne_hom_rec`、`fundamentalLoopHomEquiv`、`kanAnodyneLoopPresentation`、`kZeroGroupoidPresentation`、`objectRawBoundaryEdge`、`objectBoundaryPath`、`kZeroGroupoidPresentation_objectKClass`、`boundaryReducedRealization_vertex_eq`、`rawBoundaryPath_diagonal`、`rawBoundaryPath_cases`、`triangulatedKZeroMap_surjective`、`objectTriangulatedFunctor`、`objectRawBoundaryComparison_localized_isIso`、`rawBoundaryTriangulatedHomotopy`、`boundaryKanTriangulatedMap_unit`、`kZeroToTriangulatedMap`、`kZeroToTriangulatedMap_object_formula`、`exists_closedObjectSOne`、`kZeroToTriangulatedMap_object`、`kZeroToTriangulatedMap_left_inverse`、`kZeroToTriangulatedMap_right_inverse`、`triangulatedKZeroEquiv`、`triangulatedKZeroNatIso`、`triangulatedKZeroPiZeroIso`、`pointedExtensionTransport`、`pointedExtensionTransport_comp`、`kanAssemblyMixedChoices`、`kanAssemblyMixedFromSource`、`kanAssemblyMixedFromTarget`、`kanAssemblyMixedPost`、`kanAssemblyMixedPre`、`kanAssemblyMixedChoices_fill_boundary`、`kanAssemblyMixedPost_source`、`kanAssemblyMixedPre_target`、`kanAssemblyMixed_middle`、`kanAssemblyCompositionTriangle_nonempty`、`pointedLiftSpace`、`pointedMappingPathSectionSpace`、`pointedMappingPathInverseAt_homotopy`、`pointedMappingPathInverseFamily`、`oneDirectionKanInverseChoices`、`oneDirectionKanInverseAt_component`、`mappingPathTransport`、`oneDirectionMappingPathFunctor`、`pointedLiftTransport`、`oneDirectionInverseMixedChoices`、`oneDirectionKanInverseAt_naturality_homotopy`、`oneDirectionInverseCompositionTriangle_nonempty`、`boundaryKanAssemblyChoices`、`boundaryKanAssemblyAdjointFamily`、`boundaryKanAssemblyAdjointAt_piIsomorphism`、`kanAssemblyMixedFamily_target`、`oneDirectionInverseMixedFamily_source`、`boundaryAssemblyNaturalityFamilies_middle`、`boundaryAssemblyNaturalityFamilies_source`、`boundaryAssemblyNaturalityFamilies_target`、`boundaryAssemblyNaturalityCylinderFamily`、`doubleCylinder_toUnit_localized_isIso`、`boundaryAssemblyNaturalityParameters`、`boundaryAssemblyNaturalityParameters_relative_lifting`、`boundaryAssemblyNaturalityFamilyChoices`、`boundaryAssemblyNaturalityFamilyAt_source`、`boundaryAssemblyNaturalityFamilyAt_target`、`boundaryKanAssemblyAdjointAt_naturality_homotopy`、`boundaryAssemblyCanonicalPath_evaluated_fac`、`boundaryAssemblyMiddleParameterEdge_evaluation`、`assemblyCrossedFamily_edge_interchange`、`assemblyCrossedFamily_inverse_source`、`assemblyCrossedFamily_extension_target`、`BoundaryAssemblyNaturalityData`、`boundaryAssemblyNaturalityFactorizationTriangle_nonempty`、`boundaryAssemblyCompositionTriangle_nonempty`、`AssemblyInputArrow`、`kanAssemblyInputArrowDiagram`、`oneDirectionInverseInputArrowDiagram`、`kanAssemblyCoherentChoices`、`oneDirectionInverseCoherentChoices`、`kanAssemblyCoherentSection_extension`、`oneDirectionInverseCoherentSection_extension`、`kanAssemblyCoherentEvaluation_app`、`oneDirectionInverseCoherentEvaluation_app`、`kanAssemblyInputIdentityChoicesIso`、`oneDirectionInverseInputIdentityChoicesIso`、`boundaryKanAssemblyCoherentAdjointAt_piIsomorphism`、`kanAssemblyCoherentSourceEdge`、`kanAssemblyCoherentTargetEdge`、`oneDirectionInverseCoherentLegTriangle_nonempty`、`diagramSelectionCompositionTriangle_nonempty`、`kanCospanPastingChoices_isContractibleKan`、`diagramUniversalFamily_evaluation`、`diagramUniversalCospanPastingFamily`、`diagramUniversalCospanPastedTriangle`、`kanAssemblyCoherentPastingFamily`、`oneDirectionInverseCoherentPastingChoices_relative_lifting`、`PointedKanInfinity`、`pointedKanDiagramFunctorIso`、`pointedKanDiagramExtensionHomotopy`、`oneDirectionCoherentInverseHomotopy`、`boundaryAssemblyCoherentDiagramHomotopy`、`boundaryAssemblyCoherentDiagramTriangle`、`boundaryAssemblyCoherentDiagramMapAt`、`pointedKanHomotopyClass_eq_iff`、`pointedKanObject_component_comp_of_triangle`、`pointedKanDiagramTriangle_components`、`pointedKanDiagramInverse_right_component`、`pointedKanDiagramExtensionMapAt_component`、`boundaryAssemblyCoherentDiagramMapAt_component`、`boundaryAssemblyCoherentDiagramMapAt_original_homotopy`、`boundaryAssemblyCoherentDiagramMapAt_piIsomorphism`、`boundaryAssemblyCoherentDiagramIso`、`exists_fixedEndpoint_restriction_correction`、`vertexDiscretePinched_piZero_injective`、`exists_pointedKanDiagram_specified_components`、`exists_boundaryAssemblySpecifiedCoherentHomotopy`、`boundaryAssemblyOriginalCoherentHomotopy_component`、`boundaryAssemblyOriginalCoherentHomotopy_vertex_edge`、`boundaryAssemblyOriginalCoherentIso`、`suspensionLoopMappingIso`、`suspensionLoopMappingFamily_prePointed`、`boundaryKanAssemblySigmaFamily`、`boundaryAssemblySuspensionCylinderFamily_source`、`boundaryAssemblySuspensionCylinderFamily_target`、`suspensionLoopMappingFamilies_inv_pre`、`pointedLoopHom`、`pointedKanLoopInfinity`、`pointedKanLoopInfinity_diagram`、`boundaryAssemblyNativeOmegaHomotopy`、`boundaryAssemblyNativeOmegaIso`、`kKanSequenceLevelFunctor_map`、`kKanCoherentLevelDiagram`、`kKanNativeOmegaIso`、`suspensionLoopMappingFamilies_inv_post`、`EnrichedFunctorCollageInfinity`、`enrichedFunctorCollageProjectionInfinity`、`loopCollageEvaluationNerve`、`loopCollageCrossMap_projection`、`loopCollageCrossMap_evaluation`、`enrichedFunctorCollageCross_pre`、`enrichedFunctorCollageCross_post`、`enrichedFunctorCollageComparison`、`enrichedFunctorCollageComparisonHomotopy`、`enrichedFunctorCollageTransportTriangle`、`boundaryAssemblyCollageTriangle`、`boundaryAssemblySuspensionTransportHomotopy`

### 依存と提供
- 所有は `SerrePositivity/KST/SConstruction/`、集約、監査スクリプト、本計画。namespace は同名。
- 読取専用：Core（F0、関手圏の点ごとの極限等）、Stable（α-S）、F1/F1B（core・充満包含）、
  Spectra（L9）、Comparison（L2）、HomotopicalAlgebra（具体的 Kan 置換・局所化・対角）。
- 提供：全 gapped S• と第一行の完全な比較、安定な入力の完全関手の圏、object/core 実現比較、ρ の cofiber・gapped 性、左 fiber 内の二ホモトピー、quotient 射の局所化同型、単体積版 Quillen A、全 cofiber 図式の object/core 単回実現の加法性、S/cofiber の厳密な交換同型、正の全有限反復実現の自然な加法性、S₂ の二区間への分解、閉じた全部分圏と相対 E(A,C,B) の安定性・完全な評価、相対 object/core 単回実現と全正有限反復 core S• 実現の加法性、S_n と全部分圏・相対図式の厳密な交換同型、相対入力に関する全正反復加法性の自然同型、切断の左右支持部分圏と短い区間の S 構成の実際の同値、左右支持の相対 E と S_n C の実際の同値、元の Segal 射対の厳密な比較式、全正有限反復実現による完全な同値の保存、任意の切断位置の元の Segal 射の自然な局所化同型、全連続辺への Segal 同値、全単体作用素の元の経路境界の homotopy pullback、全ての行と全対角の homotopy pullback 比較、元の零行から既存 fiber への局所化同型、前段の既存 Kan 実現と既存 fiber への同じ Kan 模型からの全基点 π_* 比較、S/S の厳密な交換、全反復 S₁ の内外比較と元の区間族の可換性、独立な全多次数の交換と自然性、源の全零境界と既存の境界商の比較同型、全方向を動かす巡回交換と独立な全零方向の境界商の比較、座標置換の全零境界保存、標準の既存境界商の巡回自己同型、元の収縮の零行への制限と区間組み立ての厳密な式、元の点つき経路商の基点固定収縮、既存 Kan 経路への零行収縮と退化像の全時刻の固定、元の円の商からの具体的な loop 射と評価の回収式、任意の零段基点に関する点つき射と厳密な Kan 延長、元の構造射の随伴との厳密な照合、元の全零境界商への降下と商射による回収、終点固定 fiber 内の元の収縮からの実ホモトピー、定数 path 比較と収縮境界 loop 型比較の局所化同型、元の随伴の全基点 π_* 同型と同じ境界商の BF Ω スペクトル、元の K 空間を零段に保つ連結 BF K スペクトル、全負整数次数消滅、整数 K 群の可換群への関手と任意段・零次数の自然な表示、元の対象の実際の BF K 類・S₁ 補完回収・同型不変性・零対象の零性・完全関手に関する自然性、元の S₂ の三辺と対象 loop の厳密な照合、任意の元の cofiber 正方形の加法関係、三角圏 K₀ からの対象類を保つ自然な準同型、置換前の元の辺と二単体の基本亜群による実際の零次 K 群の表示、単位・積・逆の照合と同じ object S₁ の辺の対象類の回収、任意の元の境界商の辺の対象辺への帰着と対象類による生成、比較準同型の全射性、元の object S の三角圏 K₀ 値の関手・境界商への実ホモトピーによる移送と既存の Kan 境界上の厳密な延長、実際の零次 K 群からの逆向き準同型と対象類の回収、二つの逆律、三角圏 K₀ との加法群同型と完全関手に関する自然同型、元の K 空間の π₀ との自然同型。
- スペクトル値の coherent 関手性・dg 関手性・Morita 不変性は未提供。条件付きの段を完成品に数えない。
- 将来接続：L9 の Ω・π_*・BF、既存の実現比較（L2 は Auxiliary として凍結）、α-S の h C の三角構造、N の dg nerve、D の Perf。

### 未コミット
- 担当分は検証済み保存単位（新規9モジュール・集約・監査スクリプト・本計画）にコミット。未保存の担当差分なし。
- 他レーンの作業中の差分・未追跡ファイルは触れていない。

### 既知の問題
- 対象ビルド6822 jobs、公理監査4647宣言、全体 lake build 17711 jobsが成功。担当 import 閉包の破損はない。
- 名前衝突の未解決例なし。Core・Stable・F1 等の公開名・型は本レーンで変更していない。
- SConstruction 内の明示的な `[ModelCategory SSet]` 引数は検索で見つからず。HA の具体的 instance と
  anodyne 局所化を利用。推移的依存を含む model instance 全体の棚卸しは別途必要。
- 4647宣言の監査は追加公理・sorry を検出しない状態。許可は propext・Classical.choice・Quot.sound のみ。
- raw ρ の型は Ar→Fun(正方形,C)。cofiber 値への持ち上げ・gapped 性・各角の strict 回収・左 fiber 条件は証明済み。二つの実ホモトピーと quotient 射の局所化同型まで証明済み。
- cofiber 図式の圏で任意に選んだ押し出しでは、subobject・quotient の strict な回収を結論できない。
- 正の Ω 条件は元の区間商上の厳密な評価・元の収縮の fiber 内のホモトピー・loop 包含の同定から証明済み。境界列は r+1 重 S の段。既存の K の列を別に BF 模型へ束ね、元の零段の保持と負次数消滅まで証明済み。
- C×C と S₂C の ∞ 圏の同値は主張しない。加法性は S• と実現の後の定理。
- Git は既存の gc.log と unreachable loose objects の警告を出す。整理操作はしていない。

### 次の一手
- 元の全比較三角形と全交換セルを貼る実複体 `monicKPrismNativePastingDomain`・実写像 `monicKPrismNativePastingMap` は構成済み。入口は元の全第二面、出口は補正済みの同じ後続適合円柱。`CylinderCellWalk` は複体内での各共有面と両端を厳密に保持する。全補正セルは二時刻だけを交換した元の同じ交換正方形で、両横境界と全 trace・順序を回収済み。`monicKPrismNativePasting_projected_full_trace` は次段補正の全射影を一側の境界へ、`_original_full_trace` は元の合成適合円柱と前段補正全体の構造射の像をもう一側の境界へ同定する。共通の後半末尾も省略していない。零段の補正セル列自体は空。次は、この同じ実複体と共有末尾から両端固定の辺路比較を取り出し、各段の有限補正列を元の全 trace を記録した一本の実比較円柱へ合成する。合成射の直接厳密化の元の補正列とも照合し、前段比較円柱の構造射による像との端点固定二次元比較を内部構成する。その証人を単射源の構造射の制限による相対持ち上げへ渡し、全段の実 raw 比較から BF 境界を固定する相対延長へ接続する。有限列の合成と相対比較の存在を入力の仮定にせず、実複体・Kan 充填・保存済み trace から構成する。`monicKPrismTracedBFFamily`・`kTracedFamilyLiftData`・`kPrescribedRawFamilyComparisonData` は構成済み。区間の順序や数の違う二列を成分の一致だけで同じ raw 族と見なさず、`monicKToRawMap` の成分の等式だけから互換な trace の存在や境界定数性を主張しない。現在は I:Type u、SmallCategory I、F:I→StableModel.{u}。旧自然性の指定辺との比較、大きい全入力添字・入力の高次射は残り、BF スペクトル値の coherent 関手性の完了はまだ主張しない。
- その後 dg 関手性・Morita 不変性、§6 の fibration と BGT (a)、§7 の Tamme・LT に進む。整数 K 群の関手や π₀ 比較をスペクトル値の coherent 関手性の代用にしない。Ind は N・α2b の F2-lite の供給を待つ。
- 検証は対象ビルドと `lake env lean scripts/audit_kst_s_construction.lean`。他レーンは編集しない。

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md` §8 と経路正本 §13 決定16を優先。非連結化は BGT (a) のみ。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c | KSpace.lean | 各段の core、対角実現・Kan 置換・Ω、反復 S• と L9 BF スペクトルへの接続 |
| L1d | Additivity.lean | McCarthy 型ホモトピーによる実現後の加法性 |
| L1e | PiZero.lean | π₀ K(C) ≃+ TriangulatedK0(h C)、対象類と自然性 |
| L1f | DGApplication.lean | K(N_dg(Perf_dg D))、dg 関手性、Morita 不変性 |
| L3 | §6 | fibration 定理、BGT (a) の非連結化、局所化不変量 |
| K-基盤 2 | §7 | Tamme の分裂、dg 増強流の ⊙ と Land–Tamme 主定理 |

## 4. 設計と実装前の文言

### Ar と gapped

Ar[n] は Fin(n+1) の対 (i,j), i≤j の成分ごとの順序の圏。
単調写像 θ:[m]→[n] は (i,j)↦(θi,θj) を誘導する。
図式圏は ihom(N Ar[n],C)。gapped は全対角 F(i,i) が零対象であり、
i≤j≤k≤l に対する F(i,k)→F(i,l), F(j,k)→F(j,l) の全四角が pushout となる条件。
S_n はこの頂点条件による充満部分単体集合。順序写像による前合成は条件を保つため、
選択を含まず Δᵒᵖ 上の単体的対象を与える。退化する四角にも同じ pushout 条件を課す。

### §10-13：gapped と第一行

原典の結論は Gap([n],C)→Fun(Δ^{1,…,n},C) の ∞ 圏の同値である。
これだけから literal な trivial Kan fibration と結論しない。
要求された元の制限写像について、有限個の相対 cocartesian completion を積み上げ、
零対象と余極限錐の相対境界持ち上げ性から全境界に対する RLP を証明する。
n=0 は零対象の空間として別処理する。全 gapped 図式を保ち、第一行の選択模型に置換しない。
不足する相対拡張補題は本レーン内で証明する。設計変更が必要なら実装前に提案する。
Ar[n] と正方形の積から (0,i),(0,j),(i,i),(i,j) への自然な添字写像を用い、
gapped 図式の全 cofiber 四角形を一つの族として取り出す。
その族は右上角の評価で元の図式を厳密に回収するため、境界上の既存データを保持できる。
相対 cofiber 補完をこの Ar[n] パラメーターに適用する際は、第一行と対角での条件を同時に固定する。
得られる右上角の図式の全四角形が押し出しとなることは、余極限の普遍性と押し出しの貼り合わせから
別に証明する。単に各区間に cofiber を持つことだけで gapped 条件を結論しない。
点ごとの余極限・押し出しを関手 ∞ 圏へ移す向きは、相対始点境界充填と内部 Hom の交換で証明する。
正次元のパラメーター境界では全頂点が指定されているため、境界を厳密に保つ補完の gapped 性は
全部分複体の頂点条件から回収できる。零次元の gapped 性および出力の第一行の厳密な回収は別条件として残す。

### §10-11：加法性

E(A,C,B) の cofiber 列から subobject・quotient への射について、
|core S•E|→|core S•A|×|core S•B| が同値となることを証明する。
E≃A×B という ∞ 圏レベルの誤った主張にはしない。
Fiore–Pieper の McCarthy 型の経路を用い、普遍的 cocartesian completion の制限自明
ファイブレーションでパラメータ付き pushout を選び、単体ホモトピー、単体積版 Quillen A、
対角実現、object/core 比較を証明する。Waldhausen の元の証明からの経路変更を明記する。

### §10-12：最小 fibration 定理（後続 L3 の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と BGT §9 の非連結化を経由する。L11 では ∞ 版全体は未検証である。
今回の L1a–f の成果としてこの定理を完成扱いしない。

### K と界面

L9 の基点・Ω・π_* の座標に従う。BF 模型は単射 ΣX_n→X_(n+1) と、随伴の全基点 π_* 同型。
厳密な Ω 同型を要求しない。未着 API は明示的な入力として隔離し、証明済みの構成と区別する。
π₀ は一般 dg 圏の H⁰D でなく、小さい Perf の H⁰ の TriangulatedK0 と比較する。
S4 未着時は cofiber 列の像が distinguished triangle になる仮定を明記する。
相対 K は L9 のスペクトル fiber を優先し、次数ごとの kernel/cokernel から復元しない。
Kₙ の境界・比較同型は自然性と対象類の式を含む。宇宙は S1.1 に従い小さい模型にそろえる。

## 5. 検証・保存

各保存単位で `lake build SerrePositivity.KST.SConstruction` と
`lake env lean scripts/audit_kst_s_construction.lean` を実行する。
公開宣言を #check / #print axioms で監査し、許可するのは propext、Classical.choice、Quot.sound のみ。
全体ビルドは工程の区切りで行う。自分の import 閉包外の並行作業の失敗は記録して続ける。
自分の検証済みファイルだけを保存し、経緯はコミットメッセージに記す。

## 6. L3・K-基盤 1（L1c〜f の後）

- **担当境界**：K の fibration・局所化定理は本レーン。Drinfeld 商の dg nerve と ∞ 圏的 Verdier 商の比較・Verdier 列の供給は D レーン β3。H⁰ の普遍性だけで mapping 空間の比較を代用しない。
- **Ind を待つ間**：小さい安定 ∞ 圏の完全関手を基礎に、冪等完備性の述語、Cat^perf の対象・射、Verdier 列、半直交分解、Sp 値の局所化不変量の定義と分裂列の帰結を整える。Cat^perf の ∞ 圏としての構成・極限は α2b の Cat_∞ に接続する。冪等完備化の存在を未証明の仮定で完成扱いしない。
- **fibration**：W の2-out-of-3・pushout・extension 安定性、S• の相対構成と加法性から連結版を証明し、必要な cofinality を明示する（Waldhausen 1985 §1.6、BGT §7–9、80–160時間）。β3 の商との比較は到着後に接続する。
- **非連結化は BGT (a) のみ**：N の Ind・κ-compact・冪等完備化と α2b の F2-lite を待ち、BGT §9 の suspension と反復 colimit により定義する（80–160時間）。Schlichting 暫定版 (b)・Bass による定義は導入しない。
- **完了条件**：冪等完備 Verdier 列を fiber 列に送る非連結 K、Morita 不変性、filtered 余極限との可換、連結 K との比較を証明する。値域の ∞ 圏 Sp は Sp レーンの供給を使い、局所化不変量の構造体にモデル圏 instance を要求しない（BGT §8–9、40–100時間）。

## 7. K-基盤 2（dg 増強流）

- **Tamme**：完全関手の lax pullback、標準包含・射影、半直交分解と分裂列を構成し、任意の局所化不変量で分裂を証明する（Tamme 2018 §1、60–120時間）。Cat_∞ の極限は α2b、dg gluing との比較は D の β4 を読み取り専用で使う。
- **Land–Tamme の ⊙**：dg 代数の Milnor 四角形から Perf の lax pullback と対角像の Verdier 商を作り、生成元の dg 自己準同型代数として A′ ⊙_A B を構成する。D の β3・β4・β5（非可換 D(A)・相対テンソル・Morita）を使う（Land–Tamme 2019 §1–2、100–200時間）。E₁ 環スペクトル・HA §2–4 の構成には進まない。
- **主定理**：Tamme の分裂と上の Verdier 列から、B′ を ⊙ に置き換えた四角形を全ての局所化不変量が引き戻しに送ると証明する。dg の対象供給と ∞ 圏の形式的議論を接続する（Land–Tamme §2、60–120時間）。
- **pro 版**：Tor の pro 消滅から ⊙→B′ の比較を経て pro 切除へ。Tor の環論は L7 の入力を待つ（Land–Tamme §3、80–160時間）。第 II 段のスキーム応用は基盤 I-a・I-b が閉じるまで起動しない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L1-s-construction-log.md](archive/L1-s-construction-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
