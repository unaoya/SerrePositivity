# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）
- **現在地**：γ1.5 完了。γ3b は任意の小圏で元の非反転 q_x の同値性・全導来 fiber の可縮性による両向き判定と、pinched Hom の直接 fiber 模型まで公開。
  γ3c は 𝒮 の小積・Sp の有限積（空積含む）、一脚 fibration の引き戻し、fibration の塔の実際の ∞ 極限を公開。
  𝒮 の小余積・任意の span・任意の列の ∞ 余極限も公開。
  通常の随伴と整合する単体的 Hom 同型からの極限保存と、豊穣右関手の coherent nerve による像との一致を証明。
  任意の coherent な極限錐にも適用できる。γ4 の具体例 `K × − ⊣ Map(K,−)` は通常の随伴・豊穣 Hom 同型・零単体を照合。
  両対象の anodyne Kan 置換を含む frame Hom の可換性を全単体で検証し、固定した Quillen 類の保存も公開。
  一般の小図式の重み付き coend、tensor と内部 Hom の普遍性、反転係数の end との自然な同型を構成。
  Kan 置換後の Hom 比較は全 Hom パラメータの豊穣合成を保ち、恒等射の普遍切断点から復元できる。
  実際の coherent な余錐を構成し、頂点を Kan 置換した反転 coend と同定。
  通常の任意の小圏上の Kan 値図式では、構成した反対錐の ∞ 極限性・元の native な余錐の ∞ 余極限性を無条件に証明。
  任意の coherent な図式の切断空間は、形状の押し出しの引き戻し・セル付加・相対骨格の塔の厳密な極限で表示。
  left fibration では塔の各値は Kan、制限は Kan fibration。図式の底上の通常の余極限についても一般化済み。
  部分余極限頂点を付加した実際の形状と図式、指定した余錐を頂点ごと保つ延長と余極限性の保存・反映を構成。
  全ての脚を含む coherent な比較と実際の頂点間の射を抽出し、部分余極限対象の Kan 値 span とその押し出し候補を構成。
  始対象の fiber の Hom 表示と部分余錐の制限の π₀ の像を、付加比較辺そのものの類と同定。二重 coslice の比較辺の終点・射影も検証。
  共通部分で同じ連結成分にある部分余錐は、単射側を同じ成分内で直して厳密に貼れることを証明。
  fiber の Hom 表示で辺に沿う輸送が後合成になることを証明し、図式の制限との自然性を照合。
  二枝の比較辺と輸送辺の合成が一致すれば、元の図式の実際の余錐を厳密に貼れる。
  余錐の脚の合成三角形を span の実際の二辺と照合し、元の coherent 図式の余錐を構成。
  その頂点は部分余極限対象の span の小さい Kan 押し出し。
  形状の押し出しに対し、余錐全体の coslice と固定頂点の余錐空間の厳密な引き戻し表示を構成。
  単射な境界側の制限は Kan fibration。固定頂点の余錐空間自体を頂点とする native な ∞ 極限錐も公開。
  始対象の Hom 比較と底上の関手の作用を、実際の比較辺の合成三角形の族で全単体において照合。
  固定終点の左 pinched Hom の前合成を構成し、部分余錐の制限の Hom 比較の正方形を単体的ホモトピーで結ぶ。
  底に使う辺は既存の付加比較辺そのもの。二枝のホモトピーを path 置換への厳密な自然変換へ束ねた。
  元の余錐空間から部分余極限頂点の Hom の Bousfield–Kan end への実際の比較射とホモトピー同値性を証明。
  通常の span の nerve とホーンの全次数の同型・二辺の一致を構成。固定終点余錐空間を点 Hom の end と比較し、ホモトピー同値性を証明。
  持ち上げた span の二辺も付加比較辺そのものと同定。点 Hom と左 pinched Hom の cospan・end の厳密な自然同型を構成。
  元の余錐空間から native な span の余錐空間への実際のホモトピー同値と、共通 end への比較のホモトピーを公開。
  任意の余錐の全左 Hom による余錐の族を、元の余錐の余極限性を仮定せず構成。部分図式への制限を実際の付加比較辺の前合成とホモトピーで照合。
  既知の余極限余錐では、その族と既存の Hom 比較が互いに実際のホモトピー逆となることも証明。
  fiber の同じ成分への修正を、底の辺を一単体として保つ輸送辺へ織り込んだ。貼った余錐の両枝に span の実際の脚を被覆する比較辺を構成。
  その二枝の全 Hom の族と脚の前合成のホモトピーを同時に公開。
  指定境界経路の全パラメータ族を保つ右枝の修正と厳密な余錐族の貼り合わせを構成。パラメータ変更に厳密に自然。
  同じ経路と右枝を持つ持ち上げの相対ホモトピーも構成。普遍 span の実際の二単体から境界経路を抽出し、その指定経路で元の余錐を構成。
  左枝・右修正端点・修正経路の底・小さい Kan 押し出し頂点を照合。全 Hom の族から始対象性を反映し、end の同値性との余極限性の必要十分条件を証明。
  普遍 span の全 Hom の族から共通 path end への無条件の同値と、元の族の全パラメータ係数公式を公開。
  始対象を前置した指定四面体の底の辺 03 を、元の native な共通脚そのものと同定。全 Hom の族をその脚へ制限し、両端の係数を厳密に計算。
  共通部分の Hom 比較は、同じ指定余錐の頂点からの Hom 上で元の共通脚の前合成とホモトピック。元の余錐の余極限性は不要。
  元の二単体・標準二辺の三角形 prism と、底・始点を固定した長辺比較をデータ化。span の境界経路をこの比較へ差し替えた。
  二辺固定三角形の比較と単射パラメータ境界の延長を構成。指定頂点の三角形・二辺・元の二単体を照合し、対角辺と可変終点を保つ全 Hom 族を非退化な三角形全体に延長。始対象 Hom 比較も評価固定の実際の円柱として保持。end 内の整合性は未完了。
  指定比較円柱を可縮な延長空間の実際の辺として保持し、終点評価が元の合成ホモトピーの辺と厳密に一致することを証明。同じ二頂点を結ぶ比較辺の類と終点での像の一意性も公開。
  γ3c 全体・一般の γ4 は未完了。F2-lite 第 2 部の分担と工程は `infinity-core-F2.md` §3。
- **残り**（依存順・時間は再開後の概算）：
  1. γ3c：通常の小圏上の Kan 値図式の coend 余極限から、任意の coherent な図式への接続。HTT 4.2.4.1、Kerodon 7.5.4.6、20〜50時間。
  2. γ4：具体例を一般の simplicial Quillen 随伴の cofibrant-fibrant 置換・frame へ拡張する。HTT 5.2.4.6、8〜20時間。
  3. 2 と F1b の随伴 API から導来 ∞ 随伴の単位・余単位・整合性と一般の右導来関手の極限保存を構成する。HTT 5.2.4.6、Kerodon §6.2、12〜30時間。
  4. E2a-3・4 と γ2 の豊穣化の確定後、Alg_E と忘却関手へ適用する。HTT 1.1.5.10・4.2.4.1・5.2.4.6、16〜40時間。E2a の現状は下記参照。
- **主要宣言**（名前のみ。名前空間 SerrePositivity.InfinityCategories.HomotopyLimits）：
  `strictCoherentCone_isLimit_iff_general_comparisonFiber`、`strictConePinched_generalOriginalEnd_equivalence`、
  `spaceProductCone_isLimitCone`、`spacePullbackCone_isLimitCone`、`spaceTowerCone_isLimitCone`、
  `spaceArbitraryPushoutCocone_isColimitCone`、`spaceArbitrarySequentialColimitCocone_isColimitCone`、
  `SimplicialAdjunctionHomIso`、`strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso`、
  `kanTensorAdjunctionHomIso`、`kanInternalHom_map_isLimit`、`kanReplacedTensorFrameAdjunction_square`、
  `reflectedWeightedColimitHomIso`、`bousfieldKanCoherentConeComparison_homotopyEquivalence`、
  `bousfieldKanCoherentCocone`、`bousfieldKanCoherentCocone_vertex`、
  `coherentCone_isLimit_iff_reflectedNativeComparison`、`coherentConeFamily_homotopy_over_apex`、
  `coherentCone_isLimit_of_family_lifts`、`bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts`、
  `kanReflectedBousfieldKanColimitHomComparison_of_point`、`bousfieldKanCoherentConePoint_of_end_point`、
  `coherentCosliceSourcePrecomposition_weighted`、`coneIdentityCosliceSection`、
  `bousfieldKanCoherentConeSourceFamily_restrict`、`bousfieldKanCoherentOppositeCone_isLimit`、
  `bousfieldKanCoherentCocone_isColimit`、`kanDiagramCoherentNerve_hasColimit`、
  `skeletalSectionCone_isLimit`、`skeletalSectionDiagram_map_fibration`、`skeletalCellSectionCone_isLimit`、
  `colimitAttachedCocone`、`colimitAttachmentComparison_restrict`、`colimitAttachmentApexHom`、
  `cosliceShapePushoutIso`、`coconeMappingShapePushoutIso`、`coconeMappingShapeCone_isLimit`、
  `initialRestrictionHomComparison_square`、`colimitAttachmentHomPrecomposition`、
  `coconeMappingSpaceHomComparison_restrict_square`、
  `partialColimitCoconeToHomEnd`、`partialColimitCoconeToHomEnd_homotopyEquivalence`、
  `spanNerveHornIso`、`partialColimitSpanHomEndIso`、
  `partialColimitOriginalToNativeSpanCocones_homotopyEquivalence`、
  `coconePointHomFamily_restriction_homotopy`、`coconePointHomFamily_comparison_homotopy`、
  `exists_partialColimitPushout_cocone_with_branch_homotopies`、`coconeBoundaryPathRectifiedFamily`、
  `coconeBoundaryPathCorrection_unique_homotopy`、`partialColimitSpanBoundaryPath`、
  `partialColimitSpecifiedPathCocone`、`isColimitCone_iff_partialColimitHomFamilyToPathEnd`、
  `nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence`、`specifiedPathCocone_isColimit_of_pathFamily_homotopy`、
  `coherentTransportTrianglePointCompStruct_projection`、`transportTriangleInitialHomComparisonHomotopy_projection`、
  `specifiedCoconeCommonHomFamily_rootPrecomposition_homotopy`、
  `coherentTransportComparisonEndpointEdge_eq`、`transportPrismExtensionEdge_endpoint_homMk_eq`。
- **依存と提供**：Core・F1（coherent Hom、切断、edgewise、通常の豊穣関手）、F1b（trivial fibration 上の相対ホモトピー）、Stable、KST/Spectra、Simplicial の小対象分解を読み取り専用で使用。
  提供先は F2 の 𝒮、L9／K-Sp の Sp、E2b。集約は InfinityCategories/HomotopyLimits.lean、監査は scripts/audit_homotopy_limits.lean。
  型は Lean、運用規約は foundations.md §8。README に実施記録は追記しない。
- **未コミット**：今回の保存単位は prism 頂点評価・点の辺・点の三角形・相対長辺切断・全 Hom 三角形族・始対象 Hom 比較6新規モジュール、集約・監査、本 N 節、F2 計画 §3。保存後は N 所有の変更なし。共有計画は N 節だけをステージする。
  root の迷子 RelativeFreePathBoundary は正しい場所に修正版がコミット済みの N 旧稿と確認し、削除済み。
- **既知の問題**：停止時の対象ビルド・監査に失敗なし。新規 sorry・追加公理・公開名衝突なし。監査の既存の重複1件を除去済み。
  今回の公開型に ModelCategory SSet や IsRightQuillen の追加仮定なし。SSet の充填性・cofibrancy は Mathlib の固定 Quillen 類を使用。root 全体は未検証。
  完全なモデル構造の存在を与える `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので主経路へ import しない。
  今回はその存在命題を使わず固定類の保存と Hom 比較を証明しており、一般のモデル圏からの導出を済ませたとは数えない。
  γ4 用の Hom 同型は y に全単体で自然、x の高次豊穣自然性は未要求。従って通常の Quillen 条件だけからの ∞ 随伴の完成とは数えない。
  Sp では指定した Hom の局所 Kan 性・Ω 条件・cofibrancy を保持。一般の図式と右導来関手の cf 置換・高次整合性は後続課題。
  `(edgeTransport_composition_iso p σ).some` は同じ三辺の異なる σ でも同じ値となることを Lean の rfl で確認。選択した同型だけでは元の二単体の高次情報が残らない。
  `partialColimitSpanTransportIso` は実際の三角形 prism と相対ホモトピーから作る同型へ差し替え済み。元の比較円柱への射影も公開。end 内での高次整合性の証明は残る。
  依存が壊れたら回避せず停止する。他レーンの作業中変更はコミットしない。
- **次の一手**：`specifiedPathCocone_isColimit_of_pathFamily_homotopy` の全終点の族のホモトピー入力を構成する。
  元の族は `partialColimitHomFamilyToPathEnd`、同じ頂点で表示した比較先は `specifiedCoconeNativeFamilyToPathEnd`。
  後者の同値性は無条件に証明済み。前者とのホモトピーを仮定した定理は、余極限性の完成とは数えない。
  共通余錐 c の始対象の fiber 頂点に `transportTriangleInitialHomComparison` とその実際の Hom ホモトピーを適用。左右の終点の底を同じ span 頂点に揃え、指定比較円柱と元の全 Hom 係数の境界を同時に照合する。
  同じ経路の持ち上げの相対ホモトピーを共通 end に移して入力を閉じる。その後、骨格の無限段階とセルの添字の小ささを処理。
  任意の coherent 図式の余極限性を閉じてから γ4、F2-lite 第 2 部へ進む。

### E2a（既存の引き継ぎ）

- **現在地**：E2a-0（Ch(A) の射影モデル構造）、E2a-1（オペラッド・自由代数随伴）、
  E2a-2（Barratt–Eccles オペラッド・augmentation）まで完了。
  E2a-3 は承認済みの Hopf オペラッド＋区間＋path object 経路で、工程 (1) が完了。
  一般の小さい単体集合の正規化 AW 対角の鎖写像・自然性・余結合性・左右余単位と、
  一般 shuffle 鎖写像の AW 余代数射性を検証し、整数模型へ移送済み。
  `partialComposition_diagonal_tensorμ` が既存 BE 部分合成の余積適合性を与える。
  arity ごとのテンソルオペラッド `Operad.hadamard` を、両単位則・内外等変性・
  入れ子と独立な代入の結合則を含めて構成。頂点の群状元公式から単位保存を証明し、
  `hopfDiagonal` を実際の E → E ⊗ E のオペラッド射に束ねた。
  `BarrattEccles.hopf` はこの対角、既存の E → Com、余結合性・左右余単位則を持つ。
  Σ_n 同変性は対称列の自然性に含まれ、余可換性は要求しない。
  工程 (2) は P-coalgebra・射の圏・忘却関手・オペラッド射に沿う制限を構成済み。
  `CoalgebraInterval` は実際の余代数・二端点・収縮・余演算の保存図式と、
  底の境界 cofibration・収縮の擬同型からなる。区間の制限も構成済み。
  convolution の反復評価とその両変数自然性、各 arity の演算 chain map は構成済み。
  底の Hom(H,B) の `prepathComplex`、定数射と両端点評価の自然性も検証済み。
  単位則・全置換の等変性・代数射の後合成による全演算の保存を検証済み。
  `convolutionAction_comp` で全位置の部分合成則を閉じ、`convolutionAlgebra` を構成。
  前合成・後合成を代数射と `convolutionFunctor`・`convolutionPreNat` へ束ねた。
  `unitCoalgebra ε` は任意の augmentation の単位余代数。`convolutionUnitNatIso` は
  Hom(単位,B) ≅ B を自然な P 代数同型にする。区間の端点・収縮も余代数射に束ねた。
  `prepathAlgebra` は全代数の自己関手と自然な定数・両端点評価を持ち、底の既存の射と厳密に一致。
  `evaluationPair_projectiveFibration` は底の二端点評価の対が射影 fibration であることを示す。
  `constant_quasiIso` と `evaluation_quasiIso` は任意の値域で定数射・両評価の底の擬同型性を示す。
  単位の cofibrancy、端点の鎖ホモトピー逆、符号付き Hom 前合成の移送から導出済み。
  `Algebra.binaryProductIsLimit`・`terminalAlgebraIsTerminal` で積・終対象を底の複体に構成。
  `pathAlgebra` は全代数の good path object。忘却の逆像の弱同値・fibration は局所選択。
  `fibrations_llp_quasiIso` は retraction と逆合成の path から底の擬同型性を示す。
  自由像の `freeGeneratingTrivialCofibrations_cell_acyclicity` は任意の始域で成立。
  一般の極限余極限・自由像の小対象性・転送定理の適用は未完成。
  E2a-3 の工程 (2) の転送と工程 (3)・(4)、E2a-4・5、E2b・G1′ は未完成。
  現在地のコードと検証は本節と同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. 代数の積と終対象を底で構成し、忘却関手との比較から good functorial path object を完成。
     続いてこの path object から底のホモトピー同値性を示し、
     小対象性・一般の極限余極限と転送の適用を閉じる。J-cell acyclicity は構成済み。
     Berger–Moerdijk（BM）2003 命題 4.1・§4.6.3、BF §3.1、24〜60 時間。
  2. TR : E → χ のオペラッド射性を一般に証明し、χ の区間切断作用を Δ¹ に適用する。
     BF §1.3・§3.1 と McClure–Smith の区間切断作用、80〜200 時間。
     着手前にファイル数・主要補題の見積もりを計画に一段落で記す指示が未実施。
     Δ¹ の作用は必要次数 r ≤ n に特殊化してよい。TR 自体は一般に証明する。
  3. 具体区間を抽象界面へ代入して E2a-3 を完成。BM 命題 4.1、BF §3.1、8〜24 時間。
  4. E2a-4：右 Quillen、全対象 fibrant、底での homotopy 引き戻し、H⁰ の可換環構造、
     離散可換代数の E 代数化。BM 命題 4.1、BF §3.1、16〜40 時間。
  5. E2a-5：homotopy function complex と π₀ の Hom 比較。
     Hovey §5・Dwyer–Kan、既存 HomotopyFunctionComplex の具体的適用、12〜24 時間。
  6. E2b：CAlg_R := N^hc と U : CAlg_R → D(R)、離散対象と極限。
     HTT §1.1.5・§5.2.4、γ2・γ4 の適用、16〜40 時間。その後 G1′（界面の述べ直し）。
- **主要宣言**（名前のみ）：
  `SerrePositivity.EInfinity.projectiveModelCategory`、
  `SerrePositivity.EInfinity.Operad.freeAlgebraAdjunction`、
  `SerrePositivity.EInfinity.Operad.Hopf`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.hopf`、
  `SerrePositivity.EInfinity.Operad.Coalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraHom`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict`、
  `SerrePositivity.EInfinity.Operad.convolutionAlgebra`、
  `SerrePositivity.EInfinity.Operad.convolutionFunctor`、
  `SerrePositivity.EInfinity.Operad.convolutionPreNat`、
  `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat`、
  `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso`、
  `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono`、
  `SerrePositivity.EInfinity.homPrecompose_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com、
  E の Hopf 構造、余代数区間の界面、全代数の good path object と J-cell acyclicity。
  Alg_E のモデル構造・右 Quillen U・CAlg は未提供。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：対象ビルド成功（2778 jobs）、公理監査成功（5600 宣言、標準 3 公理のみ）。
  新規 sorry・追加公理・名前衝突はなく、572 モジュールの import 閉包に他レーンの未コミット依存はない。
  今回の宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：工程 (2) の一般の極限余極限と自由像の小対象性を構成する。
  極限は `Algebra.ofJointlyMonicActions` と底の極限錐を使い、忘却が極限を作ることを示す。
  余極限は自由・忘却随伴の代数的表示、filtered 余極限とテンソル冪・coinvariant の保存を使う。
  自由像の I・J の小対象性を得て、`Transfer.Right.rightTransfer` へ
  `freeGeneratingTrivialCofibrations_cell_acyclicity` を渡す。TR・具体区間には未着手。

作成日：2026-10-18。状態：計画。ε の経路として E2（モデル圏）を採用（2026-10-18 決定）。
全体の正本は [infinity-categories.md](infinity-categories.md) §0・§5。

## 0. 位置づけ

G1 の界面（perfectoid 化とその性質の束）を述べる場である CAlg_R を、
Ch(R) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏で実現する。
三段で進める。

| 段 | 内容 | 使い先 |
| --- | --- | --- |
| E2a（モデル圏まで） | オペラッド・Barratt–Eccles・E∞-dg 代数・転送モデル構造・右 Quillen な忘却関手・homotopy function complex | 界面の欄を「Alg_E の homotopy 引き戻し」「homotopy 写像空間」で述べる。γ を待たずに G1 の CAlg 版へ昇格できる |
| E2b（∞ 圏化、γ） | Alg_E の cofibrant 対象の単体的豊穣化と coherent nerve、homotopy 極限 = ∞ 極限、Quillen 随伴 = ∞ 随伴 | 界面を Lurie の言葉（quasicategory の引き戻し）で述べる。K 理論の Sp と共有 |
| E2c（BS の続き用） | 余単体的 E∞-dg 代数の Tot と余単体的可換環への E∞ 作用（Berger–Fresse）、単体的可換環のモデル圏と多項式解像度 | BS §4・§7・§8 の構成 |

E1（∞ オペラッド）は採らない。後で HA の定理を文字どおり引用したくなった場合に、
E2b ≃ E1 の比較（HA 4.5.4.7 型の rectification）を任意項目として検討する。

## 1. 既存資産

- `HomotopicalAlgebra/`：Mathlib `ModelCategory` 上の Quillen 随伴（H1）、Under（H2）、
  転送（`Transfer/Recognition.lean`：生成類から Mathlib の `ModelCategory` を構成、acyclicity は明示仮定；
  `Transfer/Right.lean`：右随伴が fibration と弱同値を作る転送）、Smith の定理、
  Bousfield 局所化、Reedy、`HomotopyFunctionComplex/`（frame による導来写像空間）、
  `Monoidal/`（モノイダルモデル圏、monoid axiom）。
- `Spectra/SymmetricSequence/`：対称列と Day 畳み込み（オペラッドの合成積の素材）。
- `DifferentialGraded/Complexes/Cells.lean`：`complexSphere`・`complexDisk`（射影モデル構造の生成 cofibration）。
- `InfinityCategories/Derived/`：semifree の閉性（cone・fiber・直和・テンソル・底変更）。
- Mathlib：`SmallObject`、`CategoryWithCofibrations/Fibrations/WeakEquivalences`、`ModelCategory`。
- 未整備：Ch(A) の非有界射影モデル構造（Mathlib は `CochainComplex.Plus` の injective のみ）、
  オペラッド、対称群作用つき複体。

## 2. E2a の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| E2a-0 | Ch(A) の非有界射影モデル構造：弱同値 = 擬同型、fibration = 各次数全射、生成 cofibration `complexSphere (n+1) → complexDisk n`、生成 trivial cofibration `0 → complexDisk n`。`Transfer/Recognition.lean` で構成 | Hovey, Model Categories 2.3.11 |
| E2a-1 | Ch(A) 上の対称オペラッド：各 arity n の複体 P(n) と Σ_n 右作用、合成、単位。代数、代数の射、自由代数 Sym_P（⊕ (P(n) ⊗ A^{⊗n})_{Σ_n}）、自由 ⊣ 忘却 | Loday–Vallette、Berger–Moerdijk 2003 §1 |
| E2a-2 | Barratt–Eccles オペラッド E：EΣ_n（Σ_n の translation 亜群の nerve）の正規化鎖。各 arity が可縮、Σ-cofibrant（各 E(n) が Σ_n 上自由な次数ごとの基底を持つ）、E → Com | Barratt–Eccles 1974、Berger–Fresse 2004 §1 |
| E2a-3 | Alg_E の完全な転送モデル構造：弱同値・fibration は忘却で作る。AW 対角による E の Hopf 構造と E-coalgebra 区間の抽象界面から全代数の functorial path object を構成し、fibrations.llp ⊆ 弱同値、J-cell acyclicity、`Transfer.Right.rightTransfer` の適用を先に証明。TR : E → χ と区間切断作用で N_*(Δ¹) を界面に代入する。始域の cofibrancy は追加しない | Berger–Moerdijk 2003 命題 4.1・§4.6.3、Berger–Fresse 2004 §3.1（TR は §1.3）。Hinich 4.1.1 は使用しない（正標数で E は Σ-split でない） |
| E2a-4 | U : Alg_E → Ch(A) は右 Quillen、全対象 fibrant、homotopy 引き戻し・homotopy 極限は底で計算。E 代数の H⁰ が可換環であること、離散可換代数は E 代数（E → Com 経由） | 同上 |
| E2a-5 | homotopy function complex Map^h(A, B)（`HomotopyFunctionComplex/` の frame を Alg_E に適用）、π₀ Map^h = Ho(Alg_E) の Hom | Hovey §5、Dwyer–Kan |

## 3. E2b（γ）の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| γ1 | 局所 Kan な単体的圏の coherent nerve は quasicategory（Mathlib `SimplicialNerve` に対して） | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| γ2 | Alg_E の cofibrant 対象の単体的豊穣化（Hopf オペラッド E による B ⊗ N^*(Δ^•) 型、または Dwyer–Kan 単体的局所化）と CAlg_R := N^hc | Berger–Moerdijk 2006、Hinich、Dwyer–Kan |
| γ3 | homotopy 極限 = ∞ 極限、右 Quillen ⇒ ∞ 極限保存、Quillen 随伴 ⇒ ∞ 随伴 | HTT 4.2.4.1、5.2.4.6 |

γ2 の単体的豊穣化が E2b の最大のリスクである。E2a の完了時点で方式を決める。

## 4. 受入基準と記録

dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。
配置は `SerrePositivity/EInfinity/`（E2a）、namespace `SerrePositivity.EInfinity`。
集約ファイルをルートに 1 行で追加する。既存の `HomotopicalAlgebra/`・`Spectra/` は編集せず、
必要な一般補題は新規ファイルに置く。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/e-infinity-algebras-log.md](archive/e-infinity-algebras-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
