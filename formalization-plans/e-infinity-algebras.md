# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  任意の小さい底上の coherent 空間値図式の余極限は `F2.hasColimit_coherentSpaceDiagram` を使用。
  `F2.coherentDiagramTotalCocone_isColimit` は元の全空間余錐の native 余極限性。F2 集約・`infinity-core-F2.md` は読み取り専用。
  **N の部分余極限経路は打ち切り。** 指定余錐の未証明の余極限性や無限骨格の接続を再開しない。
  **N-2（γ4）完了。** 固定 SM7・豊穣随伴の Hom 同型と合成互換を明示した simplicial Quillen 随伴について証明。
  元の cf 対応圏の coherent nerve は quasicategory、Δ¹ 上の元の射影は CartesianFibration かつ CocartesianFibration。
  元の右 Q(RY)→RY と左 LX→R_D(LX) の随伴像の外側ホーン充填は全次数で完了。二つの未知 Hom・全境界可換性を再実装しない。
  元の cf nerve 間の左右導来関手、標準単位・余単位・h Fun 内の両三角恒等式を持つ `QCatAdjunction` を構成。
  単位は同じ標準輸送比較のホモトピー。元の両包含・端点 fiber 同型・左右の全候補辺を保持する。
  元の通常の左右 cf 置換関手と比較自然変換を構成し、通常の nerve 全体を元の導来関手と `FunctorIso` で照合。
  左の比較は元の coCartesian prism の終点を持ち上げ空間の可縮 Kan 性で比較し、全忠実な指定 fiber へ反映する。
  `quillenCfDerivedAdjunctionWithComparisons_exists` は同じ単位の ∞ 随伴・両側 fibration・両通常置換との比較・任意 coherent 図式の指定極限保存を集約。
  右随伴の後合成の任意単体集合パラメータの Hom 同型・RightKanHom 普遍性から、元の指定極限錐の保存を証明。添字に quasicategory 性を仮定しない。
  **N-3 の指定された Tot・hG・fiber への適用は Sp の既存定理で達成。** 元の BF 対象・指定辺を保持する公開界面を読み取り専用で照合・検証。
  `homotopyFixedPointsInfinityCone_isLimit`・`homotopyTotalizationInfinityCone_isLimit` は元の作用図式・余単体図式の実 ∞ 極限錐。
  任意 coherent cospan の極限・任意辺の fiber も提供済み。Sp の任意 coherent 図式の極限・全有限極限・安定性まで完成とは扱わない。
  **N-4 着手。** `IsLocalObject W` を元の指定辺の写像空間の前合成同値で定義し、局所対象の全部分 quasicategory を構成。
  pinched・区間模型の局所性を照合。局所性の合成・二つから三つ目・対象同型不変性、任意単体集合パラメータの定値 Hom の全単射を証明。
  `reflective_isLocal_iff_unit_local` は既存反射の局所対象を全単位成分への局所性で特徴づける。逆向きは元の単位の両逆を回収。
  既存反射について、局所対象と元の反転辺集合の局所対象の一致、および S-equivalence と元の反転辺集合の一致を証明（HTT 5.5.4.2(1)・(2)）。
  `LocalEquivalenceHom`・`localEquivalences` を元の射・一次単体で定義。元の辺集合の包含、単調性・冪等性、局所対象の不変性を証明。
  元の二単体の三辺について二つから三つ目の性質を証明し、全可逆辺を含むことも回収。任意小余極限条件も下記の元の矢印圏の余錐で証明。
  全単体集合パラメータの定値 Hom の全単射と局所性の同値を公開。元の辺への局所性を終点固定 coslice の始点制限の trivial Kan 性と照合。
  元の span の左枝が指定辺集合に属するとき、局所対象への余錐の右枝・右枝終点への制限の trivial Kan 性を証明。余錐空間の厳密な引き戻しを使用。
  **元の任意の coherent な pushout での S-equivalence の保存を完了。** 下辺→上辺と左辺→右辺の両向きを公開。安定性は不要。
  反復 coslice の厳密な同型と元の左因子への制限の一致を構成し、余極限余錐全体から底図式への coslice 制限の trivial Kan 性を導出。
  **局所同値の強飽和性（HTT 5.5.4.5・5.5.4.11）を完了。** pushout・矢印圏内の任意小余極限・元の二単体の二つから三つ目と全可逆辺を保持。
  **両端が余極限余錐の元の coherent な prism について、底の全垂直辺が S-equivalence なら元の頂点辺も S-equivalence と証明。**
  終点面から全図式の余極限性を回収し、指定比較辺の底の像を元の頂点辺と厳密に同定。K の nerve・quasicategory 性は仮定しない。
  元の任意の矢印圏の余極限余錐の両端評価を、F2 の点ごとの余極限の存在と余錐全体の同型から回収。元の頂点辺の所属を証明。
  小添字 u と対象圏の宇宙 max(u,v) を分離し、ulift した全小形状の余極限の存在から強飽和性を集約。大きい宇宙の全余極限は要求しない。
  **局所対象の任意 coherent 極限での閉性を完了。** `isLocalObject_limitCone` は元の指定極限錐の頂点を保存し、添字 K の quasicategory 性・反射の存在を要求しない。
  小添字を指定した `stronglySaturatedClosure` の最小性・強飽和性・冪等性と、小生成の定義を構成。生成閉包は元の局所対象・局所同値・局所全部分圏を保持。
  **生成閉包内の局所置換の存在から、生成閉包＝局所同値と小生成性を導出。** 元の hX の Hom の持ち上げ・置換間の可逆辺・元の二単体を使用。局所置換の存在、無条件の反射の存在、P_Σ は未完了。
  局所終点を持つ元の余錐圏を引き戻しで構成し、局所同値の始点・終点への余錐制限が圏同値であることを証明。
  **局所対象へ向かう元の局所同値自身が、局所余錐圏の始対象。** 終点を重ねる元の退化三角形を使用し、一点余錐の脚が元の辺であることまで厳密に照合。
  **join 型 coslice の底変換から `unitCommaFiber` への標準比較の同値性を完了。** 任意 G:Y→X に対し標的図式を保持し、全パラメータで fiber 比較を既存の区間比較と厳密に同定。
  元の局所置換を指定 comma 始対象へ移し、その矢印の族が元の辺であることを厳密に回収。各対象の局所置換の存在から、各 comma の始対象の存在を導出。
  各 comma の始対象から相対始対象射影の自明 Kan 性を回収し、普遍矢印の coherent な切断を構成。同じ円柱から標的関手と単位を取り、各成分の元の頂点辺の類との一致を証明。
  標的固定の二重 fiber 内の同じ Hom 類の二辺を頂点同型で比較し、代表不変性と `UnitCommaInitialCondition` を持つ coherent な関手・単位を回収。
  **comma 始対象条件から、元の指定単位の標準写像空間比較の同値性と ∞ 随伴を構成。** 同じ合成三角形の円柱を、同じ comma 頂点で評価した left fibration の普遍輸送と照合。
  **各対象の局所置換が与えられれば、局所全部分圏の反射を構成。** presentable 性からの局所置換の存在は未証明。
  **P_Σ 入口：sifted 性・filtered からの入口・弱可縮性を証明。** 元の F2 の二項積の全空間 Kan 比較を sifted な底へ一般化し、空積の比較も証明。底の quasicategory 性は不要。
  **元の全空間 Kan 模型を頂点とする native 空積・二項積を構成。** 同じ比較辺の全錐円柱は底図式を固定し、読み戻した両脚は元の全空間射影の Kan 置換にホモトピック。
  **点ごとの coherent 積の元の小さい全空間→pullback の前合成同値を完了。** 両射影の fiber 作用を元の辺の輸送と照合。sifted な底で元の余極限 Kan 比較のホモトピー同値・両脚・単位式まで完了。底の quasicategory 性は不要。
  **積図式の元の余極限頂点を持つ native 二項積錐を構成。** 同じ比較辺の全錐円柱・両 Kan 脚を保持。**実際の両脚の coherent 辺が元の `coconePointHomFamily` に作用する全余錐を、元の射影変換と指定単位の合成余錐へ同定。** 元の fiber 値比較と右 Hom 比較の両逆・輸送自然性を証明し、単位表現との間の比較を完了。定値終対象 coherent 図式の元の小さい全空間射影の前合成同値性、および sifted な底上の元の余極限頂点の終対象性・native 空積錐の極限性も完了。**P_Σ を元の P(C) の全部分 quasicategory として定義。** Cᵒᵖ の元の有限離散極限錐を全錐ごと保存する条件、対象同型不変性、充満忠実な包含と族の制限を構成。空間の終対象性と元の Kan 値の可縮性を同値と照合し、元の Yoneda 前層が始対象を終対象へ送ることを証明。**任意の元の極限錐を Yoneda 前層で写した実際の native 全錐について、一点からの切断制限の同値性まで完了。** 元の反転 coslice から小さい unstraightening への底上の比較、宇宙持ち上げ・縮小・pointed pullback・join 形状同型を保持。**元の空間値錐の一点切断による極限検出と、任意小さい離散 coherent 図式の元の Kan 積からの極限存在を完了。元の表現可能前層の有限積保存を導き、元の Yoneda ∞ 関手を P_Σ へ因子化し充満忠実性を証明。** 包含後は元の全 Yoneda 写像を厳密に回収。**sifted な底の全有限非空反復対角の cofinality と、元の有限共通 fiber 積の全空間 Kan 比較を完了。** 元の全射影・単位式、元の全空間を頂点とする native 有限積錐、同じ比較辺の底図式を固定する全錐円柱、全 native 脚と元の射影の Kan 像のホモトピーまで保持。**元の有限 coherent 積の小さい unstraightening から、元の有限共通 fiber 積への比較射を構成。** 元の全成分は反復二項射影の全空間作用そのもので、底射影も厳密に保持。比較射の同値性、P_Σ 内の Yoneda の有限余積保存、sifted 閉性・生成・普遍性は未完了。
- **残り**（依存順。時間は再開時の粗い見積もり）：
  1. E2b へ γ4 を提供し、元の DK 豊穣化・忘却関手と接続。E2 の高次 Hom 比較と ∞ 局所化の普遍性が先。HTT 1.1.5.10・5.2.4.6、16〜40時間。
  2. N-4（I-b）：Bousfield 局所化・P_Σ。presentable・随伴関手定理は F1b、N は局所対象・局所化と sifted 生成を分担。HTT 5.5.4・5.5.8、規模は入口調査後に再見積もり。
  3. Sp の残る一般 coherent 極限・安定性の供給は Sp レーンと整合させる。Sp の `IsStable` は I-b 末尾に延期済み。
  Ind・compact・冪等完備化・Ind の安定性は F1b の担当。`infinity-core-F2.md` §3 を読み取り専用で使う。
- **主要宣言**（名前のみ。断りなしは namespace `SerrePositivity.InfinityCategories.HomotopyLimits`）：
  `F2.coherentDiagramTotalCocone_isColimit`、`F2.hasColimit_coherentSpaceDiagram`、`FixedSimplicialPushoutProduct`、`EnrichedAdjunctionHomComposition`、
  `quillenCfCollageInfinity_quasicategory`、`quillenCfBottomFiberIso`、`quillenCfTopFiberIso`、
  `quillenCfRightLiftEdge_isCartesian`、`quillenCfLeftLiftEdge_isCocartesian`、
  `quillenCfCollageProjection_cartesianFibration`、`quillenCfCollageProjection_cocartesianFibration`、
  `quillenCfLeftDerived`、`quillenCfRightDerived`、`quillenCfDerivedUnitMappingSpaceCondition_exists`、`quillenCfDerivedAdjunction_exists`、
  `rightKanHomUniversal_postcomp_of_unitCondition`、`mapJoinCone_isLimit_of_adjunction`、
  `quillenCfRightDerived_mapJoinCone_isLimit`、`quillenCfRightDerived_hasLimit_postcomp`、
  `quillenCfRightReplacement_transport_exists`、`quillenCfLeftReplacement_transport_exists`、
  `quillenCfRightReplacementFunctor`、`quillenCfLeftReplacementFunctor`、`quillenCfRightReplacementComparison`、`quillenCfLeftReplacementComparison`、
  `quillenCfRightDerived_ordinaryComparison`、`quillenCfLeftDerived_ordinaryComparison`、`quillenCfDerivedAdjunctionWithComparisons_exists`、
  `IsLocalForHom`、`isLocalForHom_iff_interval`、`isLocalForHom_constantHom_bijective`、
  `IsLocalObject`、`localObjectsSubcomplex`、`isLocalObject_iff_of_vertexIso`、
  `isIso_of_isLocalForHom_source_target`、`reflectiveUnit_isLocalForHom`、`reflective_isLocal_iff_unit_local`、
  `LocalEquivalenceHom`、`localEquivalences`、`localEquivalences_idempotent`、
  `reflective_isLocal_iff_invertedEdges`、`reflective_localEquivalenceHom_iff`、`reflective_localEquivalences_eq`、
  `localEquivalenceHom_iff_edge_mem`、`localEquivalences_compStruct`、`localEquivalences_compStruct_cancel_left`、`localEquivalences_compStruct_cancel_right`、
  `iteratedSliceUnderIso`、`iteratedSliceUnderIso_restriction`、`sliceUnderRestrict_cocone_trivial`、
  `localEquivalences_pushout_bottom_top`、`localEquivalences_pushout_left_right`。
  `cosliceRestriction_homotopyEquivalence_iff_sections`、`isLocalForHom_edge_iff_sectionRestriction_trivial`、
  `isLocalForHom_initialRestriction_of_fiber_equivalence`、`localEquivalences_colimitRestriction_comparison`、`localEquivalences_colimitPrism_source_comparison`、
  `colimitPrismTotalCocone_isColimit`、`colimitPrismComparisonEdge_projection`、`localEquivalences_colimitPrism_apex`、
  `isColimitCone_functor_evaluation_of_pointwise_exists`、`localEquivalences_arrowColimit`、`IsStronglySaturatedEdgeSetOfShapes`、`localEquivalences_stronglySaturated`、
  `localDiagram_coslicePrecomposition_isQCatEquivalence`、`isLocalForHom_limitCone_of_sections`、`isLocalObject_limitCone`、
  `stronglySaturatedClosure`、`IsOfSmallStrongGeneration`、`isLocalObject_stronglySaturatedClosure_iff`、`stronglySaturatedClosure_eq_localEquivalences_of_localReplacements`、
  `localTargetCoconeSpace`、`localTargetCoconeRestriction_source_isQCatEquivalence`、`edgeSourcePointCocone_leg_edge`、`localReplacement_edgeSource_isInitial`、
  `cosliceCommaComparison_isQCatEquivalence`、`localReplacementCommaPoint_isInitial`、`localReplacementCommaPoint_uncurry`、`unitCommaFiber_initial_exists_of_localReplacements`、
  `commaRelativeInitialProjection_trivialKanFibration`、`exists_unitCommaSection_of_fiberInitial`、`commaSectionUnit`、`commaSectionUnit_component`、
  `unitCommaTargetFiber_isInitial_iff_of_homMk_eq`、`commaSectionUnit_initialCondition`、`exists_unit_initialCondition_of_fiberInitial`、
  `unitIntervalMap_commaTransportIso`、`qcat_exists_adjunction_unitHom_iff_commaInitial`、`exists_qcatAdjunction_of_commaFiberInitial`、`isReflectiveSubcategory_of_localReplacements`、
  `IsSiftedInfinity`、`isWeaklyContractible_of_sifted`、`totalKanProductComparison_homotopyEquivalence_of_sifted`、`continuousKanReplacement_isContractibleKan_of_sifted`、
  `siftedProductNativeCone_isLimit`、`siftedProductNativeKanLeg_left`、`siftedProductNativeKanLeg_right`、`siftedEmptyProductNativeCone_isLimit`、`spaceTensorProduct`、`coherentSpaceTensorProduct_vertex`、`spaceTensorProductFstHomotopy_component`、`spaceTensorProductSndHomotopy_component`、`coherentSpaceTensorProductTotalComparison`、`coherentSpaceTensorProductTotalComparison_isPrecompositionEquivalence`、`coherentSpaceTensorProductTotalComparison_fiber`、`coherentProductTotalKanComparison_homotopyEquivalence`、`siftedCoherentProductNativeCone_isLimit`、`siftedCoherentProductNativeKanLeg_left`、`siftedCoherentProductNativeKanLeg_right`、`siftedCoherentProductLeftLegCoconeIso`、`siftedCoherentProductRightLegCoconeIso`、`pointedValue_transportIso`、`totalKanNativeCoconeIso`、`siftedCoherentProductLeftNativeCoconeIso`、`siftedCoherentProductRightNativeCoconeIso`、`coherentPointTotalProjection_isPrecompositionEquivalence`、`siftedCoherentPointTotalVertex_isTerminal`、`siftedCoherentEmptyProductNativeCone_isLimit`、`PreservesFiniteProductsFromSmallSource`、`SigmaPresheafInfinity`、`isSigmaPresheaf_iff_of_vertexIso`、`sigmaPresheafInfinityLift_inclusion`、`spaceInfinity_isTerminal_iff_value_isContractibleKan`、`representablePresheafInfinity_initialValue_isTerminal`、`representableCosliceComparison_projection`、`representableConeSectionRestriction_isQCatEquivalence`、`coherentPointedRestriction_isQCatEquivalence`、`representableNativeConePointedRestriction_isQCatEquivalence`、`spaceCone_isLimit_of_pointRestriction_of_hasLimit`、`hasLimit_discreteCoherentSpaceDiagram`、`representablePresheafInfinity_preservesFiniteProducts`、`sigmaYonedaInfinityMap_inclusion`、`sigmaYonedaInfinityMap_isFullyFaithful`、`nonemptyFiniteDiagonal_isRightCofinal`、`finiteCommonFiberProductKanComparison_unit`、`finiteCommonFiberProductKanComparison_homotopyEquivalence`、`finiteSiftedProductNativeCone_isLimit`、`finiteSiftedProductNativeKanLeg_projection`、`finiteCommonFiberProductLift_projection`、`finiteCommonFiberProduct_hom_ext`、`finiteCoherentSpaceProductTotalComparison_projection`、`finiteCoherentSpaceProductTotalComparison_base`。 Sp の正本は `kst-lanes/L9-spectra.md` の値域界面表。N の残りの公開名・型は集約と全監査を参照。
- **依存と提供**：F1・F1b、F2 の coherent 余極限、HomotopyFunctionComplex、Coherent、Stable、KST/Spectra・LocalizingInvariants を読み取り専用で使用。
  集約 `InfinityCategories/HomotopyLimits.lean`・全監査 `scripts/audit_homotopy_limits.lean` を Sp・E2b に提供。規約は `foundations.md` §8、README は規約だけ。
- **未コミット**：なし（今回の保存単位：有限 coherent 積の元の小さい全空間比較と普遍射の2モジュール10宣言、集約・全監査、本 N 節）。他レーンの差分は対象外。
- **既知の問題**：N の対象ビルド7430 jobs・全4744宣言監査は終了コード0、標準三公理のみ。新規2モジュール10宣言に警告・sorry・追加公理なし。
  `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので import しない。主経路に `ModelCategory SSet` を仮定しない。
  固定 SM7 と豊穣随伴の合成互換は simplicial model/adjunction の明示入力。通常の Quillen 随伴だけから導いたとは扱わず、適用先では元のデータとの互換を証明する。
  E2b は DK 型なので、この入力を未証明のまま代入しない。`Localization.IsLocalization` の定義だけを任意 W の局所化の存在定理と扱わない。
  Sp の局所 Kan 性・Ω 条件・cofibrancy を保持。他レーンの import 閉包が壊れたら回避せず停止し、作業中変更を保存しない。
- **次の一手**：N-4：`finiteCoherentSpaceProductTotalComparison` の同値性。元の有限共通 fiber 積を最初の因子と tail の引き戻しへ同型で分解し、完成済みの二項全空間比較と tail 比較の底変換との合成に元の比較射自身を照合する。任意の底上で fiber ごとの同値性を帰納し、前合成同値を回収。元の全射影・fiber 作用を保持し、同じ Kan 比較辺で元の coherent 余極限頂点へ全有限積錐を輸送。その後 F2 の元の点ごとの前層余極限へ適用し P_Σ の sifted 閉性を証明。元の Yoneda の P_Σ 内の有限余積保存・sifted 生成・普遍性と局所置換の存在も残る（HTT 5.5.8.10・11・14・15）。
  comma の局所随伴判定・局所置換からの反射は完成。逆向きの比較 fiber のホモトピーを再実装せず、同じ単位比較と普遍輸送の照合を使用。
  生成閉包＝局所同値の定理と反射の定理の `hreplace` は未供給。presentable 圏の小さい辺族から局所置換を作る存在部分が残る。入力フィールドに仮定して完成とは扱わない。
  F1 の前層・Yoneda は正本・ソースで提供済みと確認。F2 の Ind・compact は進行中、presentable・随伴関手定理は後段。条件付き反射だけで局所化の存在の完成としない。F1・F2 は読み取り専用。
  E2b の `cAlgForgetLocalization` の終域は元の全複体の具体的局所化。D(R) との比較・高次 Hom 比較・∞ 局所化の普遍性は E2 側で未提供と再確認。γ4 の入力を先取りしない。
  原典は [HTT 5.2.4.6・Remark 5.2.4.7、5.5.4・5.5.8](https://www.math.ias.edu/~lurie/papers/HTT.pdf)（本文照合済み）。

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
