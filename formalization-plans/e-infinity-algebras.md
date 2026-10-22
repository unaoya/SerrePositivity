# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**F2N-4 冪等完備化へ移行（10-22 10:10 ユーザー承認、F1b から移管）。**
  **N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  任意 coherent 空間値図式の余極限は `F2.hasColimit_coherentSpaceDiagram`・`F2.coherentDiagramTotalCocone_isColimit` を読み取り専用で使用。N の部分余極限経路は打ち切り。
  **N-2（γ4）完了。** 固定 SM7・豊穣随伴の元の Hom 同型と合成互換を明示した simplicial Quillen 随伴について証明。
  元の cf 対応圏の coherent nerve、Δ¹ 上の両側 fibration、左右の元の導来関手・標準単位余単位・両三角恒等式、通常の cf 置換との比較を構成。
  `quillenCfDerivedAdjunctionWithComparisons_exists` は同じ単位の ∞ 随伴・両側 fibration・両通常置換との比較・任意 coherent 図式の指定極限保存を集約。添字の quasicategory 性は不要。
  **N-3 の指定された Tot・hG・fiber への適用は Sp の既存定理で達成。** 元の BF 対象・指定辺を保持して読み取り専用で照合。Sp の一般 coherent 極限・全有限極限・安定性の完成とは扱わない。
  **N-4 は休止。残る e・f・g は第 II 段。** 局所同値の強飽和性・任意 coherent 極限での局所対象の閉性、各対象の局所置換が与えられた場合の反射を証明済み。presentable 性からの局所置換の存在は未証明。
  P_Σ の全部分 quasicategory・元の Yoneda の充満忠実な因子化・sifted 余極限閉性を完了。
  **有限余積保存の途中の区切り：P_Σ の元の全区間 Hom の評価自然性まで保存済み（b0ccafbc8）。** 元の Tw の恒等点輸送、同じ選択済み前合成を対角辺とする全三角形族、元の共同評価の四辺を保持した正方形輸送を使用。`sigmaYonedaFiberEvaluation_naturalityIso` は元の Yoneda 辺への前合成後の全評価と、元の標的前層の同じ反変辺の標準輸送を比較。有限余積保存そのもの・sifted 生成・普遍性は未完了。
  **F2N-4(a) 完了。** `IdemShape` は二元の一対象圏の nerve、`SplitShape` は二つの形式的像の圏の nerve。通常の Karoubi は添字模型だけに使用。
  `CoherentIdempotent` は元の全 Idem 上の写像。`StrongSplitting` は同じ包含への制限で元の全図式を厳密に回収する写像。元の自己射と同じ二頂点の retract を保持。
  `WeakShape` は Δ² の長辺を Δ⁰ へ潰す商。実際の分裂二単体との全単射、元の弱い retract から同じ二辺・分裂頂点を持つ図式を回収。
  元の商と分裂二単体の像を全次数の核の分類で同定。`weakComparison` はその元の標準比較。
  HTT 4.4.5.8：欠ける面の複体の inner anodyne 性を実際のホーン pushout の有限合成で証明。
  元の交互セルの全単体・奇数面の厳密な因子化・前段階の逆像境界・セルの核を分類し、隣接段階を実際の pushout として構成。
  退化も含む全被覆性と元の段階包含の余極限から、`weakComparison_innerAnodyne` を可算合成で証明。
  HTT 4.4.5.6：指定した弱い全 retract 図式の厳密な強い分裂への延長と、その延長空間の可縮 Kan 性を証明。
  HTT 4.4.5.9〜11：元の全 Idem 図式の錐・余錐を構成。元の包含の左右 cofinal・anodyne 性を実 comma の射影と Quillen A で証明。
  `StrongSplitting.cone_isLimit`・`.cocone_isColimit` は同じ元の全図式の指定錐・余錐そのものの普遍性。任意の後合成でも保存。
  HTT 4.4.5.14〜15：全 Idem と元の source 全部分複体を包含を保つ厳密な同型で照合し、元の包含の inner fibration・充満忠実性を証明。
  指定した全 Idem 図式の余極限から元の全局所余極限を構成し、F1B の厳密左 Kan 延長で同じ全図式の強い分裂を回収。
  元の反対圏同型は包含と厳密に可換。極限からも同じ元の全図式の強い分裂を回収し、分裂・余極限・極限の存在の同値を完成。
  **HTT 4.4.5.16：全分裂空間の可縮性を完了。** 元の任意の SplitShape 図式の全標準左 Kan 余錐の余極限性を証明。
  元の前合成 `strongSplittingRestriction` は inner fibration かつ充満忠実。元の全 Idem 図式上の fiber の零単体は厳密な強い分裂と全単射。
  正次は同じ全図式を固定した全境界を充填し、分裂があれば `strongSplittingSpace_isContractibleKan`。余極限・極限がある場合も同じ fiber の可縮性。
  有効な元の全図式の全部分 quasicategory `effectiveIdempotents` を構成。元の制限を因子化した `effectiveSplittingRestriction` 自身が自明 Kan fibration。
  全部分圏の包含後に元の前合成そのものを厳密に回収。弱い図式の延長空間やホモトピー圏の一意性だけで代用しない。
  **F2N-4(b) 完了、(c) は存在定理まで。** 元の前層圏内の Yoneda 像の retract 閉包 `Idem C` は全部分 quasicategory。元の包含・Yoneda 因子化は充満忠実で、包含後に元の全 Yoneda を厳密に回収。
  元の二元モノイドの全乗法を保つ宇宙変更から、持ち上げた元の全 Idem と大きい宇宙の同じ Idem の厳密な同型を構成。
  F1 の小さい前層余極限を元の全図式へ戻し、`presheafInfinity_isIdempotentComplete` を証明。元の強い分裂は同じ全図式を厳密に回収。
  `StrongSplitting.liftFullSubcomplex` は retract に閉じた全部分圏への分裂の反映。包含後に元の周囲の全分裂を厳密に回収し、一般の retract 閉包の冪等完備性を結論。
  `idem_isIdempotentComplete`、元の Idem(C) 内部での Yoneda 像への retract、`idemYoneda_isIdempotentCompletion` を証明。HTT 5.1.4.1〜2 の定義による存在を完了。関手 ∞ 圏の普遍性・一意性は未証明。
  **HTT 5.1.4.3 完了。** 左右 fibration の標的が冪等完備なら全体も冪等完備。元の Idem 包含の左右 anodyne 性で、同じ底の強い分裂全体を厳密に持ち上げる。
  任意の元の図式上の slice・coslice の冪等完備性を証明。添字の quasicategory 性は不要。
  **F2N-4(c)：slice・cofinal 性・制限の充満忠実性まで完了。** 元の弱い retract の分裂点の包含は right anodyne。指定した底の全弱図式と分裂点を厳密に保持する右 fibration への持ち上げを構成。
  元の分裂点を全体の同じ点に保ち、相手の像が元の指定点と厳密に一致する retract を回収。元の pullback で、充満忠実な inner fibration の冪等完備化を右 fibration に沿って底変換。
  HTT 5.1.4.4：全部分圏の元の包含を任意の slice 上へ引き戻しても冪等完備化。5.1.4.5 の双対：終対象から像への retract と元の全終対象収縮を関手空間で合成し、充満忠実性で全ホモトピーを元の底へ戻して弱可縮性を証明。
  元の各 slice と恒等錐の終対象性から Quillen A を適用し、極限側の cofinal 性を証明。coherent 完備性・指定二頂点の retract 条件を反転し、元の包含の余極限側の cofinal 性も証明。
  HTT 5.1.4.7：全部分圏の包含に沿う任意の関手の元の全標準左 Kan 余錐は余極限。元の全 slice の同じ標準余錐への制限と全写像で照合。
  元の包含への制限は全関手の全写像空間で充満忠実。さらに元の頂点像への因子化で、単射性・inner 性を仮定しない任意の冪等完備化への同じ制限にも拡張。
  `idemYoneda_pre_isFullyFaithful` は元の全 Yoneda 因子化自身への制限。標的の冪等完備性は不要。延長の存在・全関手圏の同値は未証明。
  **F2N-4(c)：本質像の retract 閉性と全前層図式の回収まで完了。** 元の任意の全 Idem 図式を使い、ULift と ∞ 圏同値による coherent 冪等完備性の保存・反映を証明。
  指定された元の retract の全弱図式を延長し、同じ元の全 Idem 図式を冪等完備な全部分圏内で強く分裂。元の全余錐の一意性で、元の retract 対象が部分圏の対象と実際に同型になることを証明。
  冪等完備な圏の充満忠実な像の retract 閉性を結論。元の Yoneda 像の retract は表現可能前層と同型、`IsRetractPresheaf` は本質的表現可能性と同値。
  元の圏が冪等完備なら、元の `idemYoneda` 自身が同値。元の一般の充満忠実な関手を全本質像への同値へ因子化し、全頂点が本質像内にある元の全図式を全自然同型まで回収。
  `exists_diagram_of_retract_presheaves` は全値が元の Yoneda retract 閉包にある全前層図式から、元の冪等完備な標的の全図式を元の宇宙で回収。前層値の左 Kan 延長の存在そのものはまだ未証明。
- **残り**（依存順、粗い見積もり）：
  1. F2N-4(c)：冪等完備な標的への延長、元の因子化による全関手 ∞ 圏の普遍性・一意性。HTT 5.1.4.8〜9、15〜45時間。
  2. F2N-4(d)：安定 ∞ 圏の冪等完備化の安定性。元の零対象・有限極限余極限の閉性を証明。HA 1.1.3.7、15〜40時間。
  3. F2N-4(e)：`Ind(C)^ω ≃ Idem(C)`。F1b の F2N-2・F2N-3 の実際の Ind・compact 界面の後。HTT 5.3.4.17・5.3.5、15〜40時間。
  N-4 の局所化・P_Σ の残り e・f・g、E2b の DK/∞ 局所化の普遍性への γ4 の接続、Sp の残る安定性との整合は第 II 段。
- **主要宣言**（namespace `SerrePositivity.InfinityCategories.F2.Idempotent`）：
  `isIdempotentComplete_iff_ulift`、`isIdempotentComplete_iff_of_equivalence`、`retract_iso_in_complete_fullSubcomplex`、
  `IsIdempotentComplete.retract_iso_in_image`、`isRetractPresheaf_iff_representable_of_complete`、`idemYonedaEquivalenceOfComplete`、
  `essentialImageEquivalence`、`exists_diagram_in_fullyFaithful_source`、`exists_diagram_of_retract_presheaves`、
  `weakDiagram_lift_exists`、`rightFibration_retract_lift`、`IsIdempotentCompletion.pullback_rightFibration`、`IsIdempotentCompletion.sliceOver`、
  `IsIdempotentComplete.op`、`IsIdempotentCompletion.op`、`IsIdempotentCompletion.isLeftCofinal`、`IsIdempotentCompletion.isRightCofinal`、
  `IsIdempotentCompletion.canonicalCocones_isColimit`、`IsIdempotentCompletion.pre_isFullyFaithful_general`、`idemYoneda_pre_isFullyFaithful`、
  `idemShapeUniverseIso`、`presheafInfinity_isIdempotentComplete`、`StrongSplitting.liftFullSubcomplex_inclusion`、
  `fullSubcomplex_isIdempotentComplete`、`retractClosure_isIdempotentComplete`、`idem_isIdempotentComplete`、
  `IsIdempotentCompletion`、`idemVertex_retract_idemYoneda`、`idemYoneda_isIdempotentCompletion`、
  `isIdempotentComplete_of_rightFibration`、`isIdempotentComplete_of_leftFibration`、`sliceOver_isIdempotentComplete`、`sliceUnder_isIdempotentComplete`、
  `strongSplittingRestriction_isFullyFaithful`、`strongSplittingSpaceVertexEquiv`、`strongSplittingSpace_isContractibleKan`、
  `effectiveIdempotents`、`effectiveSplittingRestriction_inclusion`、`effectiveSplittingRestriction_trivialKanFibration`、
  `WalkingIdem`、`WalkingSplit`、`IdemShape`、`SplitShape`、`idemInclusion`、`CoherentIdempotent`、`StrongSplitting`、`IsIdempotentComplete`、
  `WeakShape`、`WeakRetractionDiagram`、`weakDiagramEquiv`、`weakComparison`、`RetractionTriangle`、`VertexRetraction.triangle_exists`、`RetractionTriangle.weakDiagram`、
  `idemOppositeIso_inclusion`、`OppositeStrongSplitting.toStrong`、`strongSplitting_exists_of_hasLimit`、`nonemptyStrongSplitting_iff_hasLimit`、`isIdempotentComplete_iff_hasLimits`、
  `idemSourceIso_inclusion`、`idemInclusion_innerFibration`、`idemInclusion_isFullyFaithful`、`strongSplitting_exists_of_hasColimit`、`nonemptyStrongSplitting_iff_hasColimit`、`isIdempotentComplete_iff_hasColimits`、
  `idemInclusion_isLeftCofinal`、`idemInclusion_leftAnodyne`、`idemConeRestriction_trivialKanFibration`、`idemCone_isLimit_iff_restrict`、`StrongSplitting.cone_isLimit`、`StrongSplitting.hasLimit`、`StrongSplitting.postcomposeCone_isLimit`、`IsIdempotentComplete.hasLimit`、
  `StrongSplitting.cocone_isColimit`、`StrongSplitting.hasColimit`、`StrongSplitting.postcomposeCocone_isColimit`、`IsIdempotentComplete.hasColimit`、
  `walkingImageCommaIso`、`walkingSourceComma_isInitial`、`walkingComma_isWeaklyContractible`、`walkingCommaCosliceIso_projection`、`idemInclusion_isRightCofinal`、`idemInclusion_rightAnodyne`、`idemCoconeRestriction_trivialKanFibration`、`idemCocone_isColimit_iff_restrict`、
  `StrongSplitting.cone`、`StrongSplitting.cocone`、`StrongSplitting.cone_vertex`、`StrongSplitting.cocone_vertex`、`idemConeRetraction`、`idemConeRetraction_inl`、`idemShapeContraction`、`idemShape_isWeaklyContractible`、
  `walkingSplit_object_cases`、`walkingHom_cases`、`absorbingChainFace_eq`、`identityCollapse_chain_eq`、`retractionStage_contains_simplex`、`retractionStage_iSup_succ`、
  `retractionStageCocone_isColimit`、`weakComparison_innerAnodyne`、`weakComparisonRestriction_trivialKanFibration`、`weakDiagram_extension_exists`、`weakDiagram_strongSplitting_exists`、`weakDiagramExtensionSpace_isContractibleKan`、
  `alternatingCell_kernel`、`retractionStage_isPullback_app`、`retractionStage_isPushout_app`、`retractionStage_isPushout`、`retractionStageMap_innerAnodyne`、
  `chainScalar`、`alternatingCell_equal_indices`、`alternatingCell_odd_injection_exists`、`alternatingCell_odd_rank_le`、`alternatingCell_stage_preimage`、
  `oddFaceCollapse`、`oddFaceChain`、`alternatingCell_oddFace`、`alternatingCellBoundary_le_preimage`、`alternatingCellBoundaryLift`、`alternatingCellBoundaryLift_square`、
  `alternatingCell`、`alternatingCell_prefix`、`alternatingCell_one`、`retractionStage`、`retractionStage_mono`、`retractionStage_one`、`weakShapeStageOneIso_ι`、`retractionStageCell_prefix`、
  `missingFaceStage_inf_face`、`puncturedFace_coordinate_preimage`、`puncturedFace_innerAnodyne`、`missingFaceStage_innerAnodyne`、`missingFaceComplex_innerAnodyne`、`alternatingCellBoundary_innerAnodyne`、
  `walkingRetractionTriangle_kernel`、`weakComparison_mono`、`weakComparison_range`、`weakShapeImageIso`、`weakShapeImageIso_ι`、
  `isVertexRetractOf_iff_retractionTriangle`、`CoherentIdempotent.endomorphism_idem`、`StrongSplitting.vertexRetraction`、`VertexRetraction.isoOfSameIdempotent`、`VertexRetraction.hom_unique`、
  `IsVertexRetractOf`、`retractClosure`、`retractClosure_idempotent`、`IsRetractPresheaf`、`Idem`、`idemInclusionPresheaf`、`idemYoneda`、`idemYoneda_inclusion`、`idemYoneda_isFullyFaithful`、`idemVertex_retract_yoneda`。
  N-1〜4 の保存済み公開名・型は `HomotopyLimits.lean` と `scripts/audit_homotopy_limits.lean` を参照。
- **依存と提供**：F2・F1B・F1 は読み取り専用。新規所有範囲は `InfinityCategories/F2/Idempotent/`・独立集約 `F2/Idempotent.lean`・独立監査 `scripts/audit_f2_idempotent.lean`。
  F1b の F2 集約を変更しない。`infinity-core-F2.md` の表は旧担当表記のまま読み取り専用。移管の正本は上記ユーザー承認。規約は `foundations.md` §8。
- **未コミット**：なし（今回の9モジュール23宣言・独立集約・全監査、本 N 節を保存。前回保存待ちだった N 節も含む。他レーンの差分は対象外）。
- **既知の問題**：F2N-4 の集約ビルド6583 jobs・全498宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理なし。N-4 の既存保存は7604 jobs・全5288宣言監査が終了コード0、標準三公理のみ。
  `Inputs/Homotopy/KanQuillen.lean` は import せず、主経路に `ModelCategory SSet` を仮定しない。固定 SM7・豊穣随伴の合成互換を、通常の Quillen 随伴だけから得たとは扱わない。
  同じ射の類の冪等性だけを coherent 冪等図式と扱わず、ホモトピー圏の分裂の一意性だけを全分裂空間の可縮性と扱わない。存在・普遍性を未証明の入力フィールドに置いて完成とは扱わない。
- **次の一手**：F2N-4(c)：HTT 5.1.4.8 の前層値の左 Kan 延長を実際に構成する。F1 の `presheafInfinity_hasColimit` は小さい底の ULift 上の図式を受け取る。まず元の `leftKanShape δ c` の ULift と、持ち上げた包含の同じ点での左 Kan 添字を同型で照合する。`uliftSliceOverIso`・`uliftStdSimplexIso 0`・`HomotopyLimits.uliftPullbackIso` と元の射影の可換性を使う。元の各局所余極限を構成し、F1B の `exists_kanLeftCanonical_strict_extension_of_local_colimits` で元の Yoneda 後合成を延長。各値が元の像の retract であることは元の completion の retract と関手による保存から示し、今回の `exists_diagram_of_retract_presheaves` に渡す。その後元の制限の本質的全射性と全関手 ∞ 圏の同値を結論。一般の元の包含への移送では頂点像への因子化を使用。
  **N-4 の再開点（第 II 段）**：元の有限離散余極限余錐を反対圏の有限積錐へ移し、`sigmaPresheafVertexFunctor_preservesFiniteProducts` を適用。各脚の Hom 前合成を `sigmaYonedaFiberEvaluation_naturalityIso` で同じ値図式の輸送へ照合し、元の全余錐像の余極限性を写像空間で判定。空添字も含む。その後 sifted 生成・普遍性。HTT 5.5.8.10・11・14・15。
  原典：[HTT §4.4.5・§5.1.4](https://www.math.ias.edu/~lurie/papers/HTT.pdf)（本文照合済み）、HA 1.1.3.7 は安定性着手時に本文照合する。

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
