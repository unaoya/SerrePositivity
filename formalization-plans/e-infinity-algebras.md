# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**P-1 g の sifted 生成を完了。** 有限余積を持つ小さい C の各指定 P_Σ 頂点を、元の小さい sifted な元の圏上の同じ Yoneda 図式の余極限として厳密に表示。元の図式を固定した持ち上げ錐の極限性、反転全空間の有限積・元の圏の sifted 性と sifted 帰納法も証明。HTT 5.5.8.14 の simplicial Ind 表示と 5.5.8.15 の全普遍性は未完了。F2N-3 は a7 の実証拠差し替えだけ残す（提供後1コミット）。
  **F2N-4(a)〜(e) 完了。(e) は F1 の密度余錐と元の恒等点の実因子化を使用し、ℵ₀ の比較も構成。** 冪等完備化は 10-22 10:10 ユーザー承認で F1b から移管。
  **N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  任意 coherent 空間値図式の余極限は `F2.hasColimit_coherentSpaceDiagram`・`F2.coherentDiagramTotalCocone_isColimit` を読み取り専用で使用。N の部分余極限経路は打ち切り。
  **N-2（γ4）完了。** 固定 SM7・豊穣随伴の元の Hom 同型と合成互換を明示した simplicial Quillen 随伴について証明。
  元の cf 対応圏の coherent nerve、両側 fibration、左右の導来関手・標準単位余単位・両三角恒等式、通常の cf 置換との比較を構成。
  `quillenCfDerivedAdjunctionWithComparisons_exists` は同じ単位の ∞ 随伴・両側 fibration・両通常置換との比較・任意 coherent 図式の指定極限保存を集約。添字の quasicategory 性は不要。
  **N-3 の指定された Tot・hG・fiber への適用は Sp の既存定理で達成。** 元の BF 対象・指定辺を保持して照合。Sp の一般 coherent 極限・全有限極限・安定性の完成とは扱わない。
  **N-4 の局所化の存在は P へ移管。P_Σ の生成・普遍性は N の現工程。** 局所同値の強飽和性・任意 coherent 極限での局所対象の閉性、局所置換が与えられた場合の反射を証明済み。presentable 性からの局所置換の存在は未証明。
  P_Σ の全部分 quasicategory・元の Yoneda の充満忠実な因子化・sifted 余極限閉性を完了。
  **有限余積保存の区切り：P_Σ の元の全区間 Hom の評価自然性まで保存済み（b0ccafbc8）。** `sigmaYonedaFiberEvaluation_naturalityIso` は元の Yoneda 辺への前合成後の全評価と、元の標的前層の同じ反変辺の標準輸送を比較。有限余積保存そのものは未完了。sifted 生成は今回完了し、全普遍性・保存性判定を継続。
  **F2N-4(a)：coherent 分裂の存在・一意性を完了。** `IdemShape` は二元の一対象圏の nerve、`SplitShape` は二つの形式的像の圏の nerve。通常の Karoubi は添字模型だけに使用。
  `CoherentIdempotent` は元の全 Idem 上の写像。`StrongSplitting` は元の包含への制限で同じ全図式を厳密に回収。
  元の弱い retract の商・実際の分裂三角形・交互セルの核と pushout・全被覆性から `weakComparison_innerAnodyne` を証明。
  元の包含の左右 cofinal・anodyne 性と、元の強い分裂の指定錐・余錐の絶対普遍性を証明。同じ全 Idem 図式の分裂・余極限・極限の存在は同値。
  全分裂空間の零単体は元の厳密な強い分裂と全単射。正次の全境界も同じ全図式を固定して充填。元の fiber は分裂があれば可縮 Kan。
  元の前合成を有効な元の全図式の全部分圏へ因子化した制限そのものが自明 Kan fibration。弱い図式やホモトピー圏の一意性だけで代用しない。
  **F2N-4(b)：前層の retract 閉包と冪等完備性を完了。** 小さい前層余極限と元の全 Idem の宇宙同型で前層圏の coherent 冪等完備性を証明。
  元の全分裂を retract に閉じた全部分圏へ厳密に反映。元の Yoneda 像の retract 閉包 `Idem C` は冪等完備な全部分 quasicategory。
  元の包含・Yoneda 因子化は充満忠実。各対象は Idem(C) 自身の内部で元の Yoneda 像の retract。HTT 5.1.4.1〜2 の存在を完了。
  **F2N-4(c)：元の全関手 ∞ 圏の普遍性・一意性を完了。** 左右 fibration に沿う強い分裂の持ち上げと slice・coslice の冪等完備性を証明。
  元の弱い全 retract 図式を分裂点を固定して右 fibration に持ち上げ、slice 上でも冪等完備化を構成。元の全終対象収縮を関手空間で合成して底の弱可縮性を得て、Quillen A と反転で左右 cofinal 性を証明。
  全関手の元の全標準左 Kan 余錐を、元の全 slice の標準余錐への制限と照合。元の冪等完備化への制限は全写像空間で充満忠実。
  coherent 完備性の ULift・∞ 圏同値不変性、充満忠実な像の retract 閉性と Yoneda retract の表現可能性を証明。全本質像への因子化で、全前層図式を元の標的の全図式へ回収。
  元の左 Kan 添字の ULift と持ち上げた元の射・点の添字を、両射影を保つ厳密な同型で照合。元の小さい前層余極限から全局所余極限を実際に構成。
  厳密な左 Kan 存在で元の Yoneda 後合成を延長し、全値が元の Yoneda retract 閉包にあることを元の retract から証明。元の標的の図式へ回収し、元の制限の全自然同型も回収。
  頂点像への因子化で単射性・inner 性を仮定しない元の任意の冪等完備化への延長存在へ拡張。
  `IsIdempotentCompletion.pre_isQCatEquivalence`・`idemYonedaUniversalEquivalence` は元の制限そのものを順方向とする全関手 ∞ 圏の同値。局所余極限・延長・各値の表現可能性を未証明の入力に置かない。
  `IsIdempotentCompletion.equivalence_unique` は同じ元の圏の二つの完備化を、元の両包含への全自然同型を保つ同値で比較。HTT 5.1.4.2〜9 を完了。
  **F2N-4(d) の零対象条件を完了。** 元の retract と前後合成の全自然同型から全 pinched Hom の可縮性を移送。任意の冪等完備化は元の指定始対象・終対象・零対象の同じ像を保存し、`HasZeroVertex (Idem C)` を構成。新しい対象・射の fiber/cofiber と安定性も下記で完了。
  **既存の全極限・余極限の保存を完了。** 全部分圏の slice を元の右 fibration の厳密な底変換と照合し、元の頂点像への同値で任意の冪等完備化へ拡張。任意の添字の指定された元の全錐・余錐の像を保持する。普遍四角形・fiber/cofiber 列も保存し、`idemYoneda_isExactFunctor` を構成。標的の安定性・新しい図式の極限存在は仮定しない。
  **全辺の関手圏の冪等完備化を完了。** 両端の元の retract を、終点固定の slice と始点固定の coslice で順に持ち上げ、元の全辺の関手 ∞ 圏内の retract を構成。元の任意の辺は元の始域の辺の像の retract。任意の関手 ∞ 圏の coherent 完備性を証明し、元の後合成 `Fun(Δ¹,C) → Fun(Δ¹,D)` 自身を冪等完備化と判定。同じ両辺を固定する全 Idem・全 Split 図式も回収。新しい辺の fiber/cofiber の存在へ下記で接続。
  **全普遍図式の retract 閉性を完了。** 元の関手の写像空間比較を、前合成の全自然同型を持つ retract 正方形で比較し、相対始対象性と始点境界充填の閉性を証明。全普遍余錐の ∞ 圏は冪等完備。任意の全図式の極限・余極限の存在、元の押し出し・引き戻し四角形、零対象は全関手圏内の retract で閉じる。`bicartesianZeroSquares` の全部分 ∞ 圏と coherent 冪等完備性を構成。下辺への射影と新しい辺への回収も下記で完了。
  **F2N-4(d)：安定性を完了（HA 1.1.3.7）。** 零角の双普遍四角形の下辺射影の正次元全境界充填・充満忠実性と Kan 同値持ち上げを証明。元の辺の retract から像の閉性で双普遍四角形を回収し、指定辺を厳密に保持する実 cofiber を構成。反転で実 fiber も構成し、零角の双方向判定へ接続。
  `IsIdempotentCompletion.isStable` は任意の冪等完備化の安定性。宇宙持ち上げの安定性も証明し、`idem_isStable` は元の `Idem C` 自身の安定性。標的の安定性・新しい普遍図式の存在を入力に仮定しない。
  **F2N-3 の定義・判定と retract 閉性を完了。** `IsKappaCompact` は κ の宇宙の一般の小さい κ-filtered ∞ 圏と、元の全共変 Hom 関手による指定余極限余錐の保存。添字と標的の宇宙を分け、Ind 用の小さい添字を保持。`IsCompact` は同じ宇宙の ℵ₀ 版。濃度の単調性・filtered 判定・一つの余極限余錐での判定も証明。
  全共変表現可能関手を一つの反変な単体的関手に束ね、元の対象の retract を全自然 retract へ写す。相対始点境界充填の閉性で全余錐・保存関手の retract 閉性を証明。元の対象の κ-compact 性の retract 閉性・同型不変性を導く。
  `kappaCompactObjects` は元の全部分 quasicategory、包含は充満忠実。元の圏が coherent 冪等完備なら compact 部分も冪等完備。Yoneda 像の compact 性や Ind の単一 filtered 表示は未証明の入力にしていない。
  **F2N-3(b) の全 Hom と評価の自然比較を完了。** 定義に用いた元の共変 Hom を元の coslice 射影の分類図式へ全自然同型で比較。元の Yoneda 恒等点から評価の全空間への一つの大域射を構成し、同じ元の射の全 fiber 作用を既存の全 Yoneda 評価へ同定。底上の前合成同値性を証明。
  `yonedaInfinityMap_evaluationIso` は元の Yoneda 埋め込みの指定頂点からの全 Hom 関手と、元の前層評価・指定した `spaceUniverseDiagram` の合成との全自然同型。値ごとの同値だけで代用しない。宇宙変更の小さい余極限保存と前層内の compact 性本体は下記で完了。
  **宇宙変更の全空間比較を構成。** 元の任意の弱ホモトピー同値を、同じ写像の任意の宇宙持ち上げで保存する。元の全空間余錐の指定 fiber 写像は、小さい検査標的だけでなく一段大きい全 Kan 標的で弱同値。
  `spaceUniverseTransportRepresentation` は指定した同じ宇宙変更が元の全空間の持ち上げを実際に表現するデータ。元の一つの余錐全体から図式部分と指定頂点へ cartesian 制限し、両図式と元の pointed 写像を厳密に回収。元の fiber 写像と宇宙変更後の同じ余錐の fiber 写像の可換性・小余極限保存は下記で完了。
  **同じ fiber 写像の全 prism を構成。** 元の全余錐の全空間内で、始点は図式部分の包含、終点は元の `coconeFiberMap` と指定頂点の包含の合成。
  同じ一つの宇宙変更表現で prism 全体を送り、両端と元の join 円柱の底を厳密に回収。同じ終点を指定頂点の fiber へ分解する実比較 `coconeUniverseVertexMap` と、その包含式・同値性を完了。同じ始点・同じ join 円柱の二つの実 prism の終点一意性で、`coconeUniverseFiberIso` に全自然比較を構成。
  **F2N-3(b) の前層内を完了。** `spaceUniverseDiagram_map_isColimit` は元の任意の小さい coherent 図式の指定余極限余錐の保存。標準全空間余錐の元の弱同値を同じ余錐像へ移し、任意の余錐へ普遍性で移送。
  `yonedaInfinityMap_isKappaCompact`・`representablePresheafInfinity_isKappaCompact` は元の全共変 Hom による κ-compact 性。評価の全自然比較と指定余錐像の厳密な後合成式を使用。Ind 内の元の Yoneda 像の κ-compact 性も下記で完了。
  **F2N-3(b) 完了。** 全部分包含の元の coslice 正方形を厳密な引き戻しとし、`fullSubcomplexCovariantIso` は包含後の元の全 Hom と元の部分圏の全 Hom の全自然比較。
  `indYoneda_isKappaCompact` は元の Ind-Yoneda 像の κ-compact 性。元の包含による指定 κ-filtered 余極限保存と前層の compact 性を合成。F1 の単一 filtered 表示・compact 生成は仮定しない。
  **(c) の全 Hom 極限表示を完了。** `colimitRepresentableCone` は元の余極限余錐を、同じ余極限頂点からの全共変 Hom を頂点とする全極限錐へ写す。任意の全パラメーター図式へ制限しても、同じ各点極限・関手圏の極限を保持。有限形状や通常の図式だけに制限しない。
  **(d) の実比較を完成（正則 κ）。** 元の恒等図式の余錐から Idem 形状の任意 κ での κ-filtered 性を証明。同じ全 Idem 図式の小さい余極限により `ind_isIdempotentComplete` と `compactInd_isIdempotentComplete` を構成。
  `idemToCompactInd` は元の包含を保持する充満忠実な全比較。両 Yoneda の全因子化も厳密に一致。本質全射性と「全 compact Ind 対象が元の Yoneda 像の retract」の同値を証明。下記の実回収を代入し、同じ比較自身の全 ∞ 圏同値まで完成。
  **元の値からの点の回収を証明。** 離散 Kan 標的の全ラベルで成分を分離し、`weakHomotopyEquivalence_mapPiZero_surjective` を元の始域の Kan 性なしに証明。
  `coherentTotalKan_point_representative` は元の全空間 Kan 模型の任意の点を、元の一つの値から同じ比較射で成分まで回収。底の filtered 性も不要。元の脚の全一単体との一致・fiber 制限の実輸送・Kan 値への全自然比較も構成。`coherentTotalCoconeLeg_point_representative` は標準余錐の点を元の同じ脚の作用で回収。余錐同型と元の全合成三角形で任意の指定余極限余錐へ移送し、`colimitCoconeLeg_point_representative` を構成。元の全 Hom と coslice 表現の全比較・元の輸送と Kan 値の自然比較を通し、恒等点への実際の coslice 辺を回収。`IsKappaCompact.retract_of_colimit` は任意の元の κ-filtered 余極限表示の一項への retract。
- **残り**（依存順、粗い見積もり）：
  1. F2N-3(c) の非空有限余極限閉性：空形状は始対象の compact 性で完了。全 Hom 錐族の指定余錐について点ごとの補完との全比較を構成し、明示交換入力からの閉性を完了。残りは F1b の全有限交換の実証拠を渡す工程。HTT 5.3.4、提供後1コミット。
  **(d)・F2N-4(e) 完了**：`indCompact_retract_yoneda` は指定 Ind 頂点を保つ密度余錐への適用。`compactIndEquivalence` の順方向は元の `idemToCompactInd` そのもの。元の `compactIndYoneda` 自身が冪等完備化で、`compactIndOmegaEquivalence` は ℵ₀ の実比較。
  2. P-1 g：sifted 密度表示は完了。残りは simplicial Ind 表示、filtered 余極限・geometric realization を保つ全関手圏からの Yoneda 制限の同値、sifted 保存と全余極限保存の判定。HTT 5.5.8.14〜15、30〜80時間（暫定）。局所化の存在は P の担当。
- **主要宣言**（namespace `SerrePositivity.InfinityCategories.F2.Idempotent`、型は Lean が正本）：
  `IdemShape`、`SplitShape`、`CoherentIdempotent`、`StrongSplitting`、`IsIdempotentComplete`、`IsIdempotentCompletion`、
  `strongSplitting_exists_of_hasColimit`、`strongSplitting_exists_of_hasLimit`、`strongSplittingSpace_isContractibleKan`、`effectiveSplittingRestriction_trivialKanFibration`、
  `Idem`、`idemYoneda`、`idemYoneda_isIdempotentCompletion`、`isIdempotentComplete_iff_ulift`、`isIdempotentComplete_iff_of_equivalence`、
  `IsIdempotentCompletion.isLeftCofinal`、`IsIdempotentCompletion.isRightCofinal`、`IsIdempotentCompletion.pre_isFullyFaithful_general`、
  `leftKanShapeUniverseIso`、`leftKanShapeUniverseIso_projection`、`leftKanShapeUniverseIso_slice`、`exists_presheafKan_strict_extension`、
  `exists_presheafCompletion_extension`、`exists_diagram_of_retract_presheaves`、`IsIdempotentCompletion.exists_extension`、
  `IsIdempotentCompletion.pre_isQCatEquivalence`、`idempotentCompletionUniversalEquivalence`、`idemYonedaUniversalEquivalence`、`IsIdempotentCompletion.equivalence_unique`、
  `IsIdempotentCompletion.map_isZeroVertex`、`IsIdempotentCompletion.hasZeroVertex`、`idemYoneda_isZeroVertex`、`idem_hasZeroVertex`、
  `IsIdempotentCompletion.mapJoinCone_isLimit`、`IsIdempotentCompletion.mapJoinCocone_isColimit`、`IsIdempotentCompletion.isExactFunctor`、`idemYoneda_isExactFunctor`、
  `arrow_retract_lift`、`functor_isIdempotentComplete`、`IsIdempotentCompletion.arrow`、`IsIdempotentCompletion.arrow_strongSplitting`、
  `hasColimit_of_diagram_retract`、`hasLimit_of_diagram_retract`、`bicartesianZeroSquares_isIdempotentComplete`、`bicartesianZeroBottomProjection`、
  `bicartesianZeroBottomProjection_isFullyFaithful`、`bicartesianZeroBottomProjection_kanEquivalenceLifting`、
  `IsIdempotentCompletion.bicartesian_cofiber_exists`、`IsIdempotentCompletion.bicartesian_fiber_exists`、`IsIdempotentCompletion.isStable`、`isStable_ulift`、`idem_isStable`。
  compact 側（namespace `SerrePositivity.InfinityCategories.F2.Compact`）：`IsKappaCompact`、`IsCompact`、`PreservesKappaFilteredColimits`、`isKappaCompact_of_exists`、
  `covariantRepresentableDiagram`、`covariantRepresentable_retract`、`IsKappaCompact.of_retract`、`isKappaCompact_iff_of_iso`、
  `kappaCompactObjects`、`kappaCompactInclusion_isFullyFaithful`、`kappaCompactObjects_isIdempotentComplete`、
  `covariantRepresentableInfinity_cosliceIso`、`yonedaEvaluationCosliceMap`、`yonedaEvaluationCosliceMap_isPrecompositionEquivalence`、
  `yonedaEvaluation_classificationIso`、`spaceUniverseDiagram`、`yonedaInfinityMap_evaluationIso`、
  `weakHomotopyEquivalence_ulift`、`coherentTotalCoconeFiber_isWeakHomotopyEquivalence`、`spaceUniverseTransportRepresentation`、
  `spaceUniverseCoconeSourceRepresentation`、`spaceUniverseCoconeVertexRepresentation`、`spaceUniverseDiagram_map_isColimit`、
  `yonedaInfinityMap_isKappaCompact`、`fullSubcomplexCovariantIso`、`ind_isKappaCompact_of_presheaf`、`indYoneda_isKappaCompact`、`colimitRepresentableCone_isLimit`、`colimitRepresentableRestriction_isLimit`、
  `ind_isIdempotentComplete`、`idemToCompactInd`、`idemToCompactInd_isFullyFaithful`、`idemToCompactInd_isEssentiallySurjective_iff_retracts`、
  `weakHomotopyEquivalence_mapPiZero_surjective`、`colimitCoconeLeg_point_representative`、`representationValueTransportIso`、`IsKappaCompact.retract_of_colimit`、
  `indCompact_retract_yoneda`、`idemToCompactInd_isQCatEquivalence`、`compactIndEquivalence`、`compactIndYoneda_isIdempotentCompletion`、`compactIndOmegaEquivalence`、`isFilteredInfinity_ulift`、`isKappaCompact_of_isInitialVertex`、`isCompact_of_isInitialVertex`、`isKappaCompact_colimit_of_exchange`、`isKappaCompact_finiteColimit_of_exchange`、`hasFiniteColimits_kappaCompactObjects_of_exchange`。
  P-1 g：`isSiftedInfinity_of_hasBinaryCoproducts`、`sigmaElementsYonedaDiagram`、`sigmaDensityCocone`、`sigmaDensityCocone_isColimit`、`smallLeftConeRestriction_isQCatEquivalence_of_finiteProducts`、`classifiedConeExtension_isContractibleKan`、`exists_classifiedConeLift`、`exists_classifiedLimitCone`、`sigmaPresheafElements_isSifted`、`sigmaPresheaf_siftedPresentation`、`sigmaPresheaf_sifted_induction`。N-1〜4 の保存済み公開名・型は `HomotopyLimits.lean` と `scripts/audit_homotopy_limits.lean`、F2N-4 は独立集約と独立監査を参照。
- **依存と提供**：F2・F1B・F1 は読み取り専用。P（`F2/Presentable/`）も読み取り専用。所有は `HomotopyLimits/`・既存 N 集約・監査、`InfinityCategories/F2/Idempotent/`・独立集約 `F2/Idempotent.lean`・独立監査 `scripts/audit_f2_idempotent.lean`、新設 `F2/Compact/`・`F2/Compact.lean`・`scripts/audit_f2_compact.lean`、本 N 節だけ。
  F2 集約を変更しない。`infinity-core-F2.md` の表は読み取り専用。現在の分担は F1 が Ind・Ind 安定性、F1b が a7、P が accessible・presentable・局所化の存在、N が P-1 g と a7 差し替え。規約は `foundations.md` §8。
- **未コミット**：なし（今回の P_Σ 極限持ち上げ・sifted 生成8モジュール24宣言・既存 N 集約・全監査、本 N 節を保存。他レーンの差分は対象外）。
- **既知の問題**：compact 独立集約7354 jobs・全273宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理・資源上限の引き上げなし。
  F2N-4 の集約ビルド6793 jobs・全609宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理・資源上限の引き上げなし。
  N 集約は今回7705 jobs・全5328宣言監査が終了コード0、標準三公理のみ。指定された N-2 の上面制限・前半全境界の後合成可換性は保存済み（adbdbd14c・963d9e3cf）。`Inputs/Homotopy/KanQuillen.lean` は import せず、主経路に `ModelCategory SSet` を仮定しない。
  固定 SM7・豊穣随伴の合成互換を通常の Quillen 随伴だけから得たとは扱わない。coherent 冪等図式を射の類だけで代用しない。存在・普遍性を未証明の入力フィールドに置いて完成とは扱わない。
- **次の一手**：sifted 密度表示を全左 Kan 延長へ接続する。F1 の読み取り専用の Yoneda comma・小さい元の圏の比較を P_Σ の左 Kan 添字へ移し、同じ射影と密度全余錐を保つ比較を構成する。
  その後、元の制限関手の全充満忠実性・本質的全射性を示す。filtered 余極限・geometric realization による表示と保存、Yoneda の有限余積保存、HTT 5.5.8.15(2)(3) も残す。accessible・presentable は P の公開宣言を待つか明示入力にし、局所化の存在を独自に実装しない。
  F2N-3 は F1b の a7 提供後、`IndFiniteLimitExchangeInput.exchange` への実証拠受け渡しだけを1コミットで保存。N-2 の再監査は不要。
  原典：[HTT §4.4.5・§5.1.4・5.5.8.14〜15](https://www.math.ias.edu/~lurie/papers/HTT.pdf)、[HA 1.1.3.7](https://www.math.ias.edu/~lurie/papers/HA.pdf)（いずれも本文照合済み）。

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
