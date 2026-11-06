# Kerodon Ch 8〜10 の被覆状況（Lean 形式化と Mathlib）

調査日：2026-11-06（main 7d5006ee7、読み取りのみ）。対象：SerrePositivity/InfinityCategories/（Archive を除く。F1・F1B・F2・Core・Stable・StablePresentable・HomotopyLimits を主に）と Mathlib。Kerodon 本文は各 Subsection ページ（kp/<Tag>.html、抽出は stmts.txt）。

判定：「あり」＝主な定義と主要定理が sorry なしである。「一部」＝定義だけ、または一部の定理だけ。「なし」。Mathlib の 1 圏版しかない ∞ 圏的 Subsection は「なし」とし、備考に書く（8.5.2 だけは原典自体が 1 圏の節なので Mathlib で「あり」）。

sorry：InfinityCategories 全体で `sorry` は ModelBridge/Inputs/KanQuillen.lean の 1 件（Hovey 3.6.5 の引用）だけ。F1・F1B・F2・Core・Stable・StablePresentable・HomotopyLimits のどのファイルもそれを import しない（grep で確認）。表の宣言はすべてこの範囲。ソース上の確認であり、公理監査の実行はしていない。

## 集計

| 章 | Subsection | あり | 一部 | なし |
| --- | --- | --- | --- | --- |
| Ch 8 | 58 | 9 | 10 | 39 |
| Ch 9 | 58 | 15 | 20 | 23 |
| Ch 10 | 11 | 0 | 1 | 10 |
| 計 | 127 | 24 | 31 | 72 |

節ごと（あり／一部／なし）：8.1：1/1/8、8.2：0/0/6、8.3：2/3/2、8.4：1/4/4、8.5：5/2/3、8.6：0/0/9、8.7：0/0/7、9.1：2/5/2、9.2：2/5/2、9.3：3/1/3、9.4：3/5/1、9.5：4/3/0、9.6：0/0/9、9.7：1/1/6、10.1：0/1/5、10.2：0/0/5

## 要点

- 実装の多くは HTT 経由。Kerodon の引用は 8.1.1（twisted arrow／edgewise subdivision、組合せ論の補題が中心）と 9.1.1.16〜19（filtered）だけで、あとは内容から照合した。
- HTT 経由の主な塊：冪等完備化（HTT 4.4.5・5.1.4 → Kerodon 8.5.1〜8.5.5）、Yoneda と前層（HTT 5.1.3・5.1.5.3 → 8.3.1・8.3.3・8.4.2）、Ind と compact（HTT 5.3.1.18・5.3.3.3・5.3.4・5.3.5 → 9.1.8・9.2.5・9.2.8・9.3.1・9.3.2・9.3.4）、accessible・presentable（HTT 5.4.2・5.5.1〜5.5.4 → 9.4.7・9.4.8・9.5.1・9.5.2・9.5.6・9.5.7）、P_Σ と sifted（HTT 5.5.8 → 9.7.1・9.7.2）。
- 目立つ空白：8.1.3〜8.1.10（cospan・Beck–Chevalley）、8.2 全体（coupling）、8.6 全体（conjugate・dual fibration、opposition、coend）、8.7 全体（fiberwise cocompletion・flat）、9.6 全体（factorization system、small object argument。Mathlib に 1 圏版のみ）、9.7.3〜9.7.8（Lurie のテンソル積）、Ch 10 のほぼ全体（semisimplicial・Čech nerve・split・sieve・regular）。
- 「一部」でよく欠けているもの：前層の自由余完備化の同値 Fun^L(P(C),D) ≃ Fun(C,D)（P_Σ・Ind 版はある）、filtered と有限極限の交換の逆向き、Pr^L ≃ (Pr^R)^op の全体（対ごとはある）と Pr^L の小極限（e6・e7、段階 II へ）。

## 表


### 8.1

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.1.1 | 03JF | The Twisted Arrow Construction | あり | `TwistedArrow`・`twistedArrowProjection_leftFibration`（F1/TwistedArrow/Projection・LeftFibration）、`edgewiseSubdivision`（F1/TwistedArrow/EdgewiseSubdivision） | 自前。Kerodon 8.1.1.x を直接引用（唯一の Ch 8 本格引用群）。8.1.1.10（N(Tw C) ≅ Tw N(C)）・8.1.1.15（相対版）は未確認 |
| 8.1.2 | 03JV | Homotopy Transport for Twisted Arrows | 一部 | `twistedArrowHomSpace`（F1/TwistedArrow/HomSpace）、`twistedArrowHomValueEquivalence`（F1/MappingSpaces/HomInfinityBifunctor） | 自前。fiber と写像空間の比較のみ、Tw の輸送表現の一般論はなし |
| 8.1.3 | 00AY | The Cospan Construction | なし | — | Mathlib にも Cospan 構成なし |
| 8.1.4 | 03L4 | Cospans in ∞-Categories | なし | — | Stable の cospan は図式の名前で無関係 |
| 8.1.5 | 03LE | Thin 2-Simplices of Cospan(C) | なし | — |  |
| 8.1.6 | 048Z | Restricted Cospans | なし | — |  |
| 8.1.7 | 049E | Comparing C with Cospan(C) | なし | — |  |
| 8.1.8 | 03KZ | Morphisms in the Duskin Nerve | なし | — | Duskin nerve は Mathlib に TODO のみ |
| 8.1.9 | 049W | Cospan Fibrations | なし | — |  |
| 8.1.10 | 04AB | Beck-Chevalley Fibrations | なし | — |  |

### 8.2

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.2.1 | 043X | Representable Couplings | なし | — | coupling の概念なし |
| 8.2.2 | 0448 | Morphisms of Couplings | なし | — |  |
| 8.2.3 | 044Q | Representations of Couplings | なし | — |  |
| 8.2.4 | 0455 | Presentations of Representable Couplings | なし | — |  |
| 8.2.5 | 045R | Adjunctions as Couplings | なし | — | 随伴そのものは F1B/Adjunction にあるが coupling 経由ではない |
| 8.2.6 | 045W | Balanced Couplings | なし | — |  |

### 8.3

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.3.1 | 03M2 | Yoneda's Lemma | あり | `yonedaPresheafEvaluation_isQCatEquivalence`（F1/Yoneda/YonedaPresheafEvaluation）、`yonedaInfinityEvaluatedTransport_isQCatEquivalence`（F1/Yoneda/YonedaEvaluatedTransportEquivalence） | 自前（Tw 経由。HTT 5.1.3 系） |
| 8.3.2 | 03MA | Profunctors of ∞-Categories | 一部 | `twistedArrowHomInfinity`・`homInfinityJointEvaluation`（F1/Yoneda/YonedaInfinityConstruction） | 自前。C^op×C→𝒮 の Hom 二変数関手だけ、一般の profunctor・普遍元はなし（Mathlib の Profunctor は 1 圏） |
| 8.3.3 | 03MR | Hom-Functors for ∞-Categories | あり | `yonedaInfinityMap`（F1/Yoneda/YonedaInfinityConstruction）、`yonedaInfinityMap_isFullyFaithful`（F1/Yoneda/YonedaInfinityFullyFaithful）、`coyonedaInfinityMap_isFullyFaithful`（F2/Presentable/CoYonedaFullyFaithful） | 自前。Kerodon 8 を引用。「Hom-functor」の抽象的定義（輸送表現としての特徴づけ）はなし |
| 8.3.4 | 03NQ | Representable Profunctors | 一部 | `IsRepresentableSmallSpaceFunctor`（F2/Presentable/ContravariantContinuity）、`exists_leftAdjoint_iff_covariantHom_representable`（F2/Presentable/AdjunctionFromHomRepresentation） | 自前。関手の表現可能性と随伴の判定はある、profunctor 版はなし |
| 8.3.5 | 046H | Recognition of Hom-Functors | なし | — |  |
| 8.3.6 | 03N5 | Strict Models for Hom-Functors | 一部 | `RepresentableHomInfinity` ほか（F1/Coherent/RepresentableHom*） | 自前。coherent nerve の豊穣 Hom と共変 Hom の比較（HTT 5.1.3）。8.3.6.7 の引き戻し四角形はなし |
| 8.3.7 | 06BY | Hom-Functors for Oriented Fiber Products | なし | — |  |

### 8.4

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.4.1 | 03V8 | Dense Functors | 一部 | `DenseCanonicalColimits`（F2/Presentable） | 自前。局所的な密度余錐のみ、dense 関手の一般定義はなし（Mathlib の Presentable/Dense は 1 圏） |
| 8.4.2 | 03W1 | Density of Yoneda Embeddings | あり | `presheafDensityCocone_isColimit`（F1/Yoneda/PresheafDensity/PresheafDensity）、`presheafDensityEvaluationCocone_isColimit` | 自前。HTT 5.1.5.3 |
| 8.4.3 | 03W8 | Cocompletion via the Yoneda Embedding | 一部 | `presheaf_exists_yonedaLeftKan`・`presheafYonedaLeftKan_canonicalColimits`（F2/Presentable/PresheafYonedaLeftKan）、`presheafInfinity_hasLimit`（F1/Yoneda/PresheafAllSmallLimits） | 自前。前層の小（余）極限と Yoneda 左 Kan 延長の存在はある。Fun^L(P(C),D) ≃ Fun(C,D)（HTT 5.1.5.6）の同値としての述べはなし（P_Σ・Ind 版はある） |
| 8.4.4 | 06YD | Example: The Universal Property of 𝒮 | なし | — | 𝒮 の普遍性の単独の述べなし |
| 8.4.5 | 03WM | Cocontinuous Extensions | 一部 | `presheaf_exists_yonedaLeftKan`、`sigmaLeftKanExtension_preservesSmallColimits_iff`（F2/Presentable/SigmaLeftKanAllColimitPreservation） | 自前。延長の存在と P_Σ での余極限保存判定のみ |
| 8.4.6 | 04BH | Adjoining Colimits to ∞-Categories | 一部 | Ind（`indKappaContinuousRestrictionEquivalence`）、P_Σ（`sigmaSiftedContinuousRestriction_isQCatEquivalence`）、冪等完備化 | 自前。特定の 𝕂 の場合のみ、一般の 𝕂-cocompletion はなし（HTT 5.3.6 相当なし） |
| 8.4.7 | 060N | Functoriality of Cocompletion | なし | — |  |
| 8.4.8 | 03WR | Recognition of Cocompletions | なし | — |  |
| 8.4.9 | 04BU | Cocompletion and Right Fibrations | なし | — |  |

### 8.5

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.5.1 | 03YH | Retracts in ∞-Categories | あり | `IsRetractPresheaf`（F1/Idempotent/PresheafClosure）、`Core/Retracts`、Ret 図式 `WeakShape`・`WeakInnerAnodyne`（Core/Idempotent, F2/Idempotent） | 自前。HTT 4.4.5.2・5.1.4.2 |
| 8.5.2 | 03ZE | Idempotents in Ordinary Categories | あり | Mathlib `CategoryTheory.IsIdempotentComplete`・`Karoubi`（Mathlib/CategoryTheory/Idempotents/） | Mathlib（1 圏） |
| 8.5.3 | 03ZS | Idempotents in ∞-Categories | あり | `CoherentIdempotent`・`StrongSplitting`（Core/Idempotent/Coherent）、`WalkingIdem`・`WalkingSplit`（Core/Idempotent/Walking） | 自前。HTT 4.4.5 |
| 8.5.4 | 0405 | Idempotent-Completeness | あり | `IsIdempotentComplete`（Core/Idempotent/Coherent）、`presheafInfinity_isIdempotentComplete`（F1/Idempotent/PresheafComplete）、`functor_isIdempotentComplete`（F2/Idempotent/FunctorComplete） | 自前。HTT 4.4.5.13〜16、5.1.4.3 |
| 8.5.5 | 040T | Idempotent-Completion | あり | `IsIdempotentCompletion`・`idemYoneda_isIdempotentCompletion`（F1/Idempotent/Completion）、`idempotentCompletionUniversalEquivalence`（F2/Idempotent/UniversalProperty）、`IsIdempotentCompletion.equivalence_unique` | 自前。HTT 5.1.4.1〜5.1.4.9。安定性 `IsIdempotentCompletion.isStable` も |
| 8.5.6 | 05M8 | Morita Equivalence | 一部 | `IsIdempotentCompletion.pre_isQCatEquivalence`（F2/Idempotent/UniversalProperty） | 自前。Morita 同値の定義と 8.5.6.11 の判定はなし |
| 8.5.7 | 0418 | Idempotent Endomorphisms | 一部 | `WeakExtension`（弱 retract の強分裂への延長と可縮性）、`EffectiveIdempotents`（F2/Idempotent） | 自前。HTT 4.4.5.6・4.4.5.16。End^idm からの左ホモトピー逆（8.5.7.4）はなし |
| 8.5.8 | 041V | Homotopy Idempotent Endomorphisms | なし | — | HTT 4.4.5.20 相当なし |
| 8.5.9 | 042C | Partial Idempotents | なし | — |  |
| 8.5.10 | 042T | The Thompson Groupoid | なし | — |  |

### 8.6

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.6.1 | 04C6 | Conjugate Fibrations | なし | — | conjugate / dual fibration なし |
| 8.6.2 | 04CM | Existence of Conjugate Fibrations | なし | — |  |
| 8.6.3 | 04EC | Uniqueness of Conjugate Fibrations | なし | — |  |
| 8.6.4 | 04D0 | Dual Fibrations | なし | — |  |
| 8.6.5 | 04DS | Existence of Dual Fibrations | なし | — |  |
| 8.6.6 | 04ET | Comparison of Dual and Conjugate Fibrations | なし | — |  |
| 8.6.7 | 04F8 | The Opposition Functor | なし | — | opposition 関手なし |
| 8.6.8 | 05WD | Contravariant Transport Representations | なし | — | cartesian fibration の反変輸送表現なし（右 fibration の前層 unstraightening は F1/Yoneda/PresheafUnstraightening） |
| 8.6.9 | 06TV | Coends of ∞-Categories | なし | — | coend なし |

### 8.7

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 8.7.1 | 05KB | Uniqueness of Fiberwise Cocompletions | なし | — |  |
| 8.7.2 | 05LC | Fiberwise Cocompletions of Cocartesian Fibrations | なし | — |  |
| 8.7.3 | 05LR | Fiberwise Cocompletion of Cartesian Fibrations | なし | — |  |
| 8.7.4 | 05M1 | Existence of Fiberwise Cocompletions | なし | — |  |
| 8.7.5 | 05ML | Application: Flat Inner Fibrations | なし | — | flat inner fibration なし |
| 8.7.6 | 05NH | Flatness and Morphism Spaces | なし | — |  |
| 8.7.7 | 05NN | Fiberwise Cocompletion via the Yoneda Embedding | なし | — |  |

### 9.1

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.1.1 | 02P8 | Filtered ∞-Categories | あり | `IsFilteredInfinity`・`IsKappaFiltered`（Core/Filtered/FilteredInfinity）、`isWeaklyContractible_of_isFilteredInfinity`（Stable/Filtered/FilteredWeakContractibility）、`isRightCofinal_constantDiagram_of_filtered`（Stable/Filtered/FilteredDiagonalCofinality） | 自前。Kerodon 9.1.1.16〜19 を引用（Ch 9 の引用はここだけ） |
| 9.1.2 | 02PM | Local Characterization of Filtered ∞-Categories | なし | — | h C の homotopy filtered による判定（9.1.2.5）なし |
| 9.1.3 | 02Q4 | Fibrations over Filtered ∞-Categories | 一部 | `coherentFilteredTotalKan_isContractibleKan`（F1/Filtered/FilteredLeftFibrationContractibility）、`fiberProductToProduct_isRightCofinal`（Stable/Filtered/FiberProductCofinality） | 自前。9.1.3.2（E filtered ⇔ 弱可縮）はなし |
| 9.1.4 | 06CJ | Cofinal Functors of Filtered ∞-Categories | 一部 | `isRightCofinal_sliceUnderProjection_of_filtered`（Stable/Filtered/FilteredCosliceCofinality） | 自前。9.1.4.5 の cofinality 判定はなし |
| 9.1.5 | 05XR | Filtered Colimits of Spaces | 一部 | `coherentFilteredLimitExchangeShape_finite`（F2/Ind/CoherentFiniteLimitExchange）、`coherentCardinalFilteredLimitExchange_poset`（F2/Presentable） | 自前（HTT 5.3.3.3。証明に Mathlib の FilteredColimitCommutesFiniteLimit を点ごとに使用）。filtered ⇒ 交換の向きのみ、逆向きなし |
| 9.1.6 | 03DD | Filtered Colimits of Simplicial Sets | 一部 | `filteredColimitMap_isWeakHomotopyEquivalence`（HomotopyLimits/FilteredExchange/FilteredWeakEquivalences） | 自前。filtered 余極限による弱同値の保存のみ |
| 9.1.7 | 061E | Approximation by Simplicial Subsets | 一部 | `SmallFilteredPieces`・`smallFilteredPieces_cover`（F2/Presentable/SmallFilteredPieces） | 自前。濃度の小さい filtered 部分への分解の一形 |
| 9.1.8 | 02Q8 | Approximation by Partially Ordered Sets | あり | `exists_cofinal_kappaFiltered_poset`（F2/Ind/FilteredPosetNerve）、`isKappaFiltered_nerve_of_cardinalFiltered` | 自前。HTT 5.3.1.18 |
| 9.1.9 | 062Y | Filtered Colimits of ∞-Categories | なし | — | QC 内の filtered 余極限なし |

### 9.2

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.2.1 | 06DA | Filtered Cocompleteness | 一部 | `hasColimit_of_discreteRestrictions_geometricRealizations`（F2/Presentable/ColimitFromDiscreteRestrictions）、`preservesSmallColimits_of_coproducts_geometricRealizations` | 自前。HTT 4.4.2.6〜7 型の生成。有限＋filtered ⇒ 余完備の形・(κ,λ)-余完備はなし |
| 9.2.2 | 062B | Finitary Functors | 一部 | `PreservesKappaFilteredColimits`（F2/Compact/Definition） | 自前。定義と保存の補題のみ |
| 9.2.3 | 06E3 | Example: Sequential Cocompleteness | なし | — |  |
| 9.2.4 | 06EG | Fiber Products of Filtered ∞-Categories | 一部 | `pullback_hasSmallKappaFilteredColimits`・`pullback_fst_isKappaAccessibleFunctor`（F2/Presentable/PullbackFilteredColimits） | 自前。accessible cospan に限る |
| 9.2.5 | 0649 | Compact Objects | あり | `IsCompact`・`IsKappaCompact`（F2/Compact/Definition）、`ind_isKappaCompact_iff_yoneda`（F2/Ind/CompactGeneratorImage） | 自前。HTT 5.3.4 |
| 9.2.6 | 067N | Finiteness Conditions on Kan Complexes | 一部 | `finiteSpaceGeneratorVertex_isCompact`（F2/Presentable/FiniteSpaceGenerators）、`exists_spaceCompactCardinal` | 自前。有限空間の compact 性のみ、essentially finite・finitely dominated の定義なし |
| 9.2.7 | 0685 | Finiteness Conditions on ∞-Categories | なし | — |  |
| 9.2.8 | 06EU | Closure Properties of Compact Objects | あり | `isKappaCompact_finiteColimit`（F2/Compact/FiniteColimitClosureUnconditional）、`IsKappaCompact.of_retract`（F2/Compact/RepresentableRetractions）、`kappaCompactObjects_isIdempotentComplete` | 自前。HTT 5.3.4.15 相当 |
| 9.2.9 | 06F5 | Compactness in ∞-Categories of Sections | 一部 | 評価関手の余極限保存（P-12、F2/Presentable/SmallTwistedArrowShapes 付近） | 自前。HTT 5.3.4.9 の結論（Fun 頂点の κ-compact 性）は第 II 段へ保留 |

### 9.3

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.3.1 | 063J | Ind-Completion | あり | `IndInfinity`・`indYoneda_isFullyFaithful`（F2/Ind/PresheafSubcategory）、`IsIndVertex`（F2/Ind/FilteredClosure） | 自前。HTT 5.3.5 |
| 9.3.2 | 0650 | Recognition of Ind-Completions | あり | `indKappaContinuousRestrictionEquivalence`（F2/Ind/IndRestrictionEquivalence）、`compactIndYoneda_isFullyFaithful`（F2/Compact/CompactIndCompletion）、`CompactIndComparisonCriterion` | 自前。HTT 5.3.5.10〜11 |
| 9.3.3 | 06FX | Functoriality of Ind-Completion | 一部 | `indKappaContinuousRestrictionEquivalence` による延長 | 自前。Ind の QC 上の関手化はなし |
| 9.3.4 | 065H | Flat Functors | あり | `isIndVertex_iff_hasKappaFilteredElements`（F2/Ind/FilteredElementsClosure）、`isIndVertex_iff_singleFilteredPresentation` | 自前。HTT 5.3.5.4（元の圏が filtered な前層＝Ind） |
| 9.3.5 | 0669 | Exact Functors | なし | — | 左 fibration による left exact の定義なし（安定の完全関手は別物） |
| 9.3.6 | 068U | Transitivity of Ind-Completion | なし | — |  |
| 9.3.7 | 06GD | Final Objects of Ind-Completions | なし | — |  |

### 9.4

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.4.1 | 0673 | Compactly Generated ∞-Categories | あり | `IsKappaCompactGenerating`（F2/Presentable/Accessible）、`compactGenerationEquivalence`（F2/Ind/CompactGeneration）、`ind_stableCompactGeneration`（F2/Ind/StableCompactGeneration） | 自前。HTT 5.3.5.15、HA 1.1.3.6 |
| 9.4.2 | 06H3 | Compact Functors | 一部 | `adjunction_isKappaCompact_image`（F2/Presentable/AccessibleReflectiveImage）、`adjunction_hom_preservesKappaFilteredColimits_iff` | 自前。compact 関手の一般論はなし |
| 9.4.3 | 06YM | Compact Generation of Reflective Localizations | 一部 | `LocalObjects.isPresentable_of_reflection`（F2/Presentable/Localization） | 自前。反射部分圏の presentable 性のみ、compact 生成の保存はなし |
| 9.4.4 | 06HP | Compact Generation of Oriented Fiber Products | 一部 | lax pullback `laxPullback_isStable`（F2/CatInfinity/LaxPullbackStable） | 自前。oriented fiber product の構成と安定性のみ、compact 生成はなし |
| 9.4.5 | 06J5 | Compact Generation of Homotopy Fiber Products | 一部 | `AccessiblePullback.pullback_isAccessible`（F2/Presentable/AccessiblePullback/Accessibility）、`pullback_isPresentable_of_accessiblePullback` | 自前。HTT 5.4.6.6 相当の accessibility |
| 9.4.6 | 06JJ | Compactly Generated Fibrations | なし | — |  |
| 9.4.7 | 06K5 | Accessible ∞-Categories | あり | `IsKappaAccessible`・`IsAccessible`（F2/Presentable/Accessible）、`IsKappaAccessible.exists_indEquivalence`、`indInfinity_isMuAccessible`（F2/Presentable/IndCardinalChange） | 自前。HTT 5.4.2 |
| 9.4.8 | 06KX | Accessible Functors | あり | `IsKappaAccessibleFunctor`（F2/Presentable/AccessibleFunctor）、`RightAdjointAccessibility` | 自前。HTT 5.4.2・5.5.2 |
| 9.4.9 | 06LD | Stability Properties of Accessible ∞-Categories | 一部 | `functorPostcomp_isKappaAccessible`（F2/Presentable/FunctorPresentable）、`PiAccessibility`、`LimitFamilyAccessibility` | 自前。積・Fun(K,−)・引き戻し。edgewise accessible fibration はなし |

### 9.5

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.5.1 | 06NE | Presentable ∞-Categories | あり | `IsPresentable`（F2/Presentable/Definition）、`presheaf_isPresentable`（F2/Presentable/PresheafPresentable）、`IsPresentable.hasSmallLimits`（F2/Presentable/PresentableSmallLimits） | 自前。HTT 5.5.1・5.5.2.4 |
| 9.5.2 | 06Q4 | The Adjoint Functor Theorem | あり | `exists_leftAdjoint_iff_accessible_preservesLimits`（F2/Presentable/NativeAdjointFunctorCriterion）、`adjunction_preservesSmallColimits`、右随伴の存在判定（LeftAdjointFunctorCriterion） | 自前。HTT 5.5.2.9 |
| 9.5.3 | 06UF | The ∞-Category of Presentable ∞-Categories | 一部 | `PrL`・`PrR`（F2/Presentable/PrInfinity）、`presentableAdjointFunctorEquivalence`（F2/Presentable/Duality/PairDuality） | 自前。HTT 5.5.3.1・5.2.6.2。全体の双対 Pr^L ≃ (Pr^R)^op（5.5.3.4）は未完、presentable fibration なし |
| 9.5.4 | 06P5 | Closure Properties of Presentable ∞-Categories | 一部 | `piSSet_isPresentable`・`tensor_isPresentable`（二項積）・`functor_isPresentable`・`pullback_isPresentable_of_accessiblePullback` | 自前。HTT 5.5.3.6。Pr^L の小極限（5.5.3.13）は保留 |
| 9.5.5 | 06US | Cocontinuous Functors | 一部 | `IsPresentable.exists_reflectiveIndModel`、`IsKappaAccessible.exists_indEquivalence` | 自前。κ-presentable の定義と 9.5.5.17 型の特徴づけはなし |
| 9.5.6 | 06UU | Bousfield Localization | あり | `bousfield_isReflectiveSubcategory`・`bousfieldLocalizationFunctor_isLocalization_generatedEdges`（F2/Presentable/Localization） | 自前。HTT 5.5.4 |
| 9.5.7 | 06VG | Existence of Bousfield Localizations | あり | `bousfieldLocalObjects_isPresentable`（F2/Presentable/Localization/BousfieldReflection）、`exists_bousfieldLocalReplacement` | 自前。HTT 5.5.4.15（5.5.4.14 の飽和クラスも） |

### 9.6

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.6.1 | 04KZ | Digression: Transfinite Composition | なし | — | Mathlib に 1 圏の `TransfiniteCompositionOfShape` |
| 9.6.2 | 04LG | Weakly Local Objects | なし | — |  |
| 9.6.3 | 04M7 | The Small Object Argument | なし | — | Mathlib に 1 圏の small object argument（CategoryTheory/SmallObject） |
| 9.6.4 | 04MH | Lifting Problems in ∞-Categories | なし | — | Mathlib に 1 圏の `HasLiftingProperty` |
| 9.6.5 | 04N9 | Weak Factorization Systems | なし | — | Mathlib に 1 圏の `IsWeakFactorizationSystem` |
| 9.6.6 | 04NJ | Orthogonality | なし | — |  |
| 9.6.7 | 04PQ | Uniqueness of Factorizations | なし | — |  |
| 9.6.8 | 04PC | Factorization Systems | なし | — |  |
| 9.6.9 | 06X2 | Accessible Factorization Systems | なし | — | Bousfield 用の強飽和クラスはあるが分解系ではない |

### 9.7

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 9.7.1 | 06ZF | Relative Cocompletion | 一部 | P_Σ：`sigmaSiftedContinuousRestriction_isQCatEquivalence`（F2/Presentable/SigmaRestrictionEquivalence） | 自前。HTT 5.5.8.15 の特別な場合のみ |
| 9.7.2 | 02QD | Digression: Sifted ∞-Categories | あり | `IsSiftedInfinity`（F2/Presentable/SiftedInfinity）、`simplexDegreeDiagonal_nerve_isRightCofinal`（Δ^op は sifted、SiftedSimplexCategory）、`isSiftedInfinity_of_hasBinaryCoproducts`、`totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted` | 自前。HTT 5.5.8.1〜8。Mathlib に 1 圏の `IsSifted` |
| 9.7.3 | 0707 | Tensor Products of ∞-Categories | なし | — | Lurie テンソル積なし（`tensor_isPresentable` は二項積） |
| 9.7.4 | 070Q | Unitality | なし | — |  |
| 9.7.5 | 0713 | Tensor Products of Presentable ∞-Categories | なし | — |  |
| 9.7.6 | 071H | Locally Truncated ∞-Categories | なし | — |  |
| 9.7.7 | 071U | Associativity | なし | — |  |
| 9.7.8 | 072B | Idempotent ∞-Categories | なし | — |  |

### 10.1

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 10.1.1 | 04QQ | Geometric Realization | 一部 | `PreservesSmallGeometricRealizations`（F2/Presentable/SigmaFilteredGeometricDetection）、`sigma_hasSmallGeometricRealizations` | 自前。P_Σ の文脈のみ。|S| の余極限表示（10.1.1.1）・augmented 版はなし |
| 10.1.2 | 04R8 | Semisimplicial Objects | なし | — |  |
| 10.1.3 | 05G3 | Skeletal Simplicial Objects | なし | — | Mathlib に SSet の skeleton のみ |
| 10.1.4 | 05GU | Coskeletal Simplicial Objects | なし | — | Mathlib に SSet の coskeletal のみ |
| 10.1.5 | 04SV | The Nerve of a Morphism | なし | — | Čech nerve なし |
| 10.1.6 | 04S6 | Split Simplicial Objects | なし | — | Mathlib に 1 圏の split simplicial object（Splitting） |

### 10.2

| 番号 | Tag | 見出し | 判定 | 宣言（ファイルは SerrePositivity/InfinityCategories/ からの相対） | 出どころ・備考 |
| --- | --- | --- | --- | --- | --- |
| 10.2.1 | 04TZ | Sieves | なし | — | F2/Tensor の篩は表現可能集合値前層の 1 圏的な篩（BS 用）。Mathlib `Sieve` も 1 圏 |
| 10.2.2 | 04WG | Quotient Morphisms | なし | — |  |
| 10.2.3 | 04X1 | Images | なし | — |  |
| 10.2.4 | 04XV | Universal Quotient Morphisms | なし | — |  |
| 10.2.5 | 04YE | Regular ∞-Categories | なし | — | Mathlib に 1 圏の正則圏（RegularCategory） |
