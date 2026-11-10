# Ch 9 交差の抜き取り検査（§8.4）

- 検査日 2026-11-10。対象は -c のやり直しを取り込んだ `0d9e86356` の表。作業枝に §8.4 を含む `e3c1c6c0e` を取り込んだ。
- 乱数の種 `0x0d9e8635`。Python の `random.Random` を一つ使い、第7章から第10章まで章順に処理。各章の番号を整数の組として昇順に並べ、完全対応、partial、none の順に `sample` で重複なく抽出した。上限は 20、10、10 件。
- 抽出後は番号と Kerodon 本文を作業用一覧に出し、-c の status・理由・引用欄を伏せた。原対応表の名前候補と、番号・小節の引用、概念名・双対・特例から探し、共有ロック下で採用候補の `#check` と `#print axioms` を実行した。
- 独立照合を確定した時点のメモの SHA-256 は `f5c84a418ab11d75a1a0ebfcea6916e078cac073cbe296ff7f1e155947783bdd`。その後、差のある各行で -c の宣言と理由を読み直した。
- partial は §8.1 の四分類で判定。比較後に表の status と異なる場合を「比較後の差」と数えた。

| 抽出群 | 母数 | 抽出 | 独立照合の差 | 比較後の差 | 比較後の差の割合 |
| --- | ---: | ---: | ---: | ---: | ---: |
| own・both・mathlib | 31 | 20 | 0 | 0 | 0.0% |
| partial | 303 | 10 | 3 | 1 | 10.0% |
| none | 263 | 10 | 1 | 1 | 10.0% |

完全対応群の比較後の差は §8.4 の停止基準以下。

## 独立照合で差があった行の比較

| Kerodon | -c | 独立 | 比較後 | partial_kind | 比較後に採る判定 | 根拠 |
| --- | --- | --- | --- | --- | --- | --- |
| [9.1.3.11](https://kerodon.net/tag/05XF) | partial | none | partial | special | -c の判定 | Mathlib の `CategoryTheory.instIsFilteredGrothendieckOfαCategoryObjCat` は filtered な通常の底圏と各 `F.obj c` の filtered 性から、対応する Grothendieck 構成の全圏の filtered 性を返す。κ=ℵ₀ と通常圏の Grothendieck 構成に限ったとき、底、ファイバー、全空間が原文と対応する。 |
| [9.2.1.17](https://kerodon.net/tag/06DM) | partial | none | partial | component | -c の判定 | `HasCardinalFilteredColimits.of_le` は κ=ℵ₀ とすると通常圏で全小 filtered 余極限から小 λ-filtered 余極限を直接出す。原文の順方向の第一成分に対応する。逆方向や λ-small 側の成分はこの宣言の結論に含まれない。 |
| [9.3.6.4](https://kerodon.net/tag/068Y) | partial | none | none | — | 独立判定 | `indInfinity_isMuAccessible` と `isKappaAccessible_iff_indEquivalence` の結論はある小準圏からの Ind 同値の存在まで。指定された反復 Ind を始域、直接 Ind を終域に持つ推移性関手 T についての同値も、その構成の成分も返さない。 |
| [9.6.5.6](https://kerodon.net/tag/04M2) | none | partial | partial | special | 独立判定 | -c が挙げた `IsWeakFactorizationSystem` は二つの射クラスに因子分解を課す別の定義。ただし独立照合で型を読んだ `IsStableUnderCobaseChange`、`IsStableUnderRetracts`、`IsStableUnderTransfiniteComposition` は、一つの通常圏の同じ射クラスに対して原文の (1)～(3) をそのまま述べる。通常圏での小さい超限合成の版が直接対応し、準圏や別途与える λ による制限は残る。 |

## own・both・mathlib

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [9.1.1.1](https://kerodon.net/tag/02PB) | own | own | — | own | — | 準圏 C と任意の有限単体集合 K。K→C を延長する join 余錐の非空性を定義する。 | [`SerrePositivity.InfinityCategories.F2.IsFilteredInfinity`](../../../../SerrePositivity/InfinityCategories/Core/Filtered/FilteredInfinity.lean#L25) |
| [9.1.1.4](https://kerodon.net/tag/05X0) | own | own | — | own | — | 濃度 κ と準圏 C。非退化単体の濃度が κ 未満の K の全図式に join 余錐を要求する。cofiltered は同じ述語を反対準圏に適用する。 | [`SerrePositivity.InfinityCategories.F2.IsKappaFiltered`](../../../../SerrePositivity/InfinityCategories/Core/Filtered/FilteredInfinity.lean#L32) |
| [9.1.1.17](https://kerodon.net/tag/02PH) | own | own | — | own | — | 準圏かつ IsFilteredInfinity の C からそのまま IsWeaklyContractible を得る。 | [`SerrePositivity.InfinityCategories.F2.isWeaklyContractible_of_isFilteredInfinity`](../../../../SerrePositivity/InfinityCategories/Stable/Filtered/FilteredWeakContractibility.lean#L59) |
| [9.1.1.19](https://kerodon.net/tag/02PK) | own | own | — | own | — | 準圏間の圏同値に対し、同じ κ の filtered 性を保存し反映する。 | [`SerrePositivity.InfinityCategories.F2.isKappaFiltered_iff_of_isQCatEquivalence`](../../../../SerrePositivity/InfinityCategories/Core/Filtered/FilteredEquivalence.lean#L55) |
| [9.1.1.20](https://kerodon.net/tag/02PL) | own | own | — | own | — | Kan 複体 C について filtered 性と可縮 Kan 性の iff。宣言はリポジトリ内の Archive。 | [`SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_isContractibleKan`](../../../../SerrePositivity/Archive/InfinityCategories/FilteredExchange/FilteredKanContractibility.lean#L67) |
| [9.1.4.16](https://kerodon.net/tag/06D0) | own | own | — | own | — | 有限 K の任意の図式 p に対し coslice 射影が右共終。K=Δ⁰ とすれば対象 C での射影そのもの。 | [`SerrePositivity.InfinityCategories.F2.isRightCofinal_sliceUnderProjection_of_filtered`](../../../../SerrePositivity/InfinityCategories/Stable/Filtered/FilteredCosliceCofinality.lean#L45) |
| [9.2.0.2](https://kerodon.net/tag/063B) | mathlib | mathlib | — | mathlib | — | 通常圏の対象について共 Yoneda の Hom(C,−) が小さいフィルター余極限を保つ条件。 | `CategoryTheory.IsFinitelyPresentable`（`Mathlib/CategoryTheory/Presentable/Finite.lean:49`）、`CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`（`Mathlib/CategoryTheory/Presentable/Finite.lean:69`） |
| [9.2.2.28](https://kerodon.net/tag/06E2) | own | own | — | own | — | 正則 κ で全ての通常の κ-directed poset の nerve 上の余錐を保つなら、全小さい κ-filtered 余錐を保つ。κ=ℵ₀ で原文の非自明な向き。逆は nerve の filtered 性と保存述語の適用。 | [`SerrePositivity.InfinityCategories.F2.Ind.Compact.preservesKappaFilteredColimits_of_poset`](../../../../SerrePositivity/InfinityCategories/F2/Ind/NativePreservationPosetReductionUniverse.lean#L21) |
| [9.2.5.26](https://kerodon.net/tag/064Y) | own | own | — | own | — | 有限図式の各頂点が κ-compact なら、既存の余極限余錐の頂点も κ-compact。κ=ℵ₀ が原文の compact 版。 | [`SerrePositivity.InfinityCategories.F2.Compact.isKappaCompact_finiteColimit`](../../../../SerrePositivity/InfinityCategories/F2/Compact/FiniteColimitClosureUnconditional.lean#L21) |
| [9.3.5.1](https://kerodon.net/tag/066A) | mathlib | mathlib | — | mathlib | — | 通常圏間の関手で有限形状の極限を全て保つ述語。左完全関手は同じ述語を満たす充満部分圏として束ねる。 | `CategoryTheory.Limits.PreservesFiniteLimits`（`Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:44`）、`CategoryTheory.LeftExactFunctor`（`Mathlib/CategoryTheory/Limits/ExactFunctor.lean:51`） |
| [9.4.0.1](https://kerodon.net/tag/06GU) | mathlib | mathlib | — | mathlib | — | 通常圏で正則 κ の存在、κ-filtered 余極限、小さい κ-presentable 生成族を定める。κ-presentable の部分圏の本質的小ささも同じ仮定の下で Mathlib にある。 | `CategoryTheory.IsAccessibleCategory`（`Mathlib/CategoryTheory/Presentable/LocallyPresentable.lean:87`）、`CategoryTheory.IsCardinalAccessibleCategory`（`Mathlib/CategoryTheory/Presentable/LocallyPresentable.lean:50`） |
| [9.4.7.1](https://kerodon.net/tag/06K6) | own | own | — | own | — | 正則 κ の条件の下で κ-accessibility と、小さい準圏 A の Indκ(A) からの同値の存在との iff。 | [`SerrePositivity.InfinityCategories.F2.Presentable.isKappaAccessible_iff_indEquivalence`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/AccessibleEquivalence.lean#L45) |
| [9.4.7.15](https://kerodon.net/tag/06KM) | own | own | — | own | — | accessible 準圏 C と同じ宇宙の任意の濃度上限 σ から、σ より大きい κ-accessibility の濃度を得る。正則性は IsKappaAccessible の成分。 | [`SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.exists_larger`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/IndCardinalChange.lean#L64) |
| [9.4.8.18](https://kerodon.net/tag/06LC) | own | own | — | own | — | 両端が accessible で随伴を与える。右随伴の accessibility は直接、左随伴は小余極限保存から accessibility を得る。 | [`SerrePositivity.InfinityCategories.F2.Presentable.rightAdjoint_isAccessible`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/NativeAdjointFunctorCriterion.lean#L55)、[`SerrePositivity.InfinityCategories.F2.Presentable.adjunction_preservesSmallColimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/LeftAdjointAllColimitPreservation.lean#L69)、[`SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.isAccessibleFunctor`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/Definition.lean#L57) |
| [9.5.0.1](https://kerodon.net/tag/06PT) | mathlib | mathlib | — | mathlib | — | 任意の完備束とその任意の部分集合に対し、sSup が最小上界である。 | `isLUB_sSup`（`Mathlib/Order/CompleteLattice/Defs.lean:82`） |
| [9.5.1.2](https://kerodon.net/tag/06ND) | own | own | — | own | — | 準圏の accessibility と全小余極限の存在を合わせた定義。小極限の存在も別の定理で従う。 | [`SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/Definition.lean#L34)、[`SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasSmallLimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/PresentableSmallLimits.lean#L25) |
| [9.5.2.1](https://kerodon.net/tag/06Q5) | own | own | — | own | — | presentable な二準圏の間で、右随伴の存在は小余極限保存と iff、左随伴の存在は accessibility と小極限保存の連言と iff。 | [`SerrePositivity.InfinityCategories.F2.Presentable.exists_rightAdjoint_iff_preservesSmallColimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/AdjointFunctorTheorem.lean#L45)、[`SerrePositivity.InfinityCategories.F2.Presentable.exists_leftAdjoint_iff_accessible_preservesLimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/NativeAdjointFunctorCriterion.lean#L96) |
| [9.5.7.1](https://kerodon.net/tag/06VH) | own | own | — | own | — | presentable 準圏 C と小さい辺族。指定辺に局所な頂点で張る充満部分圏の反射とその局所化関手を構成する。 | [`SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfield_isReflectiveSubcategory`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/Localization/BousfieldReflection.lean#L36)、[`SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfieldLocalizationFunctor`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/Localization/BousfieldReflection.lean#L51) |
| [9.6.0.3](https://kerodon.net/tag/06VU) | mathlib | mathlib | — | mathlib | — | 通常圏の二射クラス。因子分解・両クラスの retract 閉性・持ち上げの存在から WFS を構成し、WFS からも因子分解と持ち上げを取り出せる。両側の llp／rlp の等式は retract 閉性を含む。 | `CategoryTheory.MorphismProperty.IsWeakFactorizationSystem`（`Mathlib/CategoryTheory/MorphismProperty/WeakFactorizationSystem.lean:35`）、`CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk'`（`Mathlib/CategoryTheory/MorphismProperty/WeakFactorizationSystem.lean:44`）、`CategoryTheory.MorphismProperty.hasLiftingProperty_of_wfs`（`Mathlib/CategoryTheory/MorphismProperty/WeakFactorizationSystem.lean:65`） |
| [9.7.2.10](https://kerodon.net/tag/02QP) | own | own | — | own | — | 小さい宇宙に移した単体圏の反対の nerve が sifted。cosifted は反対の sifted 性という定義。 | [`SerrePositivity.InfinityCategories.F2.Presentable.smallSimplexOpposite_isSiftedInfinity`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/SiftedSimplexCategory.lean#L53) |

## partial

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [9.1.3.11](https://kerodon.net/tag/05XF) | partial | none | — | partial | special | cocartesian fibration の κ-filtered な底と全頂点ファイバーから全空間の κ-filtered 性を探した。PointFiberFilteredColimits はファイバーでの余極限の存在、FilteredRetracts はレトラクトによる filtered 性で、同じ結論を与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.1.5.7](https://kerodon.net/tag/05XW) | partial | partial | component | partial | component | 準圏の filtered 性と、任意の有限 K の対角関手の右共終性との iff を与える。空間で有限極限と交換する二条件はこの型に含まれない。 | [`SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_constantDiagram_rightCofinal`](../../../../SerrePositivity/Archive/InfinityCategories/FilteredExchange/FilteredDiagonalCriterion.lean#L49) |
| [9.1.8.7](https://kerodon.net/tag/02QA) | partial | partial | component | partial | component | 正則 κ と κ-filtered 準圏 C から κ-filtered な通常の半順序集合の nerve と右共終関手を取る。λ 未満の濃度評価は型に含まれない。 | [`SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_cardinalFiltered_poset`](../../../../SerrePositivity/InfinityCategories/F2/Ind/CofinalFilteredPoset.lean#L20) |
| [9.1.8.8](https://kerodon.net/tag/0627) | partial | partial | direction | partial | direction | 正則 κ で κ-filtered 準圏から κ-directed 半順序の nerve による右共終表示を得る。任意の右共終表示から C の κ-filtered 性を取り出す向きは未確認。 | [`SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_kappaFiltered_poset`](../../../../SerrePositivity/InfinityCategories/F2/Ind/FilteredPosetNerve.lean#L31) |
| [9.2.1.17](https://kerodon.net/tag/06DM) | partial | none | — | partial | component | λ-filtered 余極限と λ-small filtered 余極限の二仮定から任意の小さい filtered 余極限の存在を出す型を探索。CardinalDirectedPoset と SmallFilteredPieces は添字の模型で、二仮定だけからの存在を型に持たない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.3.4.26](https://kerodon.net/tag/0666) | partial | partial | special | partial | special | 小さい C と宇宙段で束ねた Indκ について、filtered elements の対象判定と、κ-filtered 余極限を保つ関手の Yoneda 制限の同値がある。指定の κ◁λ における切った宇宙の同定は未確認。 | [`SerrePositivity.InfinityCategories.F2.Ind.indKappaContinuousRestrictionEquivalence`](../../../../SerrePositivity/InfinityCategories/F2/Ind/IndRestrictionEquivalence.lean#L60)、[`SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_iff_hasKappaFilteredElements`](../../../../SerrePositivity/InfinityCategories/F2/Ind/FilteredElementsClosure.lean#L40) |
| [9.3.6.4](https://kerodon.net/tag/068Y) | partial | none | — | none | — | 三つの正則濃度で反復 Ind と直接 Ind を結ぶ指定 T の同値を探索。IndCardinalChange は個々の Ind の accessibility と濃度変更を与えるが、T の型は現れない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.5.1.12](https://kerodon.net/tag/06UE) | partial | partial | special | partial | special | 小さい形状 K と presentable な C に限れば同じ K-indexed limit の存在を与える。指定された λ-compact 生成と λ-small 空間の形状別仮定だけからの一般版は未確認。 | [`SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasLimit`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/PresentableSmallLimits.lean#L36) |
| [9.6.2.13](https://kerodon.net/tag/04LW) | partial | partial | stronger-hyp | partial | stronger-hyp | 同じ準圏の押し出しで、左辺に関する Hom 空間全体の局所性を仮定し、右辺の同じ局所性を得る。空間の同値は成分での弱い局所性を含むが、弱い入力だけの主張は未確認。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.isLocalForHom_pushout_right_of_left`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/Presentable/LocalPushoutEquivalences.lean#L69) |
| [9.7.1.13](https://kerodon.net/tag/06ZU) | partial | partial | special | partial | special | 小さい準圏の全前層への標準 Yoneda では、恒等関手をその Yoneda に沿う左 Kan 延長として表す。指定した関係を課す任意の K-cocompletion は未確認。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.presheafDensity_image_isLeftKanExtension`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/PresheafDensityLeftKan.lean#L67) |

## none

| Kerodon | -c | 独立 | 独立 partial_kind | 比較後 | 比較後 partial_kind | 独立照合での仮定・結論 | 型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [9.2.3.1](https://kerodon.net/tag/06E4) | none | none | — | none | — | Ord<κ の nerve を形状に取る余極限の存在とその保存を探索。SequentialPreservedColimits の自然数列に関する命題は原文の濃度付き存在・保存の定義を置かない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.2.5.11](https://kerodon.net/tag/064L) | none | none | — | none | — | 部分集合の濃度と包含順序の nerve 内での κ-compact 性の iff を探索。Mathlib の IsCompactElement は順序論の compact 性で、準圏の κ-compact 判定と結ぶ型は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.2.7.12](https://kerodon.net/tag/068L) | none | none | — | none | — | 有限単体集合の retract である有限支配性と、CatInfinity の対象としての compact 性の iff を探索。FiniteColimitClosure は既に compact と分かった対象の余極限を扱う。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.3.3.3](https://kerodon.net/tag/063W) | none | none | — | none | — | 指数共終数の条件下で Indκ^λ の本質的 μ-small 性を探した。IndCardinalChange は accessibility の濃度を変更し、Ind 全体の本質的な単体数を評価しない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.4.6.4](https://kerodon.net/tag/06JN) | none | none | — | none | — | 内ファイブレーションの全 Δⁿ への引き戻しに (κ,λ)-compact generation を課す述語を探索。PointFiberFilteredColimits は頂点ファイバーの余極限性だけを扱う。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.5.4.13](https://kerodon.net/tag/06UN) | none | none | — | none | — | Pr の左／右随伴の関手を持つ二つの準圏そのものの小余極限を探索。PresentableSmallLimits は各対象圏の小極限、AdjointComposition は随伴関手の合成を扱う。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.6.1.13](https://kerodon.net/tag/04L9) | none | none | — | none | — | κ-small な超限合成の最小閉包を探索。Mathlib の transfiniteCompositionsOfShape は固定された順序型の一回の合成で、原文の指定濃度の閉包述語と最小性を与える型は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.6.5.6](https://kerodon.net/tag/04M2) | none | partial | special | partial | special | 通常圏の射クラスでは pushout、retract、指定宇宙の全超限合成に閉じる条件が三つともある。準圏および濃度 λ による制限の定義は未確認。 | `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange`（`Mathlib/CategoryTheory/MorphismProperty/Limits.lean:118`）、`CategoryTheory.MorphismProperty.IsStableUnderRetracts`（`Mathlib/CategoryTheory/MorphismProperty/Retract.lean:31`）、`CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition`（`Mathlib/CategoryTheory/MorphismProperty/TransfiniteComposition.lean:299`） |
| [9.6.8.15](https://kerodon.net/tag/04PT) | none | none | — | none | — | 三角形の分解関手が圏同値という条件を含む ∞ 圏の因子分解系判定を探索。通常の WFS の持ち上げの存在は三角形の関手圏の同値を与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [9.7.5.7](https://kerodon.net/tag/071A) | none | none | — | none | — | 二つの compactly generated ∞ 圏の余完備テンソル積の compact generation を探索。TensorSmallColimits の単体集合の積上の余極限性は余完備テンソル積の主張とは対象が異なる。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## 独立照合の kernel 出力

<details>
<summary>SerrePositivity.InfinityCategories.F2.IsFilteredInfinity</summary>

```lean
SerrePositivity.InfinityCategories.F2.IsFilteredInfinity.{u_1} : (C : SSet.{u_1}) → [SSet.Quasicategory.{u_1} C] → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.IsKappaFiltered</summary>

```lean
SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} : Cardinal.{u_1} →
  (C : SSet.{u_1}) → [SSet.Quasicategory.{u_1} C] → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.isWeaklyContractible_of_isFilteredInfinity</summary>

```lean
SerrePositivity.InfinityCategories.F2.isWeaklyContractible_of_isFilteredInfinity.{u_1} : ∀ (C : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} C] [SerrePositivity.InfinityCategories.F2.IsFilteredInfinity.{u_1} C],
  SerrePositivity.InfinityCategories.IsWeaklyContractible.{u_1} C
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.isKappaFiltered_iff_of_isQCatEquivalence</summary>

```lean
@SerrePositivity.InfinityCategories.F2.isKappaFiltered_iff_of_isQCatEquivalence.{u_1} : ∀ {κ : Cardinal.{u_1}}
  {C D : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} C] [inst_1 : SSet.Quasicategory.{u_1} D]
  {f : Quiver.Hom.{u_1, u_1 + 1} C D},
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} f →
    (SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} κ C ↔
      SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} κ D)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_isContractibleKan</summary>

```lean
SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_isContractibleKan.{u_1} : ∀ (C : SSet.{u_1})
  [inst : SSet.KanComplex.{u_1} C],
  SerrePositivity.InfinityCategories.F2.IsFilteredInfinity.{u_1} C ↔
    SerrePositivity.InfinityCategories.IsContractibleKan.{u_1} C
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.isRightCofinal_sliceUnderProjection_of_filtered</summary>

```lean
@SerrePositivity.InfinityCategories.F2.isRightCofinal_sliceUnderProjection_of_filtered.{u_1} : ∀ {K C : SSet.{u_1}}
  [SSet.Finite.{u_1} K] [inst : SSet.Quasicategory.{u_1} C]
  [SerrePositivity.InfinityCategories.F2.IsFilteredInfinity.{u_1} C] (p : Quiver.Hom.{u_1, u_1 + 1} K C),
  SerrePositivity.InfinityCategories.IsRightCofinal.{u_1}
    (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1} p)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_constantDiagram_rightCofinal</summary>

```lean
SerrePositivity.InfinityCategories.F2.isFilteredInfinity_iff_constantDiagram_rightCofinal.{u_1} : ∀ (C : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} C],
  SerrePositivity.InfinityCategories.F2.IsFilteredInfinity.{u_1} C ↔
    ∀ (K : SSet.{u_1}) [SSet.Finite.{u_1} K],
      SerrePositivity.InfinityCategories.IsRightCofinal.{u_1}
        (SerrePositivity.InfinityCategories.F2.constantDiagram.{u_1} K C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_cardinalFiltered_poset</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_cardinalFiltered_poset.{u_1} : ∀ {κ : Cardinal.{u_1}}
  [inst : Fact (Cardinal.IsRegular.{u_1} κ)] (C : SSet.{u_1}) [inst_1 : SSet.Quasicategory.{u_1} C]
  [SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} κ C],
  ∃ I o f,
    CategoryTheory.IsCardinalFiltered.{u_1, u_1, u_1} I κ ∧ SerrePositivity.InfinityCategories.IsRightCofinal.{u_1} f
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_kappaFiltered_poset</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Ind.exists_cofinal_kappaFiltered_poset.{u_1} : ∀ {κ : Cardinal.{u_1}}
  [inst : Fact (Cardinal.IsRegular.{u_1} κ)] (C : SSet.{u_1}) [inst_1 : SSet.Quasicategory.{u_1} C]
  [SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} κ C],
  ∃ I o f,
    CategoryTheory.IsCardinalFiltered.{u_1, u_1, u_1} I κ ∧
      SerrePositivity.InfinityCategories.F2.IsKappaFiltered.{u_1} κ (CategoryTheory.nerve.{u_1, u_1} I) ∧
        SerrePositivity.InfinityCategories.IsRightCofinal.{u_1} f
```

</details>

<details>
<summary>CategoryTheory.IsFinitelyPresentable</summary>

```lean
@CategoryTheory.IsFinitelyPresentable.{u_1, u_2,
    u_3} : {C : Type u_3} → [CategoryTheory.Category.{u_2, u_3} C] → C → Prop
```

</details>

<details>
<summary>CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits</summary>

```lean
@CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X : C},
  CategoryTheory.IsFinitelyPresentable.{u_1, u_1, u_2} X ↔
    CategoryTheory.Limits.PreservesFilteredColimits.{u_1, u_1, u_2, u_1 + 1}
      (CategoryTheory.Functor.obj.{u_1, max u_2 u_1, u_2, max u_2 (u_1 + 1)} CategoryTheory.coyoneda.{u_1, u_2}
        (Opposite.op.{u_2 + 1} X))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.Compact.preservesKappaFilteredColimits_of_poset</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Ind.Compact.preservesKappaFilteredColimits_of_poset.{u_1,
    u_2} : ∀ {κ : Cardinal.{u_1}} [inst : Fact (Cardinal.IsRegular.{u_1} κ)] {C : SSet.{max u_1 u_2}}
  {Y : SSet.{(max u_1 u_2) + 1}} [SSet.Quasicategory.{max u_1 u_2} C] [SSet.Quasicategory.{max (u_1 + 1) (u_2 + 1)} Y]
  (F :
    Quiver.Hom.{max (u_1 + 1) (u_2 + 1), max (u_1 + 2) (u_2 + 2)}
      (CategoryTheory.Functor.obj.{max u_1 u_2, max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1),
          max (u_1 + 2) (u_2 + 2)}
        SSet.uliftFunctor.{(max u_1 u_2) + 1, max u_1 u_2} C)
      Y),
  (∀ (I : Type u_1) [inst_3 : PartialOrder.{u_1} I] [CategoryTheory.IsCardinalFiltered.{u_1, u_1, u_1} I κ]
      (D :
        Quiver.Hom.{max u_1 u_2, max (u_1 + 1) (u_2 + 1)}
          (CategoryTheory.Functor.obj.{u_1, max u_1 u_2, u_1 + 1, max (u_1 + 1) (u_2 + 1)} SSet.uliftFunctor.{u_2, u_1}
            (CategoryTheory.nerve.{u_1, u_1} I))
          C)
      (c : SerrePositivity.InfinityCategories.JoinCocone.{max u_1 u_2} D),
      SerrePositivity.InfinityCategories.IsColimitCone.{max u_1 u_2} c →
        SerrePositivity.InfinityCategories.IsColimitCone.{max (u_1 + 1) (u_2 + 1)}
          (SerrePositivity.InfinityCategories.mapJoinCocone.{max (u_1 + 1) (u_2 + 1)} F
            (SerrePositivity.InfinityCategories.JoinCocone.ulift.{max u_1 u_2, max (u_1 + 1) (u_2 + 1)} c))) →
    SerrePositivity.InfinityCategories.F2.Compact.PreservesKappaFilteredColimits.{u_1, u_2} κ F
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Compact.isKappaCompact_finiteColimit</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Compact.isKappaCompact_finiteColimit.{u_1,
    u_2} : ∀ {κ : Cardinal.{u_1}},
  LE.le.{u_1 + 1} Cardinal.aleph0.{u_1} κ →
    ∀ {K C : SSet.{max u_1 u_2}} [SSet.Finite.{max u_1 u_2} K] [inst : SSet.Quasicategory.{max u_1 u_2} C]
      {D : Quiver.Hom.{max u_1 u_2, max (u_1 + 1) (u_2 + 1)} K C}
      (a : SerrePositivity.InfinityCategories.JoinCocone.{max u_1 u_2} D),
      SerrePositivity.InfinityCategories.IsColimitCone.{max u_1 u_2} a →
        (∀
            (k :
              CategoryTheory.Functor.obj.{0, max u_1 u_2, 0, max (u_1 + 1) (u_2 + 1)} K (Opposite.op.{1} { len := 0 })),
            SerrePositivity.InfinityCategories.F2.Compact.IsKappaCompact.{u_1, u_2} κ
              ((CategoryTheory.ConcreteCategory.hom.{max u_1 u_2, max u_1 u_2, max (u_1 + 1) (u_2 + 1), max u_1 u_2}
                  (CategoryTheory.NatTrans.app.{0, max u_1 u_2, 0, max (u_1 + 1) (u_2 + 1)} D
                    (Opposite.op.{1} { len := 0 })))
                k)) →
          SerrePositivity.InfinityCategories.F2.Compact.IsKappaCompact.{u_1, u_2} κ
            (SerrePositivity.InfinityCategories.JoinCocone.vertex.{max u_1 u_2} a)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.indKappaContinuousRestrictionEquivalence</summary>

```lean
SerrePositivity.InfinityCategories.F2.Ind.indKappaContinuousRestrictionEquivalence.{u_1} : (κ : Cardinal.{u_1}) →
  [Fact (Cardinal.IsRegular.{u_1} κ)] →
    (C : SSet.{u_1}) →
      [inst : SSet.Quasicategory.{u_1} C] →
        (D : SSet.{u_1 + 1}) →
          [inst_1 : SSet.Quasicategory.{u_1 + 1} D] →
            SerrePositivity.InfinityCategories.F2.Ind.HasSmallKappaFilteredColimits.{u_1} κ D →
              SerrePositivity.InfinityCategories.QCatEquivalence.{u_1 + 1}
                (SerrePositivity.InfinityCategories.F2.Ind.KappaContinuousFunctorInfinity.{u_1} κ
                  (SerrePositivity.InfinityCategories.F2.Ind.IndInfinity.{u_1} κ C) D)
                (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} C ⟹ D)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_iff_hasKappaFilteredElements</summary>

```lean
SerrePositivity.InfinityCategories.F2.Ind.isIndVertex_iff_hasKappaFilteredElements.{u_1} : ∀ (κ : Cardinal.{u_1})
  [Fact (Cardinal.IsRegular.{u_1} κ)] (C : SSet.{u_1}) [inst : SSet.Quasicategory.{u_1} C]
  (v :
    CategoryTheory.Functor.obj.{0, u_1 + 1, 0, u_1 + 2} (SerrePositivity.InfinityCategories.PresheafInfinity.{u_1} C)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.F2.Ind.IsIndVertex.{u_1} κ C v ↔
    SerrePositivity.InfinityCategories.F2.Ind.HasKappaFilteredElements.{u_1} κ v
```

</details>

<details>
<summary>CategoryTheory.Limits.PreservesFiniteLimits</summary>

```lean
@CategoryTheory.Limits.PreservesFiniteLimits.{u_1, u_2, u_3,
    u_4} : {C : Type u_3} →
  [inst : CategoryTheory.Category.{u_1, u_3} C] →
    {D : Type u_4} →
      [inst_1 : CategoryTheory.Category.{u_2, u_4} D] → CategoryTheory.Functor.{u_1, u_2, u_3, u_4} C D → Prop
```

</details>

<details>
<summary>CategoryTheory.LeftExactFunctor</summary>

```lean
CategoryTheory.LeftExactFunctor.{u_1, u_2, u_3,
  u_4} : (C : Type u_3) →
  [CategoryTheory.Category.{u_1, u_3} C] →
    (D : Type u_4) → [CategoryTheory.Category.{u_2, u_4} D] → Type (max (max (max u_3 u_4) u_1) u_2)
```

</details>

<details>
<summary>CategoryTheory.IsAccessibleCategory</summary>

```lean
CategoryTheory.IsAccessibleCategory.{u_1, u_2,
  u_3} : (C : Type u_3) → [hC : CategoryTheory.Category.{u_2, u_3} C] → Prop
```

</details>

<details>
<summary>CategoryTheory.IsCardinalAccessibleCategory</summary>

```lean
CategoryTheory.IsCardinalAccessibleCategory.{u_1, u_2,
  u_3} : (C : Type u_3) →
  [CategoryTheory.Category.{u_2, u_3} C] → (κ : Cardinal.{u_1}) → [Fact (Cardinal.IsRegular.{u_1} κ)] → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.isKappaAccessible_iff_indEquivalence</summary>

```lean
SerrePositivity.InfinityCategories.F2.Presentable.isKappaAccessible_iff_indEquivalence.{u_1} : ∀ (κ : Cardinal.{u_1})
  (C : SSet.{u_1 + 1}) [inst : SSet.Quasicategory.{u_1 + 1} C],
  SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible.{u_1} κ C ↔
    Cardinal.IsRegular.{u_1} κ ∧
      ∃ A,
        ∃ (hA : SSet.Quasicategory.{u_1} A),
          Nonempty.{u_1 + 2}
            (SerrePositivity.InfinityCategories.QCatEquivalence.{u_1 + 1}
              (SerrePositivity.InfinityCategories.F2.Ind.IndInfinity.{u_1} κ A) C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.exists_larger</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.exists_larger.{u_1} : ∀ {C : SSet.{u_1 + 1}}
  [inst : SSet.Quasicategory.{u_1 + 1} C],
  SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.{u_1} C →
    ∀ (σ : Cardinal.{u_1}),
      ∃ μ, LT.lt.{u_1 + 1} σ μ ∧ SerrePositivity.InfinityCategories.F2.Presentable.IsKappaAccessible.{u_1} μ C
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.rightAdjoint_isAccessible</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.rightAdjoint_isAccessible.{u_1} : ∀ {C D : SSet.{u_1 + 1}}
  [inst : SSet.Quasicategory.{u_1 + 1} C] [inst_1 : SSet.Quasicategory.{u_1 + 1} D],
  SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.{u_1} C →
    SerrePositivity.InfinityCategories.F2.Presentable.IsAccessible.{u_1} D →
      ∀ {L : Quiver.Hom.{u_1 + 1, u_1 + 2} C D} {R : Quiver.Hom.{u_1 + 1, u_1 + 2} D C}
        (a : SerrePositivity.InfinityCategories.QCatAdjunction.{u_1 + 1} L R),
        SerrePositivity.InfinityCategories.F2.Presentable.IsAccessibleFunctor.{u_1} R
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.adjunction_preservesSmallColimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.adjunction_preservesSmallColimits.{u_1} : ∀ {X Y : SSet.{u_1 + 1}}
  [inst : SSet.Quasicategory.{u_1 + 1} X] [inst_1 : SSet.Quasicategory.{u_1 + 1} Y]
  {L : Quiver.Hom.{u_1 + 1, u_1 + 2} X Y} {R : Quiver.Hom.{u_1 + 1, u_1 + 2} Y X}
  (a : SerrePositivity.InfinityCategories.QCatAdjunction.{u_1 + 1} L R),
  SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.{u_1} L
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.isAccessibleFunctor</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.isAccessibleFunctor.{u_1} : ∀
  {C E : SSet.{u_1 + 1}} {F : Quiver.Hom.{u_1 + 1, u_1 + 2} C E},
  SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.{u_1} F →
    SerrePositivity.InfinityCategories.F2.Presentable.IsAccessibleFunctor.{u_1} F
```

</details>

<details>
<summary>isLUB_sSup</summary>

```lean
@isLUB_sSup.{u_1} : ∀ {α : Type u_1} [inst : CompleteSemilatticeSup.{u_1} α] (s : Set.{u_1} α),
  IsLUB.{u_1} s (SupSet.sSup.{u_1} s)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable</summary>

```lean
SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} : (C : SSet.{u_1 + 1}) →
  [SSet.Quasicategory.{u_1 + 1} C] → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasSmallLimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasSmallLimits.{u_1} : ∀ {C : SSet.{u_1 + 1}}
  [inst : SSet.Quasicategory.{u_1 + 1} C],
  SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
    SerrePositivity.InfinityCategories.F2.Presentable.HasSmallLimits.{u_1} C
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasLimit</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.hasLimit.{u_1} : ∀ {C : SSet.{u_1 + 1}}
  [inst : SSet.Quasicategory.{u_1 + 1} C],
  SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
    ∀ {K : SSet.{u_1}}
      (D :
        Quiver.Hom.{u_1 + 1, u_1 + 2}
          (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} K) C),
      SerrePositivity.InfinityCategories.HasLimit.{u_1 + 1} D
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.exists_rightAdjoint_iff_preservesSmallColimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.exists_rightAdjoint_iff_preservesSmallColimits.{u_1} : ∀
  {C D : SSet.{u_1 + 1}} [inst : SSet.Quasicategory.{u_1 + 1} C] [inst_1 : SSet.Quasicategory.{u_1 + 1} D],
  SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
    SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} D →
      ∀ (L : Quiver.Hom.{u_1 + 1, u_1 + 2} C D),
        (∃ R, Nonempty.{u_1 + 2} (SerrePositivity.InfinityCategories.QCatAdjunction.{u_1 + 1} L R)) ↔
          SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.{u_1} L
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.exists_leftAdjoint_iff_accessible_preservesLimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.exists_leftAdjoint_iff_accessible_preservesLimits.{u_1} : ∀
  {C D : SSet.{u_1 + 1}} [inst : SSet.Quasicategory.{u_1 + 1} C] [inst_1 : SSet.Quasicategory.{u_1 + 1} D],
  SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
    SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} D →
      ∀ (R : Quiver.Hom.{u_1 + 1, u_1 + 2} D C),
        (∃ L, Nonempty.{u_1 + 2} (SerrePositivity.InfinityCategories.QCatAdjunction.{u_1 + 1} L R)) ↔
          SerrePositivity.InfinityCategories.F2.Presentable.IsAccessibleFunctor.{u_1} R ∧
            SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallLimits.{u_1} R
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfield_isReflectiveSubcategory</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfield_isReflectiveSubcategory.{u_1} : ∀
  {C : SSet.{u_1 + 1}} [inst : SSet.Quasicategory.{u_1 + 1} C],
  SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
    ∀ {I : Type u_1} (edges : I → CategoryTheory.Functor.obj.{0, u_1 + 1, 0, u_1 + 2} C (Opposite.op.{1} { len := 1 })),
      SerrePositivity.InfinityCategories.IsReflectiveSubcategory.{u_1 + 1} C
        (SerrePositivity.InfinityCategories.HomotopyLimits.IsLocalObject.{u_1 + 1} (Set.range.{u_1 + 1, u_1 + 1} edges))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfieldLocalizationFunctor</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.Localization.bousfieldLocalizationFunctor.{u_1} : {C :
    SSet.{u_1 + 1}} →
  [inst : SSet.Quasicategory.{u_1 + 1} C] →
    SerrePositivity.InfinityCategories.F2.Presentable.IsPresentable.{u_1} C →
      {I : Type u_1} →
        (edges : I → CategoryTheory.Functor.obj.{0, u_1 + 1, 0, u_1 + 2} C (Opposite.op.{1} { len := 1 })) →
          Quiver.Hom.{u_1 + 1, u_1 + 2} C
            (SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.Category.{u_1} edges)
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.IsWeakFactorizationSystem</summary>

```lean
@CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    CategoryTheory.MorphismProperty.{u_1, u_2} C → CategoryTheory.MorphismProperty.{u_1, u_2} C → Prop
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk'</summary>

```lean
@CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.mk'.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C]
  (W₁ W₂ : CategoryTheory.MorphismProperty.{u_1, u_2} C)
  [CategoryTheory.MorphismProperty.HasFactorization.{u_1, u_2} W₁ W₂]
  [CategoryTheory.MorphismProperty.IsStableUnderRetracts.{u_1, u_2} W₁]
  [CategoryTheory.MorphismProperty.IsStableUnderRetracts.{u_1, u_2} W₂],
  (∀ {A B X Y : C} (i : Quiver.Hom.{u_1, u_2} A B) (p : Quiver.Hom.{u_1, u_2} X Y),
      W₁ i → W₂ p → CategoryTheory.HasLiftingProperty.{u_1, u_2} i p) →
    CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.{u_1, u_2} W₁ W₂
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.hasLiftingProperty_of_wfs</summary>

```lean
@CategoryTheory.MorphismProperty.hasLiftingProperty_of_wfs.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C]
  {W₁ W₂ : CategoryTheory.MorphismProperty.{u_1, u_2} C}
  [CategoryTheory.MorphismProperty.IsWeakFactorizationSystem.{u_1, u_2} W₁ W₂] {A B X Y : C}
  (i : Quiver.Hom.{u_1, u_2} A B) (p : Quiver.Hom.{u_1, u_2} X Y),
  W₁ i → W₂ p → CategoryTheory.HasLiftingProperty.{u_1, u_2} i p
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.isLocalForHom_pushout_right_of_left</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.isLocalForHom_pushout_right_of_left.{u_1} : ∀ {X : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X]
  (R :
    Quiver.Hom.{u_1, u_1 + 1}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_1 + 1}
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 })
        (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 1 }))
      X),
  SerrePositivity.InfinityCategories.IsPushoutSquare.{u_1} R →
    ∀ (z : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })),
      SerrePositivity.InfinityCategories.HomotopyLimits.IsLocalForHom.{u_1}
          (SSet.Truncated.HomotopyCategory.homMk.{u_1}
            (SerrePositivity.InfinityCategories.HomotopyLimits.edgeCosliceEdge.{u_1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.squareLeftEdge.{u_1}
                R)))
          z →
        SerrePositivity.InfinityCategories.HomotopyLimits.IsLocalForHom.{u_1}
          (SSet.Truncated.HomotopyCategory.homMk.{u_1}
            (SerrePositivity.InfinityCategories.HomotopyLimits.edgeCosliceEdge.{u_1}
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
                SerrePositivity.InfinityCategories.squareRightEdge.{u_1} R)))
          z
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.IsStableUnderCobaseChange</summary>

```lean
@CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.MorphismProperty.{u_1, u_2} C → Prop
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.IsStableUnderRetracts</summary>

```lean
@CategoryTheory.MorphismProperty.IsStableUnderRetracts.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.MorphismProperty.{u_1, u_2} C → Prop
```

</details>

<details>
<summary>CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition</summary>

```lean
@CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.{u_1, u_2,
    u_3} : {C : Type u_3} →
  [inst : CategoryTheory.Category.{u_2, u_3} C] → CategoryTheory.MorphismProperty.{u_2, u_3} C → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.presheafDensity_image_isLeftKanExtension</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.presheafDensity_image_isLeftKanExtension.{u_1} : ∀ {C : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} C] {E : SSet.{u_1 + 2}} [SSet.Quasicategory.{u_1 + 2} E]
  (q :
    Quiver.Hom.{u_1 + 2, u_1 + 3}
      (CategoryTheory.Functor.obj.{u_1 + 1, u_1 + 2, u_1 + 2, u_1 + 3} SSet.uliftFunctor.{u_1 + 2, u_1 + 1}
        (SerrePositivity.InfinityCategories.PresheafInfinity.{u_1} C))
      E),
  (∀
      (F :
        Quiver.Hom.{u_1 + 1, u_1 + 2}
          (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1}
            (SSet.op.{u_1} C))
          SerrePositivity.InfinityCategories.SpaceInfinity.{u_1}),
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1 + 2}
        (SerrePositivity.InfinityCategories.mapJoinCocone.{u_1 + 2} q
          (SerrePositivity.InfinityCategories.JoinCocone.ulift.{u_1 + 1, u_1 + 2}
            (SerrePositivity.InfinityCategories.F2.Ind.presheafDensityCocone.{u_1} F)))) →
    SerrePositivity.InfinityCategories.IsLeftKanExtension.{u_1 + 2}
      (CategoryTheory.Functor.map.{u_1 + 1, u_1 + 2, u_1 + 2, u_1 + 3} SSet.uliftFunctor.{u_1 + 2, u_1 + 1}
        (SerrePositivity.InfinityCategories.yonedaInfinityMap.{u_1} C))
      (CategoryTheory.CategoryStruct.comp.{u_1 + 2, u_1 + 3}
        (CategoryTheory.Functor.map.{u_1 + 1, u_1 + 2, u_1 + 2, u_1 + 3} SSet.uliftFunctor.{u_1 + 2, u_1 + 1}
          (SerrePositivity.InfinityCategories.yonedaInfinityMap.{u_1} C))
        q)
      q
      (SerrePositivity.InfinityCategories.functorHomotopyRefl.{u_1 + 2}
        (CategoryTheory.CategoryStruct.comp.{u_1 + 2, u_1 + 3}
          (CategoryTheory.Functor.map.{u_1 + 1, u_1 + 2, u_1 + 2, u_1 + 3} SSet.uliftFunctor.{u_1 + 2, u_1 + 1}
            (SerrePositivity.InfinityCategories.yonedaInfinityMap.{u_1} C))
          q))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.smallSimplexOpposite_isSiftedInfinity</summary>

```lean
SerrePositivity.InfinityCategories.F2.Presentable.smallSimplexOpposite_isSiftedInfinity.{u_1} : SerrePositivity.InfinityCategories.HomotopyLimits.IsSiftedInfinity.{u_1}
  (CategoryTheory.nerve.{u_1, u_1} SerrePositivity.InfinityCategories.F2.Presentable.SmallSimplexOpposite.{u_1})
```

</details>
