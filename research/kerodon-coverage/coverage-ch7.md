# Kerodon Chapter 7（Limits and Colimits）のカバー状況

調査日 2026-11-06。main（7d5006ee7）を読んだだけで、ビルドはしていない。

- 対象：SerrePositivity/InfinityCategories（Core・F1・F1B・F2・HomotopyLimits・Stable・Derived）、HomotopicalAlgebra、Mathlib（.lake/packages/mathlib）。
- Kerodon 本文：49 の Subsection ページを取得した（`ch7/*.html`）。番号と Tag の対応表は `ch7/allitems.json`、宣言の索引は `ch7/decls.txt`。
- sorry：`InfinityCategories`・`KST`・`HomotopicalAlgebra` で `sorry` を grep した。証明本体にある sorry は `ModelBridge/Inputs/KanQuillen.lean:42`（Hovey 3.6.5 の引用）の 1 件だけ。これを import しているのは ModelBridge/Inputs の 2 ファイルだけなので、下の表に挙げた宣言はどれも sorry に依存していない。`[ModelCategory SSet]` を仮定に持つ宣言は ModelBridge/HA にしかなく、表の宣言には出てこない。
- Mathlib：∞ 圏版の第 7 章の内容はない。Mathlib にあるのは quasicategory・inner fibration・nerve の基礎だけで、join・slice・∞ 極限・∞ Kan 拡張はない。1 圏版の対応物（`Functor.Final`、`Functor.LeftExtension`、`IsPullback` の貼り合わせ、`HasLimitsOfShape`）は「備考」に書いた。したがって判定はすべて自前の実装による。
- 判定の基準：「あり」は主な定義と主要な定理が sorry なしで揃うもの、「一部」は定義だけか一部の定理だけのもの、「なし」は該当が見つからないもの。

## 表

| 番号 | Tag | 見出し | 判定 | 主な宣言（ファイル、`InfinityCategories/` 以下） | 備考 |
|---|---|---|---|---|---|
| 7.1.1 | 02VY | Limits and Colimits in ∞-Categories | あり | `HasLimit`・`limitVertexIso`（Core/Limit）、`isLimitCone_iff_mappingEvaluation_homotopyEquivalence`（HomotopyLimits/ConeSpanLimitCriterion） | 写像空間による定義（7.1.1.1）と slice の終対象による定義が同値であること、および一意性。「K 添字の極限を持つ」（7.1.1.15）は `HasSmallLimits`・`HasFiniteLimits` の形でだけある |
| 7.1.2 | 03EX | Constant Diagrams | 一部 | `constantDiagramCone_isLimit`（Derived/WeaklyContractibleConstantLimit）、`tensorSpaceFunctor`（F2/Tensor/Space） | 弱可縮な形の定数図式と、presentable な場合の空間とのテンソルだけ。冪の定義 7.1.2.1、7.1.2.8、dg 版 7.1.2.16 はない |
| 7.1.3 | 02JA | Limit and Colimit Diagrams | あり | `IsLimitCone`（Core/Limit、7.1.3.4 そのもの）、`isLimitCone_iff_trivialKanFibration`（Core/Limit）、`isLimitCone_iff_of_diagram_eq`（Core/EquivalenceAllLimits） | 7.1.3.17〜7.1.3.20 に相当するものもある。cube 版 7.1.3.15 はない |
| 7.1.4 | 02JV | Preservation of Limits and Colimits | あり | `IsQCatEquivalence.isLimitCone_iff`（Core/EquivalenceAllLimits）、`isLimitCone_of_conservative_image`（F2/Compact/ConservativeLimitReflection）、`mapJoinCocone_isColimit_of_adjunction`（F2/Presentable/LeftAdjointAllColimitPreservation） | 反射的部分圏（`reflectiveSubcategory_hasSmallLimits`）もある。保存の定義は `PreservesSmallLimits`・`PreservesSmallColimits` の形。「創る」（7.1.4.23）と切り詰め版 7.1.4.15/17 はない |
| 7.1.5 | 02WE | Relative Initial and Final Objects | あり | `KanRelativeInitialVertex`・`.comp`（F1B/KanExtension/RelativeColimit）、`kanRelativeInitialVertex_iff_initialBoundary`（F1B/KanExtension/RelativeInitialBoundaryCriterion）、`terminalBoundaryLifting_of_isTerminalVertex_fiber`（Core/CocartesianTerminalBoundary） | 7.1.5.10〜7.1.5.12、7.1.5.19、7.1.5.21。coreflective localization（7.1.5.13〜7.1.5.15）はない |
| 7.1.6 | 02KF | Relative Limits and Colimits | あり | `IsRelativeLimitCone`（F1B/KanExtension/RelativeLimit）、`IsRelativeColimitCone`（F1B/KanExtension/RelativeColimit）、`kanIsRelativeColimitCone_iff_family_relativeInitial`（F1B/KanExtension/RelativeColimitFamilyCriterion） | 7.1.6.1、7.1.6.13 型の判定、推移性 |
| 7.1.7 | 069P | Colimits Relative to a Fibration | 一部 | `kanRelativeCoconeLifting_iff_isRelativeColimitCone`（F1B/KanExtension/RelativeCoconeCriterion） | 持ち上げによる判定（7.1.7.1）だけ。left fibration が弱可縮な余極限を創ること（7.1.7.4/5）、edgewise 余極限（7.1.7.9 以降）、pullback 版（7.1.7.6/7）はない |
| 7.1.8 | 02X8 | Limits and Colimits in Diagram ∞-Categories | あり | `IsPointwiseLimitCone`（Core/FunctorLimits）、`exists_pointwiseLimitCone`（Core/FunctorPointwiseLimitExistence）、`isLimitCone_of_pointwise`（Core/FunctorPointwiseLimitCriterion） | 相対版 `kanIsRelativeColimitCone_functor_of_pointwise`（7.1.8.10）もある。Fubini（7.1.8.4/6）は見つからない |
| 7.1.9 | 06A8 | Colimits and Categorical Pullback Squares | あり | `exists_colimitCone_laxPullback_with_components`（F2/CatInfinity/LaxPullbackColimitConeExistence）、`isColimitCone_of_isPullback_of_components`（F2/CatInfinity/PullbackSquareCoconeCriterion） | oriented fiber product での判定と存在（06AD/06AE）、inner fibration に沿う引き戻し（06AH 相当）。塔の版 7.1.9.9 はない |
| 7.1.10 | 06AN | Colimits in ∞-Categories of Sections | なし | — | 切断 ∞ 圏の余極限を各 fiber で計算する定理（06AP）は見つからない |
| 7.2.1 | 02N0 | Cofinal Morphisms of Simplicial Sets | あり | `IsLeftCofinal`（F1B/Cofinality/Cofinality、7.2.1.1 そのもの）、`IsLeftCofinal.leftAnodyneExtensions`（F1B/Cofinality/CofinalAnodyneRecognition）、`IsLeftCofinal.comp`（F1B/Cofinality/CofinalComposition） | 7.2.1.3/5/6/14 もある。局所化との関係（7.2.1.10/11）は見ていない |
| 7.2.2 | 02NQ | Cofinality and Limits | あり | `isLimitCone_iff_restrict_of_leftCofinal`（Derived/CofinalLimitTransfer）、`hasLimit_of_leftCofinal`（F1B/Cofinality/LimitExistence）、`initialCofinality`（Core/InitialCofinality） | 7.2.2.1 の逆向き（極限の保存から cofinal を導く）は確認していない |
| 7.2.3 | 02NX | Quillen's Theorem A for ∞-Categories | あり | `isLeftCofinal_iff_weaklyContractible_slices`（F1B/Cofinality/QuillenALeft）、`isRightCofinal_iff_weaklyContractible_coslices`（F1B/Cofinality/QuillenA）、`leftFibration_pullback_isRightCofinal`（F1B/Cofinality/LeftFibrationCofinalPullback） | 7.2.3.1（Joyal）、7.2.3.10、7.2.3.12。Mathlib には 1 圏版（`Functor.Final` と comma 圏の連結性）がある |
| 7.3.1 | 02Y7 | Kan Extensions along General Functors | あり | `IsLeftKanExtension`・`IsRightKanExtension`（F1B/KanExtension/Definition）、`isLeftKanExtension_iff_of_homMk_eq`（F1B/KanExtension/LeftHomotopyInvariant） | 7.3.1.2/5/10。Mathlib には 1 圏版の Kan 拡張がある |
| 7.3.2 | 02YP | Kan Extensions along Inclusions | 一部 | `IsRelativeLeftKanExtendedFrom`（F1B/KanExtension/RelativeLeftCanonical） | 相対版を U と恒等でとれば包含に沿う場合になる。7.3.2.6・7.3.2.11 を名前のある定理として述べたものはない |
| 7.3.3 | 02Z2 | Relative Kan Extensions | あり | `IsRelativeLeftKanExtension`（F1B/KanExtension/RelativeLeftExtension）、`kanLeftTransport_isRelativeColimit_iff`（同ファイル） | 底変換（02ZG）・推移性（02ZE）の個別の定理は確認していない |
| 7.3.4 | 02ZL | Kan Extensions along Fibrations | あり | `RelativeJoin*` の一式（F1B/KanExtension/RelativeJoinDiagramAssembly ほか）、`kanRelativeJoinRestriction_preservesCartesianEdges`（F1B/KanExtension/RelativeJoinCartesianRestriction） | cocartesian fibration に沿う相対 join `K ⋆_C C` |
| 7.3.5 | 02ZZ | Existence of Kan Extensions | あり | `exists_kanRightExtension_iff_local_limits`（F1B/KanExtension/RightExistence）、`exists_kanLeftExtension_of_local_colimits`（F1B/KanExtension/LeftCommaCoconeColimit） | 0300 と、0302 の相対版 |
| 7.3.6 | 0308 | The Universal Property of Kan Extensions | あり | `kanLeftKanExtension_homUniversal`（F1B/KanExtension/LeftHomUniversal）、`kanRelativeLeftKanRestriction_trivialKanFibration`（F1B/KanExtension/RelativeLeftRestrictionTheorem） | 0309、Theorem 7.3.6.14（030R）の相対版、030M |
| 7.3.7 | 047V | Kan Extensions in Functor ∞-Categories | なし | — | exponentiable inner fibration を使う 7.3.7.1 は見つからない |
| 7.3.8 | 030U | Transitivity of Kan Extensions | なし | — | 0312 などの推移性と相対余極限の Fubini は見つからない |
| 7.3.9 | 031Q | Relative Colimits for Cocartesian Fibrations | なし | — | 06B2・031R・031W は見つからない |
| 7.4.1 | 05QM | Limits of Spaces | あり | `hasLimit_coherentSpaceDiagram`（F1/Coherent/SpaceSmallLimits）、`space_hasSmallLimits`（F2/Presentable/Definition）、`transportSectionsConeIsLimit`（HomotopyLimits/TransportSectionsLimit） | 7.4.1.6（切断空間が極限）に相当。`LeftTransportRepresentation.coneRestriction_iff`（Derived/LeftTransportConeRestriction）もある |
| 7.4.2 | 05R5 | Digression: Functoriality of Covariant Transport | 一部 | `LeftTransportRepresentation`（F1/Transport/…）、`essentiallySmallLeftTransportRepresentation_nonempty`（F1/Universe/EssentiallySmallWitnessContractible） | 表現の存在と整合性はある。関手性の定理 7.4.2.4 そのものは確認していない |
| 7.4.3 | 05RN | Colimits of Spaces | あり | `hasColimit_coherentSpaceDiagram`（F1/FilteredExchange/CoherentTotalColimit：全空間が余極限）、`space_hasSmallColimits`（F2/Presentable/Definition） | 02VE に相当。大きさの評価（05RR・05RW）は見ていない |
| 7.4.4 | 02T0 | Limits of ∞-Categories | 一部 | `qCatPullbackInfinityCone_isLimit`（F2/CatInfinity/QCatPullbackLimit） | QC での引き戻しだけ。cocartesian 切断を極限とする定理（05RX）と diffraction（02T8）はない。`cocartesianSectionCoreColimitCone_isLimit`（F1/Cocartesian、休止中の入口）は 1 圏的な極限 |
| 7.4.5 | 02UN | Colimits of ∞-Categories | なし | — | refraction（02UU）はない |
| 7.4.6 | 02V2 | Proof of the Refraction Criterion | なし | — | |
| 7.5.1 | 039Z | Homotopy Limits of Kan Complexes | あり | `bousfieldKanHolim`（HomotopyLimits/BousfieldKan）、`bousfieldKanHolim_kanComplex`（HomotopyLimits/SectionsKan） | 03A0・03A1。重み付き nerve による Bousfield–Kan 型の構成 |
| 7.5.2 | 03A7 | Homotopy Limits of ∞-Categories | 一部 | `bousfieldKanHolim`（任意の SSet 値図式で定義されている） | 定義だけ。QCat 値図式の holim が ∞ 圏であること（03AB）の instance は見つからない |
| 7.5.3 | 03AP | The Homotopy Limit as a Derived Functor | 一部 | `bousfieldKanLimitComparison_homotopyEquivalence_of_extensions`（HomotopyLimits/BousfieldKanComparison）、`bousfieldKanLimitComparison_{cospan,tower,discrete}_homotopyEquivalence` | 7.5.3.12（lim から holim への包含が同値）は延長の仮定の下と、cospan・塔・離散の形でだけある。isofibrant の一般の定義と置換（03AS/03AU）はない |
| 7.5.4 | 03B5 | Homotopy Limit Diagrams | あり | `strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison`（HomotopyLimits/WeightedConeRestriction）、`reflectedHomHolimConeComparison_homotopyEquivalence`（HomotopyLimits/GeneralHomHolimComparison） | 7.5.4.6（03BB、HTT 4.2.4.1）に相当：局所 Kan 単体圏での strict な錐が coherent nerve の極限であることを、Hom の holim の比較で特徴付ける |
| 7.5.5 | 03BL | Categorical Limit Diagrams | 一部 | `qCatPullbackInfinityCone_isLimit`（F2/CatInfinity/QCatPullbackLimit） | QCat の cospan の場合だけ。03BM・03BT の一般形はない |
| 7.5.6 | 03C3 | The Homotopy Colimit as a Derived Functor | 一部 | `homotopyColimit_comparison_weakEquivalence`（HomotopicalAlgebra/Diagram/PointwiseColimitComparison） | 一般の組合せモデル圏の射影モデルでの hocolim。Set_Δ・Kan に特化した 03C4〜03CG の形はない |
| 7.5.7 | 03CM | Homotopy Colimit Diagrams | 一部 | `strictCoherentCocone_isColimit_iff`（HomotopyLimits/StrictCocones） | 反対の錐の極限性に帰着する接続だけ。hocolim diagram の定義（03CQ）はない |
| 7.5.8 | 03CY | Categorical Colimit Diagrams | なし | — | |
| 7.6.1 | 03E9 | Products and Coproducts | 一部 | `spaceProductCone_isLimitCone`（HomotopyLimits/SpaceProducts）、`hasBinaryCoproduct_of_binaryColimit`（Stable/HomotopyBinaryCoproduct） | 𝒮 での積と安定圏の二項積・二項余積。一般の積の定義（03EC）と、極限を積で書き直す定理（03ES）はない |
| 7.6.2 | 03FE | Pullback and Pushout Squares | あり | `IsPullbackSquare`（Core/Pullback）、`IsPushoutSquare`（Core/PushoutShape）、`isPullbackSquare_pasting_iff`（Stable/PullbackPasting：任意の quasicategory） | 貼り合わせ（03FZ）と関手圏での点ごとの判定。05S7・04Q9 系はない。Mathlib には 1 圏版の `IsPullback` の貼り合わせがある |
| 7.6.3 | 03G3 | Examples of Pullback and Pushout Squares | あり | `spacePullbackCone_isLimitCone`（HomotopyLimits/SpacePullbacks）、`reflectedHomHolimConeComparison_cospan_homotopyEquivalence`（HomotopyLimits/ReflectedHomHolimComparison）、`qCatPullbackInfinityCone_isLimit` | 03G4（局所 Kan 単体圏の homotopy pullback）、03GA（QC） |
| 7.6.4 | 03GL | Equalizers and Coequalizers | なし | — | ∞ 圏のイコライザーの定義そのものがない |
| 7.6.5 | 03HG | Sequential Limits and Colimits | 一部 | `spaceTowerCone_isLimitCone`（HomotopyLimits/SpaceTowers）、`sequentialTelescopeFinalVertices_isRightCofinal`（F2/Presentable/Supply/SequentialTelescopeColimits） | Kan fibration の塔（03HU 相当）と telescope。一般の塔（03HV）と、イコライザーとして書く定理（03J0）はない |
| 7.6.6 | 03UC | Completeness and Cocompleteness | 一部 | `HasSmallLimits`・`HasSmallColimits`（F2/Presentable/Definition）、`hasFiniteLimits_of_terminal_pullbacks`（F1/Joins/FiniteLimitGeneration） | complete と finite complete はある。κ-complete（03UD）、𝕂-complete、𝕂-cocomplete fibration（05KC 以降）はない |
| 7.7.1 | 05SL | Cartesian Natural Transformations | なし | — | |
| 7.7.2 | 05TC | Descent Diagrams | なし | — | |
| 7.7.3 | 05UE | Cartesian Closed ∞-Categories | なし | — | |
| 7.7.4 | 05V6 | Disjoint Coproducts | なし | — | |
| 7.7.5 | 05VM | The Mather Cube Theorem Revisted | なし | — | |
| 7.7.6 | 05VZ | Descent in the ∞-Category of Spaces | なし | — | 近いのは F2/Ind の filtered right fibration の fiber の余極限（`strictRightFibrationColimitFiber_isPullback`）だけ |
| 7.7.7 | 05XG | Digression: Commutation of Limits and Colimits | 一部 | `smallSpaceFilteredColimit_map_isLimit_finite`（F2/Ind/FilteredColimitFiniteLimitPreservation） | 𝒮 で filtered 余極限が有限極限と交換すること（特別な場合）だけ。一般の定義 05XJ はない |

## 集計（49 Subsection）

| 節 | あり | 一部 | なし |
|---|---|---|---|
| 7.1（10） | 7 | 2 | 1 |
| 7.2（3） | 3 | 0 | 0 |
| 7.3（9） | 5 | 1 | 3 |
| 7.4（6） | 2 | 2 | 2 |
| 7.5（8） | 2 | 5 | 1 |
| 7.6（6） | 2 | 3 | 1 |
| 7.7（7） | 0 | 1 | 6 |
| 計 | 21 | 14 | 14 |

すべて自前の実装（SerrePositivity）による。Mathlib は 1 圏版の対応物を持つだけで、∞ 圏版で数えられるものは 0。

## 引用番号の照合（抜き取り）

Lean の引用 1,594 件（第 7 章の番号）と、Kerodon の現行版を照合した。

| 引用の番号（件数） | 現行版のその番号 | Lean 側（例） | 所見 |
|---|---|---|---|
| 7.5.4.6（553） | Cor 03BB：局所 Kan 単体圏で holim diagram であることと N^hc での極限であることの同値 | HomotopyLimits の多数のファイルの「使われ方」 | 内容は一致。ただし補助補題にも一律に付けている |
| 7.4.1.6（312） | Prop 05QS：Fun_/C(C,E) は Kan 複体で、covariant transport の極限 | HomotopyLimits/TransportSectionsLimit ほか | 一致 |
| 7.5.3.12（235） | Prop 03B1：isofibrant な図式で lim ↪ holim が同値 | HomotopyLimits/BousfieldKanComparison ほか | 一致。ただし Lean は特別な形の場合だけ |
| 7.5.1.1（19） | Construction 03A0：Kan 複体の holim | `bousfieldKanWeight`・`bousfieldKanHolim` | 一致 |
| 7.3（2） | 節 7.3 は Kan Extensions | Core/Pullback `IsPullbackSquare` | ずれている。正しくは Def 7.6.2.1（03FF） |
| 7.1.8.5（2） | Remark 06A3（Fubini の補足） | Core/FunctorPointwiseLimitCriterion `isLimitCone_of_pointwise` | ずれている。内容は Cor 7.1.8.15（02XP、levelwise 余極限は余極限）の双対 |
| 7.2.1.15（11） | Cor 02NE：left cofinal であることと、left anodyne と自明 Kan fibration への分解の同値 | F1B/Fibrations/LeftAnodyneFactorization `exists_leftAnodyne_leftFibration_factorization` | 内容がずれている。Lean は一般の left anodyne と left fibration への分解（小対象の論法） |
| 7.2.3.1（10） | Theorem 02NY（Joyal：Quillen A） | F1B/Homotopy/WeakHomotopy `IsWeaklyContractible`（定義） | 定義に定理の番号を付けている。軽いずれ |
| 7.3.1.4（3） | Warning 02YB（ホモトピー類で決まるという注意） | `LeftKanCoconeTransport.isColimitCone_iff` | Warning を定理として引いている。おおむね妥当 |
| 7.1.5（46） | 節番号だけ | Core/BoundaryPrismOpposite など組合せ論の補助 | 節単位の緩い引用 |

ほかに 7.1.5.19（02WU）、7.1.6.13（02XB）、7.1.8.7（06A5）、7.1.8.10（02XK）、7.2.1.3（02N3）、7.2.1.5（02N5）、7.2.1.14（02ND）、7.2.3.10（02P6）、7.2.3.12（03J8）、7.3.1.10（02YG）、7.3.4.5（02ZR）、7.3.6.1（0309）、7.3.6.7（030F）、7.3.6.9（030M）も照合し、いずれも内容は一致した。

- 多い番号（7.5.4.6・7.4.1.6・7.5.3.12）は現行版と一致している。古い版の番号だという疑いは当たらない。件数が多いのは、同じ番号を一律に貼っているため。
- 7.1.1〜7.1.4 は joined.md では引用 0 だが、実装は Core にある。引用が「Kerodon 7.1」（67 件）と節単位になっているために数えられていない。
