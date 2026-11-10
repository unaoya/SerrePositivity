# Ch 7 交差の抜き取り検査（§8.3）

- 検査日 2026-11-10。対象は -c を取り込んだ `0d9e86356` の表。作業枝に §8.3 を含む `abe0628ab` を取り込んだ。
- 乱数の種 `0x0d9e8635`。Python の `random.Random` を一つ使い、第7章から第10章まで章順に処理。番号を整数の組として昇順に並べた各プールから、完全対応、partial、none の順に `sample` で重複なく抽出した。上限は 20、10、10 件。
- 抽出後は対象番号と Kerodon 本文のみで独立判定を作成した。宣言は原対応表の名前候補、番号・小節の引用、概念名・双対・特殊化によるソース検索から探した。採用した宣言は共有ロック下で `#check` と `#print axioms` を確認した。
- -c の status を開く前の独立判定メモの SHA-256 は `4b4d4598986d08f04e588e63231285064e0a28f94c4792abeb77afc9d0ae72e2`。比較後の型の再点検で 7.2.2.3 に標的 B の準圏性があることを確認し、own から stronger-hyp の partial に訂正した。完全対応群の差は訂正前後で同じ。訂正後の SHA-256 は `72b1979726c8bf9bd4c6ba53f887da94b698568c91a5d673132e4892ec191307`。
- partial は原文の同じ主張を直接与える範囲に限り、§8.1 の四分類を付けた。探索で見つけた補題や別の比較射は、該当する結論を直接与えるかを区別した。

| 抽出群 | 母数 | 抽出 | 一致 | 差 | 差の割合 |
| --- | ---: | ---: | ---: | ---: | ---: |
| own・both・mathlib | 46 | 20 | 18 | 2 | 10.0% |
| partial | 299 | 10 | 3 | 7 | 70.0% |
| none | 174 | 10 | 10 | 0 | 0.0% |

完全対応の群の差は §8.3 の停止基準以下。

- own → none は 1 件。
- own → partial は 1 件。
- partial → none は 6 件。
- partial → own は 1 件。

## own・both・mathlib

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 採用宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [7.1.3.20](https://kerodon.net/tag/02K2) | own | own | — | 一致 | 準圏への同じ形状の二図式の FunctorIso を仮定し、極限と余極限の存在それぞれの iff を得る。 | [`SerrePositivity.InfinityCategories.hasLimit_iff_of_functorIso`](../../../../SerrePositivity/InfinityCategories/Core/LimitDiagramIso.lean#L39)、[`SerrePositivity.InfinityCategories.hasColimit_iff_of_functorIso`](../../../../SerrePositivity/InfinityCategories/Core/ColimitDiagramIso.lean#L56) |
| [7.1.4.12](https://kerodon.net/tag/02JZ) | own | own | — | 一致 | 準圏間の同値と任意の形状 K。写した錐・余錐でそれぞれ極限性・余極限性を保存し反映する。 | [`SerrePositivity.InfinityCategories.IsQCatEquivalence.isLimitCone_iff`](../../../../SerrePositivity/InfinityCategories/Core/EquivalenceAllLimits.lean#L60)、[`SerrePositivity.InfinityCategories.F2.Presentable.equivalence_isColimitCone_iff`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/EquivalenceColimits.lean#L24) |
| [7.1.4.28](https://kerodon.net/tag/02KE) | own | own | — | 一致 | 準圏間の随伴と任意の単体集合形状。右随伴で極限錐、左随伴で余極限錐を保存する。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.mapJoinCone_isLimit_of_adjunction`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/AdjunctionLimits.lean#L52)、[`SerrePositivity.InfinityCategories.F2.Presentable.mapJoinCocone_isColimit_of_adjunction`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/LeftAdjointAllColimitPreservation.lean#L27) |
| [7.1.5.21](https://kerodon.net/tag/02WV) | own | own | — | 一致 | 内ファイブレーションで相対始対象から頂点ファイバーの始対象を得る。cartesian fibration を加えると逆向きもある。 | [`SerrePositivity.InfinityCategories.InitialBoundaryLifting.isInitialVertex_fiber`](../../../../SerrePositivity/InfinityCategories/Core/RelativeInitialBoundary.lean#L68)、[`SerrePositivity.InfinityCategories.F1B.initialBoundaryLifting_of_isInitialVertex_fiber`](../../../../SerrePositivity/InfinityCategories/F1B/Fibrations/CartesianInitialBoundary.lean#L55) |
| [7.1.8.1](https://kerodon.net/tag/05QF) | own | own | — | 一致 | 内部 Hom への任意の余錐・錐を各頂点で評価し、余極限・極限であることを全頂点で要求する。 | [`SerrePositivity.KST.SConstruction.IsPointwiseColimitCone`](../../../../SerrePositivity/KST/SConstruction/FunctorPointwiseColimits.lean#L33)、[`SerrePositivity.InfinityCategories.IsPointwiseLimitCone`](../../../../SerrePositivity/InfinityCategories/Core/FunctorLimits.lean#L54) |
| [7.1.8.2](https://kerodon.net/tag/05QG) | own | own | — | 一致 | 準圏 C と任意の形状 K、B。各評価図式に余極限があれば Fun(B,C) の余極限が存在し、余錐が余極限である iff の一方向を頂点評価の保存に使える。 | [`SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits`](../../../../SerrePositivity/KST/SConstruction/FunctorPointwiseColimitExistence.lean#L74)、[`SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits`](../../../../SerrePositivity/KST/SConstruction/FunctorPointwiseColimitExistence.lean#L101) |
| [7.3.1.2](https://kerodon.net/tag/02Y9) | own | own | — | 一致 | δ、F₀、F と Fδ→F₀ の変換を入力し、各頂点で under と K の引き戻し上の誘導錐が極限となることを課す。 | [`SerrePositivity.InfinityCategories.IsRightKanExtension`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/Definition.lean#L144)、[`SerrePositivity.InfinityCategories.rightKanDiagram`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/Shapes.lean#L55) |
| [7.3.1.5](https://kerodon.net/tag/02YC) | own | own | — | 一致 | δ、F₀、F と F₀→Fδ の変換を入力し、各頂点で over と K の引き戻し上の誘導余錐が余極限となることを課す。 | [`SerrePositivity.InfinityCategories.IsLeftKanExtension`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/Definition.lean#L152)、[`SerrePositivity.InfinityCategories.leftKanDiagram`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/Shapes.lean#L62) |
| [7.3.1.10](https://kerodon.net/tag/02YG) | own | own | — | 一致 | 同じ両端でホモトピー圏の射の等しさを仮定して、左右の指定変換付き Kan 延長性それぞれの iff を得る。 | [`SerrePositivity.InfinityCategories.isLeftKanExtension_iff_of_homMk_eq`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/LeftHomotopyInvariant.lean#L152)、[`SerrePositivity.InfinityCategories.isRightKanExtension_iff_of_homMk_eq`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/RightHomotopyInvariant.lean#L97) |
| [7.3.2.8](https://kerodon.net/tag/02YW) | own | none | — | 差 | 存在条件同士の iff を探した。LeftCommaCoconeColimit は指定変換付き延長の存在と局所余極限、RelativeLeftCanonical は相対の標準局所条件と恒等変換を比較する。指定 F₀ から一般の β を恒等へ換える原文の存在比較は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.3.5.5](https://kerodon.net/tag/0302) | own | partial | direction | 差 | 充満忠実な内包含と同値持ち上げのもと、各頂点の指定された局所 U-余極限を仮定して、底上の厳密延長とその相対左 Kan 性を得る。原文の存在から局所条件を取り出す逆向きはここに含まれない。 | [`SerrePositivity.InfinityCategories.F1B.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits`](../../../../SerrePositivity/InfinityCategories/F1B/KanExtension/RelativeLeftCanonicalExistence.lean#L54) |
| [7.4.1.7](https://kerodon.net/tag/02VD) | own | own | — | 一致 | 任意の小さい形状 B の空間値図式で unstraightening 射影の単体的切断を頂点とする錐を構成し、同じ錐が極限となる。 | [`SerrePositivity.InfinityCategories.coherentDiagramSectionsCone`](../../../../SerrePositivity/InfinityCategories/F1/Coherent/DiagramSectionsCone.lean#L30)、[`SerrePositivity.InfinityCategories.coherentDiagramSectionsCone_isLimit`](../../../../SerrePositivity/InfinityCategories/F1/Coherent/SpaceSmallLimits.lean#L36) |
| [7.4.1.8](https://kerodon.net/tag/05QT) | own | own | — | 一致 | 左ファイブレーション上の空間値図式と、底を保つ pointed-space への比較を扱う。各頂点ファイバー上の比較に圏同値を課し、Kan ファイバー上のホモトピー同値の条件を表す。 | [`SerrePositivity.InfinityCategories.LeftTransportRepresentation`](../../../../SerrePositivity/InfinityCategories/F1/Transport/LeftTransportRepresentation.lean#L66)、[`SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap`](../../../../SerrePositivity/InfinityCategories/F1/Transport/LeftTransportRepresentation.lean#L78)、[`SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap_projection`](../../../../SerrePositivity/InfinityCategories/F1/Transport/LeftTransportRepresentation.lean#L87) |
| [7.5.1.1](https://kerodon.net/tag/03A0) | own | own | — | 一致 | 通常圏の Kan 値図式。Bousfield–Kan の重みの切断模型を weighted nerve 射影の単体的切断と標準同型で同定する。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanHolim`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/BousfieldKan.lean#L37)、[`SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanSectionsIso`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/BousfieldKanSectionsIso.lean#L90) |
| [7.5.4.5](https://kerodon.net/tag/03BA) | own | own | — | 一致 | 小圏の KanObject 値の錐を入力し、その coherent nerve の極限錐性と頂点から Bousfield–Kan 極限への標準比較の弱同値を iff で結ぶ。両端は Kan。 | [`SerrePositivity.InfinityCategories.F2.Presentable.kanCone_isLimit_iff_bousfieldKanComparison`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/KanConeComparisonCriterion.lean#L82) |
| [7.5.4.6](https://kerodon.net/tag/03BB) | own | own | — | 一致 | 小圏の局所 Kan 単体豊穣圏値の錐を入力し、coherent nerve の極限性と全対象で表現可能 Hom のホモトピー極限比較のホモトピー同値を iff で結ぶ。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/GeneralReflectedCriterion.lean#L26) |
| [7.6.5.9](https://kerodon.net/tag/03HS) | own | own | — | 一致 | ℕ はフィルター圏。単体集合で取った余極限の Kan 性と、その underlying 余極限錐を空間の余極限錐にする型がある。 | [`SerrePositivity.InfinityCategories.Kan.filteredColimit_kanComplex`](../../../../SerrePositivity/InfinityCategories/Kan/FilteredKanColimit.lean#L92)、[`SerrePositivity.InfinityCategories.F2.Ind.strictNativeCocone_isColimit_of_filtered_forget`](../../../../SerrePositivity/InfinityCategories/F2/Ind/FilteredKanCocone.lean#L21) |
| [7.6.5.11](https://kerodon.net/tag/03HU) | own | own | — | 一致 | 各遷移が Kan ファイブレーションの可算逆塔。台の厳密極限は Kan で、同じ錐の空間での極限性を与える。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerUnderlyingCone_kanComplex`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/SpaceTowers.lean#L37)、[`SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerCone_forget_isLimit`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/SpaceTowers.lean#L66)、[`SerrePositivity.InfinityCategories.HomotopyLimits.spaceTowerCone_isLimitCone`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/SpaceTowers.lean#L90) |
| [7.6.6.4](https://kerodon.net/tag/06BA) | own | own | — | 一致 | 小さい単体集合を宇宙埋め込みして全て量化し、準圏の関手での極限錐と余極限錐の保存をそれぞれ定義する。 | [`SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallLimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/EquivalenceSmallLimits.lean#L25)、[`SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/Definition.lean#L29) |
| [7.7.3.1](https://kerodon.net/tag/05UF) | mathlib | mathlib | — | 一致 | 通常圏の有限積から Cartesian monoidal 構造を取り、積との随伴の Hom 全単射で指数と評価を表す。全対象が Closed である MonoidalClosed が cartesian closed に対応する。 | `CategoryTheory.CartesianMonoidalCategory`（`Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean:98`）、`CategoryTheory.Closed`（`Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:39`）、`CategoryTheory.MonoidalClosed`（`Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:46`） |

## partial

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 採用宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [7.1.1.15](https://kerodon.net/tag/02JK) | partial | own | — | 差 | 任意の単体集合 K と K→C。各図式の JoinCone／JoinCocone とその極限／余極限性を存在量化する。図式をすべて量化すると原文の固定形状の定義になる。 | [`SerrePositivity.InfinityCategories.HasLimit`](../../../../SerrePositivity/InfinityCategories/Core/Limit.lean#L53)、[`SerrePositivity.InfinityCategories.HasColimit`](../../../../SerrePositivity/InfinityCategories/Core/Cocone.lean#L44) |
| [7.1.8.5](https://kerodon.net/tag/06A3) | partial | partial | special | 一致 | 通常圏の図式で積添字の余極限と両順序の反復余極限が同型。任意の ∞ 圏は対象外。 | `CategoryTheory.Limits.colimitIsoColimitCurryCompColim`（`Mathlib/CategoryTheory/Limits/Fubini.lean:636`）、`CategoryTheory.Limits.colimitCurrySwapCompColimIsoColimitCurryCompColim`（`Mathlib/CategoryTheory/Limits/Fubini.lean:707`） |
| [7.2.2.3](https://kerodon.net/tag/02XR) | partial | partial | stronger-hyp | 一致 | 左共終な単体集合射に沿う錐の制限の前後で IsLimitCone の iff を与える。型は射の標的 B に Quasicategory を要求し、原文は任意の単体集合 B。 | [`SerrePositivity.InfinityCategories.isLimitCone_iff_restrict_of_leftCofinal`](../../../../SerrePositivity/InfinityCategories/Derived/CofinalLimitTransfer.lean#L15) |
| [7.2.2.5](https://kerodon.net/tag/02XV) | partial | none | — | 差 | 終対象／始対象への一点制限と、脚の cocartesian／cartesian 性を直接結ぶ型を探索。RelativeColimitTerminalIndex は制限した余錐の相対余極限性で止まり、脚の性質を結論にしない。 番号の直接引用 0 件、同じ小節の引用 5 件。 | — |
| [7.3.8.14](https://kerodon.net/tag/0314) | partial | none | — | 差 | 二段の充満包含について、延長の推移性と制限からの逆判定を探索。LeftCommaCoconeColimit の iff は一つの包含の局所余極限を試す。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.4.1.19](https://kerodon.net/tag/06MH) | partial | partial | stronger-hyp | 一致 | 底で極限となる錐に対し、その持ち上げの全延長空間が可縮と仮定すると同じ錐が全空間で極限。原文の空間値輸送が極限という条件と持ち上げ条件の iff は未確認。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.isLimitCone_of_leftFibration_extension`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/LeftFibrationConeLimit.lean#L26) |
| [7.4.1.20](https://kerodon.net/tag/06MK) | partial | none | — | 差 | 任意の持ち上げの極限存在・保存と輸送が元の図式の極限を保つことの iff を探索。LeftTransportConeRestriction は制限射の同値の比較、LeftFibrationConeLimit は既に選んだ錐についての判定。 番号の直接引用 0 件、同じ小節の引用 312 件。 | — |
| [7.4.6.3](https://kerodon.net/tag/02V7) | partial | none | — | 差 | inner anodyne に沿う cocartesian fibration の引き戻しでは全空間間の前合成同値を確認。cocartesian 辺だけを反転した二つの局所化の間の比較の同値を述べる型は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.5.7.6](https://kerodon.net/tag/03CT) | partial | none | — | 差 | 任意の単体集合値余錐を全 Kan 複体への指数図式で判定する iff を探索。GeneralReflectedCriterion は局所 Kan 豊穣圏の native 余極限性を述べ、単体集合値のホモトピー余極限述語の iff とは対象が異なる。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.5.7.7](https://kerodon.net/tag/03CU) | partial | none | — | 差 | Kan 値余錐のホモトピー余極限性と空間の coherent nerve の余極限性の iff を探索。GeneralReflectedCriterion は表現可能 Hom の比較を使い、原文の余極限 augmentation の弱同値との両向きの橋を含まない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## none

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 採用宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [7.1.2.8](https://kerodon.net/tag/03F6) | none | none | — | 一致 | locally Kan な豊穣 Hom と hc nerve の比較はあるが、一般の K からの e が tensor／cotensor を表示することと、全 Z に対する Hom の試験を結ぶ型は見つからなかった。WeightedCotensor の同型は重み付き切断の計算。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.1.7.5](https://kerodon.net/tag/02KT) | none | none | — | 一致 | 弱可縮 K を仮定したときの左ファイブレーションによる余極限の存在・保存と右側の双対を探索。LeftFibrationConeLimit は左ファイブレーションで全延長空間の可縮性を仮定する極限の結果。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.2.3.5](https://kerodon.net/tag/02XX) | none | none | — | 一致 | 弱可縮形状で全辺を可逆に送る錐と極限錐の iff を探索。IdentityCocone の一点定値の型と InitialTerminalWeakContractibility の形状自体の可縮性は、この条件付きの iff を与えない。 番号の直接引用 0 件、同じ小節の引用 19 件。 | — |
| [7.3.7.5](https://kerodon.net/tag/0480) | none | none | — | 一致 | 積上の左 Kan 延長を curry した関手圏値の左 Kan 延長に移す型を探索。RelativeColimitPointwise は既に同じ形状で得られる相対余錐の点ごとの判定で、積包含の局所添字を比較しない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.3.8.22](https://kerodon.net/tag/031F) | none | none | — | 一致 | 中間部分圏への相対左 Kan 延長が指定されたままの延長を探索。RelativeLeftCanonicalExistence の出力は一つの包含の延長で、指定された中間段階への制限の一致がない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.4.5.18](https://kerodon.net/tag/02UX) | none | none | — | 一致 | 右錐への cocartesian fibration の延長と先端ファイバーへの refraction が局所化になる組を探索。MarkedCocartesian 系の切断の余極限・マークの保存は先端ファイバーへの局所化を与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.4.5.23](https://kerodon.net/tag/03U8) | none | none | — | 一致 | QC の κ-small 対象の充満部分圏の κ-small 余極限と宇宙間の保存を探索。space_hasSmallColimits は空間の ∞ 圏で、準圏の濃度部分圏ではない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.5.8.7](https://kerodon.net/tag/03D6) | none | none | — | 一致 | projective cofibrancy を仮定する単体集合の余極限から categorical colimit への移送を探索。FilteredKanCocone は Kan 値フィルター図式を空間へ移す型で、任意の単体集合値余錐の categorical 判定がない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.6.2.38](https://kerodon.net/tag/048E) | none | none | — | 一致 | 相対引き戻し／押し出しと四角形内の二辺の cartesian／cocartesian 性の iff を探索。FinalHornPullbackExtension は底変換の厳密な引き戻しで辺を持ち上げ、元の四角形の相対普遍性を判定しない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [7.7.1.20](https://kerodon.net/tag/05T9) | none | none | — | 一致 | 全 K 余極限の普遍性の二条件を探索。Mathlib の IsUniversalColimit は一つの通常圏の余錐を扱い、任意の ∞ 圏での形状全体の iff は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## kernel の確認

<details>
<summary>SerrePositivity.InfinityCategories.HasLimit</summary>

```lean
@SerrePositivity.InfinityCategories.HasLimit.{u_1} : {K X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} K X → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HasColimit</summary>

```lean
@SerrePositivity.InfinityCategories.HasColimit.{u_1} : {K X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} K X → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.hasLimit_iff_of_functorIso</summary>

```lean
@SerrePositivity.InfinityCategories.hasLimit_iff_of_functorIso.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X]
  {p q : Quiver.Hom.{u_1, u_1 + 1} K X} (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} p q),
  SerrePositivity.InfinityCategories.HasLimit.{u_1} p ↔ SerrePositivity.InfinityCategories.HasLimit.{u_1} q
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.hasColimit_iff_of_functorIso</summary>

```lean
@SerrePositivity.InfinityCategories.hasColimit_iff_of_functorIso.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p q : Quiver.Hom.{u_1, u_1 + 1} K X}
  (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} p q),
  SerrePositivity.InfinityCategories.HasColimit.{u_1} p ↔ SerrePositivity.InfinityCategories.HasColimit.{u_1} q
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.IsQCatEquivalence.isLimitCone_iff</summary>

```lean
@SerrePositivity.InfinityCategories.IsQCatEquivalence.isLimitCone_iff.{u_1} : ∀ {K X Y : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] {f : Quiver.Hom.{u_1, u_1 + 1} X Y},
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} f →
    ∀ {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
      SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c ↔
        SerrePositivity.InfinityCategories.IsLimitCone.{u_1} (SerrePositivity.InfinityCategories.mapJoinCone.{u_1} f c)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.equivalence_isColimitCone_iff</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.equivalence_isColimitCone_iff.{u_1} : ∀ {K C E : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} C] [inst_1 : SSet.Quasicategory.{u_1} E] {G : Quiver.Hom.{u_1, u_1 + 1} C E},
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} G →
    ∀ {D : Quiver.Hom.{u_1, u_1 + 1} K C} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} D),
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
        SerrePositivity.InfinityCategories.IsColimitCone.{u_1}
          (SerrePositivity.InfinityCategories.mapJoinCocone.{u_1} G c)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.mapJoinCone_isLimit_of_adjunction</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.mapJoinCone_isLimit_of_adjunction.{u_1} : ∀ {K X Y : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] {F : Quiver.Hom.{u_1, u_1 + 1} X Y}
  {G : Quiver.Hom.{u_1, u_1 + 1} Y X} (a : SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G)
  {p : Quiver.Hom.{u_1, u_1 + 1} K Y} (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} p),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.IsLimitCone.{u_1} (SerrePositivity.InfinityCategories.mapJoinCone.{u_1} G c)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.mapJoinCocone_isColimit_of_adjunction</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.mapJoinCocone_isColimit_of_adjunction.{u_1} : ∀ {K X Y : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] {F : Quiver.Hom.{u_1, u_1 + 1} X Y}
  {G : Quiver.Hom.{u_1, u_1 + 1} Y X} (a : SerrePositivity.InfinityCategories.QCatAdjunction.{u_1} F G)
  {p : Quiver.Hom.{u_1, u_1 + 1} K X} (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.IsColimitCone.{u_1} (SerrePositivity.InfinityCategories.mapJoinCocone.{u_1} F c)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.InitialBoundaryLifting.isInitialVertex_fiber</summary>

```lean
@SerrePositivity.InfinityCategories.InitialBoundaryLifting.isInitialVertex_fiber.{u_1} : ∀ {E B : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 }))
  (x :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} p ↑x →
    SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F1B.initialBoundaryLifting_of_isInitialVertex_fiber</summary>

```lean
@SerrePositivity.InfinityCategories.F1B.initialBoundaryLifting_of_isInitialVertex_fiber.{u_1} : ∀ {E B : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} E] [SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  [SerrePositivity.InfinityCategories.CartesianFibration.{u_1} p]
  (b : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} B (Opposite.op.{1} { len := 0 }))
  (x :
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.vertexFiber.{u_1} p b)
      (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x →
    SerrePositivity.InfinityCategories.InitialBoundaryLifting.{u_1} p ↑x
```

</details>

<details>
<summary>SerrePositivity.KST.SConstruction.IsPointwiseColimitCone</summary>

```lean
@SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.{u_1} : {J K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} J (K ⟹ X)} → SerrePositivity.InfinityCategories.JoinCocone.{u_1} p → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.IsPointwiseLimitCone</summary>

```lean
@SerrePositivity.InfinityCategories.IsPointwiseLimitCone.{u_1} : {J K X : SSet.{u_1}} →
  {p : Quiver.Hom.{u_1, u_1 + 1} J (K ⟹ X)} → SerrePositivity.InfinityCategories.JoinCone.{u_1} p → Prop
```

</details>

<details>
<summary>SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits</summary>

```lean
@SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits.{u_1} : ∀ {J K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} J (K ⟹ X)),
  SerrePositivity.KST.SConstruction.HasPointwiseColimits.{u_1} p → SerrePositivity.InfinityCategories.HasColimit.{u_1} p
```

</details>

<details>
<summary>SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits</summary>

```lean
@SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits.{u_1} : ∀ {J K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p : Quiver.Hom.{u_1, u_1 + 1} J (K ⟹ X)},
  SerrePositivity.KST.SConstruction.HasPointwiseColimits.{u_1} p →
    ∀ (c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p),
      SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c ↔
        SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.{u_1} c
```

</details>

<details>
<summary>CategoryTheory.Limits.colimitIsoColimitCurryCompColim</summary>

```lean
@CategoryTheory.Limits.colimitIsoColimitCurryCompColim.{u_1, u_2, u_3, u_4, u_5,
    u_6} : {J : Type u_2} →
  {K : Type u_4} →
    [inst : CategoryTheory.Category.{u_1, u_2} J] →
      [inst_1 : CategoryTheory.Category.{u_3, u_4} K] →
        {C : Type u_6} →
          [inst_2 : CategoryTheory.Category.{u_5, u_6} C] →
            (G : CategoryTheory.Functor.{max u_1 u_3, u_5, max u_4 u_2, u_6} (Prod.{u_2, u_4} J K) C) →
              [inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u_3, u_4, u_5, u_6} K C] →
                [inst_4 :
                    CategoryTheory.Limits.HasColimit.{u_1, u_2, u_5, u_6}
                      (CategoryTheory.Functor.comp.{u_1, max u_4 u_5, u_5, u_2, max (max (max u_6 u_4) u_5) u_3, u_6}
                        (CategoryTheory.Functor.obj.{max (max u_4 u_2) u_5, max (max u_4 u_2) u_5,
                            max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1,
                            max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1}
                          CategoryTheory.Functor.curry.{u_1, u_3, u_5, u_2, u_4, u_6} G)
                        CategoryTheory.Limits.colim.{u_3, u_4, u_5, u_6})] →
                  CategoryTheory.Iso.{u_5, u_6} (CategoryTheory.Limits.colimit.{max u_1 u_3, max u_2 u_4, u_5, u_6} G)
                    (CategoryTheory.Limits.colimit.{u_1, u_2, u_5, u_6}
                      (CategoryTheory.Functor.comp.{u_1, max u_4 u_5, u_5, u_2, max (max (max u_6 u_4) u_5) u_3, u_6}
                        (CategoryTheory.Functor.obj.{max (max u_4 u_2) u_5, max (max u_4 u_2) u_5,
                            max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1,
                            max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1}
                          CategoryTheory.Functor.curry.{u_1, u_3, u_5, u_2, u_4, u_6} G)
                        CategoryTheory.Limits.colim.{u_3, u_4, u_5, u_6}))
```

</details>

<details>
<summary>CategoryTheory.Limits.colimitCurrySwapCompColimIsoColimitCurryCompColim</summary>

```lean
@CategoryTheory.Limits.colimitCurrySwapCompColimIsoColimitCurryCompColim.{u_1, u_2, u_3, u_4, u_5,
    u_6} : {J : Type u_2} →
  {K : Type u_4} →
    [inst : CategoryTheory.Category.{u_1, u_2} J] →
      [inst_1 : CategoryTheory.Category.{u_3, u_4} K] →
        {C : Type u_6} →
          [inst_2 : CategoryTheory.Category.{u_5, u_6} C] →
            (G : CategoryTheory.Functor.{max u_1 u_3, u_5, max u_4 u_2, u_6} (Prod.{u_2, u_4} J K) C) →
              [inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u_3, u_4, u_5, u_6} K C] →
                [inst_4 : CategoryTheory.Limits.HasColimitsOfShape.{u_1, u_2, u_5, u_6} J C] →
                  [inst_5 :
                      CategoryTheory.Limits.HasColimit.{u_1, u_2, u_5, u_6}
                        (CategoryTheory.Functor.comp.{u_1, max u_4 u_5, u_5, u_2, max (max (max u_6 u_4) u_5) u_3, u_6}
                          (CategoryTheory.Functor.obj.{max (max u_4 u_2) u_5, max (max u_4 u_2) u_5,
                              max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1,
                              max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1}
                            CategoryTheory.Functor.curry.{u_1, u_3, u_5, u_2, u_4, u_6} G)
                          CategoryTheory.Limits.colim.{u_3, u_4, u_5, u_6})] →
                    CategoryTheory.Iso.{u_5, u_6}
                      (CategoryTheory.Limits.colimit.{u_3, u_4, u_5, u_6}
                        (CategoryTheory.Functor.comp.{u_3, max u_2 u_5, u_5, u_4, max (max (max u_6 u_2) u_5) u_1, u_6}
                          (CategoryTheory.Functor.obj.{max (max u_2 u_4) u_5, max (max u_2 u_4) u_5,
                              max (max (max (max (max u_6 u_2) u_4) u_5) u_1) u_3,
                              max (max (max (max (max u_6 u_2) u_4) u_5) u_1) u_3}
                            CategoryTheory.Functor.curry.{u_3, u_1, u_5, u_4, u_2, u_6}
                            (CategoryTheory.Functor.comp.{max u_1 u_3, max u_1 u_3, u_5, max u_2 u_4, max u_2 u_4, u_6}
                              (CategoryTheory.Prod.swap.{u_3, u_1, u_4, u_2} K J) G))
                          CategoryTheory.Limits.colim.{u_1, u_2, u_5, u_6}))
                      (CategoryTheory.Limits.colimit.{u_1, u_2, u_5, u_6}
                        (CategoryTheory.Functor.comp.{u_1, max u_4 u_5, u_5, u_2, max (max (max u_6 u_4) u_5) u_3, u_6}
                          (CategoryTheory.Functor.obj.{max (max u_4 u_2) u_5, max (max u_4 u_2) u_5,
                              max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1,
                              max (max (max (max (max u_6 u_4) u_2) u_5) u_3) u_1}
                            CategoryTheory.Functor.curry.{u_1, u_3, u_5, u_2, u_4, u_6} G)
                          CategoryTheory.Limits.colim.{u_3, u_4, u_5, u_6}))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.isLimitCone_iff_restrict_of_leftCofinal</summary>

```lean
@SerrePositivity.InfinityCategories.isLimitCone_iff_restrict_of_leftCofinal.{u_1} : ∀ {A B X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} B] [SSet.Quasicategory.{u_1} X] (u : Quiver.Hom.{u_1, u_1 + 1} A B),
  SerrePositivity.InfinityCategories.IsLeftCofinal.{u_1} u →
    ∀ (F : Quiver.Hom.{u_1, u_1 + 1} B X) (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} F),
      SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c ↔
        SerrePositivity.InfinityCategories.IsLimitCone.{u_1}
          (SerrePositivity.InfinityCategories.restrictJoinCone.{u_1} c u)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.IsRightKanExtension</summary>

```lean
@SerrePositivity.InfinityCategories.IsRightKanExtension.{u_1} : {K C D : SSet.{u_1}} →
  (δ : Quiver.Hom.{u_1, u_1 + 1} K C) →
    (F₀ : Quiver.Hom.{u_1, u_1 + 1} K D) →
      (F : Quiver.Hom.{u_1, u_1 + 1} C D) →
        SSet.Homotopy.{u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ F) F₀ → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.rightKanDiagram</summary>

```lean
@SerrePositivity.InfinityCategories.rightKanDiagram.{u_1} : {K C D : SSet.{u_1}} →
  (δ : Quiver.Hom.{u_1, u_1 + 1} K C) →
    Quiver.Hom.{u_1, u_1 + 1} K D →
      (c : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := 0 })) →
        Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.rightKanShape.{u_1} δ c) D
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.IsLeftKanExtension</summary>

```lean
@SerrePositivity.InfinityCategories.IsLeftKanExtension.{u_1} : {K C D : SSet.{u_1}} →
  (δ : Quiver.Hom.{u_1, u_1 + 1} K C) →
    (F₀ : Quiver.Hom.{u_1, u_1 + 1} K D) →
      (F : Quiver.Hom.{u_1, u_1 + 1} C D) →
        SSet.Homotopy.{u_1} F₀ (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ F) → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.leftKanDiagram</summary>

```lean
@SerrePositivity.InfinityCategories.leftKanDiagram.{u_1} : {K C D : SSet.{u_1}} →
  (δ : Quiver.Hom.{u_1, u_1 + 1} K C) →
    Quiver.Hom.{u_1, u_1 + 1} K D →
      (c : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := 0 })) →
        Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.leftKanShape.{u_1} δ c) D
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.isLeftKanExtension_iff_of_homMk_eq</summary>

```lean
@SerrePositivity.InfinityCategories.isLeftKanExtension_iff_of_homMk_eq.{u_1} : ∀ {K C D : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} D] (δ : Quiver.Hom.{u_1, u_1 + 1} K C) (F₀ : Quiver.Hom.{u_1, u_1 + 1} K D)
  (F : Quiver.Hom.{u_1, u_1 + 1} C D)
  (α β : SSet.Homotopy.{u_1} F₀ (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ F)),
  Eq.{u_1 + 1}
      (SSet.Truncated.HomotopyCategory.homMk.{u_1}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u_1} α))
      (SSet.Truncated.HomotopyCategory.homMk.{u_1}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u_1} β)) →
    (SerrePositivity.InfinityCategories.IsLeftKanExtension.{u_1} δ F₀ F α ↔
      SerrePositivity.InfinityCategories.IsLeftKanExtension.{u_1} δ F₀ F β)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.isRightKanExtension_iff_of_homMk_eq</summary>

```lean
@SerrePositivity.InfinityCategories.isRightKanExtension_iff_of_homMk_eq.{u_1} : ∀ {K C D : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} D] (δ : Quiver.Hom.{u_1, u_1 + 1} K C) (F₀ : Quiver.Hom.{u_1, u_1 + 1} K D)
  (F : Quiver.Hom.{u_1, u_1 + 1} C D)
  (α β : SSet.Homotopy.{u_1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ F) F₀),
  Eq.{u_1 + 1}
      (SSet.Truncated.HomotopyCategory.homMk.{u_1}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u_1} α))
      (SSet.Truncated.HomotopyCategory.homMk.{u_1}
        (SerrePositivity.InfinityCategories.functorEdgeOfSimplicialHomotopy.{u_1} β)) →
    (SerrePositivity.InfinityCategories.IsRightKanExtension.{u_1} δ F₀ F α ↔
      SerrePositivity.InfinityCategories.IsRightKanExtension.{u_1} δ F₀ F β)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F1B.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits</summary>

```lean
@SerrePositivity.InfinityCategories.F1B.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits.{u_1} : ∀
  {K C D E : SSet.{u_1}} [SSet.Quasicategory.{u_1} K] [SSet.Quasicategory.{u_1} C] [SSet.Quasicategory.{u_1} D]
  [SSet.Quasicategory.{u_1} E] (U : Quiver.Hom.{u_1, u_1 + 1} D E),
  SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.{u_1} U →
    ∀ (δ : Quiver.Hom.{u_1, u_1 + 1} K C) [CategoryTheory.Mono.{u_1, u_1 + 1} δ] [SSet.InnerFibration.{u_1} δ],
      SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1} δ →
        ∀ (F₀ : Quiver.Hom.{u_1, u_1 + 1} K D) (H₀ : Quiver.Hom.{u_1, u_1 + 1} C E),
          Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} F₀ U)
              (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ H₀) →
            (∀ (c : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := 0 })),
                ∃ z,
                  SerrePositivity.InfinityCategories.F1B.IsRelativeColimitCone.{u_1} U z ∧
                    Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (↑z) U)
                      ↑(SerrePositivity.InfinityCategories.leftKanCanonicalCocone.{u_1} δ H₀ c)) →
              ∃ G,
                Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} δ G) F₀ ∧
                  Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} G U) H₀ ∧
                    SerrePositivity.InfinityCategories.F1B.IsRelativeLeftKanExtendedFrom.{u_1} U δ G
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.coherentDiagramSectionsCone</summary>

```lean
@SerrePositivity.InfinityCategories.coherentDiagramSectionsCone.{u_1} : {B : SSet.{u_1}} →
  (F :
      Quiver.Hom.{u_1 + 1, u_1 + 2}
        (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} B)
        SerrePositivity.InfinityCategories.SpaceInfinity.{u_1}) →
    SerrePositivity.InfinityCategories.JoinCone.{u_1 + 1} F
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.coherentDiagramSectionsCone_isLimit</summary>

```lean
@SerrePositivity.InfinityCategories.coherentDiagramSectionsCone_isLimit.{u_1} : ∀ {B : SSet.{u_1}}
  (F :
    Quiver.Hom.{u_1 + 1, u_1 + 2}
      (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} B)
      SerrePositivity.InfinityCategories.SpaceInfinity.{u_1}),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1 + 1}
    (SerrePositivity.InfinityCategories.coherentDiagramSectionsCone.{u_1} F)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.LeftTransportRepresentation</summary>

```lean
@SerrePositivity.InfinityCategories.LeftTransportRepresentation.{u_1} : {E B : SSet.{u_1 + 1}} →
  (p : Quiver.Hom.{u_1 + 1, u_1 + 2} E B) →
    [SerrePositivity.InfinityCategories.LeftFibration.{u_1 + 1} p] → Type (u_1 + 1)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap</summary>

```lean
@SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap.{u_1} : {E B : SSet.{u_1 + 1}} →
  {p : Quiver.Hom.{u_1 + 1, u_1 + 2} E B} →
    [inst : SerrePositivity.InfinityCategories.LeftFibration.{u_1 + 1} p] →
      SerrePositivity.InfinityCategories.LeftTransportRepresentation.{u_1} p →
        Quiver.Hom.{u_1 + 1, u_1 + 2} E SerrePositivity.InfinityCategories.PointedSpaceInfinity.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap_projection</summary>

```lean
@SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap_projection.{u_1} : ∀ {E B : SSet.{u_1 + 1}}
  {p : Quiver.Hom.{u_1 + 1, u_1 + 2} E B} [inst : SerrePositivity.InfinityCategories.LeftFibration.{u_1 + 1} p]
  (R : SerrePositivity.InfinityCategories.LeftTransportRepresentation.{u_1} p),
  Eq.{u_1 + 2}
    (CategoryTheory.CategoryStruct.comp.{u_1 + 1, u_1 + 2}
      (SerrePositivity.InfinityCategories.LeftTransportRepresentation.pointedMap.{u_1} R)
      SerrePositivity.InfinityCategories.pointedSpaceProjection.{u_1})
    (CategoryTheory.CategoryStruct.comp.{u_1 + 1, u_1 + 2} p
      (SerrePositivity.InfinityCategories.LeftTransportRepresentation.diagram.{u_1} R))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.isLimitCone_of_leftFibration_extension</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.isLimitCone_of_leftFibration_extension.{u_1} : ∀ {K E B : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} E B)
  [SerrePositivity.InfinityCategories.LeftFibration.{u_1} p] {d : Quiver.Hom.{u_1, u_1 + 1} K E}
  (a : SerrePositivity.InfinityCategories.JoinCone.{u_1} d),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1} (SerrePositivity.InfinityCategories.mapJoinCone.{u_1} p a) →
    SerrePositivity.InfinityCategories.IsContractibleKan.{u_1}
        (SerrePositivity.InfinityCategories.relativeFunctorExtensionSpace.{u_1} p
          (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (↑a) p)
          (SerrePositivity.InfinityCategories.joinInr.{u_1}
            (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 0 }) K)
          d ⋯) →
      SerrePositivity.InfinityCategories.IsLimitCone.{u_1} a
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanHolim</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanHolim.{u_1} : {I : Type u_1} →
  [inst : CategoryTheory.SmallCategory.{u_1} I] →
    CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} I SSet.{u_1} → SSet.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanSectionsIso</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanSectionsIso.{u_1} : {I : Type u_1} →
  [inst : CategoryTheory.SmallCategory.{u_1} I] →
    (H : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} I SSet.{u_1}) →
      CategoryTheory.Iso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanHolim.{u_1} H)
        (SerrePositivity.InfinityCategories.HomotopyLimits.simplicialSections.{u_1}
          (SerrePositivity.InfinityCategories.weightedNerveProjection.{u_1} H))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.kanCone_isLimit_iff_bousfieldKanComparison</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.kanCone_isLimit_iff_bousfieldKanComparison.{u_1} : ∀ {I : Type u_1}
  [inst : CategoryTheory.SmallCategory.{u_1} I]
  {F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} I SerrePositivity.InfinityCategories.KanObject.{u_1}}
  (c : CategoryTheory.Limits.Cone.{u_1, u_1, u_1, u_1 + 1} F),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1 + 1}
      (SerrePositivity.InfinityCategories.HomotopyLimits.strictCoherentCone.{u_1, u_1 + 1} c) ↔
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence.{u_1}
      (SerrePositivity.InfinityCategories.HomotopyLimits.bousfieldKanConeComparison.{u_1}
        (CategoryTheory.Functor.mapCone.{u_1, u_1, u_1, u_1, u_1 + 1, u_1 + 1}
          SerrePositivity.InfinityCategories.kanObjectForget.{u_1} c))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.strictCoherentCone_isLimit_iff_reflectedRepresentableComparison.{u_1,
    u_2} : ∀ {I : Type u_1} [inst : CategoryTheory.SmallCategory.{u_1} I] {C : Type u_2}
  [inst_1 : CategoryTheory.Category.{u_1, u_2} C] [inst_2 : CategoryTheory.SimplicialCategory.{u_1, u_2} C]
  [∀ (a b : C), SSet.KanComplex.{u_1} (CategoryTheory.SimplicialCategory.sHom.{u_1, u_2} a b)]
  {F : CategoryTheory.Functor.{u_1, u_1, u_1, u_2} I C} (c : CategoryTheory.Limits.Cone.{u_1, u_1, u_1, u_2} F),
  SerrePositivity.InfinityCategories.IsLimitCone.{max u_2 u_1}
      (SerrePositivity.InfinityCategories.HomotopyLimits.strictCoherentCone.{u_1, u_2} c) ↔
    ∀ (x : C),
      SerrePositivity.InfinityCategories.IsSimplicialHomotopyEquivalence.{u_1}
        (SerrePositivity.InfinityCategories.HomotopyLimits.reflectedRepresentableComparison.{u_1, u_2} c x)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.Kan.filteredColimit_kanComplex</summary>

```lean
@SerrePositivity.InfinityCategories.Kan.filteredColimit_kanComplex.{u_1} : ∀ {J : Type u_1}
  [inst : CategoryTheory.SmallCategory.{u_1} J] [CategoryTheory.IsFiltered.{u_1, u_1} J]
  (D : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} J SSet.{u_1})
  [∀ (j : J), SSet.KanComplex.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} D j)],
  SSet.KanComplex.{u_1} (CategoryTheory.Limits.colimit.{u_1, u_1, u_1, u_1 + 1} D)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Ind.strictNativeCocone_isColimit_of_filtered_forget</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Ind.strictNativeCocone_isColimit_of_filtered_forget.{u_1} : ∀ {I : Type u_1}
  [inst : CategoryTheory.SmallCategory.{u_1} I] [CategoryTheory.IsFiltered.{u_1, u_1} I]
  {F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} I SerrePositivity.InfinityCategories.KanObject.{u_1}}
  (c : CategoryTheory.Limits.Cocone.{u_1, u_1, u_1, u_1 + 1} F)
  (hc :
    CategoryTheory.Limits.IsColimit.{u_1, u_1, u_1, u_1 + 1}
      (CategoryTheory.Functor.mapCocone.{u_1, u_1, u_1, u_1, u_1 + 1, u_1 + 1}
        SerrePositivity.InfinityCategories.kanObjectForget.{u_1} c)),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1 + 1}
    (SerrePositivity.InfinityCategories.HomotopyLimits.strictNativeCocone.{u_1, u_1 + 1} c)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerUnderlyingCone_kanComplex</summary>

```lean
SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerUnderlyingCone_kanComplex.{u_1} : ∀
  (F :
    CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} (CategoryTheory.AsSmall.{u_1, 0, 0} (Opposite.{1} ℕ))
      SerrePositivity.InfinityCategories.KanObject.{u_1})
  [∀ (n : ℕ),
      HomotopicalAlgebra.Fibration.{u_1, u_1 + 1}
        (have this :=
          CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1 + 1} F
            (CategoryTheory.Functor.map.{0, u_1, 0, u_1} CategoryTheory.AsSmall.up.{0, 0, u_1}
              (Quiver.Hom.op.{0, 0} (CategoryTheory.homOfLE.{0} ⋯)));
        this)],
  SSet.KanComplex.{u_1}
    (CategoryTheory.Limits.Cone.pt.{u_1, u_1, u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerUnderlyingCone.{u_1} F))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerCone_forget_isLimit</summary>

```lean
SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerCone_forget_isLimit.{u_1} : (F :
    CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} (CategoryTheory.AsSmall.{u_1, 0, 0} (Opposite.{1} ℕ))
      SerrePositivity.InfinityCategories.KanObject.{u_1}) →
  [inst :
      ∀ (n : ℕ),
        HomotopicalAlgebra.Fibration.{u_1, u_1 + 1}
          (have this :=
            CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1 + 1} F
              (CategoryTheory.Functor.map.{0, u_1, 0, u_1} CategoryTheory.AsSmall.up.{0, 0, u_1}
                (Quiver.Hom.op.{0, 0} (CategoryTheory.homOfLE.{0} ⋯)));
          this)] →
    CategoryTheory.Limits.IsLimit.{u_1, u_1, u_1, u_1 + 1}
      (CategoryTheory.Functor.mapCone.{u_1, u_1, u_1, u_1, u_1 + 1, u_1 + 1}
        SerrePositivity.InfinityCategories.kanObjectForget.{u_1}
        (SerrePositivity.InfinityCategories.HomotopyLimits.kanTowerCone.{u_1} F))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.spaceTowerCone_isLimitCone</summary>

```lean
SerrePositivity.InfinityCategories.HomotopyLimits.spaceTowerCone_isLimitCone.{u_1} : ∀
  (F :
    CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} (CategoryTheory.AsSmall.{u_1, 0, 0} (Opposite.{1} ℕ))
      SerrePositivity.InfinityCategories.KanObject.{u_1})
  [inst :
    ∀ (n : ℕ),
      HomotopicalAlgebra.Fibration.{u_1, u_1 + 1}
        (have this :=
          CategoryTheory.Functor.map.{u_1, u_1, u_1, u_1 + 1} F
            (CategoryTheory.Functor.map.{0, u_1, 0, u_1} CategoryTheory.AsSmall.up.{0, 0, u_1}
              (Quiver.Hom.op.{0, 0} (CategoryTheory.homOfLE.{0} ⋯)));
        this)],
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1 + 1}
    (SerrePositivity.InfinityCategories.HomotopyLimits.spaceTowerCone.{u_1} F)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallLimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallLimits.{u_1} : {C E : SSet.{u_1 + 1}} →
  Quiver.Hom.{u_1 + 1, u_1 + 2} C E → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Presentable.PreservesSmallColimits.{u_1} : {C E : SSet.{u_1 + 1}} →
  Quiver.Hom.{u_1 + 1, u_1 + 2} C E → Prop
```

</details>

<details>
<summary>CategoryTheory.CartesianMonoidalCategory</summary>

```lean
CategoryTheory.CartesianMonoidalCategory.{u_1,
  u_2} : (C : Type u_2) → [CategoryTheory.Category.{u_1, u_2} C] → Type (max u_2 u_1)
```

</details>

<details>
<summary>CategoryTheory.Closed</summary>

```lean
@CategoryTheory.Closed.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    [CategoryTheory.MonoidalCategory.{u_1, u_2} C] → C → Type (max u_2 u_1)
```

</details>

<details>
<summary>CategoryTheory.MonoidalClosed</summary>

```lean
CategoryTheory.MonoidalClosed.{u_1,
  u_2} : (C : Type u_2) →
  [inst : CategoryTheory.Category.{u_1, u_2} C] → [CategoryTheory.MonoidalCategory.{u_1, u_2} C] → Type (max u_2 u_1)
```

</details>
