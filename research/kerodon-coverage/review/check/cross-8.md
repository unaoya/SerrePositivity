# Ch 8 交差の抜き取り検査（§8.3）

- 検査日 2026-11-10。対象は -c を取り込んだ `0d9e86356` の表。作業枝に §8.3 を含む `abe0628ab` を取り込んだ。
- 乱数の種 `0x0d9e8635`。Python の `random.Random` を一つ使い、第7章から第10章まで章順に処理。番号を整数の組として昇順に並べた各プールから、完全対応、partial、none の順に `sample` で重複なく抽出した。上限は 20、10、10 件。
- 抽出後は対象番号と Kerodon 本文のみで独立判定を作成した。宣言は原対応表の名前候補、番号・小節の引用、概念名・双対・特殊化によるソース検索から探した。採用した宣言は共有ロック下で `#check` と `#print axioms` を確認した。
- 独立判定メモを確定した時点の SHA-256 は `4e1174d7161dfd8f3a8e52d13c188fc83e75286177d6c109b3f089216ddcb5b5`。その後に -c の status を開いて比較した。
- partial は原文の同じ主張を直接与える範囲に限り、§8.1 の四分類を付けた。探索で見つけた補題や別の比較射は、該当する結論を直接与えるかを区別した。

| 抽出群 | 母数 | 抽出 | 一致 | 差 | 差の割合 |
| --- | ---: | ---: | ---: | ---: | ---: |
| own・both・mathlib | 36 | 20 | 17 | 3 | 15.0% |
| partial | 173 | 10 | 4 | 6 | 60.0% |
| none | 274 | 10 | 10 | 0 | 0.0% |

完全対応の群で差が 1 割を超えたため、§8.3 に従いこの章で停止。

- mathlib → none は 1 件。
- own → none は 2 件。
- partial → none は 5 件。
- partial → own は 1 件。

## own・both・mathlib

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 独立照合で型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [8.1.0.1](https://kerodon.net/tag/00AZ) | mathlib | none | — | 差 | 通常圏の逆向き第一辺・順向き第二辺の組で射を定義する Tw を探索。Mathlib の CostructuredArrow は端点を固定する。EdgewiseSubdivision は単体集合に値を取る。 番号の直接引用 0 件、同じ小節の引用 206 件。 | — |
| [8.1.1.1](https://kerodon.net/tag/03JG) | own | own | — | 一致 | 任意の単体集合 C。単体圏で Jᵒᵖ⋆J を表す edgewiseWeight による前合成を各次数に取り、Tw を定義する。 | [`SerrePositivity.InfinityCategories.TwistedArrow`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/Projection.lean#L20)、[`SerrePositivity.InfinityCategories.edgewiseSubdivision`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseSubdivision.lean#L35)、[`SerrePositivity.InfinityCategories.edgewiseWeight`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseSubdivision.lean#L23) |
| [8.1.1.11](https://kerodon.net/tag/03JQ) | own | own | — | 一致 | 準圏 C に対する標準射 Tw(C)→Cᵒᵖ×C が左ファイブレーション。 | [`SerrePositivity.InfinityCategories.twistedArrowProjection_leftFibration`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/LeftFibration.lean#L61) |
| [8.1.1.12](https://kerodon.net/tag/03JR) | own | own | — | 一致 | 準圏 C の twisted arrow 単体集合が準圏。 | [`SerrePositivity.InfinityCategories.twistedArrow_quasicategory`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/LeftFibration.lean#L73) |
| [8.1.1.13](https://kerodon.net/tag/048H) | own | own | — | 一致 | Kan C に対して同じ Tw(C) が Kan、同じ両端射影は左ファイブレーションで、Kan 複体間の左ファイブレーションを Kan ファイブレーションにする型が適用できる。 | [`SerrePositivity.InfinityCategories.twistedArrowProjection_leftFibration`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/LeftFibration.lean#L61)、[`SerrePositivity.InfinityCategories.edgewiseSubdivision_kanComplex`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseRightFilling.lean#L104)、[`SerrePositivity.InfinityCategories.leftFibration_fibration_of_kanComplex`](../../../../SerrePositivity/InfinityCategories/F1/Fibrations/LeftKanFibration.lean#L52) |
| [8.1.2.3](https://kerodon.net/tag/048J) | own | own | — | 一致 | Kan C を仮定し、edgewise subdivision の左端 Cᵒᵖ と右端 C への二つの射影それぞれが自明 Kan ファイブレーション。 | [`SerrePositivity.InfinityCategories.edgewiseLeft_trivialKanFibration`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseLeftFilling.lean#L42)、[`SerrePositivity.InfinityCategories.edgewiseRight_trivialKanFibration`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseRightFilling.lean#L95) |
| [8.1.2.11](https://kerodon.net/tag/03K1) | own | own | — | 一致 | 準圏 C の指定した両端で coslice の包含から誘導される左 pinched Hom の射そのものが圏同値。両端は Kan なのでホモトピー同値に対応する。 | [`SerrePositivity.InfinityCategories.cosliceTwistedHomMap`](../../../../SerrePositivity/InfinityCategories/F1/Joins/CosliceTwistedHomComparison.lean#L24)、[`SerrePositivity.InfinityCategories.cosliceTwistedHomMap_isQCatEquivalence`](../../../../SerrePositivity/InfinityCategories/F1/Joins/CosliceTwistedHomEquivalence.lean#L27) |
| [8.3.1.1](https://kerodon.net/tag/03M3) | mathlib | mathlib | — | 一致 | 通常圏の任意の対象 X と Set 値 F。coyoneda から F への自然変換を X の恒等射で評価する全単射。 | `CategoryTheory.coyonedaEquiv`（`Mathlib/CategoryTheory/Yoneda.lean:999`）、`CategoryTheory.coyonedaEquiv_apply`（`Mathlib/CategoryTheory/Yoneda.lean:1007`） |
| [8.5.1.1](https://kerodon.net/tag/03YJ) | own | own | — | 一致 | 準圏の頂点間で section と retraction を取り、ホモトピー圏でその合成が恒等という条件を定義する。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.IsVertexRetractOf`](../../../../SerrePositivity/InfinityCategories/Core/Retracts.lean#L50)、[`SerrePositivity.InfinityCategories.F2.Idempotent.VertexRetraction`](../../../../SerrePositivity/InfinityCategories/Core/Retracts.lean#L21) |
| [8.5.1.12](https://kerodon.net/tag/05E6) | own | own | — | 一致 | 同じ錐形状から出る二図式について、全関手圏の余極限余錐の retract が余極限余錐。 | [`SerrePositivity.InfinityCategories.F2.Compact.isColimitCone_of_functorRetraction`](../../../../SerrePositivity/InfinityCategories/F2/Compact/ColimitRetractions.lean#L24) |
| [8.5.1.22](https://kerodon.net/tag/03YZ) | own | own | — | 一致 | 準圏の二頂点を固定して 2-単体の長辺を恒等にする述語付きの型。頂点を動かすと原文の retraction diagram のデータを与える。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/RetractionTriangle.lean#L24) |
| [8.5.1.31](https://kerodon.net/tag/03Z7) | own | own | — | 一致 | 準圏 X で WeakShape→SplitShape に沿う制限が自明 Kan ファイブレーション。WeakShape の像 R との同型は包含を厳密に回収する。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.weakComparisonRestriction_trivialKanFibration`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/WeakExtension.lean#L22)、[`SerrePositivity.InfinityCategories.F2.Idempotent.weakShapeImageIso_ι`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/WeakImage.lean#L36) |
| [8.5.1.36](https://kerodon.net/tag/03ZB) | own | own | — | 一致 | 任意の n と有限部分集合 S。S の二点間に S にない点があれば、S 全体を含まない面で張る包含が内アノダイン。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.missingFaceComplex_innerAnodyne`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/MissingFaceInnerAnodyne.lean#L22) |
| [8.5.3.5](https://kerodon.net/tag/03ZX) | own | own | — | 一致 | coherent idempotent の IdemShape→X を厳密に回収する SplitShape→X と制限等式の型。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplitting`](../../../../SerrePositivity/InfinityCategories/Core/Idempotent/Coherent.lean#L36) |
| [8.5.3.10](https://kerodon.net/tag/0402) | own | own | — | 一致 | 任意の準圏で Ret から Idem への前合成が充満忠実。有効な元の全 Idem 図式で張る充満部分圏への因子化が自明 Kan ファイブレーション。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.strongSplittingRestriction_isFullyFaithful`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/SplittingRestriction.lean#L33)、[`SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_trivialKanFibration`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/EffectiveSplittingRestriction.lean#L69)、[`SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_inclusion`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/EffectiveIdempotents.lean#L56) |
| [8.5.4.1](https://kerodon.net/tag/0406) | own | own | — | 一致 | 全ての coherent IdemShape 図式に対して強い分裂が存在するという述語。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentComplete`](../../../../SerrePositivity/InfinityCategories/Core/Idempotent/Coherent.lean#L40) |
| [8.5.4.26](https://kerodon.net/tag/0606) | own | own | — | 一致 | 左ファイブレーションの底が冪等完備なら、全空間も冪等完備。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.isIdempotentComplete_of_leftFibration`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/FibrationComplete.lean#L31) |
| [8.5.5.1](https://kerodon.net/tag/040U) | own | own | — | 一致 | 指定関手について、充満忠実性、値域の冪等完備性、値域の全頂点が像の retract であることを結ぶ述語。関手の存在量化で圏の完備化の定義を得る。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentCompletion`](../../../../SerrePositivity/InfinityCategories/F1/Idempotent/Completion.lean#L29) |
| [8.6.7.2](https://kerodon.net/tag/04FA) | own | none | — | 差 | 任意の locally Kan E の非対称模型と指定の忘却射を探索。EdgewiseKanEnriched の比較は KanObject の別模型で、同じ E^≍→E の弱同値を型に含まない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.6.7.5](https://kerodon.net/tag/04FD) | own | none | — | 差 | QCat の非対称模型の準圏性と指定忘却射の同値を探索。CatInfinity と edgewiseOppositeKanInfinityEquivalence は元の QC と空間の別模型を扱う。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## partial

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 独立照合で型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [8.1.2.16](https://kerodon.net/tag/03LX) | partial | partial | direction | 一致 | 充満忠実な F から Tw(F) と底の Fᵒᵖ×F に対する厳密引き戻しへの指定比較射が前合成同値。逆向きにこの四角から F の充満忠実性を出す型は未確認。 | [`SerrePositivity.InfinityCategories.HomotopyLimits.twistedArrowFunctorComparison_isPrecompositionEquivalence`](../../../../SerrePositivity/InfinityCategories/HomotopyLimits/TwistedArrowFunctorComparison.lean#L52) |
| [8.2.5.1](https://kerodon.net/tag/045S) | partial | none | — | 差 | representable／corepresentable coupling と随伴の iff を探索。AdjunctionHomFamily は既に随伴があるとき固定 x で共変 Hom を比較し、与えられた両変数の coupling を対象にした結論がない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.3.3.13](https://kerodon.net/tag/03NJ) | partial | partial | special | 一致 | 小さい準圏に対する前層と共変関手への両 Yoneda の充満忠実性がある。大きい局所小な C を許す同じ値域と本質像の両記述までは未確認。 | [`SerrePositivity.InfinityCategories.yonedaInfinityMap_isFullyFaithful`](../../../../SerrePositivity/InfinityCategories/F1/Yoneda/YonedaInfinityFullyFaithful.lean#L72)、[`SerrePositivity.InfinityCategories.F2.Presentable.coyonedaInfinityMap_isFullyFaithful`](../../../../SerrePositivity/InfinityCategories/F2/Presentable/CoYonedaFullyFaithful.lean#L74) |
| [8.3.3.17](https://kerodon.net/tag/03Y7) | partial | partial | special | 一致 | 小さい準圏に対し、前層への充満忠実な写像は小さい形状の極限を保ち、前層は小さい極限と余極限を持つ。同じ宇宙の一般の κ による形状を明示する型は未確認。 | [`SerrePositivity.InfinityCategories.yonedaInfinityMap_isFullyFaithful`](../../../../SerrePositivity/InfinityCategories/F1/Yoneda/YonedaInfinityFullyFaithful.lean#L72)、[`SerrePositivity.InfinityCategories.presheafInfinity_hasLimit`](../../../../SerrePositivity/InfinityCategories/F1/Yoneda/PresheafAllSmallLimits.lean#L30)、[`SerrePositivity.InfinityCategories.presheafInfinity_hasColimit`](../../../../SerrePositivity/InfinityCategories/F1/Yoneda/PresheafPointwiseColimits.lean#L34)、[`SerrePositivity.InfinityCategories.yonedaInfinityMap_isLimit`](../../../../SerrePositivity/InfinityCategories/F1/Yoneda/YonedaLimits.lean#L22) |
| [8.3.6.1](https://kerodon.net/tag/03N6) | partial | partial | special | 一致 | 小さい locally Kan 豊穣圏と第一変数を一対象 x に固定した場合、その coherent nerve から空間への Hom(x,−) の関手がある。両変数を一つに束ねた構成は未確認。 | [`SerrePositivity.InfinityCategories.representableHomCoherent`](../../../../SerrePositivity/InfinityCategories/F1/Coherent/RepresentableHomFunctor.lean#L77) |
| [8.4.6.6](https://kerodon.net/tag/04BN) | partial | none | — | 差 | 任意の形状集合 K で前層内の最小な余極限閉包を探索。IndVertexDensity は κ-filtered な表示を持つ対象の密度で、指定された K による最小性を与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.4.6.11](https://kerodon.net/tag/05ZZ) | partial | none | — | 差 | 指定の変換について K-cocontinuous な延長と左 Kan 延長の iff を探索。PresheafYonedaLeftKan は前層からの構成、IndContinuousLeftKan は特定の拡張で、一般の二条件の iff は見つからなかった。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.5.1.27](https://kerodon.net/tag/03Z3) | partial | own | — | 差 | WalkingSplit の nerve に包含・射影からなる標準 2-単体を作り、長辺が恒等であることと、その像部分複体を与える。 | [`SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle`](../../../../SerrePositivity/InfinityCategories/Core/Idempotent/WeakComparison.lean#L24)、[`SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle_longEdge`](../../../../SerrePositivity/InfinityCategories/Core/Idempotent/WeakComparison.lean#L42)、[`SerrePositivity.InfinityCategories.F2.Idempotent.weakRetractionImage`](../../../../SerrePositivity/InfinityCategories/F2/Idempotent/WeakImage.lean#L22) |
| [8.6.7.11](https://kerodon.net/tag/04FK) | partial | none | — | 差 | 空間の共通 edgewise 解像上に元の空間と反対空間の FunctorIso がある。型を再確認すると、QC 上の opposition の指定制限はこの二射に現れず、同定を別に要する。 番号の直接引用 0 件、同じ小節の引用 0 件。 | [`SerrePositivity.InfinityCategories.edgewiseKanOppositeInfinityComparisonIso`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseOppositeKanComparison.lean#L58)、[`SerrePositivity.InfinityCategories.edgewiseOppositeKanInfinityEquivalence`](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseOppositeKanComparison.lean#L66) |
| [8.6.8.19](https://kerodon.net/tag/05WU) | partial | none | — | 差 | 左随伴を右随伴に移す QC 上の反変関手と、対象付きの指定射影を探索。AdjunctionHomFamily は既に随伴を与えたときの Hom の同型を返す。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## none

| Kerodon | -c | 独立判定 | partial_kind | 比較 | 仮定と結論の照合 | 独立照合で型を確認した宣言 |
| --- | --- | --- | --- | --- | --- | --- |
| [8.2.6.6](https://kerodon.net/tag/045Z) | none | none | — | 一致 | balanced coupling と両向きの同値による表示の判定を探索。Mathlib の Balanced は mono かつ epi の同型性。AdjunctionHomFamily は随伴から一変数の Hom を比較する。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.4.1.23](https://kerodon.net/tag/03VZ) | none | none | — | 一致 | 任意の dense F を含む充満部分圏の dense 性の型を探索。PresheafDensity は標準 Yoneda の表示で、指定の F を別の充満部分圏へ拡張する含意はない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.4.7.8](https://kerodon.net/tag/060X) | none | none | — | 一致 | QC の K-cocomplete 側への反射と、単位が cocompletion を表示する iff を探索。NativeAdjointFunctorCriterion は既にある準圏関手の随伴を判定する別の型。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.5.8.6](https://kerodon.net/tag/0421) | none | none | — | 一致 | 連結 Kan の点付き自己射の homotopy idempotent から分裂を作る型を探索。StrongSplittingLimitExistence は最初から coherent IdemShape を入力する。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.5.10.7](https://kerodon.net/tag/0430) | none | none | — | 一致 | Duskin nerve の BDy 上の延長と homotopy idempotent の iff を探索。WeakExtension の弱い Ret 図式は BDy でなく、同じ入力の延長を述べない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.6.2.3](https://kerodon.net/tag/04CQ) | none | none | — | 一致 | Tw の指定底上で cocartesian 辺を保つ関手圏の cartesian conjugate と評価を探索。FiberwiseHomCartesianFibration はマークと相対値域のない一般の指数射影。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.6.2.7](https://kerodon.net/tag/04CU) | none | none | — | 一致 | 制限前後の cartesian 辺の反映と、マークを保つ部分複体への制限を探索。FiberwiseHomCartesianEdges はマークなしの相対指数で辺を可逆化する条件。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.6.8.11](https://kerodon.net/tag/05WM) | none | none | — | 一致 | 反変輸送の各底辺で三列の指定比較が可換となる型を探索。RepresentationComparisonRestriction は制限の図式の同型で、一般の cartesian fibration と元の三列の各辺の輸送を比較しない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.7.6.2](https://kerodon.net/tag/05NK) | none | none | — | 一致 | Δ² 上の flat 内ファイブレーションで h_X の ≥1 への制限が 1 上から左 Kan 延長になる型を探索。RelativeLeftCanonicalExistence は各点の相対余極限を別に仮定する。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |
| [8.7.7.7](https://kerodon.net/tag/05NV) | none | none | — | 一致 | flat 内ファイブレーションの相対 Hom によるファイバー別 κ-cocompletion を探索。FiberwiseHom は内部 Hom の構成で、指定写像の普遍性を与えない。 番号の直接引用 0 件、同じ小節の引用 0 件。 | — |

## 停止基準にかかった3件

集計の 3/20 は、-c の宣言欄を開く前の独立判定と照合したときの差。以下は比較後に -c の引用を確認した結果で、独立判定の欄と集計は初回のまま記録した。

- 8.1.0.1（`mathlib → none`）は独立探索で `CategoryTheory.Functor.Elements` に届かなかった。-c の構成は `Functor.uncurry.obj coyoneda` の圏 of elements。Mathlib の定義を展開すると、対象は `X ⟶ Y`、射は `Cᵒᵖ × C` の射と Hom の像の等式、合成は底の成分ごとの合成になる。-c の引用は `Mathlib/CategoryTheory/Elements.lean:48`、`Mathlib/CategoryTheory/Functor/Currying.lean:37`、`Mathlib/CategoryTheory/Yoneda.lean:89`。
- 8.6.7.2（`own → none`）は独立照合で KanObject 用の比較を調べたが、-c は任意の局所 Kan な豊穣圏に対する宣言を挙げていた。原文の Notation 8.6.7.1 は各豊穣 Hom に Tw を施す構成で、Lean の `EdgewiseEnrichedObject` もその Hom を `edgewiseSubdivision` とする。局所 Kan 性、右端射影とその Hom ごとの自明 Kan ファイブレーション性、右端射影の coherent nerve の同値が該当する。[EdgewiseEnrichedCategory](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseEnrichedCategory.lean#L153)・[EdgewiseEnrichedComparison](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseEnrichedComparison.lean#L78)・[EdgewiseRightFilling](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseRightFilling.lean#L95)
- 8.6.7.5（`own → none`）も、-c の引用は同じ一般比較を `QCat` に適用するものだった。指定射 `edgewiseEnrichedInfinityMap QCat` の値域は `SimplicialNerve QCat = CatInfinity`。独立照合ではこの一般比較を見落とした。[EdgewiseEnrichedComparison](../../../../SerrePositivity/InfinityCategories/F1/TwistedArrow/EdgewiseEnrichedComparison.lean#L78)・[CatInfinity](../../../../SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean#L23)

## kernel の確認

<details>
<summary>SerrePositivity.InfinityCategories.TwistedArrow</summary>

```lean
SerrePositivity.InfinityCategories.TwistedArrow.{u_1} : SSet.{u_1} → SSet.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseSubdivision</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseSubdivision.{u_1} : SSet.{u_1} → SSet.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseWeight</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseWeight.{u_1} : CategoryTheory.Functor.{0, u_1, 0, u_1 + 1} SimplexCategory
  SSet.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.twistedArrowProjection_leftFibration</summary>

```lean
SerrePositivity.InfinityCategories.twistedArrowProjection_leftFibration.{u_1} : ∀ (C : SSet.{u_1})
  [SSet.Quasicategory.{u_1} C],
  SerrePositivity.InfinityCategories.LeftFibration.{u_1}
    (SerrePositivity.InfinityCategories.twistedArrowProjection.{u_1} C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.twistedArrow_quasicategory</summary>

```lean
SerrePositivity.InfinityCategories.twistedArrow_quasicategory.{u_1} : ∀ (C : SSet.{u_1}) [SSet.Quasicategory.{u_1} C],
  SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.TwistedArrow.{u_1} C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseSubdivision_kanComplex</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseSubdivision_kanComplex.{u_1} : ∀ (K : SSet.{u_1}) [SSet.KanComplex.{u_1} K],
  SSet.KanComplex.{u_1} (SerrePositivity.InfinityCategories.edgewiseSubdivision.{u_1} K)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.leftFibration_fibration_of_kanComplex</summary>

```lean
@SerrePositivity.InfinityCategories.leftFibration_fibration_of_kanComplex.{u_1} : ∀ {X Y : SSet.{u_1}}
  [SSet.KanComplex.{u_1} X] [SSet.KanComplex.{u_1} Y] (q : Quiver.Hom.{u_1, u_1 + 1} X Y)
  [SerrePositivity.InfinityCategories.LeftFibration.{u_1} q], HomotopicalAlgebra.Fibration.{u_1, u_1 + 1} q
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseLeft_trivialKanFibration</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseLeft_trivialKanFibration.{u_1} : ∀ (X : SSet.{u_1})
  [SSet.KanComplex.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1} (SerrePositivity.InfinityCategories.edgewiseLeft.{u_1} X)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseRight_trivialKanFibration</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseRight_trivialKanFibration.{u_1} : ∀ (K : SSet.{u_1})
  [SSet.KanComplex.{u_1} K],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.edgewiseRight.{u_1} K)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.cosliceTwistedHomMap</summary>

```lean
@SerrePositivity.InfinityCategories.cosliceTwistedHomMap.{u_1} : {C : SSet.{u_1}} →
  (x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := 0 })) →
    Quiver.Hom.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.vertexFiber.{u_1}
        (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1}
          ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1}) x))
        y)
      (SerrePositivity.InfinityCategories.twistedArrowHomSpace.{u_1} x y)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.cosliceTwistedHomMap_isQCatEquivalence</summary>

```lean
@SerrePositivity.InfinityCategories.cosliceTwistedHomMap_isQCatEquivalence.{u_1} : ∀ {C : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} C]
  (x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := 0 })),
  SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1}
    (SerrePositivity.InfinityCategories.cosliceTwistedHomMap.{u_1} x y)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.HomotopyLimits.twistedArrowFunctorComparison_isPrecompositionEquivalence</summary>

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.twistedArrowFunctorComparison_isPrecompositionEquivalence.{u_1} : ∀
  {C D : SSet.{u_1}} [SSet.Quasicategory.{u_1} C] [SSet.Quasicategory.{u_1} D] (f : Quiver.Hom.{u_1, u_1 + 1} C D),
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1} f →
    SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1}
      (SerrePositivity.InfinityCategories.HomotopyLimits.twistedArrowFunctorComparison.{u_1} f)
```

</details>

<details>
<summary>CategoryTheory.coyonedaEquiv</summary>

```lean
@CategoryTheory.coyonedaEquiv.{u_1,
    u_2} : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    {X : C} →
      {F : CategoryTheory.Functor.{u_1, u_1, u_2, u_1 + 1} C (Type u_1)} →
        Equiv.{(max u_2 u_1) + 1, u_1 + 1}
          (Quiver.Hom.{max u_2 u_1, max u_2 (u_1 + 1)}
            (CategoryTheory.Functor.obj.{u_1, max u_2 u_1, u_2, max u_2 (u_1 + 1)} CategoryTheory.coyoneda.{u_1, u_2}
              (Opposite.op.{u_2 + 1} X))
            F)
          (CategoryTheory.Functor.obj.{u_1, u_1, u_2, u_1 + 1} F X)
```

</details>

<details>
<summary>CategoryTheory.coyonedaEquiv_apply</summary>

```lean
@CategoryTheory.coyonedaEquiv_apply.{u_1,
    u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X : C}
  {F : CategoryTheory.Functor.{u_1, u_1, u_2, u_1 + 1} C (Type u_1)}
  (f :
    Quiver.Hom.{max u_2 u_1, max u_2 (u_1 + 1)}
      (CategoryTheory.Functor.obj.{u_1, max u_2 u_1, u_2, max u_2 (u_1 + 1)} CategoryTheory.coyoneda.{u_1, u_2}
        (Opposite.op.{u_2 + 1} X))
      F),
  Eq.{u_1 + 1} (CategoryTheory.coyonedaEquiv.{u_1, u_2} f)
    ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1}
        (CategoryTheory.NatTrans.app.{u_1, u_1, u_2, u_1 + 1} f X))
      (CategoryTheory.CategoryStruct.id.{u_1, u_2} X))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.yonedaInfinityMap_isFullyFaithful</summary>

```lean
SerrePositivity.InfinityCategories.yonedaInfinityMap_isFullyFaithful.{u_1} : ∀ (C : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} C],
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1 + 1}
    (SerrePositivity.InfinityCategories.yonedaInfinityMap.{u_1} C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Presentable.coyonedaInfinityMap_isFullyFaithful</summary>

```lean
SerrePositivity.InfinityCategories.F2.Presentable.coyonedaInfinityMap_isFullyFaithful.{u_1} : ∀ (C : SSet.{u_1})
  [inst : SSet.Quasicategory.{u_1} C],
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1 + 1}
    (SerrePositivity.InfinityCategories.coyonedaInfinityMap.{u_1} C)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.presheafInfinity_hasLimit</summary>

```lean
@SerrePositivity.InfinityCategories.presheafInfinity_hasLimit.{u_1} : ∀ {B C : SSet.{u_1}}
  (p :
    Quiver.Hom.{u_1 + 1, u_1 + 2}
      (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} B)
      (SerrePositivity.InfinityCategories.PresheafInfinity.{u_1} C)),
  SerrePositivity.InfinityCategories.HasLimit.{u_1 + 1} p
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.presheafInfinity_hasColimit</summary>

```lean
@SerrePositivity.InfinityCategories.presheafInfinity_hasColimit.{u_1} : ∀ {B C : SSet.{u_1}}
  (p :
    Quiver.Hom.{u_1 + 1, u_1 + 2}
      (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1} B)
      (SerrePositivity.InfinityCategories.PresheafInfinity.{u_1} C)),
  SerrePositivity.InfinityCategories.HasColimit.{u_1 + 1} p
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.yonedaInfinityMap_isLimit</summary>

```lean
@SerrePositivity.InfinityCategories.yonedaInfinityMap_isLimit.{u_1} : ∀ {K C : SSet.{u_1}}
  [inst : SSet.Quasicategory.{u_1} C] {D : Quiver.Hom.{u_1, u_1 + 1} K C}
  (c : SerrePositivity.InfinityCategories.JoinCone.{u_1} D),
  SerrePositivity.InfinityCategories.IsLimitCone.{u_1} c →
    SerrePositivity.InfinityCategories.IsLimitCone.{u_1 + 1}
      (SerrePositivity.InfinityCategories.mapJoinCone.{u_1 + 1}
        (SerrePositivity.InfinityCategories.yonedaInfinityMap.{u_1} C)
        (SerrePositivity.InfinityCategories.JoinCone.ulift.{u_1, u_1 + 1} c))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.representableHomCoherent</summary>

```lean
@SerrePositivity.InfinityCategories.representableHomCoherent.{u_1} : {D : Type u_1} →
  [inst : CategoryTheory.Category.{u_1, u_1} D] →
    [inst_1 : CategoryTheory.SimplicialCategory.{u_1, u_1} D] →
      [∀ (a b : D), SSet.KanComplex.{u_1} (CategoryTheory.SimplicialCategory.sHom.{u_1, u_1} a b)] →
        D →
          Quiver.Hom.{u_1 + 1, u_1 + 2}
            (CategoryTheory.Functor.obj.{u_1, u_1 + 1, u_1 + 1, u_1 + 2} SSet.uliftFunctor.{u_1 + 1, u_1}
              (CategoryTheory.SimplicialNerve.{u_1, u_1} D))
            SerrePositivity.InfinityCategories.SpaceInfinity.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.IsVertexRetractOf</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.IsVertexRetractOf.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.VertexRetraction</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.VertexRetraction.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Type u_1
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Compact.isColimitCone_of_functorRetraction</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Compact.isColimitCone_of_functorRetraction.{u_1} : ∀ {K X : SSet.{u_1}}
  [SSet.Quasicategory.{u_1} X] {p q : Quiver.Hom.{u_1, u_1 + 1} K X}
  {c : SerrePositivity.InfinityCategories.JoinCocone.{u_1} p}
  {d : SerrePositivity.InfinityCategories.JoinCocone.{u_1} q}
  (r :
    SerrePositivity.InfinityCategories.F2.Idempotent.VertexRetraction.{u_1}
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑c)
      (SerrePositivity.InfinityCategories.functorVertex.{u_1} ↑d)),
  SerrePositivity.InfinityCategories.IsColimitCone.{u_1} d → SerrePositivity.InfinityCategories.IsColimitCone.{u_1} c
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.RetractionTriangle.{u_1} : {X : SSet.{u_1}} →
  CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) →
    CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Type u_1
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle.{u_1} : Quiver.Hom.{u_1, u_1 + 1}
  (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SSet.stdSimplex.{u_1} { len := 2 })
  SerrePositivity.InfinityCategories.F2.Idempotent.SplitShape.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle_longEdge</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle_longEdge.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.CosimplicialObject.δ.{u_1, u_1 + 1} SSet.stdSimplex.{u_1} 1)
    SerrePositivity.InfinityCategories.F2.Idempotent.walkingRetractionTriangle.{u_1})
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    SerrePositivity.InfinityCategories.F2.Idempotent.longEdgeCollapse.{u_1}
    ((Equiv.symm.{u_1 + 1, u_1 + 1} SSet.yonedaEquiv.{u_1})
      ((Equiv.symm.{u_1 + 1, u_1 + 1} CategoryTheory.nerveEquiv.{u_1, u_1})
        SerrePositivity.InfinityCategories.F2.Idempotent.walkingImage.{u_1})))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.weakRetractionImage</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.weakRetractionImage.{u_1} : SSet.Subcomplex.{u_1}
  SerrePositivity.InfinityCategories.F2.Idempotent.SplitShape.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.weakComparisonRestriction_trivialKanFibration</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.weakComparisonRestriction_trivialKanFibration.{u_1} : ∀
  (X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1}
      (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1}
        SerrePositivity.InfinityCategories.F2.Idempotent.weakComparison.{u_1})
      X)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.weakShapeImageIso_ι</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.weakShapeImageIso_ι.{u_1} : Eq.{u_1 + 1}
  (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
    (CategoryTheory.Iso.hom.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.F2.Idempotent.weakShapeImageIso.{u_1})
    (SSet.Subcomplex.ι.{u_1} SerrePositivity.InfinityCategories.F2.Idempotent.weakRetractionImage.{u_1}))
  SerrePositivity.InfinityCategories.F2.Idempotent.weakComparison.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.missingFaceComplex_innerAnodyne</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.missingFaceComplex_innerAnodyne.{u_1} : ∀ {n : ℕ}
  (J : Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} n 1))) (j i k : Fin (HAdd.hAdd.{0, 0, 0} n 1)),
  j ∉ J →
    Membership.mem.{0, 0} J i →
      Membership.mem.{0, 0} J k →
        LT.lt.{0} i j →
          LT.lt.{0} j k →
            SSet.innerAnodyneExtensions.{u_1}
              (SSet.Subcomplex.ι.{u_1} (SerrePositivity.InfinityCategories.F2.Idempotent.missingFaceComplex.{u_1} J))
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplitting</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplitting.{u_1} : {X : SSet.{u_1}} →
  SerrePositivity.InfinityCategories.F2.Idempotent.CoherentIdempotent.{u_1} X → Type u_1
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.strongSplittingRestriction_isFullyFaithful</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.strongSplittingRestriction_isFullyFaithful.{u_1} : ∀ (X : SSet.{u_1})
  [SSet.Quasicategory.{u_1} X],
  SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1}
    (SerrePositivity.InfinityCategories.F2.Idempotent.strongSplittingRestriction.{u_1} X)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_trivialKanFibration</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_trivialKanFibration.{u_1} : ∀
  (X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X],
  SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1}
    (SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction.{u_1} X)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_inclusion</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction_inclusion.{u_1} : ∀ (X : SSet.{u_1}),
  Eq.{u_1 + 1}
    (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1}
      (SerrePositivity.InfinityCategories.F2.Idempotent.effectiveSplittingRestriction.{u_1} X)
      (SSet.Subcomplex.ι.{u_1} (SerrePositivity.InfinityCategories.F2.Idempotent.effectiveIdempotents.{u_1} X)))
    (SerrePositivity.InfinityCategories.F2.Idempotent.strongSplittingRestriction.{u_1} X)
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentComplete</summary>

```lean
SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentComplete.{u_1} : SSet.{u_1} → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.isIdempotentComplete_of_leftFibration</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.isIdempotentComplete_of_leftFibration.{u_1} : ∀ {X Y : SSet.{u_1}}
  (p : Quiver.Hom.{u_1, u_1 + 1} X Y) [SerrePositivity.InfinityCategories.LeftFibration.{u_1} p],
  SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentComplete.{u_1} Y →
    SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentComplete.{u_1} X
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentCompletion</summary>

```lean
@SerrePositivity.InfinityCategories.F2.Idempotent.IsIdempotentCompletion.{u_1} : {C D : SSet.{u_1}} →
  Quiver.Hom.{u_1, u_1 + 1} C D → Prop
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseKanOppositeInfinityComparisonIso</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseKanOppositeInfinityComparisonIso.{u_1} : SerrePositivity.InfinityCategories.FunctorIso.{u_1 +
      1}
  (SerrePositivity.InfinityCategories.edgewiseEnrichedInfinityMap.{u_1, u_1 + 1}
    SerrePositivity.InfinityCategories.KanObject.{u_1})
  SerrePositivity.InfinityCategories.edgewiseOppositeKanInfinityMap.{u_1}
```

</details>

<details>
<summary>SerrePositivity.InfinityCategories.edgewiseOppositeKanInfinityEquivalence</summary>

```lean
SerrePositivity.InfinityCategories.edgewiseOppositeKanInfinityEquivalence.{u_1} : SerrePositivity.InfinityCategories.QCatEquivalence.{u_1 +
      1}
  (CategoryTheory.SimplicialNerve.{u_1, u_1 + 1}
    (SerrePositivity.InfinityCategories.EdgewiseEnrichedObject.{u_1 + 1}
      SerrePositivity.InfinityCategories.KanObject.{u_1}))
  SerrePositivity.InfinityCategories.SpaceInfinity.{u_1}
```

</details>
