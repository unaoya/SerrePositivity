# Archive を参照する Kerodon 行（AR-W1）

対応表は変更していない。全 `review/ch*.csv` の `Archive` と旧 `InfinityCategories.F2` を検索した。宣言欄に Archive のパスがあるのは4行、理由欄だけで Archive に言及するものが1行。F2 という旧名前空間だけでは Archive の宣言と判定しない。

## 4.3.6.12 — partial を維持する案

元行：`review/ch4.csv:94`。Archive の `SerrePositivity.InfinityCategories.F2.sliceOverRestrict_rightFibration_of_mono`（`ConeMappingRestriction.lean:25`）と、本体の `sliceUnderRestrict_leftFibration`（`FibrationRestriction.lean:69`）を挙げている。

[原典 Tag 018K](https://kerodon.net/tag/018K) は、準圏内の図式を部分単体集合へ制限した際、slice の制限が right fibration、coslice の制限が left fibration になるという両側の主張。Archive の型は `X` が準圏、`p : K ⟶ X`、`i : L ⟶ K` が単射なら `RightFibration (sliceOverRestrict p i)`。部分複体包含より一般の単射を許し、原典の右側を含む。

本体の型は部分複体包含に対する **coslice/left** 側であり、名前が似ていても同じ右側の主張ではない。右側の本体宣言は今回の探索では確定できなかった。案は partial を維持し、Archive の名を形式化済みの宣言として数えず参考欄へ分離すること。`FE/SliceRestriction` の2本を本体へ移す候補とする。P⁰ 閉包に4.3.6.12がある。

## 9.1.1.18 — partial を維持し、条件と向きを詳しくする案

元行：`review/ch9.csv:8`。Archive の `isKappaFiltered_iff_weaklyContractible_coslices`（`FilteredDiagonalCriterion.lean:36`）と、本体の `isRightCofinal_constantDiagram_of_kappaFiltered`（`FilteredDiagonalCofinality.lean:64`）、`isWeaklyContractible_sliceUnder_of_kappaFiltered`（`KappaFilteredCoslices.lean:58`）を挙げている。

[原典の小節 Tag 02P8](https://kerodon.net/tag/02P8) の Proposition 9.1.1.18 は、無限基数κについて、κ-filtered、全κ-small図式の coslice がκ-filtered/filtered/弱可縮、全κ-small形状への対角が right cofinal、の5条件の同値。単独 Tag 02PJ の取得はタイムアウトしたため、同じ命題を掲載する小節で照合した。

Archive は `hκ : κ.IsRegular` と `Quasicategory C` を仮定し、κ-filtered と全κ-small図式の coslice の弱可縮性を iff で結ぶ。別の同じファイルの `isKappaFiltered_iff_constantDiagram_rightCofinal` は対角条件との iff。原典の任意の無限κより仮定が強く、この2つだけで5条件すべての一般版を得たとはしない。

本体で確認した上記2型は正則κでの必要方向だけ。逆方向を含む本体の同じ型は見つからなかった。案は partial の維持、理由を5条件に合わせて書き直し、「正則κでの必要方向は本体、逆方向の原稿は Archive」と区別すること。`FE/FilteredCriterionCore` の切り出しを推奨。P⁰ 閉包に9.1.1.18がある。

## 9.1.1.20 — own から partial へ変更する案

元行：`review/ch9.csv:10`。唯一の対応宣言は Archive の `isFilteredInfinity_iff_isContractibleKan`（`FilteredKanContractibility.lean:69`）。

[原典 Tag 02PL](https://kerodon.net/tag/02PL) は Kan 複体で filtered と可縮が同値。Archive の型も `KanComplex C` の下で `IsFilteredInfinity C ↔ IsContractibleKan C`。一般の準圏には広げていないので、数学の主張としては一致する。

ただしこの型がビルド外にある以上 own の根拠にしない。本体の `isWeaklyContractible_of_isFilteredInfinity`（`FilteredWeakContractibility.lean:65`）と `isWeaklyContractible_iff_isContractibleKan`（`KanComplexes/HomotopyGroups/WeakContractibleKan.lean:40`）の型を合わせると **filtered Kan ⇒ 可縮 Kan** の方向に当たる。逆向きを含む同じ名前付き iff は探索で確認できなかった。案は partial とし、この本体の一方向を示して Archive の iff を参考に分離すること。9.1.1.20は今回のP⁰閉包にはないが、既存表の誤った own を直すためにも小さい復帰候補として記録する。

## 9.1.5.7 — partial を維持する案

元行：`review/ch9.csv:45`。Archive の `isFilteredInfinity_iff_constantDiagram_rightCofinal`（`FilteredDiagonalCriterion.lean:49`）と、本体の `isRightCofinal_constantDiagram_of_filtered`（`FilteredDiagonalCofinality.lean:57`）、`coherentFilteredLimitExchangeShape_finite`（`CoherentFiniteLimitExchange.lean:26`）を挙げている。

[原典 Tag 05XW](https://kerodon.net/tag/05XW) では filtered、全有限単体集合への対角の right cofinality、適切な非可算正則λでの小空間の有限極限と余極限の交換（存在版・全称版）が同値。

Archive の iff は最初の二条件の同値であり、交換から filtered への逆向きやλの条件まで含まない。本体の `smallSpaceFilteredColimit_map_isLimit_finite`（`UniversalityOfColimits/FilteredColimitFiniteLimitPreservation.lean:40`）は、filtered な準圏B上の空間値関手の余極限関手が有限形状の極限錐を保つ型。そこから上記 `coherentFilteredLimitExchangeShape_finite` は元の指定された点ごとの錐族へ戻す。旧 native cospan の特定座標に限定されず、交換の必要方向の本体として使えるが、原典の四条件の iff とは異なる。

案は partial を維持し、Archive の iff を本体の証拠と分離すること。復帰候補は対角判定の逆向きだけで、一般交換を得るために旧経路1,726本を戻す必要があるとは言えない。P⁰ 閉包に9.1.5.7がある。

## 9.1.8.11 — 理由欄の Archive 言及だけ

元行：`review/ch9.csv:85`。宣言欄は本体の `isKappaFiltered_of_isTerminalVertex` と `idemShape_isKappaFiltered`。理由欄で Archive の `isKappaFiltered_iff_constantDiagram_rightCofinal` を別の判定として言及する。

Archive の型は全κ-small形状への対角の right cofinality による判定であり、終対象・κ-small性・冪等完備性等を比較するこの行の不足方向の代わりにはならない。partial を維持し、Archive の言及は同じ主張の候補として数えない案。今回その原典の全条件の再監査はしていない。

## 旧 F2 表記で検索されたが Archive 参照ではない行

9.1.2.12 は旧 Core/Filtered の本体パス、9.2.8.3 は理由に旧名前空間の記載、9.7.2.3・9.7.2.8 は F2 を含む現本体ファイル名が一致したもの。これらは Archive のパスも同じ Archive 宣言の引用もないため、上の4宣言行・1言及行には足さない。旧パス・名前の更新は別の表刷新の範囲。

この文書は型と原典の主張の比較・訂正案だけ。対応表・Lean は未変更。ビルド・kernel 検証はしていない。
