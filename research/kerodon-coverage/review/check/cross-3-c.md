# 第3章の交差抜き取り検査（-c）

- 対象表は main の `e3c1c6c0e`。抽出後の `abe0628ab` からの差分には章別 CSV・検査証拠の変更がない。
- 乱数の種は `0xabe0628a`。Python 3.14.7 の `random.Random(seed).sample` を使用。章を 1→2→3、区分を own・both・mathlib の合算→partial→none の順に取り、各母集団は番号の数値順に整列してから重複なしで抽出した。
- 独立照合では抽出に元表の区分を使い、引用の宣言名を段1・段1′および章別 kernel evidence の型の取得に使った。元表の理由は独立判定を固定した後に読んだ。Kerodon 本文と型・定義本体を照らし、必要な候補の型を追加確認した。
- §8.1 の直接対応を partial の基準とした。差は対応区分で数え、同じ区分を支える引用の補足は別記した。§8.4 の停止基準は own・both・mathlib 群の比較後の差に適用する。

| 元の区分 | 母集団 | 抽出 | 独立照合の差 | 比較後の差 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 65 | 20 | 0/20（0%） | 0/20（0%） |
| partial | 121 | 10 | 4/10（40%） | 4/10（40%） |
| none | 153 | 10 | 2/10（20%） | 2/10（20%） |

比較後の own・both・mathlib の差は1割以下。partial・none の差は §8.2 の一括見直し用に記録した。

## own・both・mathlib

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [3.1.1.1](https://kerodon.net/tag/00T1) | mathlib | mathlib | mathlib | — | 任意の単体集合間の f。fibration_iff は J に対する RLP、J は n>0 の全ホーン包含。名前空間に Quillen が入るが型には ModelCategory SSet の仮定がない。 `SSet.modelCategoryQuillen.fibration_iff` (`Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:91`), `SSet.modelCategoryQuillen.J` (`Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:48`) |
| [3.1.2.1](https://kerodon.net/tag/00UH) | mathlib | mathlib | mathlib | — | 任意の単体集合間の射。anodyneExtensions=J.rlp.llp は弱飽和で J を含み、retracts/transfiniteCompositions/pushouts による生成式が最小性を与える。生成式の coproducts は同時付着の表示。 `SSet.anodyneExtensions` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean:75`), `SSet.anodyneExtensions_eq_retracts_transfiniteCompositions` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean:114`) |
| [3.1.3.3](https://kerodon.net/tag/00TM) | mathlib | mathlib | mathlib | — | 単射 i と Kan 複体 X。instFibrationAppPreOfMonoOfKanComplex は指定の Fun(B,X)→Fun(A,X) が Fibration。 `SSet.instFibrationAppPreOfMonoOfKanComplex` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/PushoutProduct.lean:148`) |
| [3.1.3.6](https://kerodon.net/tag/00UT) | own | own | own | — | アノダイン i と Kan 標的 X。trivialKanFibration_pre_of_anodyne は指定の前合成が TrivialKanFibration。 `SerrePositivity.InfinityCategories.HomotopyLimits.trivialKanFibration_pre_of_anodyne` (`SerrePositivity/InfinityCategories/HomotopyLimits/KanSourceReplacement.lean:25`) |
| [3.1.5.9](https://kerodon.net/tag/00TX) | own | own | own | — | 単体集合間の f。functorVertex f を internal Hom の 0-単体に取り、SSet.π₀.mk が指定ホモトピー類を返す。 `SerrePositivity.InfinityCategories.functorVertex` (`SerrePositivity/InfinityCategories/Core/Equivalence.lean:26`), `SSet.π₀.mk` (`Mathlib/AlgebraicTopology/SimplicialSet/PiZero.lean:57`) |
| [3.1.7.14](https://kerodon.net/tag/00UP) | own | own | own | — | アノダイン i。isWeakHomotopyEquivalence はすべての Kan 標的への前合成の成分全単射。homotopyEquivalence_pre_of_anodyne の写像空間同値もこれを直接与える。 `SerrePositivity.InfinityCategories.HomotopyLimits.homotopyEquivalence_pre_of_anodyne` (`SerrePositivity/InfinityCategories/HomotopyLimits/KanSourceReplacement.lean:41`), `SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence` (`SerrePositivity/EInfinity/FrameHom/AnodyneWeakDetection.lean:67`) |
| [3.2.1.3](https://kerodon.net/tag/050Q) | mathlib | mathlib | mathlib | — | 任意の部分複体 K を相対始域に取る。RelativeMorphism.Homotopy.rel は K×Δ¹ への制限が K への射影を通じて指定した共通制限になる等式。因子は端点での制限により決まる。 `SSet.RelativeMorphism.Homotopy` (`Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean:87`) |
| [3.2.2.1](https://kerodon.net/tag/00VK) | own | own | own | — | 単体集合 B と A⊆B。cofiberQuotient は A の一点への射との pushout、cofiberQuotient_condition と cofiber が頂点を基点にする指定の対象を与える。 `SerrePositivity.PointedObject.cofiber` (`SerrePositivity/Spectra/Pointed/Cofiber.lean:35`), `SerrePositivity.PointedObject.cofiberQuotient` (`SerrePositivity/Spectra/Pointed/Cofiber.lean:38`), `SerrePositivity.PointedObject.cofiberQuotient_condition` (`SerrePositivity/Spectra/Pointed/Cofiber.lean:41`) |
| [3.2.2.6](https://kerodon.net/tag/00VQ) | own | own | own | — | 点付き Kan 複体。equivPiZero は KanHomotopyZero の類と π₀ X の集合の同値。群構造は正次数用の別の interface。 `SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.equivPiZero` (`SerrePositivity/InfinityCategories/Kan/HomotopyDegreeZero.lean:51`), `SerrePositivity.InfinityCategories.Kan.KanHomotopyZero` (`SerrePositivity/InfinityCategories/Kan/HomotopyDegreeZero.lean:33`) |
| [3.2.5.3](https://kerodon.net/tag/00WG) | own | own | own | — | Kan fibration と点付き Kan 基底。connecting と connectingHom は最後の面を取るので Kerodon 3.2.5.1 の第0面の規約を別に照合。零次数は pointedConnectingZero_inverse_edge で底のループを反転し、次数1は FiberTriangle.connecting_product で第0面だけを残す。次数 m≥2 は SphericalFiberLift.alternatingClass_connecting で第0面だけを残し (−1)^(m+1) を掛ける。正次数ではこの補正も群準同型を保つ。 `SerrePositivity.InfinityCategories.Kan.connecting` (`SerrePositivity/InfinityCategories/Kan/FibrationBoundary.lean:412`), `SerrePositivity.InfinityCategories.Kan.connectingHom` (`SerrePositivity/InfinityCategories/Kan/FibrationMultiplication.lean:206`)。追加確認 `SerrePositivity/KST/Spectra/ReverseComponentConnecting.lean:31`, `SerrePositivity/InfinityCategories/Kan/FiberTriangleConnecting.lean:31`, `SerrePositivity/InfinityCategories/Kan/SphericalFiberRelation.lean:105` |
| [3.2.7.1](https://kerodon.net/tag/00WV) | own | own | own | — | Kan 複体間の f。正次数の全基点での π 同型と成分全単射から KanPiIsomorphism と成分全射を得て Whitehead を適用。逆は kanPiIsomorphism_of_homotopyEquivalence と同じ同値の mapPiZero_bijective。 `SerrePositivity.InfinityCategories.HomotopyLimits.homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective` (`SerrePositivity/InfinityCategories/HomotopyLimits/KanWhiteheadComparison.lean:93`), `SerrePositivity.InfinityCategories.HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence` (`SerrePositivity/InfinityCategories/HomotopyLimits/KanWhiteheadComparison.lean:51`) |
| [3.3.2.5](https://kerodon.net/tag/00XN) | mathlib | mathlib | mathlib | — | 任意の X と n。sd が非空部分集合の順序圏の nerve を与え、ex は sd の表現可能図式による Hom を次数ごとに取る。構造写像は指定の sd 写像での前合成。 `SSet.ex` (`Mathlib/AlgebraicTopology/SimplicialSet/Subdivision.lean:49`), `SimplexCategory.sd` (`Mathlib/AlgebraicTopology/SimplicialSet/Subdivision.lean:39`) |
| [3.3.4.3](https://kerodon.net/tag/00YU) | own | own | own | — | 任意の X。subdivisionLastVertexMap の各頂点は部分集合の最大元。exUnitAt はこの写像と σ の合成を使い、sd⊣Ex で随伴する単体写像。 `SerrePositivity.KST.Comparison.subdivisionLastVertexMap` (`SerrePositivity/KST/Comparison/SubdivisionLastVertexMap.lean:29`), `SerrePositivity.KST.Comparison.exUnitAt` (`SerrePositivity/KST/Comparison/ExUnit.lean:29`) |
| [3.3.6.6](https://kerodon.net/tag/00ZG) | own | own | own | — | 任意の f に J.rlp を仮定。exInfinity_map_rlp が同じ関手の f の像に J.rlp を返す。Kan 基底の追加仮定はない。 `SerrePositivity.KST.Comparison.exInfinity_map_rlp` (`SerrePositivity/KST/Comparison/ExInfinityFibrations.lean:45`) |
| [3.3.6.9](https://kerodon.net/tag/00ZK) | own | own | own | — | 任意の単体集合 X。exInfinity_kanComplex が Ex∞(X) 自体に KanComplex を返す。 `SerrePositivity.KST.Comparison.exInfinity_kanComplex` (`SerrePositivity/KST/Comparison/ExInfinityKan.lean:55`) |
| [3.4.0.2](https://kerodon.net/tag/0109) | own | own | own | — | 二つの指定脚の J.rlp と三つの比較射の弱同値。fibrantCospanMap_localized_isIso は同じ pullback 比較に適用できる。弱同値から局所化可逆性は weakHomotopyEquivalence_anodyneQ_isIso、逆は KanTestDetection と写像空間の成分類の比較で同じ射を検査する。 `SerrePositivity.KST.Comparison.fibrantCospanMap_localized_isIso` (`SerrePositivity/KST/Comparison/FibrantCospanInvariance.lean:30`)。追加確認 `SerrePositivity/KST/Fibration/WeakHomotopyAnodyneComparison.lean:18`, `SerrePositivity/HomotopicalAlgebra/Simplicial/KanTestDetection.lean:111`, `SerrePositivity/InfinityCategories/F1/KanModels/KanAnodyneLocalization.lean:24` |
| [3.4.1.2](https://kerodon.net/tag/010N) | own | own | own | — | 弱同値と Kan fibration による指定分解。alternative_fiber は局所化可逆な第一脚を許し、厳密 pullback への指定比較の局所化可逆性と IsHomotopyPullback を同値にする。第一脚・結論の局所化条件はいずれも Kan テストで弱同値に対応する。 `SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative` (`SerrePositivity/KST/Comparison/AlternativePullback.lean:63`), `SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber` (`SerrePositivity/KST/Comparison/AlternativeFiberCriterion.lean:30`) |
| [3.4.5.4](https://kerodon.net/tag/0124) | own | own | own | — | 任意の X。freeDegeneraciesNormalForm は全射と元の単体の組、augmentation はその全射による評価。localized_isIso がこの augmentation に適用され、Kan テストによる弱同値判定と一致。 `SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso` (`SerrePositivity/KST/Comparison/FreeDegeneraciesEquivalence.lean:29`), `SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation` (`SerrePositivity/KST/Comparison/FreeDegeneracies.lean:61`) |
| [3.6.1.1](https://kerodon.net/tag/0131) | mathlib | mathlib | mathlib | — | 任意の単体集合。Finite は非退化単体全体の有限性。finite_of_hasDimensionLT が本文の二条件からこれを与え、逆は hasDimensionLT_of_finite と全次数の Finite (X.obj n) の instance。 `SSet.Finite` (`Mathlib/AlgebraicTopology/SimplicialSet/Finite.lean:32`), `SSet.hasDimensionLT_of_finite` (`Mathlib/AlgebraicTopology/SimplicialSet/Finite.lean:57`), `SSet.finite_of_hasDimensionLT` (`Mathlib/AlgebraicTopology/SimplicialSet/Finite.lean:44`) |
| [3.6.1.10](https://kerodon.net/tag/03X6) | own | own | own | — | 有限単体集合 X。finiteInternalHom_preservesFilteredColimits が ihom X に filtered colimit の保存を与える。 `SerrePositivity.InfinityCategories.F2.finiteInternalHom_preservesFilteredColimits` (`SerrePositivity/InfinityCategories/Core/FilteredExchange/FiniteInternalHomContinuity.lean:40`) |

## partial

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [3.2.2.10](https://kerodon.net/tag/00VU) | partial | partial | partial | component | instGroup と境界充填判定、n≥2 の CommGroup が存在する。任意の群演算が指定の単位と交代積の条件を満たせば一致するという一意性までは確認できなかった。 `SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup` (`SerrePositivity/InfinityCategories/Kan/HomotopyGroups.lean:101`), `SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.instGroup` (`SerrePositivity/InfinityCategories/Kan/HomotopyGroups.lean:243`), `SerrePositivity.InfinityCategories.Kan.instCommGroupKanHomotopyGroupHAddNatOfNat` (`SerrePositivity/InfinityCategories/Kan/Commutativity.lean:466`), `SerrePositivity.InfinityCategories.Kan.SphericalBoundary.boundary_filler_iff` (`SerrePositivity/InfinityCategories/Kan/SphericalBoundaryMap.lean:74`) |
| [3.2.4.11](https://kerodon.net/tag/050V) | partial | partial | partial | special | LastHornContraction.homotopy を σ₀ と後合成すると最後のホーンの場合の零ホモトピーが得られる。他の全 i を量化した零ホモトピーの型は確認できなかった。 `SerrePositivity.InfinityCategories.Kan.LastHornContraction.homotopy` (`SerrePositivity/InfinityCategories/Kan/LastHornContraction.lean:139`) |
| [3.2.6.7](https://kerodon.net/tag/00WT) | partial | own | own | — | Kerodon 3.2.5.5 の作用は第0面で計算する境界写像。pointedConnectingZero_inverse_edge により、基点から出る lift の終点の成分は Lean の connecting を底ループの逆元に適用した値。componentConnecting_one_at と componentConnecting_kernel で逆元が π₁(f) の像に入ることと同値で、群準同型の像は逆元で閉じるため指定の stabilizer が同じ像。 `SerrePositivity.InfinityCategories.Kan.componentConnecting_kernel` (`SerrePositivity/InfinityCategories/Kan/FiberComponents.lean:119`)。追加確認 `SerrePositivity/KST/Spectra/ReverseComponentConnecting.lean:31`, `SerrePositivity/InfinityCategories/Kan/FiberComponents.lean:69` |
| [3.3.1.4](https://kerodon.net/tag/00XX) | partial | partial | partial | special | Nonsingular を仮定した nonDegenerate_δ は非退化単体の面が非退化という成分を返す。一般の braced 条件での閉性と半単体集合の構成は確認できなかった。 `SSet.nonDegenerate` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:44`), `SSet.nonDegenerate_δ` (`Mathlib/AlgebraicTopology/SimplicialSet/Nonsingular.lean:91`) |
| [3.3.5.2](https://kerodon.net/tag/0103) | partial | own | own | — | 単一段の exUnitAt_anodyne と exUnitAt_naturality を確認。自然性正方形の水平二射はともに弱同値なので IsWeakHomotopyEquivalence.comp と両側の cancel を適用して f と Ex(f) の iff を得る。Ex∞ の式もあるが単一段の根拠は前者。 `SerrePositivity.KST.Comparison.exInfinity_map_localized_isIso_iff` (`SerrePositivity/KST/Comparison/ExInfinityLocalization.lean:66`), `SerrePositivity.KST.Comparison.exUnitAt_anodyne` (`SerrePositivity/KST/Comparison/ExUnitAnodyne.lean:40`)。追加確認 `SerrePositivity/KST/Comparison/ExUnit.lean:56`, `SerrePositivity/InfinityCategories/F1B/Homotopy/WeakHomotopy.lean:62` |
| [3.4.1.5](https://kerodon.net/tag/010Q) | partial | own | own | — | alternative_fiber で q を q の後に恒等 Kan fibration を合成する形に取れる。恒等射の厳密 pullback は X₁ で、指定比較は q'。Kan テストの対応を通して、正方形の homotopy pullback 性と q' の弱同値性の iff が得られる。 `SerrePositivity.KST.Comparison.IsHomotopyPullback` (`SerrePositivity/KST/Comparison/HomotopyPullback.lean:134`), `SerrePositivity.KST.Comparison.pullback_localized_isIso` (`SerrePositivity/KST/Comparison/ArbitraryBasePullback.lean:32`)。追加確認 `SerrePositivity/KST/Comparison/AlternativeFiberCriterion.lean:30` |
| [3.5.1.13](https://kerodon.net/tag/04GZ) | partial | partial | partial | stronger-hyp | KanPiIsomorphism は各基点・全次数の全単射を要求する。成分の全射性も仮定すれば、本文が要求する m<n の全単射と m=n の全射が得られる。有限の次数 n で切った定義そのものは確認できなかった。 `SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism` (`SerrePositivity/InfinityCategories/Kan/HomotopyIsomorphism.lean:32`) |
| [3.5.2.1](https://kerodon.net/tag/04HC) | partial | partial | partial | stronger-hyp | fibration_rlp_of_piIsomorphism は非空な Kan 源と Kan 基底、全次数の π 同型を仮定してすべての単射への RLP を返す。従って (3),(4) の強い仮定版。有限次数の仮定や fiber 側との iff は未確認。 `SerrePositivity.InfinityCategories.F1.Pointed.fibration_rlp_of_piIsomorphism` (`SerrePositivity/InfinityCategories/F1/Pointed/AcyclicFibrationLifting.lean:161`) |
| [3.5.2.13](https://kerodon.net/tag/04HG) | partial | none | none | — | instFibrationMapIhom は f 自体が Fibration の場合に写像空間の Fibration を与える。m+n の連結性から n の連結性を返す型ではない。 `SSet.instFibrationMapIhom` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/PushoutProduct.lean:143`) |
| [3.6.6.11](https://kerodon.net/tag/0224) | partial | partial | partial | special | IsCoveringMap.liftHomotopy と lifts・zero の等式は、離散な一定 fiber を持つ被覆のホモトピー持ち上げを任意の試験空間に与える。一般の束では確認できなかった。 `IsCoveringMap.liftHomotopy` (`Mathlib/Topology/Homotopy/Lifting.lean`) |

## none

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [3.3.5.9](https://kerodon.net/tag/00Z9) | none | partial | partial | special | Mathlib の anodyneExtensions.horn_ι を n=1,i=0 に取ると、J が一元集合である場合の空集合頂点の包含に一致。upperMissingCube は高次元で上面を一枚除く別の部分複体で、全体集合頂点を除く一般の型は確認できなかった。 —。追加確認 `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean:88` |
| [3.4.2.6](https://kerodon.net/tag/032P) | none | none | none | — | opFunctor と opposite_map_isWeakHomotopyEquivalence、doubleMappingCylinder の比較を探索。homotopy pushout の指定正方形を反対にしたときの iff を結論する型は確認できなかった。 — |
| [3.4.3.3](https://kerodon.net/tag/011M) | none | none | none | — | spanPushout_vertex_homotopyPullback は上下の厳密 pushout と縦の引戻し性を入力して残りの側面の引戻し性を返す。本文の四側面と下面から上面の homotopy pushout を返す向きは確認できなかった。 — |
| [3.5.1.15](https://kerodon.net/tag/04H1) | none | partial | partial | component | continuousKanReplacement とその単位は f の自然な置換正方形、二つの Kan 対象と弱同値な水平辺を与える。置換に依存しない有限次数 n-connective の述語・比較は未確認。 —。追加確認 `SerrePositivity/InfinityCategories/F1/Yoneda/PresheafDensity/Support/ContinuousKanFilling.lean:39`, `SerrePositivity/InfinityCategories/F1/Yoneda/PresheafDensity/Support/ContinuousKanWeakEquivalence.lean:26` |
| [3.5.1.28](https://kerodon.net/tag/04H9) | none | none | none | — | KanPiIsomorphism.comp は各基点の全次数の全単射の合成。成分全射や境界次数の全射といった n-connective の有限条件を含めた三つの規則は確認できなかった。 — |
| [3.5.4.22](https://kerodon.net/tag/053C) | none | none | none | — | SSet.cosk と coskAdj、境界の TrivialKanFibration 判定を探索。指定の修正 cosk° と cosk_(n+1) からの比較射の型は確認できなかった。 — |
| [3.5.4.26](https://kerodon.net/tag/053H) | none | none | none | — | SSet.cosk の単位と Kan fibration を探索。通常の coskeleton の随伴の型には、本文の修正 cosk° への単位の Kan 性はない。 — |
| [3.5.8.9](https://kerodon.net/tag/055V) | none | none | none | — | PostnikovTower、KanFibrationTower、Eilenberg–MacLane を探索。DG 代数の Postnikov 余切断や一般の Kan 塔はあるが、任意の Kan X の指定塔と π_n からのファイバー同定の型は確認できなかった。 — |
| [3.5.9.1](https://kerodon.net/tag/055Z) | none | none | none | — | Is0TruncatedSpace と KanPiIsomorphism を確認。空間の対象としての離散性や全次数の全単射の述語はあるが、射に対する指定の n+1 次単射条件と高次数全単射条件を束ねる型は確認できなかった。 — |
| [3.5.9.32](https://kerodon.net/tag/056U) | none | none | none | — | KanPiIsomorphism、relative functor homotopy pullback、境界充填を探索。n-truncated の有限条件と (n+1)-connective 全射または標準境界に対する指定の正方形を結ぶ型は確認できなかった。 — |

## 差があった行の比較

### [3.2.6.7](https://kerodon.net/tag/00WT)（-a2 `partial`、独立 `own`、比較後 `own`）

- -a2 の理由を照合した記録。componentConnecting_kernel は、指定ファイバー成分に戻る底のループ類と全空間の基本群の像を同定する。π₁ の全成分上の作用としての安定化群は未確認。
- 今回の判定。-a2 の componentConnecting_kernel に pointedConnectingZero_inverse_edge を加えると、本文が作用を特徴づける第0面の計算と照合できる。第0面と最後の面の差は底のループの逆元で、像の部分群では逆元を取っても所属が同値。

### [3.3.5.2](https://kerodon.net/tag/0103)（-a2 `partial`、独立 `own`、比較後 `own`）

- -a2 の理由を照合した記録。Ex∞ 版の anodyne 局所化同型の同値と、単一の Ex の単位の anodyne 性を確認。単一の Ex による弱ホモトピー同値の両方向を述べる宣言は未確認。
- 今回の判定。-a2 が確認した単一段の単位のアノダイン性に exUnitAt_naturality を合わせると、同じ f と Ex(f) の合成が一致する。弱同値の comp と二つの cancel により両向きを得る。

### [3.4.1.5](https://kerodon.net/tag/010Q)（-a2 `partial`、独立 `own`、比較後 `own`）

- -a2 の理由を照合した記録。一般の引き戻しの比較の型と、Kan fibration に沿う弱同値の引き戻しはある。右脚が弱同値の正方形で左脚の弱同値性とホモトピー引き戻し性を直接同値にする宣言は未確認。
- 今回の判定。-a2 の引戻しの基底変更結果より直接的な isHomotopyPullback_iff_alternative_fiber を、右脚 q の分解 (q,id) と id の pullback に適用する。比較射 k に左脚 q' を代入するので、指定二条件の iff が得られる。

### [3.5.2.13](https://kerodon.net/tag/04HG)（-a2 `partial`、独立 `none`、比較後 `none`）

- -a2 の理由を照合した記録。Kan fibration による内部 Hom の後合成が fibration になる。f の有限次数の連結度がそのまま保たれる結論は未確認。
- 今回の判定。-a2 の候補が直接与えるのは Fibration 性で、本文のどの次数についても π の全射・全単射を述べていない。Kan fibration を追加してもその型は n-connectivity の結論にならない。

### [3.3.5.9](https://kerodon.net/tag/00Z9)（-a2 `none`、独立 `partial`、比較後 `partial`）

- -a2 の理由を照合した記録。orderSubtypeNerve_anodyne は部分順序の指定点を通る上向きの変形を要求する。上面一枚を欠く立方体の補題もあるが、最大頂点だけを除いた部分順序集合の nerve の指定包含とは異なる。
- 今回の判定。-a2 が退けた orderSubtypeNerve_anodyne の仮定では一般の場合は埋まらない。J が一元集合のときは指定包含そのものが標準 1 単体の第0ホーンの包含なので、horn_ι の直接の特例。

### [3.5.1.15](https://kerodon.net/tag/04H1)（-a2 `none`、独立 `partial`、比較後 `partial`）

- -a2 の理由を照合した記録。Ex∞ と弱同値の保存・反映はある。任意の射を Kan 置換の正方形で n-connective と判定する述語と選択独立性は見つからない。
- 今回の判定。-a2 の指摘どおり n-connective の述語と選択独立性は未確認。一方 continuousKanReplacement の自然変換の両端は本文の正方形の Kan 置換と弱同値を与えるので、構成のこの成分を確認できる。

## 追加の kernel 型

追加の `#check` は既存モジュールの import だけを使い、章別3回と補足2回に分けて共有鍵を取得した。各回の上限は500秒、実測の最長は約15秒。

```lean
SerrePositivity.KST.Comparison.exUnitAt_anodyne : ∀ (X : SSet),
  SSet.anodyneExtensions (SerrePositivity.KST.Comparison.exUnitAt X)
@SerrePositivity.KST.Comparison.exUnitAt_naturality : ∀ {X Y : SSet} (f : X ⟶ Y),
  CategoryTheory.CategoryStruct.comp f (SerrePositivity.KST.Comparison.exUnitAt Y) =
    CategoryTheory.CategoryStruct.comp (SerrePositivity.KST.Comparison.exUnitAt X) (SSet.ex.map f)
@SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber : ∀ {A X Y B E P : SSet} {a : A ⟶ X}
  {b : A ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B} (sq : CategoryTheory.CommSq a b f g) (i : X ⟶ E),
  CategoryTheory.IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map i) →
    ∀ (p : E ⟶ B),
      SSet.modelCategoryQuillen.J.rlp p →
        CategoryTheory.CategoryStruct.comp i p = f →
          ∀ {r : P ⟶ Y} {s : P ⟶ E},
            CategoryTheory.IsPullback r s g p →
              ∀ (k : A ⟶ P),
                CategoryTheory.CategoryStruct.comp k r = b →
                  CategoryTheory.CategoryStruct.comp k s = CategoryTheory.CategoryStruct.comp a i →
                    (SerrePositivity.KST.Comparison.IsHomotopyPullback sq ↔
                      CategoryTheory.IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map k))
@SerrePositivity.KST.Fibration.weakHomotopyEquivalence_anodyneQ_isIso : ∀ {X Y : SSet} (f : X ⟶ Y),
  SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence f →
    CategoryTheory.IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map f)
@SerrePositivity.SimplicialModel.KanTestDetection.anodyneQ_isIso_iff_tests : ∀ {X Y : SSet} (f : X ⟶ Y),
  CategoryTheory.IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map f) ↔
    SerrePositivity.SimplicialModel.KanTestDetection.Tests f
@SerrePositivity.InfinityCategories.anodyneHomClassToPiZero : {A Z : SSet} →
  [Z.KanComplex] → SerrePositivity.SimplicialModel.HomotopyClasses.obj A Z → (A ⟹ Z).π₀
SerrePositivity.InfinityCategories.F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence : ∀ (X : SSet),
  SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
    (SerrePositivity.InfinityCategories.F2.continuousKanReplacementUnit.app X)
SerrePositivity.InfinityCategories.F2.continuousKanReplacement_kanComplex : ∀ (X : SSet),
  (SerrePositivity.InfinityCategories.F2.continuousKanReplacement.obj X).KanComplex
@IsCoveringMap.liftHomotopy : {E : Type u_1} →
  {X : Type u_2} →
    {A : Type u_3} →
      [inst : TopologicalSpace E] →
        [inst_1 : TopologicalSpace X] →
          [inst_2 : TopologicalSpace A] →
            {p : E → X} →
              IsCoveringMap p →
                (H : C(↑unitInterval × A, X)) →
                  (f : C(A, E)) → (∀ (a : A), H (0, a) = p (f a)) → C(↑unitInterval × A, E)
@SerrePositivity.KST.Spectra.pointedConnectingZero_inverse_edge : ∀ {E B : SerrePositivity.PointedSimplicialSet}
  (p : E ⟶ B) [inst : HomotopicalAlgebra.Fibration (CategoryTheory.Under.Hom.right p)]
  [inst_1 : (CategoryTheory.Under.right B).KanComplex]
  (s :
    (CategoryTheory.Under.right B).PtSimplex 1
      ((CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Under.Hom.right p).app (Opposite.op { len := 0 })))
        E.basepoint))
  (a :
    (CategoryTheory.Under.right (SerrePositivity.KST.Spectra.pointedFiber p)).PtSimplex 0
      (SerrePositivity.KST.Spectra.pointedFiber p).basepoint)
  (T : SSet.stdSimplex.obj { len := 1 } ⟶ CategoryTheory.Under.right E),
  CategoryTheory.CategoryStruct.comp T (CategoryTheory.Under.Hom.right p) = s.map →
    CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 0) T =
        CategoryTheory.CategoryStruct.comp a.map
          (CategoryTheory.Under.Hom.right (SerrePositivity.KST.Spectra.pointedFiberι p)) →
      CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ 1) T = SSet.const E.basepoint →
        SerrePositivity.KST.Spectra.pointedConnectingZero p
            ((SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso 0
                  (CategoryTheory.Iso.refl (CategoryTheory.Under.right B)) ⋯)
                (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk s))⁻¹ =
          SerrePositivity.InfinityCategories.Kan.KanHomotopy.mk 0 a
@SerrePositivity.InfinityCategories.Kan.componentConnecting_kernel : ∀ {E B : SSet} [inst : E.KanComplex]
  [inst_1 : B.KanComplex] (p : E ⟶ B) [inst_2 : HomotopicalAlgebra.Fibration p] (e : E.obj (Opposite.op { len := 0 }))
  (b : B.obj (Opposite.op { len := 0 }))
  (hb : (CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e = b)
  (c :
    SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup B 0
      ((CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e)),
  SerrePositivity.InfinityCategories.Kan.componentConnecting p e b hb c =
      SerrePositivity.InfinityCategories.Kan.componentConnecting p e b hb 1 ↔
    ∃ d, (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map p ⋯) d = c
@SerrePositivity.InfinityCategories.Kan.FiberTriangle.connecting_product : ∀ {E B : SSet} {p : E ⟶ B}
  [inst : HomotopicalAlgebra.Fibration p] [inst_1 : E.KanComplex] [inst_2 : B.KanComplex]
  {e : E.obj (Opposite.op { len := 0 })}
  {s : B.PtSimplex 2 ((CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e)}
  {a :
    Fin 3 →
      (SerrePositivity.InfinityCategories.Kan.KanFiber p
            ((CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e)).PtSimplex
        1 (SerrePositivity.InfinityCategories.Kan.fiberPoint p e)}
  (T : SerrePositivity.InfinityCategories.Kan.SphericalFiberLift p e s a),
  (SerrePositivity.InfinityCategories.Kan.connectingHom p e 0)
      (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk s) =
    (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk (a 1))⁻¹ *
        SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk (a 2) *
      SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk (a 0)
@SerrePositivity.InfinityCategories.Kan.SphericalFiberLift.alternatingClass_connecting : ∀ {E B : SSet} {p : E ⟶ B}
  [inst : HomotopicalAlgebra.Fibration p] [inst_1 : E.KanComplex] [inst_2 : B.KanComplex]
  {e : E.obj (Opposite.op { len := 0 })} {n : ℕ}
  {s : B.PtSimplex (n + 3) ((CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e)}
  {a :
    Fin (n + 4) →
      (SerrePositivity.InfinityCategories.Kan.KanFiber p
            ((CategoryTheory.ConcreteCategory.hom (p.app (Opposite.op { len := 0 }))) e)).PtSimplex
        (n + 2) (SerrePositivity.InfinityCategories.Kan.fiberPoint p e)}
  (T : SerrePositivity.InfinityCategories.Kan.SphericalFiberLift p e s a),
  SerrePositivity.InfinityCategories.Kan.SphericalBoundary.alternatingClass a =
    (-1) ^ (n + 3) •
      Additive.ofMul
        ((SerrePositivity.InfinityCategories.Kan.connectingHom p e (n + 1))
          (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.mk s))
```

## 元の kernel evidence から照合した型

`ch3-kernel-evidence.json`、段1、段1′から own・both・mathlib 群の型を取得した。表示用に空白を整えた。

### 3.1.1.1

```lean
@SSet.modelCategoryQuillen.fibration_iff.{u_1} : ∀ {X Y : SSet.{u_1}} (f : Quiver.Hom.{u_1, u_1 + 1} X Y), HomotopicalAlgebra.Fibration.{u_1, u_1 + 1} f ↔ CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} f
SSet.modelCategoryQuillen.J.{u_1} : CategoryTheory.MorphismProperty.{u_1, u_1 + 1} SSet.{u_1}
```

### 3.1.2.1

```lean
SSet.anodyneExtensions.{u_1} : CategoryTheory.MorphismProperty.{u_1, u_1 + 1} SSet.{u_1}
SSet.anodyneExtensions_eq_retracts_transfiniteCompositions.{u_1} : Eq.{u_1 + 2} SSet.anodyneExtensions.{u_1} (CategoryTheory.MorphismProperty.retracts.{u_1, u_1 + 1} (CategoryTheory.MorphismProperty.transfiniteCompositions.{u_1, u_1, u_1 + 1} (CategoryTheory.MorphismProperty.pushouts.{u_1, u_1 + 1} (CategoryTheory.MorphismProperty.coproducts.{u_1, u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1}))))
```

### 3.1.3.3

```lean
@SSet.instFibrationAppPreOfMonoOfKanComplex.{u_1} : ∀ {A B : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} A B) [CategoryTheory.Mono.{u_1, u_1 + 1} i] (X : SSet.{u_1}) [SSet.KanComplex.{u_1} X], HomotopicalAlgebra.Fibration.{u_1, u_1 + 1} (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} i) X)
```

### 3.1.3.6

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.trivialKanFibration_pre_of_anodyne.{u_1} : ∀ {A B : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} A B), SSet.anodyneExtensions.{u_1} i → ∀ (X : SSet.{u_1}) [SSet.KanComplex.{u_1} X], SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1} (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} i) X)
```

### 3.1.5.9

```lean
@SerrePositivity.InfinityCategories.functorVertex.{u_1} : {X Y : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X Y → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (X ⟹ Y) (Opposite.op.{1} { len := 0 })
@SSet.π₀.mk.{u_1} : {X : SSet.{u_1}} → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → SSet.π₀.{u_1} X
```

### 3.1.7.14

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.homotopyEquivalence_pre_of_anodyne.{u_1} : ∀ {A B : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} A B), SSet.anodyneExtensions.{u_1} i → ∀ (X : SSet.{u_1}) [SSet.KanComplex.{u_1} X], SerrePositivity.InfinityCategories.IsSimplicialHomotopyEquivalence.{u_1} (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} i) X)
@SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence.{u_1} : ∀ {A B : SSet.{u_1}} (f : Quiver.Hom.{u_1, u_1 + 1} A B), CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} f) → SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence.{u_1} f
```

### 3.2.1.3

```lean
@SSet.RelativeMorphism.Homotopy.{u_1} : {X Y : SSet.{u_1}} → {A : SSet.Subcomplex.{u_1} X} → {B : SSet.Subcomplex.{u_1} Y} → {φ : Quiver.Hom.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} A) (SSet.Subcomplex.toSSet.{u_1} B)} → SSet.RelativeMorphism.{u_1} A B φ → SSet.RelativeMorphism.{u_1} A B φ → Type u_1
```

### 3.2.2.1

```lean
@SerrePositivity.PointedObject.cofiber.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → [inst_1 : CategoryTheory.CartesianMonoidalCategory.{u_1, u_2} C] → {X Y : C} → (f : Quiver.Hom.{u_1, u_2} X Y) → [CategoryTheory.Limits.HasPushout.{u_1, u_2} f (CategoryTheory.SemiCartesianMonoidalCategory.toUnit.{u_1, u_2} X)] → SerrePositivity.PointedObject.{u_1, u_2} C
@SerrePositivity.PointedObject.cofiberQuotient.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → [inst_1 : CategoryTheory.CartesianMonoidalCategory.{u_1, u_2} C] → {X Y : C} → (f : Quiver.Hom.{u_1, u_2} X Y) → [inst_2 : CategoryTheory.Limits.HasPushout.{u_1, u_2} f (CategoryTheory.SemiCartesianMonoidalCategory.toUnit.{u_1, u_2} X)] → Quiver.Hom.{u_1, u_2} Y (CategoryTheory.Under.right.{u_1, u_2} (SerrePositivity.PointedObject.cofiber.{u_1, u_2} f))
@SerrePositivity.PointedObject.cofiberQuotient_condition.{u_1, u_2} : ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory.{u_1, u_2} C] {X Y : C} (f : Quiver.Hom.{u_1, u_2} X Y) [inst_2 : CategoryTheory.Limits.HasPushout.{u_1, u_2} f (CategoryTheory.SemiCartesianMonoidalCategory.toUnit.{u_1, u_2} X)], Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_2} f (SerrePositivity.PointedObject.cofiberQuotient.{u_1, u_2} f)) (CategoryTheory.CategoryStruct.comp.{u_1, u_2} (CategoryTheory.SemiCartesianMonoidalCategory.toUnit.{u_1, u_2} X) (CategoryTheory.Under.hom.{u_1, u_2} (SerrePositivity.PointedObject.cofiber.{u_1, u_2} f)))
```

### 3.2.2.6

```lean
@SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.equivPiZero.{u_1} : {X : SSet.{u_1}} → {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} → Equiv.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.{u_1} X x) (SSet.π₀.{u_1} X)
SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.{u_1} : (X : SSet.{u_1}) → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → Type u_1
```

### 3.2.5.3

```lean
@SerrePositivity.InfinityCategories.Kan.connecting.{u_1} : {E B : SSet.{u_1}} → (p : Quiver.Hom.{u_1, u_1 + 1} E B) → [inst : HomotopicalAlgebra.Fibration.{u_1, u_1 + 1} p] → [inst_1 : SSet.KanComplex.{u_1} B] → (e : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} E (Opposite.op.{1} { len := 0 })) → (n : ℕ) → SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.{u_1} B n ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} p (Opposite.op.{1} { len := 0 }))) e) → SerrePositivity.InfinityCategories.Kan.KanHomotopy.{u_1} (SerrePositivity.InfinityCategories.Kan.KanFiber.{u_1} p ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} p (Opposite.op.{1} { len := 0 }))) e)) n (SerrePositivity.InfinityCategories.Kan.fiberPoint.{u_1} p e)
@SerrePositivity.InfinityCategories.Kan.connectingHom.{u_1} : {E B : SSet.{u_1}} → (p : Quiver.Hom.{u_1, u_1 + 1} E B) → [inst : HomotopicalAlgebra.Fibration.{u_1, u_1 + 1} p] → [SSet.KanComplex.{u_1} E] → [inst_2 : SSet.KanComplex.{u_1} B] → (e : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} E (Opposite.op.{1} { len := 0 })) → (n : ℕ) → MonoidHom.{u_1, u_1} (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.{u_1} B (HAdd.hAdd.{0, 0, 0} n 1) ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} p (Opposite.op.{1} { len := 0 }))) e)) (SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.{u_1} (SerrePositivity.InfinityCategories.Kan.KanFiber.{u_1} p ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} p (Opposite.op.{1} { len := 0 }))) e)) n (SerrePositivity.InfinityCategories.Kan.fiberPoint.{u_1} p e))
```

### 3.2.7.1

```lean
@SerrePositivity.InfinityCategories.HomotopyLimits.homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.KanComplex.{u_1} X] [inst_1 : SSet.KanComplex.{u_1} Y] (f : Quiver.Hom.{u_1, u_1 + 1} X Y), SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism.{u_1} f → Function.Surjective.{u_1 + 1, u_1 + 1} (SSet.mapπ₀.{u_1} f) → SerrePositivity.InfinityCategories.IsSimplicialHomotopyEquivalence.{u_1} f
@SerrePositivity.InfinityCategories.HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.KanComplex.{u_1} X] [inst_1 : SSet.KanComplex.{u_1} Y] (f : Quiver.Hom.{u_1, u_1 + 1} X Y), SerrePositivity.InfinityCategories.IsSimplicialHomotopyEquivalence.{u_1} f → SerrePositivity.InfinityCategories.Kan.KanPiIsomorphism.{u_1} f
```

### 3.3.2.5

```lean
SSet.ex.{u_1} : @CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1})
SimplexCategory.sd.{u_1} : @CategoryTheory.Functor.{0, u_1, 0, u_1 + 1} SimplexCategory SimplexCategory.smallCategory SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1})
```

### 3.3.4.3

```lean
SerrePositivity.KST.Comparison.subdivisionLastVertexMap.{u_1} : Quiver.Hom.{u_1 + 1, u_1 + 1} SSet.sd.{u_1} (CategoryTheory.Functor.id.{u_1, u_1 + 1} SSet.{u_1})
SerrePositivity.KST.Comparison.exUnitAt.{u_1} : (X : SSet.{u_1}) → Quiver.Hom.{u_1, u_1 + 1} X (CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.ex.{u_1} X)
```

### 3.3.6.6

```lean
@SerrePositivity.KST.Comparison.exInfinity_map_rlp.{u_1} : ∀ {E B : SSet.{u_1}} (p : Quiver.Hom.{u_1, u_1 + 1} E B), CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} p → CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} (CategoryTheory.Functor.map.{u_1, u_1, u_1 + 1, u_1 + 1} SerrePositivity.KST.Comparison.exInfinity.{u_1} p)
```

### 3.3.6.9

```lean
SerrePositivity.KST.Comparison.exInfinity_kanComplex.{u_1} : ∀ (X : SSet.{u_1}), SSet.KanComplex.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SerrePositivity.KST.Comparison.exInfinity.{u_1} X)
```

### 3.4.0.2

```lean
@SerrePositivity.KST.Comparison.fibrantCospanMap_localized_isIso.{u_1} : ∀ {X E B X' E' B' : SSet.{u_1}} (f : Quiver.Hom.{u_1, u_1 + 1} X B) (p : Quiver.Hom.{u_1, u_1 + 1} E B), CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} p → ∀ (f' : Quiver.Hom.{u_1, u_1 + 1} X' B') (p' : Quiver.Hom.{u_1, u_1 + 1} E' B'), CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} p' → ∀ (a : Quiver.Hom.{u_1, u_1 + 1} X X') (b : Quiver.Hom.{u_1, u_1 + 1} E E') (c : Quiver.Hom.{u_1, u_1 + 1} B B'), Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} f c) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} a f') → Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} p c) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} b p') → CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} a) → CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} b) → CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} c) → ∀ (m : Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Limits.pullback.{u_1, u_1 + 1} f p) (CategoryTheory.Limits.pullback.{u_1, u_1 + 1} f' p')), Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} m (CategoryTheory.Limits.pullback.fst.{u_1, u_1 + 1} f' p')) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (CategoryTheory.Limits.pullback.fst.{u_1, u_1 + 1} f p) a) → Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} m (CategoryTheory.Limits.pullback.snd.{u_1, u_1 + 1} f' p')) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (CategoryTheory.Limits.pullback.snd.{u_1, u_1 + 1} f p) b) → CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} m)
```

### 3.4.1.2

```lean
@SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative.{u_1} : ∀ {P X Y Z T : SSet.{u_1}} {a : Quiver.Hom.{u_1, u_1 + 1} P X} {b : Quiver.Hom.{u_1, u_1 + 1} P Y} {f : Quiver.Hom.{u_1, u_1 + 1} X Z} {g : Quiver.Hom.{u_1, u_1 + 1} Y Z} (sq : CategoryTheory.CommSq.{u_1, u_1 + 1} a b f g) (i : Quiver.Hom.{u_1, u_1 + 1} Y T), SSet.anodyneExtensions.{u_1} i → ∀ (p : Quiver.Hom.{u_1, u_1 + 1} T Z), CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} p → ∀ (h : Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} i p) g), SerrePositivity.KST.Comparison.IsHomotopyPullback.{u_1} sq ↔ CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} (SerrePositivity.KST.Comparison.alternativePullbackComparison.{u_1} sq i p h))
@SerrePositivity.KST.Comparison.isHomotopyPullback_iff_alternative_fiber.{u_1} : ∀ {A X Y B E P : SSet.{u_1}} {a : Quiver.Hom.{u_1, u_1 + 1} A X} {b : Quiver.Hom.{u_1, u_1 + 1} A Y} {f : Quiver.Hom.{u_1, u_1 + 1} X B} {g : Quiver.Hom.{u_1, u_1 + 1} Y B} (sq : CategoryTheory.CommSq.{u_1, u_1 + 1} a b f g) (i : Quiver.Hom.{u_1, u_1 + 1} X E), CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} i) → ∀ (p : Quiver.Hom.{u_1, u_1 + 1} E B), CategoryTheory.MorphismProperty.rlp.{u_1, u_1 + 1} SSet.modelCategoryQuillen.J.{u_1} p → Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} i p) f → ∀ {r : Quiver.Hom.{u_1, u_1 + 1} P Y} {s : Quiver.Hom.{u_1, u_1 + 1} P E}, CategoryTheory.IsPullback.{u_1, u_1 + 1} r s g p → ∀ (k : Quiver.Hom.{u_1, u_1 + 1} A P), Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} k r) b → Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} k s) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} a i) → (SerrePositivity.KST.Comparison.IsHomotopyPullback.{u_1} sq ↔ CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} k))
```

### 3.4.5.4

```lean
SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation_localized_isIso.{u_1} : ∀ (X : SSet.{u_1}), CategoryTheory.IsIso.{u_1 + 1, u_1 + 1} (CategoryTheory.Functor.map.{u_1, u_1 + 1, u_1 + 1, u_1 + 1} SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{u_1} (CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation.{u_1} X))
SerrePositivity.KST.Comparison.freeDegeneraciesAugmentation.{u_1} : Quiver.Hom.{u_1 + 1, u_1 + 1} SerrePositivity.KST.Comparison.freeDegeneracies.{u_1} (CategoryTheory.Functor.id.{u_1, u_1 + 1} SSet.{u_1})
```

### 3.6.1.1

```lean
SSet.Finite.{u_1} : SSet.{u_1} → Prop
SSet.hasDimensionLT_of_finite.{u_1} : ∀ (X : SSet.{u_1}) [X.Finite], ∃ d, X.HasDimensionLT d
SSet.finite_of_hasDimensionLT.{u_1} : ∀ (X : SSet.{u_1}) (d : Nat) [X.HasDimensionLT d], (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i d → Finite.{u_1 + 1} (@Set.Elem.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := i })) (X.nonDegenerate i))) → X.Finite
```

### 3.6.1.10

```lean
SerrePositivity.InfinityCategories.F2.finiteInternalHom_preservesFilteredColimits.{u_1} : ∀ (K : SSet.{u_1}) [SSet.Finite.{u_1} K], CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u_1, u_1, u_1, u_1, u_1 + 1, u_1 + 1} (CategoryTheory.ihom.{u_1, u_1 + 1} K)
```
