# 第1章の交差抜き取り検査（-c）

- 対象表は main の `e3c1c6c0e`。抽出後の `abe0628ab` からの差分には章別 CSV・検査証拠の変更がない。
- 乱数の種は `0xabe0628a`。Python 3.14.7 の `random.Random(seed).sample` を使用。章を 1→2→3、区分を own・both・mathlib の合算→partial→none の順に取り、各母集団は番号の数値順に整列してから重複なしで抽出した。
- 独立照合では抽出に元表の区分を使い、引用の宣言名を段1・段1′および章別 kernel evidence の型の取得に使った。元表の理由は独立判定を固定した後に読んだ。Kerodon 本文と型・定義本体を照らし、必要な候補の型を追加確認した。
- §8.1 の直接対応を partial の基準とした。差は対応区分で数え、同じ区分を支える引用の補足は別記した。§8.4 の停止基準は own・both・mathlib 群の比較後の差に適用する。

| 元の区分 | 母集団 | 抽出 | 独立照合の差 | 比較後の差 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 111 | 20 | 0/20（0%） | 0/20（0%） |
| partial | 40 | 10 | 1/10（10%） | 4/10（40%） |
| none | 29 | 10 | 2/10（20%） | 2/10（20%） |

比較後の own・both・mathlib の差は1割以下。partial・none の差は §8.2 の一括見直し用に記録した。

## own・both・mathlib

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [1.1.0.4](https://kerodon.net/tag/000C) | mathlib | mathlib | mathlib | — | 普通圏 C のみを仮定。二つの abbrev は Δᵒᵖ ⥤ C と Δ ⥤ C を表す。 `CategoryTheory.SimplicialObject` (`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:48`), `CategoryTheory.CosimplicialObject` (`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:527`) |
| [1.1.2.3](https://kerodon.net/tag/0012) | mathlib | mathlib | mathlib | — | 任意の単体集合と n。degenerate_eq_iUnion_range_σ が退化写像の像の和、nonDegenerate が補集合、degenerate_zero が次数 0 の空性を与える。 `SSet.degenerate` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:38`), `SSet.nonDegenerate` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:44`), `SSet.degenerate_zero` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:47`) |
| [1.2.1.6](https://kerodon.net/tag/00GB) | mathlib | mathlib | mathlib | — | 任意の単体集合。IsConnected は非空で π₀ が高々一点。各 summand の特性関数は離散二点への写像で、PiZeroConstant.homEquiv により π₀ 上の二値関数と対応するため、空と全体だけという定義と一致。 `SSet.IsConnected` (`Mathlib/AlgebraicTopology/SimplicialSet/PiZero.lean:168`)。追加確認 `SerrePositivity/InfinityCategories/Kan/PiZeroConstant.lean:121` |
| [1.2.1.22](https://kerodon.net/tag/00GT) | mathlib | mathlib | mathlib | — | 任意の単体集合。isColimitCoforkπ₀ の余叉の二脚は δ₁ と δ₀、余叉の射は π₀.mk。二脚を交換しても同じ余等化子。 `SSet.isColimitCoforkπ₀` (`Mathlib/AlgebraicTopology/SimplicialSet/PiZero.lean:130`) |
| [1.2.2.2](https://kerodon.net/tag/001R) | mathlib | mathlib | mathlib | — | 任意の TopCat の対象。toSSet の各成分は TopCat.toSSetObjEquiv で実標準単体からの連続写像に一致し、構造射は標準単体間の連続写像による前合成。 `TopCat.toSSet` (`Mathlib/AlgebraicTopology/SingularSet.lean:50`), `TopCat.toSSetObjEquiv` (`Mathlib/AlgebraicTopology/SingularSet.lean:56`) |
| [1.2.3.15](https://kerodon.net/tag/002F) | mathlib | mathlib | mathlib | — | 小余極限を持つ C と Q:Δ→C。HasPointwiseLeftKanExtension は同じファイルの余極限仮定から得られ、L に uliftYoneda.leftKanExtension Q を取れる。右随伴 restrictedULiftYoneda Q の成分は Hom(Q[n],−)。 `CategoryTheory.Presheaf.uliftYonedaAdjunction` (`Mathlib/CategoryTheory/Limits/Presheaf.lean:171`) |
| [1.2.4.1](https://kerodon.net/tag/000U) | mathlib | mathlib | mathlib | — | n と i:Fin(n+1)。n>0 で horn の成分は i 以外の頂点を落とす面の和。本文の内外の区別は同じ添字条件。 `SSet.horn` (`Mathlib/AlgebraicTopology/SimplicialSet/Horn.lean:33`) |
| [1.2.5.10](https://kerodon.net/tag/00HC) | own | own | own | — | 任意の Kan 複体と頂点 v,w。元引用は点付き零次類の補題。nonempty_edge_of_piZero_eq が同じ成分なら v→w の辺を直接与え、SSet.π₀.sound が逆向き。引用補正で対応区分は一致。 `SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.mk_eq_iff` (`SerrePositivity/InfinityCategories/Kan/HomotopyZeroRelations.lean:128`), `SerrePositivity.InfinityCategories.Kan.ZeroRelations.equivalence` (`SerrePositivity/InfinityCategories/Kan/HomotopyZeroRelations.lean:117`), `SerrePositivity.InfinityCategories.Kan.KanHomotopyZero` (`SerrePositivity/InfinityCategories/Kan/HomotopyDegreeZero.lean:33`), `SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.equivPiZero` (`SerrePositivity/InfinityCategories/Kan/HomotopyDegreeZero.lean:51`)。追加確認 `SerrePositivity/KST/Spectra/PointedMappingComponents.lean:31`, `Mathlib/AlgebraicTopology/SimplicialSet/PiZero.lean:64` |
| [1.3.1.1](https://kerodon.net/tag/002N) | mathlib | mathlib | mathlib | — | 任意の普通圏 C。nerve の各成分は [n]⥤C で、構造写像は順序写像での前合成。nerveFunctor が圏と関手に対する関手性を与える。 `CategoryTheory.nerve` (`Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean:37`), `CategoryTheory.nerveFunctor` (`Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean:74`) |
| [1.3.2.3](https://kerodon.net/tag/00BR) | mathlib | mathlib | mathlib | — | 単位付きモノイド間の写像。MonoidHom の単位・積の保存と、それを射とする MonCat の Category instance が一致。 `MonoidHom` (`Mathlib/Algebra/Group/Hom/Defs.lean:366`), `MonCat` (`Mathlib/Algebra/Category/MonCat/Basic.lean:42`) |
| [1.3.7.1](https://kerodon.net/tag/00HK) | mathlib | mathlib | mathlib | — | 任意の Quiver。Paths の Hom は Quiver.Path、恒等射は空路で合成は Path.comp による連結。 `CategoryTheory.Paths` (`Mathlib/CategoryTheory/PathCategory/Basic.lean:32`) |
| [1.4.2.2](https://kerodon.net/tag/003N) | mathlib | mathlib | mathlib | — | 任意の単体集合。opFunctor は SimplexCategory.rev の反対で前合成し、各順序写像の両端の反転による原文の Op と一致。 `SSet.opFunctor` (`Mathlib/AlgebraicTopology/SimplicialSet/Op.lean:44`) |
| [1.4.2.8](https://kerodon.net/tag/050H) | mathlib | mathlib | mathlib | — | X が Kan 複体。instKanComplexOp は X.op が Kan 複体という同じ結論。 `SSet.instKanComplexOp` (`Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean:103`) |
| [1.4.5.2](https://kerodon.net/tag/004B) | mathlib | mathlib | mathlib | — | 準圏の二次切断は Quasicategory₂。instCategoryHomotopyCategory₂ の合成は三角形で定めた辺の類、Category の assoc・id_comp・comp_id が本文の三式。 `SSet.Truncated.instCategoryHomotopyCategory₂` (`Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:299`) |
| [1.4.5.3](https://kerodon.net/tag/004C) | both | both | both | — | 準圏の二次切断から Mathlib が頂点・辺のホモトピー類・三角形による合成を持つ圏を作る。本体の homotopyCategoryBridge がこの模型と hoFunctor の同値を与える。 `SSet.Truncated.HomotopyCategory₂` (`Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean:194`), `SerrePositivity.InfinityCategories.homotopyCategoryBridge` (`SerrePositivity/InfinityCategories/Core/HomotopyCategoryBridge.lean:88`), `SSet.hoFunctor` (`Mathlib/AlgebraicTopology/SimplicialSet/HomotopyCat.lean:609`) |
| [1.4.6.1](https://kerodon.net/tag/004R) | own | own | own | — | 準圏の辺。IsInvertibleEdge はその hC での像の IsIso。VertexIso は hC での対象の同型で、Nonempty が本文の対象同型の条件。 `SerrePositivity.InfinityCategories.IsInvertibleEdge` (`SerrePositivity/InfinityCategories/Core/InvertibleEdgeLifting.lean:28`)。追加確認 `SerrePositivity/InfinityCategories/Core/Equivalence.lean:41` |
| [1.4.6.10](https://kerodon.net/tag/0052) | own | own | own | — | 任意の Kan 複体。kanComplex_ho_isGroupoid がその hC の全射に IsIso を与える。 `SerrePositivity.InfinityCategories.kanComplex_ho_isGroupoid` (`SerrePositivity/InfinityCategories/Core/OuterHornConverse.lean:206`), `SerrePositivity.InfinityCategories.kanComplex_iff_isGroupoid` (`SerrePositivity/InfinityCategories/Core/KanCharacterization.lean:73`) |
| [1.5.3.8](https://kerodon.net/tag/0067) | mathlib | mathlib | mathlib | — | 終域 D が準圏なら始域 A は任意。instQuasicategoryObjIhom が本文の Fun(C,D) の準圏性をより弱い仮定で与える。 `SSet.instQuasicategoryObjIhom` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean:157`) |
| [1.5.4.3](https://kerodon.net/tag/006E) | mathlib | mathlib | mathlib | — | 任意の普通圏の二射。HasLiftingProperty は任意の可換正方形の lift の存在、llp と rlp はこれを指定クラスに量化する。 `CategoryTheory.HasLiftingProperty` (`Mathlib/CategoryTheory/LiftingProperties/Basic.lean:45`), `CategoryTheory.MorphismProperty.llp` (`Mathlib/CategoryTheory/MorphismProperty/LiftingProperty.lean:35`) |
| [1.5.7.6](https://kerodon.net/tag/00J9) | own | own | own | — | 内アノダイン射と準圏 C。trivialKanFibration_pre_of_innerAnodyne はその射での前合成が TrivialKanFibration と結論する。 `SerrePositivity.InfinityCategories.trivialKanFibration_pre_of_innerAnodyne` (`SerrePositivity/InfinityCategories/Core/InnerAnodyneEquivalence.lean:23`) |

## partial

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [1.1.2.10](https://kerodon.net/tag/0011) | partial | partial | partial | component | degenerate_eq_iUnion_range_σ と mem_degenerate_iff により、退化写像の像 (1) と小さい次数への全射による分解 (3) の同値は直接確認できる。任意の非単射第一脚による (5) の形を含む五条件一括の型は確認できなかった。 `SSet.mem_degenerate_iff` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:70`), `SSet.degenerate_eq_iUnion_range_σ` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:98`) |
| [1.1.4.7](https://kerodon.net/tag/0501) | partial | partial | mathlib | — | ofSimplex_le_skeleton と mem_skeleton_obj_iff_of_nonDegenerate により、k 以下の非退化単体が skeleton (k+1) に入るため、次元 ≤ k の任意の部分複体の包含を le_iff_contains_nonDegenerate で確認できる。骨格自体への次元上界を独立に返す型は確認できなかった。 `SSet.Subcomplex.le_iff_contains_nonDegenerate` (`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:287`), `SSet.ofSimplex_le_skeleton` (`Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean:72`)。追加確認 `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean:77`, `Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean:281` |
| [1.1.5.10](https://kerodon.net/tag/00FZ) | partial | partial | partial | special | PiZeroConstant.discrete T は定数単体集合。さらに DiscreteNerveIso.iso が X=nerve (Discrete T) の場合にその定数単体集合との同型を直接与える。任意の X の離散性をこの存在条件で定義する述語は確認できなかった。 `SerrePositivity.SimplicialModel.PiZeroConstant.discrete` (`SerrePositivity/InfinityCategories/Kan/PiZeroConstant.lean:48`)。追加確認 `SerrePositivity/InfinityCategories/F1B/Localization/DwyerKan/DiscreteNerveIso.lean:33` |
| [1.2.1.13](https://kerodon.net/tag/00GJ) | partial | none | none | — | componentSubcomplex と componentClassEquiv は指定の成分集合が切り出す部分複体と、その π₀ を扱う。元の単体集合への成分の余積の比較が同型という結論は確認できなかった。 `SerrePositivity.KST.Comparison.componentSubcomplex` (`SerrePositivity/KST/Comparison/ComponentSubcomplex.lean:31`), `SerrePositivity.KST.Comparison.componentClassEquiv` (`SerrePositivity/KST/Comparison/ComponentSubcomplex.lean:108`), `SerrePositivity.SimplicialModel.PiZeroConstant.homEquiv` (`SerrePositivity/InfinityCategories/Kan/PiZeroConstant.lean:121`) |
| [1.2.3.1](https://kerodon.net/tag/001Y) | partial | partial | partial | special | sSetTopAdj.homEquiv と随伴の単位の公式で、Y=toTop(S)、u が指定の随伴単位の場合に本文の全単射を得る。任意の候補 (Y,u) に対してこの条件を表す専用の述語は元引用にない。 `SSet.toTop` (`Mathlib/AlgebraicTopology/SingularSet.lean:65`), `sSetTopAdj` (`Mathlib/AlgebraicTopology/SingularSet.lean:73`) |
| [1.2.5.9](https://kerodon.net/tag/00MG) | partial | partial | partial | special | ringSpace_kanComplex は simplicial ring の加法群の underlying SSet の Kan 性を返す。任意の simplicial group に対する宣言は確認できなかった。 `SerrePositivity.KST.Comparison.ringSpace_kanComplex` (`SerrePositivity/KST/Comparison/SimplicialRingKan.lean:30`) |
| [1.3.4.1](https://kerodon.net/tag/0031) | partial | partial | partial | direction | nerve の StrictSegal・準圏性と、各内ホーン上の写像を spine が決めることから nerve の一意延長側を確認。任意の一意内ホーン充填 S から普通圏の nerve への同型を返す宣言は確認できなかった。 `CategoryTheory.Nerve.strictSegal` (`Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean:522`), `SSet.StrictSegal` (`Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean:264`) |
| [1.3.4.2](https://kerodon.net/tag/0032) | partial | partial | mathlib | — | StrictSegal.quasicategory で充填の存在。thinNerve_hom_ext_horn が充填の一意性を直接述べるのは対象が前順序の nerve の場合で、任意の普通圏について同じ一意性を直接述べる型は確認できなかった。 `CategoryTheory.Nerve.strictSegal` (`Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean:522`), `SSet.StrictSegal.quasicategory` (`Mathlib/AlgebraicTopology/Quasicategory/StrictSegal.lean:36`), `SerrePositivity.InfinityCategories.thinNerve_hom_ext_horn` (`SerrePositivity/InfinityCategories/F1/Fibrations/ThinNerveInnerFibration.lean:46`)。追加確認 `Mathlib/AlgebraicTopology/SimplicialSet/Path.lean:383`, `Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean:322` |
| [1.5.5.6](https://kerodon.net/tag/0070) | partial | partial | own | — | ihomMap_trivialKanFibration は A=∅ としたときの比較 Fun(B,X)→Fun(B,Y) を扱う。一般の A↪B で終域が相対 pullback になる場合の結論はこの型にない。 `SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration` (`SerrePositivity/KST/SConstruction/STrivialFibration.lean:23`)。追加確認 `SerrePositivity/InfinityCategories/Core/RelativeInternalHomTrivialFibration.lean:24` |
| [1.5.6.1](https://kerodon.net/tag/0079) | partial | partial | partial | direction | Λ²₁ の包含が内アノダインであることと trivialKanFibration_pre_of_innerAnodyne の適用で (1)→(2)。この一つのホーンから全内ホーンの充填を返す逆は確認できなかった。 `SerrePositivity.InfinityCategories.trivialKanFibration_pre_of_innerAnodyne` (`SerrePositivity/InfinityCategories/Core/InnerAnodyneEquivalence.lean:23`), `SSet.innerAnodyneExtensions.horn_ι` (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/Basic.lean:58`) |

## none

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [1.1.1.9](https://kerodon.net/tag/04FQ) | none | none | none | — | SemiSimplexCategory.toSimplexCategory と Mathlib の face の関係式を探索。与えた顔写像と顔関係から任意の値圏の反変関手を一意に作る宣言は確認できなかった。 — |
| [1.1.2.12](https://kerodon.net/tag/04ZR) | none | mathlib | mathlib | — | WideSubcategory (MorphismProperty.epimorphisms SimplexCategory) は全ての [n] を対象に持つ。epimorphisms の IsMultiplicative instance が恒等・合成を与え、SimplexCategory.epi_iff_surjective で各 Hom は非減少全射に一致する。 —。追加確認 `Mathlib/CategoryTheory/Widesubcategory.lean:98`, `Mathlib/CategoryTheory/MorphismProperty/Composition.lean:236`, `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:629` |
| [1.2.1.24](https://kerodon.net/tag/00GV) | none | none | none | — | SSet.isColimitCoforkπ₀ は全辺による余等化子。非退化辺への制限や Gr(S) の成分との同定を結論する型は確認できなかった。 — |
| [1.2.1.26](https://kerodon.net/tag/00GW) | none | none | none | — | SSet.isConnected_iff_nonempty_unique と π₀ の積比較を探索。有限積の π₀ の積公式または連結性の保存は確認できなかった。 — |
| [1.2.3.7](https://kerodon.net/tag/0024) | none | partial | partial | special | SSet.stdSimplex.face は頂点部分集合 T を指定し、像が T に含まれる単体の部分複体を返す。非空部分集合族 U が T に含まれる集合全体である場合の単体側に一致。任意の U と実現側を同時に扱う型は確認できなかった。 —。追加確認 `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean:279` |
| [1.2.3.19](https://kerodon.net/tag/00H6) | none | none | none | — | SSet.toTop・SSet.π₀・Top の ConnectedComponents と singular comparison を探索。実現の位相連結成分と単体 π₀ の指定全単射を確認できなかった。 — |
| [1.3.2.14](https://kerodon.net/tag/04G8) | none | none | none | — | MonCat・nerveFunctor と非単位的半群の豊穣・半単体 nerve を探索。非単位的モノイドの指定された半単体 nerve の全忠実性とその本質像の型は確認できなかった。 — |
| [1.3.4.3](https://kerodon.net/tag/0033) | none | none | none | — | StrictSegal.spineEquiv と spineToSimplex_map は spine で各単体を復元する。頂点・辺の全単射を仮定して指定射を同型とする型、および一意内ホーン条件から使える一般の橋渡しは確認できなかった。 — |
| [1.5.2.6](https://kerodon.net/tag/005P) | none | none | none | — | CategoryTheory.Paths と nerve の随伴を探索。対象は有向路の自由圏で、可換性により路を同一視した到達可能性の半順序・埋込み・一意延長の組は確認できなかった。 — |
| [1.5.6.8](https://kerodon.net/tag/00J2) | none | none | none | — | CategoryTheory.Nerve.strictSegal と SSet.innerAnodyneExtensions、一意 lift の飽和を探索。任意の内アノダインに対する一意 lift と普通圏の nerve の同値、または同じ条件の片側を直接結論する宣言は確認できなかった。 — |

## 差があった行の比較

### [1.1.4.7](https://kerodon.net/tag/0501)（-a2 `partial`、独立 `partial`、比較後 `mathlib`）

- -a2 の理由を照合した記録。非退化単体による包含の判定と生成単体のskeletonへの包含。最大の次元上界部分複体という一括の主張は引用されていない。
- 今回の判定。-a2 の二候補に mem_skeleton_obj_iff_of_nonDegenerate と Subcomplex.mem_nonDegenerate_iff を加えて照合。骨格の非退化単体は d<k+1 のものにちょうど一致するので、骨格自体の次元上界と任意の次元 ≤k の部分複体の包含が両方従う。k<0 は skeleton_zero と HasDimensionLT 0。

### [1.2.1.13](https://kerodon.net/tag/00GJ)（-a2 `partial`、独立 `none`、比較後 `none`）

- -a2 の理由を照合した記録。成分の集合で指定した部分複体とそのπ₀との全単射はある。S全体の余積分解の宣言ではない。PiZeroConstant.homEquivの名前空間を補正。
- 今回の判定。-a2 の componentClassEquiv の結論は部分複体の成分集合の同値。本文の分解で要求するのは成分部分複体の余積から元の S への同型であり、成分を個別に指定できることはその分解の準備に当たる。

### [1.3.4.2](https://kerodon.net/tag/0032)（-a2 `partial`、独立 `partial`、比較後 `mathlib`）

- -a2 の理由を照合した記録。一般のnerveの内ホーン充填存在はある。一意性の引用はQuiver.IsThin Cを追加仮定する特例。thinNerveの名前空間を補正。
- 今回の判定。-a2 の準圏性は存在を与える。一意性には IsThin は不要で、horn.spineId_map_hornInclusion が内ホーン内に spine 全体を載せ、StrictSegal.spineInjective が nerve の二つの延長を同じ spine から同一視する。

### [1.5.5.6](https://kerodon.net/tag/0070)（-a2 `partial`、独立 `partial`、比較後 `own`）

- -a2 の理由を照合した記録。ihomMap_trivialKanFibrationはAが空の場合だけ。一般の制限と後合成のpullback-power射に対する宣言ではない。
- 今回の判定。-a2 の ihomMap_trivialKanFibration は A=∅ の版。trivialKanFibration_pullbackObjObjπ は任意の単射 i と自明 Kan fibration p に対し、同じ制限・後合成の pullback を入力に取り、その比較射 π 自体の自明 Kan 性を返す。

### [1.1.2.12](https://kerodon.net/tag/04ZR)（-a2 `none`、独立 `mathlib`、比較後 `mathlib`）

- -a2 の理由を照合した記録。確認済み・なし（対象ソースの探索範囲内）。全射単体圏の名称・順序写像の全射部分圏を検索。全射の補題は多数あるが、Δ_surjそのものの対応宣言は見つからない。
- 今回の判定。-a2 が確認した全射判定に WideSubcategory を適用すると、専用の定数名がなくても、本文の全対象・全射だけの Hom・単体圏から継承する恒等と合成がそろう。

### [1.2.3.7](https://kerodon.net/tag/0024)（-a2 `none`、独立 `partial`、比較後 `partial`）

- -a2 の理由を照合した記録。確認済み・なし（対象ソースの探索範囲内）。下方閉集合・標準単体の部分複体・台による位相部分空間を検索。一般のfaceや部分複体の構成はあるが、原文の組み合わされた構成は見つからない。
- 今回の判定。-a2 のいう一般の U と位相側の両方は未確認。U が一つの頂点集合 T の非空部分集合全体の場合、mem_face_iff の像条件は本文の単体側に直接一致する。

## 追加の kernel 型

追加の `#check` は既存モジュールの import だけを使い、章別3回と補足2回に分けて共有鍵を取得した。各回の上限は500秒、実測の最長は約15秒。

```lean
@SerrePositivity.KST.Spectra.nonempty_edge_of_piZero_eq : ∀ {Z : SSet} [Z.KanComplex]
  {v w : Z.obj (Opposite.op { len := 0 })}, SSet.π₀.mk v = SSet.π₀.mk w → Nonempty (SSet.Edge v w)
@SerrePositivity.InfinityCategories.VertexIso : {X : SSet} →
  X.obj (Opposite.op { len := 0 }) → X.obj (Opposite.op { len := 0 }) → Type u_1
@SSet.π₀.sound : ∀ {X : SSet} {x₀ x₁ : X.obj (Opposite.op { len := 0 })} (e : SSet.Edge x₀ x₁),
  SSet.π₀.mk x₀ = SSet.π₀.mk x₁
@CategoryTheory.Presheaf.uliftYonedaAdjunction : {C : Type u_4} →
  [inst : CategoryTheory.Category.{u_2, u_4} C] →
    {ℰ : Type u_5} →
      [inst_1 : CategoryTheory.Category.{u_3, u_5} ℰ] →
        {A : CategoryTheory.Functor C ℰ} →
          [CategoryTheory.uliftYoneda.{max u_1 u_3, u_2, u_4}.HasPointwiseLeftKanExtension A] →
            (L : CategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ (Type (max u_1 u_2 u_3))) ℰ) →
              (α : A ⟶ CategoryTheory.uliftYoneda.{max u_1 u_3, u_2, u_4}.comp L) →
                [L.IsLeftKanExtension α] → L ⊣ CategoryTheory.Presheaf.restrictedULiftYoneda A
@SSet.stdSimplex.mem_face_iff : ∀ {n : ℕ} (S : Finset (Fin (n + 1))) {d : ℕ}
  (x : (SSet.stdSimplex.obj { len := n }).obj (Opposite.op { len := d })),
  x ∈ (SSet.stdSimplex.face S).obj (Opposite.op { len := d }) ↔ ∀ (i : Fin (d + 1)), x i ∈ S
CategoryTheory.WideSubcategory (CategoryTheory.MorphismProperty.epimorphisms SimplexCategory) : Type
@SimplexCategory.epi_iff_surjective : ∀ {n m : SimplexCategory} {f : n ⟶ m},
  CategoryTheory.Epi f ↔ Function.Surjective ⇑(SimplexCategory.Hom.toOrderHom f)
SerrePositivity.EInfinity.Hammock.DiscreteNerve.iso : (T : Type u_1) →
  CategoryTheory.nerve (CategoryTheory.Discrete T) ≅ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj T
SSet.mem_skeleton_obj_iff_of_nonDegenerate : ∀ (X : SSet) {d : ℕ} (x : ↑(X.nonDegenerate d)) (n : ℕ),
  ↑x ∈ (X.skeleton n).obj (Opposite.op { len := d }) ↔ d < n
@SSet.Subcomplex.mem_nonDegenerate_iff : ∀ {X : SSet} (A : X.Subcomplex) {n : ℕ}
  (x : ↑(A.obj (Opposite.op { len := n }))), x ∈ A.toSSet.nonDegenerate n ↔ ↑x ∈ X.nonDegenerate n
@SSet.Subcomplex.le_iff_contains_nonDegenerate : ∀ {X : SSet} (A B : X.Subcomplex),
  A ≤ B ↔
    ∀ (n : ℕ) (x : ↑(X.nonDegenerate n)), ↑x ∈ A.obj (Opposite.op { len := n }) → ↑x ∈ B.obj (Opposite.op { len := n })
@SSet.horn.spineId_map_hornInclusion : ∀ {n : ℕ} (i : Fin (n + 3)) (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)),
  (SSet.horn.spineId i h₀ hₙ).map (SSet.horn (n + 2) i).ι = SSet.stdSimplex.spineId (n + 2)
@SSet.StrictSegal.spineInjective : ∀ {X : SSet} (sx : X.StrictSegal) {n : ℕ}, Function.Injective ⇑(sx.spineEquiv n)
@SerrePositivity.InfinityCategories.trivialKanFibration_pullbackObjObjπ : ∀ {A B E Y : SSet} (i : A ⟶ B)
  [CategoryTheory.Mono i] (p : E ⟶ Y) [SerrePositivity.InfinityCategories.TrivialKanFibration p]
  (sq' : CategoryTheory.MonoidalClosed.internalHom.PullbackObjObj i p),
  SerrePositivity.InfinityCategories.TrivialKanFibration sq'.π
```

## 元の kernel evidence から照合した型

`ch1-kernel-evidence.json`、段1、段1′から own・both・mathlib 群の型を取得した。表示用に空白を整えた。

### 1.1.0.4

```lean
CategoryTheory.SimplicialObject.{u_1, u_2} : (C : Type u_2) → [CategoryTheory.Category.{u_1, u_2} C] → Type (max u_1 u_2)
CategoryTheory.CosimplicialObject.{u_1, u_2} : (C : Type u_2) → [CategoryTheory.Category.{u_1, u_2} C] → Type (max u_1 u_2)
```

### 1.1.2.3

```lean
SSet.degenerate.{u_1} : (X : SSet.{u_1}) → (n : Nat) → Set.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := n }))
SSet.nonDegenerate.{u_1} : (X : SSet.{u_1}) → (n : Nat) → Set.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := n }))
SSet.degenerate_zero.{u_1} : ∀ (X : SSet.{u_1}), @Eq.{u_1 + 1} (Set.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) }))) (X.degenerate (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@EmptyCollection.emptyCollection.{u_1} (Set.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) }))) (@Set.instEmptyCollection.{u_1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) }))))
```

### 1.2.1.6

```lean
SSet.IsConnected.{u_1} : SSet.{u_1} → Prop
```

### 1.2.1.22

```lean
@SSet.isColimitCoforkπ₀.{u_1} : {X : SSet.{u_1}} → @CategoryTheory.Limits.IsColimit.{0, u_1, 0, u_1 + 1} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.Limits.parallelPair.{u_1, u_1 + 1} (Type u_1) (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })) CategoryTheory.types.{u_1} (@CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ⋯ (nat_lit 1)))) (@CategoryTheory.SimplicialObject.δ.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (nat_lit 0) (@Fin.instOfNat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ⋯ (nat_lit 0))))) (@SSet.coforkπ₀.{u_1} X)
```

### 1.2.2.2

```lean
TopCat.toSSet.{u_1} : @CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} TopCat.{u_1} TopCat.instCategory.{u_1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1})
TopCat.toSSetObjEquiv.{u_1} : (X : TopCat.{u_1}) → (n : Opposite.{1} SimplexCategory) → Equiv.{u_1 + 1, u_1 + 1} (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} TopCat.{u_1} TopCat.instCategory.{u_1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) TopCat.toSSet.{u_1} X) n) (@ContinuousMap.{0, u_1} (@Convexity.StdSimplex.{0, 0} Real Real.instLE Real.instAddCommMonoid Real.instOne (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Opposite.unop.{1} SimplexCategory n).len (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (↑X) (@Convexity.StdSimplex.topologicalSpace.{0, 0} Real Real.partialOrder Real.instRing (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.instIsStrictOrderedRing (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Opposite.unop.{1} SimplexCategory n).len (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) X.str)
```

### 1.2.3.15

```lean
@CategoryTheory.Presheaf.uliftYonedaAdjunction.{u_1, u_2, u_3, u_4, u_5} : {C : Type u_4} → [inst : CategoryTheory.Category.{u_2, u_4} C] → {ℰ : Type u_5} → [inst_1 : CategoryTheory.Category.{u_3, u_5} ℰ] → {A : @CategoryTheory.Functor.{u_2, u_3, u_4, u_5} C inst ℰ inst_1} → [@CategoryTheory.Functor.HasPointwiseLeftKanExtension.{u_2, u_4, max (max (max u_3 u_1) u_4) u_2, max (max (max (u_3 + 1) (u_1 + 1)) u_4) (u_2 + 1), u_3, u_5} C (@CategoryTheory.Functor.{u_2, max u_2 u_1 u_3, u_4, max (u_2 + 1) ((max u_1 u_3) + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max (max u_1 u_3) u_2)) CategoryTheory.types.{max u_2 u_1 u_3}) ℰ inst (@CategoryTheory.Functor.category.{u_2, max u_2 u_1 u_3, u_4, max (u_2 + 1) ((max u_1 u_3) + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max (max u_1 u_3) u_2)) CategoryTheory.types.{max u_2 u_1 u_3}) inst_1 (@CategoryTheory.uliftYoneda.{max u_1 u_3, u_2, u_4} C inst) A] → (L : @CategoryTheory.Functor.{max (max (max u_4 u_2) u_3) u_1, u_3, max (max (max (max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)) u_4) (max u_2 u_3) u_1) u_2, u_5} (@CategoryTheory.Functor.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) (@CategoryTheory.Functor.category.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) ℰ inst_1) → (α : @Quiver.Hom.{max u_4 u_3, max (max (max u_4 u_5) u_2) u_3} (@CategoryTheory.Functor.{u_2, u_3, u_4, u_5} C inst ℰ inst_1) (@CategoryTheory.CategoryStruct.toQuiver.{max u_4 u_3, max (max (max u_4 u_5) u_2) u_3} (@CategoryTheory.Functor.{u_2, u_3, u_4, u_5} C inst ℰ inst_1) (@CategoryTheory.Category.toCategoryStruct.{max u_4 u_3, max (max (max u_4 u_5) u_2) u_3} (@CategoryTheory.Functor.{u_2, u_3, u_4, u_5} C inst ℰ inst_1) (@CategoryTheory.Functor.category.{u_2, u_3, u_4, u_5} C inst ℰ inst_1))) A (@CategoryTheory.Functor.comp.{u_2, max (max (max u_4 u_2) u_3) u_1, u_3, u_4, max (max (max u_4 (u_2 + 1)) (u_3 + 1)) (u_1 + 1), u_5} C inst (@CategoryTheory.Functor.{u_2, max u_2 u_1 u_3, u_4, max (u_2 + 1) ((max u_1 u_3) + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max (max u_1 u_3) u_2)) CategoryTheory.types.{max u_2 u_1 u_3}) (@CategoryTheory.Functor.category.{u_2, max u_2 u_1 u_3, u_4, max (u_2 + 1) ((max u_1 u_3) + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max (max u_1 u_3) u_2)) CategoryTheory.types.{max u_2 u_1 u_3}) ℰ inst_1 (@CategoryTheory.uliftYoneda.{max u_1 u_3, u_2, u_4} C inst) L)) → [@CategoryTheory.Functor.IsLeftKanExtension.{u_2, u_4, u_3, u_5, max (max (max u_4 u_2) u_3) u_1, max (max (max u_4 (u_2 + 1)) (u_3 + 1)) (u_1 + 1)} C ℰ (@CategoryTheory.Functor.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) inst inst_1 (@CategoryTheory.Functor.category.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) L (@CategoryTheory.uliftYoneda.{max u_1 u_3, u_2, u_4} C inst) A α] → @CategoryTheory.Adjunction.{max (max (max u_4 u_2) u_3) u_1, u_3, max (max (max u_4 (u_2 + 1)) (u_3 + 1)) (u_1 + 1), u_5} (@CategoryTheory.Functor.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) (@CategoryTheory.Functor.category.{u_2, max (max u_2 u_3) u_1, u_4, max (max (u_2 + 1) (u_3 + 1)) (u_1 + 1)} (Opposite.{u_4 + 1} C) (@CategoryTheory.Category.opposite.{u_2, u_4} C inst) (Type (max u_1 u_2 u_3)) CategoryTheory.types.{max (max u_2 u_3) u_1}) ℰ inst_1 L (@CategoryTheory.Presheaf.restrictedULiftYoneda.{max u_1 u_2, u_2, u_3, u_4, u_5} C inst ℰ inst_1 A)
```

### 1.2.4.1

```lean
SSet.horn.{u_1} : (n : Nat) → Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) → (@CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} SimplexCategory SimplexCategory.smallCategory SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) SSet.stdSimplex.{u_1} { len := n }).Subcomplex
```

### 1.2.5.10

```lean
@SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.mk_eq_iff.{u_1} : ∀ {X : SSet.{u_1}} [X.KanComplex] {x : @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })} (f g : X.PtSimplex (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x), Iff (@Eq.{u_1 + 1} (SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.{u_1} X x) (@SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.mk.{u_1} X x f) (@SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.mk.{u_1} X x g)) (Nonempty.{u_1 + 1} (@SSet.PtSimplex.RelStruct₀.{u_1} X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x f g))
@SerrePositivity.InfinityCategories.Kan.ZeroRelations.equivalence.{u_1} : ∀ {X : SSet.{u_1}} [X.KanComplex] {x : @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })}, @Equivalence.{u_1 + 1} (X.PtSimplex (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) fun f g => Nonempty.{u_1 + 1} (@SSet.PtSimplex.RelStruct₀.{u_1} X (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x f g)
SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.{u_1} : (X : SSet.{u_1}) → @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) }) → Type u_1
@SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.equivPiZero.{u_1} : {X : SSet.{u_1}} → {x : @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })} → Equiv.{u_1 + 1, u_1 + 1} (SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.{u_1} X x) X.π₀
```

### 1.3.1.1

```lean
CategoryTheory.nerve.{u_1, u_2} : (C : Type u_2) → [CategoryTheory.Category.{u_1, u_2} C] → SSet.{max u_2 u_1}
CategoryTheory.nerveFunctor.{u_1, u_2} : @CategoryTheory.Functor.{max u_2 u_1, max u_2 u_1, max (u_2 + 1) (u_1 + 1), (max u_2 u_1) + 1} CategoryTheory.Cat.{u_1, u_2} CategoryTheory.Cat.category.{u_1, u_2} SSet.{max u_2 u_1} (@CategoryTheory.Functor.category.{0, max u_2 u_1, 0, (max u_2 u_1) + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type (max u_2 u_1)) CategoryTheory.types.{max u_2 u_1})
```

### 1.3.2.3

```lean
MonoidHom.{u_1, u_2} : (M : Type u_1) → (N : Type u_2) → [MulOne.{u_1} M] → [MulOne.{u_2} N] → Type (max u_1 u_2)
MonCat.{u_1} : Type (u_1 + 1)
```

### 1.3.7.1

```lean
CategoryTheory.Paths.{u_1} : Type u_1 → Type u_1
```

### 1.4.2.2

```lean
SSet.opFunctor.{u_1} : @CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1})
```

### 1.4.2.8

```lean
@SSet.instKanComplexOp.{u_1} : ∀ {X : SSet.{u_1}} [X.KanComplex], X.op.KanComplex
```

### 1.4.5.2

```lean
@SSet.Truncated.instCategoryHomotopyCategory₂.{u_1} : {A : SSet.Truncated.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))} → [A.Quasicategory₂] → CategoryTheory.Category.{u_1, u_1} A.HomotopyCategory₂
```

### 1.4.5.3

```lean
SSet.Truncated.HomotopyCategory₂.{u_1} : SSet.Truncated.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Type u_1
SerrePositivity.InfinityCategories.homotopyCategoryBridge.{u_1} : (X : SSet.{u_1}) → [inst : X.Quasicategory] → @CategoryTheory.Equivalence.{u_1, u_1, u_1, u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (SSet.Truncated.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@CategoryTheory.Category.opposite.{0, 0} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.ObjectProperty.FullSubcategory.category.{0, 0} SimplexCategory SimplexCategory.smallCategory fun a => @LE.le.{0} Nat instLENat a.len (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (Type u_1) CategoryTheory.types.{u_1}) (SSet.truncation.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) X).HomotopyCategory₂ (@CategoryTheory.Bundled.α.{u_1, u_1 + 1} CategoryTheory.Category.{u_1, u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X)) (@SSet.Truncated.instCategoryHomotopyCategory₂.{u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (SSet.Truncated.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@CategoryTheory.Category.opposite.{0, 0} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.ObjectProperty.FullSubcategory.category.{0, 0} SimplexCategory SimplexCategory.smallCategory fun a => @LE.le.{0} Nat instLENat a.len (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (Type u_1) CategoryTheory.types.{u_1}) (SSet.truncation.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) X) ⋯) (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X).str
SSet.hoFunctor.{u_1} : @CategoryTheory.Functor.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1}
```

### 1.4.6.1

```lean
@SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} : {X : SSet.{u_1}} → {x y : @CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} X (@Opposite.op.{1} SimplexCategory { len := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })} → @SSet.Truncated.Edge.{u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (SSet.Truncated.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@CategoryTheory.Category.opposite.{0, 0} (SimplexCategory.Truncated (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@CategoryTheory.ObjectProperty.FullSubcategory.category.{0, 0} SimplexCategory SimplexCategory.smallCategory fun a => @LE.le.{0} Nat instLENat a.len (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (Type u_1) CategoryTheory.types.{u_1}) (SSet.truncation.{u_1} (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) X) x y → Prop
```

### 1.4.6.10

```lean
SerrePositivity.InfinityCategories.kanComplex_ho_isGroupoid.{u_1} : ∀ (X : SSet.{u_1}) [X.KanComplex], @CategoryTheory.IsGroupoid.{u_1, u_1} (@CategoryTheory.Bundled.α.{u_1, u_1 + 1} CategoryTheory.Category.{u_1, u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X)) (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X).str
SerrePositivity.InfinityCategories.kanComplex_iff_isGroupoid.{u_1} : ∀ (X : SSet.{u_1}) [X.Quasicategory], Iff X.KanComplex (@CategoryTheory.IsGroupoid.{u_1, u_1} (@CategoryTheory.Bundled.α.{u_1, u_1 + 1} CategoryTheory.Category.{u_1, u_1} (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X)) (@CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) CategoryTheory.Cat.{u_1, u_1} CategoryTheory.Cat.category.{u_1, u_1} SSet.hoFunctor.{u_1} X).str)
```

### 1.5.3.8

```lean
@SSet.instQuasicategoryObjIhom.{u_1} : ∀ {A X : SSet.{u_1}} [X.Quasicategory], (A ⟹ X).Quasicategory
```

### 1.5.4.3

```lean
@CategoryTheory.HasLiftingProperty.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → {A B X Y : C} → @Quiver.Hom.{u_1, u_2} C (@CategoryTheory.CategoryStruct.toQuiver.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C inst)) A B → @Quiver.Hom.{u_1, u_2} C (@CategoryTheory.CategoryStruct.toQuiver.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C inst)) X Y → Prop
@CategoryTheory.MorphismProperty.llp.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → @CategoryTheory.MorphismProperty.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C inst) → @CategoryTheory.MorphismProperty.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C inst)
```

### 1.5.7.6

```lean
@SerrePositivity.InfinityCategories.trivialKanFibration_pre_of_innerAnodyne.{u_1} : ∀ {A B : SSet.{u_1}} (i : @Quiver.Hom.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.ReflQuiver.toQuiver.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.catToReflQuiver.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}))) A B), @SSet.innerAnodyneExtensions.{u_1} A B i → ∀ (Y : SSet.{u_1}) [Y.Quasicategory], @SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1} (B ⟹ Y) (A ⟹ Y) (@CategoryTheory.NatTrans.app.{u_1, u_1, u_1 + 1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.ihom.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.Monoidal.functorCategoryMonoidal.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} CategoryTheory.typesCartesianMonoidalCategory.{u_1}))) B (@CategoryTheory.FunctorToTypes.closed.{u_1, 0, 0} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) B)) (@CategoryTheory.ihom.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.Monoidal.functorCategoryMonoidal.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} CategoryTheory.typesCartesianMonoidalCategory.{u_1}))) A (@CategoryTheory.FunctorToTypes.closed.{u_1, 0, 0} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) A)) (@CategoryTheory.MonoidalClosed.pre.{u_1, u_1 + 1} SSet.{u_1} (@CategoryTheory.Functor.category.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.Monoidal.functorCategoryMonoidal.{0, u_1, 0, u_1 + 1} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} (@CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory.{u_1, u_1 + 1} (Type u_1) CategoryTheory.types.{u_1} CategoryTheory.typesCartesianMonoidalCategory.{u_1}))) B A (@CategoryTheory.FunctorToTypes.closed.{u_1, 0, 0} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) B) (@CategoryTheory.FunctorToTypes.closed.{u_1, 0, 0} (Opposite.{1} SimplexCategory) (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) A) i) Y)
```
