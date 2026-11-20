# 球面モノイド上の加群としての対称スペクトル

`SymmetricSpectrum` は `GeneralSymmetricSpectrum PointedSimplicialSet PointedSimplicialSet.circle` の略記である。
各段・作用・構造射には `GeneralSymmetricSpectrum.level`・`action`・`structureMap` を使う。
円周への特殊化は [Basic.lean](Basic.lean)、球面スペクトルは [Sphere.lean](Sphere.lean)、
基点のない単体集合による作用と写像空間は [Simplicial.lean](Simplicial.lean) に置く。
宣言の移動先は[段 9 の対応表](../../../research/cleanup-zero-base/spectra/stage9.csv)にある。
基礎圏は基点付き単体的集合の対称列、テンソル積は登録済みのconvolutionである。
各段の対象は基点付き単体的集合であり、球面の作用から和次数への構造射を得る。

段階2までの入口は [StageTwo](../StageTwo.lean)。基点付きの作用、単体的写像対象と豊穣構造、
tensor・cotensor、懸垂・ループ、構造射の随伴表示をこの一つのimportから利用できる。
一般の球面加群と各段の計算の詳細も含めた入口は [Foundations](../Foundations.lean)。

```lean
import SerrePositivity.Spectra.StageTwo
```

単体的豊穣構造は、`pointedMappingEnrichedOrdinaryCategory` を局所登録してから
`TransportOrdinaryEnrichment.ordinaryCategory` に `PointedSimplicialSet.forget` と
`PointedSimplicialSet.forgetUnitHomEquiv`、その式 `PointedSimplicialSet.forgetUnitHomEquiv_formula` を渡して得る。
構成済みの対象・射・随伴と引継ぎAPIは次のとおり。

| 用途 | 主なAPI | 法則・比較 |
| --- | --- | --- |
| 基点付きの作用 | `pointwiseTensorFunctor`, `cotensorFunctor` | `pointwiseTensorCotensorAdjunction`、各段のsmash・内部Homとの一致 |
| 作用の単位・結合 | `pointwiseTensorUnitNatIso`, `pointwiseTensorAssociatorNatIso` | 各段の通常の比較、三変数の自然性、pentagon・triangle・左単位 |
| 基点付き写像対象 | `GeneralSymmetricSpectrum.mappingObject`, `GeneralSymmetricSpectrum.mappingObjectAdjunction` | `homEquiv` による転置・逆転置、余単位による評価 |
| 写像の合成・単位 | `GeneralSymmetricSpectrum.mappingObjectComposition`, `GeneralSymmetricSpectrum.mappingObjectUnit` | 結合・左右単位則、通常の射の恒等射・合成との一致 |
| 単体的豊穣構造 | `simplicialMappingSpace`, `TransportOrdinaryEnrichment.ordinaryCategory` | `simplicialMappingVertexEquiv`、既存の圏構造との一致 |
| 通常の単体的作用 | `simplicialTensorFunctor`, `simplicialCotensorFunctor` | 三つのHom同値の三変数の自然性、評価・余評価 |
| 単位と反復作用 | `simplicialTensorUnitNatIso`, `simplicialTensorProductNatIso` | 右随伴側は `ActionUnitAdjunction.rightUnitIso` と `ActionComparisonAdjunction.rightIso` で比較する |
| 懸垂・ループ | `suspensionFunctor`, `loopFunctor`, `suspensionLoopAdjunction` | 自然なHom同値、単位・余単位・triangle、各段の公式 |
| 構造射の随伴表示 | `GeneralSymmetricSpectrum.adjointStructureMap` | `GeneralSymmetricSpectrum.uncurry_adjointStructureMap`、`MonoidalClosed.curry_uncurry`、自然性。添字の移送は `suspensionMap` の `Nat.one_add` |

計画の最終検証例は [check_spectra_stage2](../../../scripts/check_spectra_stage2.lean)、
標準公理のみ・sorry依存なしの監査は [audit_spectra](../../../scripts/audit_spectra.lean) に置く。
集約ビルドの後、次のコマンドで再確認できる。

```sh
lake build SerrePositivity.Spectra.Foundations
lake env lean scripts/check_spectra_stage2.lean
lake env lean scripts/audit_spectra.lean
```

モデル構造の選定、レベル・安定弱同値とfibration・cofibration、関手的な置換、
Quillen公理とpushout-product公理、導来演算、安定ホモトピー群、次数シフトは次の検討に残る。
その検討では、採用する定義と既存の自由対象・各段の極限余極限・作用・写像対象との接続を確認する。
段階2の構成にはモデル構造を仮定する入力を加えていない。

- [MappingSpaceNaturality](MappingSpaceNaturality.lean)：原変数スペクトルの射による写像対象の前合成と、転置・逆転置の原変数の自然性の法則。
- [MappingSpace](MappingSpace.lean)：内部Homの第0段の基点付き写像対象、二変数関手、各段のsmashとの随伴・表現性と評価・転置・逆転置の法則。
- [MappingSpaceComposition](MappingSpaceComposition.lean)：二回の評価からの合成、作用の単位比較からの単位、その評価の法則。通常の射と写像対象の単位からの射の同値、恒等射と単位の対応。
- [MappingSpaceUnitLaws](MappingSpaceUnitLaws.lean)：基点付き写像対象の合成の左右単位則と、単位を合成した後の評価の法則。
- [MappingSpaceAssociativity](MappingSpaceAssociativity.lean)：基点付き写像対象の合成の結合則と、三回の評価への帰着。
- [MappingSpaceArrowComposition](MappingSpaceArrowComposition.lean)：通常のスペクトル射に対応する点の評価と、通常の射の合成と写像対象の点の合成の一致。
- [MappingSpaceSimplicial](MappingSpaceSimplicial.lean)：基点を忘れた単体的写像対象、直積からの合成と単位、零次単体と通常のスペクトル射の同値。
- [MappingSpaceEnriched](MappingSpaceEnriched.lean)：基点付き写像対象の合成の因子を交換して得る豊穣構造。
- [MappingSpacePointedOrdinary](MappingSpacePointedOrdinary.lean)：基点付き豊穣構造と既存のスペクトルの圏構造の一致、Hom同値の恒等射・合成の保存。
- [MappingSpaceSimplicialEnriched](MappingSpaceSimplicialEnriched.lean)：忘却関手で移した単体的豊穣構造と、構成済みの直積からの合成・単位との一致。
- [MappingSpaceSimplicialOrdinary](MappingSpaceSimplicialOrdinary.lean)：既存の圏構造と整合するSimplicialCategoryのデータ、零次単体のHom同値との一致と恒等射・合成の保存。
- [SimplicialTensorCotensor](SimplicialTensorCotensor.lean)：通常の単体的集合への自由な基点の追加によるtensor・cotensor、二つの随伴と三つのHom同値、評価・余評価と三角形の法則。
- [SimplicialTensorNaturality](SimplicialTensorNaturality.lean)：単体的集合のtensor・cotensorの射と、三つのHom同値の三変数の自然性。
- [SimplicialTensorProduct](SimplicialTensorProduct.lean)：直積による反復tensor・cotensorの自然同型、合成随伴、評価・転置との両立。
- [SimplicialTensorProductNaturality](SimplicialTensorProductNaturality.lean)：反復tensorの比較の単体的集合の両変数の自然性。
- [SimplicialCotensorProductNaturality](SimplicialCotensorProductNaturality.lean)：反復転置と反復cotensorの比較の単体的集合の両変数の自然性。
- [SimplicialTensorUnit](SimplicialTensorUnit.lean)：Δ[0]によるtensor・cotensorの単位自然同型、cotensorの比較の評価による公式。
- [AdjointStructureMaps](AdjointStructureMaps.lean)：懸垂構造射の各段の通常のループへの随伴表示、逆転置による既存の構造射との一致と自然性。
- [SuspensionLoop](SuspensionLoop.lean)：円による懸垂・ループの関手、随伴・自然なHom同値、単位・余単位・triangle則と各段の対象の公式。
- [PointwiseTensorAssociator](PointwiseTensorAssociator.lean)：F_0の積の比較による作用の結合同型、生成対象の両変数と値域スペクトルを含む三変数の自然性。
- [PointwiseTensorAssociatorLevels](PointwiseTensorAssociatorLevels.lean)：係数加群の結同比較との一致、順逆の各段の通常のsmashの結合子との一致。
- [PointwiseTensorCoherence](PointwiseTensorCoherence.lean)：作用の五角形、右単位の三角形、左単位との整合性。
- [PointwiseTensorUnit](PointwiseTensorUnit.lean)：F_0 S^0と球面の比較、生成元の単位射との両立、作用の単位自然同型と各段の通常の左単位子との一致。
- [PointwiseTensorMapLevels](PointwiseTensorMapLevels.lean)：cotensorの前合成、生成対象のテンソル射と両変数のテンソル射の各段の通常のsmashの法則。
- [CotensorCurryNaturality](CotensorCurryNaturality.lean)：生成対象の射によるcotensorの前合成とテンソルの射、比較・転置・逆転置・評価の自然性。
- [PointwiseTensorLevelEvaluation](PointwiseTensorLevelEvaluation.lean)：各段のsmashからの余単位の評価と、転置・逆転置の通常の内部Homの各段の法則。
- [PointwiseTensorAdjunction](PointwiseTensorAdjunction.lean)：各段のsmashを持つテンソルとcotensorの随伴、転置・逆転置の相互逆性・自然性・既存の転置との比較と余単位の評価。
- [PointwiseTensorFunctor](PointwiseTensorFunctor.lean)：各段のsmashを持つテンソルの二変数関手、F_0との両変数の自然比較とスペクトル射の移送公式。
- [PointwiseTensor](PointwiseTensor.lean)：各段が通常のsmashとなるスペクトル、値域関手、F_0とのテンソル積からの全体の自然同型と各段の比較との一致。
- [CotensorMapLevels](CotensorMapLevels.lean)：cotensorの二変数の射と全体の比較の公式、基礎対称列・各段の通常の前合成・後合成の法則。
- [CotensorLevelEvaluation](CotensorLevelEvaluation.lean)：各段の逆比較の下で、cotensorの余単位の評価が通常の内部Homの評価法則を満たすことの証明。
- [FreeLeftUncurry](FreeLeftUncurry.lean)：左自由因子の比較の下での逆転置と、cotensorの全体の逆比較の相殺公式。
- [TensorFreeZeroLevels](TensorFreeZeroLevels.lean)：F_0との球面上のテンソル積の各段と通常のsmashの比較。
- [CotensorAdjunction](CotensorAdjunction.lean)：F_0とのテンソル積とcotensorの随伴、自然なHom同値、転置・逆転置・評価の公式。
- [CotensorFunctor](CotensorFunctor.lean)：cotensorの値域関手と二変数関手、F_0からの内部Homとの両変数の自然同型、スペクトル射。
- [Cotensor](Cotensor.lean)：各段が通常の内部Homとなるスペクトル、F_0からの内部Homとの全体の同型、置換作用・構造射・懸垂射の公式。
- [InternalHomShiftZero](InternalHomShiftZero.lean)：生成次数零の各段の比較、添字の置換を含まない構造射・懸垂射の直接公式とF_0への適用。
- [InternalHomShiftNaturality](InternalHomShiftNaturality.lean)：次数をずらした内部Homの両変数の射、構造射・懸垂射の直接公式の自然性。
- [InternalHomShiftSuspension](InternalHomShiftSuspension.lean)：値域の懸垂構造射による内部Homの直接公式、次数移送と第一球面の公式との一致。
- [InternalHomShiftStructure](InternalHomShiftStructure.lean)：値域の構造射と添字のブロック交換による内部Homの構造射の直接公式。
- [InternalHomShift](InternalHomShift.lean)：次数をずらした内部Homスペクトル、F_nからの内部Homとの同型、構造射・懸垂構造射との両立と移送公式。
- [InternalHomFreePermutation](InternalHomFreePermutation.lean)：F_nからの内部Homの各段の比較と後ろのブロックの置換作用、作用付き対象としての同型。
- [InternalHomFreeLevels](InternalHomFreeLevels.lean)：F_nからの内部Homの第m段と、第n+m段への基点付き内部Homの比較・第零段の特殊化。
- [InternalHomFreeNaturality](InternalHomFreeNaturality.lean)：通常の内部Hom上のスペクトル射、自由原変数の比較とF_nの比較の自然性。
- [InternalHomFree](InternalHomFree.lean)：自由原変数の内部Homと生成対称列からの通常の内部Homの比較、球面作用の移送、F_nへの特殊化。
- [InternalHomFunctor](InternalHomFunctor.lean)：内部Homの反変関手性・二変数関手、球面からの内部Homと恒等関手の自然同型。
- [Closed](Closed.lean)：球面上のテンソル積と内部Homの自然なHom同値・随伴、閉モノイダル構造。
- [InternalHom](InternalHom.lean)：球面作用を持つ内部Homスペクトルと、球面上のテンソル積からの評価射。
- [InternalHomUnderlying](InternalHomUnderlying.lean)：内部Homの基礎対称列、評価、右convolutionからの射を分類する自然なHom同値。
- [Basic](Basic.lean)：対象・射・圏、忠実な忘却関手、加群作用と法則、対象と射の構成子、各段の成分。
- [StructureMaps](StructureMaps.lean)：各次数の構造射、ブロック置換の同変性、射との両立、単位・結合則。
- [Suspension](Suspension.lean)：円のsmashから次の段への懸垂構造射と、スペクトルの射との両立。
- [Sphere](Sphere.lean)：球面モノイド自身の正則加群と、既存の連結同型との比較。
- [Free](Free.lean)：自由球面加群、生成元と射の延長、Hom同値、忘却関手との随伴と単位・余単位。
- [Evaluation](Evaluation.lean)：第n段を生成する自由スペクトルF_n、評価との随伴、延長の一意性。
- [Limits](Limits.lean)：極限・余極限、忘却関手による創出、各段の比較同型、自由関手の余極限保存。
- [FreeLevels](FreeLevels.lean)：自由スペクトルの各段の分解図式、生成元による射の決定、置換の関係式、n未満の段の零対象性。
- [FreeLevelInduction](FreeLevelInduction.lean)：第二ブロックをnに固定した誘導図式の余極限表示、m−n次球面との比較、比較同型の両方向と生成元の両立。
- [FreeLevelAction](FreeLevelAction.lean)：誘導表示の出力の対称群作用、入力の射への関手性、自由スペクトルの作用付き各段との自然同型。
- [FreeLevelQuotient](FreeLevelQuotient.lean)：球面側の対称群の関係式による余等化子表示、各段・誘導図式との比較、生成元と零対象性。
- [FreeLevelQuotientAction](FreeLevelQuotientAction.lean)：明示的な商表示上の対称群作用、入力の同変射、各段・誘導表示との作用付き自然同型と比較の合成。
- [FreeLevelPermutation](FreeLevelPermutation.lean)：n以上の段のΣ_mで添字付けた誘導商、球面側の右乗法の関係式、出力の左乗法、各段との作用付き自然同型。
- [TensorQuotient](TensorQuotient.lean)：球面上のテンソル積の基礎となる対称列の余等化子、釣り合い射とのHom同値、二変数の関手性と各段の表示。
- [Tensor](Tensor.lean)：釣り合い商上の球面作用とその法則、対称スペクトルのテンソル積と二変数関手、球面作用と両立する釣り合い射の降下。
- [TensorRightUnit](TensorRightUnit.lean)：球面スペクトルとの右テンソル積の単位同型、作用・単位射との比較と自然同型。
- [TensorLeftUnit](TensorLeftUnit.lean)：球面スペクトルとの左テンソル積の単位自然同型、作用・単位射との比較と球面自身での左右の一致。
- [TensorFreeRight](TensorFreeRight.lean)：自由球面加群との右テンソル積を対称列とのconvolutionへ比較する自然同型、生成元の公式とF_nへの特殊化。
- [TensorFreePair](TensorFreePair.lean)：二つの自由球面加群の積を生成対称列のconvolutionの自由加群へ比較する自然同型、生成元の公式とF_m・F_nへの特殊化。
- [TensorFreeAtSum](TensorFreeAtSum.lean)：F_m XとF_n Yの球面上の積をF_(m+n)(X∧Y)へ比較する同型、両方の入力に関する自然性と二変数の自然同型。
- [TensorSymmetry](TensorSymmetry.lean)：球面上のテンソル積の交換自然同型、標準射の公式・二回交換の恒等性と左右の単位比較との両立。
- [TensorAssociator](TensorAssociator.lean)：球面上の三重テンソル積の結合自然同型、左右の標準射・エピ性と結合子の順逆の公式。
- [TensorTriangle](TensorTriangle.lean)：球面を中央に置いた結合同型と左右の単位比較のtriangle整合性、逆結合同型を使う形。
- [TensorPentagon](TensorPentagon.lean)：球面上のテンソル積のpentagon整合性と四因子の標準射のエピ性。
- [TensorMonoidal](TensorMonoidal.lean)：球面単位のモノイダル構造の登録、テンソル積・射・単位・比較同型と既存の構成との一致。
- [TensorHexagon](TensorHexagon.lean)：球面上の結合・交換同型の順逆のhexagon整合性。
- [TensorSymmetric](TensorSymmetric.lean)：球面上のテンソル積の対称モノイダル構造の登録、braidingと構成済みの交換同型との一致。
- [FreeMonoidal](FreeMonoidal.lean)：自由スペクトル関手の強モノイダル・braided構造、単位・テンソル比較と既存の構成との一致。
- [TensorFreeLeft](TensorFreeLeft.lean)：自由球面加群を左因子とする積と左convolutionの自然比較、生成元の挿入の公式とF_nへの特殊化。

通常の極限・余極限はunderlying対称列から作用を誘導して構成する。
第n段への評価が両方を保存するため、各段での極限・余極限の計算が可能である。
比較同型は射影・包含との両立を含む。ホモトピー極限・余極限はモデル構造とともに後から扱う。

F_nの入力は置換作用を持たない基点付き単体的集合である。
[対称列の自由生成](../SymmetricSequence/Evaluation.lean)と自由球面加群を順に適用する。
第n段で指定した射からの延長と生成元の射も、この二段の構成と一致する。
各段の余極限表示と全単射で添字付けた生成元を構成し、出力と球面側のブロックの作用を比較した。
n未満の段は零対象である。第二ブロックをnに固定した誘導図式の余極限との比較同型も構成した。
各項はm−n次球面とXのsmashであり、第一ブロックの全単射の作用を同一視する。
出力の全単射による作用と入力の射を余極限へ誘導し、各段の作用との比較を自然同型へまとめた。
第一ブロックの対称群の関係式を表す二つの射を構成し、各段との余等化子の比較同型を得た。
n以上の段では全単射の添字は出力の対称群と同値であり、n未満では商も零対象である。
商の普遍性から出力の置換作用と入力の同変射を構成し、各段・誘導表示との作用付き自然同型を得た。
n以上の段では全単射の添字をΣ_mへ移送した余等化子と、各段との作用付き自然同型も構成した。
関係式は球面側のブロック置換の右乗法、出力の置換作用は左乗法で記述する。
球面上のテンソル積の基礎となる釣り合い商を対称列として構成した。
二つの作用を同一視する射の降下・一意性と二変数の関手性を備え、各段も余等化子として計算できる。
この商上へ球面作用を降ろし、単位・結合の作用則と、対称スペクトルのテンソル積の二変数関手を構成した。
球面スペクトルとの左右のテンソル積の単位自然同型を構成した。
球面スペクトル自身では左右の比較が一致する。
自由球面加群との右テンソル積は、生成対称列とのconvolutionへ作用を与えたスペクトルと自然同型である。
第n段からの自由スペクトルF_nとの右テンソル積にもこの比較を特殊化した。
二つの自由球面加群の積は、生成対称列のconvolutionから作る自由球面加群と自然同型である。
生成対称列の積をm+n次の自由生成へ比較し、F_m XとF_n Yの積とF_(m+n)(X∧Y)の自然同型を構成した。
球面上のテンソル積の交換自然同型と、二回の交換の恒等性・単位比較との両立も構成した。
三重テンソル積の結合自然同型を構成し、標準射上で基礎対称列の結合子とその逆を比較した。
結合同型と左右の単位比較のtriangle整合性も証明した。
pentagon整合性を証明し、球面単位のモノイダル構造を登録した。
順逆のhexagonを証明して対称モノイダル構造を登録し、braidingを構成済みの交換同型と比較した。
自由スペクトル関手の単位・テンソル比較の整合性も証明し、強モノイダル・braided構造を登録した。
自由球面加群を左因子とする積を、生成対称列との左convolutionへ比較する自然同型も構成した。
逆射は生成元を第一因子に挿入する射であり、F_nにも特殊化できる。

内部Homの基礎対称列は球面作用に関する等化子で構成し、右convolutionからの射を分類する。
等化子上の球面作用とその単位・結合則を構成し、評価を球面上のテンソル積からのスペクトル射へ降ろした。
テンソル積との自然なHom同値と随伴を構成し、閉モノイダル構造を登録した。
登録した内部Hom・評価・curryingは構成済みの対象・射に一致し、対称構造と合わせて利用できる。

内部Homの前合成・二変数関手性と評価・転置との両立を公開した。
球面からの内部Homは元のスペクトルと自然同型であり、比較の順逆の公式も使える。

自由スペクトルからの内部Homは、生成対称列からの通常の内部Homに球面作用を移送したスペクトルと同型である。
順逆の評価公式を公開し、F_nにも特殊化した。
生成対称列には反変、値域スペクトルには共変な射を構成し、比較の両変数に関する自然性を証明した。
射の基礎射は通常の内部Homの前合成・後合成であり、移送した作用は係数の交換・評価・値域の作用で記述できる。
射の基礎射と作用の公式は共通層のAPIとして公開する。F_nの比較も両変数に関して自然である。

F_nを原変数とする内部Homの第m段を、生成元から値域の第n+m段への基点付き内部Homへ比較した。
対称列側の各段の比較は値域に関して自然であり、第零段のスペクトルの比較も使える。
各段の比較は、第m段の置換と値域の後ろのm要素の置換を対応させる。
比較を対称群作用を持つ基点付き単体的集合の同型へ持ち上げた。
各段の比較を対称列全体の同型へまとめ、球面作用を移送して次数をずらした内部Homスペクトルを構成した。
F_nからの内部Homとのスペクトル同型の成分が既存の各段の比較に一致し、構造射・懸垂構造射との両立を証明した。
移送後の評価と値域の作用の公式は共通層で公開する。
各段の構造射は、通常の評価・値域の構造射・添字のブロック交換を合成して転置した射に一致する。
ブロック交換はp+(n+q)からn+(p+q)へ球面のp要素と生成元のn要素を交換する。
F_nからの内部Homの構造射も各段の比較を介してこの公式で計算できる。
円による懸垂構造射も、通常の評価・値域の懸垂構造射・添字のブロック交換を転置した射に一致する。
この添字の射は(n+q)+1からn+(q+1)へ、懸垂の一要素を生成元のn要素の後ろへ移す。
次数の等式による移送は値域の移送による後合成であり、第一球面の直接公式との一致も証明した。
F_nからの内部Homの懸垂構造射にも各段の比較を介して適用できる。
生成対象に反変、値域に共変な次数をずらした内部Homの射をスペクトル射として構成した。
各段の成分は通常の内部Homの前合成と後合成である。
比較の自然性は対称列側の一般の係数加群の各段の補題で公開する。
構造射・懸垂構造射の直接公式の両変数に関する自然性も証明した。
生成次数零では空のブロックとの交換を次数の等式による移送へ簡約できる。
各段を値域の同じ段への通常の内部Homへ比較すると、構造射・懸垂射の直接公式に添字の置換は入らない。
F_0からの内部Homの各段の比較も構成し、その構造射・懸垂射がこの直接公式に移ることを証明した。
各段の通常の内部Homの対称列へ球面作用を移し、cotensor X Eをスペクトルとして構成した。
その第q段はXからEの第q段への通常の内部Homと定義的に一致する。
F_0からの内部Homとのスペクトル全体の同型を構成し、順逆の成分が既存の各段の比較に一致することを証明した。
cotensorの置換は値域の同じ段の置換による後合成であり、構造射・懸垂射には前段階の直接公式が使える。
cotensorは生成対象に反変、値域スペクトルに共変な二変数関手として利用できる。
F_0からの内部Homとの比較は両変数に関する自然同型である。
F_0 Xとの球面上のテンソル積はcotensor関手の左随伴であり、自然なHom同値と転置・逆転置を公開した。
転置は既存の内部Homへの転置と比較の順射の合成であり、評価は比較の逆射の逆転置に一致する。
F_0 Xとの球面上のテンソル積の第q段を、通常のXとEの第q段のsmashへ比較した。
この比較は対称列の点ごとの随伴と左随伴の一意性から構成する。
左自由因子の比較の下での逆転置と、cotensorの逆比較の相殺公式を公開した。
一般の係数加群で各段の評価法則を構成し、cotensorの余単位へ接続した。
各段の逆比較を介したcotensorの評価は、通常の内部Homの評価法則を満たす。
法則を命題として公開し、具体的な係数加群の型を再展開せずに利用できる。
cotensorの二変数の射は、全体の比較の順逆で内部Homの射を移した射である。
基礎対称列と各段で、通常の内部Homの前合成・後合成の法則を満たす。

各段が通常のsmashとなるpointwiseTensorを球面作用の移送で構成した。
F_0 Xとの球面上のテンソル積との比較を、値域スペクトルに関する自然同型へまとめた。
全体の比較の各段は既存の各段の比較に一致し、置換作用と関手の射は第二因子との通常のsmashである。

pointwiseTensorは生成対象と値域スペクトルの両方に共変な二変数関手として利用できる。
F_0との全体の比較は両変数に自然であり、両変数のスペクトル射をこの比較の順逆で記述した。
pointwiseTensor関手はcotensor関手の左随伴であり、転置・逆転置の相互逆性と自然性を公開した。
既存のF_0とのテンソル積による転置・逆転置との比較公式と、余単位としての評価も構成した。

各段のsmashからの余単位は、全体の逆比較を介した既存のcotensorの評価である。
その各段は通常の内部Homの評価であり、転置・逆転置も通常の各段の転置・逆転置の法則を満たす。
法則を命題として公開し、具体的な係数加群の型を再展開せずに利用できる。

生成対象の射によるcotensorの前合成cotensorPreとテンソルの射pointwiseTensorPostを公開した。
転置はテンソル側の生成対象の射とcotensor側の前合成を対応させる。
逆転置と評価もこの対応と両立し、生成対象に関する自然性を満たす。

cotensorPreの各段は通常の内部Homの前合成である。
pointwiseTensorPostの各段は生成対象の射と同じ段の恒等射のsmashであり、
両変数の射pointwiseTensorMap f gの第q段はfとgの第q段の射の通常のsmashになる。

球面の第n段は円の反復smashである。境界を潰した単体的球面との比較は別の課題として扱う。
弱同値、モデル構造、導来smash、安定ホモトピー群はまだ登録していない。
