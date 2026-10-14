# 球面モノイド上の加群としての対称スペクトル

Mathlibの `CategoryTheory.Mod` を、構成済みの球面対称列へ適用する。
基礎圏は基点付き単体的集合の対称列、テンソル積は登録済みのconvolutionである。
各段の対象は基点付き単体的集合であり、球面の作用から和次数への構造射を得る。

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
比較を対称群作用を持つ基点付き単体的集合の同型へ持ち上げた。球面作用・構造射の具体式は次の段階で整える。

球面の第n段は円の反復smashである。境界を潰した単体的球面との比較は別の課題として扱う。
弱同値、モデル構造、導来smash、安定ホモトピー群はまだ登録していない。
