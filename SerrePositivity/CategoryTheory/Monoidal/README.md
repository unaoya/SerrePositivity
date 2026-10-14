# 共通のモノイダル圏論基盤

一般のモノイダル圏での内部加群と、対称モノイダル圏での反復テンソル・置換作用を置く。
群論の型Aと対称群の同型は `GroupTheory/Coxeter` へ依存し、
スペクトル・基点付き単体的集合・円の構成には依存しない。

- [TensorPowers](TensorPowers.lean)：反復テンソル、射の関手性、次数の連結同型。
- [TensorPowerCoherence](TensorPowerCoherence.lean)：次数の移送を含む連結の左右単位・結合の整合性。
- [TensorPowerBlockGenerators](TensorPowerBlockGenerators.lean)：右ブロックの隣接交換と連結の両立。
- [TensorPowerLeftBlock](TensorPowerLeftBlock.lean)：先頭二因子の一般比較と、左ブロックの隣接交換の両立。
- [TensorPowerBlockPermutations](TensorPowerBlockPermutations.lean)：左右の任意のブロック置換に関する連結の同変性。
- [TensorPowerFirstCrossing](TensorPowerFirstCrossing.lean)：先頭因子を末尾へ移す隣接交換の列とbraidingの比較。
- [TensorPowerFirstCrossingAction](TensorPowerFirstCrossingAction.lean)：その移動を既存の対称群作用と巡回置換へ接続する。
- [TensorPermutations](TensorPermutations.lean)：最初の二因子の交換と自然性。
- [AdjacentTranspositions](AdjacentTranspositions.lean)：全位置の隣接交換、対合性、遠隔可換性。
- [AdjacentBraid](AdjacentBraid.lean)：Yang–Baxterから全位置のbraid関係への接続。
- [PermutationAction](PermutationAction.lean)：型Aの普遍性と対称群の同型による全次数の作用。
- [PowerBijectionFunctor](PowerBijectionFunctor.lean)：全置換作用を有限全単射圏上の一つの関手へまとめる。
- [PowerBijectionAppend](PowerBijectionAppend.lean)：連結を全単射圏上の一つの自然変換へまとめる。
- [BraidingPreservation](BraidingPreservation.lean)：モノイダル関手のbraidingの保存をテンソル積へ拡張する。
- [FreeModule](FreeModule.lean)：一般のモノイド対象上の自由内部加群、生成元によるHom同値、忘却関手との随伴。
- [FunctorTransport](../FunctorTransport.lean)：対象ごとの同型による関手の移送と、元の関手との自然同型、二変数の射との両立と順逆の比較公式。
- [ModuleInternalHomTransportComparison](ModuleInternalHomTransportComparison.lean)：比較同型の合成による二段階の作用移送の加群比較、順逆の基礎射の公式。
- [ModuleInternalHomTransport](ModuleInternalHomTransport.lean)：通常の内部Homの作用の同型による移送、加群の同型、移送後の評価と値域の作用の公式。
- [ModuleInternalHomFreeLeftEvaluation](ModuleInternalHomFreeLeftEvaluation.lean)：左自由因子の比較の下での逆転置と通常の内部Homの評価の公式。
- [ModuleInternalHomFreeNaturality](ModuleInternalHomFreeNaturality.lean)：自由原変数の比較の反変・共変自然性、通常の内部Homへの射の移送、値域の作用による作用公式。
- [ModuleInternalHomFree](ModuleInternalHomFree.lean)：自由原変数の内部Homの基礎対象の比較、生成元上の評価公式、作用の移送と加群の同型。
- [ModuleInternalHomFunctor](ModuleInternalHomFunctor.lean)：内部Homの前合成・二変数関手性と、正則加群からの内部Homの自然比較。
- [ModuleClosed](ModuleClosed.lean)：釣り合いテンソル積との自然なHom同値・随伴、内部Hom関手、閉モノイダル構造。
- [ModuleInternalHomAction](ModuleInternalHomAction.lean)：可換係数上の内部Homの作用、単位・結合則、釣り合いテンソル積からの加群としての評価。
- [ModuleInternalHom](ModuleInternalHom.lean)：作用の等化子、評価、線形射と右テンソル加群の射のHom同値。
- [ModuleTransport](ModuleTransport.lean)：任意の基礎対象の同型による内部加群の作用の移送、全体の同型と基礎射・作用の公式。
- [ModuleLimits](ModuleLimits.lean)：内部加群の極限錐の構成、忘却関手による極限の創出と同型の反映。
- [ModuleColimits](ModuleColimits.lean)：左テンソルの余極限保存を仮定した内部加群の余極限と創出。
- [BalancedTensor](BalancedTensor.lean)：二つの加群作用を同一視する余等化子、釣り合い射とのHom同値、標準射のエピ性と二変数の関手性。
- [TensorRightModule](TensorRightModule.lean)：第一因子から得る右テンソルの加群作用、加群の射・結合子、可換係数の左右の作用の整合性。
- [BalancedTensorModule](BalancedTensorModule.lean)：釣り合い商上の加群作用、作用の法則、加群圏の二変数関手と線形な釣り合い射の降下。
- [BalancedTensorRightUnit](BalancedTensorRightUnit.lean)：正則加群との右テンソル積の単位同型、順逆の基礎射の公式と自然同型。
- [BalancedTensorLeftUnit](BalancedTensorLeftUnit.lean)：正則加群との左テンソル積の単位同型、作用・単位射との比較と自然同型。
- [BalancedTensorFreeRight](BalancedTensorFreeRight.lean)：自由加群との右テンソル積を通常の右テンソルへ比較する加群同型、生成元の公式と二変数の自然同型。
- [BalancedTensorFreePair](BalancedTensorFreePair.lean)：二つの自由加群の積を生成対象の積の自由加群へ比較する自然同型、結合子と生成元の公式。
- [BalancedTensorSymmetry](BalancedTensorSymmetry.lean)：対称構造による釣り合い商の交換同型、加群作用との両立・自然性・二回交換の恒等性と単位比較との両立。
- [BalancedTensorIterated](BalancedTensorIterated.lean)：釣り合い商の左右テンソル後の降下、商の右作用の公式と三因子の標準射・エピ性・自然性。
- [BalancedTensorAssociator](BalancedTensorAssociator.lean)：二段の釣り合い商の結合比較、順逆の標準射の公式、加群の結合同型と三変数の自然同型。
- [BalancedTensorTriangle](BalancedTensorTriangle.lean)：結合同型と左右の単位比較のtriangle整合性、逆結合同型を使う経路の一致。
- [BalancedTensorPentagon](BalancedTensorPentagon.lean)：四因子の五つの結合順の標準射、五辺の結合比較とpentagon整合性。
- [BalancedTensorMonoidal](BalancedTensorMonoidal.lean)：釣り合いテンソル積と正則加群単位による内部加群圏のモノイダル構造の登録。
- [BalancedTensorHexagon](BalancedTensorHexagon.lean)：三因子の標準射上の内外の交換公式と順逆のhexagon整合性。
- [BalancedTensorSymmetric](BalancedTensorSymmetric.lean)：構成済みの交換同型による内部加群圏の対称モノイダル構造の登録。
- [FreeModuleMonoidal](FreeModuleMonoidal.lean)：自由加群関手の単位比較、生成元上の結合・単位・交換の整合性と強モノイダル・braided関手の登録。
- [BalancedTensorFreeAssociator](BalancedTensorFreeAssociator.lean)：二つの左自由因子の結同比較と、基礎圏の結合子・逆結合子との一致。
- [BalancedTensorFreeLeft](BalancedTensorFreeLeft.lean)：交換で移した左テンソルの作用、左自由因子の比較同型・生成元の挿入と二変数の自然同型。

極限の構成にはテンソル積の極限保存を仮定しない。
余極限の構成では、全ての左テンソルが対象とする図式の形の余極限を保存することを仮定する。
閉モノイダル圏では左テンソルの随伴からこの仮定を供給できる。

釣り合いテンソル積の基礎対象はbraidingと余等化子から構成する。
係数の可換性と左テンソルの余等化子保存から、基礎対象上の加群作用と二変数関手も構成した。
正則加群との左右のテンソル積の単位同型と自然性も証明した。
自由加群を右因子とする場合、通常の右テンソルとの比較も二変数の自然同型として構成した。
二つの自由加群の釣り合いテンソル積と、生成対象の積の自由加群との自然同型も構成した。
対称構造から商上の交換自然同型を構成し、二回の交換の恒等性と単位比較との両立も証明した。
左右のテンソルの余等化子保存から、反復釣り合い商の結合自然同型も構成した。
結合同型と左右の単位比較のtriangle整合性も証明した。
四因子の標準射からpentagonを証明し、加群圏のモノイダル構造を登録した。
順逆のhexagonも証明し、基礎圏が対称な場合の内部加群圏の対称モノイダル構造を登録した。
自由内部加群関手も、構成済みの積の比較を使う強モノイダル・braided関手として登録した。
左自由因子の積も、生成対象を加群の左にテンソルした加群と自然同型で比較した。

モノイダル構造を使わない補助結果として、
[InitialColimits](../Limits/InitialColimits.lean) に始対象の図式の余極限の始対象性を置く。

将来の共通数学ライブラリへまとめるための配置であり、今は独立したパッケージを新設しない。
既存の `Spectra/SymmetricSequence` の四つの一般論のimport経路は互換入口として維持する。
宣言のnamespace `SerrePositivity.TensorPowers` と既存の宣言名は変更していない。
球面に固有の対象や作用の特殊化は `Spectra/SymmetricSequence` に残す。

有限全単射圏そのものは [FiniteBijection](../FiniteBijection.lean)、
任意の対象の族と各段の作用から関手を作る一般論は
[FiniteBijectionAction](../FiniteBijectionAction.lean) に置く。
これらはモノイダル構造を仮定しない共通の圏論であり、対称列以外にも使える。
以前の `Spectra/SymmetricSequence/FiniteBijection` のimport経路も互換入口として維持する。

有限全単射のブロックへの組み合わせは [FiniteBlockEquiv](../FiniteBlockEquiv.lean) に置く。
既存の `Spectra/SymmetricSequence/DisjointUnion` からも同じ宣言を利用できる。
直和の対象・射・二変数関手は [FiniteBijectionSum](../FiniteBijectionSum.lean) に置き、
その `DisjointUnion` の経路を互換入口として維持する。
