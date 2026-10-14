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
- [ModuleLimits](ModuleLimits.lean)：内部加群の極限錐の構成、忘却関手による極限の創出と同型の反映。
- [ModuleColimits](ModuleColimits.lean)：左テンソルの余極限保存を仮定した内部加群の余極限と創出。
- [BalancedTensor](BalancedTensor.lean)：二つの加群作用を同一視する余等化子、釣り合い射とのHom同値、標準射のエピ性と二変数の関手性。
- [TensorRightModule](TensorRightModule.lean)：第一因子から得る右テンソルの加群作用、加群の射・結合子、可換係数の左右の作用の整合性。
- [BalancedTensorModule](BalancedTensorModule.lean)：釣り合い商上の加群作用、作用の法則、加群圏の二変数関手と線形な釣り合い射の降下。
- [BalancedTensorRightUnit](BalancedTensorRightUnit.lean)：正則加群との右テンソル積の単位同型、順逆の基礎射の公式と自然同型。
- [BalancedTensorLeftUnit](BalancedTensorLeftUnit.lean)：正則加群との左テンソル積の単位同型、作用・単位射との比較と自然同型。

極限の構成にはテンソル積の極限保存を仮定しない。
余極限の構成では、全ての左テンソルが対象とする図式の形の余極限を保存することを仮定する。
閉モノイダル圏では左テンソルの随伴からこの仮定を供給できる。

釣り合いテンソル積の基礎対象はbraidingと余等化子から構成する。
係数の可換性と左テンソルの余等化子保存から、基礎対象上の加群作用と二変数関手も構成した。
正則加群との左右のテンソル積の単位同型と自然性も証明した。
結合子・対称性と加群圏のモノイダル構造は今後登録する。

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
