# 共通群論基盤：型A Coxeter群と対称群

[TypeA.lean](TypeA.lean) は ArxivFormalization から移植した一般の群論。
スペクトル・smash・円の構成には依存せず、将来のリポジトリ統合時に一本化する対象とする。

元ソースは
[ArxivFormalization/Coxeter/TypeA.lean](https://github.com/unaoya/arxiv_formalization/blob/761bc6bc1b8f18764afa9f2d439264e79da14a31/ArxivFormalization/Coxeter/TypeA.lean)。
元コミットは `761bc6bc1b8f18764afa9f2d439264e79da14a31`。
確認したファイルの SHA256 は
`16a2c3c77f0dec26ca5bb5ea6f5380c4fa599db962bedb6935d94f9fc72da188`。
移植日は2026-10-13。移植先のLeanは `v4.35.0-rc4`、Mathlibは
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。

数学部分の定義・主張と、挿入ソートによる正規形・単射性の証明を維持した。
移植時の差分は次の通り。

- namespaceを `ArxivFormalization.Coxeter` から `SerrePositivity.Coxeter` へ変更。
- `module`・public import・公開sectionを本リポジトリの形式へ合わせた。
- `Meta.Blueprint` のimportと管理用属性9個を取り除いた。数学の依存には含めない。
- 非推奨の `if_neg`・`if_pos` を現行名へ更新した（3箇所）。
- `castSucc_isLiftable` で簡約後に不要になった場合分け5行を削除した。
- `permRestrict_apply_castSucc` のsimp集合を明示した。その他は空白と行長の調整。

追加した [InvolutionRelations.lean](InvolutionRelations.lean) は、対合とbraid・可換関係を
Coxeter行列の冪の関係へ接続する二つの一般補題。
[PermutationInduction.lean](PermutationInduction.lean) は、型Aの同型を介して
恒等置換と右からの隣接互換による帰納を有限対称群へ移す一般補題。
[FirstToLast.lean](FirstToLast.lean) は、先頭を固定する尾の置換と隣接互換から
先頭を末尾へ送る置換を構成し、Mathlibの逆向きの巡回置換と比較する一般論。
[反復テンソルへの作用](../../CategoryTheory/Monoidal/PermutationAction.lean) は別の圏論層に置き、
球面への特殊化はスペクトル層に置く。

今は元リポジトリ全体をLake依存として追加しない。
この移植を二つの独立した証明として拡張せず、群論の修正時には元コミットからの差分を確認し、
両リポジトリでの適用可否を記録する。版差の調整と数学的変更を分けて管理する。
元リポジトリへの反映やリポジトリ統合は、別途その作業が依頼された時に行う。

検証は `lake build SerrePositivity.Spectra.Foundations` の後に
`lake env lean scripts/audit_spectra.lean` を実行する。
同監査は共通群論・共通モノイダル圏論とスペクトル基盤の公開宣言を含む。
