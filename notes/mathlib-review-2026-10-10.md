# 形式化の議論の整理と Mathlib との対応

2026年10月10日時点。対象は本プロジェクトの46モジュールと公開入口（設定の整理前は47モジュール）、および `lake-manifest.json` に固定された Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。Mathlib の現在の公開最新版についての調査ではない。

一般的な長さ・台・分解の基礎は、すでに Mathlib を利用している。次に効果が大きいのは、入力クラスのうち既存の結果から証明できる項目を減らすことと、共通する数学的な変換を一度だけ記述することである。初回は説明コメントのみを整備した。その後、承認された項目1〜3を実装した（以下の実施記録を参照）。

## 日本語の説明と形式化の範囲

初回のコメント整備時点で、全ファイルに日本語のモジュール説明があり、定理・補題・定義・構造体・クラス・インスタンスの352宣言に日本語の説明を付けた。入力クラスの各主張、構造体のデータと型クラスの計119フィールドにも説明を付けた。既存の日本語で適切に説明されている部分は維持した。統合したファイルでは、冒頭で後半の内容も案内し、旧ファイルの見出しを節見出しにそろえた。

特に次の区別を明記した。

- `IsPerfectSupported` は、有界な有限自由複体という具体的なモデルである。一般の環上の有限射影複体すべてや導来圏の完全対象との比較は、別途必要である。
- `NormalizedLength` は同型不変性と、指定したイデアルの冪で消える加群の短完全列における加法性を備えた構造である。論文の上限による性質や具体的な長さ代数の構成は含めていない。
- 長さを実数に移す `toReal`、自然数に移す `toNat` は無限長を零に送る。`finsum` も非零項が無限にある場合は零になる。定義上の等式と、有限性を確認した Euler 標数の加法性は区別する。
- Hilbert–Samuel 重複度は極限を表す式として定義されているが、極限の存在・通常の重複度との一致・正値性は未証明である。
- `TorAlg φ i V` は `V` を分解する係数拡大の左導来関手であり、このプロジェクトでは `Tor_i^A(C,V)` の順序で説明する。論文と変数の順序が異なる箇所がある。Tor の対称性の証明は使っていない。
- 補題5.2には五つの一般的な入力クラスと、補題3.5からの未証明結果への依存が残る。`Section5/Positivity` の入口も補題5.2を呼ぶ形に接続済みであり、同じ依存が明示される。

## 数学的な整理候補

### 有限長テンソル積の入力を既存の一般論から導く

`Inputs.FiniteModuleGeometry.tensor_finite` は、正則性を使わず、Noether 局所環上で証明できる。

`I M = 0` と `J N = 0` から、純テンソル上の計算で `(I + J)(M ⊗ N) = 0` が出る。したがって `√(I + J) = m_R` なら `m_R ⊆ √Ann(M ⊗ N)`。テンソル積の有限生成性と剰余体の Artin 性を使い、既存の `isFiniteLength_of_le_radical_annihilator` を適用すればよい。

この導出は確認用ファイルで Lean を通した。`#print axioms tensorFiniteReview` は `[propext, Classical.choice, Quot.sound]` のみで、`sorryAx` も交点理論の入力クラスも使わない。その後、本体の `CommutativeAlgebra/FiniteLength.lean` に `length_tensorProduct_ne_top_of_annihilator` として登録し、入力クラスから削除した。

### 二つの Euler 評価で共通する添字の変更

`ResolutionEvaluation` の正規化評価と通常評価には、整数添字から `i ↦ -i` によって自然数添字へ移る証明がある。正次数が零という条件のもとで交代和を取り直す一般補題を置けば、この部分を共通化できる。通常評価側の整数から実数への変換は別の短い段階に残すとよい。

通常の長さの写像錐加法性は、すでに `NormalizedLength.ordinary` を通じて正規化長さの一般定理から導いている。ここは重複した加法性の証明を新たに作る必要がない。

### 系2.6と補題3.5の長さ代数の適用部分

`Corollary2_6` と `Section5/NormApplication` では、極大イデアルの冪の包含を使って長さの加法性の対象を取り替え、パラメータの冪の評価を合成した環準同型に沿って書き直している。この「長さ代数の性質を基底のパラメータで表す」段階は共通化の候補である。

ただし、系2.6は冪が1の場合、補題3.5への適用はすべての冪と冪が0の場合の処理を必要とする。一つの大きな構造体にまとめるより、正の冪の消滅と商の評価を返す補題が適している。有限長加群への組成列の帰納法は、現在の `NormalizedTor` の一つの一般定理として維持できる。

### 入力クラスの大きさを見直す

`IntersectionAdditivity` の有限直和の公式は、それぞれの変数の加法性から証明し、入力から削除した。帰納法の各段階のテンソル積の有限長性も確認した。

分解の存在の入力は `RegularResolution`、Tor の一般論の入力は `TorHomologicalAlgebra` に分離した。後者の比較同型と有限長性そのものは未証明である。

### 補題5.2と正値性の入口を接続する

実施済み。現在の `core_of_inputs` は対象・仮定を直接受け取り、`firstComparison` を適用する。`Inputs.Core` と一括設定は、後続の整理で削除した。

第一比較の結論を入力から外した一方、`core_of_inputs` は補題5.2の五つの一般論の入力クラスを要求する。データの存在・第二比較・補題5.2の未証明依存を解消したわけではない。

## Mathlib で確認できた結果

以下のパスは `.lake/packages/mathlib/Mathlib/` からの相対パスである。「接続が必要」は、必要な材料があることを示し、このプロジェクトの主張がそのまま既存定理で置換できるという意味ではない。

| 内容 | Mathlib の宣言とファイル | このプロジェクトでの扱い |
|---|---|---|
| 長さの完全列に対する加法性 | `Module.length_eq_add_of_exact`、`RingTheory/Length.lean` | すでに使用。通常の長さの加法性を作り直す必要はない。 |
| 有限長と Noether・Artin の同値 | `isFiniteLength_iff_isNoetherian_isArtinian`、`RingTheory/FiniteLength.lean` | すでに使用。単純加群の有限長性などは短い適用補題。 |
| 同型による長さの不変性 | `LinearEquiv.length_eq`、`RingTheory/Length.lean` | すでに使用。 |
| 全射な環準同型に沿う長さの比較 | `Module.length_eq_of_surjective`、`RingTheory/Length.lean` | 剰余体への全射という本プロジェクトの仮定より強い。直接の置換ではない。 |
| 有限生成加群の台 | `Module.support_eq_zeroLocus`、`RingTheory/Support.lean` | `Supp M = V(Ann M)` は既存。複体の台と零ホモトピーの橋渡しは本プロジェクトの議論。 |
| 台の次元 | `Module.supportDim_eq_ringKrullDim_quotient_annihilator`、`RingTheory/KrullDimension/Module.lean` | 階数から台の次元を導く入力の材料。商環上の作用との接続が必要。 |
| 局所環の Artin 商と極大イデアルの冪 | `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`、`RingTheory/LocalRing/Quotient.lean` | `LocalAlgebra` ですでに使っている。 |
| 完全列の単射・全射の判定 | `LinearMap.injective_iff_eq_zero_of_exact`、`surjective_iff_eq_zero_of_exact`、`Algebra/Exact/Basic.lean` | 使用箇所4か所で直接適用し、private 補題2個を削除済み。 |
| 任意の射影分解で左導来関手を計算する同型 | `ProjectiveResolution.isoLeftDerivedObj`、`CategoryTheory/Abelian/LeftDerived.lean` | `Tor` の計算で使用。整数添字との変換や係数作用の比較は追加の接続が必要。 |
| 係数拡大の合成 | `ModuleCat.extendScalarsComp`、`Algebra/Category/ModuleCat/ChangeOfRings.lean` | `baseChangeCompIso` はこれを複体に適用したもの。独立の数学的な証明を重ねていない。 |
| 一般点の基底の候補 | `exists_linearIndependent_of_le_finrank`、`LinearAlgebra/Dimension/Finite.lean` | 階数個の独立な元は取れる。余核の低次元性までの接続は別に必要。 |
| 正の階数と忠実性 | `Module.finrank_eq_zero_of_not_faithfulSMul`、同上 | 対偶により正の階数から忠実性を得る候補。 |
| 階数零とねじれ | `Module.finrank_eq_zero_iff_isTorsion`、`LinearAlgebra/Dimension/Torsion/Finite.lean` | 有限生成な余核をねじれと判定する材料。 |
| 非零因子で割ったときの次元低下 | `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`、`RingTheory/KrullDimension/NonZeroDivisors.lean` | ねじれな余核の次元低下を導く材料。 |
| 整拡大の素イデアルの比較 | `Ideal.IsIntegral.under_lt_under` と lying-over の定理、`RingTheory/Ideal/GoingUp.lean` | 有限整拡大の次元不変性の材料。今回の検索では、入力と同じ形の次元等式は確認できていない。 |

小さな適用補題をすべて消す必要はない。たとえば `isZero_homology_of_isZero_X` は既存の短複体の結果を、普段使う複体の表記に直す便利な入口である。逆に、数行で既存定理に還元でき、呼び出し箇所も少ない private 補題は整理しやすい。

## そのまま使える結果を確認できなかった範囲

固定された Mathlib のソースでは、可換代数の Koszul 複体の構成・分解定理、Hilbert–Samuel 重複度のこの形の理論、交点重複度の消滅定理を、そのまま使える宣言として確認できなかった。`RingTheory/Regular/RegularSequence.lean` には正則列の定義と基本性質があるが、Koszul 正則性については TODO がある。したがって、現在の Koszul 複体の構成を丸ごと既存定義に置き換えられるとは言えない。

`CategoryTheory/Monoidal/Tor.lean` は第2変数で導来した `Tor` と第1変数で導来した `Tor'` を定義し、両者の同型は今後の課題と明記している。二つの変数の階数比較を独立に扱う現在の方針を維持する理由になる。

正則局所環の定義はあるが、任意の有限生成加群の有界有限自由分解を、この入力と同じ形で供給する定理は確認できなかった。`RingTheory/Regular/ProjectiveDimension.lean` には正則元で割ったときの射影次元の公式があるものの、正則局所環の定義から必要な分解を得るまでの接続は別問題である。

これらは検索した版での調査結果であり、別名・別形式の定理から導出できないことの証明ではない。

## 残る数学的な入力

`Inputs/IntersectionTheory` の現在の7項目は次のように整理できる。

| 入力 | 次の作業の見通し |
|---|---|
| `resolution` | 正則局所環と有限射影次元の接続、および有限自由な分解の構成が必要。 |
| `ordinaryTorIso` | 同じ分解で計算し、係数制限とホモロジー、二つのテンソル関手を同一視する。 |
| `finiteTor` | 有限生成性と台または消去元の議論が必要。今回、完成した証明は作っていない。 |
| `add_left`、`add_right` | Tor の長完全列に加え、有限性・高次数消滅を用いて交代和の加法性を示す。 |
| `generic_basis` | 独立な元の存在、余核のねじれ性、台の次元低下を接続する。 |
| `vanish` | Roberts–Gillet–Soulé の消滅定理という大きな外部入力。 |

明示的な `sorry` は引き続き7個である。論文の主定理と帰着先の主張が2個、正則局所環の入力が2個、系2.6の正値性、定理3.1の帰結、補題3.5aの正規化長さの有限性が各1個。クラスの未供給の7項目はこの7個には数えていない。

有限長テンソル積の本体への組み込みと Euler 評価の添字変更の共通化は実施済み。補題5.2の最終入口への接続も実施済みである。零ホモトピーとホモロジーの台を結ぶ議論、通常長と正規化長の共通の加法性、Koszul 生成による補題3.5bの帰着は、現在の分離を保つ価値がある。

## 承認された項目1〜3の実施記録

1. `CommutativeAlgebra/FiniteLength` に、Noether 局所環上の有限長テンソル積の定理を証明付きで追加した。`Inputs.FiniteModuleGeometry.tensor_finite` を削除し、有限拡大の階数計算と補題5.2の計6か所を新定理に置き換えた。四つの入力クラスの主張は12個から11個になった。
2. `IntersectionMultiplicity/ResolutionEvaluation` に `alternating_finsum_eq_nat` を追加し、通常長・正規化長の両方で使用した。`Inputs/LengthAlgebra` に証明済みの準備 `restrictLength`、`base_values`、`base_values_one` を追加し、系2.6と `Section5/NormApplication` の重複を除いた。新しいファイルや入力フィールドは増やしていない。
3. `CommutativeAlgebra/HomologyLength` の単射・全射判定を Mathlib の完全列の判定定理による1行の証明に置き換えた。

続く依頼で、項目5の最終入口への接続も実施した。`Inputs.Core` から第一比較を外し、`core_of_inputs` で補題5.2を適用する。また、項目3の補助補題2個は使用箇所で直接 Mathlib を使う形にして削除した。明示的な `sorry` の個数は7個のままであり、今回の変更によって新しい未証明箇所は追加していない。

## 接続後の4つの整理の実施記録

以下は再点検で挙げた候補を、その後の依頼により本体へ反映した記録である。

### 1. 台から零ホモトピーへの証明で共通の冪をとる処理

`PerfectComplex/Support` の `isSupported_of_homologySupport` の末尾で `isSupported_of_forall` を再利用した。各生成元の零ホモトピーを `nonempty_homotopy_smul_id_zero_iff` でホモトピー圏の等式に変え、既存補題を適用する。`Finset.univ.sup` とスカラー倍による冪の調整を重ねて書く必要がなくなった。

ホモロジーの次数全体について冪をそろえる前段の議論は、有界性を使う別の操作なので残した。

### 2. 正の階数から台の次元を導く

`CommutativeAlgebra/LocalAlgebra` に `supportDim_of_quotient_rank_pos` を証明した。商環上の正の階数から忠実性を得て、`Module.comap_annihilator` によって `Ann_R M = I` を導き、Mathlib の台の次元公式を適用する。正則性、局所性、Noether 性は不要であり、商環上の有限生成性も定理の仮定から外せた。

`FiniteModuleGeometry.supportDim_of_rank_pos` を削除し、有限拡大の階数計算で新定理を使った。

### 3. 有限直和の評価を加法性から導く

`IntersectionMultiplicity/FiniteExtension` に `chi_pi_left_of_additivity` と `chi_pi_right_of_additivity` を証明した。零個の場合は零加群上の加法性から `χ = 0` を得る。後続段階は、先頭成分への射影と残りの成分の埋め込みによる分裂短完全列に加法性を使う。

有限長性は `TensorProduct.piLeft` / `piRight` と `Module.length_pi_of_fintype` による。Tor の対称性や `χ` の同型不変性を別途仮定する必要はなかった。二つの定理は正則性を仮定せず、加法性の入力だけを使う。

入力フィールド `pi_left` と `pi_right` を削除し、有限拡大の証明の使用箇所も置き換えた。

### 4. 分解の存在と Tor の一般論を分ける

`RegularHomologicalAlgebra` を次の二つに分離した。

- `RegularResolution`：正則局所環上の有限生成加群に、有界有限自由分解が存在するという入力。
- `TorHomologicalAlgebra`：任意の可換環上の `ordinaryTorIso` と、Noether 環上の `finiteTor` の入力。

比較同型と Tor の有限長性の証明は今回行っていない。入力の数学的な適用範囲と依存関係を分けた変更である。`ResolutionEvaluation` は分解の存在を仮定せず、与えられた分解を使用する。台を持つ複体を作る定理も正則局所環から Noether 環に一般化した。補題5.2と正値性の入口は二つの入力を明示的に受け取る。

入力を整理する単位は4クラスから5クラスになったが、仮定する主張の総数は11個から8個に減った。クラスとして束ねるか個別の仮定にするかは、次の相談事項として残す。

### 維持する分離

通常長の Euler 加法性はすでに正規化長の一般定理を利用しており、再度統合する必要はない。正値性の最後の算術 `chi_pos_of_comparisons` は二つの比較を明示的に受け取る形にし、その外側の `core_of_inputs` で論文の補題を接続する。これにより、算術の議論と論文固有の依存関係を区別できる。

### 今回の検証

4つの整理後も全体ビルドは成功した。台の冪の共通化、台の次元、左右の有限直和の定理について `#print axioms` は `[propext, Classical.choice, Quot.sound]` のみだった。左右の公式は明示した加法性の入力に依存する。明示的な `sorry` は7個のままである。

`lake build SerrePositivity` と `git diff --check` は成功した。`#print core_of_inputs` で第一比較を `firstComparison` から得ていることを確認した。`#print axioms core_of_inputs` には `sorryAx` が現れる。これは補題5.2から既存の未証明結果への依存を接続したためであり、新たな `sorry` を追加したものではない。

## 一括設定を減らす整理の実施記録

相談した方針を本体へ反映した。

### 補題5.2の仮定と結論

`CoreData` と `CoreData.IsPaperData` を削除し、`firstComparison` が次を直接受け取る形にした。

- `R/P` と `R/Q` 上の有限代数 `D, E`、正則局所環 `A`、長さを測る代数 `C`、作用群 `G`。
- パラメータ系、剰余体への全射、スペクトルへの全射、幾何的推移性。
- 商環上の階数の正値性と、商環の次元を自然数で指定する等式。
- 正規化長さ `λ` と、高次 Koszul ホモロジーの消滅 `hzero`、商の長さの公式 `hquot`。
- 残る一般論の入力、標数、次元の和、閉点での交わりの条件。

結論も `FirstComparison` という命題名で包まず、Tor の長さの有限性と共役和の等式を直接書いた。`aD`, `aE` と `aD_eq`, `aE_eq` はなくなり、`Module.finrank` をそのまま使う。第二の正規化基底・群作用・剰余体条件や、第一の群が Galois 群であるという未使用の条件も持ち回らない。必要な幾何的推移性は独立の仮定として残る。

商環の次元の指定を直接受け取るため、以前の `ringDim_of_rank_pos` は呼ばれなくなった。この未使用の入力を削除し、`FiniteModuleGeometry` は一つの入力だけを持つ `GenericBasis` に改名した。入力クラスの項目は8個から7個になったが、この減少は次元不変性を証明したという意味ではない。対応する次元の等式は定理の明示的な仮定である。

### 正値性の入口

`core_of_inputs` も同じ対象と条件を直接受け取り、第二比較の実数値の族 `b`、比較等式 `hsecond`、正値性 `hpos` を別の引数にした。`SecondComparison` と一括存在入力 `Inputs.Core` は削除した。

この定理は、与えられた対象について補題5.2と第二比較から正値性を導く。環・素イデアルの条件だけから対象を構成する定理ではない。以前も構成は `Inputs.Core` の未供給の入力に含まれており、構成や第二比較が新たに証明されたわけではない。主定理と帰着先の未証明のステートメントは変更していない。

最後の有限和の算術を `chi_pos_of_comparisons` として独立させた。ここでは群構造や局所環の構造は不要で、有限な非空の添字集合と正の階数因子を使う。

### 正規化基底の構成と利用の分離

- `normComparison_of_lengthAlgebra` は有限性、正則性、パラメータの条件、剰余体への全射、長さの二つの評価を直接受け取る。完備性・分離性は要求しない。
- `cor_2_6_tor` も `IsRegularNormalizationBase` を受け取らず、実際に使う正則性・有限性・パラメータ系の条件を受け取る。
- 正規化長さの定義域の制限は、一般論 `NormalizedLength.restrictToBase` として `PerfectComplex/NormalizedLength` に移した。
- `LengthAlgebraProps.base_values` はパラメータ系から評価の値を取り出すだけになり、有限性や、制限後の長さへの変換を必要としない。構成された長さ代数から `hzero`・`hquot` を得る入口として使える。

`IsRegularNormalizationBase`、`LengthAlgebraData`、`LengthAlgebraProps` は定理2.5の存在入力に残す。未証明の `cor_2_6_pos` のステートメントも従来の構成条件を保持した。評価関数とその公理を表す `NormalizedLength` も維持する。

### ファイルと依存関係

不要になった `Paper/Section5/Setup.lean` を削除した。ひねった係数構造は `twistedAlgebraMap`、その評価は `twistedEuler` として `FirstComparison.lean` に置く。`FirstComparison.lean`、`Lemma5_2.lean`、`Positivity.lean` はいずれも設定の構造体を経由しない。公開入口の import と README も更新した。

全体ビルドと差分の空白検査に成功した。明示的な `sorry` は7個のまま。`firstComparison` と `core_of_inputs` は引き続き既存の未証明結果に依存する。
