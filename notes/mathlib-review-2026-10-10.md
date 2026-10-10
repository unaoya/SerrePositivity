# 形式化の議論の整理と Mathlib との対応

> 最新の変更：入力クラス3つは名前付きの `sorry` 定理へ移行した。
> 以下の入力クラスについての記述は各作業時点の履歴。最新の優先順位は `PLAN.md` 冒頭参照。
> 系2.6の正値性は保留し、3.5a の正規化長さの有限性に着手した。

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

## 一般論の証明の追加：一般点の基底と通常 Tor の比較

Roberts–Gillet–Soulé の消滅定理は、引き続き `Inputs.IntersectionVanishing` として引用する。
今回、次の二項目を Mathlib に基づく証明で置き換えた。

1. `CommutativeAlgebra/LocalAlgebra.lean` の `exists_genericBasis`：
   `exists_linearIndependent_of_le_finrank` で階数個の独立な元を取り、自由部分加群を作る。
   `Module.finrank_quotient_add_finrank_le` から余核の階数は零、
   `Module.finrank_eq_zero_iff_isTorsion` からねじれ加群となる。
   有限生成ねじれ加群全体を消す非零因子を選び、
   `ringKrullDim_succ_le_of_surjective` で `dim Supp(coker) + 1 ≤ dim(R/I)` を得る。
   有限次元の場合の狭義不等式に直して有限拡大の階数倍公式に適用した。
   正則性・局所性・正の階数を仮定せずに証明でき、入力クラス `GenericBasis` を削除した。
2. `HomologicalAlgebra/Tor.lean` の `ordinaryTorIso`：
   係数拡大後の係数制限と `T ⊗[R] -` の自然同型を構成する。
   `ShortComplex.mapHomologyIso` による係数制限とホモロジーの可換性、
   既存の整数添字と自然数添字の分解の比較、`ProjectiveResolution.isoLeftDerivedObj` を合成する。
   通常の Euler 評価および台つき完全複体の構成でこの証明済み同型を使うようにした。
   `TorHomologicalAlgebra` から比較の項目を削除し、残った有限長性の入力を `TorFiniteLength` とした。

以上で `Inputs/IntersectionTheory.lean` の未供給の入力は7項目から5項目へ減った。
残るのは、有界有限自由分解の存在、Tor の有限長性、左右の加法性、引用する消滅定理である。
通常 Euler 評価の等式 `chiOrd_baseChange_resolution` には、このファイルの入力クラスが不要になった。
一般点の基底の構成に正の階数が不要になったため、有限拡大の公式と補題5.2から不要になった
第1変数の階数の正値条件も除いた。最終的な正値性の導出では引き続き両方の階数の正値性を仮定する。
明示的な `sorry` の7箇所（補題3.5など）は今回の証明対象に含めず、新しい `sorry` は追加していない。

検証：`lake build SerrePositivity` は成功（2856 jobs）。上記の次元評価・基底の構成・
自然同型・Tor 比較・`chiOrd_baseChange_resolution` の `#print axioms` は、いずれも
`propext`, `Classical.choice`, `Quot.sound` のみで、`sorryAx` に依存しない。

## 導来関手を基礎とする一般論の整備

既存の定義は Mathlib の `Functor.leftDerived` と `CategoryTheory.Tor` を維持し、
係数拡大に特化していた証明を一般の加法的関手の証明に置き換えた。

### 今回証明したこと

- `Resolution.leftDerivedIsoCochain`（宣言の名前空間は `SerrePositivity`）：
  加群圏の間の加法的関手を、任意の射影コチェイン分解で計算する同型。
  Mathlib の `ProjectiveResolution.isoLeftDerivedObj` と添字の比較を合成する。
- `isZero_leftDerived_eventually_of_resolution`：
  左側で有界な射影コチェイン分解から高次左導来関手の消滅を導く。
  正則性や有限生成性は仮定しない。
- `leftDerived_longExact`：任意の加法的関手の左導来関手に対する長完全列。
  既存の係数拡大専用の写像錐の証明を一般化し、`torAlg_longExact` はその適用にした。
  通常の任意の加群を係数とする `torModule_longExact` も同じ一般定理から得る。
- `torModuleZeroEquiv` と `torModuleIsoCochain`：通常の Tor の零次の同一視と分解による計算。
  代数構造をもたない加群も扱う。
- `finite_torModule`：Noether 環上の有限生成加群どうしの Tor は各次数で有限生成。
  Mathlib の `Module.Finite.exists_fin'` で有限自由加群からの全射を取り、
  核が有限生成であることと Tor の長完全列を使って次数で帰納する。
  `Tor₀` はテンソル積、自由加群の高次 Tor は Mathlib の定理で零なので、
  連結射によって一つ低い次数の Tor に単射を得る。この証明には正則性も有界分解も不要。

### Mathlib の到達点と残る作業

参照したのは、このプロジェクトが固定している Mathlib のソースである。

- `CategoryTheory/Abelian/LeftDerived.lean`：分解による計算とその自然性、零次の比較、射影対象上の高次消滅。
- `CategoryTheory/Monoidal/Tor.lean`：第2変数で導来する `Tor` と、第1変数で導来する `Tor'`。
  両者の比較はファイル冒頭でも未整備と明記されている。
- `Algebra/Homology/Bifunctor.lean`、`TotalComplex.lean`、`TotalComplexSymmetry.lean`：
  二重複体の全複体と交換の構成はある。Tor の両変数の比較をこれだけで得られるわけではなく、
  分解を増大射で比較したときに擬同型になることの証明が必要である。
- `Algebra/Category/ModuleCat/Localization.lean`：局所化関手、その完全性、有限極限・余極限の保存。
  今後の Tor の局所化との比較に利用できる。

現在の長完全列は構成した射の完全性を証明する形である。
導来関手の標準の射との一致と連結射の自然性は、まだ証明していない。
Tor の両変数の比較・対称性、局所化との比較と台の評価、有限長性、Euler 数の左右の加法性は残る。
今回の `finite_torModule` は有限生成性の証明であり、有限長性の入力 `TorFiniteLength` の解消ではない。
新しい未証明入力や `sorry` は追加していない。

検証：全体ビルド成功（2875 jobs）、差分の空白検査成功。
今回の分解計算、高次消滅、零次 Tor、一般の長完全列とその二つの適用、Tor の有限生成性、
既存の `ordinaryTorIso` の公理依存はいずれも `propext`, `Classical.choice`, `Quot.sound` のみだった。

## 続報：Tor の台と有限長性の入力を解消

上の「有限長性は残る」という段階から、次の一般論を証明した。

- 加法的関手の左導来関手も加法的である。環準同型に沿う射のスカラー倍の保存も
  左導来関手へ移る。これを `Resolution.lean` にまとめた。
- 複体の各項の零化イデアルは、その次数のホモロジーの零化イデアルに含まれる。
  この事実と導来関手のスカラー作用から、Tor は両変数の零化イデアルで消える。
- 有限生成加群について、`Supp(M ⊗ N) = Supp(M) ∩ Supp(N)`。
  Mathlib の剰余体へのテンソル積による台の判定と、体上の非零テンソル積を使う。
- 有限長加群の台に属する素イデアルはすべて極大である。Noether 環上の有限生成加群では
  逆も成立する。逆向きは零化イデアルによる商の零次元性と Artin 性による。
- `support_torModule_subset`：有限生成加群どうしの Tor の台は両方の台の共通部分に含まれる。
  零化イデアルの包含と Mathlib の `Module.mem_support_iff_of_finite` で直接証明する。
  この証明には Tor の局所化比較や両変数の対称性を先に構築する必要はない。
- `isFiniteLength_torModule`：Noether 環上の有限生成加群のテンソル積が有限長なら、
  すべての Tor が有限長である。既に証明した有限生成性と上の台の評価を組み合わせる。
  正則性・有界有限自由分解は仮定しない。

利用側も更新した。`TorFiniteLength` 入力クラスを削除し、補題5.2と Section 5 の仮定から除いた。
`ResolutionEvaluation.lean` は一般論の入力ファイルを import せず、証明済み定理を使う。
有限長性の移送は長さの等式の変形から `LinearEquiv.isFiniteLength` に簡略化した。
係数拡大版 Tor の零化も一般の左導来関手の定理の適用へ短縮し、零加群の Tor の消滅は
加法的関手の零対象保存から一様に証明する。

`IntersectionTheory.lean` に残る入力は3クラス・4主張：有界有限自由分解の存在、
交点重複度の左右の加法性、Roberts–Gillet–Soulé の消滅定理である。
長完全列の標準射との一致・自然性、Tor の両変数の比較は引き続き未整備。
今回は新しい入力・公理・`sorry` を追加していない。

検証：全体ビルド成功（2875 jobs）、`git diff --check` 成功。
新しい14個の基礎定理・適用先を `#print axioms` で確認し、すべて
`propext`, `Classical.choice`, `Quot.sound` のみだった。
特に `isFiniteLength_torModule` と `isPerfectSupported_baseChange_resolution` に
`sorryAx` への依存はない。既存の論文側の未証明結果は引き続き残る。

## 続報：交点重複度の左右の加法性を証明

`chi` の定義を変更せず、次の順序で加法性を証明した。

1. `HomologyLength.lean` の `lengthInt_eq_add_range`：有限長な中央の項の長さを、
   前後の射の像の長さの和で表す。Mathlib の `Module.length_eq_add_of_exact` を使う。
2. `lengthEuler_longExact` と `lengthEuler_finsum_longExact`：三列からなる長完全列について、
   切断した交代和の誤差を連結射の像の長さとして計算する。
   各項が有限長で、高次が零になれば、中央の交代和は左右の交代和の和になる。
3. `TorLES.lean` の `tensorComplex_shortExact` と `torModule_longExact_left`：
   第2変数の射影分解を固定し、各項の平坦性によって第1変数の短完全列を複体の短完全列にする。
   Mathlib の `HomologicalComplex.shortExact_of_degreewise_shortExact` と
   `ShortComplex.ShortExact.homology_exact₁/₂/₃` を使い、分解との比較同型で Tor に移す。
   Tor の対称性は仮定しない。長完全列の標準射との一致や連結射の自然性は引き続き別の課題であり、
   今回の数値的加法性には必要ない。
4. 新しい `IntersectionMultiplicity/Additivity.lean`：まず Noether 環上で高次 Tor の消滅を
   明示した `chi_add_left_of_eventually` と `chi_add_right_of_eventually` を証明する。
   中央のテンソル積の有限長性から、台の包含によって両端の有限長性を導き、
   証明済みの Tor の有限長性と長完全列の交代和を適用する。
5. 正則局所環では `RegularResolution` の分解の存在から高次 Tor の消滅を導き、
   `chi_add_left` と `chi_add_right` を得る。加法性を別に仮定する必要はなくなった。

`IntersectionAdditivity` クラスを削除し、有限直和の評価、有限拡大の階数倍の公式、補題5.2、
Section 5 の正値性の記述を更新した。一般論の入力として残るのは
`RegularResolution` と `IntersectionVanishing` の2クラス・2主張である。
前者は引き続き未証明の分解存在の仮定、後者は指定どおり引用扱いの消滅定理である。
新しい `sorry` や公理は追加していない。

検証：全体ビルド成功（2877 jobs）、差分の空白検査成功。
長完全列の交代和、第1変数の Tor 長完全列、一般の高次消滅条件のもとでの左右の加法性、
正則局所環への適用、および `chi_finite_extensions` の計11宣言について公理依存を確認した。
いずれも `propext`, `Classical.choice`, `Quot.sound` のみで、`sorryAx` への依存はない。
ただし、`chi_add_left/right` は明示的な引数として `RegularResolution` を受け取り、
`chi_finite_extensions` はさらに `IntersectionVanishing` を受け取ることも型で確認した。
公理依存検査が、これらの入力の証明を与えるわけではない。


## 入力の明示化と次の証明課題（2026-10-10）

入力クラス `RegularResolution`、`IntersectionVanishing`、`LengthAlgebra` を廃止した。
それぞれ `Inputs.regularResolution`、`Inputs.intersectionVanishing`、
`Inputs.exists_lengthAlgebra` という名前付きの `sorry` 定理に置き換えた。
分解と消滅定理の呼び出しは証明内で行い、利用先の入力クラス引数を削除した。
長さ代数の存在定理は、現在まだデータ構成段階で使われていない。

検証：全体の `lake build` が成功。`#print axioms` で三つの未証明定理と
`chi_add_left`、`chi_add_right`、`firstComparison` に `sorryAx` が現れることを確認した。
直接の `sorry` は7か所から10か所へ増えたが、増分は従来入力クラスに隠れていた三つの主張である。

3.5a の準備として、`lambdaHomology_cone_le`、`lambdaHomology_cone_ne_top`、
`lambdaHomology_ne_top_of_nullHomotopic_cone` を証明した。三つとも公理依存は
`propext`、`Classical.choice`、`Quot.sound` のみで `sorryAx` を含まない。
3.5a 本体の `sorry` は残っており、Koszul テンソルと有限フィルトレーションの接続を続ける。
系2.6の正値性、有限自由分解の存在、正則パラメータの正則性は今回証明しない。
Theorem 3.1 の引用も維持する。最新の順序は `PLAN.md` 冒頭に記録した。

## 設定の構造体の廃止（2026-10-10）

入力クラスに続いて、`Setup34`、`IsRegularNormalizationBase`、`LengthAlgebraProps`、
`LengthAlgebraData` も削除した。各定理の前提は個別の引数とし、定理2.5の存在結論は
環・環構造・代数構造・正規化長さを直接量化して、四つの性質を明記する。
補題3.4では完備性・標数・整域性等の使っていなかった仮定を除いた。
系2.6の Tor 評価も必要な (2.4)、(2.6) だけを受け取る。
未証明の系2.6の正値性と定理2.5では、元の前提と結論を展開して保持している。
仮定の束を別名の連言へ置き換えることはしない。
