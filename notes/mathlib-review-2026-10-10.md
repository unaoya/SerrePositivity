# Mathlib との対応

2026-10-10 調査、同日整理。対象は `lake-manifest.json` に固定された Mathlib
`e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。Mathlib の公開最新版についての調査ではない。

このノートには、固定版の Mathlib で確認できた結果と確認できなかった範囲、および形式化の範囲についての注意を残す。
入力クラスを段階的に減らし、名前付きの `sorry` 定理へ移した作業の実施記録は削除した（git の履歴にある）。
現在の方針は `PLAN.md` 冒頭と §1 にある。

## 形式化の範囲についての注意

- `IsPerfectSupported` は、有界な有限自由複体という具体的なモデルである。一般の環上の有限射影複体すべてや
  導来圏の完全対象との比較は、別途必要である。
- `NormalizedLength` は同型不変性と、指定したイデアルの冪で消える加群の短完全列における加法性を備えた構造である。
  論文の上限の性質（(2.3)）は具体的な塔の長さ `λ_∞` の側で扱う。
- 長さを実数に移す `toReal`、自然数に移す `toNat` は無限長を零に送る。`finsum` も非零項が無限にある場合は零になる。
  定義上の等式と、有限性を確認した Euler 標数の加法性は区別する。
- `TorAlg φ i V` は `V` を分解する係数拡大の左導来関手であり、このプロジェクトでは `Tor_i^A(C,V)` の順序で説明する。
  論文と変数の順序が異なる箇所がある。

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

## 導来関手まわりの Mathlib の到達点

参照したのは、このプロジェクトが固定している Mathlib のソースである。

- `CategoryTheory/Abelian/LeftDerived.lean`：分解による計算とその自然性、零次の比較、射影対象上の高次消滅。
- `CategoryTheory/Monoidal/Tor.lean`：第2変数で導来する `Tor` と、第1変数で導来する `Tor'`。
  両者の比較はファイル冒頭でも未整備と明記されている。
- `Algebra/Homology/Bifunctor.lean`、`TotalComplex.lean`、`TotalComplexSymmetry.lean`：
  二重複体の全複体と交換の構成はある。Tor の両変数の比較をこれだけで得られるわけではなく、
  分解を増大射で比較したときに擬同型になることの証明が必要である。
- `Algebra/Category/ModuleCat/Localization.lean`：局所化関手、その完全性、有限極限・余極限の保存。
  今後の Tor の局所化との比較に利用できる。

プロジェクト側では、Tor の長完全列（`HomologicalAlgebra/TorLES.lean`）、有限長性
（`CommutativeAlgebra/TorFiniteLength.lean`）、交点重複度の左右の加法性（`IntersectionMultiplicity/Additivity.lean`）、
両変数を交換した線形同値（`HomologicalAlgebra/TorSymmetry.lean`）を証明した。残るのは次の点である。

- 長完全列は構成した射の完全性を証明する形で、導来関手の標準の射との一致と連結射の自然性は証明していない。
- 両変数の交換の高次の自然性と、局所化との比較。
