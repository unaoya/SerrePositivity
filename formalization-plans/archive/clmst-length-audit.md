# C1/C2 と根の塔の長さ構成の監査

> **アーカイブ（2026-10-17）**：この計画は完了したか、ほかへ吸収された。内容の要約先：[CLMST 主計画](clmst.md)。将来は削除する予定で、以下は当時の計画と実施記録のまま。


監査日：2026-10-13。対象は共通層への抽出を始める直前の宣言と、公開入口
`SerrePositivity.lean` の import 閉包。Lean の主張・引用は変更していない。
[主計画](clmst.md)・[実装境界 T0-a](clmst-interfaces.md)の補助文書である。

## 続きの実装による更新

以下は初回抽出前の監査記録として保持する。続く実装では C1 の有限生成一致を証明し、
旧 `towerLengthFun_eq_fgLength` の `sorry` を除去した。
現在は Noether 局所基底・素数 p・座標の極大イデアル所属を明示し、利用先へ渡す。
有限表示の場合の一致も証明済みである。
C2 の一般加法性も同じ条件で証明し、旧 `towerLengthFun_add_of_exact` の `sorry` を除去した。
`towerLength`・`towerLengthOn`・`completedTowerLength`・`μT` と、Section 2・5 の利用先を
条件つきの証明済み構成へ移した。標準冪級数表示の情報の伝播は C1・C2 とも不要となった。
以下の広い署名・引用依存の記述と70宣言・28モジュールという件数は初回監査の記録であり、
現行の署名ではない。現在の数値評価・引用境界は[主計画§0](clmst.md)を参照する。
現在の依存は `scripts/audit_clmst.lean` と `scripts/audit_axioms.lean` で確認する。

## 1. 初回監査時の結論と確認範囲

初回監査時の C1/C2 は `CommRing A`・`IsLocalRing A` のみを基底の条件とする。
`p` は任意の自然数、`t : Fin h → A` は任意の族であり、素数性、Noether 性、
正則性、完備性、剰余体、次元、座標の生成条件を要求していない。
CLMST §2.2 の標準基底より一般的な型である。

これは、現行主張が偽だという判定ではない。CLMST Remark 2.2.2 自体が
より一般の正規化長さに言及している。Gabber–Ramero Remark 14.5.69、
Lemma 14.5.74、Theorem 14.5.75 の一般設定から現行の全範囲へ適用できるかは、
この監査では未検証である。原典の正確な CLMST 引用を、そのまま旧型の根拠としない。

機械監査では、コンパイル済み公開入口の各プロジェクト宣言の型・値に現れる
定数参照から C1/C2 への推移的到達を計算した。内部生成宣言を除く **70 宣言、28 モジュール**が到達する。
型に `towerLength` 等が現れるだけの引用も含むため、「証明が C1/C2 を適用した件数」ではない。
全ソースの `rg` 検索も併用し、構造を作る入口、数値関数だけを使う入口、
標準表示を持つ最終入口を確認した。全宣言の一覧は末尾に置く。

一時監査コードは `/tmp/serre-clmst-length-audit.lean`、結果は
`/tmp/serre-clmst-length-audit.tsv`。前者は `lake env lean` で成功した。
リポジトリへ新しい Lean 宣言・引用・公理を追加する作業ではない。
抽出後に宣言の実体を移した場合は、新しい公開入口でこの依存監査を再実行する。

## 2. 原典に対応させる前提

CLMST §2.2 は、完全剰余体 k を持つ d 次元完備正則局所環 A を、
等標数の `k[[x_1,…,x_d]]` または非分岐混標数の `W(k)[[x_2,…,x_d]]`
として固定している。混標数では `x_1=p`。加群の範囲は、一つの
`m_A^N` で加群全体が消えるもの。C1 は Prop 2.2.3 の有限生成一致部分、
C2 は Prop 2.2.6(a) の加法性部分に対応する。
[CLMST v4 §2.2](https://arxiv.org/html/2209.04046v4)

以後「標準基底」は、次の数学的データを意味する。未実装の class 名ではない。

- 共通：素数 p、完全体 k、`CharP k p`、次元と座標数の一致。
- 等標数：`e : A ≃+* MvPowerSeries (Fin h) k`、`e (t i)=X i`。
- 混標数：`0<h`、`t 0=p`、残りの変数を添字とする Witt 冪級数環への同型 e、
  残りの座標の像が対応する X であること。
- その表示から正則・完備・局所・剰余体の条件を供給し、原典の根の塔と
  商による `TowerStage`・`Tower` の同型および代数作用を比較する。

現行数値定義は有限段上の長さを用い、原典は A 上の長さを用いる。
`residue_surjective_towerStage` と `length_eq_of_common_residueField` による比較が必要。
下限による `presentedLength` と原典の「任意の降下の値」の一致も別途記録する。
`fgLength` は型上、冪ねじれを要求しない有限表示 P も下限の候補に含むため、
原典の冪ねじれカテゴリー内の候補への制限が値を変えないことを比較に含める。
有限段からの候補があれば P の冪ねじれが従い、候補のない P の値は `⊤` となる、
という分解が比較の候補である。これはこの監査で完成した Lean 補題ではない。

## 3. 初回監査時の直接利用と無条件の構成

下表の宣言名は、別記がなければ `SerrePositivity.Section2.` を省略する。

| 宣言 | 現在の仮定と依存 | 原典型へ移行する場合の作業 |
| --- | --- | --- |
| `towerLengthFun_eq_fgLength`（C1） | local A、有限生成 N、`IsPowTorsion (towerMaxIdeal …) N`。直接 `sorry` | 標準基底で原典引用を置く。旧一般型を維持するなら別の一般定理と適用条件を検証する |
| `towerLengthFun_add_of_exact`（C2） | local A、線形短完全列、中項の一様冪ねじれ。直接 `sorry` | 同上。両端の冪ねじれは中項と完全性から供給できる |
| `towerLengthFun_tensor` | C1 を直接利用。Noether/local A、prime p、`t_i∈m_A`、有限長と冪ねじれ | 標準基底仮定を追加するか、C1 を引数化した一般版を経由する |
| `towerLength_hasSup` | C1 を直接利用し、型の `towerLength` は C2 に依存。基底は local のみ | 加法性で組み立てた構造に C1 を接続する。RawDefs 層へ置かない |
| `towerLength` | C2 を直接利用して `NormalizedLength` を構成。local のみ | 正確な引用の後段へ。一般の constructor は加法性の証拠を明示的引数として受け取れる |
| `towerLengthOn` | `towerLength.comap`。有限単射 A→D、両方 local、作用の両立 | 基底仮定の伝播、または一般 `lam : NormalizedLength …` を受ける係数制限に分離 |
| `completedTowerLength` | `towerLength.comap`。local のみ | 完備化の環の定義から分離し、引用後段で構成する |
| `μT` | `towerLength.comap`、`TS=Tower⊗_A T`。local A のみ | 同じく具体的な長さ構造の特殊化を引用後段へ置く |

以上が、全ソース検索で確認した根の塔由来の具体的 `NormalizedLength` constructor 全部である。
`HasSup` の具体的供給は `towerLength_hasSup` 一つであり、`towerLengthOn_hasSup` や
`completedTowerLength_hasSup` の既存宣言は見つからなかった。
一般の `NormalizedLength.comap` と `NormalizedLength.HasSup` は C1/C2 を import せず、
抽象的な長さを引数とする。これらの一般性を狭める必要はない。

所在：[TowerLength](../../SerrePositivity/Paper/Section2/TowerLength.lean)、
[TowerLengthOn](../../SerrePositivity/Paper/Section2/TowerLengthOn.lean)、
[CompletedTower](../../SerrePositivity/Paper/Section2/CompletedTower.lean)、
[TowerApproximation](../../SerrePositivity/Paper/Section2/TowerApproximation.lean)。

## 4. 間接利用の前提の差

| 入口・宣言群 | 現在供給される基底の条件 | 標準表示の有無／移行時の扱い |
| --- | --- | --- |
| `exists_descent`、`fgLength_tensor` | Noether/local、prime。後者は `t_i∈m_A` | C1/C2 への定数依存はない。数値定義・降下・有限段計算を RawDefs 後段に切り出せる |
| `towerLengthFun_tensor_of_finiteLength`、`towerLengthFun_koszulHomology_of_baseChange`、`towerLengthFun_quotient_of_baseChange` | Noether/local、prime、`t_i∈m_A` | 標準表示なし。C1 の適用を引数化する版と標準版の wrapper を分ける候補 |
| `lemma_2_4_iSup`、`lemma_2_4_directSum`、`lemma_2_4_iSup_of_directed`、`lemma_2_4_directLimit` | local のみ。一様な冪ねじれは適切に要求済み | 原典型へ狭めるなら基底仮定を追加。内容の一般形は既存 `NormalizedLength`＋`HasSup` の補題を維持 |
| `towerLengthFun_quotient_eq_iSup_image`、`towerLengthFun_quotientImage_tendsto` | local A、prime、D の char p、商の冪ねじれ | 正則・完備・標準表示なし。長さ構造＋`HasSup` を受ける一般版への分離候補 |
| `exists_fg_quotient_le`、`exists_finitePresentation_approx` | local A。`μT` と C1/C2 を内部で使用 | 標準表示なし。長さ構造・上限性と、有限表示近似の固有条件を分ける |
| `towerLengthFun_baseChangeT`、`towerLengthFun_homology_tensorRes`、`exists_stage_step`、`exists_tower_approximation`、`exists_tower_approximation_B` | Noether/local、prime、`t_i∈m_A`、有限局所 T、固定冪零化、共通剰余体 | 正則・完備・座標生成・標準表示なし。C1/C2 を原典型にするならこれらへ仮定を渡すか、必要な長さの性質を明示引数化 |
| perfection の有限近似・核／像比較、高次 Koszul の極限（末尾一覧） | 正則完備局所 A、prime、perfect residue、char p、`span(range t)=m_A`、`dim A=h`、有限単射と共通剰余体等 | 正則パラメータはあるが、冪級数表示 e は要求しない。表示を導く定理を完成させるか、上流から伝播する |
| `perfectClosure_length_properties_of_higher_tendsto`、`…_of_roberts`、`perfectClosure_length_properties`、`lengthAlgebra_equalCharacteristic` | 上の正則等標数基底。後二者は Roberts 引用を利用 | e/he なし。現行の広い一般性を保持するのか、標準表示付きの入口を追加するのかを別変更として決める |
| `mixedPerfectoid_length_properties`、`lengthAlgebra_mixedCharacteristic` | 正則完備局所、prime、perfect residue、char zero、`t_0=p`、Witt 冪級数表示 e/he | 原典に対応する表示をすでに持つ。型・作用の整合を確認して正確な C1/C2 を供給可能 |
| `theorem_2_5` | `hbase` に等標数／混標数双方の標準表示を持つ | 等標数枝で現在 e/he を捨てている。正確な引用へ移す場合はこの情報を等標数の構成へ渡す |
| `Section5.lemma_5_4`、`Section5.lambdaChi_pos_of_parameter_tower` | 塔の A₀ は Noether/local、prime、座標の m 所属まで。別の正則基底 A の条件はある | **別の基底 A の正則性は塔の A₀ の条件を補わない。** A₀ の標準基底データを伝播するか、長さの性質を引数として保つ |
| `Section5.core_of_lengthAlgebras`、`…_with_parameter_choice`、`twistedEuler_pos_of_lengthAlgebras`、`lambdaChi_pos_of_parameter_lengthAlgebras` | 具体的 `towerLengthOn` を条件・結論に利用 | 完備正則／生成条件を持つ箇所でも、標準表示は引数にない。一般補題と具体的特殊化を分ける候補 |
| `Section5.core_of_normalization_bases` | `hbaseD`、`hbaseT` に双方の標準表示 | A₀ 側と A 側それぞれの長さに仮定を供給できる、主要な標準入口 |

所在：[TowerDescent](../../SerrePositivity/Paper/Section2/TowerDescent.lean)、
[PerfectApproximationLength](../../SerrePositivity/Paper/Section2/PerfectApproximationLength.lean)、
[LengthAlgebraConstruction](../../SerrePositivity/Paper/Section2/LengthAlgebraConstruction.lean)、
[Theorem2_5](../../SerrePositivity/Paper/Section2/Theorem2_5.lean)、
[ParameterQuotient](../../SerrePositivity/Paper/Section5/ParameterQuotient.lean)、
[TowerPositivity](../../SerrePositivity/Paper/Section5/TowerPositivity.lean)、
[NormalizationPositivity](../../SerrePositivity/Paper/Section5/NormalizationPositivity.lean)。

等標数の完備正則局所環から標準表示を取り直せることは数学的な候補であるが、
指定した座標 t をそのまま X に送る同型まで、この監査では形式化済みとは確認していない。
「正則・完備なら CLMST の原典型をそのまま適用できる」と省略しない。

## 5. 当初の移行案（移行は実施済み）

最初の機械抽出では、C1/C2 の型・直接 `sorry` と既存利用先を保持する。
名前を移したことだけを、原典の正確な引用への移行完了とは扱わない。
新しい引用を追加する工程とは分ける。

```text
RootTower の環・段・写像
  → RootTowerLength/RawDefs（presentedLength, fgLength, towerLengthFun）
  → 降下・有限段の presented/fg 計算
  → CLMST の標準基底上の引用と、raw 数値定義との比較
  → NormalizedLength の組立・HasSup・係数制限
  → 完備化上の長さ、Serre／Lech の接続
```

- RawDefs は C1/C2・`towerLength`・CLMST を import しない。
  零・線形同型不変の証明もこの側へ置ける。
- `exists_descent` と `fgLength_tensor` の証明に C1/C2 の参照はない。
  現行 `TowerDescent` が `TowerLength` 全体を import するというモジュール依存を外す。
  末尾の `towerLengthFun_tensor` 二定理は C1 の後段へ分離する。
- `CLMST.normalizedLength` を raw な数値関数の別名として使うなら、その定義ファイルは
  RawDefs のみを import する。`NormalizedLength` 構造を表す別名とは区別する。
- 引用のステートメントは raw 数値関数について述べ、引用から構造を組み立てる。
  C2 のステートメントを書くために、C2 で組み立てた構造を先に import しない。
- 実際の Prop 2.2.3 の証明を始める際にも、C1 依存の
  `towerLengthFun_tensor` や `towerLength_hasSup` を循環して使わない。
  使えるのは raw 定義・降下・`fgLength_tensor` 等、引用に依存しない側である。
- 一般の係数制限は `lam : NormalizedLength …` を引数とする既存 `comap` を使う。
  具体的な `towerLengthOn`・`completedTowerLength`・`μT` は後段で代入する。

移行の二つの選択肢は、(a) GR の一般設定への適用を確認・証明して旧一般型を維持する、
(b) 正確な標準基底の引用と、その仮定を伝播した具体的長さを用意し、
一般補題は必要な長さの証拠を引数化する、である。
この文書は (a) の根拠を確認済みとしていないし、(b) の仮定変更も実施していない。

## 6. 検証記録と宣言一覧

確認したこと：全ソースの名前検索、関連 section の仮定・`include`／`omit`、
公開入口のコンパイル済み定数依存、下記リンク先の存在。
一般 GR の適用、仮定変更後の Lean ビルド、抽出先の型・import 監査は後続作業。

表の C1/C2 は、型と値を合わせた推移的定数依存。引用名自身も含む。
名前は `SerrePositivity.` を省略し、ファイルは `SerrePositivity/` 以下を示す。

| ファイル | 宣言 | C1 | C2 |
| --- | --- | --- | --- |
| [Inputs/CLMST.lean](../../SerrePositivity/Inputs/CLMST.lean) | `Inputs.clmst_length_eq_zero_of_perfectoidIdeal_annihilates` | — | ✓ |
| 同上 | `Inputs.clmst_parameter_quotient_length` | — | ✓ |
| [Paper/Section2/CompletedTower.lean](../../SerrePositivity/Paper/Section2/CompletedTower.lean) | `Section2.completedTowerLength` | — | ✓ |
| 同上 | `Section2.towerLengthOn_eq_completedTowerLength` | — | ✓ |
| [Paper/Section2/Lemma2_4.lean](../../SerrePositivity/Paper/Section2/Lemma2_4.lean) | `Section2.lemma_2_4_directLimit` | ✓ | ✓ |
| 同上 | `Section2.lemma_2_4_directSum` | ✓ | ✓ |
| 同上 | `Section2.lemma_2_4_iSup` | ✓ | ✓ |
| 同上 | `Section2.lemma_2_4_iSup_of_directed` | ✓ | ✓ |
| [Paper/Section2/LengthAlgebraConstruction.lean](../../SerrePositivity/Paper/Section2/LengthAlgebraConstruction.lean) | `Section2.lengthAlgebra_equalCharacteristic` | ✓ | ✓ |
| 同上 | `Section2.lengthAlgebra_mixedCharacteristic` | — | ✓ |
| 同上 | `Section2.perfectClosure_length_properties` | ✓ | ✓ |
| 同上 | `Section2.perfectClosure_length_properties_of_higher_tendsto` | ✓ | ✓ |
| 同上 | `Section2.perfectClosure_length_properties_of_roberts` | ✓ | ✓ |
| [Paper/Section2/MixedLengthAlgebra.lean](../../SerrePositivity/Paper/Section2/MixedLengthAlgebra.lean) | `Section2.mixedPerfectoid_length_properties` | — | ✓ |
| [Paper/Section2/PerfectApproximationLength.lean](../../SerrePositivity/Paper/Section2/PerfectApproximationLength.lean) | `Section2.normalized_frobenius_length_tendsto_perfection_quotient` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_frobenius_quotient` | ✓ | — |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_frobenius_quotient_le` | ✓ | — |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_frobenius_quotient_tendsto_zero` | ✓ | — |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_kernel_add_range` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_kernel_le` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_kernel_tendsto_zero` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_quotient` | ✓ | — |
| 同上 | `Section2.towerLengthFun_perfectionApproximation_quotient_of_finiteLength` | ✓ | — |
| 同上 | `Section2.towerLengthFun_perfection_quotientImage_tendsto` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_quotientImage_tendsto` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_quotient_eq_iSup_image` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_quotient_of_baseChange` | ✓ | — |
| [Paper/Section2/PerfectKoszulLength.lean](../../SerrePositivity/Paper/Section2/PerfectKoszulLength.lean) | `Section2.perfectionApproximation_koszulHomology_length` | ✓ | — |
| [Paper/Section2/PerfectKoszulLimit.lean](../../SerrePositivity/Paper/Section2/PerfectKoszulLimit.lean) | `Section2.towerLengthFun_perfection_koszulHomology_eq_zero_of_tendsto` | ✓ | ✓ |
| 同上 | `Section2.towerLengthOn_perfection_koszulHomology_eq_zero_of_tendsto` | ✓ | ✓ |
| [Paper/Section2/PerfectQuotientLimit.lean](../../SerrePositivity/Paper/Section2/PerfectQuotientLimit.lean) | `Section2.normalized_frobenius_length_tendsto_perfection_quotient_of_primary` | ✓ | ✓ |
| 同上 | `Section2.normalized_frobenius_length_tendsto_towerLengthOn_quotient` | ✓ | ✓ |
| 同上 | `Section2.towerLengthOn_perfection_parameter_quotient_eq_multiplicity_of_higher_tendsto` | ✓ | ✓ |
| [Paper/Section2/Theorem2_5.lean](../../SerrePositivity/Paper/Section2/Theorem2_5.lean) | `Section2.theorem_2_5` | ✓ | ✓ |
| [Paper/Section2/TowerApproximation.lean](../../SerrePositivity/Paper/Section2/TowerApproximation.lean) | `Section2.exists_fg_quotient_le` | ✓ | ✓ |
| 同上 | `Section2.exists_finitePresentation_approx` | ✓ | ✓ |
| 同上 | `Section2.exists_stage_step` | ✓ | ✓ |
| 同上 | `Section2.exists_tower_approximation` | ✓ | ✓ |
| 同上 | `Section2.exists_tower_approximation_B` | ✓ | ✓ |
| 同上 | `Section2.towerLengthFun_baseChangeT` | ✓ | — |
| 同上 | `Section2.towerLengthFun_homology_tensorRes` | ✓ | — |
| 同上 | `Section2.μT` | — | ✓ |
| 同上 | `Section2.μT_TS_ne_top` | ✓ | ✓ |
| 同上 | `Section2.μT_pi_ne_top` | ✓ | ✓ |
| 同上 | `Section2.μT_tensor_eq` | — | ✓ |
| [Paper/Section2/TowerDescent.lean](../../SerrePositivity/Paper/Section2/TowerDescent.lean) | `Section2.towerLengthFun_tensor` | ✓ | — |
| 同上 | `Section2.towerLengthFun_tensor_of_finiteLength` | ✓ | — |
| [Paper/Section2/TowerKoszulLength.lean](../../SerrePositivity/Paper/Section2/TowerKoszulLength.lean) | `Section2.towerLengthFun_koszulHomology_of_baseChange` | ✓ | — |
| [Paper/Section2/TowerLength.lean](../../SerrePositivity/Paper/Section2/TowerLength.lean) | `Section2.towerLength` | — | ✓ |
| 同上 | `Section2.towerLengthFun_add_of_exact` | — | ✓ |
| 同上 | `Section2.towerLengthFun_eq_fgLength` | ✓ | — |
| 同上 | `Section2.towerLength_hasSup` | ✓ | ✓ |
| 同上 | `Section2.towerLength_len` | — | ✓ |
| [Paper/Section2/TowerLengthOn.lean](../../SerrePositivity/Paper/Section2/TowerLengthOn.lean) | `Section2.towerLengthOn` | — | ✓ |
| 同上 | `Section2.towerLengthOn_len` | — | ✓ |
| [Paper/Section5/CompletionReduction.lean](../../SerrePositivity/Paper/Section5/CompletionReduction.lean) | `Section5.positivity_of_residueCharP` | ✓ | ✓ |
| [Paper/Section5/Core.lean](../../SerrePositivity/Paper/Section5/Core.lean) | `Section5.core_of_complete_algClosed` | ✓ | ✓ |
| [Paper/Section5/CoreLengthPositivity.lean](../../SerrePositivity/Paper/Section5/CoreLengthPositivity.lean) | `Section2.towerLengthOn.congr_simp` | — | ✓ |
| 同上 | `Section5.core_of_lengthAlgebras` | ✓ | ✓ |
| [Paper/Section5/ModuleReduction.lean](../../SerrePositivity/Paper/Section5/ModuleReduction.lean) | `Section5.positivity_of_complete_algClosed` | ✓ | ✓ |
| [Paper/Section5/NormalizationPositivity.lean](../../SerrePositivity/Paper/Section5/NormalizationPositivity.lean) | `Section5.core_of_normalization_bases` | ✓ | ✓ |
| [Paper/Section5/ParameterLengthPositivity.lean](../../SerrePositivity/Paper/Section5/ParameterLengthPositivity.lean) | `Section5.lambdaChi_pos_of_parameter_lengthAlgebras` | ✓ | ✓ |
| [Paper/Section5/ParameterQuotient.lean](../../SerrePositivity/Paper/Section5/ParameterQuotient.lean) | `Section5.lemma_5_4` | ✓ | ✓ |
| [Paper/Section5/PrimeReduction.lean](../../SerrePositivity/Paper/Section5/PrimeReduction.lean) | `Section5.chi_prime_pos_of_complete_algClosed` | ✓ | ✓ |
| [Paper/Section5/ResidueFieldReduction.lean](../../SerrePositivity/Paper/Section5/ResidueFieldReduction.lean) | `Section5.positivity_of_complete_residueCharP` | ✓ | ✓ |
| [Paper/Section5/SelectedParameterPositivity.lean](../../SerrePositivity/Paper/Section5/SelectedParameterPositivity.lean) | `Section5.core_of_lengthAlgebras_with_parameter_choice` | ✓ | ✓ |
| [Paper/Section5/TowerPositivity.lean](../../SerrePositivity/Paper/Section5/TowerPositivity.lean) | `Section5.lambdaChi_pos_of_parameter_tower` | ✓ | ✓ |
| [Paper/Section5/TwistedLengthPositivity.lean](../../SerrePositivity/Paper/Section5/TwistedLengthPositivity.lean) | `Section5.twistedEuler_pos_of_lengthAlgebras` | ✓ | ✓ |
| [Paper/Statement.lean](../../SerrePositivity/Paper/Statement.lean) | `core_statement` | ✓ | ✓ |
| 同上 | `main_statement` | ✓ | ✓ |
