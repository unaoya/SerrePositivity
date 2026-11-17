# Kerodon の被覆の調査（2026-11-06）

作成：段階 II の調整役（調査は読み取りだけのエージェント 7 本）。対象：Kerodon（https://kerodon.net、取得 11-06）の本文 Ch 1〜10 の Subsection 418 個について、SerrePositivity（主に `InfinityCategories/`）と Mathlib に何があるか。
方法：Kerodon の各ページで主な定義・定理を把握し、宣言名と主張の grep で照合した。**証明の中身は読んでいない。公理の監査も流していない**（sorry はソースの grep で確認：`InfinityCategories/` で実の sorry は `ModelBridge/Inputs/KanQuillen.lean` の 1 件だけ（Hovey 3.6.5）で、主要な層からは import されない）。判定は「あり（主な定義と主要な定理が sorry なし）」「一部」「なし」。

## 集計

| 章 | Subsection | あり | 一部 | なし | 主な出どころ |
| --- | --- | --- | --- | --- | --- |
| 1 The Language of ∞-Categories | 31 | 20 | 10 | 1 | ほぼ Mathlib |
| 2 Examples of ∞-Categories | 36 | 17 | 10 | 9 | 2.1・2.2・2.5.1 などは Mathlib、2.4.5・2.5.2〜2.5.9 は自前 |
| 3 Kan Complexes | 46 | 12 | 9 | 25 | 3.1.1〜3.1.3 は Mathlib、ほかは自前 |
| 4 The Homotopy Theory of ∞-Categories | 64 | 28 | 16 | 20 | 自前が大半、Mathlib 8 |
| 5 Fibrations of ∞-Categories | 46 | 13 | 16 | 17 | 自前 |
| 6 Adjoint Functors | 19 | 9 | 4 | 6 | 6.1 は Mathlib の双圏の随伴、6.2・6.3 は自前 |
| 7 Limits and Colimits | 49 | 21 | 14 | 14 | 自前 |
| 8 The Yoneda Embedding | 58 | 9 | 10 | 39 | 自前（HTT 経由） |
| 9 Large ∞-Categories | 58 | 15 | 20 | 23 | 自前（HTT 経由） |
| 10 Exactness and Animation | 11 | 0 | 1 | 10 | — |
| **計** | **418** | **144** | **110** | **164** | |

## 章ごとの要点

- **Ch 1〜3**：Ch 1 は Mathlib でほぼ埋まる（空白は Sing が Kan、Joyal の判定 Thm 1.5.6.1、Thm 1.5.7.1、nerve の特徴付けの逆）。空いているのは 2.3 Duskin nerve（全部）、2.4.6、2.4.4 の Path[S] の左随伴、3.3 Ex∞、3.4 ホモトピー引き戻し・押し出し（Mather・excision・van Kampen）、3.5 truncation と Postnikov 塔、3.6 位相空間との比較（Kan–Quillen は引用の sorry）、3.1.4 covering map、Thm 3.2.4.3。
- **Ch 4**：join・slice の Joyal の定理群、Thm 4.4.2.6、同値の判定 Thm 4.8.4.1、blunt join の比較、coherent nerve の写像空間、終対象は揃う。空白は 4.7（truncated・mono・n-圏・高次ホモトピー圏）、4.8 の full・faithful・connective、4.5.3 categorical pullback square の定義と一般の性質、4.6.8 一般の写像空間の合成、4.6.1 の pinch していない Hom（方針で右 pinch）、isofibration の名前を持つ定義。
- **Ch 5〜6**：𝒮 値の straightening は一般の底（同値は `[Quasicategory B]` の下）。Cat∞ 値は通常の圏の nerve 上と有限の Δⁿ までで休止（`F1/Cocartesian/` はビルド対象外）。5.4 ∞-bicategory は方針で全部なし。6.3.2 局所化の存在は調査では「なし」としたが、**`KST/LocalizingInvariants/LocalizationResolution.lean` の `exists_quasicategory_localization` にある**（調査の見落とし、調整役が訂正）。F1B/Localization/DwyerKan/（約 600 本）は途中で入口が空。
- **Ch 7**：極限の基本、cofinality と Quillen A、Kan 拡張の中心、𝒮 の極限・余極限、Bousfield–Kan の holim、pullback・pushout は揃う。空白は 7.7 Universality of Colimits（descent・Mather・disjoint coproduct）、7.3.7〜7.3.9、7.4.4〜7.4.6、7.6.4 イコライザー。
- **Ch 8〜10**：HTT から作った塊が厚い（冪等完備化 8.5、Yoneda と前層 8.3・8.4 の一部、filtered・compact・Ind 9.1〜9.3、accessible・presentable・随伴関手定理・Bousfield 9.4・9.5、P_Σ と sifted 9.7.1・9.7.2）。空白は 8.1.3〜8.1.10（cospan・Beck–Chevalley）、8.2、8.6、8.7、9.6（factorization system・small object argument）、9.7.3〜（presentable のテンソル積）、Ch 10 のほぼ全部。

## 引用番号の照合

11-06 の調査で、Lean の引用は 9,711 件・1,851 ファイルだった。段階 II の KL-W1 では、項目の Tag を項目表から、節・小節の Tag を目次から照合して既存の docstring に加えた。[当時の引用集計](citations-summary.md)、[KL-W1 の報告](../../formalization-plans/stage-ii/bulk/kerodon-layout-w1-report.md)

| 旧引用 | 照合後の参照先 |
| --- | --- |
| join の構成で §4.3.5 | join の構成は [4.3.3（Tag 016K）](https://kerodon.net/tag/016K)。 |
| 終対象で Proposition 4.7.3.6 | 終対象は Proposition [4.7.3.11（Tag 06R1）](https://kerodon.net/tag/06R1)。 |
| 元素 ∞ 圏で Remark 5.6.2.5 | 底変換は Remark [5.6.2.18（Tag 0271）](https://kerodon.net/tag/0271)、ファイバーは Example [5.6.2.19（Tag 0272）](https://kerodon.net/tag/0272)、空間値の構成は Example [5.6.2.9（Tag 026S）](https://kerodon.net/tag/026S)。一般の文脈は小節 [5.6.2（Tag 026H）](https://kerodon.net/tag/026H)。 |
| 引き戻し四角形で §7.3 | 小節 [7.6.2（Tag 03FE）](https://kerodon.net/tag/03FE)、定義は Definition [7.6.2.1（Tag 03FF）](https://kerodon.net/tag/03FF)。 |
| 各点ごとの極限で Proposition 7.1.8.5 | Corollary [7.1.8.15（Tag 02XP）](https://kerodon.net/tag/02XP) の双対。 |
| 可縮な Kan 複体で §3.5 | Definition [1.5.5.8（Tag 0072）](https://kerodon.net/tag/0072)。 |
| 連結射で Construction 3.2.5.1 | Construction [3.2.5.3（Tag 00WG）](https://kerodon.net/tag/00WG)。 |
| 圏論的引き戻しの比較で §4.5.5 | 引き戻しは [4.5.3（Tag 032Y）](https://kerodon.net/tag/032Y)。押し出しの比較では [4.5.5（Tag 01F6）](https://kerodon.net/tag/01F6) を使う。 |
| 充満忠実な内ファイブレーションの底変換で Proposition 4.8.4.5 | 写像空間と充満忠実性を扱う小節 [4.8.3（Tag 05AW）](https://kerodon.net/tag/05AW)。 |
| 一般の anodyne–fibration 因子分解で Corollary 7.2.1.15 | 因子分解を扱う小節 [4.2.4（Tag 014S）](https://kerodon.net/tag/014S)。cofinal な射の判定には元の Corollary を使う。 |
| 弱可縮性の定義で Theorem 7.2.3.1 | Quillen A の文脈を示す小節 [7.2.3（Tag 02NX）](https://kerodon.net/tag/02NX)。定理の証明では項目 [7.2.3.1（Tag 02NY）](https://kerodon.net/tag/02NY) を使う。 |

Kan fibration の塔の旧引用は付録で番号と Tag を確認した。[Corollary 11.9.7.2（Tag 01C7）](https://kerodon.net/tag/01C7)

## 項目ごとの対応表（2026-11-07）

Subsection 単位の調査の後に、項目（a.b.c.d）ごとの対応表を作った。対象は 3,553 項目で、Definition・Theorem・Proposition・Lemma・Corollary・Construction・Variant・Notation の全部と、Lean が番号で引いている Example・Remark など。ワークフローで 29 の塊に分け、各項目を判定した。「なし」とした Definition・Theorem・Proposition は、別のエージェントが探し直した（58 エージェント）。探した範囲は SerrePositivity 全体（KST・HomotopicalAlgebra・DifferentialGraded・EInfinity・Archive を含む）と Mathlib。**Lean を動かしての確認はまだ**で、Codex の確認を依頼する（`codex-review.md`）。

| | 項目 | 自前 | 両方 | Mathlib | 一部 | なし |
| --- | --- | --- | --- | --- | --- | --- |
| 計 | 3,553 | 499 | 21 | 255 | 831 | 1,947 |

- 確度：high 1,080、med 2,126、low 347。
- 章・種類・節ごとの集計は `items-summary.md`、各塊の所見（InfinityCategories の外で見つかったもの、定義の違い、番号のずれ、本文の抜き出しの欠け）は `items-remarks.md`。
- 表 `items.csv` の `subsection_tag` は Subsection の Tag。抜き出しのときに取った項目ごとの Tag は不正確だったので載せていない。
- 注意：項目の本文の抜き出し（先頭 500 字）は、参照だけの項目で最初の言及を取っていたものがある。各エージェントが元のページを見直して判定したが、確度を low・med にしたものが多い。

ファイル（追加）：`items.csv`、`items-summary.md`、`items-remarks.md`、`codex-review.md`（Codex への依頼。全項目を確認し、結果は `review/ch<N>.csv`）、`review-targets.csv`（誤りが多そうな 417 項目の印。先に見る）。

## ファイル

- `toc.md`：Kerodon の目次（番号・Tag・見出し）。
- `coverage-ch1-3.md`・`coverage-ch4.md`・`coverage-ch5-6.md`・`coverage-ch7.md`・`coverage-ch8-10.md`：Subsection ごとの表（判定・出どころ・主な宣言とファイル・注記）。
- `citations.csv`：Lean の Kerodon の引用の一覧（一引用一行、11-06 の main で採取）。`citations-summary.md`：その集計。


## P⁰閉包からの未照合項目の追加（2026-11-16、⑤d）

main `671f6eafe` のP⁰閉包にあり、従来の項目表・reviewにない531項目を `items.csv` の末尾へ追加した。既存3,553行は変更せず、計4,084行。追加行の状態・宣言・確度・Lean引用数は空欄で、③-a・③-bの取り込み後の対応表更新時にまとめて照合する。上の3,553項目の既存集計にこの531項目は含まない。

書誌情報の5列（番号・種類・原典の見出し・節・項目Tag）は [p0-added-items.csv](p0-added-items.csv)。既存8列の `items.csv` では見出しを `note` に置き、`subsection_tag` は従来どおり小節Tagだけを持つ。項目自身のTagは `item-tags.csv` にあり、既掲載516件はそのまま、未掲載15件だけを追記した。reviewは未変更。

追加した全531番号と検収は [追加報告](p0-added-items-report.md) を参照。今回の作業は書誌情報の追加だけで、Leanの変更・ビルドや実装状態の判定は行っていない。
