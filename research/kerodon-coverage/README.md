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

- Lean の Kerodon の引用は 9,711 件・1,851 ファイル（`citations-summary.md`）。Tag 形式の引用は 0 件。
- 件数の多い番号（5.6.0.6 の 984 件、7.5.4.6 の 553 件など）は現行版と一致。同じ番号を補助補題に決まり文句として付けているので件数が多い。存在しない番号は Ch 4・5・6 で 0 件。
- 直すべきずれ（抜き取り。保守で直す候補）：
  - `Core/Join.lean` の join の構成 66 件が §4.3.5（現行は slice）→ §4.3.3。
  - `Core/Terminal.lean` の Prop 4.7.3.6 → 4.7.3.11。
  - Remark 5.6.2.5 の 93 件（`vertexFiberPullbackIso` など）→ 現行では Example 5.6.2.19・5.6.2.9。
  - `Core/Pullback.lean` の `IsPullbackSquare` が 7.3 → 7.6.2.1。
  - `Core/FunctorPointwiseLimitCriterion.lean` の 7.1.8.5 → 7.1.8.15 の双対。
  - `Core/ContractibleKan.lean` の §3.5 → Def 1.5.5.8。
  - `Kan/FibrationBoundary.lean` の Construction 3.2.5.1 → Construction 3.2.5.3。
  - ほか、§4.5.5・Prop 4.8.4.5・7.2.1.15・7.2.3.1 の用法、見出し語だけの違い（Proposition/Corollary など）が数件。各章のファイルの注記を参照。
- 古い docstring：`InfinityCategories/DoldKanComparison.lean` の「∞ 圏の同値の証明は残る」は古い（`coherentComparison_isQCatEquivalence` がある）。

## ファイル

- `toc.md`：Kerodon の目次（番号・Tag・見出し）。
- `coverage-ch1-3.md`・`coverage-ch4.md`・`coverage-ch5-6.md`・`coverage-ch7.md`・`coverage-ch8-10.md`：Subsection ごとの表（判定・出どころ・主な宣言とファイル・注記）。
- `citations-summary.md`：Lean の Kerodon の引用の集計。
