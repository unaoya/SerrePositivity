# Codex 作業指示書 BS-D2：drafts の主張の具体化（第二束：A0 の残り 1 件、A4、A7、A8 の残り。ビルドなし）

作成：2026-11-03（BS 作業チャット）。宛先：Codex。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。** BS-D1（`bhatt-scholze-codex-d1.md`、§5 に経緯）の続き。
基準コミット：開始時に記入（main `________`。BS-D1 完了は a3a65d6cd）。

## 0. 背景と規則（BS-D1 と同じ）

- 計画：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を原典の経路 A0〜A9 で消す。設計書は
  `formalization-plans/bhatt-scholze/design/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、骨組みは `drafts/`（`SerrePositivity/` の外、ビルドしていない）。
  Codex レビュー W9（`review-codex-w9.md`）で条件付き妥当。本体の `BhattScholze/` の Lean は 2a の取り込み（11-05）まで凍結。
- 作業：drafts の `: True := by trivial`／`Type u := sorry` の仮置きを、docstring（概要／方針／規約／使われ方）の主張の具体的な Lean の型に直す。証明は `sorry -- 理由`。
  定義は型・インスタンス・単位射まで具体的に。書き方は完成した `drafts/A6/ArcSite.lean`・`ArcSheafProperty.lean`・`A8/Stratification.lean`・`A0/CechAlexander.lean` に揃える。
- **やらないこと**：`lake build`・`lake env lean`、`SerrePositivity/`・設計書・ノートの編集、指定外の drafts の編集、新しい `axiom`、主張の数学的な変更（変えたくなったら止めて報告）、`git add -A`。
- 既存の名前は grep で確かめる（`SerrePositivity/`・`.lake/packages/mathlib/`。`design-status.md` §2 (A)・(B)、`bhatt-scholze-codex-d1.md` §4）。見つからないものは `-- 要確認：` 付きの仮の名前で。
- 止めて報告する点：主張が曖昧で型にできない／設計書と食い違う、既存の名前の形が前提と合わない、一ファイルで `要確認` が 10 を超える。
- 報告：`formalization-plans/bhatt-scholze/reports/report-codex-d2.md`（新規、日本語）。コミットは drafts と報告だけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/reports/report-codex-d2.md && git commit -m "docs(bs): drafts statements (BS-D2 part N)"`。

## 1. 対象と順序（残る `True` の一覧は `report-codex-d1.md` 第 7 部）

1. **A0 の残り 1 件**：`drafts/A0/PrismaticSite.lean` の `prismaticCohomologyFrobenius`（Δ → φ_{A*}Δ、φ_A に沿うスカラー制限は `InfinityCategories/Derived/ScalarRestrictionNerve.lean`、
   W9-II-01：塔は φ_{A*}^n）。
2. **A4**（設計 `a4-design.md`、16 件）：`drafts/A4/Perfectoidization.lean`（`frobeniusTower`：CAlg_A の ℕ 添字の図式、遷移 φ_{A*}^n(φ)；`prismaticPerfectionFrobenius`；Lemma 8.4 の
   (a)(b)(c) と `prismaticPerfectionPrism`；`prismaticPerfection_filteredColimit`）、`drafts/A4/InterfaceFields.lean`（`e3Perfd_of_complete`・`e3Unit_of_complete`・`e3H0_of_complete` は
   `SerrePositivity/EInfinity/Perfectoidization/Interface.lean` の欄の型に合わせる、`hodgeTateUnit`・`toPerfection`）、`drafts/A4/AfterComparison.lean`（`e3Perfd_eq_direct`、Example 8.3）。
   A2 の `derivedPrismaticFrobenius`（`drafts/A2/DerivedPrismaticCohomology.lean`）はまだ `True` なので、A4 側に離散 S での成分 Δ_S → φ_{A*}Δ_S（CAlg_A の辺、
   `cAlgRestrictScalars φ_A`）を「A2 待ち」の理由つきの型つき定義として置いてよい（11-03 承認）。A2 を具体化する束（BS-D4）でその成分に置き換える。
   — **停止点 1**。
3. **A7**（設計 `a7-design.md`、22 件）：`drafts/A7/AnimatedDomain.lean`（`animatedCompletion`：反射的局所化、`discreteToAnimated_complete`）、`drafts/A7/AnimatedPerfectoidization.lean`
   （相対テンソル＝bar 構成の sifted 余極限 G-A7-2、Δ・colim_φ・完備化・⊗A/d との可換性 G-A7-4、Prop 8.13 の比較射と同値）、`drafts/A7/DiscreteCore.lean`（G-A7-5 の三つ）、
   `drafts/A7/UniversalProperty.lean`（`perfectoidization_of_perfectoid`、存在、G-A7-8 `perfectoidization_map_unit_eq_unit`、`selfTensor_*`、一意性、Cor 8.14、`e3Universal`）。
   A2 の animated 代数の名前（`AnimatedAlgebra`・`discreteToAnimated`・`derivedPrismaticCohomology` ほか）が未確定の箇所は `要確認` で進む。— **停止点 2**。
4. **A8 の残り**（設計 `a8-design.md`、40 件）：`drafts/A8/AlmostConnectivity.lean`（`IsAlmostConnective`、一般 J の核 K = ker(R → (R/J)_perfd)、忘却 U の完全忠実性、Prop 10.4 の非有界版、
   G-A8-1 の系二つ、Lemma 10.5、√J・生成元ごと・忠実平坦基底変換）、`drafts/A8/AlmostPurityConnectivity.lean`（有限表示有限 S、`trivialCoverComparison` の有限性・整性・局所化・完備性 G-A8-3′、
   `arcOutside_of_integral_of_localization_iso` G-A8-3″、Cor 8.12 からの almost 同型、Thm 10.9 の J-almost 連結性）、`drafts/A8/IntegralDiscreteness.lean`（G-A8-6・8・9、n = 1、帰納の段の二段の比較、
   整閉包 T と T̂ = completionRing T、`exists_finitePresentation_approximation_fixedLocalization`、Thm 10.11、`e3Integral`）。— **停止点 3（総括）**。
各停止点で報告して止まる。総括では直した宣言の数、`要確認` の一覧、設計と違うと感じた点。

## 2. 設計上の約束（変わらない）

定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号（ユーザーが付ける）。A8 の有限表示有限（W9-III-01）、T と T̂ の区別（W9-III-04、D70）、almost 連結性の
余極限保存は G-A8-1 の系で G-A8-8 を A_λ の段で使わない（W9-III-10）、Cor 8.14 の乗法は単位の整合性 G-A7-8 から（W9-II-23）、P⁰ は基盤側（D43）。

## 3. 経緯（2026-11-03）

- 第 1 部（641c7db03）：A0 の `prismaticCohomologyFrobenius` の標的で停止——(A) の調査で挙げた `dgNerveRestrictScalarsIso` は dg 圏の Hom の係数制限で、D(T) → D(S) の関手ではない。
  **決定**：係数制限の ∞ 関手を基盤待ちの宣言として `drafts/DerivedGeneral/ScalarRestriction.lean`（M13）に置く（378b17471）。A4 の塔は CAlg の中なので CAlg 版
  `cAlgRestrictScalars` と忘却との比較 `cAlgRestrictScalars_forget` を同ファイルに追加、f は明示引数（acebb81cc）。A2 の `derivedPrismaticFrobenius` がまだ `True` なので
  A4 に離散 S での成分 `discreteDeltaFrobenius` を A2 待ちの仮置きとして置くことを承認（7be013b32）。
- 第 2 部（d68904dec、**停止点 1 完了・検収済み**）：A0 の 1 件と A4 の 17 件（`perfectPrismRing` を含む）。A4 の「ScalarRestriction へ」三件（塔の余極限の保存、完備化との両立、H⁰）は
  一般形を `ScalarRestriction.lean` に置いた（27bbde06d：`cAlgRestrictScalars_isColimitCone`・`derivedInfinityRestrictScalars_completion`・`cAlgRestrictScalars_h0`）。
  A2 の名前 3 件（`completeCAlgInclusion`・`reflectCompleteCAlg`・`modPrismFunctor`）は BS-D4（A2）で確定。
- 次：停止点 2（A7）。
- 第 3 部（b682bd4a4、**停止点 2 完了・検収済み**）：A7 の 4 ファイル 22 件。Prop 8.13 は完備 CAlg の押し出しからの指定比較射の可逆性、Cor 8.14 は F(η_S) = η_P を先に置いて乗法との一致。
  A2 待ちの仮置き 5（sifted 延長、A/d ≃ R に沿う基底移送、animated Frobenius、Fil₀ の始域の E∞ 実現、Fil₀ の単位射）。**D2-01**：`cAlgRestrictScalars_isColimitCone` は任意の図式では偽
  （空図式で ℤ → F₂）→ sifted 図式に限定し、同型に沿う制限の全余極限保存を別補題に（ScalarRestriction.lean、design-status §5）。
- 次：停止点 3（A8 の残り）。
- 第 4・5 部（1189e6dfe、**停止点 3 完了・BS-D2 終了・検収済み**）：A8 の 40 件＋型 3 件。**D2-02**：`perfectoidIdeal_baseChange` の右辺は完備テンソル K ⊗̂_R R′ の像
  （J_perfd R′ の p 進閉包、Fayolle Prop 2.9）で通常の `Ideal.map` ではない；`Ideal.map` との一致の補題は置かない（有界ねじれだけでは偽、Codex の反例）。
  **BS-D2 全体 83 件（`True` 79、`Type u := sorry` 4）。** drafts 全体の残り 187 件は A5・A6 の excision（BS-D3）、A1〜A3（BS-D4）、基盤（W2b 後）。
