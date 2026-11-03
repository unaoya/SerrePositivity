# Codex 作業指示書 BS-D4：drafts の主張の具体化（第四束：A1〜A3 と A2 待ちの仮置きの接続。ビルドなし）

作成：2026-11-03（BS 作業チャット）。宛先：Codex。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。** BS-D1〜D3（`bhatt-scholze-codex-d1/2/3.md`、各 §経緯）の続き。
基準コミット：開始時に記入（main `________`。BS-D3 完了は 3b026a1af）。

## 0. 背景と規則（BS-D1〜D3 と同じ）

- 計画：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を原典の経路 A0〜A9 で消す。設計書は
  `formalization-plans/bhatt-scholze/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、骨組みは `drafts/`（`SerrePositivity/` の外、ビルドしていない）。
  Codex レビュー W9（`review-codex-w9.md`）で条件付き妥当。本体の `BhattScholze/` の Lean は 2a の取り込み（11-05）まで凍結。
- 作業：drafts の `: True := by trivial`／`Type u := sorry` の仮置きを、docstring（概要／方針／規約／使われ方）の主張の具体的な Lean の型に直す。証明は `sorry -- 理由`。
  書き方は完成した A0・A4〜A8 の drafts に揃える。
- **やらないこと**：`lake build`・`lake env lean`、`SerrePositivity/`・設計書・ノートの編集、指定外の drafts の編集（基盤側 `Sheaves/`・`DerivedGeneral/`・`Shared/` は読むだけ。
  足りない補題は「要確認：〜へ」）、新しい `axiom`、主張の数学的な変更（変えたくなったら止めて報告）、`git add -A`。
- 既存の名前は grep で確かめる（`design-status.md` §2 (A)・(B)、`bhatt-scholze-codex-d1.md` §4）。見つからないものは `-- 要確認：` 付きの仮の名前で。
- 止めて報告する点：主張が曖昧で型にできない／設計書と食い違う、既存の名前の形が前提と合わない、一ファイルで `要確認` が 10 を超える。
- 報告：`formalization-plans/bhatt-scholze/report-codex-d4.md`（新規、日本語）。コミットは drafts と報告だけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/report-codex-d4.md && git commit -m "docs(bs): drafts statements (BS-D4 part N)"`。

## 1. 対象と順序（残る `True` の一覧は `report-codex-d3.md` の最終報告）

1. **A2**（設計 `a2-design.md`、25 件。先に行う：A4・A5・A7 の「A2 待ち」の仮置きの行き先）：`drafts/A2/AnimatedAlgebra.lean`（5：`polyCoproduct_isCoproduct`、`polyYoneda_fullyFaithful`、
   `animatedAlgebra_siftedColimits`、`discreteToAnimated_poly`、`discreteToAnimated_fullyFaithful`。P_Σ(Poly_k) は F2 の `SigmaPresheafInfinity`、sifted 延長は `exists_siftedExtension`）、
   `drafts/A2/DerivedPrismaticCohomology.lean`（9：`completeCAlg_siftedColimits`、`prismaticCohomologyCAlg`（A0 の `structurePresheaf` を `ringPresheafToCAlg` で CAlg 値に、S2 の
   `derivedGlobalSectionsCAlg`。**A5 の第 0 脚（D3-01）の行き先**）、`prismaticCohomologyCAlg_eq_totEInfinity`、`prismaticFrobeniusPoly`、`derivedPrismaticCohomology_preservesSifted`、
   `derivedPrismaticCohomology_poly`、`derivedPrismaticFrobenius`（**A4 の `discreteDeltaFrobenius`、A7 の `animatedDeltaFrobenius` の行き先**）、`derivedPrismaticCohomologyDerived`、
   `derivedPrismaticCohomology_h0_ring`）、`drafts/A2/HodgeTateFiltration.lean`（7：`hodgeTatePoly_gr`・`_bounded`、`hodgeTateFiltration_step`・`_gr`・`_exhaustive`・`_zero`
   （D(k)_{p-comp} 内の LΛ_p ∘ Lan、W9 で訂正）、`hodgeTateUnitCAlg`（**A4 の `directHodgeTateUnit`、A7 の `animatedPerfdUnit` の行き先**））、`drafts/A2/BaseChangeAndTensor.lean`
   （4：`derivedPrismaticCohomology_baseChange`（(4)、**A7 の `animatedDelta` の基底移送**）、`derivedPrismaticCohomology_siftedColimit`、`prismaticCohomologyPoly_tensor`、
   `derivedPrismaticCohomology_tensor`（(5)）、`derivedPrismaticCohomology_completion_animated`（D32））。
   A4・A5・A7 の仮置き（`discreteDeltaFrobenius`、`directHodgeTateUnit`、`completeCAlgInclusion`、`reflectCompleteCAlg`、`modPrismFunctor`、`animatedDelta`、`animatedDeltaFrobenius`、
   `animatedRealization`、`animatedPerfdUnit`、`perfdOverPerfectPrism`、`piZeroReflection`）の**正しい行き先を A2 に定義し**、A4・A5・A7 側は編集せず、報告に「仮置き → A2 の宣言」の対応表を
   書く（置き換え自体は中身の段階）。— **停止点 1**。
2. **A3**（設計 `a3-design.md`、13 件）：`drafts/A3/DiscreteCase.lean`（3：`deltaStructure_of_envelopeIso`、`discrete_weaklyInitial`、`exists_initial_of_discrete`。D36 (a)：δ 射は p ねじれなしの標的に
   限定、始性は envelope の普遍性から）、`drafts/A3/LciAndQuasiregular.lean`（10：`lciDerivedEnvelope`・`_eq_prismatic`・`_isEnvelope_of_discrete`、`lci_envelope_surjective_invert_p_universal`
   （G-A3-7、証明予定）、`prismaticCohomology_lci_eq_envelope`（Ex 7.9、原典の順序：B := LΛ_I(E ⊗^L_U A)、H⁰ 比較、W₂ 切断の δ 押し出し、W9-I-39）、`qrsp_isDiscretePrismatic`、
   `qrsp_completelyFaithfullyFlat`、`regularSemiperfectoid_prismatic`（G-A5-17 = G-A2-10）、`qrsp_initial`、`rootQuotient_prismatic_perfection_eq`（Prop 7.10。qrsp は有界 p 冪ねじれつき D39））。
   — **停止点 2**。
3. **A1**（設計 `a1-design.md`、24 件）：`drafts/A1/CrystallineInput.lean`（2：黒箱 `crystalline_deRham_polynomial_Zp` は仕様つき（自然性・乗法・Bockstein・根の遷移）の主張に、
   `hodgeTate_of_deRham_cartier`）、`drafts/A1/HodgeTateMap.lean`（5：`reducedModel`、`hodgeTateMapZero`・`One`、`bockstein_sq_zero`、`hodgeTateMap`。Shared の cup 積・Bockstein・de Rham の
   名前で）、`drafts/A1/HodgeTateComparison.lean`（13：`hodgeTate_iso_polynomial_Zp`（黒箱の系）、`hodgeTate_iso_crystalline`（Cor 5.5）、普遍向き付き prism の性質、Construction 6.1 の
   保存性・Tor 振幅・Δ の比較（Bhatt–de Jong の行の収縮 G-A1-14、Čech 因子 E^• G-A1-16、W9-I-13/18）、`hodgeTate_iso_of_construction61`、底変換 `baseChangeB`・`C` と保存性、
   `baseChange_cechAlexanderAffine_eq`、`hodgeTate_iso`（Thm 6.3）、`bockstein_sq_zero'`、`prismaticCohomology_baseChange'`）、`drafts/A1/DeRhamComparisonPoly.lean`（4：A1-5、D69 の経路：
   普遍向き付き prism A_0 上で Thm 6.4 を行い完全 prism へ底変換。`deRham_iso_polynomial_crystalline`、`_universal`、`_modP`、`deRham_iso_rootAlgebra_modP`。**A5 StrongDescent の
   `rootMap_modP_eq_deRham`・`rootDeRhamSource`・`rootDeRhamAugmentation` の行き先**）。— **停止点 3（総括）**。
各停止点で報告して止まる。総括では直した宣言の数、`要確認` の一覧、設計と違うと感じた点、「仮置き → A2／A1 の宣言」の対応表、drafts 全体に残る `True`（基盤側だけになるはず）。

## 2. 設計上の約束（変わらない）

定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号（ユーザーが付ける）。A2：P_Σ、HT filtration は完備圏内（D31〜D35）、G-A2-10 の前倒し。A3：D36 (a)、qrsp に有界 p 冪ねじれ（D39）、
Ex 7.9 は原典の順序（W9-I-39）、G-A3-7 は証明予定。A1：D68（de Rham 形の黒箱一件、HT は Cartier）、D69（普遍 A_0 上で Thm 6.4 を証明して底変換）、D20（Def 2.42 の平坦性は H⁰ 平坦＋底変換同型）。
