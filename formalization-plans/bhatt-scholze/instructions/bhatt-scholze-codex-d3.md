# Codex 作業指示書 BS-D3：drafts の主張の具体化（第三束：A5 と A6 の excision。ビルドなし）

作成：2026-11-03（BS 作業チャット）。宛先：Codex。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。** BS-D1・BS-D2（`bhatt-scholze-codex-d1.md`・`-d2.md`、各 §経緯）の続き。
基準コミット：開始時に記入（main `________`。BS-D2 完了は 1189e6dfe）。

## 0. 背景と規則（BS-D1・D2 と同じ）

- 計画：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を原典の経路 A0〜A9 で消す。設計書は
  `formalization-plans/bhatt-scholze/design/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、骨組みは `drafts/`（`SerrePositivity/` の外、ビルドしていない）。
  Codex レビュー W9（`review-codex-w9.md`）で条件付き妥当。本体の `BhattScholze/` の Lean は 2a の取り込み（11-05）まで凍結。
- 作業：drafts の `: True := by trivial`／`Type u := sorry` の仮置きを、docstring（概要／方針／規約／使われ方）の主張の具体的な Lean の型に直す。証明は `sorry -- 理由`。
  定義は型・インスタンス・単位射まで具体的に。書き方は完成した `drafts/A6/ArcSite.lean`・`A6/ArcSheafProperty.lean`・`A8/*.lean`・`A4/*.lean`・`A7/*.lean` に揃える。
- **やらないこと**：`lake build`・`lake env lean`、`SerrePositivity/`・設計書・ノートの編集、指定外の drafts の編集（基盤側 `DerivedGeneral/ScalarRestriction.lean` も編集しない。
  足りない補題は「要確認：ScalarRestriction へ」）、新しい `axiom`、主張の数学的な変更（変えたくなったら止めて報告）、`git add -A`。
- 既存の名前は grep で確かめる（`SerrePositivity/`・`.lake/packages/mathlib/`。`design-status.md` §2 (A)・(B)、`bhatt-scholze-codex-d1.md` §4）。見つからないものは `-- 要確認：` 付きの仮の名前で。
  A2 待ちの仮置き（`discreteDeltaFrobenius`・`directHodgeTateUnit`・`completeCAlgInclusion`・`reflectCompleteCAlg`・`modPrismFunctor`・`animatedDelta`・`animatedDeltaFrobenius`・
  `animatedRealization`・`animatedPerfdUnit`）は A4・A7 と同じ仮の名前を使う（新しい仮名を増やさない）。
- 止めて報告する点：主張が曖昧で型にできない／設計書と食い違う、既存の名前の形が前提と合わない、一ファイルで `要確認` が 10 を超える。
- 報告：`formalization-plans/bhatt-scholze/reports/report-codex-d3.md`（新規、日本語）。コミットは drafts と報告だけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/reports/report-codex-d3.md && git commit -m "docs(bs): drafts statements (BS-D3 part N)"`。

## 1. 対象と順序（残る `True` の一覧は `report-codex-d2.md` 第 5 部）

1. **A5 の先行定義**（設計 `a5-design.md` §2.1・§2.2・§3.4）：`drafts/A5/PerfectSite.lean`（8 件：`perfUnder_cechNerveData` は既存 Cor 7.3 の普遍環 `exists_perfectoidization_of_perfectoid_surjective_quotient`
   から直接、Perfd_{S/} の余積は (T₁ ⊗̂_S T₂)_perfd（W9-II-06）、`perfectSite_cechNerveData`、`perfectStructurePresheaf(_isSheaf)`（G-A5-5：O は完全 site で flat 層、Cor 3.12 の制限）、
   `perfectPrism_hom_lift_unique`・`perfectSiteEquivPerfectoidUnder`（Lemma 4.8、既存 `PerfectPrismHomLift`）、`perfectionComparisonLeg`（f_n = φ_B^{-n} ∘ f、W9-II-07）、`perfectionComparison`）、
   `drafts/A5/SemiperfectoidCase.lean`（17 件：G-A5-17 の基底の取り替え `baseComparison`・`cotangent_perfectoid_vanish`・`derivedPrismaticCohomology_baseIndep`、連結性の三段、
   離散性と perfectoid 性（DiscreteCore へ渡す）、Cor 7.3 との比較 `perfectoidizationToUniversal(_splitSurjective)`、全射性の五段 `exists_perfectoid_surjection`〜`surjective_unit_of_semiperfectoid`、
   `perfectoidization_semiperfectoid_iso`）。`IsSemiperfectoid` は perfectoid 環の商（perfectoid 基底が要る、W9-II-16）。— **停止点 1**。
2. **A5 の降下と Prop 8.5**：`drafts/A5/RootAdjunction.lean`（残り 2 件：`algebraicRootClosure_filteredColimit`（`CategoryTheory.Limits` の colimit との比較の形）、
   `polyAlgebraToRoot_pCompletelyFaithfullyFlat`（記録））、`drafts/A5/StrongDescent.lean`（11 件：Lemma 8.6、descendability は `Shared/Descendable` の `IsDescendable`／`IsDescendableOver`（Mat16）、
   n = 1 への帰着、G-A5-6′ は任意の離散 C 加群 L を係数とする (∗) と有限 Koszul 複体 K_A(p,e) の Postnikov filtration（W9 第 2 部続き 6 §G-A5-6′）、`rootMap_modP_eq_deRham` は A1-5 の
   `DeRhamComparisonPoly`、`deRhamOneVariable_formal`（G-A5-12）、`squareZero_rhom_coconnective`（任意係数版））、`drafts/A5/WeaklyInitialAndDescent.lean`（15 件：`rootClosure_isSemiperfectoid`・
   `rootCover_isSemiperfectoid`（G-A5-14、perfectoid 基底）、`algebraicRootCover_properties`・`cech_independent_of_flatSemiperfectoidCover`（G-A5-18、Q(U) 弱始、W9-II-11）、弱始対象と S3 の二回の適用
   `limit_perfUnder_eq_tot`・`limit_perfectSite_eq_tot`・`limit_perfUnder_eq_limit_perfectSite`（D47。S3 は添字圏が大きい版、W9-I-04）、filtered 余極限の段（左辺は A4 の `prismaticPerfection_filteredColimit`）、
   Lemma 8.6 による降下の四段）、`drafts/A5/PerfectSiteComparison.lean`（7 件：Prop 8.5 `perfectionComparison_isIso(_topology)`（⊥ ≤ J ≤ flat の任意の位相、D46）、系 `perfectoidization_isLimit(_u)`・
   `perfectoidization_indep`・`perfectoidization_semiperfectoid`、animated 版 `perfectionComparison_isIso_animated`（D45 改訂、定義域は `CompleteAnimatedAlgebra`）と系 4 `perfectoidization_piZero`）。
   — **停止点 2**。
3. **A6 の excision**（設計 `a6-design.md` §2.3・§2.4・§3.2・§8）：`drafts/A6/SheafOfSetsExcision.lean`（13 件：二つの arc 被覆 `isArcCover_of_arcOutside`・`isArcCover_diagonal_of_arcOutside`・
   `isArcCover_quotient_split`（G-A6-9）、有限積 `perfectoid_factor_of_idempotent`・`perfdUnderProdEquiv`・`perfectoidization_prod`（G-A6-2・G-A6-12）、`excision_of_excision_prod`（(B×C)×_{D×C}C ≃ B×_D C、
   g : B → D と h : C → D を書き分ける、W9-II-19）、`extendArcSheaf`（Mathlib `Functor.sheafInducedTopologyEquivOfIsCoverDense`、包含は `affPerfdInclusion.op`、W9-II-25）、
   `sheafOfSets_excision`・`homSheaf`・`hom_homSheaf_eq`・`homSheaf_pushout`・`homSheaf_quotient_mono`（集合の層の等式と押し出し、1 圏 Mathlib））、
   `drafts/A6/Excision.lean`（5 件：`sectionsOf_homSheaf_eq_perfectoidization`（S8 の Γ(F_T, O) = T_perfd、O は CAlg_ℤ 値を F_U の元の圏で CAlg_R に持ち上げる、W9-II-22）、
   `homPresheafPushout_localEquiv`（S8-2・3）、`perfectoidization_excision`（Cor 8.12、CAlg_R の引き戻し）、`quotient_isModuleComplete`（S/I のみ）、`homPresheaf_completionRing_iso`・
   `sectionsOf_homSheaf_eq_e3Perfd`（T/IT は `completionRing` 経由の自然同型、W9-II-15））、`drafts/A6/PerfectoidFiniteProduct.lean`（1 件：`fontaineTheta_prod_compat`、`wittVectorProdEquiv`・
   `preTiltProdEquiv` の向きを決めて θ の両立を式に）。— **停止点 3（総括）**。
各停止点で報告して止まる。総括では直した宣言の数、`要確認` の一覧、設計と違うと感じた点、A2・基盤待ちの仮置きの一覧。

## 2. 設計上の約束（変わらない）

定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号（ユーザーが付ける）。A5：Prop 8.5 は animated 入力と系 4（D45 改訂）、完全 site の余積は Cor 7.3 の普遍環（W9-II-06）、
S̃ は弱始性・濃度用で filtered 余極限は E 被覆（W9-II-09・11）、semiperfectoid 性には perfectoid 基底（W9-II-16）、G-A5-6′ は任意係数の (∗)（W9-II-12）。
A6：global な affCompl_κ と前段 G-A6-11、Čech データは sieve の圏（D1-01）、層判定は有限積保存 ∧ 一点 Čech（D1-02）、tilt は零環を含む `tiltRing`（D1-03）、O は CAlg_ℤ 値（W9-II-22）、
T/IT は completionRing 経由（W9-II-15）、積の取り替えは (B×C)×_{D×C}C（W9-II-19）。

## 3. 経緯（2026-11-03）

- 第 1 部（4f9f983ee、**停止点 1 完了・検収済み**）：PerfectSite 8 件、SemiperfectoidCase 17 件、`universalPerfectoidRing` は Cor 7.3 の選択。途中の設計上の確認：Lemma 4.8 は有界標的版で十分
  （3acedf8eb）、**D3-01** 比較の第 0 脚は A3 の `prismMapOfDiscrete` ではなく A0/S2 の CAlg 値 RΓ の射影（1480a4e5c）、**D3-02** `PerfUnder_u` は大きい圏なので S3 の大きい版 `CechNerveDataLarge`
  を基盤側に置く（2bb0d406c）、**D3-03** 離散代数の埋め込みと係数制限の比較 `cAlgRestrictScalars_algebraEmbedding` を基盤側に（本コミット）。
- 次：停止点 2（RootAdjunction の残り 2、StrongDescent 11、WeaklyInitialAndDescent 15、PerfectSiteComparison 7）。
- 第 2 部（0deed4fbc、**停止点 2 完了・検収済み**）：RootAdjunction 2、StrongDescent 11、WeaklyInitialAndDescent 15、PerfectSiteComparison 8（系 4 を含む）の計 36 件。
  **D3-04**（Lemma 8.6 の底 Δ_T は離散でない）→ `IsDescendableOver A R B (f : SSet.Edge R B)` を基盤側に確定（df86ebb71）。**D3-05**（CAlg の係数拡大）→ `cAlgBaseChange` を
  ScalarRestriction.lean に（本コミット）。要確認 9 のうち残りは M15 の Mod_D（1）、A1-5（3）、S3 の大きい版（1）、G12（1）、BS-D4（2）。
- 次：停止点 3（A6 の excision：SheafOfSetsExcision 13、Excision 5、PerfectoidFiniteProduct 1）。
- 第 3 部（3b026a1af、**停止点 3 完了・BS-D3 終了・検収済み**）：SheafOfSetsExcision 13、Excision 6、PerfectoidFiniteProduct 1。**D3-06**（延長は比較同値の `.functor`）、
  **D3-07**（S8 の離散入口 `IsLocalEquivSet`・`sectionsOf`・`sectionsOf_eq_limit_elements`・`sections_localEquiv_iso` を基盤側に型つきで）。Cor 8.12 の証明は `sectionsOf_pushout`
  （引き戻しの述語）待ち。**BS-D3 全体 88 件（`True` 81、環の型 7）。** 残りは A1〜A3（BS-D4）と基盤（W2b 後）。
