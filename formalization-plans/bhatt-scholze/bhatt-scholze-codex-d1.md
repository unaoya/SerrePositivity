# Codex 作業指示書 BS-D1：drafts の主張の具体化（段 1 ③④⑤の入口。ビルドなし）

作成：2026-11-03（BS 作業チャット）。宛先：Codex。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。**
基準コミット：main `e743b6a57`（drafts と設計書はこの時点のもの。以後の他セッションのコミットは触らない）。

## 0. 前提と方針

- 対象は `formalization-plans/bhatt-scholze/drafts/` の骨組み（Lean、ビルドしていない）。設計書（`a*-design.md`）とノート（`exposition/ja/bs/`）は**読むだけ**。
- **やること**：下の各ファイルで `: True := by trivial`／`: True := trivial`／`Type u := sorry` のままの宣言を、docstring（概要／方針／規約／使われ方）に書いてある主張の
  **具体的な Lean の型**に直す。証明は `sorry`（理由を一行添える）。定義は `sorry` のままでよいが、型・インスタンス・単位射は具体的に。
  11-03 に `drafts/A5/RootAdjunction.lean` と `drafts/A6/PerfectoidFiniteProduct.lean` で同じ作業をしてあるので、書き方（型の粒度、`letI`、インスタンスの置き方、
  `sorry -- 理由`）はそれに揃える。
- **やらないこと**：`lake build`・`lake env lean` など Lean の実行の一切、`SerrePositivity/` の編集、設計書・ノートの編集、drafts の他ファイルの編集、新しい `axiom`、
  主張の数学的な変更（原典・設計書と違う主張にしない。違えたくなったら止めて報告）、`git add -A`。
- 型を書くのに要る**既存の名前は grep で確かめる**（`SerrePositivity/` と `.lake/packages/mathlib/`）。design-status §2 (A) に 11-03 の調査結果（12 項目）がある。
  下の §4 にもよく使う名前を挙げた。見つからない名前は `-- 要確認：…` を添えて仮の名前で書く（推測した名前だと分かるようにする）。
- 報告ファイル：`formalization-plans/bhatt-scholze/report-codex-d1.md`（新規、日本語）。コミットは drafts と報告ファイルだけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/report-codex-d1.md && git commit -m "docs(bs): drafts statements (BS-D1 part N)"`。

## 1. 作業 1：段 1 ③④の残り（A6・A8）

1. `drafts/A6/ArcSite.lean`：`AffCompl`・`AffPerfd`（`CommRingCat.{u}` の充満部分圏——導来 p 完備、濃度 ≤ κ——の `SmallModel`。要確認：A0/PrismaticSite の
   `PrismOverSmall` と同じ道具）、`affPerfdInclusion`、`arcTopology`（有限 arc 被覆族の生成 sieve を含む Grothendieck 位相の sInf。A0 の `flatTopology` と同じ形）、
   `arcTopologyPerfd`（`Functor.inducedTopology`）、coverage の三補題 `isArcCoverFamily_baseChange`・`_comp`・`_prod_iff`（`IsArcCoverFamily` は既に具体的）、
   `isSheaf_arc_iff_cech`（S1 の生成系の補題を使う部分は主張だけ）、G-A6-11 の `baseExtension_cardinal_le`・`baseExtensionUnit_pCompletelyFaithfullyFlat`（記録）・
   `exists_baseExtension_lift`、G-A6-3 の `exists_perfectoid_valuation_extension`・`perfectoidBaseRing_toValuationExtension`、`exists_perfectoid_arcCover`
   （`IsArcCoverFamily` の一点族の形で）。設計は a6-design §2.1・§4（G-A6-3・G-A6-11）。
2. `drafts/A6/ArcSheafProperty.lean`：G-A6-1b `arcSheaf_of_vSheaf_of_valuationSquares`（共変 `Ring_{F_p} → D(ℤ)^{≥0}`、W9-II-17。引用なので主張の形だけ正確に）、
   `cech_exact_of_arcCover_perfect`、G-A6-4 `completedTensor_tilt`、G-A6-5 `witt_exact_of_perfect`・`modD_exact_of_regular`（W9-II-20 の形：余単体的な完全環、
   levelwise の W_n、d の cofiber）、G-A6-6 `untilt_rankOneValuationRing`・`tilt_rankOneValuationRing`（a6-design §3.1(2) の四分岐）、`tilt_arcCoverFamily`
   （`IsArcCoverFamilyCharP`）、G-A6-7 `cech_completion_kills_inverted`、`cech_exact_of_arcCover_perfectoid`、`structurePresheaf_isArcSheaf`（O は CAlg_ℤ 値、W9-II-22）、
   `homPresheaf_isArcSheaf`（Mathlib `Presheaf.IsSheaf`、集合値）、`perfectoidization_eq_arcCohomology`（記録）。設計は a6-design §2.2・§3.1・§4。
3. `drafts/A8/Stratification.lean`：`IsUniversalHomeomorphism` の性質 6 件（底変換・合成・冪零核・標数 p の判定・完全環から被約環への普遍同相は全単射・純非分離）、
   `exists_noetherianApproximation`・`generic_structure`・`spread_out_generic`。Lemma 10.12 の最終主張 `exists_finiteEtaleStratification` は結論 (1)(2)(3) を
   具体的な ∃ 文にする（層別 g_1..g_n、各 R_i := (R/(g_1..g_{i−1}))_red[1/g_i]、R_i → T_i 有限エタール、T_i → S_i 普遍同相、各 R_i で p = 0 または p 可逆）。
   設計は a8-design §2.3・§3.4、Codex W9 第 3 部続き 2 §3.5 の筋。Mathlib：`Algebra.IsIntegral`、`PrimeSpectrum.comap`、`Algebra.FinitePresentation`、
   `Algebra.Etale`、`minimalPrimes`、`isOpen_etaleLocus`（要確認：名前）。
- **停止点 1**：A6/ArcSite が済んだ時点。**停止点 2**：A6/ArcSheafProperty。**停止点 3**：A8/Stratification。各停止点で報告して止まる（続行指示を待つ）。

## 2. 作業 2：段 1 ⑤（A0）

1. `drafts/A0/PrismaticSite.lean`：残る `prismaticCohomology_cutoff_invariant`（κ₀ ≤ κ ≤ κ′ の site の包含 ι と、ι に沿う前層の制限で `derivedGlobalSections` を
   比較する可逆な辺。頂点の等号は主張しない、W9-I-03・design-status §2 (B)）。
2. `drafts/A0/PrismaticEnvelope.lean`：`IsPrismaticEnvelope.of_closure`（閉包 J := ker(B → H⁰ の一変数導来 p 完備化 (B/J₀B))、(B) の決定、W9-I-09）、
   `prismaticEnvelope_baseChange_of_variables`（変数の場合の底変換）。
3. `drafts/A0/CechAlexander.lean`：`cechNerveData`（S3 の `CechNerveData` を `PrismOverSmall` の側で、`equivSmallModel` で移送）、`cechAlexander_isLimitCone_iff`、
   `prismaticCohomology_eq_cechAlexanderTot`、`cechAlexanderAffine`（R = A/d⟨X_1..X_r⟩、R の形は (B) の決定：`MvPolynomial (Fin r) (A ⧸ P.ideal)` の一変数 p 進完備化の H⁰）、
   `cechAlexanderAffine_computes`、`cechAlexanderAffine_baseChange`。設計は a0-design §2.8、design-status §2 (B)。
- **停止点 4**：A0 の三本が済んだ時点。総括（直した宣言の数、`要確認` で残した名前の一覧、設計書と違うと感じた点）を報告して終了。

## 3. 止めて報告する点

- docstring の主張が曖昧で型にできない、または設計書と食い違う（その宣言は `True` のまま残し、理由を報告に書く）。
- 既存の名前の形が docstring の前提と合わない（例：`IsCoverDense` の向き、`SmallModel` の宇宙）。
- 一つのファイルで `要確認` が 10 を超える（名前の調査が先に要る）。

## 4. よく使う既存の名前（11-03 の調査）

- perfectoid：`IsIntegralPerfectoid S p`（`CommutativeAlgebra/IntegralPerfectoid.lean`：`Subsingleton S ∨ …`）、`IsPerfectoidization p f`、
  `isIntegralPerfectoid_of_ringEquiv`（`Prism/Perfectoid/PerfectPrismPerfectoid.lean:166`）、Cor 7.3 の入口 `exists_perfectoidization_of_perfectoid_surjective_quotient`
  （`Semiperfectoid/Perfectoidization.lean:383`）、`IsIntegralPerfectoid.isReduced`（`Perfectoid/Torsion.lean`）。
- 完備化：`IsModuleComplete (f : R) (M : ModuleCat R)`（`HA/DerivedCompletion/Module.lean:26`）、`PrincipalCompletionH0 R f`・`principalCompletionCommRing`
  （`HA/DerivedCompletion/PrincipalKoszulRing.lean`）、`completionRing p S`・`completion_existsUnique`（`BhattScholze/Perfectoidization/Derived/Interface.lean:206・235`）、
  `IsAdicComplete (Ideal.span {(p : R)}) R`（Mathlib）。
- tilt：`ModP O p := O ⧸ span {p}`、`PreTilt O p := Perfection (ModP O p) p`（Mathlib `RingTheory/Perfection.lean`）、`WittVector.fontaineTheta R p : 𝕎 R♭ →+* R`
  （Mathlib `RingTheory/Perfectoid/FontaineTheta.lean`、`[Fact (¬IsUnit (p:R))] [IsAdicComplete (span {p}) R]`）、`WittVector.map`・`map_coeff`、`Perfection.map`。
- site：`Functor.IsCoverDense (G : C ⥤ D) (K)`（Mathlib `Sites/DenseSubsite/Basic.lean:92`）、`Functor.inducedTopology`・`Functor.sheafInducedTopologyEquivOfIsCoverDense`
  （`Sites/DenseSubsite/InducedTopology.lean`）、`Presheaf.IsSheaf`、`Sieve.generate`・`Presieve.ofArrows`、`SmallModel`・`equivSmallModel`（Mathlib EssentiallySmall）。
- 付値環：`ValuationRing`、`ringKrullDim`、`IsIntegralClosure`、`integralClosure`、`IsFractionRing`（Mathlib）。界面の `ArcOutside`（`Derived/Interface.lean:645`）。
- ∞ 側（A0 で使う）：`functorVertexEquiv`（`InfinityCategories/Core/EquivalencePath.lean`）、`FunctorIso`、S1〜S3 の名前は `drafts/Sheaves/*.lean`。
