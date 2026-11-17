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
- 報告ファイル：`formalization-plans/bhatt-scholze/reports/report-codex-d1.md`（新規、日本語）。コミットは drafts と報告ファイルだけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/reports/report-codex-d1.md && git commit -m "docs(bs): drafts statements (BS-D1 part N)"`。

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

## 5. 経緯（2026-11-03、停止点 1 まで。新しいチャットで続ける Codex のために）

- **背景**：この計画は Serre positivity の形式化で唯一残る perfectoid 側の文献入力 E3（`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3`）を、
  Bhatt–Scholze 原典の経路（A0〜A9：prismatic site、HT 比較、導来 Δ、semiperfectoid、Def 8.2、Prop 8.5、arc 降下と excision、Prop 8.13・Cor 8.14、§10 の almost、組み立て）で
  消すためのもの。設計は `formalization-plans/bhatt-scholze/design/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、Lean の骨組みは `drafts/`（`SerrePositivity/` の外、
  **一度もビルドしていない**）。Codex のレビュー W9（`review-codex-w9.md`、致命 14 件を訂正）で設計は条件付き妥当と判定済み。
- **いまの段階**：本体の `BhattScholze/` の Lean は論文の層の整理 2a の取り込み（11-05）まで凍結。その間に drafts の `True`／`Type u := sorry` の仮置きを具体的な型に直す
  下書き作業が BS-D1（本指示書）。実装は 2a 後に BS-W10（CompletedTensor の分割、Lemma 10.12）、BS-W11（根添加・付値環・arc site）から。
- **BS-D1 の進み**（報告 `report-codex-d1.md` 第 1〜3 部、コミット 034e12102・1c4a324b8・106e8d227）：
  - 第 1 部：`drafts/A6/ArcSite.lean` の AffCompl・AffPerfd・包含・位相・coverage の三補題を具体化。**D1-01** で停止：S3 の `CechNerveData`（`drafts/Sheaves/CechConerveLimit.lean`）は
    圏 𝒟 の絶対積のデータだが、arc site で要る Čech 項 S ⊗̂_R S は相対（R = S = F_p[t] の恒等被覆で絶対積 S ⊗̂_{ℤ_p} S と異なる）。
    **決定**（Claude、3628dc9ca）：Čech データは被覆 f の生成 sieve Q の圏 `sieveCategory Q`（S1、`drafts/Sheaves/SheafCondition.lean`）の中で取る。
    U = f.op が弱終、U の冪は op R 上のファイバー積。主張を (1) 生成 sieve ごとの Čech 同値 `isSheaf_generateSieve_iff_cech` と (2) 層判定 `isSheaf_arc_iff_cech` に分けた。
  - 第 2 部：(1) と一点被覆の coverage `arcCoverage` を具体化。**D1-02** で停止：有限族の coverage と一点族の coverage は同じ位相を生成しない
    （k × k → k の二つの射影は有限 arc 被覆だが、生成 sieve は一点被覆を含まない。任意の前層では一点 Čech 条件だけで層にならない：二点集合の定数前層と零環の空族）。
    **決定**（Claude、f1947a44c）：`arcTopology = K₁ ⊔ K_ext`（一点被覆と有限積の射影の族）。任意の前層の層判定は「有限積を保つ ∧ 一点被覆の相対 Čech 条件」
    （`PreservesFiniteRingProducts`、S1-E `isSheaf_extensive_iff_preservesFiniteProducts` は基盤待ち）。O（CAlg_ℤ 値）と Hom(T, −) は有限積を保つので Prop 8.10 の帰着は一点被覆で足りる。
  - 第 3 部：D1-02 の三定義、G-A6-11（R₀ = ℤ_p[p^{1/p^∞}]^∧ の表示、S₀ = completionRing(S ⊗_{ℤ_p} R₀)、濃度）、G-A6-3（試験付値環 V の perfectoid な拡大 W と p の両立根）、
    `exists_baseExtension_lift`、`exists_perfectoid_arcCover`、`affPerfdInclusion_isCoverDense`（Mathlib `Functor.isCoverDense_of_generate_singleton_functor_π_mem`）を具体化。
    ArcSite の `True` は 0 件。**停止点 1 完了、検収済み**（734b702ba）。
- **次**：停止点 2（`drafts/A6/ArcSheafProperty.lean`）。要点は §1 の 2 と、続行指示（O は CAlg_ℤ 値、`PreservesFiniteRingProducts` を O と Hom(T, −) について、
  三つの引用の形、G-A6-4〜7、Prop 8.10 の主張）。その後、停止点 3（`drafts/A8/Stratification.lean`）、停止点 4（A0 の三本）。
- **設計上の約束**（変わらない）：定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号（ユーザーが付ける）。主張を変えたくなったら止めて報告。
  ビルド・`lake env lean` なし。編集は drafts の指定ファイルと報告ファイルだけ。
- **第 4 部（停止点 2 の途中、ce81ee8f0）**：`drafts/A6/ArcSheafProperty.lean` の三引用（1a は結論を増大 Čech 複体の完全性 `AugmentedRingCechExact` に、1b は共変
  `A_R (ULift (ZMod p))` → `derivedInfinityCategory (ULift ℤ)` で、1c は短完全列 `MilnorShortExact`）と `cech_exact_of_arcCover_perfect` を具体化。**D1-03** で停止：
  Mathlib の `PreTilt O p` の環構造は `Fact (¬IsUnit (p : O))` を要求し、設計が含む零環（両因子が非零でも相対完備テンソルは零になり得る）と合わない。
  **決定**（Claude）：零環を含む tilt `tiltRing`（零環なら零環、非零なら `PreTilt`。p 完備で非零なら p は Jacobson 根基に入り非単元）と関手性 `tiltMap`、
  `IsTiltGenerator`、G-A6-4 の具体的な型を ArcSheafProperty に置いた（G-A6-14、a6-design §4）。原典の tilt は零環で零環なので定義の変更ではない。
- **次（停止点 2 の残り）**：G-A6-5〜7（`witt_exact_of_perfect`・`modD_exact_of_regular`・`untilt_rankOneValuationRing`・`tilt_rankOneValuationRing`・
  `tilt_arcCoverFamily`・`cech_completion_kills_inverted`）、Prop 8.10（`cech_exact_of_arcCover_perfectoid`・`structurePresheaf_isArcSheaf`・`homPresheaf_isArcSheaf`・
  `perfectoidization_eq_arcCohomology`）、O と Hom(T, −) の `PreservesFiniteRingProducts`。tilt は `tiltRing`・`tiltMap` で述べる。
- **第 5 部（停止点 2 完了、57141fc91、検収済み）**：ArcSheafProperty の残り 10 件を具体化。G-A6-5 は増大余単体的な完全環の図式に levelwise の W_n・W と d の商、
  G-A6-6 は a = d mod p の分岐込み（完備化と体の拡大は別補題 `arcValuation_completeAt`・`arcValuation_extendField`）、G-A6-7 は相対余脈体の次数ごとの a 進完備化、
  Prop 8.10 は一点被覆の相対 Čech 余脈体を次数ごとに完備化した増大交代和複体の完全性、O は `CAlg_R (ULift ℤ)` 値で `structurePresheaf_isArcSheaf : Sheaves.IsSheaf (arcTopologyPerfd …)`、
  Hom(T, −) は `Presieve.IsSheaf`、有限積保存は `PreservesFiniteRingProductsOnPerfd` で O・Hom の二件、Cor 8.11 は StructuredArrow の slice 位相上の RΓ への可逆な辺。
  零環を含む箇所では `CharP` の代わりに `(p : B) = 0 ∧ PerfectRing B p`。要確認 0 件、新しい設計差なし。
- **次**：停止点 3（`drafts/A8/Stratification.lean`、Lemma 10.12）、停止点 4（A0 の三本）。
- **第 6 部（停止点 3 完了、64cfd0b92、検収済み）**：`drafts/A8/Stratification.lean`。G-A8-4 の核は nil イデアル（`RingHom.ker f ≤ nilradical A`、p 冪の指数は b ごと。
  ユーザーの回答と a8-design G-A8-4、7a59fd9ed）、`isUniversalHomeomorphism_of_nil_kernel` に改名。noetherian 近似（ℤ_(p) は ℤ の (p) での局所化、hZp から R への射）、
  `generic_structure`（極小点の剰余体の積、(K ⊗ S)_red の体の積分解、分離閉包と純非分離）、`spread_out_generic`（全極小点を含む D(g)、`HasEtaleFactorization`）、
  `exists_finiteEtaleStratification`（`StratumRing I g = (R/√I)[1/g]`、`earlierIdeal`、(1)(2)(3)、p 反転後の同型は同じ T → S_i の誘導射の全単射）。要確認 0 件。
- **次**：停止点 4（A0 の三本：`drafts/A0/PrismaticSite.lean` の `prismaticCohomology_cutoff_invariant`、`drafts/A0/PrismaticEnvelope.lean` の `IsPrismaticEnvelope.of_closure`・
  `prismaticEnvelope_baseChange_of_variables`、`drafts/A0/CechAlexander.lean` の `cechNerveData`・`cechAlexander_isLimitCone_iff`・`prismaticCohomology_eq_cechAlexanderTot`・
  `cechAlexanderAffine`・`cechAlexanderAffine_computes`・`cechAlexanderAffine_baseChange`）。prismatic site は最初から R 上の相対な圏なので D1-01 の sieve の圏は不要。
- **第 7 部（停止点 4 完了、a3a65d6cd、検収済み）・BS-D1 終了**：A0 の 9 件。cutoff 不変性は `HasEnvelopes P R`・許容 κ ≤ κ′ を仮定し CechAlexander の Tot 比較の直後に（包含と制限は Site）、
  `IsPrismaticEnvelope.of_closure`（A/d = 0 を別扱い）、変数の envelope の完備底変換（`PDCompletionH0`）、`cechAlexander_isCoproduct` は標準頂点の脚の `IsColimit`（def）、
  `cechNerveData`・`cechAlexander_isLimitCone_iff`・`prismaticCohomology_eq_cechAlexanderTot`、Rem 4.19 の模型と Tot 比較・項ごとの底変換。
  **BS-D1 全体：49 件（`True` 45、`Type u := sorry` 4）を具体化、指定対象の残り 0 件。** drafts 全体に残る `True` は 270 件（報告第 7 部の一覧）。次の下書き束は BS-D2。
