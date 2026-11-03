# Codex 作業指示書 BS-D5：drafts の主張の具体化（第五束：基盤側 Shared・Sheaves・DerivedGeneral。ビルドなし）

作成：2026-11-03（BS 作業チャット）。宛先：Codex（新しいチャット）。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。**
基準コミット：開始時に記入（main `________`。この指示書のコミット以後）。

## 0. 経緯と規則

### 経緯（新しいチャット向けの要約）

- 計画：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を原典 Bhatt–Scholze の経路 A0〜A9 で消す。
  設計書は `formalization-plans/bhatt-scholze/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、Lean の骨組みは `formalization-plans/bhatt-scholze/drafts/`
  （`SerrePositivity/` の外、ビルドしていない。51 本、約 12,100 行）。Codex レビュー W9（`review-codex-w9.md`）で設計は条件付き妥当。
- BS-D1〜D4（`bhatt-scholze-codex-d1.md`〜`d4.md`、報告 `report-codex-d1.md`〜`d4.md`）で、A0〜A9 の drafts にあった `: True := by trivial`／`Type u := sorry` の仮置き
  （計 284 件）を具体的な型にした。**A0〜A9 には仮置きが残っていない。** その過程で出た設計の食い違い D1-01〜D4-06 は設計側で解決済み（`design-status.md` §5）。
- 残る仮置きは基盤側の 53 件（`drafts/DerivedGeneral/` 14、`drafts/Shared/` 28、`drafts/Sheaves/` 11）。これらは ∞ 圏基盤の一般論（∞ 層、D(A) の t 構造と完備化、
  係数制限、Tot_{E∞}、descendability、冪作用 P⁰）で、実装は ∞ レーンの W2b 取り込み後（段 G）。**主張を型にする作業は今できる**ので、それが本束。
- 正本の表：`foundation-entry-points.md`（基盤の入口表）。§1 に 53 件の一つ一つについて「使う側」「D5 で型にできるか（○／△／×）」「推奨する形」を書いた。
  **この指示書は入口表 §1 の形を実行に移すもの**で、迷ったら入口表と各ファイルの docstring（概要／方針／規約／使われ方）に戻る。
- 本体の `BhattScholze/` の Lean は 2a の取り込み（11-05）まで凍結。drafts の import 行は 2a・2b の改名表が来たら追従する（本束の対象外）。

### 規則（BS-D1〜D4 と同じ。太字は本束で特に効く点）

- 作業：基盤側 drafts の `: True := by trivial`／`def … : True := trivial` を、docstring の主張の具体的な Lean の型に直す。証明は `sorry -- 理由`。
  書き方は完成した A0〜A9 の drafts と、同じファイル内の型つき宣言に揃える。
- **やらないこと**：`lake build`・`lake env lean`、`SerrePositivity/`・設計書・ノート・入口表の編集、**A0〜A9 の drafts の編集（読むだけ）**、新しい `axiom`、
  主張の数学的な変更（変えたくなったら止めて報告）、`git add -A`。
- **A 側から参照されている名前は変えない。** 引数を足すのはよいが、足したら報告に「A 側の呼び出し箇所」を列挙する（置き換えは中身の段階）。参照されている名前：
  `totEInfinity`、`completedBaseChange`（A2）、`truncationLE`、`derived_nakayama`、`cAlgRestrictScalars`、`cAlgBaseChange`、`derivedInfinityRestrictScalars`、
  `IsDescendableOver`、`HasDescentIndexLE`、`isDescendable_tot_equiv`、`sectionsOf`、`IsLocalEquivSet`、`presheafPushout`、`Sheafification`、`derivedGlobalSections`、
  `isLimitCone_iff_restrict_cech`、`CechNerveDataLarge`、`regularBockstein`、`bockstein_natural`、`completedForms`、`completedDeRhamComplex`、`cohomologyEquivHomology`、
  `IsConnectiveAt`、`IsCoconnectiveAt`、`cAlgH0Algebra`（A4 の定義。基盤側には別名 `cAlgH0Ring` を新設する）。
- **body が `sorry` の宣言は section `variable` が落ちる**（D4-03・D4-06 の教訓）。利用側が渡す引数は明示の binder にするか、`include x in` を直前に置く。
- 既存の名前は grep で確かめる（`design-status.md` §2 (A)・(B)、入口表 §3 の一覧）。見つからないものは `-- 要確認：` 付きの仮の名前で。
  本束で仮名が要ると分かっているもの：空間の ∞ 圏 `SpaceInfinity`、`discretePresheaf`、`Is0Truncated`（§1 の 3）。
- 止めて報告する点：主張が曖昧で型にできない／設計書・入口表と食い違う、既存の名前の形が前提と合わない、一ファイルで `要確認` が 10 を超える、
  入口表で ○ とした宣言が型にできないと分かった。
- 報告：`formalization-plans/bhatt-scholze/report-codex-d5.md`（新規、日本語）。コミットは drafts と報告だけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/report-codex-d5.md && git commit -m "docs(bs): drafts statements (BS-D5 part N)"`。

## 1. 対象と順序（詳細は入口表 §1 の各表）

### 停止点 1：DerivedGeneral（14 件＋新設の API）

1. `drafts/DerivedGeneral/CompletionFunctor.lean`（5：`completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange`）。
   先に API を揃える：`completeAt (a : A)`（A2/DerivedPrismaticCohomology の定義と同じ式。基盤に移す）、`IsDerivedComplete (s : Finset A)`、`completeSubcomplex s`、
   `completionReflection s : Σ L, QCatAdjunction L (completeSubcomplex s).ι`、`completion s := L ≫ ι`。CAlg 版 `cAlgCompleteSubcomplex s`・`cAlgCompletionReflection s`・
   `cAlgCompletion s` も**ここに**置く（置き場所の最終判断は調整役。A1 `primeAlgReflection`・A2 `prismCompleteReflection`・A4 `reflectCompleteCAlg` の行き先）。
   `completedBaseChange f s := derivedInfinityBaseChange f ≫ completion B (s.image f)` は **A2 の参照箇所を読んでから**引数を決める。
   `completion_tensor_koszul`・`derived_nakayama` は ⊗^L の ∞ 関手を待たず、semifree 代表上の `koszulComplexOn` で述べる（A1 `HasFiniteCompleteTorAmplitude` と同じ）。
2. `drafts/DerivedGeneral/Truncation.lean`（5：`truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`（三つに分ける）、`truncationLE_of_isConnective`、`derived_nakayama`）。
   追加：`truncationLE_step n : FunctorHom (truncationLE A n) (truncationLE A (n+1))`（A2 HodgeTateFiltration:139 が待つ）。
3. `drafts/DerivedGeneral/ScalarRestriction.lean`（4：`derivedInfinityBaseChange_restrictScalars_adjunction`・`cAlgBaseChange_restrictScalars_adjunction` は `QCatAdjunction`、
   `derivedInfinityRestrictScalars_completion` は `completion` の Finset 引数で、`cAlgRestrictScalars_h0` は新設 `cAlgH0Ring (x) : Type u`＋`CommRing`＋`Algebra S` で）。
   報告に「A2 `perfectBaseComparison`・A4 の三件・A5 `prismScalarExtension` が何を呼ぶか」の対応表。— **停止点 1**。

### 停止点 2：Shared（28 件のうち型にできる 22 件）

4. `drafts/Shared/CosimplicialBockstein.lean`（2：`bockstein_leibniz`、`bockstein_natural`。`cohomologyEquivHomology` で `Cosimplicial.cohomology` に移してから cup で述べる）。
5. `drafts/Shared/CosimplicialEInfinity.lean`（4：`totEInfinity_forget`、`totEInfinity_isLimitCone`、`totEInfinity_map`、`derivedGlobalSectionsCAlg_eq_totEInfinity`）。
   `totEInfinity` は**関手形** `totEInfinityFunctor : nerve (CosimplicialAlgebra A) ⟶ CAlg_R A` にし、`totEInfinity X` は `abbrev` で保つ（A1・A2 が参照）。
   `totEInfinity_cohomologyRing` は × のまま（E∞ 代数のホモトピー環の基盤名がない。理由を書く）。
6. `drafts/Shared/DeRhamPolynomial.lean`（1：`completedForms_eq_derivedCompletion_of_boundedTorsion`。`completion k {p}`・`discreteEmbedding`。有界 p 冪ねじれの述語は
   `IsBoundedPrism` が使っている既存名を grep）。
7. `drafts/Shared/EInfinityPowerOperation.lean`（4：`powerOperationZero_zero`（π_0 ≃ `cAlgH0Ring`、Frobenius）、`powerOperationZero_natural`（`homotopyMap` を追加）、
   `powerOperationZero_natTrans : FunctorHom (cAlgForgetDerived k) (cAlgForgetDerived k)`、`powerOperationZero_eq_frobenius_tot`）。
8. `drafts/Shared/Descendable.lean`（16 のうち 11：`isDescendableOver_unit_iff`、`_pushout`、`_comp`、`_tensor`、`_tot_equiv`（`structure AmitsurData` を置く。M = R の場合だけ）、
   `hasDescentIndexLEOver_frobeniusColimit`、`isDescendable_baseChange`、`_comp`、`_tensor`、`_tot_equiv`、`hasDescentIndexLE_frobeniusColimit`、`isDescendable_of_faithfullyFlat`）。
   × のまま残すもの（理由を docstring に）：`hasDescentIndexLEOver_two_of_rhom`・`hasDescentIndexLE_two_of_rhom`（内部 Hom の ∞ 関手がない）、`isDescendableOver_complete`・
   `isDescendable_complete`（完備テンソルが ⊗^L 待ち）、`IsThickTensorIdeal.tensor` の欄（⊗^L 待ち。`finiteColimits`・`retracts`・`shifts` は型にする）。— **停止点 2**。

### 停止点 3：Sheaves（11 件＋S1 の二補題）

9. `drafts/Sheaves/SheafCondition.lean`：A6/ArcSite に仮置きされている S1-E `isSheaf_extensive_iff_preservesFiniteProducts` を**ここに**型つきで置く（A6 側は触らない）。
   `isSheaf_sup_iff`（J ⊔ J′ の層 ⇔ 両方の層）を新設。
10. `drafts/Sheaves/GlobalSections.lean`（`sheafifyUnit_isEquivalence_of_isSheaf`、`derivedGlobalSections_of_le` の `∃ e, True`。ihom の辺に `IsInvertibleEdge`）。
11. `drafts/Sheaves/CechConerveLimit.lean`（`isLimitCone_iff_restrict_cech_large`。`PresheafLarge 𝒟 E := nerve 𝒟ᵒᵖ ⟶ E`、ulift 不要）。
12. `drafts/Sheaves/CAlgValued.lean`（3：`forget_conservative`、`forget_sheafify`（各 F で `FunctorIso`。`Sheafification` は Prop なので関手 L は使えない）、`forget_derivedGlobalSections`）。
13. `drafts/Sheaves/SpaceValued.lean`（6：`sheafification_exists_spaces`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`、`discretePushout_isDiscrete`、`sectionsOf_pushout`、
    `sectionsOf_colimit`）。空間の ∞ 圏は**リポジトリに名前がない**ので `SpaceInfinity : SSet.{u+1}` と `instance : Quasicategory SpaceInfinity` を `-- 要確認（G13、∞ レーン）` 付きの仮名で
    先頭に置き、`discretePresheaf`・`Is0Truncated` も同様。`sectionsOf_colimit` は ∞ 余極限（`Presheaf 𝒞 SpaceInfinity` の `IsColimitCone`）で述べる
    （1 圏の余極限では偽：余等化子で円が出る）。— **停止点 3（総括）**。

各停止点で報告して止まる。総括では直した宣言の数、新設した宣言の一覧（名前・ファイル）、`要確認` の一覧、× のまま残した宣言とその理由、
A 側の呼び出しに影響する引数の変更の対応表、入口表 §1 と違うと感じた点。

## 2. 設計上の約束（変わらない）

定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号（ユーザーが付ける）。基盤側は BS 固有の仮定（prism、p、κ）を持ち込まない（一般の A・E・𝒞 で述べる）。
完備性の述語は `Finset A` の元ごと（p と d は適用側で与える）。切り捨ての名前は原典どおり（connective ＝ D^{≤n}、W9-I-28）。
descendable の一般形は Mod_R の thick ⊗-ideal（W9-II-13、D3-04）、離散環版はその特殊化。Bockstein の係数は共通の基底環 k（W9-I-21、D4-03）。

## 3. 経緯（2026-11-03）

- 指示書作成（入口表 `foundation-entry-points.md` と同時）。開始は BS-D4 の後、2a の取り込みを待たない。基準コミット dc77a84dd。
- 調整役回答（11-03、coordination.md 8ef332d45）：BS-D5 の開始を了承。空間の ∞ 圏の名前の候補は `SpaceInfinity`（∞ レーンが作る）なので、停止点 3 の仮名はこれに揃える。S4・S5 は BS が書く（後続の束）。
- **D5-01**：入口表 §1.2 の shift の式の向きを訂正（`IsConnectiveAt n x ↔ IsConnectiveAt (n-1) (Σx)`、Σ = [1] は `derivedSuspensionShiftObjectIso`）。分解は τ^{≤n} → id → τ^{≥n+1} の cofiber＝fiber 四角形。
