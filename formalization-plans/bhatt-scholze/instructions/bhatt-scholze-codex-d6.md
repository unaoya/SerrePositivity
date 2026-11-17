# Codex 作業指示書 BS-D6：段 G 停止点 1 への追従（Descendable の ⊗^L、S4 の G4・G6、S8 の G13。ビルドなし）

作成：2026-11-04（BS 作業チャット）。宛先：Codex（新しいチャット）。**読んで書くだけの作業で、ビルドも `lake env lean` もしない。** 小さな束（三件）、停止点は最後の一つ。
基準コミット：開始時に記入（main `________`。この指示書のコミット以後）。

## 0. 経緯と規則

### 経緯（新しいチャット向けの要約）

- 計画：E3（`SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` の `exists_perfectoidizationInterfaceE3`）を原典 Bhatt–Scholze の経路 A0〜A9 で消す。
  設計書は `formalization-plans/bhatt-scholze/design/a0-design.md`〜`a9-design.md`、状態は `design-status.md`、Lean の骨組みは `formalization-plans/bhatt-scholze/drafts/`
  （`SerrePositivity/` の外、ビルドしていない。51 本、約 12,700 行）。
- BS-D1〜D5（`bhatt-scholze-codex-d1.md`〜`d5.md`、報告 `report-codex-d1.md`〜`d5.md`）で drafts の仮置きを型にし、残りは Shared の 5 件（理由つき）だけ。
  基盤側の宣言が何を待っているかは `foundation-entry-points.md`（入口表）にある。
- ∞ 圏基盤レーンの段 G（`../infinity-codex-g1.md`、停止点 1 の承認は同 §4、main 7401c3588）から BS への連絡が三つ来た。これに drafts を合わせるのが本束。
  1. **G4・G6 は既存で済む**：`F2.Presentable.functor_isPresentable (nerve Cᵒᵖ) hE`（関手圏の presentable 性）と
     `F2.Presentable.Localization.exists_bousfieldLocalEquivalenceReplacement hE w x`（局所置換の存在）／`bousfield_isReflectiveSubcategory hE w`（反射まで）。S4 はこれを使う。
  2. **⊗^L**：`tensorWith M : D A ⟶ D A`（N ↦ N ⊗ᴸ M）と `tensorLeft M`、対称性 `FunctorIso (tensorWith M) (tensorLeft M)` を `Derived/Tensor/` に置く（**供給予定**、まだ main にない）。
     BS 側で `IsThickTensorIdeal.tensor` の欄（現行 `True`）を `∀ x M, P x → P ((tensorWith M).app _ x)` に替える。
  3. **G13**：`discreteSpaceInclusion : nerve (Type u) ⟶ SpaceInfinity.{u}`（`IsFullyFaithful` つき）と述語 `Is0TruncatedSpace` を `F1/` に置く（**供給予定**）。
     drafts の `Is0Truncated`（前層圏での本質像）との接続——点ごとの適用と `discretePresheafInclusion` の頂点・辺の式——は BS 側。
- 運用（調整役了解、11-03）：drafts の import は**移動後の名前**で書き、書いたら `ls` で実在を確かめる。供給予定の名前は `-- 要確認（IF-G1 ○○：供給予定）` を付けて使う。

### 規則（BS-D5 と同じ）

- `lake build`・`lake env lean` をしない。`SerrePositivity/`・設計書・ノート・入口表・A0〜A9 の drafts は読むだけ。新しい `axiom` なし。主張の数学的な変更なし（変えたくなったら止めて報告）。`git add -A` なし。
- A 側から参照されている名前は変えない（`IsDescendable`、`IsDescendableOver`、`HasDescentIndexLE`、`sheafification_exists`、`Sheafification`、`sheafify`、`discretePresheaf`、`Is0Truncated`、`sectionsOf` ほか）。
- body が `sorry` の宣言は section `variable` が落ちる：利用側が渡す引数は明示の binder か `include x in`。
- 既存の名前は grep で確かめる。供給予定の三つの名前（`tensorWith`、`discreteSpaceInclusion`、`Is0TruncatedSpace`）は仮名のまま `-- 要確認（IF-G1）` を付ける。
- 報告：`formalization-plans/bhatt-scholze/reports/report-codex-d6.md`（新規、日本語）。コミットは drafts と報告だけ：
  `git add -- formalization-plans/bhatt-scholze/drafts formalization-plans/bhatt-scholze/reports/report-codex-d6.md && git commit -m "docs(bs): drafts statements (BS-D6)"`。

## 1. 対象（三件、順序はこのとおり）

1. **`drafts/Shared/Descendable.lean`（⊗^L）**
   - `IsThickTensorIdeal.tensor : True` → `tensor : ∀ (x M : (derivedInfinityCategory A) _⦋0⦌), P x → P ((tensorWith M).app _ x)`（`tensorWith M : derivedInfinityCategory A ⟶ derivedInfinityCategory A`、
     `-- 要確認（IF-G1 ⊗^L：Derived/Tensor/ に供給予定）`）。docstring の「×」を消す。
   - `IsDescendable B : Prop := sorry` → `thickTensorIdealGenerated A ((cAlgForgetDerived A).app _ B) ((cAlgForgetDerived A).app _ (単位の頂点))`（単位の頂点は第 2 部で新設した単位代数の頂点。名前は grep）。
   - (h) 離散底の完備版：`IsThickCompleteTensorIdeal (s : Finset A) P`（`tensor` 欄だけ `(tensorWith M ≫ Derived.completion A s).app _ x` に替えた同じ構造）、`IsDescendableComplete (s) (B)`（完備 thick ⊗-ideal の生成が
     `completion A s` を当てた単位を含む）、`isDescendable_complete (s) (B) (hB : IsDerivedComplete A s ((cAlgForgetDerived A).app _ B)) : IsDescendable A B → IsDescendableComplete A s B`
     （完備化は対称モノイダルな局所化。証明は `sorry`）。`isDescendableOver_complete`（一般底 Mod_R）は Mod_R の完備テンソルが M15 待ちなので **× のまま**（理由を書き換える：⊗^L は来たが Mod_R 側が未定）。
   - `hasDescentIndexLE_two_of_rhom`・`hasDescentIndexLEOver_two_of_rhom` は内部 Hom 待ちのまま ×。
2. **`drafts/Sheaves/GlobalSections.lean`（S4）**
   - `sheafification_exists` を二段に分ける（名前は保つ）：
     `sheafification_of_generatingEdges (J) (hE : IsPresentable E) {I : Type u} (edges : I → (PresheafCat 𝒞 E) _⦋1⦌) (hW : ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F) : Sheafification J E`
     ——証明の筋：`F2.Presentable.functor_isPresentable (nerve 𝒞ᵒᵖ) hE`（`PresheafCat 𝒞 E = (ihom ((uliftFunctor).obj (nerve 𝒞ᵒᵖ))).obj E` なので形が合う）で前層圏が presentable、
     `F2.Presentable.Localization.bousfield_isReflectiveSubcategory (その presentable 性) edges` で局所対象への反射、`hW` で述語を `sheafProperty J` に書き換える。**この補題は `[IsStable E]` を要らない**。
     `exists_sheafGeneratingEdges (J) (hE : IsPresentable E) : ∃ (I : Type u) (edges : I → (PresheafCat 𝒞 E) _⦋1⦌), ∀ F, IsLocalObject (Set.range edges) F ↔ sheafProperty J F`
     ——W ＝ 被覆篩の単射 S ⊗ M → h_U ⊗ M（M は E の生成系）。空間とのテンソルは G8（`-- 要確認（IF-G1 G8：BS が要る形の `Map_PSh(X ⋙ tensorSpaceFunctor hE M, F) ≃ Map_E(M, Γ(X, F))` を供給予定）`）。
     `sheafification_exists (J) [IsStable E] (hE) : Sheafification J E := sheafification_of_generatingEdges J hE _ (exists_sheafGeneratingEdges J hE).choose_spec.choose_spec` の形（`obtain` で）。
   - `drafts/Sheaves/SpaceValued.lean` の `sheafification_exists_spaces` と `drafts/Sheaves/CAlgValued.lean` の `sheafification_exists_cAlg` は、同じ二つの補題から（E = `SpaceInfinity` は `space_isPresentable`、E = `CAlg_R A` は `hA`）。
     証明は `sorry` のままでよいが、docstring の方針を「`sheafification_of_generatingEdges` ＋ `exists_sheafGeneratingEdges`」に直す。
3. **`drafts/Sheaves/SpaceValued.lean`（G13）**
   - `-- 要確認（G13、∞ レーン）` の行を、供給予定の名前への接続に替える：
     `discreteSpaceInclusion : nerve (Type u) ⟶ SpaceInfinity.{u}` と `Is0TruncatedSpace : SpaceInfinity.{u} _⦋0⦌ → Prop` を `-- 要確認（IF-G1 G13：F1 に供給予定）` 付きの仮名で先頭に置く。
     `discretePresheaf_vertex (P) (U : 𝒞) : (discretePresheaf P).app _ (ULift.up (nerveVertex (Opposite.op U))) = discreteSpaceInclusion.app _ (nerveVertex (P.obj (Opposite.op U)))`（点ごとの適用）、
     `discretePresheafInclusion_edge`（φ : P ⟶ Q の辺を各 U で `discreteSpaceInclusion` の辺に送る式。現行の `discretePresheafInclusion` の第二成分の右辺をこれで言い換える）、
     `is0Truncated_iff_pointwise (x) : Is0Truncated x ↔ ∀ U, Is0TruncatedSpace ((vertexToPresheaf x).app _ (ULift.up (nerveVertex (Opposite.op U))))`。
     いずれも証明は `sorry`。`setsToKan`・`kanDiagramCoherentNerve` による現行の構成は残し、`discreteSpaceInclusion` との一致を上の式で述べる。

報告には：変えた宣言と新設した宣言の一覧、仮名三つの使用箇所、A 側の呼び出しへの影響（引数の変更があれば）、∞ レーンに伝えるべき型の要望（供給予定の三名の型が drafts の使い方と合わないと感じた点）。

## 2. 設計上の約束（変わらない）

定義は原典どおり、定理は E3 に要る特別な場合だけ。descendable は [Mat16] の thick ⊗-ideal（決定 2、D49）、完備版は完備テンソル。S4 は HTT 5.5.4.15。S8 の離散埋め込みは点ごと。

## 3. 経緯（2026-11-04）

- 指示書作成（段 G 停止点 1 の承認 7401c3588 を受けて）。基準コミット 95c78fa64。
- 調整役了解（11-04）：方針・仮名運用・S4 の生成辺は G8 待ちで可。G8 は数日先、供給名が入ったら連絡が来る。
- 完了（2074a8d9e、**検収済み**）：三件とも指示どおり。残る `True` は 4。∞ への要望（`discreteSpaceInclusion` の頂点・辺の厳密な等号、`Is0TruncatedSpace` ＝ 離散埋め込みの本質像）は報告の「∞ レーンとの型の照合」。供給名が入ったら仮名を実名に追従する（次の小束）。
