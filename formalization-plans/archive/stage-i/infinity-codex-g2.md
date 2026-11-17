# Codex 依頼書 IF-G2：段 G の第二の束 ― G8 の自然性、G8 の一般形、G9・G10、G12

作成：2026-11-04 夜（管理は Claude）。宛先：**∞ の数学レーンの Codex（G1 と同じチャット・worktree `../SerrePositivity-ig1`）**。
前提：[IF-G1](infinity-codex-g1.md)（§2 の進め方・§3 の禁止事項をそのまま使う：新規ファイルだけ、sorry・公理・引用を残さない、全ビルドなし、小さなビルドは coordination.md §2-4a）。G1 の第一区切りは main に入った（7bda72c3c）。
**最初に**：`math/g1` に main（8878743e3 以降。W2c・B4 を含む）を取り込み、衝突は main 側を正として解く（G1 の新規ファイルは変えない）。以後、整理の束が main に入るたびに取り込む。新しい枝 `math/g2` を切ってもよい。

## 1. 項目（この順）

| # | 項目 | 主張（言葉で） | 置き場所 | 使う側 |
| --- | --- | --- | --- | --- |
| G8n | **G8 の X についての自然性**（最優先） | 集合値前層の射 φ : X ⟶ Y について、四角形 Map(Y ⋙ ⊗M, F) → Map(X ⋙ ⊗M, F)（φ の前合成）と Map(M, Γ(Y, F)) → Map(M, Γ(X, F))（drafts の `sectionsOf_map φ` の後合成）、縦は G8 の同値（`sectionsEquivalence` など）、が**空間のホモトピー圏で可換**。高次の整合性は要らない | `F2/Tensor/`（`SetSections` の隣） | BS の S4 の生成辺（篩の包含 S ↪ h_U、「W 局所 ⇔ 層」）と S8-5（任意の局所同値） |
| G8g | G8 の一般の空間値の形 | 空間値前層 X について Map(X ⋙ ⊗M, F) ≃ Map(M, Γ(X, F))、Γ は `weightedSectionsData` の右 Kan 拡張との比較で | `F2/Tensor/` | BS の S8-4 |
| G9・G10 | 効果的エピの Čech 脈体の実現（または Bousfield–Kan との比較）、Δ 上の極限 ＝ 全複体 | IF-G1 の表のとおり | `HomotopyLimits/`・`DoldKanComparison/`・`Derived/` | BS の S3。**BS が S3 の経路を決めてから**（BS に確認。決まっていなければ飛ばす） |
| G12a | 前提 (a)：具体的な `CAlg_R A` のモデル側のホモトピー余極限を coherent nerve の余極限へ移す比較 | 計画 γ3（holim ＝ ∞ 極限）の余極限版 | `ModelBridge/`（中核の外） | G12 |
| G12b | 前提 (b)：セル表示から κ-compact 生成の表示へ移す一般論 | presentable 性の判定に使う | `F2/Presentable/` | G12 |
| G12 | `IsPresentable (CAlg_R A)`（HA 3.2.3.5） | G12a・G12b を使う | `EInfinity/BarrattEccles/` の隣 | BS の A2 以降（CAlg 値の層化） |

## 2. 進め方

1. **G8n を先に**：型を BS の drafts（`formalization-plans/bhatt-scholze/drafts/Sheaves/SpaceValued.lean` の `sectionsOf_map`、S4 の生成辺の sorry）に合わせて短く報告（停止点 1、G8n だけでよい）→ 承認後に証明 → 取り込みは単独でも可（Claude が merge し、BS が sorry を閉じる）。
2. G8g → G9・G10（BS の確認後）→ G12a → G12b → G12。G12a・G12b・G12 は重いので、紙の筋（既存と新規の切り分け、規模の見込み）を先に報告。
3. 項目ごとに別コミット、入口・監査への登録（**監査で `importModules` を使うなら、同じモジュールを `import` 行にも書く**：verify がビルド対象を `import` 行からしか拾わないため。W2c §8）。
4. 終えられない項目は止めて報告。段 F（名前空間の付け替え）が始まる前に、それまでの成果を main に入れる（Claude が日程を伝える）。

## 3. 追記（2026-11-05、G8n の篩包含版の優先と、G14 の追加）

- **G8n は篩の包含の場合を先に**（BS の回答）：任意の篩 S、包含 `S.functorInclusion : S.functor ⟶ yoneda.obj U`、任意の前層 F（層と仮定しない）、指定された極限錐 cS, cU について、四角形（上：`sieveTensorEdge` による前合成、下：`sieveSectionsMap` による後合成、縦：`tensorSpaceFunctor_setWeightHomNatural`）が空間のホモトピー圏で可換。h_U の要素の圏の始対象 (U, 𝟙) を使う直接比較を優先。一般の φ は S8-5 用に後回し。先行分 f2b665682（指定錐版 `sectionsMap`、篩包含の二辺、別版の同値、F2 監査 PASS）は段 F の verify の後に main へ。
- **G14（新規、小さい）**：presentable な E から写像空間で同値を検出する小さい族（BS の drafts の型、main 27636cc4a の `drafts/Sheaves/SheafGenerators.lean`）：

```lean
def IsDetectingFamily {ι : Type u} (M : ι → E _⦋0⦌) : Prop :=
  ∀ {x y : E _⦋0⦌} (f : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y),
    IsIso f ↔ ∀ i, IsQCatEquivalence (PinchedInterval.postcompose (M i) f)

theorem exists_detectingFamily (hE : IsPresentable E) :
    ∃ (ι : Type u) (M : ι → E _⦋0⦌), IsDetectingFamily M
```

  E は `SSet.{u+1}`、添字は `Type u`、写像空間は pinched Hom。既存の `IsPresentable.exists_limitDetectingPresheafModel` を一点の図式に当て、評価 `R ≫ presheafInfinityEvaluation a` を `pinchedHom (g_a) −` と同一視する一歩を足す。置き場所は `F2/Presentable/`（`ReflectiveModelLimitDetection` の隣）。別の書き方が自然なら型を報告（BS が合わせる）。

## 4. 追記（2026-11-05、S3 の経路の決定と G9・G10 の差し替え：BS 11-04 夜、`bhatt-scholze/design/foundation-entry-points.md` §4.1）

- **S3 の経路は (c) Quillen A による余終性**（効果的エピの実現・Bousfield–Kan は採らない）。BS が comma の同一視と縮約（1 圏）を書き、∞ に頼むのは次の三つの小補題（**G9 の差し替え**。型は §4.1）：
  - G9-1：left 側の nerve の Quillen A（既存の right 版 `F2.Presentable.nerveMap_isRightCofinal_of_weaklyContractible_comma` の双対）。
  - G9-2：宇宙の持ち上げで left cofinal は保たれる（`cechShape` は `uliftFunctor.map`）。
  - G9-3：縮約の向きを逆にした版（既存 `nerve_isWeaklyContractible_of_contractionSpan` は T ⟶ 𝟭・T ⟶ const）。
  Δ が `Type` なので、G9-1 に `SimplexCategory` を入れるときの宇宙の扱い（`ULiftHom`／`AsSmall` など）は ∞ 側で決めてよい。drafts の `cechShape` の形に合えばよい。
- **G10 は S3 には不要**、応用（A0 の Čech–Alexander の Tot、Shared/CosimplicialEInfinity）で要る：余単体的 A 加群の D(A) での Δ 上の極限は交代余面複体で計算される（型は §4.1）。G12 より前、G9 の後。
- 順序（改訂）：G8n（篩包含の四角形）と G14 → G9-1〜3 → G8 の一般の φ → G10 → G8 の一般形 → G12。
