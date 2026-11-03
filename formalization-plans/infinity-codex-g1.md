# Codex 依頼書 IF-G1：段 G の最初の束 ― BS 発の一般論の ∞ 側（G3・G4・G6・G7・G8・G9・G10・G12・G13・⊗^L・Core の小補題）

作成：2026-11-03 深夜（∞ 基盤の整備、管理は Claude）。宛先：**∞ の数学レーンの Codex（整理の W2c とは別のチャット・別の worktree）**。
位置づけ：[infinity-foundation-plan.md](infinity-foundation-plan.md) 段 G の M12b・M12c・M12d と β5 の一部。BS の設計書 [infinity-sheaves-design.md](bhatt-scholze/infinity-sheaves-design.md) §4（G1〜G12）と入口表 [foundation-entry-points.md](bhatt-scholze/foundation-entry-points.md) §4・§5 が出所。使う側は BS の drafts（`formalization-plans/bhatt-scholze/drafts/`）で、そこに仮置き（`sorry`）の形で**型が書いてある**。
**原則**：新しいファイルだけを書く（既存の宣言の本文・型・名前は変えない）。`sorry`・公理・新しい引用を残さない（終えられない項目は止めて報告）。全ビルドはしない（新規ファイルとその閉包の `lake build` だけ。§2-4a の規則で鍵と `ps` を確かめる）。整理の束（W2c・段 F）が同じ層のファイルを動かすことがあるので、import は既存の入口（`F2.Presentable` など）を使い、改名表が来たら追従する。

worktree：`../SerrePositivity-ig1`（新規。`git worktree add ../SerrePositivity-ig1 -b math/g1 main`）。キャッシュがあるので復元は数分。

## 1. 項目（BS の点検表 §5 の順）

| # | 項目 | 主張（言葉で） | 置き場所 | 既存の部品・前提 | 使う側（drafts） |
| --- | --- | --- | --- | --- | --- |
| G3 | `IsPresentable (derivedInfinityCategory A)` | D(A) は presentable（HA 1.3.5.21 の系）。compact 生成された安定 ∞ 圏は presentable、D(A) は A の shift で compact 生成される | `Derived/`（新しい下位 `Derived/Presentable/`） | `F2/Presentable/Definition`（`IsPresentable`）、`IndPresentable`、`StablePresentable`（骨組み）、Derived の κ-compact な余積・compact 生成の部品 | S2 `hasLimit_presheaf`、A0・A2・A5・A6 |
| G4 | 前層 ∞ 圏の presentable 性（HTT 5.5.3.6） | 𝒞 小・E presentable ⇒ `ihom (uliftFunctor.obj (nerve 𝒞ᵒᵖ)) E` は presentable | `F2/Presentable/` | `Presentable/FunctorPresheafModel`・`SmallShapePresentable`（確認）、accessible の一般論 | S4 |
| G6 | 局所置換の存在（HTT 5.5.4.15 前半） | E presentable、W が射の小さい集合なら、各対象に W 局所置換がある | `F2/Presentable/`（`LocalReplacementReflection` の隣。後半＝反射の構成は既存） | `Localization/BousfieldReflection`、`LocalReplacementReflection` | S4 |
| G7 | 安定 ∞ 圏の間の左随伴は完全（HA 1.1.4.1） | 左随伴は余極限を保ち、安定なら有限極限も保つ | `Stable/` | Stable の完全関手の定義、F1B の随伴 | S5（層化の完全性） |
| G8 | 空間とのテンソル | presentable E、空間 X、M ∈ E に対し X ⊗ M と、Map(X ⊗ M, F) ≃ Map(M, lim_{el X} F)（HTT 5.1.5・4.2.4） | `F2/`（`F2/Tensor/`）か `HomotopyLimits/` | F1 の Yoneda・表現可能関手・随伴の Hom 表示、HomotopyLimits の極限 | S3 の証明、S4、S8-4 |
| G9・G10 | 効果的エピの Čech 脈体の実現（または Bousfield–Kan との比較）、Δ 上の極限 ＝ 全複体（Dold–Kan の双対） | 空間の π₀ 全射 X → Y の Čech 脈体の幾何学的実現は Y と同値；D(A) の余単体的対象の極限は全複体で計算される | `HomotopyLimits/`、`DoldKanComparison/`（双対）・`Derived/` | HomotopyLimits の Bousfield–Kan、Derived の `CofinalLimitTransfer`・`WeaklyContractibleConstantLimit`、DoldKanComparison 層 | S3 `isLimitCone_iff_restrict_cech` |
| G12 | `IsPresentable (CAlg_R A)`（HA 3.2.3.5） | E∞ 代数の ∞ 圏は presentable。忘却の極限保存は既存（`FreeProbeDerivedLimits`） | EInfinity 側（`EInfinity/BarrattEccles/` の隣。E2 レーンの範囲） | `BarrattEccles/CAlg`、転送モデル構造、`FreeProbeDerivedLimits` | `sheafification_exists_cAlg`、A2、A5 |
| G13 | 離散埋め込みと 0 切り捨て | `Type u → 𝒮` の離散埋め込み（集合を離散空間に）と、0 切り捨ての公開名の照合（既存なら名前を報告、なければ定義） | `F1/`（`SpaceInfinity` の隣）か `F2/Presentable/SpacePresentable` の隣 | `SpaceInfinity`、`space_isPresentable`（既存） | S8-1・S8-2 |
| ⊗^L | 導来テンソルの ∞ 関手（β5 の一部） | 固定対象とのテンソル `tensorWith M : D(A) ⟶ D(A)` の ∞ 関手と対称性 `tensorWith M ⋙ … ≅ …`。複体レベルの `derivedTensor*`（HA）の同型を dg nerve で関手化 | `Derived/`（`Derived/Tensor/`） | `dgSemifreeDerivedHomTensorInfinity`（Derived）、HA の `DerivedTensor*`、DGNerve の関手性 | M15 descendable の thick ⊗-ideal |
| Core | 小さい模型の nerve の比較 | `uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C` の比較射（存在確認のうえ、なければ Core に一つ） | `Core/` | Core の `uliftFunctor`・nerve | A0 `structurePresheafDerived` |

## 2. 進め方

1. **型の確定を先に**：各項目について、BS の drafts の仮置きの型（例：`hasLimit_presheaf (hE : IsPresentable E) (F : Presheaf 𝒞 E) : HasLimit F`、`sheafification_exists`、`IsThickTensorIdeal.tensor`）を読み、∞ 側で置く宣言の**型**を決めて、項目ごとに「主張・型・置き場所・前提」を短く報告する（**止めて報告する点 1**、項目ごとでよい）。BS の drafts と型が食い違う場合は BS に合わせるか、差を報告して Claude が BS と調整する。
2. 承認後に証明を書く。項目ごとに別コミット（「G3」「G4」…）。新規ファイルは置き場所の入口（`F2/Presentable.lean` など）に登録し、監査（`make_area_audits.py` の再生成）に入れる。公理は propext・Classical.choice・Quot.sound だけ。
3. ビルドは新規ファイルとその閉包だけ。下流への影響は入口への 1 行の追加だけなので、全ビルドは暦の他の束に便乗する（Claude が合図）。
4. 順序は表のとおり（G3 → G4 → G6 → G7 → G8 → G12 → G13 → ⊗^L → Core。G9・G10 は S3 の証明経路が決まってから）。重いもの（G4・G8・G12）は、紙の筋を §1 の報告に添えてから着手する。
5. 終えられない項目（既存の部品が足りない、前提の一般論が要る）は止めて報告（`sorry` を残して先へ進まない）。

## 3. 禁止事項

- 既存の宣言の本文・型・名前の変更。整理の束（W2c・段 F）の対象ファイルの編集。全ビルド。`sorry`・公理・引用の追加。BS の drafts の編集（型の調整は報告で）。

## 4. 追記（2026-11-04 未明、停止点 1 の承認：型案と順序）

**承認**：型案はすべて採る（略記 D A・↑K・PSh C E も報告の定義でよい）。項目ごとの判断：

| # | 判断 |
| --- | --- |
| G4 | **既存で済む**：`F2.Presentable.functor_isPresentable (nerve Cᵒᵖ) hE`。新規なし。BS の S4 はこれを使う（Claude が BS に伝える） |
| G6 | **既存で済む**：`F2.Presentable.Localization.exists_bousfieldLocalEquivalenceReplacement hE w x`（反射まで使うなら `bousfield_isReflectiveSubcategory hE w`）。新規なし。BS に伝える |
| G7 | 承認。`isExactFunctor_of_adjunction` を `Stable/` に。層圏の安定性は S5 側の前提でよい |
| Core | 承認。`smallModelNerveComparison C` を `Core/` に（向きは報告のとおり） |
| G13 | 承認。`discreteSpaceInclusion : nerve (Type u) ⟶ SpaceInfinity.{u}` と `IsFullyFaithful`、述語 `Is0TruncatedSpace` を `F1/` に。BS の `Is0Truncated`（前層圏での本質像）との接続（点ごとの適用と `discretePresheafInclusion` の頂点・辺の式）は BS 側。Claude が伝える |
| ⊗^L | 承認。`tensorWith M : D A ⟶ D A`（N ↦ N ⊗ᴸ M）と `tensorLeft M`、対称性 `FunctorIso (tensorWith M) (tensorLeft M)` を `Derived/Tensor/` に。BS の `IsThickTensorIdeal.tensor` の欄（現行 `True`）を `∀ x M, P x → P ((tensorWith M).app _ x)` に替えるのは BS 側の調整（Claude が伝える） |
| G3 | 承認、ただし**紙の筋を先に**（§2-4）：D(A) が A の shift で compact 生成されること、各対象が半自由セル閉包の小模型から filtered 余極限で表示されること、accessibility。既存の部品で足りない箇所を一覧にしてから着手。全小図式の余極限は `Derived/StableLimits` の範囲を確認 |
| G8 | 承認。まず **BS が要る形**（S4 の篩と表現可能＝集合値の X）で `Map_PSh(X ⋙ tensorSpaceFunctor hE M, F) ≃ Map_E(M, Γ(X, F))` を、草稿の `sectionsOfDiagram X F` の極限に一致する形で供給する。一般の空間値 X（S8-4、`weightedSectionsData` の右 Kan 拡張との比較）は後回し |
| G12 | 承認、ただし**最後**。EInfinity 側（E2 レーンの範囲）で重い（転送モデル構造の accessible 表示と具体的 nerve への比較）。紙の筋を先に報告してから。非安定な係数での層化は BS 側 |
| G9・G10 | S3 の経路決定後（保留のまま） |

**順序**：G7 → Core → G13 → ⊗^L → G3（紙の筋 → 証明）→ G8 → G12。項目ごとに別コミットと入口への登録、監査の再生成。

**ビルド**：11-04 未明は論文の層 2a の全ビルドと verify が走っている。新規ファイルの型検査（小さなビルド）も、それが終わるまで待つ（§2-4a：`ps` で `lake build`・`verify.sh` がないことを確かめてから）。Lean のテキストは書き進めてよい。
