# quasicategory の一般論（レーン α）

作成日：2026-10-17。現在地（2026-10-18）：A1・A2・A3a–e 完了、A2h 二宇宙版完了。A6 完了。α は今回の担当を完了、A6 後は指示待ち。A4・A5 は D（α-S、InfinityCategories/Stable/）へ移管。A3f は任意、A3g は保留。
全体の目標と依存関係の正本は [infinity-categories.md](infinity-categories.md) §0・§2。

## 0. 目標と範囲

Mathlib の `Quasicategory` をそのまま ∞ 圏の定義とし、Joyal モデル構造・straightening・
∞ 局所化を使わずに、次を順に整備する。

| 項目 | 内容 | 原典 |
| --- | --- | --- |
| A1 | ホモトピー圏の橋：quasicategory で `HomotopyCategory₂ ((truncation 2).obj X) ≌ hoFunctor.obj X`。ホモトピー X ⊗ Δ[1] ⟶ Y ↦ `hoFunctor.map f ⟶ hoFunctor.map g` の自然変換 | HTT 1.2.3、Kerodon 1.4 |
| A2 | join・slice・極限：単体集合の join、slice X_{/p}・coslice、X_{/p} → X が right fibration（X が quasicategory のとき）、終対象・始対象、極限 := slice の終対象、引き戻し四角形、始対象を持つ 1 圏上の極限は F(c) | HTT 1.2.8、1.2.12、2.1.2.1–2.1.2.3、4.1.1.8、Kerodon 4.3.5–4.3.6、4.6.7、7.1、7.2 |
| A3 | 写像空間と同値：pinched 模型と両端固定模型の比較、写像空間は Kan 複体、可逆辺の特徴づけ、充満忠実＋本質的全射 ⇒ 圏同値、成分が可逆な自然変換は可逆、極限は写像空間で検出される | HTT 1.2.5.1、2.2、4.4.2、Kerodon 4.4、4.6.2、4.6.5、7.1 |
| A6 | 関手 ∞ 圏 Fun(K,X) の極限：評価図式の極限の存在から自然な極限錐を構成し、極限錐と点ごとの極限錐を比較 | HTT 5.1.2.2、現行 Kerodon 7.1.8（旧参照 7.1.6） |
| A4 | 安定 ∞ 圏：零対象、fiber・cofiber、安定性、Σ・Ω、h C の三角構造、fiber 列の長完全列 | HA 1.1.1–1.1.3 |
| A5 | 完全関手と自然変換、h での三角関手 | HA 1.1.4 |

α の現担当は A6 の完了・報告まで。A4・A5 は D（α-S）が `InfinityCategories/Stable/` で担当し、α は実装しない。A6 後の工程は別途指示を待つ。基盤全体の正本は [foundations.md](foundations.md)。F1 は α2 が担当し、Core の既存の公開名・型の変更は事前に報告する。

現在の主要宣言：`isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`（A3 の同値判定）、`QCatEquivalence.isLimitCone_iff`（任意の極限錐の同値不変性）、`initialCofinality`（対象・Hom の二宇宙）。

A6 は完了。`exists_pointwiseLimitCone` が各頂点の通常の極限の存在から自然な点ごとの極限錐を構成し、`hasLimit_of_hasPointwiseLimits` が関手 ∞ 圏での極限の存在を与える。`isLimitCone_of_pointwise` が点ごとの極限性からの方向を、`isLimitCone_iff_pointwise_of_hasPointwiseLimits` が同じ存在仮定の下で任意の錐の判定の同値を与える。前提は X の quasicategory 性と明示した点ごとの存在のみ。添字 J・K は任意。証明は join・slice の比較、cocartesian な輸送、相対境界充填、相対骨格を用いる。全公開宣言の正確な型・前提・検証は §6 に記録。

## 1. Mathlib（固定版）の現状

あるもの：`SSet`、`Δ[n]`、`∂Δ[n]`、`Λ[n, i]`、`Subcomplex`、`stdSimplex`、`horn.face`・`horn.hom_ext`、
`Quasicategory`（Λ[n+2, i] の充填）、`InnerFibration`・`innerFibrations`（inner horn の rlp）、
`quasicategory_of_innerFibration`、`KanComplex`、`anodyneExtensions`・`strongAnodyneExtensions`・
`innerAnodyneExtensions`・`strongInnerAnodyneExtensions`、`Subcomplex.Pairing`（anodyne 性を
非退化単体の対で示す技法）、pushout-product（`AnodyneExtensions/PushoutProduct.lean`、`Inner/PushoutProduct.lean`）、
`ihom`（Fun(K, X) の quasicategory 性）、`hoFunctor : SSet ⥤ Cat`（`nerve ⊣ hoFunctor`、有限積保存）、
`Quasicategory₂`・`HomotopyCategory₂`・`Edge.comp`・`CompStruct.comp_unique`・`HomotopicL/R`、
π₀（`PiZero.lean`）、`AugmentedSimplexCategory` の順序和モノイダル構造（`SimplexCategory/Augmented/Monoidal.lean`）。

ないもの：join、slice、left/right fibration、trivial Kan fibration の一般論、終対象・始対象、
極限・余極限、写像空間、圏同値、安定 ∞ 圏。リポジトリ（`HomotopicalAlgebra/`）にもこれらはない。

## 2. A1 の工程

配置は `SerrePositivity/InfinityCategories/Core/`、namespace `SerrePositivity.InfinityCategories`、
集約ファイル `SerrePositivity/InfinityCategories/Core.lean` をルートに 1 行で追加する。
規約の記録は `SerrePositivity/InfinityCategories/Core/README.md`。

| 工程 | ファイル | 内容 |
| --- | --- | --- |
| A1a | `Core/HomotopyCategoryBridge.lean` | `[Quasicategory X]` に対し `HomotopyCategory₂ ((truncation 2).obj X) ≌ hoFunctor.obj X`。`hoFunctor₂` の普遍性（`nerve ⊣ hoFunctor`）か、`HomotopyCategory₂` が同じ生成元と関係で与えられることを使う |
| A1b | `Core/HomotopyCategoryMap.lean` | `HomotopyCategory₂` の射への関手性（`map`、`map_id`、`map_comp`）と A1a の自然性 |
| A1c | `Core/HomotopyNatTrans.lean` | ホモトピー H : X ⊗ Δ[1] ⟶ Y（両端 f, g）から自然変換 `hoFunctor.map f ⟶ hoFunctor.map g`。成分は各頂点での辺、自然性は Δ[1] × Δ[1] の二つの三角形 |
| A1d | `Core/Checks.lean` | `nerve C` での具体化、公理監査 |

## 3. A2 の工程

| 工程 | ファイル | 内容 |
| --- | --- | --- |
| A2a | `Core/Join.lean` | join K ⋆ L。n 単体は k ∈ {−1, …, n} ごとの K_k × L_{n−1−k}（K_{−1} = L_{−1} = 点）の直和。Δ の射 α : [m] → [n] は {0..k} の逆像で分解。包含 K → K ⋆ L ← L、`Δ[i] ⋆ Δ[j] ≅ Δ[i+j+1]`、関手性、`∅ ⋆ L = L`、結合律は必要な範囲だけ |
| A2b | `Core/Slice.lean` | p : K ⟶ X に対し slice X_{/p}：n 単体は Δ[n] ⋆ K ⟶ X で K 上 p に一致するもの。coslice X_{p/}。射影 X_{/p} → X。K = Δ[0] の場合 X_{/x} |
| A2c | `Core/JoinAnodyne.lean` | pushout-join 補題：単射 A₀ → A、B₀ → B に対し (A₀ ⋆ B) ∪ (A ⋆ B₀) → A ⋆ B が、一方が right／left anodyne のとき inner anodyne（HTT 2.1.2.3、Kerodon 4.3.6）。`Subcomplex.Pairing` で示す。最初に紙で正確な文言を固定する |
| A2d | `Core/RightFibration.lean` | left/right fibration を left/right horn の rlp で定義。right fibration ⇒ inner fibration。X が quasicategory なら X_{/p} → X は right fibration、よって X_{/p} は quasicategory（HTT 2.1.2.1–2.1.2.2） |
| A2e | `Core/Terminal.lean` | 終対象 x：n ≥ 1 で最後の頂点が x の ∂Δ[n] → X が Δ[n] に延びる（HTT 1.2.12.3）。X_{/x} → X が trivial Kan fibration との同値。二つの終対象は h X で同型。始対象は双対 |
| A2f | `Core/Limit.lean` | 極限 := X_{/p} の終対象。錐 Δ[0] ⋆ K ⟶ X に対する `IsLimitCone`。一意性は h(X_{/p}) で |
| A2g | `Core/Pullback.lean` | K = Λ[2, 2]。`Δ[0] ⋆ Λ[2, 2] ≅ Δ[1] ⊗ Δ[1]` を経て、四角形 Δ[1] ⊗ Δ[1] ⟶ X に対する `IsPullbackSquare` |
| A2h | `Core/InitialCofinality.lean` | 1 圏 I が始対象 c を持ち F : nerve I ⟶ X なら、制限 X_{/F} → X_{/F(c)} が trivial Kan fibration（HTT 4.1.1.8 の必要な場合、Kerodon 7.2.2）。{c} → nerve I の anodyne 性と A2c で示す。最初に紙で文言を固定する |
| A2i | `Core/Checks.lean` | `nerve C` での極限が 1 圏の極限と一致する例、公理監査 |

## 4. 設計上の決定

- join は直接定義する。`AugmentedSimplexCategory` の順序和による Day 畳み込みは使わない。
- left/right/trivial Kan fibration は lifting property（`MorphismProperty.rlp`）で定義し、
  Mathlib の `innerFibrations`・`fibrations` と同じ流儀にする。
- 終対象は HTT 1.2.12.3 の充填条件で定義し、写像空間の可縮性（A3）との同値は後で示す。
- A2c と A2h の文言は実装前に紙で固定し、`Core/README.md` に記録する。
- `sorry`・公理・引用は導入しない。Mathlib の更新は待たない。

## 5. 受入基準

1. 各ファイルがビルドし、公開宣言は標準 3 公理のみ。
2. docstring は README「Conventions」の形式。原典の番号を書く。
3. §6 に公開宣言名・正確な型・前提・未完了の範囲を記録する。

## 7. A3 の工程（2026-10-18 追加）

A1・A2 の完了を受けて着手する。優先順は G1（infinity-categories.md §0）と D4・ε が使う順。
Joyal モデル構造は使わず、Kerodon 第 4 章の組み合わせ論で進める。
各工程の文言（特に A3b）は実装前に原典と照合して `Core/README.md` に記録する。

| 工程 | ファイル | 内容 | 原典 |
| --- | --- | --- | --- |
| A3a | `Core/Equivalence.lean` | quasicategory の同値：f : X ⟶ Y、g : Y ⟶ X と、`hoFunctor.obj (ihom X X)` で可逆な 2 胞体 g ∘ f ≅ id、f ∘ g ≅ id（`QCat.strictBicategory` の同値）。合成・逆、`hoFunctor` が圏同値に送ること（A1c）。頂点の同型 := h X の同型 | HTT 1.2.10、Kerodon 1.5.? |
| A3b | `Core/InvertibleEdge.lean` | Joyal の定理：quasicategory X の辺 e が h X で可逆 ⟺ e を含む外側ホーン Λ[n,0]（最初の辺が e）・Λ[n,n]（最後の辺が e）が充填できる。系：X が Kan 複体 ⟺ h X が亜群 | HTT 1.2.4.3、2.1.2.?、Kerodon 4.4.2（Theorem 4.4.2.6）、4.4.3 |
| A3c | `Core/MappingSpaceKan.lean` | 右 pinched 写像空間 `pinchedHom x y`（`PinchedHom/Basic.lean`）が Kan 複体。left 版も。π₀ = h X の Hom | HTT 1.2.2.3、Kerodon 4.6.5.? |
| A3d | `Core/TerminalMappingSpace.lean` | x が終対象 ⟺ 全ての z で pinchedHom z x が可縮（終対象の列は可縮な Kan 複体）。系：終対象は h X の同型で閉じる。`IsLimitCone` は錐の頂点の同型で閉じる（同じ図式上の錐が slice で同型なら一方が極限なら他方も） | HTT 1.2.12.4、1.2.12.9、Kerodon 4.6.7 |
| A3e | `Core/FullyFaithful.lean` | 充満忠実（写像空間のホモトピー同値）＋本質的全射（h で）⇒ A3a の同値。同値は極限錐を保ち反映する | HTT 2.2.?、Kerodon 4.6.2.21、7.1.? |
| A3f（任意） | `Core/MappingSpaceModels.lean` | pinched 模型と両端固定模型 `Fun(Δ[1], X) ×_{X×X} {(x,y)}` の比較 | Kerodon 4.6.5.10 |
| A3g（保留） | `Core/LimitDetection.lean` | 極限は写像空間で検出される。N7 の直接証明がうまく行けば不要 | Kerodon 7.1.? |

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-log.md](../../infinity-core-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
