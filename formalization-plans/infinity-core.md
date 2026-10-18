# quasicategory の一般論（レーン α）

作成日：2026-10-17。現在地（2026-10-18）：A1・A2・A3a–e 完了、A2h 二宇宙版完了。A6 進行中。次は A4・A5。A3f は任意、A3g は保留。
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

担当順は A6 → A4 → A5。基盤全体の正本は [foundations.md](foundations.md)。F1 は α2 が担当し、Core の既存の公開名・型の変更は事前に報告する。

現在の主要宣言：`isQCatEquivalence_iff_fullyFaithful_essentiallySurjective`（同値判定）、`QCatEquivalence.isLimitCone_iff`（任意の極限錐の同値不変性）、`initialCofinality`（対象・Hom の二宇宙）、`IsPointwiseLimitCone`・`HasPointwiseLimits`（A6 の主定理の条件）、`isTerminalVertex_functorVertex_of_pointwise`（点ごとの終対象から関手単体集合の終対象）。A6 は標的を固定した相対境界充填の関手への移送まで完了し、任意図式の錐との比較と主定理は未完了。

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

## 6. 記録

（各工程の完了時に追記する。）

### A1a（2026-10-17）：ホモトピー圏の比較同値

`Core/HomotopyCategoryBridge.lean` に以下を実装した。
namespace は全て `SerrePositivity.InfinityCategories`、宇宙は任意の `u`。
以下は `open CategoryTheory SSet SSet.Truncated SimplicialObject.Truncated` の下での正確な型。

```lean
pathToEdgeHomotopyCategory (A : SSet.Truncated.{u} 2) [Quasicategory₂ A] :
  A.HomotopyCategory ⥤ HomotopyCategory₂ A

homotopic_path_eq (A : SSet.Truncated.{u} 2)
  {x y : A _⦋0⦌₂} {f g : Edge x y} (h : HomotopicL f g) :
  HomotopyCategory.homMk f = HomotopyCategory.homMk g

edgeToPathHomotopyCategory (A : SSet.Truncated.{u} 2) [Quasicategory₂ A] :
  HomotopyCategory₂ A ⥤ A.HomotopyCategory

edge_path_inverse (A : SSet.Truncated.{u} 2) [Quasicategory₂ A] :
  edgeToPathHomotopyCategory A ⋙ pathToEdgeHomotopyCategory A = 𝟭 (HomotopyCategory₂ A)

path_edge_inverse (A : SSet.Truncated.{u} 2) [Quasicategory₂ A] :
  pathToEdgeHomotopyCategory A ⋙ edgeToPathHomotopyCategory A = 𝟭 A.HomotopyCategory

homotopyCategoryBridge (X : SSet.{u}) [Quasicategory X] :
  HomotopyCategory₂ ((truncation 2).obj X) ≌ hoFunctor.obj X
```

証明は道の圏の普遍性と辺の商を往復する。比較関手の逆関係は辺の生成元上で証明した。
原典：HTT §1.2.3、Kerodon Construction 1.4.5.1、Proposition 1.4.5.7。
対象 `lake build SerrePositivity.InfinityCategories.Core` は終了コード 0。
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0、上記全 6 宣言が
`propext`・`Classical.choice`・`Quot.sound` のみ。追加公理・引用・`sorry` はない。
`Core.lean` を集約とし、ルートにはその import を 1 行追加した。
A1b〜A1d・A2a〜A2i は未完了であり、自然性や極限の理論の完成は主張しない。

### A1b（2026-10-17）：関手性と比較の自然性

`Core/HomotopyCategoryMap.lean` の公開宣言は次の 4 件。
namespace は `SerrePositivity.InfinityCategories.HomotopyCategoryMap`。
任意の宇宙 `u`、`{X Y Z : SSet.{u}}` を用い、各宣言が使う単体集合のみ
`[Quasicategory X]`・`[Quasicategory Y]`・`[Quasicategory Z]` を仮定する。
`open CategoryTheory SSet SSet.Truncated` の下での型は次の通り。

```lean
map {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
  HomotopyCategory₂ ((truncation 2).obj X) ⥤ HomotopyCategory₂ ((truncation 2).obj Y)

map_id {X : SSet.{u}} [Quasicategory X] : map (𝟙 X) = 𝟭 _

map_comp {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ⋙ map g

bridge_naturality {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
  map f ⋙ (homotopyCategoryBridge Y).functor =
    (homotopyCategoryBridge X).functor ⋙ (hoFunctor.map f).toFunctor
```

辺と合成二単体の像から関手を構成し、代表元上で恒等・合成・自然性を示した。
原典：HTT §1.2.3、Kerodon §1.4.5（特に Proposition 1.4.5.7）。
`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計全 10 公開宣言が標準三公理のみ。
A1c〜A1d・A2a〜A2i は未完了。

### A1c（2026-10-17）：ホモトピーから自然変換

`Core/HomotopyNatTrans.lean` の公開宣言は次の 4 件。
namespace は `SerrePositivity.InfinityCategories`。宇宙 `u` は任意。
`open CategoryTheory MonoidalCategory SSet SimplicialObject.Truncated` と
`open scoped Simplicial` の下で、正確な型は次の通り。

```lean
homotopyIntervalEdge : SSet.Truncated.Edge
  (X := (truncation 2).obj (Δ[1] : SSet.{u}))
  (stdSimplex.obj₀Equiv.symm 0) (stdSimplex.obj₀Equiv.symm 1)

homotopyNatTrans {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) :
  (hoFunctor.map (SSet.ι₀ ≫ H)).toFunctor ⟶
    (hoFunctor.map (SSet.ι₁ ≫ H)).toFunctor

homotopyNatTrans_app {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (x : X _⦋0⦌) :
  (homotopyNatTrans H).app (SSet.HomotopyCategory.mk x) =
    SSet.Truncated.HomotopyCategory.homMk
      (((SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).tensor
        homotopyIntervalEdge).map ((truncation 2).map H))

homotopyNatTransOfEndpoints {X Y : SSet.{u}} {f g : X ⟶ Y}
  (H : X ⊗ Δ[1] ⟶ Y) (h₀ : SSet.ι₀ ≫ H = f) (h₁ : SSet.ι₁ ≫ H = g) :
  (hoFunctor.map f).toFunctor ⟶ (hoFunctor.map g).toFunctor
```

quasicategory の仮定は不要。成分は頂点での縦辺の像。
自然性は `HomotopyCategory.BinaryProduct.square` を使う。この補題の証明は
正方形の二つの三角形（`idComp` と `compId` のテンソル）の合成関係である。
原典：HTT §1.2.3、Kerodon §1.4.5。
A1d と A2a〜A2i は未完了。

対象 `lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 14 公開宣言を監査し、許された標準三公理以外への依存はない。

### A1d（2026-10-17）：通常の圏の nerve での検査

`Core/Checks.lean` の公開宣言は次の 2 件。
namespace は `SerrePositivity.InfinityCategories`。宇宙 `u` は任意。
`open CategoryTheory SSet SSet.Truncated` の下での正確な型：

```lean
nerveHomotopyCategoryEquivalence (C : Type u) [Category.{u} C] :
  HomotopyCategory₂ ((truncation 2).obj (nerve C)) ≌ C

nerveBridge_map_edge {C : Type u} [Category.{u} C] {x y : C} (f : x ⟶ y) :
  (homotopyCategoryBridge (nerve C)).functor.map
    (HomotopyCategory₂.homMk (CategoryTheory.nerve.edgeMk f).toTruncated) =
      SSet.HomotopyCategory.homMk (CategoryTheory.nerve.edgeMk f)
```

前提は通常の小さい圏のみ。A1a の同値と nerve 随伴の可逆な余単位を合成した。
辺では A1a が元の射に対応する辺を保持することを定義から確認した。
原典：HTT §1.2.3、Kerodon Example 1.4.5.4。
`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計全 16 公開宣言が標準三公理のみ。A1a〜A1d は完了。
A2a〜A2i は未完了であり、nerve における極限の一致はこの工程に含めない。

### A1 最終全体ビルド（2026-10-17）

A1d までを含めた `set -o pipefail; lake build` は終了コード 0
（7335 jobs）。他チャットのルート追加 import を含む作業ツリーで確認した。
Core の変更には他チャットのハンクを含めていない。

### A2a 前段階（2026-10-17）：直接表現と切断の計算

**A2a は未完了。** A2a・A2b の設計を `Core/README.md` に記録して報告した。
次数 −1 を頂点数 0 で表し、join の n 単体を計画通りの直和で直接定義する。
slice は `{σ : join Δ[n] K ⟶ X // joinInr Δ[n] K ≫ σ = p}` とする設計。
§4 の設計は変更していない。

`Core/Join.lean` の前段階の公開宣言は次の 14 件。
namespace は `SerrePositivity.InfinityCategories.Join`、宇宙 `u` は任意。
`open CategoryTheory SSet`、`open scoped Simplicial` の下での正確な型：

```lean
augObj (K : SSet.{u}) : ℕ → Type u

augMap (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) :
  augObj K n → augObj K m

augMap_id (K : SSet.{u}) (n : ℕ) (x : augObj K n) :
  augMap K (OrderHom.id : Fin n →o Fin n) x = x

augMap_comp (K : SSet.{u}) {l m n : ℕ}
  (α : Fin m →o Fin n) (β : Fin l →o Fin m) (x : augObj K n) :
  augMap K (α.comp β) x = augMap K β (augMap K α x)

Simplex (K L : SSet.{u}) (n : ℕ) : Type u

pullCut {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : ℕ

pullCut_le {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) : pullCut α ℓ ≤ m

lt_pullCut_iff {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) (i : Fin m) :
  i.val < pullCut α ℓ ↔ (α i).val < ℓ

cut_ext {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
  (h : ∀ i : Fin n, i.val < a ↔ i.val < b) : a = b

pullCut_id {n : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ n) :
  pullCut (OrderHom.id : Fin n →o Fin n) ℓ = ℓ

pullCut_comp {l m n : ℕ} (α : Fin m →o Fin n) (β : Fin l →o Fin m) (ℓ : ℕ) :
  pullCut (α.comp β) ℓ = pullCut β (pullCut α ℓ)

leftMap {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) :
  Fin (pullCut α ℓ) →o Fin ℓ

rightMap {m n : ℕ} (α : Fin m →o Fin n) (ℓ : ℕ) :
  Fin (m - pullCut α ℓ) →o Fin (n - ℓ)

simplexMap (K L : SSet.{u}) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
  Simplex K L n → Simplex K L m
```

仮定は任意の単体集合と有限順序集合の単調写像のみ。
`augObj K 0 = PUnit`、`augObj K (r+1) = K _⦋r⦌`。
`Simplex K L n = Σ ℓ : Fin (n+2), augObj K ℓ.val × augObj L (n+1-ℓ.val)`。
切断の逆像が先頭区間になることを上下からの濃度比較で証明した。
`simplexMap` は左右の制限から定義済みだが、その恒等・合成則は未証明。
したがって `join : SSet → SSet → SSet`、包含、標準単体の同型、空 join の同型、
join の射への関手性は未構成。slice も設計のみで未実装。
A2a〜A2i のいずれも完了とは数えない。

前段階の対象 `lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 30 明示的公開宣言を監査し、全て `propext`・`Classical.choice`・`Quot.sound` のみ。
原典：HTT §1.2.8、Kerodon §4.3.5。追加公理・引用・`sorry` はない。

前段階を集約した全体 `set -o pipefail; lake build` も終了コード 0（7349 jobs）。


### A2a 途中②（2026-10-17）：join の関手法則・包含・部分複体

**A2a はまだ未完了。** 承認された直接構成を維持し、追加された三要件を
Core/README.md に記録した。今回、切断と左右の cast を扱う ext 補題を先に用意し、
その後に単体作用の恒等・合成則と `join : SSet → SSet → SSet` を構成した。
`joinMap` の関手性・単射性、左右の包含とその自然性、部分複体の join とその和、
部分複体の像との同型、空 join の同型を実装した。

以下は今回追加した全 36 明示的公開宣言の正確な型。宇宙 `u` は任意、
`open CategoryTheory SSet` と `open scoped Simplicial` の下で記す。
`[Mono f]` のある宣言以外には単射の前提を置かず、quasicategory の仮定も不要。
namespace：`SerrePositivity.InfinityCategories.Join`。

```lean
augHom {K L : SSet.{u}} (f : K ⟶ L) : (n : ℕ) → augObj K n → augObj L n

augHom_naturality {K L : SSet.{u}} (f : K ⟶ L) {m n : ℕ}
    (α : Fin m →o Fin n) (x : augObj K n) :
    augHom f m (augMap K α x) = augMap L α (augHom f n x)

augHom_id (K : SSet.{u}) (n : ℕ) (x : augObj K n) : augHom (𝟙 K) n x = x

augHom_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) (x : augObj K n) :
    augHom (f ≫ g) n x = augHom g n (augHom f n x)

augHom_injective {K L : SSet.{u}} (f : K ⟶ L) [Mono f] (n : ℕ) :
    Function.Injective (augHom f n)

stdAugEquiv (n r : ℕ) : augObj (Δ[n] : SSet.{u}) r ≃ (Fin r →o Fin (n + 1))

concat {p q r : ℕ} (ℓ : ℕ) (_hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) : Fin r →o Fin (p + q)

concat_lt_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) :
    (concat ℓ hℓ f g i).val < p ↔ i.val < ℓ

Simplex.ext {K L : SSet.{u}} {n : ℕ} (s t : Simplex K L n)
    (hcut : s.1 = t.1)
    (hleft : cast (congrArg (fun ℓ : Fin (n + 2) ↦ augObj K ℓ.val) hcut) s.2.1 = t.2.1)
    (hright : cast (congrArg (fun ℓ : Fin (n + 2) ↦ augObj L (n + 1 - ℓ.val)) hcut)
      s.2.2 = t.2.2) : s = t

augMap_congr (K : SSet.{u}) {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (α : Fin m →o Fin n) (β : Fin m' →o Fin n')
    (hα : ∀ (i : Fin m) (j : Fin m'), i.val = j.val → (α i).val = (β j).val)
    (x : augObj K n) (x' : augObj K n')
    (hx : cast (congrArg (augObj K) hn) x = x') :
    cast (congrArg (augObj K) hm) (augMap K α x) = augMap K β x'

pullCut_zero {m n : ℕ} (α : Fin m →o Fin n) : pullCut α 0 = 0

pullCut_all {m n : ℕ} (α : Fin m →o Fin n) : pullCut α n = m

pullCut_concat {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) :
    pullCut (concat ℓ hℓ f g) p = ℓ

simplexMap_id (K L : SSet.{u}) (n : ℕ) (s : Simplex K L n) :
    simplexMap K L OrderHom.id s = s

simplexMap_comp (K L : SSet.{u}) {l m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (l + 1) →o Fin (m + 1))
    (s : Simplex K L n) :
    simplexMap K L (α.comp β) s = simplexMap K L β (simplexMap K L α s)

Simplex.inl {K L : SSet.{u}} {n : ℕ} (x : K _⦋n⦌) : Simplex K L n

Simplex.inr {K L : SSet.{u}} {n : ℕ} (y : L _⦋n⦌) : Simplex K L n

simplexMap_inl (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (x : K _⦋n⦌) :
    simplexMap K L α (Simplex.inl x) = Simplex.inl (augMap K α x)

simplexMap_inr (K L : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (y : L _⦋n⦌) :
    simplexMap K L α (Simplex.inr y) = Simplex.inr (augMap L α y)

```

namespace：`SerrePositivity.InfinityCategories`。

```lean
join (K L : SSet.{u}) : SSet.{u}

joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    join K L ⟶ join K' L'

joinMap_id (K L : SSet.{u}) : joinMap (𝟙 K) (𝟙 L) = 𝟙 (join K L)

joinMap_comp {K K' K'' L L' L'' : SSet.{u}}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    joinMap (f ≫ f') (g ≫ g') = joinMap f g ≫ joinMap f' g'

joinMap_mono {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') [Mono f] [Mono g] :
    Mono (joinMap f g)

joinInl (K L : SSet.{u}) : K ⟶ join K L

joinInr (K L : SSet.{u}) : L ⟶ join K L

joinInl_joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    joinInl K L ≫ joinMap f g = f ≫ joinInl K' L'

joinInr_joinMap {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    joinInr K L ≫ joinMap f g = g ≫ joinInr K' L'

joinSubcomplexLeft {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    (join A B).Subcomplex

joinSubcomplexRight (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    (join A B).Subcomplex

joinUnion {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    (join A B).Subcomplex

joinSubcomplexLeftIso {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    join (A₀ : SSet.{u}) B ≅ (joinSubcomplexLeft A₀ B : SSet.{u})

joinSubcomplexRightIso (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    join A (B₀ : SSet.{u}) ≅ (joinSubcomplexRight A B₀ : SSet.{u})

joinSubcomplexLeftIso_hom_ι {A : SSet.{u}} (A₀ : A.Subcomplex) (B : SSet.{u}) :
    (joinSubcomplexLeftIso A₀ B).hom ≫ (joinSubcomplexLeft A₀ B).ι =
      joinMap A₀.ι (𝟙 B)

joinSubcomplexRightIso_hom_ι (A : SSet.{u}) {B : SSet.{u}} (B₀ : B.Subcomplex) :
    (joinSubcomplexRightIso A B₀).hom ≫ (joinSubcomplexRight A B₀).ι =
      joinMap (𝟙 A) B₀.ι

emptyJoinIso (A L : SSet.{u}) :
    join ((⊥ : A.Subcomplex) : SSet.{u}) L ≅ L

```

`@[reassoc]` が生成する以下の公開宣言 2 件も監査した。

```lean
joinInl_joinMap_assoc {K K' L L' Z : SSet.{u}}
  (f : K ⟶ K') (g : L ⟶ L') (h : join K' L' ⟶ Z) :
  joinInl K L ≫ joinMap f g ≫ h = f ≫ joinInl K' L' ≫ h

joinInr_joinMap_assoc {K K' L L' Z : SSet.{u}}
  (f : K ⟶ K') (g : L ⟶ L') (h : join K' L' ⟶ Z) :
  joinInr K L ≫ joinMap f g ≫ h = g ≫ joinInr K' L' ≫ h
```

`emptyJoinIso A L` は任意の A の空部分複体を空の単体集合の模型に取る。
これは条件付きの空性の仮定を課さない実際の同型である。
`stdAugEquiv`・`concat`・`concat_lt_iff`・`pullCut_concat` は
標準単体の join の同型に向けた有限順序集合の計算であり、同型自体の完成ではない。

対象 `lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 66 明示的公開宣言と生成補題 2 件、計 68 件は標準三公理のみ。
原典：HTT §1.2.8・2.1.2.3、Kerodon §4.3.5–4.3.6。

未完了：`Δ[i] ⋆ Δ[j] ≅ Δ[i+j+1]`。したがって A2a は未完了。
A2b の slice・coslice・射影・直接構成による普遍性も未実装で、A2c 以降には進んでいない。
A2c・A2h の正確な anodyne の文言は、実装前に照合して README に記録・報告する。

全体ビルドの結果：`set -o pipefail; lake build` は終了コード 1。
Core の対象ビルドと公理監査は成功したが、編集禁止の並行作業範囲
`SerrePositivity/InfinityCategories/Derived/SemifreeClosure.lean` が失敗した。
202 行・230 行に `Unknown identifier Limits.Limits.Sigma.map`、
219 行に書き換えの失敗、230 行・233 行に heartbeat 超過、
255 行に `Unknown identifier coproductFiltrationIsColimit` が報告された。
このファイルは変更せず、依存先破損時は止める指示に従い以降の実装を停止した。
回避策・依存先の差し替えは作っていない。全体ビルドの成功は主張しない。


### A2a 完了（2026-10-17）：標準単体の join の同型

ユーザー指示で停止基準を明確化した。停止するのは Core 自身の import 閉包内の
並行作業による破損のみ。各保存単位の検証は対象ビルドと公理監査で足り、
他レーンの編集中ファイルによる全体ビルド失敗は記録だけにする。
Derived は Core の import 閉包外なので前回の失敗を理由にした停止を解除した。
§4 の設計は変更していない。

標準単体の join の各次数を順序写像の連結と分解で同一視し、
その対応の単体作用との可換性を証明して `joinStdSimplexIso` を構成した。
追加の 12 公開宣言の正確な型を以下に記す。宇宙 `u` は任意、
`open CategoryTheory SSet`、`open scoped Simplicial` の下での型。
quasicategory 性・単射性などの追加前提はない。

namespace：`SerrePositivity.InfinityCategories.Join`。

```lean
stdAugEquiv_augMap (n : ℕ) {r s : ℕ} (α : Fin r →o Fin s)
    (x : augObj (Δ[n] : SSet.{u}) s) (i : Fin r) :
    stdAugEquiv n r (augMap Δ[n] α x) i = stdAugEquiv n s x (α i)

concat_of_lt {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) (hi : i.val < ℓ) :
    (concat ℓ hℓ f g i).val = (f ⟨i.val, hi⟩).val

concat_of_ge {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (i : Fin r) (hi : ℓ ≤ i.val) :
    (concat ℓ hℓ f g i).val = p + (g ⟨i.val - ℓ, by have

stdEncode (i j n : ℕ) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    Fin (n + 1) →o Fin ((i + 1) + (j + 1))

pullCut_stdEncode (i j n : ℕ) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    pullCut (stdEncode i j n s) (i + 1) = s.1.val

stdEncode_injective (i j n : ℕ) : Function.Injective (stdEncode.{u} i j n)

stdDecode (i j n : ℕ) (α : Fin (n + 1) →o Fin ((i + 1) + (j + 1))) :
    Simplex (Δ[i] : SSet.{u}) Δ[j] n

stdEncode_stdDecode (i j n : ℕ)
    (α : Fin (n + 1) →o Fin ((i + 1) + (j + 1))) :
    stdEncode i j n (stdDecode.{u} i j n α) = α

stdSimplexEquiv (i j n : ℕ) : Simplex (Δ[i] : SSet.{u}) Δ[j] n ≃
    (Fin (n + 1) →o Fin ((i + 1) + (j + 1)))

stdEncode_naturality (i j : ℕ) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Simplex (Δ[i] : SSet.{u}) Δ[j] n) :
    stdEncode i j m (simplexMap Δ[i] Δ[j] α s) = (stdEncode i j n s).comp α

stdSimplexTargetEquiv (i j n : ℕ) :
    (Fin (n + 1) →o Fin ((i + 1) + (j + 1))) ≃ (Δ[i + j + 1] : SSet.{u}) _⦋n⦌

```

namespace：`SerrePositivity.InfinityCategories`。

```lean
joinStdSimplexIso (i j : ℕ) :
    join (Δ[i] : SSet.{u}) Δ[j] ≅ Δ[i + j + 1]

```

A2a の全要求を実装した：直接構成の `join`、`joinInl`・`joinInr`、
`joinMap` とその恒等・合成則、`joinStdSimplexIso`、`emptyJoinIso`、
部分複体の `joinSubcomplexLeft`・`joinSubcomplexRight` とその像との同型、
および和 `joinUnion`。切断と両因子の cast を扱う `Join.Simplex.ext` を
単体作用の合成則の証明に先立って用意した。
原典：HTT §1.2.8、Kerodon §4.3.5。

未完了：A2b の slice・coslice・射影・任意の単体集合に対する直接構成の普遍性、
および A2c 以降。A2a の完成をそれらの完成とは数えない。

`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 80 公開宣言（明示的 78、生成補題 2）の監査出力を照合し、標準三公理のみ。
追加公理・引用・`sorry` はない。


### A2b 途中①（2026-10-17）：slice・coslice と slice 側の普遍性

承認された部分型表示の `sliceOver` と `sliceUnder`、左右の射影、
頂点上の特殊化、join からの射を各単体上に制限する curry を構成した。
さらに slice 側では各単体 a の錐を `(ℓ,id,k)` で評価して束ねる直接構成を行い、
自然性、固定条件、制限との両逆関係を証明して `sliceOverEquiv` を構成した。
余極限の一般論は使わない。§4 の設計変更はない。

追加した全 22 公開宣言の正確な型を以下に記す。宇宙 `u` は任意、
`open CategoryTheory SSet` と `open scoped Simplicial` の下での型。
単体集合・射・単体の指定以外に、quasicategory 性・単射性等の追加前提はない。

namespace：`SerrePositivity.InfinityCategories.Join`。

```lean
leftMapAt {m n : ℕ} (α : Fin m →o Fin n) (ℓ c : ℕ) (hc : pullCut α ℓ = c) :
    Fin c →o Fin ℓ

rightMapAt {m n : ℕ} (α : Fin m →o Fin n) (ℓ c : ℕ) (hc : pullCut α ℓ = c) :
    Fin (m - c) →o Fin (n - ℓ)

simplexMap_eq_at (A K : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (ℓ : Fin (n + 2))
    (c : ℕ) (hc : pullCut α ℓ.val = c) (a : augObj A ℓ.val) (k : augObj K (n + 1 - ℓ.val)) :
    simplexMap A K α ⟨ℓ, a, k⟩ =
      ⟨⟨c, by have

```

namespace：`SerrePositivity.InfinityCategories`。

```lean
sliceOver {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u}

sliceUnder {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u}

sliceOverProjection {K X : SSet.{u}} (p : K ⟶ X) : sliceOver p ⟶ X

sliceUnderProjection {K X : SSet.{u}} (p : K ⟶ X) : sliceUnder p ⟶ X

sliceOverVertex {X : SSet.{u}} (x : X _⦋0⦌) : SSet.{u}

sliceUnderVertex {X : SSet.{u}} (x : X _⦋0⦌) : SSet.{u}

sliceOverCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) : A ⟶ sliceOver p

sliceUnderCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) : A ⟶ sliceUnder p

sliceOverUncurryApp {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) (n : ℕ) :
    (join A K) _⦋n⦌ → X _⦋n⦌

sliceOverUncurryApp_inr {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) (n : ℕ) (k : K _⦋n⦌) :
    sliceOverUncurryApp f n ((joinInr A K).app _ k) = p.app _ k

sliceOverUncurryApp_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) (n : ℕ) (s : (join A K) _⦋n⦌) :
    sliceOverUncurryApp (sliceOverCurry F hF) n s = F.app _ s

sliceOverGenerator (K : SSet.{u}) (n r : ℕ) (hr : r + 1 ≤ n + 1)
    (k : Join.augObj K (n + 1 - (r + 1))) : Join.Simplex (Δ[r] : SSet.{u}) K n

sliceOverGenerator_map_zero (K : SSet.{u}) {m n r : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hr : r + 1 ≤ n + 1)
    (hc : Join.pullCut α (r + 1) = 0) (k : Join.augObj K (n + 1 - (r + 1))) :
    Join.simplexMap Δ[r] K α (sliceOverGenerator K n r hr k) =
      (joinInr Δ[r] K).app _ (Join.augMap K (Join.rightMapAt α (r + 1) 0 hc) k)

sliceOverGenerator_map_succ (K : SSet.{u}) {m n r c : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hr : r + 1 ≤ n + 1)
    (hc : Join.pullCut α (r + 1) = c + 1) (k : Join.augObj K (n + 1 - (r + 1))) :
    Join.simplexMap Δ[r] K α (sliceOverGenerator K n r hr k) =
      (joinMap (stdSimplex.map (SimplexCategory.mkHom (Join.leftMapAt α (r + 1) (c + 1) hc)))
        (𝟙 K)).app (Opposite.op ⦋m⦌)
        (sliceOverGenerator K m c (by have

sliceOverUncurryApp_naturality {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (s : (join A K) _⦋n⦌) :
    sliceOverUncurryApp f m (Join.simplexMap A K α s) =
      X.map (SimplexCategory.mkHom α).op (sliceOverUncurryApp f n s)

sliceOverUncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) : join A K ⟶ X

sliceOverUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    joinInr A K ≫ sliceOverUncurry f = p

sliceOverUncurryApp_yoneda {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) {n d : ℕ} (a : A _⦋n⦌) (s : (join Δ[n] K) _⦋d⦌) :
    sliceOverUncurryApp f d ((joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)).app _ s) =
      (f.app _ a).val.app _ s

sliceOverEquiv {A K X : SSet.{u}} (p : K ⟶ X) :
    (A ⟶ sliceOver p) ≃ {F : join A K ⟶ X // joinInr A K ≫ F = p}

```

原典：HTT §1.2.8・2.1.2、Kerodon §4.3.5。
**A2b は未完了。** coslice 側の curry はあるが、直接束ねる逆写像と
`(A ⟶ sliceUnder p) ≃ {F : join K A ⟶ X // joinInl K A ≫ F = p}` は未構成。
この双対の普遍性を残して A2b の完成とは数えない。A2c 以降にも未着手。

`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 102 公開宣言（明示的 100、生成補題 2）の公理監査を照合し、標準三公理のみ。
追加公理・引用・`sorry` はない。全体ビルドは新しい指示どおりこの保存単位では行わない。


### A2b 完了（2026-10-17）：coslice 側の直接構成による普遍性

`Core/Coslice.lean` に coslice 側の普遍性を直接構成した。左右の頂点数の和で
既存の join の単体を表示し、右単体 a に付いた錐を `(k,id)` で評価して束ねる。
引き戻しの自然性と固定条件を証明し、Yoneda 射による制限との両逆関係を示した。
join・slice の定義や §4 の設計は変えていない。余極限の一般論も用いていない。

追加した全 20 公開宣言の正確な型。宇宙 `u` は任意、
`open CategoryTheory SSet`、`open scoped Simplicial` の下で記す。
単体集合・射・単体と、左右の頂点数や切断を指定する算術等式のみを前提とし、
quasicategory 性・単射性は仮定しない。

namespace：`SerrePositivity.InfinityCategories.Join`。

```lean
mkOfSum {K L : SSet.{u}} {n l r : ℕ} (h : l + r = n + 1)
    (a : augObj K l) (b : augObj L r) : Simplex K L n

rightMapOfSum {m n l r c d : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hn : l + r = n + 1) (hm : c + d = m + 1) (hc : pullCut α l = c) : Fin d →o Fin r

simplexMap_mkOfSum (K L : SSet.{u}) {m n l r c d : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hn : l + r = n + 1) (hm : c + d = m + 1)
    (hc : pullCut α l = c) (a : augObj K l) (b : augObj L r) :
    simplexMap K L α (mkOfSum hn a b) =
      mkOfSum hm (augMap K (leftMapAt α l c hc) a) (augMap L (rightMapOfSum α hn hm hc) b)

augHom_cast {K L : SSet.{u}} (f : K ⟶ L) {r s : ℕ} (h : r = s) (a : augObj K r) :
    cast (congrArg (augObj L) h) (augHom f r a) =
      augHom f s (cast (congrArg (augObj K) h) a)

```

namespace：`SerrePositivity.InfinityCategories`。

```lean
joinMap_mkOfSum {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {n l r : ℕ} (h : l + r = n + 1) (a : Join.augObj K l) (b : Join.augObj L r) :
    (joinMap f g).app (Opposite.op ⦋n⦌) (Join.mkOfSum h a b) =
      Join.mkOfSum h (Join.augHom f l a) (Join.augHom g r b)

```

namespace：`SerrePositivity.InfinityCategories.Join`。

```lean
mkOfSum_zero_right {K L : SSet.{u}} {n : ℕ} (h : (n + 1) + 0 = n + 1)
    (k : augObj K (n + 1)) (a : augObj L 0) : mkOfSum h k a = Simplex.inl k

mkOfSum_eta {K L : SSet.{u}} {n : ℕ} (s : Simplex K L n) :
    mkOfSum (by have

```

namespace：`SerrePositivity.InfinityCategories`。

```lean
sliceUnderEval {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) (n l : ℕ) :
    (r : ℕ) → (h : l + r = n + 1) → Join.augObj K l → Join.augObj A r → X _⦋n⦌

sliceUnderEval_castRight {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p)
    {n l r r' : ℕ} (he : r = r') (h : l + r = n + 1) (h' : l + r' = n + 1)
    (k : Join.augObj K l) (a : Join.augObj A r) :
    sliceUnderEval f n l r h k a =
      sliceUnderEval f n l r' h' k (cast (congrArg (Join.augObj A) he) a)

sliceUnderUncurryApp {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) (n : ℕ)
    (s : Join.Simplex K A n) : X _⦋n⦌

sliceUnderUncurryApp_mkOfSum {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) {n l r : ℕ} (h : l + r = n + 1)
    (k : Join.augObj K l) (a : Join.augObj A r) :
    sliceUnderUncurryApp f n (Join.mkOfSum h k a) = sliceUnderEval f n l r h k a

sliceUnderGenerator_map_succ (K : SSet.{u}) {m n l r c d : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hn : l + (r + 1) = n + 1)
    (hm : c + (d + 1) = m + 1) (hc : Join.pullCut α l = c) (k : Join.augObj K l) :
    Join.simplexMap K Δ[r] α (Join.mkOfSum hn k (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌))) =
      (joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.mkHom
        (Join.rightMapOfSum α hn hm hc)))).app (Opposite.op ⦋m⦌)
        (Join.mkOfSum hm (Join.augMap K (Join.leftMapAt α l c hc) k)
          (stdSimplex.objEquiv.symm (𝟙 ⦋d⦌)))

sliceUnderEval_naturality {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p)
    {m n l r c d : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hn : l + r = n + 1) (hm : c + d = m + 1) (hc : Join.pullCut α l = c)
    (k : Join.augObj K l) (a : Join.augObj A r) :
    sliceUnderEval f m c d hm (Join.augMap K (Join.leftMapAt α l c hc) k)
        (Join.augMap A (Join.rightMapOfSum α hn hm hc) a) =
      X.map (SimplexCategory.mkHom α).op (sliceUnderEval f n l r hn k a)

sliceUnderUncurryApp_naturality {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (s : Join.Simplex K A n) :
    sliceUnderUncurryApp f m (Join.simplexMap K A α s) =
      X.map (SimplexCategory.mkHom α).op (sliceUnderUncurryApp f n s)

sliceUnderUncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) : join K A ⟶ X

sliceUnderUncurryApp_inl {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) (n : ℕ) (k : K _⦋n⦌) :
    sliceUnderUncurryApp f n ((joinInl K A).app _ k) = p.app _ k

sliceUnderUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) :
    joinInl K A ≫ sliceUnderUncurry f = p

sliceUnderEval_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) {n l r : ℕ}
    (h : l + r = n + 1) (k : Join.augObj K l) (a : Join.augObj A r) :
    sliceUnderEval (sliceUnderCurry F hF) n l r h k a = F.app _ (Join.mkOfSum h k a)

sliceUnderEval_yoneda {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) {n d l r : ℕ} (a : A _⦋n⦌) (h : l + r = d + 1)
    (k : Join.augObj K l) (b : Join.augObj (Δ[n] : SSet.{u}) r) :
    sliceUnderEval f d l r h k (Join.augHom (SSet.yonedaEquiv.symm a) r b) =
      (f.app _ a).val.app (Opposite.op ⦋d⦌) (Join.mkOfSum h k b)

sliceUnderEquiv {A K X : SSet.{u}} (p : K ⟶ X) :
    (A ⟶ sliceUnder p) ≃ {F : join K A ⟶ X // joinInl K A ≫ F = p}

```

A2b の全要求（slice・coslice・射影・頂点の場合・両側の任意の単体集合に対する
普遍性）を実装した。原典：HTT §1.2.8・2.1.2、Kerodon §4.3.5。
A2c〜A2i は未完了。A2b の完成から持ち上げ性・極限の理論の完成を主張しない。

`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` は終了コード 0。
累計 122 公開宣言（明示的 120、生成補題 2）の監査出力を照合し、標準三公理のみ。
追加公理・引用・`sorry` はない。

### A2c 生成セル（2026-10-17、A2c 全体は未完了）

README に HTT Lemma 2.1.2.3・Kerodon Proposition 4.3.6.4 の正確な向きを実装前に記録した。
左の right anodyne、または右の left anodyne が仮定である。追加承認は不要というユーザー指示に従った。
`Core/JoinAnodyne.lean` にホーン生成クラスと二つの基本セルを実装した。
宇宙 `u` は任意、`open CategoryTheory SSet MorphismProperty` と `open scoped Simplicial` の下で、
公開宣言の正確な型は以下の通り。各コードブロックの namespace を明示する。

namespace `SerrePositivity.InfinityCategories`：

```lean
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) : rightHornInclusions Λ[n + 1, i].ι
```

namespace `SerrePositivity.InfinityCategories`：

```lean
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
      leftHornInclusions Λ[n + 1, i].ι
```

namespace `SerrePositivity.InfinityCategories`：

```lean
def rightAnodyneExtensions : MorphismProperty SSet.{u}
```

namespace `SerrePositivity.InfinityCategories`：

```lean
def leftAnodyneExtensions : MorphismProperty SSet.{u}
```

namespace `SerrePositivity.InfinityCategories`：

```lean
lemma rightAnodyneExtensions_horn {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
    rightAnodyneExtensions.{u} (horn (n + 1) i).ι
```

namespace `SerrePositivity.InfinityCategories`：

```lean
lemma leftAnodyneExtensions_horn {n : ℕ} (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    leftAnodyneExtensions.{u} (horn (n + 1) i).ι
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
def augMem {K : SSet.{u}} (K₀ : K.Subcomplex) : (r : ℕ) → augObj K r → Prop
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma augMem_iff_exists {K : SSet.{u}} (K₀ : K.Subcomplex) (r : ℕ) (a : augObj K r) :
    augMem K₀ r a ↔ ∃ b : augObj (K₀ : SSet.{u}) r, augHom K₀.ι r b = a
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_joinSubcomplexLeft {A B : SSet.{u}} (A₀ : A.Subcomplex)
    {n : ℕ} (s : Simplex A B n) :
    s ∈ (joinSubcomplexLeft A₀ B).obj (Opposite.op ⦋n⦌) ↔
      augMem A₀ s.1.val s.2.1
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_joinSubcomplexRight {A B : SSet.{u}} (B₀ : B.Subcomplex)
    {n : ℕ} (s : Simplex A B n) :
    s ∈ (joinSubcomplexRight A B₀).obj (Opposite.op ⦋n⦌) ↔
      augMem B₀ (n + 1 - s.1.val) s.2.2
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_joinUnion {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex)
    {n : ℕ} (s : Simplex A B n) :
    s ∈ (joinUnion A₀ B₀).obj (Opposite.op ⦋n⦌) ↔
      augMem A₀ s.1.val s.2.1 ∨ augMem B₀ (n + 1 - s.1.val) s.2.2
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma augMem_boundary_iff (p r : ℕ) (a : augObj (Δ[p] : SSet.{u}) r) :
    augMem (boundary p) r a ↔ ∃ v : Fin (p + 1), v ∉ Set.range (stdAugEquiv p r a)
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma augMem_horn_iff (p r : ℕ) (i : Fin (p + 2))
    (a : augObj (Δ[p + 1] : SSet.{u}) r) :
    augMem (horn (p + 1) i) r a ↔
      ∃ v : Fin (p + 2), v ≠ i ∧ v ∉ Set.range (stdAugEquiv (p + 1) r a)
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_range_concat_left {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (v : Fin p) :
    v.castAdd q ∈ Set.range (concat ℓ hℓ f g) ↔ v ∈ Set.range f
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_range_concat_right {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (v : Fin q) :
    v.natAdd p ∈ Set.range (concat ℓ hℓ f g) ↔ v ∈ Set.range g
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma missing_concat_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) (w : Fin (p + q)) :
    (∃ v : Fin (p + q), v ≠ w ∧ v ∉ Set.range (concat ℓ hℓ f g)) ↔
      (∃ v : Fin p, v.castAdd q ≠ w ∧ v ∉ Set.range f) ∨
      (∃ v : Fin q, v.natAdd p ≠ w ∧ v ∉ Set.range g)
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma missing_cast_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) (w : Fin p) :
    (∃ v : Fin q, v ≠ Fin.cast h w ∧ v ∉ Set.range (fun a ↦ Fin.cast h (f a))) ↔
      ∃ v : Fin p, v ≠ w ∧ v ∉ Set.range f
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma mem_horn_joinStdSimplexIso_iff (p q n : ℕ)
    (s : Simplex (Δ[p] : SSet.{u}) Δ[q] n) (w : Fin ((p + 1) + (q + 1))) :
    (joinStdSimplexIso p q).hom.app (Opposite.op ⦋n⦌) s ∈
      (horn (p + q + 1) (Fin.cast (by omega) w)).obj (Opposite.op ⦋n⦌) ↔
        ∃ v, v ≠ w ∧ v ∉ Set.range (stdEncode p q n s)
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma horn_boundary_preimage (p q : ℕ) (i : Fin (p + 2)) :
    (horn ((p + 1) + q + 1) (Fin.cast (by omega) (i.castAdd (q + 1)))).preimage
      (joinStdSimplexIso.{u} (p + 1) q).hom = joinUnion (horn (p + 1) i) (boundary q)
```

namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma boundary_horn_preimage (p q : ℕ) (j : Fin (q + 2)) :
    (horn (p + (q + 1) + 1) (Fin.cast (by omega) (j.natAdd (p + 1)))).preimage
      (joinStdSimplexIso.{u} p (q + 1)).hom = joinUnion (boundary p) (horn (q + 1) j)
```

namespace `SerrePositivity.InfinityCategories`：

```lean
def subcomplexPreimageIso {X Y : SSet.{u}} (B : Y.Subcomplex) (e : X ≅ Y) :
    (B.preimage e.hom : SSet.{u}) ≅ (B : SSet.{u})
```

namespace `SerrePositivity.InfinityCategories`：

```lean
lemma innerAnodyne_preimage_iff {X Y : SSet.{u}} (B : Y.Subcomplex) (e : X ≅ Y) :
    innerAnodyneExtensions (B.preimage e.hom).ι ↔ innerAnodyneExtensions B.ι
```

namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinUnion_rightHorn_boundary_innerAnodyne (p q : ℕ) (i : Fin (p + 2)) (h0 : 0 < i) :
    innerAnodyneExtensions (joinUnion (horn (p + 1) i) (boundary q)).ι
```

namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinUnion_boundary_leftHorn_innerAnodyne (p q : ℕ) (j : Fin (q + 2))
    (hn : j < Fin.last (q + 1)) :
    innerAnodyneExtensions (joinUnion (boundary p) (horn (q + 1) j)).ι
```

`rightAnodyneExtensions`・`leftAnodyneExtensions` はそれぞれ生成族の `rlp.llp`。
両者に IsMultiplicative・RespectsIso・IsStableUnderCobaseChange・IsStableUnderRetracts・
IsStableUnderTransfiniteComposition・IsStableUnderCoproducts のインスタンスを導出した。
生成セルの前提は左が正次元の右ホーン（0<i）、右が任意次元の境界、またはその左右双対。
標準単体の join の同型の下で和の部分複体が内ホーンに一致することから証明した。
Core の対象ビルド、公理監査とも終了コード 0。新規 24 明示的宣言とホーン生成族の構成子 2 件、
累計 148 件を監査し、標準三公理以外への依存はない（公理なしの宣言もある）。
一般の単射と right/left anodyne 射への閉包、A2d〜A2i は未完了。
従ってこの保存単位を A2c 全体の完成とは数えない。引き続き持ち上げ問題の移送を実装する。

### A2c 完了（2026-10-18）：一般の pushout-join 補題

`JoinCells.lean` は前保存単位の生成セル（宣言名・型は維持）、`SliceMap.lean` は制限と標的の作用、
`JoinLifting.lean` は和の pushout と相対 slice・coslice による持ち上げ問題の往復、
`JoinAnodyne.lean` は主定理を公開する。§4 の設計は維持し、モデル構造は用いない。

主定理は、任意の宇宙 `u`、`A B : SSet.{u}` と部分複体 `A₀`・`B₀` に対し、
**左の包含が right anodyne** または **右の包含が left anodyne** のいずれかだけを仮定する。
反対側の包含には部分複体包含という単射性以上の仮定はない。
生成ホーン・境界の計算を、相対 slice・coslice の持ち上げ問題の同値を通じて広げた。
`SSet.rlp_monomorphisms` の境界によるセル分解を用い、Kan–Quillen や Joyal のモデル構造は使わない。
条件付きの一般化の仮定束ではなく、指定された一般の補題を証明した。

追加公開宣言 44 件の正確な型を以下に列挙する。全て namespace は
`SerrePositivity.InfinityCategories`、宇宙 `u` は任意。
`open CategoryTheory Limits SSet MorphismProperty`、`open scoped Simplicial` とする。

SliceMap.lean
```lean
def sliceUnderRestrict {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    sliceUnder p ⟶ sliceUnder (f ≫ p)
```

SliceMap.lean
```lean
def sliceUnderPostcomp {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) :
    sliceUnder p ⟶ sliceUnder (p ≫ q)
```

SliceMap.lean
```lean
def sliceOverRestrict {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    sliceOver p ⟶ sliceOver (f ≫ p)
```

SliceMap.lean
```lean
def sliceOverPostcomp {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) :
    sliceOver p ⟶ sliceOver (p ≫ q)
```

SliceMap.lean
```lean
lemma sliceUnderRestrict_postcomp {K₀ K X Y : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceUnderPostcomp p q ≫ sliceUnderRestrict (p ≫ q) f =
      sliceUnderRestrict p f ≫ sliceUnderPostcomp (f ≫ p) q
```

SliceMap.lean
```lean
lemma sliceOverRestrict_postcomp {K₀ K X Y : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceOverPostcomp p q ≫ sliceOverRestrict (p ≫ q) f =
      sliceOverRestrict p f ≫ sliceOverPostcomp (f ≫ p) q
```

SliceMap.lean
```lean
lemma sliceUnderCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) :
    sliceUnderCurry (sliceUnderUncurry f) (sliceUnderUncurry_fixed f) = f
```

SliceMap.lean
```lean
lemma sliceUnderUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) :
    sliceUnderUncurry (sliceUnderCurry F hF) = F
```

SliceMap.lean
```lean
lemma sliceUnderCurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) (g : A₀ ⟶ A) :
    g ≫ sliceUnderCurry F hF =
      sliceUnderCurry (joinMap (𝟙 K) g ≫ F)
        (by rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF])
```

SliceMap.lean
```lean
lemma sliceUnderCurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) (f : K₀ ⟶ K) :
    sliceUnderCurry F hF ≫ sliceUnderRestrict p f =
      sliceUnderCurry (joinMap f (𝟙 A) ≫ F)
        (by rw [← Category.assoc, joinInl_joinMap, Category.assoc, hF])
```

SliceMap.lean
```lean
lemma sliceUnderCurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) (q : X ⟶ Y) :
    sliceUnderCurry F hF ≫ sliceUnderPostcomp p q =
      sliceUnderCurry (F ≫ q) (by rw [← Category.assoc, hF])
```

SliceMap.lean
```lean
lemma sliceUnderUncurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) (g : A₀ ⟶ A) :
    sliceUnderUncurry (g ≫ f) = joinMap (𝟙 K) g ≫ sliceUnderUncurry f
```

SliceMap.lean
```lean
lemma sliceUnderUncurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) (g : K₀ ⟶ K) :
    sliceUnderUncurry (f ≫ sliceUnderRestrict p g) = joinMap g (𝟙 A) ≫ sliceUnderUncurry f
```

SliceMap.lean
```lean
lemma sliceUnderUncurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceUnder p) (q : X ⟶ Y) :
    sliceUnderUncurry (f ≫ sliceUnderPostcomp p q) = sliceUnderUncurry f ≫ q
```

SliceMap.lean
```lean
lemma sliceOverCurry_uncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    sliceOverCurry (sliceOverUncurry f) (sliceOverUncurry_fixed f) = f
```

SliceMap.lean
```lean
lemma sliceOverUncurry_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) :
    sliceOverUncurry (sliceOverCurry F hF) = F
```

SliceMap.lean
```lean
lemma sliceOverCurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) (g : A₀ ⟶ A) :
    g ≫ sliceOverCurry F hF =
      sliceOverCurry (joinMap g (𝟙 K) ≫ F)
        (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF])
```

SliceMap.lean
```lean
lemma sliceOverCurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) (f : K₀ ⟶ K) :
    sliceOverCurry F hF ≫ sliceOverRestrict p f =
      sliceOverCurry (joinMap (𝟙 A) f ≫ F)
        (by rw [← Category.assoc, joinInr_joinMap, Category.assoc, hF])
```

SliceMap.lean
```lean
lemma sliceOverCurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) (q : X ⟶ Y) :
    sliceOverCurry F hF ≫ sliceOverPostcomp p q =
      sliceOverCurry (F ≫ q) (by rw [← Category.assoc, hF])
```

SliceMap.lean
```lean
lemma sliceOverUncurry_precomp {A₀ A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) (g : A₀ ⟶ A) :
    sliceOverUncurry (g ≫ f) = joinMap g (𝟙 K) ≫ sliceOverUncurry f
```

SliceMap.lean
```lean
lemma sliceOverUncurry_restrict {A K₀ K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) (g : K₀ ⟶ K) :
    sliceOverUncurry (f ≫ sliceOverRestrict p g) = joinMap (𝟙 A) g ≫ sliceOverUncurry f
```

SliceMap.lean
```lean
lemma sliceOverUncurry_postcomp {A K X Y : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) (q : X ⟶ Y) :
    sliceOverUncurry (f ≫ sliceOverPostcomp p q) = sliceOverUncurry f ≫ q
```

JoinLifting.lean
```lean
lemma joinMap_range_inf {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    Subfunctor.range (joinMap A₀.ι B₀.ι) =
      joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀
```

JoinLifting.lean
```lean
noncomputable def joinIntersectionIso {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) (B₀ : SSet.{u}) ≅
      ((joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀ :
        (join A B).Subcomplex) : SSet.{u})
```

JoinLifting.lean
```lean
lemma joinIntersectionIso_hom_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    (joinIntersectionIso A₀ B₀).hom ≫
      (joinSubcomplexLeft A₀ B ⊓ joinSubcomplexRight A B₀).ι = joinMap A₀.ι B₀.ι
```

JoinLifting.lean
```lean
def joinUnionLeft {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join (A₀ : SSet.{u}) B ⟶ (joinUnion A₀ B₀ : SSet.{u})
```

JoinLifting.lean
```lean
def joinUnionRight {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    join A (B₀ : SSet.{u}) ⟶ (joinUnion A₀ B₀ : SSet.{u})
```

JoinLifting.lean
```lean
lemma joinUnion_isPushout {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    IsPushout (joinMap (𝟙 (A₀ : SSet.{u})) B₀.ι)
      (joinMap A₀.ι (𝟙 (B₀ : SSet.{u}))) (joinUnionLeft A₀ B₀) (joinUnionRight A₀ B₀)
```

JoinLifting.lean
```lean
lemma joinUnionLeft_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinUnionLeft A₀ B₀ ≫ (joinUnion A₀ B₀).ι = joinMap A₀.ι (𝟙 B)
```

JoinLifting.lean
```lean
lemma joinUnionRight_ι {A B : SSet.{u}} (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) :
    joinUnionRight A₀ B₀ ≫ (joinUnion A₀ B₀).ι = joinMap (𝟙 A) B₀.ι
```

JoinLifting.lean
```lean
lemma sliceUnderUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) :
    Function.Injective (sliceUnderUncurry (A
```

JoinLifting.lean
```lean
noncomputable def relativeSliceUnder {K₀ K X Y : SSet.{u}}
    (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) : SSet.{u}
```

JoinLifting.lean
```lean
noncomputable def relativeSliceUnderMap {K₀ K X Y : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceUnder p ⟶ relativeSliceUnder p f q
```

JoinLifting.lean
```lean
lemma relativeSliceUnderMap_hasLiftingProperty {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : HasLiftingProperty (joinUnion A₀ B₀).ι q) (p : A ⟶ X) :
    HasLiftingProperty B₀.ι (relativeSliceUnderMap p A₀.ι q)
```

JoinLifting.lean
```lean
lemma joinUnion_hasLiftingProperty_of_relativeSliceUnderMap {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : ∀ p : A ⟶ X, HasLiftingProperty B₀.ι (relativeSliceUnderMap p A₀.ι q)) :
    HasLiftingProperty (joinUnion A₀ B₀).ι q
```

JoinLifting.lean
```lean
lemma joinUnion_rightHorn_innerAnodyne {B : SSet.{u}} (B₀ : B.Subcomplex)
    (n : ℕ) (i : Fin (n + 2)) (h0 : 0 < i) :
    innerAnodyneExtensions (joinUnion (horn (n + 1) i) B₀).ι
```

JoinLifting.lean
```lean
lemma sliceOverUncurry_injective {A K X : SSet.{u}} (p : K ⟶ X) :
    Function.Injective (sliceOverUncurry (A
```

JoinLifting.lean
```lean
noncomputable def relativeSliceOver {K₀ K X Y : SSet.{u}}
    (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) : SSet.{u}
```

JoinLifting.lean
```lean
noncomputable def relativeSliceOverMap {K₀ K X Y : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) (q : X ⟶ Y) :
    sliceOver p ⟶ relativeSliceOver p f q
```

JoinLifting.lean
```lean
lemma relativeSliceOverMap_hasLiftingProperty {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : HasLiftingProperty (joinUnion B₀ A₀).ι q) (p : A ⟶ X) :
    HasLiftingProperty B₀.ι (relativeSliceOverMap p A₀.ι q)
```

JoinLifting.lean
```lean
lemma joinUnion_hasLiftingProperty_of_relativeSliceOverMap {A B X Y : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (q : X ⟶ Y)
    (h : ∀ p : A ⟶ X, HasLiftingProperty B₀.ι (relativeSliceOverMap p A₀.ι q)) :
    HasLiftingProperty (joinUnion B₀ A₀).ι q
```

JoinLifting.lean
```lean
lemma joinUnion_leftHorn_innerAnodyne {A : SSet.{u}} (A₀ : A.Subcomplex)
    (n : ℕ) (i : Fin (n + 2)) (hn : i < Fin.last (n + 1)) :
    innerAnodyneExtensions (joinUnion A₀ (horn (n + 1) i)).ι
```

JoinAnodyne.lean
```lean
lemma joinUnion_innerAnodyne_of_rightAnodyne {A B : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (hA : rightAnodyneExtensions A₀.ι) :
    innerAnodyneExtensions (joinUnion A₀ B₀).ι
```

JoinAnodyne.lean
```lean
lemma joinUnion_innerAnodyne_of_leftAnodyne {A B : SSet.{u}}
    (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) (hB : leftAnodyneExtensions B₀.ι) :
    innerAnodyneExtensions (joinUnion A₀ B₀).ι
```

Core の対象ビルドと公理監査はともに終了コード 0。累計 192 件の監査対象は標準三公理のみ
（公理なしも含む）。A2c は完了。A2d〜A2i は未完了。全体ビルドは工程の区切りで実施する。
次は A2d の left/right fibration と slice 射影の right fibration 性へ進む。

### A2d 完了（2026-10-18）：左右のファイブレーションと slice・coslice

`Core/RightFibration.lean` に実装した。左右のホーンの `rlp` がそれぞれ
right/left fibration であり、どちらも inner fibration へ接続する。
任意の `p : K ⟶ X` と `[Quasicategory X]` に対し slice 射影は右ファイブレーション、
coslice 射影は左ファイブレーション。K の有限性等の仮定はない。
各 slice/coslice の quasicategory 性は Mathlib の `quasicategory_of_innerFibration` を使った。
射影の持ち上げは、空部分複体と元の錐を pushout-join で貼り合わせ、A2c で延長した。
モデル構造や追加公理を用いていない。

任意の宇宙 `u`、namespace `SerrePositivity.InfinityCategories`、
`open CategoryTheory Limits SSet MorphismProperty` と `open scoped Simplicial` の下で
全ての明示的公開宣言の正確な型は次の通り。クラスの構成子 `.mk` と射影 `.mem` も監査した。

```lean
def rightFibrations : MorphismProperty SSet.{u}
```

```lean
def leftFibrations : MorphismProperty SSet.{u}
```

```lean
class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : rightFibrations p
```

```lean
class LeftFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : leftFibrations p
```

```lean
instance rightFibration_innerFibration {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    InnerFibration p
```

```lean
instance leftFibration_innerFibration {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] :
    InnerFibration p
```

```lean
noncomputable def joinEmptyIso (A K : SSet.{u}) :
    join A ((⊥ : K.Subcomplex) : SSet.{u}) ≅ A
```

```lean
lemma joinEmptyIso_inv (A K : SSet.{u}) :
    (joinEmptyIso A K).inv = joinInl A ((⊥ : K.Subcomplex) : SSet.{u})
```

```lean
lemma joinEmptyIso_naturality {A B : SSet.{u}} (f : A ⟶ B) (K : SSet.{u}) :
    joinMap f (𝟙 ((⊥ : K.Subcomplex) : SSet.{u})) ≫ (joinEmptyIso B K).hom =
      (joinEmptyIso A K).hom ≫ f
```

```lean
lemma sliceOverCurry_projection {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join A K ⟶ X) (hF : joinInr A K ≫ F = p) :
    sliceOverCurry F hF ≫ sliceOverProjection p = joinInl A K ≫ F
```

```lean
lemma sliceOverUncurry_projection {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    joinInl A K ≫ sliceOverUncurry f = f ≫ sliceOverProjection p
```

```lean
lemma sliceOverProjection_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (hA : rightAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (sliceOverProjection p)
```

```lean
instance sliceOverProjection_rightFibration {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    RightFibration (sliceOverProjection p)
```

```lean
instance sliceOver_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (sliceOver p)
```

```lean
lemma emptyJoinIso_inv (K A : SSet.{u}) :
    (emptyJoinIso K A).inv = joinInr ((⊥ : K.Subcomplex) : SSet.{u}) A
```

```lean
lemma sliceUnderCurry_projection {A K X : SSet.{u}} {p : K ⟶ X}
    (F : join K A ⟶ X) (hF : joinInl K A ≫ F = p) :
    sliceUnderCurry F hF ≫ sliceUnderProjection p = joinInr K A ≫ F
```

```lean
lemma sliceUnderUncurry_projection {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) :
    joinInr K A ≫ sliceUnderUncurry f = f ≫ sliceUnderProjection p
```

```lean
lemma sliceUnderProjection_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (hA : leftAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (sliceUnderProjection p)
```

```lean
instance sliceUnderProjection_leftFibration {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    LeftFibration (sliceUnderProjection p)
```

```lean
instance sliceUnder_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (sliceUnder p)
```

Core の対象ビルド・公理監査は終了コード 0。累計 216 件が標準三公理のみ
（公理なしも含む）。A2d は完了。A2e〜A2i は未完了。引き続き終対象の充填条件へ進む。

### A2e 完了（2026-10-18）：終対象・始対象と trivial Kan fibration

`Terminal.lean` の `IsTerminalVertex` は、n≥1 の境界の最後の頂点が x であるとき
境界全体が延長できる条件（HTT Definition 1.2.12.3）。`IsInitialVertex` は最初の頂点を固定する双対。
`boundaryVertex` は実際の標準単体の指定頂点から境界への包含であり、
`boundaryVertex_ι` がその意味を明示する。条件の差し替えや未証明の仮定束は使っていない。

`trivialKanFibrations := (monomorphisms SSet).rlp` と型クラス `TrivialKanFibration` を定義した。
全境界包含の rlp との同値は単射の境界セル分解を使う。モデル構造は使わない。
`isTerminalVertex_iff_trivialKanFibration` と `isInitialVertex_iff_trivialKanFibration` は
任意の単体集合 X に対し、それぞれ slice/coslice 射影の trivial Kan fibration 性との同値を与える。
この同値には quasicategory の仮定は不要。

`TerminalUniqueness.lean` と `InitialUniqueness.lean` では、射影の持ち上げ性から辺と片側逆射を作った。
二回の片側逆射の二単体を用いて、`[Quasicategory X]` の下で `terminalVertexIso`・`initialVertexIso` が
Mathlib のホモトピー圏 `hoFunctor.obj X` での同型を与える。
`JoinBoundary.lean`・`SliceExtension.lean` は、境界の join の同型と持ち上げ問題の往復の補助。

追加公開宣言 53 件と型クラスの構成子・射影 2 件、計 55 件の正確な型を以下に記録する。
宇宙 `u` は任意。namespace は各コードブロックに示す。
`open CategoryTheory Limits SSet MorphismProperty SSet.Truncated SimplicialObject.Truncated`、
`open scoped Simplicial` の下の型であり、`Edge` は `SSet.Truncated.Edge` を指す。

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma missing_concat_boundary_iff {p q r : ℕ} (ℓ : ℕ) (hℓ : ℓ ≤ r)
    (f : Fin ℓ →o Fin p) (g : Fin (r - ℓ) →o Fin q) :
    (∃ v : Fin (p + q), v ∉ Set.range (concat ℓ hℓ f g)) ↔
      (∃ v : Fin p, v ∉ Set.range f) ∨ (∃ v : Fin q, v ∉ Set.range g)
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma missing_cast_boundary_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) :
    (∃ v : Fin q, v ∉ Set.range (fun a ↦ Fin.cast h (f a))) ↔
      ∃ v : Fin p, v ∉ Set.range f
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories.Join`：

```lean
lemma boundary_boundary_preimage (p q : ℕ) :
    (boundary (p + q + 1)).preimage (joinStdSimplexIso.{u} p q).hom =
      joinUnion (boundary p) (boundary q)
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def boundaryJoinIso (p q : ℕ) :
    (joinUnion (boundary p) (boundary q) : SSet.{u}) ≅ (boundary (p + q + 1) : SSet.{u})
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma boundaryJoinIso_hom_ι (p q : ℕ) :
    (boundaryJoinIso p q).hom ≫ (boundary (p + q + 1)).ι =
      (joinUnion (boundary p) (boundary q)).ι ≫ (joinStdSimplexIso.{u} p q).hom
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_inr_vertex (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)))
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma vertex_mem_boundary (n : ℕ) (i : Fin (n + 2)) :
    stdSimplex.obj₀Equiv.symm i ∈ (boundary.{u} (n + 1)).obj (Opposite.op ⦋0⦌)
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def boundaryVertex (n : ℕ) (i : Fin (n + 2)) : (Δ[0] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u})
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma boundaryVertex_ι (n : ℕ) (i : Fin (n + 2)) :
    boundaryVertex n i ≫ (boundary (n + 1)).ι =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i)
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma boundaryJoinIso_inr_vertex (n : ℕ) :
    joinInr (boundary n : SSet.{u}) Δ[0] ≫ joinUnionLeft (boundary n) (boundary 0) ≫
      (boundaryJoinIso n 0).hom = boundaryVertex n (Fin.last (n + 1))
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_inl_vertex (n : ℕ) :
    joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (joinStdSimplexIso 0 n).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (0 + n + 1 + 1)))
```

JoinBoundary.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma boundaryJoinIso_inl_vertex (n : ℕ) :
    joinInl (Δ[0] : SSet.{u}) (boundary n : SSet.{u}) ≫
      joinUnionRight (boundary 0) (boundary n) ≫ (boundaryJoinIso 0 n).hom =
        boundaryVertex (0 + n) 0
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def SliceOverExtensionProperty {A K X : SSet.{u}} (A₀ : A.Subcomplex) (p : K ⟶ X) : Prop
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceOverExtensionProperty_of_lifting {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : HasLiftingProperty A₀.ι (sliceOverProjection p)) :
    SliceOverExtensionProperty A₀ p
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceOverProjection_lifting_of_extension {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : SliceOverExtensionProperty A₀ p) :
    HasLiftingProperty A₀.ι (sliceOverProjection p)
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def SliceUnderExtensionProperty {A K X : SSet.{u}} (A₀ : A.Subcomplex) (p : K ⟶ X) : Prop
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceUnderExtensionProperty_of_lifting {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : HasLiftingProperty A₀.ι (sliceUnderProjection p)) :
    SliceUnderExtensionProperty A₀ p
```

SliceExtension.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceUnderProjection_lifting_of_extension {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : SliceUnderExtensionProperty A₀ p) :
    HasLiftingProperty A₀.ι (sliceUnderProjection p)
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def trivialKanFibrations : MorphismProperty SSet.{u}
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
class TrivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : trivialKanFibrations p
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma trivialKanFibration_iff_boundary {X Y : SSet.{u}} (p : X ⟶ Y) :
    TrivialKanFibration p ↔ ∀ n : ℕ, HasLiftingProperty (boundary n).ι p
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
instance trivialKanFibration_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : RightFibration p
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
instance trivialKanFibration_leftFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : LeftFibration p
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def IsTerminalVertex {X : SSet.{u}} (x : X _⦋0⦌) : Prop
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma isTerminalVertex_iff_sliceOverExtension {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ ∀ n : ℕ,
      SliceOverExtensionProperty (boundary n) (SSet.yonedaEquiv.symm x)
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma isTerminalVertex_iff_trivialKanFibration {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ TrivialKanFibration (sliceOverProjection (SSet.yonedaEquiv.symm x))
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def IsInitialVertex {X : SSet.{u}} (x : X _⦋0⦌) : Prop
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma isInitialVertex_iff_sliceUnderExtension {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔ ∀ n : ℕ,
      SliceUnderExtensionProperty (boundary n) (SSet.yonedaEquiv.symm x)
```

Terminal.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma isInitialVertex_iff_trivialKanFibration {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔ TrivialKanFibration (sliceUnderProjection (SSet.yonedaEquiv.symm x))
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_zero_inl :
    joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom = stdSimplex.δ 1
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_zero_inr :
    joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).hom = stdSimplex.δ 0
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_one_inl :
    joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 1 0).hom = stdSimplex.δ 2
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_one_vertex (i : Fin 2) :
    joinMap (stdSimplex.δ i) (𝟙 (Δ[0] : SSet.{u})) ≫ (joinStdSimplexIso 1 0).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ i.castSucc
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def sliceOverVertexEdge {X : SSet.{u}} (x : X _⦋0⦌)
    (σ : (sliceOver (SSet.yonedaEquiv.symm x)) _⦋0⦌) :
    Edge (X
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma IsTerminalVertex.nonempty_edge {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (y : X _⦋0⦌) :
    Nonempty (Edge (X
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceOverCurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (sliceOver p) _⦋n⦌) :
    sliceOverCurry σ.val σ.property = SSet.yonedaEquiv.symm σ
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceOverUncurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (sliceOver p) _⦋n⦌) :
    sliceOverUncurry (SSet.yonedaEquiv.symm σ) = σ.val
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def sliceIdentityCone {X : SSet.{u}} (x : X _⦋0⦌) :
    (sliceOver (SSet.yonedaEquiv.symm x)) _⦋0⦌
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceIdentityCone_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (sliceIdentityCone x) = x
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma IsTerminalVertex.nonempty_split {X : SSet.{u}} {x y : X _⦋0⦌}
    (hx : IsTerminalVertex x) (f : Edge (X
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
noncomputable def terminalVertexIso₂ {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : IsTerminalVertex x) (hy : IsTerminalVertex y) :
    HomotopyCategory₂.mk (A
```

TerminalUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
noncomputable def terminalVertexIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : IsTerminalVertex x) (hy : IsTerminalVertex y) :
    (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk y
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_one_inr :
    joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom = stdSimplex.δ 0
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma joinStdSimplexIso_vertex_one (i : Fin 2) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) ≫ (joinStdSimplexIso 0 1).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ i.succ
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def sliceUnderVertexEdge {X : SSet.{u}} (x : X _⦋0⦌)
    (σ : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌) :
    Edge (X
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma IsInitialVertex.nonempty_edge {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsInitialVertex x) (y : X _⦋0⦌) :
    Nonempty (Edge (X
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceUnderCurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (sliceUnder p) _⦋n⦌) :
    sliceUnderCurry σ.val σ.property = SSet.yonedaEquiv.symm σ
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma sliceUnderUncurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (sliceUnder p) _⦋n⦌) :
    sliceUnderUncurry (SSet.yonedaEquiv.symm σ) = σ.val
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
def cosliceIdentityCone {X : SSet.{u}} (x : X _⦋0⦌) :
    (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma cosliceIdentityCone_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone x) = x
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
lemma IsInitialVertex.nonempty_split {X : SSet.{u}} {x y : X _⦋0⦌}
    (hy : IsInitialVertex y) (f : Edge (X
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
noncomputable def initialVertexIso₂ {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : IsInitialVertex x) (hy : IsInitialVertex y) :
    HomotopyCategory₂.mk (A
```

InitialUniqueness.lean、namespace `SerrePositivity.InfinityCategories`：

```lean
noncomputable def initialVertexIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : IsInitialVertex x) (hy : IsInitialVertex y) :
    (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk y
```

Core の対象ビルド・公理監査はともに終了コード 0。累計 271 件は標準三公理のみ
（公理なしも含む）。A2e は双対と hX での同型まで完了。A2f〜A2i は未完了。
引き続き極限を slice の終対象として定義する。

### A2f 完了（2026-10-18）：join の錐と極限

`Core/Limit.lean` に、join の錐を固定条件付きの射の部分型 `JoinCone p` として定義した。
これは定義上 `sliceOver p` の零単体そのもの。`IsLimitCone c` は対応する slice の頂点の終対象性。
`[Quasicategory X]` の下で `limitConeIso` は二つの極限錐の h(slice) での同型、
`limitVertexIso` はその射影による hX での頂点の同型を与える。
`HasLimit p` は極限錐の存在。追加公理やモデル構造の仮定はない。

全 8 公開宣言の正確な型は次の通り。宇宙 `u` は任意、namespace は
`SerrePositivity.InfinityCategories`、`open CategoryTheory SSet` と `open scoped Simplicial`。

```lean
abbrev JoinCone {K X : SSet.{u}} (p : K ⟶ X)
```

```lean
def JoinCone.vertex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : X _⦋0⦌
```

```lean
lemma JoinCone.vertex_eq {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    c.vertex = SSet.yonedaEquiv (joinInl Δ[0] K ≫ c.val)
```

```lean
def IsLimitCone {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) : Prop
```

```lean
def HasLimit {K X : SSet.{u}} (p : K ⟶ X) : Prop
```

```lean
lemma isLimitCone_iff_trivialKanFibration {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ TrivialKanFibration
      (sliceOverProjection (K
```

```lean
noncomputable def limitConeIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ≅ SSet.HomotopyCategory.mk d
```

```lean
noncomputable def limitVertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d) :
    (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk d.vertex
```

Core の対象ビルド・公理監査は終了コード 0。累計 279 件が標準三公理のみ
（公理なしも含む）。A2f 完了。A2g〜A2i は未完了。引き続き cospan と正方形の比較へ進む。

### A2g 完了（2026-10-18）：cospan の錐と引き戻し四角形

`Square.lean` の `cospanConeSquareIso` が、要求された同型
`join Δ[0] (horn 2 2) ≅ Δ[1] ⊗ Δ[1]` を与える。
両側を対角の辺に沿う二つの三角形の pushout として表示し、普遍性で比較した。
正方形側は Mathlib の最大次元の非退化単体の列挙を用いて全次数の和・交わりを証明した。
`JoinFunctor.lean` は右因子の部分複体の二項の和・交わりを join が保つ補助。

座標は錐頂点が (0,0)、ホーンの頂点 0 が (1,0)、1 が (0,1)、2 が (1,1)。
`cospanSquareBoundary_rightEdge`・`cospanSquareBoundary_topEdge` により
0→2 と 1→2 がそれぞれ正方形の右辺と上辺になることを証明した。
`Pullback.lean` の `pullbackCone F` はこの cospan 上の錐、
`IsPullbackSquare F := IsLimitCone (pullbackCone F)` が求める引き戻し四角形の定義である。
定義自体に quasicategory 性は不要。追加公理・モデル構造は使わない。

新規全 36 公開宣言の正確な型を以下に記録する。宇宙 `u` は任意、namespace は
`SerrePositivity.InfinityCategories`。`open CategoryTheory Limits MonoidalCategory SSet`、
`open scoped Simplicial` の下の型。

JoinFunctor.lean：

```lean
def joinRightFunctor (A : SSet.{u}) : SSet.{u} ⥤ SSet.{u}
```

JoinFunctor.lean：

```lean
lemma Join.augMem_inf {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) (r : ℕ) (b : Join.augObj B r) :
    Join.augMem (B₀ ⊓ B₁) r b ↔ Join.augMem B₀ r b ∧ Join.augMem B₁ r b
```

JoinFunctor.lean：

```lean
lemma Join.augMem_sup {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) (r : ℕ) (b : Join.augObj B r) :
    Join.augMem (B₀ ⊔ B₁) r b ↔ Join.augMem B₀ r b ∨ Join.augMem B₁ r b
```

JoinFunctor.lean：

```lean
lemma joinSubcomplexRight_inf (A : SSet.{u}) {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) :
    joinSubcomplexRight A (B₀ ⊓ B₁) = joinSubcomplexRight A B₀ ⊓ joinSubcomplexRight A B₁
```

JoinFunctor.lean：

```lean
lemma joinSubcomplexRight_sup (A : SSet.{u}) {B : SSet.{u}} (B₀ B₁ : B.Subcomplex) :
    joinSubcomplexRight A (B₀ ⊔ B₁) = joinSubcomplexRight A B₀ ⊔ joinSubcomplexRight A B₁
```

JoinFunctor.lean：

```lean
lemma joinSubcomplexRight_bicartSq (A : SSet.{u}) {B : SSet.{u}}
    {B₀ B₁ B₂ B₃ : B.Subcomplex} (h : Subcomplex.BicartSq B₀ B₁ B₂ B₃) :
    Subcomplex.BicartSq (joinSubcomplexRight A B₀) (joinSubcomplexRight A B₁)
      (joinSubcomplexRight A B₂) (joinSubcomplexRight A B₃)
```

JoinFunctor.lean：

```lean
noncomputable def joinRightSubcomplexIso (A : SSet.{u}) {B C : SSet.{u}}
    (B₀ : B.Subcomplex) (e : C ≅ (B₀ : SSet.{u})) :
    join A C ≅ (joinSubcomplexRight A B₀ : SSet.{u})
```

JoinFunctor.lean：

```lean
lemma joinRightSubcomplexIso_hom_ι (A : SSet.{u}) {B C : SSet.{u}}
    (B₀ : B.Subcomplex) (e : C ≅ (B₀ : SSet.{u})) :
    (joinRightSubcomplexIso A B₀ e).hom ≫ (joinSubcomplexRight A B₀).ι =
      joinMap (𝟙 A) (e.hom ≫ B₀.ι)
```

JoinFunctor.lean：

```lean
lemma joinRight_horn₂₂_isPushout (A : SSet.{u}) :
    IsPushout (joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)))
      (joinMap (𝟙 A) (stdSimplex.δ (0 : Fin 2)))
      (joinMap (𝟙 A) horn₂₂.ι₀₂) (joinMap (𝟙 A) horn₂₂.ι₁₂)
```

Square.lean：

```lean
lemma mono_yoneda_prod_nonDegenerate {p q n : ℕ}
    (s : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) : Mono (SSet.yonedaEquiv.symm s.val)
```

Square.lean：

```lean
noncomputable def squareTriangleSimplex (i : Fin 2) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}).nonDegenerate 2
```

Square.lean：

```lean
def squareDiagonalSimplex : (Δ[1] ⊗ Δ[1] : SSet.{u}).nonDegenerate 1
```

Square.lean：

```lean
noncomputable def squareTriangle (i : Fin 2) : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]
```

Square.lean：

```lean
def squareDiagonal : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]
```

Square.lean：

```lean
lemma squareTriangle_diagonal (i : Fin 2) :
    stdSimplex.δ (1 : Fin 3) ≫ squareTriangle.{u} i = squareDiagonal
```

Square.lean：

```lean
lemma squareTriangle_inf :
    Subcomplex.ofSimplex (squareTriangleSimplex.{u} 0).val ⊓
      Subcomplex.ofSimplex (squareTriangleSimplex 1).val =
        Subcomplex.ofSimplex squareDiagonalSimplex.val
```

Square.lean：

```lean
lemma squareTriangle_sup :
    Subcomplex.ofSimplex (squareTriangleSimplex.{u} 0).val ⊔
      Subcomplex.ofSimplex (squareTriangleSimplex 1).val = ⊤
```

Square.lean：

```lean
noncomputable def prodSimplexImageIso {p q n : ℕ}
    (s : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) :
    (Δ[n] : SSet.{u}) ≅ (Subcomplex.ofSimplex s.val : SSet.{u})
```

Square.lean：

```lean
lemma square_isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    (squareTriangle.{u} 0) (squareTriangle 1)
```

Square.lean：

```lean
def cospanConeTriangleLeft : (Δ[2] : SSet.{u}) ⟶ join Δ[0] (horn 2 2 : SSet.{u})
```

Square.lean：

```lean
def cospanConeTriangleRight : (Δ[2] : SSet.{u}) ⟶ join Δ[0] (horn 2 2 : SSet.{u})
```

Square.lean：

```lean
lemma cospanCone_isPushout : IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
    cospanConeTriangleLeft.{u} cospanConeTriangleRight
```

Square.lean：

```lean
noncomputable def cospanConeSquareIso :
    join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}) ≅ Δ[1] ⊗ Δ[1]
```

Square.lean：

```lean
lemma cospanConeSquareIso_left :
    cospanConeTriangleLeft ≫ cospanConeSquareIso.{u}.hom = squareTriangle 1
```

Square.lean：

```lean
lemma cospanConeSquareIso_right :
    cospanConeTriangleRight ≫ cospanConeSquareIso.{u}.hom = squareTriangle 0
```

Pullback.lean：

```lean
def squareRightEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]
```

Pullback.lean：

```lean
def squareTopEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]
```

Pullback.lean：

```lean
lemma squareTriangle_rightEdge :
    stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 1 = squareRightEdge
```

Pullback.lean：

```lean
lemma squareTriangle_topEdge :
    stdSimplex.δ (0 : Fin 3) ≫ squareTriangle.{u} 0 = squareTopEdge
```

Pullback.lean：

```lean
noncomputable def cospanSquareBoundary : (horn 2 2 : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]
```

Pullback.lean：

```lean
lemma cospanSquareBoundary_rightEdge :
    horn₂₂.ι₀₂ ≫ cospanSquareBoundary.{u} = squareRightEdge
```

Pullback.lean：

```lean
lemma cospanSquareBoundary_topEdge :
    horn₂₂.ι₁₂ ≫ cospanSquareBoundary.{u} = squareTopEdge
```

Pullback.lean：

```lean
noncomputable def pullbackCospan {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (horn 2 2 : SSet.{u}) ⟶ X
```

Pullback.lean：

```lean
noncomputable def pullbackCone {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    JoinCone (pullbackCospan F)
```

Pullback.lean：

```lean
def IsPullbackSquare {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) : Prop
```

Pullback.lean：

```lean
lemma isPullbackSquare_iff_trivialKanFibration {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare F ↔ TrivialKanFibration
      (sliceOverProjection (X
```

Core の対象ビルド・公理監査は終了コード 0。累計 315 件が標準三公理のみ
（公理なしも含む）。A2g 完了。A2h〜A2i は未完了。
A2h の正確な文言・前提と原典の向きを README に実装前に固定し、報告してから着手する。

### A2h 完了（2026-10-18）：始対象による slice の制限

実装前に README に正確な文言・前提・向き・原典を固定して報告し、
追加承認を待たず着手するというユーザー指示に従った。
`InitialCofinality.lean` の `initialCofinality` は、任意の小圏 I の通常の始対象 c と
任意の単体集合の射 `F : nerve I ⟶ X`、`[Quasicategory X]` に対し
`TrivialKanFibration (initialRestriction F c)` を証明する。制限の標的は
`sliceOver (nervePoint c ≫ F)` であり、全図式から c での値へ向かう。

`SliceRestriction.lean` は A2c を用い、一般の left anodyne 単射による slice の制限の
trivial Kan fibration 性を証明した。単射を像への同型と部分複体包含に分け、前者での制限は同型。
`ConeAnodyne.lean` は点を左から join した任意の単射の left anodyne 性を、
境界セルでの最初のホーンの同定と coslice の普遍性・境界セル分解で証明した。
`NerveCone.lean` は各射列に始対象からの一意な射を前置して自然な錐を作り、
c 上で恒等辺になることを示した。元の c 側の端点を使う矢の retract により、
`nervePoint_leftAnodyne` が成立する。c に入る非恒等射がないという余分な仮定はない。
一般の cofinality 理論やモデル構造は使っていない。

全 41 新規公開宣言の正確な型を以下に記録する。namespace は
`SerrePositivity.InfinityCategories`、宇宙 `u` は任意、
`open CategoryTheory Limits SSet MorphismProperty` と `open scoped Simplicial` の下の型。

SliceRestriction.lean：

```lean
lemma sliceOverRestrict_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : leftAnodyneExtensions K₀.ι) : HasLiftingProperty A₀.ι (sliceOverRestrict p K₀.ι)
```

SliceRestriction.lean：

```lean
lemma sliceOverRestrict_subcomplex_trivialKanFibration {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) (hK : leftAnodyneExtensions K₀.ι) :
    TrivialKanFibration (sliceOverRestrict p K₀.ι)
```

SliceRestriction.lean：

```lean
lemma sliceOverRestrict_comp {K₀ K₁ K X : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K₁) (g : K₁ ⟶ K) :
    sliceOverRestrict p (f ≫ g) = sliceOverRestrict p g ≫ sliceOverRestrict (g ≫ p) f
```

SliceRestriction.lean：

```lean
lemma sliceOverRestrict_isIso {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) [IsIso f] :
    IsIso (sliceOverRestrict p f)
```

SliceRestriction.lean：

```lean
lemma sliceOverRestrict_trivialKanFibration {K₀ K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : K₀ ⟶ K) [Mono f] (hf : leftAnodyneExtensions f) :
    TrivialKanFibration (sliceOverRestrict p f)
```

ConeAnodyne.lean：

```lean
lemma coneBoundary_horn_preimage (n : ℕ) :
    (horn (0 + n + 1) 0).preimage (joinStdSimplexIso.{u} 0 n).hom =
      joinSubcomplexRight Δ[0] (boundary n)
```

ConeAnodyne.lean：

```lean
lemma joinPoint_boundary_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary n).ι)
```

ConeAnodyne.lean：

```lean
lemma sliceUnderPostcomp_boundary_lifting {X Y : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (q : X ⟶ Y) [LeftFibration q] (n : ℕ) :
    HasLiftingProperty (boundary n).ι (sliceUnderPostcomp p q)
```

ConeAnodyne.lean：

```lean
lemma sliceUnderPostcomp_trivialKanFibration {X Y : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [LeftFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q)
```

ConeAnodyne.lean：

```lean
lemma joinPoint_mono_leftAnodyne {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    leftAnodyneExtensions (joinMap (𝟙 (Δ[0] : SSet.{u})) f)
```

NerveCone.lean：

```lean
def prependOrderHom {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Fin (m + 2) →o Fin (n + 2)
```

NerveCone.lean：

```lean
lemma prependOrderHom_zero {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    prependOrderHom α 0 = 0
```

NerveCone.lean：

```lean
lemma prependOrderHom_succ {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    prependOrderHom α i.succ = (α i).succ
```

NerveCone.lean：

```lean
lemma Join.stdAugEquiv_augHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ)
    (a : Join.augObj (Δ[m] : SSet.{u}) r) :
    Join.stdAugEquiv n r (Join.augHom (stdSimplex.map α) r a) =
      α.toOrderHom.comp (Join.stdAugEquiv m r a)
```

NerveCone.lean：

```lean
lemma concat_prependOrderHom {m n r : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (ℓ : ℕ) (hℓ : ℓ ≤ r) (f : Fin ℓ →o Fin 1) (g : Fin (r - ℓ) →o Fin (m + 1))
    (i : Fin r) :
    (Join.concat ℓ hℓ f (α.comp g) i).val =
      (prependOrderHom α (Fin.cast (by omega) (Join.concat ℓ hℓ f g i))).val
```

NerveCone.lean：

```lean
def simplexCastIso {m n : ℕ} (h : m = n) : (Δ[m] : SSet.{u}) ≅ Δ[n]
```

NerveCone.lean：

```lean
lemma simplexCastIso_hom_app_val {m n : ℕ} (h : m = n) (d : ℕ)
    (s : (Δ[m] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((simplexCastIso h).hom.app (Opposite.op ⦋d⦌) s i).val = (s i).val
```

NerveCone.lean：

```lean
def pointJoinStdSimplexIso (n : ℕ) : join (Δ[0] : SSet.{u}) Δ[n] ≅ Δ[n + 1]
```

NerveCone.lean：

```lean
lemma pointJoinStdSimplexIso_hom_app_val (n d : ℕ)
    (s : Join.Simplex (Δ[0] : SSet.{u}) Δ[n] d) (i : Fin (d + 1)) :
    ((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌) s i).val =
      (Join.stdEncode 0 n d s i).val
```

NerveCone.lean：

```lean
lemma joinStdSimplexIso_point_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.map α) ≫ (pointJoinStdSimplexIso n).hom =
      (pointJoinStdSimplexIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (prependOrderHom α.toOrderHom))
```

NerveCone.lean：

```lean
def nerveVertex {I : Type u} [Category.{u} I] (c : I) : (nerve I) _⦋0⦌
```

NerveCone.lean：

```lean
def nervePoint {I : Type u} [Category.{u} I] (c : I) : (Δ[0] : SSet.{u}) ⟶ nerve I
```

NerveCone.lean：

```lean
noncomputable def initialChain {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : ComposableArrows I n) : ComposableArrows I (n + 1)
```

NerveCone.lean：

```lean
lemma initialChain_naturality {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op (initialChain hc F) =
      initialChain hc ((nerve I).map α.op F)
```

NerveCone.lean：

```lean
lemma initialChain_tail {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) : (nerve I).δ 0 (initialChain hc F) = F
```

NerveCone.lean：

```lean
lemma initialChain_vertex {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (initialChain hc F) = nerveVertex c
```

NerveCone.lean：

```lean
lemma pointJoinStdSimplexIso_inl_vertex (n : ℕ) :
    joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (pointJoinStdSimplexIso n).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)))
```

NerveCone.lean：

```lean
lemma pointJoinStdSimplexIso_inr (n : ℕ) :
    joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ (pointJoinStdSimplexIso n).hom = stdSimplex.δ 0
```

NerveCone.lean：

```lean
noncomputable def nerveInitialConeSimplex {I : Type u} [Category.{u} I] {c : I}
    (hc : IsInitial c) {n : ℕ} (F : (nerve I) _⦋n⦌) : (sliceUnder (nervePoint c)) _⦋n⦌
```

NerveCone.lean：

```lean
noncomputable def nerveInitialSection {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    nerve I ⟶ sliceUnder (nervePoint c)
```

NerveCone.lean：

```lean
lemma nerveInitialSection_projection {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    nerveInitialSection hc ≫ sliceUnderProjection (nervePoint c) = 𝟙 (nerve I)
```

NerveCone.lean：

```lean
noncomputable def nerveInitialCone {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    join (Δ[0] : SSet.{u}) (nerve I) ⟶ nerve I
```

NerveCone.lean：

```lean
lemma nerveInitialCone_inr {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    joinInr (Δ[0] : SSet.{u}) (nerve I) ≫ nerveInitialCone hc = 𝟙 (nerve I)
```

NerveCone.lean：

```lean
lemma initialChain_self {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    initialChain hc (nerveVertex c) = (nerve I).σ 0 (nerveVertex c)
```

NerveCone.lean：

```lean
lemma nerveInitialSection_at_point {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    nervePoint c ≫ nerveInitialSection hc =
      (SSet.yonedaEquiv (X
```

NerveCone.lean：

```lean
lemma nerveInitialCone_at_point {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint c) ≫ nerveInitialCone hc =
      SSet.const (nerveVertex c)
```

NerveCone.lean：

```lean
instance nervePoint_mono {I : Type u} [Category.{u} I] (c : I) : Mono (nervePoint c)
```

NerveCone.lean：

```lean
noncomputable def nervePointRetract {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    RetractArrow (nervePoint c) (joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint c))
```

NerveCone.lean：

```lean
lemma nervePoint_leftAnodyne {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c) :
    leftAnodyneExtensions (nervePoint c)
```

InitialCofinality.lean：

```lean
def initialRestriction {I : Type u} [Category.{u} I] {X : SSet.{u}}
    (F : nerve I ⟶ X) (c : I) : sliceOver F ⟶ sliceOver (nervePoint c ≫ F)
```

InitialCofinality.lean：

```lean
lemma initialCofinality {I : Type u} [Category.{u} I] {c : I} (hc : IsInitial c)
    {X : SSet.{u}} [Quasicategory X] (F : nerve I ⟶ X) :
    TrivialKanFibration (initialRestriction F c)
```

Core の対象ビルド・公理監査はともに終了コード 0。累計 356 件は標準三公理のみ
（公理なしも含む）。A2h は固定した一般性で完了。A2i は未完了。
次に通常の圏の nerve における具体的な極限の検算と最終監査へ進む。


### A2i 完了（2026-10-18）：通常の圏の nerve の極限の比較と最終監査

`Checks.lean` から `LimitExamples.lean` を公開 import し、通常の順序圏
`ULift.{0} (Fin 2)`（0→1）の二対象離散図式 `(1,1)` で極限を比較した。
`topPairDiagram_nerve_eq` は図式の一致、`topPairNerveCone_vertex` は錐の頂点の一致。
`topPairOrdinaryCone_isLimit_iff` と `topPairNerveCone_isLimit_iff` は両側とも
極限性が `v = 1` と同値であることを示す。従って v=1 の正例だけでなく v=0 の負例も含む。
主定理 `topPair_limit_agreement` は、同じ図式・頂点の通常の錐と join の錐の極限性の同値。
さらに任意の単体集合 K について標準辺の終対象 1 への定数図式の極限錐を直接検証した。

以下が新規の全 34 公開宣言の正確な型。TerminalMap は namespace
`SerrePositivity.InfinityCategories`、LimitExamples はその内部の `LimitChecks`。
`universe u`、`open CategoryTheory Limits SSet`、`open scoped Simplicial` を前提とする。
有限の通常圏の比較例は宇宙 0、標準辺・移送の補題は任意の宇宙 u。
quasicategory 等の前提は型中に全て明記しており、具体例には追加仮定はない。

TerminalMap.lean：

```lean
instance isIso_trivialKanFibration {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q] :
    TrivialKanFibration q
```

TerminalMap.lean：

```lean
lemma isTerminalVertex_of_trivialKanFibration {X Y : SSet.{u}} (q : X ⟶ Y)
    [TrivialKanFibration q] {x : X _⦋0⦌} (hx : IsTerminalVertex (q.app (Opposite.op ⦋0⦌) x)) :
    IsTerminalVertex x
```

TerminalMap.lean：

```lean
lemma IsTerminalVertex.map_of_isIso {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q]
    {x : X _⦋0⦌} (hx : IsTerminalVertex x) :
    IsTerminalVertex (q.app (Opposite.op ⦋0⦌) x)
```

TerminalMap.lean：

```lean
lemma sliceOverPostcomp_isIso {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) [IsIso q] :
    IsIso (sliceOverPostcomp p q)
```

TerminalMap.lean：

```lean
def JoinCone.postcomp {K X Y : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (q : X ⟶ Y) :
    JoinCone (p ≫ q)
```

TerminalMap.lean：

```lean
lemma IsLimitCone.postcomp_of_isIso {K X Y : SSet.{u}} {p : K ⟶ X} {c : JoinCone p}
    (hc : IsLimitCone c) (q : X ⟶ Y) [IsIso q] : IsLimitCone (c.postcomp q)
```

TerminalMap.lean：

```lean
def JoinCone.cast {K X : SSet.{u}} {p q : K ⟶ X} (c : JoinCone p) (h : p = q) : JoinCone q
```

TerminalMap.lean：

```lean
lemma JoinCone.vertex_cast {K X : SSet.{u}} {p q : K ⟶ X} (c : JoinCone p) (h : p = q) :
    (c.cast h).vertex = c.vertex
```

TerminalMap.lean：

```lean
lemma JoinCone.vertex_postcomp {K X Y : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (q : X ⟶ Y) :
    (c.postcomp q).vertex = q.app (Opposite.op ⦋0⦌) c.vertex
```

TerminalMap.lean：

```lean
lemma IsLimitCone.cast {K X : SSet.{u}} {p q : K ⟶ X} {c : JoinCone p}
    (hc : IsLimitCone c) (h : p = q) : IsLimitCone (c.cast h)
```

LimitExamples.lean：

```lean
lemma hom_ext_to_stdSimplex {A : SSet.{u}} {n : ℕ} (f g : A ⟶ Δ[n])
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g
```

LimitExamples.lean：

```lean
lemma join_hom_ext_to_stdSimplex {A B : SSet.{u}} {n : ℕ} (f g : join A B ⟶ Δ[n])
    (hA : joinInl A B ≫ f = joinInl A B ≫ g)
    (hB : joinInr A B ≫ f = joinInr A B ≫ g) : f = g
```

LimitExamples.lean：

```lean
def intervalTerminalExtension : join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1]
```

LimitExamples.lean：

```lean
lemma intervalTerminalExtension_inl :
    joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ intervalTerminalExtension = 𝟙 Δ[1]
```

LimitExamples.lean：

```lean
lemma intervalTerminalExtension_inr :
    joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ intervalTerminalExtension =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
```

LimitExamples.lean：

```lean
def intervalTerminalDiagram (K : SSet.{u}) : K ⟶ (Δ[1] : SSet.{u})
```

LimitExamples.lean：

```lean
lemma intervalTerminalProjection_isIso (K : SSet.{u}) :
    IsIso (sliceOverProjection (intervalTerminalDiagram K))
```

LimitExamples.lean：

```lean
lemma intervalLast_isTerminal :
    IsTerminalVertex (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))
```

LimitExamples.lean：

```lean
def intervalTerminalCone (K : SSet.{u}) : JoinCone (intervalTerminalDiagram K)
```

LimitExamples.lean：

```lean
lemma intervalTerminalCone_isLimit (K : SSet.{u}) : IsLimitCone (intervalTerminalCone K)
```

LimitExamples.lean：

```lean
def intervalConeAtVertex (K : SSet.{u}) (v : Fin 2) : JoinCone (intervalTerminalDiagram K)
```

LimitExamples.lean：

```lean
lemma intervalConeAtVertex_vertex (K : SSet.{u}) (v : Fin 2) :
    (intervalConeAtVertex K v).vertex = stdSimplex.obj₀Equiv.symm v
```

LimitExamples.lean：

```lean
lemma intervalConeAtVertex_one_isLimit (K : SSet.{u}) : IsLimitCone (intervalConeAtVertex K 1)
```

LimitExamples.lean：

```lean
def walkingArrowTop : ULift.{0} (Fin 2)
```

LimitExamples.lean：

```lean
def topPairDiagram : Discrete Bool ⥤ ULift.{0} (Fin 2)
```

LimitExamples.lean：

```lean
def topPairOrdinaryCone (v : Fin 2) : Limits.Cone topPairDiagram
```

LimitExamples.lean：

```lean
def topPairOrdinaryCone_one_isLimit : Limits.IsLimit (topPairOrdinaryCone 1)
```

LimitExamples.lean：

```lean
lemma topPairOrdinaryCone_isLimit_iff (v : Fin 2) :
    Nonempty (Limits.IsLimit (topPairOrdinaryCone v)) ↔ v = 1
```

LimitExamples.lean：

```lean
lemma topPairDiagram_nerve_eq :
    nerveMap topPairDiagram = intervalTerminalDiagram (nerve (Discrete Bool)) ≫
      (stdSimplex.isoNerve.{0} 1).hom
```

LimitExamples.lean：

```lean
def topPairNerveCone (v : Fin 2) : JoinCone (nerveMap topPairDiagram)
```

LimitExamples.lean：

```lean
lemma topPairNerveCone_vertex (v : Fin 2) :
    (topPairNerveCone v).vertex = CategoryTheory.nerveEquiv.symm (ULift.up v)
```

LimitExamples.lean：

```lean
lemma topPairNerveCone_one_isLimit : IsLimitCone (topPairNerveCone 1)
```

LimitExamples.lean：

```lean
lemma topPairNerveCone_isLimit_iff (v : Fin 2) : IsLimitCone (topPairNerveCone v) ↔ v = 1
```

LimitExamples.lean：

```lean
lemma topPair_limit_agreement (v : Fin 2) :
    Nonempty (Limits.IsLimit (topPairOrdinaryCone v)) ↔ IsLimitCone (topPairNerveCone v)
```


検証：`lake build SerrePositivity.InfinityCategories.Core` と
`lake env lean scripts/audit_infinity_core.lean` はともに終了コード 0。
累計 390 件の `#print axioms` の出力を検査し、公理なし又は
`propext`・`Classical.choice`・`Quot.sound` のみであることを確認した。
Core/*.lean の明示的な公開宣言名を抽出して監査スクリプトと照合し、未登録名はない。
工程末の全体 `set -o pipefail; lake build` も終了コード 0（7507 jobs）。
ログは `/tmp/serre-core-a2i-build.log`・`/tmp/serre-core-a2i-audit.log`・
`/tmp/serre-core-a2-full-build.log`。

A1a–A1d、A2a–A2i は全て完了。これらの要求の範囲に未完了項目はない。
A2i は指定通り具体例による検算であり、任意の通常圏の全ての極限を比較する一般定理は
今回の要求に含まず、主張もしない。§4 の設計変更はない。A3 以降は別途指示を待つ。


### A3a 完了（2026-10-18）：関手単体集合の可逆二胞体による同値

`Core/Equivalence.lean` を追加。namespace は `SerrePositivity.InfinityCategories`、
任意の宇宙 u、`open CategoryTheory MonoidalCategory MonoidalClosed SSet`。
`FunctorIso f g` は h((ihom X).obj Y) での f,g の零単体間の同型。
`QCatEquivalence X Y` は hom、inv、homInvIso、invHomIso の四つのフィールドを持つ。
前後合成で二胞体を写して `refl`・`symm`・`trans` を構成した。
`functorHomotopyEvaluation` は積比較と評価から構成した関手であり、
`FunctorIso.toNatIso` で可逆二胞体を通常の自然同型へ送る。
`toHoEquivalence` は順方向と逆方向が正確に hoFunctor.map hom / inv である圏同値。
頂点の同型 `VertexIso` は定義通り hX の同型。
quasicategory の同値に必要な仮定は両側の Quasicategory のみで、追加の充填公理はない。
閉構造・評価の補題は任意の単体集合で成立する。

新規の明示的な公開宣言 19 件の正確な型は以下。
構造 QCatEquivalence の型に加え、そのフィールドの型は上記四フィールドを持つソース定義の通り。
監査には構造・構築子・全四フィールドを含む 24 件を追加した。

```lean
def functorVertex {X Y : SSet.{u}} (f : X ⟶ Y) : ((ihom X).obj Y) _⦋0⦌
```

```lean
abbrev FunctorIso {X Y : SSet.{u}} (f g : X ⟶ Y)
```

```lean
abbrev VertexIso {X : SSet.{u}} (x y : X _⦋0⦌)
```

```lean
def VertexIso.map {X Y : SSet.{u}} {x y : X _⦋0⦌} (e : VertexIso x y) (f : X ⟶ Y) :
    VertexIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
```

```lean
structure QCatEquivalence (X Y : SSet.{u}) [Quasicategory X] [Quasicategory Y]
```

```lean
def IsQCatEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) : Prop
```

```lean
lemma QCatEquivalence.isQCatEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : IsQCatEquivalence e.hom
```

```lean
noncomputable def IsQCatEquivalence.choose {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (h : IsQCatEquivalence f) : QCatEquivalence X Y
```

```lean
def FunctorIso.postcomp {X Y Z : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) (q : Y ⟶ Z) :
    FunctorIso (f ≫ q) (g ≫ q)
```

```lean
def FunctorIso.precomp {W X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) (q : W ⟶ X) :
    FunctorIso (q ≫ f) (q ≫ g)
```

```lean
def QCatEquivalence.refl (X : SSet.{u}) [Quasicategory X] : QCatEquivalence X X
```

```lean
def QCatEquivalence.symm {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : QCatEquivalence Y X
```

```lean
def QCatEquivalence.trans {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory Z] (e : QCatEquivalence X Y) (d : QCatEquivalence Y Z) :
    QCatEquivalence X Z
```

```lean
def functorHomotopyEvaluation (X Y : SSet.{u}) :
    hoFunctor.obj ((ihom X).obj Y) ⥤ (hoFunctor.obj X ⥤ hoFunctor.obj Y)
```

```lean
lemma functorHomotopyEvaluation_obj {X Y : SSet.{u}} (f : X ⟶ Y) :
    (functorHomotopyEvaluation X Y).obj (SSet.HomotopyCategory.mk (functorVertex f)) =
      (hoFunctor.map f).toFunctor
```

```lean
def FunctorIso.toNatIso {X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) :
    (hoFunctor.map f).toFunctor ≅ (hoFunctor.map g).toFunctor
```

```lean
def QCatEquivalence.toHoEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : hoFunctor.obj X ≌ hoFunctor.obj Y
```

```lean
lemma QCatEquivalence.toHoEquivalence_functor {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.toHoEquivalence.functor = (hoFunctor.map e.hom).toFunctor
```

```lean
lemma QCatEquivalence.toHoEquivalence_inverse {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (e : QCatEquivalence X Y) :
    e.toHoEquivalence.inverse = (hoFunctor.map e.inv).toFunctor
```


構造のフィールドの正確な型：
```lean
hom : X ⟶ Y
inv : Y ⟶ X
homInvIso : FunctorIso (hom ≫ inv) (𝟙 X)
invHomIso : FunctorIso (inv ≫ hom) (𝟙 Y)
```
`QCatEquivalence.mk` はこれら四データを順に受け取る構築子。
Core 対象ビルド・公理監査は終了コード 0、累計 414 件は標準三公理のみ。
A3a 完了。A3b–e は未完了、A3f は任意、A3g は保留。
設計 §4 は変更していない。次に A3b の文言を原典と照合・記録・報告して実装する。


### A3b 前段階（2026-10-18）：最後の外側ホーンの充填の順方向

A3b 全体は未完了。README の実装前の文言は変更していない。
可逆辺から最後の外側ホーンの充填条件への方向
`hasFinalHornFillers_of_isInvertibleEdge` を、全ての次数二以上で証明した。
左右ファイブレーションのうち左側について、三角形の持ち上げ、可逆性の反映、
終点を固定した可逆辺の厳密な持ち上げを整備した。
`FibrationRestriction.lean` の coslice の部分図式への制限は左ファイブレーション。
`OuterHornJoin.lean` は境界と一次ホーンの pushout-join を最後の外側ホーンと同定し、
右因子が最後の辺に一致することも証明する。
これらを用いた `joinUnion_extend_of_invertible_rightEdge` は任意の左因子・部分複体を扱う。

以下が全 26 新規公開宣言の正確な型。namespace は
`SerrePositivity.InfinityCategories`、任意の宇宙 u。
`open CategoryTheory SSet SSet.Truncated`、`open scoped Simplicial`。
Quasicategory / LeftFibration 等の前提は各型中に明記した。

InvertibleEdge.lean：

```lean
abbrev IsInvertibleEdge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
def edgeOfSimplex {X : SSet.{u}} (s : X _⦋1⦌) :
    SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma isInvertibleEdge_congr {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
def initialHornEdge (n : ℕ) : (horn (n + 2) 0 : SSet.{u}) _⦋1⦌
```

InvertibleEdge.lean：

```lean
def finalHornEdge (n : ℕ) : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) _⦋1⦌
```

InvertibleEdge.lean：

```lean
def HasInitialHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
def HasFinalHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma hasInitialHornFillers_of_kanComplex {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma hasFinalHornFillers_of_kanComplex {X : SSet.{u}} [KanComplex X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma IsInvertibleEdge.map {X Y : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma homotopyCategory_homMk_surjective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Surjective
      (SSet.Truncated.HomotopyCategory.homMk :
        SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma compStruct_nonempty_of_homMk_fac {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma IsInvertibleEdge.nonempty_inverse {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma leftFibration_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y) [LeftFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma leftFibration_reflects_invertibleEdge {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (q : X ⟶ Y) [LeftFibration q] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma leftFibration_liftEdge_source {X Y : SSet.{u}} (q : X ⟶ Y) [LeftFibration q]
    (x : X _⦋0⦌) {y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma leftFibration_liftInvertibleEdge_target {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [LeftFibration q] {a : Y _⦋0⦌} (b : X _⦋0⦌)
    (e : SSet.Truncated.Edge (X
```

InvertibleEdge.lean：

```lean
lemma leftFibration_liftHorn_one_last {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [LeftFibration q] (a : (horn 1 1 : SSet.{u}) ⟶ X)
    (b : (Δ[1] : SSet.{u}) ⟶ Y) (sq : CommSq a (horn 1 1).ι q b)
    (hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv b))) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X, (horn 1 1).ι ≫ F = a ∧ F ≫ q = b
```

InvertibleEdge.lean：

```lean
lemma joinUnion_extend_of_invertible_rightEdge {K X : SSet.{u}} [Quasicategory X]
    (K₀ : K.Subcomplex) (T : (joinUnion K₀ (horn 1 1) : SSet.{u}) ⟶ X)
    (he : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (joinInr (K₀ : SSet.{u}) Δ[1] ≫
        joinUnionLeft K₀ (horn 1 1) ≫ T)))) :
    ∃ L : join K (Δ[1] : SSet.{u}) ⟶ X, (joinUnion K₀ (horn 1 1)).ι ≫ L = T
```

InvertibleEdge.lean：

```lean
lemma hasFinalHornFillers_of_isInvertibleEdge {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

FibrationRestriction.lean：

```lean
lemma sliceUnderRestrict_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hA : leftAnodyneExtensions A₀.ι) : HasLiftingProperty A₀.ι (sliceUnderRestrict p K₀.ι)
```

FibrationRestriction.lean：

```lean
instance sliceUnderRestrict_leftFibration {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) : LeftFibration (sliceUnderRestrict p K₀.ι)
```

OuterHornJoin.lean：

```lean
lemma finalHornJoin_preimage (n : ℕ) :
    (horn (n + 2) (Fin.last (n + 2))).preimage (joinStdSimplexIso.{u} n 1).hom =
      joinUnion (boundary n) (horn 1 1)
```

OuterHornJoin.lean：

```lean
def finalHornJoinIso (n : ℕ) :
    (joinUnion (boundary n) (horn 1 1) : SSet.{u}) ≅ horn (n + 2) (Fin.last (n + 2))
```

OuterHornJoin.lean：

```lean
lemma finalHornJoinIso_hom_ι (n : ℕ) :
    (finalHornJoinIso.{u} n).hom ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      (joinUnion (boundary n) (horn 1 1)).ι ≫ (joinStdSimplexIso n 1).hom
```

OuterHornJoin.lean：

```lean
lemma joinStdSimplexIso_inr_edge (n : ℕ) :
    SSet.yonedaEquiv (joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso n 1).hom) =
      stdSimplex.edge (n + 2) ⟨n + 1, by omega⟩ (Fin.last (n + 2)) (Fin.le_last _)
```


Core 対象ビルドは終了コード 0（1550 jobs）。公理監査も終了コード 0、
累計 440 件は標準三公理のみ。
未完了：A3b の充填条件から可逆性への方向、最初の外側ホーン側、Kan⇔hX の全射可逆。
A3c–e も未完了。条件付き・片方向の成果を A3b の完成とは数えていない。
次に二次・三次のホーンによる逆向きへ進む。


### A3b 完了（2026-10-18）：Joyal の可逆辺の定理・Kan の特徴づけ

`Core/InvertibleEdge.lean` を全結果の公開入口とした。
前段階の実装は `InvertibleEdgeLifting.lean` に分離し、公開名・型は保持した。
`isInvertibleEdge_iff_hasInitialHornFillers` と
`isInvertibleEdge_iff_hasFinalHornFillers` により README で固定した三条件を
それぞれ同値として証明した。全ての n≥2 を扱う。
最後のホーンの逆向きは二次・三次ホーンのみを使い、quasicategory 性すら不要。
最初の側は単体集合の反転、quasicategory 性の反転保存、充填と可逆辺の反転を証明して帰着した。
`kanComplex_iff_isGroupoid X [Quasicategory X]` は Mathlib の KanComplex と
命題値の IsGroupoid (hoFunctor.obj X) の同値。一次ホーンも定数辺で充填している。

以下の追加 41 公開宣言の正確な型。namespace は
`SerrePositivity.InfinityCategories`、任意の宇宙 u。
`open CategoryTheory SSet`、`open scoped Simplicial`。
前提は各型中に明記したものだけで、外側ホーンの充填や
写像空間の Kan 性などを追加仮定にした条件付きの完成ではない。

OuterHornConverse.lean：

```lean
lemma HasFinalHornFillers.nonempty_leftInverse {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

OuterHornConverse.lean：

```lean
lemma isInvertibleEdge_of_hasFinalHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

OuterHornConverse.lean：

```lean
lemma isInvertibleEdge_iff_hasFinalHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

OuterHornConverse.lean：

```lean
instance kanComplex_ho_isGroupoid (X : SSet.{u}) [KanComplex X] :
    IsGroupoid (hoFunctor.obj X)
```

Opposite.lean：

```lean
def subcomplexOppositeIso {X : SSet.{u}} (A : X.Subcomplex) :
    (A : SSet.{u}).op ≅ (A.op : SSet.{u})
```

Opposite.lean：

```lean
lemma subcomplexOppositeIso_hom_ι {X : SSet.{u}} (A : X.Subcomplex) :
    (subcomplexOppositeIso A).hom ≫ A.op.ι = SSet.opFunctor.map A.ι
```

Opposite.lean：

```lean
def hornReverseIso (n : ℕ) (i : Fin (n + 1)) :
    (horn n i.rev : SSet.{u}) ≅ (horn n i : SSet.{u}).op
```

Opposite.lean：

```lean
lemma hornReverseIso_hom_ι (n : ℕ) (i : Fin (n + 1)) :
    (hornReverseIso.{u} n i).hom ≫ SSet.opFunctor.map (horn n i).ι =
      (horn n i.rev).ι ≫ (stdSimplex.opIso ⦋n⦌).inv
```

Opposite.lean：

```lean
lemma stdSimplex_doubleReverse (n : ℕ) :
    (stdSimplex.opIso.{u} ⦋n⦌).inv ≫ SSet.opFunctor.map (stdSimplex.opIso ⦋n⦌).inv ≫
      (SSet.opFunctorCompOpFunctorIso.app (Δ[n] : SSet.{u})).hom = 𝟙 Δ[n]
```

Opposite.lean：

```lean
instance quasicategory_op (X : SSet.{u}) [Quasicategory X] : Quasicategory X.op
```

Opposite.lean：

```lean
def edgeOp {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

Opposite.lean：

```lean
lemma edgeOp_id {X : SSet.{u}} (x : X _⦋0⦌) :
    edgeOp (SSet.Truncated.Edge.id (X
```

Opposite.lean：

```lean
def compStructOp {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X
```

Opposite.lean：

```lean
lemma IsInvertibleEdge.op {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

Opposite.lean：

```lean
lemma isInvertibleEdge_op_iff {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

Opposite.lean：

```lean
def reverseSimplex {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{u}) ⟶ X.op
```

Opposite.lean：

```lean
lemma reverseSimplex_comp {X Y : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X)
    (q : X ⟶ Y) : reverseSimplex n (F ≫ q) = reverseSimplex n F ≫ SSet.opFunctor.map q
```

Opposite.lean：

```lean
lemma opFunctorCompOpFunctorIso_coherence (X : SSet.{u}) :
    SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app X).hom =
      (SSet.opFunctorCompOpFunctorIso.app X.op).hom
```

Opposite.lean：

```lean
lemma reverseSimplex_double {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X) :
    reverseSimplex n (reverseSimplex n F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F
```

Opposite.lean：

```lean
lemma reverseSimplex_back {X : SSet.{u}} (n : ℕ) (F : (Δ[n] : SSet.{u}) ⟶ X.op) :
    reverseSimplex n (reverseSimplex n F ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom) = F
```

Opposite.lean：

```lean
def reverseHornMap {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{u}) ⟶ X) : (horn n i.rev : SSet.{u}) ⟶ X.op
```

Opposite.lean：

```lean
lemma reverseHornMap_restrict {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (F : (Δ[n] : SSet.{u}) ⟶ X) :
    reverseHornMap n i ((horn n i).ι ≫ F) = (horn n i.rev).ι ≫ reverseSimplex n F
```

Opposite.lean：

```lean
lemma reverseHornMap_injective (X : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (reverseHornMap (X
```

Opposite.lean：

```lean
lemma hornFiller_of_reverseHornFiller {X : SSet.{u}} (n : ℕ) (i : Fin (n + 1))
    (σ : (horn n i : SSet.{u}) ⟶ X) (F : (Δ[n] : SSet.{u}) ⟶ X.op)
    (hF : (horn n i.rev).ι ≫ F = reverseHornMap n i σ) :
    ∃ G : (Δ[n] : SSet.{u}) ⟶ X, (horn n i).ι ≫ G = σ
```

OuterHornDuality.lean：

```lean
def initialHornReverseIndexIso (n : ℕ) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ≅ horn (n + 2) (0 : Fin (n + 3)).rev
```

OuterHornDuality.lean：

```lean
def finalHornReverseIndexIso (n : ℕ) :
    (horn (n + 2) 0 : SSet.{u}) ≅ horn (n + 2) (Fin.last (n + 2)).rev
```

OuterHornDuality.lean：

```lean
def reverseInitialHornMap {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X.op
```

OuterHornDuality.lean：

```lean
def reverseFinalHornMap {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X) :
    (horn (n + 2) 0 : SSet.{u}) ⟶ X.op
```

OuterHornDuality.lean：

```lean
lemma reverseInitialHornMap_edge {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X) :
    (reverseInitialHornMap n σ).app (Opposite.op ⦋1⦌) (finalHornEdge.{u} n) =
      SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) (initialHornEdge.{u} n))
```

OuterHornDuality.lean：

```lean
lemma reverseFinalHornMap_edge {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X) :
    (reverseFinalHornMap n σ).app (Opposite.op ⦋1⦌) (initialHornEdge.{u} n) =
      SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) (finalHornEdge.{u} n))
```

OuterHornDuality.lean：

```lean
lemma initialHornReverseIndexIso_hom_ι (n : ℕ) :
    (initialHornReverseIndexIso.{u} n).hom ≫ (horn (n + 2) (0 : Fin (n + 3)).rev).ι =
      (horn (n + 2) (Fin.last (n + 2))).ι
```

OuterHornDuality.lean：

```lean
lemma finalHornReverseIndexIso_hom_ι (n : ℕ) :
    (finalHornReverseIndexIso.{u} n).hom ≫ (horn (n + 2) (Fin.last (n + 2)).rev).ι =
      (horn (n + 2) 0).ι
```

OuterHornDuality.lean：

```lean
lemma hasInitialHornFillers_of_hasFinalHornFillers_op {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma hasFinalHornFillers_of_hasInitialHornFillers_op {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma hasInitialHornFillers_congr {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma HasInitialHornFillers.map_iso {X Y : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma hasInitialHornFillers_of_isInvertibleEdge {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma isInvertibleEdge_of_hasInitialHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

OuterHornDuality.lean：

```lean
lemma isInvertibleEdge_iff_hasInitialHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X
```

KanCharacterization.lean：

```lean
lemma kanComplex_of_isGroupoid (X : SSet.{u}) [Quasicategory X]
    [IsGroupoid (hoFunctor.obj X)] : KanComplex X
```

KanCharacterization.lean：

```lean
lemma kanComplex_iff_isGroupoid (X : SSet.{u}) [Quasicategory X] :
    KanComplex X ↔ IsGroupoid (hoFunctor.obj X)
```


Core 対象ビルドは終了コード 0（1555 jobs）、公理監査は終了コード 0。
累計 481 件は標準三公理のみ。全 Core の明示的公開名の監査登録も確認。
A3b 完了。A3a も完了済み。A3c–e は未完了、A3f は任意、A3g は保留。
次に N レーンの PinchedHom/Basic.lean を変更せず読み込んで A3c を実装する。


### A3c 完了（2026-10-18）：左右の pinched 写像空間の Kan 性と π₀

`Core/MappingSpaceKan.lean` を公開入口とし、右模型の直接証明を
`MappingSpaceRightKan.lean`、零・一単体と π₀ の比較を `MappingSpacePiZero.lean`、
左模型と反転の比較を `MappingSpaceLeft.lean` に分けた。
N レーンの `PinchedHom/Basic.lean`・`Index.lean` は編集していない。

`pinchedHom_kanComplex` と `pinchedHomLeft_kanComplex` は元の X の Quasicategory のみを前提にする。
右ホーンの各面に先頭の定値面を加え、元の X の内ホーンを充填する直接証明とした。
右ホーンの全充填から A3b の Kan 判定へ接続し、一次ホーンも含めた全次数を証明した。
左模型は反転した X の右模型をパラメータでも反転して構成した。

`pinchedHomPiZeroEquiv` と `pinchedHomLeftPiZeroEquiv` はそれぞれの π₀ と
`(SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)` の同値。
零単体と辺を直接同定し、右模型の一次単体と右ホモトピーの三角形を往復して証明した。
左側には辺・ホモトピー関係・連結成分の反転と A1 の比較同値を用いた。
写像空間の Kan 性を π₀ の比較の追加仮定にしていない。

以下が全 28 新規公開宣言の正確な型。namespace は
`SerrePositivity.InfinityCategories`、任意の宇宙 u、
`open CategoryTheory SSet SSet.Truncated`、`open scoped Simplicial`。
Quasicategory 等の前提は各型中に明記したものだけ。

MappingSpacePiZero.lean：

```lean
lemma pinchedConstant_zero {X : SSet.{u}} (x : X _⦋0⦌) : PinchedHom.constant x 0 = x
```

MappingSpacePiZero.lean：

```lean
lemma pinchedConstant_one {X : SSet.{u}} (x : X _⦋0⦌) :
    PinchedHom.constant x 1 = (SSet.Truncated.Edge.id (X
```

MappingSpacePiZero.lean：

```lean
def pinchedHomVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    (pinchedHom x y) _⦋0⦌ ≃ SSet.Truncated.Edge (X
```

MappingSpacePiZero.lean：

```lean
lemma pinchedExtend_face_one (i : Fin 2) :
    PinchedHom.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc
```

MappingSpacePiZero.lean：

```lean
def pinchedHomEdge_compStruct {X : SSet.{u}} {x y : X _⦋0⦌}
    {a b : (pinchedHom x y) _⦋0⦌} (p : SSet.Edge (X
```

MappingSpacePiZero.lean：

```lean
def pinchedHomPiZeroToHom {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.π₀ (pinchedHom x y) → (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)
```

MappingSpacePiZero.lean：

```lean
def pinchedSimplexOfRightHomotopy {X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X
```

MappingSpacePiZero.lean：

```lean
def pinchedHomEdgeOfRightHomotopy {X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X
```

MappingSpacePiZero.lean：

```lean
lemma pinchedHomPiZeroToHom_injective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Injective (pinchedHomPiZeroToHom x y)
```

MappingSpacePiZero.lean：

```lean
lemma pinchedHomPiZeroToHom_surjective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Surjective (pinchedHomPiZeroToHom x y)
```

MappingSpacePiZero.lean：

```lean
noncomputable def pinchedHomPiZeroEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : SSet.π₀ (pinchedHom x y) ≃
      (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)
```

MappingSpaceRightKan.lean：

```lean
lemma kanComplex_of_rightHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), 0 < i →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X
```

MappingSpaceRightKan.lean：

```lean
lemma pinchedExtend_δ {n : ℕ} (i : Fin (n + 2)) :
    PinchedHom.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc
```

MappingSpaceRightKan.lean：

```lean
lemma pinchedHom_rightHornFilling {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (hi : 0 < i)
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ pinchedHom x y)
    (hf : horn.IsCompatible f) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ pinchedHom x y,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ F = f j hj
```

MappingSpaceRightKan.lean：

```lean
instance pinchedHom_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (pinchedHom x y)
```

MappingSpaceLeft.lean：

```lean
def edgeUnop {X : SSet.{u}} {x y : X.op _⦋0⦌}
    (e : SSet.Truncated.Edge (X
```

MappingSpaceLeft.lean：

```lean
def edgeOpEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.Truncated.Edge (X
```

MappingSpaceLeft.lean：

```lean
lemma edgeUnop_id {X : SSet.{u}} (x : X.op _⦋0⦌) :
    edgeUnop (X
```

MappingSpaceLeft.lean：

```lean
def compStructUnop {X : SSet.{u}} {x y z : X.op _⦋0⦌}
    {f : SSet.Truncated.Edge (X
```

MappingSpaceLeft.lean：

```lean
lemma homotopicL_edgeOp_iff {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (f g : SSet.Truncated.Edge (X
```

MappingSpaceLeft.lean：

```lean
noncomputable def homotopyCategory₂OpHomEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    (HomotopyCategory₂.mk (A
```

MappingSpaceLeft.lean：

```lean
noncomputable def homotopyCategoryOpHomEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) :
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) ≃
      ((SSet.HomotopyCategory.mk (SSet.opObjEquiv.symm y) : hoFunctor.obj X.op) ⟶
        SSet.HomotopyCategory.mk (SSet.opObjEquiv.symm x))
```

MappingSpaceLeft.lean：

```lean
def piZeroOpToPiZero (X : SSet.{u}) : SSet.π₀ X.op → SSet.π₀ X
```

MappingSpaceLeft.lean：

```lean
def piZeroToPiZeroOp (X : SSet.{u}) : SSet.π₀ X → SSet.π₀ X.op
```

MappingSpaceLeft.lean：

```lean
def piZeroOpEquiv (X : SSet.{u}) : SSet.π₀ X.op ≃ SSet.π₀ X
```

MappingSpaceLeft.lean：

```lean
def pinchedHomLeft {X : SSet.{u}} (x y : X _⦋0⦌) : SSet.{u}
```

MappingSpaceLeft.lean：

```lean
instance pinchedHomLeft_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (pinchedHomLeft x y)
```

MappingSpaceLeft.lean：

```lean
noncomputable def pinchedHomLeftPiZeroEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : SSet.π₀ (pinchedHomLeft x y) ≃
      (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y)
```


Core 対象ビルドは終了コード 0（1566 jobs）、公理監査は終了コード 0。
累計 509 件は標準三公理のみ。明示的な全公開宣言名の監査登録も確認した。
A3a–c 完了。A3d–e は未完了、A3f は任意、A3g は保留。
§4 の設計変更はない。次に終対象と写像空間の可縮性の同値へ進む。


### A3d 前半保存：可縮性と slice fiber（2026-10-18）

終対象から右 pinched 写像空間の可縮性を導く方向を実装。逆方向・同型不変性・終対象全体の可縮性は未完了であり、A3d 完了とは数えない。A3e も未着手。§4 の設計変更はない。以下の型は各ファイルの公開宣言の全ヘッダー。共通の `universe u`、`open CategoryTheory Limits SSet`、`open scoped Simplicial` の下で読む。

ContractibleKan：

```lean
def IsContractibleKan (K : SSet.{u}) : Prop

lemma isContractibleKan_iff_trivialKanFibration (K : SSet.{u}) :
    IsContractibleKan K ↔ TrivialKanFibration (terminal.from K)

lemma IsContractibleKan.nonempty {K : SSet.{u}} (h : IsContractibleKan K) : Nonempty (K _⦋0⦌)

lemma IsContractibleKan.kanComplex {K : SSet.{u}} (h : IsContractibleKan K) : KanComplex K

lemma IsContractibleKan.isTerminalVertex {K : SSet.{u}} (h : IsContractibleKan K)
    (x : K _⦋0⦌) : IsTerminalVertex x

lemma IsContractibleKan.isInitialVertex {K : SSet.{u}} (h : IsContractibleKan K)
    (x : K _⦋0⦌) : IsInitialVertex x

lemma IsContractibleKan.piZero_subsingleton {K : SSet.{u}} (h : IsContractibleKan K) :
    Subsingleton (SSet.π₀ K)

lemma isContractibleKan_of_nonempty_of_all_terminal {K : SSet.{u}}
    (hne : Nonempty (K _⦋0⦌)) (hterm : ∀ x : K _⦋0⦌, IsTerminalVertex x) :
    IsContractibleKan K

lemma isContractibleKan_of_iso {K L : SSet.{u}} (e : K ≅ L) (h : IsContractibleKan K) :
    IsContractibleKan L
```

VertexFiber：

```lean
def vertexFiber {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) : SSet.{u}

def vertexFiberι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) : vertexFiber p b ⟶ E

lemma vertexFiberι_comp {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiberι p b ≫ p = SSet.const b

def vertexFiberLift {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ E) (hf : f ≫ p = SSet.const b) : A ⟶ vertexFiber p b

lemma vertexFiberLift_ι {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ E) (hf : f ≫ p = SSet.const b) : vertexFiberLift p b f hf ≫ vertexFiberι p b = f

lemma vertexFiber_hom_ext {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {f g : A ⟶ vertexFiber p b} (h : f ≫ vertexFiberι p b = g ≫ vertexFiberι p b) : f = g

lemma vertexFiber_isContractibleKan {E B : SSet.{u}} (p : E ⟶ B) [TrivialKanFibration p]
    (b : B _⦋0⦌) : IsContractibleKan (vertexFiber p b)

lemma vertexFiber_kanComplex {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
    (b : B _⦋0⦌) : KanComplex (vertexFiber p b)
```

PinchedSlice：

```lean
lemma concat_extendOrderHom {m n r : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (ℓ : ℕ) (hℓ : ℓ ≤ r) (f : Fin ℓ →o Fin (m + 1)) (g : Fin (r - ℓ) →o Fin 1)
    (i : Fin r) :
    (Join.concat ℓ hℓ (α.comp f) g i).val =
      (PinchedHom.extendOrderHom α (Join.concat ℓ hℓ f g i)).val

lemma joinStdSimplexIso_rightPoint_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (stdSimplex.map α) (𝟙 (Δ[0] : SSet.{u})) ≫ (joinStdSimplexIso n 0).hom =
      (joinStdSimplexIso m 0).hom ≫ stdSimplex.map (PinchedHom.extend α)

lemma joinStdSimplexIso_rightPoint_inl (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
      stdSimplex.map (PinchedHom.front n)

lemma joinStdSimplexIso_rightPoint_inr (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso n 0).hom =
      stdSimplex.map (PinchedHom.lastVertex n)

def pinchedSimplexToFiber {X : SSet.{u}} {x y : X _⦋0⦌} {n : ℕ}
    (s : PinchedHom.Simplex x y n) :
    (vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌

def pinchedHomToSliceFiber {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x

def fiberSimplexToPinched {X : SSet.{u}} {x y : X _⦋0⦌} {n : ℕ}
    (s : (vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌) :
    PinchedHom.Simplex x y n

noncomputable def pinchedHomSliceFiberIso {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedHom x y ≅ vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x
```

TerminalMappingSpace：

```lean
lemma IsTerminalVertex.pinchedHom_isContractibleKan {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (z : X _⦋0⦌) : IsContractibleKan (pinchedHom z x)

noncomputable def IsTerminalVertex.isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (hx : IsTerminalVertex x) :
    IsTerminal (SSet.HomotopyCategory.mk x : hoFunctor.obj X)
```

Core 対象ビルド：終了コード 0（1570 jobs）。監査：終了コード 0、累計 536 宣言、許可された標準三公理のみ。全体ビルドは A3 完了時に実行する。


### A3d 続き：終対象の全部分複体・同型不変性（2026-10-18）

終対象の頂点の全部分複体が非空なら可縮な Kan 複体になること、および終対象性と極限性の同型不変性を証明した。quasicategory の仮定を必要とする箇所は型に明記。`IsLimitCone.of_vertexIso` の同型は h(sliceOver p) であり h X の頂点の同型ではない。以下は共通の `universe u`、`open CategoryTheory Limits SSet`、`open scoped Simplicial` の下での全公開宣言の型。

TerminalVertices：

```lean
def fullSubcomplexOnVertices (X : SSet.{u}) (P : X _⦋0⦌ → Prop) : X.Subcomplex

lemma fullSubcomplexOnVertices_vertex {X : SSet.{u}} {P : X _⦋0⦌ → Prop}
    (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) : P x.val

def fullSubcomplexLiftSimplex {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X)
    (hF : ∀ v : ⦋0⦌ ⟶ ⦋n⦌, P (SSet.yonedaEquiv (stdSimplex.map v ≫ F))) :
    (Δ[n] : SSet.{u}) ⟶ (fullSubcomplexOnVertices X P : SSet.{u})

def terminalVertices (X : SSet.{u}) : X.Subcomplex

lemma fullSubcomplexLiftSimplex_ι {X : SSet.{u}} (P : X _⦋0⦌ → Prop) {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X)
    (hF : ∀ v : ⦋0⦌ ⟶ ⦋n⦌, P (SSet.yonedaEquiv (stdSimplex.map v ≫ F))) :
    fullSubcomplexLiftSimplex P F hF ≫ (fullSubcomplexOnVertices X P).ι = F

lemma terminalVertices_isContractibleKan {X : SSet.{u}}
    (hne : ∃ x : X _⦋0⦌, IsTerminalVertex x) :
    IsContractibleKan (terminalVertices X : SSet.{u})
```

HornPointJoin：

```lean
lemma finalHornPointJoin_preimage (n : ℕ) :
    (horn (n + 1) (Fin.last (n + 1))).preimage (joinStdSimplexIso.{u} n 0).hom =
      joinSubcomplexLeft (boundary n) Δ[0]

noncomputable def finalHornPointJoinIso (n : ℕ) :
    join (boundary n : SSet.{u}) Δ[0] ≅ horn (n + 1) (Fin.last (n + 1))

lemma finalHornPointJoinIso_hom_ι (n : ℕ) :
    (finalHornPointJoinIso.{u} n).hom ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
      joinMap (boundary n).ι (𝟙 Δ[0]) ≫ (joinStdSimplexIso n 0).hom

lemma finalHornPointJoinIso_edge (n : ℕ) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso.{u} (n + 1)).hom) = finalHornEdge n
```

TerminalTransport：

```lean
lemma IsTerminalVertex.exists_sliceLift {A X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (b : A ⟶ X) :
    ∃ C : A ⟶ sliceOver (SSet.yonedaEquiv.symm x),
      C ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b

lemma isTerminalVertex_of_isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsTerminalVertex x)
    (hy : IsTerminal (SSet.HomotopyCategory.mk y : hoFunctor.obj X)) : IsTerminalVertex y

lemma IsTerminalVertex.of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (hx : IsTerminalVertex x) (e : VertexIso x y) : IsTerminalVertex y

lemma isTerminalVertex_iff_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) : IsTerminalVertex x ↔ IsTerminalVertex y

lemma IsLimitCone.of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (hc : IsLimitCone c) (e : VertexIso (X := sliceOver p) c d) :
    IsLimitCone d

lemma isLimitCone_iff_of_vertexIso {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (e : VertexIso (X := sliceOver p) c d) : IsLimitCone c ↔ IsLimitCone d
```

Core 対象ビルド：終了コード 0（1573 jobs）。監査：終了コード 0、累計 552 宣言、標準三公理のみ。A3d は写像空間の可縮性から終対象性を導く逆方向だけ未完了。A3e は未着手、A3f は任意、A3g は保留。§4 の設計変更はない。


### A3d 逆方向の準備：境界の prism と fiber での充填（2026-10-18）

Kerodon Lemma 4.4.2.15 の右ファイブレーション版を進めた。正則 pairing の左右のホーンの判定、終端と任意の単射の pushout-product の right anodyne 性、標準単体の先頭への収縮、右ファイブレーションへの境界ホモトピーの持ち上げ、可縮な先頭 fiber での境界の充填を実装。prism 全体への延長はまだ未完了であり、右ファイブレーションの可縮 fiber 判定も A3d の逆方向も完成と数えない。共通の `universe u`、`open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty`、`open scoped Simplicial` の下での公開宣言の型は以下。

PairingHorns：

```lean
lemma pairing_leftAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (hn : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1)) :
    leftAnodyneExtensions A.ι

lemma pairing_rightAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (h0 : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ 0) :
    rightAnodyneExtensions A.ι

lemma pairingCore_leftAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.PairingCore) [P.pairing.IsRegular]
    (hn : ∀ s : P.ι, P.index s ≠ Fin.last (P.dim s + 1)) :
    leftAnodyneExtensions A.ι

lemma leftAnodyneExtensions_unionProd {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    leftAnodyneExtensions (Subcomplex.unionProd.{u} (horn (m + 1) k.castSucc) (boundary n)).ι

lemma uniquelyCodimOneFace_op_index {X : SSet.{u}} {x y : X.S}
    (h : x.IsUniquelyCodimOneFace y) : h.op.index rfl = (h.index rfl).rev

lemma pairing_op_index_ne_zero {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsProper]
    (hn : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1))
    (s : P.op.II) : (P.op.isUniquelyCodimOneFace s).index rfl ≠ 0

lemma pairing_ofIso_index_ne_zero {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex}
    (P : A.Pairing) [P.IsProper] (e : Y ≅ X) (hA : A.preimage e.hom = B)
    (h0 : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ 0)
    (s : (P.ofIso e hA).II) : ((P.ofIso e hA).isUniquelyCodimOneFace s).index rfl ≠ 0

lemma rightAnodyneExtensions_unionProd_point (n : ℕ) :
    rightAnodyneExtensions (Subcomplex.unionProd.{u} (horn 1 1) (boundary n)).ι
```

RightPrism：

```lean
lemma rightAnodyneExtensions_pushoutObjObj_point {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn 1 1).ι i) :
    rightAnodyneExtensions sq.ι

lemma rightAnodyneExtensions_point_whiskerRight (A : SSet.{u}) :
    rightAnodyneExtensions ((horn 1 1).ι ▷ A)
```

PrismContraction：

```lean
def prismFirstOrderHom (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1)

def prismFirstContraction (n : ℕ) : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[n]

noncomputable def prismEndpoint (i : Fin 2) (A : SSet.{u}) : A ⟶ (Δ[1] : SSet.{u}) ⊗ A

lemma prismEndpoint_naturality (i : Fin 2) {A B : SSet.{u}} (f : A ⟶ B) :
    prismEndpoint i A ≫ (Δ[1] ◁ f) = f ≫ prismEndpoint i B

lemma prismFirstContraction_one (n : ℕ) :
    prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ prismFirstContraction n = 𝟙 Δ[n]

lemma prismFirstContraction_zero (n : ℕ) :
    prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ prismFirstContraction n =
      SSet.const (stdSimplex.obj₀Equiv.symm 0)

lemma prismFirstContraction_horn_one (n : ℕ) :
    ((horn 1 1).ι ▷ (Δ[n] : SSet.{u})) ≫ prismFirstContraction n =
      snd (horn 1 1 : SSet.{u}) Δ[n]

def hornOneLastVertex : (horn 1 1 : SSet.{u}) _⦋0⦌

noncomputable def hornOneLastSection (A : SSet.{u}) : A ⟶ (horn 1 1 : SSet.{u}) ⊗ A

lemma hornOneLastSection_ι (A : SSet.{u}) :
    hornOneLastSection A ≫ ((horn 1 1).ι ▷ A) = prismEndpoint 1 A

lemma hornOneLastSection_snd (A : SSet.{u}) :
    hornOneLastSection A ≫ snd (horn 1 1 : SSet.{u}) A = 𝟙 A
```

BoundaryPrism：

```lean
lemma rightFibration_liftBoundaryPrism {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [RightFibration p]
    (a : (boundary n : SSet.{u}) ⟶ E) (ha : a ≫ p = (boundary n).ι) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E,
      prismEndpoint 1 (boundary n : SSet.{u}) ≫ H = a ∧
        H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n

lemma boundaryPrism_zero_comp {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n) :
    (prismEndpoint 0 (boundary n : SSet.{u}) ≫ H) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm 0)

lemma boundaryPrism_fillZero {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n)
    (hc : IsContractibleKan (vertexFiber p (stdSimplex.obj₀Equiv.symm 0))) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ E,
      (boundary n).ι ≫ F = prismEndpoint 0 (boundary n : SSet.{u}) ≫ H ∧
        F ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm 0)
```

Core 対象ビルド：終了コード 0（1586 jobs）。監査：終了コード 0、累計 576 宣言、標準三公理のみ。A3d の逆方向、A3e は引き続き未完了。§4 の設計変更はない。


### A3d 完了：終対象と写像空間の可縮性（2026-10-18）

全写像空間の可縮性から終対象性を導く逆方向を完成。Kerodon Proposition 4.4.2.14 の右ファイブレーション・可縮 fiber 判定を、Lemma 4.4.2.15 の prism 分解と A3b の Joyal の定理で証明した。先頭と境界の和の正則 pairing で、内ホーンと可逆な最初の辺を持つ零番目の外側ホーンを充填する。モデル構造は用いていない。

A3d 全体として、(i) `[Quasicategory X]` の下で終対象性と全右 pinched 写像空間の可縮性の同値、(ii) h X の同型による終対象性の不変性、(iii) h(sliceOver p) の錐の同型による極限性の不変性、(iv) 終対象が存在するとき終対象の全部分複体の可縮 Kan 性を全て達成した。(iv) と同値の順方向には周囲の quasicategory 性は不要。可縮性は全境界の充填であり、π₀ が一点という弱い条件ではない。

今回追加した公開宣言28件の正確な型は以下。共通の `universe w t v u`、`open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty`、`open scoped Simplicial` の下で読む。既存の同型不変性と全部分複体の宣言の型は直前の A3d 保存記録に記載。

VertexFiber：

```lean
lemma rightFibration_isInvertibleEdge_of_constant_image {E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌) (s : E _⦋1⦌)
    (hs : p.app (Opposite.op ⦋1⦌) s = PinchedHom.constant b 1) :
    IsInvertibleEdge (edgeOfSimplex s)
```

CellExtension：

```lean
lemma attachCells_exists_extension {C : Type u} [Category.{v} C]
    {I : Type w} {A B : I → C} {g : ∀ i, A i ⟶ B i}
    {X Y E : C} {j : X ⟶ Y} (c : AttachCells.{t} g j) (f : X ⟶ E)
    (h : ∀ i : c.ι, ∃ F : B (c.π i) ⟶ E,
      g (c.π i) ≫ F = c.cofan₁.inj i ≫ c.g₁ ≫ f) :
    ∃ F : Y ⟶ E, j ≫ F = f

lemma pairing_filtration_exists_extension {X E : SSet.{u}} {A : X.Subcomplex}
    {P : A.Pairing} [P.IsProper] (r : P.RankFunction ℕ) (a : (A : SSet.{u}) ⟶ E)
    (n : ℕ) (g : (r.filtration n : SSet.{u}) ⟶ E)
    (hg : Subcomplex.homOfLE (r.le_filtration n) ≫ g = a)
    (h : ∀ c : r.Cell n, ∃ F : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
      c.horn.ι ≫ F = c.mapHorn ≫ g) :
    ∃ g' : (r.filtration (n + 1) : SSet.{u}) ⟶ E,
      Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫ g' = g ∧
        Subcomplex.homOfLE (r.le_filtration (n + 1)) ≫ g' = a

lemma pairing_exists_extension {X E : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] (a : (A : SSet.{u}) ⟶ E)
    (h : ∀ (n : ℕ) (g : (P.rankFunction.filtration n : SSet.{u}) ⟶ E),
      Subcomplex.homOfLE (P.rankFunction.le_filtration n) ≫ g = a →
      ∀ c : P.rankFunction.Cell n, ∃ F : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
        c.horn.ι ≫ F = c.mapHorn ≫ g) :
    ∃ F : X ⟶ E, A.ι ≫ F = a

lemma pairingCore_cell_index {X : SSet.{u}} {A : X.Subcomplex}
    (Q : A.PairingCore) [Q.IsProper] (r : Q.pairing.RankFunction ℕ) {n : ℕ}
    (s : Q.ι) (hs : r.rank (Q.equivII s) = n) :
    (show r.Cell n from ⟨Q.equivII s, hs⟩).index = Q.index s

lemma pairingCore_cell_map {X : SSet.{u}} {A : X.Subcomplex}
    (Q : A.PairingCore) [Q.IsProper] (r : Q.pairing.RankFunction ℕ) {n : ℕ}
    (s : Q.ι) (hs : r.rank (Q.equivII s) = n) :
    (show r.Cell n from ⟨Q.equivII s, hs⟩).map = SSet.yonedaEquiv.symm (Q.simplex s)
```

PrismPairing：

```lean
lemma prismPairing_first_right_zero (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) :
    (s.x.cast s.hd).simplex.2 (0 : Fin (s.d + 2)) = 0

lemma prismPairing_second_right_zero (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) (hi : s.index = 0) :
    (s.x.cast s.hd).simplex.2 (1 : Fin (s.d + 2)) = 0

def prismFirstVerticalEdge (n : ℕ) : ((Δ[1] : SSet.{u}) ⊗ Δ[n]) _⦋1⦌

lemma prismPairing_firstEdge_eq (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) (hi : s.index = 0) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[n]).map
      (stdSimplex.objEquiv (stdSimplex.edge.{u} (s.d + 1) 0 1 (Fin.zero_le _))).op
        (s.x.cast s.hd).simplex = prismFirstVerticalEdge n

lemma prismFirstVerticalEdge_mem (n : ℕ) :
    prismFirstVerticalEdge.{u} (n + 1) ∈
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).obj (Opposite.op ⦋1⦌)

lemma prismFirstVerticalEdge_contraction (n : ℕ) :
    (prismFirstContraction.{u} n).app (Opposite.op ⦋1⦌) (prismFirstVerticalEdge n) =
      PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1

lemma prismPairing_dim_ge (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) : n ≤ s.d

lemma prismPairing_dim_eq (n : ℕ)
    (s : prodStdSimplex.pairingCore.Type₁.{u} (0 : Fin 1) n) : s.d = n
```

PrismExtension：

```lean
lemma prism_exists_extension_of_invertible_firstEdge {E : SSet.{u}} [Quasicategory E]
    (n : ℕ) (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : IsInvertibleEdge (edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
      ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E,
      (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a
```

SimplexVertexDetection：

```lean
instance stdSimplex_quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u})

lemma stdSimplex_hom_ext_vertices {A : SSet.{u}} {n : ℕ} {f g : A ⟶ (Δ[n] : SSet.{u})}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g

lemma stdSimplex_hom_ext_of_subcomplex_vertices {A : SSet.{u}} {n : ℕ}
    (A₀ : A.Subcomplex) (hA : ∀ v : A _⦋0⦌, v ∈ A₀.obj (Opposite.op ⦋0⦌))
    {f g : A ⟶ (Δ[n] : SSet.{u})} (h : A₀.ι ≫ f = A₀.ι ≫ g) : f = g
```

PrismFilling：

```lean
lemma hornOneFirst_prism_factorization (A : SSet.{u}) :
    ((horn 1 0).ι ▷ A) = snd (horn 1 0 : SSet.{u}) A ≫ prismEndpoint 0 A

lemma prismDomain_contains_vertices (n : ℕ)
    (v : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌) :
    v ∈ (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).obj (Opposite.op ⦋0⦌)

lemma prism_extension_comp {E : SSet.{u}} (n : ℕ) (p : E ⟶ (Δ[n + 1] : SSet.{u}))
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫
      prismFirstContraction (n + 1))
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E)
    (hF : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a) :
    F ≫ p = prismFirstContraction (n + 1)

lemma rightFibration_fillBoundary_over_stdSimplex_succ {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [RightFibration p]
    (hc : IsContractibleKan (vertexFiber p (stdSimplex.obj₀Equiv.symm 0)))
    (b : (boundary (n + 1) : SSet.{u}) ⟶ E) (hb : b ≫ p = (boundary (n + 1)).ι) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ E, (boundary (n + 1)).ι ≫ f = b ∧ f ≫ p = 𝟙 _
```

RightFibrationContractible：

```lean
instance rightFibration_pullback_snd {E B A : SSet.{u}} (p : E ⟶ B) (f : A ⟶ B)
    [RightFibration p] : RightFibration (pullback.snd p f)

lemma vertexFiber_pullback_isContractibleKan {E B A : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (b : A _⦋0⦌)
    (hc : IsContractibleKan (vertexFiber p (f.app (Opposite.op ⦋0⦌) b))) :
    IsContractibleKan (vertexFiber (pullback.snd p f) b)

lemma rightFibration_fillBoundary_over_stdSimplex {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{u})) [RightFibration p]
    (hc : IsContractibleKan (vertexFiber p (stdSimplex.obj₀Equiv.symm 0)))
    (a : (boundary n : SSet.{u}) ⟶ E) (ha : a ≫ p = (boundary n).ι) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ E, (boundary n).ι ≫ F = a ∧ F ≫ p = 𝟙 _

lemma rightFibration_trivialKanFibration_of_contractible_fibers {E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (hc : ∀ b : B _⦋0⦌, IsContractibleKan (vertexFiber p b)) :
    TrivialKanFibration p
```

TerminalMappingSpace：

```lean
lemma isTerminalVertex_of_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (h : ∀ z : X _⦋0⦌, IsContractibleKan (pinchedHom z x)) :
    IsTerminalVertex x

lemma isTerminalVertex_iff_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) : IsTerminalVertex x ↔
      ∀ z : X _⦋0⦌, IsContractibleKan (pinchedHom z x)
```

Core 対象ビルド：終了コード 0（1593 jobs）。監査：終了コード 0、累計 604 宣言、標準三公理のみ。A3a–d 完了。A3e は未完了、A3f は任意、A3g は保留。A3 全体の完了時に全体ビルドを行う。§4 の設計変更はない。承認を待たず A3e に進む。


### A3e 前半：写像空間の関手性とホモトピー圏への帰結（2026-10-18）

実装前に README へ文言を記録し、現行 Kerodon §4.8.1・§4.8.3・Theorem 4.8.4.1 と照合した。写像空間の関手性、実際の単体的ホモトピー逆の存在による充満忠実性、本質的全射性、ホモトピー圏での充満忠実性と圏同値を実装した。関手単体集合の同型から代表の可逆辺と実際のホモトピーを得る API も追加。

重要：`IsFullyFaithful.toHoEquivalence` は通常のホモトピー圏の圏同値であり、A3a の `QCatEquivalence` を構成する主定理の代替ではない。充満忠実＋本質的全射から quasicategory の逆射を構成すること、および同値による任意の極限錐の保存・反映は未完了。A3e 完了とは数えない。§4 の設計変更はない。

公開宣言31件の型は以下。共通の `universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet`、`open scoped Simplicial` の下で読む。

MappingSpaceMap：

```lean
lemma pinchedConstant_map {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) (n : ℕ) :
    f.app (Opposite.op ⦋n⦌) (PinchedHom.constant x n) =
      PinchedHom.constant (f.app (Opposite.op ⦋0⦌) x) n

def pinchedSimplexMap {X Y : SSet.{u}} (f : X ⟶ Y) {x y : X _⦋0⦌} {n : ℕ}
    (s : PinchedHom.Simplex x y n) :
    PinchedHom.Simplex (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) n

def pinchedHomMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    pinchedHom x y ⟶ pinchedHom (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)

lemma pinchedHomMap_id {X : SSet.{u}} (x y : X _⦋0⦌) : pinchedHomMap (𝟙 X) x y = 𝟙 _

lemma pinchedHomMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x y : X _⦋0⦌) :
    pinchedHomMap (f ≫ g) x y = pinchedHomMap f x y ≫
      pinchedHomMap g (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)

lemma pinchedHomPiZeroToHom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌)
    (a : SSet.π₀ (pinchedHom x y)) :
    pinchedHomPiZeroToHom (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
      (SSet.mapπ₀ (pinchedHomMap f x y) a) =
        (hoFunctor.map f).toFunctor.map (pinchedHomPiZeroToHom x y a)
```

SimplicialHomotopyEquivalence：

```lean
def simplicialHomotopyVertexEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X _⦋0⦌) :
    SSet.Edge (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) x)

lemma mapPiZero_eq_of_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (a : SSet.π₀ X) : SSet.mapπ₀ f a = SSet.mapπ₀ g a

def IsSimplicialHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop

lemma isSimplicialHomotopyEquivalence_id (X : SSet.{u}) :
    IsSimplicialHomotopyEquivalence (𝟙 X)

lemma IsSimplicialHomotopyEquivalence.mapPiZero_bijective {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsSimplicialHomotopyEquivalence f) : Function.Bijective (SSet.mapπ₀ f)
```

FullyFaithful：

```lean
def IsFullyFaithful {X Y : SSet.{u}} (f : X ⟶ Y) : Prop

def IsEssentiallySurjective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop

lemma isFullyFaithful_id (X : SSet.{u}) : IsFullyFaithful (𝟙 X)

lemma isEssentiallySurjective_id (X : SSet.{u}) : IsEssentiallySurjective (𝟙 X)

lemma IsFullyFaithful.homotopyCategoryMap_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    (x y : X _⦋0⦌) : Function.Bijective
      ((hoFunctor.map f).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
        (SSet.HomotopyCategory.mk (f.app (Opposite.op ⦋0⦌) x) ⟶
          SSet.HomotopyCategory.mk (f.app (Opposite.op ⦋0⦌) y)))

noncomputable def IsFullyFaithful.toHoFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f) :
    (hoFunctor.map f).toFunctor.FullyFaithful

lemma isEssentiallySurjective_iff_hoFunctor {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsEssentiallySurjective f ↔ (hoFunctor.map f).toFunctor.EssSurj

lemma QCatEquivalence.isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsEssentiallySurjective e.hom

lemma IsEssentiallySurjective.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsEssentiallySurjective f) (hg : IsEssentiallySurjective g) :
    IsEssentiallySurjective (f ≫ g)

noncomputable def IsFullyFaithful.toHoEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y}
    (hf : IsFullyFaithful f) (he : IsEssentiallySurjective f) :
    hoFunctor.obj X ≌ hoFunctor.obj Y

noncomputable def FunctorIso.app {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (x : X _⦋0⦌) :
    VertexIso (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) x)
```

FunctorHomotopy：

```lean
lemma functorVertex_injective {X Y : SSet.{u}} :
    Function.Injective (functorVertex (X := X) (Y := Y))

lemma functorVertex_uncurry_zero {X Y : SSet.{u}} (s : ((ihom X).obj Y) _⦋1⦌) :
    functorVertex (SSet.ι₀ ≫ uncurry (SSet.yonedaEquiv.symm s)) =
      ((ihom X).obj Y).δ 1 s

lemma functorVertex_uncurry_one {X Y : SSet.{u}} (s : ((ihom X).obj Y) _⦋1⦌) :
    functorVertex (SSet.ι₁ ≫ uncurry (SSet.yonedaEquiv.symm s)) =
      ((ihom X).obj Y).δ 0 s

def simplicialHomotopyOfFunctorEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)) : SSet.Homotopy f g

noncomputable def FunctorIso.edge {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)

lemma FunctorIso.edge_homMk {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) :
    SSet.Truncated.HomotopyCategory.homMk (FunctorIso.edge e) = e.hom

lemma FunctorIso.edge_isInvertible {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) : IsInvertibleEdge (FunctorIso.edge e)

noncomputable def FunctorIso.simplicialHomotopy {X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) : SSet.Homotopy f g

lemma IsQCatEquivalence.isSimplicialHomotopyEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsQCatEquivalence f) :
    IsSimplicialHomotopyEquivalence f
```

Core 対象ビルド：終了コード 0（1602 jobs）。監査：終了コード 0、累計 635 宣言、標準三公理のみ。A3a–d は完了、A3e は上記の主定理と極限の保存・反映が未完了。A3f は任意、A3g は保留。続行する。


### A3e 続き：同値による終対象の保存・反映（2026-10-18）

関手単体集合の可逆な辺を各頂点で評価する API と、同型な境界図式間で充填の存在を移す prism の補題を実装した。これにより A3a の `QCatEquivalence` が終対象性を保存・反映することを直接証明。さらに Kan 複体間の実際の単体的ホモトピー同値と quasicategory の同値が同値であること、可縮性がこの同値で不変なこと、充満忠実な射が終対象性を反映することを証明した。

未完了：充満忠実＋本質的全射から A3a の逆射と可逆二胞体を構成する主定理、任意の図式の極限錐の保存・反映。終対象の保存・反映だけで極限全体の工程を完成とは数えない。§4 の設計変更はない。以下は共通の `universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、`open scoped Simplicial` の下での公開宣言18件の正確な型。

FunctorEvaluation：

```lean
def evaluateFunctorAt {X Y : SSet.{u}} (x : X _⦋0⦌) : (ihom X).obj Y ⟶ Y

lemma evaluateFunctorAt_functorVertex {X Y : SSet.{u}} (x : X _⦋0⦌) (f : X ⟶ Y) :
    (evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋0⦌) (functorVertex f) =
      f.app (Opposite.op ⦋0⦌) x

lemma evaluateFunctorAt_edge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge (simplicialHomotopyOfFunctorEdge e) x).edge =
      (evaluateFunctorAt (Y := Y) x).app (Opposite.op ⦋1⦌) e.edge

lemma simplicialHomotopyOfFunctorEdge_vertex_isInvertible {X Y : SSet.{u}}
    [Quasicategory Y] {f g : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)) (he : IsInvertibleEdge e) (x : X _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (simplicialHomotopyOfFunctorEdge e) x).toTruncated
```

KanHomotopyEquivalence：

```lean
def functorEdgeOfSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g)

noncomputable def functorIsoOfSimplicialHomotopy {X Y : SSet.{u}} [KanComplex Y]
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) : FunctorIso f g

lemma IsSimplicialHomotopyEquivalence.isQCatEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {f : X ⟶ Y} (hf : IsSimplicialHomotopyEquivalence f) :
    IsQCatEquivalence f

lemma isSimplicialHomotopyEquivalence_iff_isQCatEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence f ↔ IsQCatEquivalence f
```

HomotopyBoundaryExtension：

```lean
lemma prismEndpoint_zero_braiding (A : SSet.{u}) :
    prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₀

lemma prismEndpoint_one_braiding (A : SSet.{u}) :
    prismEndpoint 1 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₁

lemma FunctorIso.exists_boundaryFilling {Y : SSet.{u}} [Quasicategory Y] {n : ℕ}
    {f g : (boundary n : SSet.{u}) ⟶ Y} (e : FunctorIso f g)
    (hf : ∃ F : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ F = f) :
    ∃ G : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ G = g

lemma FunctorIso.boundaryFilling_iff {Y : SSet.{u}} [Quasicategory Y] {n : ℕ}
    {f g : (boundary n : SSet.{u}) ⟶ Y} (e : FunctorIso f g) :
    (∃ F : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ F = f) ↔
      (∃ G : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ G = g)
```

EquivalenceTerminal：

```lean
lemma QCatEquivalence.map_isTerminalVertex {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) : IsTerminalVertex (e.hom.app (Opposite.op ⦋0⦌) x)

lemma QCatEquivalence.isTerminalVertex_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ IsTerminalVertex (e.hom.app (Opposite.op ⦋0⦌) x)

lemma QCatEquivalence.isContractibleKan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) (hX : IsContractibleKan X) :
    IsContractibleKan Y

lemma QCatEquivalence.isContractibleKan_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsContractibleKan X ↔ IsContractibleKan Y

lemma IsSimplicialHomotopyEquivalence.isContractibleKan_iff {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {f : X ⟶ Y} (hf : IsSimplicialHomotopyEquivalence f) :
    IsContractibleKan X ↔ IsContractibleKan Y

lemma IsFullyFaithful.reflects_isTerminalVertex {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {x : X _⦋0⦌} (hx : IsTerminalVertex (f.app (Opposite.op ⦋0⦌) x)) : IsTerminalVertex x
```

Core 対象ビルド：終了コード 0（1607 jobs）。監査：終了コード 0、累計 653 宣言、標準三公理のみ。A3a–d は完了、A3e は上記の主定理と極限一般が未完了。A3f は任意、A3g は保留。続行する。


### A3e 続き：特殊な射の同値・極限と path の準備（2026-10-18）

trivial Kan fibration と inner anodyne 射は、始域・終域が quasicategory なら明示的な逆射と可逆二胞体を持つ。同値の二対三則を実装した。trivial Kan fibration は任意の図式の極限錐を保存・反映する。可逆な辺からなる path の単体集合と端点評価も定義した。Core 対象ビルド成功（1612 jobs）、公開宣言累計687件の公理監査は標準3公理のみ。未完了：一般の充満忠実＋本質的全射の同値判定、および一般の同値による極限の保存・反映。path の端点評価の持ち上げ性も未完了。§4 の変更はない。

以下は namespace `SerrePositivity.InfinityCategories`、`universe u` と `open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、`open scoped Simplicial` の下の新規34宣言の正確な型。型中の型クラスと明示的引数が全ての前提である。

TrivialFibrationEquivalence：

```lean
instance trivialKanFibration_ihom_map {E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration p] (A : SSet.{u}) : TrivialKanFibration ((ihom A).map p)

lemma trivialKanFibration_exists_section {E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration p] : ∃ s : B ⟶ E, s ≫ p = 𝟙 B

noncomputable def qCatEquivalenceOfTrivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    QCatEquivalence E B

lemma isQCatEquivalence_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [TrivialKanFibration p] :
    IsQCatEquivalence p

```

InnerAnodyneEquivalence：

```lean
lemma trivialKanFibration_pre_of_innerAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : innerAnodyneExtensions i) (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration ((pre i).app Y)

lemma innerAnodyne_exists_retraction {A B : SSet.{u}} [Quasicategory A]
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) : ∃ r : B ⟶ A, i ≫ r = 𝟙 A

noncomputable def qCatEquivalenceOfInnerAnodyne {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    QCatEquivalence A B

lemma isQCatEquivalence_of_innerAnodyne {A B : SSet.{u}}
    [Quasicategory A] [Quasicategory B] (i : A ⟶ B) (hi : innerAnodyneExtensions i) :
    IsQCatEquivalence i

```

EquivalenceCalculus：

```lean
lemma IsQCatEquivalence.ofFunctorIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y}
    (hf : IsQCatEquivalence f) (e : FunctorIso f g) : IsQCatEquivalence g

lemma IsQCatEquivalence.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsQCatEquivalence f) (hg : IsQCatEquivalence g) : IsQCatEquivalence (f ≫ g)

lemma IsQCatEquivalence.cancel_left {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsQCatEquivalence f) (hfg : IsQCatEquivalence (f ≫ g)) : IsQCatEquivalence g

lemma IsQCatEquivalence.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsQCatEquivalence g) (hfg : IsQCatEquivalence (f ≫ g)) : IsQCatEquivalence f

lemma IsSimplicialHomotopyEquivalence.comp {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSimplicialHomotopyEquivalence f) (hg : IsSimplicialHomotopyEquivalence g) :
    IsSimplicialHomotopyEquivalence (f ≫ g)

lemma IsFullyFaithful.comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFullyFaithful f) (hg : IsFullyFaithful g) : IsFullyFaithful (f ≫ g)

```

EquivalenceLimits：

```lean
def mapJoinCone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCone p) :
    JoinCone (p ≫ f)

lemma mapJoinCone_eq_sliceOverPostcomp {K X Y : SSet.{u}} (f : X ⟶ Y)
    {p : K ⟶ X} (c : JoinCone p) :
    mapJoinCone f c = (sliceOverPostcomp p f).app (Opposite.op ⦋0⦌) c

lemma mapJoinCone_vertex {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCone p) :
    (mapJoinCone f c).vertex = f.app (Opposite.op ⦋0⦌) c.vertex

instance trivialKanFibration_sliceOverPostcomp {K E B : SSet.{u}} (p : K ⟶ E) (q : E ⟶ B)
    [TrivialKanFibration q] : TrivialKanFibration (sliceOverPostcomp p q)

lemma isLimitCone_iff_mapJoinCone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    {p : K ⟶ E} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone q c)

```

TerminalVertices：

```lean
def fullSubcomplexLift {A X : SSet.{u}} (P : X _⦋0⦌ → Prop) (f : A ⟶ X)
    (hf : ∀ a : A _⦋0⦌, P (f.app (Opposite.op ⦋0⦌) a)) :
    A ⟶ (fullSubcomplexOnVertices X P : SSet.{u})

lemma fullSubcomplexLift_ι {A X : SSet.{u}} (P : X _⦋0⦌ → Prop) (f : A ⟶ X)
    (hf : ∀ a : A _⦋0⦌, P (f.app (Opposite.op ⦋0⦌) a)) :
    fullSubcomplexLift P f hf ≫ (fullSubcomplexOnVertices X P).ι = f

```

EquivalencePath：

```lean
def functorVertexEquiv (X Y : SSet.{u}) : (X ⟶ Y) ≃ ((ihom X).obj Y) _⦋0⦌

lemma functorVertexEquiv_apply {X Y : SSet.{u}} (f : X ⟶ Y) :
    functorVertexEquiv X Y f = functorVertex f

def intervalFunctorVertexEdge {Y : SSet.{u}} (v : ((ihom (Δ[1] : SSet.{u})).obj Y) _⦋0⦌) :
    Y _⦋1⦌

lemma intervalFunctorVertexEdge_functorVertex {Y : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ Y) :
    intervalFunctorVertexEdge (functorVertex f) = SSet.yonedaEquiv f

def IsEquivalencePathVertex {Y : SSet.{u}}
    (v : ((ihom (Δ[1] : SSet.{u})).obj Y) _⦋0⦌) : Prop

def equivalencePath (Y : SSet.{u}) : SSet.{u}

def equivalencePathι (Y : SSet.{u}) : equivalencePath Y ⟶ (ihom (Δ[1] : SSet.{u})).obj Y

def equivalencePathEndpoint (Y : SSet.{u}) (i : Fin 2) : equivalencePath Y ⟶ Y

lemma isEquivalencePathVertex_const {Y : SSet.{u}} (y : Y _⦋0⦌) :
    IsEquivalencePathVertex (functorVertex (SSet.const y : (Δ[1] : SSet.{u}) ⟶ Y))

noncomputable def equivalencePathRefl (Y : SSet.{u}) : Y ⟶ equivalencePath Y

lemma equivalencePathRefl_endpoint (Y : SSet.{u}) (i : Fin 2) :
    equivalencePathRefl Y ≫ equivalencePathEndpoint Y i = 𝟙 Y

lemma intervalFunctorVertexEdge_curry {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (x : A _⦋0⦌) :
    intervalFunctorVertexEdge ((curry H).app (Opposite.op ⦋0⦌) x) =
      H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)

lemma curry_evaluateFunctorAt_interval {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (i : Fin 2) :
    curry H ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = prismEndpoint i A ≫ H

```


### A3e 続き：可逆 path の持ち上げと関手の置換（2026-10-18）

可逆 path の始点評価は trivial Kan fibration。任意の単射上のホモトピーを始点を固定して延長し、全垂直辺の可逆性を保てる。点ごとに可逆なホモトピーの両端から関手単体集合での同型を構成した。関手 f の path による置換は始域への trivial Kan fibration と終点評価を持ち、元の関手の同値性を終点評価の同値性へ還元できる。Core 対象ビルド成功（1616 jobs）、累計710宣言の公理監査は標準3公理のみ。未完了：置換された終点評価の inner fibration 性、充満忠実＋本質的全射から A3a の同値を構成する主定理、一般の同値による極限の保存・反映。§4 の設計変更なし。

新規23公開宣言の名前・正確な型・全前提を以下に記録する。共通の namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、`open scoped Simplicial`。

PrismBoundaryExtension：

```lean
def hornOneFirstVertex : (horn 1 0 : SSet.{u}) _⦋0⦌

noncomputable def hornOneFirstSection (A : SSet.{u}) : A ⟶ (horn 1 0 : SSet.{u}) ⊗ A

lemma hornOneFirstSection_ι (A : SSet.{u}) :
    hornOneFirstSection A ≫ ((horn 1 0).ι ▷ A) = prismEndpoint 0 A

lemma hornOneFirstSection_snd (A : SSet.{u}) :
    hornOneFirstSection A ≫ snd (horn 1 0 : SSet.{u}) A = 𝟙 A

def prismBoundaryFirstVerticalEdge (n : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u})) _⦋1⦌

lemma prismBoundaryFirstVerticalEdge_ι₁ (n : ℕ) :
    (Subcomplex.unionProd.ι₁ (horn 1 0) (boundary (n + 1))).app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n) =
        ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩

lemma prism_extend_boundary_with_endpoint {Y : SSet.{u}} [Quasicategory Y] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ Y)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ = prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (hH : IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ Y,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧ prismEndpoint 0 Δ[n + 1] ≫ F = F₀

```

EquivalencePathLifting：

```lean
instance trivialKanFibration_equivalencePathEndpoint_zero (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration (equivalencePathEndpoint Y 0)

instance equivalencePath_quasicategory (Y : SSet.{u}) [Quasicategory Y] :
    Quasicategory (equivalencePath Y)

lemma equivalenceHomotopy_extend {A B Y : SSet.{u}} [Quasicategory Y]
    (i : A ⟶ B) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (f : B ⟶ Y)
    (h₀ : prismEndpoint 0 A ≫ H = i ≫ f)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 0 B ≫ F = f ∧
      ∀ x : B _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
        (F.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))

```

EquivalencePathIso：

```lean
noncomputable def functorIsoOfTrivialKanFibration {A E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    FunctorIso f g

noncomputable def functorIsoOfEquivalenceHomotopy {A Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    FunctorIso (prismEndpoint 0 A ≫ H) (prismEndpoint 1 A ≫ H)

```

EquivalencePathReplacement：

```lean
instance trivialKanFibration_pullback_snd {E B A : SSet.{u}} (p : E ⟶ B) (f : A ⟶ B)
    [TrivialKanFibration p] : TrivialKanFibration (pullback.snd p f)

noncomputable def equivalencePathReplacement {X Y : SSet.{u}} (f : X ⟶ Y) : SSet.{u}

noncomputable def equivalencePathReplacementProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacement f ⟶ X

instance equivalencePathReplacementProjection_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory Y] (f : X ⟶ Y) : TrivialKanFibration (equivalencePathReplacementProjection f)

instance equivalencePathReplacement_quasicategory {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    Quasicategory (equivalencePathReplacement f)

noncomputable def equivalencePathReplacementMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacement f ⟶ Y

noncomputable def equivalencePathReplacementFunctorIso {X Y : SSet.{u}}
    [Quasicategory Y] (f : X ⟶ Y) :
    FunctorIso (equivalencePathReplacementProjection f ≫ f) (equivalencePathReplacementMap f)

noncomputable def equivalencePathReplacementSection {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ equivalencePathReplacement f

lemma equivalencePathReplacementSection_projection {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacementSection f ≫ equivalencePathReplacementProjection f = 𝟙 X

lemma equivalencePathReplacementSection_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathReplacementSection f ≫ equivalencePathReplacementMap f = f

lemma isQCatEquivalence_iff_equivalencePathReplacementMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    IsQCatEquivalence f ↔ IsQCatEquivalence (equivalencePathReplacementMap f)

```


### A3e 続き：path 置換の inner fibration 性と頂点全射性（2026-10-18）

区間の二端点の図式と、内ホーン上の prism の両端を固定した延長を実装。両端が quasicategory の関手の path による置換の終点評価は inner fibration となる。元の関手が本質的全射なら終点評価は頂点上で全射。Core 対象ビルド成功（1619 jobs）、累計725宣言の公理監査は標準3公理のみ。未完了：充満忠実性から全境界の持ち上げ性への移行、主定理の明示的な逆射、一般の同値による極限錐の保存・反映。§4 の変更なし。

以下は新規15公開宣言の正確な型と全前提。共通の namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet`、`open scoped Simplicial`。

IntervalBoundary：

```lean
lemma boundaryOne_simplex_constant {n : ℕ} (s : (boundary 1 : SSet.{u}) _⦋n⦌)
    (j : Fin (n + 1)) : s.val j = s.val 0

def intervalBoundaryDiagram {A Y : SSet.{u}} (f g : A ⟶ Y) :
    (boundary 1 : SSet.{u}) ⊗ A ⟶ Y

noncomputable def intervalBoundaryEndpoint (i : Fin 2) (A : SSet.{u}) :
    A ⟶ (boundary 1 : SSet.{u}) ⊗ A

lemma intervalBoundaryEndpoint_ι (i : Fin 2) (A : SSet.{u}) :
    intervalBoundaryEndpoint i A ≫ ((boundary 1).ι ▷ A) = prismEndpoint i A

lemma intervalBoundaryDiagram_zero {A Y : SSet.{u}} (f g : A ⟶ Y) :
    intervalBoundaryEndpoint 0 A ≫ intervalBoundaryDiagram f g = f

lemma intervalBoundaryDiagram_one {A Y : SSet.{u}} (f g : A ⟶ Y) :
    intervalBoundaryEndpoint 1 A ≫ intervalBoundaryDiagram f g = g

lemma intervalBoundaryDiagram_naturality {A B Y : SSet.{u}} (i : A ⟶ B) (f g : B ⟶ Y) :
    ((boundary 1 : SSet.{u}) ◁ i) ≫ intervalBoundaryDiagram f g =
      intervalBoundaryDiagram (i ≫ f) (i ≫ g)

lemma intervalBoundaryDiagram_restrict {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    ((boundary 1).ι ▷ A) ≫ H =
      intervalBoundaryDiagram (prismEndpoint 0 A ≫ H) (prismEndpoint 1 A ≫ H)

```

EquivalencePathInnerFibration：

```lean
lemma vertex_mem_horn (n : ℕ) (i : Fin (n + 3)) (v : (Δ[n + 2] : SSet.{u}) _⦋0⦌) :
    v ∈ (horn (n + 2) i).obj (Opposite.op ⦋0⦌)

lemma prism_extend_innerHorn_with_endpoints {Y : SSet.{u}} [Quasicategory Y]
    {n : ℕ} (i : Fin (n + 1)) (h0 : 0 < i) (hn : i < Fin.last n)
    (H : (Δ[1] : SSet.{u}) ⊗ (horn n i : SSet.{u}) ⟶ Y)
    (f g : (Δ[n] : SSet.{u}) ⟶ Y)
    (hf : prismEndpoint 0 (horn n i : SSet.{u}) ≫ H = (horn n i).ι ≫ f)
    (hg : prismEndpoint 1 (horn n i : SSet.{u}) ≫ H = (horn n i).ι ≫ g) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Y,
      (Δ[1] ◁ (horn n i).ι) ≫ F = H ∧
      prismEndpoint 0 Δ[n] ≫ F = f ∧ prismEndpoint 1 Δ[n] ≫ F = g

instance equivalencePathReplacementMap_innerFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    InnerFibration (equivalencePathReplacementMap f)

```

EquivalencePathVertices：

```lean
def equivalencePathVertex {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y)
    (he : IsInvertibleEdge e) : (equivalencePath Y) _⦋0⦌

lemma equivalencePathVertex_zero {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : IsInvertibleEdge e) :
    (equivalencePathEndpoint Y 0).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = x

lemma equivalencePathVertex_one {Y : SSet.{u}} {x y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y) x y) (he : IsInvertibleEdge e) :
    (equivalencePathEndpoint Y 1).app (Opposite.op ⦋0⦌) (equivalencePathVertex e he) = y

lemma IsEssentiallySurjective.equivalencePathReplacementMap_surjective {X Y : SSet.{u}}
    [Quasicategory Y] {f : X ⟶ Y} (hf : IsEssentiallySurjective f) :
    Function.Surjective ((equivalencePathReplacementMap f).app (Opposite.op ⦋0⦌))

```


### A3e 続き：写像空間と coslice の相対的な持ち上げ（2026-10-18）

inner fibration が右 pinched 写像空間上に誘導する射は右ファイブレーションであり、その各頂点上の fiber は Kan 複体となる。coslice の制限と後合成を引き戻しにまとめた相対制限は左ファイブレーションとなる。これらの持ち上げ定理には元の単体集合の quasicategory 性は不要。相対 coslice の標的の quasicategory 性には両端の quasicategory 性を仮定する。Core 対象ビルド成功（1621 jobs）、累計734宣言の標準3公理監査成功。未完了：相対外側ホーンの充填、充満忠実性から写像空間の fiber の可縮性への移行、主同値判定、一般の同値による極限の保存・反映。§4 の設計変更はない。

以下は新規9公開宣言の正確な型と全前提。共通の namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits SSet`、`open scoped Simplicial`。

MappingSpaceFibration：

```lean
lemma pinchedHomMap_rightHornFilling {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (hi : 0 < i)
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ pinchedHom x y)
    (hf : horn.IsCompatible f)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ pinchedHom
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y))
    (hb : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      f j hj ≫ pinchedHomMap p x y = stdSimplex.δ j ≫ b) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ pinchedHom x y,
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ F = f j hj) ∧
      F ≫ pinchedHomMap p x y = b

instance pinchedHomMap_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) : RightFibration (pinchedHomMap p x y)

lemma pinchedHomMap_vertexFiber_kanComplex {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) (s : (pinchedHom
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) :
    KanComplex (vertexFiber (pinchedHomMap p x y) s)

```

RelativeCoslice：

```lean
noncomputable def relativeCosliceTarget {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (K₀ : K.Subcomplex) : SSet.{u}

noncomputable def relativeCosliceMap {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (K₀ : K.Subcomplex) : sliceUnder p ⟶ relativeCosliceTarget p q K₀

lemma relativeCosliceMap_hasLiftingProperty {A K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hA : leftAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (relativeCosliceMap p q K₀)

instance relativeCosliceMap_leftFibration {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    [InnerFibration q] (K₀ : K.Subcomplex) : LeftFibration (relativeCosliceMap p q K₀)

instance leftFibration_pullback_fst {E B A : SSet.{u}} (p : A ⟶ B) (q : E ⟶ B)
    [LeftFibration q] : LeftFibration (pullback.fst p q)

instance relativeCosliceTarget_quasicategory {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) :
    Quasicategory (relativeCosliceTarget p q K₀)

```


### A3e 続き：相対 Joyal 充填と全ホーンの持ち上げ（2026-10-18）

inner fibration は始域・終域が quasicategory のとき、始域で指定辺が可逆な先頭・末尾の外側ホーンを、指定した標的の単体へ厳密に持ち上げる。Kan 複体間の右ファイブレーションは全てのホーンを持ち上げる。従って quasicategory 間の inner fibration が右 pinched 写像空間上に誘導する射も全ホーンの rlp を持つ。Mathlib の `HomotopicalAlgebra.Fibration` への接続はホーンの rlp という定義だけを使用し、Kan–Quillen モデル構造・弱同値・モデル圏による因子分解は使用しない。同値である Fibration は厳密な切断を持つことも構成した。Core 対象ビルド成功（1624 jobs）、累計748宣言の標準3公理監査成功。未完了：写像空間のホモトピー同値と全ホーンの rlp から fiber の可縮性への移行、充満忠実＋本質的全射による主同値判定、一般の同値による極限の保存・反映。§4 の設計変更はない。

以下は新規14公開宣言の正確な型と全前提。namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra`、`open scoped Simplicial`。最後の KanFibrationTools の型では、Mathlib がホーンの rlp と定義するクラスの scoped instance を有効にする `open SSet.modelCategoryQuillen` を用いる。

RelativeOuterHorn：

```lean
lemma joinUnion_lift_of_invertible_rightEdge {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) [InnerFibration q]
    (K₀ : K.Subcomplex) (T : (joinUnion K₀ (horn 1 1) : SSet.{u}) ⟶ X)
    (W : join K (Δ[1] : SSet.{u}) ⟶ Y)
    (hTW : T ≫ q = (joinUnion K₀ (horn 1 1)).ι ≫ W)
    (he : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (joinInr (K₀ : SSet.{u}) Δ[1] ≫
        joinUnionLeft K₀ (horn 1 1) ≫ T)))) :
    ∃ L : join K (Δ[1] : SSet.{u}) ⟶ X, (joinUnion K₀ (horn 1 1)).ι ≫ L = T ∧ L ≫ q = W

lemma innerFibration_lift_finalHorn {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [InnerFibration q] (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X)
    (β : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hσq : σ ≫ q = (horn (n + 2) (Fin.last (n + 2))).ι ≫ β)
    (he : IsInvertibleEdge (edgeOfSimplex
      (σ.app (Opposite.op ⦋1⦌) (finalHornEdge n)))) :
    ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X,
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = σ ∧ F ≫ q = β

```

RelativeOuterHornOp：

```lean
instance innerFibration_op {X Y : SSet.{u}} (q : X ⟶ Y) [InnerFibration q] :
    InnerFibration (SSet.opFunctor.map q)

lemma reverseSimplex_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective (reverseSimplex (X := X) n)

lemma innerFibration_lift_initialHorn {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [InnerFibration q] (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X)
    (β : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hσq : σ ≫ q = (horn (n + 2) 0).ι ≫ β)
    (he : IsInvertibleEdge (edgeOfSimplex
      (σ.app (Opposite.op ⦋1⦌) (initialHornEdge n)))) :
    ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X,
      (horn (n + 2) 0).ι ≫ F = σ ∧ F ≫ q = β

instance rightFibration_op_leftFibration {X Y : SSet.{u}} (q : X ⟶ Y) [RightFibration q] :
    LeftFibration (SSet.opFunctor.map q)

lemma rightFibration_liftHorn_one_zero {X Y : SSet.{u}} [Quasicategory Y]
    (q : X ⟶ Y) [RightFibration q] (a : (horn 1 0 : SSet.{u}) ⟶ X)
    (b : (Δ[1] : SSet.{u}) ⟶ Y) (sq : CommSq a (horn 1 0).ι q b)
    (hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv b))) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X, (horn 1 0).ι ≫ F = a ∧ F ≫ q = b

lemma rightFibration_hasLiftingProperty_horn_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [RightFibration q]
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι q

```

MappingSpaceFibration：

```lean
lemma pinchedHomMap_hasLiftingProperty_horn {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι (pinchedHomMap p x y)

```

KanFibrationTools：

```lean
lemma fibration_of_hasLiftingProperty_horn {X Y : SSet.{u}} (q : X ⟶ Y)
    (h : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty (horn (n + 1) i).ι q) :
    Fibration q

instance fibration_leftFibration {X Y : SSet.{u}} (q : X ⟶ Y) [Fibration q] :
    LeftFibration q

instance rightFibration_fibration_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [RightFibration q] : Fibration q

lemma fibration_exists_section_of_isQCatEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) : ∃ s : B ⟶ E, s ≫ p = 𝟙 B

lemma IsQCatEquivalence.functorIsoOfSection {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {p : E ⟶ B} (he : IsQCatEquivalence p)
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) : Nonempty (FunctorIso (p ≫ s) (𝟙 E))

```


### A3e 続き：同値である Fibration の境界充填と写像空間の可縮な fiber（2026-10-18）

quasicategory 間の Fibration が A3a の同値なら trivial Kan fibration となることを直接証明した。厳密な切断を選び、切断で戻した辺と元の辺の退化三角形を持ち上げ、射影が恒等辺である単位の辺を構成する。その実際の fiber 内のホモトピーと相対 prism の持ち上げで任意の境界を充填する。従って、充満忠実な inner fibration が右 pinched 写像空間上に誘導する射は trivial Kan fibration であり、各 fiber は可縮な Kan 複体。Core 対象ビルド成功（1629 jobs）、累計756宣言の標準3公理監査成功。未完了：写像空間の基底変換と標準単体上の境界の持ち上げ、一般の充満忠実＋本質的全射による同値判定、一般の同値による極限の保存・反映。§4 の設計変更なし。

新規8公開宣言の正確な型・全前提を以下に記録する。共通の namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet HomotopicalAlgebra`、`open SSet.modelCategoryQuillen`、`open scoped Simplicial`。Fibration はホーンの rlp という既存の定義だけを使い、モデル構造・弱同値は使わない。

FiberEdgeCorrection：

```lean
lemma leftFibration_correct_edge_over_identity {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) {x y : E _⦋0⦌}
    (h : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (hx : s.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) x) = x)
    (hy : s.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) y) = x)
    (hxy : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      p.app (Opposite.op ⦋1⦌) k.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
          (p.app (Opposite.op ⦋0⦌) y)).edge

```

FiberwiseHomotopy：

```lean
lemma fibration_exists_section_and_relativeFunctorEdge {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B ∧
      ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
        (functorVertex (p ≫ s)) (functorVertex (𝟙 E)),
        ((ihom E).map p).app (Opposite.op ⦋1⦌) k.edge =
          (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom E).obj B))
            (functorVertex p)).edge

lemma simplicialHomotopyOfFunctorEdge_comp_eq_constant {A E B : SSet.{u}}
    {f g : A ⟶ E} (p : E ⟶ B) (b : A ⟶ B)
    (k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj E))
      (functorVertex f) (functorVertex g))
    (hk : ((ihom A).map p).app (Opposite.op ⦋1⦌) k.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj B))
        (functorVertex b)).edge) :
    (simplicialHomotopyOfFunctorEdge k).h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ b

```

KanPrismLifting：

```lean
lemma fibration_lift_prism {A E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    (A₀ : A.Subcomplex) (H : (Δ[1] : SSet.{u}) ⊗ (A₀ : SSet.{u}) ⟶ E)
    (F₀ : A ⟶ E) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hF₀ : A₀.ι ≫ F₀ = prismEndpoint 0 (A₀ : SSet.{u}) ≫ H)
    (hH : H ≫ q = (Δ[1] ◁ A₀.ι) ≫ b)
    (hb : F₀ ≫ q = prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      (Δ[1] ◁ A₀.ι) ≫ F = H ∧ prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ q = b

```

KanFibrationEquivalence：

```lean
lemma trivialKanFibration_of_fibration_of_isQCatEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) : TrivialKanFibration p

lemma trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (he : IsSimplicialHomotopyEquivalence p) : TrivialKanFibration p

```

FullyFaithfulFibration：

```lean
lemma IsFullyFaithful.pinchedHomMap_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : IsFullyFaithful p) (x y : X _⦋0⦌) : TrivialKanFibration (pinchedHomMap p x y)

lemma IsFullyFaithful.pinchedHomMap_vertexFiber_isContractibleKan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : IsFullyFaithful p) (x y : X _⦋0⦌)
    (s : (pinchedHom (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (pinchedHomMap p x y) s)

```


### Π2 対応：始対象 cofinality の二宇宙化（2026-10-18）

A3e を一時中断し、`initialCofinality`・`initialRestriction` と nerve の頂点・始対象の錐・retract の補題を、既存名のまま `{I : Type v} [Category.{w} I]` へ一般化した。nerve と全ての join・slice は `SSet.{max v w}` に置く。旧来の同一宇宙は v=w の特殊化となる。対象 Type (u+1)・Hom Type u の場合は `nerve I : SSet.{u+1}`、図式の標的も `X : SSet.{u+1}` として使用できる。`PerfUnder_u p S` の内部や他レーンのファイルは変更していない。

検証：`lake build SerrePositivity.InfinityCategories.Core` 成功（1629 jobs）。その完了後に `lake env lean scripts/audit_infinity_core.lean` 成功、累計756宣言は標準3公理のみ。監査スクリプトには一般二宇宙・Type (u+1)/Hom Type u・従来の同一宇宙の三つの型検査例を追加した。新名・公理・sorry は追加していない。今回の要請に未完了箇所はなく、A3e の作業に戻る。A3e の主同値判定と一般の極限不変性は引き続き未完了。§4 の設計変更なし。

一般化した公開19宣言の正確な型と全前提は以下。namespace は `SerrePositivity.InfinityCategories`、`universe u v w`、`open CategoryTheory Limits SSet`、`open scoped Simplicial`。

NerveCone：

```lean
def nerveVertex {I : Type v} [Category.{w} I] (c : I) : (nerve I) _⦋0⦌

def nervePoint {I : Type v} [Category.{w} I] (c : I) : (Δ[0] : SSet.{max v w}) ⟶ nerve I

noncomputable def initialChain {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : ComposableArrows I n) : ComposableArrows I (n + 1)

lemma initialChain_naturality {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op (initialChain hc F) =
      initialChain hc ((nerve I).map α.op F)

lemma initialChain_tail {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) : (nerve I).δ 0 (initialChain hc F) = F

lemma initialChain_vertex {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (initialChain hc F) = nerveVertex c

noncomputable def nerveInitialConeSimplex {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) {n : ℕ} (F : (nerve I) _⦋n⦌) : (sliceUnder (nervePoint c)) _⦋n⦌

noncomputable def nerveInitialSection {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nerve I ⟶ sliceUnder (nervePoint c)

lemma nerveInitialSection_projection {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nerveInitialSection hc ≫ sliceUnderProjection (nervePoint c) = 𝟙 (nerve I)

noncomputable def nerveInitialCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    join (Δ[0] : SSet.{max v w}) (nerve I) ⟶ nerve I

lemma nerveInitialCone_inr {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    joinInr (Δ[0] : SSet.{max v w}) (nerve I) ≫ nerveInitialCone hc = 𝟙 (nerve I)

lemma initialChain_self {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    initialChain hc (nerveVertex c) = (nerve I).σ 0 (nerveVertex c)

lemma nerveInitialSection_at_point {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nervePoint c ≫ nerveInitialSection hc =
      (SSet.yonedaEquiv (X := sliceUnder (nervePoint c))).symm
        (cosliceIdentityCone (nerveVertex c))

lemma nerveInitialCone_at_point {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    joinMap (𝟙 (Δ[0] : SSet.{max v w})) (nervePoint c) ≫ nerveInitialCone hc =
      SSet.const (nerveVertex c)

instance nervePoint_mono {I : Type v} [Category.{w} I] (c : I) : Mono (nervePoint c)

noncomputable def nervePointRetract {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    RetractArrow (nervePoint c) (joinMap (𝟙 (Δ[0] : SSet.{max v w})) (nervePoint c))

lemma nervePoint_leftAnodyne {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    leftAnodyneExtensions (nervePoint c)

```

InitialCofinality：

```lean
def initialRestriction {I : Type v} [Category.{w} I] {X : SSet.{max v w}}
    (F : nerve I ⟶ X) (c : I) : sliceOver F ⟶ sliceOver (nervePoint c ≫ F)

lemma initialCofinality {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    TrivialKanFibration (initialRestriction F c)

```


### A3e 続き：充満忠実な inner fibration の境界充填（2026-10-18）

Mathlib の引き戻しの単体と右 pinched 写像空間の基底変換を実装。充満忠実な inner fibration の quasicategory への引き戻しは充満忠実である。標準単体の最後の頂点の終対象性を写像空間の各次数の一意性と非空性で証明し、標準単体への基底変換で終対象性を反映することにより、充満忠実な inner fibration の全正次元境界の持ち上げ性を証明した。頂点上の全射性を加えれば trivial Kan fibration であり A3a の同値となる。これは一般の本質的全射な関手の判定を完成したものではない。Core 対象ビルド成功（1634 jobs）、累計781宣言の標準3公理監査成功。未完了：一般の関手の path 置換への充満忠実性の移行と主同値判定、一般の同値による極限の保存・反映。§4 の設計変更なし。

新規25公開宣言の正確な型と全前提を以下に記録する。namespace は `SerrePositivity.InfinityCategories`、`universe u`、`open CategoryTheory Limits SSet`、`open scoped Simplicial`。

PullbackSimplex：

```lean
noncomputable def pullbackSimplex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback p q) _⦋n⦌

lemma pullbackSimplex_fst {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback.fst p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h) = x

lemma pullbackSimplex_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y) :
    (pullback.snd p q).app (Opposite.op ⦋n⦌) (pullbackSimplex p q x y h) = y

lemma pullbackSimplex_ext {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    {x y : (pullback p q) _⦋n⦌}
    (hf : (pullback.fst p q).app (Opposite.op ⦋n⦌) x = (pullback.fst p q).app (Opposite.op ⦋n⦌) y)
    (hs : (pullback.snd p q).app (Opposite.op ⦋n⦌) x = (pullback.snd p q).app (Opposite.op ⦋n⦌) y) :
    x = y

lemma pullbackSimplex_compat {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : (pullback p q) _⦋n⦌) :
    p.app (Opposite.op ⦋n⦌) ((pullback.fst p q).app (Opposite.op ⦋n⦌) x) =
      q.app (Opposite.op ⦋n⦌) ((pullback.snd p q).app (Opposite.op ⦋n⦌) x)

lemma pullbackSimplex_eta {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n : ℕ}
    (x : (pullback p q) _⦋n⦌) :
    pullbackSimplex p q ((pullback.fst p q).app (Opposite.op ⦋n⦌) x)
      ((pullback.snd p q).app (Opposite.op ⦋n⦌) x) (pullbackSimplex_compat p q x) = x

lemma pullbackSimplex_map {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) {n m : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (y : Y _⦋n⦌)
    (h : p.app (Opposite.op ⦋n⦌) x = q.app (Opposite.op ⦋n⦌) y)
    (h' : p.app (Opposite.op ⦋m⦌) (X.map α.op x) = q.app (Opposite.op ⦋m⦌) (Y.map α.op y)) :
    (pullback p q).map α.op (pullbackSimplex p q x y h) =
      pullbackSimplex p q (X.map α.op x) (Y.map α.op y) h'

```

MappingSpacePullback：

```lean
noncomputable def pinchedPullbackSimplex {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ}
    (x : (pinchedHom ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)) _⦋n⦌)
    (y : (pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w)) _⦋n⦌)
    (h : p.app (Opposite.op ⦋n + 1⦌) x.val = q.app (Opposite.op ⦋n + 1⦌) y.val) :
    (pinchedHom v w) _⦋n⦌

lemma pinchedPullbackSimplex_fst {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ} (x y) (h) :
    (pinchedHomMap (pullback.fst p q) v w).app (Opposite.op ⦋n⦌)
      (pinchedPullbackSimplex p q v w x y h) = x

lemma pinchedPullbackSimplex_snd {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {n : ℕ} (x y) (h) :
    (pinchedHomMap (pullback.snd p q) v w).app (Opposite.op ⦋n⦌)
      (pinchedPullbackSimplex p q v w x y h) = y

noncomputable def pinchedHomPullbackLift {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌)
    (f : A ⟶ pinchedHom ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))
    (g : A ⟶ pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w))
    (hc : ∀ (n : ℕ) (a : A _⦋n⦌),
      p.app (Opposite.op ⦋n + 1⦌) (f.app (Opposite.op ⦋n⦌) a).val =
        q.app (Opposite.op ⦋n + 1⦌) (g.app (Opposite.op ⦋n⦌) a).val) :
    A ⟶ pinchedHom v w

lemma pinchedHomPullbackLift_fst {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) p q v w f g hc ≫ pinchedHomMap (pullback.fst p q) v w = f

lemma pinchedHomPullbackLift_snd {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) p q v w f g hc ≫ pinchedHomMap (pullback.snd p q) v w = g

lemma pinchedHomPullback_hom_ext {A X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) {f g : A ⟶ pinchedHom v w}
    (hf : f ≫ pinchedHomMap (pullback.fst p q) v w = g ≫ pinchedHomMap (pullback.fst p q) v w)
    (hs : f ≫ pinchedHomMap (pullback.snd p q) v w = g ≫ pinchedHomMap (pullback.snd p q) v w) :
    f = g

```

FullyFaithfulBaseChange：

```lean
noncomputable def pinchedHomPullbackBaseMap {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w) ⟶
    pinchedHom (p.app (Opposite.op ⦋0⦌) ((pullback.fst p q).app (Opposite.op ⦋0⦌) v))
      (p.app (Opposite.op ⦋0⦌) ((pullback.fst p q).app (Opposite.op ⦋0⦌) w))

lemma pinchedHomPullbackBaseMap_comm {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    pinchedHomMap (pullback.fst p q) v w ≫
        pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
          ((pullback.fst p q).app (Opposite.op ⦋0⦌) w) =
      pinchedHomMap (pullback.snd p q) v w ≫ pinchedHomPullbackBaseMap p q v w

lemma IsFullyFaithful.pinchedHomMap_pullback_snd_trivialKanFibration {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B] {p : X ⟶ B} [InnerFibration p]
    (hp : IsFullyFaithful p) (q : Y ⟶ B) (v w : (pullback p q) _⦋0⦌) :
    TrivialKanFibration (pinchedHomMap (pullback.snd p q) v w)

lemma IsFullyFaithful.pullback_snd {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B] [Quasicategory Y] {p : X ⟶ B} [InnerFibration p]
    (hp : IsFullyFaithful p) (q : Y ⟶ B) : IsFullyFaithful (pullback.snd p q)

```

StdSimplexTerminal：

```lean
lemma isContractibleKan_of_nonempty_of_degreewise_subsingleton (K : SSet.{u})
    (hne : Nonempty (K _⦋0⦌)) (hs : ∀ n : ℕ, Subsingleton (K _⦋n⦌)) :
    IsContractibleKan K

instance pinchedHom_stdSimplex_subsingleton {n : ℕ} (a b : (Δ[n] : SSet.{u}) _⦋0⦌)
    (m : ℕ) : Subsingleton ((pinchedHom a b) _⦋m⦌)

lemma pinchedHom_stdSimplex_last_nonempty {n : ℕ} (a : (Δ[n] : SSet.{u}) _⦋0⦌) :
    Nonempty ((pinchedHom a (stdSimplex.obj₀Equiv.symm (Fin.last n))) _⦋0⦌)

lemma stdSimplex_last_isTerminalVertex (n : ℕ) :
    IsTerminalVertex (X := (Δ[n] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (Fin.last n))

```

FullyFaithfulBoundary：

```lean
lemma IsFullyFaithful.hasLiftingProperty_boundary_succ {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : IsFullyFaithful p) (n : ℕ) : HasLiftingProperty (boundary (n + 1)).ι p

lemma IsFullyFaithful.trivialKanFibration_of_surjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : IsFullyFaithful p) (hs : Function.Surjective (p.app (Opposite.op ⦋0⦌))) :
    TrivialKanFibration p

lemma IsFullyFaithful.isQCatEquivalence_of_surjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y} [InnerFibration p]
    (hp : IsFullyFaithful p) (hs : Function.Surjective (p.app (Opposite.op ⦋0⦌))) :
    IsQCatEquivalence p

```


### A3e 続き：pinched 普遍性・trivial fibration の充満忠実性・消去則（2026-10-18）

任意のパラメーターに対する右 pinched 写像空間の普遍性と後合成の自然性を実装。trivial Kan fibration が誘導する写像空間の射は trivial Kan fibration となり、quasicategory 間では充満忠実。Kan 複体のホモトピー同値の左右消去則と充満忠実な後合成による検出も成立する。公開18宣言の正確な型と全前提は以下。Core ビルド1637 jobs、公開宣言799件の監査成功、標準3公理のみ。一般の関手の path 置換への充満忠実性の移行、主同値判定、一般の同値による極限不変性は未完了。

PinchedUniversal：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
noncomputable def pinchedHomUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) : join A (Δ[0] : SSet.{u}) ⟶ X

lemma pinchedHomUncurry_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) : joinInl A Δ[0] ≫ pinchedHomUncurry f = SSet.const x

lemma pinchedHomUncurry_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    joinInr A Δ[0] ≫ pinchedHomUncurry f = SSet.yonedaEquiv.symm y

noncomputable def pinchedHomCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) : A ⟶ pinchedHom x y

lemma pinchedHomUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) :
    pinchedHomUncurry (pinchedHomCurry F hx hy) = F

lemma pinchedHomUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (pinchedHomUncurry (A := A) (x := x) (y := y))

lemma pinchedHomCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    pinchedHomCurry (pinchedHomUncurry f) (pinchedHomUncurry_inl f) (pinchedHomUncurry_inr f) = f

lemma pinchedHomUncurry_precomp {A C X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ C) (f : C ⟶ pinchedHom x y) :
    pinchedHomUncurry (i ≫ f) = joinMap i (𝟙 Δ[0]) ≫ pinchedHomUncurry f

lemma pinchedHomSliceFiberIso_inv_app {X : SSet.{u}} (x y : X _⦋0⦌) {n : ℕ}
    (s : (vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌) :
    (pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌) s = fiberSimplexToPinched s

lemma pinchedHomCurry_postcomp {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (F : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) (p : X ⟶ Y)
    (hx' : joinInl A Δ[0] ≫ (F ≫ p) = SSet.const (p.app (Opposite.op ⦋0⦌) x))
    (hy' : joinInr A Δ[0] ≫ (F ≫ p) = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) y)) :
    pinchedHomCurry F hx hy ≫ pinchedHomMap p x y = pinchedHomCurry (F ≫ p) hx' hy'

lemma pinchedHomUncurry_postcomp {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) (p : X ⟶ Y) :
    pinchedHomUncurry (f ≫ pinchedHomMap p x y) = pinchedHomUncurry f ≫ p

end SerrePositivity.InfinityCategories
```

MappingSpaceTrivialFibration：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma pinchedHomMap_hasLiftingProperty_of_trivialKanFibration {A X Y : SSet.{u}}
    (p : X ⟶ Y) [TrivialKanFibration p] (x y : X _⦋0⦌) (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (pinchedHomMap p x y)

instance pinchedHomMap_trivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] (x y : X _⦋0⦌) : TrivialKanFibration (pinchedHomMap p x y)

lemma isFullyFaithful_of_trivialKanFibration {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [TrivialKanFibration p] : IsFullyFaithful p

end SerrePositivity.InfinityCategories
```

FullyFaithfulCalculus：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma IsSimplicialHomotopyEquivalence.cancel_right {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsSimplicialHomotopyEquivalence g) (hfg : IsSimplicialHomotopyEquivalence (f ≫ g)) :
    IsSimplicialHomotopyEquivalence f

lemma IsSimplicialHomotopyEquivalence.cancel_left {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSimplicialHomotopyEquivalence f) (hfg : IsSimplicialHomotopyEquivalence (f ≫ g)) :
    IsSimplicialHomotopyEquivalence g

lemma IsFullyFaithful.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsFullyFaithful g) (hfg : IsFullyFaithful (f ≫ g)) : IsFullyFaithful f

lemma isFullyFaithful_comp_iff {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsFullyFaithful g) : IsFullyFaithful (f ≫ g) ↔ IsFullyFaithful f

end SerrePositivity.InfinityCategories
```


### A3e 主同値判定：充満忠実かつ本質的全射な関手（2026-10-18）

prism の反転によって可逆 path の終点評価も trivial Kan fibration と証明。関手同型による充満忠実性の不変性を経て、一般の充満忠実かつ本質的全射な関手に実際の逆射と関手単体集合の可逆二胞体を構成した。主同値判定は完了。A3e 全体では一般の同値による任意の極限錐の保存・反映が未完了。公開18宣言の全ての型・前提は以下。Core ビルド1641 jobs、累計817宣言の標準3公理監査成功。既存の公開名・型は変更していない。今後の担当順は foundations.md に従い A3e → A6（HTT 5.1.2.2）→ A4・A5、F1 は α2 が担当。

PrismOpposite：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
def opTensorIso (A B : SSet.{u}) : A.op ⊗ B.op ≅ (A ⊗ B).op

def reversePrism {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op

lemma reversePrism_precomp {A B Y : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y) :
    reversePrism ((Δ[1] ◁ i) ≫ H) = (Δ[1] ◁ SSet.opFunctor.map i) ≫ reversePrism H

lemma reversePrism_postcomp {A Y Z : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (p : Y ⟶ Z) : reversePrism (H ≫ p) = reversePrism H ≫ SSet.opFunctor.map p

lemma reversePrism_endpoint {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (i : Fin 2) : prismEndpoint i A.op ≫ reversePrism H =
      SSet.opFunctor.map (prismEndpoint i.rev A ≫ H)

lemma reversePrism_double {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) :
    reversePrism (reversePrism H) ≫ (SSet.opFunctorCompOpFunctorIso.app Y).hom =
      (Δ[1] ◁ (SSet.opFunctorCompOpFunctorIso.app A).hom) ≫ H

lemma reversePrism_vertical_isInvertible {A Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))))
    (x : A.op _⦋0⦌) : IsInvertibleEdge (edgeOfSimplex
      ((reversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))

def unreversePrism {A Y : SSet.{u}} (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op) :
    (Δ[1] : SSet.{u}) ⊗ A ⟶ Y

lemma unreversePrism_reversePrism {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) : unreversePrism (reversePrism H) = H

lemma unreversePrism_precomp {A B Y : SSet.{u}} (i : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ B.op ⟶ Y.op) :
    unreversePrism ((Δ[1] ◁ SSet.opFunctor.map i) ≫ H) =
      (Δ[1] ◁ i) ≫ unreversePrism H

lemma unreversePrism_endpoint {A Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A.op ⟶ Y.op) (i : Fin 2) :
    prismEndpoint i A ≫ unreversePrism H =
      (SSet.opFunctorCompOpFunctorIso.app A).inv ≫
        SSet.opFunctor.map (prismEndpoint i.rev A.op ≫ H) ≫
          (SSet.opFunctorCompOpFunctorIso.app Y).hom

end SerrePositivity.InfinityCategories
```

EquivalencePathFinalLifting：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma equivalenceHomotopy_extend_final {A B Y : SSet.{u}} [Quasicategory Y]
    (i : A ⟶ B) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y) (f : B ⟶ Y)
    (h₁ : prismEndpoint 1 A ≫ H = i ≫ f)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 1 B ≫ F = f

instance trivialKanFibration_equivalencePathEndpoint_one (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration (equivalencePathEndpoint Y 1)

end SerrePositivity.InfinityCategories
```

FullyFaithfulIso：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma isFullyFaithful_iff_of_equivalenceHomotopy {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    IsFullyFaithful (prismEndpoint 0 A ≫ H) ↔ IsFullyFaithful (prismEndpoint 1 A ≫ H)

lemma FunctorIso.isFullyFaithful_iff {A Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y] {f g : A ⟶ Y} (e : FunctorIso f g) :
    IsFullyFaithful f ↔ IsFullyFaithful g

end SerrePositivity.InfinityCategories
```

FullyFaithfulEquivalence：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma IsFullyFaithful.equivalencePathReplacementMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f) :
    IsFullyFaithful (equivalencePathReplacementMap f)

lemma isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : IsFullyFaithful f) (he : IsEssentiallySurjective f) : IsQCatEquivalence f

noncomputable def qCatEquivalenceOfFullyFaithfulEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (hf : IsFullyFaithful f) (he : IsEssentiallySurjective f) : QCatEquivalence X Y

end SerrePositivity.InfinityCategories
```


### A3e 完了：同値判定の両方向と任意の極限錐の保存・反映（2026-10-18）

`IsQCatEquivalence f ↔ IsFullyFaithful f ∧ IsEssentiallySurjective f` を、全ての右 pinched 写像空間の実際のホモトピー同値の意味で証明した。任意の単体集合 K、図式 p : K ⟶ X、錐 c : JoinCone p について、同値 f は `IsLimitCone c ↔ IsLimitCone (mapJoinCone f c)` を満たす。path 置換の二つの射影が trivial Kan fibration となり、元の関手はその厳密な切断と終点射に分解されることを用いた。追加公理・sorry・モデル構造は使わない。公開10宣言の正確な型・全前提は以下。

検証：`lake build SerrePositivity.InfinityCategories.Core` 成功（1644 jobs）、`lake env lean scripts/audit_infinity_core.lean` 成功（累計827宣言、標準3公理のみ）、工程区切りの全体 `lake build` も成功（7911 jobs）。A3a–e の必須項目は完了。A3f は任意項目として未完了、A3g は指示どおり保留。A6 と A4・A5 はこの保存単位では未着手。既存の公開名・型は変更していない。

EquivalenceTwoOfSix：

```lean
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma isQCatEquivalence_of_composites {A B C D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : IsQCatEquivalence (f ≫ g)) (hgh : IsQCatEquivalence (g ≫ h)) :
    IsQCatEquivalence g

lemma isSimplicialHomotopyEquivalence_of_composites {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : IsSimplicialHomotopyEquivalence (f ≫ g))
    (hgh : IsSimplicialHomotopyEquivalence (g ≫ h)) :
    IsSimplicialHomotopyEquivalence g

end SerrePositivity.InfinityCategories
```

EquivalenceFullyFaithful：

```lean
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma IsQCatEquivalence.isFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : IsQCatEquivalence f) :
    IsFullyFaithful f

lemma QCatEquivalence.isFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) : IsFullyFaithful e.hom

lemma isQCatEquivalence_iff_fullyFaithful_essentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    IsQCatEquivalence f ↔ IsFullyFaithful f ∧ IsEssentiallySurjective f

end SerrePositivity.InfinityCategories
```

EquivalenceAllLimits：

```lean
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma IsQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : IsQCatEquivalence f) :
    TrivialKanFibration (equivalencePathReplacementMap f)

lemma isLimitCone_iff_of_diagram_eq {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (hp : p = q) (hc : c.val = d.val) :
    IsLimitCone c ↔ IsLimitCone d

lemma isLimitCone_iff_mapJoinCone_of_section {K X E : SSet.{u}}
    [Quasicategory X] [Quasicategory E] (q : E ⟶ X) [TrivialKanFibration q]
    (s : X ⟶ E) (hs : s ≫ q = 𝟙 X) {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone s c)

lemma IsQCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : IsQCatEquivalence f)
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone f c)

lemma QCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone e.hom c)

end SerrePositivity.InfinityCategories
```


### A6 前段：評価錐・相対骨格による延長・点ごとの終対象（2026-10-18）

現行 Kerodon の該当節は §7.1.8（https://kerodon.net/tag/02X8）、特に Proposition 7.1.8.3 の双対。計画の §7.1.6 は相対極限の節。A6 の主目標は各評価図式が極限を持つときの自然な極限錐の存在と、同じ自然な錐について極限性と点ごとの極限性の同値。点ごとの極限錐から全体の極限錐への方向は、与えられた錐そのものから評価図式の極限の存在が従う。逆方向では評価図式の極限の存在仮定を保持する。

評価図式・評価錐・HasPointwiseLimits・IsPointwiseLimitCone を定義し、同じ slice 内の同型による点ごとの極限性の不変性を証明した。相対骨格での境界充填の貼り合わせと自然数上の互換な延長の余極限を実装。全頂点を含む部分複体上の射について、その外の各正次元単体の終点が終対象へ写れば全体へ延長することを証明した。これを直積に適用し、点ごとに終対象である関手の頂点が関手単体集合でも終対象になることを得た（この向きは標的の quasicategory 性不要）。A6 の任意図式の主定理・自然な極限錐の存在・評価による保存の一般形は未完了。A4・A5 は未着手。

検証：Core ビルド1648 jobs、累計846公開宣言の標準3公理監査成功。既存の公開名・型は変更していない。新規19宣言の全ての型・前提：

FunctorLimits：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
def evaluateFunctorDiagram {J K X : SSet.{u}} (p : J ⟶ (ihom K).obj X)
    (k : K _⦋0⦌) : J ⟶ X

def evaluateFunctorCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCone p) (k : K _⦋0⦌) : JoinCone (evaluateFunctorDiagram p k)

lemma evaluateFunctorCone_vertex {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCone p) (k : K _⦋0⦌) :
    (evaluateFunctorCone c k).vertex = (evaluateFunctorAt k).app (Opposite.op ⦋0⦌) c.vertex

def HasPointwiseLimits {J K X : SSet.{u}} (p : J ⟶ (ihom K).obj X) : Prop

def IsPointwiseLimitCone {J K X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : JoinCone p) : Prop

lemma IsPointwiseLimitCone.hasPointwiseLimits {J K X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : JoinCone p} (hc : IsPointwiseLimitCone c) :
    HasPointwiseLimits p

lemma IsPointwiseLimitCone.of_vertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} {c d : JoinCone p}
    (hc : IsPointwiseLimitCone c) (e : VertexIso (X := sliceOver p) c d) :
    IsPointwiseLimitCone d

lemma isPointwiseLimitCone_iff_of_vertexIso {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} {c d : JoinCone p}
    (e : VertexIso (X := sliceOver p) c d) : IsPointwiseLimitCone c ↔ IsPointwiseLimitCone d

end SerrePositivity.InfinityCategories
```

SkeletalExtension：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma exists_extension_skeletonOfMono_succ {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (d : ℕ) (f : (skeletonOfMono i d : SSet.{u}) ⟶ X)
    (hf : ∀ c : Cell i d, ∃ F : (Δ[d] : SSet.{u}) ⟶ X,
      (boundary d).ι ≫ F = c.ιSigmaBoundary ≫ t i d ≫ f) :
    ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X, r i d ≫ F = f

def skeletonBase {A B : SSet.{u}} (i : A ⟶ B) (d : ℕ) :
    A ⟶ (skeletonOfMono i d : SSet.{u})

lemma skeletonBase_succ {A B : SSet.{u}} (i : A ⟶ B) (d : ℕ) :
    skeletonBase i d ≫ r i d = skeletonBase i (d + 1)

noncomputable def skeletonBaseZeroIso {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (skeletonOfMono i 0 : SSet.{u}) ≅ A

lemma skeletonBaseZeroIso_inv {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    (skeletonBaseZeroIso i).inv = skeletonBase i 0

lemma exists_extension_of_skeletal_extensions {A B X : SSet.{u}} (i : A ⟶ B) [Mono i]
    (a : A ⟶ X)
    (hstep : ∀ d (f : (skeletonOfMono i d : SSet.{u}) ⟶ X),
      skeletonBase i d ≫ f = a →
        ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X, r i d ≫ F = f) :
    ∃ F : B ⟶ X, i ≫ F = a

end SerrePositivity.InfinityCategories
```

TerminalExtension：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
def simplexLastVertex {B : SSet.{u}} {n : ℕ} (s : B _⦋n⦌) : B _⦋0⦌

lemma exists_extension_of_terminal_last_vertices {B X : SSet.{u}} (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌)) (a : (A : SSet.{u}) ⟶ X)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a

end SerrePositivity.InfinityCategories
```

FunctorTerminal：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma simplexLastVertex_stdSimplex_of_notMem_boundary {n m : ℕ}
    (s : (Δ[n] : SSet.{u}) _⦋m⦌) (hs : s ∉ (boundary n).obj (Opposite.op ⦋m⦌)) :
    simplexLastVertex s = stdSimplex.obj₀Equiv.symm (Fin.last n)

lemma simplexLastVertex_prod {A B : SSet.{u}} {n : ℕ} (s : (A ⊗ B) _⦋n⦌) :
    simplexLastVertex s = (simplexLastVertex s.1, simplexLastVertex s.2)

lemma isTerminalVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, IsTerminalVertex (f.app (Opposite.op ⦋0⦌) k)) :
    IsTerminalVertex (functorVertex f)

end SerrePositivity.InfinityCategories
```


### A6 続き：標的を固定したセル延長と点ごとの相対境界充填（2026-10-18）

相対骨格の各境界充填について標的への射との可換性を保持して貼り合わせた。`TerminalBoundaryLifting p x` は終点 x を固定した正次元境界の厳密な持ち上げ条件であり、相対終対象性との同値をこの定義自体では主張しない。各点のこの条件は `(ihom K).map p` 上の関手の頂点にも移る。新規5宣言は全て quasicategory 性・fibration 性を仮定しない。Core ビルド1651 jobs、累計851宣言の標準3公理監査成功。任意図式の錐とこの相対境界判定の比較、A6 の一般の存在・点ごとの判定は未完了。A4・A5 は未着手。既存の公開名・型は変更していない。

SkeletalLifting：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma exists_lift_skeletonOfMono_succ {A B X Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) (b : B ⟶ Y) (d : ℕ)
    (f : (skeletonOfMono i d : SSet.{u}) ⟶ X)
    (hfp : f ≫ p = (skeletonOfMono i d).ι ≫ b)
    (hf : ∀ c : Cell i d, ∃ F : (Δ[d] : SSet.{u}) ⟶ X,
      (boundary d).ι ≫ F = c.ιSigmaBoundary ≫ t i d ≫ f ∧ F ≫ p = c.map ≫ b) :
    ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X,
      r i d ≫ F = f ∧ F ≫ p = (skeletonOfMono i (d + 1)).ι ≫ b

lemma exists_lift_of_skeletal_lifts {A B X Y : SSet.{u}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (hw : a ≫ p = i ≫ b)
    (hstep : ∀ d (f : (skeletonOfMono i d : SSet.{u}) ⟶ X),
      skeletonBase i d ≫ f = a → f ≫ p = (skeletonOfMono i d).ι ≫ b →
        ∃ F : (skeletonOfMono i (d + 1) : SSet.{u}) ⟶ X,
          r i d ≫ F = f ∧ F ≫ p = (skeletonOfMono i (d + 1)).ι ≫ b) :
    ∃ F : B ⟶ X, i ≫ F = a ∧ F ≫ p = b

end SerrePositivity.InfinityCategories
```

RelativeTerminalExtension：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
def TerminalBoundaryLifting {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌) : Prop

lemma exists_lift_of_terminal_last_vertices {B X Y : SSet.{u}} (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (p : X ⟶ Y) (a : (A : SSet.{u}) ⟶ X) (b : B ⟶ Y) (hw : a ≫ p = A.ι ≫ b)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      TerminalBoundaryLifting p (a.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hA _⟩)) :
    ∃ F : B ⟶ X, A.ι ≫ F = a ∧ F ≫ p = b

end SerrePositivity.InfinityCategories
```

FunctorRelativeTerminal：

```lean
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma terminalBoundaryLifting_ihom_of_pointwise {K X Y : SSet.{u}}
    (p : X ⟶ Y) (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, TerminalBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
    TerminalBoundaryLifting ((ihom K).map p) (functorVertex f)

end SerrePositivity.InfinityCategories
```

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

