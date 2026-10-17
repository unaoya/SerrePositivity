# quasicategory の一般論（レーン α）

作成日：2026-10-17。状態：A1・A2 から着手。
全体の目標と依存関係の正本は [infinity-categories.md](infinity-categories.md) §0・§2。

## 0. 目標と範囲

Mathlib の `Quasicategory` をそのまま ∞ 圏の定義とし、Joyal モデル構造・straightening・
∞ 局所化を使わずに、次を順に整備する。

| 項目 | 内容 | 原典 |
| --- | --- | --- |
| A1 | ホモトピー圏の橋：quasicategory で `HomotopyCategory₂ ((truncation 2).obj X) ≌ hoFunctor.obj X`。ホモトピー X ⊗ Δ[1] ⟶ Y ↦ `hoFunctor.map f ⟶ hoFunctor.map g` の自然変換 | HTT 1.2.3、Kerodon 1.4 |
| A2 | join・slice・極限：単体集合の join、slice X_{/p}・coslice、X_{/p} → X が right fibration（X が quasicategory のとき）、終対象・始対象、極限 := slice の終対象、引き戻し四角形、始対象を持つ 1 圏上の極限は F(c) | HTT 1.2.8、1.2.12、2.1.2.1–2.1.2.3、4.1.1.8、Kerodon 4.3.5–4.3.6、4.6.7、7.1、7.2 |
| A3 | 写像空間と同値：pinched 模型と両端固定模型の比較、写像空間は Kan 複体、可逆辺の特徴づけ、充満忠実＋本質的全射 ⇒ 圏同値、成分が可逆な自然変換は可逆、極限は写像空間で検出される | HTT 1.2.5.1、2.2、4.4.2、Kerodon 4.4、4.6.2、4.6.5、7.1 |
| A4 | 安定 ∞ 圏：零対象、fiber・cofiber、安定性、Σ・Ω、h C の三角構造、fiber 列の長完全列 | HA 1.1.1–1.1.3 |
| A5 | 完全関手と自然変換、h での三角関手 | HA 1.1.4 |

A3 以降の指示は A2 の設計を見てから出す。

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

