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
