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
