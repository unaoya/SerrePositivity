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
