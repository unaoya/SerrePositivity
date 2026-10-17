# dg nerve（∞ 圏基盤のマイルストーン N）

作成日：2026-10-17。状態：着手前（単一チャットに N0〜N6 をまとめて割り当てる）。

## 0. 位置づけと方針

2026-10-17 に、Bhatt–Scholze の §7–§8（導来 perfectoid 化、E∞-S 代数の引き戻し）と
K 理論（定理 3.1・補題 4.6）を、ともに ∞ 圏（quasicategory）の基盤の上に載せる方針を決めた。
最初の具体的目標は、可換環 S の導来 ∞ 圏を semifree 複体の充満 dg 部分圏の dg nerve
D(S) := N_dg(Semifree(S)) として定義することである。本計画はその前段として、
**任意の dg 圏に対する dg nerve と、その基本性質**を形式化する。

- 原典：Lurie, Higher Algebra（HA）§1.3.1。Construction 1.3.1.6（dg nerve）、
  Proposition 1.3.1.10（quasicategory）。ホモトピー圏と pinched 写像空間は
  Kerodon §2.5.3、§4.6.5 の記述に従う。
- 規約：リポジトリの dg 層（[DifferentialGraded/README.md](../SerrePositivity/DifferentialGraded/README.md)）
  に合わせる。`A : Type u`、`[CommRing A]`、`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`、
  微分は次数 +1、dg 圏は `DGCategory A D := EnrichedCategory (Complex A) D`、
  斉次射は `GradedHom A x y n`、通常順合成 `compose g f`（Leibniz 則は後に作用する g の次数で符号）。
  HA は chain 規約（次数 +m）なので、本計画では次数を −m に読み替える。
- モデル構造、Joyal の定理、∞ 局所化、coherent nerve は使わない。
  有限の代数計算と Mathlib の `Quasicategory`・`HomotopyCategory₂`・`KanComplex` だけで完結させる。
- 引用・追加公理・`sorry` は導入しない。

## 1. 数学的内容

### 1.1 定義

dg 圏 C の dg nerve N_dg(C) の n 単体は次の組である。

- 対象 X₀, …, Xₙ。
- {0, …, n} の各部分集合 I（|I| ≥ 2）に対し、a = min I、b = max I として
  f_I ∈ Hom^{2−|I|}(X_a, X_b)。
- すべての I について

```
δ f_I = Σ_{j ∈ I, a<j<b} (−1)^{#{k ∈ I : k > j}} ( f_{I∖{j}} − compose f_{I∩[j,b]} f_{I∩[a,j]} )
```

単体的構造：Δ の射 α: [m] → [n] に対し、対象を X_{α(i)} に取り替え、
g_J := f_{α(J)}（α が J 上単射）、g_J := id（|J| = 2 で α が J を潰す）、g_J := 0（それ以外）。

低次の形：0 単体は対象、1 単体は閉次数 0 の射、2 単体は chain map f₀₁, f₁₂, f₀₂ と
δ f₀₁₂ = f₁₂ ∘ f₀₁ − f₀₂ を満たす次数 −1 の f₀₁₂、退化単体は辺が id で三角形以上が 0。

符号は N0 でリポジトリ規約に対して検証し、必要なら上の式を訂正して本節に記録する。

### 1.2 基本定理

| 番号 | 主張 | 証明の性格 |
| --- | --- | --- |
| N2 | N_dg(C) は quasicategory | 内部ホーン Λ[n,i] に対し f_[n] := 0 と置き、I = [n] の方程式を f_{[n]∖{i}} について解く。解が自分の方程式を満たすことは δ² = 0、Leibniz 則、結合律の有限計算 |
| N3 | h N_dg(C) ≅ H⁰(C) | 辺は閉次数 0 の射、辺 (id, g, f) の三角形の f₀₁₂ は δ f₀₁₂ = f − g なので chain homotopy。合成はホーン充填の式で本物の合成 |
| N4 | 右 pinched 写像空間 Hom^R(X, Y) は単体的 A 加群で Kan 複体、π₀ = H⁰ Hom^•(X, Y) | n 単体は [n] の空でない部分集合 J ごとの f_J（次数 −(|J|−1)）で、方程式は線形 δ f_J = Σ ± f_{J∖{j}}。Kan 性は線形方程式の直接の充填 |
| N5 | 関手性 | dg 関手は定義を保つ。厳密 dg 自然変換は切れ目ごとの式で単体的ホモトピーを与える |

両端固定模型 Fun(Δ¹, X) ×_{X×X} {(x,y)} との比較、quasi-equivalence ⇒ 圏同値、
テンソル積との両立 N_dg(C) × N_dg(C′) → N_dg(C ⊗ C′) は本計画の範囲外（α・δ の計画）。

## 2. 作業項目

配置は `SerrePositivity/InfinityCategories/DGNerve/`、namespace は
`SerrePositivity.InfinityCategories`。集約ファイル `SerrePositivity/InfinityCategories/DGNerve.lean`
をルート `SerrePositivity.lean` に 1 行で追加する。
規約・式の記録は `SerrePositivity/InfinityCategories/README.md` に置く（`notes/` は作らない）。

| 工程 | ファイル | 内容 | 検証 |
| --- | --- | --- | --- |
| N0 | `InfinityCategories/README.md` | HA 1.3.1.6・1.3.1.10 の式をリポジトリ規約へ翻訳。§1.1 の方程式、ホーン充填の解の式、pinched 空間の線形方程式と Λ₀ 型の可解性を紙で確認し記録 | 2 単体・3 単体で `differential_compose` と整合することを手計算で確認 |
| N1 | `DGNerve/Simplex.lean`、`DGNerve/Basic.lean` | 単体の構造体、単体的構造、`dgNerve A D : SSet.{max u v}`、0・1・2 単体の特徴づけ、面・退化の計算補題 | 対象ビルド、`#print axioms` |
| N2 | `DGNerve/HornFilling.lean`、`DGNerve/Quasicategory.lean` | 解の式、主恒等式、面からのデータ回収、`instance : Quasicategory (dgNerve A D)` | 同上 |
| N3 | `DGNerve/HomotopyCategory.lean` | `HomotopyCategory₂ ((truncation 2).obj (dgNerve A D)) ≌ HomotopyCategory A D` | 同上 |
| N4 | `PinchedHom/Basic.lean`、`DGNerve/PinchedHom.lean` | 任意の SSet の右 pinched Hom、dg nerve での明示的記述、単体的 A 加群構造、`KanComplex`、π₀ = H⁰ | 同上 |
| N5 | `DGNerve/Functor.lean`、`DGNerve/NatTrans.lean` | `dgNerve.map`、`map_id`、`map_comp`、充満 dg 部分圏との両立、厳密 dg 自然変換 ↦ ホモトピー | 同上 |
| N6 | `DGNerve/Checks.lean`、`scripts/audit_dg_nerve.lean` | 一点 dg 圏と `Complex A` 自身での具体化、公開宣言の公理監査 | 標準 3 公理のみ |

順序は N0 → N1 → N2 → N3 → N5 → N4 → N6 を基本とするが、N2〜N5 は N1 の後なら入れ替えてよい。
各工程を一つの保存単位（対象ビルド、監査、本計画 §5 への追記）とする。

## 3. 設計上の決定

- **単体の表現。** 部分集合は `Finset (Fin (n + 1))`。`hom` は端点 a, b と次数 k を引数に取り、
  「a = min I、b = max I、k = 2 − |I|、2 ≤ |I|」の証明を添えた
  `GradedHom A (obj a) (obj b) k` を返す。`I.erase j` や `I.filter` の min・max・card は
  命題的にしか一致しないため、この形で cast を避ける。順序埋め込み `Fin (k+2) ↪o Fin (n+1)`
  による添字は同じ cast 問題が残るので採らない。
- **符号。** `(−1)^{#{k ∈ I : k > j}}` は `Int.negOnePow` と `Finset.card` で表す。
- **単体的構造。** Mathlib `SimplexCategory` の射 α に対し `Finset.image α.toOrderHom`、
  単射性は `Set.InjOn`。`map_id`・`map_comp` は三分岐（単射・2 点を潰す・それ以外）の場合分け。
- **Mathlib の API。** `Quasicategory`（Λ[n+2, i] の充填）、`horn.face`、`horn.hom_ext`、
  `yonedaEquiv`、`Quasicategory₂`・`HomotopyCategory₂`・`Edge.comp`・`CompStruct.comp_unique`
  （`Quasicategory/TwoTruncated.lean`）、`KanComplex`、`PiZero.lean` の π₀、
  `GradedNatTrans`（`Enriched/Basic.lean`、次数は単位対象）。
- **リポジトリの API。** `GradedHom`、`differential`、`compose`、`differential_compose`
  （`Category/Components.lean`）、結合則（`Complexes/CompositionLaws.lean`）、
  `HomotopyCategory A D`・`boundaryRelation`・`closedHomEquiv`（`Category/Homotopy.lean`）、
  `DGFunctor`（`Functor/Basic.lean`）、`DGFullSubcategory`・`dgFullSubcategoryInclusion`
  （`Category/FullSubcategory.lean`）。
- **pinched Hom。** n 単体は (n+1) 単体で、最初の n 面が x で退化し最終頂点が y。
  関手性は [m] → [n] を最終点を固定して [m+1] → [n+1] へ延ばす写像で与える。
  Kan 性は線形方程式の直接の充填で示す。一般の「単体的群は Kan」は α の計画で整備するなら
  後で置き換える。
- **宇宙。** `dgNerve A D : SSet.{max u v}`（`nerve` と同じ）。

## 4. 受入基準

1. 各ファイルがビルドし、`sorry`・公理・引用がない。公開宣言は標準 3 公理のみ。
2. docstring は README「Conventions」の形式（概要／方針／規約／使われ方）。原典の番号を書く。
3. N0 の規約と式が `InfinityCategories/README.md` にあり、Lean の定義と一致する。
4. 本計画 §5 に、各工程の公開宣言名・正確な型・前提・未完了の範囲を記録する。
5. 主定理の経路には触れない。README の状態表は変えない。

## 5. 記録

（各工程の完了時に追記する。）

### N0（2026-10-17）：紙の検証と規約

- `SerrePositivity/InfinityCategories/README.md` に HA の cochain 翻訳、2・3 単体の
  展開と微分の相殺、負次数の Leibniz 符号を含む 4 単体の検算を記録した。
  §1.1 の符号は訂正不要。Kerodon の成分との再符号化も明記した。
- 内部ホーンで `f_[n]=0` として欠けた面を解く式と、欠けた面の方程式を導く
  残差恒等式の計算方針を記録した。右 pinched Hom は先頭の n+1 頂点の張る面全体を
  x に定値とする意味で読み、線形方程式の第 0 項を退化辺との合成から導いた。
  第 0 ホーンを含む全ホーンの線形解も記録した。§3 の設計変更はない。
- 公開 Lean 宣言名・型：N0 は文書のみであり、新規公開宣言はない。
  前提は任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
- 検証：`set -o pipefail` の下で
  `lake build SerrePositivity.DifferentialGraded.Category.Components
  SerrePositivity.DifferentialGraded.Category.Homotopy
  SerrePositivity.DifferentialGraded.Functor.Basic
  SerrePositivity.DifferentialGraded.Category.FullSubcategory` が終了コード 0（1758 jobs）。
  `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
  再利用する `differential_compose`・`compose_assoc`・`differential_unit`・
  `compose_unit`・`unit_compose` の 5 宣言は標準 3 公理のみ。
- 未完了：N1〜N6。紙の残差計算と線形ホーンの計算は Lean の証明ではなく、
  dg nerve、Quasicategory、H⁰ 比較、KanComplex をまだ構成していない。

### N1a 保存（2026-10-17、N1 は未完了）

- 単体の型 `Simplex A D n` を、計画 §3 の `Finset (Fin (n+1))`、端点・次数の
  証明を受ける `hom`、HA の微分方程式で定義した。射族のみの `SimplexData` と
  方程式の項 `term`・右辺 `rhs` を分けて、引き戻しのデータと方程式の保存を区別する。
- 対象と零単体の同値 `Simplex.vertexEquiv`、一単体と二頂点・閉次数零元の同値
  `Simplex.edgeEquiv`、既存の `closedHomEquiv` による `Simplex.edgeClosed`、
  `Simplex.differential_triangleHom` の `δh = f₁₂ ∘ f₀₁ - f₀₂` を証明した。
- `SimplexData.pullback` は計画通りの三分岐で定義し、データについてのみ
  `pullback_id` と `pullback_comp` を証明した。部分集合の像・削除・切断・濃度・端点の
  補題は `DGNerve/Index.lean` に置いた。設計変更はない。
- 前提は任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
  添字の補題は任意の線形順序型で成立する。**条件付きの単体的集合を定義して
  完成とする構成はしていない**。
- 検証：`set -o pipefail` の下で
  `lake build SerrePositivity.InfinityCategories.DGNerve.LowDimensional
  SerrePositivity.InfinityCategories.DGNerve.Reindex` が終了コード 0（3285 jobs）。
  `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
  明示的な新規公開宣言 46 件と既存則 5 件は全て標準 3 公理のみ。
  監査スクリプトは全 46 件について `#print axioms` と `#check @宣言名` を実行する。
- **未完了**：引き戻しによる単体の方程式の保存、`dgNerve : SSet`、面・退化の計算補題、
  二単体の特徴づけの逆方向、N2〜N6。したがって N1 の完了報告ではない。
  集約ファイルと共有ルートの import は `dgNerve` の構成後に追加する。

公開宣言の正確な型は次の Lean の検査出力のとおり。
`⋯` は証明引数の pretty-printer による省略で、端点に使う非空性の証明は
`Index.nonempty hI`（ソースの定義通り）である。

<details>
<summary>N1a の全公開宣言の型（46 件）</summary>

```text
@SerrePositivity.InfinityCategories.DGNerve.Index.nonempty : ∀ {α : Type u_1} {I : Finset α}, 2 ≤ I.card → I.Nonempty
@SerrePositivity.InfinityCategories.DGNerve.Index.two_le_card : ∀ {α : Type u_1} [LinearOrder α] {I : Finset α}
  {a b : α}, a ∈ I → b ∈ I → a ≠ b → 2 ≤ I.card
@SerrePositivity.InfinityCategories.DGNerve.Index.erase_two : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a b j : α}, a ∈ I → b ∈ I → a < j → j < b → 2 ≤ (I.erase j).card
@SerrePositivity.InfinityCategories.DGNerve.Index.erase_min : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a j : α}, IsLeast (↑I) a → a < j → ∀ (h : (I.erase j).Nonempty), a = (I.erase j).min' h
@SerrePositivity.InfinityCategories.DGNerve.Index.erase_max : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {b j : α}, IsGreatest (↑I) b → j < b → ∀ (h : (I.erase j).Nonempty), b = (I.erase j).max' h
@SerrePositivity.InfinityCategories.DGNerve.Index.left_two : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a j : α}, a ∈ I → j ∈ I → a < j → 2 ≤ {x ∈ I | x ≤ j}.card
@SerrePositivity.InfinityCategories.DGNerve.Index.right_two : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {b j : α}, j ∈ I → b ∈ I → j < b → 2 ≤ {x ∈ I | j ≤ x}.card
@SerrePositivity.InfinityCategories.DGNerve.Index.left_min : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a j : α}, IsLeast (↑I) a → a ≤ j → ∀ (h : {x ∈ I | x ≤ j}.Nonempty), a = {x ∈ I | x ≤ j}.min' h
@SerrePositivity.InfinityCategories.DGNerve.Index.left_max : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α}, j ∈ I → ∀ (h : {x ∈ I | x ≤ j}.Nonempty), j = {x ∈ I | x ≤ j}.max' h
@SerrePositivity.InfinityCategories.DGNerve.Index.right_min : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α}, j ∈ I → ∀ (h : {x ∈ I | j ≤ x}.Nonempty), j = {x ∈ I | j ≤ x}.min' h
@SerrePositivity.InfinityCategories.DGNerve.Index.right_max : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {b j : α}, IsGreatest (↑I) b → j ≤ b → ∀ (h : {x ∈ I | j ≤ x}.Nonempty), b = {x ∈ I | j ≤ x}.max' h
@SerrePositivity.InfinityCategories.DGNerve.Index.split_card : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α}, j ∈ I → {x ∈ I | x ≤ j}.card + {x ∈ I | j ≤ x}.card = I.card + 1
@SerrePositivity.InfinityCategories.DGNerve.Index.eq_pair : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a b : α}, I.card = 2 → IsLeast (↑I) a → IsGreatest (↑I) b → I = {a, b}
@SerrePositivity.InfinityCategories.DGNerve.Index.image_min : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → IsLeast (↑I) a → ∀ (h : (Finset.image f I).Nonempty), f a = (Finset.image f I).min' h
@SerrePositivity.InfinityCategories.DGNerve.Index.image_max : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {b : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → IsGreatest (↑I) b → ∀ (h : (Finset.image f I).Nonempty), f b = (Finset.image f I).max' h
@SerrePositivity.InfinityCategories.DGNerve.Index.image_two : ∀ {α : Type u_1} {I : Finset α} {β : Type u_2}
  [inst : LinearOrder β] {f : α → β}, Set.InjOn f ↑I → 2 ≤ I.card → 2 ≤ (Finset.image f I).card
@SerrePositivity.InfinityCategories.DGNerve.Index.image_erase : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Set.InjOn f ↑I → j ∈ I → Finset.image f (I.erase j) = (Finset.image f I).erase (f j)
@SerrePositivity.InfinityCategories.DGNerve.Index.image_le_iff : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → ∀ {x y : α}, x ∈ I → y ∈ I → (f x ≤ f y ↔ x ≤ y)
@SerrePositivity.InfinityCategories.DGNerve.Index.collapse_two : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {a b : α} {β : Type u_2} [LinearOrder β] {f : α → β},
  ¬Set.InjOn f ↑I → I.card = 2 → IsLeast (↑I) a → IsGreatest (↑I) b → f a = f b
@SerrePositivity.InfinityCategories.DGNerve.Index.image_left : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → j ∈ I → Finset.image f ({x ∈ I | x ≤ j}) = {x ∈ Finset.image f I | x ≤ f j}
@SerrePositivity.InfinityCategories.DGNerve.Index.image_right : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {j : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → j ∈ I → Finset.image f ({x ∈ I | j ≤ x}) = {x ∈ Finset.image f I | f j ≤ x}
SerrePositivity.InfinityCategories.DGNerve.HomFamily : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → {n : ℕ} → (Fin (n + 1) → D) → Type u_1
SerrePositivity.InfinityCategories.DGNerve.SimplexData : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → ℕ → Type (max u_1 u_2)
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (j : Fin (n + 1)) →
                            j ∈ I →
                              a < j →
                                j < b → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))
SerrePositivity.InfinityCategories.DGNerve.Simplex : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → ℕ → Type (max u_1 u_2)
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.ext : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  {s t : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n}, s.obj = t.obj → s.hom ≍ t.hom → s = t
@SerrePositivity.InfinityCategories.DGNerve.zero_hom_heq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {obj obj' : Fin 1 → D}
  (f : SerrePositivity.InfinityCategories.DGNerve.HomFamily A D obj)
  (g : SerrePositivity.InfinityCategories.DGNerve.HomFamily A D obj'), f ≍ g
@SerrePositivity.InfinityCategories.DGNerve.Simplex.ext : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  {s t : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n}, s.toSimplexData = t.toSimplexData → s = t
@SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        D → SerrePositivity.InfinityCategories.DGNerve.Simplex A D 0
@SerrePositivity.InfinityCategories.DGNerve.Simplex.vertexEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.Simplex A D 0 ≃ D
@SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeHom : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) →
            (a b : Fin (n + 1)) → a < b → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) 0)
@SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_edgeHom : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (a b : Fin (n + 1)) (hab : a < b),
  SerrePositivity.DifferentialGraded.differential A (s.edgeHom a b hab) = 0
@SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) →
            (a b : Fin (n + 1)) →
              a < b →
                ↥(SerrePositivity.DifferentialGraded.zeroCycles
                    (SerrePositivity.DifferentialGraded.homObject A D (s.obj a) (s.obj b)))
SerrePositivity.InfinityCategories.DGNerve.two_eq_univ : ∀ (I : Finset (Fin 2)), 2 ≤ I.card → I = Finset.univ
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofEdge : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (obj : Fin 2 → D) →
          ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (obj 0) (obj 1))) →
            SerrePositivity.InfinityCategories.DGNerve.SimplexData A D 1
@SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (obj : Fin 2 → D) →
          ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (obj 0) (obj 1))) →
            SerrePositivity.InfinityCategories.DGNerve.Simplex A D 1
@SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] (obj : Fin 2 → D)
  (f :
    ↥(SerrePositivity.DifferentialGraded.zeroCycles
        (SerrePositivity.DifferentialGraded.homObject A D (obj 0) (obj 1)))),
  (SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge obj f).edgeCycle 0 1
      SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge._proof_1 =
    f
@SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge_edgeCycle : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D 1),
  SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge s.obj
      (s.edgeCycle 0 1 SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge._proof_1) =
    s
@SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.Simplex A D 1 ≃
          (obj : Fin 2 → D) ×
            ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (obj 0) (obj 1)))
@SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeClosed : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) →
            (a b : Fin (n + 1)) →
              a < b →
                (CategoryTheory.ForgetEnrichment.of (SerrePositivity.DifferentialGraded.Complex A) (s.obj a) ⟶
                  CategoryTheory.ForgetEnrichment.of (SerrePositivity.DifferentialGraded.Complex A) (s.obj b))
@SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleHom : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2) →
          ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj 0) (s.obj 2) (-1))
@SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2),
  SerrePositivity.DifferentialGraded.differential A s.triangleHom =
    SerrePositivity.DifferentialGraded.compose A
        (s.edgeHom 1 2 SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom._proof_1)
        (s.edgeHom 0 1 SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom._proof_2)
        SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom._proof_3 -
      s.edgeHom 0 2 SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom._proof_4
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {m n : ℕ} →
          SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n →
            (Fin (m + 1) →o Fin (n + 1)) → SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_id : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n), s.pullback OrderHom.id = s
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_comp : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {l m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (l + 1) →o Fin (m + 1))
  (β : Fin (m + 1) →o Fin (n + 1)), (s.pullback β).pullback α = s.pullback (β.comp α)
```

</details>

### N1b 保存（2026-10-17、N1 は未完了）

- 単射な部分集合上での右側点数の保存、引き戻しの成分・各項・右辺全体の移送を証明した。
  有限和は所属証明付き有限型とその像の全単射に沿って再添字付けした。
- `Simplex.pullback_equation_of_inj` は **J 上単射** を仮定して J の方程式の保存を示す。
  `Simplex.pullbackOfInjective` は **全域で単射** な単調写像に沿う実際の単体を構成する。
  `Simplex.pullback_equation_of_card_two` は任意の単調写像について二点集合の方程式を示す。
  潰れた辺には既存 dg 単位の閉性を用いる。
- 前提は N1a と同じ任意の可換環・dg 圏。**非単射で三点以上の部分集合の方程式は
  未証明**。したがって `dgNerve : SSet` も N1 完了も主張しない。§3 の設計変更なし。
- 検証：`set -e`・`set -o pipefail` の下で
  `lake build SerrePositivity.InfinityCategories.DGNerve.LowDimensional
  SerrePositivity.InfinityCategories.DGNerve.PullbackEquation` が終了コード 0（3286 jobs）。
  `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
  新規 10 件、累計 56 件の明示的公開宣言と既存則 5 件は標準 3 公理のみ。
- 残る範囲：非単射で三点以上の場合の相殺、一般の単体の引き戻し、SSet の構成、
  面・退化の計算補題、二単体の特徴づけの逆方向、N2〜N6。

追加公開宣言の正確な型は次のとおり（証明引数の省略記号は N1a と同じ）。

<details>
<summary>N1b で追加した公開宣言の型（10 件）</summary>

```text
@SerrePositivity.InfinityCategories.DGNerve.Index.image_lt_iff : ∀ {α : Type u_1} [inst : LinearOrder α] {I : Finset α}
  {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → ∀ {x y : α}, x ∈ I → y ∈ I → (f x < f y ↔ x < y)
@SerrePositivity.InfinityCategories.DGNerve.Index.image_strict_right : ∀ {α : Type u_1} [inst : LinearOrder α]
  {I : Finset α} {j : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → j ∈ I → Finset.image f ({x ∈ I | j < x}) = {x ∈ Finset.image f I | f j < x}
@SerrePositivity.InfinityCategories.DGNerve.Index.image_sign_card : ∀ {α : Type u_1} [inst : LinearOrder α]
  {I : Finset α} {j : α} {β : Type u_2} [inst_1 : LinearOrder β] {f : α → β},
  Monotone f → Set.InjOn f ↑I → j ∈ I → {x ∈ Finset.image f I | f j < x}.card = {x ∈ I | j < x}.card
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_inj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card) (hi : Set.InjOn ⇑α ↑J),
  (s.pullback α).hom J a b k hJ ha hb hk = s.hom (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_of_card_two : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  J.card = 2 → s.rhs J a b k hJ ha hb hk = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_inj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card) (hi : Set.InjOn ⇑α ↑J) (j : Fin (m + 1)) (hj : j ∈ J) (haj : a < j) (hjb : j < b),
  (s.pullback α).term J a b k hJ ha hb hk j hj haj hjb = s.term (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯ (α j) ⋯ ⋯ ⋯
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_rhs_of_inj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card) (hi : Set.InjOn ⇑α ↑J),
  (s.pullback α).rhs J a b k hJ ha hb hk = s.rhs (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_inj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  Set.InjOn ⇑α ↑J →
    SerrePositivity.DifferentialGraded.differential A ((s.pullback α).hom J a b k hJ ha hb hk) =
      (s.pullback α).rhs J a b k hJ ha hb hk
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullbackOfInjective : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {m n : ℕ} →
          SerrePositivity.InfinityCategories.DGNerve.Simplex A D n →
            (α : Fin (m + 1) →o Fin (n + 1)) →
              Function.Injective ⇑α → SerrePositivity.InfinityCategories.DGNerve.Simplex A D m
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_card_two : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  J.card = 2 →
    SerrePositivity.DifferentialGraded.differential A ((s.pullback α).hom J a b k hJ ha hb hk) =
      (s.pullback α).rhs J a b k hJ ha hb hk
```

</details>

### N1c 保存（2026-10-17、dg nerve の単体的集合を構成、N1 全体は未完了）

- 基本退化の部分集合の計算を `DGNerve/DegeneracyIndex.lean` に置き、片方の重複点を
  消したときの単射性、削除後の像の一致、右側点数の差が一であることを証明した。
- `DGNerve/DegeneracyEquation.lean` は、重複二点以外の内部点の項の消滅、内部での二項の
  相殺、始点・終点に接する重複での単位則を証明する。
  `Simplex.predAbove_equation` は **全ての部分集合** について基本退化の方程式を保ち、
  `Simplex.degeneracy` は実際の高次単体を返す。単位則の移送補題は `DGNerve/Algebra.lean`。
- `DGNerve/Pullback.lean` は任意の単調写像による単体の引き戻しを構成する。
  非単射写像を基本退化経由に分解する Mathlib の
  `SimplexCategory.eq_σ_comp_of_not_injective` によって源の次元を下げる。
  対象・成分は既存の三分岐の `SimplexData.pullback` に **定義上** 一致し、
  単体の `pullback_id`・`pullback_comp` も証明済み。§3 の設計変更なし。
- `DGNerve/Basic.lean` に次の無条件の単体的集合を定義した。
  共通の前提は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]` のみ。

  ```lean
  dgNerve A D : SSet.{max u v}
  dgNerve.vertexEquiv A D : (dgNerve A D) _⦋0⦌ ≃ D
  dgNerve.edgeEquiv A D : (dgNerve A D) _⦋1⦌ ≃
    Σ obj : Fin 2 → D, zeroCycles (homObject A D (obj 0) (obj 1))
  ```

  `dgNerve.δ_obj`・`dgNerve.σ_obj` は面・退化の頂点の計算を与える。
  `SerrePositivity/InfinityCategories/DGNerve.lean` を集約入口として追加した。
- 検証：`set -e`・`set -o pipefail` の下で
  `lake build SerrePositivity.InfinityCategories.DGNerve` が終了コード 0（3310 jobs）。
  `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
  今回の新規 37 件、累計 93 件の明示的公開宣言と既存則 5 件は標準 3 公理のみ。
  監査対象はこの作業の `DGNerve/` と集約入口に限定し、並行作業の `Core/`・`Derived/` は含めない。
- **未完了**：二単体の特徴づけの逆方向と同値、面・退化の斉次成分の公開計算補題の整備、
  共有ルートへの集約入口の import 追加、N2〜N6。
  `dgNerve` の構成を N1 全体の完了や quasicategory 性の証明とは数えない。

追加公開宣言の正確な型は次のとおり（証明引数の省略記号は N1a と同じ）。

<details>
<summary>N1c で追加した公開宣言の型（37 件）</summary>

```text
@SerrePositivity.InfinityCategories.DGNerve.compose_zero : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A g 0 h = 0
@SerrePositivity.InfinityCategories.DGNerve.zero_compose : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A 0 f h = 0
@SerrePositivity.InfinityCategories.DGNerve.compose_unit_of_heq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (hn : p + q = k),
  x = y →
    p = 0 →
      f ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A y) →
        SerrePositivity.DifferentialGraded.compose A g f hn ≍ g
@SerrePositivity.InfinityCategories.DGNerve.unit_compose_of_heq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (hn : p + q = k),
  y = z →
    q = 0 →
      g ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A z) →
        SerrePositivity.DifferentialGraded.compose A g f hn ≍ f
SerrePositivity.InfinityCategories.dgNerve : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → SSet
SerrePositivity.InfinityCategories.dgNerve.obj : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] (n : ℕ),
  (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n }) =
    SerrePositivity.InfinityCategories.DGNerve.Simplex A D n
SerrePositivity.InfinityCategories.dgNerve.vertexEquiv : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := 0 }) ≃ D
SerrePositivity.InfinityCategories.dgNerve.edgeEquiv : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := 1 }) ≃
          (obj : Fin 2 → D) ×
            ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (obj 0) (obj 1)))
SerrePositivity.InfinityCategories.dgNerve.δ_obj : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 2))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n + 1 })) (j : Fin (n + 1)),
  ((CategoryTheory.ConcreteCategory.hom
            (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) i))
          s).obj
      j =
    s.obj (i.succAbove j)
SerrePositivity.InfinityCategories.dgNerve.σ_obj : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 1))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n })) (j : Fin (n + 2)),
  ((CategoryTheory.ConcreteCategory.hom
            (CategoryTheory.SimplicialObject.σ (SerrePositivity.InfinityCategories.dgNerve A D) i))
          s).obj
      j =
    s.obj (i.predAbove j)
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_collision_away : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 2) →o Fin (n + 1)) (i : Fin (m + 1))
  (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  i.castSucc ∈ J →
    i.succ ∈ J →
      α i.castSucc = α i.succ →
        ∀ (j : Fin (m + 2)) (hj : j ∈ J) (haj : a < j) (hjb : j < b),
          j ≠ i.castSucc → j ≠ i.succ → (s.pullback α).term J a b k hJ ha hb hk j hj haj hjb = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_terms_cancel : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card)
  (hp : i.castSucc ∈ J) (hq : i.succ ∈ J) (hap : a < i.castSucc) (hqb : i.succ < b),
  (s.pullback i.predAboveOrderHom).term J a b k hJ ha hb hk i.castSucc hp hap ⋯ +
      (s.pullback i.predAboveOrderHom).term J a b k hJ ha hb hk i.succ hq ⋯ hqb =
    0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_interior : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  i.castSucc ∈ J →
    i.succ ∈ J → a < i.castSucc → i.succ < b → (s.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_min : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : i.castSucc = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card)
  (hq : i.succ ∈ J) (hqb : i.succ < b),
  (s.pullback i.predAboveOrderHom).term J i.castSucc b k hJ ha hb hk i.succ hq ⋯ hqb = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_max : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (a : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : i.succ = J.max' ⋯) (hk : k = 2 - ↑J.card)
  (hp : i.castSucc ∈ J) (hap : a < i.castSucc),
  (s.pullback i.predAboveOrderHom).term J a i.succ k hJ ha hb hk i.castSucc hp hap ⋯ = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_collision : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  i.castSucc ∈ J → i.succ ∈ J → (s.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk = 0
@SerrePositivity.InfinityCategories.DGNerve.Simplex.predAbove_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D m) (i : Fin (m + 1)) (J : Finset (Fin (m + 2)))
  (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  SerrePositivity.DifferentialGraded.differential A ((s.pullback i.predAboveOrderHom).hom J a b k hJ ha hb hk) =
    (s.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk
@SerrePositivity.InfinityCategories.DGNerve.Simplex.degeneracy : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {m : ℕ} →
          SerrePositivity.InfinityCategories.DGNerve.Simplex A D m →
            Fin (m + 1) → SerrePositivity.InfinityCategories.DGNerve.Simplex A D (m + 1)
@SerrePositivity.InfinityCategories.DGNerve.Index.three_le_card : ∀ {α : Type u_1} [inst : LinearOrder α] {J : Finset α}
  {x y z : α}, x ∈ J → y ∈ J → z ∈ J → x < y → y < z → 3 ≤ J.card
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_left : ∀ {n : ℕ} (i : Fin (n + 1))
  {J : Finset (Fin (n + 2))}, i.castSucc ∉ J → Set.InjOn i.predAbove ↑J
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_right : ∀ {n : ℕ} (i : Fin (n + 1))
  {J : Finset (Fin (n + 2))}, i.succ ∉ J → Set.InjOn i.predAbove ↑J
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_iff : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), Set.InjOn i.predAbove ↑J ↔ ¬(i.castSucc ∈ J ∧ i.succ ∈ J)
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_image_erase : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))),
  i.castSucc ∈ J →
    i.succ ∈ J → Finset.image i.predAbove (J.erase i.castSucc) = Finset.image i.predAbove (J.erase i.succ)
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_sign_card : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), i.succ ∈ J → {x ∈ J | i.castSucc < x}.card = {x ∈ J | i.succ < x}.card + 1
@SerrePositivity.InfinityCategories.DGNerve.Index.not_injOn_of_equal : ∀ {α : Type u_1} {β : Type u_2} {J : Finset α}
  {f : α → β} {p q : α}, p ∈ J → q ∈ J → p ≠ q → f p = f q → ¬Set.InjOn f ↑J
@SerrePositivity.InfinityCategories.DGNerve.Index.erase_three_of_internal : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))) {a b j : Fin (n + 2)},
  IsLeast (↑J) a →
    IsGreatest (↑J) b → i.castSucc ∈ J → i.succ ∈ J → a < j → j < b → j ≠ i.castSucc → j ≠ i.succ → 3 ≤ (J.erase j).card
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_min : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), IsLeast (↑J) i.castSucc → i.succ ∈ J → {x ∈ J | x ≤ i.succ} = {i.castSucc, i.succ}
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_min : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), IsLeast (↑J) i.castSucc → {x ∈ J | i.succ ≤ x} = J.erase i.castSucc
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_max : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), i.castSucc ∈ J → IsGreatest (↑J) i.succ → {x ∈ J | i.castSucc ≤ x} = {i.castSucc, i.succ}
@SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_max : ∀ {n : ℕ} (i : Fin (n + 1))
  (J : Finset (Fin (n + 2))), IsGreatest (↑J) i.succ → {x ∈ J | x ≤ i.castSucc} = J.erase i.succ
@SerrePositivity.InfinityCategories.DGNerve.Simplex.exists_pullback : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (m + 1) →o Fin (n + 1)),
  ∃ t, t.toSimplexData = s.pullback α
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {m n : ℕ} →
          SerrePositivity.InfinityCategories.DGNerve.Simplex A D n →
            (Fin (m + 1) →o Fin (n + 1)) → SerrePositivity.InfinityCategories.DGNerve.Simplex A D m
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_data : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (m + 1) →o Fin (n + 1)),
  (s.pullback α).toSimplexData = s.pullback α
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_id : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n), s.pullback OrderHom.id = s
@SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_comp : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {l m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (l + 1) →o Fin (m + 1))
  (β : Fin (m + 1) →o Fin (n + 1)), (s.pullback β).pullback α = s.pullback (β.comp α)
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_not_inj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card), ¬Set.InjOn ⇑α ↑J → J.card ≠ 2 → (s.pullback α).hom J a b k hJ ha hb hk = 0
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_collapsed_pair : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (J : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  ¬Set.InjOn ⇑α ↑J →
    J.card = 2 →
      (s.pullback α).hom J a b k hJ ha hb hk ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A (s.obj (α b)))
```

</details>

### N1d・N1 完了（2026-10-17）：二単体の同値と公開成分計算

- `DGNerve/Triangle.lean` に `TriangleData A D` を定義した。
  これは `obj : Fin 3 → D`、三つの閉零射 `f01`・`f12`・`f02`、次数 −1 の `homotopy` と
  `differential A homotopy = compose A f12.val f01.val (by decide) - f02.val` を持つ。
  `Simplex.ofTriangle` と `Simplex.toTriangle` の両方の逆写像の法則を証明し、
  `Simplex.triangleEquiv` と次の公開同値を構成した。

  ```lean
  dgNerve.triangleEquiv A D : (dgNerve A D) _⦋2⦌ ≃ DGNerve.TriangleData A D
  ```

- `DGNerve/Computations.lean` は `δ_data`・`σ_data`、全域単射な面の `δ_hom`、
  退化の `σ_hom_of_inj`・`σ_hom_eq_zero`・`σ_hom_of_collapsed_pair` を公開する。
  最後の補題は端点・次数の等式で移送した単位との `HEq` を用い、cast の選択に依存しない。
- 前提は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]` のみ。
  宇宙は `dgNerve A D : SSet.{max u v}`。設計 §3 の変更はない。
- 集約入口に三角形の同値と成分計算を追加した。共有ルートには
  `public import SerrePositivity.InfinityCategories.DGNerve` を一行だけ追加した。
  並行作業のルートの他のハンクをコミットに混ぜないよう分離して保存する。
- 検証：`set -e`・`set -o pipefail` の下で
  `lake build SerrePositivity.InfinityCategories.DGNerve` は終了コード 0（3312 jobs）、
  `lake build SerrePositivity` も終了コード 0（7348 jobs）。
  `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
  今回の新規 17 件、累計 110 件の明示的公開宣言と既存則 5 件は全て標準 3 公理のみ。
- **N1 は完了**：単体の構造体、三分岐の単体的構造、恒等・合成則、0・1・2 単体の同値、
  面・退化の成分計算、集約入口とルート import を揃えた。
  **未完了は N2〜N6**。quasicategory 性、H⁰ 比較、右 pinched 写像空間、dg 関手性、
  自然変換のホモトピー、一点 dg 圏・複体圏での受入検査はまだ主張しない。

追加公開宣言の正確な型は次のとおり（証明引数の省略記号は N1a と同じ）。

<details>
<summary>N1d で追加した公開宣言の型（17 件）</summary>

```text
SerrePositivity.InfinityCategories.dgNerve.δ_data : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 2))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n + 1 })),
  ((CategoryTheory.ConcreteCategory.hom
          (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) i))
        s).toSimplexData =
    s.pullback i.succAboveOrderEmb.toOrderHom
SerrePositivity.InfinityCategories.dgNerve.σ_data : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 1))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n })),
  ((CategoryTheory.ConcreteCategory.hom
          (CategoryTheory.SimplicialObject.σ (SerrePositivity.InfinityCategories.dgNerve A D) i))
        s).toSimplexData =
    s.pullback i.predAboveOrderHom
SerrePositivity.InfinityCategories.dgNerve.δ_hom : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 2))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n + 1 })) (J : Finset (Fin (n + 1)))
  (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  let α := i.succAboveOrderEmb.toOrderHom;
  ((CategoryTheory.ConcreteCategory.hom
            (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) i))
          s).hom
      J a b k hJ ha hb hk =
    s.hom (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯
SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_inj : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 1))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n })) (J : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card)
  (hi : Set.InjOn ⇑i.predAboveOrderHom ↑J),
  let α := i.predAboveOrderHom;
  ((CategoryTheory.ConcreteCategory.hom
            (CategoryTheory.SimplicialObject.σ (SerrePositivity.InfinityCategories.dgNerve A D) i))
          s).hom
      J a b k hJ ha hb hk =
    s.hom (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯
SerrePositivity.InfinityCategories.dgNerve.σ_hom_eq_zero : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 1))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n })) (J : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  i.castSucc ∈ J →
    i.succ ∈ J →
      J.card ≠ 2 →
        ((CategoryTheory.ConcreteCategory.hom
                  (CategoryTheory.SimplicialObject.σ (SerrePositivity.InfinityCategories.dgNerve A D) i))
                s).hom
            J a b k hJ ha hb hk =
          0
SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_collapsed_pair : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (i : Fin (n + 1))
  (s : (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n })) (J : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  i.castSucc ∈ J →
    i.succ ∈ J →
      J.card = 2 →
        ((CategoryTheory.ConcreteCategory.hom
                  (CategoryTheory.SimplicialObject.σ (SerrePositivity.InfinityCategories.dgNerve A D) i))
                s).hom
            J a b k hJ ha hb hk ≍
          ↑(SerrePositivity.DifferentialGraded.unitElement A (s.obj (i.predAboveOrderHom b)))
SerrePositivity.InfinityCategories.DGNerve.TriangleData : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → Type (max u_1 u_2)
SerrePositivity.InfinityCategories.DGNerve.three_eq_univ : ∀ (I : Finset (Fin 3)), I.card = 3 → I = Finset.univ
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.edgeHom : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (a b : Fin (n + 1)) → a < b → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) 0)
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D 2),
  s.rhs Finset.univ 0 2 (-1) SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_1
      SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_2
      SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_3
      SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_4 =
    SerrePositivity.DifferentialGraded.compose A
        (s.edgeHom 1 2 SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_5)
        (s.edgeHom 0 1 SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_6)
        SerrePositivity.InfinityCategories.DGNerve.TriangleData._proof_1 -
      s.edgeHom 0 2 SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle._proof_7
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofTriangle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.TriangleData A D →
          SerrePositivity.InfinityCategories.DGNerve.SimplexData A D 2
@SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.TriangleData A D →
          SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2
@SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2 →
          SerrePositivity.InfinityCategories.DGNerve.TriangleData A D
@SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle_ofTriangle : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (t : SerrePositivity.InfinityCategories.DGNerve.TriangleData A D),
  (SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle t).toTriangle = t
@SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle_toTriangle : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2),
  SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle s.toTriangle = s
@SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.Simplex A D 2 ≃
          SerrePositivity.InfinityCategories.DGNerve.TriangleData A D
SerrePositivity.InfinityCategories.dgNerve.triangleEquiv : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := 2 }) ≃
          SerrePositivity.InfinityCategories.DGNerve.TriangleData A D
```

</details>

### N2a 保存（2026-10-17、既知のホーン成分と有限和、N2 は未完了）

HA Proposition 1.3.1.10 の充填に使う補題を追加した。`HornIndex` は利用可能な面の存在と
その添字の逆像、`HornFaces` はホーン単体の制限の自然性と面の選択によらない一致を証明する。
`HornData.vertexObj` と `HornData.recoverHom` はホーンから対象と既知の斉次成分の値を回収する。
`recoverHom` の成分ごとの選択独立性と各面への制限との一致は未証明である。

`Index.sign` は右側点数の負一冪。`sign_erase_swap` と `sum_double_erase` は二重削除の相殺、
`sign_double_cut` は Leibniz の符号を含む二重切断の係数の反転を示す。
`Algebra` に合成の加法・差・符号スカラーの法則を追加した。
`SimplexData.residual` は δf−rhs。微分の二乗が零であることから `differential_residual` を示す。
`HornEquation.missingComponent` は加法可換群内で欠けた成分を解く値で、
`sum_missingComponent` が最上位方程式の右辺の零、`missingComponent_eq` が N0 の式との一致を示す。

前提：dg 圏の結果は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
ホーンの対象・成分回収は任意の `σ : Λ[n+2,i] ⟶ dgNerve A D` に対する。
`recoverHom` は `2 ≤ I.card`、端点・次数の指定、`I ≠ univ` と `I ≠ univ.erase i` を要求する。
有限和の解は任意の加法可換群で `i ∈ K` を要求する。切断・削除の符号補題には、以下の型に
記した点の所属と大小関係を要求する。内部ホーンの充填そのものを前提にも結論にも加えていない。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3343 jobs、終了コード 0。
引き続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
既存 dg 則 5 件と自身の全 157 件の明示的公開宣言（今回 47 件追加）を監査し、
全 162 件とも依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
ルート import は N1d の 1 行をそのまま用い、この保存ではルートを編集しない。

未完了：回収した成分の選択独立性・各面との一致と既知方程式の保存、
削除と切断の混合項および三重合成項の有限和の整理を含む主残差恒等式、
未知の二成分の単体データへの組込みと欠けた面自身の方程式、ホーン貼合せ、
`Quasicategory (dgNerve A D)`。N2 の完了とは数えない。N3〜N6 も未完了。

今回の公開宣言名・正確な型（`#check @...` の出力。`⋯` は Lean が省略表示した証明引数で、
N1a と同じく対応する定義の命題証明を意味する。implicit 引数も `@` で表示）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.compose_add_left : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g g' : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A (g + g') f h =
    SerrePositivity.DifferentialGraded.compose A g f h + SerrePositivity.DifferentialGraded.compose A g' f h

@SerrePositivity.InfinityCategories.DGNerve.compose_add_right : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f f' : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A g (f + f') h =
    SerrePositivity.DifferentialGraded.compose A g f h + SerrePositivity.DifferentialGraded.compose A g f' h

@SerrePositivity.InfinityCategories.DGNerve.compose_sub_left : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g g' : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A (g - g') f h =
    SerrePositivity.DifferentialGraded.compose A g f h - SerrePositivity.DifferentialGraded.compose A g' f h

@SerrePositivity.InfinityCategories.DGNerve.compose_sub_right : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ}
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f f' : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A g (f - f') h =
    SerrePositivity.DifferentialGraded.compose A g f h - SerrePositivity.DifferentialGraded.compose A g f' h

@SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_left : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ} (c : ℤˣ)
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A (c • g) f h = c • SerrePositivity.DifferentialGraded.compose A g f h

@SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_right : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y z : D} {p q k : ℤ} (c : ℤˣ)
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A g (c • f) h = c • SerrePositivity.DifferentialGraded.compose A g f h

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.exists_covering_face : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] (I : Finset α) (i : α), (∃ j, j ≠ i ∧ j ∉ I) ↔ I ≠ Finset.univ ∧ I ≠ Finset.univ.erase i

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace : {n : ℕ} →
  (I : Finset (Fin (n + 1))) → (i : Fin (n + 1)) → I ≠ Finset.univ → I ≠ Finset.univ.erase i → Fin (n + 1)

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_ne : ∀ {n : ℕ} (I : Finset (Fin (n + 1)))
  (i : Fin (n + 1)) (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i),
  SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace I i hfull hmissing ≠ i

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_notMem : ∀ {n : ℕ} (I : Finset (Fin (n + 1)))
  (i : Fin (n + 1)) (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i),
  SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace I i hfull hmissing ∉ I

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.image_preimage : ∀ {n : ℕ} (I : Finset (Fin (n + 2))),
  ∀ j ∉ I, Finset.image j.succAbove (I.preimage j.succAbove ⋯) = I

@SerrePositivity.InfinityCategories.DGNerve.HornIndex.card_preimage : ∀ {n : ℕ} (I : Finset (Fin (n + 2))),
  ∀ j ∉ I, (I.preimage j.succAbove ⋯).card = I.card

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell : {m n : ℕ} →
  (i : Fin (n + 2)) →
    (θ : { len := m } ⟶ { len := n + 1 }) →
      (j : Fin (n + 2)) →
        j ≠ i →
          (∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j) →
            (SSet.horn (n + 1) i).toSSet.obj (Opposite.op { len := m })

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell_eq : ∀ {m n : ℕ} (i : Fin (n + 2))
  (θ : { len := m } ⟶ { len := n + 1 }) (j j' : Fin (n + 2)) (hji : j ≠ i) (hj'i : j' ≠ i)
  (hj : ∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j)
  (hj' : ∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j'),
  SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i θ j hji hj =
    SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i θ j' hj'i hj'

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_cell : ∀ {l m n : ℕ} (i : Fin (n + 2))
  (θ : { len := m } ⟶ { len := n + 1 }) (j : Fin (n + 2)) (hji : j ≠ i)
  (hj : ∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j) (α : { len := l } ⟶ { len := m }),
  (CategoryTheory.ConcreteCategory.hom ((SSet.horn (n + 1) i).toSSet.map α.op))
      (SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i θ j hji hj) =
    SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i (CategoryTheory.CategoryStruct.comp α θ) j hji ⋯

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_face : ∀ {m n : ℕ} (i : Fin (n + 2))
  (θ : { len := m } ⟶ { len := n + 1 }) (j : Fin (n + 2)) (hji : j ≠ i)
  (hj : ∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j),
  (CategoryTheory.ConcreteCategory.hom ((SSet.horn (n + 1) i).toSSet.map (SimplexCategory.factor_δ θ j).op))
      (SSet.horn.face i j hji) =
    SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i θ j hji hj

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_from_face : ∀ {m n : ℕ} {X : SSet} (i : Fin (n + 2))
  (σ : (SSet.horn (n + 1) i).toSSet ⟶ X) (θ : { len := m } ⟶ { len := n + 1 }) (j : Fin (n + 2)) (hji : j ≠ i)
  (hj : ∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j),
  (CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := m })))
      (SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell i θ j hji hj) =
    (CategoryTheory.ConcreteCategory.hom (X.map (SimplexCategory.factor_δ θ j).op))
      ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n }))) (SSet.horn.face i j hji))

@SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_independent : ∀ {m n : ℕ} {X : SSet} (i : Fin (n + 2))
  (σ : (SSet.horn (n + 1) i).toSSet ⟶ X) (θ : { len := m } ⟶ { len := n + 1 }) (j j' : Fin (n + 2)) (hji : j ≠ i)
  (hj'i : j' ≠ i),
  (∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j) →
    (∀ (k : Fin ({ len := m }.len + 1)), (SimplexCategory.Hom.toOrderHom θ) k ≠ j') →
      (CategoryTheory.ConcreteCategory.hom (X.map (SimplexCategory.factor_δ θ j).op))
          ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n }))) (SSet.horn.face i j hji)) =
        (CategoryTheory.ConcreteCategory.hom (X.map (SimplexCategory.factor_δ θ j').op))
          ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n }))) (SSet.horn.face i j' hj'i))

@SerrePositivity.InfinityCategories.DGNerve.HornData.map_const_face : ∀ {n : ℕ} (i j : Fin (n + 3)) (hji : j ≠ i)
  (k : Fin (n + 2)),
  (CategoryTheory.ConcreteCategory.hom ((SSet.horn (n + 2) i).toSSet.map ({ len := 0 }.const { len := n + 1 } k).op))
      (SSet.horn.face i j hji) =
    SSet.horn.const n i (j.succAbove k) (Opposite.op { len := 0 })

@SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            ((SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) → Fin (n + 3) → D

@SerrePositivity.InfinityCategories.DGNerve.HornData.face_obj : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j : Fin (n + 3)) (hji : j ≠ i)
  (k : Fin (n + 2)),
  ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)).obj k =
    SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ (j.succAbove k)

@SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              (j : Fin (n + 3)) →
                j ≠ i →
                  (J : Finset (Fin (n + 2))) →
                    (a b : Fin (n + 2)) →
                      (k : ℤ) →
                        (hJ : 2 ≤ J.card) →
                          a = J.min' ⋯ →
                            b = J.max' ⋯ →
                              k = 2 - ↑J.card →
                                ↑(SerrePositivity.DifferentialGraded.GradedHom A
                                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ (j.succAbove a))
                                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ (j.succAbove b)) k)

@SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j : Fin (n + 3)) (hji : j ≠ i)
  (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace σ j hji J a b k hJ ha hb hk ≍
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)).hom J a b k
      hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              (I : Finset (Fin (n + 3))) →
                (a b : Fin (n + 3)) →
                  (k : ℤ) →
                    (hI : 2 ≤ I.card) →
                      a = I.min' ⋯ →
                        b = I.max' ⋯ →
                          k = 2 - ↑I.card →
                            I ≠ Finset.univ →
                              I ≠ Finset.univ.erase i →
                                ↑(SerrePositivity.DifferentialGraded.GradedHom A
                                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ a)
                                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ b) k)

@SerrePositivity.InfinityCategories.DGNerve.Index.sign : {α : Type u_1} → [LinearOrder α] → Finset α → α → ℤˣ

@SerrePositivity.InfinityCategories.DGNerve.Index.right_filter_erase_le : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α}, j ≤ k → {x ∈ I.erase j | k < x} = {x ∈ I | k < x}

@SerrePositivity.InfinityCategories.DGNerve.Index.right_card_erase_lt : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α}, k ∈ I → j < k → {x ∈ I.erase k | j < x}.card + 1 = {x ∈ I | j < x}.card

@SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_of_lt : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α},
  k ∈ I →
    j < k →
      SerrePositivity.InfinityCategories.DGNerve.Index.sign I j *
          SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k =
        -(SerrePositivity.InfinityCategories.DGNerve.Index.sign I k *
            SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase k) j)

@SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_swap : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α},
  j ∈ I →
    k ∈ I →
      j ≠ k →
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j *
            SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k =
          -(SerrePositivity.InfinityCategories.DGNerve.Index.sign I k *
              SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase k) j)

@SerrePositivity.InfinityCategories.DGNerve.Index.double_erase_pair : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I : Finset α) (f : Finset α → M) {j k : α},
  j ∈ I →
    k ∈ I →
      j ≠ k →
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k • f ((I.erase j).erase k) +
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase k) j • f ((I.erase k).erase j) =
          0

@SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_erase : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  K ⊆ I →
    ∀ (f : Finset α → M),
      ∑ jk ∈ K.offDiag,
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I jk.1 •
            SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase jk.1) jk.2 • f ((I.erase jk.1).erase jk.2) =
        0

@SerrePositivity.InfinityCategories.DGNerve.Index.sign_right_cut : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α},
  j ≤ k →
    SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | j ≤ x}) k =
      SerrePositivity.InfinityCategories.DGNerve.Index.sign I k

@SerrePositivity.InfinityCategories.DGNerve.Index.right_cut_card : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {k : α}, k ∈ I → {x ∈ I | k ≤ x}.card = {x ∈ I | k < x}.card + 1

@SerrePositivity.InfinityCategories.DGNerve.Index.left_right_sign_card : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α}, j < k → {x ∈ {x ∈ I | x ≤ k} | j < x}.card + {x ∈ I | k < x}.card = {x ∈ I | j < x}.card

@SerrePositivity.InfinityCategories.DGNerve.Index.sign_double_cut : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α},
  k ∈ I →
    j < k →
      SerrePositivity.InfinityCategories.DGNerve.Index.sign I j *
          SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | j ≤ x}) k =
        -(SerrePositivity.InfinityCategories.DGNerve.Index.sign I k * (2 - ↑{x ∈ I | k ≤ x}.card).negOnePow *
            SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ k}) j)

@SerrePositivity.InfinityCategories.DGNerve.differential_squared : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {k : ℤ}
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  SerrePositivity.DifferentialGraded.differential A (SerrePositivity.DifferentialGraded.differential A f) = 0

@SerrePositivity.InfinityCategories.DGNerve.differential_add : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {k : ℤ}
  (f g : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  SerrePositivity.DifferentialGraded.differential A (f + g) =
    SerrePositivity.DifferentialGraded.differential A f + SerrePositivity.DifferentialGraded.differential A g

@SerrePositivity.InfinityCategories.DGNerve.differential_sub : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {k : ℤ}
  (f g : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  SerrePositivity.DifferentialGraded.differential A (f - g) =
    SerrePositivity.DifferentialGraded.differential A f - SerrePositivity.DifferentialGraded.differential A g

@SerrePositivity.InfinityCategories.DGNerve.differential_units_smul : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {k : ℤ} (c : ℤˣ)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  SerrePositivity.DifferentialGraded.differential A (c • f) = c • SerrePositivity.DifferentialGraded.differential A f

@SerrePositivity.InfinityCategories.DGNerve.differential_sum : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {ι : Type u_3} {x y : D} {k : ℤ} (S : Finset ι)
  (f : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  SerrePositivity.DifferentialGraded.differential A (∑ t ∈ S, f t) =
    ∑ t ∈ S, SerrePositivity.DifferentialGraded.differential A (f t)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_eq_zero_iff : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  s.residual I a b k hI ha hb hk = 0 ↔
    SerrePositivity.DifferentialGraded.differential A (s.hom I a b k hI ha hb hk) = s.rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_residual : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  SerrePositivity.DifferentialGraded.differential A (s.residual I a b k hI ha hb hk) =
    -SerrePositivity.DifferentialGraded.differential A (s.rhs I a b k hI ha hb hk)

@SerrePositivity.InfinityCategories.DGNerve.Simplex.residual_eq_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
  (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card), s.residual I a b k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent : {α : Type u_1} →
  [LinearOrder α] → {M : Type u_2} → [AddCommGroup M] → Finset α → Finset α → α → (α → M) → (α → M) → M

@SerrePositivity.InfinityCategories.DGNerve.HornEquation.sum_missingComponent : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  ∀ i ∈ K,
    ∀ (deleted composed : α → M),
      ∑ j ∈ K,
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
            ((if j = i then
                SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent I K i deleted composed
              else deleted j) -
              composed j) =
        0

@SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent_eq : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  ∀ i ∈ K,
    ∀ (deleted composed : α → M),
      SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent I K i deleted composed =
        ∑ j ∈ K,
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I i •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign I j • composed j -
          ∑ j ∈ K.erase i,
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I i •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign I j • deleted j
```

### N2b 保存（2026-10-17、回収成分の整合性と既知方程式、N2 は未完了）

`HornComponents.lean` は、同じ大域部分集合に対応する二面の斉次成分の一致
`HornData.face_hom_heq` と、回収した値の任意の面の成分との一致
`HornData.recoverHom_heq_face` を証明する。比較の補助として有限部分集合の順序による
列挙を使うが、単体の表現・添字は §3 の有限部分集合のままとし、設計を変更していない。
`HomFamily.heq_of_pointwise`、`SimplexData.hom_heq_of_indices`、
`Simplex.hom_heq_of_eq`、`Simplex.hom_heq_of_pullback_eq` はその従属型の移送の補題。

`HornPartial.lean` の `HornData.knownData` は既知成分を回収し、未知の全体集合と欠けた面の
成分を仮に零としておくデータ。`knownData_pullback_face` は任意の利用可能な面への制限が
元の面の単体データと等しいことを示す。`knownData_equation_image` はその像の部分集合の
方程式、`knownData_equation` は全体集合と欠けた面以外の任意の部分集合の方程式を証明する。
これにより N2a の「回収成分の選択独立性・各面との一致・既知方程式の保存」は解消した。

前提：`A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`、
`σ : Λ[n+2,i] ⟶ dgNerve A D`。面の比較では面番号が i と異なり、二つの部分集合の
大域での像が等しいことを要求する。成分には従来と同じ端点・濃度・次数の証明を要求する。
`knownData_equation` はさらに `I ≠ univ`、`I ≠ univ.erase i` を要求する。
この保存の定理は i が内部点であることを必要としない。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3345 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 169 件の明示的公開宣言（今回 12 件追加）と既存 dg 則 5 件、全 174 件の依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。対象ソースの lint 警告なし。
この保存でもルート import は編集しない。

未完了：`knownData` は充填単体ではなく、未知の二成分の方程式は主張しない。
欠けた面の成分を最上位方程式の解へ置き換えたデータ、その変更による既知方程式の保存、
主残差恒等式と欠けた面自身の方程式、ホーンの貼合せと `Quasicategory` instance が残る。
N2 全体の完了とは数えない。N3〜N6 も未完了。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` は N1a と同じく Lean が
省略表示した命題証明の引数。型と前提を省略して成果を強めた表記ではない）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.HomFamily.heq_of_pointwise : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {obj obj' : Fin (n + 1) → D},
  obj = obj' →
    ∀ (f : SerrePositivity.InfinityCategories.DGNerve.HomFamily A D obj)
      (g : SerrePositivity.InfinityCategories.DGNerve.HomFamily A D obj'),
      (∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯)
          (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card), f I a b k hI ha hb hk ≍ g I a b k hI ha hb hk) →
        f ≍ g

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I J : Finset (Fin (n + 1)))
  (a b c d : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card)
  (hJ : 2 ≤ J.card) (hc : c = J.min' ⋯) (hd : d = J.max' ⋯) (hk' : k = 2 - ↑J.card),
  I = J → a = c → b = d → s.hom I a b k hI ha hb hk ≍ s.hom J c d k hJ hc hd hk'

@SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_eq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  {s t : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n},
  s = t →
    ∀ (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
      (hk : k = 2 - ↑J.card), s.hom J a b k hJ ha hb hk ≍ t.hom J a b k hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_pullback_eq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {l m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D m)
  (t : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (α : Fin (l + 1) →o Fin (m + 1))
  (β : Fin (l + 1) →o Fin (n + 1)),
  s.pullback α = t.pullback β →
    ∀ (J : Finset (Fin (l + 1))) (a b : Fin (l + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
      (hk : k = 2 - ↑J.card) (hα : Set.InjOn ⇑α ↑J) (hβ : Set.InjOn ⇑β ↑J),
      s.hom (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯ ≍ t.hom (Finset.image (⇑β) J) (β a) (β b) k ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.HornData.face_hom_heq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j l : Fin (n + 3)) (hji : j ≠ i)
  (hli : l ≠ i) (J L : Finset (Fin (n + 2))) (a b c d : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯)
  (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card) (hL : 2 ≤ L.card) (hc : c = L.min' ⋯) (hd : d = L.max' ⋯)
  (hk' : k = 2 - ↑L.card),
  Finset.image j.succAbove J = Finset.image l.succAbove L →
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)).hom J a b k
        hJ ha hb hk ≍
      ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i l hli)).hom L c d
        k hL hc hd hk'

@SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom_heq_face : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (I : Finset (Fin (n + 3)))
  (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card)
  (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) (j : Fin (n + 3)) (hji : j ≠ i)
  (J : Finset (Fin (n + 2))) (c d : Fin (n + 2)) (hJ : 2 ≤ J.card) (hc : c = J.min' ⋯) (hd : d = J.max' ⋯)
  (hk' : k = 2 - ↑J.card),
  Finset.image j.succAbove J = I →
    SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom σ I a b k hI ha hb hk hfull hmissing ≍
      ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)).hom J c d
        k hJ hc hd hk'

@SerrePositivity.InfinityCategories.DGNerve.HornData.knownData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            ((SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 2)

@SerrePositivity.InfinityCategories.DGNerve.HornData.image_known : ∀ {n : ℕ} {i : Fin (n + 3)} (j : Fin (n + 3)),
  j ≠ i →
    ∀ (J : Finset (Fin (n + 2))),
      Finset.image j.succAbove J ≠ Finset.univ ∧ Finset.image j.succAbove J ≠ Finset.univ.erase i

@SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_hom_heq_face : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j : Fin (n + 3)) (hji : j ≠ i)
  (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  ((SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).pullback j.succAboveOrderEmb.toOrderHom).hom J a b
      k hJ ha hb hk ≍
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)).hom J a b k
      hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_pullback_face : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j : Fin (n + 3)) (hji : j ≠ i),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).pullback j.succAboveOrderEmb.toOrderHom =
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 })))
        (SSet.horn.face i j hji)).toSimplexData

@SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation_image : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (j : Fin (n + 3)),
  j ≠ i →
    ∀ (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
      (hk : k = 2 - ↑J.card),
      SerrePositivity.DifferentialGraded.differential A
          ((SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).hom (Finset.image j.succAbove J)
            (j.succAbove a) (j.succAbove b) k ⋯ ⋯ ⋯ ⋯) =
        (SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).rhs (Finset.image j.succAbove J)
          (j.succAbove a) (j.succAbove b) k ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (I : Finset (Fin (n + 3)))
  (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  I ≠ Finset.univ →
    I ≠ Finset.univ.erase i →
      SerrePositivity.DifferentialGraded.differential A
          ((SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).hom I a b k hI ha hb hk) =
        (SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).rhs I a b k hI ha hb hk
```

### N2c 保存（2026-10-17、未知成分の補正と最上位方程式、N2 は未完了）

`Replace.lean` は対象族を固定した一集合の成分の置換 `SimplexData.replace` と、その集合以外の
成分の保存、像が指定集合を避ける引き戻しの保存、指定集合自身の右辺の保存を証明する。
`EquationTransfer.lean` は一集合の方程式を `SimplexData.Equation` に束ね、面の制限が単体なら
その像の集合で方程式が成り立つことを示す。`HornData.equation_of_faces` は既知の面への制限
だけから既知方程式を回収する。`replace_missing_pullback_face` と `replace_missing_equation` は
欠けた面の成分を任意に置き換えても、既知の面と既知方程式が保たれることを証明する。

`TopCorrection.lean` の `term_replace_of_ne`、`term_replace_same`、`rhs_replace` は、
I の内部点 i と M=I\{i} に対し `F'_I-F_I=ε(I,i)(f'_M-f_M)` を証明する。
ここで F_I は単体の方程式の右辺。左右切断は両端を同時に含まないので M と異なり、
有限和では i の削除項だけが変わる。`correctingHom` は `f'_M=f_M-ε(I,i)F_I` を与え、
`rhs_solveTop` は補正後の右辺が零であることを示す。既知データでは f_M=0 なので、
この補正は N0 の最上位方程式の解である。

`HornFilling.lean` の `HornData.fillerData` は、内部ホーンの既知データにこの補正を適用する。
`fillerData_pullback_face` は既知の面との一致、`fillerData_known_equation` は全ての既知方程式、
`fillerData_top_zero` は最上位成分の零、`fillerData_top_equation` は最上位方程式を証明する。
残る欠けた面の方程式を明示的な前提として、`fillerOfMissingEquation` は実際の単体を作り、
`extensionOfMissingEquation` は米田対応と `horn.hom_ext` で元のホーン写像の延長を与える。
**この前提付きの延長を、無条件の内部ホーン充填や N2 の完成とは数えない。**

前提：dg 圏は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
補正は集合 I の端点 a,b と次数 k に加え `i ∈ I`、`a < i`、`i < b` を要求する。
充填候補は `σ : Λ[n+2,i] ⟶ dgNerve A D`、`0 < i`、`i < Fin.last (n+2)` に対する。
既知集合の方程式には `I ≠ univ`、`I ≠ univ.erase i` を要求する。
末尾三宣言の単体・面の一致・延長には、追加で
`(fillerData σ h0 hlast).Equation (univ.erase i)` という未証明の前提を要求する。
全ての従属する端点・濃度・次数の証明は、以下の正確な型に表示した通り。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3349 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 197 件の明示的公開宣言（今回 28 件追加）と既存 dg 則 5 件、全 202 件の依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。新規四モジュールの対象ビルドに警告なし。
ルートは変更せず、集約入口は `HornFilling` を公開する。

未完了：主残差恒等式と、それによる `fillerData` の欠けた面自身の方程式の無条件の証明、
その証明を適用した無条件の延長と `Quasicategory (dgNerve A D)` instance。
貼合せの構成は上記の前提付きで検証したが、内部ホーンの充填存在はまだ証明していない。
N2 全体と N3〜N6 は未完了。§3 の設計と他節は変更しない。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` は N1a と同じく Lean が
省略表示した命題証明引数。前提付きの結果の前提もそのまま表示する）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (M : Finset (Fin (n + 1))) →
              ((a b : Fin (n + 1)) →
                  (k : ℤ) →
                    (hM : 2 ≤ M.card) →
                      a = M.min' ⋯ →
                        b = M.max' ⋯ →
                          k = 2 - ↑M.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k)) →
                SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_same : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (M : Finset (Fin (n + 1)))
  (f :
    (a b : Fin (n + 1)) →
      (k : ℤ) →
        (hM : 2 ≤ M.card) →
          a = M.min' ⋯ →
            b = M.max' ⋯ → k = 2 - ↑M.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k))
  (a b : Fin (n + 1)) (k : ℤ) (hM : 2 ≤ M.card) (ha : a = M.min' ⋯) (hb : b = M.max' ⋯) (hk : k = 2 - ↑M.card),
  (s.replace M f).hom M a b k hM ha hb hk = f a b k hM ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_of_ne : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (M : Finset (Fin (n + 1)))
  (f :
    (a b : Fin (n + 1)) →
      (k : ℤ) →
        (hM : 2 ≤ M.card) →
          a = M.min' ⋯ →
            b = M.max' ⋯ → k = 2 - ↑M.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k))
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯)
  (hk : k = 2 - ↑I.card), I ≠ M → (s.replace M f).hom I a b k hI ha hb hk = s.hom I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_pullback_of_omits : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (M : Finset (Fin (n + 1)))
  (f :
    (a b : Fin (n + 1)) →
      (k : ℤ) →
        (hM : 2 ≤ M.card) →
          a = M.min' ⋯ →
            b = M.max' ⋯ → k = 2 - ↑M.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k))
  (α : Fin (m + 1) →o Fin (n + 1)), ∀ j ∈ M, (∀ (x : Fin (m + 1)), α x ≠ j) → (s.replace M f).pullback α = s.pullback α

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_self : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1)))
  (f :
    (a b : Fin (n + 1)) →
      (k : ℤ) →
        (hI : 2 ≤ I.card) →
          a = I.min' ⋯ →
            b = I.max' ⋯ → k = 2 - ↑I.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k))
  (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card)
  (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  (s.replace I f).term I a b k hI ha hb hk j hj haj hjb = s.term I a b k hI ha hb hk j hj haj hjb

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace_self : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1)))
  (f :
    (a b : Fin (n + 1)) →
      (k : ℤ) →
        (hI : 2 ≤ I.card) →
          a = I.min' ⋯ →
            b = I.max' ⋯ → k = 2 - ↑I.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k))
  (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  (s.replace I f).rhs I a b k hI ha hb hk = s.rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.Equation : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} → SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n → Finset (Fin (n + 1)) → Prop

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_image_of_pullback : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (α : Fin (m + 1) →o Fin (n + 1))
  (t : SerrePositivity.InfinityCategories.DGNerve.Simplex A D m),
  s.pullback α = t.toSimplexData → ∀ (J : Finset (Fin (m + 1))), Set.InjOn ⇑α ↑J → s.Equation (Finset.image (⇑α) J)

@SerrePositivity.InfinityCategories.DGNerve.HornData.equation_of_faces : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D)
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 2)),
  (∀ (j : Fin (n + 3)) (hji : j ≠ i),
      s.pullback j.succAboveOrderEmb.toOrderHom =
        ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 })))
            (SSet.horn.face i j hji)).toSimplexData) →
    ∀ (I : Finset (Fin (n + 3))), I ≠ Finset.univ → I ≠ Finset.univ.erase i → s.Equation I

@SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_pullback_face : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  {i : Fin (n + 3)} (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D)
  (f :
    (a b : Fin (n + 3)) →
      (k : ℤ) →
        (hM : 2 ≤ (Finset.univ.erase i).card) →
          a = (Finset.univ.erase i).min' ⋯ →
            b = (Finset.univ.erase i).max' ⋯ →
              k = 2 - ↑(Finset.univ.erase i).card →
                ↑(SerrePositivity.DifferentialGraded.GradedHom A
                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ a)
                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ b) k))
  (j : Fin (n + 3)) (hji : j ≠ i),
  ((SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).replace (Finset.univ.erase i) f).pullback
      j.succAboveOrderEmb.toOrderHom =
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 })))
        (SSet.horn.face i j hji)).toSimplexData

@SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D)
  (f :
    (a b : Fin (n + 3)) →
      (k : ℤ) →
        (hM : 2 ≤ (Finset.univ.erase i).card) →
          a = (Finset.univ.erase i).min' ⋯ →
            b = (Finset.univ.erase i).max' ⋯ →
              k = 2 - ↑(Finset.univ.erase i).card →
                ↑(SerrePositivity.DifferentialGraded.GradedHom A
                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ a)
                    (SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj σ b) k))
  (I : Finset (Fin (n + 3))),
  I ≠ Finset.univ →
    I ≠ Finset.univ.erase i →
      ((SerrePositivity.InfinityCategories.DGNerve.HornData.knownData σ).replace (Finset.univ.erase i) f).Equation I

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_of_ne : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  ∀ i ∈ I,
    a < i →
      i < b →
        ∀
          (f :
            (c d : Fin (n + 1)) →
              (q : ℤ) →
                (hM : 2 ≤ (I.erase i).card) →
                  c = (I.erase i).min' ⋯ →
                    d = (I.erase i).max' ⋯ →
                      q = 2 - ↑(I.erase i).card →
                        ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj c) (s.obj d) q))
          (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b),
          j ≠ i →
            (s.replace (I.erase i) f).term I a b k hI ha hb hk j hj haj hjb = s.term I a b k hI ha hb hk j hj haj hjb

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_same : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (i : Fin (n + 1))
  (hi : i ∈ I) (hai : a < i) (hib : i < b)
  (f :
    (c d : Fin (n + 1)) →
      (q : ℤ) →
        (hM : 2 ≤ (I.erase i).card) →
          c = (I.erase i).min' ⋯ →
            d = (I.erase i).max' ⋯ →
              q = 2 - ↑(I.erase i).card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj c) (s.obj d) q)),
  (s.replace (I.erase i) f).term I a b k hI ha hb hk i hi hai hib - s.term I a b k hI ha hb hk i hi hai hib =
    SerrePositivity.InfinityCategories.DGNerve.Index.sign I i •
      (f a b (k + 1) ⋯ ⋯ ⋯ ⋯ - s.hom (I.erase i) a b (k + 1) ⋯ ⋯ ⋯ ⋯)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (i : Fin (n + 1))
  (hi : i ∈ I) (hai : a < i) (hib : i < b)
  (f :
    (c d : Fin (n + 1)) →
      (q : ℤ) →
        (hM : 2 ≤ (I.erase i).card) →
          c = (I.erase i).min' ⋯ →
            d = (I.erase i).max' ⋯ →
              q = 2 - ↑(I.erase i).card → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj c) (s.obj d) q)),
  (s.replace (I.erase i) f).rhs I a b k hI ha hb hk - s.rhs I a b k hI ha hb hk =
    SerrePositivity.InfinityCategories.DGNerve.Index.sign I i •
      (f a b (k + 1) ⋯ ⋯ ⋯ ⋯ - s.hom (I.erase i) a b (k + 1) ⋯ ⋯ ⋯ ⋯)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (i : Fin (n + 1)) →
                            i ∈ I →
                              a < i →
                                i < b →
                                  (c d : Fin (n + 1)) →
                                    (q : ℤ) →
                                      (hM : 2 ≤ (I.erase i).card) →
                                        c = (I.erase i).min' ⋯ →
                                          d = (I.erase i).max' ⋯ →
                                            q = 2 - ↑(I.erase i).card →
                                              ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj c) (s.obj d) q)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom_self : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (i : Fin (n + 1))
  (hi : i ∈ I) (hai : a < i) (hib : i < b) (hM : 2 ≤ (I.erase i).card) (haM : a = (I.erase i).min' ⋯)
  (hbM : b = (I.erase i).max' ⋯) (hkM : k + 1 = 2 - ↑(I.erase i).card),
  s.correctingHom I a b k hI ha hb hk i hi hai hib a b (k + 1) hM haM hbM hkM =
    s.hom (I.erase i) a b (k + 1) hM haM hbM hkM -
      SerrePositivity.InfinityCategories.DGNerve.Index.sign I i • s.rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.solveTop : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (i : Fin (n + 1)) →
                            i ∈ I → a < i → i < b → SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_solveTop : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (i : Fin (n + 1))
  (hi : i ∈ I) (hai : a < i) (hib : i < b), (s.solveTop I a b k hI ha hb hk i hi hai hib).rhs I a b k hI ha hb hk = 0

SerrePositivity.InfinityCategories.DGNerve.HornData.univ_min_zero : ∀ (n : ℕ) (h : Finset.univ.Nonempty),
  0 = Finset.univ.min' h

SerrePositivity.InfinityCategories.DGNerve.HornData.univ_max_last : ∀ (n : ℕ) (h : Finset.univ.Nonempty),
  Fin.last (n + 2) = Finset.univ.max' h

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            ((SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              0 < i → i < Fin.last (n + 2) → SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 2)

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_pullback_face : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hji : j ≠ i),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).pullback j.succAboveOrderEmb.toOrderHom =
    ((CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 })))
        (SSet.horn.face i j hji)).toSimplexData

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_known_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)) (I : Finset (Fin (n + 3))),
  I ≠ Finset.univ →
    I ≠ Finset.univ.erase i → (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation I

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)) (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ Finset.univ.card) (ha : a = Finset.univ.min' ⋯)
  (hb : b = Finset.univ.max' ⋯) (hk : k = 2 - ↑Finset.univ.card),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).hom Finset.univ a b k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation Finset.univ

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              (h0 : 0 < i) →
                (hlast : i < Fin.last (n + 2)) →
                  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation
                      (Finset.univ.erase i) →
                    SerrePositivity.InfinityCategories.DGNerve.Simplex A D (n + 2)

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation_face : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2))
  (hmissing :
    (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation (Finset.univ.erase i))
  (j : Fin (n + 3)) (hji : j ≠ i),
  (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) j))
      (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation σ h0 hlast hmissing) =
    (CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)

@SerrePositivity.InfinityCategories.DGNerve.HornData.extensionOfMissingEquation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation (Finset.univ.erase i) →
    ∃ τ, σ = CategoryTheory.CategoryStruct.comp (SSet.horn (n + 2) i).ι τ
```

### N2d 保存（2026-10-17、残差展開と相殺の有限和、N2 は未完了）

`LinearBoundary.lean` は内部点集合 `Index.interior` と、適切な端点・次数・濃度で元の
斉次成分を返し、それ以外で零となる補助評価 `SimplexData.homOrZero` を定義する。
これは有限和の計算の補助であり、§3 の単体の表現と添字は変更していない。
`linearBoundary_squared` は実際の斉次成分の削除部分を二度適用する和の零を示す。
証明では二重和を相異なる点の組に移し、既存の符号反転と対合を使う。

`BoundaryDecomposition.lean` の `cutCompose` と `quadraticBoundary` は切断合成の全域化と
その符号付き和。`rhs_eq_linear_sub_quadratic` は元の右辺 F_I を削除部分 L_I と合成部分 Q_I の
差 F_I=L_I-Q_I に分解する。`differential_cutCompose` は通常順合成の Leibniz 則、
`differential_rhs` はこの分解の微分を与える。

`CompositionCancellation.lean` は、共通の値にそろえた削除・切断の混合項の係数と二重和の相殺
`sum_mixed_cancel`、二重切断の二重和の相殺 `sum_double_cut_cancel` を証明する。
`cubic_compose_cancel` は実際の三つの斉次射の二つの結合順の寄与が相殺することを示す。
これらを元の `rhsContribution` の入れ子の切断集合と次数へ接続する証明はまだない。

`ResidualExpansion.lean` は R_I=δf_I-F_I として、各内部点 j の寄与の微分を
`residualContribution` と `rhsContribution` に分解する。削除集合を E、左右切断を L,R、
右成分の次数を q とすると、それぞれ ε(I,j)(R_E−R_R∘f_L−(−1)^q f_R∘R_L) と
ε(I,j)(F_E−F_R∘f_L−(−1)^q f_R∘F_L)。
`differential_term` は各項、`differential_rhs_expansion` は有限和全体について
δF_I=Σ residualContribution+Σ rhsContribution を証明する。
主残差恒等式に必要な実際の Σ rhsContribution=0 は未証明であり、上記の係数の相殺だけで
この未証明部分を完了と数えない。

前提：dg 圏の結果は `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
`homOrZero` と `linearBoundary_squared` は任意の I,a,b,k に定義・適用できる。
元の方程式との一致と残差展開には `2 ≤ I.card`、端点の最小・最大、次数 `k=2−|I|` を要求し、
各寄与にはさらに内部点 `j ∈ I` と `a < j < b` を要求する。
係数と有限和の相殺は任意の線形順序と加法可換群で、型に示した所属・大小関係と `K ⊆ I` の下。
三重合成の相殺はさらに右端の射の次数 `r=2−|I.filter(k≤·)|` と合計次数の等式を要求する。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3353 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 221 件の明示的公開宣言（今回 24 件追加）と既存 dg 則 5 件、全 226 件の依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。新規四モジュールの対象ビルドは警告なし。
ルートは編集せず、集約入口で `ResidualExpansion` を公開する。

未完了：実際の Σ rhsContribution の集合・端点・次数を相殺二重和にそろえて総和を零とすること、
主残差恒等式を用いた `fillerData` の欠けた面自身の方程式の証明、無条件のホーン充填と
`Quasicategory (dgNerve A D)` instance。N2 および N3〜N6 は未完了。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` は N1a と同じく Lean が
省略表示した命題証明引数。条件を省略して主張を強めていない）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.Index.interior : {α : Type u_1} →
  [LinearOrder α] → Finset α → α → α → Finset α

@SerrePositivity.InfinityCategories.DGNerve.Index.interior_erase : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) (a b j : α),
  SerrePositivity.InfinityCategories.DGNerve.Index.interior (I.erase j) a b =
    (SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b).erase j

@SerrePositivity.InfinityCategories.DGNerve.Index.sum_offDiag_eq : ∀ {α : Type u_1} [inst : DecidableEq α]
  {M : Type u_2} [inst_1 : AddCommMonoid M] (K : Finset α) (f : α → α → M),
  ∑ jk ∈ K.offDiag, f jk.1 jk.2 = ∑ j ∈ K, ∑ k ∈ K.erase j, f j k

@SerrePositivity.InfinityCategories.DGNerve.Index.nested_double_erase : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  K ⊆ I →
    ∀ (f : Finset α → M),
      ∑ j ∈ K,
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
            ∑ k ∈ K.erase j,
              SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k • f ((I.erase j).erase k) =
        0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) → (k : ℤ) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) k)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero_eq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  s.homOrZero I a b k = s.hom I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) →
                (k : ℤ) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary_squared : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
      SerrePositivity.InfinityCategories.DGNerve.Index.sign I j • s.linearBoundary (I.erase j) a b (k + 1) =
    0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) →
                (k : ℤ) → Fin (n + 1) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.quadraticBoundary : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) →
                (k : ℤ) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_linear_sub_cut : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1))
  (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  s.term I a b k hI ha hb hk j hj haj hjb =
    SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
      (s.homOrZero (I.erase j) a b (k + 1) - s.cutCompose I a b k j)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_eq_linear_sub_quadratic : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  s.rhs I a b k hI ha hb hk = s.linearBoundary I a b k - s.quadraticBoundary I a b k

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_cutCompose : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (j : Fin (n + 1)) (hsum : 2 - ↑{x ∈ I | x ≤ j}.card + (2 - ↑{x ∈ I | j ≤ x}.card) = k + 1),
  SerrePositivity.DifferentialGraded.differential A (s.cutCompose I a b k j) =
    SerrePositivity.DifferentialGraded.compose A
        (SerrePositivity.DifferentialGraded.differential A
          (s.homOrZero ({x ∈ I | j ≤ x}) j b (2 - ↑{x ∈ I | j ≤ x}.card)))
        (s.homOrZero ({x ∈ I | x ≤ j}) a j (2 - ↑{x ∈ I | x ≤ j}.card)) ⋯ +
      (2 - ↑{x ∈ I | j ≤ x}.card).negOnePow •
        SerrePositivity.DifferentialGraded.compose A (s.homOrZero ({x ∈ I | j ≤ x}) j b (2 - ↑{x ∈ I | j ≤ x}.card))
          (SerrePositivity.DifferentialGraded.differential A
            (s.homOrZero ({x ∈ I | x ≤ j}) a j (2 - ↑{x ∈ I | x ≤ j}.card)))
          ⋯

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  SerrePositivity.DifferentialGraded.differential A (s.rhs I a b k hI ha hb hk) =
    ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
          SerrePositivity.DifferentialGraded.differential A (s.homOrZero (I.erase j) a b (k + 1)) -
      ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
          SerrePositivity.DifferentialGraded.differential A (s.cutCompose I a b k j)

@SerrePositivity.InfinityCategories.DGNerve.Index.sign_mixed_right : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) {j k : α},
  j ∈ I →
    k ∈ I →
      k < j →
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j *
            SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k =
          -(SerrePositivity.InfinityCategories.DGNerve.Index.sign I k *
              SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | k ≤ x}) j)

@SerrePositivity.InfinityCategories.DGNerve.Index.mixed_right_cancel : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I : Finset α) {j k : α},
  j ∈ I →
    k ∈ I →
      k < j →
        ∀ (z : M),
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
                SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k • z +
              SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
                SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | k ≤ x}) j • z =
            0

@SerrePositivity.InfinityCategories.DGNerve.Index.mixed_left_cancel : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I : Finset α) {j k : α},
  k ∈ I →
    j < k →
      ∀ (z : M),
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k • z +
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
              (2 - ↑{x ∈ I | k ≤ x}.card).negOnePow •
                SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ k}) j • z =
          0

@SerrePositivity.InfinityCategories.DGNerve.Index.sum_mixed_cancel : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  K ⊆ I →
    ∀ (f : α → α → M),
      ∑ j ∈ K,
              SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
                ∑ k ∈ K.erase j, SerrePositivity.InfinityCategories.DGNerve.Index.sign (I.erase j) k • f j k +
            ∑ k ∈ K,
              SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
                ∑ j ∈ K with k < j, SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | k ≤ x}) j • f j k +
          ∑ k ∈ K,
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
              (2 - ↑{x ∈ I | k ≤ x}.card).negOnePow •
                ∑ j ∈ K with j < k, SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ k}) j • f j k =
        0

@SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_cut_cancel : ∀ {α : Type u_1} [inst : LinearOrder α]
  {M : Type u_2} [inst_1 : AddCommGroup M] (I K : Finset α),
  K ⊆ I →
    ∀ (f : α → α → M),
      ∑ j ∈ K,
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
              ∑ k ∈ K with j < k, SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | j ≤ x}) k • f j k +
          ∑ k ∈ K,
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
              (2 - ↑{x ∈ I | k ≤ x}.card).negOnePow •
                ∑ j ∈ K with j < k, SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ k}) j • f j k =
        0

@SerrePositivity.InfinityCategories.DGNerve.cubic_compose_cancel : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {α : Type u_3} [inst_2 : LinearOrder α] (I : Finset α)
  {j k : α},
  k ∈ I →
    j < k →
      ∀ {w x y z : D} {p q r m : ℤ} (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A w x p))
        (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y q))
        (h : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z r)) (hr : r = 2 - ↑{x ∈ I | k ≤ x}.card)
        (hm : p + q + r = m),
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
              SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | j ≤ x}) k •
                SerrePositivity.DifferentialGraded.compose A (SerrePositivity.DifferentialGraded.compose A h g ⋯) f ⋯ +
            SerrePositivity.InfinityCategories.DGNerve.Index.sign I k •
              r.negOnePow •
                SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ k}) j •
                  SerrePositivity.DifferentialGraded.compose A h (SerrePositivity.DifferentialGraded.compose A g f ⋯)
                    hm =
          0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (j : Fin (n + 1)) →
                            j ∈ I →
                              a < j →
                                j < b →
                                  ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1 + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (j : Fin (n + 1)) →
                            j ∈ I →
                              a < j →
                                j < b →
                                  ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1 + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_term : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1))
  (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  SerrePositivity.DifferentialGraded.differential A (s.term I a b k hI ha hb hk j hj haj hjb) =
    s.residualContribution I a b k hI ha hb hk j hj haj hjb + s.rhsContribution I a b k hI ha hb hk j hj haj hjb

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs_expansion : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  SerrePositivity.DifferentialGraded.differential A (s.rhs I a b k hI ha hb hk) =
    (∑ j, if h : a < ↑j ∧ ↑j < b then s.residualContribution I a b k hI ha hb hk ↑j ⋯ ⋯ ⋯ else 0) +
      ∑ j, if h : a < ↑j ∧ ↑j < b then s.rhsContribution I a b k hI ha hb hk ↑j ⋯ ⋯ ⋯ else 0
```

### N2e・N2 完了（2026-10-17）：主残差恒等式と無条件の内部ホーン充填

`CutErasure.lean` は、削除後の切断合成を元の左右切断の片側の削除として表し、
集合・次数・合成値を全て同定する。`CutBoundary.lean` は一つ高い次数の境界族の
左右合成 `cutBoundary` を定義し、その線形部分を共通の削除後の合成の二重和へ移す。
`SimplexData.mixedBoundary_eq_zero` が
**実際の単体成分**の削除・切断の混合総和の零を証明する。

`NestedCut.lean` は二重切断の中央の集合と中間次数を同定し、通常順合成の結合律を適用する。
`CubicBoundary.lean` は実際の三重合成の総和の零を証明する。
これらと N2d の二重削除の零から、`Bianchi.lean` の `sum_rhsContribution_eq_zero` が
実際の純代数寄与の総和の零、`bianchi` が主残差恒等式
δF_I=Σ residualContribution を証明する。

`HornResidual.lean` の `HornData.fillerData_missing_equation` は、これを充填候補の全体集合に
適用する。全体方程式と δ²=0 から左辺は零、左右切断と既知削除面の残差は既知方程式により零。
唯一残る ε(V,i)R_{V\{i}} の零から、符号を再び掛けて欠けた面の残差の零を得る。
**未証明の方程式を前提としていない。** これで N2a〜N2d の未完了項目を解消した。

`Quasicategory.lean` の公開 API：
- `dgNerve.filler` は任意の内部ホーンから充填単体を構成する。
- `dgNerve.filler_face` は全ての利用可能な面が元のホーン面と一致することを示す。
- `dgNerve.hornFilling` は `σ = Λ[n+2,i].ι ≫ τ` を満たす標準単体上の延長 τ の存在を示す。
  貼合せは既に検証済みの `horn.hom_ext` による構成に、今回の無条件の方程式の証明を渡す。
- 名前付き instance `dgNerve.instQuasicategory` は `Quasicategory (dgNerve A D)`。

前提：任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]` のみ。
充填 API には `σ : Λ[n+2,i] ⟶ dgNerve A D` と内部点の `0 < i`、`i < Fin.last (n+2)` を要求する。
補助計算の点の所属・大小関係・次数の和は以下の型の通り。instance には内部点や方程式の
追加仮定はない。有界性・平坦性・体・標数の追加仮定もない。宇宙は `SSet.{max u v}`。
最上位成分の零と最上位方程式は N2c、既知の面からの回収・整合性・既知方程式は N2a〜N2b、
残る欠けた面の方程式はこの保存で証明済みであり、§2 の N2 の全項目を満たした。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3432 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 246 件の明示的公開宣言（今回 25 件追加、名前付き instance を含む）と既存 dg 則 5 件、
全 251 件の依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
さらに自身の全 DGNerve ソースの明示的宣言を再走査し、246 件全てが監査に含まれることを確認。
監査末尾の一般の環・dg 圏の `example` で instance が `inferInstance` により得られることも検証。
今回の対象モジュールの最終ビルドには警告なし。ルートは編集せず、既存の一行 import により
新しい集約入口の quasicategory instance を公開する。

未完了：N3 の H⁰ とのホモトピー圏の比較、N5 の dg 関手・厳密自然変換・充満部分圏との両立、
N4 の右 pinched 写像空間と Kan 性・π₀、N6 の具体例と最終監査。
N2 は完了したが、N0〜N6 全体の目標は未完了であり継続する。
§3 の設計、他節、他チャットのファイルは変更していない。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` は N1a と同じく Lean が
省略表示した命題証明引数。無条件の充填 API と instance の全前提も表示する）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.compose_sum_left : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {ι : Type u_3} {x y z : D} {p q k : ℤ} (S : Finset ι)
  (g : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A (∑ i ∈ S, g i) f h =
    ∑ i ∈ S, SerrePositivity.DifferentialGraded.compose A (g i) f h

@SerrePositivity.InfinityCategories.DGNerve.compose_sum_right : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {ι : Type u_3} {x y z : D} {p q k : ℤ} (S : Finset ι)
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (h : p + q = k),
  SerrePositivity.DifferentialGraded.compose A g (∑ i ∈ S, f i) h =
    ∑ i ∈ S, SerrePositivity.DifferentialGraded.compose A g (f i) h

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_left : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (j l : Fin (n + 1)),
  j ∈ I →
    j < l →
      ∀ (hsum : 2 - ↑{x ∈ I | x ≤ l}.card + (2 - ↑{x ∈ I | l ≤ x}.card) = k + 1),
        s.cutCompose (I.erase j) a b (k + 1) l =
          SerrePositivity.DifferentialGraded.compose A (s.homOrZero ({x ∈ I | l ≤ x}) l b (2 - ↑{x ∈ I | l ≤ x}.card))
            (s.homOrZero ({x ∈ I | x ≤ l}.erase j) a l (2 - ↑{x ∈ I | x ≤ l}.card + 1)) ⋯

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_right : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (j l : Fin (n + 1)),
  j ∈ I →
    l < j →
      ∀ (hsum : 2 - ↑{x ∈ I | x ≤ l}.card + (2 - ↑{x ∈ I | l ≤ x}.card) = k + 1),
        s.cutCompose (I.erase j) a b (k + 1) l =
          SerrePositivity.DifferentialGraded.compose A
            (s.homOrZero ({x ∈ I | l ≤ x}.erase j) l b (2 - ↑{x ∈ I | l ≤ x}.card + 1))
            (s.homOrZero ({x ∈ I | x ≤ l}) a l (2 - ↑{x ∈ I | x ≤ l}.card)) ⋯

@SerrePositivity.InfinityCategories.DGNerve.Index.interior_right_cut : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) (a b j : α),
  a < j →
    SerrePositivity.InfinityCategories.DGNerve.Index.interior ({x ∈ I | j ≤ x}) j b =
      {x ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b | j < x}

@SerrePositivity.InfinityCategories.DGNerve.Index.interior_left_cut : ∀ {α : Type u_1} [inst : LinearOrder α]
  (I : Finset α) (a b j : α),
  j < b →
    SerrePositivity.InfinityCategories.DGNerve.Index.interior ({x ∈ I | x ≤ j}) a j =
      {x ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b | x < j}

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (Finset (Fin (n + 1)) →
                (a b : Fin (n + 1)) →
                  (k : ℤ) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))) →
              Finset (Fin (n + 1)) →
                (a b : Fin (n + 1)) →
                  (k : ℤ) →
                    Fin (n + 1) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1 + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  k = 2 - ↑I.card →
    ∀ l ∈ I,
      a < l →
        l < b →
          s.cutBoundary s.linearBoundary I a b k l =
            ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b with l < j,
                SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | l ≤ x}) j •
                  s.cutCompose (I.erase j) a b (k + 1) l +
              (2 - ↑{x ∈ I | l ≤ x}.card).negOnePow •
                ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b with j < l,
                  SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ l}) j •
                    s.cutCompose (I.erase j) a b (k + 1) l

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.mixedBoundary_eq_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  k = 2 - ↑I.card →
    ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I j • s.quadraticBoundary (I.erase j) a b (k + 1) +
        ∑ l ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
          SerrePositivity.InfinityCategories.DGNerve.Index.sign I l • s.cutBoundary s.linearBoundary I a b k l =
      0

@SerrePositivity.InfinityCategories.DGNerve.compose_assoc_of_sum : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {w x y z : D} {p q r a b t : ℤ}
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A w x p))
  (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y q))
  (h : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z r)) (ha : p + q = a) (hb : q + r = b) (ht : a + r = t),
  SerrePositivity.DifferentialGraded.compose A h (SerrePositivity.DifferentialGraded.compose A g f ha) ht =
    SerrePositivity.DifferentialGraded.compose A (SerrePositivity.DifferentialGraded.compose A h g hb) f ⋯

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  Fin (n + 1) →
                    Fin (n + 1) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1 + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutLeft : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            Finset (Fin (n + 1)) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  Fin (n + 1) →
                    Fin (n + 1) → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1 + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight_eq_left : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  k = 2 - ↑I.card →
    ∀ (j l : Fin (n + 1)), j ∈ I → l ∈ I → j < l → s.nestedCutRight I a b k j l = s.nestedCutLeft I a b k j l

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_quadratic : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  k = 2 - ↑I.card →
    ∀ l ∈ I,
      a < l →
        l < b →
          s.cutBoundary s.quadraticBoundary I a b k l =
            ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b with l < j,
                SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | l ≤ x}) j •
                  s.nestedCutRight I a b k l j +
              (2 - ↑{x ∈ I | l ≤ x}.card).negOnePow •
                ∑ j ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b with j < l,
                  SerrePositivity.InfinityCategories.DGNerve.Index.sign ({x ∈ I | x ≤ l}) j •
                    s.nestedCutLeft I a b k j l

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cubicBoundary_eq_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ),
  k = 2 - ↑I.card →
    ∑ l ∈ SerrePositivity.InfinityCategories.DGNerve.Index.interior I a b,
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I l • s.cutBoundary s.quadraticBoundary I a b k l =
      0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution_eq_boundaries : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1))
  (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  s.rhsContribution I a b k hI ha hb hk j hj haj hjb =
    SerrePositivity.InfinityCategories.DGNerve.Index.sign I j •
      (s.linearBoundary (I.erase j) a b (k + 1) - s.quadraticBoundary (I.erase j) a b (k + 1) -
          s.cutBoundary s.linearBoundary I a b k j +
        s.cutBoundary s.quadraticBoundary I a b k j)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.sum_rhsContribution_eq_zero : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  (∑ j, if h : a < ↑j ∧ ↑j < b then s.rhsContribution I a b k hI ha hb hk ↑j ⋯ ⋯ ⋯ else 0) = 0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.bianchi : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  SerrePositivity.DifferentialGraded.differential A (s.rhs I a b k hI ha hb hk) =
    ∑ j, if h : a < ↑j ∧ ↑j < b then s.residualContribution I a b k hI ha hb hk ↑j ⋯ ⋯ ⋯ else 0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_zero_of_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))),
  s.Equation I →
    ∀ (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
      s.residual I a b k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution_of_cuts : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1))
  (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  s.Equation ({x ∈ I | x ≤ j}) →
    s.Equation ({x ∈ I | j ≤ x}) →
      s.residualContribution I a b k hI ha hb hk j hj haj hjb =
        SerrePositivity.InfinityCategories.DGNerve.Index.sign I j • s.residual (I.erase j) a b (k + 1) ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_missing_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)),
  (SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData σ h0 hlast).Equation (Finset.univ.erase i)

SerrePositivity.InfinityCategories.dgNerve.filler : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          {i : Fin (n + 3)} →
            ((SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) →
              0 < i →
                i < Fin.last (n + 2) →
                  (SerrePositivity.InfinityCategories.dgNerve A D).obj (Opposite.op { len := n + 2 })

SerrePositivity.InfinityCategories.dgNerve.filler_face : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D) (h0 : 0 < i)
  (hlast : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hji : j ≠ i),
  (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) j))
      (SerrePositivity.InfinityCategories.dgNerve.filler A D σ h0 hlast) =
    (CategoryTheory.ConcreteCategory.hom (σ.app (Opposite.op { len := n + 1 }))) (SSet.horn.face i j hji)

SerrePositivity.InfinityCategories.dgNerve.hornFilling : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} {i : Fin (n + 3)}
  (σ : (SSet.horn (n + 2) i).toSSet ⟶ SerrePositivity.InfinityCategories.dgNerve A D),
  0 < i → i < Fin.last (n + 2) → ∃ τ, σ = CategoryTheory.CategoryStruct.comp (SSet.horn (n + 2) i).ι τ

SerrePositivity.InfinityCategories.dgNerve.instQuasicategory : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  (SerrePositivity.InfinityCategories.dgNerve A D).Quasicategory
```

### N3a 保存（2026-10-18、端点付きの辺と境界関係、N3 は未完了）

namespace は `DGNerve.HomotopyComparison`。
`TruncatedEdges.lean` は `twoTruncation=(SSet.truncation 2).obj (dgNerve A D)` と、
端点の固定された辺を両端の対象間の閉零元へ移送する `edgeCycle`、逆向きの `edgeOfCycle`、
両向きの逆則、同値 `edgeCycleEquiv` を構成する。端点は元の零単体 x,y のまま固定し、
対象だけを x.obj 0,y.obj 0 として読む。単体の表現は変更していない。

`TruncatedTriangles.lean` は二単体の三つの面の計算、
次数 −1 の射 t と δt=g∘f−h から合成構造を作る `compStructOfHomotopy`、
逆向きの `homotopy_of_compStruct`、存在の同値 `compStruct_iff_homotopy` を証明する。
`EdgeHomotopy.lean` は閉零圏への対象・辺の写像 `vertexClosed`、`edgeClosed` と同値
`edgeClosedEquiv` を与え、退化辺の閉零成分が dg 単位であることを `edgeCycle_id` で示す。
`homotopicL_iff_exists` と `homotopicR_iff_exists` は、左右の辺ホモトピーを δt=f−g の
原始元の存在に翻訳する。原始元の次数は −1。定理の型ではその微分を `.d (-1) 0` と書く。
`boundary_iff_exists` は既存の H⁰ の境界判定を使い、
`homotopicL_iff_boundary` と `homotopicR_iff_boundary` はそれぞれ既存の
`boundaryRelation A D (edgeClosed f) (edgeClosed g)` との同値を証明する。
既存の dg 理論や H⁰ の定義は変更していない。

前提：任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]`。
辺は固定された二つの零単体 x,y の間、三角形では x,y,z と対応する三辺を指定する。
合成構造の逆構成には閉次数零成分の合成と第三辺の差の原始元と、その微分の等式を要求する。
ホモトピーと境界関係の同値には追加の方程式の前提はない。
型の移送の補題には明示的な対象の等式のみを要求する。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3437 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 274 件の明示的公開宣言（今回 28 件追加）と既存 dg 則 5 件、全 279 件の依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。全 DGNerve ソースを再走査し監査の包含を確認。
監査末尾で既存の quasicategory instance と、新たに二次切断の `Quasicategory₂` instance が
`inferInstance` により得られることを検証。新規三モジュールの最終対象ビルドに警告なし。
ルートは編集せず、集約入口に `EdgeHomotopy` を追加する。

未完了：N3 の実際の合成と `Edge.comp` の比較、h=0 の明示的な合成構造、
商上の両向きの関手と圏同値 `HomotopyCategory₂ (...) ≌ HomotopyCategory A D`。
射とホモトピー関係の比較だけを、圏同値の完成と数えない。N3 全体および N4〜N6 は未完了。
§3 の設計と他節は変更しない。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` や生成された `_proof_...` は
Lean が表示する命題証明引数。元の端点付きの型と全前提をそのまま表示する）：

```lean
SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → SSet.Truncated 2

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj : {D : Type u_1} → D → D → Fin 2 → D

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })}
  (e : SSet.Truncated.Edge x y), e.edge.obj 0 = x.obj 0

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_target_obj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })}
  (e : SSet.Truncated.Edge x y), e.edge.obj 1 = y.obj 0

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property :=
                    SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })} →
          SSet.Truncated.Edge x y →
            ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)))

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property :=
                    SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })} →
          ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0))) →
            SSet.Truncated.Edge x y

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_edgeOfCycle : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })}
  (f :
    ↥(SerrePositivity.DifferentialGraded.zeroCycles
        (SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)))),
  SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle f) =
    f

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle_edgeCycle : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })}
  (e : SSet.Truncated.Edge x y),
  SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle e) =
    e

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycleEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (x y :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property :=
                    SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj._proof_1 })) →
          SSet.Truncated.Edge x y ≃
            ↥(SerrePositivity.DifferentialGraded.zeroCycles
                (SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)))

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.tripleObj : {D : Type u_1} → D → D → D → Fin 3 → D

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face01 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (t : SerrePositivity.InfinityCategories.DGNerve.TriangleData A D),
  (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) 2))
      (SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle t) =
    SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj (t.obj 0) (t.obj 1)) t.f01

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face12 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (t : SerrePositivity.InfinityCategories.DGNerve.TriangleData A D),
  (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) 0))
      (SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle t) =
    SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj (t.obj 1) (t.obj 2)) t.f12

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face02 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (t : SerrePositivity.InfinityCategories.DGNerve.TriangleData A D),
  (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.SimplicialObject.δ (SerrePositivity.InfinityCategories.dgNerve A D) 1))
      (SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle t) =
    SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj (t.obj 0) (t.obj 2)) t.f02

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y z :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property :=
                    SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_1 })} →
          (f : SSet.Truncated.Edge x y) →
            (g : SSet.Truncated.Edge y z) →
              (h : SSet.Truncated.Edge x z) →
                (t : ↑(SerrePositivity.DifferentialGraded.GradedHom A (x.obj 0) (z.obj 0) (-1))) →
                  SerrePositivity.DifferentialGraded.differential A t =
                      SerrePositivity.DifferentialGraded.compose A
                          (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g))
                          (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f))
                          SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_2 -
                        ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle h) →
                    f.CompStruct g h

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopy_of_compStruct : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y z :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_1 })}
  {f : SSet.Truncated.Edge x y} {g : SSet.Truncated.Edge y z} {h : SSet.Truncated.Edge x z} (c : f.CompStruct g h),
  ∃ t,
    SerrePositivity.DifferentialGraded.differential A t =
      SerrePositivity.DifferentialGraded.compose A
          (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g))
          (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f))
          SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_2 -
        ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle h)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStruct_iff_homotopy : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y z :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_1 })}
  (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) (h : SSet.Truncated.Edge x z),
  Nonempty (f.CompStruct g h) ↔
    ∃ t,
      SerrePositivity.DifferentialGraded.differential A t =
        SerrePositivity.DifferentialGraded.compose A
            (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g))
            (↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f))
            SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy._proof_2 -
          ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle h)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
            (Opposite.op
              { obj := { len := 0 },
                property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 }) →
          SerrePositivity.DifferentialGraded.ClosedCategory A D

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })} →
          SSet.Truncated.Edge x y →
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed x ⟶
              SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed y)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_cycle : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (e : SSet.Truncated.Edge x y),
  (SerrePositivity.DifferentialGraded.closedHomEquiv A D
        (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed x)
        (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed y))
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed e) =
    SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle e

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosedEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (x y :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })) →
          SSet.Truncated.Edge x y ≃
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed x ⟶
              SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed y)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.castCycle_val_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y x' y' : D} (hx : x = x')
  (hy : y = y')
  (f : ↥(SerrePositivity.DifferentialGraded.zeroCycles (SerrePositivity.DifferentialGraded.homObject A D x y))),
  ↑(cast ⋯ f) ≍ ↑f

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_val_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (e : SSet.Truncated.Edge x y),
  ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle e) ≍
    ↑(SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle e.edge 0 1
        SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_val_heq._proof_1)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_id : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (x :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })),
  SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle (SSet.Truncated.Edge.id x) =
    SerrePositivity.DifferentialGraded.unitElement A (x.obj 0)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_exists : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (f g : SSet.Truncated.Edge x y),
  SSet.Truncated.HomotopicL f g ↔
    ∃ t,
      (CategoryTheory.ConcreteCategory.hom
            ((SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)).d (-1) 0))
          t =
        ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f) -
          ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_exists : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (f g : SSet.Truncated.Edge x y),
  SSet.Truncated.HomotopicR f g ↔
    ∃ t,
      (CategoryTheory.ConcreteCategory.hom
            ((SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)).d (-1) 0))
          t =
        ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f) -
          ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.boundary_iff_exists : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (f g : SSet.Truncated.Edge x y),
  SerrePositivity.DifferentialGraded.boundaryRelation A D
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed f)
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed g) ↔
    ∃ t,
      (CategoryTheory.ConcreteCategory.hom
            ((SerrePositivity.DifferentialGraded.homObject A D (x.obj 0) (y.obj 0)).d (-1) 0))
          t =
        ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle f) -
          ↑(SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_boundary : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (f g : SSet.Truncated.Edge x y),
  SSet.Truncated.HomotopicL f g ↔
    SerrePositivity.DifferentialGraded.boundaryRelation A D
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed f)
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_boundary : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed._proof_1 })}
  (f g : SSet.Truncated.Edge x y),
  SSet.Truncated.HomotopicR f g ↔
    SerrePositivity.DifferentialGraded.boundaryRelation A D
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed f)
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed g)
```

### N3b・N3 完了（2026-10-18）：合成の比較と H⁰ との圏同値

namespace は `DGNerve.HomotopyComparison`。
`ClosedComposition.lean` は既存の閉零圏の恒等射と合成の次数零評価を、dg 単位と通常順合成に
それぞれ同定する。`strictComp` は実際の閉零射の合成を辺との同値の逆で戻した対角辺。
`strictCompStruct` は f,g,strictComp f g と **h=0** による明示的な三角形の合成構造。
`comp_homotopic_strictComp` は `CompStruct.comp_unique` をこれと Mathlib の合成構造に適用し、
選択された `Edge.comp` が実際の合成と左ホモトピックであることを証明する。

`HomotopyCategory.lean` の `nerveHomotopyCategory A D` は
`SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (dgNerve A D))`。
`toH0` はその辺のホモトピー類を、既存の閉零射の境界類へ送る関手。
N3a の関係の同値で商へ降ろし、恒等辺の単位の計算と上記の合成比較で関手性を証明する。
`toH0_homMk` は代表元での計算。`toH0_faithful` は H⁰ の等式が境界関係であることから、
`toH0_full` は任意の閉零代表元に辺との同値の逆を適用して、
`toH0_essSurj` は任意の dg 対象の定値零単体から、それぞれ三つの性質を証明する。
`toH0_isEquivalence` はこれらをまとめた名前付き instance。

`equivalence : nerveHomotopyCategory A D ≌ DifferentialGraded.HomotopyCategory A D`
を構成した。`fromH0` は逆関手、`unitIso` と `counitIso` は両方向の往復の自然同型。
逆関手と自然同型は、証明済みの充満・忠実・本質的全射性から Mathlib の一般の圏同値の
構成で得る。したがって両向きの関手とその逆の確認まで含む。
N3a の辺・左右ホモトピー・境界関係の比較と合わせ、§2 の N3 の全項目を満たした。

前提：任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]` のみ。
閉零合成の計算は既存の閉零圏の対象・合成可能な射を指定する。
辺の合成比較は二次切断の三頂点と合成可能な二辺を指定する。
関手・圏同値・逆関手・単位余単位には追加の方程式・有界性・平坦性・体・標数の前提はない。
前提付きの結果を圏同値と数えていない。対象宇宙・射宇宙は既存の二つの圏のものをそのまま使う。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3439 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 292 件の明示的公開宣言（今回 18 件追加、名前付き instance を含む）と既存 dg 則 5 件、
全 297 件の依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
全 DGNerve ソースを再走査し、292 件の宣言全てが監査されることを確認した。
新規二モジュールの最終ビルドには警告なし。既存の dg 圏の H⁰ の定義は変更していない。
ルートは編集せず、集約入口で `HomotopyCategory` を公開する。

未完了：N5 の dg 関手・厳密自然変換・充満部分圏との両立、N4 の右 pinched 写像空間と
Kan 性・π₀、N6 の具体例と最終監査。N0〜N3 は完了したが全体の目標は未完了。
§3 の設計と他節、他チャットのファイルは変更していない。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` や `_proof_...` は N3a と同じく
Lean の命題証明引数。両方向の関手と自然同型の全前提をそのまま表示する）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_id : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (x : SerrePositivity.DifferentialGraded.ClosedCategory A D),
  (SerrePositivity.DifferentialGraded.closedHomEquiv A D x x) (CategoryTheory.CategoryStruct.id x) =
    SerrePositivity.DifferentialGraded.unitElement A
      (CategoryTheory.ForgetEnrichment.to (SerrePositivity.DifferentialGraded.Complex A) x)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_comp : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y z : SerrePositivity.DifferentialGraded.ClosedCategory A D} (f : x ⟶ y) (g : y ⟶ z),
  ↑((SerrePositivity.DifferentialGraded.closedHomEquiv A D x z) (CategoryTheory.CategoryStruct.comp f g)) =
    SerrePositivity.DifferentialGraded.compose A (↑((SerrePositivity.DifferentialGraded.closedHomEquiv A D y z) g))
      (↑((SerrePositivity.DifferentialGraded.closedHomEquiv A D x y) f))
      SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_comp._proof_1

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  (x :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id._proof_1 })),
  SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed (SSet.Truncated.Edge.id x) =
    CategoryTheory.CategoryStruct.id (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed x)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y z :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id._proof_1 })} →
          SSet.Truncated.Edge x y → SSet.Truncated.Edge y z → SSet.Truncated.Edge x z

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_strictComp : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y z :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id._proof_1 })}
  (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z),
  SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp f g) =
    CategoryTheory.CategoryStruct.comp (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed f)
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictCompStruct : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y z :
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
              (Opposite.op
                { obj := { len := 0 },
                  property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id._proof_1 })} →
          (f : SSet.Truncated.Edge x y) →
            (g : SSet.Truncated.Edge y z) →
              f.CompStruct g (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp f g)

@SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.comp_homotopic_strictComp : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y z :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id._proof_1 })}
  (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z),
  SSet.Truncated.HomotopicL (f.comp g) (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp f g)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → Type (max u_2 u_1)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        CategoryTheory.Functor (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory A D)
          (SerrePositivity.DifferentialGraded.HomotopyCategory A D)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_homMk : ∀ (A : Type u_1) [inst : CommRing A]
  (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  {x y :
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D).obj
      (Opposite.op
        { obj := { len := 0 },
          property := SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_homMk._proof_1 })}
  (f : SSet.Truncated.Edge x y),
  (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).map
      (SSet.Truncated.HomotopyCategory₂.homMk f) =
    (SerrePositivity.DifferentialGraded.toHomotopy A D).map
      (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed f)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_faithful : ∀ (A : Type u_1) [inst : CommRing A]
  (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).Faithful

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_full : ∀ (A : Type u_1) [inst : CommRing A]
  (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).Full

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_essSurj : ∀ (A : Type u_1) [inst : CommRing A]
  (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).EssSurj

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_isEquivalence : ∀ (A : Type u_1) [inst : CommRing A]
  (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).IsEquivalence

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.equivalence : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory A D ≌
          SerrePositivity.DifferentialGraded.HomotopyCategory A D

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.fromH0 : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        CategoryTheory.Functor (SerrePositivity.DifferentialGraded.HomotopyCategory A D)
          (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory A D)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.counitIso : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.fromH0 A D).comp
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D) ≅
          CategoryTheory.Functor.id (SerrePositivity.DifferentialGraded.HomotopyCategory A D)

SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.unitIso : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        CategoryTheory.Functor.id
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory A D) ≅
          (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0 A D).comp
            (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.fromH0 A D)
```

### N5a 保存（2026-10-18、dg 関手の写像と充満部分圏、N5 は未完了）

§2 の基本順序 N0→N1→N2→N3→N5→N4→N6 に従い、N3 完了後に N5 の関手性へ進む。
`FunctorMapping.lean` は dg 関手の微分・通常順合成の保存と、対象の等式で移送した単位の保存を
証明する。`SimplexData.map` は各対象と Hom 複体の各斉次元を写し、`map_term`、`map_rhs` が
符号付き項と右辺の保存、`Simplex.map` が単体の方程式の保存を与える。

`Functor.lean` はデータの恒等・合成の法則と `SimplexData.map_pullback` を証明する。
最後の自然性では単射の像の成分・潰れた二点の単位・その他の零の全三分岐を扱う。
`dgNerve.map` はこれを各次元に適用する単体的写像であり、
`dgNerve.map_id` と `dgNerve.map_comp` が恒等 dg 関手と合成の保存を示す。

`FullSubcategory.lean` の `DGNerve.fullOnObjects A D P` は、全頂点の対象が P を満たす単体による
部分複体。引き戻しで対象を前合成するためこの条件は保存される。
`liftToFull` はこの条件を満たす任意の単体を `DGFullSubcategory D P` の単体へ持ち上げ、
Hom 複体と全方程式は元のものを使う。`map_inclusion_lift` は包含で元へ戻ること、
`range_inclusion` は包含の dg nerve の像の部分複体が `fullOnObjects` と等しいことを証明する。

前提：任意の `A : Type u`、`[CommRing A]` と各対象型の `[DGCategory A ...]`。
単体データと単体の像は D,E,T の対象宇宙をそれぞれ v,w,t として独立に扱う。
`dgNerve.map` などの SSet の射は Mathlib の通常の `nerve` の写像と同じく、
D,E,T を共通の対象宇宙 v に置く。SSet の宇宙は設計通り `max u v` で、§3 の変更はない。
充満部分圏の結果は任意の `P : D → Prop`。持ち上げには全頂点の P の証明を要求するが、
像の等式には対象の性質 P 以外の閉性・平坦性・有界性・標数の仮定はない。

検証：`set -e` と `set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3447 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 309 件の明示的公開宣言（今回 17 件追加）と既存 dg 則 5 件、全 314 件の依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。全 DGNerve ソースを再走査し監査の包含を確認。
新規三モジュールの最終ビルドは警告なし。既存 dg 理論とルートは編集せず、集約入口に
`FullSubcategory` を追加して関手の写像と像の定理を公開する。

未完了：N5 の厳密 dg 自然変換から `dgNerve A D ⊗ Δ[1] ⟶ dgNerve A E` への
単体的ホモトピーの構成。N5 の全体の完了とは数えない。
N4 の右 pinched 写像空間・Kan 性・π₀、N6 の具体例と最終監査も未完了。
他節、他の計画ファイル、他チャットのファイルは変更していない。

今回の全公開宣言名・正確な型（`#check @...` の出力。`⋯` は従来と同じ命題証明引数。
対象宇宙と dg 圏構造を含む全前提をそのまま表示する）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.map_differential : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] (F : SerrePositivity.DifferentialGraded.DGFunctor A D E)
  {x y : D} {k : ℤ} (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  (CategoryTheory.ConcreteCategory.hom ((F.map x y).f (k + 1))) (SerrePositivity.DifferentialGraded.differential A f) =
    SerrePositivity.DifferentialGraded.differential A ((CategoryTheory.ConcreteCategory.hom ((F.map x y).f k)) f)

@SerrePositivity.InfinityCategories.DGNerve.map_compose : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] (F : SerrePositivity.DifferentialGraded.DGFunctor A D E)
  {x y z : D} {p q k : ℤ} (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z q))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y p)) (hk : p + q = k),
  (CategoryTheory.ConcreteCategory.hom ((F.map x z).f k)) (SerrePositivity.DifferentialGraded.compose A g f hk) =
    SerrePositivity.DifferentialGraded.compose A ((CategoryTheory.ConcreteCategory.hom ((F.map y z).f q)) g)
      ((CategoryTheory.ConcreteCategory.hom ((F.map x y).f p)) f) hk

@SerrePositivity.InfinityCategories.DGNerve.map_unit_of_heq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] (F : SerrePositivity.DifferentialGraded.DGFunctor A D E)
  {x y : D} (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y 0)),
  x = y →
    f ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A y) →
      (CategoryTheory.ConcreteCategory.hom ((F.map x y).f 0)) f ≍
        ↑(SerrePositivity.DifferentialGraded.unitElement A (F.obj y))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            {n : ℕ} →
              SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n →
                SerrePositivity.DifferentialGraded.DGFunctor A D E →
                  SerrePositivity.InfinityCategories.DGNerve.SimplexData A E n

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_term : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n)
  (F : SerrePositivity.DifferentialGraded.DGFunctor A D E) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
  (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1)) (hj : j ∈ I)
  (haj : a < j) (hjb : j < b),
  (CategoryTheory.ConcreteCategory.hom ((F.map (s.obj a) (s.obj b)).f (k + 1)))
      (s.term I a b k hI ha hb hk j hj haj hjb) =
    (s.map F).term I a b k hI ha hb hk j hj haj hjb

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_rhs : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n)
  (F : SerrePositivity.DifferentialGraded.DGFunctor A D E) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
  (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  (CategoryTheory.ConcreteCategory.hom ((F.map (s.obj a) (s.obj b)).f (k + 1))) (s.rhs I a b k hI ha hb hk) =
    (s.map F).rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.Simplex.map : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            {n : ℕ} →
              SerrePositivity.InfinityCategories.DGNerve.Simplex A D n →
                SerrePositivity.DifferentialGraded.DGFunctor A D E →
                  SerrePositivity.InfinityCategories.DGNerve.Simplex A E n

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_id : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n),
  s.map (SerrePositivity.DifferentialGraded.DGFunctor.id D) = s

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_comp : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  {E : Type u_3} {T : Type u_4} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  [inst_3 : SerrePositivity.DifferentialGraded.DGCategory A T] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n)
  (F : SerrePositivity.DifferentialGraded.DGFunctor A D E) (G : SerrePositivity.DifferentialGraded.DGFunctor A E T),
  s.map (F.comp G) = (s.map F).map G

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_pullback : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n)
  (F : SerrePositivity.DifferentialGraded.DGFunctor A D E) (α : Fin (m + 1) →o Fin (n + 1)),
  (s.pullback α).map F = (s.map F).pullback α

@SerrePositivity.InfinityCategories.dgNerve.map : {A : Type u_1} →
  [inst : CommRing A] →
    {D E : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
          SerrePositivity.DifferentialGraded.DGFunctor A D E →
            (SerrePositivity.InfinityCategories.dgNerve A D ⟶ SerrePositivity.InfinityCategories.dgNerve A E)

@SerrePositivity.InfinityCategories.dgNerve.map_id : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D],
  SerrePositivity.InfinityCategories.dgNerve.map (SerrePositivity.DifferentialGraded.DGFunctor.id D) =
    CategoryTheory.CategoryStruct.id (SerrePositivity.InfinityCategories.dgNerve A D)

@SerrePositivity.InfinityCategories.dgNerve.map_comp : ∀ {A : Type u_1} [inst : CommRing A] {D E T : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  [inst_3 : SerrePositivity.DifferentialGraded.DGCategory A T] (F : SerrePositivity.DifferentialGraded.DGFunctor A D E)
  (G : SerrePositivity.DifferentialGraded.DGFunctor A E T),
  SerrePositivity.InfinityCategories.dgNerve.map (F.comp G) =
    CategoryTheory.CategoryStruct.comp (SerrePositivity.InfinityCategories.dgNerve.map F)
      (SerrePositivity.InfinityCategories.dgNerve.map G)

SerrePositivity.InfinityCategories.DGNerve.fullOnObjects : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (D → Prop) → (SerrePositivity.InfinityCategories.dgNerve A D).Subcomplex

SerrePositivity.InfinityCategories.DGNerve.liftToFull : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (P : D → Prop) →
          {n : ℕ} →
            (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) →
              (∀ (i : Fin (n + 1)), P (s.obj i)) →
                SerrePositivity.InfinityCategories.DGNerve.Simplex A
                  (SerrePositivity.DifferentialGraded.DGFullSubcategory D P) n

SerrePositivity.InfinityCategories.DGNerve.map_inclusion_lift : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] (P : D → Prop) {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (hs : ∀ (i : Fin (n + 1)), P (s.obj i)),
  (SerrePositivity.InfinityCategories.DGNerve.liftToFull A D P s hs).map
      (SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A D P) =
    s

SerrePositivity.InfinityCategories.DGNerve.range_inclusion : ∀ (A : Type u_1) [inst : CommRing A] (D : Type u_2)
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] (P : D → Prop),
  SSet.Subcomplex.range
      (SerrePositivity.InfinityCategories.dgNerve.map
        (SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A D P)) =
    SerrePositivity.InfinityCategories.DGNerve.fullOnObjects A D P
```

### N5b：厳密 dg 自然変換の単体的ホモトピー、N5 完了（2026-10-18）

`StrictNatTrans.lean` は閉次数零成分と全斉次射に対する厳密自然性を持つ専用構造体を定義した。
`phaseObj` は零相で F、一相で G の対象を取り、`transition` は同じ相なら各 dg 関手の写像、
零相から一相へは η の終端成分と F の像の合成を取る。三つの相の組の評価、零・差・
整数単位スカラー・有限和・微分・合成・単位の保存を証明した。
混合相の合成保存では厳密自然性と dg 合成の結合律を使い、微分保存では成分の閉性と
Leibniz 則を使う。自然変換の成分を可逆とは仮定しない。

`NatTransSimplex.lean` は任意の単体 s と単調な二相の選択 β から単体を作る。
切れ目をまたぐ任意濃度の成分に `transition` を適用し、符号付き削除項と切断合成の保存から
全単体方程式を証明する。引き戻しとの自然性は単射・潰れた辺の単位・その他の零の
全三分岐で証明した。したがって面だけでなく全ての退化とも可換である。

`NatTrans.lean` は標準一単体の単体を β と読み、
`homotopyMap : dgNerve A D ⊗ Δ[1] ⟶ dgNerve A E` を構成した。
`homotopyMap_zero` と `homotopyMap_one` は端点が F と G の像であることを示し、
`homotopy` は Mathlib の `SSet.Homotopy (dgNerve.map F) (dgNerve.map G)` を与える。
これで N5a に残っていた厳密 dg 自然変換の項目が解消し、N5 を完了した。

前提：任意の可換環 A、任意の dg 圏 D,E、dg 関手 F,G と厳密 dg 自然変換 η のみ。
二相と単体の構成では対象宇宙 v,w を独立に扱い、SSet の射とホモトピーでは N5a と同じく
D,E の対象宇宙を共通の v に置く。可逆性・有界性・平坦性・標数の追加仮定はない。
§3 の設計上の決定は変更していない。

検証：`set -e`、`set -o pipefail` の下で集約対象
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3460 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
新規 26 宣言を含め、担当ディレクトリの全 335 個の明示的公開宣言と再利用する既存 5 則、
合計 340 件の公理表示を検査した。全件の依存公理は標準三公理
`propext`・`Classical.choice`・`Quot.sound` の部分集合である。
全明示的宣言のソース名と監査対象を照合し漏れなし。新しい sorry・axiom・引用はない。

未完了：N4 の一般の右 pinched Hom、dg nerve での線形表示、各次数の A 加群構造、
Kan 性、π₀ と H⁰ の射の同定。N6 の一点 dg 圏・複体 dg 圏による具体化と全体検査。
N0〜N3 と N5 は完了しているが、目標 N0〜N6 全体の完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            SerrePositivity.DifferentialGraded.DGFunctor A D E →
              SerrePositivity.DifferentialGraded.DGFunctor A D E → Type (max u_1 u_2)

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            SerrePositivity.DifferentialGraded.DGFunctor A D E →
              SerrePositivity.DifferentialGraded.DGFunctor A D E → Fin 2 → D → E

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E} →
              SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G →
                {x y : D} →
                  {k : ℤ} →
                    (p q : Fin 2) →
                      p ≤ q →
                        ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k) →
                          ↑(SerrePositivity.DifferentialGraded.GradedHom A
                              (SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj F G p x)
                              (SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj F G q y) k)

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_00 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (h : 0 ≤ 0)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition 0 0 h f = (CategoryTheory.ConcreteCategory.hom ((F.map x y).f k)) f

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_01 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (h : 0 ≤ 1)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition 0 1 h f =
    SerrePositivity.DifferentialGraded.compose A (↑(η.app y))
      ((CategoryTheory.ConcreteCategory.hom ((F.map x y).f k)) f) ⋯

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_11 : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (h : 1 ≤ 1)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition 1 1 h f = (CategoryTheory.ConcreteCategory.hom ((G.map x y).f k)) f

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q),
  η.transition p q hpq 0 = 0

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sub : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
  (f g : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition p q hpq (f - g) = η.transition p q hpq f - η.transition p q hpq g

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_smul : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
  (c : ℤˣ) (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition p q hpq (c • f) = c • η.transition p q hpq f

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_differential : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition p q hpq (SerrePositivity.DifferentialGraded.differential A f) =
    SerrePositivity.DifferentialGraded.differential A (η.transition p q hpq f)

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_compose : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y z : D} {i j k : ℤ} (p q r : Fin 2)
  (hpq : p ≤ q) (hqr : q ≤ r) (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A y z j))
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y i)) (hk : i + j = k),
  η.transition p r ⋯ (SerrePositivity.DifferentialGraded.compose A g f hk) =
    SerrePositivity.DifferentialGraded.compose A (η.transition q r hqr g) (η.transition p q hpq f) hk

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) (p : Fin 2) (x : D),
  η.transition p p ⋯ ↑(SerrePositivity.DifferentialGraded.unitElement A x) =
    ↑(SerrePositivity.DifferentialGraded.unitElement A
        (SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj F G p x))

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sum : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {ι : Type u_4} {x y : D} {k : ℤ} (p q : Fin 2)
  (hpq : p ≤ q) (S : Finset ι) (f : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)),
  η.transition p q hpq (∑ t ∈ S, f t) = ∑ t ∈ S, η.transition p q hpq (f t)

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit_of_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {x y : D} (p q : Fin 2) (hpq : p ≤ q)
  (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A x y 0)),
  x = y →
    p = q →
      f ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A y) →
        η.transition p q hpq f ≍
          ↑(SerrePositivity.DifferentialGraded.unitElement A
              (SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj F G q y))

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E} →
              SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G →
                {n : ℕ} →
                  SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n →
                    (Fin (n + 1) →o Fin 2) → SerrePositivity.InfinityCategories.DGNerve.SimplexData A E n

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_term : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (β : Fin (n + 1) →o Fin 2)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯)
  (hk : k = 2 - ↑I.card) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  η.transition (β a) (β b) ⋯ (s.term I a b k hI ha hb hk j hj haj hjb) =
    (η.simplexData s β).term I a b k hI ha hb hk j hj haj hjb

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_rhs : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (β : Fin (n + 1) →o Fin 2)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯)
  (hk : k = 2 - ↑I.card) (hab : a ≤ b),
  η.transition (β a) (β b) ⋯ (s.rhs I a b k hI ha hb hk) = (η.simplexData s β).rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      {E : Type u_3} →
        [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
          [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
            {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E} →
              SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G →
                {n : ℕ} →
                  SerrePositivity.InfinityCategories.DGNerve.Simplex A D n →
                    (Fin (n + 1) →o Fin 2) → SerrePositivity.InfinityCategories.DGNerve.Simplex A E n

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_pullback : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (β : Fin (n + 1) →o Fin 2)
  (α : Fin (m + 1) →o Fin (n + 1)), η.simplexData (s.pullback α) (β.comp α) = (η.simplexData s β).pullback α

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_pullback : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} {E : Type u_3} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {m n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n) (β : Fin (n + 1) →o Fin 2)
  (α : Fin (m + 1) →o Fin (n + 1)), η.simplex (s.pullback α) (β.comp α) = (η.simplex s β).pullback α

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D E : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n),
  η.simplex s ((OrderHom.const (Fin (n + 1))) 0) = s.map F

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_one : ∀ {A : Type u_1} [inst : CommRing A]
  {D E : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G) {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.Simplex A D n),
  η.simplex s ((OrderHom.const (Fin (n + 1))) 1) = s.map G

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap : {A : Type u_1} →
  [inst : CommRing A] →
    {D E : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
          {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E} →
            SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G →
              (CategoryTheory.MonoidalCategoryStruct.tensorObj (SerrePositivity.InfinityCategories.dgNerve A D)
                  (SSet.stdSimplex.obj { len := 1 }) ⟶
                SerrePositivity.InfinityCategories.dgNerve A E)

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D E : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G),
  CategoryTheory.CategoryStruct.comp SSet.ι₀ η.homotopyMap = SerrePositivity.InfinityCategories.dgNerve.map F

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_one : ∀ {A : Type u_1} [inst : CommRing A]
  {D E : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D]
  [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E]
  {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E}
  (η : SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G),
  CategoryTheory.CategoryStruct.comp SSet.ι₁ η.homotopyMap = SerrePositivity.InfinityCategories.dgNerve.map G

@SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopy : {A : Type u_1} →
  [inst : CommRing A] →
    {D E : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        [inst_2 : SerrePositivity.DifferentialGraded.DGCategory A E] →
          {F G : SerrePositivity.DifferentialGraded.DGFunctor A D E} →
            SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans F G →
              SSet.Homotopy (SerrePositivity.InfinityCategories.dgNerve.map F)
                (SerrePositivity.InfinityCategories.dgNerve.map G)
```

### N4a：一般の右 pinched Hom と閉零頂点（2026-10-18、N4 は未完了）

`PinchedHom/Index.lean` は任意の単体圏の射 α を最終頂点固定で一段延長する `extend` を定義する。
その単調写像は先頭頂点で α、最終点で最終点を取り、先頭面の包含 `front`、最終頂点の選択
`lastVertex` との可換性、恒等射と合成の保存を証明した。`front_eq_δ` は先頭面が最終頂点を
飛ばす面であることを確認し、零次では `front_zero` と `lastVertex_zero` が一単体の二つの面に一致する。

`PinchedHom/Basic.lean` は任意の `X : SSet` と `x y : X _⦋0⦌` に対する
`InfinityCategories.pinchedHom x y : SSet` を定義した。n 単体は次の二条件付きの元 `s : X _⦋n+1⦌`：
先頭の n+1 頂点が張る面全体の引き戻しが `constant x n` に一致し、最終頂点が y に一致する。
複数の余次元一の面全てを定値にする条件は課していない。引き戻しには `extend` を用い、
二条件の保存と、単体的恒等・合成の法則を証明した。任意の X の構成であり quasicategory は仮定しない。

`PinchedHom/Edges.lean` の `vertexEquiv` はこの右 pinched Hom の零単体を X の端点付き辺
`X.Edge x y` に同定する。順逆とも元の一単体をそのまま使う。
`DGNerve/PinchedHom.lean` は dg 圏の二対象 x,y に対する `DGNerve.pinchedHom A D x y` を定義し、
`DGNerve.PinchedHom.vertexCycleEquiv` により、その零単体を
`zeroCycles (homObject A D x y)` に同定した。後者は一般の頂点の同値と N3 の辺の閉零成分の同値の合成。

前提：一般の構成は任意の単体的集合 X と二頂点のみ。dg 圏での構成は任意の可換環 A、
任意の `[DGCategory A D]` と二対象 x,y のみ。対象宇宙 v と Hom 宇宙 u は独立で、
写像空間の宇宙は `max u v`。有界性・平坦性・標数や追加の単体方程式の仮定はない。
N0 に記録した先頭面全体という規約および計画 §3 の設計を変更していない。

検証：`set -e`、`set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3464 jobs、終了コード 0。
続く `lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
担当する DGNerve/ と PinchedHom/ の全 361 個の明示的公開宣言と既存 5 則、計 366 件を監査し、
依存公理は全件で `propext`・`Classical.choice`・`Quot.sound` の部分集合。
全ソース宣言名を `#print axioms` と `#check @` の対象と照合して漏れなし。
新しい sorry・axiom・引用はない。

未完了：N4 の全 n 単体と非空有限部分集合の線形族の同値、線形方程式の導出、
各次数の A 加群構造と面・退化の線形性、全ホーンの直接充填による Kan 性、
π₀ と H⁰ の射の同定。今回の零単体の同値だけでそれらを完了とは数えない。
N6 の具体例と最終の全体検査も未完了。N0〜N3・N5 の完了状態は変わらない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom : {m n : ℕ} →
  (Fin (m + 1) →o Fin (n + 1)) → Fin (m + 2) →o Fin (n + 2)

@SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_castSucc : ∀ {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
  (i : Fin (m + 1)), (SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom α) i.castSucc = (α i).castSucc

@SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_last : ∀ {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)),
  (SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom α) (Fin.last (m + 1)) = Fin.last (n + 1)

@SerrePositivity.InfinityCategories.PinchedHom.extend : {m n : SimplexCategory} →
  (m ⟶ n) → ({ len := m.len + 1 } ⟶ { len := n.len + 1 })

SerrePositivity.InfinityCategories.PinchedHom.front : (n : ℕ) → { len := n } ⟶ { len := n + 1 }

SerrePositivity.InfinityCategories.PinchedHom.lastVertex : (n : ℕ) → { len := 0 } ⟶ { len := n + 1 }

@SerrePositivity.InfinityCategories.PinchedHom.front_extend : ∀ {m n : SimplexCategory} (α : m ⟶ n),
  CategoryTheory.CategoryStruct.comp (SerrePositivity.InfinityCategories.PinchedHom.front m.len)
      (SerrePositivity.InfinityCategories.PinchedHom.extend α) =
    CategoryTheory.CategoryStruct.comp α (SerrePositivity.InfinityCategories.PinchedHom.front n.len)

@SerrePositivity.InfinityCategories.PinchedHom.lastVertex_extend : ∀ {m n : SimplexCategory} (α : m ⟶ n),
  CategoryTheory.CategoryStruct.comp (SerrePositivity.InfinityCategories.PinchedHom.lastVertex m.len)
      (SerrePositivity.InfinityCategories.PinchedHom.extend α) =
    SerrePositivity.InfinityCategories.PinchedHom.lastVertex n.len

SerrePositivity.InfinityCategories.PinchedHom.extend_id : ∀ (n : SimplexCategory),
  SerrePositivity.InfinityCategories.PinchedHom.extend (CategoryTheory.CategoryStruct.id n) =
    CategoryTheory.CategoryStruct.id { len := n.len + 1 }

@SerrePositivity.InfinityCategories.PinchedHom.extend_comp : ∀ {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n),
  SerrePositivity.InfinityCategories.PinchedHom.extend (CategoryTheory.CategoryStruct.comp α β) =
    CategoryTheory.CategoryStruct.comp (SerrePositivity.InfinityCategories.PinchedHom.extend α)
      (SerrePositivity.InfinityCategories.PinchedHom.extend β)

SerrePositivity.InfinityCategories.PinchedHom.front_eq_δ : ∀ (n : ℕ),
  SerrePositivity.InfinityCategories.PinchedHom.front n = SimplexCategory.δ (Fin.last (n + 1))

SerrePositivity.InfinityCategories.PinchedHom.front_zero : SerrePositivity.InfinityCategories.PinchedHom.front 0 =
  SimplexCategory.δ 1

SerrePositivity.InfinityCategories.PinchedHom.lastVertex_zero : SerrePositivity.InfinityCategories.PinchedHom.lastVertex
    0 =
  SimplexCategory.δ 0

@SerrePositivity.InfinityCategories.PinchedHom.constant : {X : SSet} →
  X.obj (Opposite.op { len := 0 }) → (n : ℕ) → X.obj (Opposite.op { len := n })

@SerrePositivity.InfinityCategories.PinchedHom.constant_pullback : ∀ {X : SSet} (x : X.obj (Opposite.op { len := 0 }))
  {m n : SimplexCategory} (α : m ⟶ n),
  (CategoryTheory.ConcreteCategory.hom (X.map α.op)) (SerrePositivity.InfinityCategories.PinchedHom.constant x n.len) =
    SerrePositivity.InfinityCategories.PinchedHom.constant x m.len

@SerrePositivity.InfinityCategories.PinchedHom.Simplex : {X : SSet} →
  X.obj (Opposite.op { len := 0 }) → X.obj (Opposite.op { len := 0 }) → ℕ → Type u_1

@SerrePositivity.InfinityCategories.PinchedHom.Simplex.ext : ∀ {X : SSet} {x y : X.obj (Opposite.op { len := 0 })}
  {n : ℕ} {s t : SerrePositivity.InfinityCategories.PinchedHom.Simplex x y n}, s.val = t.val → s = t

@SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback : {X : SSet} →
  {x y : X.obj (Opposite.op { len := 0 })} →
    {m n : SimplexCategory} →
      SerrePositivity.InfinityCategories.PinchedHom.Simplex x y n.len →
        (m ⟶ n) → SerrePositivity.InfinityCategories.PinchedHom.Simplex x y m.len

@SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_id : ∀ {X : SSet}
  {x y : X.obj (Opposite.op { len := 0 })} {n : SimplexCategory}
  (s : SerrePositivity.InfinityCategories.PinchedHom.Simplex x y n.len),
  s.pullback (CategoryTheory.CategoryStruct.id n) = s

@SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_comp : ∀ {X : SSet}
  {x y : X.obj (Opposite.op { len := 0 })} {l m n : SimplexCategory}
  (s : SerrePositivity.InfinityCategories.PinchedHom.Simplex x y n.len) (α : l ⟶ m) (β : m ⟶ n),
  (s.pullback β).pullback α = s.pullback (CategoryTheory.CategoryStruct.comp α β)

@SerrePositivity.InfinityCategories.pinchedHom : {X : SSet} →
  X.obj (Opposite.op { len := 0 }) → X.obj (Opposite.op { len := 0 }) → SSet

@SerrePositivity.InfinityCategories.PinchedHom.constant_zero : ∀ {X : SSet} (x : X.obj (Opposite.op { len := 0 })),
  SerrePositivity.InfinityCategories.PinchedHom.constant x 0 = x

@SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv : {X : SSet} →
  (x y : X.obj (Opposite.op { len := 0 })) →
    (SerrePositivity.InfinityCategories.pinchedHom x y).obj (Opposite.op { len := 0 }) ≃ SSet.Edge x y

@SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv_edge : ∀ {X : SSet} (x y : X.obj (Opposite.op { len := 0 }))
  (s : (SerrePositivity.InfinityCategories.pinchedHom x y).obj (Opposite.op { len := 0 })),
  ((SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv x y) s).edge = s.val

SerrePositivity.InfinityCategories.DGNerve.pinchedHom : (A : Type u_1) →
  [inst : CommRing A] → (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → D → D → SSet

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.vertexCycleEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (x y : D) →
          (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := 0 }) ≃
            ↥(SerrePositivity.DifferentialGraded.zeroCycles (SerrePositivity.DifferentialGraded.homObject A D x y))
```

### N4b：線形方程式の解の加群と全成分の回収（2026-10-18、N4 は未完了）

`DGNerve/PinchedLinear.lean` は `PinchedHom.LinearData A x y n` を定義する。
成分の添字は非空の `J : Finset (Fin (n+1))` と `k = 1 - |J|` の組で、成分は
`GradedHom A x y k`。集合・次数・証明を一つの subtype の添字にまとめることで、
成分族に通常の従属関数の A 加群構造を与え、`LinearData.component` は J、k とその証明で評価する。
元の `Simplex.hom` の表現や §3 の設計は変更していない。

`LinearData.rhs` は `|J|≥2` のとき
`Σ j:J, (#{t∈J : j<t}+1).negOnePow • f_(J.erase j)`、それ以外では零である。
これは N0.3 の `(-1)^(r-a+1)` の cochain 規約そのもの。零・加法・A スカラー倍の保存を
証明した。`linearSubmodule A x y n` は全ての非空 J で `δ f_J = rhs f J` を満たす族の部分加群、
`LinearSimplex A x y n` はその台型であり、`AddCommGroup` と `Module A` が自動推論される。
`LinearSimplex.equation` が全方程式を取り出し、`closed_singleton` は各一点集合の成分が閉零元であることを示す。

`PinchedLinearReindex.lean` の `LinearData.pullback α` は成分族の A 線形写像。
J 上で α が単射なら J.image α の成分、それ以外なら零を取り、両分岐の計算補題と恒等則・合成則を証明した。
ここでの線形性は方程式を課す前の成分族についての結果であり、まだ解の部分加群への制限は構成していない。

`PinchedIndex.lean` の `withLast J` は J の先頭埋め込みの像に最終点を加えた集合。
濃度が |J|+1、最小点が元の最小点の埋め込み、最大点が最終点であることを証明した。
`PinchedComponents.lean` は実際の右 pinched 単体について、全先頭頂点の対象が x、最終対象が y と証明し、
`toLinearData` により任意の非空 J の `withLast J` の成分を回収する。
`toLinearData_component_heq` は対象を移送した値が元の成分と異種等号で一致することを示す。

前提：全て任意の可換環 A、任意の dg 圏 D、二対象 x,y。追加の標数・有界性・平坦性の仮定はない。
線形族の Hom の宇宙は u、実際の右 pinched 単体の宇宙は `max u v`。
`LinearSimplex` に線形方程式を課すのは模型の定義であり、実際の単体からその方程式を導く証明は未完了である。
これを条件付きの dg nerve の線形表示や N4 完了と数えていない。

検証：`set -e`、`set -o pipefail` の下で集約対象
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3468 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
担当する DGNerve/ と PinchedHom/ の全 387 個の明示的公開宣言と再利用する既存 5 則、
計 392 件の公理表示は全て標準三公理 `propext`・`Classical.choice`・`Quot.sound` の部分集合。
全明示的ソース宣言名と `#print axioms`・`#check @` を照合して漏れなし。
監査の型検査で全 n の `LinearSimplex` の `Module A` と `AddCommGroup` の instance 推論も確認した。
新しい sorry・axiom・引用はない。

未完了：実際の右 pinched 単体の方程式の線形化、線形解から元の単体への再構成と両逆則、
線形成分の引き戻しによる方程式の保存、実際の写像空間への加群構造と線形性の移送、
全ホーンの直接充填・Kan 性、π₀ と H⁰ の射の比較。N6 の具体例・最終検査も未完了。
N0〜N3・N5 は完了しているが、N4 と目標全体は未完了のまま。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData : (A : Type u_1) →
  [inst : CommRing A] → {D : Type u_2} → [SerrePositivity.DifferentialGraded.DGCategory A D] → D → D → ℕ → Type u_1

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.component : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n →
              (J : Finset (Fin (n + 1))) →
                (k : ℤ) → J.Nonempty → k = 1 - ↑J.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A x y k)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.erase_nonempty : ∀ {n : ℕ} {J : Finset (Fin (n + 1))},
  2 ≤ J.card → ∀ j ∈ J, (J.erase j).Nonempty

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n →
              (J : Finset (Fin (n + 1))) →
                (k : ℤ) → k = 1 - ↑J.card → ↑(SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - ↑J.card),
  SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs 0 J k hk = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_add : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f g : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hk : k = 1 - ↑J.card), (f + g).rhs J k hk = f.rhs J k hk + g.rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_smul : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ} (c : A)
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hk : k = 1 - ↑J.card), (c • f).rhs J k hk = c • f.rhs J k hk

SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearSubmodule : (A : Type u_1) →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (x y : D) → (n : ℕ) → Submodule A (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n)

SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex : (A : Type u_1) →
  [inst : CommRing A] → {D : Type u_2} → [SerrePositivity.DifferentialGraded.DGCategory A D] → D → D → ℕ → Type u_1

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  SerrePositivity.DifferentialGraded.differential A ((↑s).component J k hJ hk) = (↑s).rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.closed_singleton : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n) (a : Fin (n + 1)),
  SerrePositivity.DifferentialGraded.differential A ((↑s).component {a} 0 ⋯ ⋯) = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {m n : ℕ} →
            (Fin (m + 1) →o Fin (n + 1)) →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n →ₗ[A]
                SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y m

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_inj : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {m n : ℕ}
  (α : Fin (m + 1) →o Fin (n + 1)) (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n)
  (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - ↑J.card) (hi : Set.InjOn ⇑α ↑J),
  ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback α) f).component J k hJ hk =
    f.component (Finset.image (⇑α) J) k ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_not_inj : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {m n : ℕ}
  (α : Fin (m + 1) →o Fin (n + 1)) (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n)
  (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  ¬Set.InjOn ⇑α ↑J →
    ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback α) f).component J k hJ hk = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_id : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback OrderHom.id) f = f

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_comp : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {l m n : ℕ}
  (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1))
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback α)
      ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback β) f) =
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback (β.comp α)) f

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast : {n : ℕ} → Finset (Fin (n + 1)) → Finset (Fin (n + 2))

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.last_not_mem_image : ∀ {n : ℕ} (J : Finset (Fin (n + 1))),
  Fin.last (n + 1) ∉ Finset.image Fin.castSucc J

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1))),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).card = J.card + 1

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.two_withLast : ∀ {n : ℕ} {J : Finset (Fin (n + 1))},
  J.Nonempty → 2 ≤ (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).card

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withLast : ∀ {n : ℕ} {J : Finset (Fin (n + 1))}
  (hJ : J.Nonempty) (h : (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).Nonempty),
  (J.min' hJ).castSucc = (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).min' h

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.max_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (h : (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).Nonempty),
  Fin.last (n + 1) = (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).max' h

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.source_obj : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (i : Fin (n + 1)), s.val.obj i.castSucc = x

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.target_obj : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n })),
  s.val.obj (Fin.last (n + 1)) = y

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }) →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_component_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component J k hJ hk ≍
    s.val.hom (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1))
      k ⋯ ⋯ ⋯ ⋯
```

### N4c：先頭面の単位・零と線形化の切断計算（2026-10-18、N4 は未完了）

`DGNerve/PinchedFront.lean` は一般の定値 dg nerve 単体の成分を三分岐の定義から評価する。
二点以上の集合では零単体への定値写像は非単射であることを `not_injOn_constant` で示し、
`constant_hom_unit` は濃度二の成分を単位に、`constant_hom_zero` は濃度二以外の成分を零に同定する。
実際の右 pinched 単体 s の先頭面の固定条件を各成分で評価し、`front_hom_heq` で
先頭埋め込みの像の成分をその定値単体の成分に比較した。
`front_hom_unit` と `front_hom_zero` はしたがって実際の s の先頭面の全ての辺が単位、
三点以上の全成分が零であることを与える。辺の同定は対象の等式の移送を保持した異種等号である。
`compose_front_hom_unit` はこの辺を先に作用させる合成が後の射に一致すること、
`compose_front_hom_zero` は先頭高次成分を先に作用させる合成が零であることを示す。
任意の高次成分の線形方程式は仮定していない。

`PinchedCuts.lean` は `withLast J` について次を証明した。
先頭点の削除は `withLast (J.erase j)`、先頭点 j までの左切断は `(J.filter (·≤j)).image castSucc`、
j からの右切断は `withLast (J.filter (j≤·))`、j より大きい点の集合は
`withLast (J.filter (j<·))` に一致する。したがって dg nerve の符号の指数は
`#{t∈J : j<t}+1` であり、N0.3 の線形方程式の削除係数に一致する。

`PinchedSecond.lean` の `second J hJ` は、二点以上の J の最小点を消した集合の最小点。
その所属、最小点より真に大きいこと、二番目までの左切断が最初の二点だけからなること、
二番目からの右切断が最小点の削除であることを証明した。
`left_card_two_iff` は最小点より大きい所属点 j について、左切断の濃度が二であることと
j が二番目の点であることが同値であると示す。
`sign_second` は N0.3 の削除係数について、二番目の点の係数が最小点の係数の逆符号であることを示す。
この符号の等式は二つの厳密右切断の濃度が一違うことから証明した。
以上は線形化で単位の合成項が最初の削除項になるための有限集合と代数の計算である。

前提：任意の可換環 A、任意の dg 圏 D、実際の右 pinched 単体 s。
先頭面の成分の評価では元の `Simplex.hom` と同じ端点・次数・濃度の証明を明示する。
二番目の点の計算では J の濃度二以上、内部切断の判定では j の所属と最小点より大きい条件を使う。
追加の方程式・標数・有界性・平坦性の仮定はない。§3 の設計は変更していない。

検証：`set -e`、`set -o pipefail` の下で集約対象
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3471 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
全 409 個の担当する明示的公開宣言と既存 5 則、計 414 件の公理表示を確認し、全て
標準三公理 `propext`・`Classical.choice`・`Quot.sound` の部分集合。
全ソース宣言名と監査・型検査対象を照合して漏れなし。新しい sorry・axiom・引用はない。

未完了：回収した全成分についての線形右辺と dg nerve の右辺の有限和の同定、
`toLinearData` の線形方程式の証明、解からの単体への再構成と両逆則。
解の引き戻しと実際の写像空間への A 加群構造・線形性の移送、直接ホーン充填・Kan 性、
π₀ と H⁰ の射の比較、N6 の具体例と最終検査も未完了。今回の補題で N4 完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.not_injOn_constant : ∀ {n : ℕ} {J : Finset (Fin (n + 1))},
  2 ≤ J.card → ¬Set.InjOn ⇑(SimplexCategory.Hom.toOrderHom ({ len := n }.const { len := 0 } 0)) ↑J

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (x : D) (J : Finset (Fin (n + 1)))
  (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  J.card ≠ 2 →
    (SerrePositivity.InfinityCategories.PinchedHom.constant
            (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
        J a b k hJ ha hb hk =
      0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_unit : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ} (x : D) (J : Finset (Fin (n + 1)))
  (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  J.card = 2 →
    (SerrePositivity.InfinityCategories.PinchedHom.constant
            (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
        J a b k hJ ha hb hk ≍
      ↑(SerrePositivity.DifferentialGraded.unitElement A x)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.PinchedHom.constant
          (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
      J a b k hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card), J.card ≠ 2 → s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯ = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  J.card = 2 →
    s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯ ≍
      ↑(SerrePositivity.DifferentialGraded.unitElement A x)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_zero : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  J.card ≠ 2 →
    ∀ {z : D} {q t : ℤ} (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.val.obj b.castSucc) z q))
      (ht : k + q = t),
      SerrePositivity.DifferentialGraded.compose A g
          (s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯) ht =
        0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_unit : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
  (hk : k = 2 - ↑J.card),
  J.card = 2 →
    ∀ {z : D} {q t : ℤ} (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.val.obj b.castSucc) z q))
      (ht : k + q = t),
      SerrePositivity.DifferentialGraded.compose A g
          (s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯) ht ≍
        g

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erase_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (j : Fin (n + 1)),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J).erase j.castSucc =
    SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast (J.erase j)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (j : Fin (n + 1)),
  {x ∈ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J | x ≤ j.castSucc} =
    Finset.image Fin.castSucc ({x ∈ J | x ≤ j})

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (j : Fin (n + 1)),
  {x ∈ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J | j.castSucc ≤ x} =
    SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast ({x ∈ J | j ≤ x})

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (j : Fin (n + 1)),
  {x ∈ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J | j.castSucc < x} =
    SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast ({x ∈ J | j < x})

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_above_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (j : Fin (n + 1)),
  {x ∈ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J | j.castSucc < x}.card =
    {x ∈ J | j < x}.card + 1

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second : {n : ℕ} →
  (J : Finset (Fin (n + 1))) → 2 ≤ J.card → Fin (n + 1)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second_mem_erase : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card), SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ ∈ J.erase (J.min' ⋯)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.first_lt_second : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card), J.min' ⋯ < SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_second : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card),
  {x ∈ J | x ≤ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ} =
    {J.min' ⋯, SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ}

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_second : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card),
  {x ∈ J | SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ ≤ x} = J.erase (J.min' ⋯)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_first : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card), {x ∈ J | J.min' ⋯ < x} = J.erase (J.min' ⋯)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_second : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card),
  {x ∈ J | SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ < x} =
    (J.erase (J.min' ⋯)).erase (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sign_second : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card),
  (↑{x ∈ J | SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ < x}.card + 1).negOnePow =
    -(↑{x ∈ J | J.min' ⋯ < x}.card + 1).negOnePow

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_card_two_iff : ∀ {n : ℕ} (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card),
  ∀ j ∈ J,
    J.min' ⋯ < j → ({x ∈ J | x ≤ j}.card = 2 ↔ j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ)
```

### N4d：全内部点の一項の線形化（2026-10-18、N4 は未完了）

`PinchedFront.lean` に、集合 I が先頭埋め込みの像に等しい場合の成分比較
`front_hom_heq_of_image` と、その零・単位の場合の評価を追加した。
集合の等式だけを書き換えると hom の濃度・端点・次数の証明引数の型が依存して変わるため、
既存の `hom_heq_of_indices` により成分を異種等号で比較し、定値面の評価につなぐ。
これにより切断集合の実際の証明引数を保って先頭面の零・単位を適用できる。

`PinchedTerms.lean` は一般の単体データに対し左右切断成分 `cutLeft`・`cutRight`、
その通常順合成 `cutComposite`、一点削除成分 `erasedComponent` を取り出す。
`term_eq_sub_cutComposite` は元の term が削除成分から切断合成を引いたものの符号倍であることを示す。
いずれも元の `SimplexData.term` の定義と同じ式であり、元の定義や設計は変更していない。
`hom_heq_of_indices_degree` は集合・端点に加えて次数も等しい場合の成分を比較する。

実際の右 pinched 単体 s と二点以上の J について、
`cutComposite_zero_of_ne_second` は二番目以外の全内部点で切断合成が零になることを証明する。
`cutComposite_second` は二番目での合成が右切断成分に戻ることを、先頭面の単位と単位則から示す。
`cutRight_second_heq_component` と `cutComposite_second_heq_component` はその値が
`toLinearData s` の最小点を消した集合の次数 k+1 の成分であることを同定する。
`erasedComponent_heq_component` は任意の内部先頭点 j の削除成分を、同じ回収族の J.erase j の成分に同定する。

`PinchedTermLinear.lean` の `term_heq_linear` は、全ての j∈J で min J<j の寄与を
次の形にまとめる。`f = toLinearData s`、`a=min J`、`b=second J`、`k=1-|J|` として、
元の `withLast J` の j.castSucc における term は

```
(#{t∈J : j<t}+1).negOnePow • (f_(J.erase j) - if j=b then f_(J.erase a) else 0)
```

と異種等号で一致する。全成分の次数は k+1。
証明では切断合成の零・単位の二分岐と、対象を移送した符号付き差の比較
`smul_sub_heq_of_obj_eq` を使う。単体の線形方程式は仮定せず、実際の先頭面固定条件から導出した。

前提：任意の可換環 A、dg 圏 D、実際の右 pinched 単体 s、J の濃度二以上と k=1-|J|、
内部先頭点については j∈J と min J<j。零の分岐は j≠second J、単位の分岐は二番目の点である。
これらは各項の式の範囲を指定する添字条件であり、追加の高次方程式・有界性・平坦性・標数の仮定はない。
全公開型は以下に記録する。§3 の設計は変更していない。

検証：`set -e`、`set -o pipefail` の下で集約対象
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3473 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
新規 16 宣言を含む全 425 個の担当する明示的公開宣言と既存 5 則、計 430 件の公理表示が
標準三公理 `propext`・`Classical.choice`・`Quot.sound` の部分集合であることを確認した。
全ソース宣言名と監査・型検査対象を照合して漏れなし。新しい sorry・axiom・引用はない。

未完了：今回の各項の式を有限和にまとめ、最小点の削除項の符号を反転して全右辺を同定すること。
それによる `toLinearData` の線形方程式、解からの逆構成と両逆則、解の単体的構造と
実際の写像空間への加群構造・線形性の移送、直接ホーン充填・Kan 性、π₀ と H⁰ の射の比較。
N6 の具体例と最終検査も未完了。各項の線形化だけで N4 全体を完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq_of_image : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a.castSucc = I.min' ⋯) (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card)
  (haJ : a = J.min' ⋯) (hbJ : b = J.max' ⋯) (hIJ : I = Finset.image Fin.castSucc J),
  s.val.hom I a.castSucc b.castSucc k hI ha hb hk ≍
    (SerrePositivity.InfinityCategories.PinchedHom.constant
          (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
      J a b k hJ haJ hbJ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero_of_image : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a.castSucc = I.min' ⋯) (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card),
  a = J.min' ⋯ →
    b = J.max' ⋯ → I = Finset.image Fin.castSucc J → J.card ≠ 2 → s.val.hom I a.castSucc b.castSucc k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit_of_image : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a.castSucc = I.min' ⋯) (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card),
  a = J.min' ⋯ →
    b = J.max' ⋯ →
      I = Finset.image Fin.castSucc J →
        J.card = 2 →
          s.val.hom I a.castSucc b.castSucc k hI ha hb hk ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A x)

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices_degree : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) {I J : Finset (Fin (n + 1))}
  {a b c d : Fin (n + 1)} {k l : ℤ} {hI : 2 ≤ I.card} {ha : a = I.min' ⋯} {hb : b = I.max' ⋯} {hk : k = 2 - ↑I.card}
  {hJ : 2 ≤ J.card} {hc : c = J.min' ⋯} {hd : d = J.max' ⋯} {hl : l = 2 - ↑J.card},
  I = J → a = c → b = d → k = l → s.hom I a b k hI ha hb hk ≍ s.hom J c d l hJ hc hd hl

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutLeft : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a : Fin (n + 1)) →
                (hI : 2 ≤ I.card) →
                  a = I.min' ⋯ →
                    (j : Fin (n + 1)) →
                      j ∈ I →
                        a < j →
                          ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj j)
                              (2 - ↑{x ∈ I | x ≤ j}.card))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutRight : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (b : Fin (n + 1)) →
                (hI : 2 ≤ I.card) →
                  b = I.max' ⋯ →
                    (j : Fin (n + 1)) →
                      j ∈ I →
                        j < b →
                          ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj j) (s.obj b)
                              (2 - ↑{x ∈ I | j ≤ x}.card))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutComposite : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (j : Fin (n + 1)) →
                            j ∈ I →
                              a < j →
                                j < b → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.erasedComponent : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) →
            (I : Finset (Fin (n + 1))) →
              (a b : Fin (n + 1)) →
                (k : ℤ) →
                  (hI : 2 ≤ I.card) →
                    a = I.min' ⋯ →
                      b = I.max' ⋯ →
                        k = 2 - ↑I.card →
                          (j : Fin (n + 1)) →
                            j ∈ I →
                              a < j →
                                j < b → ↑(SerrePositivity.DifferentialGraded.GradedHom A (s.obj a) (s.obj b) (k + 1))

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_sub_cutComposite : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
  (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card) (j : Fin (n + 1))
  (hj : j ∈ I) (haj : a < j) (hjb : j < b),
  s.term I a b k hI ha hb hk j hj haj hjb =
    (↑{x ∈ I | j < x}.card).negOnePow •
      (s.erasedComponent I a b k hI ha hb hk j hj haj hjb - s.cutComposite I a b k hI ha hb hk j hj haj hjb)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_zero_of_ne_second : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J)
  (haj : J.min' ⋯ < j),
  j ≠ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ →
    s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
        (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ =
      0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ⋯ ≍
    s.val.cutRight (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (Fin.last (n + 1)) ⋯ ⋯
      (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutRight_second_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutRight (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (Fin.last (n + 1)) ⋯ ⋯
      (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erasedComponent_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J)
  (haj : J.min' ⋯ < j),
  s.val.erasedComponent (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase j) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.smul_sub_heq_of_obj_eq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {a b c d : D},
  a = c →
    b = d →
      ∀ {k : ℤ} (e : ℤˣ) (f g : ↑(SerrePositivity.DifferentialGraded.GradedHom A a b k))
        (f' g' : ↑(SerrePositivity.DifferentialGraded.GradedHom A c d k)), f ≍ f' → g ≍ g' → e • (f - g) ≍ e • (f' - g')

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.term_heq_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J)
  (haj : J.min' ⋯ < j),
  s.val.term (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ ≍
    (↑{x ∈ J | j < x}.card + 1).negOnePow •
      ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase j) (k + 1) ⋯ ⋯ -
        if j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ then
          (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase (J.min' ⋯)) (k + 1)
            ⋯ ⋯
        else 0)
```

### N4e：全右辺の同定と全次数の線形模型への順写像（2026-10-18、N4 は未完了）

`DGNerve/PinchedSum.lean` の `withLastEquiv J` は `Option J ≃ withLast J` を与える。
none は追加した最終点、some は先頭埋め込みの点に対応する。
`sum_withLast` はこの同値に沿って所属証明付きの和を最終点の項と先頭集合の和に分ける。

`PinchedSumLinear.lean` の `sum_linear_terms` は任意の加法可換群 M と族 `f : J → M` について、
N4d の内部点の和が全点の削除係数付きの和に等しいことを示す。
二番目だけにある補正項を取り出し、`sign_second` で係数の符号を反転させると最小点の項が戻る。
最小点の項を戻した和が全有限和に一致することは有限和の加法性で証明した。
この証明は dg 圏や追加の単体方程式に依存しない有限の加法計算である。

`PinchedRhs.lean` の `rhs_withLast` は一般の単体データの右辺を先頭集合の内部点の和に直す。
最終点の項は内部点でないため零である。
`sum_heq_of_obj_eq` と N4d の `term_heq_linear` により、`rhs_heq_linear_terms` は
実際の右 pinched 単体の右辺と各項の線形表示の和を比較する。
`rhs_heq_linear` は上の有限和の等式を適用し、元の右辺を `toLinearData s` の
全削除和 `LinearData.rhs` と異種等号で同定した。

`toLinearData_equation` は任意の非空 J、任意の k=1-|J| に対して

```
differential A ((toLinearData s).component J k hJ hk) = (toLinearData s).rhs J k hk
```

を証明する。左辺は対象の移送に沿う微分の比較 `differential_heq_of_obj_eq` を用い、
元の `s.val.equation` と右辺の線形化を合成する。二点以上の J には全右辺の同定を使う。
一点の J では `withLast J` が二点集合なので、元の右辺は `rhs_of_card_two` で零になり、
線形右辺も定義上零である。したがって零次を含む全 n と全ての非空 J を扱っている。

`toLinearSimplex` はその結果を用い、実際の右 pinched 単体を、全線形方程式を満たす
`LinearSimplex A x y n` に送る。これは N4b のデータだけの `toLinearData` を解の部分加群へ
実際に持ち上げた順写像であり、線形方程式を仮定に追加していない。

前提：実際の単体からの構成は任意の可換環 A、任意の dg 圏 D、二対象 x,y、全次数 n のみ。
全方程式の取り出しは J の非空性と k=1-|J| の指定を使う。中間の全右辺同定の補題は |J|≥2 だが、
最終の `toLinearData_equation` と `toLinearSimplex` にはこの制約はない。
有限和の加法計算は任意の加法可換群で成立する。標数・有界性・平坦性の追加仮定はなく、§3 は変更していない。

検証：`set -e`、`set -o pipefail` の下で集約対象
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3476 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
新規 10 宣言を含む全 435 個の担当する明示的公開宣言と既存 5 則、計 440 件の公理表示が
標準三公理 `propext`・`Classical.choice`・`Quot.sound` の部分集合。
全ソース宣言名と監査・型検査対象を照合して漏れなし。新しい sorry・axiom・引用はない。

未完了：線形解から元の右 pinched 単体への再構成と、全次数での両逆則。
解の単体的構造と実際の写像空間への A 加群構造・線形性の移送、
直接ホーン充填・Kan 性、π₀ と H⁰ の射の比較、N6 の具体例と最終検査。
今回の全次数の順写像だけで線形表示の同値や N4 の完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLastEquiv : {n : ℕ} →
  (J : Finset (Fin (n + 1))) → Option ↥J ≃ ↥(SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_withLast : ∀ {n : ℕ} {M : Type u_1} [inst : AddCommMonoid M]
  (J : Finset (Fin (n + 1))) (f : ↥(SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) → M),
  ∑ i, f i = f ⟨Fin.last (n + 1), ⋯⟩ + ∑ j, f ⟨(↑j).castSucc, ⋯⟩

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_linear_terms : ∀ {n : ℕ} {M : Type u_1}
  [inst : AddCommGroup M] (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (f : ↥J → M),
  (∑ j,
      if J.min' ⋯ < ↑j then
        (↑{x ∈ J | ↑j < x}.card + 1).negOnePow •
          (f j - if ↑j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ then f ⟨J.min' ⋯, ⋯⟩ else 0)
      else 0) =
    ∑ j, (↑{x ∈ J | ↑j < x}.card + 1).negOnePow • f j

@SerrePositivity.InfinityCategories.DGNerve.sum_heq_of_obj_eq : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {ι : Type u_3} [inst_2 : Fintype ι] {a b c d : D},
  a = c →
    b = d →
      ∀ {k : ℤ} (f : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A a b k))
        (g : ι → ↑(SerrePositivity.DifferentialGraded.GradedHom A c d k)), (∀ (i : ι), f i ≍ g i) → ∑ i, f i ≍ ∑ i, g i

@SerrePositivity.InfinityCategories.DGNerve.differential_heq_of_obj_eq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {a b c d : D},
  a = c →
    b = d →
      ∀ {k : ℤ} (f : ↑(SerrePositivity.DifferentialGraded.GradedHom A a b k))
        (g : ↑(SerrePositivity.DifferentialGraded.GradedHom A c d k)),
        f ≍ g →
          SerrePositivity.DifferentialGraded.differential A f ≍ SerrePositivity.DifferentialGraded.differential A g

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_withLast : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 1)) (J : Finset (Fin (n + 1))) (hJ : J.Nonempty)
  (k : ℤ) (hk : k = 1 - ↑J.card),
  s.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k ⋯ ⋯
      ⋯ ⋯ =
    ∑ j,
      if h : J.min' hJ < ↑j then
        s.term (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc
          (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ (↑j).castSucc ⋯ ⋯ ⋯
      else 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear_terms : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ ≍
    ∑ j,
      if J.min' ⋯ < ↑j then
        (↑{x ∈ J | ↑j < x}.card + 1).negOnePow •
          ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase ↑j) (k + 1) ⋯ ⋯ -
            if ↑j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ then
              (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component (J.erase (J.min' ⋯))
                (k + 1) ⋯ ⋯
            else 0)
      else 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_equation : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }))
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  SerrePositivity.DifferentialGraded.differential A
      ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).component J k hJ hk) =
    (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s).rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }) →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n
```

### N4f：データの逆構成と端点・片側の逆則（2026-10-18、N4 は未完了）

`PinchedRecoverIndex.lean` は `withoutLast I` を、castSucc により I に属する先頭添字の集合と定義する。
像が I.erase last に一致すること、最終点を含む I に対する `withLast (withoutLast I)=I`、
任意の J に対する `withoutLast (withLast J)=J` を証明した。
濃度の一つの差、二点以上の I の最小点が最終点でないこと、先頭集合の非空性と最小点の対応も証明した。

`PinchedReadData.lean` の `SimplexData.toPinchedLinearData` は、全先頭対象が x、最終対象が y の
任意の単体データから全終端成分を回収する。単体方程式は要求しない。
既存の実際の単体からの `PinchedHom.toLinearData` は、この共通の操作に `source_obj` と `target_obj`
を渡す定義に整理した。公開型は変更せず、N4e の全方程式の証明も再ビルドした。

`PinchedReconstructData.lean` の `reconstructObj x y` は先頭点で x、最終点で y。
`LinearData.toSimplexData` は全ての I の成分を次の三分岐で再構成する：
最大点が最終点なら `withoutLast I` の線形成分、最終点以外を終点とする二点なら単位、その他なら零。
対象と次数の移送だけを cast で行う。三つの `toSimplexData_hom_*` 補題で全分岐を計算した。
`toSimplexData_toPinchedLinearData` は、再構成したデータの全終端成分を回収すると元の線形族に戻ると示す。
これは全 n、任意の線形族 f に対するデータの片側の逆則で、線形方程式の仮定は不要である。

`PinchedReconstructFaces.lean` の `toSimplexData_front` は先頭面全体が x の定値単体のデータに一致し、
`toSimplexData_last` は最終頂点が y の零単体のデータに一致することを示す。
前者は単射な先頭埋め込みの引き戻しの単位・零の比較、後者は零単体の射族の一意性による。
これらはいずれも方程式を添える前の `SimplexData` の等式である。

前提：任意の可換環 A、任意の dg 圏 D、二対象 x,y、全次数 n、任意の `LinearData A x y n`。
データの型を実際の単体の代わりにして完成扱いにはしていない。
線形解 `LinearSimplex` から実際の `Simplex` にするには、その線形方程式から全単体方程式を導く必要があり、
これは未完了。元の `Simplex.hom` の添字・次数は変更せず、§3 の設計変更はない。

検証：`set -e`、`set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3480 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
新規 21 宣言を含む全 456 個の担当する明示的公開宣言と既存 5 則、計 461 件を監査した。
460 件の依存公理の表示は標準三公理の部分集合、`reconstructObj` の 1 件は公理への依存なし。
両形式を合わせた全表示名と監査対象名を照合して一致し、全ソース宣言の型検査も漏れなし。
新しい sorry・axiom・引用はない。

未完了：再構成データの全単体方程式と実際の右 pinched 単体への逆写像、
両逆則による全次数の同値、実際の写像空間への A 加群構造・単体的な線形性の移送、
直接ホーン充填・Kan 性、π₀ と H⁰ の射の比較、N6 の具体例と最終検査。
今回のデータの逆構成と片側の逆則で N4 全体を完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast : {n : ℕ} →
  Finset (Fin (n + 2)) → Finset (Fin (n + 1))

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.image_withoutLast : ∀ {n : ℕ} (I : Finset (Fin (n + 2))),
  Finset.image Fin.castSucc (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I) =
    I.erase (Fin.last (n + 1))

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast_withoutLast : ∀ {n : ℕ} (I : Finset (Fin (n + 2))),
  Fin.last (n + 1) ∈ I →
    SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast
        (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I) =
      I

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_withLast : ∀ {n : ℕ} (J : Finset (Fin (n + 1))),
  SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast
      (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) =
    J

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withoutLast : ∀ {n : ℕ} (I : Finset (Fin (n + 2))),
  Fin.last (n + 1) ∈ I → I.card = (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I).card + 1

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_nonempty : ∀ {n : ℕ} {I : Finset (Fin (n + 2))},
  2 ≤ I.card → Fin.last (n + 1) ∈ I → (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I).Nonempty

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_ne_last : ∀ {n : ℕ} (I : Finset (Fin (n + 2)))
  (hI : 2 ≤ I.card), I.min' ⋯ ≠ Fin.last (n + 1)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withoutLast : ∀ {n : ℕ} (I : Finset (Fin (n + 2)))
  (hI : 2 ≤ I.card) (h : Fin.last (n + 1) ∈ I),
  ((SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I).min' ⋯).castSucc = I.min' ⋯

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {n : ℕ} →
          (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 1)) →
            (x y : D) →
              (∀ (i : Fin (n + 1)), s.obj i.castSucc = x) →
                s.obj (Fin.last (n + 1)) = y → SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData_component_heq : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 1)) (x y : D)
  (hx : ∀ (i : Fin (n + 1)), s.obj i.castSucc = x) (hy : s.obj (Fin.last (n + 1)) = y) (J : Finset (Fin (n + 1)))
  (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  (s.toPinchedLinearData x y hx hy).component J k hJ hk ≍
    s.hom (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k ⋯
      ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj : {D : Type u_1} →
  D → D → {n : ℕ} → Fin (n + 2) → D

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_ne_last : ∀ {D : Type u_1} (x y : D) {n : ℕ}
  {i : Fin (n + 2)},
  i ≠ Fin.last (n + 1) → SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj x y i = x

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_eq_last : ∀ {D : Type u_1} (x y : D) {n : ℕ}
  {i : Fin (n + 2)},
  i = Fin.last (n + 1) → SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj x y i = y

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_castSucc : ∀ {D : Type u_1} (x y : D) {n : ℕ}
  (i : Fin (n + 1)), SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj x y i.castSucc = x

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n →
              SerrePositivity.InfinityCategories.DGNerve.SimplexData A D (n + 1)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_last : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n) (I : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card)
  (hbLast : b = Fin.last (n + 1)),
  f.toSimplexData.hom I a b k hI ha hb hk ≍
    f.component (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I) k ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_unit : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n) (I : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  b ≠ Fin.last (n + 1) →
    I.card = 2 → f.toSimplexData.hom I a b k hI ha hb hk ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A x)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_zero : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n) (I : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card),
  b ≠ Fin.last (n + 1) → I.card ≠ 2 → f.toSimplexData.hom I a b k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_toPinchedLinearData : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n),
  f.toSimplexData.toPinchedLinearData x y ⋯ ⋯ = f

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_front : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n),
  f.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom =
    (SerrePositivity.InfinityCategories.PinchedHom.constant
        (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).toSimplexData

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_last : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n),
  f.toSimplexData.pullback
      (SimplexCategory.Hom.toOrderHom (SerrePositivity.InfinityCategories.PinchedHom.lastVertex n)) =
    (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex y).toSimplexData
```

### N4g：実際の逆構成と全次数の線形同値（2026-10-18、N4 は未完了）

`PinchedData.lean` の `PinchedHom.Data` は、先頭面が定値データで最終対象が y という条件だけを持つ
単体データをまとめる。単体方程式はこの構造体に課さない。
実際の単体からの `Data.ofSimplex` と、線形族からの `LinearData.toData` の両方を構成し、
成分の回収 `Data.toLinearData` と既存の操作の一致、再構成して回収した族の逆則を証明した。
これは逆構成の証明で、再構成データが既に単体であると仮定する循環を避ける共通の補助対象である。
元の dg nerve の単体や右 pinched Hom の定義は変更していない。

`PinchedDataFront.lean`・`PinchedDataTerms.lean`・`PinchedDataRhs.lean` は先頭面の条件だけから
単位・零の成分、削除と切断の計算、各項と全右辺の線形化を証明する。
有限集合・符号・単位則・既存の和の計算を再利用し、単体方程式は一切要求しない。
一点集合も含む `rhs_heq_linear_all` を得て、`cone_equation_of_linear` は回収族の線形方程式から
最終点を含む元の成分の方程式を導く。

`PinchedDataEquation.lean` の `source_equation_on_image` は先頭面内の成分の方程式を、
定値単体の全方程式と単射な引き戻しの成分・右辺の計算から得る。
`Data.equation_of_linear` は全ての I を最終点を含むか否かで分け、前者では `withoutLast I` への線形化、
後者では先頭面の像への同定を使い、回収族が線形解なら元のデータが全単体方程式を満たすと証明する。
この補題の線形解という前提は、逆構成の入力である `LinearSimplex` の定義された方程式から供給する。
元の単体方程式を新しい前提として付け加えてはいない。

`PinchedReconstruct.lean` の `LinearSimplex.toSimplex` は、その結果を再構成したデータに適用して
実際の dg nerve の (n+1) 単体を作る。`LinearSimplex.toPinched` は既証の端点のデータの等式から
先頭面・最終頂点を固定した実際の右 pinched 単体を作る。
`toLinearSimplex_toPinched` はこの単体を回収すると元の線形解に戻ることを示す。

`PinchedLinearEquiv.lean` は `Data.toLinearData_injective` を証明する。
全対象は共通の x,y で決まり、最終点を含む成分は回収族から、含まない成分は定値先頭面から
一意に決まる。これを実際の単体に適用した `toPinched_toLinearSimplex` がもう一方の逆則である。
したがって `PinchedHom.linearEquiv x y n` により

```
(DGNerve.pinchedHom A D x y) _⦋n⦌ ≃ PinchedHom.LinearSimplex A x y n
```

を全 n で構成した。N4e の順写像は既存の成分のままであり、今回の逆構成と両逆則で
**全次数の単体の線形表示の同値**を得た。条件付きのデータの同値に置き換えてはいない。

前提：任意の可換環 A、任意の dg 圏 D、二対象 x,y、全 n。追加の有界性・平坦性・標数の仮定はない。
単体方程式の逆方向に使う線形方程式は入力の `LinearSimplex` が持つ方程式そのもの。
先頭面と終端は元の定義の固定条件であり、追加条件ではない。対象宇宙 v と Hom 宇宙 u は独立、
元の写像空間の宇宙は `max u v`、線形解の宇宙は u。§3 の設計は変更していない。

検証：`set -e`、`set -o pipefail` の下で
`lake build SerrePositivity.InfinityCategories.DGNerve` が 3487 jobs、終了コード 0。
`lake env lean scripts/audit_dg_nerve.lean` も終了コード 0。
新規 35 宣言を含む全 491 個の担当する明示的公開宣言と既存 5 則、計 496 件の公理表示を確認した。
公理への依存なしの表示も空集合として数え、全件で標準三公理の部分集合。
全表示名と監査対象名が一致し、全ソース宣言の型検査も漏れなし。新しい sorry・axiom・引用はない。

未完了：全次数の同値を通じた実際の写像空間の A 加群構造、面・退化の線形性、
直接の線形ホーン充填による Kan 性、π₀ と H⁰ の射の比較、N6 の具体例と最終検査。
単体の型の全次数の同値はできたが、N4 全体および目標全体の完了とは数えない。

今回の全新規公開宣言の正確な型（`#check @` の出力）：

```lean
SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data : (A : Type u_1) →
  [inst : CommRing A] →
    (D : Type u_2) → [SerrePositivity.DifferentialGraded.DGCategory A D] → D → D → ℕ → Type (max u_1 u_2)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_obj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (i : Fin (n + 1)), s.val.obj i.castSucc = x

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.target_obj : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n), s.val.obj (Fin.last (n + 1)) = y

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_component_heq : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  s.toLinearData.component J k hJ hk ≍
    s.val.hom (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1))
      k ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ofSimplex : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }) →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_ofSimplex : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n })),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ofSimplex s).toLinearData =
    SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData s

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toData : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n →
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toLinearData_toData : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData A x y n), f.toData.toLinearData = f

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.data_hom_heq_of_eq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  {s t : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n},
  s = t →
    ∀ (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯)
      (hk : k = 2 - ↑J.card), s.hom J a b k hJ ha hb hk ≍ t.hom J a b k hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  s.val.hom (Finset.image Fin.castSucc J) a.castSucc b.castSucc k ⋯ ⋯ ⋯ ⋯ ≍
    (SerrePositivity.InfinityCategories.PinchedHom.constant
          (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
      J a b k hJ ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq_of_image : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (I : Finset (Fin (n + 2)))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' ⋯)
  (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card) (haJ : a = J.min' ⋯) (hbJ : b = J.max' ⋯)
  (hIJ : I = Finset.image Fin.castSucc J),
  s.val.hom I a.castSucc b.castSucc k hI ha hb hk ≍
    (SerrePositivity.InfinityCategories.PinchedHom.constant
          (SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex x) n).hom
      J a b k hJ haJ hbJ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_zero_of_image : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (I : Finset (Fin (n + 2)))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' ⋯)
  (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card),
  a = J.min' ⋯ →
    b = J.max' ⋯ → I = Finset.image Fin.castSucc J → J.card ≠ 2 → s.val.hom I a.castSucc b.castSucc k hI ha hb hk = 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_unit_of_image : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (I : Finset (Fin (n + 2)))
  (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' ⋯)
  (hb : b.castSucc = I.max' ⋯) (hk : k = 2 - ↑I.card) (hJ : 2 ≤ J.card),
  a = J.min' ⋯ →
    b = J.max' ⋯ →
      I = Finset.image Fin.castSucc J →
        J.card = 2 →
          s.val.hom I a.castSucc b.castSucc k hI ha hb hk ≍ ↑(SerrePositivity.DifferentialGraded.unitElement A x)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_zero_of_ne_second : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' ⋯ < j),
  j ≠ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ →
    s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
        (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ =
      0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ⋯ ≍
    s.val.cutRight (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (Fin.last (n + 1)) ⋯ ⋯
      (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutRight_second_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutRight (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (Fin.last (n + 1)) ⋯ ⋯
      (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ≍
    s.toLinearData.component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.cutComposite (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ).castSucc ⋯ ⋯ ⋯ ≍
    s.toLinearData.component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.erasedComponent_heq_component : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' ⋯ < j),
  s.val.erasedComponent (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc
      (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ ≍
    s.toLinearData.component (J.erase j) (k + 1) ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.term_heq_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card) (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' ⋯ < j),
  s.val.term (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ j.castSucc ⋯ ⋯ ⋯ ≍
    (↑{x ∈ J | j < x}.card + 1).negOnePow •
      (s.toLinearData.component (J.erase j) (k + 1) ⋯ ⋯ -
        if j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ then
          s.toLinearData.component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯
        else 0)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_terms : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ ≍
    ∑ j,
      if J.min' ⋯ < ↑j then
        (↑{x ∈ J | ↑j < x}.card + 1).negOnePow •
          (s.toLinearData.component (J.erase ↑j) (k + 1) ⋯ ⋯ -
            if ↑j = SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second J hJ then
              s.toLinearData.component (J.erase (J.min' ⋯)) (k + 1) ⋯ ⋯
            else 0)
      else 0

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - ↑J.card),
  s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' ⋯).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ ≍
    s.toLinearData.rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_all : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
      ⋯ ⋯ ⋯ ⋯ ≍
    s.toLinearData.rhs J k hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cone_equation_of_linear : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
  (hJ : J.Nonempty) (hk : k = 1 - ↑J.card),
  SerrePositivity.DifferentialGraded.differential A (s.toLinearData.component J k hJ hk) = s.toLinearData.rhs J k hk →
    SerrePositivity.DifferentialGraded.differential A
        (s.val.hom (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc
          (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯) =
      s.val.rhs (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast J) (J.min' hJ).castSucc
        (Fin.last (n + 1)) k ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_of_indices : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.SimplexData A D n) {I J : Finset (Fin (n + 1))}
  {a b c d : Fin (n + 1)} {k : ℤ} {hI : 2 ≤ I.card} {ha : a = I.min' ⋯} {hb : b = I.max' ⋯} {hk : k = 2 - ↑I.card}
  {hJ : 2 ≤ J.card} {hc : c = J.min' ⋯} {hd : d = J.max' ⋯} {hkJ : k = 2 - ↑J.card},
  I = J →
    a = c →
      b = d →
        SerrePositivity.DifferentialGraded.differential A (s.hom J c d k hJ hc hd hkJ) = s.rhs J c d k hJ hc hd hkJ →
          SerrePositivity.DifferentialGraded.differential A (s.hom I a b k hI ha hb hk) = s.rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_equation_on_image : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (J : Finset (Fin (n + 1)))
  (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card) (ha : a = J.min' ⋯) (hb : b = J.max' ⋯) (hk : k = 2 - ↑J.card),
  let α := Fin.castSuccOrderEmb.toOrderHom;
  SerrePositivity.DifferentialGraded.differential A (s.val.hom (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯) =
    s.val.rhs (Finset.image (⇑α) J) (α a) (α b) k ⋯ ⋯ ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.equation_of_linear : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n),
  s.toLinearData ∈ SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearSubmodule A x y n →
    ∀ (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯)
      (hk : k = 2 - ↑I.card),
      SerrePositivity.DifferentialGraded.differential A (s.val.hom I a b k hI ha hb hk) = s.val.rhs I a b k hI ha hb hk

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toSimplex : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n →
              SerrePositivity.InfinityCategories.DGNerve.Simplex A D (n + 1)

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toPinched : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        {x y : D} →
          {n : ℕ} →
            SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n →
              (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n })

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (f : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n),
  SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex f.toPinched = f

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ext : ∀ {A : Type u_1} [inst : CommRing A] {D : Type u_2}
  [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  {s t : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n}, s.val = t.val → s = t

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.hom_heq_linear_of_last : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data A D x y n) (I : Finset (Fin (n + 2)))
  (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card) (ha : a = I.min' ⋯) (hb : b = I.max' ⋯) (hk : k = 2 - ↑I.card)
  (hbLast : b = Fin.last (n + 1)),
  s.val.hom I a b k hI ha hb hk ≍
    s.toLinearData.component (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast I) k ⋯ ⋯

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_injective : ∀ {A : Type u_1}
  [inst : CommRing A] {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ},
  Function.Injective SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toPinched_toLinearSimplex : ∀ {A : Type u_1} [inst : CommRing A]
  {D : Type u_2} [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D} {n : ℕ}
  (s : (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n })),
  (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex s).toPinched = s

@SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearEquiv : {A : Type u_1} →
  [inst : CommRing A] →
    {D : Type u_2} →
      [inst_1 : SerrePositivity.DifferentialGraded.DGCategory A D] →
        (x y : D) →
          (n : ℕ) →
            (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj (Opposite.op { len := n }) ≃
              SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n
```

## 6. 次のマイルストーン D（本計画の範囲外）

- Semifree(S) を `DGFullSubcategory`（`moduleSemifree` または一点 dg 圏上の複体版）として置き、
  D(S) := `dgNerve` とする。
- h D(S) と Mathlib `DerivedCategory (ModuleCat S)` の比較
  （`DerivedCategory.KProjective.Qh_map_bijective` と semifree 解像度）。
- 関手的 semifree 分解、cone による安定性、底変更 − ⊗_S T の関手性。
- α（quasicategory の一般論）・δ（テンソル積との両立）との境界は §1.2 末尾のとおり。
