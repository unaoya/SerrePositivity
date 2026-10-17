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

## 6. 次のマイルストーン D（本計画の範囲外）

- Semifree(S) を `DGFullSubcategory`（`moduleSemifree` または一点 dg 圏上の複体版）として置き、
  D(S) := `dgNerve` とする。
- h D(S) と Mathlib `DerivedCategory (ModuleCat S)` の比較
  （`DerivedCategory.KProjective.Qh_map_bijective` と semifree 解像度）。
- 関手的 semifree 分解、cone による安定性、底変更 − ⊗_S T の関手性。
- α（quasicategory の一般論）・δ（テンソル積との両立）との境界は §1.2 末尾のとおり。
