# dg nerve（∞ 圏基盤のマイルストーン N）

作成日：2026-10-17。更新：2026-10-18。状態：N0〜N6 と N7a〜N7e は完了。

## 現在地

任意の dg 圏の dg nerve、quasicategory 性、H⁰ 比較、右 pinched 写像空間の Kan 性と π₀、
関手性・厳密自然変換のホモトピーを構成済み。非有界複体の零対象と標準 fiber の ∞ 引き戻し性、
充満 dg 部分圏・Semifree への制限、任意の引き戻しの頂点から標準 fiber への誘導射の
同型性・ホモトピー同値・擬同型性も証明済み。

N7 の必須項目に残りはない。N7f の cofiber の双対は任意項目として未実装。
別系列 γ1 は [e-infinity-algebras.md §3](e-infinity-algebras.md#3-e2bγの工程) に従う。
N7 では coherent nerve・モデル構造・Joyal の定理を使っていない。

公開 1081 宣言の明示型と、基礎 dg 五宣言を含む 1086 件の公理監査が通過し、標準三公理のみ。
集約入口は `SerrePositivity/InfinityCategories/DGNerve.lean`、
監査は `scripts/audit_dg_nerve.lean`。数学の規約・証明方針は
[InfinityCategories/README.md](../../../../SerrePositivity/InfinityCategories/README.md) と Lean の docstring に置く。

### 主要宣言

`SerrePositivity.InfinityCategories`（以下 DGNerve 内のものは相対名）：

| 範囲 | 宣言 |
| --- | --- |
| 定義・quasicategory | `dgNerve`、`dgNerve.instQuasicategory` |
| H⁰ 比較 | `DGNerve.HomotopyComparison.equivalence` |
| 充満部分圏の像 | `DGNerve.range_inclusion` |
| 零対象 | `DGNerve.isTerminalVertex_zero`、`DGNerve.isInitialVertex_zero` |
| 標準 fiber | `DGNerve.standardFiberCone_isLimit`、`DGNerve.standardFiberSquare_isPullback` |
| 充満部分圏・Semifree | `DGNerve.fullFiberSquare_isPullback`、`DGNerve.semifreeFiberSquare_isPullback` |
| 任意の引き戻しの比較 | `DGNerve.squareFiberComparison_nerve_isIso`、`DGNerve.squareFiberComparison_H0_isIso` |
| 比較の帰結 | `DGNerve.squareFiberComparison_homotopyEquivalence`、`DGNerve.squareFiberComparison_quasiIso` |

型と前提は各宣言の Lean ソースと明示的な `#check @` を正本とする。
任意の引き戻しの比較の最終前提は、可換環 A、非有界複体の dg nerve の四角形 F、
`IsPullbackSquare F` だけであり、図式一致や整合式を追加仮定していない。

## 0. 位置づけと方針

2026-10-17 に、Bhatt–Scholze の §7–§8（導来 perfectoid 化、E∞-S 代数の引き戻し）と
K 理論（定理 3.1・補題 4.6）を、ともに ∞ 圏（quasicategory）の基盤の上に載せる方針を決めた。
最初の具体的目標は、可換環 S の導来 ∞ 圏を semifree 複体の充満 dg 部分圏の dg nerve
D(S) := N_dg(Semifree(S)) として定義することである。本計画はその前段として、
**任意の dg 圏に対する dg nerve と、その基本性質**を形式化する。

- 原典：Lurie, Higher Algebra（HA）§1.3.1。Construction 1.3.1.6（dg nerve）、
  Proposition 1.3.1.10（quasicategory）。ホモトピー圏と pinched 写像空間は
  Kerodon §2.5.3、§4.6.5 の記述に従う。
- 規約：リポジトリの dg 層（[DifferentialGraded/README.md](../../../../SerrePositivity/DifferentialGraded/README.md)）
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
各工程を対象ビルド・公開型と公理の監査・コミットをそろえた保存単位とする。
今後の実施記録はコミットメッセージに置き、本文には現在地・残り・方針だけを保つ。

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
4. 本文の現在地と短い主要宣言一覧を更新する。正確な型と前提は Lean ソースと監査、実施記録はコミットを正本とする。
5. 主定理の経路には触れない。README の状態表は変えない。

## 5. 過去の実施記録

旧 §5 の全記録は [archive/dg-nerve-log.md](../../dg-nerve-log.md) へ移した。
ここには今後の実施記録を追記しない。現在地は冒頭、数学は README・Lean docstring、検証記録はコミットに置く。

## 6. 次のマイルストーン D（本計画の範囲外）

- Semifree(S) を `DGFullSubcategory`（`moduleSemifree` または一点 dg 圏上の複体版）として置き、
  D(S) := `dgNerve` とする。
- h D(S) と Mathlib `DerivedCategory (ModuleCat S)` の比較
  （`DerivedCategory.KProjective.Qh_map_bijective` と semifree 解像度）。
- 関手的 semifree 分解、cone による安定性、底変更 − ⊗_S T の関手性。
- α（quasicategory の一般論）・δ（テンソル積との両立）との境界は §1.2 末尾のとおり。

## 7. N7：錐と ∞ 極限（マイルストーン D の D4 の核。2026-10-18 追加）

N0〜N6 の完了を受け、同じチャットが担当する。α の A2（join・slice・極限の定義）が完了したので、
dg nerve の中で「dg の錐が ∞ 極限である」ことを直接の充填で証明する。
α の定義は `InfinityCategories/Core/`：`join`、`sliceOver p`（n 単体は `join Δ[n] K ⟶ X` で K 上 p）、
`sliceOverEquiv`（任意の A に対する普遍性）、`IsTerminalVertex`（n ≥ 1 で最後の頂点が x の
`∂Δ[n] ⟶ X` が延びる）、`JoinCone p`、`IsLimitCone c := IsTerminalVertex (sliceOver p) c`、
`pullbackCone`・`IsPullbackSquare F`（F : Δ[1] ⊗ Δ[1] ⟶ X、cospan Λ[2,2] の錐として）、
極限の一意性（`Limit.lean`・`TerminalUniqueness.lean`）。これらは読むだけで編集しない。

| 工程 | 内容 | 方針 |
| --- | --- | --- |
| N7a（紙） | cospan B → D ← C の錐（頂点 A）が `sliceOver` の終対象である条件を dg nerve の成分で書き下す。未知成分は `[n] ∪ J`（J ∈ {∅,{B},{C},{D},{B,D},{C,D}}）の f で、方程式系が「Hom(X₀, A) → fib(Hom(X₀,B) ⊕ Hom(X₀,C) → Hom(X₀,D)) の錐」の線形代数に帰着すること、A が dg の fiber（B ⊕ C → D の mapping cone の [−1] シフト）なら各次数で明示的に解けることを確認し、`InfinityCategories/README.md` に N7.1 として記録する | N0 と同じ形式。I = [n] の方程式が既知データへの制約になる点に注意し、fiber の普遍性でそれが解けることを明示する |
| N7b 零対象 | 零対象を持つ dg 圏（まず `Complex A`）の dg nerve で、零複体が `IsTerminalVertex` かつ始対象。Hom(x, 0) = 0 なので欠けた成分を 0 と置けば全方程式が成り立つ | 直接の充填 |
| N7c fiber 錐 | `dgNerve A (Complex A)` で、chain map g : B ⟶ D、h : C ⟶ D に対し P := fiber(B ⊕ C → D) と標準の錐（二つの辺、二つの三角形は mapping cone の標準ホモトピー）を `JoinCone` として構成し、`IsPullbackSquare` を証明する。Hom 複体側は Mathlib の `mappingCone` の cochain API（`inl`・`fst`・`snd`・`δ_*`、`ext_from`・`ext_to`）で Hom(X, P) ≅ fib(Hom(X,B) ⊕ Hom(X,C) → Hom(X,D)) を厳密に使う | N2 の `recoverHom`・残差恒等式の道具を再利用する |
| N7d 充満部分圏 | 錐・fiber・有限直和で閉じた充満 dg 部分圏（D の `Semifree S`、D2h の閉性が届いた後）へ N7b・N7c を制限する。`FullSubcategory.range_inclusion` を使う | 充填単体が部分圏の対象だけを使うことを確認 |
| N7e 帰結 | `IsPullbackSquare` な任意の四角形について、その頂点 A から標準 fiber P への誘導射が `nerveHomotopyCategory` で同型（極限の一意性）、よって H⁰ で同型、よってホモトピー同値・擬同型であること | A2 の一意性と N3 の H⁰ 同定の合成 |
| N7f（任意） | coslice と cofiber（pushout）の双対。安定性（pullback ⟺ pushout）は α の A4 と合わせて後で | |

受入基準・記録は §4・§5 と同じ。設計 §3 は変えない。
