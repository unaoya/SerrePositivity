# D(S)：semifree 複体の dg nerve としての導来 ∞ 圏（レーン D）

作成日：2026-10-17。状態：D2 から着手（N に依存しない）。
全体の目標と依存関係の正本は [infinity-categories.md](infinity-categories.md) §0・§3。
dg nerve（レーン N）は [dg-nerve.md](dg-nerve.md)。

## 0. 目標

可換環 S に対し、semifree 複体の充満 dg 部分圏 Semifree(S) ⊆ Ch(S) の dg nerve として
導来 ∞ 圏 D(S) を定義し、そのホモトピー圏が Mathlib の導来圏 `DerivedCategory (ModuleCat S)` と
圏同値であることを証明する。

| 段 | 主張 | 依存 |
| --- | --- | --- |
| D2 | `HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat S)` | なし（古典的） |
| D1 | `Semifree S := DGFullSubcategory (Complex S) (complexSemifree S)`、`D(S) := dgNerve S (Semifree S)`、quasicategory | N1・N2 |
| D3 | `HomotopyCategory₂ ((truncation 2).obj D(S)) ≌ DerivedCategory (ModuleCat S)` | N3・D2 |
| D4 | 零対象、「四角形が ∞ 引き戻し ⟺ A → fib(B ⊕ C → D) が擬同型」、D(S) の安定性、h D(S) の三角構造が Mathlib のものと一致 | α の A2・A3 |

semifree を K-projective より優先する理由：cone・シフト・直和・テンソル積・底変更で閉じ、
D(S)^⊗ を対称モノイダル dg 圏の dg nerve として作れる。K-projective 版との同値は後の項目。

## 1. 数学的内容（D2）

- semifree 複体：部分複体の増大列 0 = P(−1) ⊆ P(0) ⊆ … で網羅的、各商 P(n)/P(n−1) が
  微分零の自由複体 ⊕ S⟨k⟩ の直和。
- semifree ⇒ K-projective（Hom^•(P, N) は N が acyclic なら acyclic）：段ごとの帰納と
  telescope の Milnor 列。
- 任意の複体 M に semifree 解像度 P → M（全射な擬同型）がある。
- K-projective どうしの擬同型はホモトピー同値。
- よって H⁰(Semifree(S)) → K(S) → D(S) は充満忠実（K-projective からの Hom は K と D で一致）
  かつ本質的全射（解像度）。

## 2. 既存資産

dg 加群層（`SerrePositivity/DifferentialGraded/`）は一点 dg 圏 `PUnit` 上の加群と複体の橋を
既に持つので、D2 はほぼ転送で済む。

| 宣言 | 場所 | 内容 |
| --- | --- | --- |
| `ringModuleEquivalence : ModuleCategory A PUnit ≌ Complex A` | `Module/Ring.lean` | 一点 dg 圏上の加群と複体の同値（`ringModule`、`ringModuleObjEquiv`） |
| `ModuleSemifreeFiltration`、`moduleSemifree` | `Module/Semifree/Basic.lean` | dg 加群の semifree filtration（`freeSphere` 余積、次数付き分裂、余極限） |
| `exists_semifree_resolution` | `Module/Semifree/Resolution.lean` | 任意の dg 加群の semifree 解像度（全射擬同型） |
| `moduleSemifree_homotopicallyProjective` | `Derived/SemifreeProjective.lean` | semifree ⇒ homotopically projective |
| `ringModule_homotopicallyProjective_iff` | `Module/RingProjective.lean` | 一点 dg 圏上の homotopically projective ⟺ Mathlib `IsKProjective` |
| `isKProjective_iff_homComplex_acyclic` | `Complexes/KProjectiveHom.lean` | `IsKProjective` ⟺ Hom 複体の acyclic 性 |
| `ringModuleQuasiIso_iff` | `Derived/Ring.lean` | 加群の擬同型と複体の擬同型の一致 |
| `complexHomotopyEquivalence : HomotopyCategory A (Complex A) ≌ HomotopyCategory (ModuleCat A) (.up ℤ)` | `Category/ComplexHomotopyComparison.lean` | 主 dg 圏の H⁰ と Mathlib のホモトピー圏 |
| `DGFullSubcategory`、`dgFullSubcategoryInclusion` | `Category/FullSubcategory.lean` | 充満 dg 部分圏（Z⁰・H⁰ で包含は充満忠実） |
| `ringDerivedEquivalence : DerivedModuleCategory A PUnit ≌ DerivedCategory (ModuleCat A)` | `Derived/Ring.lean` | 主導来圏と Mathlib の導来圏 |
| `complexHomotopyRingDerivedIso` | `Perfect/RingHomotopyDerivedComparison.lean` | `HasDerivedCategory.{w}` の扱いの手本 |
| `complexSphere`、`complexDisk`、`complex_quasiIso_of_boundary_lifting` | `Complexes/Cells.lean`、`CellCriterion.lean` | 複体の球面・円板と cell 判定 |
| Mathlib `DerivedCategory.KProjective.Qh_map_bijective`、`quasiIso_iff` | `Algebra/Homology/DerivedCategory/KProjective.lean` | K-projective からの Hom は K と D で一致、K-projective 間の擬同型はホモトピー同値 |

## 3. 工程

配置は `SerrePositivity/InfinityCategories/Derived/`、namespace `SerrePositivity.InfinityCategories`、
集約ファイル `SerrePositivity/InfinityCategories/Derived.lean` をルートに 1 行で追加する。
レーン N のディレクトリ `InfinityCategories/DGNerve/` と `InfinityCategories/README.md` は編集しない。

| 工程 | ファイル | 内容 |
| --- | --- | --- |
| D2a | `Derived/Semifree.lean` | `complexSemifree S : ObjectProperty (Complex S)` を `moduleSemifree S PUnit` の `ringModuleEquivalence` による転送で定義し、展開補題（filtration の各段が複体として何か）を付ける。`complexSphere` との対応 |
| D2b | `Derived/SemifreeKProjective.lean` | `complexSemifree S P → P.IsKProjective`（`moduleSemifree_homotopicallyProjective` と `ringModule_homotopicallyProjective_iff`） |
| D2c | `Derived/SemifreeResolution.lean` | `∀ M : Complex S, ∃ P q, complexSemifree S P ∧ QuasiIso q`（各次数全射も保持。`exists_semifree_resolution S PUnit` と `ringModuleQuasiIso_iff` の転送） |
| D2d | `Derived/SemifreeSubcategory.lean` | `Semifree S := DGFullSubcategory (Complex S) (complexSemifree S)`。`HomotopyCategory S (Semifree S)` から `HomotopyCategory (ModuleCat S) (.up ℤ)` への充満忠実関手（包含と `complexHomotopyEquivalence`） |
| D2e | `Derived/DerivedComparison.lean` | 関手 `HomotopyCategory S (Semifree S) ⥤ DerivedCategory (ModuleCat S)` := D2d ⋙ `Qh`。充満忠実は `Qh_map_bijective`、本質的全射は D2c と「`Q` は擬同型を同型に送る」。`semifreeDerivedEquivalence` |
| D2f | `Derived/DerivedComparisonShift.lean` | 同値のシフトとの両立（`CommShift`）。D4 の三角構造の一致に使う。任意 |
| D2g | `Derived/Checks.lean`、`scripts/audit_derived_infinity.lean` | `HasDerivedCategory.standard` での具体化と公理監査 |
| D1 | `Derived/InfinityCategory.lean` | N1・N2 の後。`derivedInfinityCategory S := dgNerve S (Semifree S)`、quasicategory |
| D3 | `Derived/HomotopyCategoryComparison.lean` | N3 の後。`HomotopyCategory₂` の同値と D2e の合成 |
| D4 | 別途 | α の A2・A3 の後に計画を書く |

## 4. 設計上の決定

- `HasDerivedCategory` は宣言では `[HasDerivedCategory.{w} (ModuleCat.{u} S)]` を変数にし、
  検査では `HasDerivedCategory.standard` を局所 instance にする（`Perfect/RingPerfectRepresentatives.lean` と同じ）。
- `complexSemifree` は転送で定義する。複体レベルの filtration 構造体は、テンソル積や底変更の
  保存を示す段階で必要になったときに追加し、転送定義との同値を証明する。
- 新しい `sorry`・公理・引用は導入しない。dg 層のファイルは編集せず、必要な補題は新規ファイルに置く。

## 5. 受入基準

1. 各ファイルがビルドし、公開宣言は標準 3 公理のみ。
2. docstring は README「Conventions」の形式。
3. §6 に公開宣言名・正確な型・前提・未完了の範囲を記録する。
4. 主定理の経路には触れない。

## 6. 記録

（各工程の完了時に追記する。）

### D2a（2026-10-17）

完了。以下は namespace `SerrePositivity.InfinityCategories`、共通前提
`(S : Type u) [CommRing S]`。`open CategoryTheory DifferentialGraded` とする。
公開宣言の型（暗黙引数も明示）：

```lean
complexSemifree (S : Type u) [CommRing S] : ObjectProperty (Complex S)
complexSemifree_iff (S : Type u) [CommRing S] (P : Complex S) :
  complexSemifree S P ↔ Nonempty (ModuleSemifreeFiltration S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S P)))
complexSemifree_evaluation (S : Type u) [CommRing S]
  (M : ModuleCategory S PUnit.{1}) :
  complexSemifree S ((ringModuleEquivalence S).functor.obj M) ↔ moduleSemifree S PUnit.{1} M
complexSemifreeStage (S : Type u) [CommRing S] {M : ModuleCategory S PUnit.{1}}
  (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) : Complex S
complexSemifreeQuotient (S : Type u) [CommRing S] {M : ModuleCategory S PUnit.{1}}
  (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) : Complex S
freeSphereEvaluationIso (S : Type u) [CommRing S] (n : ℤ) :
  (ringModuleEquivalence S).functor.obj (freeSphere S PUnit.{1} PUnit.unit n) ≅ complexSphere S n
spherePresentationEvaluationIso (S : Type u) [CommRing S] {M : ModuleCategory S PUnit.{1}}
  (E : ModuleSphereFreePresentation S PUnit.{1} M) :
  (ringModuleEquivalence S).functor.obj M ≅ ∐ (fun t : E.Index => complexSphere S (E.degree t))
complexSemifreeStageZeroIso (S : Type u) [CommRing S] {M : ModuleCategory S PUnit.{1}}
  (F : ModuleSemifreeFiltration S PUnit.{1} M) :
  complexSemifreeStage S F 0 ≅ ∐ (fun t : F.initial.Index => complexSphere S (F.initial.degree t))
complexSemifreeQuotientIso (S : Type u) [CommRing S] {M : ModuleCategory S PUnit.{1}}
  (F : ModuleSemifreeFiltration S PUnit.{1} M) (n : ℕ) :
  complexSemifreeQuotient S F n ≅ ∐ (fun t : (F.quotientPresentation n).Index =>
    complexSphere S ((F.quotientPresentation n).degree t))
```

対象ビルド `lake build SerrePositivity.InfinityCategories.Derived.Semifree` 成功（終了コード 0）。
`lake env lean scripts/audit_derived_infinity.lean` 成功（終了コード 0）、全9宣言は
`propext`, `Classical.choice`, `Quot.sound` のみ。D2a に残りはない。
未完了：D2b〜D2e・D2g。D2f は任意、D1・D3・D4 は今回の範囲外。

### D2b（2026-10-17）

完了。公開定理（namespace は同上）：
```lean
complexSemifree_isKProjective (S : Type u) [CommRing S]
  {P : Complex S} (hP : complexSemifree S P) : P.IsKProjective
```
前提は可換環と semifree 性のみ。既存の加群の射影性と一点環の橋を合成した。
対象ビルド `lake build SerrePositivity.InfinityCategories.Derived.SemifreeKProjective`、
`lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
全10公開宣言の公理は標準3公理のみ。D2b に残りなし。未完了は D2c〜D2e・D2g。

### D2c（2026-10-17）

完了。公開定理（namespace は同上）：
```lean
exists_complexSemifree_resolution (S : Type u) [CommRing S] (M : Complex S) :
  ∃ (P : Complex S) (q : P ⟶ M),
    complexSemifree S P ∧ (∀ n : ℤ, Function.Surjective (q.f n)) ∧
      HomologicalComplex.QuasiIso q
```
前提は可換環のみ。有界性・有限生成性・射影性の仮定なし。一点加群の解像度を評価した。
対象ビルド `lake build SerrePositivity.InfinityCategories.Derived.SemifreeResolution` と
`lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
全11公開宣言の公理は標準3公理のみ。D2c に残りなし。未完了は D2d・D2e・D2g。

### D2d（2026-10-17）

完了。公開宣言（namespace は同上、共通前提 `(S : Type u) [CommRing S]`）：
```lean
Semifree (S : Type u) [CommRing S] := DGFullSubcategory (Complex S) (complexSemifree S)
semifreeHomotopyComparison (S : Type u) [CommRing S] :
  DifferentialGraded.HomotopyCategory S (Semifree S) ⥤
    _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ)
semifreeHomotopyComparisonFull (S : Type u) [CommRing S] :
  (semifreeHomotopyComparison S).Full
semifreeHomotopyComparisonFaithful (S : Type u) [CommRing S] :
  (semifreeHomotopyComparison S).Faithful
```
包含と `complexHomotopyEquivalence` の順関手を合成した。追加の前提なし。
対象ビルド `lake build SerrePositivity.InfinityCategories.Derived.SemifreeSubcategory` と
`lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
全15公開宣言の公理は標準3公理のみ。D2d に残りなし。未完了は D2e・D2g。

### D2e（2026-10-17）

完了。共通前提は `(S : Type u) [CommRing S]
[HasDerivedCategory.{w} (ModuleCat.{u} S)]`。namespace は同上。
以下の全宣言にこの前提を付す（`H := DifferentialGraded.HomotopyCategory S (Semifree S)`、
`D := DerivedCategory (ModuleCat.{u} S)` は型を短縮して表示するための記号）：

```lean
semifreeDerivedComparison : H ⥤ D
semifreeDerivedComparison_map_bijective (X Y : H) :
  Function.Bijective ((semifreeDerivedComparison S).map :
    (X ⟶ Y) → ((semifreeDerivedComparison S).obj X ⟶ (semifreeDerivedComparison S).obj Y))
semifreeDerivedComparisonFull : (semifreeDerivedComparison S).Full
semifreeDerivedComparisonFaithful : (semifreeDerivedComparison S).Faithful
semifreeDerivedComparisonEssSurj : (semifreeDerivedComparison S).EssSurj
semifreeDerivedComparisonIsEquivalence : (semifreeDerivedComparison S).IsEquivalence
semifreeDerivedEquivalence (S : Type u) [CommRing S]
  [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
  DifferentialGraded.HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat.{u} S)
```

比較関手は D2d の関手と `DerivedCategory.Qh` の合成。
K-projective からの `CochainComplex.IsKProjective.Qh_map_bijective` により充満忠実、
D2c と `Q` が擬同型を同型に送ることにより本質的全射。
`HasDerivedCategory` は導来圏の選択であり、未証明の数学的性質を仮定する束ではない。
対象ビルド `lake build SerrePositivity.InfinityCategories.Derived.DerivedComparison` と
`lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
全22公開宣言の公理は標準3公理のみ。D2e に残りなし。未完了は D2g（標準 instance での
具体化、集約ファイル、ルートの import）。D2f は任意で未実装、D1・D3・D4 は範囲外。

### D2g・集約（2026-10-17）

完了。`Derived/Checks.lean` では `HasDerivedCategory.standard` を局所 instance にし、
任意の `(S : Type u) [CommRing S]` に対して公開同値・逆関手・単位・余単位を型検査した。
さらに `S = ℤ`、`ModuleCat.{0} ℤ` で具体化した。新しい名前付き公開宣言はない。
型検査した型は次のとおり（`E := semifreeDerivedEquivalence S`）：

```lean
DifferentialGraded.HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat.{u} S)
DifferentialGraded.HomotopyCategory ℤ (Semifree ℤ) ≌ DerivedCategory (ModuleCat.{0} ℤ)
DerivedCategory (ModuleCat.{u} S) ⥤ DifferentialGraded.HomotopyCategory S (Semifree S)
𝟭 _ ≅ E.functor ⋙ E.inverse
E.inverse ⋙ E.functor ≅ 𝟭 _
```

`InfinityCategories/Derived.lean` に D2 の各モジュールを集約し、ルート
`SerrePositivity.lean` に `public import SerrePositivity.InfinityCategories.Derived` の1行を追加。
既存の他チャットの import 変更はコミットに含めない。

検証はすべて終了コード 0：
- `set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived`（2174 jobs）。
- `set -o pipefail; lake env lean scripts/audit_derived_infinity.lean`。
  公開22宣言を個別表示し、実装5モジュールの生成補題を含む42宣言を `collectAxioms` で検査。
  標準3公理以外があればエラーにする監査が成功した。
- `set -o pipefail; lake build SerrePositivity`（7323 jobs）。既存部分の警告はあるがエラーなし。
- 新規 Lean ファイルに `sorry`・追加 `axiom` がなく、全公開名が個別監査に含まれることを確認。

D2a〜D2e・D2g は無条件の数学的成果として完了（宣言上は可換環と導来圏の選択のみ）。
未完了：任意工程 D2f の `CommShift`。D1・D3・D4 は別途指示の範囲であり未着手。
