# D(S) の実施記録・公開型一覧

本文と現在地は [derived-infinity-category.md](../derived-infinity-category.md)。
過去の §6 を移した記録であり、実装の正本は各 Lean モジュールと公理監査。

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

### D1（2026-10-17、N1 完了後）

`dg-nerve.md` §5 の「N1d・N1 完了」を確認して着手した。N2〜N6 は未完了の記録。
公開宣言（namespace `SerrePositivity.InfinityCategories`、共通前提 `(S : Type u) [CommRing S]`）：
```lean
derivedInfinityCategory (S : Type u) [CommRing S] : SSet.{u + 1}
derivedInfinityCategory_obj (S : Type u) [CommRing S] (n : ℕ) :
  (derivedInfinityCategory S) _⦋n⦌ = DGNerve.Simplex S (Semifree S) n
derivedInfinityCategoryVertexEquiv (S : Type u) [CommRing S] :
  (derivedInfinityCategory S) _⦋0⦌ ≃ Semifree S
derivedInfinityCategoryEdgeEquiv (S : Type u) [CommRing S] :
  (derivedInfinityCategory S) _⦋1⦌ ≃ Σ obj : Fin 2 → Semifree S,
    zeroCycles (homObject S (Semifree S) (obj 0) (obj 1))
derivedInfinityCategoryTriangleEquiv (S : Type u) [CommRing S] :
  (derivedInfinityCategory S) _⦋2⦌ ≃ DGNerve.TriangleData S (Semifree S)
```

定義は `dgNerve S (Semifree S)`。辺・三角形の特徴づけを N1 の公開同値から具体化した。
`set -o pipefail` の下で `lake build SerrePositivity.InfinityCategories.Derived` と
`lake env lean scripts/audit_derived_infinity.lean` が終了コード 0。
公理監査は公開27宣言と、生成補題を含む6モジュール47宣言で標準3公理のみ。
D1 の定義・低次特徴づけは完了。quasicategory instance は N2 完了記録待ちで未実装。
D2f・D2h は未完了、D2i は任意・未着手。D3 は別途指示待ち。

### D2f・D2h 途中／依存先の並行変更による停止（2026-10-17）

未完了。`Derived/SemifreeClosure.lean` に同型・零・sphere・整数シフトの閉性を実装し、
`Derived/DerivedComparisonShift.lean` に元の複体のシフトによる H⁰ のシフトと、
`semifreeDerivedEquivalence` の順関手の `CommShift ℤ` を実装した。
`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived.DerivedComparisonShift`
は終了コード 0（2174 jobs）。ただし保存単位の公理監査は未実施なので完了扱いしない。

続く `set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` が終了コード 1。
並行変更中の `InfinityCategories/DGNerve/Algebra.lean:116:8` で
`typeclass instance problem is stuck: SMulCommClass ?m.45 ?m.46 ?m.47`。
ビルドと `&&` でつないだ公理監査は起動されなかった。
指示に従い依存先には手を加えず、import の迂回も作らず停止した。
新規2ファイル、集約入口・Checks・監査スクリプトの変更は未コミットで保持。
D1 の保存済み成果（`f67411c3`）とは区別する。

未完了：D2f の集約ビルド・公理監査・保存、D2h の余積と任意の射の cone の閉性、
D2h 全体の監査・保存。D2i は未着手。D1 の quasicategory は N2 完了記録待ち。
依存先が復旧した後は同じ集約ビルドと監査を再実行して続ける。

### D2f 完了・D2h のシフトまで（2026-10-17）

依存先の復旧を集約ビルドで確認し、監査を再実行して成功した。
以下は namespace `SerrePositivity.InfinityCategories`。共通前提は
`(S : Type u) [CommRing S]`。表示用に `H := DifferentialGraded.HomotopyCategory S (Semifree S)`、
`C := semifreeHomotopyComparison S` と略記する。
公開宣言の正確な型：

```lean
complexSemifree_of_iso (S : Type u) [CommRing S] {P Q : Complex S}
  (e : P ≅ Q) (hP : complexSemifree S P) : complexSemifree S Q
complexSemifree_zero (S : Type u) [CommRing S] : complexSemifree S (0 : Complex S)
complexSemifree_sphere (S : Type u) [CommRing S] (n : ℤ) : complexSemifree S (complexSphere S n)
complexSemifree_shift (S : Type u) [CommRing S] {P : Complex S}
  (hP : complexSemifree S P) (s : ℤ) : complexSemifree S (P⟦s⟧)
semifreeHomotopyObject (S : Type u) [CommRing S] (X : H) : Semifree S
semifreeShiftObject (S : Type u) [CommRing S] (s : ℤ) (X : H) : H
semifreeShiftObjectIso (S : Type u) [CommRing S] (s : ℤ) (X : H) :
  C.obj (semifreeShiftObject S s X) ≅ (C.obj X)⟦s⟧
semifreeShift (S : Type u) [CommRing S] (s : ℤ) : H ⥤ H
semifreeShiftComparisonIso (S : Type u) [CommRing S] (s : ℤ) :
  semifreeShift S s ⋙ C ≅ C ⋙ shiftFunctor (_root_.HomotopyCategory (ModuleCat S) (.up ℤ)) s
semifreeHomotopyHasShift (S : Type u) [CommRing S] : HasShift H ℤ
semifreeHomotopyComparisonCommShift (S : Type u) [CommRing S] : C.CommShift ℤ
semifreeDerivedComparisonCommShift (S : Type u) [CommRing S]
  [HasDerivedCategory.{w} (ModuleCat.{u} S)] : (semifreeDerivedComparison S).CommShift ℤ
semifreeDerivedEquivalenceCommShift (S : Type u) [CommRing S]
  [HasDerivedCategory.{w} (ModuleCat.{u} S)] : (semifreeDerivedEquivalence S).functor.CommShift ℤ
```

零・sphere は定数 filtration、シフトは段・商・次数付き分裂をシフトして構成した。
H⁰ のシフトは対象として元の複体を実際にシフトし、通常のホモトピー圏のシフトを
充満忠実比較で引き戻して零・加法の整合性を付けた。`Qh` と合成して D2f を得る。
Checks に任意環および整数環での標準導来圏に対する `CommShift ℤ` の具体化を追加した。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3581 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
公開40宣言と生成補題を含む8モジュール120宣言の公理は標準3公理のみ。
D2f は完了。D2h は同型・零・sphere・シフトのみ完了で、全体の完成とは数えない。
未完了：D2h の余積・任意の射の cone。D2i は任意・未着手。
D1 の quasicategory は N2 完了記録待ち、D3 は別途指示待ち。

### D2h 余積の閉性（2026-10-17）

任意の u-small な添字型と有限添字について完了。namespace は同上。
公開宣言の正確な型・前提：
```lean
complexSemifree_coproduct (S : Type u) [CommRing S]
  {I : Type v} [Small.{u} I] (P : I → Complex S)
  (hP : ∀ i, complexSemifree S (P i)) : complexSemifree S (∐ P)
complexSemifree_finiteCoproduct (S : Type u) [CommRing S]
  (n : ℕ) (P : Fin n → Complex S)
  (hP : ∀ i, complexSemifree S (P i)) : complexSemifree S (∐ P)
```
段・商・次数付き分裂を成分ごとに余積にし、自由 sphere 表示の添字を直和型にまとめた。
余極限の存在・普遍性は各成分の filtration から実際に構成した。
宇宙の異なる u-small な添字型は `Shrink` と余積の再添字付け同型で処理する。
有限性・有界性・有限生成性の追加仮定はない（有限版だけ `Fin n` を使う）。
Checks は整数環で添字の宇宙が独立な場合を具体化する。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3611 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
公開42宣言と、生成補題を含む8モジュール146宣言で標準3公理のみ。
D2h 全体は未完了：任意の semifree 間の射の mapping cone の閉性が残る。
D2f は完了。D2i は任意・未着手。D1 の quasicategory は N2 完了記録待ち。

### D2h cone の補助表現に関する設計提案（未承認・未実装）

任意の射 `f : P ⟶ Q` は選んだ二つの filtration の段を保存するとは限らない。
初期段が無限の自由 sphere 余積なら、その生成元の像が Q の任意に高い段に現れ得るため、
段ごとの cone や、一律の有限個の段の繰り上げでは一般の場合を構成できない。

§4 の「複体レベルの filtration 構造体はテンソル積や底変更で必要になったときに追加」
という時期を前倒しし、補助的な semibasis 表現を追加することを提案する。
`complexSemifree` の正本は既存の転送定義のままとし、新しい公理・仮定にはしない。
配置候補は `Derived/SemifreeBasis.lean`、namespace は既存どおり。
補助データは、各次数 k の基底 `basis k : Module.Basis (I k) S (P.X k)` と
自然数値 `height k : I k → ℕ`、各基底元の微分の有限な基底展開の台にある元の height が
元の height より真に小さいという法則。

1. 既存の filtration の自由商と次数付き分裂からこのデータの存在を証明する。
2. 逆に height ≤ n の基底元で張る部分複体を使って `ModuleSemifreeFiltration` を構成し、
   その存在と `complexSemifree S P` の同値を証明する。
3. cone の基底を Q と P[1] の基底の直和にする。P 側の新しい height を、f の像に出る
   有限個の Q 基底元の height と、微分に出る P 基底元の新 height の最大値 + 1 として、
   元の P の height による整礎再帰で定義する。これで cone の微分が height を下げる。
4. 2 の逆向きで、要求された無条件の cone 閉性へ戻す。

この補助表現の追加は初回指示の設計変更の承認条項に従い、承認前には実装しない。
cone の閉性を、filtration を保存する射だけの条件付き成果へ置き換えない。

### D2h 補助表現の承認・基礎部分（2026-10-17）

ユーザーが選択肢「補助表現の追加を承認する（推奨）」に回答したため、上の設計提案を承認済みとする。
`Derived/SemifreeBasis.lean` を追加した。既存の `complexSemifree` は変更していない。
これは cone 閉性のための基礎部分の保存であり、D2h 全体の完成ではない。

公開宣言：namespace `SerrePositivity.InfinityCategories` に
`ComplexSemifreeBasis (S : Type u) [CommRing S] (P : Complex S) : Type (u + 1)`。
これは次のフィールドを持つ数学的データであり、存在を仮定する追加公理ではない。
```lean
Index : ℤ → Type u
basis : ∀ k, Module.Basis (Index k) S (P.X k)
height : ∀ k, Index k → ℕ
lowering : ∀ (k : ℤ) (i : Index k) (j : Index (k + 1)),
  j ∈ ((basis (k + 1)).repr ((P.d k (k + 1)) (basis k i))).support →
    height (k + 1) j < height k i
```
フィールドの公開名は `ComplexSemifreeBasis.Index`・`.basis`・`.height`・`.lowering`。
以下は namespace `SerrePositivity.InfinityCategories.ComplexSemifreeBasis`。
全ての共通引数は `{S : Type u} [CommRing S] {P : Complex S} (B : ComplexSemifreeBasis S P)`。
公開宣言の正確な残りの型：
```lean
stageSubmodule (n : ℕ) (k : ℤ) : Submodule S (P.X k)
mem_stageSubmodule_iff (n : ℕ) (k : ℤ) (x : P.X k) :
  x ∈ B.stageSubmodule n k ↔ ∀ i ∈ ((B.basis k).repr x).support, B.height k i ≤ n
stageSubmodule_mono {n m : ℕ} (h : n ≤ m) (k : ℤ) :
  B.stageSubmodule n k ≤ B.stageSubmodule m k
exists_mem_stageSubmodule (k : ℤ) (x : P.X k) : ∃ n, x ∈ B.stageSubmodule n k
differential_mem_previous (n : ℕ) (k : ℤ) {x : P.X k}
  (hx : x ∈ B.stageSubmodule (n + 1) k) :
  (P.d k (k + 1)) x ∈ B.stageSubmodule n (k + 1)
differential_mem_stage (n : ℕ) (k : ℤ) {x : P.X k}
  (hx : x ∈ B.stageSubmodule n k) : (P.d k (k + 1)) x ∈ B.stageSubmodule n (k + 1)
stageDifferential (n : ℕ) (k : ℤ) :
  ModuleCat.of S (B.stageSubmodule n k) ⟶ ModuleCat.of S (B.stageSubmodule n (k + 1))
stageDifferential_squared (n : ℕ) (k : ℤ) :
  B.stageDifferential n k ≫ B.stageDifferential n (k + 1) = 0
stageComplex (n : ℕ) : Complex S
stageInclusion (n : ℕ) : B.stageComplex n ⟶ P
stageMap {n m : ℕ} (h : n ≤ m) : B.stageComplex n ⟶ B.stageComplex m
stageMap_inclusion {n m : ℕ} (h : n ≤ m) :
  B.stageMap h ≫ B.stageInclusion m = B.stageInclusion n
stageBasis (n : ℕ) (k : ℤ) :
  Module.Basis {i : B.Index k // B.height k i ≤ n} S (B.stageSubmodule n k)
stageDiagram : ℕ ⥤ Complex S
stageCocone : CategoryTheory.Limits.Cocone B.stageDiagram
differential_eq_zero_on_stageZero (k : ℤ) {x : P.X k}
  (hx : x ∈ B.stageSubmodule 0 k) : (P.d k (k + 1)) x = 0
```

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3614 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
新規21個の名前（構造と4フィールドを含む）を個別監査し、9モジュール193宣言を機械監査。
許された標準3公理のみ。段の微分閉性、網羅性、初期段の微分零を実際に証明した。
未完了：cocone の余極限性、自由商の表示、既存 filtration との同値、cone の高さ再構成。
これらの未完了を `ComplexSemifreeBasis` の存在仮定で代替して完了とはしない。
D2i は D2h 後の任意工程で未着手。D1 の quasicategory は N2 完了記録待ち。

### D2h semibasis の段の余極限（2026-10-17）

`Derived/SemifreeBasisColimit.lean` を追加し、高さで切った部分複体の cocone の
余極限普遍性を証明した。namespace は `SerrePositivity.InfinityCategories.ComplexSemifreeBasis`。
以下の共通引数は `{S : Type u} [CommRing S] {P : Complex S} (B : ComplexSemifreeBasis S P)`。
公開宣言の正確な残りの型：
```lean
basis_mem_stage (k : ℤ) (i : B.Index k) (n : ℕ) (h : B.height k i ≤ n) :
  B.basis k i ∈ B.stageSubmodule n k
colimitComponent (c : CategoryTheory.Limits.Cocone B.stageDiagram) (k : ℤ) :
  P.X k →ₗ[S] c.pt.X k
colimitComponent_comm (c : CategoryTheory.Limits.Cocone B.stageDiagram) (k : ℤ) :
  ModuleCat.ofHom (B.colimitComponent c k) ≫ c.pt.d k (k + 1) =
    P.d k (k + 1) ≫ ModuleCat.ofHom (B.colimitComponent c (k + 1))
stageColimitDesc (c : CategoryTheory.Limits.Cocone B.stageDiagram) : P ⟶ c.pt
stageColimitDesc_fac (c : CategoryTheory.Limits.Cocone B.stageDiagram) (n : ℕ) :
  B.stageInclusion n ≫ B.stageColimitDesc c = c.ι.app n
stageCoconeIsColimit : CategoryTheory.Limits.IsColimit B.stageCocone
```
各基底元をその高さの段から写すことで線形延長し、線形包上の帰納で各段との一致を証明した。
各斉次要素がある段に属することから微分との可換性を示し、基底元上の値で一意性を示した。
追加の有界性・有限生成性の仮定はない。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3615 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
新規公開6宣言と、10モジュール206宣言の公理は標準3公理のみ。
未完了：自由商の表示、既存 filtration との同値、cone の高さ再構成と閉性。
D2h 全体を完成とは数えない。D2i は未着手、D1 の quasicategory は N2 完了記録待ち。

### D2h cone の高さの再構成（2026-10-17）

`Derived/SemifreeBasisHeight.lean` を追加した。
namespace `SerrePositivity.InfinityCategories`、共通引数
`{I : Type u} (rank : I → ℕ) (dependencies : I → Finset I)
(lowering : ∀ i j, j ∈ dependencies i → rank j < rank i) (bound : I → ℕ)`。
`R := semifreeReheight rank dependencies lowering bound` と略記して公開型を示す。
```lean
semifreeReheight : I → ℕ
semifreeReheight_eq (i : I) :
  R i = max (bound i) ((dependencies i).attach.sup (fun j => R j.val)) + 1
bound_lt_semifreeReheight (i : I) : bound i < R i
semifreeReheight_dependency_lt (i j : I) (h : j ∈ dependencies i) : R j < R i
```
namespace `SerrePositivity.InfinityCategories.ComplexSemifreeBasis`、共通引数
`{S : Type u} [CommRing S] {P Q : Complex S} (B : ComplexSemifreeBasis S P)`：
```lean
differentialDependencies (a : Σ k, B.Index k) : Finset (Σ k, B.Index k)
differentialDependencies_lowering (a b : Σ k, B.Index k)
  (h : b ∈ B.differentialDependencies a) : B.height b.1 b.2 < B.height a.1 a.2
```
さらに `(C : ComplexSemifreeBasis S Q) (f : P ⟶ Q)` を引数に取る公開宣言：
```lean
imageHeightBound (a : Σ k, B.Index k) : ℕ
coneSourceHeight (k : ℤ) (i : B.Index k) : ℕ
image_lt_coneSourceHeight (k : ℤ) (i : B.Index k) (j : C.Index k)
  (h : j ∈ ((C.basis k).repr ((f.f k) (B.basis k i))).support) :
  C.height k j < B.coneSourceHeight C f k i
differential_lt_coneSourceHeight (k : ℤ) (i : B.Index k) (j : B.Index (k + 1))
  (h : j ∈ ((B.basis (k + 1)).repr ((P.d k (k + 1)) (B.basis k i))).support) :
  B.coneSourceHeight C f (k + 1) j < B.coneSourceHeight C f k i
```
`measure rank` による整礎再帰で、依存先と指定下限の最大値 + 1 を定めた。
微分の台を次数付き添字へ埋め込み、像に出る終域の高さを下限として具体化した。
f が既存 filtration を保存する仮定や、一律の段のずれの仮定はない。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3616 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
新規公開10宣言と、11モジュール220宣言の公理は標準3公理のみ。
未完了：自由商の表示と既存 filtration との同値、cone の基底への高さの適用、無条件の cone 閉性。
D2h 全体は未完了。D2i は未着手、D1 の quasicategory は N2 完了記録待ち。

### D2h 微分零の自由複体の sphere 表示（2026-10-17）

`Derived/ZeroBasisSpheres.lean` を追加した。namespace は `SerrePositivity.InfinityCategories`。
公開宣言の正確な型（共通引数 `(S : Type u) [CommRing S]`）：
```lean
sphereCycle_comp {P Q : Complex S} (k : ℤ) (f : complexSphere S k ⟶ P) (g : P ⟶ Q) :
  (complexSphereHomEquiv S Q k (f ≫ g)).val =
    (g.f k) (complexSphereHomEquiv S P k f).val
```
以下はさらに `{P : Complex S} {I : ℤ → Type u}
(E : ∀ k, Module.Basis (I k) S (P.X k)) (hz : ∀ k : ℤ, P.d k (k + 1) = 0)` を共通引数とする。
`F := fun a : Σ k, I k => complexSphere S a.1` と略記：
```lean
zeroBasisSphereCofan : CategoryTheory.Limits.Cofan F
zeroBasisSphereDesc (c : CategoryTheory.Limits.Cofan F) : P ⟶ c.pt
zeroBasisSphereDesc_fac (c : CategoryTheory.Limits.Cofan F) (a : Σ k, I k) :
  (zeroBasisSphereCofan S E hz).inj a ≫ zeroBasisSphereDesc S E hz c = c.inj a
zeroBasisSphereIsColimit : CategoryTheory.Limits.IsColimit (zeroBasisSphereCofan S E hz)
zeroBasisSphereIso : P ≅ ∐ F
zeroBasisModuleSpherePresentation : ModuleSphereFreePresentation S PUnit.{1}
  (ForgetEnrichment.of (Complex S) (ringModule S P))
```
各基底元を cycle とする sphere 射を取り、基底からの線形延長で余積の普遍性を証明した。
一点加群への表示は評価の余積保存と `freeSphereEvaluationIso` を経由して戻した。
基底の有限性・環の整域性などは仮定しない。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3625 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
新規公開7宣言と12モジュール252宣言の公理は標準3公理のみ。
未完了：semibasis の各商の次数付き分裂、既存 filtration との両向きの同値、cone 閉性。
D2h 全体の完成とは数えない。

### D2h 次数付き分裂の転送と座標射影（2026-10-17）

`Derived/RingGradedSplit.lean` と `Derived/BasisCut.lean` を追加した。
namespace `SerrePositivity.InfinityCategories`。`ringGradedNaturality` は
`(S : Type u) [CommRing S] {P Q : Complex S} (a : ∀ k : ℤ, P.X k ⟶ Q.X k)
(p i j : ℤ) (hij : i + p = j)
(f : GradedHom S (Opposite.op (PUnit.unit : PUnit.{1}))
  (Opposite.op (PUnit.unit : PUnit.{1})) p)` の下で
```lean
moduleActionComponent S PUnit.{1}
  (ForgetEnrichment.of (Complex S) (ringModule S P)) PUnit.unit PUnit.unit p i j hij f ≫ a j =
 a i ≫ moduleActionComponent S PUnit.{1}
  (ForgetEnrichment.of (Complex S) (ringModule S Q)) PUnit.unit PUnit.unit p i j hij f
```
を示す。a に chain map 条件はない。ほかの公開型：
```lean
ringComplexMap (S : Type u) [CommRing S] {P Q : Complex S} (f : P ⟶ Q) :
  ForgetEnrichment.of (Complex S) (ringModule S P) ⟶
    ForgetEnrichment.of (Complex S) (ringModule S Q)
ringComplexMap_evaluation (S : Type u) [CommRing S] {P Q : Complex S} (f : P ⟶ Q) :
  (moduleEvaluation S PUnit.{1} PUnit.unit).map (ringComplexMap S f) = f
ringComplexGradedSplit (S : Type u) [CommRing S] {P Q R : Complex S}
  (f : P ⟶ Q) (g : Q ⟶ R)
  (r : ∀ k : ℤ, Q.X k ⟶ P.X k) (s : ∀ k : ℤ, R.X k ⟶ Q.X k)
  (hfr : ∀ k, f.f k ≫ r k = 𝟙 _) (hsg : ∀ k, s k ≫ g.f k = 𝟙 _)
  (hsr : ∀ k, s k ≫ r k = 0) (hfg : f ≫ g = 0)
  (hdecomp : ∀ k, r k ≫ f.f k + g.f k ≫ s k = 𝟙 _) :
  ModuleGradedSplit S PUnit.{1} (ringComplexMap S f) (ringComplexMap S g)
```
座標射影の共通引数は `{S : Type u} [CommRing S] {V : Type v} [AddCommGroup V]
[Module S V] {I : Type v} (E : Module.Basis I S V)`。所属の判定は局所的な古典論理を使う。
```lean
basisCoordinateCut (s : Set I) : V →ₗ[S] V
basisCoordinateCut_repr (s : Set I) (x : V) (i : I) :
  E.repr (basisCoordinateCut E s x) i = if i ∈ s then E.repr x i else 0
basisCoordinateCut_mem (s : Set I) (x : V) :
  basisCoordinateCut E s x ∈ Submodule.span S (E '' s)
basisCoordinateCut_eq_self (s : Set I) {x : V}
  (hx : x ∈ Submodule.span S (E '' s)) : basisCoordinateCut E s x = x
basisCoordinateCut_disjoint (s t : Set I) (hst : Disjoint s t) (x : V) :
  basisCoordinateCut E s (basisCoordinateCut E t x) = 0
basisCoordinateCut_add (s t : Set I) (hst : Disjoint s t) {x : V}
  (hx : x ∈ Submodule.span S (E '' (s ∪ t))) :
  basisCoordinateCut E s x + basisCoordinateCut E t x = x
```
`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3627 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
新規公開10宣言と14モジュール284宣言の公理は標準3公理のみ。
未完了は各高さの自由商・既存 filtration との同値・cone 閉性。補助補題をそれらの完成とは数えない。

### D2h semibasis から既存 filtration の構成（2026-10-18）

semibasis から既存 `ModuleSemifreeFiltration` への構成と、既存の `complexSemifree` を満たすことを証明した。
これは同値の十分性側の完成であり、逆向きと cone 閉性は未完了。
namespace は `SerrePositivity.InfinityCategories.ComplexSemifreeBasis`。
以下の全宣言の共通引数は `{S : Type u} [CommRing S] {P : Complex S}
(B : ComplexSemifreeBasis S P)`。公開型をソースの宣言からそのまま記録する：

`Derived/SemifreeBasisLayers.lean`：
```lean
layerSubmodule (n : ℕ) (k : ℤ) : Submodule S (P.X k)
layerBasis (n : ℕ) (k : ℤ) :
    Module.Basis {i : B.Index k // B.height k i = n} S (B.layerSubmodule n k)
layerComplex (n : ℕ) : Complex S
layerSubmodule_le_stage (n : ℕ) (k : ℤ) :
    B.layerSubmodule n k ≤ B.stageSubmodule n k
lowRetraction (n : ℕ) (k : ℤ) :
    (B.stageComplex (n + 1)).X k ⟶ (B.stageComplex n).X k
highProjection (n : ℕ) (k : ℤ) :
    (B.stageComplex (n + 1)).X k ⟶ (B.layerComplex (n + 1)).X k
highSection (n : ℕ) (k : ℤ) :
    (B.layerComplex (n + 1)).X k ⟶ (B.stageComplex (n + 1)).X k
inclusion_lowRetraction (n : ℕ) (k : ℤ) :
    (B.stageMap (Nat.le_succ n)).f k ≫ B.lowRetraction n k = 𝟙 _
highSection_projection (n : ℕ) (k : ℤ) :
    B.highSection n k ≫ B.highProjection n k = 𝟙 _
highSection_lowRetraction (n : ℕ) (k : ℤ) :
    B.highSection n k ≫ B.lowRetraction n k = 0
inclusion_highProjection (n : ℕ) (k : ℤ) :
    (B.stageMap (Nat.le_succ n)).f k ≫ B.highProjection n k = 0
highProjection_differential (n : ℕ) (k : ℤ)
    (x : B.stageSubmodule (n + 1) k) :
    basisCoordinateCut (B.basis (k + 1)) {i | B.height (k + 1) i = n + 1}
      ((P.d k (k + 1)) x.val) = 0
layerQuotientMap (n : ℕ) : B.stageComplex (n + 1) ⟶ B.layerComplex (n + 1)
low_high_decomposition (n : ℕ) (k : ℤ) :
    B.lowRetraction n k ≫ (B.stageMap (Nat.le_succ n)).f k +
      B.highProjection n k ≫ B.highSection n k = 𝟙 _
layerSpherePresentation (n : ℕ) : ModuleSphereFreePresentation S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S (B.layerComplex n)))
initialSpherePresentation : ModuleSphereFreePresentation S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S (B.stageComplex 0)))
layerModuleGradedSplit (n : ℕ) : ModuleGradedSplit S PUnit.{1}
    (ringComplexMap S (B.stageMap (Nat.le_succ n)))
    (ringComplexMap S (B.layerQuotientMap n))
```

`Derived/SemifreeBasisFiltration.lean`：
```lean
moduleStage (n : ℕ) : ModuleCategory S PUnit.{1}
moduleTransition (n : ℕ) : B.moduleStage n ⟶ B.moduleStage (n + 1)
moduleSequenceEvaluationIso :
    Functor.ofSequence B.moduleTransition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit ≅
      B.stageDiagram
moduleStageCocone : Cocone (Functor.ofSequence B.moduleTransition)
moduleStageIsColimit : IsColimit B.moduleStageCocone
toModuleFiltration : ModuleSemifreeFiltration S PUnit.{1}
    (ForgetEnrichment.of (Complex S) (ringModule S P))
complexSemifree : SerrePositivity.InfinityCategories.complexSemifree S P
```

高さ = n の基底元の線形包を微分零の自由商とし、低い座標と高い座標への射影で分裂した。
初期段と各商の自由 sphere 表示を構成し、評価による余極限反映で一点加群上の網羅性を証明した。
`ComplexSemifreeBasis.toModuleFiltration` は既存の構造体そのものを返す。
公開定理 `ComplexSemifreeBasis.complexSemifree` の正確な型は
`{S : Type u} [CommRing S] {P : Complex S} (B : ComplexSemifreeBasis S P) :
SerrePositivity.InfinityCategories.complexSemifree S P`。既存定義に変更はない。

`set -o pipefail; lake build SerrePositivity.InfinityCategories.Derived` は終了コード 0（3700 jobs）。
`set -o pipefail; lake env lean scripts/audit_derived_infinity.lean` は終了コード 0。
16モジュール339宣言の公理は標準3公理のみ。新規公開宣言は 24 件。
未完了：既存 filtration から semibasis の構成と両向きの同値、cone の基底への高さの適用、無条件の cone 閉性。
D2i は D2h 後の任意工程として未着手。D1 の quasicategory は N2 完了記録待ち。


### D2h・分裂列の直和座標と自由 sphere の基底（2026-10-18）

既存 filtration から semibasis を得るための線形代数を保存。共通前提は
`{S : Type u} [CommRing S]`。`SplitModuleSequence S` は stage・quotient・包含・商射・
戻し・切断と五つの分裂等式を保持する。以下は namespace
`SerrePositivity.InfinityCategories`、列の宣言はその下の `SplitModuleSequence`。
列の共通変数は `(F : SplitModuleSequence S)`、cocone を使う宣言では
`(c : Cocone (Functor.ofSequence F.inclusion))`。sphere の宣言は `(S : Type u) [CommRing S]`。
公開型（構造体のフィールドも列挙）：

```lean
SplitModuleSequence (S : Type u) [CommRing S]
piece : ℕ → ModuleCat.{u} S
  | 0 => F.stage 0
  | n + 1 => F.quotient n

/-- 概要：各有限段の直和座標。
方針：前段への戻しの座標と新しい商の座標を加える。
規約：値域は全成分の直和。使われ方：余極限への延長。 -/
def coordinates : ∀ n, F.stage n →ₗ[S] ⨁ i, F.piece i
  | 0 => DirectSum.lof S ℕ (fun i => F.piece i) 0
  | n + 1 => coordinates n ∘ₗ (F.retraction n).hom +
      DirectSum.lof S ℕ (fun i => F.piece i) (n + 1) ∘ₗ (F.projection n).hom

/-- 概要：直和座標は包含と整合する。
方針：包含の戻しは恒等、包含の商は零であることを使う。
規約：隣接段についての等式。使われ方：座標の cocone。 -/
theorem coordinates_inclusion (n : ℕ) :
    F.coordinates (n + 1) ∘ₗ (F.inclusion n).hom = F.coordinates n
coordinates_apply_eq_zero (n i : ℕ) (h : n < i) (x : F.stage n) :
    F.coordinates n x i = 0
coordinateCocone : Cocone (Functor.ofSequence F.inclusion)
pieceMap : ∀ n, F.piece n →ₗ[S] c.pt
  | 0 => (c.ι.app 0).hom
  | n + 1 => (c.ι.app (n + 1)).hom ∘ₗ (F.section_ n).hom

/-- 概要：直和から cocone 頂点への線形写像。
方針：各成分の写像を直和の普遍性で延長する。
規約：初期成分と商成分を同じ番号で扱う。使われ方：直和表示の逆向き。 -/
def assemble : (⨁ i, F.piece i) →ₗ[S] c.pt
assemble_coordinates (n : ℕ) :
    F.assemble c ∘ₗ F.coordinates n = (c.ι.app n).hom
desc_pieceMap (hc : IsColimit c) (n : ℕ) :
    (hc.desc F.coordinateCocone).hom ∘ₗ F.pieceMap c n =
      DirectSum.lof S ℕ (fun i => F.piece i) n
linearEquiv (hc : IsColimit c) : c.pt ≃ₗ[S] ⨁ i, F.piece i
linearEquiv_leg (hc : IsColimit c) (n : ℕ) (x : F.stage n) :
    F.linearEquiv c hc ((c.ι.app n).hom x) = F.coordinates n x
linearEquiv_symm_lof (hc : IsColimit c) (n : ℕ) (x : F.piece n) :
    (F.linearEquiv c hc).symm (DirectSum.lof S ℕ (fun i => F.piece i) n x) =
      F.pieceMap c n x
  stage : ℕ → ModuleCat.{u} S
  quotient : ℕ → ModuleCat.{u} S
  inclusion : ∀ n, stage n ⟶ stage (n + 1)
  projection : ∀ n, stage (n + 1) ⟶ quotient n
  retraction : ∀ n, stage (n + 1) ⟶ stage n
  section_ : ∀ n, quotient n ⟶ stage (n + 1)
  inclusion_retraction : ∀ n, inclusion n ≫ retraction n = 𝟙 _
  section_projection : ∀ n, section_ n ≫ projection n = 𝟙 _
  section_retraction : ∀ n, section_ n ≫ retraction n = 0
  inclusion_projection : ∀ n, inclusion n ≫ projection n = 0
  decomposition : ∀ n,
    retraction n ≫ inclusion n + projection n ≫ section_ n = 𝟙 _

sphere_degree_free (n k : ℤ) : Module.Free S ((complexSphere S n).X k)
sphereCoproduct_degree_free {I : Type u} (d : I → ℤ) (k : ℤ) :
    Module.Free S ((∐ (fun i => complexSphere S (d i))).X k)
sphereCoproduct_d {I : Type u} (d : I → ℤ) (k : ℤ) :
    (∐ (fun i => complexSphere S (d i))).d k (k + 1) = 0
spherePresentation_degree_free {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) (k : ℤ) :
    Module.Free S (((ringModuleEquivalence S).functor.obj M).X k)
spherePresentation_d {M : ModuleCategory S PUnit.{1}}
    (E : ModuleSphereFreePresentation S PUnit.{1} M) (k : ℤ) :
    ((ringModuleEquivalence S).functor.obj M).d k (k + 1) = 0
```

`SplitModuleSequence.linearEquiv` は実際の線形同型であり、余極限や分裂を
未証明の仮定として追加していない（任意の与えられた分裂列とその余極限に適用する）。
`linearEquiv_leg`・`linearEquiv_symm_lof` が脚と基底成分の像を指定し、
`coordinates_apply_eq_zero` が段番号を超える座標の消滅を与える。
自由 sphere 表示について、各次数の `Module.Free` と微分零を証明。
集約 `lake build SerrePositivity.InfinityCategories.Derived` は終了コード0（3709 jobs）。
公理監査は終了コード0、18モジュール398宣言すべて標準3公理のみ。
未完了：filtration の座標への接続、semibasis の必要性・同値、任意の射の cone 閉性。
これらを完成扱いにせず、続行する。


### D2h・既存 filtration と semibasis の両向き同値（2026-10-18）

完了。namespace `SerrePositivity.InfinityCategories`。共通前提は
`{S : Type u} [CommRing S]`。`SemifreeFiltration` 名前空間の宣言では
`{M : ModuleCategory S PUnit.{1}} (F : ModuleSemifreeFiltration S PUnit.{1} M)`。
公開型は以下（各宣言に共通変数を補う）：

```lean
splitSequence (k : ℤ) : SplitModuleSequence S
degreeCocone (k : ℤ) : Cocone (Functor.ofSequence ((splitSequence F) k).inclusion)
degreeDiagramIso (k : ℤ) :
    Functor.ofSequence F.transition ⋙ moduleEvaluation S PUnit.{1} PUnit.unit ⋙
      HomologicalComplex.eval (ModuleCat S) (.up ℤ) k ≅
      Functor.ofSequence ((splitSequence F) k).inclusion
degreeIsColimit (k : ℤ) : IsColimit ((degreeCocone F) k)
degreeLinearEquiv (k : ℤ) :
    ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).X k ≃ₗ[S]
      ⨁ n, ((splitSequence F) k).piece n
piece_free (k : ℤ) (n : ℕ) : Module.Free S (((splitSequence F) k).piece n)
stageLeg (n : ℕ) : complexSemifreeStage S F n ⟶
    (moduleEvaluation S PUnit.{1} PUnit.unit).obj M
degreeLinearEquiv_stageLeg (k : ℤ) (n : ℕ)
    (x : (complexSemifreeStage S F n).X k) :
    degreeLinearEquiv F k (((stageLeg F n).f k).hom x) =
      (splitSequence F k).coordinates n x
degreeLinearEquiv_symm_lof (k : ℤ) (n : ℕ)
    (x : (splitSequence F k).piece n) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) n x) =
    (((moduleEvaluation S PUnit.{1} PUnit.unit).map F.iso.hom).f k).hom
      ((splitSequence F k).pieceMap (degreeCocone F k) n x)
pieceBasis (k : ℤ) (n : ℕ) :
    Module.Basis (letI
basis (k : ℤ)
basis_repr (k : ℤ)
    (x : ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).X k)
    (a : Σ n, letI
basis_apply (k : ℤ)
    (a : Σ n, letI
degreeLinearEquiv_symm_lof_zero (k : ℤ)
    (x : (complexSemifreeStage S F 0).X k) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) 0 x) =
      ((stageLeg F 0).f k).hom x
degreeLinearEquiv_symm_lof_succ (k : ℤ) (n : ℕ)
    (x : (complexSemifreeQuotient S F n).X k) :
    (degreeLinearEquiv F k).symm
      (DirectSum.lof S ℕ (fun n => (splitSequence F k).piece n) (n + 1) x) =
      ((stageLeg F (n + 1)).f k).hom (((F.split n).section_ PUnit.unit k).hom x)
stageLeg_zero_d (k : ℤ) (x : (complexSemifreeStage S F 0).X k) :
    ((((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)).hom)
      (((stageLeg F 0).f k).hom x) = 0
section_d_coordinates (k : ℤ) (n j : ℕ) (hj : n < j)
    (x : (complexSemifreeQuotient S F n).X k) :
    degreeLinearEquiv F (k + 1)
      ((((moduleEvaluation S PUnit.{1} PUnit.unit).obj M).d k (k + 1)).hom
        (((stageLeg F (n + 1)).f k).hom
          (((F.split n).section_ PUnit.unit k).hom x))) j = 0
toBasis (F : ModuleSemifreeFiltration S PUnit.{1} M) :
    ComplexSemifreeBasis S ((moduleEvaluation S PUnit.{1} PUnit.unit).obj M)
complexSemifree_nonempty_basis {P : Complex S} (hP : complexSemifree S P) :
    Nonempty (ComplexSemifreeBasis S P)
complexSemifree_iff_nonempty_basis (P : Complex S) :
    complexSemifree S P ↔ Nonempty (ComplexSemifreeBasis S P)
```

主定理の完全な型：
```lean
complexSemifree_iff_nonempty_basis {S : Type u} [CommRing S] (P : Complex S) :
  complexSemifree S P ↔ Nonempty (ComplexSemifreeBasis S P)
```
有界性、有限生成性、射による filtration 保存は仮定しない。
初期段および商の基底に段番号を与え、商の微分零から厳密な高さ下降を証明した。
`complexSemifree` の定義は変更していない。
対象集約ビルドは終了コード0（3771 jobs）、公理監査は終了コード0。
20モジュール442宣言は標準3公理のみ。
未完了：cone の実際の基底への高さの適用と任意の射の無条件 cone 閉性。
D2h 全体の完了とは数えず、そのまま続行する。


### D2h 完了・任意の射の cone 閉性（2026-10-18）

完了。共通変数は `{S : Type u} [CommRing S] {P Q : Complex S} (f : P ⟶ Q)`、
基底の名前空間 `ComplexSemifreeBasis` では
`(B : ComplexSemifreeBasis S P) (C : ComplexSemifreeBasis S Q)` を補う。
公開型（namespace `SerrePositivity.InfinityCategories`）：

```lean
coneDegreeEquiv (k : ℤ) : (mappingCone f).X k ≃ₗ[S] (P.X (k + 1) × Q.X k)
coneDegreeEquiv_fst (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f k x).1 = ((mappingCone.fst f).val.v k (k + 1) rfl).hom x
coneDegreeEquiv_snd (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f k x).2 = ((mappingCone.snd f).v k k (add_zero k)).hom x
coneDegreeEquiv_d_fst (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f (k + 1) (((mappingCone f).d k (k + 1)).hom x)).1 =
      -((P.d (k + 1) (k + 1 + 1)).hom (coneDegreeEquiv f k x).1)
coneDegreeEquiv_d_snd (k : ℤ) (x : (mappingCone f).X k) :
    (coneDegreeEquiv f (k + 1) (((mappingCone f).d k (k + 1)).hom x)).2 =
      (f.f (k + 1)).hom (coneDegreeEquiv f k x).1 +
        (Q.d k (k + 1)).hom (coneDegreeEquiv f k x).2
coneBasis (k : ℤ) : Module.Basis (B.Index (k + 1) ⊕ C.Index k) S ((mappingCone f).X k)
coneBasis_repr_inl (k : ℤ) (x : (mappingCone f).X k) (i : B.Index (k + 1)) :
    (B.coneBasis f C k).repr x (Sum.inl i) =
      (B.basis (k + 1)).repr (coneDegreeEquiv f k x).1 i
coneBasis_repr_inr (k : ℤ) (x : (mappingCone f).X k) (i : C.Index k) :
    (B.coneBasis f C k).repr x (Sum.inr i) =
      (C.basis k).repr (coneDegreeEquiv f k x).2 i
coneBasis_coordinates (k : ℤ) (a : B.Index (k + 1) ⊕ C.Index k) :
    coneDegreeEquiv f k (B.coneBasis f C k a) =
      (B.basis (k + 1)).prod (C.basis k) a
coneBasis_d_inl_inl (k : ℤ) (i : B.Index (k + 1))
    (j : B.Index (k + 1 + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inl i))) (Sum.inl j) =
      -((B.basis (k + 1 + 1)).repr
        ((P.d (k + 1) (k + 1 + 1)).hom (B.basis (k + 1) i)) j)
coneBasis_d_inl_inr (k : ℤ) (i : B.Index (k + 1)) (j : C.Index (k + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inl i))) (Sum.inr j) =
      (C.basis (k + 1)).repr ((f.f (k + 1)).hom (B.basis (k + 1) i)) j
coneBasis_d_inr_inl (k : ℤ) (i : C.Index k) (j : B.Index (k + 1 + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inr i))) (Sum.inl j) = 0
coneBasis_d_inr_inr (k : ℤ) (i : C.Index k) (j : C.Index (k + 1)) :
    (B.coneBasis f C (k + 1)).repr
      (((mappingCone f).d k (k + 1)).hom (B.coneBasis f C k (Sum.inr i))) (Sum.inr j) =
      (C.basis (k + 1)).repr ((Q.d k (k + 1)).hom (C.basis k i)) j
cone : ComplexSemifreeBasis S (mappingCone f)
complexSemifree_mappingCone (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
    complexSemifree S (mappingCone f)
```

主定理の完全な型：
```lean
complexSemifree_mappingCone {S : Type u} [CommRing S] {P Q : Complex S}
  (f : P ⟶ Q) (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
  complexSemifree S (CochainComplex.mappingCone f)
```
射が filtration を保存すること、有界性、有限生成性、環の追加性質を仮定しない。
cone の基底は次数 k に始域次数 k+1 と終域次数 k の直積基底を使い、
始域側には `coneSourceHeight`（`semifreeReheight` による整礎再帰）を実際に適用した。
四つの微分座標公式から厳密下降を証明し、既存 filtration へ戻した。
対象集約ビルドは終了コード0（3772 jobs）。公理監査は終了コード0、
21モジュール469宣言すべて標準3公理のみ。
D2h（零・sphere・シフト・任意余積・有限余積・任意の射の cone）は全て完了。
続行範囲：追加指示 D2h′（fiber と有限直和）、D1 の quasicategory、D3 の比較とシフト両立。
D2i はその後に任意工程として見積もりを報告する。


### D2h′ 完了・fiber と有限直和（2026-10-18）

共通変数 `(S : Type u) [CommRing S]`、namespace `SerrePositivity.InfinityCategories`。
公開宣言の型：
```lean
complexSemifree_binaryCoproduct {P Q : Complex S}
    (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
    complexSemifree S (P ⨿ Q)
complexSemifree_binaryBiproduct {P Q : Complex S}
    (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
    complexSemifree S (P ⊞ Q)
complexSemifree_finiteBiproduct {I : Type v} [Finite I] [Small.{u} I]
    (P : I → Complex S) (hP : ∀ i, complexSemifree S (P i)) :
    complexSemifree S (⨁ P)
complexSemifree_fiber {P Q : Complex S} (f : P ⟶ Q)
    (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
    complexSemifree S ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧)
complexSemifree_biprodFiber {B C D : Complex S} (f : B ⊞ C ⟶ D)
    (hB : complexSemifree S B) (hC : complexSemifree S C) (hD : complexSemifree S D) :
    complexSemifree S ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧)
```
fiber は指定通り `mappingCone f` の −1 シフトであり、射に追加仮定を置かない。
有限直和は `Type v` の任意の有限かつ u-small な添字集合。
既存の `CochainBiproduct` の有限 biproduct instance を利用し、cone・シフト・余積の閉性から証明。
対象集約ビルドは終了コード0（3936 jobs）、公理監査も終了コード0。
21モジュール474宣言すべて標準3公理のみ。D2h′ に残りなし。
未完了：D1 の quasicategory instance、D3 の同値とシフト両立。D2i の見積もりはその後。


### D1 完了・導来単体的集合の quasicategory 性（2026-10-18）

`dg-nerve.md` §5 の「N2e・N2 完了（2026-10-17）」を確認して着手。
namespace `SerrePositivity.InfinityCategories`、公開 instance の正確な型：
```lean
derivedInfinityCategoryQuasicategory (S : Type u) [CommRing S] :
  SSet.Quasicategory (derivedInfinityCategory S)
```
N2 の `dgNerve.instQuasicategory` を `Semifree S` に具体化した。
内部ホーンの方程式・有界性・有限性・環の追加性質を仮定しない。
既存の零・一・二単体同値と合わせて D1 は完了。
集約ビルドは終了コード0（3936 jobs）、公理監査は終了コード0、
21モジュール475宣言すべて標準3公理のみ。
任意の可換環と整数環で instance の自動合成も型検査した。
未完了：D3 の同値とシフト両立の保存、その後 D2i の見積もり。


### D3 完了・導来 ∞ 圏のホモトピー圏とシフト比較（2026-10-18）

N3 の無条件の `DGNerve.HomotopyComparison.equivalence` を具体化し、
D2 の `semifreeDerivedEquivalence` と合成した。namespace は
`SerrePositivity.InfinityCategories`、共通前提は `(S : Type u) [CommRing S]`。
最後の三宣言では `[HasDerivedCategory.{w} (ModuleCat.{u} S)]` を加える。
公開型：
```lean
derivedInfinityHomotopyCategory
derivedInfinityH0Equivalence : derivedInfinityHomotopyCategory S ≌
    DifferentialGraded.HomotopyCategory S (Semifree S)
derivedInfinityHomotopyShift (s : ℤ) :
    derivedInfinityHomotopyCategory S ⥤ derivedInfinityHomotopyCategory S
derivedInfinityHomotopyShiftIso (s : ℤ) :
    derivedInfinityHomotopyShift S s ⋙ (derivedInfinityH0Equivalence S).functor ≅
      (derivedInfinityH0Equivalence S).functor ⋙ shiftFunctor _ s
derivedInfinityHomotopyHasShift : HasShift (derivedInfinityHomotopyCategory S) ℤ
derivedInfinityH0EquivalenceCommShift :
    (derivedInfinityH0Equivalence S).functor.CommShift ℤ
derivedInfinityHomotopyEquivalence :
    derivedInfinityHomotopyCategory S ≌ DerivedCategory (ModuleCat.{u} S)
derivedInfinityHomotopyEquivalenceCommShift :
    (derivedInfinityHomotopyEquivalence S).functor.CommShift ℤ
derivedInfinityHomotopyEquivalenceShiftIso (s : ℤ) :
    shiftFunctor (derivedInfinityHomotopyCategory S) s ⋙
      (derivedInfinityHomotopyEquivalence S).functor ≅
        (derivedInfinityHomotopyEquivalence S).functor ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} S)) s
```
主定理の完全な型（始域の略記も展開）：
```lean
derivedInfinityHomotopyEquivalence (S : Type u) [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
  SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (derivedInfinityCategory S)) ≌
    DerivedCategory (ModuleCat.{u} S)
derivedInfinityHomotopyEquivalenceCommShift (S : Type u) [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
  (derivedInfinityHomotopyEquivalence S).functor.CommShift ℤ
```
ホモトピー圏の整数シフトは N3 の同値を通して D2f のシフトを移したもの。
充満忠実関手から `HasShift` の零・加法の coherence を誘導し、比較関手の CommShift と
D2f の CommShift を合成した。単なる各シフトでの同型にとどまらない。
`HasDerivedCategory` は圏の選択だけであり、新たな数学的仮定ではない。
標準 instance で任意の可換環と整数環の同値、シフト両立を具体化して検査。
集約ビルドは終了コード0（3937 jobs）、公理監査は終了コード0、
22モジュール487宣言すべて標準3公理のみ。D3 に残りなし。
D2h・D2h′・D1・D3 は全て完了。D4・N7 の制限そのものは今回の追加指示には含まれない。
D2i は未実装の任意工程。見積もり：3〜5保存単位（目安400〜800行、既存 API との接続で増減）。
テンソル積では次数 p+q=k の直和と基底のテンソル積、微分の Leibniz 符号を接続し、
高さを両因子の高さの和にする。底変更では各次数の基底の底変更と微分の高さ下降を接続する。
既存の semifree 閉性定理は見つからず、今回の同値を利用した新しい構成が必要。
着手するかはユーザー判断を仰ぐ。


### D2i・任意の環準同型による底変更（2026-10-18）

ユーザーが D3 後に D2i の続行を承認。底変更の保存を証明した。
共通変数は `{S T : Type u} [CommRing S] [CommRing T]`、namespace
`SerrePositivity.InfinityCategories`。基底の宣言は下位名前空間 `ComplexSemifreeBasis`、
`{P : Complex S} (B : ComplexSemifreeBasis S P) (f : S →+* T)` を補う。
公開型：
```lean
complexBaseChange (f : S →+* T) : Complex S ⥤ Complex T
baseChangeBasis (k : ℤ) : Module.Basis (B.Index k) T
    (((complexBaseChange f).obj P).X k)
baseChangeBasis_d_repr (k : ℤ) (i : B.Index k) (j : B.Index (k + 1)) :
    (B.baseChangeBasis f (k + 1)).repr
      ((((complexBaseChange f).obj P).d k (k + 1)).hom (B.baseChangeBasis f k i)) j =
      f ((B.basis (k + 1)).repr ((P.d k (k + 1)).hom (B.basis k i)) j)
baseChange : ComplexSemifreeBasis T ((complexBaseChange f).obj P)
complexSemifree_baseChange (f : S →+* T) {P : Complex S}
    (hP : complexSemifree S P) : complexSemifree T ((complexBaseChange f).obj P)
```
`complexBaseChange` は Mathlib の `ModuleCat.extendScalars f` を
`mapHomologicalComplex (.up ℤ)` で複体にした既存の関手である。
基底と高さを保持し、微分座標が環準同型による元の座標の像となることから証明。
平坦性・単射性などは不要。環と加群の宇宙は従来の規約通り同じ u。
対象集約ビルドは終了コード0（3945 jobs）、公理監査も終了コード0。
23モジュール497宣言すべて標準3公理のみ。
D2i の残り：二つの semifree 複体のテンソル積の無条件の閉性。直ちに続行する。


### D2i 完了・semifree テンソル積（2026-10-18）

namespace `SerrePositivity.InfinityCategories`、共通変数 `{S : Type u} [CommRing S]`。
`tensorDegreeEquiv`・成分の微分では `(P Q : Complex S)` を補う。
下位名前空間 `ComplexSemifreeBasis` では `{P Q : Complex S}`、
`(B : ComplexSemifreeBasis S P) (C : ComplexSemifreeBasis S Q)` を補う。
汎用の直和基底補題の変数は宣言内に全て明記。公開型：
```lean
directSumBasis_apply {R : Type u} [CommRing R] {I : Type v} [DecidableEq I]
    {V : I → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {J : I → Type w} (E : ∀ i, Module.Basis (J i) R (V i)) (a : Σ i, J i) :
    DFinsupp.basis E a = DFinsupp.single a.1 (E a.1 a.2)
TensorDegreeIndex (k : ℤ)
tensorDegreeEquiv (k : ℤ) : (P ⊗ Q).X k ≃ₗ[S]
    ⨁ a : TensorDegreeIndex k, (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S)
tensorDegreeEquiv_symm_lof (k : ℤ) (a : TensorDegreeIndex k)
    (x : (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S)) :
    (tensorDegreeEquiv P Q k).symm
      (DirectSum.lof S (TensorDegreeIndex k)
        (fun a => (P.X a.1.1 ⊗ Q.X a.1.2 : ModuleCat S)) a x) =
      (ιTensorObj P Q a.1.1 a.1.2 k a.2).hom x
TensorIndex (k : ℤ)
tensorBasis (k : ℤ) : Module.Basis (B.TensorIndex C k) S ((P ⊗ Q).X k)
tensorBasis_apply (k : ℤ) (a : B.TensorIndex C k) :
    B.tensorBasis C k a =
      (ιTensorObj P Q a.1.1.1 a.1.1.2 k a.1.2).hom
        (B.basis a.1.1.1 a.2.1 ⊗ₜ[S] C.basis a.1.1.2 a.2.2)
tensorHeight (k : ℤ) (a : B.TensorIndex C k) : ℕ
tensorLowerSpan (k : ℤ) (n : ℕ) : Submodule S ((P ⊗ Q).X k)
tensor_mem_lowerSpan_left (p q k : ℤ) (h : p + q = k) (n : ℕ)
    (j : C.Index q) (x : P.X p)
    (hx : x ∈ Submodule.span S (B.basis p '' {i | B.height p i < n})) :
    (ιTensorObj P Q p q k h).hom (x ⊗ₜ[S] C.basis q j) ∈
      B.tensorLowerSpan C k (n + C.height q j)
tensor_mem_lowerSpan_right (p q k : ℤ) (h : p + q = k) (n : ℕ)
    (i : B.Index p) (y : Q.X q)
    (hy : y ∈ Submodule.span S (C.basis q '' {j | C.height q j < n})) :
    (ιTensorObj P Q p q k h).hom (B.basis p i ⊗ₜ[S] y) ∈
      B.tensorLowerSpan C k (B.height p i + n)
tensor_summand_d (p q k : ℤ) (h : p + q = k) :
    ιTensorObj P Q p q k h ≫ (P ⊗ Q).d k (k + 1) =
      ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
        ((P.d p (p + 1) ▷ Q.X q) ≫ ιTensorObj P Q (p + 1) q (k + 1) (by omega)) +
      ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) •
        ((P.X p ◁ Q.d q (q + 1)) ≫ ιTensorObj P Q p (q + 1) (k + 1) (by omega))
tensor_summand_d_apply (p q k : ℤ) (h : p + q = k) (x : P.X p) (y : Q.X q) :
    ((P ⊗ Q).d k (k + 1)).hom ((ιTensorObj P Q p q k h).hom (x ⊗ₜ[S] y)) =
      (ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) : ℤ) •
        (ιTensorObj P Q (p + 1) q (k + 1) (by omega)).hom
          ((P.d p (p + 1)).hom x ⊗ₜ[S] y) +
      (ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) : ℤ) •
        (ιTensorObj P Q p (q + 1) (k + 1) (by omega)).hom
          (x ⊗ₜ[S] (Q.d q (q + 1)).hom y)
tensorBasis_d_mem_lowerSpan (k : ℤ) (a : B.TensorIndex C k) :
    ((P ⊗ Q).d k (k + 1)).hom (B.tensorBasis C k a) ∈
      B.tensorLowerSpan C (k + 1) (B.tensorHeight C k a)
tensor : ComplexSemifreeBasis S (P ⊗ Q)
complexSemifree_tensor (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
    complexSemifree S (P ⊗ Q)
```
主定理の完全な型：
```lean
complexSemifree_tensor {S : Type u} [CommRing S] (P Q : Complex S)
    (hP : complexSemifree S P) (hQ : complexSemifree S Q) :
  complexSemifree S (P ⊗ Q)
```
テンソル積は既存の Mathlib の monoidal tensor（各次数に直和 totalization を使用）。
基底は p+q=k ごとの左右の基底のテンソル積、自然数の高さは左右の高さの和。
標準 total 微分の符号付き二項をそれぞれ低い基底の線形包へ入れ、
基底表現の台が厳密に高さを下げることを証明した。
有界性・有限性・平坦性・環の追加性質の仮定なし。
対象集約ビルドは終了コード0（3954 jobs）。公理監査も終了コード0、
25モジュール543宣言すべて `propext`・`Classical.choice`・`Quot.sound` のみ。
`git diff --check` は今回の実装・集約・監査ファイルについて成功。
D2i（テンソル積および任意の環準同型による底変更の保存）は完了。
今回の指示 D2h・D2h′・D1・D3・承認後の D2i に未完了項目はない。
D4、N7 の ∞ 極限定理を Semifree に制限する実装そのもの、
テンソルの対称モノイダル ∞ 圏への昇格は別途の工程であり、今回の完成とは混同しない。


### D5a

```lean
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
universe u v
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
closedNerveHom {x y : ClosedCategory A D} (f : x ⟶ y) (k : ℤ) :
    GradedHom A (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y) k
closedNerveHom_zero {x y : ClosedCategory A D} (f : x ⟶ y) :
    closedNerveHom f 0 = (closedHomEquiv A D x y f).val
closedNerveHom_of_ne {x y : ClosedCategory A D} (f : x ⟶ y)
    (k : ℤ) (hk : k ≠ 0) : closedNerveHom f k = 0
closedNerveHom_comp {x y z : ClosedCategory A D} (f : x ⟶ y) (g : y ⟶ z)
    (p q r : ℤ) (hp : p = 0) (hq : q = 0) (hr : r = 0) (h : p + q = r) :
    compose A (closedNerveHom g q) (closedNerveHom f p) h = closedNerveHom (f ≫ g) r
closedNerveData {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n) :
    SimplexData A D n
closedNerveData_term {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) :
    (closedNerveData F).term I a b k hI ha hb hk j hj haj hjb = 0
closedNerveSimplex {n : ℕ} (F : ComposableArrows (ClosedCategory A D) n) : Simplex A D n
closedNerveSimplex_pullback {m n : ℕ}
    (F : ComposableArrows (ClosedCategory A D) n) (α : Fin (m + 1) →o Fin (n + 1)) :
    closedNerveSimplex (α.monotone.functor ⋙ F) = (closedNerveSimplex F).pullback α
variable (A D)
closedNerveInclusion : nerve (ClosedCategory A D) ⟶ dgNerve A D
closedNerveInclusion_vertex (F : (nerve (ClosedCategory A D)) _⦋0⦌) :
    dgNerve.vertexEquiv A D ((closedNerveInclusion A D).app _ F) =
      ForgetEnrichment.to (Complex A) (nerveEquiv F)
closedNerveInclusion_edge (F : (nerve (ClosedCategory A D)) _⦋1⦌) :
    dgNerve.edgeEquiv A D ((closedNerveInclusion A D).app _ F) =
      ⟨fun i => ForgetEnrichment.to (Complex A) (F.obj i),
        closedHomEquiv A D (F.obj 0) (F.obj 1) (F.map (homOfLE (by decide)))⟩
closedNerveInclusion_higher {n : ℕ}
    (F : (nerve (ClosedCategory A D)) _⦋n⦌) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hthree : 3 ≤ I.card) :
    (((closedNerveInclusion A D).app _ F) : Simplex A D n).hom I a b k hI ha hb hk = 0
end SerrePositivity.InfinityCategories
```


### D5b

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory Limits DifferentialGraded
variable {S : Type u} [CommRing S]
nonpositiveFreeBasis (P : Complex S) (hfree : ∀ k, Module.Free S (P.X k))
    (hzero : ∀ k : ℤ, 0 < k → IsZero (P.X k)) : ComplexSemifreeBasis S P
complexSemifree_of_nonpositive_free (P : Complex S)
    (hfree : ∀ k, Module.Free S (P.X k)) (hzero : ∀ k : ℤ, 0 < k → IsZero (P.X k)) :
    complexSemifree S P
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory Limits Abelian DifferentialGraded HomologicalComplex
variable (S : Type u) [CommRing S]
moduleFreeLeftResolution : LeftResolution (𝟭 (ModuleCat.{u} S))
moduleFreeLeftResolution_free (M : ModuleCat.{u} S) :
    Module.Free S ((moduleFreeLeftResolution S).F.obj M)
moduleFreeChainResolution : ModuleCat.{u} S ⥤ ChainComplex (ModuleCat.{u} S) ℕ
moduleFreeChainResolution_free (M : ModuleCat.{u} S) (n : ℕ) :
    Module.Free S (((moduleFreeChainResolution S).obj M).X n)
moduleFreeChainProjection (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).X 0 ⟶ M
moduleFreeChainProjection_d (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).d 1 0 ≫ moduleFreeChainProjection S M = 0
moduleFreeChainAugmentation (M : ModuleCat.{u} S) :
    (moduleFreeChainResolution S).obj M ⟶ (ChainComplex.single₀ (ModuleCat S)).obj M
moduleFreeChainProjection_exact (M : ModuleCat.{u} S) :
    (ShortComplex.mk _ _ (moduleFreeChainProjection_d S M)).Exact
moduleFreeChainProjection_epi (M : ModuleCat.{u} S) :
    Epi (moduleFreeChainProjection S M)
moduleFreeChainCokernel (M : ModuleCat.{u} S) :
    IsColimit (CokernelCofork.ofπ (moduleFreeChainProjection S M)
      (moduleFreeChainProjection_d S M))
moduleFreeChainOpcyclesIso (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).opcycles 0 ≅ M
moduleFreeChainOpcyclesIso_fac (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).pOpcycles 0 ≫ (moduleFreeChainOpcyclesIso S M).hom =
      moduleFreeChainProjection S M
moduleFreeChainAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso (moduleFreeChainAugmentation S M)
moduleFreeChainAugmentationNat :
    moduleFreeChainResolution S ⟶ ChainComplex.single₀ (ModuleCat S)
moduleFreeCochainResolution : ModuleCat.{u} S ⥤ Complex S
moduleFreeCochainResolution_free (M : ModuleCat.{u} S) (k : ℤ) :
    Module.Free S (((moduleFreeCochainResolution S).obj M).X k)
moduleFreeCochainResolution_isZero (M : ModuleCat.{u} S) (k : ℤ) (hk : 0 < k) :
    IsZero (((moduleFreeCochainResolution S).obj M).X k)
moduleFreeCochainResolution_semifree (M : ModuleCat.{u} S) :
    complexSemifree S ((moduleFreeCochainResolution S).obj M)
moduleSingleExtendIso :
    ChainComplex.single₀ (ModuleCat S) ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat S) ≅
      HomologicalComplex.single (ModuleCat S) (.up ℤ) 0
moduleFreeCochainAugmentationNat :
    moduleFreeCochainResolution S ⟶ HomologicalComplex.single (ModuleCat S) (.up ℤ) 0
moduleFreeCochainAugmentation (M : ModuleCat.{u} S) :
    (moduleFreeCochainResolution S).obj M ⟶
      (HomologicalComplex.single (ModuleCat S) (.up ℤ) 0).obj M
moduleFreeCochainAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso (moduleFreeCochainAugmentation S M)
moduleFreeCochainHomologyZeroIso (M : ModuleCat.{u} S) :
    ((moduleFreeCochainResolution S).obj M).homology 0 ≅ M
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory Limits DifferentialGraded
open scoped Simplicial
variable (S : Type u) [CommRing S]
semifreeClosedToComplex : ClosedCategory S (Semifree S) ⥤ Complex S
semifreeClosedToComplex_full : (semifreeClosedToComplex S).Full
semifreeClosedToComplex_faithful : (semifreeClosedToComplex S).Faithful
moduleSemifreeResolutionFunctor : ModuleCat.{u} S ⥤ ClosedCategory S (Semifree S)
moduleSemifreeResolutionComparison :
    moduleSemifreeResolutionFunctor S ⋙ semifreeClosedToComplex S ≅ moduleFreeCochainResolution S
moduleSemifreeResolutionAugmentation :
    moduleSemifreeResolutionFunctor S ⋙ semifreeClosedToComplex S ⟶
      HomologicalComplex.single (ModuleCat S) (.up ℤ) 0
moduleSemifreeResolutionAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso ((moduleSemifreeResolutionAugmentation S).app M)
discreteAlgebraModule : Under (CommRingCat.of S) ⥤ ModuleCat.{u} S
discreteEmbedding : nerve (Under (CommRingCat.of S)) ⟶ derivedInfinityCategory S
discreteEmbeddingHomologyZeroIso (B : Under (CommRingCat.of S)) :
    ((dgNerve.vertexEquiv S (Semifree S)
      ((discreteEmbedding S).app _ (ComposableArrows.mk₀ B))).val).homology 0 ≅
        (discreteAlgebraModule S).obj B
end SerrePositivity.InfinityCategories
```


### D5c

```lean
namespace SerrePositivity.InfinityCategories
universe u v
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve HomologicalComplex
open DifferentialGraded.ScalarExtension
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
DGRestrictScalars (D : Type v) [DGCategory T D] : Type v
variable {D : Type v} [DGCategory T D]
restrictScalars_compose {x y z : D} {p q n : ℤ}
    (g : GradedHom T y z q) (h : GradedHom T x y p) (hpq : p + q = n) :
    compose S (D := DGRestrictScalars f D) g h hpq = compose T g h hpq
restrictScalars_unit (x : DGRestrictScalars f D) :
    (unitElement S x).val = (unitElement T (D := D) x).val
restrictScalarsData {n : ℕ} (s : SimplexData T D n) :
    SimplexData S (DGRestrictScalars f D) n
restrictScalars_rhs {n : ℕ} (s : SimplexData T D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (restrictScalarsData f s).rhs I a b k hI ha hb hk = s.rhs I a b k hI ha hb hk
restrictScalarsSimplex {n : ℕ} (s : Simplex T D n) :
    Simplex S (DGRestrictScalars f D) n
unrestrictScalarsSimplex {n : ℕ} (s : Simplex S (DGRestrictScalars f D) n) :
    Simplex T D n
restrictScalarsSimplex_pullback {m n : ℕ} (s : Simplex T D n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    restrictScalarsSimplex f (s.pullback α) = (restrictScalarsSimplex f s).pullback α
dgNerveRestrictScalarsIso (D : Type v) [DGCategory T D] :
    dgNerve S (DGRestrictScalars f D) ≅ dgNerve T D
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u v w
open CategoryTheory MonoidalCategory DifferentialGraded
open DifferentialGraded.ScalarExtension
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
transposeBaseChangeDG {D : Type v} {E : Type w} [DGCategory S D] [DGCategory T E]
    (F : DGFunctor T (DGBaseChange f D) E) : DGFunctor S D (DGRestrictScalars f E)
complexBaseChangeDG : DGFunctor S (Complex S) (DGRestrictScalars f (Complex T))
semifreeBaseChangeDG : DGFunctor S (Semifree S) (DGRestrictScalars f (Semifree T))
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {S T : Type u} [CommRing S] [CommRing T]
derivedInfinityBaseChange (f : S →+* T) :
    derivedInfinityCategory S ⟶ derivedInfinityCategory T
derivedInfinityBaseChange_vertex (f : S →+* T)
    (x : (derivedInfinityCategory S) _⦋0⦌) :
    (derivedInfinityCategoryVertexEquiv T ((derivedInfinityBaseChange f).app _ x)).val =
      (complexBaseChange f).obj (derivedInfinityCategoryVertexEquiv S x).val
end SerrePositivity.InfinityCategories
```


### D5d

```lean
namespace SerrePositivity.InfinityCategories
universe u w
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
derivedInfinityHZeroFunctor : derivedInfinityHomotopyCategory S ⥤ ModuleCat.{u} S
derivedInfinityHZero (x : (derivedInfinityCategory S) _⦋0⦌) : ModuleCat.{u} S
derivedInfinityHZeroIso (x : (derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHZero S x ≅ (derivedInfinityCategoryVertexEquiv S x).val.homology 0
derivedInfinityHZeroMap {x y : (derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) x y) :
    derivedInfinityHZero S x ⟶ derivedInfinityHZero S y
derivedInfinityHZeroMap_homotopicL {x y : (derivedInfinityCategory S) _⦋0⦌}
    {e e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) x y}
    (h : SSet.Truncated.HomotopicL e e') :
    derivedInfinityHZeroMap S e = derivedInfinityHZeroMap S e'
derivedInfinityHZeroMap_homotopicR {x y : (derivedInfinityCategory S) _⦋0⦌}
    {e e' : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) x y}
    (h : SSet.Truncated.HomotopicR e e') :
    derivedInfinityHZeroMap S e = derivedInfinityHZeroMap S e'
derivedInfinityHZeroMap_id (x : (derivedInfinityCategory S) _⦋0⦌) :
    derivedInfinityHZeroMap S (SSet.Truncated.Edge.id x) = 𝟙 (derivedInfinityHZero S x)
derivedInfinityHZeroSimplexMap (e : (derivedInfinityCategory S) _⦋1⦌) :
    derivedInfinityHZero S ((derivedInfinityCategory S).δ 1 e) ⟶
      derivedInfinityHZero S ((derivedInfinityCategory S).δ 0 e)
derivedInfinityHZeroMap_comp {x y z : (derivedInfinityCategory S) _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) x y}
    {f : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) y z}
    {g : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory S)) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    derivedInfinityHZeroMap S e ≫ derivedInfinityHZeroMap S f = derivedInfinityHZeroMap S g
end SerrePositivity.InfinityCategories
```


### D4

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S]
derivedInfinityInclusion : derivedInfinityCategory S ⟶ dgNerve S (Complex S)
derivedSquarePresentation
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    ComplexCospanPresentation (pullbackCospan (F ≫ derivedInfinityInclusion))
derivedSquarePresentation_left
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSquarePresentation F).leftObj
derivedSquarePresentation_right
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSquarePresentation F).rightObj
derivedSquarePresentation_target
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    complexSemifree S (derivedSquarePresentation F).targetObj
derivedSquareStandardFiber
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) : Semifree S
derivedSquareFiberSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S
derivedSquareFiberSquare_isPullback
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPullbackSquare (derivedSquareFiberSquare F)
derivedSquareFiberSquare_cospan
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    pullbackCospan (derivedSquareFiberSquare F) = pullbackCospan F
derivedSquareFiberSquare_vertex
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    (pullbackCone (derivedSquareFiberSquare F)).vertex =
      Simplex.vertex (derivedSquareStandardFiber F)
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]
derivedSquareComparisonCone
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    JoinCone (pullbackCospan (derivedSquareFiberSquare F))
derivedSquareComparisonSliceEdge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      (sliceOver (pullbackCospan (derivedSquareFiberSquare F))))
        (derivedSquareComparisonCone F) (pullbackCone (derivedSquareFiberSquare F))
derivedSquareComparisonEdge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    SSet.Truncated.Edge (X := twoTruncation S (Semifree S))
      (pullbackCone F).vertex (Simplex.vertex (derivedSquareStandardFiber F))
derivedSquareComparisonEdge_isIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : IsPullbackSquare F) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (derivedSquareComparisonEdge F))
derivedSquareFiberComparison
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    ((pullbackCone F).vertex.obj 0).val ⟶ (derivedSquareStandardFiber F).val
derivedSquareFiberComparison_homotopyEquivalence
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : IsPullbackSquare F) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (derivedSquareFiberComparison F)
derivedSquareFiberComparison_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : IsPullbackSquare F) : QuasiIso (derivedSquareFiberComparison F)
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory SSet SimplicialObject.Truncated
open scoped Simplicial
derived_rightFibration_liftCompStruct {X Y : SSet.{u}} (q : X ⟶ Y) [RightFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌}
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ x₂)
    (h : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₂)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x₀) (q.app (Opposite.op ⦋0⦌) x₁))
    (t : SSet.Truncated.Edge.CompStruct f (g.map ((truncation 2).map q))
      (h.map ((truncation 2).map q))) :
    Nonempty (Σ f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ x₁,
      {t' : SSet.Truncated.Edge.CompStruct f' g h //
        q.app (Opposite.op ⦋2⦌) t'.simplex = t.simplex})
derived_rightFibration_reflects_invertibleEdge {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (q : X ⟶ Y) [RightFibration q] {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : IsInvertibleEdge (e.map ((truncation 2).map q))) : IsInvertibleEdge e
end SerrePositivity.InfinityCategories
```

```lean
namespace SerrePositivity.InfinityCategories
universe u
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open DGNerve.HomotopyComparison
open scoped Simplicial
variable {S : Type u} [CommRing S]
derived_edge_invertible_of_quasiIso {x y : (derivedInfinityCategory S) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Semifree S)) x y)
    (he : QuasiIso (edgeChainMap (e.map ((SSet.truncation 2).map derivedInfinityInclusion)))) :
    IsInvertibleEdge e
derived_isPullbackSquare_of_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : QuasiIso (derivedSquareFiberComparison F)) : IsPullbackSquare F
derived_isPullbackSquare_iff_quasiIso
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPullbackSquare F ↔ QuasiIso (derivedSquareFiberComparison F)
end SerrePositivity.InfinityCategories
```
