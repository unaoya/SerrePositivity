# SC-W1：2g-2残部から2hまでの補題単位の証明計画（11-17）

> 実装進捗（47e147525）：G4・G5の89署名中58署名を検証・監査済み。N01〜N06、D01〜D03、E01〜E15・E17、P01〜P19、C01〜C11、F01〜F03。実測21,207行、残部に係数2を掛けた完成見込み23,569〜26,009行（登録等の予備を含む）。一般のv被覆の降下は未完成。2g-2完成後はH01〜H04を別枠1,200行で進め、その後2iの段0の紙で停止する。以下の署名・元の見積表は保存する。





> 更新（11-17、28,000行の承認後）：下記は `3d89d7e5f` 作成時の紙と23,000行での判定を保存した記録。現在は指示書末尾の追記により外枠28,000行、105署名の範囲内は事前承認。補正後の上端27,935行は枠内で、main は `31b811097` で取り込み済み。対象ビルド後に再開する。型・仮定・範囲・見込みの表は変更しない。

## 判定と状態

ユーザーが11-17に2g-2の外枠を**23,000行**へ変更した。これは同じ型・範囲についての承認であり、「本紙を先に作り、係数2で補正した上端が枠内の場合だけLeanへ進む」という開始条件を伴う。

本紙は**紙だけ**である。新しいLeanファイル・宣言・テストは追加しておらず、Lean・lake・監査も実行していない。mainを取り込んでいない。数学の先端は6fd35a6d3、既存の実測は19,409行のまま。コード枠は提案する宣言の完全な署名で、証明・定義の実装本体は付けない（値を固定できる短い定義だけ本文を表示）。Leanのelaborationを確認したという主張ではない。未決の数学的主張を既存宣言として扱わない。

旧見込みの「相対fppfの代入」には、係数複体を持つ同じ二重nerveの構成、三重totalの括り方、切断に適合する被覆、非アフィンな各nerveのアフィン交叉での比較が含まれていなかった。本紙で全て名前と型を与え、**新しい照合は★**として計数した。法則の代入と判断した場合も、その理由を一行付けた。

一覧：済み1／全体3（うち追加0）。2hの主項目：済み1／全体4（うち追加0、既存χのH02）。以下のIDは主項目の新設ではなく、G4・G5・H01〜H04の内部の証明分割案である。

## 1. 共通の完全展開記法

名前空間はSerrePositivity.AlgebraicGeometry。以下のCoZ・BiZ・TriZ・TL・TR・AT・Cpx・PC・AN・tripleIotaLeft/Rightは**この紙だけの展開略記**であり、新しい未定義の数学の入力ではない。各署名の自由変数・宇宙はここで全て固定し、各宣言のその他の変数は各署名内に束縛する。省略記号で仮定や結論を伏せていない。宣言の末尾の `𝟙 _` の対象だけは式から一意に推論される。

```lean
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open _root_.AlgebraicGeometry TopologicalSpace Opposite
open scoped Simplicial
namespace SerrePositivity.AlgebraicGeometry
local notation "up" => ComplexShape.up ℕ

abbrev CoZ := CochainComplex (ModuleCat.{u} ℤ) ℕ
abbrev BiZ := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up
abbrev TriZ := HomologicalComplex₂ CoZ.{u} up up
abbrev TL (K : TriZ.{u}) : CoZ.{u} := (K.total up).total up
abbrev TR (K : TriZ.{u}) : CoZ.{u} :=
  ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K).total up
abbrev AT (E : CosimplicialObject.Augmented CoZ.{u}) : CoZ.{u} :=
  (SerrePositivity.Cech.augmentedCochain.obj E).total up

abbrev Cpx (X : Scheme.{u}) {ι : Type} [DecidableEq ι]
    (U : ι → X.Opens) (p : ℕ) (hp : p.Prime)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0) : CoZ.{u} :=
  fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) U)

abbrev PC {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) : Prop :=
  ((schemePerfectCechTupleDouble g U p hp hR).total up).Acyclic

abbrev AN {X S : Scheme.{u}} (f : X ⟶ S) :
    AugmentedSimplexCategoryᵒᵖ ⥤ Scheme.{u} :=
  AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk f).augmentedCechNerve

abbrev tripleIotaLeft (K : TriZ.{u}) (a b c n : ℕ) (hn : a+b+c=n) :
    ((K.X a).X b).X c ⟶ (TL K).X n :=
  (K.ιTotal up a b (a+b) (by rfl)).f c ≫
    (K.total up).ιTotal up (a+b) c n (by change (a+b)+c=n; exact hn)
abbrev tripleIotaRight (K : TriZ.{u}) (a b c n : ℕ) (hn : a+b+c=n) :
    ((K.X a).X b).X c ⟶ (TR K).X n :=
  (K.X a).ιTotal up b c (b+c) (by rfl) ≫
    ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K).ιTotal up a (b+c) n
      (by change a+(b+c)=n; omega)
```

ANのstarにおける対象・脚は既存の増大nerveの同値による元のSと照合する。P01・P06はこの同型の移送を含む。これを未証明の「定義的一致」で省略しない。新しい略記をLean本体へ追加する必要が生じた場合の行は、下の登録・整形枠に含める。

## 2. 原典との対応の読み方

[BS17（2017年版）](https://arxiv.org/pdf/1507.06490)、[Rydh（2010年版）](https://davidrydh.se/papers/submersion20100305.pdf)と番号を照合した。各IDの「原典」は上記のどの証明段を形式化するかを示し、コードの型そのものが原典にそのまま載るという意味ではない。「形式化のための補題」は原典に独立番号のない計算・自然性である。

本体は承認済みのČech経路を維持する。原典の層のHⁱとの比較をこの計画へ追加しない。[Stacks 01XD（30.2.6）](https://stacks.math.columbia.edu/tag/01XD)の比較はdocstringに明記するが形式化しない。中間の射影補題はČech版、最終出力は同じAugmentedRingCechExactである。

## 3. 補題単位の一覧（依存順）

行数は**素の見込みの下端〜上端／その両端の2倍**。各値にはその宣言のdocstringと証明を含める。型の違う既存宣言にそのまま代入できない場合は、理由に「新しい照合」と明記した。★は型・被覆・符号・選択したcolimitの脚で膨らむおそれがあるもの。

<a id="n01"></a>
### N01 — theorem fullCechComplexMap_isIso_of_nonempty_support

区分：G4。素：25〜45行、係数2：50〜90行。依存：なし（既存宣言から）。

```lean
theorem fullCechComplexMap_isIso_of_nonempty_support
    {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E)
    (hη : ∀ T : Finset ι, T.Nonempty → IsIso (η.app T)) :
    IsIso (fullCechComplexMap η)
```

原典：形式化のための補題。独立した原典番号なし。アフィン被覆のČechの各項の法則（比較自体は形式化しない[Stacks 01XD](https://stacks.math.columbia.edu/tag/01XD)のČech側）。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.fullCechCochainsMap` — [SerrePositivity/AlgebraicGeometry/ProjectiveCechFunctor.lean:33](../../SerrePositivity/AlgebraicGeometry/ProjectiveCechFunctor.lean)。
- `SerrePositivity.AlgebraicGeometry.fullCechComplexMap` — [SerrePositivity/AlgebraicGeometry/ProjectiveCechFunctor.lean:52](../../SerrePositivity/AlgebraicGeometry/ProjectiveCechFunctor.lean)。

判断：新しい完全性定理ではない。長さq+1のタプルのsupportが非空なので、既存の各項のPi写像を成分ごとの同型で判定する。

<a id="n02"></a>
### N02 ★ — theorem nilImmersion_app_universalHomeomorphism

区分：G4。素：30〜60行、係数2：60〜120行。依存：なし（既存宣言から）。

```lean
theorem nilImmersion_app_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism (f.app U).hom
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.affineNilImmersion_restrict_appTop_universalHomeomorphism` — [SerrePositivity/AlgebraicGeometry/AffineNilImmersionFrobeniusCoefficients.lean:36](../../SerrePositivity/AlgebraicGeometry/AffineNilImmersionFrobeniusCoefficients.lean)。
- `morphismRestrict_appTop` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:665](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean)。

判断：既存appTopの結論を、明示した制限の等式と環同型で元のapp Uへ運ぶ。appTopとapp Uを定義的同一視しない。

<a id="n03"></a>
### N03 — theorem nilImmersion_perfectCechPullback_isIso

区分：G4。素：35〜70行、係数2：70〜140行。依存：[N01](#n01), [N02](#n02)。

```lean
theorem nilImmersion_perfectCechPullback_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : ℕ) (hp : p.Prime)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    {ι : Type} [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (schemeStructurePerfectCechPullbackMap f p hp hY hX U)
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechPullbackMap` — [SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechPullback.lean:41](../../SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechPullback.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechPreimageComplexIso` — [SerrePositivity/AlgebraicGeometry/SchemeCechPreimage.lean:35](../../SerrePositivity/AlgebraicGeometry/SchemeCechPreimage.lean)。
- `SerrePositivity.AlgebraicGeometry.cechOpenIntersection_isAffineOpen` — [SerrePositivity/AlgebraicGeometry/SchemeCommonAffineCover.lean:49](../../SerrePositivity/AlgebraicGeometry/SchemeCommonAffineCover.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitUniversalHomeomorphism_bijective` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitInvariance.lean:44](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitInvariance.lean)。

判断：元の前層の射を各非空アフィン交叉で同型とし、既存の逆像被覆の同型と合成する。

<a id="n04"></a>
### N04 — theorem nilBaseChange_cechNerve_map

区分：G4。素：15〜30行、係数2：30〜60行。依存：なし（既存宣言から）。

```lean
theorem nilBaseChange_cechNerve_map
    {f g : Arrow Scheme.{u}} (F : f ⟶ g)
    (H : IsPullback F.left f.hom g.hom F.right)
    [IsClosedImmersion F.right] [Surjective F.right] (n : SimplexCategoryᵒᵖ) :
    IsClosedImmersion ((Arrow.mapCechNerve F).app n) ∧
      Surjective ((Arrow.mapCechNerve F).app n)
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_cechNerve_base` — [SerrePositivity/AlgebraicGeometry/CechNerveCartesianBaseChange.lean:20](../../SerrePositivity/AlgebraicGeometry/CechNerveCartesianBaseChange.lean)。
- `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:375](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean)。
- `CategoryTheory.MorphismProperty.of_isPullback` — [.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Limits.lean:108](../../.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Limits.lean)。

判断：既存のCartesianな各nerveの射へ、二つの性質の底変換安定性を代入する。最後の二つのinstance名は実装時にはMorphismProperty.of_isPullbackで参照する。

<a id="n05"></a>
### N05 ★ — theorem nilBaseChange_tupleAugmentedPullback_isIso

区分：G4。素：40〜80行、係数2：80〜160行。依存：[N03](#n03), [N04](#n04)。

```lean
theorem nilBaseChange_tupleAugmentedPullback_isIso
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated g] (F : Arrow.mk f ⟶ Arrow.mk g)
    (H : IsPullback F.left f g F.right)
    [IsClosedImmersion F.right] [Surjective F.right]
    (q : R →+* S) (hq : F.right = Spec.map (CommRingCat.ofHom q))
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (schemePerfectCechTupleAugmentedPullback f g F q hq U p hp hR hS)
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_mapCechNerve_preimage` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean:19](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean)。
- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleAugmentedPullback` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedPullback.lean:54](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedPullback.lean)。
- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleAugmentationHom_pullback` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedPullback.lean:27](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedPullback.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_isAffine` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean:62](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean)。

判断：正次数は同じ逆像タプル被覆の同型、増大項はqのcanonicalなFrobenius同型のsingle。既存の増大の可換性を使う。

<a id="n06"></a>
### N06 — theorem nilBaseChange_tupleTotal_acyclic_iff

区分：G4。素：10〜20行、係数2：20〜40行。依存：[N05](#n05)。

```lean
theorem nilBaseChange_tupleTotal_acyclic_iff
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated g] (F : Arrow.mk f ⟶ Arrow.mk g)
    (H : IsPullback F.left f g F.right)
    [IsClosedImmersion F.right] [Surjective F.right]
    (q : R →+* S) (hq : F.right = Spec.map (CommRingCat.ofHom q))
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    PC g U p hp hR ↔ PC f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDoublePullback` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleDouble.lean:59](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleDouble.lean)。
- `SerrePositivity.AlgebraicGeometry.cechIntegerLiftTotalFunctor` — [SerrePositivity/AlgebraicGeometry/CechIntegerLiftTotalFunctor.lean:19](../../SerrePositivity/AlgebraicGeometry/CechIntegerLiftTotalFunctor.lean)。

判断：同じ増大対象の同型を既存のaugmentedCochainとtotalで写すだけで、別のホモロジーを定義しない。

<a id="d01"></a>
### D01 — def PerfectCechUniversalDescent (p : ℕ) (hp : p.Prime)

区分：G4。素：8〜15行、係数2：16〜30行。依存：なし（既存宣言から）。

```lean
def PerfectCechUniversalDescent (p : ℕ) (hp : p.Prime)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : (p : R) = 0) (t : Spec (CommRingCat.of R) ⟶ Y)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (U : ι → (pullback f t).Opens),
    (∀ i, IsAffineOpen (U i)) → (⨆ i, U i) = ⊤ →
      PC (pullback.snd f t) U p hp hR
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleDouble.lean:23](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleDouble.lean)。

判断：新しい内部述語。元の射を先に固定して全てのNoetherアフィン底変換を量化する。最終の仮定には現れない。

<a id="d02"></a>
### D02 ★ — theorem perfectCechUniversalDescent_baseChange

区分：G4。素：35〜65行、係数2：70〜130行。依存：[D01](#d01)。

```lean
theorem perfectCechUniversalDescent_baseChange
    (p : ℕ) (hp : p.Prime) {X Y T : Scheme.{u}} (f : X ⟶ Y) (t : T ⟶ Y)
    (hf : PerfectCechUniversalDescent p hp f) :
    PerfectCechUniversalDescent p hp (pullback.snd f t)
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_cartesianBaseChangeComparison` — [SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean:38](../../SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_comp` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechPullbackComposition.lean:32](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechPullbackComposition.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_compIndex` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedComposition.lean:34](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedComposition.lean)。

判断：既存の反復pullbackの同型と同じ逆像被覆の合成則へ代入する。被覆の移送を明示する分を計上する。

<a id="d03"></a>
### D03 — theorem perfectCechUniversalDescent_flat_surjective

区分：G4。素：15〜30行、係数2：30〜60行。依存：[D01](#d01)。

```lean
theorem perfectCechUniversalDescent_flat_surjective
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsSeparated f] [QuasiCompact f]
    [LocallyOfFinitePresentation f] : PerfectCechUniversalDescent p hp f
```

原典：BS17 Thm 2.9(i)、Lemma 3.4(xii)。環の入力は[Stacks 023M](https://stacks.math.columbia.edu/tag/023M)。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_flat_surjective` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean:36](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean)。

判断：各Noetherアフィン底変換で既存のflat totalの定理を適用する。元の中間基底のΓの平坦性は使わない。

<a id="d04"></a>
### D04 — theorem perfectCechUniversalDescent_nilImmersion

区分：G4。素：35〜65行、係数2：70〜130行。依存：[N06](#n06), [D01](#d01)。

```lean
theorem perfectCechUniversalDescent_nilImmersion
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] [LocallyOfFinitePresentation f] :
    PerfectCechUniversalDescent p hp f
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_constant` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean:48](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean)。
- `SerrePositivity.AlgebraicGeometry.affineNilImmersion_frobeniusEquiv_toRingHom` — [SerrePositivity/AlgebraicGeometry/AffineNilImmersionFrobeniusCoefficients.lean:57](../../SerrePositivity/AlgebraicGeometry/AffineNilImmersionFrobeniusCoefficients.lean)。

判断：恒等射の同じČech列の完全性をnil底変換の同型へ渡す。恒等射の被覆比較は既存のアフィン出口を使う。

<a id="p01"></a>
### P01 — def augmentedNerveBase {X S : Scheme.{u}} (f : X ⟶ S)

区分：G4。素：8〜18行、係数2：16〜36行。依存：なし（既存宣言から）。

```lean
def augmentedNerveBase {X S : Scheme.{u}} (f : X ⟶ S)
    (a : AugmentedSimplexCategory) : (AN f).obj (op a) ⟶ S
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `AugmentedSimplexCategory.equivAugmentedSimplicialObject` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:95](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean)。
- `CategoryTheory.Arrow.augmentedCechNerve` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean:72](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean)。

判断：ANは共通略記に展開した既存の増大nerve。starへの脚を元の増大項の同型でSへ戻す。

<a id="p02"></a>
### P02 — def augmentedTupleLength (a : AugmentedSimplexCategory) : ℕ :=

区分：G4。素：4〜8行、係数2：8〜16行。依存：なし（既存宣言から）。

```lean
def augmentedTupleLength (a : AugmentedSimplexCategory) : ℕ :=
  match a with
  | .star => 0
  | .of n => n.len + 1
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `AugmentedSimplexCategory` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:33](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean)。

判断：形式化の添字の略記。新しい幾何はない。

<a id="p03"></a>
### P03 — def augmentedTupleIndexMap {a b : AugmentedSimplexCategory} (α : a ⟶ b) :

区分：G4。素：10〜20行、係数2：20〜40行。依存：[P02](#p02)。

```lean
def augmentedTupleIndexMap {a b : AugmentedSimplexCategory} (α : a ⟶ b) :
    Fin (augmentedTupleLength a) → Fin (augmentedTupleLength b)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `AugmentedSimplexCategory.equivAugmentedCosimplicialObject` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:52](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean)。

判断：starからは空関数、正次数は元のtoOrderHom。

<a id="p04"></a>
### P04 — theorem augmentedTupleIndexMap_id (a : AugmentedSimplexCategory) :

区分：G4。素：4〜8行、係数2：8〜16行。依存：[P03](#p03)。

```lean
theorem augmentedTupleIndexMap_id (a : AugmentedSimplexCategory) :
    augmentedTupleIndexMap (𝟙 a) = id
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SimplexCategory.toOrderHom` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:36](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean)。

判断：場合分け後は元の恒等順序写像。

<a id="p05"></a>
### P05 — theorem augmentedTupleIndexMap_comp {a b c : AugmentedSimplexCategory}

区分：G4。素：5〜10行、係数2：10〜20行。依存：[P03](#p03)。

```lean
theorem augmentedTupleIndexMap_comp {a b c : AugmentedSimplexCategory}
    (α : a ⟶ b) (β : b ⟶ c) :
    augmentedTupleIndexMap (α ≫ β) = augmentedTupleIndexMap β ∘ augmentedTupleIndexMap α
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SimplexCategory.toOrderHom` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:36](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean)。

判断：場合分け後は元の順序写像の合成。

<a id="p06"></a>
### P06 — def augmentedTupleOpen {X S : Scheme.{u}} (f : X ⟶ S)

区分：G4。素：10〜20行、係数2：20〜40行。依存：[P02](#p02)。

```lean
def augmentedTupleOpen {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type} (U : ι → X.Opens) (a : AugmentedSimplexCategory)
    (t : Fin (augmentedTupleLength a) → ι) : ((AN f).obj (op a)).Opens
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean:20](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean)。

判断：starはSの全開集合、正次数は元のschemeCechTupleOpen。starでの既存同値のobjectの同型を明示する。

<a id="p07"></a>
### P07 — def pairedCechScheme {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：4〜8行、係数2：8〜16行。依存：[P01](#p01)。

```lean
def pairedCechScheme {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a b : AugmentedSimplexCategory) : Scheme.{u} :=
  pullback (augmentedNerveBase h a) (augmentedNerveBase g b)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `CategoryTheory.Limits.pullback.hom_ext` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:222](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：元の二つのnerveの実際のS上のpullbackを取るだけ。

<a id="p08"></a>
### P08 — def pairedCechSchemeMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：15〜30行、係数2：30〜60行。依存：[P07](#p07)。

```lean
def pairedCechSchemeMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b') :
    pairedCechScheme h g a' b' ⟶ pairedCechScheme h g a b
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `CategoryTheory.Arrow.augmentedCechNerve` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean:72](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean)。
- `CategoryTheory.Limits.pullback.map` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:266](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：元のAN h・AN gの写像をpullback.mapへ代入し、増大の自然性で四角形を照合する。

<a id="p09"></a>
### P09 — theorem pairedCechSchemeMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：5〜10行、係数2：10〜20行。依存：[P08](#p08)。

```lean
theorem pairedCechSchemeMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a b : AugmentedSimplexCategory) : pairedCechSchemeMap h g (𝟙 a) (𝟙 b) = 𝟙 _
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `CategoryTheory.Limits.pullback.hom_ext` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:222](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：二つの射影で既存のmap_idを確認する。

<a id="p10"></a>
### P10 — theorem pairedCechSchemeMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：8〜15行、係数2：16〜30行。依存：[P08](#p08)。

```lean
theorem pairedCechSchemeMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {a a' a'' b b' b'' : AugmentedSimplexCategory}
    (α : a ⟶ a') (α' : a' ⟶ a'') (β : b ⟶ b') (β' : b' ⟶ b'') :
    pairedCechSchemeMap h g (α ≫ α') (β ≫ β') =
      pairedCechSchemeMap h g α' β' ≫ pairedCechSchemeMap h g α β
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `CategoryTheory.Limits.pullback.hom_ext` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:222](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：反変な二つの元のnerveのmap_compを二つの射影で確認する。

<a id="p11"></a>
### P11 — def pairedCechOpen {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：6〜12行、係数2：12〜24行。依存：[P06](#p06), [P07](#p07)。

```lean
def pairedCechOpen {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (a b : AugmentedSimplexCategory)
    (t : (Fin (augmentedTupleLength a) → ι) × (Fin (augmentedTupleLength b) → κ)) :
    (pairedCechScheme h g a b).Opens :=
  pullback.fst (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
      augmentedTupleOpen h U a t.1 ⊓
    pullback.snd (augmentedNerveBase h a) (augmentedNerveBase g b) ⁻¹ᵁ
      augmentedTupleOpen g V b t.2
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleIntersection_rectangular` — [SerrePositivity/AlgebraicGeometry/RectangularCechTupleIntersection.lean:35](../../SerrePositivity/AlgebraicGeometry/RectangularCechTupleIntersection.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_iSup` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean:25](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean)。

判断：二つの元のタプル開の逆像の交叉。新しい被覆の選び直しではない。

<a id="p12"></a>
### P12 ★ — theorem pairedCechOpen_map_le {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：20〜40行、係数2：40〜80行。依存：[P03](#p03), [P08](#p08), [P11](#p11)。

```lean
theorem pairedCechOpen_map_le {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b')
    (t : (Fin (augmentedTupleLength a') → ι) × (Fin (augmentedTupleLength b') → κ)) :
    pairedCechOpen h g U V a' b' t ≤ pairedCechSchemeMap h g α β ⁻¹ᵁ
      pairedCechOpen h g U V a b
        (t.1 ∘ augmentedTupleIndexMap α, t.2 ∘ augmentedTupleIndexMap β)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_map_le` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean:46](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_mapCechNerve_preimage` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean:19](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean)。

判断：元の各座標の逆像の包含を二つのpullbackの射影へ移す。増大と正次数の両方の照合を計上する。

<a id="p13"></a>
### P13 — theorem pairedCechPrimeCast {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：8〜15行、係数2：16〜30行。依存：[P07](#p07)。

```lean
theorem pairedCechPrimeCast {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (p : ℕ) (hR : (p : R) = 0) (a b : AugmentedSimplexCategory)
    (O : ((pairedCechScheme h g a b).Opens)ᵒᵖ) :
    (p : (pairedCechScheme h g a b).presheaf.obj O) = 0
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeScalarPresheaf_primeCast` — [SerrePositivity/AlgebraicGeometry/SchemeCechNerveScalars.lean:30](../../SerrePositivity/AlgebraicGeometry/SchemeCechNerveScalars.lean)。

判断：実際のpullbackからSpec Rへの脚に既存の標数の移送を適用する。

<a id="p14"></a>
### P14 — def pairedPerfectCechComplex {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：4〜8行、係数2：8〜16行。依存：[P11](#p11), [P13](#p13)。

```lean
def pairedPerfectCechComplex {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (a b : AugmentedSimplexCategory) : CoZ.{u} :=
  Cpx (pairedCechScheme h g a b) (pairedCechOpen h g U V a b) p hp
    (pairedCechPrimeCast h g p hR a b)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_apply` — [SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean:35](../../SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean)。

判断：Cpxは共通略記に完全展開した既存fullCechComplex。値を持つ元の係数複体を固定する。

<a id="p15"></a>
### P15 — def pairedPerfectCechMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：10〜20行、係数2：20〜40行。依存：[P12](#p12), [P14](#p14)。

```lean
def pairedPerfectCechMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b') :
    pairedPerfectCechComplex h g U V p hp hR a b ⟶
      pairedPerfectCechComplex h g U V p hp hR a' b'
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap` — [SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean:27](../../SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean)。

判断：同じpairedCechSchemeMapと二つのtuple index mapを既存のrefinedPullbackへ代入する。

<a id="p16"></a>
### P16 — theorem pairedPerfectCechMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：10〜20行、係数2：20〜40行。依存：[P04](#p04), [P09](#p09), [P15](#p15)。

```lean
theorem pairedPerfectCechMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (a b : AugmentedSimplexCategory) :
    pairedPerfectCechMap h g U V p hp hR (𝟙 a) (𝟙 b) = 𝟙 _
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_id` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedIdentity.lean:19](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedIdentity.lean)。

判断：既存の引き戻しの恒等則と、元のscheme map・添字写像の恒等則を代入する。

<a id="p17"></a>
### P17 — theorem pairedPerfectCechMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：15〜30行、係数2：30〜60行。依存：[P05](#p05), [P10](#p10), [P15](#p15)。

```lean
theorem pairedPerfectCechMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {a a' a'' b b' b'' : AugmentedSimplexCategory}
    (α : a ⟶ a') (α' : a' ⟶ a'') (β : b ⟶ b') (β' : b' ⟶ b'') :
    pairedPerfectCechMap h g U V p hp hR (α ≫ α') (β ≫ β') =
      pairedPerfectCechMap h g U V p hp hR α β ≫
        pairedPerfectCechMap h g U V p hp hR α' β'
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_compIndex` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedComposition.lean:34](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechRefinedComposition.lean)。

判断：既存のcompIndexで元の二つの係数の合成を一つにする。添字は反変なscheme mapと逆向きになる。

<a id="p18"></a>
### P18 — def pairedPerfectCech {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：8〜15行、係数2：16〜30行。依存：[P16](#p16), [P17](#p17)。

```lean
def pairedPerfectCech {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u}
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleFunctor` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFunctor.lean:72](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFunctor.lean)。

判断：obj=P14、map=P15、法則=P16・P17の既存のČech関手の二変数版。新しい整合性を省略しない。

<a id="p19"></a>
### P19 ★ — theorem pairedCechOpen_isAffineOpen_cover {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：30〜60行、係数2：60〜120行。依存：[P11](#p11)。

```lean
theorem pairedCechOpen_isAffineOpen_cover {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    [IsSeparated h] [IsSeparated g]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤)
    (a b : AugmentedSimplexCategory) :
    (∀ t, IsAffineOpen (pairedCechOpen h g U V a b t)) ∧
      (⨆ t, pairedCechOpen h g U V a b t) = ⊤
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_isAffine` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean:62](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_iSup` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean:25](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean)。
- `SerrePositivity.AlgebraicGeometry.isPullbackAffineOpen_inf` — [SerrePositivity/AlgebraicGeometry/SchemePullbackAffineTupleOpen.lean:37](../../SerrePositivity/AlgebraicGeometry/SchemePullbackAffineTupleOpen.lean)。

判断：正次数は既存のアフィンタプル開のS上の積、starはSpec R。全ての次数のcoverを同じ座標で照合する。

<a id="c01"></a>
### C01 ★ — def cechTripleTotalComponentIso (K : TriZ.{u}) (n : ℕ) :

区分：G4。素：60〜110行、係数2：120〜220行。依存：なし（既存宣言から）。

```lean
def cechTripleTotalComponentIso (K : TriZ.{u}) (n : ℕ) :
    (TL K).X n ≅ (TR K).X n
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean:569](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean)。
- `HomologicalComplex₂.totalDesc` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean:349](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean)。

判断：新しい照合。三つの非負次数の和がnの同じ有限直和を、選択した二つの括り方の直和へ比較する。単なるQuasiIsoの代入ではない。

<a id="c02"></a>
### C02 — theorem cechTripleTotalComponentIso_ι (K : TriZ.{u}) (a b c n : ℕ)

区分：G4。素：25〜50行、係数2：50〜100行。依存：[C01](#c01)。

```lean
theorem cechTripleTotalComponentIso_ι (K : TriZ.{u}) (a b c n : ℕ)
    (hn : a + b + c = n) :
    tripleIotaLeft K a b c n hn ≫ (cechTripleTotalComponentIso K n).hom =
      tripleIotaRight K a b c n hn
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `HomologicalComplex₂.ι_totalDesc` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean:354](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean)。

判断：共通略記の三重の元の脚ごとにFubiniの標準脚の式を確認する。

<a id="c03"></a>
### C03 ★ — theorem cechTripleTotalComponentIso_d (K : TriZ.{u}) (n : ℕ) :

区分：G4。素：50〜90行、係数2：100〜180行。依存：[C02](#c02)。

```lean
theorem cechTripleTotalComponentIso_d (K : TriZ.{u}) (n : ℕ) :
    (cechTripleTotalComponentIso K n).hom ≫ (TR K).d n (n+1) =
      (TL K).d n (n+1) ≫ (cechTripleTotalComponentIso K (n+1)).hom
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `HomologicalComplex₂.ι_D₁` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean:308](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean)。
- `HomologicalComplex₂.ι_D₂` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean:314](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean)。

判断：新しい微分の照合。両方の括り方で符号は1,(-1)^a,(-1)^(a+b)。既存の各脚の式を三方向へ代入する。

<a id="c04"></a>
### C04 — def cechTripleTotalAssociator (K : TriZ.{u}) : TL K ≅ TR K

区分：G4。素：8〜15行、係数2：16〜30行。依存：[C03](#c03)。

```lean
def cechTripleTotalAssociator (K : TriZ.{u}) : TL K ≅ TR K
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `HomologicalComplex.Hom.isoOfComponents` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/HomologicalComplex.lean:498](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/HomologicalComplex.lean)。

判断：同じ成分の同型とC03を既存のisoOfComponentsへ代入する。

<a id="c05"></a>
### C05 — theorem cechTripleTotalAssociator_naturality {K L : TriZ.{u}} (f : K ⟶ L) :

区分：G4。素：20〜40行、係数2：40〜80行。依存：[C04](#c04)。

```lean
theorem cechTripleTotalAssociator_naturality {K L : TriZ.{u}} (f : K ⟶ L) :
    HomologicalComplex₂.total.map (HomologicalComplex₂.total.map f up) up ≫
      (cechTripleTotalAssociator L).hom =
    (cechTripleTotalAssociator K).hom ≫ HomologicalComplex₂.total.map
      ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).map f) up
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `HomologicalComplex₂.ιTotal_map` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean:453](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplex.lean)。

判断：同じ元の各三重脚でmapと標準同型の自然性を照合する。

<a id="c06"></a>
### C06 — def complexValuedAugmentedDouble

区分：G4。素：12〜25行、係数2：24〜50行。依存：なし（既存宣言から）。

```lean
def complexValuedAugmentedDouble
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u}) : TriZ.{u}
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `CategoryTheory.Functor.curry` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Currying.lean:72](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Currying.lean)。
- `AugmentedSimplexCategory.equivAugmentedCosimplicialObject` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean:52](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Augmented/Basic.lean)。
- `SerrePositivity.Cech.augmentedCochain` — [SerrePositivity/HomologicalAlgebra/Cech/Basic.lean:62](../../SerrePositivity/HomologicalAlgebra/Cech/Basic.lean)。

判断：同じFをcurryし、内外に既存の増大cochainを一回ずつ適用する。B1の微分・対角線消去を再実装しない。

<a id="c07"></a>
### C07 ★ — def complexValuedAugmentedDouble_swapIso

区分：G4。素：35〜70行、係数2：70〜140行。依存：[C06](#c06)。

```lean
def complexValuedAugmentedDouble_swapIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u}) :
    TL (complexValuedAugmentedDouble F) ≅
      TL (complexValuedAugmentedDouble ((Prod.braiding _ _).functor ⋙ F))
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `HomologicalComplex₂.totalFlipIso` — [.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplexSymmetry.lean:113](../../.lake/packages/mathlib/Mathlib/Algebra/Homology/TotalComplexSymmetry.lean)。
- `SerrePositivity.Cech.row` — [SerrePositivity/HomologicalAlgebra/Cech/Double.lean:47](../../SerrePositivity/HomologicalAlgebra/Cech/Double.lean)。
- `SerrePositivity.Cech.col` — [SerrePositivity/HomologicalAlgebra/Cech/Double.lean:53](../../SerrePositivity/HomologicalAlgebra/Cech/Double.lean)。

判断：同じ増大二方向のtransposeと既存の(-1)^(a*b)のtotalFlipIsoを係数複体へ適用する。全てのstarと正次数の評価を含む。

<a id="c08"></a>
### C08 — def complexValuedAugmentedDouble_columnIso

区分：G4。素：15〜30行、係数2：30〜60行。依存：[C06](#c06)。

```lean
def complexValuedAugmentedDouble_columnIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u}) (i : ℕ) :
    ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj
      (complexValuedAugmentedDouble F)).X i ≅
        AT (SerrePositivity.Cech.col F i)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `SerrePositivity.Cech.mapAugmentedCochainIso` — [SerrePositivity/HomologicalAlgebra/Cech/Basic.lean:161](../../SerrePositivity/HomologicalAlgebra/Cech/Basic.lean)。
- `SerrePositivity.AlgebraicGeometry.cechIntegerLiftTotalFunctor_additive` — [SerrePositivity/AlgebraicGeometry/CechIntegerLiftTotalFunctor.lean:23](../../SerrePositivity/AlgebraicGeometry/CechIntegerLiftTotalFunctor.lean)。

判断：既存の加法関手とaugmentedCochainの交換の同型を同じtotal関手へ代入する。

<a id="c09"></a>
### C09 — def complexValuedAugmentedDouble_columnZeroProjection

区分：G4。素：8〜16行、係数2：16〜32行。依存：[C08](#c08)。

```lean
def complexValuedAugmentedDouble_columnZeroProjection
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u}) :
    TR (complexValuedAugmentedDouble F) ⟶ AT (SerrePositivity.Cech.col F 0)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.cechIntegerTotalToColumnZero_naturality` — [SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean:42](../../SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean)。

判断：元の零次列射影の後にC08の同じ零次の同型を合成する。

<a id="c10"></a>
### C10 — theorem complexValuedAugmentedDouble_columnZeroProjection_quasiIso

区分：G4。素：15〜30行、係数2：30〜60行。依存：[C09](#c09)。

```lean
theorem complexValuedAugmentedDouble_columnZeroProjection_quasiIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u})
    (hF : ∀ i, 0 < i → (AT (SerrePositivity.Cech.col F i)).Acyclic) :
    QuasiIso (complexValuedAugmentedDouble_columnZeroProjection F)
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10の二重図式を複体値のČechモデルで実装するtotalの法則。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.cechIntegerTotalToColumnZero_quasiIso` — [SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean:101](../../SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean)。

判断：正の列はC08で仮定と同じ複体。既存の零次列射影の判定を使う。

<a id="c11"></a>
### C11 ★ — theorem complexValuedDoubleCech_axes_acyclic_iff

区分：G4。素：25〜50行、係数2：50〜100行。依存：[C04](#c04), [C07](#c07), [C10](#c10)。

```lean
theorem complexValuedDoubleCech_axes_acyclic_iff
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CoZ.{u})
    (hc : ∀ i, 0 < i → (AT (SerrePositivity.Cech.col F i)).Acyclic)
    (hr : ∀ j, 0 < j → (AT (SerrePositivity.Cech.row F j)).Acyclic) :
    (AT (SerrePositivity.Cech.col F 0)).Acyclic ↔
      (AT (SerrePositivity.Cech.row F 0)).Acyclic
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.Cech.doubleCech_acyclic_iff` — [SerrePositivity/HomologicalAlgebra/Cech/Double.lean:183](../../SerrePositivity/HomologicalAlgebra/Cech/Double.lean)。
- `SerrePositivity.AlgebraicGeometry.cechIntegerTotalToColumnZero_quasiIso` — [SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean:101](../../SerrePositivity/AlgebraicGeometry/CechIntegerTotalToColumnZeroQuasiIso.lean)。

判断：B1と同じ二方向の軸比較を複体値へ移す既存totalの法則。B1のAddCommGrp版に複体値をそのまま代入できるとは主張しない。

<a id="p20"></a>
### P20 ★ — theorem pairedPerfectCech_zero_col_acyclic_iff {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：35〜65行、係数2：70〜130行。依存：[P18](#p18)。

```lean
theorem pairedPerfectCech_zero_col_acyclic_iff {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (AT (SerrePositivity.Cech.col (pairedPerfectCech h g U V p hp hR) 0)).Acyclic ↔
      PC g V p hp hR
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.cechSingleTotal_acyclic_of_constant` — [SerrePositivity/AlgebraicGeometry/CechConstantTotalRetraction.lean:147](../../SerrePositivity/AlgebraicGeometry/CechConstantTotalRetraction.lean)。
- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_constant` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean:48](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean)。
- `SerrePositivity.AlgebraicGeometry.cechTupleReindex_comp` — [SerrePositivity/AlgebraicGeometry/CechTupleReindex.lean:28](../../SerrePositivity/AlgebraicGeometry/CechTupleReindex.lean)。

判断：片方がstarのpullbackは元のnerve、添字の空タプル因子はUnit。元のconstant角からsingleへの比較を両方向に照合する。一方向のretractの定理だけで同値を主張しない。

<a id="p21"></a>
### P21 — theorem pairedPerfectCech_zero_row_acyclic_iff {R : Type u} [CommRing R] {X Y : Scheme.{u}}

区分：G4。素：20〜40行、係数2：40〜80行。依存：[P20](#p20)。

```lean
theorem pairedPerfectCech_zero_row_acyclic_iff {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (AT (SerrePositivity.Cech.row (pairedPerfectCech h g U V p hp hR) 0)).Acyclic ↔
      PC h U p hp hR
```

原典：形式化のための補題。独立した原典番号なし。BS17 Lemma 2.10で使う二重nerveを、選択した有限アフィン被覆と同じ射で扱うための座標・自然性。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.cechSingleTotal_acyclic_of_constant` — [SerrePositivity/AlgebraicGeometry/CechConstantTotalRetraction.lean:147](../../SerrePositivity/AlgebraicGeometry/CechConstantTotalRetraction.lean)。
- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_constant` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean:48](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleConstantTotal.lean)。

判断：P20の二つの因子の順序を、元のpullbackの対称同型と被覆のreindexで交換する。

<a id="f01"></a>
### F01 — theorem exists_section_adapted_affine_cover

区分：G4。素：25〜50行、係数2：50〜100行。依存：なし（既存宣言から）。

```lean
theorem exists_section_adapted_affine_cover
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : ι → Y.Opens) (hcU : (⨆ i, U i) = ⊤) :
    ∃ (n : ℕ) (V : Fin n → (Spec (CommRingCat.of R)).Opens) (ρ : Fin n → ι),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        ∀ j, V j ≤ s ⁻¹ᵁ U (ρ j)
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_finite_affineOpenCover` — [SerrePositivity/AlgebraicGeometry/FiniteAffineCover.lean:26](../../SerrePositivity/AlgebraicGeometry/FiniteAffineCover.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCommonOpenCover_iSup` — [SerrePositivity/AlgebraicGeometry/SchemeCommonAffineCover.lean:24](../../SerrePositivity/AlgebraicGeometry/SchemeCommonAffineCover.lean)。

判断：元のsの逆像開被覆を有限アフィン細分する。切断の像が一つの既存のUに収まるという未供給の仮定を置かない。

<a id="f02"></a>
### F02 — theorem section_affine_chart_retraction

区分：G4。素：25〜50行、係数2：50〜100行。依存：[F01](#f01)。

```lean
theorem section_affine_chart_retraction
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hVs : V ≤ s ⁻¹ᵁ U) :
    ∃ r : Γ((U ⊓ g ⁻¹ᵁ V).toScheme, ⊤) ⟶ Γ(V.toScheme, ⊤),
      (g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).appTop ≫ r = 𝟙 _
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `Scheme.Hom.resLE` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:774](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean)。
- `morphismRestrict_appLE` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:677](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean)。

判断：同じ切断の制限をΓで反変に写す。局所に新しい切断を仮定するのではなくsから作る。

<a id="f03"></a>
### F03 — theorem section_affine_chart_frobeniusCechExact

区分：G4。素：15〜30行、係数2：30〜60行。依存：[F02](#f02)。

```lean
theorem section_affine_chart_frobeniusCechExact
    {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (U : Y.Opens) (hU : IsAffineOpen U)
    (V : (Spec (CommRingCat.of R)).Opens) (hV : IsAffineOpen V)
    (hVs : V ≤ s ⁻¹ᵁ U) (p : ℕ) (hp : p.Prime)
    (hz : (p : Γ(V.toScheme, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk (g.resLE V (U ⊓ g ⁻¹ᵁ V) inf_le_right).appTop) p hp hz)
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `SerrePositivity.Cech.isCechExact_of_retraction` — [SerrePositivity/HomologicalAlgebra/Cech/Split.lean:38](../../SerrePositivity/HomologicalAlgebra/Cech/Split.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusAugmentedRingCoefficients_exact_iff` — [SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean:106](../../SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitMap_comp` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:71](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean)。

判断：元の局所の環のretractionへFrobenius写像の合成則を適用し、B1の切断の完全性で閉じる。

<a id="f04"></a>
### F04 ★ — theorem pairedCech_col_acyclic_of_sections {R : Type u} [CommRing R] [IsNoetherianRing R]

区分：G4。素：120〜240行、係数2：240〜480行。依存：[F03](#f03), [P19](#p19), [C11](#c11)。

```lean
theorem pairedCech_col_acyclic_of_sections {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hσ : ∀ i : ℕ, 0 < i →
      ∃ s : (AN h).obj (op (SerrePositivity.Cech.simplex i)) ⟶
        pullback g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)),
        s ≫ pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)) = 𝟙 _) :
    ∀ i : ℕ, 0 < i →
      (AT (SerrePositivity.Cech.col
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) i)).Acyclic
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_apply` — [SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean:35](../../SerrePositivity/AlgebraicGeometry/SchemeStructurePerfectCechRefinedPullback.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeModuleAffineCoverCech_acyclic` — [SerrePositivity/AlgebraicGeometry/SchemeModuleAffineCoverCech.lean:58](../../SerrePositivity/AlgebraicGeometry/SchemeModuleAffineCoverCech.lean)。
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopy` — [SerrePositivity/AlgebraicGeometry/OpenCoverCechRefinementIndependence.lean:41](../../SerrePositivity/AlgebraicGeometry/OpenCoverCechRefinementIndependence.lean)。

判断：新しい局所から全体への照合。F01のsに適合した細分上でF03を全ての非空交叉へ適用し、既存の共通細分の比較で元のVへ戻す。B1の環の切断を非アフィンなΓ(Y)へ直接適用しない。

<a id="f05"></a>
### F05 ★ — theorem pairedCech_col_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]

区分：G4。素：70〜140行、係数2：140〜280行。依存：[D01](#d01), [P19](#p19), [C11](#c11)。

```lean
theorem pairedCech_col_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hd : ∀ i : ℕ, 0 < i → PerfectCechUniversalDescent p hp
      (pullback.snd g (augmentedNerveBase h (SerrePositivity.Cech.simplex i)))) :
    ∀ i : ℕ, 0 < i →
      (AT (SerrePositivity.Cech.col
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) i)).Acyclic
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.affineCechNerveTupleAugmentedGlobalTotal_quasiIso` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedGlobal.lean:70](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleAugmentedGlobal.lean)。
- `SerrePositivity.AlgebraicGeometry.affineScalarPerfectAugmentedIso` — [SerrePositivity/AlgebraicGeometry/AffineScalarPerfectTupleTotal.lean:25](../../SerrePositivity/AlgebraicGeometry/AffineScalarPerfectTupleTotal.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_mapCechNerve_preimage` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean:19](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleBaseChange.lean)。

判断：新しい係数の照合。Aの各nerveはアフィンでNoetherなのでisoSpecへ移し、同じVの逆像のhdを適用する。定数のUnit被覆との比較も含む。

<a id="f06"></a>
### F06 ★ — theorem pairedCech_row_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]

区分：G4。素：90〜180行、係数2：180〜360行。依存：[D01](#d01), [P19](#p19), [C11](#c11)。

```lean
theorem pairedCech_row_acyclic_of_baseChangeDescent {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A Y : Scheme.{u}} [IsAffine A]
    (h : A ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation h] [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    {κ : Type} [Fintype κ] [DecidableEq κ] (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hd : ∀ j : ℕ, 0 < j → PerfectCechUniversalDescent p hp
      (pullback.snd h (augmentedNerveBase g (SerrePositivity.Cech.simplex j)))) :
    ∀ j : ℕ, 0 < j →
      (AT (SerrePositivity.Cech.row
        (pairedPerfectCech h g (fun _ : Unit ↦ ⊤) V p hp hR) j)).Acyclic
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_isAffine` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean:62](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleAffine.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeCechTupleOpen_iSup` — [SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean:25](../../SerrePositivity/AlgebraicGeometry/SchemeCechTupleCover.lean)。
- `SerrePositivity.AlgebraicGeometry.cechIntegerAugmentedDouble_acyclic_of_rows` — [SerrePositivity/AlgebraicGeometry/CechAugmentedDoubleRows.lean:33](../../SerrePositivity/AlgebraicGeometry/CechAugmentedDoubleRows.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeModuleCechRefinement_homologyMap_isIso` — [SerrePositivity/AlgebraicGeometry/SchemeModuleCechRefinement.lean:27](../../SerrePositivity/AlgebraicGeometry/SchemeModuleCechRefinement.lean)。

判断：新しい照合。Yの各nerveのVタプルの全アフィン交叉にhdを適用し、その同じ被覆のČech方向をtotalへ渡す。Yの各nerve自体をアフィンとは扱わない。

<a id="f07"></a>
### F07 — theorem section_perfectCechTupleTotal_acyclic

区分：G4。素：30〜60行、係数2：60〜120行。依存：[F04](#f04), [F06](#f06), [D03](#d03), [P20](#p20), [P21](#p21), [C11](#c11)。

```lean
theorem section_perfectCechTupleTotal_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g] (s : Spec (CommRingCat.of R) ⟶ Y)
    (hs : s ≫ g = 𝟙 _) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) : PC g U p hp hR
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_flat_surjective` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean:36](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean)。

判断：paired図式の一方を恒等射にし、切断側にF04、恒等側に既存のflat入力を使う。非アフィンな始域の切断を環のretractionと同一視しない。

<a id="d05"></a>
### D05 — theorem perfectCechUniversalDescent_of_section

区分：G4。素：15〜30行、係数2：30〜60行。依存：[F07](#f07)。

```lean
theorem perfectCechUniversalDescent_of_section
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 _) : PerfectCechUniversalDescent p hp f
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `CategoryTheory.Limits.pullback.hom_ext` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:222](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：各アフィン試験基底へ同じ切断をpullbackしてF07を適用する。

<a id="d06"></a>
### D06 ★ — theorem perfectCechUniversalDescent_of_affine_refinement

区分：G4。素：60〜120行、係数2：120〜240行。依存：[D02](#d02), [D05](#d05), [F04](#f04), [F06](#f06), [P20](#p20), [P21](#p21), [C11](#c11)。

```lean
theorem perfectCechUniversalDescent_of_affine_refinement
    (p : ℕ) (hp : p.Prime) {X Y A : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (a : A ⟶ X) [IsAffineHom (a ≫ f)] [LocallyOfFinitePresentation (a ≫ f)]
    (ha : PerfectCechUniversalDescent p hp (a ≫ f)) :
    PerfectCechUniversalDescent p hp f
```

原典：BS17 Lemma 2.10(a)の切断と細分の消去の証明段。表示した相対Čech型は形式化用の補題。

既存の宣言と場所：

- `SerrePositivity.Cech.isCechExact_of_comp` — [SerrePositivity/HomologicalAlgebra/Cech/Composition.lean:160](../../SerrePositivity/HomologicalAlgebra/Cech/Composition.lean)。
- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTuplePullback_naturality` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleNaturality.lean:33](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleNaturality.lean)。

判断：同じアフィン細分のnerveの正次数には元のaからfの底変換への切断がある。F04とhaの底変換のF06で両軸を比較する。合成則D07を使わず先に証明する。

<a id="f08"></a>
### F08 — def fppfComparisonRefiner

区分：G4。素：15〜30行、係数2：30〜60行。依存：[P01](#p01)。

```lean
def fppfComparisonRefiner
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    (q : A ⟶ B) (g : B ⟶ Spec (CommRingCat.of R)) (n : SimplexCategory) :
    pullback q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0) ⟶
      pullback (q ≫ g) (augmentedNerveBase g (.of n))
```

原典：BS17 Lemma 2.10(b)の合成の証明段。表示したアフィンなfppf細分の場合に使う内部の補題。

既存の宣言と場所：

- `CategoryTheory.Arrow.augmentedCechNerve` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean:72](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean)。
- `CategoryTheory.Limits.pullback.lift` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:129](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：同じn番目のnerveの最初のB座標に沿うqの底変換を、q≫gの底変換へ送る標準lift。

<a id="f09"></a>
### F09 — theorem fppfComparisonRefiner_over

区分：G4。素：5〜10行、係数2：10〜20行。依存：[F08](#f08)。

```lean
theorem fppfComparisonRefiner_over
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    (q : A ⟶ B) (g : B ⟶ Spec (CommRingCat.of R)) (n : SimplexCategory) :
    fppfComparisonRefiner q g n ≫ pullback.snd (q ≫ g) (augmentedNerveBase g (.of n)) =
      pullback.snd q (WidePullback.π (fun _ : Fin (n.len+1) ↦ g) 0)
```

原典：BS17 Lemma 2.10(b)の合成の証明段。表示したアフィンなfppf細分の場合に使う内部の補題。

既存の宣言と場所：

- `CategoryTheory.Limits.pullback.lift_snd` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:179](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean)。

判断：元のpullback.lift_sndの式そのもの。

<a id="f10"></a>
### F10 — theorem fppfComparison_baseChange_descent

区分：G4。素：30〜60行、係数2：60〜120行。依存：[F09](#f09), [D03](#d03), [D06](#d06)。

```lean
theorem fppfComparison_baseChange_descent
    {R : Type u} [CommRing R] {A B : Scheme.{u}} [IsAffine A]
    (q : A ⟶ B) [IsAffineHom q] [Flat q] [Surjective q]
    [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g] (n : SimplexCategory)
    (p : ℕ) (hp : p.Prime) : PerfectCechUniversalDescent p hp
      (pullback.snd (q ≫ g) (augmentedNerveBase g (.of n)))
```

原典：BS17 Lemma 2.10(b)の合成の証明段。表示したアフィンなfppf細分の場合に使う内部の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_affine_flatSurjective_refinement` — [SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean:21](../../SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean)。

判断：F08の細分は元のqのアフィン平坦全射の底変換。その普遍的完全性をD06で合成の底変換へ消去する。合成自身の完全性は仮定しない。

<a id="f11"></a>
### F11 — theorem affine_fppf_composite_tupleTotal_acyclic

区分：G4。素：35〜70行、係数2：70〜140行。依存：[F05](#f05), [F06](#f06), [F10](#f10), [D02](#d02), [P20](#p20), [P21](#p21), [C11](#c11)。

```lean
theorem affine_fppf_composite_tupleTotal_acyclic
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A B : Scheme.{u}} [IsAffine A] (q : A ⟶ B)
    [IsAffineHom q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsProper g] [Surjective g]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (hg : PerfectCechUniversalDescent p hp g) :
    PC (q ≫ g) (fun _ : Unit ↦ ⊤) p hp hR
```

原典：BS17 Lemma 2.10(b)の合成の証明段。表示したアフィンなfppf細分の場合に使う内部の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_flat_surjective` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean:36](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean)。
- `SerrePositivity.AlgebraicGeometry.affineFlatSurjective_restrict_frobeniusCechExact` — [SerrePositivity/AlgebraicGeometry/RelativeAffineFlatFrobeniusCech.lean:35](../../SerrePositivity/AlgebraicGeometry/RelativeAffineFlatFrobeniusCech.lean)。

判断：一方の正軸はhgの底変換、他方はF10。ゼロ軸のgの完全性から同じアフィン合成へ戻す。Γ(B)の平坦性は仮定しない。

<a id="d07"></a>
### D07 ★ — theorem perfectCechUniversalDescent_affine_fppf_comp

区分：G4。素：35〜70行、係数2：70〜140行。依存：[F11](#f11), [D02](#d02)。

```lean
theorem perfectCechUniversalDescent_affine_fppf_comp
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A B : Scheme.{u}} [IsAffine A] (q : A ⟶ B)
    [IsAffineHom q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (g : B ⟶ Spec (CommRingCat.of R)) [IsProper g] [Surjective g]
    (p : ℕ) (hp : p.Prime) (hg : PerfectCechUniversalDescent p hp g) :
    PerfectCechUniversalDescent p hp (q ≫ g)
```

原典：BS17 Lemma 2.10(b)の合成の証明段。表示したアフィンなfppf細分の場合に使う内部の補題。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeCechPullback_comparison_naturality` — [SerrePositivity/AlgebraicGeometry/SchemeCechPullbackComparison.lean:28](../../SerrePositivity/AlgebraicGeometry/SchemeCechPullbackComparison.lean)。
- `SerrePositivity.AlgebraicGeometry.openCoverCechRefinementHomotopy` — [SerrePositivity/AlgebraicGeometry/OpenCoverCechRefinementIndependence.lean:41](../../SerrePositivity/AlgebraicGeometry/OpenCoverCechRefinementIndependence.lean)。

判断：各Noetherアフィン底変換後にF11を適用し、Unit被覆から任意の有限アフィン被覆へ既存の比較で戻す。任意の非アフィンなΓの合成則には広げない。

<a id="d08"></a>
### D08 — theorem perfectCechUniversalDescent_targetIso

区分：G4。素：20〜40行、係数2：40〜80行。依存：[D02](#d02)。

```lean
theorem perfectCechUniversalDescent_targetIso
    (p : ℕ) (hp : p.Prime) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) :
    PerfectCechUniversalDescent p hp (f ≫ e.hom) ↔ PerfectCechUniversalDescent p hp f
```

原典：BS17 Lemma 2.10の普遍的な降下・底変換・二重図式の証明段。一般の空間値の定理は作らず、表示したČech型だけを証明する。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_cartesianBaseChangeComparison` — [SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean:38](../../SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeStructurePerfectCechRefinedPullbackMap_comp` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechPullbackComposition.lean:32](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechPullbackComposition.lean)。

判断：同じ試験写像をe.hom/e.invで移し、既存のpullbackの同型を元のタプル被覆へ運ぶ。

<a id="d09"></a>
### D09 — theorem perfectCechUniversalDescent_of_nil_baseChange

区分：G4。素：35〜70行、係数2：70〜140行。依存：[N06](#n06), [D02](#d02)。

```lean
theorem perfectCechUniversalDescent_of_nil_baseChange
    (p : ℕ) (hp : p.Prime) {X Y Y₀ : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (i : Y₀ ⟶ Y) [IsClosedImmersion i] [Surjective i] [LocallyOfFinitePresentation i]
    (hf : PerfectCechUniversalDescent p hp (pullback.snd f i)) :
    PerfectCechUniversalDescent p hp f
```

原典：[BS17](https://arxiv.org/pdf/1507.06490) Lemma 3.8、Thm 2.9のnil段。[Stacks 04DC](https://stacks.math.columbia.edu/tag/04DC)の普遍同相の安定性。ここでのapp U・タプルの型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemeNilradicalSubscheme_surjective` — [SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean:38](../../SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean)。
- `SerrePositivity.AlgebraicGeometry.isPullback_cartesianBaseChangeComparison` — [SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean:38](../../SerrePositivity/AlgebraicGeometry/CartesianBaseChangeComparison.lean)。

判断：試験アフィン基底のnil閉厚化は閉部分なので再びNoetherアフィン。hfをその同じ基底で使い、N06で元のtotalへ戻す。

<a id="i01"></a>
### I01 — structure BlowupPerfectCechBaseChangeData

区分：G4。素：12〜24行、係数2：24〜48行。依存：なし（既存宣言から）。

```lean
structure BlowupPerfectCechBaseChangeData
    {Y : Scheme.{u}} (J : Y.IdealSheafData)
    {A : Type u} [CommRing A] (t : Spec (CommRingCat.of A) ⟶ Y) where
  ideal : Ideal A
  centerIso : (J.comap t).subscheme ≅ Spec (CommRingCat.of (A ⧸ ideal ^ 1))
  center_over : centerIso.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal ^ 1))) =
    (J.comap t).subschemeι
  model : DegreeOneProjectiveModel (R := A) (pullback.snd (blowupπ J) t)
  outside : IsIso (pullback.snd (blowupπ J) t ∣_ affineCenterComplement ideal)
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_inductiveCenterRestrictionBaseChangeMap` — [SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean:47](../../SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean)。
- `SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel.baseChange` — [SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveModelBaseChange.lean:43](../../SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveModelBaseChange.lean)。

判断：内部の証人の型。任意の底変換を逆像イデアルのblowupと同定するfieldは置かない。

<a id="i02"></a>
### I02 ★ — def blowupPerfectCechBaseChangeData

区分：G4。素：60〜120行、係数2：120〜240行。依存：[I01](#i01)。

```lean
def blowupPerfectCechBaseChangeData
    {Y : Scheme.{u}} [IsAffine Y] [_root_.AlgebraicGeometry.IsNoetherian Y]
    (J : Y.IdealSheafData) {A : Type u} [CommRing A] [IsNoetherianRing A]
    (t : Spec (CommRingCat.of A) ⟶ Y) : BlowupPerfectCechBaseChangeData J t
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.nonempty_blowupAffinePullbackProjectiveModel` — [SerrePositivity/AlgebraicGeometry/BlowupAffineProjectiveModel.lean:31](../../SerrePositivity/AlgebraicGeometry/BlowupAffineProjectiveModel.lean)。
- `SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel.baseChange` — [SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveModelBaseChange.lean:43](../../SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveModelBaseChange.lean)。
- `SerrePositivity.AlgebraicGeometry.isPullback_inductiveCenterBaseChangeProjection` — [SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean:27](../../SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean)。
- `SerrePositivity.AlgebraicGeometry.pullback_snd_isIso_of_open_preimage_top` — [SerrePositivity/AlgebraicGeometry/OpenIsomorphismBaseChange.lean:34](../../SerrePositivity/AlgebraicGeometry/OpenIsomorphismBaseChange.lean)。

判断：Y.isoSpecで元のblowupの次数一表示を取り、その表示だけをtへ係数移送する。中心の商表示とoutsideの式も同じtで照合する。

<a id="i03"></a>
### I03 ★ — theorem blowupBaseChange_center_universalDescent

区分：G4。素：40〜80行、係数2：80〜160行。依存：[D02](#d02), [D08](#d08), [I02](#i02)。

```lean
theorem blowupBaseChange_center_universalDescent
    {Y : Scheme.{u}} (J : Y.IdealSheafData) {A : Type u} [CommRing A]
    (t : Spec (CommRingCat.of A) ⟶ Y) (d : BlowupPerfectCechBaseChangeData J t)
    (p : ℕ) (hp : p.Prime)
    (hc : PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι)) :
    PerfectCechUniversalDescent p hp
      (pullback.snd (pullback.snd (blowupπ J) t)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ 1)))))
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_inductiveCenterRestrictionBaseChangeMap` — [SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean:47](../../SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean)。
- `SerrePositivity.AlgebraicGeometry.inductiveCenterRestrictionBaseChangeMap` — [SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean:35](../../SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean)。

判断：中心自身のcomapのCartesianな式とd.centerIsoで、元の中心のhcを実際のR/I^1の中心へ移す。中心のTへの像の次元は使わない。

<a id="i04"></a>
### I04 — theorem perfectCechUniversalDescent_blowup_of_center

区分：G4。素：35〜70行、係数2：70〜140行。依存：[I03](#i03)。

```lean
theorem perfectCechUniversalDescent_blowup_of_center
    {Y : Scheme.{u}} [IsAffine Y] [_root_.AlgebraicGeometry.IsNoetherian Y]
    (J : Y.IdealSheafData) [Surjective (blowupπ J)] (p : ℕ) (hp : p.Prime)
    (hc : PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι)) :
    PerfectCechUniversalDescent p hp (blowupπ J)
```

原典：BS17 Lemma 4.6(i)の射影の場合（BST13 Lemma 3.9のČech版）。一般の固有コホモロジーやStein分解を追加しない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModel.perfectCechTupleTotal_acyclic_of_center` — [SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveCechTupleCenterCriterion.lean:30](../../SerrePositivity/AlgebraicGeometry/DegreeOneProjectiveCechTupleCenterCriterion.lean)。

判断：各試験基底でI02の同じ表示とI03の中心の入力を、検証済みの射影Čech判定へ代入する。一般のproperを射影と仮定しない。

<a id="i05"></a>
### I05 — def closedCenterImage {S Y : Scheme.{u}} (j : Y ⟶ S) [IsClosedImmersion j]

区分：G4。素：8〜16行、係数2：16〜32行。依存：なし（既存宣言から）。

```lean
def closedCenterImage {S Y : Scheme.{u}} (j : Y ⟶ S) [IsClosedImmersion j]
    (J : Y.IdealSheafData) : TopologicalSpace.Closeds S
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:471](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean)。

判断：台はSet.range (J.subschemeι ≫ j)。閉埋め込みの合成の閉像として同じ集合を取る。

<a id="i06"></a>
### I06 — theorem closedCenterImage_lt

区分：G4。素：20〜40行、係数2：40〜80行。依存：[I05](#i05)。

```lean
theorem closedCenterImage_lt
    {S Y : Scheme.{u}} (j : Y ⟶ S) [IsClosedImmersion j] [Nonempty Y]
    (C : TopologicalSpace.Closeds S) (hj : Set.range j = (C : Set S))
    (J : Y.IdealSheafData) (hJ : Dense (centerComplement J).carrier) :
    closedCenterImage j J < C
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.preimage_centerComplement_comap` — [SerrePositivity/AlgebraicGeometry/IdealComplementPullback.lean:27](../../SerrePositivity/AlgebraicGeometry/IdealComplementPullback.lean)。
- `SerrePositivity.AlgebraicGeometry.exists_proper_fppf_blowup_refinement_of_proper_surjective` — [SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean:93](../../SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean)。

判断：元のYが非空で、同じcenterComplementが稠密だから中心の像が真に小さい。テスト基底Tでこの不等式を主張しない。

<a id="i07"></a>
### I07 — def NoetherClosedPerfectCechProperty (S : Scheme.{u}) (p : ℕ) (hp : p.Prime)

区分：G4。素：8〜15行、係数2：16〜30行。依存：[D01](#d01)。

```lean
def NoetherClosedPerfectCechProperty (S : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds S) : Prop :=
  ∀ (Y : Scheme.{u}) (j : Y ⟶ S), IsClosedImmersion j →
    Set.range j = (C : Set S) →
    ∀ (X : Scheme.{u}) (f : X ⟶ Y), IsProper f → Surjective f →
      PerfectCechUniversalDescent p hp f
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `NoetherianSpace` — [.lake/packages/mathlib/Mathlib/Topology/NoetherianSpace.lean:52](../../.lake/packages/mathlib/Mathlib/Topology/NoetherianSpace.lean)。

判断：内部の帰納述語。閉像C上の元のfを固定してから任意のNoetherアフィン底変換を量化する。

<a id="i08"></a>
### I08 — theorem noetherClosedPerfectCechProperty_empty

区分：G4。素：20〜40行、係数2：40〜80行。依存：[I07](#i07)。

```lean
theorem noetherClosedPerfectCechProperty_empty
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp ⊥
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.schemePerfectCechTupleDouble_acyclic_of_flat_surjective` — [SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean:36](../../SerrePositivity/AlgebraicGeometry/SchemePerfectCechTupleFlatTotal.lean)。
- `AlgebraicGeometry.isIso_of_isEmpty` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:108](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean)。

判断：空基底を独立に処理する。非空性なしにI06の真の不等式を使わない。

<a id="i09"></a>
### I09 — theorem noetherClosed_center_input

区分：G4。素：25〜50行、係数2：50〜100行。依存：[I06](#i06), [I07](#i07)。

```lean
theorem noetherClosed_center_input
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R)))
    (ih : ∀ D < C, NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp D)
    {Y : Scheme.{u}} (j : Y ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion j]
    [Nonempty Y] (hj : Set.range j = (C : Set (Spec (CommRingCat.of R))))
    (J : Y.IdealSheafData) (hJ : Dense (centerComplement J).carrier)
    [Surjective (blowupπ J)] :
    PerfectCechUniversalDescent p hp (pullback.snd (blowupπ J) J.subschemeι)
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isPullback_inductiveCenterRestrictionBaseChangeMap` — [SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean:47](../../SerrePositivity/AlgebraicGeometry/InductiveCenterBaseChange.lean)。
- `AlgebraicGeometry.IsProper` — [.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:41](../../.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean)。

判断：元の閉像closedCenterImage j Jへihを適用する。中心の射はblowupの固有全射の同じ底変換。

<a id="i10"></a>
### I10 ★ — theorem noetherClosedPerfectCechProperty_step

区分：G4。素：80〜160行、係数2：160〜320行。依存：[I04](#i04), [I08](#i08), [I09](#i09), [D06](#d06), [D07](#d07), [D08](#d08), [D09](#d09)。

```lean
theorem noetherClosedPerfectCechProperty_step
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R)))
    (ih : ∀ D < C, NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp D) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp C
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_proper_fppf_blowup_refinement_of_proper_surjective` — [SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean:93](../../SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeNilradicalSubscheme_isReduced` — [SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean:20](../../SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean)。
- `SerrePositivity.AlgebraicGeometry.schemeNilradicalSubscheme_surjective` — [SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean:38](../../SerrePositivity/AlgebraicGeometry/SchemeNilradicalReduction.lean)。
- `SerrePositivity.AlgebraicGeometry.exists_affine_flatSurjective_refinement` — [SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean:21](../../SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean)。

判断：新しい帰納の合成。Yを被約化し、元のYでRGの中心を先に選ぶ。I09→I04、同じfppfのアフィン細分→D07→D06、最後にD09。各順序を省略せず照合する。

<a id="i11"></a>
### I11 — theorem noetherClosedPerfectCechProperty_all

区分：G4。素：10〜20行、係数2：20〜40行。依存：[I10](#i10)。

```lean
theorem noetherClosedPerfectCechProperty_all
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R))) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp C
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `NoetherianSpace` — [.lake/packages/mathlib/Mathlib/Topology/NoetherianSpace.lean:52](../../.lake/packages/mathlib/Mathlib/Topology/NoetherianSpace.lean)。

判断：Noether空間の閉集合の真の包含によるwell-founded帰納へI10を代入する。Krull次元の有限性は要求しない。

<a id="i12"></a>
### I12 — theorem properSurjective_perfectCechUniversalDescent

区分：G4。素：8〜16行、係数2：16〜32行。依存：[I11](#i11)。

```lean
theorem properSurjective_perfectCechUniversalDescent
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Surjective f]
    (p : ℕ) (hp : p.Prime) : PerfectCechUniversalDescent p hp f
```

原典：BS17 Lemma 2.6のNoether帰納、RG71 Thm 5.2.2を使う段。[Stacks 0815](https://stacks.math.columbia.edu/tag/0815)は既存の平坦化の供給。追加の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_proper_fppf_blowup_refinement_of_proper_surjective` — [SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean:93](../../SerrePositivity/AlgebraicGeometry/ProperFlatteningNoetherian.lean)。

判断：C=⊤、j=恒等でI11を適用する。元のfに射影性を要求しない。

<a id="i13"></a>
### I13 ★ — theorem noetherianAffineVCover_frobeniusCechExact

区分：G4。素：55〜110行、係数2：110〜220行。依存：[I12](#i12), [D06](#d06), [D07](#d07)。

```lean
theorem noetherianAffineVCover_frobeniusCechExact
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (hfp : f.FinitePresentation) (hv : IsAffineVCover f)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom f)) p hp hR)
```

原典：[Rydh Thm 3.10](https://davidrydh.se/papers/submersion20100305.pdf)。BS17のTheorem 2.4（より強い開被覆による細分）を使う位置を、承認済みのfppf–proper経路で置き換える。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineBase` — [SerrePositivity/AlgebraicGeometry/AffineBaseVCoverRefinement.lean:20](../../SerrePositivity/AlgebraicGeometry/AffineBaseVCoverRefinement.lean)。
- `SerrePositivity.AlgebraicGeometry.exists_affine_flatSurjective_refinement` — [SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean:21](../../SerrePositivity/AlgebraicGeometry/RelativeFppfAffineRefinement.lean)。
- `SerrePositivity.AlgebraicGeometry.ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic` — [SerrePositivity/AlgebraicGeometry/SpecScalarPerfectTupleTotal.lean:65](../../SerrePositivity/AlgebraicGeometry/SpecScalarPerfectTupleTotal.lean)。
- `SerrePositivity.AlgebraicGeometry.isSchemeVCover_specMap_iff` — [SerrePositivity/AlgebraicGeometry/SchemeVCover.lean:27](../../SerrePositivity/AlgebraicGeometry/SchemeVCover.lean)。

判断：Rydhの既存細分、properのI12、相対fppfのD07、細分消去D06を順に使い、元のfの環のconerveへ既存の出口で戻す。模型やNoether性はG5で消去する。

<a id="e01"></a>
### E01 — def frobeniusArrowFamilyDiagram {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：18〜36行、係数2：36〜72行。依存：なし（既存宣言から）。

```lean
def frobeniusArrowFamilyDiagram {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    J ⥤ (AsSmall.{u} ℕ ⥤ Arrow CommRingCat.{u})
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallDiagramMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:59](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallDiagramMap_id` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean:38](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallDiagramMap_comp` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean:45](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean)。

判断：objは既存のfrobeniusArrowSmallDiagram、mapと二法則も同じ既存宣言。charの証明の移送は命題のproof irrelevanceだけ。

<a id="e02"></a>
### E02 — def frobeniusArrowFamilyLimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：15〜30行、係数2：30〜60行。依存：なし（既存宣言から）。

```lean
def frobeniusArrowFamilyLimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) : J ⥤ Arrow CommRingCat.{u}
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:21](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap_id` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean:57](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap_comp` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean:72](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean)。

判断：objは元の各矢印の実際のFrobenius順極限、map・法則は既存の同じ写像。

<a id="e03"></a>
### E03 — def frobeniusArrowFamilyStandardIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：12〜24行、係数2：24〜48行。依存：[E01](#e01), [E02](#e02)。

```lean
def frobeniusArrowFamilyStandardIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    frobeniusArrowFamilyLimit D p hp hL hR ≅
      frobeniusArrowFamilyDiagram D p hp hL hR ⋙ colim
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallColimitIso` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowCocone.lean:118](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowCocone.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallColimitIso_naturality` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:91](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。

判断：既存の標準同型を対象ごとに取り、既存の元の四角形への自然性でまとめる。

<a id="e04"></a>
### E04 — def frobeniusArrowFamilyTargetCocone {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：15〜30行、係数2：30〜60行。依存：[E02](#e02)。

```lean
def frobeniusArrowFamilyTargetCocone {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0) :
    Cocone (frobeniusArrowFamilyLimit D p hp hL hR)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:21](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap_comp` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean:72](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowMapLaws.lean)。

判断：頂点はPF c.pt、脚は元のc.ι.app jの同じFrobenius写像。coconeの自然性をmap_compで写す。

<a id="e05"></a>
### E05 — theorem frobeniusArrowFamilyTargetCocone_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：3〜6行、係数2：6〜12行。依存：[E04](#e04)。

```lean
theorem frobeniusArrowFamilyTargetCocone_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (j : J) :
    (frobeniusArrowFamilyTargetCocone D p hp hL hR c hTL hTR).ι.app j =
      frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitArrowMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:21](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。

判断：E04の定義の同じ標準脚の式。

<a id="e06"></a>
### E06 — def frobeniusArrowFamilyStageCocone {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：12〜24行、係数2：24〜48行。依存：[E01](#e01)。

```lean
def frobeniusArrowFamilyStageCocone {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (n : AsSmall.{u} ℕ) :
    Cocone ((frobeniusArrowFamilyDiagram D p hp hL hR).flip.obj n)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallDiagramMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:59](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。

判断：各Frobenius段の対象・J方向の射は元のDそのもの。頂点と脚をcと同じに取る。

<a id="e07"></a>
### E07 — def frobeniusArrowFamilyStageCoconeIsColimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：12〜24行、係数2：24〜48行。依存：[E06](#e06)。

```lean
def frobeniusArrowFamilyStageCoconeIsColimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hc : IsColimit c) (n : AsSmall.{u} ℕ) :
    IsColimit (frobeniusArrowFamilyStageCocone D p hp hL hR c n)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowDiagramMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:39](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。
- `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean:157](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean)。

判断：同じDへの恒等成分の図式同型を介して、与えられたhcを移送する。

<a id="e08"></a>
### E08 ★ — def frobeniusArrowFamilyStageColimitIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：35〜70行、係数2：70〜140行。依存：[E07](#e07)。

```lean
def frobeniusArrowFamilyStageColimitIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    (frobeniusArrowFamilyDiagram D p hp hL hR).flip ⋙ colim ≅
      frobeniusArrowSmallDiagram c.pt p hp hTL hTR
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowCocone_map` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:74](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectSystemMap_naturality` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:20](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean)。

判断：新しい段間の照合。各段のcolimitはE07だが、n方向の遷移が元のc.ptのFrobeniusであることを同じc.ιで確認する。

<a id="e09"></a>
### E09 — theorem frobeniusArrowFamilyStageColimitIso_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：8〜16行、係数2：16〜32行。依存：[E08](#e08)。

```lean
theorem frobeniusArrowFamilyStageColimitIso_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) (j : J) (n : AsSmall.{u} ℕ) :
    colimit.ι ((frobeniusArrowFamilyDiagram D p hp hL hR).flip.obj n) j ≫
      (frobeniusArrowFamilyStageColimitIso D p hp hL hR c hTL hTR hc).hom.app n =
        c.ι.app j
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean:157](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean)。

判断：同じ各段のcolimitの一意同型の標準脚の式。

<a id="e10"></a>
### E10 — def frobeniusArrowFamilyFubiniIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：3〜6行、係数2：6〜12行。依存：[E01](#e01)。

```lean
def frobeniusArrowFamilyFubiniIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    colimit ((frobeniusArrowFamilyDiagram D p hp hL hR).flip ⋙ colim) ≅
      colimit (frobeniusArrowFamilyDiagram D p hp hL hR ⋙ colim)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean:569](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean)。

判断：既存のFubiniの同型への直接代入。新しい余極限交換定理は証明しない。

<a id="e11"></a>
### E11 ★ — def frobeniusArrowFamilyTargetCoconeIsColimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：40〜80行、係数2：80〜160行。依存：[E03](#e03), [E05](#e05), [E08](#e08), [E09](#e09), [E10](#e10)。

```lean
def frobeniusArrowFamilyTargetCoconeIsColimit {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    IsColimit (frobeniusArrowFamilyTargetCocone D p hp hL hR c hTL hTR)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowSmallIsColimit` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowCocone.lean:113](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowCocone.lean)。
- `CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim_ι_ι_hom` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean:579](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Fubini.lean)。

判断：E03・E08・E10の合成がE04の同じcoconeを表すことを、二重の標準脚で照合する。単に対象の同型の存在だけでは済ませない。

<a id="e12"></a>
### E12 — def frobeniusArrowFamilyColimitIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：6〜12行、係数2：12〜24行。依存：[E11](#e11)。

```lean
def frobeniusArrowFamilyColimitIso {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) :
    colimit (frobeniusArrowFamilyLimit D p hp hL hR) ≅
      Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hTL hTR c.pt.hom.hom))
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean:157](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/IsLimit.lean)。

判断：E11と既存のcolimit.isColimitの一意同型。

<a id="e13"></a>
### E13 — theorem frobeniusArrowFamilyColimitIso_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：5〜10行、係数2：10〜20行。依存：[E12](#e12)。

```lean
theorem frobeniusArrowFamilyColimitIso_ι {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    (hc : IsColimit c) (j : J) :
    colimit.ι (frobeniusArrowFamilyLimit D p hp hL hR) j ≫
      (frobeniusArrowFamilyColimitIso D p hp hL hR c hTL hTR hc).hom =
        frobeniusDirectLimitArrowMap (c.ι.app j) p hp (hL j) (hR j) hTL hTR
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusArrowCocone_map` — [SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean:74](../../SerrePositivity/AlgebraicGeometry/FrobeniusArrowNaturality.lean)。

判断：E11の同じcoconeの脚なので一意同型の標準脚の式を使う。

<a id="e14"></a>
### E14 — theorem frobeniusCechExact_of_filtered_arrow_models {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})

区分：G5。素：15〜30行、係数2：30〜60行。依存：[E12](#e12)。

```lean
theorem frobeniusCechExact_of_filtered_arrow_models {J : Type u} [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0)
    (c : Cocone D) (hTL : (p : c.pt.left) = 0) (hTR : (p : c.pt.right) = 0)
    [IsFiltered J] (hc : IsColimit c)
    (hd : ∀ j, SerrePositivity.Cech.IsCechExact
      (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp (hL j) (hR j) (D.obj j).hom.hom)))) :
    SerrePositivity.Cech.IsCechExact
      (Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hTL hTR c.pt.hom.hom)))
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.Cech.isCechExact_colimit` — [SerrePositivity/HomologicalAlgebra/Cech/Filtered.lean:99](../../SerrePositivity/HomologicalAlgebra/Cech/Filtered.lean)。
- `SerrePositivity.Cech.ringCechExact_iff_of_iso` — [SerrePositivity/HomologicalAlgebra/Cech/Basic.lean:190](../../SerrePositivity/HomologicalAlgebra/Cech/Basic.lean)。

判断：各段の完全性を既存のfiltered完全性へ代入し、E12を既存のconerve関手で写した同型で移す。無限の極限と余極限を一般に交換しない。

<a id="e15"></a>
### E15 — theorem coefficientVCoverModel_primeCast

区分：G5。素：8〜16行、係数2：16〜32行。依存：なし（既存宣言から）。

```lean
theorem coefficientVCoverModel_primeCast
    (k : Type u) [CommRing k] [IsNoetherianRing k]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : R →ₐ[k] S) (p : ℕ) (hK : (p : k) = 0)
    (j : CoefficientVCoverModelIndex k g) :
    (p : ((coefficientVCoverModelSmallArrowDiagram k g).obj j).left) = 0 ∧
      (p : ((coefficientVCoverModelSmallArrowDiagram k g).obj j).right) = 0
```

原典：BS17 Lemma 2.12の模型への帰着。固有性の模型の[Stacks 0A0P](https://stacks.math.columbia.edu/tag/0A0P)はG2で供給済み。ここで模型を作り直さない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.coefficientVCoverModelSmallBase_algebra` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean:20](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean)。
- `SerrePositivity.AlgebraicGeometry.coefficientVCoverModelSmallSource_algebra` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean:24](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean)。

判断：各段の同じalgebraMapにnatCastの零性を写すだけ。模型の有限表示性は別の既存宣言を使う。

<a id="e16"></a>
### E16 ★ — theorem coefficientVCover_frobeniusCechExact

区分：G5。素：35〜70行、係数2：70〜140行。依存：[I13](#i13), [E14](#e14), [E15](#e15)。

```lean
theorem coefficientVCover_frobeniusCechExact
    (k : Type u) [CommRing k] [IsNoetherianRing k]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : R →ₐ[k] S) (hv : IsAffineVCover g.toRingHom)
    (p : ℕ) (hp : p.Prime) (hK : (p : k) = 0) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom g.toRingHom)) p hp hR)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.coefficientVCoverModelSmallArrowCoconeIsColimit` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelFinal.lean:45](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelFinal.lean)。
- `SerrePositivity.AlgebraicGeometry.isFiltered_coefficientVCoverModelIndex` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelFinal.lean:34](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelFinal.lean)。
- `SerrePositivity.AlgebraicGeometry.coefficientVCoverModelSmallArrow_finitePresentation` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean:71](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean)。
- `SerrePositivity.AlgebraicGeometry.coefficientVCoverModelSmallArrow_vCover` — [SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean:39](../../SerrePositivity/AlgebraicGeometry/CoefficientVCoverModelStages.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusAugmentedRingCoefficients_exact_iff` — [SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean:106](../../SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean)。

判断：同じ小さい被覆模型の各Noether段にI13を適用し、既存のactual coconeをE14へ渡す。新しい模型は作らない。

<a id="e17"></a>
### E17 — def primeFieldRingHom (R : Type u) [CommRing R] (p : ℕ) (hR : (p : R) = 0) :

区分：G5。素：5〜10行、係数2：10〜20行。依存：なし（既存宣言から）。

```lean
def primeFieldRingHom (R : Type u) [CommRing R] (p : ℕ) (hR : (p : R) = 0) :
    ULift.{u} (ZMod p) →+* R
```

原典：BS17 Lemma 2.12の模型への帰着。固有性の模型の[Stacks 0A0P](https://stacks.math.columbia.edu/tag/0A0P)はG2で供給済み。ここで模型を作り直さない。

既存の宣言と場所：

- `ZMod.castHom` — [.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean:331](../../.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean)。
- `ringChar.dvd` — [.lake/packages/mathlib/Mathlib/Algebra/CharP/Basic.lean:45](../../.lake/packages/mathlib/Mathlib/Algebra/CharP/Basic.lean)。

判断：ZMod.castHom (ringChar.dvd hR) RとULift.ringEquivの合成。零環にもCharP R pを新たに要求しない。

<a id="e18"></a>
### E18 — theorem affineVCover_frobeniusCechExact

区分：G5。素：15〜30行、係数2：30〜60行。依存：[E16](#e16), [E17](#e17)。

```lean
theorem affineVCover_frobeniusCechExact
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hv : IsAffineVCover f) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom f)) p hp hR)
```

原典：BS17 Corollary 2.14のfiltered表示を使う証明段。完全性の保存は[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB)と同じ入力を持つ既存B1。Fubiniの脚の型は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.exists_primeField_vCover_filtered_model` — [SerrePositivity/AlgebraicGeometry/PrimeFieldVCoverFilteredModel.lean:40](../../SerrePositivity/AlgebraicGeometry/PrimeFieldVCoverFilteredModel.lean)。

判断：k=ULift Fp、Rの構造はE17、Sの構造はfとの合成を使ってE16へ代入する。元のRのNoether性・fの有限表示性は結論の仮定にない。

<a id="h01a"></a>
### H01a — def perfectFrobeniusStageMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：12〜24行、係数2：24〜48行。依存：なし（既存宣言から）。

```lean
def perfectFrobeniusStageMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) : A →+* A
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.projectivePrimePowerRingHom` — [SerrePositivity/AlgebraicGeometry/ProjectiveLocalizedFrobenius.lean:19](../../SerrePositivity/AlgebraicGeometry/ProjectiveLocalizedFrobenius.lean)。
- `RingEquiv.ofBijective` — [.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:446](../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean)。

判断：同じFrobeniusのcanonicalな逆のn乗を環準同型として取る。Mathlib Perfectionの逆極限へ構成を変更しない。

<a id="h01b"></a>
### H01b — theorem perfectFrobeniusStageMap_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：4〜8行、係数2：8〜16行。依存：[H01a](#h01a)。

```lean
theorem perfectFrobeniusStageMap_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    perfectFrobeniusStageMap A p hp hA hFA 0 = RingHom.id A
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `RingEquiv.ofBijective` — [.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:446](../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean)。

判断：逆の零乗の恒等則。

<a id="h01c"></a>
### H01c — theorem perfectFrobeniusStageMap_succ_comp (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：12〜24行、係数2：24〜48行。依存：[H01a](#h01a)。

```lean
theorem perfectFrobeniusStageMap_succ_comp (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) :
    (perfectFrobeniusStageMap A p hp hA hFA (n+1)).comp
      (projectivePrimePowerRingHom (A := A) p hp hA) =
        perfectFrobeniusStageMap A p hp hA hFA n
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `RingEquiv.ofBijective` — [.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:446](../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean)。

判断：同じ環同型の逆射と順射の合成が恒等である法則へ代入する。

<a id="h01d"></a>
### H01d — def perfectFrobeniusLimitMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：18〜36行、係数2：36〜72行。依存：[H01b](#h01b), [H01c](#h01c)。

```lean
def perfectFrobeniusLimitMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    FrobeniusDirectLimit A p hp hA →+* A
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `DirectLimit.Ring.lift` — [.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:681](../../.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectSystemMap` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean:19](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean)。

判断：H01cを反復して同じDirectLimit.Ring.liftの互換条件を満たす。

<a id="h01e"></a>
### H01e — theorem perfectFrobeniusLimitMap_comp_of (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：4〜8行、係数2：8〜16行。依存：[H01d](#h01d)。

```lean
theorem perfectFrobeniusLimitMap_comp_of (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) :
    (perfectFrobeniusLimitMap A p hp hA hFA).comp
      (frobeniusDirectLimitOf A p hp hA n) = perfectFrobeniusStageMap A p hp hA hFA n
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `DirectLimit.Ring.lift_comp_of` — [.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:690](../../.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean)。

判断：lift_comp_ofの同じ構造射の式。

<a id="h01f"></a>
### H01f ★ — def perfectFrobeniusLimitEquiv (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：30〜60行、係数2：60〜120行。依存：[H01e](#h01e)。

```lean
def perfectFrobeniusLimitEquiv (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    FrobeniusDirectLimit A p hp hA ≃+* A
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `DirectLimit.Ring.hom_ext` — [.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:695](../../.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitOf_eq_iff` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean:66](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean)。

判断：順射はH01d、逆射は元の第0段の構造射。各段の元の表示で両逆性を確認する。

<a id="h01g"></a>
### H01g — theorem perfectFrobeniusLimitEquiv_comp_of_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

区分：H01。素：4〜8行、係数2：8〜16行。依存：[H01b](#h01b), [H01e](#h01e), [H01f](#h01f)。

```lean
theorem perfectFrobeniusLimitEquiv_comp_of_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    (perfectFrobeniusLimitEquiv A p hp hA hFA).toRingHom.comp
      (frobeniusDirectLimitOf A p hp hA 0) = RingHom.id A
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitOf` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean:54](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimit.lean)。

判断：canonicalな第0段との式をH01b・H01eからそのまま渡す。

<a id="h01h"></a>
### H01h ★ — theorem perfectFrobeniusLimitEquiv_naturality {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

区分：H01。素：25〜50行、係数2：50〜100行。依存：[H01f](#h01f), [H01g](#h01g)。

```lean
theorem perfectFrobeniusLimitEquiv_naturality {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    (perfectFrobeniusLimitEquiv B p hp hB hFB).toRingHom.comp
      (frobeniusDirectLimitMap p hp hA hB f) =
    f.comp (perfectFrobeniusLimitEquiv A p hp hA hFA).toRingHom
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusDirectLimitMap_of` — [SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean:37](../../SerrePositivity/AlgebraicGeometry/FrobeniusDirectLimitMap.lean)。
- `DirectLimit.Ring.hom_ext` — [.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean:695](../../.lake/packages/mathlib/Mathlib/Algebra/Colimit/DirectLimit.lean)。

判断：環の射は元のFrobeniusと可換なので逆とも可換。同じ各段の構造射で照合する。単なる非自然な同型の存在では済ませない。

<a id="h02a"></a>
### H02a — -- 既存宣言をそのまま使用する（新規本体0行）。

区分：H02。素：0〜0行、係数2：0〜0行。依存：なし（既存宣言から）。

```lean
-- 既存宣言をそのまま使用する（新規本体0行）。
def frobeniusAugmentedRingCoefficientsIso
    (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    frobeniusAugmentedRingCoefficients f p hp hA ≅
      (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.frobeniusAugmentedRingCoefficientsIso` — [SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean:91](../../SerrePositivity/AlgebraicGeometry/FrobeniusAugmentedRingCoefficients.lean)。
- `SerrePositivity.AlgebraicGeometry.frobeniusConervePerfectIso_arrow_naturality` — [SerrePositivity/AlgebraicGeometry/FrobeniusConerveArrowNaturality.lean:23](../../SerrePositivity/AlgebraicGeometry/FrobeniusConerveArrowNaturality.lean)。

判断：既に検証済み。増大項と余面・退化の全図式の同型なので、H02の独立なテンソル冪の構成を再実装しない。

<a id="h02b"></a>
### H02b — def perfectFrobeniusOriginalArrowIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

区分：H02。素：15〜30行、係数2：30〜60行。依存：[H01h](#h01h)。

```lean
def perfectFrobeniusOriginalArrowIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f)) ≅
      Arrow.mk (CommRingCat.ofHom f)
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `CategoryTheory.Arrow.isoMk` — [.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/Arrow.lean:215](../../.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/Arrow.lean)。

判断：H01の両端の同型と同じ自然性の可換式をArrow.isoMkへ代入する。

<a id="h02c"></a>
### H02c — def perfectFrobeniusOriginalCechIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

区分：H02。素：8〜16行、係数2：16〜32行。依存：[H02a](#h02a), [H02b](#h02b)。

```lean
def perfectFrobeniusOriginalCechIso {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom f)) p hp hA ≅
      (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `CategoryTheory.CosimplicialObject.augmentedCechConerve` — [.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean:208](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/CechNerve.lean)。

判断：H02aと、既存のconerve関手がH02bを写した同型を合成する。

<a id="h03a"></a>
### H03a — theorem perfectAffineVCover_cechExact {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

区分：H03。素：10〜20行、係数2：20〜40行。依存：[E18](#e18), [H02c](#h02c)。

```lean
theorem perfectAffineVCover_cechExact {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB))
    (hv : IsAffineVCover f) : SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom f)).augmentedCechConerve
```

原典：BS17 Thm 4.1(i)の指定されたn=1・構造層・affine有限族の出口。有限積の各法則は形式化用。

既存の宣言と場所：

- `SerrePositivity.Cech.ringCechExact_iff_of_iso` — [SerrePositivity/HomologicalAlgebra/Cech/Basic.lean:190](../../SerrePositivity/HomologicalAlgebra/Cech/Basic.lean)。

判断：一般のv被覆に対するE18の結果を同じ増大環図式のH02cで移す。条件付きのNoether段の結果を直接最終出力にしない。

<a id="h04a"></a>
### H04a — theorem finitePi_primeCast_eq_zero {ι : Type u} (B : ι → Type u)

区分：H04。素：3〜6行、係数2：6〜12行。依存：なし（既存宣言から）。

```lean
theorem finitePi_primeCast_eq_zero {ι : Type u} (B : ι → Type u)
    [∀ i, CommRing (B i)] (p : ℕ) (hB : ∀ i, (p : B i) = 0) :
    (p : ∀ i, B i) = 0
```

原典：BS17 Thm 4.1(i)の指定されたn=1・構造層・affine有限族の出口。有限積の各法則は形式化用。

既存の宣言と場所：

- `Pi.evalRingHom` — [.lake/packages/mathlib/Mathlib/Algebra/Ring/Pi.lean:175](../../.lake/packages/mathlib/Mathlib/Algebra/Ring/Pi.lean)。

判断：座標ごとのnatCastの式。空の族も同じfunextで処理する。

<a id="h04b"></a>
### H04b — theorem finitePi_primePower_bijective {ι : Type u} (B : ι → Type u)

区分：H04。素：12〜24行、係数2：24〜48行。依存：[H04a](#h04a)。

```lean
theorem finitePi_primePower_bijective {ι : Type u} (B : ι → Type u)
    [∀ i, CommRing (B i)] (p : ℕ) (hp : p.Prime) (hB : ∀ i, (p : B i) = 0)
    (hFB : ∀ i, Function.Bijective
      (projectivePrimePowerRingHom (A := B i) p hp (hB i))) :
    Function.Bijective (projectivePrimePowerRingHom (A := ∀ i, B i) p hp
      (finitePi_primeCast_eq_zero B p hB))
```

原典：BS17 Thm 4.1(i)の指定されたn=1・構造層・affine有限族の出口。有限積の各法則は形式化用。

既存の宣言と場所：

- `Function.Bijective.piMap` — [.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean:625](../../.lake/packages/mathlib/Mathlib/Logic/Function/Basic.lean)。

判断：単射性は座標ごと、全射性は座標ごとの逆像の選択。積の非自明性・CharP・ExpCharを新しく仮定しない。

<a id="h04c"></a>
### H04c — theorem perfectRing_primePower_bijective

区分：H04。素：3〜6行、係数2：6〜12行。依存：なし（既存宣言から）。

```lean
theorem perfectRing_primePower_bijective
    (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) [PerfectRing A p]
    (hA : (p : A) = 0) :
    Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)
```

原典：BS17 Proposition 4.5・Lemma 3.8の完全環への移送。canonicalな段の式・Arrowの自然性は形式化用で、サイト全体の同値を作らない。

既存の宣言と場所：

- `PerfectRing.bijective_frobenius` — [.lake/packages/mathlib/Mathlib/FieldTheory/Perfect.lean:108](../../.lake/packages/mathlib/Mathlib/FieldTheory/Perfect.lean)。
- `SerrePositivity.AlgebraicGeometry.projectivePrimePowerRingHom` — [SerrePositivity/AlgebraicGeometry/ProjectiveLocalizedFrobenius.lean:19](../../SerrePositivity/AlgebraicGeometry/ProjectiveLocalizedFrobenius.lean)。

判断：PerfectRingの定義のp乗写像の全単射性そのもの。

<a id="h04d"></a>
### H04d — theorem cech_exact_of_vCover_perfect

区分：H04。素：15〜30行、係数2：30〜60行。依存：[H03a](#h03a), [H04a](#h04a), [H04b](#h04b), [H04c](#h04c)。

```lean
theorem cech_exact_of_vCover_perfect
    (p : ℕ) [Fact p.Prime]
    {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i) (hf : IsAffineVCoverFamily B f) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve
```

原典：BS17 Thm 4.1(i)の指定されたn=1・構造層・affine有限族の出口。有限積の各法則は形式化用。

既存の宣言と場所：

- `SerrePositivity.AlgebraicGeometry.isAffineVCoverFamily_iff_pi` — [SerrePositivity/AlgebraicGeometry/AffineVCoverFamily.lean:20](../../SerrePositivity/AlgebraicGeometry/AffineVCoverFamily.lean)。
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.cech_exact_of_vCover_perfect` — [formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean:117](../../formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean)。

判断：同じ有限族を積への一射へ送り、零環も許す冪写像の全単射性をH03aへ渡す。利用側のaffineFamilyCechと完全性は定義を展開して同じ型。

## 4. 一本につないだ依存順

1. **nil接続**：N01・N02 → N03、既存Cartesianなnerve → N04 → N05 → N06 → D04・D09。
2. **同じ二重図式**：P01〜P19で座標・被覆・元の係数の全ての射を固定。C01〜C11で同じ複体値の二重図式の軸を比較し、P20・P21で元のPCへ戻す。
3. **循環しない降下の消去**：局所切断F01〜F03 → F04とF07 → D05。D02とF04・F06からD06（細分の消去）を先に証明する。D07はD06の証明には使わない。
4. **相対fppfの合成**：F08・F09の元の細分はflat入力D03を持つ。D06でF10 → F05・F06・C11からF11 → D07。非アフィンなBのΓにはflatを仮定しない。
5. **Noether閉像**：I01〜I03で同じ任意のアフィン底変換後の表示と中心を照合 → I04。I05〜I09で元の閉像の真の包含と中心のIHを作る → I10（元のRG細分、D07、D06、nil反映D09）→ I11 → I12。
6. **RydhからNoetherの環へ**：既存Rydh 3.10の細分と相対アフィン細分にI12・D07・D06を使い、I13。旧来の一般のProperInductiveLevelのrを射影と仮定する道は使わない。
7. **G5**：E01〜E13が元の実際の模型とFrobeniusの二方向の余極限を、脚まで一致するArrowの同型へ運ぶ。各段I13と既存のG2の有限表示・v判定 → E14・E15 → E16。E17で素体の構造を取り、E18で元の任意の環のv被覆の同じAugmentedRingCechExactを出力する。
8. **2h**：H01a〜H01h → H02b。既存χ=H02aと合成してH02c。E18とH02c → H03a。H04a〜H04cと既存の族・積の橋 → H04d **cech_exact_of_vCover_perfect**。

D01のNoetherな試験基底の量化は内部の述語であり、E18とH04dには残らない。G4の中心の完全性はI09の帰納仮定から供給され、最終の追加仮定にしない。

## 5. 利用側との型の接続

H04dの目標は利用側 `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean` の `SerrePositivity.BhattScholze.Perfectoidization.Derived.cech_exact_of_vCover_perfect` と同じ有限族・宇宙・標数・完全性を持つ。利用側のIsVCoverFamilyと⑥のIsAffineVCoverFamilyは、同じValuativeCoverFamilyをfun _ => Trueで定義したもの。利用側のaffineFamilyCechはArrow.mk (RingHom.pi f)の同じ増大conerve。完全性も増大の単射・第0次・全正次数の同じ定義である。H04dへの受け渡しで変えるのは名前の参照だけで、利用側の型は変更しない。

想定する利用側の証明項（**紙のみ。draftsを⑥本体へimportしない**）：

```lean
SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect p B f
  (show SerrePositivity.AlgebraicGeometry.IsAffineVCoverFamily B f from hf)
```

零環・空の族を除外しない。積へCharP _ pやExpChar _ pを無条件で立てず、H04a・H04bの零性とp乗写像の全単射性でH03aを使う。Wittの一般のnや一般の有限射影係数へ主張を広げない。H02aは既存のχとして検証済みで、H02b・H02cはH03への係数移送の法則である。

## 6. 見込みの集計と開始条件

| 範囲 | 内部の署名数 | 素の見込み | 係数2の見込み |
| --- | ---: | ---: | ---: |
| G4 | 71 | 1766〜3489 | 3532〜6978 |
| G5 | 18 | 262〜524 | 524〜1048 |
| H01 | 8 | 109〜218 | 218〜436 |
| H02 | 3 | 23〜46 | 46〜92 |
| H03 | 1 | 10〜20 | 20〜40 |
| H04 | 4 | 33〜66 | 66〜132 |
| 2g-2のimport・module・入口・検証の追記 | — | 100〜250 | 200〜500 |
| 2g-2残り合計（G4・G5のみ） | 89 | **2,128〜4,263** | **4,256〜8,526** |
| 2hのimport・入口・型照合の追記 | — | 30〜100 | 60〜200 |
| 2h残り合計（2g-2には算入しない） | 16 | **205〜450** | **410〜900** |

2g-2の現在の検証済み実測は **19,409行**。既に通った行を係数2で数え直さず、残りにだけ係数を掛ける。

- 素の見込みによる2g-2完成：**21,537〜23,672行**。
- 係数2で補正した2g-2完成：**23,665〜27,935行**。
- 開始条件の上端 **27,935行 > 23,000行**。したがって**Leanには戻らず、ここで報告して止める**。

上限に合わせて係数を小さくしたり、型・範囲を狭めたり、G4の不足を2hへ移したりはしない。旧見込みの上端約22,000行は本紙の分解で置き換える。最も膨らむ箇所はF04〜F06の被覆・局所切断の比較、P12・P19の座標、C01〜C07の同じ三重totalの符号と括り方、I02・I03・I10の元の中心と任意の底変換の照合である。

2hの補正見込みは **410〜900行**。これはH02のχが既に供給された状態からの残りであり、H02を新しく構成した昔の見積もりではない。2hの外枠は今回決めず、2g-2完成時にこの紙と実測を使って調整役が決める。

## 7. 静的な確認と未検証の点

- 全105署名のID・依存先を列挙し、依存グラフが循環しないことを文書生成器で確認した。表示は依存順で、各署名の自由変数は共通略記または明示binderに限る。
- 使う既存のファイルの存在と、宣言名の字面を現在のworktreeで照合し、各参照に場所を付けた。匿名の性質のinstanceは、それを使う名前付きのMorphismPropertyの法則と併記する。
- これはLeanのelaboration・宇宙や型クラスの解決・証明の検証ではない。特にstarの既存同値のobjectの式、固定したcolimitの同型、被覆のreindexには明示的なeqToHomや単位・結合の同型を挿入する可能性があり、★の見込みに含めた。
- 原典の該当箇所はリンクした版で番号を確認した。形式化用の中間補題を原典にある名前付きの定理と装わない。原典の層のHとの比較は追加しない。
- Leanファイルの差分なし。ビルド・監査・root・下流の全ビルドなし。mainの取り込みなし。

一覧：済み1／全体3（うち追加0）。
