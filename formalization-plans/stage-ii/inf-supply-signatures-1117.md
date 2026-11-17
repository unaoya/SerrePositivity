# 5∞-1 標準署名台帳（11-17午後）

これは c4a239f81 の紙を標準化したもの。main は取り込んでいない。
対象は**今回の再開範囲（元の残り1〜17項）**。過去に検収されたS2〜S6の閉じた出力を
再採番せず、ここにある各署名IDを一つずつ数える。旧「5／8」は以後この台帳の進捗に使わない。
小さい既存構成の法則・証明の分割は親署名内に記録するが、上端200行超は独立署名。

署名36本＝検証済み18本＋未完16本＋別停止点へ切り離す2本。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。
追加1は11-17夕承認のP3-C1P。着手判定22,975＋800＝23,775行。以前の35署名の表は履歴として保持。

## 最新の検証記録（P3-B1）

この検証組は107行。検証済み累計22,686行。
対象ビルド・小監査：1モジュール・6宣言、標準三公理のみ。
証拠：`/tmp/is-w1/p3-b1/production/target-audit-result.json`（ソースSHAを照合）。元の見込みはJSONのoriginal欄にも保持。

## 最新の検証記録（P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0）

この検証組は199行。検証済み累計22,885行。
対象ビルド・小監査：2モジュール・18宣言、標準三公理のみ。
証拠：`/tmp/is-w1/p3-b2/production/target-audit-result.json`（ソースSHAを照合）。元の見込みはJSONのoriginal欄にも保持。

## 最新の検証記録（P3-B2e）

この検証組は90行。検証済み累計22,975行。
対象ビルド・小監査：1モジュール・6宣言、標準三公理のみ。
証拠：`/tmp/is-w1/p3-b2e/production/target-audit-result.json`（ソースSHAを照合）。元の見込みはJSONのoriginal欄にも保持。

## P3-C1Pの途中の検証

証明分割2本、87行の対象ビルド・小監査が成功。累計23,062行。
親署名の主張は未完のため済み18／36のまま。全体の残り見込みはまだ短縮しない。

## 型の共通環境

下記は**紙の型であり、未実装の署名のLean elaboration成功を主張しない**。
すべての型の自由な宇宙変数は `universe u`。各型は明示的な∀から始まり、暗黙のC/E/P/Qを置かない。
既存の短い名前は次の名前空間で読む（特にIsPresentableはHTTのもの）。

```lean
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
```

P3の型のelaborationで使う局所instanceも、次の通り固定する。

```lean
local instance signaturePullbackLeft {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩
```

P3の引き戻しのLeftFibration instanceは、既存 `leftFibrations.pullback_snd` と
`LeftFibration.mem` により各局所スコープで供給する。追加仮定ではない。
P3-C0は以前の紙で略記した標準pullback比較とそのuliftの証拠を独立署名へ露出しただけ。
P3-C1や最終P3-Eへ任意のpullback比較を新たに仮定しない。

原典対応は特殊な模型・既存構成の法則を含む。「独立番号なし」とした法則に、原典の
同名定理があると主張しない。属性を付ける段階でも適切なpartialと理由を保持する。

## 規模と停止点（段0時点の履歴）

検証済み累計22,534行は固定。既に通った署名の残り見込みは0行（過去の実測を消していない）。

| 範囲 | 素の残り | 係数2の残り | 検証済みとの累計 |
|---|---:|---:|---:|
| P3-A〜E（B2・Cの分割を含む） | 940〜1,550 | 1,880〜3,100 | 24,414〜25,634 |
| 第3〜15項の未完署名全体 | 2,390〜4,310 | 4,780〜8,620 | 27,314〜31,154 |
| 第16・17項 | 700〜1,300 | 1,400〜2,600 | 今回の停止点から分離 |
| 分離前の全体 | 3,090〜5,610 | 6,180〜11,220 | 28,714〜33,754 |

上端が29,000行を超えるため、11-17の規則どおり第16・17項を**次の停止点**へ分離する。
その型は弱めず、次の紙・外枠は取り込みの後に決める。今回その新外枠を独断で設定しない。
分離しても補正上端31,154行は29,000行より2,154行高い。この点も調整役の判断材料として
明示する。最後の外枠を上げたり、補正係数を変えたり、指定比較を短縮したりしない。
実装は指定順で実測を追い、28,500行で途中報告する。S7・R2・R3は再開しない。

## 現在の実測（P3-A検証後）

検証済み累計22,579行。P3-A実測45行。元の見込みは200〜350行（補正400〜700行）。
未完の補正後残り4,380〜7,920行。係数2は変えず、次のまとまりごとに着手前の上端を判定する。
P3-B1は22,579＋300＝22,879行で着手可。

## 指定構成とchooseの点検

先の `inf-supply-choose-1117.md`・`.json` は変更せず保持している。255候補の全列挙を
今回の型付き署名へ接続して点検した。今回必要な**追加の既存本文の置き換えは0件**。
下表は現ソースの式を点検したもの。行数・公理・公開型の新しいv3b検査を行ったという意味ではない。
現ソースSHAは `inf-supply-signatures-1117-choice-check.json` に保存する。

| 記号・既存の定義 | 指定構成との両立／現在の扱い | 新たな置き換え |
|---|---|---|
| N1 `leftCoherentTransportDirectComparison` | 指定scaffoldの相対制限同型を含む強い存在から選択。済み第1項と接続。 現式：`scaffoldCoherentComparison p` | 不要（N1〜N5は承認済み修正を保持） |
| N2 `smallLeftUnstraighteningComparisonOfFunctorIso` | η.homそのものを使い、指定同型の射を保持する。 現式：`smallUnstraighteningFunctorHom η.hom` | 不要（N1〜N5は承認済み修正を保持） |
| N3 `weightedSections_nativeShapeLimitIso` | 同じ元の余単位に沿うvalueTransportの錐。 現式：`weightedSections_valueTransport O hE P` | 不要（N1〜N5は承認済み修正を保持） |
| N4 `nativeWeightedSections_leftLimitIso` | 同じ元の余単位に沿うvalueTransportの錐。 現式：`nativeWeightedSections_valueTransport` | 不要（N1〜N5は承認済み修正を保持） |
| N5 `weightedSections_leftLimitIso` | 同じ元の余単位に沿うvalueTransportの錐。 現式：`nativeWeightedSections_valueTransport` | 不要（N1〜N5は承認済み修正を保持） |
| C6 `leftStraighteningInfinityDiagram_representationIso` | FFによる指定eの逆像。map_preimageで元のeとの両立が仕様に残る。 現式：`preimageVertexIso e` | 不要（N1〜N5は承認済み修正を保持） |
| C7 `leftStraighteningSectionJointDiagram_baseChangeIso` | 同じjoint比較の逆像。既存firstVertex照合法則が指定比較との一致を保持。 現式：`preimageVertexIso e` | 不要（N1〜N5は承認済み修正を保持） |
| C8 `weightedSections_discrete` | 中間極限は元の値定義の選択を保つ。P3・R04〜R06で同じ錐の一意性による相殺を証明する。 現式：`Classical.choose hd` | 不要（N1〜N5は承認済み修正を保持） |
| C9 `sheafifyUnitHom` | 同じhJから同じ反射・単位を使う。別の反射を選んで同一視しない。 現式：`(Classical.choice hJ).unit` | 不要（N1〜N5は承認済み修正を保持） |
| C10 `KanEnrichedDiagramComparison.realizationIso` | jointComparisonIsoは実際の辺の類のasIso。curryして同じ族を保持。P3-Aはその合成則を証明する。 現式：`jointComparisonIso` | 不要（N1〜N5は承認済み修正を保持） |

`directKanUnstraighteningComparison` の弱い存在からの選択は、指定比較の同定には使わない。
前の表の推移的importerは8,054本で、置換の候補にはしない。P3-B2bは実際のUnder.postから
自然変換を直接定義する。P3-C0は指定二座標のpullback.liftを使う。新しい弱いchooseを入れない。
既存本文の変更は計画していないため、他レーンの既存ファイルへの変更も計画していない。
新しい置換や他レーンのファイルの変更が必要になった時は停止して報告する。

## 依存グラフの検査

`python3 formalization-plans/stage-ii/check-inf-supply-signatures-1117.py` を実行した。
Kahn法で35頂点・50辺を全て処理し、**循環なし**。未知の依存ID、重複ID、重複宣言名、
2倍補正の不一致も0件。既存宣言の全参照は、記載したパス・行に宣言名があることを検査済み。
検査結果と参照ソースSHAは `inf-supply-signatures-1117-check.json`。
これは**依存DAGと台帳の検査**であり、未実装の数学の証明やLeanの型検査ではない。

主要な順序は P3-A → P3-B1/B2 → P3-C0/C1 → P3-D → P3-E → R04 → R05 → R06 →
R08 → R09 → R12a/b → R13b → R14 → R15a/b/c。R16 → R17は別停止点へ切り離した。
検証済みのR01・R02・R07・R10a/b・R11a〜d・R13aは境界の再利用として残す。

## 署名ごとの完全な型と依存

### R01 — `scaffoldCoherentComparison_scaffoldIso`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p],
FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (universalScaffold p) ≫
        scaffoldCoherentComparison p)
      ((SSet.uliftFunctor.{u + 1, u}).map (tautScaffold (leftStrictTransportDiagram p)) ≫
        leftCoherentTransportComparison p)
```

使う既存の宣言：

- `scaffoldCoherentComparison_scaffoldIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean`。

### R02 — `leftStraighteningInfinityReconstruction_representationComparison`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p)),
let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)
    let a := leftStraighteningInfinityDiagram_representationIso p R
    let f := smallLeftUnstraighteningLift R.diagram R.comparison ≫ smallUnstraighteningFunctorHom a.inv
    ∃ hf : f ≫ q = p,
      Nonempty (VertexIso
        (relativeFunctorVertex q p (leftStraighteningInfinityReconstruction p)
          (leftStraighteningInfinityReconstruction_projection p))
        (relativeFunctorVertex q p f hf))
```

使う既存の宣言：

- `leftStraighteningInfinityReconstruction_representationComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean`。

### P3-A — `kanEnrichedDiagramRealizationIso_trans`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：200〜350行、補正400〜700行。実測45行。

原典：HTT §1.1.5、Kerodon §3.1（Tag 00SZ）。既存のcoherent実現の合成則で、独立の原典番号はない。

```lean
∀ {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  {J : Type u} [Category.{u} J] {D E F : KanEnrichedDiagram C J}
  (η : KanEnrichedDiagramComparison D E) (θ : KanEnrichedDiagramComparison E F)
  (χ : KanEnrichedDiagramComparison D F)
  (hχ : ∀ j, χ.component j = KanEnrichedComparison.trans (η.component j) (θ.component j))
  (hη : ∀ j (X : C), IsQCatEquivalence ((η.component j).val X))
  (hθ : ∀ j (X : C), IsQCatEquivalence ((θ.component j).val X))
  (hχe : ∀ j (X : C), IsQCatEquivalence ((χ.component j).val X)),
  η.realizationIso hη ≪≫ θ.realizationIso hθ = χ.realizationIso hχe
```

使う既存の宣言：

- `jointRealizationIso_trans` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/JointRealizationComposition.lean:94`
- `kanEnrichedComparisonEdge_hom_trans` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedComparisonEdgeComposition.lean:59`
- `kanEnrichedComparisonTriangle_first_diagonal` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedComparisonFaces.lean:72`
- `kanEnrichedComparisonTriangle_second_diagonal` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedComparisonFaces.lean:151`
- `kanEnrichedComparisonTriangle_long_diagonal` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedComparisonFaces.lean:230`

既存jointRealizationIso_trans（JointRealizationComposition.lean:94）を再利用。χをjointComparisonTransへ同定するだけ。旧見込み200〜350行との差は既存APIの照合漏れによる。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedDiagramRealizationComposition.lean`。

### P3-B1 — `relativeSectionBaseChangeRealizationIso_overPre`

状態：verified。依存署名：`P3-A`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[100, 150]、補正[200, 300]。実測は同じ検証組P3-B1で107行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} {J : Type u} [Category.{u} J]
  (k : D ⟶ B) {A T : Jᵒᵖ ⥤ Over D} (η : A ⟶ T)
  (hη : ∀ j (p : LeftFibrationObject D),
    IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))))
  (hηk : ∀ j (p : LeftFibrationObject B),
    IsQCatEquivalence (relativeFunctorOverPre p.val.hom
      ((Functor.whiskerRight η (Over.map k)).app (Opposite.op j)))),
  relativeSectionBaseChangeRealizationIso k T ≪≫
    relativeSectionRealizationComparisonIso (Functor.whiskerRight η (Over.map k)) hηk =
  (relativeSectionRealizationComparisonIso η hη).precomp (leftFibrationInfinityBaseChange k) ≪≫
    relativeSectionBaseChangeRealizationIso k A
```

使う既存の宣言：

- `relativeFunctorBaseChangeForward_overPre` @ `SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/FunctorCategories/RelativeFunctorBaseChangeNaturality.lean:89`
- `relativeSectionBaseChangeRealizationIso` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionBaseChangeComparison.lean:53`
- `relativeSectionRealizationComparisonIso` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionJointComparison.lean:201`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionBaseChangePasting.lean`。

### P3-B2a — `transportSimplexUnderDomainMap_baseChange`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[20, 30]、補正[40, 60]。実測は同じ検証組P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0で199行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} (k : D ⟶ B) (s : TransportSimplexCategory D),
  nerveMap (Under.post (X := s) (transportSimplexFunctor k)) ≫
    transportSimplexUnderDomainMap ((transportSimplexFunctor k).obj s) =
  transportSimplexUnderDomainMap s
```

使う既存の宣言：

- `transportSimplexUnderDomainMap_baseChange` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:33`（今回検証済み）
- `transportSimplexUnderDomainMap` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderDomains.lean:53`

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean`。

### P3-B2b — `transportSimplexUnderBaseChangeTransformation`

状態：verified。依存署名：`P3-B2a`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[20, 40]、補正[40, 80]。実測は同じ検証組P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0で199行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} (k : D ⟶ B),
  transportSimplexUnderDomains D ⋙ Over.map k ⟶
    (transportSimplexFunctor k).op ⋙ transportSimplexUnderDomains B
```

使う既存の宣言：

- `transportSimplexUnderBaseChangeTransformation` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:48`（今回検証済み）
- `transportSimplexUnderDomainTransformation` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderDomains.lean:164`

ρのs成分のleftはnerveMap (Under.post (X := s) (transportSimplexFunctor k))。NatTransをこの式で直接定義し、存在命題からchooseしない。小さい成分の等式の法則もここで保持。

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean`。

### P3-B2c — `transportSimplexUnderTransformation_baseChange`

状態：verified。依存署名：`P3-B2a`, `P3-B2b`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[20, 40]、補正[40, 80]。実測は同じ検証組P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0で199行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} (k : D ⟶ B),
  let ρ := transportSimplexUnderBaseChangeTransformation k
  Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k) =
    ρ ≫ Functor.whiskerLeft (transportSimplexFunctor k).op
        (transportSimplexUnderDomainTransformation B) ≫
      eqToHom (transportSimplexDomainFunctor_baseChange k)
```

使う既存の宣言：

- `transportSimplexUnderTransformation_baseChange` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:88`（今回検証済み）
- `transportSimplexUnderDomainTransformation` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderDomains.lean:164`

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean`。

### P3-B2d — `transportSimplexUnderBaseChangeComparison_isQCatEquivalence`

状態：verified。依存署名：`P3-B2b`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[30, 50]、補正[60, 100]。実測は同じ検証組P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0で199行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} (k : D ⟶ B)
  (s : TransportSimplexCategory D) (p : LeftFibrationObject B),
  IsQCatEquivalence (relativeFunctorOverPre p.val.hom
    ((transportSimplexUnderBaseChangeTransformation k).app (Opposite.op s)))
```

使う既存の宣言：

- `transportSimplexUnderBaseChangeComparison_isQCatEquivalence` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:107`（今回検証済み）
- `relativeFunctorOverPre_isQCatEquivalence_of_initialComparison` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionInitialRestriction.lean:43`

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean`。

### P3-B2e — `transportSimplexUnderRealization_baseChange_composition`

状態：verified。依存署名：`P3-A`, `P3-B2c`, `P3-B2d`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[30, 60]、補正[60, 120]。実測は同じ検証組P3-B2eで90行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {B D : SSet.{u}} (k : D ⟶ B),
  let ρ := transportSimplexUnderBaseChangeTransformation k
  let ηD := Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k)
  let ηB := Functor.whiskerLeft (transportSimplexFunctor k).op
      (transportSimplexUnderDomainTransformation B) ≫
    eqToHom (transportSimplexDomainFunctor_baseChange k)
  ∀ (hηB : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (ηB.app (Opposite.op j))))
    (hηD : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (ηD.app (Opposite.op j)))),
  relativeSectionRealizationComparisonIso ηB hηB ≪≫
    relativeSectionRealizationComparisonIso ρ
      (fun j p => transportSimplexUnderBaseChangeComparison_isQCatEquivalence k j p) =
    relativeSectionRealizationComparisonIso ηD hηD
```

使う既存の宣言：

- `transportSimplexUnderRealization_baseChange_composition` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/SimplexUnderJointComposition.lean:71`（今回検証済み）
- `relativeSectionRealizationComparisonIso` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionJointComparison.lean:201`

hηB/hηDは適用で既存の初頂点の制限・係数移送から証明する。第3項の最終仮定には足さない。

置き場所：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/SimplexUnderJointComposition.lean`。

### P3-C0 — `leftStraighteningBaseChangePullbackData`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み：[40, 80]、補正[80, 160]。実測は同じ検証組P3-B2a,P3-B2b,P3-B2c,P3-B2d,P3-C0で199行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  { t : pullback q lD ⟶ pullback p lB //
      t ≫ pullback.fst p lB = pullback.fst q lD ≫ pullback.fst p k ∧
      t ≫ p₀ = r ≫ nerveMap H ∧
      IsPullback t r p₀ (nerveMap H) ∧
      IsPullback (U.map t) (U.map r) (U.map p₀) (U.map (nerveMap H)) }
```

使う既存の宣言：

- `leftStraighteningBaseChangePullbackData` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePullbackData.lean:27`（今回検証済み）
- `cartesianRestrict_diagramIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonRestriction.lean:27`

P3-Cの標準pullbackの前提計算を独立に明示した。tは指定二座標のpullback.liftで構成する。htUも証明する。任意のtやhtUを最終型に仮定しない。

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePullbackData.lean`。

### P3-C1P — `leftStraighteningBaseChange_pointedPrism`

状態：pending。依存署名：R01, R02, P3-B1, P3-B2e, P3-C0。

素の残り：250〜400行。係数2の残り：500〜800行。

原典：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）。指定pointed比較の照合で、独立の原典番号はない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  ∃ W : (Δ[1] : SSet.{u+1}) ⊗ U.obj (pullback q lD) ⟶ PointedSpaceInfinity.{u},
    prismEndpoint 0 (U.obj (pullback q lD)) ≫ W = R₀.pointedMap ∧
    prismEndpoint 1 (U.obj (pullback q lD)) ≫ W = Rr.pointedMap ∧
    W ≫ pointedSpaceProjection = (Δ[1] ◁ U.map r) ≫ functorEdgePrism e
```

使う既存の宣言：

- `scaffoldCoherentComparison_scaffoldIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30`
- `leftStraighteningInfinityReconstruction_representationComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34`
- `smallFiberTransportRepresentationVertexIso_unique` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:26`

置き場所：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean`。

11-17夕、調整役・ユーザー承認。報告66ad88611の型をそのまま登録。元のνとその指定辺を保つ。

### P3-C1 — `leftStraighteningBaseChange_transportWitness`

状態：pending。依存署名：`R01`, `R02`, `P3-B1`, `P3-B2e`, `P3-C0`, `P3-C1P`。

素の残り：310〜420行。係数2の残り：620〜840行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  ∃ a : VertexIso (transportWitnessVertex R₀) (transportWitnessVertex Rr),
    R₀.diagramIso Rr a = ν
```

使う既存の宣言：

- `scaffoldCoherentComparison_scaffoldIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/ScaffoldCoherentComparisonRestriction.lean:30`
- `leftStraighteningInfinityReconstruction_representationComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/StraighteningReconstructionRepresentationComparison.lean:34`
- `smallFiberTransportRepresentationVertexIso_unique` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonCoherence.lean:26`

200行超。数学的な芯。νそのものを表す全空間の表現の点aを構成する。可縮性だけからνの表現可能性を仮定しない。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningBaseChange_transportWitness.lean`。

### P3-D — `leftStraighteningRepresentation_baseChange_firstVertex`

状態：pending。依存署名：`P3-C1`。

素の残り：120〜220行。係数2の残り：240〜440行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  (leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map lD) ≪≫
    leftStraighteningInfinityDiagram_firstVertexTransportIso q ≪≫
    nerveCoherentTransportRepresentationIso r ((R.nativeRestrict k).nativeRestrict lD) =
  ((leftStraighteningInfinityDiagram_representationIso p R).precomp (U.map k)).precomp
    (U.map lD)
```

使う既存の宣言：

- `nerveCoherentTransportRepresentationIso_comp_diagramIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/NerveRepresentationComparisonLaw.lean:27`
- `cartesianRestrict_diagramIso` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RepresentationComparisonRestriction.lean:27`

上端200行超のため独立署名。標準aへの一意性と同じ初頂点の制限の式を使用。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningRepresentation_baseChange_firstVertex.lean`。

### P3-E — `leftStraighteningInfinityDiagram_representationIso_baseChange`

状態：pending。依存署名：`P3-D`。

素の残り：50〜110行。係数2の残り：100〜220行。

原典：HTT §3.3.2（特に3.3.2.8）、Kerodon Corollary 5.6.0.6（Tag 028T）。指定構成の法則で、独立した原典の補題番号はない。

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  ∀ R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p),
  leftStraighteningInfinityDiagram_baseChangeIso p k ≪≫
    leftStraighteningInfinityDiagram_representationIso (pullback.snd p k) (R.nativeRestrict k) =
  (leftStraighteningInfinityDiagram_representationIso p R).precomp
    ((SSet.uliftFunctor.{u+1,u}).map k)
```

使う既存の宣言：

- `functorIso_precomp_injective` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/StraighteningBaseChangeRestriction.lean:101`
- `transportSimplexFirstVertexMap_ulift_isLocalization` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/Localization/LocalizationUlift.lean:22`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/leftStraighteningInfinityDiagram_representationIso_baseChange.lean`。

### R04 — `rightKanIndexTransport_valueHom`

状態：pending。依存署名：`P3-E`, `R02`。

素の残り：250〜450行。係数2の残り：500〜900行。

原典：HTT 5.1.5.6の双対、Kerodon Definition 7.3.1.2（Tag 02Y9）。指定余単位に沿う値の比較の法則。

```lean
∀ {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
  (β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌),
  let b := (e.postcomp G).hom ≫
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  ∀ (s : RightKanConeTransport δ O G (functorHomHomotopy b) v)
    (t : RightKanConeTransport δ' O G β v)
    (hs : IsLimitCone s.cone) (ht : IsLimitCone t.cone),
  eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      s.cone_vertex.symm) ≫
    (rightKanLimitVertexIsoOfFunctorIso e O v s.cone t.cone hs ht).hom ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
      t.cone_vertex) = 𝟙 (HomotopyCategory.mk (G.app _ v))
```

使う既存の宣言：

- `rightKanLimitVertexIsoOfFunctorIso` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/RightKanLimitVertexTransport.lean:35`

200行超。指定e・元の余単位の類・同じ錐を保持。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/RightKanIndexTransportValue.lean`。

### R05 — `weightedSections_nativeShapeLimitIso_hom_eq_globalComparison`

状態：pending。依存署名：`R04`。

素の残り：80〜150行。係数2の残り：160〜300行。

原典：HTT 5.1.5.6（双対）、Kerodon Definition 7.3.1.2（Tag 02Y9）。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : IsPresentable E)
  {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
  (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O)
  (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β)
  (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
  (t : RightKanConeTransport (nativeSetShapeOppositeYoneda C) O G β P)
  (ht : IsLimitCone t.cone)
  (d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
  (hd : IsLimitCone d),
  (weightedSections_nativeShapeLimitIso O hE P d hd).hom =
    functorHomEvaluate (weightedSections_nativeShape_comparison O hE β hβ).hom P ≫
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj E))
      t.cone_vertex.symm) ≫ (limitVertexIso t.cone d ht hd).hom
```

使う既存の宣言：

- `weightedSections_nativeShape_comparison_transport_vertex` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsGlobalComparisonVertex.lean:32`
- `rightKanHomUniversalIso_hom_fac` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/KanExtensions/UniversalProperty.lean:83`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_nativeShapeLimitIso_hom_eq_globalComparison.lean`。

### R06 — `weightedSections_discrete_map`

状態：pending。依存署名：`R05`。

素の残り：200〜400行。係数2の残り：400〜800行。

原典：HTT 5.1.5.6（双対）。指定値比較の自然性の法則。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (O : Presheaf C E) (hE : IsPresentable E) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hP : HasLimit (sectionsOfDiagram P O))
  (hQ : HasLimit (sectionsOfDiagram Q O)),
  let e := (nerve.edgeMk φ).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  Truncated.HomotopyCategory.homMk r ≫ (weightedSections_discrete O hE P hP).hom =
    (weightedSections_discrete O hE Q hQ).hom ≫
      Truncated.HomotopyCategory.homMk (sectionsOf_map φ O hP hQ).toTruncated
```

使う既存の宣言：

- `weightedSections_discrete` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsDiscrete.lean:34`
- `sectionsEquivalenceNatural` @ `SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsNaturality.lean:78`

上端200行超。draftsの元の値の選択を保持。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_discrete_map.lean`。

### R07 — `weightedSections_relativeCechDiagonalHom`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 6.2.2.6、小さい通常のsiteの相対Čech対角。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {P Q : Cᵒᵖ ⥤ Type u},
∀ (f : P ⟶ Q) {E : SSet.{u+1}} [Quasicategory E]
 (O : Presheaf C E)
 (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
FunctorHom
  (opFunctor.map (strictCoherentDiagram (relativeCechDiagram f ⋙ kanDiscretePresheafFunctor C) ≫
    kanDiagramRealization Cᵒᵖ) ≫ weightedSections O hE)
  (SSet.const ((weightedSections O hE).app _
    (opObjEquiv.symm (functorVertex (discretePresheaf P)))))
```

使う既存の宣言：

- `relativeCechDiagonal_sections_isInvertible` @ `SerrePositivity/InfinityCategories/Sheaves/RelativeCechLocalSections.lean:35`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsRelativeCechDiagonal.lean`。

### R08 — `weightedSections_relativeCechDiagonalHom_isIso`

状態：pending。依存署名：`R06`, `R07`。

素の残り：100〜180行。係数2の残り：200〜360行。

原典：HTT 6.2.2.6、小さい通常のsiteのČech層条件への特殊化。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (O : Presheaf C E) (hO : IsSheaf J O) (hE : IsPresentable E),
  IsIso (weightedSections_relativeCechDiagonalHom f O hE)
```

使う既存の宣言：

- `relativeCechDiagonal_sections_isInvertible` @ `SerrePositivity/InfinityCategories/Sheaves/RelativeCechLocalSections.lean:35`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/weightedSections_relativeCechDiagonalHom_isIso.lean`。

### R09 — `sections_localEquiv_iso_space`

状態：pending。依存署名：`R06`, `R08`。

素の残り：250〜420行。係数2の残り：500〜840行。

原典：HTT 6.2.2.6・5.5.4.20の局所対象の筋。小さい通常のsiteと離散な局所同値への特殊化。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

使う既存の宣言：

- `rangeCechCocone_isColimit` @ `SerrePositivity/InfinityCategories/Sheaves/LocalEquivalenceImageReduction.lean:46`
- `cechConstantCone_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/CechIndexConstantLimit.lean:55`

200行超。元のrangeの増大射と元のφとの同定も含む。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/sections_localEquiv_iso_space.lean`。

### R10a — `siteLiftElementsShapeIso`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (P : Cᵒᵖ ⥤ Type u),
(SSet.uliftFunctor.{u + 1, u}).obj (nerve P.Elements) ≅
      nerve (siteLiftPresheaf P).Elements
```

使う既存の宣言：

- `siteLiftElementsShapeIso` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftElementsShape.lean:24`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftElementsShape.lean`。

### R10b — `siteLiftElementsShapeIso_naturality`

状態：verified。依存署名：`R10a`。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q),
(siteLiftElementsShapeIso P).hom ≫ nerveMap (siteLiftPresheafMap φ).mapElements =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements) ≫
        (siteLiftElementsShapeIso Q).hom
```

使う既存の宣言：

- `siteLiftElementsShapeIso` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftElementsShape.lean:24`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftElementsShape.lean`。

### R11a — `siteLiftSectionsCone`

状態：verified。依存署名：`R10a`, `R10b`。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {E : SSet.{u+1}},
∀ (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)),
JoinCone (nativeSetSectionsDiagram (siteLiftPresheaf P) ((asSmallSiteShapeIso C).inv ≫ O))
```

使う既存の宣言：

- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean`。

### R11b — `siteLiftSectionsCone_vertex`

状態：verified。依存署名：`R10a`, `R10b`。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {E : SSet.{u+1}},
∀ (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram P O)),
(siteLiftSectionsCone P O c).vertex = c.vertex
```

使う既存の宣言：

- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean`。

### R11c — `siteLiftSectionsCone_restrict`

状態：verified。依存署名：`R10a`, `R10b`。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {E : SSet.{u+1}},
∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (O : Presheaf C E)
    (c : JoinCone (sectionsOfDiagram Q O)),
joinMap (𝟙 _) (nerveMap (siteLiftPresheafMap φ).mapElements) ≫
        (siteLiftSectionsCone Q O c).val =
      (siteLiftSectionsCone P O
        (SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.restrictSectionsCone φ O c)).val
```

使う既存の宣言：

- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean`。

### R11d — `siteLiftSectionsCone_isLimit_iff`

状態：verified。依存署名：`R10a`, `R10b`。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 4.1.1.8、同値な添字による極限の移送。宇宙持ち上げの法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {E : SSet.{u+1}},
∀ [Quasicategory E]
    (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E) (c : JoinCone (sectionsOfDiagram P O)),
IsLimitCone (siteLiftSectionsCone P O c) ↔ IsLimitCone c
```

使う既存の宣言：

- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean`。

### R12a — `restrictSectionsCone_isLimit_of_localEquiv`

状態：pending。依存署名：`R09`, `R10a`, `R10b`, `R11a`, `R11b`, `R11c`, `R11d`。

素の残り：100〜250行。係数2の残り：200〜500行。

原典：HTT 6.2.2.6、表現可能関手による極限の検出（Kerodon §7.1）。任意の準圏係数への反映。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (c : JoinCone (sectionsOfDiagram Q O)) (hc : IsLimitCone c),
  IsLimitCone (SetWeight.restrictSectionsCone φ O c)
```

使う既存の宣言：

- `isLimitCone_of_covariantRepresentableInfinity` @ `SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/RepresentableLimitCharacterization.lean:52`
- `siteLiftSectionsCone_isLimit_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SiteLiftSectionsCone.lean:76`

上端200行超。係数のpresentabilityを仮定しない。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/restrictSectionsCone_isLimit_of_localEquiv.lean`。

### R12b — `sections_localEquiv_iso`

状態：pending。依存署名：`R12a`。

素の残り：20〜50行。係数2の残り：40〜100行。

原典：HTT 6.2.2.6・5.5.4.20。draftsの元の局所同値の型。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C E) (hO : IsSheaf J O)
  (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
  IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated
```

使う既存の宣言：

- `sectionsMap_isInvertible_iff` @ `SerrePositivity/InfinityCategories/Sheaves/SieveSectionsCriterion.lean:62`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/sections_localEquiv_iso.lean`。

### R13a — `discretePresheafHom`

状態：verified。依存署名：なし。

素の残り：0〜0行。係数2の残り：0〜0行。

原典：HTT 5.5.6.28。元の離散前層埋め込みのHom作用の正規化。

```lean
∀ {C : Type u} [SmallCategory C],
∀ {P Q : Cᵒᵖ ⥤ Type u},
∀ (φ : P ⟶ Q),
FunctorHom (discretePresheaf P) (discretePresheaf Q)
```

使う既存の宣言：

- `sectionsEquivalenceNatural` @ `SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsNaturality.lean:78`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/DiscretePresheafHom.lean`。

### R13b — `discreteHom_isLocalForHom_of_localEquiv`

状態：pending。依存署名：`R09`, `R13a`。

素の残り：150〜250行。係数2の残り：300〜500行。

原典：HTT 5.5.4.20・6.2.2.6。小さい通常のsiteの離散重みでの局所Hom。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u}
  (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ)
  (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O),
  IsLocalForHom (discretePresheafHom φ) (functorVertex O)
```

使う既存の宣言：

- `sectionsEquivalenceNatural` @ `SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsNaturality.lean:78`

上端200行超。全族G8比較を使用。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/discreteHom_isLocalForHom_of_localEquiv.lean`。

### R14 — `localEquiv_of_sheafifyIso`

状態：pending。依存署名：`R13b`。

素の残り：60〜110行。係数2の残り：120〜220行。

原典：HTT 5.5.4.15・6.2.2.7。指定された反射による局所同値の反転。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (hφ : IsLocalEquivSet J φ),
  IsInvertibleEdge ((nerve.edgeMk φ).map
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)).toTruncated
```

使う既存の宣言：

- `reflective_isIso_map_iff_localHom` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/ReflectiveInvertedHom.lean:80`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/localEquiv_of_sheafifyIso.lean`。

### R15a — `sheafifyDiscreteFunctorIso`

状態：pending。依存署名：`R14`, `R13a`。

素の残り：200〜330行。係数2の残り：400〜660行。

原典：HTT 5.5.6.28・6.2.2.7。集合値層化と0切り捨ての層化の比較の特殊な表示。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  FunctorIso
    ((discretePresheafInclusion C).val ≫ sheafificationFunctor J hJ)
    (nerveMap (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)) ≫
      (discretePresheafInclusion C).val)
```

使う既存の宣言：

- `isSheaf_discretePresheaf_iff` @ `SerrePositivity/InfinityCategories/Sheaves/DiscreteSheafCondition.lean:48`
- `reflective_isIso_map_iff_localHom` @ `SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/ReflectiveInvertedHom.lean:80`

200行超。元のordinary単位の全自然変換のmateを作る。点ごとの同型を集めない。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/sheafifyDiscreteFunctorIso.lean`。

### R15b — `sheafify_discrete_eq`

状態：pending。依存署名：`R15a`。

素の残り：20〜80行。係数2の残り：40〜160行。

原典：HTT 5.5.6.28、draftsの同名の型。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  FunctorIso (sheafify J hJ (discretePresheaf P))
    (discretePresheaf (((presheafToSheaf J (Type u)).obj P).obj))
```

使う既存の宣言：

- `isSheaf_discretePresheaf_iff` @ `SerrePositivity/InfinityCategories/Sheaves/DiscreteSheafCondition.lean:48`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/sheafify_discrete_eq.lean`。

### R15c — `sheafify_discrete_eq_hom_fac`

状態：pending。依存署名：`R15a`, `R15b`, `R13a`。

素の残り：20〜90行。係数2の残り：40〜180行。

原典：HTT 5.5.6.28・5.5.4.15。元の反射単位を保つ比較の法則。

```lean
∀ {C : Type u} [SmallCategory C],
∀ (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u})
  (P : Cᵒᵖ ⥤ Type u),
  sheafifyUnitHom J hJ (discretePresheaf P) ≫ (sheafify_discrete_eq J hJ P).hom =
    discretePresheafHom (CategoryTheory.toSheafify J P)
```

使う既存の宣言：

- `sheafifyUnitHom` @ `SerrePositivity/InfinityCategories/Sheaves/SheafifyUnit.lean:35`
- `sheafificationReindexSpecifiedMateIso_mate` @ `SerrePositivity/InfinityCategories/Sheaves/SheafificationSiteSpecifiedComparison.lean:53`

元のsheafifyUnitHomを使う。指定全mateのhom_facを保つ既存のsite比較と同じ手法を用いる。必要な随伴のHom普遍性は指定の反射から証明して渡す。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/sheafify_discrete_eq_hom_fac.lean`。

### R16 — `coverage_basis_pullback_isLimit`

状態：deferred_next_checkpoint。依存署名：なし。

素の残り：650〜1200行。係数2の残り：1300〜2400行。

原典：HTT 6.2.2.6・6.2.2.7の生成被覆系の判定。通常圏での基準はMathlib Presieve.isSheaf_coverage。∞版への接続自体が残る数学。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (K : Coverage C) (F : Presheaf C E)
  (hF : ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
    IsLimitCone (restrictionCone F (Sieve.generate R)))
  {U V : C} (R : Presieve U) (hR : R ∈ K.coverings U) (f : V ⟶ U),
  IsLimitCone (restrictionCone F ((Sieve.generate R).pullback f))
```

使う既存の宣言：

- `coveragePullbackRefinement_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/CoveragePullbackRefinement.lean:32`
- `restrictionCone_inf_isLimit_iff_of_pullbacks` @ `SerrePositivity/InfinityCategories/Sheaves/SieveIntersectionDescent.lean:23`

200行超。29,000行の最後の外枠の規則により別停止点へ切り離す。前提計算42行だけ検証済み、主張は未完。

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/coverage_basis_pullback_isLimit.lean`。

### R17 — `isSheaf_toGrothendieck_iff`

状態：deferred_next_checkpoint。依存署名：`R16`。

素の残り：50〜100行。係数2の残り：100〜200行。

原典：HTT 6.2.2.6・6.2.2.7、Mathlib Presieve.isSheaf_coverageの∞版。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
∀ (K : Coverage C) (F : Presheaf C E),
  IsSheaf K.toGrothendieck F ↔
    ∀ (U : C) (R : Presieve U), R ∈ K.coverings U →
      IsLimitCone (restrictionCone F (Sieve.generate R))
```

使う既存の宣言：

- `isSheaf_toGrothendieck_iff_universallyDescending` @ `SerrePositivity/InfinityCategories/Sheaves/CoverageUniversalDescent.lean:23`

置き場所（新規の場合の案）：`SerrePositivity/InfinityCategories/Sheaves/isSheaf_toGrothendieck_iff.lean`。

一覧：済み 18／全体 36（うち追加 1、別停止点 2）。
