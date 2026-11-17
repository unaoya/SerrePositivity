# 5∞-1 標準署名台帳（11-17午後）

<!-- current-signature-state:begin -->
## 最新の進行状態と停止判定

既計上の累計：27,446行。外枠：29,000行。係数：2。
行別の実測は既計上の補助・共有検証組を含みうるため、合計して累計を作り直さない。
この表が進行状態・残り見込みの現在値。後の各節は署名の型・設計・検証履歴を保持する。

|署名ID|状態|実測または部分計上|残り（素）|残り（係数2）|
|---|---|---:|---:|---:|
|R01|verified|—|0〜0|0〜0|
|R02|verified|—|0〜0|0〜0|
|P3-A|verified|45|0〜0|0〜0|
|P3-B1|verified|—|0〜0|0〜0|
|P3-B2a|verified|—|0〜0|0〜0|
|P3-B2b|verified|—|0〜0|0〜0|
|P3-B2c|verified|—|0〜0|0〜0|
|P3-B2d|verified|—|0〜0|0〜0|
|P3-B2e|verified|—|0〜0|0〜0|
|P3-C0|verified|—|0〜0|0〜0|
|P3-C1P|verified|675|0〜0|0〜0|
|P3-C1|verified|157|0〜0|0〜0|
|P3-D|verified|332|0〜0|0〜0|
|P3-E|verified|52|0〜0|0〜0|
|R04|pending|613|250〜400|500〜800|
|R05|pending|—|80〜150|160〜300|
|R06|pending|—|200〜400|400〜800|
|R07|verified|—|0〜0|0〜0|
|R08|pending|—|100〜180|200〜360|
|R09|pending|—|70〜120|140〜240|
|R10a|verified|—|0〜0|0〜0|
|R10b|verified|—|0〜0|0〜0|
|R11a|verified|—|0〜0|0〜0|
|R11b|verified|—|0〜0|0〜0|
|R11c|verified|—|0〜0|0〜0|
|R11d|verified|—|0〜0|0〜0|
|R12a|pending|—|100〜250|200〜500|
|R12b|pending|—|20〜50|40〜100|
|R13a|verified|—|0〜0|0〜0|
|R13b|pending|—|150〜250|300〜500|
|R14|pending|—|60〜110|120〜220|
|R15a|pending|—|80〜140|160〜280|
|R15b|pending|—|20〜80|40〜160|
|R15c|pending|—|20〜90|40〜180|
|R16|deferred_next_checkpoint|—|650〜1200|1300〜2400|
|R17|deferred_next_checkpoint|—|50〜100|100〜200|
|P3-C1PN|verified|—|0〜0|0〜0|
|R09-Cech|pending|—|220〜360|440〜720|
|R15-Unit|pending|—|220〜340|440〜680|
|P3-C1PNV|verified|—|0〜0|0〜0|
|P3-C1PNH|verified|—|0〜0|0〜0|
|P3-C1PNO|verified|—|0〜0|0〜0|
|P3-C1PNON|verified|—|0〜0|0〜0|
|P3-C1PNG|verified|—|0〜0|0〜0|
|P3-C1PNB|verified|—|0〜0|0〜0|
|P3-C1PNQ|verified|—|0〜0|0〜0|
|P3-C1PNC|verified|—|0〜0|0〜0|
|P3-C1PNU|verified|—|0〜0|0〜0|
|P3-C1PNL|verified|—|0〜0|0〜0|
|P3-C1PNR|verified|—|0〜0|0〜0|
|P3-C1PS|verified|400|0〜0|0〜0|
|P3-C1PSG|verified|224|0〜0|0〜0|

<!-- current-signature-state:end -->

これは c4a239f81 の紙を標準化したもの。11-17夕の明示指示により main 35988dd08 を取り込んだ（e2fec6929）。
対象は**今回の再開範囲（元の残り1〜17項）**。過去に検収されたS2〜S6の閉じた出力を
再採番せず、ここにある各署名IDを一つずつ数える。旧「5／8」は以後この台帳の進捗に使わない。
小さい既存構成の法則・証明の分割は親署名内に記録するが、上端200行超は独立署名。

署名52本＝検証済み36本＋未完14本＋別停止点へ切り離す2本。
一覧：済み 36／全体 52（うち追加 17、別停止点 2）。
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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

状態：verified。依存署名：`R01`, `R02`, `P3-B1`, `P3-B2e`, `P3-C0`, `P3-C1PN`, `P3-C1PS`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

状態：verified。依存署名：`R01`, `R02`, `P3-B1`, `P3-B2e`, `P3-C0`, `P3-C1P`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

状態：verified。依存署名：`P3-C1`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

状態：verified。依存署名：`P3-D`。

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：250〜400行。係数2の残り：500〜800行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：80〜150行。係数2の残り：160〜300行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：200〜400行。係数2の残り：400〜800行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：100〜180行。係数2の残り：200〜360行。元の見込み・実測はJSONと検証記録を参照。

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

状態：pending。依存署名：`R06`, `R08`, `R09-Cech`。

素の残り：70〜120行。係数2の残り：140〜240行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：100〜250行。係数2の残り：200〜500行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：20〜50行。係数2の残り：40〜100行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：0〜0行。係数2の残り：0〜0行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：150〜250行。係数2の残り：300〜500行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：60〜110行。係数2の残り：120〜220行。元の見込み・実測はJSONと検証記録を参照。

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

状態：pending。依存署名：`R14`, `R13a`, `R15-Unit`。

素の残り：80〜140行。係数2の残り：160〜280行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：20〜80行。係数2の残り：40〜160行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：20〜90行。係数2の残り：40〜180行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：650〜1200行。係数2の残り：1300〜2400行。元の見込み・実測はJSONと検証記録を参照。

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

素の残り：50〜100行。係数2の残り：100〜200行。元の見込み・実測はJSONと検証記録を参照。

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

## P3-C1Pの途中の検証（324行）

親署名は未完。既計上87行から237行増、累計23,299行。
対象ビルド・小監査1モジュール・23所有宣言、標準三公理のみ。
証拠は `evidence/inf-supply/c1p-prefix324-20261117/manifest.json`。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

## P3-C1Pの途中の検証（493行）

同じ引き戻し射とscaffoldの射の一致、元の指定相対同型のpointed移送まで。
前回から169行増、累計23468行。1モジュール・30宣言、標準三公理のみ。
親署名の指定νとの照合は未完。
一覧：済み 18／全体 36（うち追加 1、別停止点 2）。

## P3-C1Pの途中の検証（数学620行、物理624行）

前回から数学127行増、累計23595行。文献メタデータ4行は外枠から除外。
1モジュール・34所有宣言の対象ビルド・小監査成功、標準三公理のみ。
P3-C1Pは未完。新規の署名案P3-C1PN（指定νとnative区間の類の照合）は報告に置き、
承認済み台帳の分母へは入れていない。
一覧：済み 18／全体 36（うち追加 1、別停止点 2。追加署名案は分母外）。

## 11-17夕：一括洗い直し

P3-C1PNは型と依存を保持して承認済み登録。R09-Cech・R15-Unitは今回の一括事前承認の法則。
各新規署名の補正上端は800行以下。元の署名の主張は変更せず、残り見込みだけを更新。
詳細な全行の型・依存・所在・見込みはreport-bs-infinity-a1-stage0.md末尾。

### P3-C1PN — `leftStraighteningBaseChange_nativeInterval_hom`

状態pending、依存：P3-B1, P3-B2e, P3-C0。
素220〜360、補正440〜720行。

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
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated
```

文献：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の指定構成の照合。独立の原典定理番号を主張しない。
- `relativeSectionBaseChangeRealizationIso_overPre` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/RelativeSectionBaseChangePasting.lean:58`
- `transportSimplexUnderRealization_baseChange_composition` @ `SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimits/SimplexUnderJointComposition.lean:71`
- `kanEnrichedRealizationValueIso_heq_precomp` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:66`
- `straighteningBaseChangeIso_firstVertex` @ `SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/StraighteningBaseChangeRestriction.lean:77`
- `kanEnrichedJointEvaluation_restrict` @ `SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanEnrichedRealizationValue.lean:35`
- `pullbackStrictComparison` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:214`
- `naturalHomVertex` @ `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:501`

### R09-Cech — `weightedSections_toRangeHom_isInvertible`

状態pending、依存：R06, R08。
素220〜360、補正440〜720行。

```lean
∀ {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]
  (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
  [CategoryTheory.Presheaf.IsLocallyInjective J f]
  (O : Presheaf C E) (hO : IsSheaf J O) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
  let e := (nerve.edgeMk (Subfunctor.toRange f)).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  IsInvertibleEdge r
```

文献：HTT 6.2.2.6 の小さい通常 site の集合値Čech解消への特殊化。全族の極限比較の照合。
- `weightedSections_rangeCech_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/WeightedSectionsRelativeCech.lean:39`
- `relativeCechDiagonal_sections_isInvertible` @ `SerrePositivity/InfinityCategories/Sheaves/RelativeCechLocalSections.lean:35`
- `cechConstantCone_isLimit` @ `SerrePositivity/InfinityCategories/Sheaves/CechIndexConstantLimit.lean:55`

### R15-Unit — `exists_discreteSheafificationUnitHom`

状態pending、依存：R14, R13a。
素220〜340、補正440〜680行。

```lean
∀ {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (hJ : Sheafification J SpaceInfinity.{u}),
  let S := presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u)
  let I := (discretePresheafInclusion C).val
  ∃ η : FunctorHom I (nerveMap S ≫ I),
    (∀ P : Cᵒᵖ ⥤ Type u,
      let h₁ := (discretePresheafInclusion C).property.1 P
      let h₂ : (nerveMap S ≫ I).app _ (nerveVertex P) =
          functorVertex (discretePresheaf (S.obj P)) := by
        exact (congrArg (fun v => I.app _ v) (nerveMap_app_mk₀ S P)).trans
          ((discretePresheafInclusion C).property.1 (S.obj P))
      functorHomEvaluate η (nerveVertex P) =
        eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₁) ≫
          discretePresheafHom (CategoryTheory.toSheafify J P) ≫
          eqToHom (congrArg (fun v => HomotopyCategory.mk v) h₂.symm)) ∧
    IsIso (SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp I (nerveMap S ≫ I) (sheafificationFunctor J hJ) η)
```

文献：HTT 6.2.2.7・5.5.4.15 の離散係数と小さい通常siteの場合。指定したMathlibの層化単位を全関手射として実現する法則。
- `isLocalEquivSet_toSheafify` @ `SerrePositivity/InfinityCategories/Sheaves/SetLocalEquivalence.lean:38`
- `resizedNatTransMap` @ `SerrePositivity/InfinityCategories/Project/HomotopyDiagramComparison/CatInfinity/StrictCoherentNatTrans.lean:30`
- `kanDiscretePresheafMap_vertex` @ `SerrePositivity/InfinityCategories/Sheaves/DiscretePresheafInclusion.lean:40`
- `sheafifyUnitHom` @ `SerrePositivity/InfinityCategories/Sheaves/SheafifyUnit.lean:35`

一覧：済み 18／全体 39（うち追加 4、別停止点 2）。


## P3-C1PNV（11-17夕承認）

名前：`leftStraightening_firstVertexTransport_underValue`。依存：なし。P3-C1PNが依存する。

```lean
∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
  let C := TransportSimplexCategory B
  let j := edgewiseEnrichedInfinityMap (LeftFibrationObject B)
  let b := leftFibrationEdgewiseFirstVertexBaseChange B
  let h : j ≫ (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
      leftStraighteningCoherentMap C) =
      b ≫ (edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve C)) ≫
        leftStraighteningCoherentMap C) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection,
      Category.assoc]
  let γ := (transportSimplexUnderRealizationIso B).precomp j ≪≫
    ((transportSimplexUnderBaseChangeRealizationIso B).precomp j).symm ≪≫
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h) ≪≫
    (leftStraighteningCoherentMap_oppositeIso C).precomp b
  let X := edgewiseOrdinaryObject (leftFibrationObjectOf p)
  HEq ((leftClassificationSimplexIso p).symm ≪≫
      leftStraighteningInfinityDiagram_firstVertexTransportIso p)
    (functorIsoValue γ (coherentNerveVertex X))
```

素190〜270行、係数2で380〜540行。既存宣言と場所・原典はJSONと報告末尾。


P3-C1PNV：対象ビルド・9宣言の小監査成功、標準三公理のみ。実測171行、累計24,004行。


## P3-C1PNH（11-17夕、構成の制限則）

```lean
∀ {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J)
    {F G : KanDiagramObject J} (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
    kanFunctorHomCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      (precomposeFunctorHom ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))
        (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated)) =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨H ⋙ F.val, trivial⟩) (G := ⟨H ⋙ G.val, trivial⟩)
        (Functor.whiskerLeft H η)).toTruncated
```

依存：なし。素60〜100行、補正120〜200行。既存参照・原典はJSONと報告。


P3-C1PNH：実測78行、対象ビルドと3宣言の小監査成功（標準三公理のみ）。累計24,082行。


## P3-C1PNO（既存の係数反転の成分分解）

```lean
∀ {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X : C),
  let Z := edgewiseOrdinaryObject X
  let z := coherentNerveVertex Z
  let j := edgewiseEnrichedInfinityMap C
  let hf : (j ≫ D.realization).app _ z =
      functorVertex (kanDiagramCoherentNerve (D.evaluate X)) := by
    change D.realization.app _ ((coherentNerveMap (edgewiseEnrichedRight C)).app _ z) = _
    rw [coherentNerveMap_vertex]
    exact D.realization_vertex X
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  (eqToIso (congrArg (fun v => HomotopyCategory.mk v) hf)).symm ≪≫
    functorIsoValue D.oppositeRealizationIso z ≪≫
    eqToIso (congrArg (fun v => HomotopyCategory.mk v) (D.opposite.realization_vertex Z)) =
  (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR Z).symm ≪≫
    kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL Z
```

依存なし。素160〜250行、補正320〜500行。既存参照と原典はJSONと報告。


## P3-C1PNON（指定された反転比較の自然性）

```lean
∀ {J : Type u} [SmallCategory J] {F G : KanDiagramObject J}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget),
  let D := kanDiagramUniversalEnriched J
  let hR := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseRight ((D.obj j).obj Y.val).obj)
  let hL := fun j (Y : SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (KanDiagramObject J)) =>
    isQCatEquivalence_of_trivialKanFibration (edgewiseLeft ((D.obj j).obj Y.val).obj)
  let o := fun P : KanDiagramObject J =>
    (kanEnrichedRealizationValueIso D.edgewiseRightComparison hR (edgewiseOrdinaryObject P)).symm ≪≫
      kanEnrichedRealizationValueIso D.edgewiseLeftComparison hL (edgewiseOrdinaryObject P)
  Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated ≫
    (o G).hom = (o F).hom ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (G := ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩)
        (Functor.whiskerRight η SSet.opFunctor)).toTruncated
```

依存なし。素160〜250行、補正320〜500行。既存参照はJSONと報告。


## P3-C1PNG（指定三成分の合成の照合）

```lean
∀ {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p],
  (leftClassificationSimplexIso p).symm ≪≫
    leftStraighteningInfinityDiagram_firstVertexTransportIso p = firstVertexNativeCoefficientIso p
```

依存P3-C1PNV・P3-C1PNO・P3-C1PNON。素200〜350行、補正400〜700行（成分の略記も含む）。


P3-C1PNO・P3-C1PNON：実測115・138行、対象ビルドと5・13宣言の小監査成功。累計24,335行。


## P3-C1PNB（元の底変換比較の値の照合）

```lean
∀ {B D : SSet.{u}} {J : Type u} [Category.{u} J]
      (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (p : LeftFibrationObject B),
    HEq (kanEnrichedRealizationValueIso (relativeSectionBaseChangeComparison k A)
      (relativeSectionBaseChangeComparison_isQCatEquivalence k A) p)
      (functorIsoValue (relativeSectionBaseChangeRealizationIso k A) (coherentNerveVertex p))
```

依存なし。素60〜120行、補正120〜240行。既存宣言と場所はJSONと報告。


P3-C1PNB：対象ビルド・1宣言の小監査成功、標準三公理のみ。実測53行、累計24,388行。


## P3-C1PNQ（指定反転比較の添字制限）

```lean
∀ {I J : Type u} [SmallCategory I] [SmallCategory J] (H : I ⥤ J) (F : KanDiagramObject J),
    diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H (F.val ⋙ kanObjectOpFunctor))
      ((kanDiagramOppositeValueIso F).precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H))) =
    kanDiagramOppositeValueIso ⟨H ⋙ F.val, trivial⟩
```

依存P3-C1PNH・P3-C1PNON。素120〜220行、補正240〜440行。


P3-C1PNG：二ファイル計320行、対象ビルド・所有31宣言の小監査成功。累計24,708行。


## P3-C1PNC（元の単体切断係数の自然変換による表示）

```lean
∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let F : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)), trivial⟩
    let G : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨transportSimplexFunctor k ⋙
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p), trivial⟩
    HEq (simplexSectionBaseChangeCoefficient p k).hom
      (Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := F) (G := G) (simplexSectionNativeBaseChange p k)).toTruncated)
```

依存P3-C1PNB。素200〜350行、補正400〜700行。完全な既存参照はJSON。


## P3-C1PNU（元のunder制限と単体切断の底変換の長方形）

```lean
∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    simplexSectionNativeBaseChange p k ≫
      Functor.whiskerLeft (transportSimplexFunctor k)
        ((nativeUnderJointComparison B).app (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    (nativeUnderJointComparison D).app (leftFibrationObjectOf (pullback.snd p k)) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p)
```

依存：P3-C1PNC・P3-C1PNG・P3-B2c。素200〜350行、補正400〜700行。
既存参照：
- `transportSimplexUnderTransformation_baseChange` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/SimplexUnderBaseChangeNaturality.lean:88
- `relativeFunctorBaseChangeForward_overPre` @ SerrePositivity/InfinityCategories/Project/FibrationAuxiliaries/FunctorCategories/RelativeFunctorBaseChangeNaturality.lean:89
- `relativeFunctorOverPre_comp` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorOverPrecomposition.lean:56
- `simplexSectionNativeTarget_eq` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexSectionNativeBaseChange.lean:41

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。元の制限と底変換の合成の特殊な照合。
新しい数学・仮定・chooseなし。元の定義域等式による移送、既存のunder三角形、底変換と制限の可換式だけを使用する。


## P3-C1PNL（指定pullbackの二つの底変換との長方形）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    Functor.whiskerLeft H
      ((relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B))).app
        (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1 ≫
      (relativeSectionBaseChangeComparison lD (strictTransportDomains (TransportSimplexCategory D))).app
        (leftFibrationObjectOf q) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p)
```

依存：P3-C0・P3-B2b。素120〜220行、補正240〜440行。
既存参照：
- `pullbackStrictComparison_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:334
- `leftStraighteningBaseChangePullbackData` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePullbackData.lean:27
- `relativeFunctorBaseChangeForward_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorBaseChange.lean:58
- `relativeFunctorOverPre_uncurry` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorSquarePost.lean:68

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。指定pullbackの二座標と相対uncurryの既存の合成則の特殊化。
既存のαのuncurryの公式を同じ二つの射影へ合成する照合。親ファイルはこの枝の新規ファイルでmainには存在しない。既存本文を変えずprivate補題を追記する。


## P3-C1PNR（反転前の指定長方形の実現と相殺）

```lean
∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let t := U.map (nerveMap H)
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let ν₀ := (FunctorIso.precomp
        (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
      (simplexSectionBaseChangeCoefficient p k).symm ≪≫
      nativeUnderCoefficientIso q ≪≫ (nativeBaseChangeCoefficientIso q).symm
    let hsrc : t ≫ leftStraighteningCandidate p₀ = kanDiagramCoherentNerve Fh.val := by
      change t ≫ kanDiagramCoherentNerve (leftStrictTransportFunctor p₀) =
        kanDiagramCoherentNerve (H ⋙ leftStrictTransportFunctor p₀)
      exact kanDiagramCoherentNerve_precomp H _
    ν₀.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := Fh) (G := Fr) α).toTruncated
```

依存：P3-C1PNU・P3-C1PNL・P3-C1PNH・P3-C1PNC・P3-C1PNG。素180〜300行、補正360〜600行。
既存参照：
- `simplexUnderNativeBaseChange_square` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexUnderNativeBaseChange.lean:78
- `leftStraighteningBaseChange_native_pullback_square` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:632
- `kanDiagramNaturalTransformationHom_comp` @ SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanDiagramNaturalTransformationComposition.lean:43
- `kanDiagramNaturalTransformationHom_precomp` @ SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/KanDiagramNaturalTransformationPrecomposition.lean:47
- `simplexSectionBaseChangeCoefficient_native_hom` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SimplexSectionNativeBaseChange.lean:125

HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の法則。上下の元の自然変換の長方形を実現し可逆な底変換を相殺する照合。
新しい数学・choose・仮定なし。前合成と自然変換の実現の既存法則、指定長方形U/L、同型の相殺だけを使用する。private αの同じ型を保持するため親の枝だけの新規ファイルにprivate補題として追記。


P3-C1PNC・U・L：対象3モジュール・所有53宣言の小監査成功、標準三公理のみ。実測160＋119＋68＝347行、累計25,173行。


P3-C1PNR：実測180行、対象1モジュール・所有40宣言の小監査成功。標準三公理のみ。累計25,353行。


## P3-C1PS（同じscaffoldでの指定pointed比較）

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
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
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
    ∃ e : FunctorIso (i ≫ R₀.pointedMap) (i ≫ Rr.pointedMap),
      e.postcomp pointedSpaceProjection =
        (functorIsoOfEq (FunctorIso.precomp ν (U.map r)) R₀.pointedMap_projection.symm
          Rr.pointedMap_projection.symm).precomp i
```

依存：P3-C1PN・R01・R02・P3-C0。素200〜350行、補正400〜700行。
既存参照：
- `scaffoldPointedRelativeIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:456
- `oppositeHomComparison_at_natural` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:536
- `oppositeComparisonPointedBase` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:141
- `pointedIsoOfProjectedPrism` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:581
- `leftUnstraighteningEdgeLiftFamily_projection` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:58

HTT §3.3.2・特に3.3.2.8、Kerodon §5.6（Tag 028T）の指定構成の法則。このscaffold上での指定pointed比較への特殊化。
既存のscaffold制限比較・反転Homの指定比較・全写像空間の持ち上げを同じ辺で合成する照合。新しい数学・仮定・choose・main既存本文の変更なし。


P3-C1PSの再利用先を補記（型・依存・見込みは変更なし）：
- `relativeFunctorVertexIsoImage_postcomp` @ SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/RelativeFunctorVertexIsoProjection.lean:34
- `tautScaffold_map` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementFunctor.lean:97
- `tautScaffold_baseMap` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementBaseChange.lean:73
- `leftUnstraighteningEdgeLiftFamily_zero` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:49
- `leftUnstraighteningEdgeLiftFamily_one` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean:67

全写像空間の持ち上げは元の同じ族で始点・射影を保ち、終点はその族から定義される。追加のchoose置き換えは不要。
一覧：済み 29／全体 51（うち追加 16、別停止点 2）。


P3-C1PN：元の型のまま対象1モジュール・48宣言の小監査成功。標準三公理のみ。素220〜360／補正440〜720に対し実測260行。累計25,613行。


### P3-C1PSの短い射影の計算法則（11-17夜）

新規補助ファイル `SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean`。既存の `relativeFunctorVertexIsoImage_postcomp` を再利用し、同じ指定同型を前合成・端点移送したときの射影を計算する。200行未満で、Sの証明分割として数え、署名の型・見込みは変えない。新しい選択・仮定はない。

```lean
lemma functorIsoEq_precomp {A D X : SSet.{u}} {f g : A ⟶ X}
    (h : f = g) (i : D ⟶ A) :
    FunctorIso.precomp (eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) h)) i =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k))
        (congrArg (fun k => i ≫ k) h))
```

```lean
lemma relativeFunctorVertexIsoImage_transport_projection
    {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f g : A ⟶ E) (hf : f ≫ p = a) (hg : g ≫ p = a)
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (i : D ⟶ A) {f' g' : D ⟶ E} (hf' : i ≫ f = f') (hg' : i ≫ g = g')
    (hp : f' ≫ p = g' ≫ p) :
    (functorIsoOfEq ((relativeFunctorVertexIsoImage p a f g hf hg e).precomp i) hf' hg').postcomp p =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) hp)
```

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。


### P3-C1PSの補助部分の検証（11-17夜）

新規補助ファイル `CartesianFibrations/RelativeFunctorIsoImageTransport.lean` の5宣言の対象ビルド・小監査成功、標準三公理のみ。
相対同型の射影の本体の宣言と、前合成・底変換・端点移送・prismの既存の構成の法則を再利用した。
新しい選択・仮定はなく、mainの既存の本文は変更していない。
実測**100行**。Sは未完のまま、検証済みの証明分割として累計に一度だけ加算する。
累計25,613 → **25,713行**。
Sの残りは素150〜300行・補正300〜600行とする。元の補正上端700に対し、検証済み100＋残り補正600＝700で着手枠を保っている。
次の判定25,713＋600＝26,313で今回の区切りの範囲内。補助ファイル全体は200行未満なので署名の数は増やさない。
主な射影公式にはHTT §3.3.2 special属性、Kerodon Tag 028Tはdocstringに特殊化として記載。
証拠：`evidence/inf-supply/c1ps-projection-1117/manifest.json`。

一覧：済み 30／全体 51（うち追加 16、別停止点 2）。


## P3-C1PSG（νに独立な三つの指定pointed比較）

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
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
    let ε := intervalMappingEdgeOfVertex y
    let FH := kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor)
    let FR := kanDiagramCoherentNerve (Fr.val ⋙ kanObjectOpFunctor)
    let v := U.map (tautScaffold (Fh.val ⋙ kanObjectForget))
    let f₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫ pullback.fst pointedSpaceProjection FH
    let f₁ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫
      leftUnstraighteningEdgeLiftMap FH FR ε ≫ pullback.fst pointedSpaceProjection FR
    let fT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val ≫
      pullback.fst pointedSpaceProjection FR
    ∃ (h₀ : (i ≫ R₀.pointedMap) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
      (h₁ : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
      (hT : (i ≫ Rr.pointedMap) ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection),
      ∃ a₀ : FunctorIso (i ≫ R₀.pointedMap) f₀,
      ∃ a₁ : FunctorIso f₁ fT,
      ∃ aT : FunctorIso (i ≫ Rr.pointedMap) fT,
        a₀.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₀) ∧
        a₁.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₁) ∧
        aT.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)
```

依存：R01・R02・P3-C0。素180〜300行、補正360〜600行。
既存参照：
- `scaffoldPointedRelativeIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:456
- `scaffoldPullbackData_eq` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:392
- `oppositeHomComparison_at_natural` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:536
- `oppositeComparisonPointedBase` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftStraighteningBaseChangePointedPrism.lean:141
- `relativeFunctorVertexIsoImage_transport_projection` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean:45
- `relativeFunctorBaseChangeForward_vertexIso` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/RelativeFunctorIsoImageTransport.lean:71
- `tautScaffold_map` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementFunctor.lean:97
- `tautScaffold_baseMap` @ SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/SimplicialReplacementBaseChange.lean:73

HTT §3.3.2（特に3.3.2.8）・Kerodon §5.6（Tag 028T）の既存構成の法則。scaffold制限同型と元の全写像空間の区間族の三成分の照合。
νに依存しない三つの指定pointed比較を記録する。既に検証済みのC1P内の証明分割を使い、未完のC1P本体には依存しない。新しい数学・仮定・choose・mainの既存本文の変更なし。

P3-C1PSは一般のνに対する短い証明分割の型も数え、残り見込みを素140〜300・補正280〜600へ更新（既に加算した100行は除外）。三署名の次のまとまりは25,713＋600＋600＋300＝27,213で区切り内。

Sの再見込みは型の記載を含め素200〜380・補正400〜760（各補正上端800以下）。三署名の着手判定は25,713＋600＋760＋300＝27,373で29,000以内。

## 最新の検証記録（P3-C1PSG・P3-C1PS・P3-C1P、再開後）

build-11：対象ビルド5,599 jobs成功、小監査1モジュール61宣言、標準三公理のみ。対象のソースSHAを終了時・記録時に照合。三署名の主張と指定νを保ち、計算上限を上げずに完了。
新規計上579行＝PSG 224＋S 300＋P 55（輸入・docstringを含む保守的な差分）。既計上のPの補助620行・Sの補助100行を二度数えない。累計26,292行。
見込み（最後の素／補正）との比較：PSG 180〜300／360〜600に対し224、Sの残り200〜380／400〜760に対し300、Pの残り90〜150／180〜300に対し55。Sのkernelの時間切れは一般の合成則への分割と三端点の結合順序を署名に揃えたCategory.assocの明記で解消。
次のC1は補正上端360なので26,292＋360＝26,652で29,000以内。C1の下書き152行を検証する。
一覧：済み 33／全体 52（うち追加 17、別停止点 2）。

## 最新の検証記録（P3-C1）

build-4：対象ビルド5,604 jobs、小監査1モジュール3宣言、標準三公理のみ。ソースSHA照合済み。素90〜180・補正180〜360に対し実測157行（輸入・docstring込み）。累計26,449行。主な宣言にHTT special属性、Kerodon特殊化はdocstring。
一覧：済み 34／全体 52（うち追加 17、別停止点 2）。

P3-Dの短い四法則の型・依存・既存参照は報告末尾に記録。全体の素の再見込み200〜380、補正400〜760。26,449＋760＝27,209で29,000以内。各法則は200行未満なので署名数は増やさない。

## 最新の検証記録（P3-D）

build-7：対象ビルド5,610 jobs成功、小監査4モジュール16宣言、標準三公理のみ。現行ソースSHA一致。診断用出力を除き、計算上限不変。素200〜380・補正400〜760に対し332行。累計26,781。
次のEの補正上端220を足して27,001で29,000以内。
一覧：済み 35／全体 52（うち追加 17、別停止点 2）。

## 最新の検証記録（P3-E）

build-3：対象ビルド5,611 jobs成功、小監査1モジュール1宣言、標準三公理のみ。現行ソースSHA一致。素50〜110・補正100〜220に対し52行。累計26,833。
次のR04の補正上端800を足して27,633で29,000以内。
一覧：済み 36／全体 52（うち追加 17、別停止点 2）。

## R04の検証済みの証明分割（署名本体は未完）

三本218行（76＋72＋70）が、同時の対象ビルド5,634 jobs・小監査3モジュール6宣言を通過。標準三公理のみ、現行SHA一致。中間極限の二つの選択は元のchooseから動かさず、指定極限比較の合成則で消去する。指定引き戻し分類同型は同じ元の表現上の同型の作用へ戻せる。主な宣言に文献のspecial属性、Kerodonの特殊化はdocstring。
累計26,833＋218＝27,051。R04本体（元の余単位に沿う輸送錐と頂点射の照合）は未完。今は残りにも安全側に元の補正上端800を保持し、27,051＋800＝27,851で区切り内。既計上218行はR04の完成時に二度数えない。
一覧：済み 36／全体 52（うち追加 17、別停止点 2）。
