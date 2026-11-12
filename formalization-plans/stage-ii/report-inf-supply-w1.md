# IS-W1 段0：G8 の四角形・G14・G9 の洗い出し

2026-11-12、③-a。**停止点0。実装・ビルド・監査は未実施。**
main `ef145b288`（指定の `52682962c` を含む）から、既存 worktree `SerrePositivity-bs-classical` で枝 `math/inf-supply` を切った。準備メモ `inf-supply-w1-bs-classical-preparation.md`（0850731ff）を使い、IS-W1 §0〜§1、IF-G2-finish §1、IF-G2 §1・§3・§4、`infinity-g2-progress.md` の末尾二節、BS の SheafGenerators・SpaceValued と入口表 §4・§4.1 を現行ソースに照合した。

以下の型は紙の案で、名前空間・標準的な端点移送を省略している。Lean の型検査済みとは扱わない。新規ファイル・宣言名も案。既存 G1・G2 の宣言や drafts の型は変えず、必要な比較を入力の仮定に足さない。

## 1. 既存宣言との照合

パスは `SerrePositivity/InfinityCategories/` 以下。既存の `Project/` の宣言は新しい正規の名前で再利用する。旧 F2・HomotopyLimits のパスや deprecated alias は新規 import に使わない。

| 現行ファイル | 再利用する宣言・確認した範囲 |
| --- | --- |
| `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationMappingSpan.lean`・`RightFibrationHomComparison.lean` | `rightFibrationMappingTotal`、`rightFibrationMappingHomProjection` の自明 Kan fibration、`rightFibrationMappingSection`、`rightFibrationMappingSection_projection`、`rightFibrationHomComparison`。**選んだ切断の終点に関する自然性は仕様にない** |
| 同節の `FixedApexLimitCriterion.lean`・`NormalizedConeRestrictionComparison.lean` | `fixedApexConeHomComparison` は上の選んだ切断を使う。固定端点模型と、`normalizedSectionEndpointComparison_restrict` による制限との整合性は既存 |
| `Project/SetWeightedTensors/SetSectionsLimitNaturality.lean` | `limitConeEndpointComparison`、`limitConeMapIsoOfConeFamilyIso`、`limitConeMap_homMk_eq_of_coneFamilyIso`、`sectionsConeFamilyRestriction_fromSections`。最後の等式は全パラメータの厳密な制限比較だが、G8 の比較との照合までは含まない |
| 同系列の `SetSectionsSieveNaturality.lean`・`SetSectionsSieveHomotopy.lean` | `sieveEvaluationTriangle`、`sieveEvaluation_postcomposeIso`、`sieveEvaluation_postcompose_homMk_eq`。評価錐側の全写像空間の比較は完成済み。これを②の完成とは数えない |
| 同系列の `SetSectionsNaturality.lean` | 正本 `elementsComparisonNatural`、`sectionsEquivalenceNatural`、`tensorSpaceFunctor_setWeightHomNatural`。`elementsToReplacement_naturality`・`elementsWeighted_naturality`・`tensorSpaceFunctor_diagramHom_weight_naturality` も再利用 |
| 同系列の `SetSectionsUnstraightening.lean` | `relativePreIso`、`unstraighteningPrecompositionIso`・`unstraighteningPinchedPrecompositionIso`。相対空間内の頂点同型から**前合成の全族**へ移す部分は作り直さない |
| `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/DiagramSectionsCone.lean` | `coherentDiagramSectionsCone` とその頂点の等式。G8 が実際に使う切断の錐を保持する |

進捗記録の「残る数学的な一歩」と現行の型は一致した。`limitConeMap_homMk_eq_of_coneFamilyIso` の入力は、二つの**写像そのもの**を固定端点模型へ送った後の `FunctorIso`。各頂点での Ho 等式だけではこの入力を満たさない。

## 2. 段1：②――切断制限と G8 の後段

### 型案と必要な新しい比較

まず一般の right fibration の補題を二つに分ける。

1. **底上の射との比較**：`r : E → B`、`s : E' → B` が right fibrations、`q : E → E'` が `q ≫ s = r` を満たすとき、任意の `c : E₀`・`x : B₀` に対し、
   `comparison(r,c,x) ≫ fiberMap(q,x)` と `comparison(s,q(c),x)` の **FunctorIso** を構成する。始域は `pinchedHom x (r c)`、終域は `vertexFiber s x`。`s(q(c)) = r(c)` による端点移送は明示する。
2. **錐の辺との比較**：`B` は quasicategory、`e : Edge c₀ c₁` は全空間の辺として、

   ```text
   FunctorIso
     (rightFibrationHomComparison r c₀ x)
     (PinchedInterval.postcompose x [e.map r] ≫
       rightFibrationHomComparison r c₁ x)
   ```

   を作る。始域は `pinchedHom x (r c₀)`、終域は `vertexFiber r x`。`[e.map r]` は Ho(B) の同じ指定辺の類。全写像間の同型なので、任意のパラメータからの前合成後にも使える。頂点ごとにホモトピーを選んで束ねる方法は採らない。

底上の射では span の全空間間の実射を作り、射影と評価の可換性を示す。錐の辺では合成三角形の族を保持した共通 span を作る。自明 Kan fibration の持ち上げで、既存の選んだ切断と共通 span から得る切断を**全パラメータのまま**比較する。既存切断の定義は変更しない。固定頂点・固定端点の模型へ移す際も、射影と端点の等式を追跡する。

その後、篩 S ⊆ h_U、任意の前層 F、presentable E、M ∈ E、指定極限錐 cS・cU について、G8 の既存定義の後段を次のように名前付けする。

- `t := spaceTensorData hE M`、`gP := diagram P (F ≫ t.hom)`。
- `ΓP` は `sectionsEquivalenceNatural P (F ≫ t.hom)` の終域である、宇宙を持ち上げた**実切断空間**。
- `λP : ΓP → pinchedHom M cP.vertex` は、既存 G8 の本文の `coherentDiagramSectionsCone gP` から指定錐への比較、`spaceUniverseValueEquivalence`、表現可能値の比較を**同じ順・同じ選択**で合成した後段。
- `ρ : Γ(h_U) → Γ(S)` は要素の圏の射に沿う実切断制限。unstraightening の底変換同型・小さい模型・宇宙変更による移送も定義に明示する。

狙う独立の結論は

```text
FunctorIso (ρ ≫ λS) (λU ≫ PinchedInterval.postcompose M [sieveSectionsMap …])
```

である。比較の原料は上の一般補題と `sectionsConeFamilyRestriction_fromSections`、評価三角形。`limitConeMap_homMk_eq_of_coneFamilyIso` へ渡す固定端点模型内の全族同型を先に作り、その後に Ho の等式を得る。さらに、既存 `tensorSpaceFunctor_setWeightHomNatural` の順射が「随伴比較 ≫ sectionsEquivalenceNatural ≫ λP」であることを、本文に沿う等式として確認する。別の容易な同値へ置き換えて自然性を主張しない。

### 不足と規模

不足は、(a) 辺と底上の射を扱う共通 span の全族、(b) 選んだ切断と評価への比較、(c) 固定端点模型への移送、(d) G8 の実際の後段・宇宙変更・表現可能値の射との照合。既存の評価三角形や全族同型から Ho 等式へ落とす補題は完成済みとして使う。

**6〜9新規ファイル、約1,600〜2,600行**を見込む。最大の不確実性は (a)(b) で、原典の自然性を現行の選択された模型の全族へ接続する部分。span の端点別の存在だけで規模を小さく見積もらない。

配置案：一般部分を `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationMappingOverNaturality.lean`・`RightFibrationMappingEdgeFamily.lean`・`FixedEndpointConeComparisonNaturality.lean` など。G8 固有の接続は HTT の空間テンソル・presentable 圏の主題として `HTT/PresentableInfinityCategories/SetWeightSectionsLimitComparison.lean` など。ファイルの分割は証明後の実量に合わせる。

## 3. 段2：①――篩包含の相対比較と四角形

底 B を固定し、`φ := S.functorInclusion` とする。二つの射は「φ の unstraightening 上の像の指定頂点と `elementsComparisonNatural S.functor` の合成」と「`nerveMap φ.mapElements` と `elementsComparisonNatural (yoneda.obj U)` の合成」。前者は `unstraighteningPrecompositionIso` が使う辺の像と同じものを、小さい模型へ移して使う。両方を底上の射 `f,g : a ⟶ b` として定義し、射影の等式も証明する。

第一の型案は、同じ相対関手空間における

```text
VertexIso (relativeFunctorVertex b.hom a.hom f.left f.w)
          (relativeFunctorVertex b.hom a.hom g.left g.w)
```

の**構成**。これを入力に要求する定理は完成と扱わない。`elementsToReplacement_naturality`・`elementsWeighted_naturality` に、反転係数・weighted unstraightening の比較をつなぎ、同じ底を保ったまま像の指定頂点へ比較する。`relativePreIso` と `unstraighteningPinchedPrecompositionIso` を再利用して、①を実切断制限 ρ までの全族の同型にする。

最終型案を正確に固定するため、既存の

```text
eS := tensorSpaceFunctor_setWeightHomNatural S.functor hE M F cS hcS
eU := tensorSpaceFunctor_setWeightHomNatural (yoneda.obj U) hE M F cU hcU
α  := PinchedInterval.precompose (functorVertex F) [sieveTensorEdge S hE M]
β  := PinchedInterval.postcompose M [sieveSectionsMap S F cS hcS cU hcU]
```

を使う。狙う四角形は **Ho(SpaceInfinity) における `[α ≫ eS.hom] = [eU.hom ≫ β]`**。括弧は元の Kan 空間間の写像から作る coherent edge の Ho 類を表す。任意の M、任意の前層 F、指定された両極限錐を量化し、F に層条件を課さない。①、段1の②、既存の随伴比較の重み自然性を合成して得る。

不足は、反転・unstraightening の指定比較の相対自然性、small/large の模型と底変換同型への移送、四角形の合成。全写像空間の `relativePreIso` や随伴比較は作り直さない。**3〜5ファイル、約800〜1,400行**。配置案は相対 unstraightening の一般部分を `Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/`、篩の G8 比較を `HTT/PresentableInfinityCategories/SetWeightSieveNaturality.lean` など。既存の `Project/SetWeightedTensors/` の数学は変更しない。

## 4. 段3：G14――小さい検出族

BS drafts の結論を維持する。E : SSet.{u+1} は quasicategory で presentable、族の添字は **Type u**、射は Ho(E)、写像空間は pinched Hom。

```text
IsDetectingFamily M := ∀ {x y} (f : Hom_Ho(E)(x,y)),
  IsIso f ↔ ∀ i, IsQCatEquivalence (PinchedInterval.postcompose (M i) f)
exists_detectingFamily (hE : IsPresentable E) :
  ∃ (ι : Type u) (M : ι → E₀), IsDetectingFamily M
```

再利用：

- `Kerodon/LimitsAndColimits/LimitsAndColimits/ReflectiveModelLimitDetection.lean` の `IsPresentable.exists_limitDetectingPresheafModel`：全図式に共通の小さい A と評価族を供給する。ただし、これだけから評価を Hom と同定したとは扱わない。
- `Kerodon/LargeInfinityCategories/PresentableInfinityCategories/PresentablePresheafReflection.lean` の **`IsPresentable.exists_presheafReflection`**：実際の L ⊣ R、R の充満忠実性を供給する。評価を表現する対象を作るためにこれを使う。
- `Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/PinchedObjectNaturality.lean` の `pinchedMap_naturality_right`、`Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/YonedaPresheafEvaluation.lean` の `yonedaPresheafEvaluationEquivalence`、既存の関手圏での点ごとの可逆性判定。

小さい A の頂点 a に対し **`M_a := L(y(a))`** を構成する。随伴と Yoneda 評価を合成して Map_E(M_a,x) と R(x)(a) を比較し、同じ f の後合成と R(f)(a) との整合性を証明する。R の充満忠実性と前層の点ごとの同値判定で検出を閉じる。個々の x で同値が存在するだけでは、f の検出へ移さない。

不足：Yoneda 評価の**標的射への自然性を同じ指定写像で使う接続**、随伴との合成、Ho の射・宇宙を合わせた可逆性判定。評価から検出への鎖を先に公開する。**2〜4ファイル、約450〜900行**。一般の評価比較を `Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/YonedaPresheafEvaluationPostcomposition.lean`、結論を `Kerodon/LargeInfinityCategories/PresentableInfinityCategories/DetectingFamily.lean` の案とする。G8 や D(A) 専用の仮定に狭めない。

## 5. 段4：G9-1〜3

入口表 §4.1 の三つの結論を維持する。

```text
G9-1: (F : P ⥤ Q) → (∀ q, IsWeaklyContractible (nerve (CostructuredArrow F q)))
      → IsLeftCofinal (nerveMap F)
G9-2: IsLeftCofinal f → IsLeftCofinal ((SSet.uliftFunctor.{u+1,u}).map f)
G9-3: (v : C) → (T : C ⥤ C) → (𝟭 C ⟶ T) → ((Functor.const C).obj v ⟶ T)
      → IsWeaklyContractible (nerve C)
```

P・Q・C は Type u、射も宇宙 u。G9-2 は一般の小さい単体集合の射 f を対象とする。G9-3 の nerve に Kan 性を課さない。

| 項目 | 既存と再利用 | 残り・配置案・規模 |
| --- | --- | --- |
| G9-1 | **単体集合版 left Quillen A は完成済み**：`Kerodon/LimitsAndColimits/Cofinality/QuillenALeft.lean` の `isLeftCofinal_of_weaklyContractible_slices`。通常 comma の同型は既存の `Project/LocalizationAndKanExtensionAuxiliaries/NerveComparison/LeftKanShapeIso.lean` の `nerveLeftKanShapeIso` | CostructuredArrow の nerve と slice 引き戻しを、射影を保つ同じ同型（必要なら pullbackSymmetry）でつなぐ薄い補題。右版の Quillen A を複製しない。新規 `Kerodon/LimitsAndColimits/Cofinality/NerveLeftQuillenA.lean`、約60〜130行 |
| G9-2 | `Kerodon/LargeInfinityCategories/IndCompletionsOfInfinityCategories/CofinalUniverseLift.lean` の **`isRightCofinal_ulift`**、`CofinalOpposite.lean` の `isLeftCofinal_iff_isRightCofinal_op`・`of_arrow_iso`、`Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/OppositeKanHomotopy.lean` の `uliftOppositeIso` | opposite → 既存 right ulift → opposite の順に移す。`uliftOppositeIso` による射の可換正方形も確認する。大きい宇宙の試験 fibration を、小さいものだけで足りると仮定しない。新規 `Kerodon/LimitsAndColimits/Cofinality/LeftCofinalUniverseLift.lean`、約90〜190行 |
| G9-3 | `Kerodon/KanComplexes/HomotopyGroups/WeakContractibleContractionSpan.lean` の証明、既存 `nerveNatTransHomotopy`・`functorIsoPrecompositionOfHomotopy_kan` | 自然変換 id→T・const→T を元のホモトピーへ送り、**Kan 標的への関手空間の中で**逆向きの同型にする。元の自然変換の逆や nerve の Kan 性を要求しない。新規 `Kerodon/KanComplexes/HomotopyGroups/WeakContractibleContractionCospan.lean`、約50〜130行 |

合計 **3ファイル、約200〜450行**。BS が担当する通常 comma の具体的表示・縮約は作り直さない。S3 は Quillen A の経路のままで、G10 や効果的エピの実現を前提に戻さない。

## 6. 規模・順序・検証の予定

| 段 | 新規ファイル | 新規行数の見込み |
| --- | ---: | ---: |
| 1：②、共通 span と G8 後段 | 6〜9 | 1,600〜2,600 |
| 2：①、篩包含の四角形 | 3〜5 | 800〜1,400 |
| 3：G14、実検出族 | 2〜4 | 450〜900 |
| 4：G9-1〜3 | 3 | 200〜450 |
| 合計 | **14〜21** | **3,050〜5,350** |

既存の一般 API の再利用を含む実装量の見積もりで、証明済みの上限ではない。特に段1の共通 span と段3の射への自然性は、型を展開して実装し始めた時点で再評価する。先に段1、次に段2、G14、G9の順。段1・2の停止点では指示どおり報告して待つ。

実装承認後は新規モジュールと直接の importer、現行の `Project/Entrypoints/F2.lean` を対象ビルドし、`scripts/audit_infinity_f2.lean` を単独実行する。新規ファイルを通常 import とモジュール別監査・明示宣言の確認に登録し、旧 namespace の prefix 走査だけで新しい宣言も監査されたとは見なさない。root・全下流・verify は行わない。鍵は最新指示の **`--wait 3600`、ビルド・Lean 検証の間だけ、一枚ずつ**とする。

現行の coordination.md の分担も確認した。Δ・Δᵒᵖ の橋と sifted の一般部分は③-b（IS-W2）であり、③-aでは作り直さない。共通の錐・写像空間の部品は先に main に入った宣言を使う。

E は一般の presentable quasicategory とし、D(A) には限定しない。段5以降の一般の φ・G10・一般の空間値 G8、K 側の追加 cofinality は今回の実装範囲に含めない。G10 の全関手・射・指定錐までという注記は保持する。

**本ターンは枝の作成・ソースの閲覧・本報告だけ。Lean・drafts・入口・監査の変更0、ビルド0、鍵取得0。停止点0で停止し、調整役の確認を待つ。**

## 7. 段1途中：共通 span の全族比較と数学的な停止（11-12）

**段1は未完、停止点1には未到達。** 指示書 §1・11-12追記の「数学的に詰まったら、通ったところまでを報告して止める」に従い、以下の検証済み共通部品を途中の取り込み点として提出する。コードは **`b0d89c6eb`**。基点は main `2e65c20b6` を取り込んだ `e977ff8ec`。

### 通ったもの

パスは `SerrePositivity/InfinityCategories/` 以下。既存宣言は無変更。

| 新規ファイル | 公開した主張（主要名） |
| --- | --- |
| `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationMappingOverNaturality.lean`（150行、8宣言） | 正規化した slice 後合成の合成則 `pointSlicePostcomp_comp`、span の底上の射 `rightFibrationMappingOverMap`、射影・評価との厳密な可換性。**`rightFibrationHomComparison_overMapIso`** は、f:E→F、s:F→B、f≫s と s が right fibrations のとき、元の Hom 比較を f の fiber 射で後合成する経路と、F 側の元の Hom 比較との **全写像間の FunctorIso** を返す。既存の切断を変更せず、標的の同じ自明 Kan fibration 上で比較する |
| 同節の `RightFibrationMappingDiagramRestriction.lean`（90行、6宣言） | `rightFibrationMappingDiagramTotal` は任意図式 p:K→E の錐の始点を r:E→B の像 x 上で固定する実空間。`rightFibrationMappingDiagramRestriction` は図式の表示を保つ制限、`…_evaluation` は全族での評価の厳密な可換性、`…_trivialKanFibration` は left anodyne な単射の制限の自明 Kan 性を与える。図式形状 K は任意 |
| 同節の `RightFibrationInitialDiagramSpan.lean`（131行、7宣言） | 図式の始点 a:Δ[0]→K が left anodyne な単射なら、錐の全空間から元の Hom への共通自明 Kan 射影と、その全空間の切断を構成する。`rightFibrationInitialDiagramSection_sourceIso` は源側の元の Hom 比較を回収。**`rightFibrationInitialDiagramEndpointIso`** は、別の頂点 b への制限から構成した実射 β_native に対し `FunctorIso (comparison r c x) (β_native ≫ comparison r d x)` を返す。標準後合成との一致を仮定にも結論にもしていない |
| `Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/IntervalTriangleFamilyComposition.lean`（70行、2宣言） | `intervalTriangleFamilyCompStruct` は、実三角形族 T:A⊗Δ[2]→X とその三面の等式から、同じ二単体の合成構造を構成する。`intervalTriangleFamily_hom_comp` は三つの**全区間族**の h Fun での合成則を与える。T 自体の存在を供給する補題ではない |

正規化した後合成は既存の `IndCompletionsOfInfinityCategories.PointSlicePostcomp`・`PointSlicePostcompIso` を再利用した。7.4側から9.3側へのこの直接 import は、その公開宣言を実際に使うためのもの。移動や同じ構成の再定義はしていない。自明 Kan fibration 上の比較は既存の `functorIsoOfTrivialKanFibration`、図式制限は `normalizedConeRestriction`・slice 制限の持ち上げ性を使った。Δ・Δᵒᵖ の橋、sifted、BS 側の構成には手を付けていない。

### 閉じていない数学

**β_native と、同じ錐の辺の底での標準 `PinchedInterval.postcompose` の全族での同定が未証明。** β_native は共通 span の選んだ切断から得る実射であり、一般の right fibration と始点付き図式に対して定義したもの。まだ具体的な辺形状 Δ[1] への適用と、標準後合成との比較を公開していない。`rightFibrationInitialDiagramEndpointIso` を、報告 §2 の「錐の辺との比較」の完成として扱わない。

検討した筋と残る箇所は次のとおり。

1. 共通 span の切断の像を `sliceConeFamilyUncurry` と r で底へ送り、join(Δ[0],Δ[1])≅Δ[2] 上の **実三角形族**を得る。
2. その第一面が元の pinched Hom の区間模型への比較、第二面が同じ指定辺の定値族、長辺が β_native の区間模型への像であることを、**全パラメータで、終点の輸送も含めて**照合する。この三面の照合を構成し切れていない。
3. そこまで得られれば、今回の `intervalTriangleFamily_hom_comp`、既存の `intervalPostcompose_family`・`intervalFamilyHom_eq_imp_homotopy` と pinched/interval 比較を使う方針。三面が与えられた場合の合成則と、必要な三面を元の錐から作ることを区別する。

さらに、標準後合成との同定後にも、`coherentDiagramSectionsCone` から指定極限への G8 の実際の後段、宇宙変更、表現可能値の比較との接続は残る。評価錐側の既存の Ho 等式だけで代用していない。`sectionsConeFamilyRestriction_fromSections` と `limitConeMap_homMk_eq_of_coneFamilyIso` へ必要な全族同型を最後まで渡すことも、まだできていない。

したがって、G8 の②や四角形を証明したとは報告しない。必要な全族同型・標準後合成との一致を入力に足した「完成版」も置いていない。

### 検証と見込みとの差

- **4モジュール・441行・23個の名前付き公開宣言**。段1の当初見込み1,600〜2,600行に対し、実測は現時点で1,159〜2,159行少ないが、これは**未完部分を含めない途中の量**であり、完成時の削減実績ではない。上限3,380行による停止ではなく、上記の数学的な接続での停止。
- 最終の二つの葉から4本を含む対象ビルド **4,519 jobs 成功**。23件の `#check`・`#print axioms`・`#print sorries` が全件成功し、**sorry なし・標準三公理のみ**。
- ログと一覧：`/tmp/is-w1/stage1/verify-interim.log`、`modules.txt`、`declarations.txt`、`audit.lean`。最後の検証後に数学の変更はしていない。
- 入口 `Project/Entrypoints/F2.lean` と全体監査は調整役の登録待ち。今回、対象4本の23宣言は独立に監査したが、**F2全体の監査は実行していない**。既存の本体・drafts・入口・監査スクリプトは無変更。未検証の Lean 下書きは作業木に残していない。

**段1途中で停止。** 共通部品4本だけを先に取り込める状態として提出し、残る三面の照合と G8 の後段への接続について調整役へ報告する。段2・G14・G9へは進んでいない。

## 8. 段1途中：辺形状の三面と標準後合成（11-12）

§7 の未完部分のうち、**Δ[1] に限った三面と β_native の標準後合成との全族比較を閉じた**。main `7f4e750da` を取り込んで作業した。一般の図式形状への実三角形の拡張は作っていない。G8 の②全体・停止点1は未到達。

### 三面の厳密な型

`r : E → B` は right fibration、B は quasicategory、`e : Δ[1] → E`、`c,d : E₀`、`hc : δ₁ ≫ e = yoneda.symm c`、`hd : δ₀ ≫ e = yoneda.symm d`、`x : B₀` とする。`P := pinchedHom x (r c)`、`j_c := pinchedHomToIntervalMappingSpace x (r c)`、`j_d` も同様。T は**元の共通 span の同じ全切断**から作る `rightFibrationEdgeTriangle r e c hc x : P ⊗ Δ[2] → B`、β は同じ切断による `rightFibrationInitialDiagramEndpointMap` とする。次を証明した。

```text
(P ◁ δ₂) ≫ T = (intervalFamilyHomotopy j_c).h
(P ◁ δ₀) ≫ T = snd P Δ[1] ≫ e ≫ r
(P ◁ δ₁) ≫ T = (intervalFamilyHomotopy (β ≫ j_d)).h
```

対応する公開名は `rightFibrationEdgeTriangle_first`・`…_edge`・`…_long`。第一面の独立した核は `rightFibrationMappingHomProjection_intervalUncurry`：元の Hom 射影を区間へ送った族は、**元の同じ錐**に右 prism を前合成して底へ送る射に厳密に等しい。第一面の恒等性は共通切断の射影の恒等式から得る。第二面は錐の固定条件、長辺は同じ端点制限の定義から得る。三面に未証明の等式は残っていない。

辺 `e : E.Edge c d` の実代表へ適用し、定値区間族と定値関手の射との比較、`intervalTriangleFamily_hom_comp`、`intervalPostcompose_family` を使った。`rightFibrationEdgeNative_interval_homotopy` は

```text
Nonempty (SSet.Homotopy (β_native ≫ j_d)
  (j_c ≫ intervalPostcompose x [e.map r]))
```

を返す。指定された pinched/interval 比較の逆で戻し、`rightFibrationEdgeNative_postcomposeIso` を経て、次を構成した。

```text
rightFibrationHomComparison_edgeIso :
  FunctorIso (rightFibrationHomComparison r c x)
    (postcompose x [e.map r] ≫ rightFibrationHomComparison r d x)
```

各頂点だけの比較ではなく全写像間の同型で、必要な同型を入力には足していない。最後に slice 射影へ適用した `fixedApexConeHomComparison_edgeIso` は、指定された錐の辺と固定頂点の錐の全族比較を与える（極限性は不要）。

### 追加・規模・検証

パスは `SerrePositivity/InfinityCategories/Kerodon/` 以下。既存宣言は無変更。

| 新規ファイル | 行数 | 宣言数 | 内容 |
| --- | ---: | ---: | --- |
| `LimitsAndColimits/LimitsAndColimitsOfSpaces/EdgeTrianglePrism.lean` | 136 | 6 | 辺形状の prism、元の右 prism との一致、三面 |
| 同節 `RightFibrationIntervalProjection.lean` | 55 | 2 | 元の Hom 射影の pinched・区間展開の厳密な等式 |
| 同節 `RightFibrationEdgeTriangle.lean` | 156 | 8 | 同じ共通切断からの実三角形族と三面 |
| `AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/IntervalConstantFamily.lean` | 56 | 2 | 指定辺の定値区間族と定値関手の射 |
| `LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationEdgeComposition.lean` | 118 | 7 | 三面から β_native と標準後合成の全族比較 |
| 同節 `FixedApexConeEdgeComparison.lean` | 38 | 1 | 固定頂点の錐への適用 |
| **計** | **559** | **26** | |

三面そのものは最初の3本 **347行**で、今回の上限600行より253行少ない。標準後合成と錐への接続まで含めても559行。段1の累計は前回441行と合わせ **1,000行**。当初の1,600〜2,600行との差は600〜1,600行だが、後段が未完なので完成時の削減量ではない。段1の上限3,380行には未到達。

- 六本を含む葉 `FixedApexConeEdgeComparison` の対象ビルド **4,546 jobs 成功**（`/tmp/is-w1/faces/build-12.log`）。
- 個別監査の記録はこの節の追記を参照。入口・F2全体監査の登録は調整役に委ねる。
- Δ・Δᵒᵖ の橋や sifted は作っていない。生の既存の比較・切断を変更していない。

### 残る後段

三面と標準後合成の接続は済んだ。次は `coherentDiagramSectionsCone` から指定極限錐への**同じ選択**、`spaceUniverseValueEquivalence`、`spaceValueEquivalence (t.represents.app …)` の逆、`covariantRepresentableValueEquivalence` を順に追う。既存の `coneSectionsNativeComparisonIso`、`representationValueTransportIso`、`unstraighteningValueTransportIso` と今回の錐の辺の比較を再利用する。`sectionsConeFamilyRestriction_fromSections` から最終的な `limitConeMap_homMk_eq_of_coneFamilyIso` に渡す全族同型はまだ構成していない。したがって **G8 の②の完成は主張しない**。

**途中の取り込み点：`b126b94b7`（六本）。** 26件の `#check`・`#print axioms`・`#print sorries` が全件成功し、公理の集合は `propext`・`Classical.choice`・`Quot.sound` のみ、sorry 0（`/tmp/is-w1/faces/audit.log`、一覧 `declarations.txt`、監査入力 `audit.lean`）。六本はそのまま取り込める。入口・全体監査は変更しておらず、F2全体の監査は未実行。段1後段への接続を続ける。
