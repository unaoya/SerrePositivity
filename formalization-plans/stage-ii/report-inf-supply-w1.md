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

## 9. 新基準での段1の途中報告（11-12、作業継続）

main `f5baa8763` の規模基準の改定を取り込んだ。段1の停止上限は **5,200行**、途中報告の目安は段0の上端2,600行の半分の **1,300行**。現在は検証済み **1,000行**、未検証の新規下書き **358行**、計 **1,358行**（前回の六本を含む）。この時点で一度、止まらずに報告する。

下書きは、正本の選択を保持した G8 後段の因子と厳密な分解式（84行）、表現可能値の接続に使う coslice 側の三角形 prism・三面・元の輸送と区間後合成の比較（274行）。共有鍵の待ちは一枚で、最初の因子の対象ビルドから順に検証する。下書きは検証済みとは数えておらず、数学の未検証分はコミットしていない。

残りの再見積もりは約 **1,500〜2,500行**、完成見込みの合計は約 **2,900〜3,900行**。主な不足は、(1) 実際の `covariantRepresentableValueEquivalence` が経る反転・左右 Hom 比較と同じ後合成の全族比較、(2) `spaceUniverseValueEquivalence` と表現の頂点同型の同じ比較の自然性、(3) 切断錐から指定極限への比較・切断制限・固定端点模型の接続。各頂点の Ho 等式へ弱めず、既存の選択を保つための幅を含めた。上限5,200行を超える見込みは現時点ではなく、作業を続ける。

## 10. 後段の因子と coslice の全族比較（作業継続）

検証済みの六本を `27f37cc66` にコミットした（461行・16宣言）。段1の検証済み累計は **1,461行**。停止点1にはまだ到達していない。

- `HTT/PresentableInfinityCategories/SetWeightSectionsLimitFactorization.lean`（84行・3宣言）：`sectionsLimitValueEquivalence` と `setWeightSectionsLimitTail` は正本と同じ選択を保持する。`tensorSpaceFunctor_setWeightHomNatural_hom_factor` は元の順射が「元の随伴比較 ≫ 元の切断比較 ≫ 同じ後段」の厳密な合成であることを示す。別の同値への置換ではない。
- `Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/CosliceEdgeTrianglePrism.lean`（117行・5宣言）、`CosliceEdgeTriangleFamily.lean`（75行・3宣言）、`CosliceTransportIntervalComparison.lean`（84行・3宣言）：元の coslice 輸送の同じ証人の三面から、同じ区間比較の全族と標準後合成のホモトピーを得る。
- 同節 `CosliceTransportRightMappingComparison.lean`（60行・1宣言）：`cosliceTransport_rightMappingIso` は、元の `cosliceFiberRightMappingEquivalence` の順射が、同じ指定辺の輸送と標準後合成を全写像間の同型で結ぶ。
- `Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/CovariantRepresentableValueNormalization.lean`（41行・1宣言）：元の `covariantRepresentableValueEquivalence` の中で隣り合う反転同値とその逆を、指定された `homInvIso` で相殺する。元の値比較の自然性全体はまだ主張しない。

因子は6,131 jobs、coslice 三本は2,114 jobs、表現可能値の正規化はその前の対象ビルド、右模型への移送は2,116 jobs の対象ビルドで成功。15宣言の個別監査（`/tmp/is-w1/tail-audit.log`）と右模型の1宣言の監査（`coslice-right-audit.log`）は全件成功し、sorry 0・標準三公理のみ。F2全体監査は未実行、入口・監査登録は調整役が行う。

続いて、既存の `cofinalPointSliceOverOpIso`・`pointSliceReverseFiberIso`・`pointCosliceFiberMap` とその座標公式を再利用し、反転した slice fiber の元の比較を、元の coslice の左 pinched 比較へ厳密に照合している。新しい反転・slice 同型そのものは作り直していない。指定極限・宇宙変更・表現可能値を通じた G8 の全族の四角形は未完。

新しい全段の停止上限は、段1 **5,200**、段2 **2,800**、段3 **1,800**、段4 **900行**。途中報告の目安はそれぞれ **1,300・700・450・225行**。

## 11. 後段の途中保存と規模見込みによる停止（停止点1は未達）

**段1の②は未完。上限超過の見込みによる停止であり、停止点1の完成報告ではない。** 元の比較の選択は保持し、必要な同型を仮定に足した最終版は置いていない。

今回閉じたのは、(1) 元の共変表現可能値と標準後合成の全族自然性、(2) 元の宇宙変更と表現の指定成分の逆を含む Hom 値後段の全族自然性、(3) 錐の辺に沿う元の切断写像の全 fiber 上の自然性、(4) 元の選択した極限頂点の比較と値の切断写像との全族比較。正規化した形状制限の固定端点比較と、実切断の制限の評価も新規の葉で切り出した。以下の検証欄に成功したものだけを記す。

### 残る数学と型

`φ : X ⟶ Y`、元の係数図式 `F`、`t := spaceTensorData hE M` とし、`G := F ≫ t.hom`、`gX := SetWeight.diagram X G`、`gY := SetWeight.diagram Y G` と置く。`Γ(g)` は `coherentSpaceSectionsObject g` の台。`i := nerveMap φ.mapElements`、`hφ := SetWeight.elementsMap_diagram φ G` による終域の移送を含め、

```lean
ρ₀ := smallUnstraighteningSectionsRestriction gY i ≫
  eqToHom (congrArg Γ hφ)
ρ := (SSet.uliftFunctor.{u + 1, u}).map ρ₀
```

とする（この節の略記は紙の型案）。まず必要なのは、任意の `d : JoinCone gY` に対する次の**全写像**の同型。

```lean
FunctorIso
  (coneSectionsValueMapAt gY d d.vertex rfl ≫ ρ)
  (coneSectionsValueMapAt gX
    (SetWeight.restrictSectionsCone φ G d) d.vertex
    (SetWeight.restrictSectionsCone_vertex φ G d))
```

実際の切断制限であり、選んだ極限の普遍性だけから別の制限を定義して代用しない。既存の `leftUnstraighteningMappingRestrictionIso` を、定値始域の全 fiber と切断の指数同型で写す。その前後に必要な native 錐の円柱の形状自然性と、小さい表示／元の大きい表示の制限との整合性はまだ証明していない。

指定極限錐 `cX, cY` に対し、`vX := setWeightSectionsLimitTail X hE M F cX hcX`、`vY := setWeightSectionsLimitTail Y hE M F cY hcY`、`δ := [SetWeight.sectionsMap φ F cX hcX cY hcY]` と置く。上の同型、今回の切断錐から指定極限への比較、同じ `t.hom` で写した錐の辺の終対象性による比較を合わせ、残る目標は

```lean
FunctorIso (ρ ≫ vX.hom) (vY.hom ≫ postcompose M δ)
```

である。`spaceTensorHomValueTail_edgeIso` は指定された **E の辺**に沿う後段の全族自然性を閉じたが、この**形状制限**の四角形そのものはまだ閉じていない。`tensorSpaceFunctor_setWeightHomNatural_hom_factor` により元の G8 比較への厳密な因子の接続は済んでいる。

最後に上の二経路へ `SetWeight.limitConeEndpointComparison cX M` を後合成した全族同型を作り、既存の `sectionsConeFamilyRestriction_fromSections` と照合する。その同型を `limitConeMap_homMk_eq_of_coneFamilyIso` に渡す。現時点でその最終入力を構成したとは主張しない。①や Δ の橋・sifted には進んでいない。

### 再見積もり（この表は未実装分）

| 残る接続 | 行数見込み |
| --- | ---: |
| 定値始域の変換と native な錐の円柱の形状制限 | 250〜350 |
| 既存の相対 unstraightening 比較を全 fiber・実切断の比較へ移す | 550〜700 |
| 小さい／大きい切断表示、図式の等式による正規化との整合性 | 400〜500 |
| 同じテンソル随伴で写した指定極限錐・普遍辺との照合 | 300〜400 |
| 後段全体の合成、固定端点模型の照合、既存の Ho 等式への入力 | 500〜650 |
| 計 | **2,000〜2,600** |

既存の `leftUnstraighteningMappingRestrictionIso`、`normalizedConeRestriction`、`normalizedSliceEndpointComparison_restrict`、`sectionsConeFamilyRestriction_fromSections` を再利用する見込みであり、これらの持ち上げ・比較そのものは作り直さない。当初の段1の1,600〜2,600行、§9の2,900〜3,900行という見込みに対し、同じ選択の反転・表現可能値の自然性と、切断の二つの表示を全族で結ぶ部分を過小に見ていた。

今回の実測は新規26本1,814行、既検証1,461行と合わせて累計3,275行。残り2,000〜2,600行を加えると **5,275〜5,875行**（約5,300〜5,900行）となる見込みのため、上限5,200行の停止条件に従い、検証済み分を保存して止める。上限は変更していない。

### 検証・コミット

17本・1,134行・32宣言は `1534eb2bd` に保存済み。各葉の対象ビルドが成功し、32宣言の `#check`・`#print axioms`・`#print sorries` は全件成功（`/tmp/is-w1/remainder-build-1-audit.log` の監査部分）。標準三公理のみ、sorry 0。

残り9本・680行・16宣言を `8ecef8bf8` に保存した。選択した極限の比較は `remainder-build-1-audit.log`、固定端点の正規化した形状制限と共通の引き戻し切断は `remainder-build-2-audit.log` の各対象で成功。最後の小さい切断制限の対象ビルドは **2,651 jobs 成功**（`/tmp/is-w1/remainder-build-3-audit.log`）。同じログの新規26本・48宣言の `#check`・`#print axioms`・`#print sorries` は全件成功し、**sorry 0・標準三公理のみ**。

今回合計 **26本・1,814行・48宣言**、段1累計 **42本・3,275行・113宣言**。未検証の Lean 下書きは残していない。残る数学は上記の紙の型案に記録した。報告時点の作業木を清潔にして停止する。

F2全体のビルド・監査は実行していない。入口・全体監査への登録は調整役の持ち分。新しい数学は新規ファイルだけで、既存の本文・型・名前は変更していない。鍵は `--wait 3600` で一枚ずつ、ビルド・監査の実行中だけ保持した。待ち時間は停止理由にしていない。

前回の `b126b94b7`（6本）・`27f37cc66`（6本）も未取り込み。今回26本と合わせ、main未登録の新規モジュールは38本。今回の途中保存をG8の②の完成とは扱わない。

### 今回の新規ファイル・公開宣言

ファイルはすべて KL-W1 後の Kerodon／HTT の配置。既存の数学の宣言・入口・全体監査は変更していない。

| 新規ファイル | 行数 | 宣言数 |
| --- | ---: | ---: |
| [SetWeightEndpointRestrictionComparison.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightEndpointRestrictionComparison.lean) | 63 | 1 |
| [SetWeightFixedEndpointEdgeComparison.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightFixedEndpointEdgeComparison.lean) | 39 | 1 |
| [SetWeightSectionsLimitValueComparison.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsLimitValueComparison.lean) | 111 | 4 |
| [SetWeightSpaceValueComparison.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSpaceValueComparison.lean) | 58 | 2 |
| [SetWeightUniverseValueNaturality.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightUniverseValueNaturality.lean) | 73 | 1 |
| [SpaceTensorHomValueTailNaturality.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SpaceTensorHomValueTailNaturality.lean) | 98 | 2 |
| [IntervalPostcomposeIdentityFamily.lean](../../SerrePositivity/InfinityCategories/Kerodon/AdjointFunctors/AdjointFunctorsBetweenInfinityCategories/IntervalPostcomposeIdentityFamily.lean) | 37 | 1 |
| [SpaceValueHomClass.lean](../../SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/SimplicialCategories/SpaceValueHomClass.lean) | 72 | 4 |
| [CovariantCosliceFiberNormalization.lean](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/CovariantCosliceFiberNormalization.lean) | 64 | 3 |
| [PointCosliceIsoTransportComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/PointCosliceIsoTransportComparison.lean) | 75 | 2 |
| [PointSliceReversePinchedComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/CartesianFibrations/PointSliceReversePinchedComparison.lean) | 48 | 1 |
| [EquivalenceInverseSquare.lean](../../SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/EquivalenceInverseSquare.lean) | 34 | 1 |
| [FamilyEquivalenceReflection.lean](../../SerrePositivity/InfinityCategories/Kerodon/KanComplexes/TheHomotopyTheoryOfKanComplexes/FamilyEquivalenceReflection.lean) | 33 | 1 |
| [CartesianSectionsRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/CartesianSectionsRestriction.lean) | 68 | 3 |
| [ConeSectionsHomActionEdgeComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsHomActionEdgeComparison.lean) | 46 | 1 |
| [ConeSectionsHomActionVertexComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsHomActionVertexComparison.lean) | 69 | 1 |
| [ConeSectionsMapTransportNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsMapTransportNaturality.lean) | 96 | 1 |
| [ConeSectionsValueEdgeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsValueEdgeNaturality.lean) | 69 | 1 |
| [PointedIntervalTransportVertexComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/PointedIntervalTransportVertexComparison.lean) | 100 | 2 |
| [RightFibrationMappingNormalizedOverMap.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/RightFibrationMappingNormalizedOverMap.lean) | 48 | 1 |
| [SmallUnstraighteningSectionsRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/SmallUnstraighteningSectionsRestriction.lean) | 56 | 2 |
| [SmallUnstraighteningValueTransport.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/SmallUnstraighteningValueTransport.lean) | 110 | 3 |
| [CovariantRepresentableCosliceComparison.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/CovariantRepresentableCosliceComparison.lean) | 89 | 2 |
| [CovariantRepresentableValueNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/CovariantRepresentableValueNaturality.lean) | 94 | 1 |
| [ReversedRepresentableValueFactorization.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/ReversedRepresentableValueFactorization.lean) | 67 | 1 |
| [ReversedRepresentableValueTransport.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/ReversedRepresentableValueTransport.lean) | 97 | 5 |

| 公開宣言（末尾の名前） | 主張 |
| --- | --- |
| `limitConeEndpointComparison_restrictIso` | 元の錐の Hom 比較は、同じ正規化した形状制限と固定端点模型で全族として可換。 |
| `setWeightLimitConeEndpointComparison_edgeIso` | 元の固定端点比較は、同じ指定錐の辺の標準後合成に全自然。 |
| `limitVertexValue_edgeIso` | 指定極限頂点の同じ値比較は、同じ錐の辺の値の作用と全写像として同型。 |
| `limitVertexValue_coneSectionsIso` | 指定極限頂点の同じ値比較は、元の錐の値の切断写像と全族で可換。 |
| `limitVertexValueAt_coneSectionsIso` | 同じ切断錐の頂点を指定表示しても、値の切断写像との比較は保たれる。 |
| `sectionsLimitValueEquivalence_coneSectionsIso` | 正本の切断から指定極限への同じ比較は、元の値の切断写像の右逆になる。 |
| `spaceValueHomClass_spaceValueEquivalence` | 正本の選んだ値比較の順射の類は、元の頂点同型の順射そのもの。 |
| `setWeightSpaceValueSquareIso` | 空間のホモトピー圏で可換な正方形は、正本の同じ値比較による全写像間の同型を与える。 |
| `setWeightUniverseValue_edgeIso` | 元の宇宙変更の値比較は、同じ小さい分類図式の値の作用と全族で可換。 |
| `spaceTensorHomValueTail` | 元のテンソル随伴の値から右写像空間への後段の同じ比較。 |
| `spaceTensorHomValueTail_edgeIso` | 正本の同じ Hom 値比較は、指定辺の値の作用と標準後合成を全族で結ぶ。 |
| `intervalPostcompose_identityFamily_homotopy` | 指定辺による標準後合成は、恒等辺の定値全族を同じ辺の定値全族へ送る。 |
| `spaceValueHomClass` | 元の指定空間の Kan 値の実写像を、同じ端点のホモトピー圏の射で読む。 |
| `spaceValueHomClass_edgeValue` | 同じ空間辺の Kan 値を読んだ類は、元の辺の類そのもの。 |
| `spaceValueHomClass_comp` | 元の Kan 値の写像の合成を読む操作は合成を保つ。 |
| `spaceValueFunctorIso_of_homClass_eq` | 同じ端点の値の全写像の類の等式から、元の全写像間の同型を得る。 |
| `covariantCosliceFiberNormalization` | 元の左 pinched 模型を、元の単体集合の coslice fiber へ戻す同じ反転経路。 |
| `covariantCosliceFiberNormalization_hom` | 元の反転経路で戻してから左 pinched 比較を行うと恒等射。 |
| `covariantCosliceFiberNormalization_eq_inv` | 同じ反転経路は、元の左 pinched 比較の指定逆そのもの。 |
| `pointCosliceFiberMap_ι_of_iso` | 同じ底の同型による fiber 比較は、同じ coslice 全空間の後合成を誘導する。 |
| `pointCosliceIso_transportIso` | 同じ底の同型で移した coslice 輸送は、元の fiber 比較と輸送の合成に同型。 |
| `pointSliceReverseFiberIso_pinchedLeft` | 元の右 pinched fiber の反転を左模型へ送る射は、標準二重反転の射の反転。 |
| `functorIsoInverseSquare` | 同じ指定同値の順射による可換正方形から、指定逆による全族同型を得る。 |
| `functorIsoOfPrecompEquivalence` | 指定同値で前合成して全族で同型な二つの写像は、元のまま全族で同型。 |
| `sectionsRestrictionOfIso` | 指定された実際の引き戻し表示に沿って、元の切断空間の全族を制限する。 |
| `sectionsRestrictionOfIso_evaluation` | 引き戻し表示を用いた切断制限を評価すると、元の評価の制限を回収する。 |
| `sectionsRestrictionTargetIso` | 同じ引き戻し表示による切断空間は、元の射の相対関手空間と同型。 |
| `coneSectionsHomAction_edgeIso` | 元の全切断 Hom 作用は、同じ錐の辺の標準後合成と全族で可換。 |
| `coneSectionsHomAction_intervalVertexIso` | 同じ区間頂点への同型の下で Hom 作用を元の辺輸送と比較する。 |
| `coneSectionsMap_transportIso` | 元の錐の切断写像は、同じ錐の辺の頂点輸送と全 fiber 上で可換。 |
| `coneSectionsValueMap_edgeIso` | 錐の元の値の切断写像は、同じ錐の辺の値の作用と全族で可換。 |
| `pointedIntervalTransport_vertex_edgeIso` | 同じ区間頂点への同型があれば、元の全 fiber 輸送をその辺輸送へ比較できる。 |
| `pointedIntervalTransport_at_vertexIso` | 同じパラメータで評価した元の pointed 輸送は、その頂点の表す辺の輸送に同型。 |
| `rightFibrationHomComparison_overMapIso_of_eq` | 射影が等式で与えられた底上の射でも、同じ表現可能比較は全族で可換。 |
| `smallUnstraighteningSectionsRestriction` | 同じ小さい分類図式の切断を、指定形状写像に沿って実際に制限する。 |
| `smallUnstraighteningSectionsRestriction_evaluation` | 元の評価を同じ基底変更の射影へ送ると、実際の切断制限の評価になる。 |
| `smallLeftUnstraighteningFiberIso_transportIso` | 小さい射影から元の大きい射影への指定 fiber 同型は、同じ辺の輸送に自然。 |
| `smallUnstraighteningValueTransportIso` | 元の小さい fiber 値比較は、同じ図式の指定辺の値の作用に全自然。 |
| `smallUnstraighteningFiberMapValue_transportIso` | 同じ底上の射の fiber と元の小さい値比較の合成は、指定辺の作用に全自然。 |
| `cosliceRightMapping_hom_factor` | 元の coslice の右写像空間比較は、指定左 pinched 比較と左右比較の合成。 |
| `covariantRepresentableValue_cosliceIso` | 元の共変表現可能値の比較は、同じ反転 coslice の値比較の上で元の右 Hom 比較に同型。 |
| `covariantRepresentableValue_postcomposeIso` | 元の共変表現可能値の比較は、同じ指定辺の値の作用と標準後合成を全族で結ぶ。 |
| `representableOppositeHomValue_hom_factor` | 同じ反転 Hom の値比較は、反転した元の右 fiber と coslice 上の値比較の合成。 |
| `reversedRepresentableComparison` | 反対底の coslice から元の表現可能前層の小さい unstraightening への同じ比較。 |
| `reversedRepresentableComparison_projection` | 同じ復元比較は反対の底を厳密に保つ。 |
| `reversedRepresentableComparison_isPrecompositionEquivalence` | 反対底上の同じ比較は全空間の前合成同値。 |
| `reversedRepresentableValueEquivalence` | 反対底の coslice fiber を、元の表現可能前層の値へ送る同じ比較。 |
| `reversedRepresentableValueTransportIso` | 反対底の coslice の元の値比較は、同じ辺の値の作用に全自然。 |



## 12. 停止点1：G8 の四角形②（11-12夕の承認後）

**②を閉じ、停止点1で停止する。** コードは **`3b1371c0b`**（新規21本・1,332行・44宣言）。段1累計は **63本・4,607行・157宣言**。上限約6,000行以内。①と合わせた G8 の四角形全体、段2・G14・G9は今回の完成には含めない。前回の38本は調整役の途中取り込み対象であり、今回の21本と区別する。

### 主張の型と証明の要点

`φ : X ⟶ Y` は集合値重みの射、E は一般の presentable quasicategory、M はその対象、F は元の図式、cX・cY は指定された極限錐とする。ρφ は要素の圏に沿う**実際の小さい切断制限**、τX・τY は正本の `setWeightSectionsLimitTail` の同じ順射、δ は元の `SetWeight.sectionsMap`、κX・κY は元の `limitConeEndpointComparison` とする。

- **`setWeightSectionsLimitTail_shapeIso`**：`ulift(ρφ) ≫ τX ≅ τY ≫ postcompose M [δ]` を全写像間の `FunctorIso` として構成した。
- **`setWeightLimitTailConeFamilyIso`**：この二経路を κX で後合成した、固定端点模型内の全族同型。必要な同型を仮定に足していない。
- **`setWeightLimitTail_homMk_eq`**：上の構成済み同型を既存の `limitConeMap_homMk_eq_of_coneFamilyIso` に渡し、同じ二経路の空間のホモトピー圏での等式を得る。
- **`setWeightEndpointRestriction_sectionsMapIso`**：`κY ≫ sectionsConeFamilyRestriction φ F M ≅ postcompose M [δ] ≫ κX`。元の制限錐と元の指定普遍辺を使う。
- **`setWeightLimitTail_endpointRestrictionIso`**：`ulift(ρφ) ≫ τX ≫ κX ≅ τY ≫ κY ≫ sectionsConeFamilyRestriction φ F M`。右端の射は既存の `sectionsConeFamilyRestriction_fromSections` に現れる**同じ射**であり、その既存の厳密な等式と合わせて切断制限・固定端点模型の図式を結ぶ。

証明は§11の五つの接続に沿う。定値始域の区間族と錐の円柱の形状制限を厳密に計算し、既存の `leftUnstraighteningMappingSpaceMap_baseChangeIso` を相対指数同型へ移した。錐の標準変換で評価する際も、対象は**頂点 fiber 全体からの写像**であり、fiber 内の点ごとの一致へ弱めていない。大小の切断同型は元の評価式で実制限と照合し、図式の等式による移送も保持した。

続いて元の錐の値の切断写像、同じ指定極限比較の両逆の全族同型を使い、制限錐からの指定辺の値と接続した。元のテンソル随伴でその辺を写し、前回の `spaceTensorHomValueTail_edgeIso`（同じ宇宙変更と共変表現可能値の比較）を合成した。最後の固定端点模型には、前回の `limitConeEndpointComparison_restrictIso` と `setWeightLimitConeEndpointComparison_edgeIso` を再利用した。元の選択を別の普遍射へ置き換えていない。

### 五つの接続の見込みと実測

| §11の接続 | 見込み | 実測 | 上端との差 |
| --- | ---: | ---: | ---: |
| 定値始域・錐の円柱・標準変換の制限 | 250〜350 | 128 | −222 |
| 相対 unstraightening・全 fiber・実切断の比較 | 550〜700 | 454 | −246 |
| 大小の切断・指定図式の表示との整合性 | 400〜500 | 253 | −247 |
| 同じ随伴で写した指定極限・普遍辺との照合 | 300〜400 | 240 | −160 |
| 後段全体・固定端点模型・Ho等式 | 500〜650 | 257 | −393 |
| 合計 | **2,000〜2,600** | **1,332** | **−1,268** |

既存の相対底変換の全族同型と評価補題を再利用できたため、§11の再見積もりより小さく収まった。ただし段0の段1上端2,600行に対しては、累計4,607行で **+2,007行、約1.77倍**。相対表示・宇宙移送・選んだ逆の全族での照合を当初過小評価していた点は変わらない。

### 段2〜4の再見積もり

段1の実測比約1.77倍と、今回そろった一般補題を織り込む。下記は実装の見込みであり、承認済みの停止上限は変更しない。

| 段 | 段0の行数見込み | 新しい見込み（行／ファイル） | 現行停止上限 |
| --- | ---: | --- | ---: |
| 2：①と篩包含の四角形 | 800〜1,400 | **1,300〜2,500行／18〜34本** | 2,800 |
| 3：G14の実検出族 | 450〜900 | **800〜1,600行／10〜22本** | 1,800 |
| 4：G9-1〜3 | 200〜450 | **350〜800行／5〜11本** | 900 |

段2では、底を固定した相対写像空間の `elementsComparisonNatural` の自然性、`relativePreIso` との照合、元の `sectionsEquivalenceNatural` と今回の実切断制限の接続、正本の厳密な因子分解を使った四角形の合成が残る。②の値比較・固定端点比較は今回の宣言を再利用し、作り直さない。

段3では Yoneda 評価と同じ標的射の後合成の自然性、随伴を通じた `M_a := L(y(a))` の検出、充満忠実性による反映が残る。今回の全族同型の反転・表現可能値の自然性を再利用する。段4は既存の right 版からの opposite と ulift の移送が中心だが、射影を保つ同型・宇宙変更の表示合わせの分を増やした。各段の見込みの半分で途中実測を報告し、超過が見込まれたら検証済み分を保存して止める。

### 検証と残り

- 最終対象 `SetWeightEndpointShapeSquare` のビルド：**6,218 jobs 成功**。
- 新規44宣言すべての `#check`・`#print axioms`・`#print sorries` が成功。**44件すべて sorry-free、標準三公理（propext・Classical.choice・Quot.sound）のみ**。ログ：`/tmp/is-w1/shape-build-19.log`。一覧・監査入力は同ディレクトリの `shape-files.txt`・`shape-decls.txt`・`shape-audit.lean`。
- 新規21本は最終対象の依存閉包に含まれる。既存ファイルから新規ファイルへの import は追加していない。入口・全体監査の登録、F2全体のビルド・監査は調整役に委ねる。**今回F2全体の監査は実行していない**。
- 新しい数学は新規ファイルだけ。既存宣言・drafts・入口・監査スクリプトは無変更。旧F2／HomotopyLimits配置への新規追加なし。Δ／siftedの③-bの持ち分には手を付けていない。
- 鍵は `--wait 3600`、一枚ずつ、ビルド・宣言監査の間だけ保持。待ち時間による停止はしていない。

**②の残る数学はなし。段2の①は未着手。停止点1で止まり、調整役の検収を待つ。**

### 今回の新規ファイルと公開宣言

パスはすべて `SerrePositivity/InfinityCategories/` 以下（KL-W1後の配置）。

| 新規ファイル | 行数 | 宣言数 |
| --- | ---: | ---: |
| [SectionsLimitShapeValueComparison.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SectionsLimitShapeValueComparison.lean) | 80 | 3 |
| [SectionsLimitValueInverse.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SectionsLimitValueInverse.lean) | 40 | 1 |
| [SetWeightActualSectionsRestriction.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightActualSectionsRestriction.lean) | 53 | 2 |
| [SetWeightLimitTailConeSquare.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightLimitTailConeSquare.lean) | 69 | 2 |
| [SetWeightMappedSectionsEdge.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightMappedSectionsEdge.lean) | 67 | 4 |
| [SetWeightSectionsLimitTailShape.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsLimitTailShape.lean) | 77 | 1 |
| [CartesianSectionsRestrictionEvaluation.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/CartesianSectionsRestrictionEvaluation.lean) | 48 | 2 |
| [ConeSectionsMapShapeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsMapShapeNaturality.lean) | 58 | 1 |
| [ConeSectionsValueShapeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConeSectionsValueShapeNaturality.lean) | 58 | 2 |
| [ConstantSourceMapShapeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConstantSourceMapShapeNaturality.lean) | 67 | 2 |
| [ConstantSourceRelativeShapeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConstantSourceRelativeShapeNaturality.lean) | 108 | 3 |
| [ConstantSourceRestrictedRelative.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConstantSourceRestrictedRelative.lean) | 69 | 3 |
| [ConstantSourceShapeCoordinates.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/ConstantSourceShapeCoordinates.lean) | 50 | 1 |
| [NormalizedSectionsValueShape.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/NormalizedSectionsValueShape.lean) | 52 | 2 |
| [SmallSectionsComparisonEvaluation.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/SmallSectionsComparisonEvaluation.lean) | 65 | 1 |
| [SmallSectionsShapeNaturality.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/SmallSectionsShapeNaturality.lean) | 78 | 2 |
| [UnstraighteningSectionsRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/LimitsAndColimitsOfSpaces/UnstraighteningSectionsRestriction.lean) | 54 | 3 |
| [ConeCylinderShapeRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/ConeCylinderShapeRestriction.lean) | 41 | 2 |
| [ConeTransformationShapeRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/ConeTransformationShapeRestriction.lean) | 40 | 1 |
| [SourceConstantShapeRestriction.lean](../../SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/TheSliceAndJoinConstructions/SourceConstantShapeRestriction.lean) | 47 | 2 |
| [SetWeightEndpointShapeSquare.lean](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightEndpointShapeSquare.lean) | 111 | 4 |

| 公開宣言（末尾の名前） | 主張 |
| --- | --- |
| `coneApexEdgeAt` | 錐の辺の頂点を指定表示へ移した値の辺。 |
| `coneSectionsValueMap_edgeAtIso` | 始点の表示を移しても、元の錐の辺の値と切断写像の全族比較を保つ。 |
| `sectionsLimitValue_normalizedShapeIso` | 元の切断制限と同じ指定極限比較は、制限錐からの指定辺の値に全自然。 |
| `coneSectionsValueMap_sectionsLimitValueIso` | 元の値の切断写像から同じ指定極限の値へ戻る全族は恒等射と同型。 |
| `setWeightActualSectionsRestriction` | 元の要素の圏に沿う、小さい切断空間の実際の制限。 |
| `setWeightConeValue_restrictionIso` | 指定された要素の圏の制限は、元の錐の値からの切断写像と全族で可換。 |
| `setWeightLimitTailConeFamilyIso` | 元の後段の二経路は、指定極限錐の固定端点模型で全族として同型。 |
| `setWeightLimitTail_homMk_eq` | 元の後段の二経路は、空間のホモトピー圏で同じ射を定める。 |
| `edge_source_transport_simplex` | 始点の表示の等式による移送は、辺の元の一単体を変えない。 |
| `setWeightSectionsMap_simplex` | 元の切断制限の辺は、同じ指定普遍辺の射影の一単体を保持する。 |
| `setWeightMappedSectionsConeEdge` | 元の指定普遍辺を同じ関手で写した錐の辺。 |
| `setWeightMappedSectionsConeEdge_simplex` | 同じ写された錐の辺の射影は、元の切断制限の辺の像と同じ一単体。 |
| `setWeightSectionsLimitTail_shapeIso` | 元の指定極限への後段は、実切断の制限と同じ普遍辺の標準後合成に全自然。 |
| `sectionsRestrictionTargetIso_evaluation` | 同じ指定引き戻し表示の相対比較の評価は、元の評価の第一射影。 |
| `sectionsRestrictionOfIso_relative_evaluation` | 相対表示へ送った実切断制限を評価すると、元の全評価の形状制限。 |
| `coneSectionsMapAt_shapeIso` | 同じ形状へ制限した錐の切断写像は、元の全切断写像の実際の制限と同型。 |
| `smallUnstraighteningSectionsIso_inv_shape` | 小さい切断表示の逆も、実際の形状制限と厳密に可換。 |
| `coneSectionsValueMapAt_shapeIso` | 元の錐の値の全切断写像は、同じ形状の小さい実切断制限と全族で可換。 |
| `constantSourceMappingSpace_baseChangeIso` | 定値始域を正規化しても、元の相対写像空間の底変換の全族同型を使える。 |
| `coherentConstantSourceMap_shapeIso` | 元の定値始域比較と実切断の制限は、全変換空間からの写像として同型。 |
| `constantSourceRelativeShapePre` | 定値始域の実際の底変換射で、元の標的への相対写像を前合成する。 |
| `constantSourceRelativeShapePre_comparison` | 始域の制限を元の指数同型で読むと、同じ実切断の制限への後合成。 |
| `constantSourceRelativeShapePost_comparison` | 標的の底変換射による相対後合成を、同じ相対指数同型の下で読む。 |
| `constantSourceRestrictedOverIso` | 定値始域の元の直積表示を、指定された底の射で後合成する。 |
| `constantSourceRestrictedRelativeIso` | 制限された定値始域の相対関手空間を、全 fiber からの相対関手空間へ移す。 |
| `constantSourceRestrictedRelativeIso_evaluation` | 同じ相対指数同型の二重評価は、定値始域の元の逆表示による全評価。 |
| `constantSourceOverIso_inv_shape` | 元の定値始域の直積座標では、形状制限は底だけの前合成になる。 |
| `normalizedSmallSectionsRestriction` | 同じ小さい実切断の制限を、指定図式の表示へ移した射。 |
| `coneSectionsValueMapAt_normalizedShapeIso` | 指定表示へ移した制限も、元の錐の値からの切断写像を全族で保つ。 |
| `smallUnstraighteningSectionsIso_evaluation` | 元の大小の切断比較は、全評価を元の全空間の縮小同型で結ぶ。 |
| `smallUnstraighteningSectionsRestriction_map_evaluation` | 小さい実切断制限の評価は、小さい全空間の元の底変換射と可換。 |
| `smallUnstraighteningSectionsIso_shape` | 元の大小の切断同型は、同じ形状の実切断制限と厳密に可換。 |
| `unstraighteningSectionsRestriction` | 元の図式の全切断を、指定形状の引き戻しに制限する実際の射。 |
| `unstraighteningSectionsRestriction_evaluation` | 制限した切断の評価は、元の全評価を形状に沿って引き戻したもの。 |
| `unstraighteningSectionsRestrictionTargetIso` | 制限後の切断を元の相対関手空間へ送る、同じ引き戻し表示の同型。 |
| `fatConeCylinderEmbedding_naturality` | 円柱へ左の一点を補う操作は、右の形状写像と可換。 |
| `coneCylinderMap_naturality` | 元の錐の円柱は、形状の制限後も同じ join への写像になる。 |
| `coneTransformationPointAt_shapeRestriction` | 同じ形状制限で得た錐の標準変換は、元の標準変換の実際の制限。 |
| `sourceConstantShapeRestriction` | 定値始域の指定頂点を保持した、変換の全空間の形状制限。 |
| `sourceConstantShapeRestriction_prism` | 制限した全変換の円柱は、元の円柱の同じ形状への制限そのもの。 |
| `limitConeEndpointComparison_restrictAtIso` | 元の制限錐を指定表示しても、固定端点模型での全族比較を保つ。 |
| `postcompose_source_transport` | 辺の始点の表示変更は、標準後合成の始域の表示変更に一致する。 |
| `setWeightEndpointRestriction_sectionsMapIso` | 同じ指定普遍辺の後合成は、固定端点錐の元の形状制限と全族で可換。 |
| `setWeightLimitTail_endpointRestrictionIso` | 元の後段を固定端点模型へ送る比較は、元の錐の族の制限に全自然。 |


## 13. 段2の途中：元の比較を区間族へ（11-12夜、作業継続）

main `30ea26711` を取り込み、①に着手。②の宣言は変更していない。
下書きを含む追加量が見込み下端1,300行の半分を超えたので、早めの中間報告を記録する。

- **検証済み**：2本・107行・7宣言、`395bda0b4`。`SetWeightOppositeCoefficientsNaturality` と
  `WeightedCosliceBaseNaturality`。反転係数までの元の比較の自然性、および元の左 coslice 比較と
  添字の制限との厳密な可換性を証明。対象ビルド6,132 jobs成功、7宣言すべてsorry-free、標準三公理のみ。
  ログ `/tmp/is-w1/stage2/build-2.log`、`build-4.log`、監査入力 `audit-early.lean`。
- **未検証**：作業木の9本・607行。合計11本・714行。自然変換の区間図式の要素の圏、
  元のpointed比較の両端・底の照合、元の普遍持ち上げを任意の始域へ制限する相対比較、
  そこから構成する `setWeightElementsUnstraightening_naturality` の型まで書いた。
  これらはまだ成果として扱わず、対象ビルドで型エラーを修正中。
- **証明の筋**：区間上の要素の圏 → 元の比較のpointed区間族 → 元の `spaceDiagramEdge` の
  全prismとの底の一致 → 相対延長の可縮性 → 相対写像空間内の頂点同型。
  `StrictKanPointedComparison`、`relativeFunctorExtensionEndpoint_witnessIso` を再利用する。
  点ごとの一致に弱めず、比較同型を最終主張の仮定にも追加しない。
- **残りの見込み**：上記の検証・修正に100〜350行、元の切断同値への接続・宇宙比較に400〜800行、
  ②と合わせた篩包含の最終四角形に150〜300行。現時点の完成見込みは約1,400〜2,300行で、
  §12の1,300〜2,500行と上限2,800行を維持。全単体の照合の検証結果で見直す。
- 入口・全体監査登録は未変更。新規ファイルだけで進め、鍵は`--wait 3600`、待ちは一枚、ビルド中のみ保持。

**停止点2ではない。①の全体は未完成で、作業を続ける。**


## 14. 段2の途中：pointed 区間族の検証（11-12夜、継続）

- `c998275ae`：新規6本・424行を追加検証。§13の2本と合わせて8本・531行・32宣言。
  `build-11.log` の対象監査は32宣言すべて sorry-free、標準三公理のみ。
  元の要素の圏の区間族、その pointed 比較の両端、元の普遍持ち上げの制限、
  相対延長の可縮性による比較、正本の切断同値の因子分解が通った。
- 残りは作業木の下書き。通常の自然変換の辺の全単体計算、元の切断表示と宇宙変更の比較、
  ①の全族比較と②との合成を対象ビルドで修正中。最終型は、任意の前層・指定極限錐を保ち、
  `sieveTensorEdge`・`sieveSectionsMap`・`tensorSpaceFunctor_setWeightHomNatural` をそのまま使う。
- 下書きを含め約1,450行。上限2,800行の範囲で継続。共有鍵の待ちは一枚で、編集時には保持しない。
- 既存の `RelativeBaseChangeComposition.relativeFunctorPost_overPre` と
  `simplicialSectionsRelativeIso_naturality` を再利用し、同じ可換性を新たに証明しない。

**停止点2ではない。通常の辺と区間模型の全単体照合、および最終四角形の検証を続ける。**


## 15. 停止点2：G8 の篩包含の四角形①＋②（11-12夜）

**段2を完了。停止点2で止まり、調整役の検収を待つ。段3には進んでいない。**

- 数学の最終コミット：`9acf76bfb`（残り16本・1,032行）。段2の先行コミットは
  `395bda0b4` と `c998275ae`。段2全体は **新規24本・1,563行・65宣言**。
  既存の数学・入口・全体監査登録は変更していない。
- 見込みとの差：§12の1,300〜2,500行に対し1,563行（下端＋263、上端−937）。
  上限2,800行まで1,237行を残した。§13・§14で途中報告済み。
  区間上の要素の圏と元の辺の全単体照合を独立させ、②の値比較・固定端点比較を再利用したため、
  その部分を再実装せずに閉じられた。

### 最終主張の型

`η_X := (tensorSpaceFunctor_setWeightHomNatural X hE M F cX hcX).hom` と書く。
任意の小さい圏 C、篩 S ⊆ h_U、presentable な E、M ∈ E、任意の前層 F と
指定極限錐 cS・cU（それぞれの極限性）について、次を示した。F の層条件は仮定しない。

1. `setWeightElementsUnstraightening_naturality`：元の `elementsComparisonNatural` の
   大きい unstraightening 表示は、元の重みの辺の普遍持ち上げと、底を固定した相対写像空間内で同型。
   比較同型を入力にせず、区間族から実際に構成する。
2. `setWeightSectionsEquivalenceNatural_shapeIso`：元の重みの辺の前合成と
   `sectionsEquivalenceNatural` の順射の合成は、元の実切断制限との合成に全族で同型。
3. `sieveTensorSections_shapeIso`：
   `FunctorIso (precompose (functorVertex F) [sieveTensorEdge S hE M] ≫ η_S)
   (η_hU ≫ postcompose M [sieveSectionsMap S F cS hcS cU hcU])`。
   上辺・下辺・縦辺は元のG8のものを保つ。
4. `sieveTensorSections_homMk_eq`：3の二つの全写像空間の射を Kan 対象の coherent nerve の辺として読み、
   空間のホモトピー圏でその射が等しい。頂点ごとの主張には縮めていない。

これで①と既存の②を合わせた篩包含の四角形がそろった。BS の S4 の生成辺に渡す数学的な不足は残っていない。
一般の単体的な重みの射やG10は今回の範囲外。

### 証明と再利用

通常の自然変換を Fin 2 上の図式にし、その要素の圏から元の pointed 比較の区間族を作る。
元の `spaceDiagramEdge` の全単体とその区間模型を照合し、
`relativeFunctorExtensionEndpoint_witnessIso` で元の普遍持ち上げとの差を相対頂点同型にする。
`SetWeight.relativePreIso` に渡して全パラメータの前合成比較へ移し、
同じ縮小同型・ULift 同型・相対切断同型を使って元の `sectionsEquivalenceNatural` へ戻す。

再利用：`StrictKanPointedComparison`、`SetWeight.unstraighteningPinchedPrecompositionIso`、
`RelativeBaseChangeComposition.relativeFunctorPost_overPre`、
`simplicialSectionsRelativeIso_naturality`、`smallLeftUnstraighteningMap_comp`、
`tensorSpaceFunctor_diagramHom_weight_naturality`、段1の
`setWeightSectionsLimitTail_shapeIso` と `tensorSpaceFunctor_setWeightHomNatural_hom_factor`。
後段の指定極限・宇宙変更・表現可能値の比較、および固定端点の比較は段1のものをそのまま使う。

### 検証

- `lake build SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SieveTensorSectionsHomotopy`
  成功（6,246 jobs）。新規24本はこの依存閉包に含まれる。既存の直接 importer はまだない。
- 同じ鍵の中で `lake env lean /tmp/is-w1/stage2/audit-final.lean` 成功。
  新規24本を明示 import し、65宣言を `#check`・`#print axioms`・`#print sorries` で検査。
  **65宣言すべて sorry-free、公理は `propext`・`Classical.choice`・`Quot.sound` のみ**。
- 最終ログ：`/tmp/is-w1/stage2/build-30.log`。対象一覧：`audit-final-files.txt`、
  宣言一覧：`audit-final-decls.txt`（いずれも同じディレクトリ）。終了コード0。
- 鍵は `source ~/.zshenv` 後、`with_build_lock.sh --wait 3600 -- gtimeout --foreground 1700s …`。
  待ちは一枚。各ビルド失敗後は鍵を放して編集し、最後はビルドと監査の終了で解放。
- `git diff --cached --check` 成功。これは追加対象の監査であり、登録後のrootビルド・全体F2監査は調整役に委ねる。

### 登録対象の新規24本

| 新規モジュール（現行パスへのリンク） | 行数 |
| --- | ---: |
| [SetWeightBigRelativePrefix](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightBigRelativePrefix.lean) | 90 |
| [SetWeightElementsInterval](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightElementsInterval.lean) | 71 |
| [SetWeightElementsRelativeNaturality](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightElementsRelativeNaturality.lean) | 75 |
| [SetWeightIntervalCoordinates](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightIntervalCoordinates.lean) | 47 |
| [SetWeightOppositeCoefficientsNaturality](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightOppositeCoefficientsNaturality.lean) | 63 |
| [SetWeightPointedCoordinates](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightPointedCoordinates.lean) | 64 |
| [SetWeightPointedInterval](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightPointedInterval.lean) | 76 |
| [SetWeightPointedIntervalBase](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightPointedIntervalBase.lean) | 65 |
| [SetWeightRelativeUniverse](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightRelativeUniverse.lean) | 62 |
| [SetWeightSectionsBigRelativeComparison](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsBigRelativeComparison.lean) | 52 |
| [SetWeightSectionsEdgeNaturality](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsEdgeNaturality.lean) | 74 |
| [SetWeightSectionsPrefixFactorization](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsPrefixFactorization.lean) | 55 |
| [SetWeightSectionsRelativeEvaluation](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsRelativeEvaluation.lean) | 82 |
| [SetWeightSectionsRelativeNaturality](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightSectionsRelativeNaturality.lean) | 70 |
| [SetWeightUnstraighteningEdgePrecomposition](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SetWeightUnstraighteningEdgePrecomposition.lean) | 53 |
| [SieveTensorSectionsHomotopy](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SieveTensorSectionsHomotopy.lean) | 52 |
| [SieveTensorSectionsNaturality](../../SerrePositivity/InfinityCategories/HTT/PresentableInfinityCategories/SieveTensorSectionsNaturality.lean) | 56 |
| [KanDiagramOrdinaryEdgePrism](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/KanDiagramOrdinaryEdgePrism.lean) | 42 |
| [KanDiagramOrdinaryEdgeSimplex](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/KanDiagramOrdinaryEdgeSimplex.lean) | 121 |
| [LeftUnstraighteningEdgeLiftFamily](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningEdgeLiftFamily.lean) | 85 |
| [LeftUnstraighteningRestrictedWitness](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LeftUnstraighteningRestrictedWitness.lean) | 73 |
| [RelativeFunctorCompositionConstant](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorCompositionConstant.lean) | 37 |
| [RelativeFunctorOverUniverseNaturality](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorOverUniverseNaturality.lean) | 54 |
| [WeightedCosliceBaseNaturality](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/WeightedCosliceBaseNaturality.lean) | 44 |

### 追加宣言の一覧

- `setWeightElementsComparisonOver`：元の要素の圏の比較を、大きい底上の射として束縛する。
- `setWeightElementsBaseMap`：元の mapElements を、同じ大きい底上の射として束縛する。
- `setWeightBigRelativePrefix`：元の pinched 比較と、元の要素の圏の比較による前合成の全写像。
- `setWeightBigRelativePrefix_naturality`：元の pinched 比較と要素の圏による前合成は、元の重みの辺に全族で自然である。
- `setWeightIntervalDiagram`：重みの射を、区間と元の添字圏の直積上の集合値図式にする。
- `setWeightElementsIntervalZero`：元の始域の要素を、区間上の要素の圏の始点へ入れる。
- `setWeightElementsIntervalOne`：元の終域の要素を、同じ区間上の要素の圏の終点へ入れる。
- `setWeightElementsIntervalTransformation`：元の要素からその指定像へ向かう、区間上の要素の圏の自然変換。
- `setWeightElementsIntervalPrism`：要素とその指定像を全単体で結ぶ、元の自然変換の prism。
- `setWeightElementsIntervalPrism_zero`：区間族の始点は、元の要素の圏の始点への包含である。
- `setWeightElementsIntervalPrism_one`：区間族の終点は、元の mapElements と終点への包含の合成である。
- `setWeightElementsUnstraightening`：元の小さい要素の圏の比較を、同じ全空間の縮小同型で大きい表示へ移す。
- `setWeightElementsUnstraightening_projection`：大きい表示へ移しても、元の要素の圏の射影を保つ。
- `setWeightElementsUnstraightening_map_projection`：終域の元の比較を mapElements で制限しても、始域の元の射影を保つ。
- `setWeightElementsUnstraightening_naturality`：元の比較と元の重みの辺の作用の二経路は、底を固定した相対写像空間内で同型である。
- `setWeightElementsInterval_coefficients`：元の要素の区間族の係数は、同じ重みの通常の自然変換の係数図式である。
- `setWeightOppositeCoefficientsMap`：重みの射を、元の反転係数の射に写す。
- `setWeightCoefficientsOppositeIso_naturality`：元の定値係数の反転同型は、重みの実際の射と厳密に自然。
- `setWeightCoefficientsOppositeWeightedIso_naturality`：同じ反転係数同型の weighted nerve への像も、元の射と厳密に自然。
- `setWeightElementsOppositeWeighted_naturality`：元の要素の圏から反転 weighted nerve への比較は、底を変えず重みの射に自然。
- `setWeightElementsPointed`：元の要素の圏の比較の、宇宙を戻した全空間からの pointed 成分。
- `setWeightElementsPointed_formula`：元の比較の pointed 成分は、同じ係数同型と左 coslice の実際の比較で計算できる。
- `setWeightElementsPointed_base`：元の pointed 比較は、添字を通常の関手で制限しても全写像として可換である。
- `setWeightPointedInterval`：元の重みの射に沿って、元の pointed 比較を全単体で結ぶ区間族。
- `setWeightElementsPointed_intervalZero`：始点包含で制限した区間上の比較は、元の始域の比較そのものである。
- `setWeightElementsPointed_intervalOne`：終点包含で制限した区間上の比較は、元の終域の比較そのものである。
- `setWeightPointedInterval_zero`：pointed 区間族の始点は元の要素の圏の比較である。
- `setWeightPointedInterval_one`：pointed 区間族の終点は元の mapElements で制限した終域の比較である。
- `setWeightElementsPointed_projection`：元の pointed 比較は、要素の圏からの元の空間値図式を被覆する。
- `setWeightPointedInterval_projection`：元の pointed 区間族は、同じ spaceDiagramEdge の全 prism の底変換である。
- `setWeightRelativeUniverseIso`：元の要素の圏を始域に固定した、相対関手空間の大小の比較同型。
- `setWeightRelativeUniverse_pre`：元の小さい要素の圏の比較による前合成は、同じ大小の表示変更と厳密に可換。
- `setWeightSectionsBigRelativeIso`：正本の小さい切断表示から、元の大きい相対写像空間への指定同型。
- `setWeightSectionsEquivalenceNatural_bigRelative`：元の切断同値の順射を指定相対表示へ送ると、元の大きい相対比較そのものになる。
- `setWeightRelativeUniverseIso_restriction`：元の大小の相対表示の比較は、同じ要素の圏の前合成と厳密に可換。
- `setWeightSectionsBigRelativeIso_restriction`：元の小さい切断制限と大きい相対表示への比較は、同じ前合成で厳密に可換。
- `setWeightSectionsEquivalenceNatural_shapeIso`：元の切断同値の順射と元の重みの辺の前合成は、実切断制限と全族で自然である。
- `setWeightRelativeSectionsIso`：元の切断同値で使われる、相対関手空間から小さい切断への同じ同型。
- `setWeightSectionsEquivalenceNatural_hom_factor`：元の切断同値の順射は、同じ実写像と底変換同型の合成そのものである。
- `setWeightRelativeSectionsIso_inv`：元の相対切断同型の逆は、同じ指定引き戻しの切断比較である。
- `setWeightRelativeSectionsIso_inv_evaluation`：元の切断表示から相対表示への全評価は、元の小さい底変換射との合成。
- `normalizedSmallSectionsRestriction_map_evaluation`：指定表示へ正規化した実切断制限も、元の底変換射による全評価を保つ。
- `setWeightRelativeSectionsIso_restriction`：元の小さい切断制限は、元の相対表示への同型の逆と厳密に可換。
- `unstraighteningPinchedEdgeLiftPrecompositionIso`：元の pinched 前合成の比較は、元の全写像空間から取り出した実際の終点の前合成と同型。
- `sieveTensorSections_homMk_eq`：正本の G8 比較の篩包含の四角形は、全写像空間のホモトピー圏で可換。
- `sieveTensorSections_shapeIso`：篩包含の元のテンソルの前合成は、正本の G8 比較の下で元の切断辺の後合成に全自然。
- `kanDiagramNaturalTransformationEdge_prism`：元の実現した自然変換の辺の全 prism は、同じ通常の自然変換の coherent prism である。
- `kanDiagramUnderlyingTransformation`：忘却後の通常の自然変換を、元の Kan 複体の図式の自然変換として読む。
- `kanDiagramEdgeOrderDiagram`：区間の射と底の射列を同時に評価する元の通常の図式。
- `kanDiagramEdge_mixed_constant`：区間の二頂点間の混合評価は、同じ通常の自然変換と底の射の合成である。
- `kanDiagramDiagonalSimplex_edge`：元の実現した辺の任意の対角単体は、同じ通常の区間図式の coherent 表示である。
- `leftUnstraighteningEdgeLiftFamily`：元の全写像空間の持ち上げを、同じ辺の頂点で制限する。
- `leftUnstraighteningEdgeLiftMap`：元の全写像空間の終点の族を、同じ辺の頂点で制限する。
- `leftUnstraighteningEdgeLiftMap_projection`：制限した終点は元の底への射影を保つ。
- `leftUnstraighteningEdgeLiftFamily_zero`：制限した区間族の始点は、元の unstraightening の pointed 成分である。
- `leftUnstraighteningEdgeLiftFamily_projection`：制限した区間族は、元の辺の全 prism を被覆する。
- `leftUnstraighteningEdgeLiftFamily_one`：制限した区間族の終点は、同じ全写像空間の終点写像の pointed 成分である。
- `leftUnstraighteningEdgeLiftMap_vertex`：元の写像空間の比較の辺での値は、取り出した終点写像の相対頂点である。
- `leftUnstraighteningRestrictedWitnessIso`：同じ始点と底を持つ実区間族の終点は、元の辺の作用を制限した射と相対写像空間内で同型。
- `relativeFunctorComposition_const_first`：相対合成の第一成分を固定した全族は、同じ実射による前合成である。
- `uliftRelativeFunctorMap_overPre`：底上の前合成は、同じ底を保つ相対関手空間の宇宙持ち上げと可換。
- `relativeFunctorOverIso_pre_hom`：始域を同型で写してから前合成する四角形は、同じ標的の同型による移送と可換。
- `weightedConeSimplex_base`：添字の関手で射列を写した cone simplex は、制限した図式の元の simplex と一致する。
- `weightedCosliceSimplex_base`：元の左 coslice の単体は、添字を制限しても同じ単体である。
- `weightedCosliceComparison_base`：元の左 coslice 比較の全写像は、weighted nerve の添字制限と厳密に可換である。


## 16. 夜の再開：G14 の再見積もり（11-12夜、停止点3ではない）

main `de2dd0a53` を取り込んだ。段2は main に含まれる。夜の指示に従い段3へ着手した。
新規 `ReflectedRepresentableGenerators.lean` に、小さい底 A の頂点を添字とする
`reflectedRepresentable L y := L(y(y))`、指定された adjunct 比較、同値性、
任意の Ho(E) の射への全族自然性を記述した。ビルド・監査結果は次の追記で確定する。

### 上限の見直し

G14 の結論の型・範囲は変えない。元の `yonedaPresheafEvaluation` の順射は
(1) pinched mapping → 大きい相対写像空間、(2) 小さい相対表示への移送、
(3) 表現可能 coslice の恒等錐での相対評価、(4) lifted fiber と元の値との比較、の合成。
対象ごとの同値性は既存だが、この合成全体について、同じ Ho の射の後合成と
`presheafInfinityEvaluation` の射の対応を渡す定理はまだない。
`RightFibrationYonedaNaturality` は slice の評価の底上の射への自然性であり、
この pinched Hom からの合成全体の標的自然性の代用にはならない。

段2の実測（区間模型・相対自然性・小さい表示への接続で約1,400行）を踏まえた保守的な再見積もり：

| 残る接続 | 見込み行数 |
| --- | ---: |
| 元の変換辺の後合成と unstraightening の相対後合成（全族） | 450〜700 |
| 縮小・相対恒等点評価・lifted fiber の標的自然性の合成 | 450〜700 |
| 随伴と Yoneda の同じ比較射への接続・Ho と ULift の照合 | 250〜400 |
| 前層の各点可逆性、充満忠実な右随伴の反映、存在の結論 | 300〜450 |
| 最初の族と検証時の接続修正 | 100〜200 |
| 合計 | **1,550〜2,450** |

これは必要行数の下界ではなく、短い既存 API が見つからない現時点の実装予測。
上端が段3の上限1,800行を超えるため、上限超過が見込まれる条件に当たると判断する。
型を弱めたり自然性を仮定した検出族を結論にしたりはしない。
検証済みの最初の部品を保存した後、この線の Lean を止め、夜の代替作業 A-1 段0に移る。
G9・3b-3の実装にはまだ進んでいない。3b-3については IS-W2 §0・§3・§8・§10 と
③-b報告§21.3・§21.4を確認済み。見込み4,850〜7,150行のうち、全パラメータ・同じ指定余錐の族
450〜750行は3b-1からの移管分であり、対象ごとの比較だけで完了とはしない。


### 検証済みの保存と代替作業の結果

- `52aec0a75`：`ReflectedRepresentableGenerators.lean`、新規1本・58行・4宣言。
  `reflectedRepresentable` は元の小さい頂点型を添字とする族、
  `reflectedRepresentableMapping` は同じ随伴の指定比較、
  `reflectedRepresentableMapping_isQCatEquivalence` はその全写像空間の同値性、
  `reflectedRepresentableMapping_naturality` は任意のHo(E)の射への全族自然性。
- 対象ビルド成功（5,870 jobs、`/tmp/is-w1/stage3-build-1.log`）。
  追加4宣言の監査成功（`/tmp/is-w1/stage3-audit.lean`、`stage3-audit.log`）。
  全4宣言sorry-free、標準三公理のみ。鍵を解放済み。
- 未検証のLean下書きは残していない。G14の結論・G9・3b-3は未完成。
- 夜の指示の代替作業として、[A-1段0](report-bs-infinity-a1-stage0.md)を作成。
  S1〜S8の型案、本体の再利用、不足、規模、draftsの注意点、配置と順序を整理した。
  特にCAlg忘却の層化単位の比較と、大きいsiteの小ささの境界は判断点として記録。
  draftsの型や範囲は変更していない。


## 17. 段3の再開（11-13、継続中）

指示書追記と main `ecc0f2a5f` を取り込み、上限を段3 **3,200行**、段4 **1,600行**へ訂正。
§16の五行だけを進める。約1,600行の非停止の途中報告と、停止点3から段4へ進む指示を確認。
§16の上限判断で止めたG14を再開した。A-1のS6は小さい模型へのsite同値に沿う輸送だけとし、
κ切り落とし・BS固有の閉性表を作らない。S7の単位条件は5∞-1段0で確認する。

### 検証済みの最初の束

`81f4f2019`：新規5本・291行・6宣言。最初の58行と合わせ、G14累計349行・10宣言。
§16第一行と第二行の一部を実装。対象ビルド成功（3,348 jobs）、6宣言はすべてsorry-free、標準三公理のみ。
最終ログ `/tmp/is-w1/stage3-build-13.log`、監査 `/tmp/is-w1/stage3-audit-progress.lean`。

- `intervalPostcompose_triangleFamily_exists`：元の後合成と同じ三辺の全三角形族。
- `unstraighteningPostcompositionIso`：区間後合成を元のunstraighteningの相対合成へ全族で比較。
- `unstraighteningPinchedEdgeLiftPostcompositionIso`：同じpinched後合成を、元の全変換空間から取り出す実際の終点射の後合成へ比較。
- `relativeFunctorComposition_const_second`：第二成分を実射に固定した相対合成は通常の相対後合成。
- `relativeFunctorEvaluate_post`：同じ底上の標的射への相対評価の厳密な自然性。
- `transformationEdge_pointedFiberValueIso`：元の全変換空間の指定辺のpointed fiber作用と、同じ辺の点でのKan値の全fiber比較。

再利用：`intervalFamilyHom_triangle_exists`、`unstraighteningMappingTriangleIso`、
`relativeFunctorPostHom_vertex`、`uncurry_const_functorVertex`、
`leftUnstraighteningMappingFiberHom_parametrizedIso`、`pointedTransformationFiberHom_vertex`、
`parametrizedFiberTransport_at_edgeIso`、`spaceInfinityEdgeTransportValueIso`。
特にfiberの全族輸送比較が既存にあったため、その理論を再実装せず制限して使えた。

この後の作業木は、縮小表示への後合成自然性・元の表現可能恒等錐での評価の自然性の下書き。
既存 `uliftRelativeFunctorMap_post` を再利用し、同名の重複は作らない。
**停止点3ではない。G14の検出性の結論と段4は未完成で、続行する。**


## 18. 停止点3：G14 完了（11-13朝）

**G14の結論を完了。報告をコミットし、承認済みの順序で段4へ進む。**

最終数学 `ef94bfeaa`（新規10本・535行）、途中 `81f4f2019`（5本・291行）、先行 `52aec0a75`（1本・58行）。
段3全体は **新規16本・884行・21宣言**。新規ファイルだけで、既存の宣言の変更なし。

### 結論と証明

`Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_detectingFamily`：
E : SSet.{u+1} が presentable なら、ι : Type u と M : ι → E₀ が存在し、任意の Ho(E) の射 f について
`IsIso f ↔ ∀ i, IsQCatEquivalence (MorphismSpaces.postcompose (M i) f)`。
`IsDetectingFamily` はこの右辺を使う元の検出性の定義。自然性・検出性を追加入力にせず、小さい添字を保つ。

小さい前層反映 L ⊣ R を一度固定し、M(a)=L(y(a)) とする。同じ随伴比較の全族自然性、
元の `yonedaPresheafEvaluation` の後合成自然性、前層の各点可逆性を合成して R(f) を可逆と判定。
充満忠実な R の Ho での反映により f を可逆とする。順方向は元の逆射による pinched 後合成を逆に使う。
対象ごとの同値だけに弱めず、全写像空間の FunctorIso を使った。

### 見込みと実測

段0改訂見込み800〜1,600行、§16の再見積もり1,550〜2,450行に対し884行。
現行上限3,200行以内。完成時点が約1,600行の途中報告点より前なので、今回が完成報告となる。
短くなった理由は、既存 `leftUnstraighteningMappingFiberHom_parametrizedIso` と
`pointedTransformationFiberHom_vertex`、標準輸送の値比較を発見して再利用でき、
四段の自然性を新しい輸送理論を作らず合成できたため。§16の五行以外のまとまりは追加していない。
小さな同定として独立追加したのは、相対合成の第二成分の固定と相対評価の後合成の2本。

| §16の行 | 実装した内容 |
| --- | --- |
| 1 | 元の区間後合成の三角形族、unstraighteningの相対合成、元のpinched後合成と同じ実射の後合成の全族比較 |
| 2 | 相対表示の大小比較、元の恒等錐での表現可能評価、同じfiberの値比較の自然性 |
| 3 | 元のYoneda評価の四段の因子分解の全族後合成自然性、指定随伴比較への接続 |
| 4 | 全表現可能前層による辺と任意のHoの射の検出、可逆射の後合成同値、充満忠実なRの反映 |
| 5 | 同じ反映から小さい族を構成し、存在の結論まで接続・検証 |

### 検証

- `lake build SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DetectingFamily`
  成功（5,898 jobs）。全16本を依存閉包に含む。
- `/tmp/is-w1/stage3-audit-final.lean`：16本を明示importし全21宣言を `#print axioms`・`#print sorries` で監査。
  **21宣言すべてsorry-free、標準三公理のみ**。終了コード0。
- 最終ログ `/tmp/is-w1/stage3-build-28.log`。対象一覧 `stage3-final-files.txt`、宣言一覧 `stage3-final-decls.txt`。
  いずれも `/tmp/is-w1/`。ビルドと監査は `--wait 3600`、整理券一枚、鍵は実行中だけ保持し解放済み。
- `git diff --cached --check` 成功。本体入口・全体監査登録は調整役に委ねる。

### 登録対象と宣言

| 新規モジュール | 行数 |
| --- | ---: |
| [RelativeFunctorCompositionFixedTarget](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorCompositionFixedTarget.lean) | 43 |
| [RelativeFunctorUniversePostNaturality](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/RelativeFunctorUniversePostNaturality.lean) | 38 |
| [SmallRelativePostNaturality](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SmallRelativePostNaturality.lean) | 58 |
| [SmallTransformationEdgeFiberValue](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/SmallTransformationEdgeFiberValue.lean) | 49 |
| [TransformationEdgeFiberValue](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/TransformationEdgeFiberValue.lean) | 59 |
| [TransformationEdgeFiberValueComparison](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/TransformationEdgeFiberValueComparison.lean) | 54 |
| [RelativeFunctorEvaluationPostcomposition](../../SerrePositivity/InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/RelativeFunctorEvaluationPostcomposition.lean) | 37 |
| [DetectingFamily](../../SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/DetectingFamily.lean) | 60 |
| [ReflectedRepresentableGenerators](../../SerrePositivity/InfinityCategories/Kerodon/LargeInfinityCategories/PresentableInfinityCategories/ReflectedRepresentableGenerators.lean) | 58 |
| [PostcompositionIsoEquivalence](../../SerrePositivity/InfinityCategories/Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces/PostcompositionIsoEquivalence.lean) | 32 |
| [PresheafRepresentableEdgeDetection](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/PresheafRepresentableEdgeDetection.lean) | 59 |
| [PresheafRepresentableHomDetection](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/PresheafRepresentableHomDetection.lean) | 48 |
| [RepresentableUnstraighteningEvaluationPost](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/RepresentableUnstraighteningEvaluationPost.lean) | 51 |
| [YonedaPresheafEvaluationPostcomposition](../../SerrePositivity/InfinityCategories/Kerodon/TheYonedaEmbedding/TheYonedaEmbedding/YonedaPresheafEvaluationPostcomposition.lean) | 86 |
| [IntervalPostcompositionTriangle](../../SerrePositivity/InfinityCategories/Project/HomotopyDiagramComparison/IntervalPostcompositionTriangle.lean) | 39 |
| [SetSectionsUnstraighteningPostcomposition](../../SerrePositivity/InfinityCategories/Project/SetWeightedTensors/SetSectionsUnstraighteningPostcomposition.lean) | 113 |

- `relativeFunctorComposition_const_second`：相対合成の第二成分を固定した族は、同じ底上の射による後合成。
- `relativeFunctorOverIso_post_hom`：同じ底上の同型と可換四角形による相対 Hom の表示変更は、後合成に自然。
- `smallLeftUnstraighteningRelativeFunctorIso_post`：元の大小の相対写像空間の比較は、縮小した同じ全空間の射の後合成と厳密に可換。
- `smallTransformationEdge_fiberValueIso`：元の縮小fiberの値比較は、同じ全変換空間の終点射のfiber作用に全自然。
- `transformationEdge_pointedFiberValueIso`：元の変換辺のpointed fiberへの作用は、同じ辺の点での値と全fiberで可換。
- `transformationEdge_fiberValueIso`：同じ元の終点射のfiber作用は、元のfiber値比較の下で各点の空間辺の作用に全自然。
- `relativeFunctorEvaluate_post`：相対評価は、同じ標的の射がfiberに誘導する射と厳密に可換。
- `IsDetectingFamily`：元の全 pinched 写像空間の後合成の同値性によって射の可逆性を検出する族。
- `exists_detectingFamily`：任意の presentable 準圏には、Type u を添字とする実際の写像空間の検出族が存在する。
- `reflectedRepresentable`：表現可能前層を同じ左随伴で移した、元の小さい頂点型を添字とする族。
- `reflectedRepresentableMapping`：反映した表現可能対象からの写像空間を、同じ右随伴の像への写像空間に送る。
- `reflectedRepresentableMapping_isQCatEquivalence`：指定された adjunct 比較は、全写像空間の同値である。
- `reflectedRepresentableMapping_naturality`：生成族の adjunct 比較は、元の標的の任意の射の後合成に全族で自然。
- `postcompose_isQCatEquivalence_of_isIso`：可逆な射の元の pinched 後合成は、元の逆射の後合成を逆とする同値。
- `presheafEdge_isInvertible_of_representable_post`：全表現可能前層からの後合成の同値性は、元の前層の辺の可逆性を検出する。
- `presheafHom_isIso_of_representable_post`：全表現可能前層からの元の後合成の同値性は、前層のホモトピー圏の射の可逆性を検出。
- `representableUnstraighteningEvaluation_post`：元の恒等錐による表現可能評価は、標的の射が誘導するfiberの射と厳密に可換。
- `yonedaPresheafEvaluation_postcomposeIso`：元の Yoneda 評価は標的の元の辺の後合成と、同じ点での空間値の作用に全自然。
- `intervalPostcompose_triangleFamily_exists`：指定辺による元の後合成は、同じ三辺を持つ全パラメータの三角形で表せる。
- `unstraighteningPostcompositionIso`：指定辺の後合成を元の全空間の相対合成と比較する全パラメータの同型。
- `unstraighteningPinchedEdgeLiftPostcompositionIso`：元の pinched 後合成は、同じ辺の実際の持ち上げによる相対後合成と全族で同型。


## 19. 停止点4：G9-1〜3 完了（11-13朝）

**段4を完了。段4の後の仕事は③-bとB3の状況で調整役が決める指示なので、ここで区切る。**
3b-3の実装には着手していない。

数学コミット **`0d2db4d50`**。新規3本・121行・4宣言。
§12の改訂見込み350〜800行に対し121行（下端−229、上端−679）、現行上限1,600行以内。
完成が途中報告の行数に達する前なので、今回は完成報告を兼ねる。
短くなった理由は、単体集合版left Quillen A、通常commaの指定同型、right版uliftが既にあり、
元の写像の比較だけを追加して済んだため。各版の理論を複製していない。

### 型と再利用

- **G9-1 `nerveMap_isLeftCofinal_of_weaklyContractible_comma`**：
  P・Q : Type u、Category.{u}、F : P ⥤ Q。各 q について `nerve (CostructuredArrow F q)` が弱可縮なら
  `IsLeftCofinal (nerveMap F)`。`nerveLeftKanShapeIso F q` が射影を保つ元の同型であることを使い、
  `isLeftCofinal_of_weaklyContractible_slices` へ渡す。始対象の存在やnerveのKan性は仮定しない。
- **G9-2 `isLeftCofinal_ulift`**：
  任意の小さい単体集合の射 f がleft cofinalなら `(SSet.uliftFunctor.{v,u}).map f` もleft cofinal。
  vは任意（要求されたu+1への場合を含む）。`hf.op`、既存 `isRightCofinal_ulift`、
  `uliftOppositeIso` の矢の同型、反転判定を順に使う。大きい試験fibrationを小さいものに制限していない。
- **G9-3 `nerve_isWeaklyContractible_of_contractionCospan`**：
  C : Type u、Category.{u}、v : C、T : C ⥤ C、`𝟭 C ⟶ T` と `const v ⟶ T` があればnerve Cは弱可縮。
  一般単体集合版 `isWeaklyContractible_of_contractionCospan` も供給。
  元の二つの自然変換を `nerveNatTransHomotopy` へ移し、Kan標的の関手空間で
  `functorIsoPrecompositionOfHomotopy_kan` を反転・合成して点への射の弱同値性を得る。
  Cの始対象・終対象、nerve CのKan性、元の自然変換の逆は要求しない。

### 検証

- 上の3モジュールを同時対象ビルドし成功（2,440 jobs）。ログ `/tmp/is-w1/stage4-build-1.log`。
- `/tmp/is-w1/stage4-audit.lean` に明示importし全4宣言を監査。`stage4-audit.log` は終了コード0、
  **4宣言すべてsorry-free、標準三公理のみ**。
- 鍵は `--wait 3600`、整理券一枚、ビルド・監査中のみ保持し解放済み。
  `git diff --cached --check` 成功。既存の数学・入口・全体監査登録は変更していない。
- 停止点3と4の合計は **新規19本・1,005行・25宣言**。
  各対象監査は完了。登録後のrootビルド・全体F2監査は調整役に委ねる。

### 登録対象

- [WeakContractibleContractionCospan](../../SerrePositivity/InfinityCategories/Kerodon/KanComplexes/HomotopyGroups/WeakContractibleContractionCospan.lean)：56行。
- [LeftCofinalUniverseLift](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/LeftCofinalUniverseLift.lean)：30行。
- [NerveLeftQuillenA](../../SerrePositivity/InfinityCategories/Kerodon/LimitsAndColimits/Cofinality/NerveLeftQuillenA.lean)：35行。


## 20. 3b-3 段0（11-13、見込み上端超過のため実装前で停止）

main `bf5536ccc` を取り込んだ。3b-1（登録 `cfa0e8324`）は本体にある。
IS-W2 §0・§3.2・§8・§10、③-b報告§21.3・§21.4・§38.1〜§38.2を照合した。
§38は本体側の報告がまだ§21までのため、共有worktree `../SerrePositivity-bs-d68/` の同じ報告を読んだ。
⑤b枝のmerge・コードimport・編集はしていない。3b-2の未取込ファイル・G10を入力にしない。

### 型案（加群版だけ）

A : Type u、CommRing A。Jは `SimplexCategory` とその反対圏の二つだけ。
`I_J := (SSet.uliftFunctor.{u+1,0}).obj (nerve J)`、`DA := derivedInfinityCategory A`、
`D_J := (ihom I_J).obj DA` とする。`Complex A` は本体の dg 複体模型の閉零圏として扱う。

1. `W_J(f) := ∀ j, QuasiIso (f.app j)` を持つ strict な複体図式の相対圏と、その∞局所化模型
   `S_J := StrictDiagramInfinity A J` を構成する。局所化写像 `q_J : nerve (J ⥤ Complex A) ⟶ S_J` は
   W_Jの辺を反転し、`IsLocalization q_J W_J` を結論に持つ。W_Jの辺の集合への変換も明示する。
2. 実評価 `ev_J : S_J ⟶ D_J` と `IsQCatEquivalence ev_J`。
   下の全関手同型を合わせて返す：
   `FunctorIso (q_J ≫ ev_J) strictComplexDiagramFamily`。
   ここで右辺は元のstrict図式の射列をDAへ送る実評価。対象ごとの表示の選択で代用しない。
3. 任意パラメーター P と `P ⟶ D_J` の族を、同値の逆と単位・余単位の全族同型でS_Jへ運ぶ。
   対応する join 錐・余錐の族を両方向に運び、往復を元の図式同型に沿う同型として返す。
   元の頂点を固定した比較、脚・全高次単体の互換、極限性／余極限性の保存を含む。
4. J=Δᵒᵖについて、strict実現の全パラメーターの関手と
   `strictSemifreeNativeApexFamily` の FunctorIso、さらに元の標準脚を持つ指定余錐族の比較。
   これが§38.1第四行の受け渡し。Totの全族比較は③-b、BE値の厳密化は§38.2の③-bに残す。

S_Jの宇宙はDAと同じ u+1 の模型を目標にする。raw hammockの構成の宇宙を無条件に同じと扱わず、
projectiveなdg図式の模型等で小さいHomと評価を確認する。元の複体を対象ごとに独立選択して固定したまま
厳密化する主張はしない。strict模型の値を置換できる形で、元の評価との全関手同型を結論にする。

### 本体の再利用

- `DiagramComparison/StrictSemifreeDiagram` の `strictSemifreeEvaluation`・`strictSemifreeDiagram`：
  strict図式圏の全nerveにわたる実評価。これは局所化後の評価同値そのものではない。
- `StrictSemifreeColimitFamily` の `strictSemifreeDiagramFamily`・`strictSemifreeColimitFamily_projection`・
  `strictSemifreeJoinCoconeFamily`・`strictSemifreeNativeApexFamily`：同じ全高次単体の指定余錐族を再利用。
  その選択だけから具体的実現の全関手比較が出たとは扱わない。
- `StrictSemifreeRealizationCocone`、`StrictSimplicialDerivedCocone`、`SpecifiedProjectiveCocone`：
  3b-1の図式ごとの同じ頂点・標準脚の余錐と余極限性を使う。native barを作り直さない。
- `SemifreePointComparison.semifreePointEquivalence`、`derivedInfinityCategory`、dg nerve・
  projective加群の既存比較：値のDAへの接続。図式圏の写像空間の比較は別に要る。
- `HomotopicalAlgebra/Diagram/Projective.modelCategory`・`modelCategory_weakEquivalences`：
  通常の図式圏のobjectwise弱同値とprojective置換。これは∞関手圏比較を結論には持たない。
- `DGModuleFunctorResolutionNerve.dgModuleFunctorResolutionSourceNerve_isQCatEquivalence`：
  dg関手の入力射影の既存比較。任意のcoherent図式からstrict図式への持ち上げを結論に持つものではない。
- G8の全写像空間の随伴比較は指定余錐の全族自然性、G14は写像の同値性の検出、
  G9はbarの添字のleft cofinal性・uliftに再利用できる。これらから図式圏の局所化同値を直接結論しない。
- `ColimitCoconeFamilies` と既存の cone/cocone の関手単体集合・図式同型による比較を輸送へ使う。
  図式同型の往復を指定錐の全パラメーターで読む接続は新規。

除外する候補：`HomotopicalAlgebra/Rectification/HomotopyFunctionComplex/LocalizedMappingBifunctor`
は `[ModelCategory SSet]` を要求し、ordinary homotopy category値の族を延長するもので、docstringも
strictなSSet値rectificationを別課題と明記する。`Rectification/Simplicial/StrictValueObstruction`
も同じモデル圏仮定を持ち、独立に固定した値を保つ厳密化の障害の定理。どちらも今回の同値の代用にしない。

### 型つきの残りと見込み（新規実装分）

| # | 結論・受け渡しの型 | 不足の中身 | 見込み行数 |
| --- | --- | --- | ---: |
| R1 | `q_J` と `IsLocalization q_J W_J`、同じ閉零strict図式からの写像 | projective/dg図式模型とobjectwise擬同型の∞局所化を接続。通常のprojective模型の存在だけでは足りない | 600〜1,000 |
| R2 | 各X,Yで `pinchedHomMap ev_J X Y` が同値 | 局所化後の図式間の写像空間と、coherent図式の全変換空間の比較。strict自然変換の通常endやH⁰だけでは代用不可 | 2,200〜3,200 |
| R3 | `IsEssentiallySurjective ev_J` と全関手の逆・単位・余単位 | 任意の `I_J ⟶ DA` のcoherent作用をstrict複体図式へ置換。対象と射の個別表示だけで高次単体を補ったとはしない | 1,800〜2,600 |
| R4 | 任意Pの錐／余錐族の両方向輸送と往復、極限性／余極限性の保存 | 図式射への自然性、指定頂点・脚・join全体の整合性。既存の錐の比較の接続 | 900〜1,500 |
| R5 | `FunctorIso (q_J ≫ ev_J) strictComplexDiagramFamily` と同じ元の射の照合 | 局所化の評価と元の全nerve評価の一致。Semifree表示と全複体表示の比較もここに数える | 500〜900 |
| R6 | strict実現の全関手同型と同じ指定余錐の全族比較 | §8の移管分。3b-1の各図式の同型を元の射・高次単体・標準脚と同時に自然化 | 450〜750 |
| R7 | 同じ宇宙の型・端点表示の整合性 | 小さいHom・ULiftの同定、同型を通す評価と射影の局所接続。一般の形状へ範囲を広げない | 250〜450 |
| 合計 | | | **6,700〜10,400** |

§21.3の4,850〜7,150行より上端が増えた理由は、R2・R3で必要なHTT 4.2.4.4の内容を、
既存の通常図式模型・写像空間の局所比較・3b-1の図式ごとの余錐だけから短く適用できる定理として
確認できなかったため。特にR2の全変換空間とR3の全高次単体を持つstrict化を分けて数えた。
これは必要行数の下界ではなく、今回のAPI照合に基づく実装予測。

**上端10,400行が条件付き事前承認の7,150行を超えるため、段0を報告して止める。**
今回の指示どおり、Lean実装・ビルドには入っていない。新しい数学・drafts・③-b/⑤aのファイルは変更なし。
配置は全て `Project/DerivedCategories/DiagramComparison/` を候補とし、登録は調整役。
範囲をstrict図式や対象ごとの同値に狭める変更、自然性・strict表示の存在を仮定する変更はしていない。


## 21. 3b-3 再開・R1（11-13、継続）

main `c3f6cb0f1` の追記を取り込み、§20のR1〜R7・上限12,000行・約5,200行での途中報告を確認。
順序はR1→R5→R7→R6→R2→R3→R4。R6までの途中取り込み候補の報告はまだ先。
今夜のB3凍結は予告の段階で、18時の確定後はコミットを控える指示を確認。

**R1の検証済み部分**：`5ca806662`、新規2本・121行・16命名宣言。
`StrictComplexDiagram` は元の通常の複体を値とし、添字は `StrictDiagramDirection` によりΔ・Δᵒᵖだけ。
`strictDiagramQuasiIsos` と `strictDiagramWeakEdges` は元の自然変換の各成分の擬同型条件。
`StrictDiagramInfinity`・`strictDiagramLocalization` は一般辺局所化 `edgeLocalization` の実構成を使う。
同じSSet.{u+1}の準圏、元の指定局所化写像、objectwise擬同型辺の反転、全関手圏の普遍性を得た。
既存 `GeneralLocalization.edgeLocalization_isLocalization`・`edgeLocalization_universal` を再利用。

対象ビルド成功（R1単独2,395 jobs）、16宣言の監査は全てsorry-free、標準三公理のみ。
監査入力 `/tmp/is-w1/3b3-r1-audit.lean`、監査実行ログ `3b3-build-3.log`（R5の最初の評価定義と同時、4,960 jobs）。
鍵は `--wait 3600`、待ちは一枚、ビルド・監査中だけ保持し解放済み。
本体入口・全体監査登録、③-bの3b-2・G10・⑤aの既存ファイルは変更していない。

R5は作業木で進行中。通常複体の元の閉零射から、既存の一点dg加群の指定分解と
`semifreePointEquivalence` を使う実評価を作り、元の擬同型辺の反転まで対象ビルドが通った。
このR5分は一括監査前なのでまだコミットしていない。coherent図式圏への比較写像の同値性はR2・R3に残る。
**3b-3の完了・停止点5は主張せず、続行する。**

## 22. R5 の局所化評価の因子化・凍結前の検証済み分（11-13、継続）

`8fecef670`：新規3本・246行・13命名宣言。
`ComplexDerivedEvaluation` は元の複体・鎖写像の全nerveから既存D(A)への評価を構成。
`ComplexDerivedQuasiIsomorphisms` は元の擬同型の辺の反転を証明。
`StrictDiagramEvaluationFactorization` は固定添字での元の評価との等式、
全図式評価のobjectwise擬同型反転、局所化からの実評価
`strictDiagramDerivedEvaluation` と
`FunctorIso (strictDiagramLocalization ≫ strictDiagramDerivedEvaluation) strictComplexDiagramFamily`
を与える。各点の選択だけでなく全関手圏の局所化普遍性を使用。

対象ビルド成功（4,998 jobs、`/tmp/is-w1/3b3-build-13.log`）。
13宣言の監査成功（`/tmp/is-w1/3b3-r5-audit.log`、全てsorry-free、標準三公理のみ）。
R1からの検証済み累計は5本・367行・29命名宣言。
R5の半自由表示との比較は作業木で継続し、その後R7→R6へ進む。
R2・R3の充満忠実性・任意coherent図式の厳密化は未着手で、同値性の完了は主張しない。
上限12,000行・途中報告約5,200行・R6後の報告の条件に変更なし。

B3は18時の確定連絡を待つ予告として扱う。現時点の検証済み分は上のコミットに保存済み。
凍結確定後は枝へのコミットを控え、翌朝のmain取り込み・改名表への追従を行う。
未検証分はコミットしない。入口・監査の登録は調整役に委ねる。

## 23. R5・R7 の照合、R6 の実現関手側（11-13、継続）

§22に続く検証済み追加は新規4本・351行・22命名宣言。

| ファイル | 行 | 内容 |
| --- | ---: | --- |
| `ComplexDerivedSemifreeComparison` | 140 | 実分解の半自由入力への制限、定数一点加群との比較、元の通常鎖写像の表示を通す閉nerve包含との全FunctorIso |
| `StrictSemifreeEvaluationComparison` | 110 | 半自由strict図式を通常複体へ忘れる関手、全評価の自然性、3b-1の `strictSemifreeDiagramFamily` と局所化評価との全族比較 |
| `StrictDiagramEvaluationEndpoints` | 46 | 同じSSet.{u+1}で任意の全パラメーター・指定添字の評価を照合するFunctorIso |
| `StrictSemifreeRealizationFamily` | 55 | 元の自然変換を同じ `directSumTotalFunctor` で写す実現関手と全nerveの族、元の頂点・辺の像との等式。R6の指定余錐との比較はまだない |

再利用は `dgModuleResolvedInfinity_precompIso`、
`dgModuleResolvedInfinity_inclusionIso`、`dgSemifreeModulesInclusion_isFullyFaithful`、
`closedNerveInclusion_dgFunctor`、`FunctorIso.map_post`。
半自由入力の比較は、包含後の全関手比較を充満忠実性で戻して得た。
対象ごとの同型の選択から全族の自然性を仮定していない。

対象ビルド成功（7,304 jobs）。追加22宣言の一括監査成功、全てsorry-free・標準三公理のみ。
入力 `/tmp/is-w1/3b3-r5-r7-audit.lean`、ログ `/tmp/is-w1/3b3-build-23-audit.log`。
鍵は一枚・`--wait 3600`、対象ビルドと監査の間のみ保持し解放済み。
登録は調整役。本体の既存宣言、③-bの3b-2・G10・⑤aのファイルは変更・利用していない。

規模の照合：R1は121行（見込み600〜1,000）、R5は386行（500〜900）、
R7は156行（250〜450）。一般辺局所化と既存の出力分解・全関手同型のAPIを使えた分が小さい。
R6は実現関手側55行のみで、全族の指定余錐との照合は残る。
検証済み累計は9本・718行・51命名宣言。
R2・R3・R4は未着手。比較射の同値性、停止点5、R6の完成は主張しない。
次は予定どおりR6の指定余錐と元の実現関手・射を同時に比較する。
12,000行の上限、約5,200行の途中報告、R6後の報告の条件に変更なし。

## 24. R6 の実現・bar の関手比較（11-13、継続）

追加の検証済み分は新規13本・973行、監査対象45宣言。
`ProjectiveOutputResolvedComparison`・`ProjectiveComplexEvaluationComparison` は、
元の実分解の評価を、同じ射影的模型の評価へ全関手同型で比較する。
`StrictSemifreeRealizationProjective` は元の直和実現関手を同じ射で持ち上げ、
`strictSemifreeRealizationFamily_projectiveIso` を与える。射影性には3b-1を使用。

`ComplexDerivedNaturalComparison` は既存 `ordinaryNatTransPrism` と
`functorIsoOfEquivalenceHomotopy` を再利用する。
`StrictSemifreeReplacementComparison` は、既存の同じ
`replacementTotalAugmentationNatTrans` を元のstrict図式へ制限し、全関手同型へ運ぶ。
対象ごとの逆射を自然な族と仮定していない。

`StrictBarGradedFunctor`・`StrictBarNormalizedGradedFunctor` は、元の自然変換の先頭成分を
同じ射列ラベル・シフトで写す関手と、元のgraded包含・射影の自然性。
`StrictBarUnnormalizedFunctor` は、同じ `smallStrictBarTotalPointIso` に固定した非正規化barの関手と自然同型。
`StandardRowCochainNaturality`・`StrictBarColumnNaturality`・`StrictBarDegreeNaturality` は、
既存の行・余積の自然性から元の比較列の自然性を得る。
`StrictBarUnnormalizedComponents` は実barの射が各内部次数で元のgraded射そのものと証明し、
`StrictBarThetaNaturality` はその同じ射とMC項との可換式を各内部次数で証明する。
比較同型による関手の構成だけから、native余錐との整合性を主張していない。

対象ビルド成功（共通部分7,508 jobs、成分・MC項の比較5,173 jobs）。
監査ログ `/tmp/is-w1/3b3-build-38-audit.log`：45宣言全てsorry-free、標準三公理のみ。
入口・全体監査は未登録（調整役）。③-bの3b-2・G10・⑤aのファイルは変更・利用なし。

検証済み累計は22本・1,691行・監査対象96宣言。R6は種の55行を含め実測1,028行で、
当初の450〜750行を超えた。増分は元の射を保つbarの関手性と比較列の自然性の照合。
残りは、正規化MC項・元の射影の自然性、元の指定余錐の全パラメーター族、
元の実現関手と同じapex・脚・HA成分の比較。R6の完成・途中取り込み点はまだ主張しない。
R2・R3・R4の型・範囲は変更なし。残りを含む全体の暫定見込みは約8,000〜11,300行。
12,000行の上限を維持し、超過が見込まれる場合は検証済み分をコミットして止める。

## 25. R6 の正規化と全 HA 写像（11-13、継続）

検証済みの追加5本・427行、監査対象20宣言。
`StrictBarNormalizedThetaNaturality` は、前節の次数ごとの可換式を全Homへ戻し、
元の包含・射影の自然性から正規化MC項の可換式も証明した。
`StrictBarNormalizedFunctor` は同じ正規化barと射を通常関手にし、元の正規化射影を自然変換にする。
`StrictBarNormalizedEvaluationComparison` は、その同じ射影と既存の指定全複体同型から
`strictBarNormalizedTotalDerivedIso` を構成する。逆は全関手同型の逆であり、
対象ごとの逆の自然性を新たな仮定にはしていない。

`StrictSimplexMap`・`StrictSimplexMapPullback` は、全HA成分に可換する閉零写像の
恒等・合成と全ての面・退化への引き戻し。指定余錐の全族を組み立てるR6の局所データであり、
元の指定余錐でこの可換式が成立することは、これから接続して証明する。

対象ビルド成功（5,265 jobs、全族の対角データの下書き2本も含む）。
ログ `/tmp/is-w1/3b3-build-43-normalized.log`：上記20宣言は全てsorry-free、標準三公理のみ。
全族の対角評価・引き戻しの下書きは別の対象監査中で、今回のコミットには含めない。
入口・監査への登録は調整役。既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。

検証済み累計27本・2,118行、監査対象116宣言。R6実測は1,455行。
残りは元の標準脚・HA成分を持つ指定余錐の全パラメーター族と、
元の実現・native apexの全関手比較。R6完成・停止点5はまだ主張しない。
R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持する。

## 26. R6 の全 HA 族の同時評価（11-13、継続）

検証済み追加4本・386行、監査対象22宣言。
`StrictCoherentFamily` は全HA成分の可換式・恒等・合成・面・退化の整合性を持つ局所データ。
`OrderedSimplexDiagonal` は元の有限射列の閉零成分を後合成し、
切断位置の可換式と合成則から全HA方程式を満たす対角の実単体を構成する。
`OrderedSimplexPullback` は単射・潰れた辺・高次零成分の三分岐で、
同時引き戻しと対角評価の可換式を示す。
`StrictCoherentFamilyEvaluation` は同じデータを
`nerve C ⊗ ULift I ⟶ dgNerve A E` の全単体的写像へ束ねる。
定値パラメーターでは元の全HA単体と一致することも示した。

これらはR6の元の指定余錐族の組み立ての道具であり、元の余錐が入力の可換式を満たすことは
これから同じnative列の計算で証明する。元の余錐の自然性を仮定した完成版とは扱わない。

対象ビルド成功（3,504 jobs）、対象監査22宣言全てsorry-free・標準三公理のみ。
ログ `/tmp/is-w1/3b3-build-47-family-native.log` の最初の監査まで。
同じ鍵の後段で実行したnative列側はshift包含の表示の修正中で、今回には含めない。
検証済み累計31本・2,504行、監査対象138宣言。R6実測1,841行。
R6は未完成。元の指定余錐・native apexと元の実現関手の全族比較が残る。
R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。

## 27. R6 の元の列・strict 図式への接続（11-13、継続）

検証済み追加5本・308行、監査対象9宣言。
`PointShiftInNaturality` は元の符号付きshift包含の全内部次数の自然性。
`StrictBarNormalizedColumnNaturality` は元の全ラベルの包含を同じ正規化射影へ送った列の自然性と、
元の正規化shift包含との一致。退化ラベルも含む。
`StrictBarNativeColumnValues` は元のnative列の同じ全次数の値を、上の同じshift包含と列へ戻す。

`StrictModuleCoherentFamily` は元のstrict加群図式の通常関手から全HA族の入力を実際に作る。
閉零自然変換の合成を使い、全HA可換式・恒等・合成・全面退化を証明した。
`StrictModuleFamilyEvaluationComparison` はその対角評価と元の通常strict評価が、
全有限射列・全部分集合のHA成分で同じであることを示す。

対象ビルド成功（5,274 jobs）。ログ `/tmp/is-w1/3b3-build-51-native.log` の最初の監査9宣言は
全てsorry-free、標準三公理のみ。後段の合成記号への変換と添字同定の下書きは今回のコミットに含めない。
元のnative列の自然性の2宣言もビルド済みだが、対象監査は次の束に回す。
検証済み累計36本・2,812行、監査対象147宣言。R6実測2,149行。
残りは元のnative余錐の全HA写像・全パラメーター族と、元の実現・native apexとの全関手比較。
R6は未完成。R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。

## 28. R6 の native 列と単体間成分（11-13、継続）

検証済み追加4本・301行、監査対象12宣言。
`StrictBarNativeColumnNaturality` は元のnative列の厳密自然性を、全内部次数と全Homの両方で示す。
`StrictBarNativeCycleNaturality` は同じ式を、HA方程式で使う元の閉零cycleの通常順合成へ接続する。
`SmallStrictNativeLabelSource` は、元の混合成分ラベルの先頭が同じ旧頂点であることを
添字圏の中で証明する。係数加群の対象が一致することから添字の一致を推論していない。
`StrictBarNativeSimplexComponents` は、既存の同じnative単体を使い、旧頂点には元の自然変換、
apexには元の正規化barの射を与える。対象の等式に沿うcycleの移送と同じ成分との異種等号も示した。

対象ビルド成功（5,274 jobs）。ログ `/tmp/is-w1/3b3-build-54-native.log` の最初の監査12宣言は
全てsorry-free、標準三公理のみ。後段では旧成分の全HA可換式のファイルもビルドが通り、
混合成分の添字の最後の表示同定を修正中。これらの下書きは今回のコミットに含めない。
検証済み累計40本・3,113行、監査対象159宣言。R6実測2,450行。
残りは元のnative余錐の全HA写像を全族へ束ねる接続と、元の実現・native apexとの全関手比較。
joinの宇宙変更は既存の `Project/QuasicategoryAuxiliaries/UniverseJoinSimplexShapes.uliftCoconeShapeIso` を
再利用する。対象ごとの余錐の普遍性だけから全関手の比較を主張しない。
R6は未完成、R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。

## 29. R6 の元の native 単体の全 HA 写像（11-13、継続）

検証済み追加5本・461行、監査対象15宣言。
`StrictBarNativeOldComparison` は、最後へ届かない全成分を元の反復した閉零射列へ戻し、
元の自然変換の全HA可換式を証明する。
`StrictBarNativeMixedComparison` は、最後へ届く全成分を同じラベルのnative列へ戻し、
同じ閉零cycleの通常順合成の可換式を証明する。

`StrictBarNativeSimplexMap` は二つの可換式を合わせ、元のnative単体間の全HA写像を構成した。
`StrictBarNativeSimplexMapAlgebra` は、同じ写像の恒等・合成の整合性。
`StrictBarNativeSimplexMapPullback` は、既存のnative単体の引き戻しを再利用し、
apexを保つ全ての面・退化に対する整合性を示す。いずれも自然性を新たな入力にはしていない。

対象ビルド成功（5,282・5,284・5,290 jobs）。旧成分8宣言の監査は
`/tmp/is-w1/3b3-build-55-native.log` の最初、残り7宣言は
`/tmp/is-w1/3b3-build-56-native.log` の後段。15宣言全てsorry-free・標準三公理のみ。
検証済み累計45本・3,574行、監査対象174宣言。R6実測2,911行。
残りは各セルの全族をjoinの全余錐族へ貼り合わせ、元の実現・native apexの全関手同型へつなぐ接続。
R6はまだ未完成、R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。

## 30. R6 の各 HA セルの全族評価（11-13、継続）

検証済み追加5本・305行、監査対象15宣言。
`StrictSimplexCategory` は固定次元の元のHA単体と全厳密写像の独立した通常圏。
元のnative単体の通常関手と引き戻しの通常関手を、前節の同じ写像で与える。
`StrictSimplexCategoryEvaluation` は同じ小さい標準セルのYoneda図式から、
全nerveとセルの同時評価を作る。宇宙変更は既存の `uliftStdSimplexIso` を使う。

`StrictSimplexEvaluationNaturality` は全セル評価の引き戻しとの可換式と、
元のnativeセル関手の面・退化の全関手等号。
`StrictCoherentCellEvaluation` は任意の元の全HA族の一つのセルの全関手を作り、
その同時評価が元の全族の同じYoneda制限に一致することを証明する。
`StrictBarNativeCellFront` は、元のnativeセル関手の前面を元のstrict図式のセル関手へ厳密に戻す。

対象ビルド成功（5,293・5,297 jobs）。ログ `/tmp/is-w1/3b3-build-59-cells.log` の
後段15宣言は全てsorry-free・標準三公理のみ（前段8宣言と重複する分は一度だけ数えた）。
検証済み累計50本・3,879行、監査対象189宣言。R6実測3,216行。
残りは同じapex関手の全族比較、既存sliceの普遍性による全余錐族の貼り合わせ、
元の実現・native apexの全関手比較。各頂点の余錐の普遍性だけでは完成と扱わない。
R6は未完成、R2〜R4は未着手。上限12,000行・約5,200行での途中報告は維持。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。

## 31. R6 の同じ apex 関手と規模の再確認（11-13 17:36）

検証済み追加2本・175行、監査対象9宣言。
`StrictSimplexFunctorEvaluation` は固定HAセルへの通常関手の同時評価と、
引き戻し・元のnativeセルの前面の全族比較。
`StrictBarNativeCellApex` は元のnativeセルのapexを同じ正規化barの通常関手へ戻し、
その全射・全nerveで同じapex評価であることを証明した。

対象ビルド成功（5,302 jobs）。`/tmp/is-w1/3b3-build-66-cocone.log` の最初の監査9宣言は
全てsorry-free・標準三公理のみ。後段の全余錐族は公開宣言内の局所記法を明示型へ直して再検証中。
検証済み累計52本・4,054行、監査対象198宣言。R6実測3,391行。
未検証6本（全余錐の貼り合わせ、各セルと固定パラメーターの回復、射影的持ち上げ、
各パラメーターの余極限性）は作業木に置き、通るまでコミットしない。

### 上限の再見積もり

R6の実測が当初上端750行を超え、次の接続も残っている。

| R6の残り（既存の部品の接続のみ） | 型・必要な比較 | 見込み |
| --- | --- | ---: |
| 現在の未検証の束 | 同じnative余錐の全族、元の余錐への厳密な回復、射影的模型での余極限性 | 約450行＋検証の修正 |
| D(A)値の同じ全余錐族 | `nerve (StrictSemifreeDiagram A J) ⟶ colimitCocones I DA`、射影は同じ `strictSemifreeDiagramFamily A J`。一点／射影的比較の全関手同型で運ぶ | 250〜400行 |
| 元の正規化barのapexと実現 | `FunctorIso (strictSemifreeRealizationFamily A) computedApexFamily`。元の一点評価・正規化射影・指定Tot比較を使う | 200〜350行 |
| 指定native余錐族との比較 | 二重ULiftのjoinの既存同型を通した全余錐族の同型と、そのapexへの像 `FunctorIso (strictSemifreeRealizationFamily A) (strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ)` | 150〜250行 |

R6の残りは現在の検証済みから約1,050〜1,450行。
R2〜R4は未着手で、段0の4,900〜7,300行を据え置くと、全体は約10,000〜12,800行となる。
前の11,300〜11,800行という見込みの上端は維持できない。
**上限12,000行を超える見込みなので、今ある束の検証を区切り、検証済みを保存してこの線のLeanを止める。**
R6は未完成。R2〜R4をstrictな図式や点ごとの比較へ縮めて数字を合わせない。

既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。入口・監査の登録は調整役。
凍結は予告のみで、確定の連絡はまだ受けていない。今回の検証済みは18時前に保存する。

## 32. 規模による中間停止・最後の検証結果（11-13 17:49）

§31の判断に従い、この線のLeanを止めた。R6は未完成で、R6完了の途中の取り込み候補とはしない。
保存済みの数学は `a2d637dca`（2本・175行・9宣言）。検証済み累計は
**52本・4,054行、監査対象198宣言、R6実測3,391行** のまま。
全体の見込みは§31の約10,000〜12,800行で、上限12,000行を超える。R2〜R4は未着手。

最後の対象ビルドは `/tmp/is-w1/3b3-build-69-cocone.log`、終了コード1。
既検証2本の再ビルドと9宣言の再監査は成功。
`StrictBarNativeFunctorCocone.strictBarNativeFunctorOverSection` の自然性で、
`obtain ⟨⟨n⟩⟩ := n` の簡約中に `whnf` のheartbeat上限800,000へ達した。
下流の未知宣言等のエラーはこの未構成の切断に続くもの。
またdocstringと局所 `set_option ... in` の配置にも構文エラーがあった。
最終実行後、この配置だけを直したが、再検証はしていない。

未検証6本はコミットせず、作業木に残した（合計約445行）。

- `StrictBarNativeFunctorCocone`：関手単体集合のsliceによる全余錐族。上記で停止。
- `StrictBarNativeJoinCells`：貼り合わせた各joinセルを元の同じ全セル族へ戻す比較。
- `StrictSimplexEvaluationAtParameter`：定値パラメーターでの全HAセルの回復。
- `StrictBarNativeParameterRecovery`：全余錐族から元の指定native余錐全体への厳密な回復。
- `StrictBarNativeProjectiveFamily`：同じ全余錐族の射影的模型への持ち上げ。
- `StrictBarNativeProjectiveCocone`：各パラメーターの同じ余錐の余極限性の反映。

後五本の今回の対象ビルドは、最初の失敗の後に進んでいない。
ソースにsorry・axiomはないが、検証済みの成果には数えず、入口・監査への登録対象にも含めない。
再開時はまず切断の自然性の簡約を局所化してから、この順で検証する。
R6の残る型と接続、R2〜R4の見込みは§31の表と§20のまま。型・範囲を縮める変更はしていない。

共有鍵の待ちは一枚ずつとし、最後のプロセス終了で鍵は解放済み。
既存宣言・③-bの3b-2・G10・⑤aのファイルは変更なし。mainの作業木は編集・ビルドしていない。
凍結確定の連絡はまだ受けていない。検証済みのコミットとこの報告は18時前に保存した。

## 33. R6 の型つき一覧（11-13 18時の指示による再開）

§31〜32の行数による停止を解除する。外枠20,800行。R6を先に閉じて途中の取り込み点を報告し、
R2〜R4は別の型つき一覧を紙で出し直して止める。凍結確定の連絡はまだ受けていない。

以下をR6の残りの有限な一覧とする。U01〜U25は未検証6本に現在ある構成と主張の型を全て転記したもの。
各ブロックの引数・宇宙・openは当該ファイルの冒頭と同じで、定義の本体・証明を省いている。
構成の前提に新しい自然性・完全性を足さない。U26以降は§31の後三行を個別の出力に分けたもの。
証明の分割は本数に入れず、型を追記する。前提計算の法則は各U番号ごとに最大3本、
一覧外の既存構成の照合は全体で最大3本。別の数学が必要なら検証済みを保存して止める。
計算上限は既定値に戻し、簡約を局所化する。


### StrictBarNativeFunctorCocone

```lean
-- U01
def strictBarNativeFunctorDiagram : ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ⟶ (ihom (nerve (J ⥤ ModuleCategory A PUnit.{1}))).obj (dgNerve A (RightModule A PUnit.{1}))
-- U02
def strictBarNativeFunctorApex : (Δ[0] : SSet.{u + 1}) ⟶ (ihom (nerve (J ⥤ ModuleCategory A PUnit.{1}))).obj (dgNerve A (RightModule A PUnit.{1}))
-- U03
def strictBarNativeFunctorOverSimplex {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    (sliceOver (strictBarNativeFunctorApex A J)) _⦋n⦌
-- U04
def strictBarNativeFunctorOverSection : ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ⟶ sliceOver (strictBarNativeFunctorApex A J)
-- U05
lemma strictBarNativeFunctorOverSection_projection :
    strictBarNativeFunctorOverSection A J ≫ sliceOverProjection (strictBarNativeFunctorApex A J) =
      strictBarNativeFunctorDiagram A J
-- U06
def strictBarNativeFunctorCocone : JoinCocone (strictBarNativeFunctorDiagram A J)
-- U07
def strictBarNativeJoinFamily : (nerve (J ⥤ ModuleCategory A PUnit.{1})) ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ (dgNerve A (RightModule A PUnit.{1}))
-- U08
lemma strictBarNativeJoinFamily_front :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinInl ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) ≫ strictBarNativeJoinFamily A J =
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation
-- U09
lemma strictBarNativeJoinFamily_apex :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinInr ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) ≫ strictBarNativeJoinFamily A J =
      strictBarApexCellEvaluation A J
```


### StrictBarNativeJoinCells

```lean
-- U10
lemma strictBarNativeFunctorCocone_cell {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    joinMap (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))))
        (𝟙 Δ[0]) ≫ (strictBarNativeFunctorCocone A J).val =
      (joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s)
-- U11
lemma strictBarNativeJoinFamily_cell {n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ joinMap (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))))
        (𝟙 Δ[0])) ≫ strictBarNativeJoinFamily A J =
      ((nerve (J ⥤ ModuleCategory A PUnit.{1})) ◁ (joinStdSimplexIso n 0).hom) ≫ strictBarNativeCellEvaluation A J s
```


### StrictSimplexEvaluationAtParameter

```lean
-- U12
lemma strictFamilyCurry_evaluateAt {K : SSet.{u + 1}}
    (H : nerve C ⊗ K ⟶ dgNerve A E) (c : C) :
    MonoidalClosed.curry H ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (ComposableArrows.mk₀ c) =
      lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 K) ≫ H
-- U13
lemma strictSimplexFunctorEvaluation_atParameter {n : ℕ}
    (F : C ⥤ StrictSimplexCategory A E n) (c : C) :
    lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 (Δ[n] : SSet.{u + 1})) ≫
        strictSimplexFunctorEvaluation A E F =
      SSet.yonedaEquiv.symm (F.obj c).val
-- U14
lemma strictBarNativeCellEvaluation_atParameter (J : Type) [SmallCategory J]
    (F : J ⥤ ModuleCategory A PUnit.{1}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    lift (SSet.const (ComposableArrows.mk₀ F)) (𝟙 (Δ[n + 1] : SSet.{u + 1})) ≫
        strictBarNativeCellEvaluation A J s =
      SSet.yonedaEquiv.symm (strictBarNativeSimplex A J F s)
```


### StrictBarNativeParameterRecovery

```lean
-- U15
lemma strictSliceOverUncurry_eq_of_values {K L X : SSet.{u + 1}} {p q : L ⟶ X}
    (hp : p = q) (s : K ⟶ sliceOver p) (t : K ⟶ sliceOver q)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (a : K.obj n),
      (s.app n a).val = (t.app n a).val) :
    sliceOverUncurry s = sliceOverUncurry t
-- U16
lemma strictBarNativeFunctorApex_atParameter (F : J ⥤ ModuleCategory A PUnit.{1}) :
    strictBarNativeFunctorApex A J ≫ evaluateFunctorAt (ComposableArrows.mk₀ F) =
      SSet.yonedaEquiv.symm
        (dgCoherentBarNativeApex A PUnit.{1} (smallStrictBarDiagram A F)
          (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)))
-- U17
lemma strictBarNativeFunctorCocone_atParameter (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (strictBarNativeFunctorCocone A J).val ≫
        evaluateFunctorAt (ComposableArrows.mk₀ F) =
      (dgCoherentBarNormalizedNativeCocone A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F))).val
```


### StrictBarNativeProjectiveFamily

```lean
-- U18
lemma strictBarNormalizedFunctor_projective (F : J ⥤ ModuleCategory A PUnit.{1})
    (hF : ∀ j, moduleHomotopicallyProjective A PUnit.{1} (F.obj j)) :
    moduleHomotopicallyProjective A PUnit.{1} ((strictBarNormalizedFunctor A J).obj F)
-- U19
def strictBarNativeJoinFamilyAlong :
    nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ dgNerve A (RightModule A PUnit.{1})
-- U20
lemma strictBarNativeJoinFamilyAlong_projective :
    ∀ z : (nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) _⦋0⦌,
      dgModuleProjectiveProperty A PUnit.{1}
        (((strictBarNativeJoinFamilyAlong A J T).app _ z).obj 0)
-- U21
def strictBarNativeProjectiveJoinFamily :
    nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ dgProjectiveModuleNerve A PUnit.{1}
-- U22
lemma strictBarNativeProjectiveJoinFamily_image :
    strictBarNativeProjectiveJoinFamily A J T hT ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleProjectiveProperty A PUnit.{1})) =
      strictBarNativeJoinFamilyAlong A J T
```


### StrictBarNativeProjectiveCocone

```lean
-- U23
def strictBarNativeProjectiveCoconeAt (c : C) :
    JoinCocone (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ≫
      lift (SSet.const (ComposableArrows.mk₀ c)) (𝟙 _) ≫
        strictBarNativeProjectiveJoinFamily A J T hT)
-- U24
lemma strictBarNativeProjectiveCoconeAt_image (c : C) :
    (fullInclusionCocone A (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1})
      (strictBarNativeProjectiveCoconeAt A J T hT c)).val =
    (dgCoherentBarNormalizedNativeCoconeUnconditional A PUnit.{1}
      (smallStrictBarDiagram A (T.obj c))).val
-- U25
lemma strictBarNativeProjectiveCoconeAt_isColimit (c : C) :
    IsColimitCone (strictBarNativeProjectiveCoconeAt A J T hT c)
```


### §31の残る接続の型（U26以降）

以下の略記を固定する。`I₂` と `I` は同一視せず、既存の
`smallDiagramShapeIso` とjoinの同型で移送する。

```lean
variable (A : Type u) [CommRing A]
local notation "J" => SimplexCategoryᵒᵖ
local notation "C" => StrictSemifreeDiagram A J
local notation "P" => nerve C
local notation "I" => (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)
local notation "I₂" => (SSet.uliftFunctor.{u + 1, u}).obj
  ((SSet.uliftFunctor.{u, 0}).obj (nerve J))
local notation "DA" => derivedInfinityCategory A

-- U26: 元の半自由一点図式から台の加群図式への全通常関手。
def strictSemifreePointUnderlyingFunctor : C ⥤ (J ⥤ ModuleCategory A PUnit.{1})

-- U27: 構成は既存の同じ台の図式を使う。
lemma strictSemifreePointUnderlyingFunctor_obj (F : C) :
  (strictSemifreePointUnderlyingFunctor A).obj F =
    pointSemifreeUnderlyingDiagram A (strictSemifreePointDiagram A F)

-- U28: U21への射影性の入力は結論として供給する。
lemma strictSemifreePointUnderlyingFunctor_projective (F : C) (j : J) :
  moduleHomotopicallyProjective A PUnit.{1}
    (((strictSemifreePointUnderlyingFunctor A).obj F).obj j)

-- U29: U21を既存のprojectivePointEquivalenceで送る同じ全余錐族。
def strictSemifreeRawDAJoinFamily : P ⊗ join I₂ (Δ[0] : SSet.{u + 1}) ⟶ DA :=
  strictBarNativeProjectiveJoinFamily A J (strictSemifreePointUnderlyingFunctor A)
    (strictSemifreePointUnderlyingFunctor_projective A) ≫ (projectivePointEquivalence A).hom

-- U30: 同じjoinの宇宙変更。既存のsmallDiagramShapeIsoの逆を使う。
def strictSemifreeJoinShapeIso (A : Type u) :
  join I (Δ[0] : SSet.{u + 1}) ≅ join I₂ (Δ[0] : SSet.{u + 1})

-- U31: 下方図式の既存の全関手同型に沿い、同じ全族を輸送する。
def strictSemifreeComputedDAJoinFamily : P ⊗ join I (Δ[0] : SSet.{u + 1}) ⟶ DA
lemma strictSemifreeComputedDAJoinFamily_front :
  (P ◁ joinInl I (Δ[0] : SSet.{u + 1})) ≫ strictSemifreeComputedDAJoinFamily A =
    strictSemifreeEvaluation A J

-- U32: 輸送は全joinの関手同型を持つ（頂点・辺だけの対応ではない）。
def strictSemifreeComputedDAJoinFamily_transportIso :
  FunctorIso ((P ◁ (strictSemifreeJoinShapeIso A).hom) ≫
    strictSemifreeRawDAJoinFamily A) (strictSemifreeComputedDAJoinFamily A)

-- U33: 同じ全族の各パラメーターでの余錐は余極限。
def strictSemifreeComputedDACoconeAt (F : C) :
  JoinCocone (joinInl I (Δ[0] : SSet.{u + 1}) ≫
    lift (SSet.const (ComposableArrows.mk₀ F)) (𝟙 _) ≫
      strictSemifreeComputedDAJoinFamily A)
lemma strictSemifreeComputedDACoconeAt_isColimit (F : C) :
  IsColimitCone (strictSemifreeComputedDACoconeAt A F)

-- U34: 全族を普遍余錐の全部分圏へ制限する。別の族を選び直さない。
def strictSemifreeComputedColimitFamily : P ⟶ colimitCocones I DA
lemma strictSemifreeComputedColimitFamily_evaluation :
  (β_ P (join I (Δ[0] : SSet.{u + 1}))).hom ≫
    uncurry (strictSemifreeComputedColimitFamily A ≫
      (relativeInitialVertices (coconeRestriction I DA)).ι) =
    strictSemifreeComputedDAJoinFamily A

-- U35: 指定されている同じ全下方図式。
lemma strictSemifreeComputedColimitFamily_projection :
  strictSemifreeComputedColimitFamily A ≫ colimitCoconeProjection I DA =
    strictSemifreeDiagramFamily A J

-- U36: 同じ下方図式を持つ全普遍余錐族の既存比較。
def strictSemifreeComputedColimitFamilyIso :
  FunctorIso (strictSemifreeComputedColimitFamily A) (strictSemifreeColimitFamily A J)

-- U37: 同じ比較を全余錐へ送る。全高次単体と脚の比較を含む。
def strictSemifreeComputedCoconeFamilyIso :
  FunctorIso (strictSemifreeComputedColimitFamily A ≫
    (relativeInitialVertices (coconeRestriction I DA)).ι)
    (strictSemifreeCoconeFunctorFamily A J)

-- U38: 元の正規化barの同じ通常関手と複体評価。
def strictSemifreeNormalizedBarComplex : C ⥤ Complex A :=
  strictSemifreePointUnderlyingFunctor A ⋙ strictBarNormalizedFunctor A J ⋙
    moduleEvaluation A PUnit.{1} PUnit.unit
def strictSemifreeNormalizedBarRealizationIso :
  FunctorIso (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
    (strictSemifreeRealizationFamily A)

-- U39: 同じ全余錐族のapex。U32のapex制限と既存のprojective複体比較を使う。
def strictSemifreeComputedApexFamily : P ⟶ DA :=
  lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _) ≫
    (P ◁ joinInr I (Δ[0] : SSet.{u + 1})) ≫ strictSemifreeComputedDAJoinFamily A
def strictSemifreeNormalizedBarApexIso :
  FunctorIso (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
    (strictSemifreeComputedApexFamily A)

-- U40: 同じU36・U37のapexへの像。
def strictSemifreeComputedNativeApexIso :
  FunctorIso (strictSemifreeComputedApexFamily A) (strictSemifreeNativeApexFamily A J)

-- U41: R6の最終受け渡し。U37と同じ比較から作る。
def strictSemifreeRealizationNativeApexIso :
  FunctorIso (strictSemifreeRealizationFamily A) (strictSemifreeNativeApexFamily A J)
```

U31・U33・U34・U38・U39は構成とその性質を同じ番号で記載した。
単位・余単位・自然性・係数移送の前提計算：全番号とも0/3から開始。
一覧外の照合：0/3から開始。既検証52本は追加計算の枠として再度数えない。
順序はU01〜U25（未検証の解消）→U26〜U41。
R6完成後は止まらず、R2〜R4の紙の型つき一覧と③-b§38.2の3との照合へ進む。

### U04の証明の分割（追加の数学・計算枠の消費なし）

```lean
lemma strictBarNativeFunctorOverSimplex_naturality {m n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (joinStdSimplexIso m 0).hom ≫ curry (strictBarNativeCellEvaluation A J
      (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map α.op s)) =
    joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) ≫
      ((joinStdSimplexIso n 0).hom ≫ curry (strictBarNativeCellEvaluation A J s))
```

固定した次元で上式を先に証明し、切断の自然性にはこの式だけを渡す。
`maxHeartbeats 800000` は取り除いた。型の分解で大きなbarの構成を簡約しない。

### U38の前提計算（1/3、係数移送）

元の一点定数関手の評価の法則を全図式・全自然変換に移す。次の三表示は一つの係数移送の法則と、
その値の圏への分割・同じ後合成の帰結であり、新しい数学の三件とは数えない。

```lean
lemma strictSemifreePointValue_evaluation :
    (semifreePointConstant A).onClosed ⋙
      (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
        (dgModuleSemifreeProperty A PUnit.{1})).onClosed ⋙
      moduleEvaluation A PUnit.{1} PUnit.unit = semifreeUnderlyingComplex A

lemma strictSemifreePointUnderlyingFunctor_evaluation :
    strictSemifreePointUnderlyingFunctor A ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
        (moduleEvaluation A PUnit.{1} PUnit.unit) =
      strictSemifreeUnderlyingComplex A .simplicial

lemma strictSemifreePointUnderlyingFunctor_total :
    strictSemifreePointUnderlyingFunctor A ⋙ strictBarTotalComplexFunctor A SimplexCategoryᵒᵖ =
      strictSemifreeReplacementRealization A

```

既存の `strictSemifreePointDiagram_coefficients` の係数射の計算を全射に再利用する。
U38は1/3、他のU番号は0/3、一覧外の照合は0/3。下書きは未検証で、数学のコミットにはまだ含めない。

## 34. R6 U01〜U14 の検証（11-13 18:20、継続）

追加3本・238行を検証した。
`StrictBarNativeFunctorCocone`（120行）はU01〜U09、
`StrictBarNativeJoinCells`（39行）はU10〜U11、
`StrictSimplexEvaluationAtParameter`（79行）はU12〜U14。
U04は、図形だけの等式の宇宙を明示して先に固定し、後合成の大きな型推論を避けて
直接書き換えることで、既定のheartbeat上限で通った。上限の引き上げは全て取り除いた。
U04の分割は§33に記載したものだけ。追加の数学はない。
U12は既存の `curry_evaluateFunctorAt_unitHomEquiv` を再利用し、単位からの頂点表示を計算した。

対象ビルド成功（5,305 jobs）。`/tmp/is-w1/3b3-build-73-cocone.log` の前段。
対象監査は全余錐族9宣言、セル・固定パラメーター5宣言の計14宣言で、全て標準三公理のみ。
全余錐族の9宣言にはsorry検査も通り、残る5宣言にもsorryAxはない。
検証済み累計**55本・4,292行、監査対象212宣言、R6実測3,629行**。

U15以降は継続中。最初の回復ファイルでは `SimplicialRealization` のopenが抜けていたため、
名前の指定を直して再検証へ回した。U26〜U28とU38の独立した構成も下書きを用意し、
同じ対象ビルドの後続で検証する。これらはまだ数学のコミットへ含めない。
U38の前提計算は§33の1/3、その他は0/3、一覧外の照合は0/3のまま。
R6完成後は指示どおりR2〜R4の紙の一覧へ進む。凍結確定の連絡はまだ受けていない。

### U20の前提計算（1/3、パラメーター制限の自然性）

U17の元の同じ余錐への回復を、パラメーター関手Tに沿って制限する。
Tを介した全評価の既存のcurryの自然性だけを使う。

```lean
lemma strictBarNativeJoinFamilyAlong_atParameter (c : C) :
    lift (SSet.const (ComposableArrows.mk₀ c))
        (𝟙 (join ((SSet.uliftFunctor.{u + 1, u}).obj
          ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}))) ≫
      strictBarNativeJoinFamilyAlong A J T =
    (dgCoherentBarNormalizedNativeCoconeUnconditional A PUnit.{1}
      (smallStrictBarDiagram A (T.obj c))).val
```

U20の射影性はこの式を零単体で評価してから既存のbarの射影性を使う。
同じ式はU24にも再利用する。U20は1/3、U38は1/3、その他は0/3、一覧外の照合は0/3。

### U30の前提計算（2/3、join同型の単位）

既存のjoinIsoの前面・apexの法則を指定形状で読む。

```lean
lemma strictSemifreeJoinShapeIso_inl :
    joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
        (strictSemifreeJoinShapeIso A).hom =
      (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).inv ≫
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj
          ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ))) Δ[0]

lemma strictSemifreeJoinShapeIso_inr :
    joinInr ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫
        (strictSemifreeJoinShapeIso A).hom =
      joinInr ((SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ))) Δ[0]

```

U20は1/3、U30は2/3、U38は1/3、その他0/3、一覧外の照合0/3。

## 35. R6 の回復と元の実現への全関手比較（11-13 18:27、継続）

追加3本・213行、対象監査11宣言が通った。
`StrictBarNativeParameterRecovery`（83行、U15〜U17）は、
全余錐族を固定パラメーターで評価すると元の指定native余錐全体に厳密に戻る比較。
`StrictSemifreePointUnderlyingFunctor`（42行、U26〜U28）は同じ一点加群図式の全通常関手と射影性。
`StrictSemifreeNormalizedBarRealization`（88行、U38）は、元の正規化射影・指定全複体同型・
単体的置換の増大を合成した、元のstrict実現への全関手同型。

対象ビルドは `/tmp/is-w1/3b3-build-74-cocone.log` の成功した3本、
対象監査11宣言は `/tmp/is-w1/3b3-build-75-cocone.log` の最初。
全て標準三公理のみ、sorryAxなし。検証済み累計
**58本・4,505行、監査対象223宣言、R6実測3,842行**。

U18〜U25の射影的余錐への接続は、U20の§33に記載した自然性を使う形で再検証中。
U29〜U30の構成・単位則は下書きのみで、まだコミットしない。
前提計算はU20が1/3、U30が2/3、U38が1/3、他は0/3。照合0/3。
R6は未完成で、残りは§33の型つき一覧のまま。既存宣言・他レーンの持ち分の変更はない。
凍結確定の連絡はまだ受けていない。

### U31の前提計算（3/3、既存の単位・評価の自然性）

以下は既存の同値の単位と、既存の二つの全評価の係数移送の法則である。

```lean
def semifreeProjectivePointUnitIso :
    FunctorIso
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgSemifreeToProjective A PUnit.{1}) ≫ (projectivePointEquivalence A).hom)
      (semifreePointEquivalence A).hom

lemma strictModuleFamily_evaluation_factor {C : Type (u + 1)} [Category.{u} C]
    (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1})) :
    (nerveMap T ▷ (SSet.uliftFunctor.{u + 1, u}).obj
        ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) ≫
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).evaluation =
    (nerve C ◁ (smallDiagramShapeIso.{u} (nerve J)).hom) ≫
      (nerveMap T ▷ (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) ≫
      strictDiagramEvaluation J (ModuleCategory A PUnit.{1}) ≫
      closedNerveInclusion A (RightModule A PUnit.{1})

lemma strictDiagramEvaluation_postcompose {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] (V : C ⥤ D) :
    (nerveMap ((Functor.whiskeringRight J C D).obj V) ▷
        (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)) ≫ strictDiagramEvaluation J D =
      strictDiagramEvaluation J C ≫ nerveMap V

```

U31は3/3となった。U20は1/3、U30は2/3、U38は1/3、その他0/3、一覧外の照合0/3。
以後U31の前提計算を追加するときは、そのまま増やさず数え方と内容を確認する。

### U23の包装の分割（計算枠の消費なし）

次の同じ射を先に型づけし、`⟨射, rfl⟩` の型推論が全射影的持ち上げを簡約しないようにする。

```lean
def strictBarNativeProjectiveCoconeMapAt (c : C) :
    join ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶
        dgProjectiveModuleNerve A PUnit.{1}
```

U23の返す余錐は `JoinCocone (joinInl _ Δ[0] ≫ strictBarNativeProjectiveCoconeMapAt A J T hT c)`。
元の型と定義的に同じであり、実際の射と脚は変えない。計算上限は引き上げない。

## 36. 射影的な全余錐族と同じ余極限性（11-13 夜、継続）

追加5本・326行を検証した。
`StrictBarNativeProjectiveFamily`（99行、U18〜U22）は、同じ全native余錐族の射影的持ち上げ。
`StrictBarNativeProjectiveCocone`（71行、U23〜U25）は、同じ余錐を固定パラメーターへ制限し、
包含後に元の指定native余錐へ戻る等式と、その射影的模型での余極限性。
`StrictSemifreeRawDAFamily`（62行、U29〜U30）は、その全族を既存D(A)へ送る構成とjoinの形状同型。
`StrictFamilyEvaluationNaturality`（60行）はU31の二つの評価の自然性、
`SemifreeProjectivePointUnit`（34行）は既存の同値の同じ単位。

対象ビルド成功（6,343 jobs）、`/tmp/is-w1/3b3-build-78-cocone.log`。
先行する11宣言の監査と後続の監査を重複を除いて数え、追加16宣言が標準三公理のみ、sorryAxなし。
検証済み累計**63本・4,831行、監査対象239宣言、R6実測4,168行**。

U01〜U30とU38、U31の前提計算3件まで通った。R6の残りはU31〜U37・U39〜U41。
U23の包装は§33の同じ射の分割で通り、計算上限を引き上げていない。
前提計算はU20が1/3、U30が2/3、U31が3/3、U38が1/3、他は0/3。照合0/3。
次は全下方図式を指定の全評価へ接続し、同じ全余錐族・apexの比較を閉じる。
凍結確定の連絡はまだ受けていないため、検証済みの分を保存した。

### 照合C1（1/3）：同じ射影的native前面とstrict全評価

U31の二つの既存構成の前面の照合をC1として使う。最終の型は次である。

```lean
lemma strictSemifreeProjectiveFront :
  let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
  let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
  (P ◁ joinInl I (Δ[0] : SSet.{u + 1})) ≫
    (P ◁ (strictSemifreeJoinShapeIso A).hom) ≫
      strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
        (strictSemifreePointUnderlyingFunctor A)
        (strictSemifreePointUnderlyingFunctor_projective A) =
  strictDiagramEvaluation SimplexCategoryᵒᵖ (ClosedCategory A (Semifree A)) ≫
    closedNerveInclusion A (Semifree A) ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        ((semifreePointConstant A).comp (dgSemifreeToProjective A PUnit.{1}))
```

まず包含で戻した次の同じ等式を証明し、単射性で戻す。これはC1の証明の分割である。

```lean
lemma strictSemifreeProjectiveFront_image :
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0]) ≫
    (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ◁ (strictSemifreeJoinShapeIso A).hom) ≫
      strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
        (strictSemifreePointUnderlyingFunctor A)
        (strictSemifreePointUnderlyingFunctor_projective A) ≫
      SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleProjectiveProperty A PUnit.{1})) =
    (nerveMap (strictSemifreePointUnderlyingFunctor A) ▷
      (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) ≫
      strictDiagramEvaluation SimplexCategoryᵒᵖ (ModuleCategory A PUnit.{1}) ≫
        closedNerveInclusion A (RightModule A PUnit.{1})
```

前提計算はU20=1/3、U30=2/3、U31=3/3、U38=1/3、その他0/3。
照合C1を使用して1/3。新しい数学の一覧外の補題は追加していない。

### U32の前提計算（1/3、評価の余単位）

既存の `functorIsoLiftRight` と評価の後合成で、全族の同型を元の共同評価へ戻す。

```lean
def fullFamilyUncurryIso {P K D : SSet.{u}} [Quasicategory D]
    {F G : K ⟶ (ihom P).obj D} (e : FunctorIso F G) :
    FunctorIso (uncurry F) (uncurry G)
```

U32は1/3となった。U20=1/3、U30=2/3、U31=3/3、U38=1/3、その他0/3、照合C1のみ1/3。

### U31〜U32の存在部分の分割（数学・前提計算枠の消費なし）

全パラメーターを標的関手圏に入れ、既存の `exists_cartesian_cocone_lift` を使う。
底の可逆性とcartesian性から持ち上げた辺の可逆性を得る既存の定理を使うので、
新しい関手圏の持ち上げ理論は作らない。次はU31・U32の同じ主張をcurryした型である。

```lean
lemma exists_strictSemifreeTransportedFunctorCocone :
    ∃ g : join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
        (Δ[0] : SSet.{u + 1}) ⟶
        (ihom (nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ))).obj
          (derivedInfinityCategory A),
      joinInl ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)) Δ[0] ≫ g =
        strictSemifreeStrictFunctorDiagram A ∧
      Nonempty (FunctorIso g (strictSemifreeRawFunctorCoconeMap A))
```

その全関手圏での存在を一度選び、`strictSemifreeComputedFunctorCoconeMap` とする。
そのuncurryがU31の `strictSemifreeComputedDAJoinFamily`、同じ存在の同型をuncurryしたものがU32。
元の底の辺は持ち上げの等式で保たれ、全パラメーターを対象別には選ばない。

## 37. R6 の指定前面への全族輸送（約5,200行での途中報告、11-13 夜）

追加4本・350行を検証した。
`StrictSemifreeProjectiveFront`（113行）は照合C1、元の同じnative前面と全strict DG評価の等式。
`FullFamilyUncurryIso`（31行）はU32の評価の余単位の全族輸送。
`StrictSemifreeRawDAFrontIso`（61行）は同じD(A)値の前面から指定全評価へのFunctorIso。
`StrictSemifreeFunctorCoconeTransport`（145行）はU31〜U32の本体。
全パラメーターを標的関手圏へ入れ、既存の `exists_cartesian_cocone_lift` で
元の可逆な底の辺を持ち上げた。既存のcartesian辺の可逆性の判定とuncurryを使い、
指定前面の全余錐族と、元の全joinの族からの全関手同型を得た。

対象ビルドは `/tmp/is-w1/3b3-build-82-front.log`（7,552 jobs）と
`/tmp/is-w1/3b3-build-85-transport.log`（7,553 jobs）。
C1・uncurry・底の比較の4宣言と、輸送の5宣言の監査が全て標準三公理のみ、sorryAxなし。
検証済み累計**67本・5,181行、監査対象248宣言、R6実測4,518行**。

U01〜U32とU38が完了。残りは§33のU33〜U37・U39〜U41。
前提計算はU20=1/3、U30=2/3、U31=3/3、U32=1/3、U38=1/3、その他0/3。
照合はC1のみ1/3。全て計算上限は既定値。

残りの筋は、同じ輸送の全族同型を固定パラメーターへ制限し、U25の同じ余極限性を
既存の `InitialBoundaryLifting.of_vertexIso` で移す（U33）。その全族を普遍余錐の
全部分圏へ制限し（U34〜U35）、既存の全余錐族と比較する（U36〜U37）。
U39では元の正規化barの一点評価・射影的模型と同じapexを比較し、U38と合成してU40〜U41を返す。
R2〜R4はLeanに入らず、R6の完成後に紙の型つき一覧と見込みを出し直す。
行数の旧停止は再開の指示で解除済み。外枠20,800行と型つき一覧の枠を維持し、このまま続ける。
凍結確定の連絡はまだ受けていない。

### U33の前提計算（1/3、形状変更とパラメーター評価）

同じ射影的余錐を同値・形状同型で運んだものと、元の全族の固定パラメーター評価を比較する。

```lean
lemma strictSemifreeRawDACoconeAt_val (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreeRawDACoconeAt A F).val =
      lift (SSet.const (ComposableArrows.mk₀ F))
        (𝟙 (join ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
          (Δ[0] : SSet.{u + 1}))) ≫ strictSemifreeReindexedRawDAJoinFamily A
```

包装の分割 `strictSemifreeComputedDACoconeMapAt` はこの右辺と同じパラメーター制限を
計算済みの全族に適用した射。U33の余極限性は既存の同値による保存、形状同型による保存、
`InitialBoundaryLifting.of_vertexIso` を順に使う。新しい余極限の保存理論は作らない。
U33は1/3。U20=1/3、U30=2/3、U31=3/3、U32=1/3、U38=1/3、他0/3、照合C1=1/3。

### U34の前提計算（1/3、転置と頂点評価）

同じ共同評価を余錐の関手単体集合で読むと、その頂点はU33の同じ余錐である。

```lean
lemma strictSemifreeComputedCoconeFunctorMap_vertex
    (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreeComputedCoconeFunctorMap A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ F) =
      functorVertex (strictSemifreeComputedDACoconeAt A F).val
```

既存の `transposeFunctorFamily_vertex` とU12の評価を使う。U34は1/3。
その他の使用数はU20=1/3、U30=2/3、U31=3/3、U32=1/3、U33=1/3、U38=1/3、照合C1=1/3。

### U40の前提計算（1/3、apexの共同評価）

```lean
lemma coconeFamily_apex_evaluation {P I D : SSet.{u + 1}}
    (f : P ⟶ (ihom (join I (Δ[0] : SSet.{u + 1}))).obj D) :
    f ≫ coconeApexEvaluation I D =
      lift (𝟙 P) (SSet.stdSimplex.isTerminalObj₀.from P) ≫
        (P ◁ joinInr I Δ[0]) ≫ (β_ P (join I Δ[0])).hom ≫ uncurry f
```

既存の `curry_evaluateFunctorAt_vertex` と終対象の一意性による計算。
U40は1/3。新しい数学の追加ではなく、既存の評価の法則として記録する。

### U37の前提計算（1/3、既存の全余錐の包含）

```lean
lemma specifiedCoconeFamily_eq :
    strictSemifreeCoconeFunctorFamily A SimplexCategoryᵒᵖ =
      strictSemifreeColimitFamily A SimplexCategoryᵒᵖ ≫
        (relativeInitialVertices (coconeRestriction
          ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ))
            (derivedInfinityCategory A))).ι
```

既存の非expose定義の計算を私有の証明に局所化し、等式だけ公開する。
既存ファイルは変更しない。U37は1/3（証明包装の分割は数えない）。

## 38. R6 の同じ全普遍余錐族とapexへの比較（11-13 夜、継続）

- 新規3本344行：`StrictSemifreeComputedCoconePointwise`（103）、
  `StrictSemifreeComputedColimitFamily`（157）、`StrictSemifreeComputedApexComparison`（84）。
- U33〜U37・U40を検証。元の同じ全族を固定パラメーターへ制限して余極限性を移し、
  全族を普遍余錐の全部分圏へ制限、既存の指定全余錐族と比較した。
  同じ比較のapex評価も通った。対象ごとの別の余錐へ取り替えていない。
- ビルド87（U33）、93（U34〜U37）、94（U40）成功。
  監査87・93・95の計13宣言は標準三公理のみ、sorryAxなし。
  検証済み累計70本5,525行、監査対象261宣言。R6実測4,862行。
- 既存の非expose定義は、私有の定義計算の証明を公開補題に包んだ。
  既存ファイルの本文・型・属性は変更していない。
- U40の `specifiedNativeApex_eq` は既存apexの定義計算（2/3）。
  型は `strictSemifreeNativeApexFamily A J = lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
  (P ◁ joinInr I Δ[0]) ≫ (β_ P _).hom ≫ uncurry (strictSemifreeCoconeFunctorFamily A J)`
  （ここでは J=Δᵒᵖ、I・Pは§33の同じ略記）。証明包装は追加に数えない。
- 残りはU39（同じ正規化barの一点評価と計算済みapex）、U41（U38・U39・U40の合成）。
  照合C2・C3は未使用。計算上限は既定値。凍結確定の連絡は未受領。

**R6は未完了。このままU39・U41を続ける。R2〜R4のLeanには入らない。**

### 照合C2（2/3）：同じ射影的apexと正規化barの全閉nerve

```lean
lemma strictSemifreeProjectiveApex :
  let P := nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ)
  let I := (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategoryᵒᵖ)
  lift (𝟙 P) (stdSimplex.isTerminalObj₀.from P) ≫
    (P ◁ joinInr I Δ[0]) ≫ (P ◁ (strictSemifreeJoinShapeIso A).hom) ≫
      strictBarNativeProjectiveJoinFamily A SimplexCategoryᵒᵖ
        (strictSemifreePointUnderlyingFunctor A)
        (strictSemifreePointUnderlyingFunctor_projective A) =
    nerveMap (strictSemifreeNormalizedProjectiveModule A) ≫
      closedNerveInclusion A (ProjectiveDGModules A PUnit.{1})
```

`strictSemifreeNormalizedProjectiveModule` は元の正規化barと同じ射影的一点加群・同じ射の包装。
証明分割 `strictClosedVertexEvaluation` の型は、任意の通常関手
`G : C ⥤ ModuleCategory A PUnit.{1}` に対する
`lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _) ≫
 strictSimplexFunctorEvaluation A _ (G ⋙ strictBarClosedVertexFunctor A)
 = nerveMap G ≫ closedNerveInclusion A _`。
その局所成分 `closedVertex_pullback_hom` は任意の `α : Fin (n+1) →o Fin 1` で
`((closedNerveSimplex (Functor.const.obj M)).pullback α).hom T a b k ...
 = closedNerveHom (𝟙 M) k`。
既存の引き戻し等式と `data_hom_heq_of_eq` を使い、次数零の単位と高次零成分を比較する。
新しいHAセルの構成や理論を足さない。これらはC2の証明分割として数える。

### U39の前提計算（1/3）と照合C3（3/3）

```lean
lemma projectivePointRingPresentation_underlying :
  projectivePointRingPresentation A ⋙ projectiveRingUnderlyingComplex A =
    projectivePointCoefficientComplex A

def projectivePointRingPresentation_constantIso :
  projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed ≅
    𝟭 (ClosedCategory A (ProjectiveDGModules A PUnit.{1}))
```

前者は係数移送の法則（U39の1/3）。後者がC3：既存の `ringModule_recover` による
同じ一点加群の復元の全関手比較で、係数評価の充満忠実性を使う。
その証明分割 `projectivePointRingPresentation_constant_coefficients` は
`projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed ⋙
 projectivePointCoefficientComplex A = projectivePointCoefficientComplex A`。
射影性は `ringModule_recover` で元の射影性へ移すだけで、新しい射影性の定理を作らない。
照合の枠はC1・C2・C3の3/3となる。以後、新しい照合が要れば止める。

### U39の前提計算の残り（計3/3）

```lean
def projectivePointCoefficientDerivedIso :
  FunctorIso (nerveMap (projectivePointCoefficientComplex A) ≫ complexDerivedEvaluation A)
    (closedNerveInclusion A (ProjectiveDGModules A PUnit.{1}) ≫
      (projectivePointEquivalence A).hom)

lemma strictSemifreeNormalizedProjectiveModule_coefficients :
  strictSemifreeNormalizedProjectiveModule A ⋙ projectivePointCoefficientComplex A =
    strictSemifreeNormalizedBarComplex A
```

前者は既存の `complexDerivedEvaluation_projectiveRingIso` とC3の復元の合成、
後者は同じ正規化加群の係数評価。U39の前提計算はこれで3/3。
C3では同じ復元比較の強い形
`projectivePointRingPresentation A ⋙ (projectiveRingComplexConstant A).onClosed = 𝟭 _`
も証明する。別の照合ではない。
巨大な `eqToHom` の自然性の簡約を避け、私有の等式消去
`functorMap_heq_of_eq (e : F = G) (f : M ⟶ N) : HEq (F.map f) (G.map f)`
（`cases e; rfl`）と、その係数射への適用に分割した。証明分割のみで新しい数学はない。
全て既定の200,000 heartbeatsのまま検証する。

## 39. R6完成・途中の取り込み点（11-13 夜）

**§33のU01〜U41を完了。R6の途中取り込み候補として報告し、指示どおり止まらずR2〜R4の紙へ進む。**

今回の数学は新規6本521行。

| ファイル（`Project/DerivedCategories/DiagramComparison/`） | 行数 | 内容 |
| --- | ---: | --- |
| `StrictClosedVertexEvaluation` | 78 | C2の閉零セルの全HA評価 |
| `StrictSemifreeNormalizedProjectiveModule` | 64 | 元の正規化barの同じ射影的一点加群への包装 |
| `StrictSemifreeProjectiveApex` | 84 | C2：同じnative全余錐族のapexの照合 |
| `ProjectivePointRingPresentation` | 145 | C3：同じ一点加群の係数からの全関手復元 |
| `ProjectivePointCoefficientDerivedComparison` | 61 | 既存の射影的複体比較への係数移送 |
| `StrictSemifreeNormalizedBarApexComparison` | 89 | U39・U41：同じ計算済みapex、元の実現、指定apexの全関手同型 |

最終型は§33のとおり：

```lean
def strictSemifreeNormalizedBarApexIso :
  FunctorIso (nerveMap (strictSemifreeNormalizedBarComplex A) ≫ complexDerivedEvaluation A)
    (strictSemifreeComputedApexFamily A)

def strictSemifreeRealizationNativeApexIso :
  FunctorIso (strictSemifreeRealizationFamily A)
    (strictSemifreeNativeApexFamily A SimplexCategoryᵒᵖ)
```

U41はU38の逆、U39、U40を順に合成する。全余錐族自体の比較はU37。
U39は同じ全族輸送U32のapex制限から作ったため、別々に選んだ点ごとの同型ではない。

検証：`3b3-build-112-final.log` の対象ビルド7,570 jobs成功、同じ鍵の中で
`3b3-r6-final-112-audit.lean` の17宣言を監査し、全て標準三公理のみ・sorryAxなし。
C2の先行監査は103、U33〜U40の先行監査は§38を参照。
既存宣言・入口・全体監査登録・③-b・⑤aのファイルは変更していない。
`whnf`は係数射のHEqによる小さい等式消去、左右別の合成の正規化で閉じた。
新規ファイルの計算上限は既定値、上限引き上げなし。

検証済み3b-3の累計 **76本6,046行、選択監査278宣言**。
R1・R5・R7の663行を除くR6は **5,383行**。
§20のR6見込み450〜750行に対し、下端＋4,933・上端＋4,633行。
元のnativeセルの全HA成分・全面退化・全パラメーター自然性のAPIが必要だったことが主因。
§31の「四行＋未検証6本」はすべて§33の一覧を通して解消した。

枠の最終使用数：前提計算はU20=1/3、U30=2/3、U31=3/3、U32=1/3、
U33=1/3、U34=1/3、U37=1/3、U38=1/3、U39=3/3、U40=2/3、他0/3。
照合はC1・C2・C3の3/3。証明の包装・分割を新しい数学として追加していない。
外枠20,800行まで14,754行を残す。凍結確定の連絡はこの記録時点で未受領。

## 40. R2〜R4の紙の型つき一覧・再見積もり（11-13 夜、ここで停止）

R6の数学コミットは **`b54bb5e12`**（先行のU33〜U40は`15829cad7`）。
以下は未実装の型案。R2〜R4のLean・ビルドには入らない。
配置は引き続き `Project/DerivedCategories/DiagramComparison/`。
③-bの未取り込みの3b-2、G10、⑤aには依存させず、既存ファイルも変更しない。

### 40.1 共通の記号と受け渡し

以下のコード内だけで次を略記する（新しい本体の定義ではない）。

```lean
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local notation "J" => strictDiagramIndex d
local notation "I" => (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J)
local notation "DA" => derivedInfinityCategory A
local notation "S" => StrictDiagramInfinity A d
local notation "D" => (ihom I).obj DA
local notation "q" => strictDiagramLocalization A d
local notation "ev" => strictDiagramDerivedEvaluation A d
-- Pin X x y := Basic.pinchedHom (X := X) x y
-- qv X := q.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X)
-- evalVertex X := (functorVertexEquiv I DA).symm
--   ((strictComplexDiagramFamily A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
```

`d` は二つの方向だけ。`ev`はR5で作った同じ実射を保持する。
以下で模型や逆を構成するときも、別の評価写像へ結論を差し替えない。
`IsFullyFaithful` の本体の定義に合わせ、写像空間の結論は
`IsSimplicialHomotopyEquivalence` とする（H⁰や通常の自然変換の集合には縮めない）。

### 40.2 R2：写像空間の比較（型つき5項目）

R2aの `M・left・right` は証明で構成するデータであり、比較の同値性を仮定するレコードを入力にはしない。

```lean
-- R2a：両側の全変換空間へ写る同じ解像の模型を構成する。
def strictDiagramMappingSpan (x y : S _⦋0⦌) :
  Σ M : SSet.{u + 1}, (M ⟶ Pin S x y) ×
    (M ⟶ Pin D (ev.app (Opposite.op ⦋0⦌) x) (ev.app (Opposite.op ⦋0⦌) y))
-- 以下、M・left・rightはこの同じspanの射影。

-- R2b：解像から元のobjectwise局所化の全写像空間へ。
lemma strictDiagramMappingSpan_left (x y : S _⦋0⦌) :
  IsSimplicialHomotopyEquivalence (left A d x y)

-- R2c：解像からcoherentな全自然変換空間へ。
lemma strictDiagramMappingSpan_right (x y : S _⦋0⦌) :
  IsSimplicialHomotopyEquivalence (right A d x y)

-- R2d：二つの比較は指定された同じevの作用を計算する。
def strictDiagramMappingSpan_square (x y : S _⦋0⦌) :
  FunctorIso (left A d x y ≫ pinchedHomMap ev x y) (right A d x y)

-- R2e：指定の局所化評価の充満忠実性。
lemma strictDiagramDerivedEvaluation_isFullyFaithful : IsFullyFaithful ev
```

筋：projectiveな図式の解像と全Homを使う変換空間の模型を組み、局所化側とcoherent変換側へ比較する。
R2bで必要なのはobjectwise弱同値の∞局所化としての比較であり、通常のホモトピー圏のroof計算だけでは足りない。
R2cは対象ごとの `Hom` の積や通常endをそのまま使わず、射・合成・全高次成分の整合を含む。
R2dの平方も全写像空間の射として証明し、最後に既存の2-out-of-3とG14の検出を使う。

本体にあるのは `strictDiagramLocalization_isLocalization`・`_universal`、元の
`strictDiagramDerivedEvaluation_factor`、`DGModuleFunctorResolutionNerve` の入力射影の比較。
最後のものは**既にdg関手がある場合**の道具であり、R2cやR3の存在を供給するとは扱わない。
G8の全変換空間・切断比較、G14、barの射影性は再利用する。
不足は上のR2a〜R2dで、R2eはそれらの接続。局所化の頂点が全てqの像だとは無条件に仮定しない。
解像の入力へ戻す場合には局所化の普遍性による同値と端点の輸送をR2a〜R2bに含める。

| 項目 | 見込み行数 |
| --- | ---: |
| R2a：解像・全変換空間の模型 | 800〜1,200 |
| R2b：objectwise局所化との比較 | 900〜1,350 |
| R2c：coherent変換空間との比較 | 1,000〜1,550 |
| R2d・R2e：元の作用の平方・充満忠実性 | 500〜700 |
| R2計 | **3,200〜4,800** |

### 40.3 R3：任意coherent図式の厳密化（型つき5項目）

```lean
-- R3a：任意のcoherent図式Fからstrictな複体図式の模型を実際に作る。
lemma exists_strictComplexDiagram_model (F : I ⟶ DA) :
  ∃ X : StrictComplexDiagram A d, Nonempty (FunctorIso (evalVertex A d X) F)

-- R3b：元のevの本質的全射性。R5の元の因子化も使う。
lemma strictDiagramDerivedEvaluation_isEssentiallySurjective :
  IsEssentiallySurjective ev

-- R3c：順射を元のevに固定した全同値。
lemma strictDiagramDerivedEvaluation_isQCatEquivalence : IsQCatEquivalence ev

-- R3d：この同値から選ぶ逆。別の対象ごとのstrict化の選択ではない。
def strictDiagramCoherentInverse : D ⟶ S

def strictDiagramCoherentUnit :
  FunctorIso (𝟙 S) (ev ≫ strictDiagramCoherentInverse A d)

def strictDiagramCoherentCounit :
  FunctorIso (strictDiagramCoherentInverse A d ≫ ev) (𝟙 D)

-- R3e：任意のパラメーターと全高次単体への同じ逆・余単位。
def strictDiagramCoherentFamilyIso {P : SSet.{u + 1}} (F : P ⟶ D) :
  FunctorIso (F ≫ strictDiagramCoherentInverse A d ≫ ev) F
```

R3dは逆・単位・余単位の一組の構成として数える。
R3aでは頂点の複体を個別に選んでからcoherent作用の存在を仮定しない。
全作用を持つ解像からstrict図式を構成し、元の全coherent図式への同型を結論とする。
R3b〜R3cは既存の
`isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective` に接続できる。
R3d〜R3eの一般の同値の逆と前合成のAPIも既存。
不足の中心はR3aの全coherent作用のstrictな解像で、G8・G14・G9だけから存在を出したとはしない。
G9は解像の添字・宇宙変更に使う場合に限る。R6の具体的barの全族自然性は同じ計算部品として再利用する。

| 項目 | 見込み行数 |
| --- | ---: |
| R3a：全coherent作用の解像・strict図式への実構成 | 3,300〜5,300 |
| R3b・R3c：本質的全射性・指定evの同値判定 | 350〜550 |
| R3d・R3e：逆・単位・余単位と全パラメーター族 | 350〜650 |
| R3計 | **4,000〜6,500** |

**③-b報告§38.2の3との照合**：今回のR3aのFは任意のcoherentなD(A)図式であり、
strict図式に範囲を狭めない。R3eは任意Pの全族なので、任意のcoherentなBE図式のU像にも適用できる。
一方、BE作用を持つstrict表示への持ち上げそのものは、加群のstrict化の結論からは出ない。
同節が別途必要と明記した「BE図式の局所化→Fun(I,CAlg)の比較、または一般定理のBE模型への適用」は
③-bの3b-4側に残る。この不足を③-aの加群版の同値だけで済んだとは報告しない。
R3の入力にBE側のstrict表示の存在を追加することもない。

### 40.4 R4：指定錐・余錐族の両方向輸送（型つき5項目）

下の `JoinCoconeFamily F`・`JoinConeFamily F` は今後の型案。
前者は `H : P ⊗ join I Δ[0] ⟶ DA` と
`(P ◁ joinInl I Δ[0]) ≫ H = (β_ P I).hom ≫ uncurry F`、
後者は `H : P ⊗ join Δ[0] I ⟶ DA` と対応する右端の同じ等式の組である。
`apex`は同じ零単体端への制限、`IsColimitFamily`・`IsLimitFamily`は全パラメーター頂点の錐の普遍性。
`RelativeFamilyIso c c'` は全join写像の `FunctorIso` と、同じapexでの比較の辺が恒等であることを含む。
単なる点ごとのapex同型の族を表す型ではない。

```lean
-- R4a：図式の全関手同型に沿う余錐・錐の輸送（同じapexを保つ）。
def transportJoinCoconeFamily {P : SSet.{u + 1}} {F G : P ⟶ D}
    (e : FunctorIso F G) (c : JoinCoconeFamily F) : JoinCoconeFamily G

def transportJoinConeFamily {P : SSet.{u + 1}} {F G : P ⟶ D}
    (e : FunctorIso F G) (c : JoinConeFamily F) : JoinConeFamily G

-- R4b：全joinの比較と同じ指定apex。相対比較を実際に返す。
def transportJoinCoconeFamily_iso (e : FunctorIso F G) (c : JoinCoconeFamily F) :
  RelativeFamilyIso c (transportJoinCoconeFamily e c)
-- 錐にも同じ型。下方への制限は同じeと一致させる。

-- R4c：同じ逆による往復と、任意のパラメーター制限との整合性。
def transportJoinCoconeFamily_roundtrip (e : FunctorIso F G) (c : JoinCoconeFamily F) :
  RelativeFamilyIso (transportJoinCoconeFamily e.symm (transportJoinCoconeFamily e c)) c
-- 錐にも同じ型。任意r : Q ⟶ Pで制限した輸送の相対比較もこの項目。

-- R4d：余極限性・極限性の保存と反映。
lemma transportJoinCoconeFamily_isColimit (e : FunctorIso F G) (c : JoinCoconeFamily F) :
  IsColimitFamily (transportJoinCoconeFamily e c) ↔ IsColimitFamily c
-- 錐ではIsLimitFamilyの同じiff。

-- R4e：R3の同じ余単位に適用し、coherent族と局所化側の模型の族を両方向へ運ぶ。
def strictDiagramCoconeFamilyComparison {P : SSet.{u + 1}} (F : P ⟶ D) :
  QCatEquivalence
    (coconeFamilySpace (F ≫ strictDiagramCoherentInverse A d ≫ ev))
    (coconeFamilySpace F)
-- 錐にも同じ型。順逆・往復・同じapex・脚・普遍性はR4a〜R4dのデータを保持する。
```

`coconeFamilySpace F` は同じ `coconeRestriction` の関手単体集合上の引き戻しで表す予定。
パラメーターPに準圏性は課さず、既存の関手単体集合と固定apexのsliceの構成を使う。
R4a〜R4dは元の図式同型に自然な全族の接続で、型名だけを新設して性質を仮定にはしない。
`exists_cartesian_cocone_lift`、固定apexのslice、`EquivalenceColimitCones`・極限側、
全族の `FunctorIso.precomp/postcomp`・`fullFamilyUncurryIso` を再利用する。
元の具体的実現と全余錐族の比較は完成済みR6を再利用し、作り直さない。

| 項目 | 見込み行数 |
| --- | ---: |
| R4a・R4b：全族の両方向輸送・指定apexと脚の比較 | 650〜1,050 |
| R4c：往復・パラメーター制限 | 300〜500 |
| R4d・R4e：普遍性と同じR3の逆への接続 | 350〜550 |
| R4計 | **1,300〜2,100** |

### 40.5 全体見込み・停止

未実装は **8,500〜13,400行**。既検証6,046行との合計は **14,546〜19,446行**。
外枠20,800行との差は上端で1,354行。
§20のR2〜R4の計4,900〜7,300行から増えたのは、R6の実測に基づき、
全変換空間の解像と同じ評価への比較、coherent作用のstrict化、固定apexの全族輸送を分けて数え直したため。
この上端は保証ではない。特にR2c・R3aは既存のHTT 4.2.4.4の適用一行で済むAPIをまだ確認できていない。
一覧外のまとまりや外枠超過の見込みが出た場合は、その時点で止めて報告する。

**指示どおり、R2〜R4の紙の一覧を出した地点で停止。Lean実装には進まない。**
R6の途中取り込みと、この一覧の確認を調整役に渡す。共有鍵は解放済み。

## 41. R2再開：解像Homの入力の照合（11-13 夜、継続）

main `47c4c8e2a` を取り込んだ。§40の型つき一覧とR2→R3→R4の承認を確認。
R3a前の途中報告・外枠20,800行・計算上限を上げない条件を維持する。

一般projective図式APIの `IsLocallyPresentable (Complex A)` の入力をLeanで確認中。
Δ・Δᵒᵖに限れば既存の `Reedy.simplexModelCategory`・`simplexOpModelCategory` を使え、
元のobjectwise擬同型の∞局所化は変わらない。新しいprojectiveモデルの存在定理は作らない。
R2aの解像の入力として、このReedyモデルと既存の余単体的解像・horn充填を再利用する。
以下はR2aの構成の分割（まだ未検証）。R2aのspanの両射を作れたとは扱わない。

```lean
def strictDiagramReedyModelCategory : ModelCategory (StrictComplexDiagram A d)
lemma strictDiagramReedyModelCategory_weakEquivalences :
  (strictDiagramReedyModelCategory A d).categoryWithWeakEquivalences.weakEquivalences =
    strictDiagramQuasiIsos A d

def strictDiagramSourceFrame (X : StrictComplexDiagram A d) :
  letI := strictDiagramReedyModelCategory A d
  Reedy.CofibrantResolution Reedy.simplex X

def strictDiagramTargetFactorization (Y : StrictComplexDiagram A d) :
  letI := strictDiagramReedyModelCategory A d
  MorphismProperty.MapFactorizationData (trivialCofibrations (StrictComplexDiagram A d))
    (fibrations (StrictComplexDiagram A d)) (terminal.from Y)

def strictDiagramFibrantTarget (Y : StrictComplexDiagram A d) : StrictComplexDiagram A d

def strictDiagramFibrantTargetComparison (Y : StrictComplexDiagram A d) :
  Y ⟶ strictDiagramFibrantTarget A d Y

lemma strictDiagramFibrantTargetComparison_quasiIso (Y : StrictComplexDiagram A d) :
  strictDiagramQuasiIsos A d (strictDiagramFibrantTargetComparison A d Y)

lemma strictDiagramFibrantTarget_isFibrant (Y : StrictComplexDiagram A d) :
  letI := strictDiagramReedyModelCategory A d
  IsFibrant (strictDiagramFibrantTarget A d Y)

def strictDiagramFrameMapping (X Y : StrictComplexDiagram A d) : SSet.{u}
lemma strictDiagramFrameMapping_obj (X Y : StrictComplexDiagram A d) (n : SimplexCategoryᵒᵖ) :
  (strictDiagramFrameMapping A d X Y).obj n =
    ((strictDiagramSourceFrame A d X).obj.obj n.unop ⟶ strictDiagramFibrantTarget A d Y)
lemma strictDiagramFrameMapping_kanComplex (X Y : StrictComplexDiagram A d) :
  SSet.KanComplex (strictDiagramFrameMapping A d X Y)
```

いずれも既存のモデル・分解・解像・Kan性の特殊化で、新しいモデル構造や充填理論を足さない。
モデルの弱同値の等式はR2aの係数移送の法則1/3として記録する。
比較対象は元の同じ `StrictDiagramInfinity` と `strictDiagramDerivedEvaluation` のまま。
この段階では対象ごとの解像だけであり、全パラメーター自然性も完了を主張しない。

### R2aの関手的解像の証明分割（未検証）

```lean
lemma strictDiagramReedy_cof_hasFunctorialFactorization :
  letI := strictDiagramReedyModelCategory A d
  (cofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
    (trivialFibrations (StrictComplexDiagram A d))
lemma strictDiagramReedy_fib_hasFunctorialFactorization :
  letI := strictDiagramReedyModelCategory A d
  (trivialCofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
    (fibrations (StrictComplexDiagram A d))

def strictDiagramCofFactorizationData :
  letI := strictDiagramReedyModelCategory A d
  (cofibrations (StrictComplexDiagram A d)).FunctorialFactorizationData
    (trivialFibrations (StrictComplexDiagram A d))
def strictDiagramFibFactorizationData :
  letI := strictDiagramReedyModelCategory A d
  (trivialCofibrations (StrictComplexDiagram A d)).FunctorialFactorizationData
    (fibrations (StrictComplexDiagram A d))

def strictDiagramResolutionMapping :
  (StrictComplexDiagram A d)ᵒᵖ ⥤ StrictComplexDiagram A d ⥤ SSet.{u}
lemma strictDiagramResolutionMapping_kanComplex
    (X : (StrictComplexDiagram A d)ᵒᵖ) (Y : StrictComplexDiagram A d) :
  SSet.KanComplex (((strictDiagramResolutionMapping A d).obj X).obj Y)
```

複体の生成モデルの既存の関手的分解と
`Reedy.FunctorFactorizationSequence.hasFunctorialFactorization` を直接使う。
これにより、対象ごとに選ぶ解像だけで全族が自然だとは扱わず、実際の両変数の通常関手を作る。
型や最終範囲の変更はない。R2aのspan・R2b・R2cはまだ完了していない。

23時の連絡を反映：B3の凍結はmainだけ。専用枝へのコミットは続ける。
B3取り込み後のB4追従は連絡を待つ。大きい監査は行わず対象ビルドと小監査だけにする。

### 最初の検証済み分

`StrictDiagramReedyMappingModel` 111行の対象ビルド（`r2-reedy-model-3.log`、2,668 jobs）と
11宣言の小監査（`r2-reedy-model-audit.log`）が通った。標準三公理のみ、sorryAxなし。
一般projective APIの `IsLocallyPresentable.{u} (Complex A)` の自動合成は失敗を確認したが、
Reedy構成ではこの追加入力を要求せず、元の弱同値のクラスも保持できた。
R2の検証済み実測は111行（3b-3累計6,157行）。両変数の関手的解像の新規ファイルは未検証のまま。
R2a〜R2eの完成を主張せず、引き続きR2aの構成を進める。

### R2aの宇宙表示の係数移送（2/3・3/3、未検証）

```lean
def strictDiagramModelNerveIso :
  strictComplexDiagramNerve A d ≅ nerve (modelRelativeCategory (StrictComplexDiagram A d)).category
lemma strictDiagramModelNerveIso_weakEdges :
  (strictDiagramModelNerveIso A d).hom.app (Opposite.op ⦋1⦌) '' strictDiagramWeakEdges A d =
    weakNerveEdges (modelRelativeCategory (StrictComplexDiagram A d))

def strictDiagramModelLocalization :
  nerve (modelRelativeCategory (StrictComplexDiagram A d)).category ⟶ StrictDiagramInfinity A d
lemma strictDiagramModelLocalization_isLocalization :
  IsLocalization (strictDiagramModelLocalization A d)
    (weakNerveEdges (modelRelativeCategory (StrictComplexDiagram A d)))
```

AsSmallの包みの同じ順逆と弱辺の像が2/3、既存の
`isLocalization_of_precomposeIso` による同じ局所化普遍性の移送が3/3。
R2aの前提計算はこれで3/3。既存のhammock比較への入力を揃える係数移送であり、
新しい局所化一意性や一般のモデル圏比較の定理は作らない。
照合の追加枠は消費していない（R6で使ったC1〜C3と別の照合を無断で足さない）。

### R2a〜R2bの局所化側の中間比較（未検証）

```lean
def strictDiagramModelUp : StrictComplexDiagram A d ⥤
  (modelRelativeCategory (StrictComplexDiagram A d)).category
def strictDiagramModelDown : (modelRelativeCategory (StrictComplexDiagram A d)).category ⥤
  StrictComplexDiagram A d

def strictDiagramRightFrameFamily :
  letI := strictDiagramReedyModelCategory A d
  Reedy.CofibrantResolutionFamily (C := (StrictComplexDiagram A d)ᵒᵖ) Reedy.simplex

def strictDiagramRightFrameMapping (X : StrictComplexDiagram A d) :
  StrictComplexDiagram A d ⥤ SSet.{u}

def strictDiagramRightFramePinchedEquivalence (X Y : StrictComplexDiagram A d)
    [IsCofibrant X] :
  QCatEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).obj ((strictDiagramRightFrameMapping A d X).obj Y))
    (pinchedHom (X := StrictDiagramInfinity A d)
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
      ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y)))
lemma strictDiagramRightFramePinchedEquivalence_homotopyEquivalence
    (X Y : StrictComplexDiagram A d) [IsCofibrant X] :
  IsSimplicialHomotopyEquivalence (strictDiagramRightFramePinchedEquivalence A d X Y).hom
```

上のcofibrancyは同じReedyモデルで読む。最終のR2a〜R2eにこの仮定を加えない。
`modelRightFramePinchedEquivalence` は全モデル圏の∞局所化普遍性を既に証明しており、
`LocalizedMappingBifunctor` や `StrictValueObstruction` は使わない。
元の実right frame・第二分解・指定局所化射のままこのAPIを特殊化する。
`ModelUp/Down` はR2aの宇宙移送の証明分割。`nerveMap`の共通Hom宇宙の制約のため、
異なるHom宇宙の通常関手のnerve作用は、各全射列の同じ後合成として直接記述する。
新しい宇宙や射を仮定するものではない。

### R2aの任意局所化頂点への拡張の証明分割（未検証）

```lean
def strictDiagramHammockComparison :
  EInfinity.FrameHom.CoherentLocalizationComparison
    (hammockLocalizationNerveMap (modelRelativeCategory (StrictComplexDiagram A d)))
    (strictDiagramModelLocalization A d)
lemma strictDiagramLocalization_isEssentiallySurjective :
  IsEssentiallySurjective (strictDiagramLocalization A d)
```

`modelRightFrameLocalizationComparison` の既存の全同値と全二胞体、
`coherentNerveVertex_object` で、任意の局所化頂点を元の解像の入力へ戻す。
これは§40.2の「局所化の頂点を無条件にqの像と仮定しない」の解消であり、R2aの証明分割。
R3bの `strictDiagramDerivedEvaluation` の本質的全射性とは別。
任意coherent図式のstrict表示を既に得たとは扱わない。

### R2aのcofibrant表示の証明分割（未検証）

```lean
lemma exists_strictDiagramCofibrantVertex (x : (StrictDiagramInfinity A d) _⦋0⦌) :
  ∃ X : StrictComplexDiagram A d, IsCofibrant X ∧
    Nonempty (VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X)) x)
def strictDiagramCofibrantVertex (x : (StrictDiagramInfinity A d) _⦋0⦌) : StrictComplexDiagram A d
lemma strictDiagramCofibrantVertex_isCofibrant (x : (StrictDiagramInfinity A d) _⦋0⦌) :
  IsCofibrant (strictDiagramCofibrantVertex A d x)
def strictDiagramCofibrantVertexIso (x : (StrictDiagramInfinity A d) _⦋0⦌) :
  VertexIso ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ (strictDiagramCofibrantVertex A d x))) x
```

同じ局所化の頂点表示に、既存のsource frameの零次増大を合成する。
増大のobjectwise擬同型性と元のqの辺の反転を使い、中間比較のcofibrancyの仮定を放電する。
R2aの型が任意の局所化頂点を引数に取るための証明分割で、coherent図式のstrict化は仮定しない。

### R2aのspanの実構成・R2bの証明分割（未検証）

```lean
abbrev strictDiagramMappingSpace (x y : (StrictDiagramInfinity A d) _⦋0⦌) : SSet.{u + 1}
def strictDiagramMappingSpaceEquivalence (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
  QCatEquivalence (strictDiagramMappingSpace A d x y)
    (pinchedHom (X := StrictDiagramInfinity A d) x y)
def strictDiagramMappingLeft (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
  strictDiagramMappingSpace A d x y ⟶ pinchedHom (X := StrictDiagramInfinity A d) x y
def strictDiagramMappingRight (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
  strictDiagramMappingSpace A d x y ⟶
    pinchedHom ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) x)
      ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) y)
```

R2aのspanは§40.2のΣ型のまま。源は実right frame Homを同じ宇宙へ持ち上げたもの。
左脚は元のframe比較と同じcofibrant表示の端点同型の合成。
右脚は左脚と指定された同じ `pinchedHomMap ev` の合成として作る。
右脚の同値性（R2c）はこの定義からは出ず、coherent変換空間との比較の数学として残る。
R2bの型はこの同じspanの射影を使い、
`IsSimplicialHomotopyEquivalence (strictDiagramMappingSpan A d x y).2.1`。
R2dはR2cの後に証明する。一覧の順序を変えてR2cを完了したとは扱わない。

### R2a・R2bの検証結果（11-13 23時台）

上の未検証として記録した6本を対象ビルドで確認した。
`StrictDiagramFunctorialFrames` 112行、`StrictDiagramModelLocalization` 130行、
`StrictDiagramRightFrameComparison` 69行、`StrictDiagramLocalizedVertices` 65行、
`StrictDiagramCofibrantVertices` 72行、`StrictDiagramMappingSpan` 84行。
先の `StrictDiagramReedyMappingModel` 111行を含め、R2は7本643行、3b-3累計83本6,689行。
対象ビルドの最終結果は `r2-mapping-span-2.log`（9,593 jobs、成功）。
新規39宣言の小監査を分割して実施し、全て標準三公理のみ（最後の12件は
`/tmp/is-w1/r2-span-audit.log`）。sorry・新公理・計算上限の引き上げはない。

完成した一覧項目はR2a（任意の局所化頂点のspan）とR2b（その左脚の同値性）。
R2c（同じ右脚の同値性）、R2d、R2eは残る。R2全体や停止点5の完成とは扱わない。
R3aにはまだ入っていない。

11-13 23時の連絡に従い、B3中も専用枝のコミットを続ける。mainへの取り込みは行わず、
対象ビルドと上の小監査だけを行った。

### R2cの値の入力の係数移送（1/3、未検証）

```lean
lemma complexDerivedEvaluation_eq_ordinarySource :
  complexDerivedEvaluation A = EInfinity.ComplexLimits.complexOrdinaryDerivedSource A
def complexDerivedEvaluation_hammockSourceIso :
  FunctorIso (complexHammockSource A ≫ complexHammockDerivedComparison A)
    (complexRelativeNerveDown A ≫ complexDerivedEvaluation A)
```

`ComplexDerivedHammockSource.lean` に置く。前者はR2cの前提計算1/3、
後者は既存の指定sourceIsoへの係数移送の証明分割。
⑤aの既存 `ComplexHammockSource` を再利用し、⑤aのファイルは変更しない。
全複体での `ComplexHammockFullyFaithful` もmainにあることを確認した。
これは値の比較であり、図式全体でのR2cを既に証明したことにはしない。

### R2cのstrict側のendの表示（前提計算2/3、未検証）

`StrictDiagramFrameSections.lean` に同じright frameの各単体の全成分を、
全ての添字射の自然性の式を課したsubtypeとして記述する。

```lean
def StrictDiagramFrameSection (X Y : StrictComplexDiagram A d) (n : SimplexCategoryᵒᵖ) :=
  { f : ∀ j, X.obj j ⟶ ((strictDiagramFrame A d Y).obj n).obj j //
    ∀ (i j : strictDiagramIndex d) (a : i ⟶ j),
      X.map a ≫ f j = f i ≫ ((strictDiagramFrame A d Y).obj n).map a }
def strictDiagramFrameSectionsIso (X Y : StrictComplexDiagram A d) :
  (strictDiagramRightFrameMapping A d X).obj Y ≅ strictDiagramFrameSections A d X Y
```

同じ射を成分として読む係数移送で、R2cの前提計算2/3。単体作用と逆射はその証明分割。
このstrictなendがhomotopy endを計算することは、ここではまだ証明していない。
自然性を仮定として加えてR2cを済ませたり、成分ごとの弱同値だけからendの弱同値を出したりしない。

### R2cの前提計算2本の検証結果（11-13 夜）

`ComplexDerivedHammockSource` 36行、`StrictDiagramFrameSections` 89行を対象ビルドで確認した。
前者は9,395 jobs、後者は9,496 jobs、いずれも成功。
後者の初回の関手則の名前解決と自然変換の外延性の誤りを修正し、再実行で通した。
小監査7宣言は標準三公理のみ（`/tmp/is-w1/r2-value-sections-audit.log`）。

R2の実測は9本768行、3b-3累計85本6,814行、選択監査324宣言。
R2cの前提計算は2/3。残り1枠を新しい数学の仮定の導入には使わない。
右脚の同値性そのものは未了。次は同じframeの成分表示から、coherent変換空間の
homotopy endへの比較と、元の評価の誘導射との照合を行う。
これは§40のR2cの証明の残りで、R3a・R4には入っていない。

## 42. R2c：評価したframeによる値の模型（11-14、実装中）

前回は検証済み2本を `78475b4a0` に保存し、進捗あり。作業木はcleanで再開した。
R2cの残りを進めるため、以下を同じR2cの証明の分割として記録する。

```lean
-- 既存Reedy成分則の係数移送：R2cの前提計算3/3。
lemma strictDiagramEvaluationAt_isQuillen (j : strictDiagramIndex d) :
  Quillen.IsLeftQuillen ((evaluation (strictDiagramIndex d) (Complex A)).obj j) ∧
  Quillen.IsRightQuillen ((evaluation (strictDiagramIndex d) (Complex A)).obj j)
-- 図式のsource frameを、同じ各複体で評価する。
def strictDiagramEvaluatedSourceFrame (X : StrictComplexDiagram A d)
  (j : strictDiagramIndex d) : SimplexCategory ⥤ Complex A
lemma strictDiagramEvaluatedSourceFrame_cofibrant (X : StrictComplexDiagram A d)
  (j : strictDiagramIndex d) :
  Reedy.reedyLeft Reedy.simplex (cofibrations (Complex A))
    (initial.to (strictDiagramEvaluatedSourceFrame A d X j))
lemma strictDiagramEvaluatedSourceFrame_homotopicallyConstant
  (X : StrictComplexDiagram A d) (j : strictDiagramIndex d)
  {m n : SimplexCategory} (a : m ⟶ n) :
  weakEquivalences (Complex A) ((strictDiagramEvaluatedSourceFrame A d X j).map a)
lemma strictDiagramFibrantTarget_obj_isFibrant (Y : StrictComplexDiagram A d)
  (j : strictDiagramIndex d) : IsFibrant ((strictDiagramFibrantTarget A d Y).obj j)
def strictDiagramPointFrameMapping (X Y : StrictComplexDiagram A d) :
  (strictDiagramIndex d)ᵒᵖ ⥤ strictDiagramIndex d ⥤ SSet.{u}
lemma strictDiagramPointFrameMapping_kanComplex (X Y : StrictComplexDiagram A d)
  (i : (strictDiagramIndex d)ᵒᵖ) (j : strictDiagramIndex d) :
  KanComplex (((strictDiagramPointFrameMapping A d X Y).obj i).obj j)
```

最初の法則は `Reedy.cofibration_app`・`fibration_app` と同じobjectwise弱同値の特殊化。
残りは既存 `reedyCofibrant_of_preservesLatching`、frameの評価、
`cosimplicialHom_kanComplex` を同じ図式のsource frameとfibrant targetへ入れる証明分割。
新しい一般モデル構造や数学的仮定は導入しない。
このKan値の全二変数Homからhomotopy endへの比較がR2cの核心として引き続き残る。

### R2cの二変数frame Homのend（証明分割、未検証）

```lean
def strictDiagramPointFrameEndWedge (X Y : StrictComplexDiagram A d) :
  Wedge (strictDiagramPointFrameMapping A d X Y)
-- 上のwedgeの点は、元の strictDiagramFrameMapping A d X Y。
def strictDiagramPointFrameEndIsLimit (X Y : StrictComplexDiagram A d) :
  IsLimit (strictDiagramPointFrameEndWedge A d X Y)
def strictDiagramPointFrameEndIso (X Y : StrictComplexDiagram A d) :
  strictDiagramFrameMapping A d X Y ≅ end_ (strictDiagramPointFrameMapping A d X Y)
lemma strictDiagramPointFrameEnd_kanComplex (X Y : StrictComplexDiagram A d) :
  KanComplex (end_ (strictDiagramPointFrameMapping A d X Y))
```

評価したsource frameとfibrant targetの同じHomに、全ての添字射の自然性を課す。
自然変換の成分からwedgeを作り、その普遍性を全単体上で証明するR2cの証明分割。
この特定のendのKan性は元の図式圏でのframeのKan性から出す。
「Kan複体の任意のendはKan」や「通常endとhomotopy endは無条件に一致」を使わない。
後者の導来的な比較と元のspanの右脚への接続は未了のまま。

### §42の検証・実測（11-14）

- `StrictDiagramEvaluationFrames.lean`：118行、8宣言。対象ビルド成功（2,675 jobs）。
- `StrictDiagramPointFrameEnd.lean`：91行、6宣言。対象ビルド成功（2,686 jobs）。
- 14宣言の小監査成功、標準三公理のみ（`/tmp/is-w1/r2-point-end-audit.log`）。
- 初回の型クラス探索は、図式宇宙0と零対象を明示して局所化した。
  弱同値の評価はΔ・Δᵒᵖで直接簡約。計算上限は上げていない。
- 新しい入口・大きい監査は実行していない。直接のimporterは今回のendファイルで、同じ対象ビルドに含まれる。

実測：R2は11本977行、3b-3全体は87本7,023行、選択監査338宣言。
R2cの前提計算は3/3。今回の二つの補題群は§42の型で先に記録した、
同じR2cの評価・frame・endの証明分割であり、R2a〜R2eの範囲や仮定を変更していない。

### 次の接続の現状

値側には既存 `ComplexHammockFullyFaithful.complexHammockDerivedComparison_fullyFaithful`、
coherent側には
`Kerodon/LargeInfinityCategories/PresentableInfinityCategories/TwistedHomEndSection.lean` の
`twistedFunctorHomToEndSections`（全関手Homからtwisted endの切断への実比較）がある。
後者のdocstringどおり、そのファイル自身は比較射を構成するだけで、同値性の証明ではない。
`FunctorCompactEndReduction` の入力にあるendの極限錐族を、無条件に使用可能な定理と読まない。

次は、今回の特定のReedy frameによるendをcoherentな切断へ比較し、
元の `strictDiagramDerivedEvaluation` の右脚がその比較であることを証明する。
今回の通常endの普遍性・Kan性だけから、homotopy endとの一致は結論していない。
R2c・R2d・R2eは引き続き未了、R2の完成および停止点5の完成は未主張。
R3aへの着手もない。目標「R2を完成」はactiveのまま。

## 43. R2cの核心の再監査：独立の数学が不足（11-14、判断を要する地点）

現物は `6f1102459`、作業木cleanで確認した。前回は進捗あり。
R2cを既存APIだけで閉じられるか、coherent側の比較をさらに追跡した結果を記録する。
この節では新しいLeanの仮定・宣言を追加していない。

### 43.1 見つかった部品と、その限界

| 現在の本体 | 実際に証明していること | 証明していないこと |
| --- | --- | --- |
| `StrictDiagramPointFrameEnd` | 実frame Homと通常endの同型、この特定のendのKan性 | homotopy endを計算すること |
| `TwistedHomEndSection.twistedFunctorHomToEndSections` | 元のcoherentな関手Homからendの切断への実射と評価式 | その実射の同値性 |
| `EndSectionsRelativeHom.functorEndSectionsBifunctorHomEquivalence` | 切断を分類した二変数図式間のHomに移す全同値 | 元の関手F,GのHomへの全同値 |
| `EndSectionsYonedaModel.functorEndSectionsYonedaHomEquivalence` | 切断を `Hom(y_A, G ⋙ Hom_C(F(-),-))` に移す全同値 | 元のFun(A,C)のHomへの同値 |
| `HomWeightYonedaLeftKan.exists_homWeightYonedaLeftKan` | 別の選択LがLanであることと、L(c)とHom係数の対象ごとの同型 | 指定Hom係数族と指定Yoneda単位自身がLanであること |
| `HomWeightYonedaLeftKan.homWeightYonedaLeftKanComparison` | 選択Lから指定Hom係数族への実自然変換、単位との可換式 | 比較の成分が可逆であること |

`homWeightYonedaLeftKan_valueIso` は、同じ実比較の成分の可逆性ではない。
対象ごとの同型の存在だけを、指定の実自然変換の同型性として使用することはできない。
`FunctorCompactEndReduction` もendを極限として与える族を入力に取る条件付きの帰着である。
今回見つけたYoneda側の二つの同値を用いても、この不足は消えない。

### 43.2 この経路に必要な独立の数学（型）

第一はP-12のend表示の核心そのもの。既存の比較射を固定すると、必要な主張は次の型になる。

```lean
-- 一般の独立定理。現在の本体にはこの証明を確認できていない。
lemma twistedFunctorHomToEndSections_isSimplicialHomotopyEquivalence
    {K C : SSet.{v}} [Quasicategory K] [Quasicategory C] (F G : K ⟶ C) :
  IsSimplicialHomotopyEquivalence (twistedFunctorHomToEndSections F G)
```

既存のYoneda経路を完成させる場合の不足は、全Hom係数族の指定単位が左Kan延長の単位であること。
その途中で `homWeightYonedaLeftKanComparison F β hβ` の**同じ実比較**が全成分で可逆なことを、
密度の局所余錐と指定単位との両立から示す必要がある。
これは既存の単位・自然性・係数表示の計算一件ではなく、独立の数学の証明である。
P-12の一般の核心をR2cの「係数移送3/3」の中へ隠して追加しない。

第二は加群・Reedy図式側。§40.1と同じI, DAを使い、
`F_X := evalVertex A d X`、`F_Y := evalVertex A d Y` と略記すると、
実比較の存在と弱同値性として次が必要。

```lean
-- R2cで実際に要る局所形の不足。通常endのKan性からは従わない。
∃ cmp : (SSet.uliftFunctor.{u + 1, u}).obj (strictDiagramFrameMapping A d X Y) ⟶
    simplicialSections (functorEndProjection F_X F_Y),
  IsSimplicialHomotopyEquivalence cmp
```

さらに、これらを最終のright frameのspanへ移したとき、指定された元の
`strictDiagramDerivedEvaluation` が誘導する射と全族で一致する必要がある。
R2dの平方の定義的な可換性を先に書いても、R2cの弱同値性は解消しない。

### 43.3 停止条件の適用

指示書 `inf-supply-w1.md` の「R6の取り込みと、R2〜R4の承認」は
「順序はR2→R3→R4」「数え方はIS-W2 §14と同じ」。同§14の
**「それ以外の新しい数学の補題が要ったら止まる」**をここで適用する。
一般のP-12のend定理を追加するのは、承認済み§40のR2a〜R2eの実射の構成・比較そのものから
独立したまとまりであり、証明分割や前提計算として無制限に追加しない。

Leanは検証済み `6f1102459` で保存済み。この経路の追加実装は止め、
P-12のendの核心を供給側に依頼するか、③-aの追加の型つき一覧へ入れるか、
調整役の判断を待つ。Reedy側の局所比較も、上の一般end定理だけで完了したとはしない。
R2cの完成のための二つの不足と元の評価の照合を区別し、R2自体の完了は主張しない。
目標「R2を完成」はactiveのまま、blockedの判定はまだ行わない。

## 44. R2c-E・R2c-R：追加承認後の型つき一覧・再見積もり（11-14、紙）

11-14の調整役の追加承認を受け、§43の承認待ちは解消して紙の作業を再開した。
ユーザーの追加指示に従い、Eの各項目にKerodonのTagとHTTの番号を付す。
現物は `c6ac2b470`、数学の検証済みは `6f1102459`。既検証の実測は87本7,023行。
**全体の見込みは17,723〜24,273行。上端が20,800行を3,473行超えるため、
今回の条件付き承認の停止条件に当たり、新しいLeanには入らない。**
以下は追加の型案であり、証明済み宣言・本体への仮定の追加ではない。

### 44.1 共通記法・原典の確認

Eの型の中だけで次を略記する。全て実際の既存の単体集合・射。

```lean
variable {K C : SSet.{v}} [Quasicategory K] [Quasicategory C]
variable (F G : K ⟶ C)
-- U := SSet.uliftFunctor.{v + 1, v}
-- yK := yonedaInfinityMap K
-- WF := presheafHomWeightDiagram F
-- WG := presheafHomWeightDiagram G
-- TF G := twistedArrowHomSpace (functorVertex F) (functorVertex G)
-- SF G := simplicialSections (functorEndProjection F G)
-- PF G := pinchedHom (functorVertex F) (functorVertex G)
```

原典に直接ある主張と、実射の選択を保つLean固有の照合を区別する。
引用番号は同じ文言の定理だと無条件に主張するものではなく、下の表に「直接」「基礎」「合成」を明記する。

- twisted arrowの基礎：[Kerodon Construction 8.1.1.1, Tag 03JG](https://kerodon.net/tag/03JG)、
  [Proposition 8.1.1.10, Tag 03JN](https://kerodon.net/tag/03JN)、
  [Definition 8.3.3.1, Tag 046B](https://kerodon.net/tag/046B)。
- YonedaとKan：[Kerodon Proposition 8.3.1.3, Tag 03M5](https://kerodon.net/tag/03M5)、
  [Proposition 7.3.6.1, Tag 0309](https://kerodon.net/tag/0309)、
  [§8.4.3, Tag 03W8](https://kerodon.net/tag/03W8)。
- [HTT（著者公開PDF）](https://www.math.ias.edu/~lurie/papers/HTT.pdf)：
  Proposition 5.1.3.1、Lemma 5.1.5.3、Proposition 4.3.3.7、Proposition 5.2.6.3、
  Corollary 3.3.3.4を確認する。
- 関手の写像空間のend表示を**直接**述べる一次文献は、
  [Gepner–Haugseng–Nikolaus, *Lax colimits and free fibrations in ∞-categories*, Proposition 5.1, pp.13–14](https://www.uni-muenster.de/IVV5WS/WebHop/user/nikolaus/Papers/freepres_arxiv.pdf#page=13)。
  同証明がHTT 3.3.3.4・5.2.6.3・5.1.3.1へ帰着していることも確認した。
  **同じend表示を直接述べるHTTの番号は確認できていない。HTTの番号として捏造しない。**
  またtwisted arrowに関する「5.2.1.11」は同論文ではHigher Algebraの引用であり、
  HTT 5.2.1.11と取り違えない。
- 既存ファイルの一部が付しているTag 06NCは§9.5の大きい節のTagであり、
  end表示そのものの直接のTagではない。今回の一覧の出典をこれだけで済ませない。

### 44.2 R2c-E：一般のend比較（E01〜E06）

既存のYoneda経路を第一候補とする。Gepner–Haugseng–Nikolausの
presheaf随伴による別経路は、一般の指定比較の自然性の計算が既存経路より短いと確認できた場合の代案。
単にいずれかの全同値が存在するだけで、元の `twistedFunctorHomToEndSections` の同値性を済ませない。

**E01：指定されたYoneda左Kan比較の同じ成分の可逆性。**

```lean
lemma homWeightYonedaLeftKanComparison_component_isIso
    {L : U.obj C ⟶ PresheafInfinity K}
    (β : SSet.Homotopy yK (U.map F ≫ L))
    (hβ : IsLeftKanExtension (U.map F) yK L β)
    (c : C _⦋0⦌) :
  IsIso (functorHomEvaluate
    (homWeightYonedaLeftKanComparison F β hβ) (ULift.up c))
```

密度の局所余錐と指定単位の両立から、選んだ同じ比較の成分を同定する。
全比較の `IsIso` は既存 `kanFunctorHom_isIso_of_components` への接続という証明分割に含める。
対象ごとの別の同型を持ってくるだけでは代用しない。

**E02：指定単位による全写像空間のKan普遍性。**

```lean
def homWeightYonedaLanHomEquivalence (F G : K ⟶ C) :
  QCatEquivalence
    (pinchedHom (functorVertex WG) (functorVertex WF))
    (pinchedHom (functorVertex yK) (functorVertex (U.map G ≫ WF)))
```

E01と既存の単位の可換式でKan普遍性を指定Hom係数族へ運び、
全パラメーターの写像空間の同値を得る。
`kanLeftKanExtension_homUniversal` が返す通常のHomの全単射だけを、
高次を含む結論と取り違えない。既存 `LeftCanonicalMapping` の全族による判定を使う。

**E03：end切断と元の関手Homの両模型の同値。**

```lean
def twistedFunctorHomEndEquivalence (F G : K ⟶ C) :
  QCatEquivalence (U.obj (TF G)) (U.obj (SF G))
```

`functorEndSectionsYonedaHomEquivalence`、E02、
`homWeightDiagramHomEquivalence` と元のtwisted Homの模型比較を合成する。
宇宙を一度上げて比較することを型に明示し、後で元の宇宙へ反映する。

**E04：同じ実比較との全族の照合。**

```lean
def twistedFunctorHomEndEquivalence_comparison (F G : K ⟶ C) :
  FunctorIso (twistedFunctorHomEndEquivalence F G).hom
    (U.map (twistedFunctorHomToEndSections F G))
```

これはTF Gの全単体上の同じ二写像の比較。
任意Pと `a : P ⟶ U.obj (TF G)` に前合成した比較は、
同じFunctorIsoから `precomp a` で取り、Pごとの別の選択を行わない。

**E05：承認された元の一般定理。**

```lean
lemma twistedFunctorHomToEndSections_isSimplicialHomotopyEquivalence
    (F G : K ⟶ C) :
  IsSimplicialHomotopyEquivalence (twistedFunctorHomToEndSections F G)
```

E03・E04と宇宙移送の反映を使う。K・Cの一般性は保ち、Δなどに狭めない。

**E06：Reedy側が使うpinched模型の同じ比較。**

```lean
def functorPinchedEndMap (F G : K ⟶ C) : PF G ⟶ SF G
lemma functorPinchedEndMap_isSimplicialHomotopyEquivalence (F G : K ⟶ C) :
  IsSimplicialHomotopyEquivalence (functorPinchedEndMap F G)
```

既存のpinched・coslice・twisted HomのKan模型の比較とE05を合成する包装。
E06が入力する比較を、R側の三角形でも同じ射として使う。

| 項目 | Kerodonの対応Tag（役割） | HTTの対応番号（役割） | 新規配置案 |
| --- | --- | --- | --- |
| E01 | [03M5](https://kerodon.net/tag/03M5)・[03W8](https://kerodon.net/tag/03W8)：Yoneda・密度の基礎 | 5.1.3.1・5.1.5.3：基礎。指定比較の成分の照合は追加証明 | `Kerodon/TheYonedaEmbedding/Cocompletion/HomWeightYonedaKanComparison.lean` |
| E02 | [0309](https://kerodon.net/tag/0309)：Kanの全写像空間の普遍性 | 4.3.3.7：Kan随伴の基礎（別経路なら5.2.6.3） | 同上、必要なら葉を分割 |
| E03 | [046B](https://kerodon.net/tag/046B)・[03M5](https://kerodon.net/tag/03M5)：Hom分類・Yonedaの合成 | 3.3.3.4・5.1.3.1・5.2.6.3：合成の根拠。直接のend表示はGHN Prop 5.1 | `Kerodon/TheYonedaEmbedding/TwistedArrowsAndCospans/EndSectionsEquivalence.lean` |
| E04 | [03JG](https://kerodon.net/tag/03JG)・[0309](https://kerodon.net/tag/0309)：元の構成とKan比較を保持 | 3.3.3.4・4.3.3.7の比較の実射を保持する形式化上の追加照合。直接同名の命題ではない | 同節 `EndSectionsComparisonFamily.lean` |
| E05 | [03JN](https://kerodon.net/tag/03JN)・[046B](https://kerodon.net/tag/046B)・[0309](https://kerodon.net/tag/0309)：twisted arrow/endを組む基礎 | 3.3.3.4・5.1.3.1・5.2.6.3から導く。直接の主張はGHN Prop 5.1 | 同節 `EndSectionsWeakEquivalence.lean` |
| E06 | [03JV](https://kerodon.net/tag/03JV)：twisted Homのホモトピー輸送 | §1.2.2・3.3.3.4：写像空間模型と切断表示の基礎、E05の系 | 同節 `PinchedEndSections.lean` |

新しい一般定理はKerodonの章・節に置く。R2のファイルに一般定理を埋め込まない。
既存の `PresentableInfinityCategories/` の葉は再利用し、移動・本文変更はしない。
E04の全族照合は、今回承認された実比較の主張そのもので、以前の照合枠C1〜C3を再利用したとは数えない。
E01〜E06それぞれについて、追加の前提計算法則はIS-W2 §14どおり3本まで。

### 44.3 R2c-R：加群のReedy局所比較（RR01〜RR05）

型の中だけで§40.1のI, DA, S, evを使う。
`F_X := evalVertex A d X : I ⟶ DA`、
`F_x := (functorVertexEquiv I DA).symm (ev.app (Opposite.op ⦋0⦌) x)` と略記。
後者は元の同じevの頂点であり、別の評価を選ばない。
`Γ(F,G) := simplicialSections (functorEndProjection F G)` とする。
配置はいずれも `Project/DerivedCategories/DiagramComparison/` の新規ファイル。

**RR01：実frameのendからcoherent切断への実比較。**

```lean
def strictDiagramFrameEndComparison (X Y : StrictComplexDiagram A d) :
  (SSet.uliftFunctor.{u + 1, u}).obj (strictDiagramFrameMapping A d X Y) ⟶ Γ(F_X,F_Y)
```

既存の評価frameと同じsource frame・fibrant targetを使い、
全添字射・全高次単体の整合を持つ切断を作る。
`StrictDiagramPointFrameEndIso` はstrict側の表示の入口として再利用する。

**RR02：同じ比較の単体的ホモトピー同値性。**

```lean
lemma strictDiagramFrameEndComparison_isSimplicialHomotopyEquivalence
    (X Y : StrictComplexDiagram A d) :
  IsSimplicialHomotopyEquivalence (strictDiagramFrameEndComparison A d X Y)
```

通常endのKan性ではなく、Reedyのcofibrancy・fibrancyによる相対的な充填を使う。
各値の `ComplexHammockFullyFaithful` とG8の切断比較へ渡す。
相対的充填・整合を仮定したレコードを入力に追加して済ませない。

**RR03：最終の同じright frameの模型への移送。**

```lean
def strictDiagramRightFrameEndEquivalence (x y : S _⦋0⦌) :
  QCatEquivalence (strictDiagramMappingSpace A d x y) Γ(F_x,F_y)
```

同じcofibrant表示・両frameの混合比較・元の端点同型を用いる。
`strictDiagramMappingSpace` の定義や元のspanを変更しない。

**RR04：元のevの作用との全族の三角形。**

```lean
def strictDiagramRightFrameEndTriangle (x y : S _⦋0⦌) :
  FunctorIso
    (strictDiagramMappingRight A d x y ≫ functorPinchedEndMap F_x F_y)
    (strictDiagramRightFrameEndEquivalence A d x y).hom

def strictDiagramRightFrameEndTriangleFamily (x y : S _⦋0⦌)
    {P : SSet.{u + 1}} (a : P ⟶ strictDiagramMappingSpace A d x y) :
  FunctorIso
    (a ≫ strictDiagramMappingRight A d x y ≫ functorPinchedEndMap F_x F_y)
    (a ≫ (strictDiagramRightFrameEndEquivalence A d x y).hom)

lemma strictDiagramRightFrameEndTriangleFamily_restrict (x y : S _⦋0⦌)
    {P Q : SSet.{u + 1}} (r : Q ⟶ P) (a : P ⟶ strictDiagramMappingSpace A d x y) :
  strictDiagramRightFrameEndTriangleFamily A d x y (r ≫ a) =
    (strictDiagramRightFrameEndTriangleFamily A d x y a).precomp r
```

元の `strictDiagramDerivedEvaluation_factor` と同じ係数・端点移送を用いる。
後の二つは同じ最初のFunctorIsoの前合成として構成する証明分割。
点ごとの任意の同型や零単体上の一致に弱めない。

**RR05：承認済みR2cの元のspanでの結論。**

```lean
lemma strictDiagramMappingSpan_right (x y : S _⦋0⦌) :
  IsSimplicialHomotopyEquivalence (strictDiagramMappingSpan A d x y).2.2
```

E06・RR03・RR04と2-out-of-3を使う。
続くR2d・R2eは§40.2の型を変えずに証明する。
RR01〜RR05の新規配置は、例えば `StrictDiagramCoherentEndMap`、
`StrictDiagramCoherentEndWeak`、`StrictDiagramRightFrameEndComparison`、
`StrictDiagramRightFrameEndFamily`、`StrictDiagramMappingFullyFaithful` に分ける。
RR04を含む各項目に前提計算3本まで。新しい別の数学を証明分割と呼んで追加しない。

### 44.4 見込み・外枠との照合（重複なし）

以下は**未実装分だけ**。E・RRを旧R2cの1,000〜1,550行へ単純加算せず、
それを置き換える。検証済み7,023行にはR2の評価frame・endの977行を含む。

| 新しい一覧の区分 | 未実装の見込み（行） | 見積もりの中身 |
| --- | ---: | --- |
| E01 | 650〜1,050 | 同じ局所余錐・指定単位による成分の可逆性 |
| E02 | 500〜850 | 全パラメーターのKan写像空間への接続 |
| E03・E05・E06 | 200〜350 | 既存のHom模型・宇宙移送・全同値の合成 |
| E04 | 450〜750 | 元の実比較との全族照合 |
| **R2c-E小計** | **1,800〜3,000** | 一般のK・Cのまま |
| RR01 | 650〜1,050 | 相対条件を保つ実切断比較 |
| RR02 | 1,400〜2,200 | Reedyの相対充填、strict endと導来的な切断の比較 |
| RR03 | 600〜1,000 | 最終のright frame・同じ任意端点への移送 |
| RR04 | 300〜450 | 元のevと全Pの三角形 |
| RR05 | 150〜250 | 元の右脚へ2-out-of-3を戻す |
| **R2c-R小計** | **3,100〜4,950** | Γの比較と元の評価の照合を両方含む |
| R2d・R2e | 500〜700 | §40.2を維持 |
| R3 | 4,000〜6,500 | §40.3を維持（任意coherent図式のstrict化） |
| R4 | 1,300〜2,100 | §40.4を維持（両方向の指定錐・余錐の全族） |
| **未実装合計** | **10,700〜17,250** | |
| 検証済み | 7,023 | 87本、選択監査338宣言 |
| **完成までの全体** | **17,723〜24,273** | **上端は外枠より3,473行多い** |

R3を根拠なく削って帳尻を合わせない。E・RRは写像空間の比較であり、
任意coherent図式をstrict図式へ持ち上げるR3aを既に供給するものではない。
R4の同じapexと全joinの相対比較も、そのまま残す。
別証明による短縮が確認できれば見積もりを下げられるが、現時点でその短縮を保証しない。

**結論：11-14の条件付き承認の「超えるときは止まって報告」に従い、この紙の地点で停止。**
R2c-E・R2c-Rは追加承認されたが、全体の規模について調整役がユーザーに諮るための報告。
追加のLean実装・対象ビルド・大きい監査は実行していない。
R2未完のまま、検証済みの範囲と元の全目標を維持する。

## 45. R2を先行する再開（11-14、停止点5aまで）

調整役の追加承認を確認した。今回の対象はE01〜E06・RR01〜RR05・R2d・R2e。
未実装5,400〜8,650行、既検証7,023行と合わせ12,423〜15,673行。
外枠20,800行に収まる。R3・R4は利用側との範囲判断まで保留し、ここでは着手しない。
R2e（元の実評価の充満忠実性）を検証した地点を停止点5aとする。

### E01の前提計算1/3・2/3（型、未検証）

`twistedSourceHomUnit_homUniversal` は既存。これを使うため、指定Yoneda単位自身の
始点固定評価を、同じtwisted arrowの実正方形の分類へ戻す。
以下の型でUは `SSet.uliftFunctor.{u + 1, u}`、aはAの元の頂点。

```lean
-- E01-L1（1/3）：指定共同Hom単位は、元のTw(F)の実正方形の分類である。
lemma functorHomBifunctorUnit_eq_square (F : A ⟶ C) :
  functorHomBifunctorUnit F =
    precomposeFunctorHom (uliftTensorIso A.op A).inv
      (leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F))

-- E01-L2（2/3）：指定Yoneda単位の同じ前層成分での評価。
lemma homWeightYonedaUnit_evaluate_heq (F : A ⟶ C) (a : A _⦋0⦌) :
  HEq ((hoFunctor.map ((ihom (U.obj A)).map
      (evaluateFunctorAt (Y := SpaceInfinity.{u})
        (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map (homWeightYonedaUnit F))
    (precomposeFunctorHom
      (lift (SSet.const (ULift.up (SSet.opObjEquiv.symm a))) (𝟙 (U.obj A)))
      (functorHomBifunctorUnit F))
```

`HomWeightUnitEvaluation.curryFunctorHomCongr_evaluate_heq` と元の実正方形の定義を再利用する。
これらは新しい単位の選択や、任意の別の同型への変更ではない。
配置は `Kerodon/TheYonedaEmbedding/Cocompletion/HomWeightYonedaUnitSquare.lean`。
E01のdocstringにKerodon 03M5・03W8、HTT 5.1.3.1・5.1.5.3を、
基礎となる引用であると区別して記す。E01自身の完成とは扱わない。

### E01の前提計算3/3：始点固定の実引き戻し模型（未検証）

```lean
def homWeightYonedaSourcePullbackIso (F : A ⟶ C) (a : A _⦋0⦌) :
  pullback (functorHomBifunctorProjection F F) (twistedArrowSourceInclusion a) ≅
    pullback (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F
lemma homWeightYonedaSourcePullbackIso_postcomp (F : A ⟶ C) (a : A _⦋0⦌) :
  fiberComparisonBaseChange (twistedArrowProjection A) (functorHomBifunctorProjection F F)
      (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F)
      (twistedArrowSourceInclusion a) ≫ (homWeightYonedaSourcePullbackIso F a).hom =
    pullback.lift (twistedArrowSourcePostcomp F a) (twistedArrowSourceProjection a)
      (twistedArrowSourcePostcomp_projection F a)
```

既存の引き戻しの貼り合わせ同型と `twistedArrowSourceInclusion_postcomp` を使う係数移送。
両射影の計算はこの同じ移送の証明分割として記録する。
これにより、単位を評価して得る実写像を、普遍性が既知の `twistedSourceHomUnit` の
全空間写像へ照合する入力を固定する。残る分類後の同じ正方形の照合をE01の証明で行う。
E01の前提計算はこれで3/3。

## 46. E01の係数移送：検証済みの部分と、追加の合成則（11-14）

### 46.1 検証済み

新規 `Kerodon/TheYonedaEmbedding/Cocompletion/HomWeightYonedaSourcePullback.lean`。
100行・4宣言。§45のE01-L3の同じ係数移送と、その証明分割だけを実装した。

- `homWeightYonedaSourcePullbackIso`：始点固定した共同Homの引き戻しを、
  同じ始点固定Hom射影のFによる引き戻しへ移す。
- `homWeightYonedaSourcePullbackIso_hom_fst_fst`：元のtwisted arrowへの第一射影を保つ。
- `homWeightYonedaSourcePullbackIso_hom_snd`：元のAへの第二射影を保つ。
- `homWeightYonedaSourcePullbackIso_postcomp`：元のTw(F)の底変換自身が、
  同じ始点固定後合成の持ち上げと一致する。

対象ビルド `/tmp/is-w1/e01-source-pullback-3.log` 成功（5,434 jobs）。
小監査 `/tmp/is-w1/e01-pasting-type-1.log`：4宣言すべて標準三公理のみ。
この4宣言でE01そのものやR2cの同値性が出たとは扱わない。
既検証7,023行に100行を加え、3b-3の検証済みは88本・7,123行。
既存の宣言・入口・監査登録は変更していない。新しい公理・引用・sorryはない。

### 46.2 残る分類後の照合と、数え方による停止

実引き戻しの同型だけでは、指定した分類後の単位の一致はまだ出ない。
必要なのは、**既存の指定底変換同型自身の合成則**。
`leftClassificationHom_baseChange` は固定した底写像kに対して全空間射を動かす自然性で、
下の「二つの底写像k・lの合成」の式ではない。
`leftClassificationSquareHom_naturality` も底写像を固定するため、これだけでは代用できない。
`BaseChangeAssociativity*` の既存のcocartesian版は通常の圏のnerve等の別の模型であり、
一般の準圏K・Cと、この同じleft分類の指定同型を結ぶ宣言は確認できなかった。

必要な型は次。Uは `SSet.uliftFunctor.{u + 1, u}`。
引き戻しのsndがleft fibrationになる既存のinstanceを入れる。
HEqは底写像の合成の厳密な等式による端点の違いだけを除き、指定射自身を比較する。

```lean
lemma leftStraightening_baseChange_pasting
    {E B D H : SSet.{u}}
    [Quasicategory B] [Quasicategory D] [Quasicategory H]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : H ⟶ D) :
  HEq (precomposeFunctorHom (U.map l)
        (leftStraighteningInfinityDiagram_baseChangeIso p k).hom ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l).hom ≫
      leftClassificationHom (pullback.snd (pullback.snd p k) l)
        (pullback.snd p (l ≫ k)) (pullbackLeftPullbackSndIso p k l).hom
        (pullbackLeftPullbackSndIso_hom_snd p k l))
    (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)).hom
```

この命題の**型だけ**を `/tmp/is-w1/e01-pasting-type.lean` で確認した。
命題を仮定した完成版や証明は本体に追加していない。
実際に使うのはpがtwisted arrow射影で、k・lが両変数のFと始点固定包含の場合。
その特殊化でも指定同型の合成との両立を新たに示す必要がある。

`leftStraighteningInfinityDiagram_baseChangeIso` は単なる引き戻しの射影ではなく、
共同切断の比較を局所化の充満忠実性で降下した指定同型である。
したがって、上の式を実引き戻し同型の定義等式として済ませることはできない。
証明案は、初頂点局所化への制限で等式を検出し、共同切断の二回の底変換と
同じ貼り合わせ同型を照合してから降下すること。追加の見込みは250〜450行。
E01の既承認の見込み全体に必ず上乗せするという意味ではない。

これは§45のL1（単位の正方形表示）・L2（curryの評価）・L3（実引き戻しの係数移送）
とは別の、既存の指定分類に関する合成則で、**E01の前提計算の4本目**になる。
型を隠してE01の証明分割と呼んだり、別の比較同型を選んで元の指定単位との照合を省いたりしない。
IS-W2 §14の「前提計算の枠は一覧の補題ごとに3本」に従い、
この追加則の証明には入らず、検証済みを保存して報告する。
**停止点5aには未到達。R2は未完。R3・R4には着手していない。**

### 46.3 未検証の作業木

`HomWeightYonedaUnitSquare.lean` 93行は作業木に残し、コミット対象にしない。
§45のL1・L2について一般のHom作用を介する証明分割を試したが、
`/tmp/is-w1/e01-local-pair-2.log` で両方ともkernelのdeterministic timeout。
既定の計算上限を上げていない。上の追加則とは別に、この簡約の局所化も残っている。

数えない証明分割として試した型も記録する（いずれもこの未検証ファイル内）。

```lean
private lemma precomposeFunctorHom_eq_map {A B X : SSet.{u}}
    (k : B ⟶ A) {f g : A ⟶ X} (α : FunctorHom f g) :
  precomposeFunctorHom k α = (hoFunctor.map ((pre k).app X)).toFunctor.map α

private lemma curryEvaluation_of_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} {f' g' : B ⟶ (ihom A).obj X}
    (α : FunctorHom f' g') (β : FunctorHom f g)
    (hf : f' = curry f) (hg : g' = curry g) (h : HEq α (curryFunctorHom β))
    (a : A _⦋0⦌) :
  HEq ((hoFunctor.map ((ihom B).map (evaluateFunctorAt (Y := X) a))).toFunctor.map α)
    (precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) β)

private lemma unitSquare_raw (F : A ⟶ C) :
  leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
      (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
      (functorHomBifunctorDiagram_classificationIso F F).inv =
    leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
      (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
      (twistedArrowProjection_naturality F)
```

今回の増加は検証済み100行、未検証93行。
行数の外枠20,800を超えたための停止ではなく、追加の前提計算の型を示す地点での停止である。

### 46.4 保存と最終検証

- Leanのコミット：`913bd8036`（新規100行、4宣言）。
- docstring整備後の最終検証：`/tmp/is-w1/e01-final-local-1.log`。
  対象ビルド5,434 jobs成功、同じ4宣言の小監査は標準三公理のみ。
  追加則の型も同じログで確認済み（証明ではない）。
- 未検証の `HomWeightYonedaUnitSquare.lean` は作業木に保持。
  mainへの取り込み、大きい監査、入口・監査への登録は行っていない。


## 47. 指定底変換の合成則の再開（11-14、途中）

§46.2の型のままの合成則の追加承認と、法則・証明分割の数の制限撤廃を確認。
新しい構成・独立の定理・まとまり外・外枠20,800行で止まる条件を維持する。
停止点5aは引き続き元の実評価の充満忠実性まで。R3・R4は保留。

既存の `relativeSectionBaseChangeRealizationIso_comp` と
`straighteningBaseChangeIso_firstVertex` を再利用する。前者は共同切断の
**同じ指定実現同型**の合成則で、分類後の式そのものではない。
まず転置と第一変数制限を同じ端点で比較し、次にその既存合成則を転置した。
この2本（60行＋70行）は対象ビルド成功。
単体圏への再添字付けのファイルは未検証で、端点移送の簡約を局所化している。
計算上限を上げず、既存の宣言も変更していない。

以下は合成則の法則・証明分割の型。新しい構成や別の比較射への変更ではない。
各ファイルのopenとuniverseの下で読む。単体圏のファイルの補助的な異種等式は後掲。

### TransposeFunctorIsoRestriction

```lean
lemma transposeFunctorHom_precomp {A B I X : SSet.{u}} (q : B ⟶ A)
    {F G : A ⟶ (ihom I).obj X} (α : FunctorHom F G) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
        (transposeFunctorFamily_comp q F) (transposeFunctorFamily_comp q G)
        (transposeFunctorHom (precomposeFunctorHom q α)) =
      postcomposeFunctorHom ((pre q).app X) (transposeFunctorHom α)

lemma functorIsoTranspose_precomp {A B I X : SSet.{u}} (q : B ⟶ A)
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) :
    diagramIsoCongr (transposeFunctorFamily_comp q F) (transposeFunctorFamily_comp q G)
        (e.precomp q).transpose = e.transpose.postcomp ((pre q).app X)

```

### SectionDiagramBaseChangePasting

```lean
def sectionDiagramBaseChangeCompIso {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    FunctorIso
      (relativeSectionDiagramInfinity A ≫
        (pre (leftFibrationInfinityBaseChange (l ≫ k))).app SpaceInfinity.{u})
      ((relativeSectionDiagramInfinity A ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})

lemma relativeSectionDiagramInfinityBaseChangeIso_comp {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    sectionDiagramBaseChangeCompIso k l A ≪≫
      (relativeSectionDiagramInfinityBaseChangeIso l A).postcomp
        ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) ≪≫
      relativeSectionDiagramInfinityBaseChangeIso k (A ⋙ Over.map l) =
        relativeSectionDiagramInfinityBaseChangeIso (l ≫ k) A

```

### SimplexSectionBaseChangePasting

```lean
lemma simplexSectionBaseChange_target {B D : SSet.{u}} (k : D ⟶ B) :
    relativeSectionDiagramInfinity (transportSimplexDomainFunctor D ⋙ Over.map k) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B

lemma simplexSectionBaseChange_normalized {B D : SSet.{u}} (k : D ⟶ B) :
    transportSimplexSectionInfinity_baseChangeIso k =
      diagramIsoCongr rfl (simplexSectionBaseChange_target k)
        (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D))

lemma simplexSectionBaseChange_reindexed {B D T : SSet.{u}}
    (k : D ⟶ B) (l : T ⟶ D) :
    relativeSectionDiagramInfinityBaseChangeIso k
        (transportSimplexDomainFunctor T ⋙ Over.map l) =
      diagramIsoCongr
        (by rw [← Category.assoc, ← simplexSectionBaseChange_target l])
        (by rw [← simplexSectionBaseChange_target k, relativeSectionDiagramInfinity_reindex,
          ← Functor.assoc, transportSimplexDomainFunctor_baseChange])
        ((transportSimplexSectionInfinity_baseChangeIso k).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))))

```

### 47.1 検証済みの途中点（停止せず続行）

`acf003460`：5本・529行、公開18宣言。
対象ビルドと小監査は `/tmp/is-w1/section-pasting-audit-1.log`：成功、標準三公理のみ。
3b-3の検証済みは93本・7,652行。未検証の単位評価93行はコミットしていない。

| 法則・証明分割 | 実測行数 | 状態 |
| --- | ---: | --- |
| 転置と第一変数制限 | 63 | 検証済み |
| 転置後の共同切断の指定合成 | 73 | 検証済み |
| 単体圏の指定再添字付け | 108 | 検証済み |
| 全単体上の指定三因子の合成 | 159 | 検証済み |
| 分類Homの全単体切断への制限 | 126 | 検証済み |
| **合成則の証明分割の小計** | **529** | **一般の底への降下はまだ** |

単一の宣言は200行以下だが、§46.2の法則の証明分割全体では200行を超えたため、
全ファイルの実測も記す。前の追加250〜450行の見込みは超えた。
残る降下・実貼り合わせ射の係数作用の照合を400〜700行と見て、
合成則全体を約929〜1,229行へ見直す。
R2の残りはE01の未完部分1,000〜1,700、E02〜E06 1,150〜1,950、
RR01〜RR05 3,100〜4,950、R2d・R2e 500〜700、合計5,750〜9,300行。
検証済みと合わせ13,402〜16,952行で、外枠20,800行の内側。
追加の法則のための承認待ちにはせず、このまま進める。

残る数学的な照合は、全単体上で現れた標準貼り合わせ比較を、
元の引き戻し同型の `leftClassificationHom` と同じ射として回収することと、
初頂点局所化の忠実性で§46.2の**元の型**の式を降下すること。
`transportSimplexSectionInfinity_baseChange_pasting` 自体はその最終式ではない。

新しく保存した型（前掲の型と合わせて読む）：

#### SimplexSectionComposite

```lean
lemma simplexSection_def (T : SSet.{u}) :
    transportSimplexSectionInfinity T = relativeSectionDiagramInfinity
      (transportSimplexDomainFunctor T)

def simplexSectionCompIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      (transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange (l ≫ k))).app SpaceInfinity.{u})
      ((transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})

def simplexSectionFirstIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      ((transportSimplexSectionInfinity T ≫
        (pre (leftFibrationInfinityBaseChange l)).app SpaceInfinity.{u}) ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        (transportSimplexSectionInfinity D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))

def simplexSectionSecondIso {B D T : SSet.{u}} (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        (transportSimplexSectionInfinity D ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
          transportSimplexSectionInfinity B))

lemma transportSimplexSectionInfinity_baseChange_pasting {B D T : SSet.{u}}
    (k : D ⟶ B) (l : T ⟶ D) :
    HEq (simplexSectionCompIso k l ≪≫ simplexSectionFirstIso k l ≪≫
      simplexSectionSecondIso k l)
      (transportSimplexSectionInfinity_baseChangeIso (l ≫ k))

```

#### LeftClassificationSimplexRestriction

```lean
def leftStraighteningSimplexRestrictionIso (B : SSet.{u}) :
    FunctorIso
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization

lemma leftClassificationSimplex_sourceEq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
      leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u}).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p)

lemma leftClassificationSimplex_targetEq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    functorVertex (kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
        (leftFibrationObjectOf p))) =
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization.app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p)

def leftClassificationSimplexIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p)
      (kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p)))

lemma leftClassificationSimplex_component {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] :
    normalizedFunctorIsoComponent (leftStraighteningSimplexRestrictionIso B)
      (leftFibrationInfinityVertex p) (leftClassificationSimplex_sourceEq p)
      (leftClassificationSimplex_targetEq p) = leftClassificationSimplexIso p

lemma leftClassificationHom_simplexRestriction
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) :
    precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))
        (leftClassificationHom p q f hf) ≫ (leftClassificationSimplexIso q).hom =
      (leftClassificationSimplexIso p).hom ≫
        normalizedVertexHomMap
          (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization
          (leftClassificationSimplex_targetEq p) (leftClassificationSimplex_targetEq q)
          (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)

```

#### 型移送の私的な証明分割

同型の合成は `Iso.trans_assoc` で明示的に移す。異なる結合括弧を定義等式として
照合させない。二重の型移送も次の一般補題として一度だけ検証してから適用した。
いずれも既存の等式消去・制限・合成の法則であり、新しい数学的な入力ではない。

```lean
private lemma two_mpr_heq {α β γ : Sort (u + 2)}
    (h₁ : α = β) (h₂ : β = γ) (x : γ) :
  HEq (Eq.mpr h₁ (Eq.mpr h₂ x)) x

private lemma sectionBaseChangeIso_coeff_heq {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) {A A' : Jᵒᵖ ⥤ Over D}
    (h : A = A') : HEq (relativeSectionDiagramInfinityBaseChangeIso k A)
      (relativeSectionDiagramInfinityBaseChangeIso k A')

private lemma isoPrecomp_heq {W X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') (q : W ⟶ X) : HEq (e.precomp q) (e'.precomp q)

private lemma isoTrans_heq {A X : SSet.{u}} {f g h f' g' h' : A ⟶ X}
    (e : FunctorIso f g) (e' : FunctorIso f' g')
    (d : FunctorIso g h) (d' : FunctorIso g' h')
    (hf : f = f') (hg : g = g') (hh : h = h')
    (he : HEq e e') (hd : HEq d d') : HEq (e ≪≫ d) (e' ≪≫ d')

private lemma simplexSectionBaseChange_heq {B D : SSet.{u}} (k : D ⟶ B) :
  HEq (transportSimplexSectionInfinity_baseChangeIso k)
    (relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D))
```


## 48. /goalの再開と係数作用の照合（11-14、途中）

mainの `lane-goals-2026-11-14.md` の「共通の規則」「③-a」を読んだ。
B4の連絡が来れば先にする。ビルドは `--class impl --wait 3600`、対象と小監査だけ。
停止点5aまで続行し、R3・R4は実装しない。

一覧：済み 0／全体 13（うち追加 11）

数え方：今回のgoal対象は§44のE01〜E06（6）、RR01〜RR05（5）、R2d・R2e（2）。
E・RRの11項目が§40からの追加分。既に完了したR2a・R2bや、構成の法則・証明分割は
この13項目には重ねて数えない。§47の529行もE01の証明分割で、E01の完成とはしない。

残る貼り合わせ射の照合のため、次の既存構成の法則を追加している。
`KanEnrichedDiagramOrdinaryAction` の一般の実現の射作用の法則は対象ビルド成功
（`/tmp/is-w1/kan-comparison-action-pair-2.log`）。
表示の一致hを仮定したR2の完成版にはしない。実際の底上の射の場合の表示の一致を
`RelativeSectionOrdinaryAction` で証明し、同じ自然変換を使う。
係数対象への共同比較の辺の制限は、指定辺の円柱全体の式として照合中。
型を以下に記す。未検証のものは本体の完成として数えない。

### KanEnrichedDiagramOrdinaryAction

```lean
lemma KanEnrichedDiagram.realization_homMk_of_homEquiv
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    {X Y : C} (f : X ⟶ Y)
    (η : D.evaluate X ⋙ kanObjectForget ⟶ D.evaluate Y ⋙ kanObjectForget)
    (h : eHomEquiv SSet.{u} f ≫ D.toEnrichedFunctor.map X Y =
      eHomEquiv SSet.{u} (kanDiagramHom (F := ⟨D.evaluate X, trivial⟩)
        (G := ⟨D.evaluate Y, trivial⟩) η)) :
    normalizedVertexHomMap D.realization (D.realization_vertex X).symm
        (D.realization_vertex Y).symm
        (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) =
      Truncated.HomotopyCategory.homMk
        (kanDiagramNaturalTransformationEdge
          (F := ⟨D.evaluate X, trivial⟩) (G := ⟨D.evaluate Y, trivial⟩) η).toTruncated
```

### KanEnrichedComparisonEvaluation

```lean
private lemma coefficient_diagonal_constant
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    (X : C) {n : ℕ} (σ : (nerve J) _⦋n⦌) :
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ)
      ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n).comp SSet D.toEnrichedFunctor) =
      enrichedFunctorOfOrderDiagram (kanDiagramSimplexBase σ ⋙ D.evaluate X)

private lemma enriched_map_app_heq {I : Type u} [LinearOrder I]
    {F G : EnrichedFunctor SSet.{u} (SimplicialThickening I) KanObject.{u}}
    (h : F = G) (i j : SimplicialThickening I) (d : SimplexCategoryᵒᵖ)
    (P : (SimplicialCategory.sHom i j).obj d) :
    HEq ((F.map i j).app d P) ((G.map i j).app d P)

private lemma post_constant {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (d : SimplexCategoryᵒᵖ) :
    ((ihom A).map g).app d
      (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex f) d.unop.len) =
      Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex (f ≫ g)) d.unop.len

private lemma prism_transpose {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X) :
    functorFamilyPrism (transposeFunctorFamily F) = uncurry F

lemma KanEnrichedDiagramComparison.jointComparisonEdge_restrict
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (X : C) :
    ((pre (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
      (SSet.const (coherentNerveVertex X)))).app SpaceInfinity.{u}).app (Opposite.op ⦋1⦌)
        η.jointComparisonEdge.edge =
      (kanDiagramNaturalTransformationEdge
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)).edge
```

### RelativeSectionOrdinaryAction

```lean
def relativeSectionPostTransformation
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p) ⋙ kanObjectForget ⟶
      (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q) ⋙ kanObjectForget

lemma relativeSectionPostTransformation_eHom
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    eHomEquiv SSet.{u} (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from
        Over.homMk (U := Over.mk p) (V := Over.mk q) f hf) ≫
      (relativeSectionEnrichedDiagram A).toEnrichedFunctor.map
        (leftFibrationObjectOf p) (leftFibrationObjectOf q) =
      eHomEquiv SSet.{u} (kanDiagramHom
        (F := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p), trivial⟩)
        (G := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q), trivial⟩)
        (relativeSectionPostTransformation p q f hf A))

lemma relativeSectionRealization_homMk
    {E H B : SSet.{u}} (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) :
    normalizedVertexHomMap (relativeSectionEnrichedDiagram A).realization
      ((relativeSectionEnrichedDiagram A).realization_vertex (leftFibrationObjectOf p)).symm
      ((relativeSectionEnrichedDiagram A).realization_vertex (leftFibrationObjectOf q)).symm
      (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf p), trivial⟩)
        (G := ⟨(relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf q), trivial⟩)
        (relativeSectionPostTransformation p q f hf A)).toTruncated
```

三本とも同じ共同実現・相対後合成の法則。独立の数学的な入力ではない。
`RelativeSectionOrdinaryAction` の対象ビルドも成功
（`/tmp/is-w1/coefficient-section-action-pair-5.log`）。
`KanEnrichedComparisonEvaluation` は射の作用の計算中で、未検証。
私的な `prism_transpose` は `functorFamilyPrism (transposeFunctorFamily F) = uncurry F`。
三本とも現時点で200行未満。

検証追記：二本（`KanEnrichedDiagramOrdinaryAction` 60行、
`RelativeSectionOrdinaryAction` 110行）の対象ビルドと四宣言の小監査が通った。
監査は標準三公理のみ（`/tmp/is-w1/coefficient-action-pair-8.log`）。
係数制限の一本は未検証のまま作業木に残す。E01の完成とは数えない。

### 48.1 係数制限の検証（続報）

`KanEnrichedComparisonEvaluation` の対象ビルドが通った
（`/tmp/is-w1/coefficient-section-action-pair-20.log`、5,472 jobs）。
主張は上記 `jointComparisonEdge_restrict` のまま。元の一単体の全パラメーターでの等式。
定値係数の対角評価・同じ豊穣関手の表示変更・内部Homの後合成の定値単体という、
既存の構成の法則で証明を分割した。計算上限は変更していない。
次は指定実現値同型の射の照合（`kanEnrichedRealizationValueIso_hom`）。

一覧：済み 0／全体 13（うち追加 11）

### 48.2 実現値同型の射と法則の型

`kanEnrichedRealizationValueIso_hom` の対象ビルド成功
（`/tmp/is-w1/coefficient-value-1.log`、2,865 jobs）。
係数制限の一本244行と実現値の一本64行、計308行を検証した。
3b-3の検証済み累計は97本・8,130行。いずれもE01への法則・証明分割である。
以下の各宣言は200行未満（ファイル全体の行数とは区別）。

一覧：済み 0／全体 13（うち追加 11）

追加の法則・証明分割の型（§48冒頭の係数制限の主張は同じ）：

#### KanEnrichedComparisonEvaluation

```lean
private lemma coefficient_diagonal_constant
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    (X : C) {n : ℕ} (σ : (nerve J) _⦋n⦌) :
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ)
      ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n).comp SSet D.toEnrichedFunctor) =
      enrichedFunctorOfOrderDiagram (kanDiagramSimplexBase σ ⋙ D.evaluate X)

private lemma enriched_map_app_heq {I : Type u} [LinearOrder I]
    {F G : EnrichedFunctor SSet.{u} (SimplicialThickening I) KanObject.{u}}
    (h : F = G) (i j : SimplicialThickening I) (d : SimplexCategoryᵒᵖ)
    (P : (SimplicialCategory.sHom i j).obj d) :
    HEq ((F.map i j).app d P) ((G.map i j).app d P)

private lemma post_constant {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (d : SimplexCategoryᵒᵖ) :
    ((ihom A).map g).app d
      (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex f) d.unop.len) =
      Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex (f ≫ g)) d.unop.len

private lemma prism_transpose {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X) :
    functorFamilyPrism (transposeFunctorFamily F) = uncurry F

lemma KanEnrichedDiagramComparison.jointComparisonEdge_restrict
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (X : C) :
    ((pre (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
      (SSet.const (coherentNerveVertex X)))).app SpaceInfinity.{u}).app (Opposite.op ⦋1⦌)
        η.jointComparisonEdge.edge =
      (kanDiagramNaturalTransformationEdge
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)).edge
```

#### KanEnrichedRealizationValueHom

```lean
lemma kanEnrichedRealizationValueIso_hom
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E)
    (hη : ∀ j (X : C), IsQCatEquivalence
      (X := ((D.obj j).obj X).obj) (Y := ((E.obj j).obj X).obj) ((η.component j).val X))
    (X : C) :
    (kanEnrichedRealizationValueIso η hη X).hom =
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)).toTruncated
```

#### SectionBaseChangeCompValueHom

```lean
lemma sectionBaseChangeCompComparison_value_hom {E B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    (kanEnrichedRealizationValueIso (sectionBaseChangeCompComparison k l A)
      (sectionBaseChangeCompComparison_isQCatEquivalence k l A) (leftFibrationObjectOf p)).hom =
      normalizedVertexHomMap (relativeSectionEnrichedDiagram A).realization
        ((relativeSectionEnrichedDiagram A).realization_vertex
          (leftFibrationObjectOf (pullback.snd p (l ≫ k)))).symm
        ((relativeSectionEnrichedDiagram A).realization_vertex
          (leftFibrationObjectOf (pullback.snd (pullback.snd p k) l))).symm
        (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge
          (pullback.snd p (l ≫ k)) (pullback.snd (pullback.snd p k) l)
          (pullbackLeftPullbackSndIso p k l).inv
          (pullbackLeftPullbackSndIso_inv_snd_snd p k l)).toTruncated)
```

最後の `SectionBaseChangeCompValueHom` は対象ビルド待ち。新しい数学的入力ではなく、
元の反復引き戻し比較の成分と相対後合成の同じ射を照合する適用の法則。

検証追記：三本の対象ビルドと三宣言の小監査が成功
（`/tmp/is-w1/coefficient-value-3.log`、5,483 jobs、標準三公理のみ）。
`SectionBaseChangeCompValueHom` は53行。検証済み累計は98本・8,183行。
実現値の比較は標準引き戻し同型の逆射そのものへ接続できた。
E01の残りは、この同じ値の法則を指定分類の初頂点制限へ渡し、
承認済みの `leftStraightening_baseChange_pasting` を降下させる部分。

一覧：済み 0／全体 13（うち追加 11）

## 49. 指定比較の分類像と初頂点制限（11-14、途中）

一覧：済み 0／全体 13（うち追加 11）

三本の対象ビルドと四宣言の小監査が成功
（`/tmp/is-w1/classified-restriction-3.log`、5,489 jobs、標準三公理のみ）。
元の比較の値、同じ標準全空間射の分類Hom、指定底変換の初頂点制限を照合した。
これらは既存の構成の法則で、E01の完成には数えない。
型の展開が大きい箇所は合成の型とletを局所的に明示した。計算上限は変えていない。

実測：`SectionBaseChangeCompValueNormalization` 59行、`SectionBaseChangeCompClassifiedHom` 70行、`LeftStraighteningBaseChangeRestrictionNormalization` 74行。
計203行、3b-3の検証済み累計は101本・8,386行。
各宣言は200行未満。

### SectionBaseChangeCompValueNormalization

```lean
lemma sectionBaseChangeCompRealizationIso_value_heq {E B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    HEq (functorIsoValue (sectionBaseChangeCompRealizationIso k l A)
        (leftFibrationInfinityVertex p))
      (kanEnrichedRealizationValueIso (sectionBaseChangeCompComparison k l A)
        (sectionBaseChangeCompComparison_isQCatEquivalence k l A) (leftFibrationObjectOf p))
```

### SectionBaseChangeCompClassifiedHom

```lean
lemma sectionBaseChangeCompComparison_classified_hom {E B D T : SSet.{u}}
    [Quasicategory T] (p : E ⟶ B) [LeftFibration p]
    (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    (show FunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₀)
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₁) from
      precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T))
        (leftClassificationHom q₀ q₁ (pullbackLeftPullbackSndIso p k l).inv
          (pullbackLeftPullbackSndIso_inv_snd_snd p k l))) ≫
      (leftClassificationSimplexIso q₁).hom =
      (show FunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T) ≫
          leftStraighteningInfinityDiagram q₀)
        (kanDiagramCoherentNerve
          ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
            (leftFibrationObjectOf q₀))) from (leftClassificationSimplexIso q₀).hom) ≫
        (kanEnrichedRealizationValueIso
          (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
          (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
          (leftFibrationObjectOf p)).hom
```

### LeftStraighteningBaseChangeRestrictionNormalization

```lean
private lemma two_mp_heq {α β γ : Sort v} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    HEq (Eq.mp h₂ (Eq.mp h₁ x)) x

lemma leftStraighteningInfinityMap_baseChangeIso_heq_transpose {B D : SSet.{u}} (k : D ⟶ B) :
    HEq (leftStraighteningInfinityMap_baseChangeIso k)
      (leftStraighteningSectionJointDiagram_baseChangeIso k).transpose

lemma leftStraighteningInfinityMap_baseChangeIso_firstVertex_heq {B D : SSet.{u}}
    (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityMap_baseChangeIso k).postcomp
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map
        (transportSimplexFirstVertexMap D))).app SpaceInfinity.{u}))
      (straighteningBaseChangeRestrictionIso k).transpose
```

残りの接続：指定底変換の正規化した成分を内部Homで制限し、
上の全対象の初頂点制限へ移す（既存の成分の後合成の法則を再利用）。
その後、元の切断底変換の三因子の合成則で中間の制限同型を消去し、
`leftStraightening_baseChange_pasting` を初頂点局所化から反映する。
`NormalizedFunctorIsoComponentRestriction` の二法則を対象ビルド中。

### 49.1 指定対象成分と転置の係数評価

一覧：済み 0／全体 13（うち追加 11）

四本の対象ビルドと五宣言の小監査が成功
（`/tmp/is-w1/restriction-value-audit-2.log`、5,473 jobs、標準三公理のみ）。
既存の成分の後合成の法則 `functorIso_app_postcomp_heq`、
既存の同型の後合成の厳密な式 `functorIso_postcomp_eq_mapIso` を再利用した。
転置した指定比較の値は、転置前の同じ比較の評価後合成として計算できる。
以下はすべて既存構成の法則。各宣言は200行未満。

実測：`NormalizedFunctorIsoComponentRestriction` 60行、`LeftClassificationBaseChangeRestrictionValue` 70行、`InternalHomSwapEvaluationRight` 34行、`FunctorIsoTransposeValue` 44行。
計208行。検証済み累計は105本・8,594行。

#### NormalizedFunctorIsoComponentRestriction

```lean
lemma normalizedFunctorIsoComponent_heq_app {I Y : SSet.{u}}
    [Quasicategory I] [Quasicategory Y] {F G : I ⟶ Y}
    (e : FunctorIso F G) (x : I _⦋0⦌) {xf xg : Y _⦋0⦌}
    (hf : xf = F.app (Opposite.op ⦋0⦌) x) (hg : xg = G.app (Opposite.op ⦋0⦌) x) :
    HEq (normalizedFunctorIsoComponent e x hf hg) (e.app x)

lemma normalizedFunctorIsoComponent_precomp_heq {I A B X : SSet.{u}}
    [Quasicategory I] [Quasicategory X] {F G : I ⟶ (ihom A).obj X}
    (e : FunctorIso F G) (x : I _⦋0⦌) {f g : A ⟶ X}
    (hf : functorVertex f = F.app (Opposite.op ⦋0⦌) x)
    (hg : functorVertex g = G.app (Opposite.op ⦋0⦌) x) (q : B ⟶ A) :
    HEq ((show FunctorIso f g from normalizedFunctorIsoComponent e x hf hg).precomp q)
      ((e.postcomp ((pre q).app X)).app x)
```

#### LeftClassificationBaseChangeRestrictionValue

```lean
lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_heq
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))
      (functorIsoValue (straighteningBaseChangeRestrictionIso k).transpose
        (leftFibrationInfinityVertex p))
```

#### InternalHomSwapEvaluationRight

```lean
lemma internalHomSwapIso_evaluate_right (A B X : SSet.{u}) (b : B _⦋0⦌) :
    (internalHomSwapIso A B X).hom ≫ evaluateFunctorAt (Y := (ihom A).obj X) b =
      (ihom A).map (evaluateFunctorAt (Y := X) b)
```

#### FunctorIsoTransposeValue

```lean
lemma functorIsoValue_transpose_heq_postcomp {A I X : SSet.{u}}
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) (i : I _⦋0⦌) :
    HEq (functorIsoValue e.transpose i) (e.postcomp (evaluateFunctorAt (Y := X) i))
```

同じ方法で初頂点制限同型の対象成分を共同制限の評価へ戻す
`LeftClassificationSimplexRestrictionValue` を対象ビルド中。

## 50. B4（11-14、完了）

一覧：済み 0／全体 13（うち追加 11）

- 検証済みは `55c353b99` までコミットしてから採取した。
- 基準 `c5c4436c0` と自枝の三点差分・コミット履歴で対象29本を確定。
  二点差分に出る入口・監査の逆向き差分は自枝の変更に含めない。
  一覧は `inf-supply-b4/files.json`。
- 未検証下書き二本は原文とハッシュを保管し、作業木に残した。
  通常import表の移動に当たるimportは二本ともない。数学の再検証は未了。
- main取り込み前に、四本・四本・七本・七本・七本の五組で全29本を採取。
  各組 `--class impl --wait 3600`、実処理の上限280秒。整理券は常に一枚。
- 全原文・採取ソースのバイト一致と採取器の同一性を検査し、rewriteの保留0を確認。
  差分は六本の通常importのみ（+6/-6行）。各移動先はmodule表と一致。
  自枝の新しいモジュール自身の配置変更なし。プレビューによる宣言名の書換えなし。
- main `efa846fe8` を競合なく取り込んだ（merge `fe4722fb9`）。
  取り込みで自枝の原文が変わっていないことを検査後、事前プレビューの差分を適用。
  全29本がプレビューと完全一致。取り込み後のソースへ旧参照索引を流用していない。
- 対象29本のビルドと小監査を実行中。監査はビルド後の新しい環境から対象の定義元を
  取り直し、各宣言ごとに標準三公理のみを確認する（計算上限は変更しない）。

採取・プレビュー・検証ログ：`/tmp/is-w1/b4-20261114-55c353b99/`。
要約と保留表は `inf-supply-b4/` に保存した。
B4終了後は§49のE01の接続へ戻る。R2完成まで、R3・R4は実装しない。

### 50.1 結合importでの局所インスタンスの名前衝突

一覧：済み 0／全体 13（うち追加 11）

最初の対象29本のビルドは成功（11,483 jobs）。一括importによる小監査の開始時に、
`StrictDiagramEvaluationFrames` と `StrictDiagramFunctorialFrames` の
名前なし局所インスタンスが同じkernel名を持つ衝突を検出した。
自枝の未取り込み九本の34個にファイル固有の名前を明示した。
型・右辺・`local` の可視性は不変で、挿入した名前を取り除くと全29本が事前プレビューに
バイト単位で完全一致することを検査した。新しい数学的入力は追加していない。
この命名は旧索引による書換えではなく、取り込み後の結合検査に基づく修正。
詳細は `inf-supply-b4/local-instance-names.json`。

最終差分（検証中）は13本・+40/-40行（通常import六行と局所名34行）。
`integration-summary.json` に最終ソースのハッシュと不変性検査の結果を保存した。
再ビルドと新しい環境での公理監査を実行中。

### 50.2 B4完了

一覧：済み 0／全体 13（うち追加 11）

- 最終29本の対象ビルド成功（11,483 jobs、`target-and-audit-2.log`）。
- 新しい環境から定義元を採取し直し、29モジュール・208宣言の小監査成功。
  標準三公理のみ。計算上限は変更していない（`catalog-after.log`、`audit-after.log`）。
- 最終差分は13本・+40/-40行（import六行、名前なしlocal instanceの命名34行）。
  型・右辺・local指定のソースは不変。未検証下書き二本も原文のまま保管・保持した。
- `inf-supply-b4/target-audit-result.json` に結果を保存した。

B4は完了。続けて§49のE01の接続へ戻り、R2の評価の充満忠実性（停止点5a）まで進める。

## 51. B4後のE01の接続（11-14、検証中）

一覧：済み 0／全体 13（うち追加 11）

§49の続き。未検証だった初頂点制限の端点移送は、一般の `e ≪≫ eqToIso h` の
異種等式の法則へ局所化し、大きい具体的同型にsimpを走らせない形へ直している。
指定底変換を元の共同制限・元の切断比較の逆・元の共同制限の逆という三因子へ戻す
計算も、同じ端点移送と後合成の法則だけで書いた。新しい数学的入力は追加しない。
どちらも対象ビルド中。各宣言は200行未満。計算上限は変更していない。

型（既存構成の法則と証明分割、IDのある新項目には数えない）：

### LeftClassificationSimplexRestrictionValue

```lean
private lemma mp_heq {α β : Sort v} (h : α = β) (x : α) : HEq (Eq.mp h x) x

private lemma iso_trans_eqToIso_heq {L : Type v} [Category.{w} L]
    {a b c : L} (e : a ≅ b) (h : b = c) : HEq (e ≪≫ eqToIso h) e

lemma leftStraighteningSimplexRestrictionIso_heq_transpose (B : SSet.{u}) :
    HEq (leftStraighteningSimplexRestrictionIso B)
      (leftStraighteningSectionJointDiagram_restrictIso B).transpose

lemma leftClassificationSimplexIso_heq_joint_postcomp {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    HEq (leftClassificationSimplexIso p)
      ((leftStraighteningSectionJointDiagram_restrictIso B).postcomp
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
```

### LeftClassificationBaseChangeRestrictionFactorization

```lean
private lemma eqIso_trans_postcomp_heq {A X Y : SSet.{u}}
    {F F' G : A ⟶ X} (h : F = F') (e : FunctorIso F' G) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (f := F) (g := G)
      (eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h) ≪≫ e) q)
      (FunctorIso.postcomp e q)

lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_factors
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        (U.map (transportSimplexFirstVertexMap D)))
      (FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t) evp ≪≫
        FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp ≪≫
          FunctorIso.postcomp ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
            evp)
```

### 51.1 係数評価と検証済みの区切り

一覧：済み 0／全体 13（うち追加 11）

三本の対象ビルド成功（5,477 jobs）。新しい環境の小監査は8宣言、標準三公理のみ。
計算上限は変更していない。E01本体は未完了。
ログ：`/tmp/is-w1/joint-evaluation-verify/`。

- `LeftClassificationSimplexRestrictionValue`：89行。
- `LeftClassificationBaseChangeRestrictionFactorization`：83行。
- `LeftClassificationJointEvaluation`：63行。

既存構成の法則の型（各宣言200行未満）：

```lean
lemma leftStraighteningInfinityDiagram_joint_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    leftStraighteningSectionJointDiagram B ≫
      evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      leftStraighteningInfinityDiagram p

lemma transportSimplexSectionInfinity_joint_evaluate {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    transportSimplexSectionInfinity B ≫
      evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p))

```

### 51.2 三因子の第一・第三因子の正規化

一覧：済み 0／全体 13（うち追加 11）

二本の対象ビルド成功（5,470 jobs）。新しい環境の小監査は6宣言、標準三公理のみ。
計算上限は不変。ログ：`/tmp/is-w1/restriction-factor-verify/`。
既存構成の係数移送と逆・前後合成の法則のみで、新しい数学的入力はない。
E01は未完了で、次は指定底変換の同じ三因子全体の共役表示と貼り合わせへ進む。

#### LeftClassificationRestrictionFactorValues（59行）

```lean
lemma leftClassificationSimplexIso_precomp_heq_joint
    {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {K : SSet.{u + 1}}
    (t : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B))) :
    HEq (FunctorIso.postcomp
        ((leftStraighteningSectionJointDiagram_restrictIso B).precomp t)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (FunctorIso.precomp (leftClassificationSimplexIso p) t)

```

#### LeftClassificationRestrictionPullbackValue（113行）

```lean
local instance restrictionPullbackValue_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma leftFibrationBaseChange_evaluate {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u} ≫
        evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p) =
      evaluateFunctorAt (Y := SpaceInfinity.{u})
        (leftFibrationInfinityVertex (pullback.snd p k))

lemma leftClassificationSimplexIso_pullback_heq_joint
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (FunctorIso.postcomp
        (FunctorIso.postcomp (leftStraighteningSectionJointDiagram_restrictIso D)
          ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}))
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (leftClassificationSimplexIso (pullback.snd p k))

private lemma isoSymm_heq {L : Type v} [Category.{w} L]
    {a b a' b' : L} (e : a ≅ b) (e' : a' ≅ b')
    (ha : a = a') (hb : b = b') (h : HEq e e') : HEq e.symm e'.symm

lemma leftClassificationSimplexIso_pullback_symm_heq_joint
    {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (FunctorIso.postcomp
        (FunctorIso.postcomp (leftStraighteningSectionJointDiagram_restrictIso D)
          ((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})).symm
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (leftClassificationSimplexIso (pullback.snd p k)).symm

```

検証済み累計：110本・9,001行（直前105本・8,594行に、§51.1の235行と今回172行を追加）。
全宣言200行未満。外枠20,800行の内側。

### 51.3 貼り合わせへの残りの法則（検証中）

一覧：済み 0／全体 13（うち追加 11）

共役表示は対象ビルド成功。転置後の係数評価は、最初に二変数交換の向きを誤っていたため、
一般の第一変数評価の法則へ分けて修正中。既存ファイルは変更していない。
小監査は残りの対象ビルド後にまとめる。以下は既存構成の法則と証明分割のみ。
各宣言200行未満、計算上限は不変。新しい数学的入力・ID項目の追加なし。

#### FunctorIsoTransposeEvaluation（44行）

```lean
lemma functorIso_transpose_postcomp_heq_value {A I X : SSet.{u}}
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) (a : A _⦋0⦌) :
    HEq (FunctorIso.postcomp e.transpose (evaluateFunctorAt (Y := X) a))
      (functorIsoValue e a)

```

#### LeftClassificationBaseChangeConjugation（123行）

```lean
local instance baseChangeConjugation_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma isoTransThree_heq {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : L}
    (e₁ : a₀ ≅ a₁) (e₂ : a₁ ≅ a₂) (e₃ : a₂ ≅ a₃)
    (d₁ : b₀ ≅ b₁) (d₂ : b₁ ≅ b₂) (d₃ : b₂ ≅ b₃)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
    (he₁ : HEq e₁ d₁) (he₂ : HEq e₂ d₂) (he₃ : HEq e₃ d₃) :
    HEq (e₁ ≪≫ e₂ ≪≫ e₃) (d₁ ≪≫ d₂ ≪≫ d₃)

lemma leftStraighteningInfinityDiagram_baseChangeIso_firstVertex_conjugation
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        (U.map (transportSimplexFirstVertexMap D)))
      ((leftClassificationSimplexIso p).precomp t ≪≫
        diagramIsoCongr
          (by rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
          (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
            transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
          (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k).symm evp) ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm)

```

#### SimplexSectionCompValue（75行）

```lean
private lemma diagramIsoCongr_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g')
    (e : FunctorIso f g) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (diagramIsoCongr hf hg e) q) (FunctorIso.postcomp e q)

lemma simplexSectionCompIso_value_heq {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (FunctorIso.postcomp (simplexSectionCompIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (kanEnrichedRealizationValueIso
        (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
        (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
        (leftFibrationObjectOf p))

```

#### SimplexSectionBaseChangeValuePasting（67行）

```lean
lemma simplexSectionBaseChange_value_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    HEq (FunctorIso.postcomp (simplexSectionCompIso k l) evp ≪≫
        FunctorIso.postcomp (simplexSectionFirstIso k l) evp ≪≫
          FunctorIso.postcomp (simplexSectionSecondIso k l) evp)
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso (l ≫ k)) evp)

```

#### FunctorHomPrecompositionLaws（54行）

```lean
lemma precomposeFunctorHom_eq_map {A B X : SSet.{u}}
    (k : B ⟶ A) {f g : A ⟶ X} (α : FunctorHom f g) :
    precomposeFunctorHom k α =
      (hoFunctor.map ((pre k).app X)).toFunctor.map α

lemma precomposeFunctorHom_comp {A B X : SSet.{u}} (k : B ⟶ A)
    {f g h : A ⟶ X} (α : FunctorHom f g) (β : FunctorHom g h) :
    precomposeFunctorHom k (α ≫ β) =
      precomposeFunctorHom k α ≫ precomposeFunctorHom k β

lemma precomposeFunctorHom_injective {A B X : SSet.{u}} [Quasicategory X]
    (k : B ⟶ A)
    (hk : Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      ((pre k).app X))
    {f g : A ⟶ X} (α β : FunctorHom f g)
    (h : precomposeFunctorHom k α = precomposeFunctorHom k β) : α = β

```

#### HomClassificationIsoLaws（41行）

```lean
lemma leftClassificationHom_iso_hom_inv {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    leftClassificationHom p q e.hom he ≫ leftClassificationHom q p e.inv hi = 𝟙 _

lemma leftClassificationHom_iso_inv_hom {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    leftClassificationHom q p e.inv hi ≫ leftClassificationHom p q e.hom he = 𝟙 _

```


### 51.4 補正因子の端点と二因子の評価（検証中）

一覧：済み 0／全体 13（うち追加 11）

転置の第一変数評価・補正因子の係数値・前合成の法則・係数での貼り合わせ・分類した
同型と逆射の相殺はそれぞれ対象ビルドを通過。未検証だった単位の型の名前空間不足を直し、
残るkernelの簡約は既存の一般評価の二段の適用へ局所化中。上限は変更していない。
単位下書きは依然コミット対象外。

以下も既存構成の法則のみ。新しいID項目ではない。各宣言200行未満。

#### SimplexSectionCompNormalizedValue（62行）

```lean
local instance simplexCompNormalizedValue_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma simplexSectionCompIso_value_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    diagramIsoCongr
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
        transportSimplexSectionInfinity_joint_evaluate q₀])
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k,
        Category.assoc, leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate q₁])
      (FunctorIso.postcomp (simplexSectionCompIso k l) evp) =
    kanEnrichedRealizationValueIso
      (sectionBaseChangeCompComparison k l (transportSimplexDomainFunctor T))
      (sectionBaseChangeCompComparison_isQCatEquivalence k l (transportSimplexDomainFunctor T))
      (leftFibrationObjectOf p)

```

#### SimplexSectionBaseChangeFactorValues（82行）

```lean
local instance simplexFactorValues_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma diagramIsoCongr_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (hf : f = f') (hg : g = g')
    (e : FunctorIso f g) (q : X ⟶ Y) :
    HEq (FunctorIso.postcomp (diagramIsoCongr hf hg e) q) (FunctorIso.postcomp e q)

lemma simplexSectionFirstIso_value_heq {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (FunctorIso.postcomp (simplexSectionFirstIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (leftFibrationInfinityVertex (pullback.snd p k))))

lemma simplexSectionSecondIso_value {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso.postcomp (simplexSectionSecondIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)) =
      FunctorIso.precomp
        (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
          (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)))

```


### 51.5 貼り合わせの法則群の検証済み区切り

一覧：済み 0／全体 13（うち追加 11）

八本の対象ビルド成功（5,513 jobs）。新しい環境から採った24宣言の小監査成功、
標準三公理のみ。計算上限の変更なし。
ログ：`/tmp/is-w1/pasting-law-verify/run-2.log`、`catalog-after.log`、`audit-after.log`。

検証済み累計118本・9,549行（110本9,001行に八本548行を追加）。
指定底変換の初頂点制限の共役表示、同じ全単体補正因子の係数値、
二段の係数貼り合わせ、前合成の忠実性、分類した同型と逆射の相殺が通った。
これらは既存構成の法則で、E01そのものの完成には数えない。

次はこの同じ係数貼り合わせと分類像から、§46.2の指定底変換の合成式を初頂点制限で照合し、
忠実性で降下する。元の型は維持し、指定同型を選び直さない。
指定Yoneda単位の未検証下書きは作業木に残す。R3・R4には入らない。

### 51.6 正規化の逆・三因子の法則と単位の簡約（検証中）

一覧：済み 0／全体 13（うち追加 11）

端点正規化の逆同型・三因子の合成の法則を明示した。二段前合成は既存の
`Project/QuasicategoryAuxiliaries/MappingSpaces/FunctorIsoWhiskerCancellation.lean` の
`functorIso_precomp_precomp` を使い、作り直さない。
単位の下書きはkernelの既定上限に引き続き達したため、具体的な関手空間の射作用の前に
一般の圏の射作用の異種等式へ分けて再検証中。上限変更はない。
以下の型は既存構成の法則・証明分割で、新しいID項目には数えない。
いずれも200行未満。単位のLeanは未検証のままコミットしない。

#### DiagramIsoNormalizationAlgebra（44行、検証中）

```lean
lemma diagramIsoCongr_symm {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    diagramIsoCongr hg hf e.symm = (diagramIsoCongr hf hg e).symm

lemma diagramIsoCongr_trans_three {A X : SSet.{u}}
    {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : A ⟶ X}
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (h₂ : f₂ = g₂) (h₃ : f₃ = g₃)
    (e₁ : FunctorIso f₀ f₁) (e₂ : FunctorIso f₁ f₂) (e₃ : FunctorIso f₂ f₃) :
    diagramIsoCongr h₀ h₃ (e₁ ≪≫ e₂ ≪≫ e₃) =
      diagramIsoCongr h₀ h₁ e₁ ≪≫ diagramIsoCongr h₁ h₂ e₂ ≪≫ diagramIsoCongr h₂ h₃ e₃

```

#### HomWeightYonedaUnitSquare（114行、検証中）

```lean
private lemma precomposeFunctorHom_eq_map {A B X : SSet.{u}}
    (k : B ⟶ A) {f g : A ⟶ X} (α : FunctorHom f g) :
    precomposeFunctorHom k α =
      (hoFunctor.map ((pre k).app X)).toFunctor.map α

private lemma curryEvaluation_of_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} {f' g' : B ⟶ (ihom A).obj X}
    (α : FunctorHom f' g') (β : FunctorHom f g)
    (hf : f' = curry f) (hg : g' = curry g) (h : HEq α (curryFunctorHom β))
    (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom B).map (evaluateFunctorAt (Y := X) a))).toFunctor.map α)
      (precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) β)

local instance unitSquareAProduct : Quasicategory (A.op ⊗ A) := quasicategory_of_innerFibration (fst A.op A)
local instance unitSquareCProduct : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

local instance unitSquareCProduct : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

lemma functorHomBifunctorUnit_eq_square (F : A ⟶ C) :
    functorHomBifunctorUnit F =
      precomposeFunctorHom (uliftTensorIso A.op A).inv
        (leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
          (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
          (twistedArrowProjection_naturality F))

private lemma functorMapHom_heq {L : Type v} {M : Type v'}
    [Category.{w} L] [Category.{w'} M] (H : L ⥤ M)
    {x y x' y' : L} (hx : x = x') (hy : y = y')
    {α : x ⟶ y} {β : x' ⟶ y'} (h : HEq α β) : HEq (H.map α) (H.map β)

private lemma homWeightUnit_evaluate_curry_heq (F : A ⟶ C) (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).map
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map (homWeightYonedaUnit F))
      ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).map
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map
            (curryFunctorHom (functorHomBifunctorUnit F)))

lemma homWeightYonedaUnit_evaluate_heq (F : A ⟶ C) (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).map
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map (homWeightYonedaUnit F))
      (precomposeFunctorHom
        (lift (SSet.const (ULift.up (SSet.opObjEquiv.symm a)))
          (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A)))
        (functorHomBifunctorUnit F))

```


### 51.7 四端点での係数貼り合わせ（検証中）

一覧：済み 0／全体 13（うち追加 11）

元の同じ三因子を四つの対象別切断図式の端点へ正規化する法則を書いた。
`DiagramIsoNormalizationAlgebra` にも、同じ値の二表示の正規化が一致する法則を追加。
二本の対象ビルド・小監査を一枚の整理券で待っている。
ログ：`/tmp/is-w1/coefficient-normalization-verify/run.log`。検証済み累計は118本9,549行のまま。
単位下書きの最新の再分割も含め、以下は既存構成の法則・証明分割の型。
計算上限は不変、全宣言200行未満。いずれも未検証のLeanはコミットしない。

#### DiagramIsoNormalizationAlgebra（56行、現時点の型）

```lean
lemma diagramIsoCongr_symm {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    diagramIsoCongr hg hf e.symm = (diagramIsoCongr hf hg e).symm

lemma diagramIsoCongr_trans_three {A X : SSet.{u}}
    {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : A ⟶ X}
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (h₂ : f₂ = g₂) (h₃ : f₃ = g₃)
    (e₁ : FunctorIso f₀ f₁) (e₂ : FunctorIso f₁ f₂) (e₃ : FunctorIso f₂ f₃) :
    diagramIsoCongr h₀ h₃ (e₁ ≪≫ e₂ ≪≫ e₃) =
      diagramIsoCongr h₀ h₁ e₁ ≪≫ diagramIsoCongr h₁ h₂ e₂ ≪≫ diagramIsoCongr h₂ h₃ e₃

lemma diagramIsoCongr_eq_of_heq {A X : SSet.{u}}
    {f g f' g' h k : A ⟶ X} (hf : f = h) (hg : g = k)
    (hf' : f' = h) (hg' : g' = k)
    (e : FunctorIso f g) (e' : FunctorIso f' g') (he : HEq e e') :
    diagramIsoCongr hf hg e = diagramIsoCongr hf' hg' e'

```

#### SimplexSectionCoefficientPasting（104行、現時点の型）

```lean
local instance coefficientPasting_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma normalizedTriple_heq {A X : SSet.{u}}
    {f₀ f₁ f₂ f₃ f₄ g₀ g₁ g₂ g₃ g₄ : A ⟶ X}
    (e₁ : FunctorIso f₀ f₁) (e₂ : FunctorIso f₁ f₂) (e₃ : FunctorIso f₂ f₃)
    (d : FunctorIso f₀ f₄) (h : HEq (e₁ ≪≫ e₂ ≪≫ e₃) d)
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (h₂ : f₂ = g₂)
    (h₃ : f₃ = g₃) (h₄ : f₄ = g₄) :
    HEq (diagramIsoCongr h₀ h₁ e₁ ≪≫ diagramIsoCongr h₁ h₂ e₂ ≪≫
        diagramIsoCongr h₂ h₃ e₃) (diagramIsoCongr h₀ h₄ d)

lemma simplexSectionCoefficient_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let evp := evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)
    let S₀ := kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
        (leftFibrationObjectOf q₀))
    let S₁ := kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor T)).evaluate
        (leftFibrationObjectOf q₁))
    let S₂ := t ≫ kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate
        (leftFibrationObjectOf (pullback.snd p k)))
    let S₃ := t ≫ (s ≫ kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
        (leftFibrationObjectOf p)))
    let γ := diagramIsoCongr (f' := S₀) (g' := S₁)
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
        transportSimplexSectionInfinity_joint_evaluate q₀])
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate q₁])
      (FunctorIso.postcomp (simplexSectionCompIso k l) evp)
    let δ₁ := diagramIsoCongr (f' := S₁) (g' := S₂)
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate q₁])
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (FunctorIso.postcomp (simplexSectionFirstIso k l) evp)
    let δ₂ := diagramIsoCongr (f' := S₂) (g' := S₃)
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (by rw [Category.assoc, Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (simplexSectionSecondIso k l) evp)
    let δ := diagramIsoCongr (f' := S₀)
      (g' := U.map (nerveMap (transportSimplexFunctor (l ≫ k))) ≫
        kanDiagramCoherentNerve
          ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
            (leftFibrationObjectOf p)))
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p (l ≫ k),
        transportSimplexSectionInfinity_joint_evaluate q₀])
      (by rw [Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso (l ≫ k)) evp)
    HEq (γ ≪≫ δ₁ ≪≫ δ₂) δ

```

#### HomWeightYonedaUnitSquare（121行、現時点の型）

```lean
variable {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]

private lemma precomposeFunctorHom_eq_map {A B X : SSet.{u}}
    (k : B ⟶ A) {f g : A ⟶ X} (α : FunctorHom f g) :
    precomposeFunctorHom k α =
      (hoFunctor.map ((pre k).app X)).toFunctor.map α

private lemma curryEvaluation_of_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} {f' g' : B ⟶ (ihom A).obj X}
    (α : FunctorHom f' g') (β : FunctorHom f g)
    (hf : f' = curry f) (hg : g' = curry g) (h : HEq α (curryFunctorHom β))
    (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom B).map (evaluateFunctorAt (Y := X) a))).toFunctor.map α)
      (precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) β)

local instance unitSquareAProduct : Quasicategory (A.op ⊗ A) := quasicategory_of_innerFibration (fst A.op A)
local instance unitSquareCProduct : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

local instance unitSquareCProduct : Quasicategory (C.op ⊗ C) := quasicategory_of_innerFibration (fst C.op C)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

private lemma unitSquare_raw (F : A ⟶ C) :
    leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
        (functorHomBifunctorDiagram_classificationIso F F).inv =
      leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
        (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
        (twistedArrowProjection_naturality F)

private lemma functorHomUnit_heq_map (F : A ⟶ C) :
    HEq (functorHomBifunctorUnit F)
      ((hoFunctor.map ((pre (uliftTensorIso A.op A).inv).app SpaceInfinity.{u})).toFunctor.map
        (leftClassificationHom (twistedArrowProjection A) (functorHomBifunctorProjection F F)
          (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F) ≫
            (functorHomBifunctorDiagram_classificationIso F F).inv))

lemma functorHomBifunctorUnit_eq_square (F : A ⟶ C) :
    functorHomBifunctorUnit F =
      precomposeFunctorHom (uliftTensorIso A.op A).inv
        (leftClassificationSquareHom (twistedArrowProjection A) (twistedArrowProjection C)
          (SSet.opFunctor.map F ⊗ₘ F) (edgewiseSubdivisionMap F)
          (twistedArrowProjection_naturality F))

private lemma homWeightUnit_eq_normalized_curry (F : A ⟶ C) :
    homWeightYonedaUnit F =
      SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
        (U' := yonedaInfinityMap A)
        (V' := (SSet.uliftFunctor.{u + 1, u}).map F ≫
          SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F)
        rfl (functorHomBifunctorDiagram_curry F F)
        (curryFunctorHom (functorHomBifunctorUnit F))

lemma homWeightYonedaUnit_evaluate_heq (F : A ⟶ C) (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).map
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map (homWeightYonedaUnit F))
      (precomposeFunctorHom
        (lift (SSet.const (ULift.up (SSet.opObjEquiv.symm a)))
          (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A)))
        (functorHomBifunctorUnit F))

```


### 51.8 四端点の正規化の検証済み区切り

一覧：済み 0／全体 13（うち追加 11）

二本の対象ビルド成功（5,505 jobs）。新しい環境の11宣言の小監査成功、標準三公理のみ。
計算上限は不変。ログ：`/tmp/is-w1/coefficient-normalization-verify/`。
今回160行、検証済み累計120本・9,709行。E01本体の完成には数えない。

#### SimplexSectionCoefficientValues（99行、検証前の型）

既存係数評価の略記・法則のみ。新しい比較同型の選択や独立した構成はない。

```lean
local instance coefficientValues_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

abbrev simplexSectionValue {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B)) ⟶ SpaceInfinity.{u}

def simplexSectionBaseChangeCoefficient {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    FunctorIso (simplexSectionValue (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        simplexSectionValue p)

def simplexSectionCompositeCoefficient {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso (simplexSectionValue (pullback.snd p (l ≫ k)))
      (simplexSectionValue (pullback.snd (pullback.snd p k) l))

lemma simplexSectionBaseChangeCoefficient_heq {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (simplexSectionBaseChangeCoefficient p k)
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))

lemma leftStraightening_baseChange_firstVertex_coefficient
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))
      ((leftClassificationSimplexIso p).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
        (simplexSectionBaseChangeCoefficient p k).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm)

```

#### SimplexSectionCoefficientComposition（109行、検証前の型）

既存係数評価の略記・法則のみ。新しい比較同型の選択や独立した構成はない。

```lean
local instance coefficientComposition_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma simplexSectionFirstCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    diagramIsoCongr
      (f' := simplexSectionValue (pullback.snd (pullback.snd p k) l))
      (g' := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        simplexSectionValue (pullback.snd p k))
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd (pullback.snd p k) l)])
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (FunctorIso.postcomp (simplexSectionFirstIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      simplexSectionBaseChangeCoefficient (pullback.snd p k) l

lemma simplexSectionSecondCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let t := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))
    let s := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (f' := t ≫ simplexSectionValue (pullback.snd p k))
      (g' := t ≫ (s ≫ simplexSectionValue p))
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (by rw [Category.assoc, Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (simplexSectionSecondIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      (simplexSectionBaseChangeCoefficient p k).precomp t

lemma simplexSectionBaseChangeCoefficient_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (simplexSectionCompositeCoefficient p k l ≪≫
        simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
        (simplexSectionBaseChangeCoefficient p k).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))))
      (simplexSectionBaseChangeCoefficient p (l ≫ k))

```


## 52. 対象別係数の合成則と正規化した指定底変換（11-14、途中）

一覧：済み 0／全体 13（うち追加 11）

三本の対象ビルド成功（5,517 jobs）、新しい環境の32宣言の小監査成功。
標準三公理のみ、計算上限は不変。ログ：`/tmp/is-w1/coefficient-composition-verify/run-2.log`。
今回293行、検証済み累計123本・10,002行。E01本体は未完了。

元の係数評価の略記、元の係数の合成則、指定底変換の制限の共役表示を同じ端点の等式へ
戻す入力が通った。新しい比較同型・独立した構成の選択や仮定は追加していない。
標準引き戻し同型の分類は元の逆射を逆に持つ（既存の分類の合成則・恒等則の系）。

### SimplexSectionCoefficientValues（99行、既存構成の法則・略記）

```lean
local instance coefficientValues_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

abbrev simplexSectionValue {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (TransportSimplexCategory B)) ⟶ SpaceInfinity.{u}

def simplexSectionBaseChangeCoefficient {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    FunctorIso (simplexSectionValue (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        simplexSectionValue p)

def simplexSectionCompositeCoefficient {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    FunctorIso (simplexSectionValue (pullback.snd p (l ≫ k)))
      (simplexSectionValue (pullback.snd (pullback.snd p k) l))

lemma simplexSectionBaseChangeCoefficient_heq {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq (simplexSectionBaseChangeCoefficient p k)
      (FunctorIso.postcomp (transportSimplexSectionInfinity_baseChangeIso k)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p)))

lemma leftStraightening_baseChange_firstVertex_coefficient
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    HEq ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))
      ((leftClassificationSimplexIso p).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
        (simplexSectionBaseChangeCoefficient p k).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm)

```

### SimplexSectionCoefficientComposition（111行、既存構成の法則・略記）

```lean
local instance coefficientComposition_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma simplexSectionFirstCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    diagramIsoCongr
      (f' := simplexSectionValue (pullback.snd (pullback.snd p k) l))
      (g' := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l)) ≫
        simplexSectionValue (pullback.snd p k))
      (by rw [Category.assoc, leftFibrationBaseChange_evaluate p k, Category.assoc,
        leftFibrationBaseChange_evaluate (pullback.snd p k) l,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd (pullback.snd p k) l)])
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (FunctorIso.postcomp (simplexSectionFirstIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      simplexSectionBaseChangeCoefficient (pullback.snd p k) l

lemma simplexSectionSecondCoefficient_normalized {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let t := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))
    let s := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (f' := t ≫ simplexSectionValue (pullback.snd p k))
      (g' := t ≫ (s ≫ simplexSectionValue p))
      (by rw [Category.assoc, Category.assoc, leftFibrationBaseChange_evaluate p k,
        transportSimplexSectionInfinity_joint_evaluate (pullback.snd p k)])
      (by rw [Category.assoc, Category.assoc, transportSimplexSectionInfinity_joint_evaluate p])
      (FunctorIso.postcomp (simplexSectionSecondIso k l)
        (evaluateFunctorAt (Y := SpaceInfinity.{u}) (leftFibrationInfinityVertex p))) =
      (simplexSectionBaseChangeCoefficient p k).precomp t

lemma simplexSectionBaseChangeCoefficient_pasting {E B D T : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (simplexSectionCompositeCoefficient p k l ≪≫
        simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
        (simplexSectionBaseChangeCoefficient p k).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor l))))
      (simplexSectionBaseChangeCoefficient p (l ≫ k))

```

### LeftStraighteningSimplexPastingInputs（83行、既存構成の法則・略記）

```lean
local instance simplexPastingInputs_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma leftStraightening_baseChange_simplex_normalized
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc])
      rfl
      ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D))) =
      (leftClassificationSimplexIso p).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k))) ≪≫
        (simplexSectionBaseChangeCoefficient p k).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p k)).symm

lemma leftStraightening_baseChange_simplex_intertwining
    {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    (diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc])
      rfl
      ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D)))).hom ≫
      (leftClassificationSimplexIso (pullback.snd p k)).hom =
      ((leftClassificationSimplexIso p).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)))).hom ≫
        (simplexSectionBaseChangeCoefficient p k).inv

lemma leftClassificationHom_preserves_iso {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    IsIso (leftClassificationHom p q e.hom he)

```

次は、標準引き戻し同型の分類の制限を同じ補正係数の逆の共役として回収し、
二段の指定底変換の中間制限同型を相殺して初頂点制限の忠実性で降下する。
指定単位の下書きの再検証は別ログへ分離しており、この成功の宣言数には含めない。

## 53. 指定底変換の貼り合わせの降下（11-14、検証中）

一覧：済み 0／全体 13（うち追加 11）

§46.2で承認された元のHomの型で、`leftStraightening_baseChange_pasting` まで書いた。
まだビルド前で、依存する四本から対象ビルドを待っている。
新しい比較・独立した構成を選ばず、同じ制限比較の三因子の相殺と初頂点制限の忠実性で降下する。

第一の指定底変換の二段制限は対象ビルドを通過。標準比較の分類では、
元の逆射の分類の自然性に順方向の分類を合成し、同じ係数補正の逆の共役を得る。
直接底変換も同じ係数貼り合わせで共通の共役に揃える。
未検証の単位下書きのkernelの簡約の問題とは別の部分であり、成功には混ぜない。

検証済み累計は123本10,002行のまま。今回の五本は計508行、全部通ると128本10,510行。
E01本体には指定単位の始点固定とKan普遍性への接続が残る。残りの新規行数の見込みは、
E01 700〜1,400、E02〜E06 1,150〜1,950、RR01〜RR05 3,100〜4,950、R2d・R2e 500〜700。
合計5,450〜9,000行で、今回が通った時点からの全体の見込みは
15,960〜19,510行。外枠20,800行の内側で進める。

以下はすべて既存構成の法則・証明分割（新しいID項目なし）。各宣言200行未満、計算上限不変。

### LeftClassificationPullbackSimplexIso（101行）

```lean
local instance pullbackSimplexIso_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma isoPrecomp_hom {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    (e.precomp k).hom = precomposeFunctorHom k e.hom

private lemma precomp_identity {A D X : SSet.{u}} (k : D ⟶ A) (f : A ⟶ X) :
    precomposeFunctorHom k (𝟙 (HomotopyCategory.mk (functorVertex f))) = 𝟙 _

lemma leftClassification_pullbackComparison_simplexIso {E B D T : SSet.{u}}
    [Quasicategory T] (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    FunctorIso.precomp (asIso c)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap T)) =
      leftClassificationSimplexIso q₁ ≪≫ (simplexSectionCompositeCoefficient p k l).symm ≪≫
        (leftClassificationSimplexIso q₀).symm

```

### LeftStraighteningSimplexWhisker（86行）

```lean
local instance simplexWhisker_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

lemma leftStraightening_baseChange_simplex_whisker
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
        Category.assoc])
      (((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map l)).precomp
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        ((simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        ((leftClassificationSimplexIso (pullback.snd p k)).precomp t).symm

```

### LeftStraighteningSimplexComposite（97行）

```lean
local instance simplexComposite_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma conjugation_chain {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ s₀ s₁ s₂ s₃ : L}
    (r₀ : a₀ ≅ s₀) (r₁ : a₁ ≅ s₁) (r₂ : a₂ ≅ s₂) (r₃ : a₃ ≅ s₃)
    (d₀ : s₁ ≅ s₀) (d₁ : s₂ ≅ s₁) (γ : s₃ ≅ s₂) :
    (r₀ ≪≫ d₀.symm ≪≫ r₁.symm) ≪≫
        (r₁ ≪≫ d₁.symm ≪≫ r₂.symm) ≪≫
        (r₂ ≪≫ γ.symm ≪≫ r₃.symm) =
      r₀ ≪≫ (γ ≪≫ d₁ ≪≫ d₀).symm ≪≫ r₃.symm

lemma leftStraightening_baseChange_composite_simplex
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      rfl
      (FunctorIso.precomp
        ((leftStraighteningInfinityDiagram_baseChangeIso p k).precomp (U.map l) ≪≫
          leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l ≪≫ asIso c)
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        (simplexSectionCompositeCoefficient p k l ≪≫
          simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
          (simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        (leftClassificationSimplexIso q₀).symm

```

### LeftStraighteningSimplexDirect（126行）

```lean
local instance simplexDirect_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma isoSymm_heq {L : Type v} [Category.{w} L]
    {a b a' b' : L} (e : a ≅ b) (e' : a' ≅ b')
    (ha : a = a') (hb : b = b') (h : HEq e e') : HEq e.symm e'.symm

private lemma isoThree_heq {L : Type v} [Category.{w} L]
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : L}
    (e₁ : a₀ ≅ a₁) (e₂ : a₁ ≅ a₂) (e₃ : a₂ ≅ a₃)
    (d₁ : b₀ ≅ b₁) (d₂ : b₁ ≅ b₂) (d₃ : b₂ ≅ b₃)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃)
    (he₁ : HEq e₁ d₁) (he₂ : HEq e₂ d₂) (he₃ : HEq e₃ d₃) :
    HEq (e₁ ≪≫ e₂ ≪≫ e₃) (d₁ ≪≫ d₂ ≪≫ d₃)

lemma leftStraightening_baseChange_direct_simplex
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let t := U.map (nerveMap (transportSimplexFunctor l))
    let s := U.map (nerveMap (transportSimplexFunctor k))
    diagramIsoCongr
      (by
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality l,
          Category.assoc]
        apply congrArg (fun z ↦ t ≫ z)
        rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc])
      rfl
      (FunctorIso.precomp
        (diagramIsoCongr
          (f' := U.map l ≫ (U.map k ≫ leftStraighteningInfinityDiagram p))
          (by rw [Functor.map_comp, Category.assoc]) rfl
          (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)))
        (U.map (transportSimplexFirstVertexMap T))) =
      ((leftClassificationSimplexIso p).precomp s).precomp t ≪≫
        (simplexSectionCompositeCoefficient p k l ≪≫
          simplexSectionBaseChangeCoefficient (pullback.snd p k) l ≪≫
          (simplexSectionBaseChangeCoefficient p k).precomp t).symm ≪≫
        (leftClassificationSimplexIso (pullback.snd p (l ≫ k))).symm

```

### LeftStraighteningBaseChangePasting（103行）

```lean
local instance straighteningPasting_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k)

private lemma isoPrecomp_hom {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    (e.precomp k).hom = precomposeFunctorHom k e.hom

private lemma normalized_hom_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : FunctorIso f g) :
    HEq (diagramIsoCongr hf hg e).hom e.hom

lemma leftStraightening_baseChange_pasting_iso
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    let q₀ := pullback.snd p (l ≫ k)
    let q₁ := pullback.snd (pullback.snd p k) l
    let c := leftClassificationHom q₁ q₀ (pullbackLeftPullbackSndIso p k l).hom
      (pullbackLeftPullbackSndIso_hom_snd p k l)
    letI := leftClassificationHom_preserves_iso q₁ q₀ (pullbackLeftPullbackSndIso p k l)
      (pullbackLeftPullbackSndIso_hom_snd p k l)
      (pullbackLeftPullbackSndIso_inv_snd_snd p k l)
    (leftStraighteningInfinityDiagram_baseChangeIso p k).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map l) ≪≫
      leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l ≪≫ asIso c =
    diagramIsoCongr
      (f' := (SSet.uliftFunctor.{u + 1, u}).map l ≫
        ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p))
      (by rw [Functor.map_comp, Category.assoc]) rfl
      (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k))

lemma leftStraightening_baseChange_pasting
    {E B D T : SSet.{u}} [Quasicategory B] [Quasicategory D] [Quasicategory T]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) (l : T ⟶ D) :
    HEq (precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map l)
        (leftStraighteningInfinityDiagram_baseChangeIso p k).hom ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd p k) l).hom ≫
      leftClassificationHom (pullback.snd (pullback.snd p k) l)
        (pullback.snd p (l ≫ k)) (pullbackLeftPullbackSndIso p k l).hom
        (pullbackLeftPullbackSndIso_hom_snd p k l))
      (leftStraighteningInfinityDiagram_baseChangeIso p (l ≫ k)).hom

```


### 53.1 指定単位の点評価の分離と実持ち上げの合成（検証前）

一覧：済み 0／全体 13（うち追加 11）

単位の点評価は、同じ指定単位の定義式を評価関手で写す部分へ分離した。
積上の局所準圏証明を追加せず、元の一般評価則に明示した定義域・終域を渡す。
旧正方形下書きから同じ公開名の未検証の宣言を除き、重複させない。
実正方形の持ち上げの合成は、元の標準比較と二つの射影で計算する法則として書いた。
どちらも検証前で、E01の完成や検証済み行数に含めない。

#### HomWeightYonedaUnitPointEvaluation（71行）

```lean
private lemma homWeightUnit_eq_normalized_curry {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C) :
    homWeightYonedaUnit F =
      SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr
        (U' := yonedaInfinityMap A)
        (V' := (SSet.uliftFunctor.{u + 1, u}).map F ≫
          Project.HomotopyDiagramComparison.presheafHomWeightDiagram F)
        rfl (functorHomBifunctorDiagram_curry F F)
        (curryFunctorHom (functorHomBifunctorUnit F))

lemma homWeightYonedaUnit_evaluate_heq {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C) (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).map
        (evaluateFunctorAt (Y := SpaceInfinity.{u})
          (ULift.up (SSet.opObjEquiv.symm a))))).toFunctor.map (homWeightYonedaUnit F))
      (precomposeFunctorHom
        (lift (SSet.const (ULift.up (SSet.opObjEquiv.symm a)))
          (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A)))
        (functorHomBifunctorUnit F))

```

#### ClassifiedSquareLiftPasting（46行）

```lean
lemma squareLift_pasting {A B C E H J : SSet.{u}}
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    pullback.lift f p hf ≫
      F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange
        q (pullback.snd r l) (pullback.lift g q hg) (pullback.lift_snd _ _ _) k =
    pullback.lift (f ≫ g) p (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]) ≫
      (pullbackLeftPullbackSndIso r l k).inv

```


### 53.2 元の指定底変換の貼り合わせ則の検証済み区切り

一覧：済み 0／全体 13（うち追加 11）

五本の対象ビルド成功（5,526 jobs）。新しい環境の24宣言の小監査成功、標準三公理のみ。
計算上限の変更なし。ログ：`/tmp/is-w1/native-simplex-bridges-verify/run-4.log`、
`catalog-after.log`、`audit-after.log`。
今回513行、検証済み累計128本・10,515行。

§46.2で承認された `leftStraightening_baseChange_pasting` を元の型のまま証明した。
全準圏の底B・D・Tを許し、指定底変換も標準反復引き戻し比較の分類射も置き換えていない。
同じ二つの初頂点制限の共役を照合し、制限の充満忠実性で降下した。
E01本体には指定単位の始点固定評価とKan普遍性への接続が残るため、一覧の済み数は増やさない。

次は分離した指定単位の点評価と、実正方形の持ち上げの合成を検証し、
既存の `twistedSourceHomUnit_homUniversal` との同じ射の照合へ進む。
今回の実測を入れた残りの見込みは15,965〜19,515行（外枠20,800行）。
