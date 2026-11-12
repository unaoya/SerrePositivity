# IS-W2 停止点0：Δ・Δᵒᵖ の strict 模型と native な錐の橋

作成：2026-11-12、③-b ∞ 供給 b。枝 `math/inf-supply-b`、worktree `../SerrePositivity-bs-d68`。指示書：`inf-supply-w2.md` §0〜§2。**段0の紙の報告であり、Lean の実装・型検査・ビルドはしていない。停止点0で承認を待つ。**

## 0. 開始点と読んだ範囲

- BS-D69 は main の登録 `a34a840f7` で完了。clean な専用 worktree で main `6cc2795f3`（`a34a840f7` の後）から指定の枝を新規作成した。BS の枝は変更していない。
- IS-W2 §0〜§2、`bhatt-scholze/foundation-entry-points.md` §4.1 の G10、IS-W1 の追記11-10・11-11、`InfinityCategories/README.md` の配置表を読んだ。
- 指定の `report-codex-w16.md` §21.5 は開始時の main にはなく、⑤a の枝 `math/bs-impl` の `36da456c0` にある同節を `git show` で読んだ。⑤a のファイル・枝は変更していない。同節の旧パスは KL-W1 後の実在パスで照合した。
- 目標は、対象ごとの同値の集合ではなく、図式の全パラメーターに関する関手と、同じ頂点・脚・高次単体を持つ native な錐の族。`HasColimit`・`HasLimit` だけでは供給完了としない。

## 1. 既存の道具の洗い出し（指示書 §1 の表）

以下のパスは `SerrePositivity/` からの相対パス。名前空間の長い接頭辞は、ファイルの現在の namespace を使う。

| 部品・実在する入口 | 実際に得られるもの | そのままでは得られないもの／再利用の方針 |
| --- | --- | --- |
| `InfinityCategories/Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/BousfieldKan.lean`：`bousfieldKanWeight`、`bousfieldKanHolim`、`bousfieldKanEvaluation`、`bousfieldKanHolimFunctor` | 一般の通常の小圏上の重み付き end、評価、関手 | D(A) の積全複体との同定、同じ native 錐の全パラメーター化は別。Kan 値の写像空間の比較に使う。 |
| 同 `BousfieldKanColimit.lean`：`bousfieldKanColimit`、`bousfieldKanColimitHomIso`。`LimitsAndColimitsOfSpaces/BousfieldKanCoherentColimit.lean`：`bousfieldKanCoherentCocone_isColimit` | strict な `I ⥤ KanObject` の Kan 置換した coend と、元の coherent nerve 図式上の指定 native 余極限余錐。通常の小圏一般について証明済み | 名前に Coherent があっても、入力は strict 図式。任意の `nerve I → SpaceInfinity` の strictification の定理ではない。一般の加群・代数値へそのまま適用できない。 |
| `HomotopyLimitsAndColimits/BousfieldKanComparison.lean`：`bousfieldKanConeComparison_homotopyEquivalence_of_extensions`、`BousfieldKanSectionsIso.lean`：`bousfieldKanSectionsIso` | 成分ごとの anodyne 延長条件から、実際の標準比較のホモトピー同値・切断との同型 | 延長条件を具体的な Hom 図式について証明する必要がある。条件そのものを未証明の引数にして最終入口へ残さない。 |
| `HomotopicalAlgebra/Diagram/HomotopyColimit.lean`：`replacement`、`replacementComparison`、`functor`、`comparison`、`computesDerivedIso` | 関手的 projective cofibrant 置換、弱同値の保存、通常の局所化上の左導来余極限との自然同型 | `computesDerivedIso` は通常の局所化・導来関手の同型。準圏の全関手、join 余錐、指定脚への比較ではない。一般形は `[ModelCategory C]`・局所表示可能性・生成性を要求するので、複体／BE の実在する模型に具体化する。 |
| `KST/Spectra/CosimplicialTotalization.lean`：`obj`、`π`、`lift`、`uncurry`、`kanComplex`。`CosimplicialKanReplacement.lean`：`functor`、`unit`、`reedy_terminal_rlp` | 標準単体を重みとする strict Tot の end、成分の射、実際の horn filler、関手的 Reedy 置換 | raw `obj X` の Kan 性には相対 matching の条件がある。一般 X の native 極限は `obj (replacement X)` と比べる。raw Tot が無条件に ∞ 極限だとは読まない。 |
| `EInfinity/BarrattEccles/DiagramModel.lean`：`projectiveModelCategory`、`weakEquivalence_iff`、`cofibrantlyGenerated`、`isFibrant` | 任意の通常の小圏の BE 代数図式の具体的な projective 模型。弱同値は台の擬同型 | 図式がすべて fibrant なことから通常の lim の導来性は出ない。右 Quillen の忘却 U に左 Quillen 用 `QuillenColimitComparison` を適用しない。U が projective cofibrant 図式を保存するとも仮定しない。 |
| `InfinityCategories/Kerodon/LimitsAndColimits/ExamplesOfLimitsAndColimits/SiftedColimitPreservation.lean`：`PreservesSmallSiftedColimits`、`.of_functorIso` | 任意の小さい sifted 単体集合 I、任意の図式と指定 native 余極限余錐を量化する保存性。同じ全関手同型による輸送 | Δᵒᵖ の strict 図式だけの保存より強い。IS-W2 では幾何学的実現の成分とその coherent 版まで。全 sifted への延長を済ませたとは言わない。 |
| `InfinityCategories/Project/DerivedCategories/InfinityCategory.lean`：`derivedInfinityCategory`、`derivedInfinityCategoryVertexEquiv`、`derivedInfinityCategoryEdgeEquiv`、`derivedInfinityCategoryQuasicategory`。`SemifreeResolution.lean`：`exists_complexSemifree_resolution` | D(A) は半自由複体の dg nerve。任意の非有界複体に半自由分解がある | 分解の単なる選択は図式の strict functor や全関手の比較ではない。関手的な既存の導来源を使う。積・Tot の複体を半自由部分圏の対象と無条件に扱わない。 |
| `EInfinity/ComplexLimits/OrdinaryDerivedSource.lean`：`complexOrdinaryDerivedSource`、`complexOrdinaryDerivedSource_map_weak`。`DerivedSourceValues.lean`、`StrictHomology.lean`：`complexOrdinaryDerivedSourceHomologyIso` | 通常の複体圏の nerve から既存 D(A) への実際の全写像、擬同型の反転、同じ半自由出力とホモロジーの自然同型 | 使う側の `strictToD` の実例との入口。一般 D(A) 側から EInfinity への依存を増やす配置は避けたいので、実装時は既存の `Project/DerivedCategories/DGModuleOutputResolution*` の基盤を直接使うか、移動せず薄い比較を別に置く。既存宣言の移動・変更は行わない。 |
| `InfinityCategories/HA/DerivedCategoryModels/CoherentBar/NativeColimit.lean`：`dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit`。`StrictComparison/SemifreeNativeColimit.lean`：`dgSemifreeCoherent_hasColimit` | dg 加群値の任意の coherent 図式に対する指定 bar 余錐の余極限性、半自由模型への移送による余極限の存在 | 前者の値は dg 右加群、後者の返り値は `HasColimit`。既存 D(A) への一点 dg 圏による比較、幾何学的実現の具体的複体との同定、全図式族・指定脚の比較を接続する必要がある。 |
| `Project/DerivedCategories/DGStrictFunctorNerve.lean`：`dgStrictFunctorNerveMap` | strict dg 関手圏の通常の nerve から全関手 ∞ 圏への実写像。高次単体の自然性を保持する | 任意の coherent 図式を strict な通常の図式で表す essential surjectivity は別問題。全関手版のパラメーター化に再利用する。 |
| `Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/LocalKanDiagramStrictification.lean`：`localKanDiagramStrictificationIso`、`exists_localKanDiagramStrictification` | 標準単体上の空間値 coherent 図式を、有限順序の Kan 値射列へ全関手同型で移す | 単体上の局所版。Δ または Δᵒᵖ 全体の strictification・境界と射の整合までは供給していない。3b-3 の既存完成品として数えない。 |
| `EInfinity/ComplexLimits/FramedLimitDerived.lean`：`framedLimitDerivedIso`、`FramedLimitAdjunction.lean`：`framedLimitAdjunction`。⑤a §21.5 の frame 実現の部品 | 通常の局所化上の frame 極限と導来像、同じ frame の実現と射の比較 | native な錐の全関手比較と同じではない。G10 は frame 極限複体と積全複体の比較も必要。 |

### 満たせない SSet の模型仮定の扱い

上の BK の native 余錐、anodyne 延長による比較、KST の Reedy horn の入口には、追加の `[ModelCategory SSet]` 引数はない。従って「使える候補が全部その仮定を要求する」という状況ではない。

⑤a §21.5 にある `ColimitMapComparison.diagramSourceComparison_weakEquivalence` の自由な `[ModelCategory SSet]` を要求する版は採らない。`[ModelCategory C]` を持つ汎用 hocolim API は、実際に構成済みの複体／BE の模型にだけ具体化する。入口の仮定を消すために同じ仮定を別の構造体へ隠したり、比較を引数として要求したりはしない。段0では import 閉包全体の公理監査までは実行していないので、実装段階の各監査で再確認する。

## 2. 型案に共通する約束

以下は**紙の型案**。新しい名前は提案名で、Lean で型検査済みの宣言ではない。既存の使う側の drafts・界面は変更しない。

- `DA := Project.DerivedCategories.derivedInfinityCategory A`、`Q_A` は既存の `complexOrdinaryDerivedSource A` と同じ全導来源。`SF A` は既存 Semifree の通常圏、`Ch A` は整数次数 cochain 複体。
- `J` はまず Δ または Δᵒᵖ。`I_J` はその nerve を DA と同じ宇宙へ持ち上げたもの。`P_J := nerve (J ⥤ SF A)`。加群・一般複体を扱う場合のパラメーターは `nerve (J ⥤ Ch A)`。評価関手を nerve と dg nerve の包含で移した**全評価写像** `ev_J : P_J ⊗ I_J → DA` を固定する。
- Δ は `Type 0`、複体の対象宇宙は u+1。`SimplexCategory` の nerve の持ち上げと `ULift`／`ULiftHom` による小さい通常圏模型の比較を一度作り、その比較を全錐・全関手へ共用する。持ち上げの合成を定義的等号と決めつけない。
- 頂点を持つだけの関数 `X ↦ c_X` ではなく、`P_J` の全単体に関して compatible な join 錐の族を返す。`FunctorIso` の等式は全関手上で述べ、ホモトピー圏だけの自然同型は系とする。

## 3. 3b-1：D(A) 値の幾何学的実現

提案する入口：

```text
strictSimplicialRealization_A : P_(Δᵒᵖ) → DA
strictSimplicialRealizationCoconeFamily_A :
    P_(Δᵒᵖ) ⊗ (I_(Δᵒᵖ) ⋆ Δ[0]) → DA
```

図式側の制限は `ev_(Δᵒᵖ)`、apex 側の制限は `strictSimplicialRealization_A`。各 X でこの族から得られる `JoinCocone` が `IsColimitCone` を満たすことを証明する。頂点の比較は全関手の `FunctorIso` として、`Q_A` に送った具体的な直和全複体／frame の導来実現と同定する。cochain 規約の具体的模型は

`|X|^q = ⨁_(n≥0) (X_n)^(q+n)`

で、単体境界と内部微分の符号を固定する。単なる通常の `colim X` をこの実現として採用しない。各 n の脚は次数 n の評価と標準単体の重みから作り、native 余錐の高次単体と照合する。図式の射 f の像は同じ全複体の射と比較し、脚を変えた別の余錐へ置き換えて済ませない。

証明の筋：実在する図式置換／frame 実現 → strict simplicial bar の全複体との比較 → coherent bar の native 余錐との比較 → 半自由出力へ移送。同じ比較を射・高次パラメーターにも構成する。Semifree 内で直和全複体が閉じることを無条件に推論せず、必要なら同じ関手的半自由出力を頂点に使い、augmentation の同値で全体を輸送する。

不足：Δ の small 模型と universe の一括処理、実現と bar の全図式族の比較、脚と射を含む native 余錐の束。既存の colimit 存在定理だけから具体的な頂点・脚の式は出ない。

## 4. 3b-2：G10、D(A) 値の Tot

一般の strict な `X : CosimplicialObject (Ch A)` には、積全複体の関手 `TotProd_A` を作る。

`TotProd(X)^q = ∏_(n≥0) (X^n)^(q−n)`。

全微分は、余単体次数 n を横次数とし、交代余面微分と `(-1)^n` 倍の内部微分を加える規約。積の並べ替え・射・自然性を同じ関手の中で示す。必要な次数条件を省略した未定義の無限和は使わない。

```text
strictCosimplicialTotalization_A := nerveMap TotProd_A ≫ Q_A
strictCosimplicialLimitConeFamily_A :
    nerve (Δ ⥤ Ch A) ⊗ (Δ[0] ⋆ I_Δ) → DA
```

図式側は `ev_Δ`、apex 側は `strictCosimplicialTotalization_A` と一致させる。各 X の錐に `IsLimitCone` を証明する。frame で先に錐を作る場合も、TotProd 側への `FunctorIso` を錐の族全体へ持ち上げ、同じ頂点・脚で返す。

**G10 の加群入力**は離散複体への埋め込みで制限する。この場合 `TotProd` は交代余面複体を `ComplexShape.embeddingUpNat.extendFunctor` で整数次数に零延長したものと自然同型になる。従って入口表の `cosimplicialModule_limitCone` は、この指定錐とその極限性を返す系として閉じる。仮の `homology'` は本体では使わず、既存の `homology i` と零延長関手で記述する。

全ホモロジー比較は、通常の図式圏からの関手の自然同型

```text
ordinaryToHoNerve (Δ ⥤ Ch A) ⋙ hoMap strictCosimplicialTotalization_A
  ⋙ cohomologyOnHo A i
    ≅ TotProd_A ⋙ homologyFunctor A i
```

とし、加群版はその制限。射 f の正方形に加え、錐の各脚の像が Tot の標準評価を表すことを示す。次数 n の成分への射影をそのまま X^n への鎖写像と誤認しない。離散入力で高次の脚を作るには cofaces と高次 homotopy が必要で、それを join 錐で保持する。

証明の筋：半自由 Y からの derived Hom の Kan 模型を固定し、Hom と積全複体の交換、正規化／非正規化の比較、写像空間の BK/Tot の比較を自然に証明する。これを指定 join 錐の写像空間の極限判定へ渡す。非有界複体の部分には、cosimplicial additive 図式の split matching と積全複体の計算を確認する。ここを確認せずに「全対象 fibrant だから lim でよい」としない。

使う側との接続：`EInfinityTheory.ofCosimplicial_forget` は `nerveMap (cosimplicialCochains A) ≫ E.strictToD A` との `FunctorIso` を要求する（`EInfinity/Interface/Theory.lean`）。この `cosimplicialCochains` は現在、環の台の余単体加群の零延長された交代余面複体。G10 の加群制限の全関手比較と同じ型の強さになる。`E.strictToD` 一般について実例と無条件に同じとは仮定せず、実際に⑤aが構成する導来源との既存の比較を経由して接続する。

非有界な余単体的 **cdga** 全体の E∞ 積と Tot の比較は、IS-W1 追記11-10どおり範囲外。一般の複体の線形 Tot と、その乗法的な全比較は区別する。

## 5. 3b-3：coherent 図式の strictification と錐の輸送

候補の型は、J=Δ・Δᵒᵖ に対し、strict な複体図式の objectwise quasi-isomorphism による ∞ 局所化 `StrictDiagramInfinity_A J` と、全関手 ∞ 圏との比較

```text
evaluation_A,J : StrictDiagramInfinity_A J → Fun(I_J, DA)
strictDiagramComparison_A,J : QCatEquivalence evaluation_A,J
```

および逆方向の全関手と単位・余単位の `FunctorIso`。**通常の `nerve (J ⥤ SF A)` 自体が全関手 ∞ 圏と同値だとは要求しない**。objectwise 弱同値の局所化を抜いた主張にはしない。

`nerve (J ⥤ Ch A)` からの実評価と上の evaluation の factorization の全関手同型を先に固定する。任意の coherent F から逆関手で得る strict 模型は、局所化での表示として取り出し、同じ F 上の図式の同型を得る。ある図式を strict に表せるという存在形だけで終えず、図式の射の像と native 錐の輸送の可換性まで全関手圏で返す。

3b-1・3b-2 で作った錐をこの比較で前後に移す。元の指定錐 c を受け取る API も、図式の同型による錐の輸送と極限／余極限の一意性で返す。coherent 図式に対し、strict に戻した頂点が同値というだけでは元の c の保存を主張しない。

既存の局所 Kan strictification、dg strict 関手の全 nerve map、projective 図式模型・hammock の既存の局所化を再利用する。HTT 4.2.4.1・A.3.3 の図式比較の、必要な全パラメーター版が主な不足。単体上の局所比較を無限の Δ の全体へ貼る coherence は未確認であり、最も不確実な部分。まず J を Δ・Δᵒᵖ に固定し、一般の小圏の strictification まで範囲を広げない。

## 6. 3b-4：CAlg_A と点つき Kan 複体

### 6.1 CAlg_A

`CAlg_A` は⑤aが使う実際の Barratt–Eccles 模型の局所化、`U_A := cAlgForgetDerived A` とする。3b-1〜3b-3 と同じ型の全関手・錐の族を構成し、次の二つを別に証明する。

- 実現：`U_A ∘ Realize_CAlg ≃ Realize_DA ∘ U_A^(Δᵒᵖ)`。指定余錐の U 像が D(A) の指定余錐の族と全関手同型で両立し、余極限性を持つ。
- Tot：`U_A ∘ Tot_CAlg ≃ Tot_DA ∘ U_A^Δ`。指定極限錐の U 像と D(A) の錐の族との比較。⑤aの `ofCosimplicial_cone` と `ofCosimplicial_forget` に同じ頂点・脚で接続する。

Tot 側は実際の右随伴 U の極限保存と frame による頂点の比較を使う候補。native な随伴／保存定理との接続が要る。実現側は「U は右随伴」「通常の sifted colim を創出する」だけからは出ない。arity ごとの有限テンソル冪と EZ／latching の比較で、**同じ** cofibrant/Reedy 置換・増大・脚を持つ実現比較を示す必要がある。

⑤a §21.5 の境界を維持する：③-b は strict-native の橋と coherent な図式・錐の輸送を受け持つ。BE 固有の U の実現比較には⑤aの arity／frame の部品を再利用するが、未供給の比較を「既存」として入力にはしない。この残る BE 固有部分を③-b の新規ファイルで補う分も下の3b-4の見積もりに含める。⑤aの既存ファイルには手を付けず、セル対・二項余積の既存作業と重複しそうなら先に止めて調整役へ報告する。

全 sifted の完成欄 `forget_preservesSifted` を仮定して幾何学的実現保存を証明する循環は作らない。IS-W2 の返り値はまず Δᵒᵖ と Δ の全図式・指定錐についての保存。`PreservesSmallSiftedColimits U_A` そのものは、任意の sifted 単体集合形状への延長を行う⑤a側の次段階。

### 6.2 点つき Kan 複体（L9）

Reedy 条件を持つ X では、既存の `CosimplicialTotalization.obj X` を頂点とし、射影から作る同じ pointed native 錐に極限性を証明する。任意の X の派生 Tot は `obj ((CosimplicialKanReplacement.functor).obj X)`。point は既存の置換 unit の像から定め、end の整合性で Tot の point を作る。全図式の射と pointed 忘却との比較を保存する。

型の境界：raw `obj X` が任意の非 Reedy fibrant X でも native 極限だという主張はしない。L9 の既存 `kanComplex` の相対 matching 条件のある版と、無条件の置換後の版を別名で提供する。これは現行の KST の入力条件と整合し、既存の型を変更する提案ではない。

## 7. 置き場所・順序・規模

| 段 | 新規ファイル群の候補 | 規模見込み |
| --- | --- | --- |
| 共通 | `Project/DerivedCategories/DiagramComparison/UniverseShape`、`StrictEvaluation`、`ConeFamilies`。一般の join 錐の族の輸送が再利用可能なら `Kerodon/LimitsAndColimits/LimitsAndColimits/`（7.1、Tag 02H1） | 600〜1,000行、5〜8本 |
| 3b-1 | `HA/DerivedCategoryModels/SimplicialRealization/{DirectSumTotal,FrameComparison,NativeCocone,Naturality}` と D(A) の薄い入口 | 1,000〜1,800行、8〜14本 |
| 3b-2 | `HA/DerivedCategoryModels/CosimplicialTotalization/{ProductTotal,NormalizedComparison,MappingFamily,NativeCone,HomologyNaturality,DiscreteModules}` | 1,800〜3,200行、14〜24本 |
| 3b-3 | `Project/DerivedCategories/DiagramComparison/{ProjectiveLocalization,StrictCoherentEvaluation,Rectification,ConeTransport}`。一般化が本当に一般 ∞ 圏の定理になれば対応する Kerodon 節へ分ける | 2,400〜4,200行、18〜30本 |
| 3b-4 | `EInfinity/RealizationComparison/`・`EInfinity/TotalizationComparison/`。Kan の weighted Tot の一般部分は `Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/`（7.5、Tag 039Y）、空間の native 錐は `LimitsAndColimitsOfSpaces/`（7.4、Tag 02SX）、pointed の適用は `KST/Spectra/` | 2,600〜4,600行、20〜34本 |
| **合計** | 共通分を一度だけ計上。名称・分割はまだ案 | **8,400〜14,800行、65〜110本** |

置き場所のうち `Project/DerivedCategories/DiagramComparison/` は、strict 図式の実装模型を含み Kerodon の一般定理と言えない部分の**要検収候補**。IS-W2 §2.3 に従い、確定するまでは Project 側に置く。旧 `F2/`・旧 `HomotopyLimits/` のパスで新規ファイルを作らない。docstring には HTT 4.2.4.1・A.3.3、HA 1.2.4、該当する Kerodon 節番号／Tag を記載する。

規模の1.3倍の判断は、上端14,800行を基準とするなら **19,240行**。ただし段ごとの大幅な膨張や、局所 strictification から全図式族への接続の見通しが崩れた時点でも、上限まで機械的に続けず再見積もりして報告する。これは型検査前の見込みであり、3b-3 と BE の実現比較の不確実性を含む。

段1の最初の区切りは、Δᵒᵖ 上の一つの strict 図式について、実現の複体・native 余錐・標準脚・同じ射の像を照合できる最小の部品。その後に全パラメーターを束ねる。段2は G10 の加群版を射・指定錐まで閉じた時点で独立に取り込めるようにする。段3の一般 strictification を段2の唯一の証明として待つ形にはしない。G8・G9・G14 は③-aの持ち分で、新規実装の対象に含めない。

## 8. 停止点0の確認事項と状態

1. 指定の型は、全関手・指定 join 錐の族までの形で上の3b-1〜3b-4を提案する。通常の局所化の自然同型、対象ごとの `HasLimit`／`HasColimit`、通常の sifted colim の創出で代用しない。
2. 3b-3 の strict 図式の ∞ 局所化による全関手圏比較と、L9 の Reedy 条件付き raw Tot／置換後 Tot の区別を確認してほしい。使う側の drafts の型の変更は今回していない。今後の検査で既存型がこれより強いと分かった場合は、指示書どおりその時点で止める。
3. Project の仮配置と、3b-4 の BE 固有の新規補助は上の分担・規模で検収をお願いする。⑤aの既存ファイルを変更する必要や重複が見えた場合は、作業前に報告する。

この段では本報告だけを追加した。新規 Lean 宣言0、既存宣言・drafts・入口・監査スクリプトの変更0。ビルド・一時 Lean 検査・監査は未実施で、鍵も取得していない。**段1へは進まず、停止点0で待機する。**


## 9. 段1の着手：検証済みの基盤（2026-11-12、f118060a3）

main の承認 `411106ba3` を `4914d98f3` で枝へ取り込み、指示書 §3 を読んで段1を開始した。以下は実現複体との計算比較を始めるための基盤であり、**停止点1でも、依頼された「一つの strict 図式で実現複体・native 余錐・標準脚・射の像を照合する最初の区切り」の完了でもない**。その比較を引き続き実装する。

### 9.1 本体で検証したもの

- `StrictDiagramEvaluation` は strict 図式圏の全 nerve と持ち上げた添字の nerve を同時に評価する。各単体の対象・射の公式を示した。`StrictDiagramParameter` は一つの図式へ制限すると元の同じ strict nerve 写像になることを、全単体で厳密な等号として示す。
- `StrictSemifreeDiagram` は閉零圏に値を持つ strict な半自由図式を、既存の `derivedInfinityCategory A` の全図式として読む。`SemifreePointComparison` は一点 dg 加群の半自由模型からこの D(A) への実際の dg 準同値と準圏同値。⑤a の既存ファイルを変更せず、元の全 Hom の評価を制限して作った。
- `SmallDiagramShape` は宇宙0から係数環の宇宙を経由する二段の ULift と、直接の ULift の同型。`SmallShapeColimits` はこれと既存 coherent bar の native 余極限を移し、同じ D(A) の小さい形状の図式に余極限があることを示す。この存在だけを実現の比較として扱わない。
- `StrictSemifreeColimitFamily` は上の全評価を curry し、既存 `exists_colimitCoconeFamily` を用いて native 普遍余錐の全部分圏への**全写像**を作る。全余錐への包含後の下方図式は元の評価の族と厳密に一致する。実際の「パラメーター × join」からの全写像と、その同じ apex の全関手も定義した。ここでの選択だけから、apex と直和全複体の比較を証明したとはしていない。
- `DirectSumTotal` は単体的複体の交代面複体を n↦−n で延長してから、既存の直和 total を取る全関手。非有界複体を許し、加群の宇宙は既存の `Complex A` と合わせた。native な余錐への標準射とその普遍性は残件。

### 9.2 ビルド・監査・規模

- 対象ビルドは `/private/tmp/isw2-build-1.log`、`isw2-build-3.log`、`isw2-build-4.log`、`isw2-build-5.log` で成功。最新の2入口のビルドは7145 jobs。これらは依存を含む対象ビルドであり、root ビルドではない。KL-W1 後の依存は worktree の既存キャッシュに未復元だったため、Lake の共有キャッシュから復元された。一時的に main 成果物を検索先へ足す個別検査も試したが、同じパッケージ内の未復元モジュールはそれでは解決されず、成功判定は通常の対象ビルド後の結果だけを使った。
- 一時監査は `/private/tmp/AuditISW2Eight.lean`、ログ `/private/tmp/isw2-audit-eight.log`。**新規8本・62宣言、標準三公理のみ**。sorry・独自公理0。既存宣言、drafts、入口、公式監査は変更していない。`[ModelCategory SSet]` を最終定理の仮定として使っていない。
- 各ビルド・監査は `with_build_lock.sh --wait 3600` で一回ずつ鍵を取り、終了時に返却した。同時に複数の整理券を出していない。
- 実測は**共通6本・373行**、**3b-1の2本・147行**、合計520行（docstring・importを含む）。共通の見込み上端1,000行／停止基準1,300行、3b-1の見込み上端1,800行／停止基準2,340行に対して、いずれも範囲内。native な余錐の族と具体的実現の複体を結ぶ比較はまだ含まれないため、この実測から段1全体が見込みより小さくなったとは判断しない。

登録候補（まだ登録しない）：

```text
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramParameter
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeDiagram
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SmallShapeColimits
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeColimitFamily
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
```

## 10. 段1の標準脚・面ホモトピーと規模の再見積もり（2026-11-12、bf80c840b）

### 10.1 検証済みの追加

以下の5本を `bf80c840b` にコミットした。既存宣言・drafts・入口・公式監査の変更はない。

- `ColimitCoconeFamilyExtension`：パラメーターの部分単体集合上で**既に指定した普遍余錐の全族**を保ち、全パラメーターへ延長する。射影の引き戻しの trivial Kan fibration と単射に対する持ち上げだけを使う。延長の制限は厳密な等号であり、頂点だけの同定ではない。ただし、この補題へ渡す計算済みの普遍余錐を今回完成させたわけではない。
- `ZeroRowInclusion`：横次数零から出る微分が零である二重複体で、零行の同じ直和包含を鎖写像にし、二重複体の射に対する厳密な自然性を証明した。
- `StandardZeroLeg`：任意の単体的非有界複体 X に対し、添字延長の零行同型と上の包含を合成して、**具体的な**標準脚 `X₀ ⟶ directSumTotalFunctor.obj X` を定義した。図式の射 f に対して `ι_X ≫ |f| = f₀ ≫ ι_Y` を証明し、零次評価から実現全複体への自然変換を作った。
- `FirstRowHomotopy`：横次数 -1 の同じ直和包含で、横微分の後に零行の標準脚を合成した射の零ホモトピーを構成した。全微分の縦成分の符号は負であり、内部微分の項が相殺する。
- `StandardFaceHomotopy`：元の単体次数一の複体と横次数 -1 の行の同型を用い、横微分が `δ₀ − δ₁` であることを証明した。同じ第一行の包含から `Homotopy (δ₀ ≫ ι) (δ₁ ≫ ι)` を構成した。

この追加は**最初の照合の完了報告ではない**。計算複体・標準脚・射の像の線形側を固定したが、この全複体を頂点に持つ native join 余錐の高次成分と、その余極限性の証明は未完。§9 の任意に選んだ native apex を、この計算複体と同一視したとは扱わない。停止点1も未達である。

### 10.2 対象ビルド・監査・実測

- 個別検査後、`with_build_lock.sh --wait 3600` の下で小さい対象ビルドを実施した。`/private/tmp/isw2-build-6.log`（零行包含と部分族延長、2959 jobs）、`isw2-build-7.log`（標準零次脚、2385 jobs）、`isw2-build-8.log`（第一行ホモトピー、2385 jobs）、`isw2-build-9.log`（面ホモトピー、2387 jobs）はすべて成功。各実行の終了を確認してから次の整理券を出し、鍵を返却した。root ビルドは流していない。
- 全新規13本の一時監査 `/private/tmp/AuditISW2Thirteen.lean`、ログ `/private/tmp/isw2-audit-thirteen.log` は成功。**103宣言、標準三公理のみ**。内訳は監査のモジュール順で `[1, 6, 12, 8, 14, 8, 4, 11, 4, 21, 1, 8, 5]`。sorry・独自公理0。満たせない `[ModelCategory SSet]` の仮定は加えていない。
- 今回の追加は共通1本51行、3b-1の4本262行。累計は**共通7本424行、3b-1の6本409行、計13本833行**（docstring・import込み）。共通の見込み上端1000行／停止基準1300行、3b-1の見込み上端1800行／停止基準2340行に対し、現在の実測はそれぞれ576行、1391行少ない。ただし、以下の未実装の比較が主要部分として残る。

追加の登録候補（調整役による登録まで入口・公式監査へ足さない）：

```text
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilyExtension
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ZeroRowInclusion
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardZeroLeg
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.FirstRowHomotopy
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardFaceHomotopy
```

### 10.3 残件の具体化と上限による停止

既存の比較の適用条件を調べた結果、段0の「frame で比較する」という見込みは、計算複体との接続の規模を過小評価していた。

1. `CoherentBar/NativeColimit` は実際の正規化 coherent bar の指定 native 余錐を返すが、その bar は `nerve (Δᵒᵖ)` の射列で添字づけられる。今回の `DirectSumTotal` は単体次数 n の `Xₙ` で添字づけられる。二つを定義上同じ複体とすることはできず、実際の比較射・高次成分・擬同型の証明が必要。
2. `HomologicalAlgebra/BicomplexColumnQuasiIso` と `BicomplexRowQuasiIso` は第一象限の版である。前者の証明は各全次数の有限直和を用いる。今回の直和全複体は横次数 -n、縦次数は非有界の整数であり、そのまま適用できない。bar／重みの比較を使う経路では、適切な有界方向の濾過または鎖ホモトピーで、この差を埋める必要がある。
3. `ColimitMapComparison.diagramSourceComparison_weakEquivalence` と両側の frame 比較には自由な `[ModelCategory SSet]` を要求する既存版がある。承認された規則どおり使わない。実在する Kan／anodyne の比較で置き換える経路も候補だが、それだけで具体的な直和全複体と同じ join 余錐を得られるわけではない。
4. `SemifreeNativeColimit` や bar 頂点判定だけでは、同じ脚・射・高次単体を返す最終入口を閉じられない。今回の部分族延長は、計算済みの余錐を保って束ねる段階には使えるが、計算済み余錐の普遍性の証明の代用にはしない。

ここでの再見積もりは、未実装部分について次のとおり（実測ではなく設計上の幅）：

| 3b-1 の残り | 追加行数の見込み |
| --- | --- |
| 全単体次数の包含・微分公式、退化との整合、計算複体への指定余錐の高次成分 | 500〜750 |
| strict な Δᵒᵖ 図式の bar／重みと直和全複体の比較、非有界内部次数での擬同型性 | 850〜1250 |
| 実際の半自由出力分解を通した native 余錐の輸送、同じ標準脚の照合 | 500〜750 |
| 全パラメーターでの関手同型と射・指定余錐の照合 | 250〜350 |
| **追加計** | **2100〜3100** |

現在の3b-1の409行を含めて、**2509〜3509行（丸めて2500〜3500行程度）**を見込む。段0の上端1800行から約700〜1700行増え、承認済みの停止基準2340行を超える見込み。共通部分は424行で、共通の基準を超える見込みによる停止ではない。段1の不足を共通や段3へ付け替えて基準内と扱わない。

従って、[指示書 §1](inf-supply-w2.md) の「規模の上限は段0の見込みの1.3倍。超えそうなときは報告して止める。止まる前に、それまでの検証済みの分をコミットする」と、§3.6 の段ごとの基準に従い、**ここで新規実装を停止する**。検証済みコードは `bf80c840b` までコミット済み。未検証の Lean 下書きは残していない。型・範囲を弱める提案はなく、再見積もりの検収を待つ。段2（G10）には進んでいない。

## 11. §4 の承認後の再開：非有界全複体と bar の具体的比較射（2026-11-12）

main の上限改定 `0f30e1f6c` を `435647adc` で枝へ取り込み、段1を再開した。§10の「再見積もりの検収を待つ」という停止はこの承認で解除された。段1の停止基準は約3500行。

### 11.1 非有界全複体の一般補題（1729ecbe0）

新規4本308行を対象ビルド・監査後にコミットした。

- `HomologicalAlgebra/TotalHorizontalHomotopyComponents`：一般の加法圏 C の整数次数の二重複体 K, L について、必要な直和の存在 `[K.HasTotal (.up ℤ)]`・`[L.HasTotal (.up ℤ)]` のみを要求する。横次数を一つ下げる内側の鎖写像の族から、直和全複体の同じ次数 -1 の成分を `totalDesc` で作る。各因子上の公式、次数の消滅、全微分の二成分の公式を証明した。
- `HomologicalAlgebra/TotalHorizontalHomotopy`：横方向の鎖ホモトピー `h : Homotopy f g` を、同じ二つの全複体の射の鎖ホモトピーへ移す。各因子で元の横ホモトピー方程式を使い、縦微分の二項を符号の差で相殺する。横方向の鎖ホモトピー同値を、同じ前向き・後向きの射の全複体の鎖ホモトピー同値へ移す帰結もある。有界性・対角線の有限性・スペクトル系列の収束は使わない。**任意の列ごとの擬同型を全複体の擬同型へ移す一般定理を示したわけではない**。入力は内側の鎖写像で与えられた、実際の横鎖ホモトピーである。
- `HomologicalAlgebra/ChainTotalizationHomotopy`：外側の非負鎖次数を n↦-n で延長して直和全複体を取る一般関手。添字延長で同じ鎖ホモトピーを移し、上の結果を適用する。C の必要な零対象・小さい余積の存在を型に明記した。
- `SimplicialRealization/NormalizedTotalComparison`：正規化 Moore 複体の全複体から非正規化直和全複体への自然変換を、元の Moore 包含から作る。Dold–Kan の実際のホモトピー同値を上の関手で移すので、各成分は同じ比較射を持つ鎖ホモトピー同値・擬同型。単体的ホモトピーから同じ二つの実現の射の鎖ホモトピーへの移送も構成した。

一般補題を依頼どおり `HomologicalAlgebra/` に置いた。加法圏 C を一般にしているため、積全複体との双対的な接続の入力にも使える。ただし、3b-2の積全複体そのものや、その符号・添字を戻す比較はまだ実装していない。これらの行数はすべて3b-1に数える。

### 11.2 射列と元の単体次数を結ぶ同じ比較射（b8dd9dfad）

新規3本261行を対象ビルド・監査後にコミットした。

- `SimplicialRealization/SourceVertexSimplex`：Δᵒᵖ の n 本の射列 s から、途中の各標準単体の零頂点を先頭の標準単体へ戻して単調な頂点列を作り、`[n] ⟶ (s.obj 0).unop` を定義した。任意の単体作用素 r に対し、引き戻した射列の比較と先頭への射を合成したものが、元の比較と r の合成に厳密に一致する。
- `HomologicalAlgebra/SimplicialReplacement`：任意の通常の小圏 J の図式 F に対し、n 次を射列 s の先頭の値 `F(s₀)` の余積とする strict な単体的置換を構成した。単体作用素・元の図式の自然変換の作用を元の各因子で指定し、全図式圏からの関手としてまとめた。模型構造や加法性は不要で、値の圏の必要な小さい余積だけを仮定する。
- `SimplicialRealization/ReplacementAugmentation`：Δᵒᵖ 上の X の置換から X 自身への実際の単体的比較射を、上の先頭頂点単体の作用素で作った。全図式の射に自然な変換として束ね、元の各余積因子上の射を照合した。この段階では、この比較の全複体の擬同型性を主張していない。

### 11.3 検証・行数と残件

- `/private/tmp/isw2-build-10.log`（一般成分、1471 jobs）、`isw2-build-11.log`（非有界全複体・正規化比較、2398 jobs）、`isw2-build-12.log`（置換・先頭頂点・全自然比較、1143 jobs）はすべて成功。共有の鍵は各回 `--wait 3600`、整理券は一枚、ビルドの間だけ取得した。待っている間の編集と個別検査は鍵の外で行った。
- 全新規20本の一時監査 `/private/tmp/AuditISW2Twenty.lean`、ログ `/private/tmp/isw2-audit-twenty.log`：**186宣言、標準三公理のみ**。sorry・独自公理0。内訳 `[18, 10, 8, 11, 13, 12, 11, 1, 6, 12, 8, 14, 8, 4, 11, 4, 21, 1, 8, 5]`。既存の宣言・drafts・入口・公式監査は変更していない。
- 検証済み累計：共通7本424行、**3b-1の13本978行**、計20本1402行。今回の追加569行の割り当ては、§10.3表の第一行（全単体次数の具体的データ）82行、第二行（bar／重み・非有界比較）487行。表の第三・第四行は今回まだ0行。いずれも途中の実測であり、停止点1では各行を完了した状態で見込みとの差を報告する。

段1と、最初の「一つの strict 図式の実現複体・native 余錐・標準脚・射の像」の照合は、引き続き未完。残りは具体的な bar／重みの比較の鎖ホモトピー同値、native 余錐の同じ頂点・脚への輸送、全パラメーターでの照合。次は線形重みの射影分解の比較を調べ、元の比較射の擬同型性を閉じる。段2にはまだ進まない。

追加登録候補（停止点1で調整役が登録）：

```text
SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopyComponents
SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopy
SerrePositivity.HomologicalAlgebra.ChainTotalizationHomotopy
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.NormalizedTotalComparison
SerrePositivity.HomologicalAlgebra.SimplicialReplacement
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SourceVertexSimplex
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementAugmentation
```

## 12. 線形重みの同じ比較射の鎖ホモトピー同値（2026-11-12、6116404d7 まで）

### 12.1 検証済みの筋

非有界の係数複体に対し、bar の射列と元の単体次数の比較を、**線形重みの射影分解の比較**で先に閉じた。これは native な余錐の比較の完了ではなく、その計算に必要な同じ射の鎖ホモトピー同値である。

- `27efde4c1`（3本166行）：`ProjectiveFreePresheaf` は自由 Yoneda の Hom 同値で持ち上げを評価値へ戻し、射影係数の自由表現可能前層の射影性を示す。`FreePresheafFunctor` は係数の余積関手と Yoneda の全関手を合成し、元の自由前層と照合する。`StandardSimplexCoefficientContraction` は raw Yoneda の標準単体を既存の ULift 標準単体と増大ごと同型にし、その指定収縮を同じ係数の余積へ移す。
- `28f5d0fe6`（3本259行）：`AugmentedChainFunctorComparison` は交代面鎖増大と加法関手の二つの標準比較を照合し、各評価の extra degeneracy から前層全体の同じ増大の擬同型性を得る。`SimplicialReplacementAugmentation` は厳密な余錐の元の脚で単体的置換を増大する。`StandardSimplexWeight` は各次数を自由表現可能前層とする線形標準重みを構成し、その同じ増大を射影分解にまとめる。基底は `(Δᵒᵖ)ᵒᵖ` とし、opposite の Hom の包装を明示的な同型で移している。
- `328fa2e29`（4本370行）：`InitialNerveExtraDegeneracy` は始対象を射列の先頭に前置して、元の増大 nerve の指定収縮を作る。`UnderChainEquiv` は under 圏の射列を底の射列と最初の構造射の組へ表示し、恒等射での標準持ち上げと復元を照合する。`UnderNerveWeight` は x↦N(x/J) の全前層に同じ係数の余積を適用し、各評価の始対象によって同じ増大の擬同型性を示す。`BarWeightProjective` は各評価の射影性だけで済ませず、標準持ち上げの生成元で選んだ持ち上げを最初の構造射で全生成元へ延ばし、前層圏での射影性を直接示す。同じ増大を持つ bar 重みの射影分解が得られた。
- `6116404d7`（2本178行）：`UnderSourceVertex` は under の構造射と固定済みの先頭頂点単体を合成し、底の射・全単体作用素に対する同じ作用素を照合する。`BarWeightComparison` はその作用素を線形化した全自然比較を作り、同じ増大を厳密に保つことを示す。**前向きの射をこの具体的な比較射に固定した**鎖ホモトピー同値を、二つの射影分解の比較から構成した。任意の選択は後向きの持ち上げとホモトピーに限る。

この経路を選んだ理由：非有界の内部複体のホモロジーに対する収束を要求せず、重みの段階の実際の鎖ホモトピーを、加法的な線形 coend と§11の全複体関手へ移せるため。係数の図式に関する自然性を保つには、coend を係数・重みの両方の全関手として作る必要がある。その実装を続けている。加法関手でない一般の集合値重みの弱同値だけを、非有界全複体の比較の代用にはしない。

### 12.2 対象ビルド・監査・規模

`/private/tmp/isw2-build-13.log`（992 jobs）、`isw2-build-14.log`（1353 jobs）、`isw2-build-15.log`（1366 jobs）、`isw2-build-16.log`（1348 jobs）、`isw2-build-17.log`（1366 jobs）、`isw2-build-18.log`（1377 jobs）はすべて成功。各回の鍵は `--wait 3600` で一枚ずつ取得し、ビルド終了で返した。対象ビルドの間の編集は、実行中の対象に含まれない新規ファイルのみとした。root ビルド・入口・公式監査への登録は行っていない。

一時監査 `/private/tmp/AuditISW2ThirtyTwo.lean`、ログ `/private/tmp/isw2-audit-thirtytwo.log` は成功。**新規32本・299宣言、標準三公理のみ**。sorry・独自公理0。既存宣言・drafts の変更0。

検証済み累計は共通7本424行、**3b-1の25本1951行**、計32本2375行。今回§12の973行はすべて§10.3表の第二行（bar／重み・非有界比較）に数える。従って現時点の項目別途中実測は第一行82行、第二行1460行、第三行0行、第四行0行（§10以前の409行は別）。第二行は見込み850〜1250行に対し、既に上端より210行増えている。coend の計算比較を含めた最終実測と差は停止点1で再集計する。

**段1と最初の native 余錐の照合の区切りは引き続き未完**。検証済みなのは重みの具体的な比較までであり、実際の係数図式の coend と具体的な直和全複体の同定、native bar の同じ頂点・脚の比較、全パラメーターの指定余錐への接続は残る。

追加登録候補（停止点1で調整役が登録）：

```text
SerrePositivity.HomologicalAlgebra.ProjectiveFreePresheaf
SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
SerrePositivity.HomologicalAlgebra.StandardSimplexCoefficientContraction
SerrePositivity.HomologicalAlgebra.AugmentedChainFunctorComparison
SerrePositivity.HomologicalAlgebra.SimplicialReplacementAugmentation
SerrePositivity.HomologicalAlgebra.StandardSimplexWeight
SerrePositivity.HomologicalAlgebra.InitialNerveExtraDegeneracy
SerrePositivity.HomologicalAlgebra.UnderChainEquiv
SerrePositivity.HomologicalAlgebra.UnderNerveWeight
SerrePositivity.HomologicalAlgebra.BarWeightProjective
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.UnderSourceVertex
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.BarWeightComparison
```

## 13. 実際の線形 coend と非有界全複体への移送、再見積もりによる中間停止（2026-11-12）

### 13.1 今回の新規6本（484行）

重みの比較を抽象的な移送の仮定のまま残さず、元の非有界複体図式を係数とする coend を実装した。

- `HomologicalAlgebra/CoendAdditive`（39行）：加法圏 C の同じ coend 関手が加法的であることを、各 coend 包含上で証明した。必要な各 coend の存在を仮定する一般版。
- `HomologicalAlgebra/LinearWeightRealization`（95行）：加群重みを次数零の複体へ送り、元の図式 X とテンソルした coend を取る加法関手を構成した。X の全図式圏からの関手も構成し、重みの比較と X の全射に対する同じ正方形を示した。
- `HomologicalAlgebra/LinearFreeWeight`（101行）：自由表現可能重みの各生成元を、単位子と X の同じ射の合成へ送る。single とテンソルが必要な小さい余積を保つことを明示し、coend の二つの作用に関する等式を示した。一般の余極限保存を仮定せず、証明に使う余積保存だけを要求する。
- `HomologicalAlgebra/LinearCoYoneda`（103行）：自由重みの coend の評価射と、恒等射の生成元による逆射を構成した。生成元 f の評価が X.map f そのものであること、X.map f と恒等射の生成元の関係、二つの合成が恒等射であることを証明した。
- `HomologicalAlgebra/LinearCoYonedaNaturality`（70行）：この評価同型を表現対象 j の全射に関する自然同型 `freePresheafFunctor J unit ⋙ linearWeightRealization A X ≅ X` にまとめた。対象ごとの同型にとどまらず、すべての単体作用素を保つ形になった。
- `SimplicialRealization/LinearWeightTotalComparison`（76行）：具体的な coend 関手で§12の固定された重みの鎖ホモトピー同値を移し、§11の一般の非有界全複体の補題を適用した。前向きの射は元の先頭頂点比較の同じ像で、擬同型でもある。標準重みの全複体から元の `directSumTotalFunctor` の値への同型を、上の全自然 co-Yoneda 同型と交代面複体の標準比較で構成した。

最後のファイルの全複体の同型と鎖ホモトピー同値は、現時点では X ごとの宣言である。元となる coend の X に関する全関手と自然性は作ったが、**最終的な全関手同型・指定 native 余錐の族まで閉じたとは扱わない**。

### 13.2 未実装の接続と、上限の再検討

最初の「一つの strict 図式の実現複体・native 余錐・標準脚・射の像」の照合も、停止点1も未完。残る具体的な作業は次のとおり。

1. bar 重みの coend の各次数を、元の射列を添字とする `simplicialReplacement` の同じ余積へ同定し、全単体作用素と先頭頂点比較を照合する。`UnderChainEquiv` と自由重みの評価は使えるが、bar の各項の同型とその自然性そのものは未実装。
2. この交代面直和全複体を、既存の strict coherent bar の同じ複体へ結ぶ。既存の `CoherentBar/StrictComparison/Columns` で高次 prefix 項の消滅と残る face・prefix の符号公式はあるが、shift ブロックと全複体の符号を戻す鎖写像、その逆・正規化比較は別に必要。§11の `NormalizedTotalComparison` は通常の単体的複体の Moore 正規化の結果であり、それだけで既存の Maurer–Cartan bar の正規化との同一視にはならない。
3. 得た実際の比較を半自由出力分解と D(A) へ移し、同じ頂点・標準脚・高次成分を持つ join 余錐を作り、その余極限性を示す。既存の `SemifreeBarVertexCriterion` は頂点の同型の存在を返す結果なので、この指定余錐の代用にはしない。`StrictResolutionDiagramIso` の分解比較を使う場合も、その錐と脚の輸送の照合が要る。
4. この指定余錐を、strict 図式の全パラメーターで束ねる。既に作った部分族延長は、計算済みの余錐を保って束ねる段階に使えるが、上の計算や同じ脚の証明を省くものではない。

今回の484行はすべて§10.3表の第二行に数える。検証済みの3b-1は **31本2435行**、共通7本424行を含めて **38本2859行**。共通部分への付け替えはしていない。残りを具体化した再見積もりは次のとおり（未実装分は幅の見込みで、実測ではない）。

| §10.3 の項目 | §10の追加見込み | 現在の途中実測 | 残りの見込み | 完成時の見込み | 元の上端との差の見込み |
| --- | ---: | ---: | ---: | ---: | ---: |
| 全単体次数の包含・微分・退化・指定余錐の高次成分 | 500〜750 | 82 | 350〜500 | 432〜582 | −318〜−168 |
| bar／重み・直和全複体の具体的比較・非有界擬同型 | 850〜1250 | 1944 | 400〜650 | 2344〜2594 | +1094〜+1344 |
| 半自由出力分解・native 余錐の輸送・同じ脚 | 500〜750 | 0 | 500〜750 | 500〜750 | −250〜0 |
| 全パラメーターの関手同型・射・指定余錐 | 250〜350 | 0 | 250〜350 | 250〜350 | −100〜0 |
| **追加計（§10以前の409行を除く）** | **2100〜3100** | **2026** | **1500〜2250** | **3526〜4276** | **+426〜+1176** |

§10以前の409行を含めると、**3b-1完成時の見込みは3935〜4685行（約3900〜4700行）**になる。増分の主因は第二行である。非有界全複体の一般補題308行に加え、全前層の射影分解と同じ具体的比較の証明、加法的な coend の全関手と同じ生成元を保持する評価同型の実装が必要になった。coend の接続は一般の弱同値の保存を仮定して済ませず、実際の鎖ホモトピーを保持する形で証明したため、第二行の幅850〜1250行の見積もりが不足した。

これは3b-2の作業への着手や範囲の一般化による増分ではない。新しい模型構造の仮定・対象ごとの存在での代用・draftsの型の弱化も提案しない。第一行の一部を第二行で同時に処理できる分は上表で控えめに見積もったが、それでも3500行を超える見込み。

[指示書 §1・§4](inf-supply-w2.md) の「超えそうなときは報告して止める」に従い、**この区切りで新規実装を停止する**。これは停止点1の完了報告ではなく、規模の再見積もりによる中間停止である。段2（G10）には進んでいない。停止点1に到達した際には、上表の各行を完了時の実測で更新する。

### 13.3 検証済みの取り込み点と監査

今回のコードのコミットは **`1e3dfe50f`**（新規6本484行）。§12までを含む検証済みコードはすべて枝にコミット済み。未検証の Lean 下書きは残していない。

- 対象ビルド `/private/tmp/isw2-build-19.log`（2266 jobs）、`isw2-build-20.log`（2271 jobs）、最終の `isw2-build-21.log`（2434 jobs）はすべて終了コード0。最終の対象は `SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.LinearWeightTotalComparison` と、その新規依存を含む。各回 `with_build_lock.sh --wait 3600`、同じ worktree の整理券一枚、鍵は検証実行の間だけ。root ビルドはしていない。
- 一時監査 `/private/tmp/AuditISW2ThirtyEight.lean`、ログ `/private/tmp/isw2-audit-thirtyeight.log` は終了コード0。**新規38本・386宣言、標準三公理のみ**。今回6本の内訳は `[1, 22, 27, 14, 7, 16]`。sorry・独自公理0。
- 既存宣言・drafts・入口・公式監査の変更0。変更は自分の新規ファイルと報告のみで、他レーンとのファイル重複はない。`git diff --check` も成功。
- §10以前の13本を含む入口への登録は、指示どおり停止点1で調整役が行う。今回の中間停止を段1の完了と扱って登録・main取り込みを依頼するものではない。

追加登録候補（停止点1で調整役が登録）：

```text
SerrePositivity.HomologicalAlgebra.CoendAdditive
SerrePositivity.HomologicalAlgebra.LinearWeightRealization
SerrePositivity.HomologicalAlgebra.LinearFreeWeight
SerrePositivity.HomologicalAlgebra.LinearCoYoneda
SerrePositivity.HomologicalAlgebra.LinearCoYonedaNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.LinearWeightTotalComparison
```

この時点では§4の上限改定の検収を待つ。指定された型と最初の native 余錐の照合を残したまま次段へ進まない。

## 14. §5 の承認後：bar coend と元の単体的置換の接続（2026-11-12、a4d8cc83c）

main `6d71b170a` を専用枝に取り込み、§5の最後の上限4800行で再開した。§13の上限による停止はこの承認で解除された。今回の7本669行は、対象ビルドと一時監査を通して `a4d8cc83c` にコミット済み。

- `LinearWeightGenerators`：任意の線形重みの単位加群からの射を、元の coend の指定生成元へ送る。重みの全射と添字の全射に関する同じ関係式を示した。
- `BarWeightEvaluation`・`BarWeightEvaluationIso`：under 射列の先頭の構造射を作用させ、底の同じ射列の余積へ評価する。恒等射による標準持ち上げの生成元から逆射を作り、両合成が恒等射であることを証明した。
- `BarWeightRealizationNaturality`：標準持ち上げの制限の公式から、各次数の指定同型を、面と退化を含む全単体作用素に自然な同型にまとめた。
- `ReplacementWeightComparison`：元の先頭頂点単体による `replacementAugmentation` が、既存の固定された bar／標準重みの比較の coend の像と、指定同型の下で同じ射であることを証明した。bar 重み側の全複体と元の単体的置換の全複体を同じ評価で同定する。
- `ReplacementTotalHomotopy`：交代面複体と加法関手の標準同型を通して、前向きの射を元の `replacementAugmentation` の像に保った鎖ホモトピー同値を作った。非有界直和全複体への同じ鎖ホモトピー同値・擬同型を得て、全図式・全自然変換での自然比較 `replacementTotalAugmentationNatTrans` にまとめた。
- `TotalRowCochain`：一般の加法圏の整数次数の二重複体について、横次数aの同じ直和包含を次数aのcochainとして記録した。その微分は隣の行への横微分の後の同じ包含であることを、縦の二項の相殺で示した。二重複体の全射への自然性もある。有界性を仮定しない。§13.2の2で使う一般補題を依頼どおり `HomologicalAlgebra/` に置いた。

§13.2の1の接続（bar重みの各次数・全単体作用素と元の単体的置換、同じ増大の全複体の擬同型性）ができた。**native余錐との最初の照合の区切り、停止点1は依然未完**。次は§13.2の2の、既存Maurer–Cartan barの同じ微分・正規化との比較である。3・4への飛び越しや段2への着手はしていない。

検証：対象ビルド `/private/tmp/isw2-build-23.log`（2322 jobs）、`isw2-build-25.log`（2441 jobs）、`isw2-build-26.log`（2443 jobs）はすべて終了コード0。途中のbuild22・24は、全余積のinstance探索の時間制限で失敗した。複体の必要な宇宙の余積を添字ごとに既存instanceから局所的に指定し、上記の再ビルドで解消した。新しい数学的仮定は加えていない。

一時監査 `/private/tmp/AuditISW2FortyFive.lean`、ログ `/private/tmp/isw2-audit-fortyfive.log` は終了コード0。**新規45本・486宣言、標準三公理のみ**。sorry・独自公理0、既存宣言・drafts・入口・公式監査の変更0。鍵は各検証ごとに `--wait 3600` で一枚ずつ取得し、検証終了で返した。rootビルドはしていない。

検証済み累計は、共通7本424行、**3b-1の38本3104行**、計45本3528行。今回の669行は§13.2表の第一行58行（全行のcochainの一般公式）、第二行611行に数える。途中実測は第一行140行、第二行2555行、第三・第四行0行、§10以前の409行は別。停止点1で完了時の実測と差へ更新する。

追加登録候補（調整役が登録）：

```text
SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
SerrePositivity.HomologicalAlgebra.BarWeightEvaluationIso
SerrePositivity.HomologicalAlgebra.BarWeightRealizationNaturality
SerrePositivity.HomologicalAlgebra.TotalRowCochain
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementWeightComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementTotalHomotopy
```

## 15. native bar への具体的接続の準備と、最終上限による中間停止（2026-11-12）

### 15.1 §13.2の2で作った部品

§14の後、次の新規6本419行を構成した。実際のnative余錐の比較の完了ではない。

- `SmallStrictBarDiagram`（67行）：宇宙0の添字Jの strict な一点dg加群図式を、既存の二段ULiftの同型を通して、元の coherent bar の入力へ渡す。全単体は元の閉零射の列そのもので、係数環の宇宙を制限しない。各射列の先頭の係数と高次零成分を厳密に照合した。
- `StandardRowCochain`（68行）：元の単体次数nの複体から実現への次数−nの同じ標準成分を、添字延長の次数同型と全行の包含で構成した。その各成分とcochain微分を元の横微分で計算した。
- `SmallStrictBarColumns`（82行）：上の小さいstrict図式について、既存thetaの高次prefixのHom・shiftブロック・列が零であることを示した。同じthetaの各列を、元の面と先頭の射の一次列の符号付き和へ戻す。
- `SmallStrictBarTotalColumns`（88行）：射列の先頭の値を単体的置換の同じ因子へ入れ、上の次数−nの成分をshiftしたものから、既存barの各shifted因子の次数零のHom要素を構成した。一点dg加群の全Hom評価同型で戻し、既存graded余積のHom同値で一つの次数零要素にまとめた。各元の因子への制限は元の指定列そのもの。**この要素のMaurer–Cartan微分に対する閉性は、まだ証明していない**。従って、これをdg加群射や擬同型と呼ばない。
- `StandardRowBoundary`（57行）：添字延長の同じ次数同型の下で、二行間の横微分を元の交代面微分へ戻した。すべての面の順序・符号を保つ境界公式を証明した。
- `HomologicalAlgebra/UnsignedShiftCochain`（57行）：一般の加法圏のcochainについて、既存leftShiftの定数符号を打ち消す補助を作った。各成分は元の次数同型の後の同じ成分になり、同じcochain微分に両立する。零対象・有界性の追加仮定は不要。既存のleftShiftを変更していない。

### 15.2 現在の不足と見積もりの修正

§13.2の1は§14までで接続できたが、同節の2は以下の三つを残す。

1. 上の実際の列族のMaurer–Cartan微分に対する閉性を、同じthetaの面・prefixの式と全行の境界公式で示すこと。
2. 得られる**同じ射**の各次数の同型を、既存graded余積の各shifted因子と直和全複体の各因子の対応から示し、複体の同型へまとめること。
3. 既存Maurer–Cartan barの正規化射影・補正包含・ホモトピーとの比較を、元の射で照合すること。通常のMoore正規化の擬同型性だけでは、この段を置き換えられない。

その後に§13.2の3の半自由出力分解、同じD(A)の指定join余錐と標準脚・高次成分の輸送、4の全パラメーターでの族への接続が残る。既存 `SemifreeBarVertexCriterion` の頂点同型の存在だけを最終入口の代用にはしない。

§13の第二行の残り400〜650行の見積もりは、coendの同定と、既存Maurer–Cartan barとのこの具体的な接続を十分に区別していなかった。§14で前者に611行を使い、後者の準備にも今回の294行が必要になった。ここが前回の見積もりの不足である。今回の残り400〜650行は、上記1〜3そのものに対する見込みであり、さらに未実装の補題を仮定した宣言で済ませる見込みではない。

現在の実測は共通7本424行、**3b-1の44本3523行**、計51本3947行。§13.2表の現在の項目別の実測と残りは次のとおり。残りは設計上の見込みで、実測とは分けている。

| §13.2 の項目 | §10の追加見込み | 現在の途中実測 | 残りの見込み | 完成時の見込み | 元の上端との差の見込み |
| --- | ---: | ---: | ---: | ---: | ---: |
| 全単体次数の包含・微分・退化・指定余錐の高次成分 | 500〜750 | 265 | 167〜317 | 432〜582 | −318〜−168 |
| bar／重み・直和全複体の具体的比較・非有界擬同型 | 850〜1250 | 2849 | 400〜650 | 3249〜3499 | +1999〜+2249 |
| 半自由出力分解・native余錐の輸送・同じ脚 | 500〜750 | 0 | 500〜750 | 500〜750 | −250〜0 |
| 全パラメーターの関手同型・射・指定余錐 | 250〜350 | 0 | 250〜350 | 250〜350 | −100〜0 |
| **追加計（§10以前の409行を除く）** | **2100〜3100** | **3114** | **1317〜2067** | **4431〜5181** | **+1331〜+2081** |

§10以前の409行を含めると、**3b-1完成時の見込みは4840〜5590行（約4800〜5600行）**。現在のコードの明らかな重複や不要な一般化を取り除けば最終上限4800行に収まる、という根拠は得られていない。共通部分へ付け替えて数えたり、元の同じ射・全関手・指定錐の要件を弱めたりはしない。

従って[指示書§1・§5](inf-supply-w2.md)の「超えそうなら止める」と、§5が最後の上限改定であるという指示に従い、**ここで新規実装を停止する**。停止点1の完了ではなく、最終上限による中間停止である。最初のnative余錐との照合も未完で、段2（G10）には進んでいない。上限内で閉じたという扱いにせず、検証済み部品と具体的な残件を調整役へ返す。

追加登録候補（今回の停止は段1の検収とは別）：

```text
SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowBoundary
```

引き継ぐときの注意：`SmallStrictBarTotalColumns` の列族は**非正規化graded bar**からのものである。既存 `CoherentBar/NativeColumns` の `dgCoherentBarNativeColumn_degenerate` は、正規化されたnative列が退化射列で零になることを要求する。従って、今回の `standardRowCochain` の生の列を、そのままnative join余錐の高次成分と宣言してはいけない。実際の閉射を作った後、既存の正規化射影・補正包含を通した同じ列を指定し、第零列と高次列を照合する必要がある。

残る最初の宣言の型は、`G := smallStrictBarDiagram A F`、`T := smallStrictBarTotalTarget A F` として、`moduleHom A PUnit (dgCoherentBarModuleUnconditional A PUnit G) T` の次数零の要素と、その**同じ要素**の微分が零であること。その要素は、今回の `smallStrictBarTotalGradedElement` を既存の `dgCoherentBarHomDegreeEquiv` で戻して指定する。閉性を追加入力として受け取った比較を最終定理にはしない。続いて、その閉射の一点評価が `directSumTotalFunctor` の元の射列の模型との複体同型になること、正規化後の射と `replacementAugmentationTotalHomotopyEquiv` の前向きの射が同じ比較を与えることが必要である。

### 15.3 検証と確定した取り込み点

今回6本のコードのコミットは **`ac36b96ea`**。§14の `a4d8cc83c` と合わせて、main `6d71b170a` からの新規13本1088行をすべて検証・コミットした。未検証のLean下書きは残していない。

- 対象ビルド `/private/tmp/isw2-build-27.log`（3824 jobs、`SmallStrictBarDiagram`・`StandardRowCochain`）、`isw2-build-28.log`（3829 jobs、`SmallStrictBarColumns`・`SmallStrictBarTotalColumns`・`StandardRowBoundary`・`UnsignedShiftCochain` とその依存）はすべて終了コード0。個別検査からの公開import・依存型の照合も通常のモジュール単位で確かめた。
- 一時監査 `/private/tmp/AuditISW2FiftyOne.lean`、ログ `/private/tmp/isw2-audit-fiftyone.log` は終了コード0。**累計新規51本・556宣言、標準三公理のみ**。sorry・独自公理0。前段の47本の監査（`isw2-audit-fortyseven.log`、513宣言）も成功した。
- 各回 `with_build_lock.sh --wait 3600` で一枚ずつ待機し、ビルドまたは監査の実行終了で鍵を返した。最後のビルドと監査には先行一括束の順番待ちがあったが、待ちを理由に検証を省略していない。rootビルドは行っていない。
- 既存宣言・drafts・入口・公式監査の変更0。変更は新規数学ファイルと自分の報告だけ。他レーンとのファイル重複0。`git diff --check` は成功。

停止の理由は検証の失敗や鍵の待ちではなく、§15.2の最終上限超過の見込みである。停止点1を完了したとは報告せず、指定された型・同じ射・高次成分の残件を保持したまま、ここで調整役の次の判断を待つ。

## 16. §6と新しい規模規則による再開：列の微分と全単体境界（2026-11-12、437d921b1）

main の§6を `90388ad14`、新しい規模規則を `ae47e543e` で専用枝へ取り込んだ。§15の中間停止は承認により解除され、段1を継続している。3b-1は明示された5600行を維持する。新しい上限は共通2000、3b-2 8400、3b-3 8400、3b-4 9200行。段0上端の半分に達したときの報告は停止せず行う。3b-1の途中実測は既報のとおりで、停止点1では§13.2表を完了時の実測へ更新し、G10の見込みも実測を踏まえて出し直す。

### 16.1 同じ列の微分・境界の確定（新規5本338行）

- `SmallStrictBarTotalValues`：以前の各shifted因子の列を一点で評価し、元のシフト前の列を符号を変えずにshiftしたものと厳密に照合した。シフト前の各成分は同じ射列の余積因子の包含の後の標準行の包含。
- `SmallStrictBarTotalDifferential`：同じ列の微分の一点評価は、シフト前の同じcochain微分を符号を変えずにshiftしたもの。全Homの評価鎖写像の可換式から証明した。
- `StandardRowDifferential`：全行の成分公式と延長の次数同型の境界式から、標準列の微分が元の交代面微分と一つ下の標準列の合成になることを、cochain全体の等式で示した。直和包含の証明引数での依存型の書き換えを避け、同じ `ιTotalOrZero` を介して照合した。
- `SmallStrictBarUnshiftedBoundary`：零次の標準cochainは既存 `standardZeroLeg` の同じcochainであり、零次のシフト前のbar列は閉じている。正次数の列の微分は、射列の同じ因子を元の単体的置換の境界に入れた後の標準列になる。
- `HomologicalAlgebra/SimplicialReplacementBoundary`：一般の加法圏で、各元の射列上の交代面境界を、すべての面に対する先頭の射と同じ面の包含の符号付き和へ戻した。

対象ビルド `isw2-build-29.log`（3828 jobs）、`isw2-build-30.log`（3829 jobs）、`isw2-build-31.log`（2388 jobs）、`isw2-build-32.log`（3834 jobs）は成功。一時監査で新規ファイルの無名local instanceが既存 `ReplacementWeightComparison` の生成名と衝突することを検出した。新規2本のlocal instanceに固有名を付け、影響する新規ファイルを `isw2-build-33.log`（3834 jobs）で再ビルドして解消した。数学的仮定と既存の宣言は変更していない。

一時監査 `/private/tmp/AuditISW2FiftySix.lean`、成功ログ `/private/tmp/isw2-audit-fiftysix-recheck.log`：**累計新規56本・590宣言、標準三公理のみ**、終了コード0。sorry・独自公理0。全5本を **`437d921b1`** にコミットした。既存宣言・drafts・入口・公式監査は未変更。鍵は各検証ごとに `--wait 3600` で一枚ずつ取得し、実行後に返した。

検証済み累計：共通7本424行、**3b-1の49本3861行**、計56本4285行。今回338行は§13.2表の第一行74行（全標準列の微分）、第二行264行に数える。途中実測は第一行339行、第二行3113行、第三・第四行0行、§10以前409行は別。native barへの比較射全体の閉性・複体の同型・指定余錐への輸送は未完で、最初のnative余錐の区切りと停止点1にはまだ到達していない。

### 16.2 指定native余錐を直接使う短い経路の検討（紙、未実装）

§6の確認を先に行う。既存 `CoherentBar/NativeColimit` は、正規化barの**指定された** `dgCoherentBarNormalizedNativeCoconeUnconditional` とその余極限性を供給する。`NativeCoconeFamily` の `dgCoherentBarNativeCoconePoint_column` は、その全単体の係数を同じ `dgCoherentBarNativeColumn` と照合し、`dgCoherentBarNativeCoconePoint_hom` は対応するHom要素が同じ単位であることを示す。従って、正規化barから計算済みの頂点への同じ閉射が得られれば、既存 `dgCoherentBarCoconeHomSpaceIsoUnconditional` を通して指定余錐の全高次成分を輸送する候補がある。join余錐のHA方程式・退化整合性を一から再構成する経路は省ける可能性がある。

この短い候補でも、現在作っている比較射の閉性と、計算済み直和全複体への同じ射の比較は必要。非正規化barのgraded列をnative列と取り違えたり、頂点同型の存在だけで同じ標準脚を得たことにはできない。正規化の補正包含を通した射と第零のnative列の合成が、今回照合した標準脚そのものになることを確認する。全高次成分は、その同じ閉射を既存native列へ作用させたものとして指定する候補である。

また `NativeColimit` の最初の値域は全右dg加群のdg nerveである。D(A)へ移す段階では既存の射影的bar・半自由出力の比較を使い、単なる擬同型を全右dg加群のdg nerveの可逆辺とみなさない。この経路を継続して調べ、上限超過の見込みで止める必要が生じた際には、短縮できた部分と残る比較を具体的に追記する。数字だけによる中間停止は行わない。

追加登録候補（調整役が登録）：

```text
SerrePositivity.HomologicalAlgebra.SimplicialReplacementBoundary
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarUnshiftedBoundary
```

## 17. 同じ実 bar 比較の閉性と、指定 native 余錐を直接使う経路の再点検（2026-11-12）

### 17.1 段1の途中実測と確定した証明

新しい規模規則を適用し、3b-1は明示済みの5600行、共通2000行を基準とする。半分の時点の非停止報告は既報のとおりで、その後も途中実測を報告しながら進めた。以下は停止点1の完成報告ではなく、同じ比較射の閉性まで進めた区切りである。

§16以後の新規9本987行は、いずれも§13.2表の第二行に数える。共通部分や段2へ付け替えていない。

- `SmallStrictBarBlockCoefficients`・`SignedShiftBlockValues`：同じ面の係数が単位、最初のprefixの係数が元の先頭の射であることを保持し、元のshiftブロックの一点評価と外側の符号を計算した。
- `SmallStrictBarBoundarySum`・`SmallStrictBarTotalComposition`：元の交代面境界を全ての面の和へ分け、比較を余積因子へ制限した値と後合成の値を照合した。同じgraded要素を元のMC barの次数零へ戻す `smallStrictBarTotalElement` も固定した。
- `SignedShiftBlockComposition`・`SmallStrictBarSignedColumns`：正次数の面の列と最初のprefixの列の後合成を、それぞれ一つ下の同じ列、同じ先頭の射の後の列のシフトと同定した。高次prefixを残す仮定は追加していない。
- `SmallStrictBarBoundaryFaces`：先頭を保つ各面の境界項を同じ面の列へ戻し、最初のtailが第零面と同じ添字であること、第零面が元の先頭の射の後の列であることを照合した。次数の異種等号から、同じ次数へのシフト後の等式を得た。
- `SmallStrictBarThetaValues`：元のthetaの符号付き有限和を比較へ送る値が、元の同じ列の微分のシフトであることを、全正次数で証明した。
- `SmallStrictBarTotalClosed`：零次の閉性と正次数の全列の等式を直和全体へ戻し、`smallStrictBarTotalElement_closed` を証明した。これは**以前指定した同じ要素の微分が零**という宣言であり、閉性を入力としていない。`smallStrictBarTotalHom` はその要素から得る厳密な射で、`smallStrictBarTotalHom_val` が同じ閉零要素へ戻る等式を記録する。

従って§15.2の「最初の残件」であった実MC barからの同じ要素の閉性は閉じた。一方、この射の複体同型・鎖ホモトピー同値はまだ証明していない。native余錐の最初の照合、全関手比較、停止点1は未完で、G10には未着手。

### 17.2 §6の紙の検討：NativeColimitから直接進む経路

数字だけで止める前に、§16.2の候補を既存の宣言の型と照合した。短い経路は次のように具体化できるが、完成した証明とは区別する。

1. `CoherentBar/Retract/DeformationRetract` の `dgCoherentBarNormalizedModuleInclusionUnconditional` を、今回の **同じ** `smallStrictBarTotalHom` の前に合成する。その後に、既に前向きの射を固定している `replacementAugmentationTotalHomotopyEquiv` を合成すれば、正規化barから元の実現への候補の射が得られる。正規化のretractや補正包含を作り直す必要はない。
2. `CoherentBar/NativeColimit` の `dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit` と、`dgCoherentBarCoconeHomSpaceIsoUnconditional` を使い、その同じ閉射に対応する指定join余錐を取る。`NativeCoconeFamily.dgCoherentBarNativeCoconePoint_column` および `NativeHomComposition.dgCoherentBarNativeColumn_compose_eq_coordinates` を使えば、全高次成分を同じnative列への後合成として指定できる。HAのjoin方程式と退化整合性を一から作る経路は不要。
3. ただし `NativeColimit` の頂点は**正規化bar**であって、今回の直和全複体ではない。今回の閉射が可逆辺になることは、閉性だけからは従わない。まず一点評価の各次数で、元の余積因子を同じ直和全複体の因子へ送る射が同型であることを証明する必要がある。候補は、各次数のshift同型、余積の並べ替え、`totalDesc`・`ι_totalDesc` による逆射。同型の前向きの射を今回の `smallStrictBarTotalHom` の一点評価と照合する。通常のMoore正規化の同値をこの射へ無条件に置き換えない。
4. 第零の標準脚は、補正包含を通したnative第零列と今回の射の合成について厳密に確認する。生の標準列は退化射列でも一般に零ではないので、生の列をそのままnative列にする短縮は不可。高次列は2の後合成で指定できても、第零列の等式と同じ頂点の比較は残る。
5. 値域は最初、全右dg加群のdg nerveである。D(A)へは既存の射影的bar・半自由模型の比較と `SemifreePointComparison.semifreePointEquivalence` を使う。全右dg加群のdg nerveで単なる擬同型を可逆と宣言することはできない。
6. 全パラメーターの比較も残る。既存 `exists_colimitCoconeFamily_extension` は、**既に指定された余錐の部分族を保つ**延長を供給する。そこから任意に選んだapex族が具体的な直和全複体の全関手と一致する、という結論は出ない。`exists_colimitCocone_edge` も下方の図式の辺と余錐の端点を固定するが、具体的な全複体の射をapexの辺へ厳密に指定する欄ではない。同じ比較の射への自然性と全関手の `FunctorIso`、その指定余錐との両立を別に供給する必要がある。対象ごとの頂点の選択やHo上の自然同型を代用しない。

この経路はnative余錐自体の再構成を省き、第三行の残りを従来の500〜750行から350〜550行へ下げる候補になる。一方、3〜6の未実装の接続を0行とする根拠はない。既存の指定余錐から直接に標準脚を同定するだけで、同じ複体比較と全関手の欄まで自動的に閉じる短縮は確認できなかった。

### 17.3 残件の見込みと規模による中間停止

| §13.2の項目 | §10の追加見込み | 今回までの実測 | 残りの見込み | 完成時の見込み | 元の上端との差 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 全単体次数の包含・微分・退化・指定余錐の高次成分 | 500〜750 | 339 | 0（残るnative成分照合は第三行へ計上） | 339 | −411 |
| bar／重み・直和全複体の具体的比較・非有界擬同型 | 850〜1250 | 4100 | 250〜400 | 4350〜4500 | +3100〜+3250 |
| 半自由出力分解・native余錐の輸送・同じ脚 | 500〜750 | 0 | 350〜550 | 350〜550 | −400〜−200 |
| 全パラメーターの関手同型・射・指定余錐 | 250〜350 | 0 | 350〜550 | 350〜550 | 0〜+200 |
| **追加計（§10以前の409行を除く）** | **2100〜3100** | **4439** | **950〜1500** | **5389〜5939** | **+2289〜+2839** |

§10以前409行を含む3b-1の実測は **58本4848行**、共通7本424行を含む全数学は **65本5272行**。短いnative経路を使った場合でも完成時の見込みは **5798〜6348行（約5800〜6350行）** となり、承認済み5600行を超える見込み。第二行の増加は、元のMC barのshiftブロック・端点・微分の符号を、元の全単体列と同じ厳密な射へ戻す証明が当初の幅に収まらなかったことによる。第四行は、任意のapex族の選択では具体的な全複体の全関手比較にならない点を再評価した。

[指示書§6と最新の規模規則](inf-supply-w2.md)、`coordination.md` §2の「超えそうなときは、検証済みの分をコミットしてから報告して止める」に従い、検証の確定後、**ここで新規実装を中間停止する**。これは停止点1の完了報告ではない。上記は未実装部分の見込みであり、最小必要行数の証明ではない。共通への付け替えや全関手・指定錐の要件の弱化はしない。停止点1に到達した時点で§13.2表を完成実測へ更新し、G10の見込みを出し直すという指示は未消化のまま保持する。

### 17.4 今回の追加登録候補と検証記録

§16の5本とは別に、今回の9本を以下に列挙する。入口と公式監査は調整役が登録する。

```text
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBlockCoefficients
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundarySum
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalComposition
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockComposition
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarSignedColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundaryFaces
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarThetaValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalClosed
```

前8本のコードは `e664e0c80`（4本321行）、`b9f39f34e`（2本263行）、`c017fc56b`（1本138行）、`8aa62ef08`（1本139行）にコミット済み。対象ビルド `isw2-build-35.log`（3841 jobs）、`isw2-build-36.log`・`37.log`（3836 jobs）、`isw2-build-38.log`（3837 jobs）、`isw2-build-39.log`（3846 jobs）はすべて終了コード0。`37`は局所heartbeat上限の理由をコメントへ補った再ビルド。§16以降の累計一時監査は60本627宣言、62本657宣言、63本678宣言、64本691宣言で、いずれも標準三公理のみ、sorry・独自公理0。

各回 `with_build_lock.sh --wait 3600` で整理券を一枚ずつ出し、ビルドまたは監査の実行終了で鍵を返した。一括レーンおよび他の実装レーンの順番待ちは、検証を省略する理由にしていない。rootビルドは行っていない。既存宣言・drafts・入口・公式監査の変更0、他レーンとのファイルの重複0。変更は新規数学ファイルと自分の報告のみ。

最後の `SmallStrictBarTotalClosed` は対象ビルド `/private/tmp/isw2-build-40.log`（3848 jobs、終了コード0）を通し、**`170f0a4df`** にコミットした。一時監査 `/private/tmp/AuditISW2SixtyFive.lean`、ログ `/private/tmp/isw2-audit-sixtyfive.log` は終了コード0、**累計65本・707宣言、標準三公理のみ**。sorry・独自公理0。監査は65モジュールの宣言をモジュール番号で抽出して依存公理を調べ、各モジュールの宣言数が非零であることも確認している。ソースの実ファイルの再集計は65本5272行、重複・欠落なし。`git diff --check` は成功。

以上の検証済みコードを全てコミットし、未検証のLean下書きは残していない。**停止点1ではなく、§17.2の短い経路を検討した上での規模による中間停止**として、調整役の判断を待つ。停止理由は鍵待ちではない。次に再開する最初の未実装の型は、`smallStrictBarTotalHom` の一点評価を前向きの射とする複体同型（または同じ射の鎖ホモトピー同値）である。

## 18. §7による再開：同じ一点評価を前向きの射とする複体同型（2026-11-12、cc27ce728）

main `b668a7aef` の§7を `8ed15f6ae` で専用枝へ取り込んだ。3b-1の上限を約6500行とし、§17の中間停止を解除して、承認された短い経路で段1を継続している。停止点1では§13.2表を完成時の実測へ更新し、3b-2〜3b-4の見込みを実測から出し直す。G10で再利用できる加法的coend・線形co-Yoneda・非有界二重複体・shiftの符号の部品もその報告に挙げる。後続段の範囲をこちらで削らない。

### 18.1 複体同型の構成と同じ射の照合

新規5本411行を **`cc27ce728`** にコミットした。

- `RealizationDegreeCofan`：各全次数qで、元の行 `(X_n)^(q+n)` の標準包含が余積であることを証明。逆向きの射は `realizationDegreeDesc` として `totalDesc` で定義し、非正の横次数を自然数へ戻す次数同型、正の行の零性から制限公式と一意性を示した。内部次数の有界性は不要。
- `ShiftedCoproductDegreeCofan`：元の複体の余積を次数で評価し、shiftの次数同型とULiftによる射列の添字変更を同時に扱う。係数側の必要な余積を型に明記し、このレーンの宇宙0の射列では既存インスタンスで供給する。
- `SmallStrictBarDegreeCofan`：行の余積と射列ごとのshifted因子の余積を `Cofan.isColimitTrans` で合成。元の比較列の成分公式により、その脚が以前指定した `smallStrictBarTotalColumn` の一点評価そのものであることを照合した。
- `SmallStrictBarTotalHomValues`：厳密な射 `smallStrictBarTotalHom` の一点評価の各成分を、同じgraded比較と照合し、元の射列の各因子への制限も同じ比較列になることを示した。MCによる微分の変更で台の成分を取り違えていない。
- `SmallStrictBarTotalIso`：始域の各次数の元の余積と、上の標的の余積を比較。`smallStrictBarTotalDegreeIso_hom` は、その同型の前向きの射が **元の一点評価の同じ成分** であることを述べる。`smallStrictBarTotalDegreeIso_inv` は逆射を、totalDescで構成した標的の余積からの射として指定する。これらから `smallStrictBarTotalPointIso` を構成し、`smallStrictBarTotalPointIso_hom` で前向きの複体射が **smallStrictBarTotalHomの一点評価そのもの** であることを証明した。

これで§17の再開時に指定された最初の複体同型は閉じた。native余錐自体は新しく構成せず、次は既存 `dgCoherentBarNormalizedModuleInclusionUnconditional` を前に合成し、既存retractとこの同型を接続する。最初の「一つのstrict Δᵒᵖ図式のnative余錐・標準脚・射」の区切りはまだ未完。段2には進んでいない。

### 18.2 検証と途中実測

- `/private/tmp/isw2-build-41.log`：`RealizationDegreeCofan`、2387 jobs、終了コード0。
- `/private/tmp/isw2-build-42.log`：残る4本とその依存、3853 jobs、終了コード0。
- `/private/tmp/isw2-build-audit-43.log`：必要な既存 `CoherentBar/Retract/DeformationRetract` の対象ビルド（3814 jobs）と、一時監査 `/private/tmp/AuditISW2Seventy.lean`。終了コード0、**累計70本・782宣言、標準三公理のみ**。sorry・独自公理0。既存のretractのソースは変更していない。

全て `with_build_lock.sh --wait 3600` で整理券を一枚ずつ取り、各実行は30分以内。最後の枠は必要な対象ビルドと監査だけを続けて実行し、終了で鍵を返した。rootビルドは行っていない。

検証済みの累計は、共通7本424行、**3b-1の63本5259行**、全体70本5683行。今回411行は§13.2の第二行へ計上し、同表の途中実測は第一行339、第二行4511、第三・第四行0、§10以前409行は別。既存宣言・drafts・入口・公式監査の変更0、他レーンとのファイル重複0。個別検査中の正規化接続とnative判定の下書きは、この検証済みコミットへ含めていない。

追加登録候補：

```text
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.RealizationDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ShiftedCoproductDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalHomValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalIso
```


## 19. 同じ元の実現を頂点とする指定余錐の余極限性（2026-11-12、7e17c2b1e・5668d9c9a）

### 19.1 正規化との接続と同じ join 余錐

新規4本312行を **`7e17c2b1e`** にコミットした。

- `SmallStrictBarNormalizedComparison`：既存の補正包含と射影・retractホモトピーを一点評価し、§18の同じ複体同型へ合成した。正規化barから元の非正規化bar、単体的置換の全複体への合成の前向きの射を保持する。
- `ClosedMapCocone`：既存 `dgCoherentBarCoconeHomSpaceIsoUnconditional` の逆で、指定した閉零射を同じ終点の実際のjoin余錐へ送る。頂点の等式と、Hom空間へ戻したcycleが最初に指定した同じ閉射であることを証明。nativeのHA成分を作り直していない。
- `StrictSimplicialBarRealization`：正規化比較と既存 `replacementAugmentationTotalHomotopyEquiv` を合成し、**元の図式の直和全複体**を頂点とする閉射・join余錐を指定。一点評価の鎖ホモトピー同値の前向きの射が、その閉射の一点評価と同じことも照合した。
- `CosliceInvertibleLegInitial`：一般の準圏の一点図式で、実際の脚が可逆なら、その同じjoin余錐がcosliceの始対象になる。恒等余錐からの辺と左ファイブレーションの可逆辺反映を使用。Kerodon 4.7（Tag 05EA）と4.4.2（Tag 019F）の配置に置いた。

### 19.2 同じ余錐の余極限性

新規3本261行を **`5668d9c9a`** にコミットした。

- `PointHomSpaceVertexCycle`：既存の一点余錐Hom空間同型の零単体と、既存 `cosliceFiberVertexToEdge` の実際の辺のcycleを照合。端点の等式によるcastの値と、pinched Homの全係数を保っている。
- `ClosedMapCoconeInitial`：指定閉射が加群H⁰で可逆なら、上記の**同じ指定余錐**が余極限であることを証明。余錐の一点比較の脚のcycleが最初の閉射そのものであることを先に示し、上のcoslice補題と既存のHom族・fiber比較で余極限性を戻す。別の余錐を選んで、その存在だけを返していない。
- `StrictSimplicialNativeColimit`：一点評価と通常の複体ホモトピー圏の比較の同値は可逆射を反映する。元の実現への指定閉射の一点評価が既に鎖ホモトピー同値であることから、加群H⁰で同じ射が可逆と示し、**`strictSimplicialBarRealizationCocone_isColimit`** を閉じた。

ここで得た余極限性の値域は **全右dg加群のdg nerve** である。一般の擬同型をそこで可逆としていない。D(A)の射影的・半自由模型への輸送、標準脚の最終等式、全パラメーターの指定余錐・実現関手との比較は残る。したがって**停止点1でも、最初の標準脚・射までの区切りでもない**。段2へは進んでいない。

### 19.3 検証・実測・登録候補

- `/private/tmp/isw2-build-audit-44.log`：4本の対象ビルド4275 jobsと一時監査 `AuditISW2SeventyFour.lean`、終了コード0。累計74本835宣言、標準三公理のみ。
- `/private/tmp/isw2-build-audit-45.log`：3本の対象ビルド5542 jobs、次の頂点照合に必要な既存 `StrictComparison.NativeVertexModuleMaps` の対象ビルド4544 jobs、一時監査 `AuditISW2SeventySeven.lean`。終了コード0、**累計77本843宣言、標準三公理のみ**。sorry・独自公理0。

両回とも `with_build_lock.sh --wait 3600`、整理券一枚、鍵はビルドと監査の実行中だけ、一回30分以内。rootビルドなし。既存宣言・drafts・入口・公式監査の変更0。他レーンとのファイル重複0。

検証済み累計は、共通7本424行、**3b-1の70本5832行**、全体77本6256行。§13.2の途中実測は第一行339、第二行4511、第三行573、第四行0、§10以前409行は別。この節の追加573行を第三行へ計上した。未検証の頂点照合2本は、この検証済みコミットと数には含めていない。

追加登録候補（§18の5本に加えて）：

```text
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarNormalizedComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCocone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialBarRealization
SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.CosliceInvertibleLegInitial
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceVertexCycle
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeInitial
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialNativeColimit
```
