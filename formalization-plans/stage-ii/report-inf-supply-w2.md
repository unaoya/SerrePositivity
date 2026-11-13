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


## 20. 頂点列の厳密な固定と、6500行に対する残件の再評価（2026-11-12）

### 20.1 頂点列の照合

新規2本159行を **`6ba1003fa`** にコミットした。個別検査 `/private/tmp/ISW2NativeVertexInclusion.lean` は終了コード0。個別検査は新規2本を同じソースから連結し、既存の依存をimportした。検査途中の単位評価と余積の型aliasの不一致は、単位の評価と零shift同型の逆則を明示して修正した。

- `Retract/VertexProjector`：既存の安定化の制限を零単体の最初の一段へ戻し、`VertexBoundary` の境界消滅から元の単位の制限と等しいことを証明。さらにMC後の同じ自己射の成分が、元の頂点の余積包含を厳密に固定することを示す。恒等射へのホモトピーだけで代用していない。
- `Retract/NativeVertexInclusion`：既存の零次元層の包含とnative頂点列の式を使い、実閉射影・補正包含の合成を同じ安定自己射へ戻す。`dgBarNativeVertexModuleMap_inclusion_f` は、native頂点列と補正包含の合成の一点でない任意の評価・各次数の成分が、**零shift同型の逆と元の余積包含の合成**に等しいと述べる。

この二本だけで、最終的なjoin余錐の脚と元の `standardZeroLeg` の等式を閉じたとはしていない。次の接続には、同じ閉射から余錐へ戻す比較の脚の抽出、上記の式と `smallStrictBarTotalHom_point_ι`・元の増大の零行公式との合成が残る。

### 20.2 短い経路の再確認

規模の数字だけで止める前に、§17.2の既存指定余錐を使う短い経路を実装と照らし直した。

1. **短い経路は使用済み**。元のnative列と正規化barの余錐Hom空間同型をそのまま使い、同じ閉射を逆像へ送っている。新たなBarratt–Eccles作用・hammock・native HA方程式・新しい正規化barは作っていない。元の `smallStrictBarTotalHom` の一点評価を前向きの射とする同型、および元の実現への同じ比較の余極限性は§18〜§19で閉じた。
2. **標準脚の短縮**。零単体では安定作用素が厳密に恒等になるので、今回の二本で、補正包含の全成分を展開する長い経路を避けられる。この後の脚・増大の照合を100〜180行と見積もる。高次成分を生の標準列へ取り替える短縮はしない。退化列で生の列は一般に零ではない。
3. **D(A)への輸送**。`ProjectiveBarNativeCocone` の `fullInclusionLift`・`dgBarCocone_vertices`・`FullColimitReflection` と、射影的模型・半自由模型の既存の同値を再利用する。今回の同じ比較の鎖ホモトピー同値から、元の実現の射影性を戻し、**今回の同じ余錐全体**を充満部分圏へ上げて輸送する必要がある。元の正規化barのapexだけを今回の全複体と同一視して済ませない。この接続を140〜240行と見積もる。
4. **全関手**。`StrictSemifreeColimitFamily` は全nerve上のnative余錐族を既に返すが、そのapexは任意の切断であり、具体的な直和実現の射を保持する比較はまだ与えない。`exists_colimitCoconeFamily_extension` も、部分パラメーターで指定した余錐は保持するが、未構成の具体的実現関手に沿う全ての射・高次成分を自動で固定するものではない。`isColimitCone_of_pointwise` は**既に同じ全関手上の余錐がある**ことを入力とする。したがってこれらを組み合わせただけで、具体的実現との全関手同型が閉じたとする短縮は確認できない。比較閉射とnative列のstrictな自然性を全パラメーターへ組み、指定余錐族と照合する残件を従来と同じ350〜550行と見積もる。これは対象ごとの同型から高次の自然性が自動で従うという主張ではない。

### 20.3 §13.2表の途中実測と残件

| §13.2の項目 | §10の追加見込み | 今回までの実測 | 残りの見込み | 完成時の見込み | 元の上端との差 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 全単体次数の包含・微分・退化・指定余錐の高次成分 | 500〜750 | 339 | 0（nativeの最終照合は第三行へ） | 339 | −411 |
| bar／重み・直和全複体の具体的比較・非有界擬同型 | 850〜1250 | 4511 | 0 | 4511 | +3261 |
| 半自由出力分解・native余錐の輸送・同じ脚 | 500〜750 | 732 | 240〜420 | 972〜1152 | +222〜+402 |
| 全パラメーターの関手同型・射・指定余錐 | 250〜350 | 0 | 350〜550 | 350〜550 | 0〜+200 |
| **追加計（§10以前409行を除く）** | **2100〜3100** | **5582** | **590〜970** | **6172〜6552** | **+3072〜+3452** |

§10以前409行を含む3b-1の途中実測は **72本5991行**、共通7本424行を含む全数学は **79本6415行**。§18以降の増加1143行は、第二行411行、第三行732行である。§17の第二行残り250〜400行に対して実測411行で+11行、第三行残り350〜550行に対して既に732行で+182行、さらに脚・D(A)の接続が残った。増加の中心は、指定余錐の実際の一点の脚を同じcycleへ戻し、元の終点と零shift同型を厳密に保持する接続が、以前のnative接続の幅に収まらなかったことである。

現時点の完成見込みは **6581〜6961行（約6600〜7000行）** となり、[指示書§7](inf-supply-w2.md) の約6500行を超える見込み。上の幅は設計上の見込みであって、最小必要行数の証明ではない。共通部分への付け替えや、全関手・同じ指定余錐の要件の弱化はしない。

規模規則に従い、上記の二本の対象ビルド・監査を確定し、検証済みをコミットした。**ここで新規実装を中間停止する。**これは**停止点1の完了報告ではない**。停止理由は鍵待ちではない。停止点1で§13.2を完成実測へ更新し、3b-2〜3b-4を実測に基づき出し直し、G10へ再利用できる道具を挙げるという指示は保持する。後続段の範囲はユーザーの判断に委ね、こちらでは狭めない。

### 20.4 対象ビルド・監査の確定記録

`/private/tmp/isw2-build-audit-46.log`：新規二本の対象ビルド4632 jobsと一時監査 `/private/tmp/AuditISW2SeventyNine.lean` はいずれも終了コード0。**累計79本845宣言、標準三公理のみ**。sorry・独自公理0。対象ソース79本を重複・欠落なしで再集計し、6415行（共通424、3b-1 5991）を確認した。

`with_build_lock.sh --wait 3600` の一枚の整理券で待ち、実行は30分以内。対象ビルドと監査の終了で鍵を返した。rootビルドなし。`git diff --check` は成功。数学の追加は新規ファイルだけで、既存宣言・drafts・入口・公式監査の変更0、他レーンとのファイル重複0。コードコミットは **`6ba1003fa`**。未検証のLean下書きは残していない。

追加登録候補（対象ビルド・監査を確定済み）：

```text
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.VertexProjector
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.NativeVertexInclusion
```


### 20.5 G10への再利用の暫定メモ（完了時の再見積もりではない）

停止点1の完了時の見積もりと区別して、現在の部品の再利用範囲を残す。

- 加法的coendと線形co-Yonedaは、今回のbarから元のΔᵒᵖの複体への重み比較を閉じた。G10の極限にはend側の比較が必要で、同じcoend定理をそのまま積へ適用したとはしない。係数の表現可能性・添字の比較・Homによる双対の設計には再利用できる。
- 非有界な二重複体の水平鎖ホモトピーの成分と符号の証明は、内部次数の有界性を使っていない。G10の積全複体では、直和のdescを使った最終の組立てをそのまま引用できず、積のlift・各射影で検査する版が必要。成分補題は再利用し、積全複体の主張を証明済みとはしない。
- shiftブロックの符号、`unsignedLeftShift` の評価公式、shiftの次数同型は、strictな列から全複体への成分の比較に再利用可能。ただしG10側の余単体次数・積の規約で符号を照合する。今回のbar固有のprefix・faceの証明を丸ごと流用できるとは数えない。
- 同じ閉射の可逆性から同じ指定余錐の余極限性を得る今回の接続は、G10の同じ頂点・脚を保つ極限側で何を双対化する必要があるかを明確にした。今回の余極限判定そのものを、極限判定として無証明で使わない。

3b-2〜3b-4の正式な再見積もりは、まだ未完の3b-1を完成実測と呼んで出さず、停止点1の報告で更新するという指示を保持する。


## 21. IS-W2 §8：図式ごとの停止点1（2026-11-12）

### 21.1 承認された範囲と今回の完了内容

main `95c8f5c8c` の指示書§8を **`0300478e2`** で取り込んだ。停止点1は§13.2の第一〜第三行、すなわち**一つのstrict Δᵒᵖ図式ごとに、元の実現を頂点とし標準脚を持つD(A)の指定余錐と、その余極限性**とする。全パラメーターの実現関手・射・指定余錐族の比較は、ユーザー承認により3b-3へ移す。§20までの「未完」は当時の広い範囲での状態であり、この節は§8の区切りを検収するもの。

元の複体は引き続き `directSumTotalFunctor` による `|X|^q = ⨁_(n≥0) (X_n)^(q+n)`。内部次数の有界性は仮定しない。別の通常colimや、正規化barの頂点を元の全複体と同一視する置き換えはしていない。

今回の新規6本567行は、全て§13.2の第三行へ計上した。

- **`ClosedMapCoconeCoordinates`（67行、`27fd0a158`）**：終点固定の既存余錐空間同型の零次座標は、最初に指定した同じ閉射のcycleに等しい。
- **`StrictSimplicialVertexLeg`（86行、`2fdea8317`）**：`smallStrictBarNormalizedTotalHom_vertex` が、補正包含を通した同じnative頂点列を、置換の零行の余積包含に厳密に合わせる。`strictSimplicialBarRealizationHom_vertex` は、元の増大まで合成した**同じ複体射**が、先頭単体の零頂点から元の零行へ送る `strictSimplicialStandardLeg` に等しいと述べる。零shiftの次数同型も保って証明した。
- **`ClosedMapCoconeVertex`（62行、`2fdea8317`）**：`dgCoherentBarClosedMapCocone_leg_cycle` が、実際のjoin余錐の脚の閉零係数を、同じnative頂点列と指定閉射の合成へ照合する。端点のcastを異種等号で保持する。上の複体射の等式と組み合わせ、脚のホモロジーだけでなく標準脚そのものを確認できる。
- **`SpecifiedProjectiveCocone`（98行、`2fdea8317`）**：同じ閉射のH⁰での可逆性から、標的の射影性を実retractとして戻す。全頂点の射影性を入力し、計算済みの**同じ余錐全体**を既存の充満部分圏へ持ち上げる。`specifiedProjectiveCocone_image` は包含後のjoinからの全写像が元の余錐と等しいことを述べる。余極限性は充満包含で反映する。
- **`StrictSimplicialDerivedCocone`（77行、`2fdea8317`）**：元の実現の射影性を正規化barとの同じ比較から戻す。`strictSimplicialDerivedCocone` を、同じ余錐の射影的模型への持ち上げと、既存の半自由模型・一点評価の同値から定義した。`strictSimplicialDerivedCocone_isColimit` は、この**指定した余錐**が既存 `derivedInfinityCategory A` で余極限であることを示す。頂点は、同じ元の実現の半自由代表である。
- **`StrictSemifreeRealizationCocone`（177行、`866fcdba7`）**：元のstrict半自由図式へ戻す入口。半自由・射影的模型の既存同値の単位の同じ代表辺を厳密に保持して可逆円柱へ延ばし、計算済みの全余錐を左端に**厳密に保持する**延長を指定した。その右端を元の図式の余錐とする。`pointSemifreeRealizationExtension_source` が左端の全写像の等式、`strictSemifreeRealizationCocone_vertex` が同じ実現の頂点の等式を公開し、`strictSemifreeRealizationCocone_isColimit` が余極限性を示す。頂点だけを保つ任意の余錐の選択で標準脚の輸送を済ませていない。脚と高次成分は、この指定された同じ円柱上で比較する。さらに `pointSemifreeRealizationCylinder_unit` が、円柱が同値の単位を表す**同じ代表辺そのもの**を保持する等式を公開する。その辺の類が元の単位の順方向の射であることは、既存 `FunctorIso.edge_homMk` に一致する。

最後の入口の入力は `SimplicialObject (ClosedCategory A (SemifreeDGModules A PUnit))`。元の複体の半自由図式には既存 `semifreePointConstant A` の `onClosed` を適用してこの入力を与える。出力は既存 `semifreePointEquivalence A` を経由したD(A)の図式であり、別の導来∞圏を定義していない。比較対象の複体はその台の一点評価の元の直和実現。小さい添字の二段ULiftは、既存 `smallDiagramShapeIso` で直接の持ち上げへ結ぶ。

**図式ごとの版の停止点1は、この範囲で閉じた。** 全図式の射に関する実現関手同型・錐族の比較をこの完了に含めない。当初の最初の区切りのうち、図式間の射の像の比較は第四行とともに3b-3へ移した。今回確認した射は、同じbar比較と標準脚、および指定した同値の単位の辺である。

### 21.2 §13.2の表：完成時の実測

| 項目 | §10の追加見込み | 完成実測 | 元の上端との差 | 状態 |
| --- | ---: | ---: | ---: | --- |
| 全単体次数の包含・微分・退化・指定余錐の高次成分 | 500〜750 | 339 | −411 | 完了。nativeの最終照合は第三行に計上 |
| bar／重み・直和全複体の具体的比較・非有界擬同型 | 850〜1250 | 4511 | +3261 | 完了。同じ閉射の一点評価の同型を含む |
| 半自由出力分解・native余錐の輸送・同じ脚 | 500〜750 | 1299 | +549 | 完了。標準脚の最終等式・D(A)輸送・元の図式への円柱を含む |
| 全パラメーターの関手同型・射・指定余錐の族 | 250〜350 | 0 | — | §8により3b-3へ移管、未実装 |
| **今回の範囲の追加計** | **1850〜2750** | **6149** | **+3399** | 第一〜第三行 |

§10以前409行を含む3b-1は **78本6558行**。共通7本424行を含む全数学は **85本6982行**。見込みは停止点0で3b-1が1000〜1800行、その後、具体的な不足を確認して上げた停止基準が約6500行。完成実測はその約6500行に対して**+58行**。共通や段2への付け替えはしていない。今回の範囲を第一〜第三行に切った後の§20の見込み6231〜6411行に対しては、上端より147行増えた。主な増加は、元のstrict図式に戻す際に頂点だけでなく脚と全高次成分を保持する円柱の証拠を残したことによる。

第二行が当初の幅を大きく超えた理由は、加法的coend・線形co-Yoneda・非有界な全複体の水平ホモトピーの一般補題と、元のMaurer–Cartan barのshift・prefix・faceの符号を、同じ厳密な閉射へ戻す接続を別々に必要としたこと。この一般部分も含めて3b-1の実測に数えた。第三行では、余錐の実際の脚のcycle、元の終点と零shift同型、充満部分圏への持ち上げ、既存D(A)と元の図式への輸送を一体の「薄い入口」として見積もった幅が不足した。

### 21.3 3b-2〜3b-4の再見積もり

以下は**未実装分の設計見込み**。完了済み3b-1の6558行を単純に定数倍せず、再利用できる部分と、別に証明が必要な部分を分けた。既承認の停止基準は、3b-2・3b-3が8400行、3b-4が9200行のまま。今回の見積もりで基準を自動で引き上げない。

| 段 | 今回の見込み | 内訳と3b-1の実測からの修正 |
| --- | ---: | --- |
| 3b-2（G10） | **5000〜7200行** | 積全複体・正規化・非有界成分1100〜1600、end／Homとnative極限の比較1900〜2700、加群制限とホモロジー・標準脚600〜900、**全関手と指定錐族**1400〜2000。直和版の符号・成分は使えるが、積の組立てとnative錐の接続を新たに見積もった。G10の全関手版は段2に残し、段3の一般厳密化を待たせない |
| 3b-3 | **4850〜7150行** | Δ・Δᵒᵖに固定したstrict図式の∞局所化と `Fun(I_J, DA)`、coherent図式の厳密化・錐の両方向輸送4400〜6400。**移管したstrict実現の全パラメーター比較450〜750を加算**（旧見込み350〜550から、具体的な射・同じ錐の整合性を追加）。対象ごとの選択やH⁰の自然同型で代用しない |
| 3b-4 | **5300〜7800行** | BE実現1700〜2500、BEのTot1700〜2500、pointed KanのReedy条件付きraw版と置換後版1200〜1800、忘却との同じ写像・全関手比較700〜1000。⑤aのファイルは変更せず新規のBE固有補助を使う。忘却のsifted保存を仮定する循環は作らない |

今後の共通補助は追加200〜400行程度、既存共通424行を含めて624〜824行の見込み。残る三段と共通の追加は **15350〜22550行**、完了済み6982行を含めた全体は **22332〜29532行**の見込みとなる。3b-3の具体的厳密化とBEの全関手比較は依然不確実性が高い。範囲をこちらで狭める判断はしていない。段ごとの非停止の途中報告は、段0上端の半分に達する早い時点でも行い、今回の新見込みの半分まで報告を遅らせない。

### 21.4 G10へ再利用できるものと残る双対化

- **加法的coend**：`HomologicalAlgebra.CoendAdditive`・`LinearWeightRealization`・`LinearFreeWeight`。加法圏の重みの表示と関係式の道具は再利用できる。G10の極限はend側なので、同じcoend定理を積に適用したことにはしない。Homで表現したendと各射影の整合性は段2で証明する。
- **線形co-Yoneda**：`LinearCoYoneda`・`LinearCoYonedaNaturality`、`LinearWeightGenerators`・`BarWeightEvaluation*`。表現可能な係数・添字の計算と、元の同じ比較射の自然性の証明を再利用できる。余単体的入力ではHom側の係数と反変性を照合する必要がある。
- **非有界二重複体**：`TotalHorizontalHomotopyComponents`・`TotalHorizontalHomotopy`・`ChainTotalizationHomotopy`。内部次数の有界性なしの水平ホモトピーの成分と符号は使える。直和のdescで組み立てた最終定理はそのまま積に使わず、積のlift・各射影で検査する版を追加する。積の完全性を無条件に仮定しない。
- **shiftブロックの符号**：`UnsignedShiftCochain` と `SignedShiftBlockValues`・`SignedShiftBlockComposition`、次数ごとのshift・余積の照合。全次数で同じ射を保つ方法はG10へ使えるが、cosimplicialな横次数と積の規約で符号を照合する。bar固有のprefix・faceの証明はG10へそのまま持ち込まない。
- **同じ頂点・脚を保つ接続**：`ClosedMapCocone*`・`SpecifiedProjectiveCocone`・今回の円柱延長。実在する同じ閉射とnative錐を照合する手順を共用できる。極限側の主張そのものは新たに示し、余極限判定を無証明で読み替えない。

### 21.5 検証とコミット

- `/private/tmp/isw2-build-audit-47.log`：`ClosedMapCoconeCoordinates` と必要な既存の射影的模型・同じ頂点の輸送の対象ビルド6049 jobs、既存の射影的retract補題2788 jobs、一時監査80本847宣言。終了コード0、標準三公理のみ。コード **`27fd0a158`**。
- `/private/tmp/isw2-build-audit-48.log`：標準脚・実際の余錐脚・射影的持ち上げ・D(A)輸送の4本の対象ビルドと既存の閉nerve自然性6264 jobs、一時監査84本881宣言。終了コード0、標準三公理のみ。コード **`2fdea8317`**。
- `/private/tmp/isw2-build-audit-49.log`：段1・共通の全85モジュールを明示した対象ビルド7349 jobsと一時監査85本909宣言は終了コード0、標準三公理のみ。この後、円柱が同値の単位の同じ代表辺を保持することを厳密に指定すべき点を確認し、既存 `exists_kanEquivalenceInterval_extension_of_invertibleEdge` へ切り替えて `pointSemifreeRealizationCylinder_unit` を公開した。単に両端を指定する存在定理の逆像を選ぶ形を残していない。
- 補強後の `/private/tmp/isw2-build-audit-50.log`：**全85モジュールを明示した鍵付き対象ビルド7349 jobs** と `AuditISW2EightyFive.lean` による最終監査は終了コード0。**85本912宣言、標準三公理のみ、sorry・独自公理0**。最後のコードは **`866fcdba7`**。監査はモジュール番号で所有宣言を抽出して全依存公理を調べ、85本それぞれの宣言数が非零であることを確認した。

各回 `with_build_lock.sh --wait 3600`、整理券は一枚、実行は30分以内のtimeoutを設定し、ビルド・監査の実行中だけ鍵を持つ。rootビルドは行っていない。最後の鍵も検証終了で返却した。`git diff --check` は成功。未検証のLean下書きは残していない。 検証基準は取り込み済みのmain `95c8f5c8c`。この基準とHEADのLean差分を再照合し、新規47本のみで既存Leanファイルの変更0を確認した。作業中にmainは `fbd1d7698` まで進んでいたが、今回の47本の直接importに後続mainで削除されたモジュールはない。後続mainの差分は今回の検証へ取り込んでいない。既存の宣言・drafts・入口・公式監査の変更0。他レーンとのファイル重複0。

### 21.6 mainへの取り込みと登録候補

main `95c8f5c8c` のソースの有無と全85モジュールのリストを照合した。最初の38本はmainに存在し、**47本が未取り込み**。§16の5本・§17の9本・その後の途中コミットを含む以下を、停止点1でまとめて取り込む。入口と `audit_derived_infinity` への正式登録は調整役が行う。この枝では登録しない。

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeRealizationCocone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialVertexLeg
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeVertex
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplicialDerivedCocone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeCoordinates
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.VertexProjector
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.NativeVertexInclusion
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PointHomSpaceVertexCycle
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCoconeInitial
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialNativeColimit
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarNormalizedComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ClosedMapCocone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StrictSimplicialBarRealization
SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.CosliceInvertibleLegInitial
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.RealizationDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ShiftedCoproductDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDegreeCofan
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalHomValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalIso
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalClosed
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarThetaValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundaryFaces
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockComposition
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarSignedColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBlockCoefficients
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SignedShiftBlockValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundarySum
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalComposition
SerrePositivity.HomologicalAlgebra.SimplicialReplacementBoundary
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarUnshiftedBoundary
SerrePositivity.HomologicalAlgebra.UnsignedShiftCochain
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowBoundary
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarDiagram
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
SerrePositivity.HomologicalAlgebra.LinearWeightGenerators
SerrePositivity.HomologicalAlgebra.BarWeightEvaluation
SerrePositivity.HomologicalAlgebra.BarWeightEvaluationIso
SerrePositivity.HomologicalAlgebra.BarWeightRealizationNaturality
SerrePositivity.HomologicalAlgebra.TotalRowCochain
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementWeightComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.ReplacementTotalHomotopy
```

検収対象は、§8に従う図式ごとの指定余錐・同じ頂点・標準脚・余極限性。移管した全パラメーターの比較は3b-3、G10は段2であり、この停止点の完了には含めない。

以上を停止点1として報告する。段2の実装にはまだ着手していない。移管した族の比較と後続段の範囲の判断は、指示書どおりユーザー・調整役に委ねる。


## 22. 3b-2（G10）の着手：積全複体・標準脚・離散成分（2026-11-12 夜）

### 22.1 範囲と基準

指示書 §9 と停止点1の検収を受け、main `997fc2dfe`（登録 `cfa0e8324` と §9 を含む）を fast-forward で取り込んだ。3b-2 を開始する。§21末尾の「段2は未着手」は停止点1時点の記録であり、本節から更新する。

G10 は、一般の余単体的複体の積 Tot と D(A) の指定極限錐を、図式の射・全パラメーター・指定錐の族まで照合し、離散加群版をその制限として返す範囲を保つ。見込み 5,000–7,200 行、上限 8,400 行。途中の規模報告は止まらずに行う。保守的に当初の段0の上端の半分（1,600行）でも一度実測を知らせる。3b-4 の点つき Kan Tot は K の再開へ移り、このレーンでは作らない。3b-3 の分担を先取りしない。

### 22.2 最初の部品

新規10本、638行（全て3b-2に算入、共通への付け替えなし）。既存の宣言は変更していない。

| 部分 | 本数 | 行数 | 今回の内容 |
| --- | ---: | ---: | --- |
| 一般の積 total | 3 | 243 | `ProductTotal`、`ProductTotalZeroRow`、`ProductTotalFirstRow`。反対圏上の直和 total により全関手を構成。指定射影・lift・射の判定・自然性・全微分の二項公式・各対角線の積錐の普遍性。零行への鎖写像と第一行の射影による指定零ホモトピー。 |
| 余単体的複体 | 5 | 265 | `ProductTotal`、`ProductComponents`、`ProductCone`、`StandardZeroLeg`、`StandardCofaceHomotopy`。交代余面複体を整数へ零延長して適用。全次数 q の積を元の n≥0 の成分 Xⁿ[q−n] で提示し、射の自然性を証明。零次の標準脚は自然変換、二つの余面の後の脚は同じ第一行の射影でホモトピック。 |
| 離散入力の成分 | 2 | 130 | `SingleComponent`、`DiscreteComponents`。一つだけ非零の成分を持つ積の同型。加群を内部次数零へ関手的に埋め込み、負の全次数の零性と、非負全次数 n の元の余単体加群への自然同型。 |

直和全複体の無限和を積へ置き換える推測は使わない。両方向を反対圏へ移した直和 total の射影・普遍性を使用する。全微分は横微分と `(-1)^a` 倍の縦微分の二項で、無限和や積の完全性の仮定はない。全ての縦次数は非有界のまま。

`componentπ X n q` は次数ごとの射であり、Xⁿ への鎖写像と称していない。鎖写像として証明したのは零次の `standardZeroLeg`。二つの余面の両立は `standardCofaceHomotopy` が与える。高次の join 錐全体は未構成である。

離散加群の `discreteTotalDegreeNatIso` は各次数の通常の自然同型まで。交代余面複体との**複体の自然同型**、D(A) への全関手の比較やホモロジー比較が閉じた、とはしていない。

### 22.3 次の接続

1. 離散入力の成分同型を全微分と照合して、零延長された交代余面複体との複体の自然同型へまとめる。
2. 半自由試験対象からの Hom と積 total の交換、end 側の重みの比較・正規化を作る。3b-1 の coend/co-Yoneda の添字・符号・非有界性の計算は使うが、coend の定理をそのまま end に適用しない。
3. 同じ標準脚と高次成分を持つ生の dg nerve の指定錐を作り、写像空間の極限判定に接続する。既存の `Project.DerivedCategories.dgNerve_isLimitCone_iff_homTargetPointedRestriction` が同じ実錐を保持する入口となる。
4. 既存の `Project.DerivedCategories.dgModuleResolvedInfinity_isLimitCone_of_raw` により、生の指定極限錐から半自由出力へ移す経路を確認した。これは入力の Small 性や生の出力の射影性を要求しない。積 total 自体を射影的・半自由と仮定しない。全関手と指定錐の族の輸送は引き続き証明が必要。

見込みはまだ §21.3 の 5,000–7,200 行から変更しない。638行は最初の線形部品で、native 錐や全パラメーターの比較の実測をまだ得ていないため、これだけから下方修正しない。停止点2ではない。

### 22.4 検証・登録待ち

コード：`97dfd772b`（積 total の2本）、`59872193d`（成分・積錐の2本）、`7802069ad`（標準脚・余面ホモトピー・離散成分の6本）。

新規10本すべての鍵付き対象ビルド成功（2,290 jobs）。`--wait 3600` の整理券は一枚にまとめ、鍵の中はビルド・監査だけとした。待ち中に個別検査を通した離散成分2本も、開始前の同じ対象ビルドの束へ含めた。初めの8本の実測は508行（途中のチャットの509行は数え違い）、最終10本は638行。

一時監査 `/private/tmp/AuditISW2G10Ten.lean`：**156宣言、標準三公理のみ**（各モジュール 42, 13, 14, 7, 22, 13, 8, 10, 8, 19）。`sorry`・独自公理0。個別検査も成功。ビルドの警告は空白・行長の style linter のみ。ログ `/private/tmp/isw2-g10-build-3.log`、終了コード0。鍵は解放済み。

基準 `997fc2dfe` からの Lean 差分は新規10本のみ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。今回の束は着手の途中報告であり、停止点2や規模上限による中断ではない。

登録対象（停止点2で調整役が判断）：

```text
SerrePositivity.HomologicalAlgebra.ProductTotal
SerrePositivity.HomologicalAlgebra.ProductTotalZeroRow
SerrePositivity.HomologicalAlgebra.ProductTotalFirstRow
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductTotal
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardZeroLeg
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardCofaceHomotopy
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SingleComponent
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComponents
```


## 23. 3b-2 続き：離散入力の複体比較と指定射影（2026-11-12 夜）

### 23.1 今回閉じた比較

§22.3 の 1（離散入力の次数同型を微分と照合して、零延長された交代余面複体との自然同型へまとめる）を進めた。最終状態の追加は6本・433行、3b-2累計は16本・1,071行。§21.3 の完成見込み 5,000–7,200 行、上限 8,400 行は変更しない。保守的な途中報告点 1,600 行にはまだ達していない。

- `HomologicalAlgebra.ProductTotalSingleRow`（122行）：任意の非有界整数複体を縦次数零に置いた二重複体について、同じ `(q,0)` 射影を使う `singleRowDegreeIso`、微分との可換性、射への自然性を証明し、`singleRowNatIso` にまとめた。積の完全性を要求しない。
- `HomologicalAlgebra.MapExtendComplex`（30行）と `MapExtendComponents`（47行）：既存の `SerrePositivity.mapExtendIso`・`mapExtendIso_naturality` を自然同型として束ね、元の次数での前向き・逆向きの成分公式を証明した。最初に書いた交換の重複証明は取り除いた。変更したのはこのレーンで今回追加した未取り込みファイルだけで、既存 `HomologicalAlgebra/MapExtend.lean` は変更していない。
- `CosimplicialTotalization.DiscreteComplexComparison`（47行）：既存の加法的関手と交代余面複体の交換、上記の零延長との交換、一行二重複体の比較を合成し、`discreteTotalCochainNatIso : discreteTotalFunctor A ≅ discreteCochainFunctor A` を構成した。対象ごとの同型ではなく、余単体加群の図式の射と微分を含む複体の自然同型。
- `CosimplicialTotalization.DiscreteComparisonComponents`（103行）：同じ比較射の非負行を計算し、`discreteTotalCochainNatIso_hom_f_degreeIso` で、元の交代余面複体の零延長同型を後合成すると前回の `discreteTotalDegreeIso` **そのもの**になることを証明した。比較同型を選び直して済ませていない。

鍵待ち中に次の Hom 比較にも着手し、`CosimplicialTotalization.HomTotalComponents`（84行）を追加した。`homTotalComponentsEquiv` は次数 p の `Homogeneous P (Tot X) p` と `∀ n, Homogeneous P (Xⁿ) (p−n)` の線形同値。元の積射影を使う `homTotalComponent` と、`componentLift` を使う `homTotalLift` を作り、両方向の往復と成分による射の判定を証明した。試験対象・入力とも非有界のまま。Hom 微分との可換性・全関手の自然性を証明済みとはしていない。

比較先 `discreteCochainFunctor` は、`alternatingCofaceMapComplex (ModuleCat A)` と `ComplexShape.embeddingUpNat.extendFunctor (ModuleCat A)` の合成。既存の E∞ 界面や BS の `cosimplicialCochains` の宣言は変更していない。

### 23.2 native 極限へ残るもの

今回の結果は線形の複体比較であり、G10 の停止点2ではない。特に次は未完了である。

1. 半自由試験対象 P からの `homComplex A P (Tot X)` と `Tot (homComplex A P X)` の全関手比較。各次数の線形同値は今回の `homTotalComponentsEquiv` で得たが、微分・射の自然性と指定脚との両立を証明する必要がある。通常の複体の極限を保つというだけでは Tot の比較にならない。
2. 正規化・非正規化と end 側の重みの比較、同じ高次成分を持つ生の dg nerve の join 錐、その極限性。
3. 既存の `dgModuleResolvedInfinity_isLimitCone_of_raw` による半自由出力・D(A) への輸送と、**全パラメーターの指定錐の族**。G10 ではこれを3b-3へ移さない。
4. その D(A) 側の比較から、脚・標準射と両立するホモロジー比較と入口 `cosimplicialModule_limitCone` を返すこと。

次の Hom 比較で使う実名は `DifferentialGraded.homComplex`（Mathlib `CochainComplex.linearHomComplex`）、`Homogeneous`（`Cochain`）、`tensorRightHomAdjunction`。`HomLimits.homComplex_limit_ext` は指定された**通常の複体極限**への判定なので、積 Tot の極限性を先取りする入口には使わない。§21.4 の符号と非有界な成分計算を再利用する。

### 23.3 検証と登録待ち

コードコミットは `00538db81` と `471058022`。後者で、今回作った零延長比較を既存 `MapExtend` の再利用に整理し、指定成分の等式と Hom の次数付き線形同値を追加した。

最終の**全16本の鍵付き対象ビルド成功**（2,298 jobs）。`--wait 3600`、一回1,700秒の上限、整理券は同時に一枚。最初の束は15本で開始したため、Hom の1本を加えた検証はその終了・鍵解放を確認した後に一枚で並び直した。最終ログ `/private/tmp/isw2-g10-build-6.log`、終了コード0。鍵は解放済み。

一時監査 `/private/tmp/AuditISW2G10Sixteen.lean`：**232宣言、標準三公理のみ**（42, 13, 14, 7, 22, 13, 8, 10, 8, 19, 26, 2, 12, 3, 10, 23）。`sorry`・独自公理0。個別検査も成功。style／flexible tactic の linter メッセージ以外の検査上の問題はない。

基準 `997fc2dfe` からの Lean 差分は新規16本のみ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。取り込みや承認を求める停止点ではなく、G10 の停止点2には未到達。

今回の追加登録対象（先の10本に加える）：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow
SerrePositivity.HomologicalAlgebra.MapExtendComplex
SerrePositivity.HomologicalAlgebra.MapExtendComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComplexComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComparisonComponents
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComponents
```

## 24. 3b-2 続行：Hom 成分の微分・両変数自然性

### 24.1 今回の部品

追加6本・332行、3b-2累計22本・1,403行。完成見込み5,000–7,200行、上限8,400行は据え置く。保守的な途中報告点1,600行には未到達。既存の数学宣言・drafts・入口・正式監査は変更していない。

- `HomologicalAlgebra.ProductTotalHomDifferential`（54行）：一般の非有界二重複体の同じ積射影から `homRowComponent` を定義し、Hom 微分の行成分を横微分と `(-1)^a` 倍の行内 Hom 微分の和に分けた。試験複体の前合成項の符号は `a+(p+1−a)=p+1` で一致する。有界性・積の完全性を仮定しない。
- `CosimplicialTotalization.HomTotalDifferential`（72行）：上の式を指定 `rowIso` で移し、前回の `homTotalComponent` 自体について `homTotalComponent_differential` を証明。第0行の横項の消滅も証明した。
- `CosimplicialTotalization.HomTotalHorizontal`（54行）：全ての非負行の `rowDifferential` と、正の行の横項を元の交代余面微分の後合成で表す `homTotalHorizontalTerm_succ_v`。零延長の射を選び直していない。
- `CosimplicialTotalization.HomTotalNaturality`（55行）：指定成分の評価公式、入力図式の射についての後合成の自然性、試験対象の射についての前合成の自然性。
- `HomologicalAlgebra.ComplexHomAdditive`（29行）：既存の `DifferentialGraded.homFunctor` に加法性の instance を供給。既存の関手の定義は変更していない。
- `CosimplicialTotalization.HomDoubleComplexComparison`（68行）：加法的関手と交代余面・零延長の既存の交換を合成し、`homDoubleComplexIso` とその積全複体への像 `homDiagramTotalIso` を作った。いずれも入力図式の射を含む自然同型。前向き射の行成分が `rowIso` とその Hom 像の合成であることも証明した。

最後の自然同型は **Tot(Hom(P,X)) と、元の二重複体の各行に Hom(P,−) を適用した積 Tot の比較**である。`Hom(P,Tot X)` からの複体同型が完成したという主張ではない。今回はそのための微分・自然性・標的の交換を揃えた。

### 24.2 残りの順序

1. 元の二重複体の行射影を使い、`Hom(P,Tot X)` から行 Hom の積 Tot への複体の同型を構成する。今回の微分公式を閉性に、前回の次数付き線形同値を逆射に使う。今回の `homDiagramTotalIso` と合わせ、指定射影・射を保つ Hom–Tot の全関手比較へまとめる。
2. 正規化・重み付き end との比較、同じ高次成分を持つ dg nerve の join 錐とその極限性。
3. `dgModuleResolvedInfinity_isLimitCone_of_raw` による D(A) への輸送と全パラメーターの指定錐の族、元の加群版入口とホモロジー比較。

§23.2 の未完了項目は保持する。G10 の停止点2には未到達。

### 24.3 検証と登録待ち

コードコミット `391dbede1`。6本とも個別検査は成功。新規6本の**鍵付き対象ビルド成功**（2,295 jobs）、一時監査は**累計22本・292宣言、標準三公理のみ**。今回の6本の宣言数は21, 1, 13, 7, 7, 11。`sorry`・独自公理0。

整理券一枚・`--wait 3600`・一回1,700秒の上限で実行し、終了コード0を確認。ログ `/private/tmp/isw2-g10-build-7.log`、監査 `/private/tmp/AuditISW2G10TwentyTwo.lean`。鍵待ち中に追加した最後の1本も対象ビルドと監査に含まれたことを確認した。鍵は解放済み。style／flexible tactic の linter メッセージのみで、検査上のエラーはない。

基準 `997fc2dfe` からの Lean 差分は新規22本のみ。ルートビルドは実行していない。停止点2の検収・取り込みを求める報告ではない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalHomDifferential
SerrePositivity.HomologicalAlgebra.ComplexHomAdditive
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalDifferential
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalHorizontal
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDoubleComplexComparison
```

## 25. 3b-2 続行：非有界 Hom–Tot の複体自然同型

### 25.1 早めの途中報告と実測

保守的な途中報告点1,600行に達したので、停止せず実測と残りを記録する。今回7本・465行を追加し、3b-2累計は29本・1,868行。完成見込み5,000–7,200行、上限8,400行は据え置く。この見込みとの差分として残りは約3,100–5,300行。半分の正式な基準を改定後の見込みに取る場合にも、ここでは早めに報告しておく。

§24.2 の1の中心である Hom–Tot の複体自然同型を閉じた。今回の一般補題は内部次数・横次数・試験対象のいずれにも有界性を課さない。積の完全性や試験対象の射影性も仮定しない。

- `HomologicalAlgebra.ProductTotalHomMap`（88行）：全次数等式を持つ `homRowLinear`、指定射影を保つ `homTotalDegreeMap`、前回の符号公式による微分可換性、鎖写像 `homTotalMap`。
- `HomologicalAlgebra.ProductTotalHomIso`（93行）：行 Hom の積の元を元の Tot への射へ戻す `homTotalDegreeInverse`。同じ射影で両逆を証明し、`homTotalDegreeEquiv` と複体同型 `homTotalIso` を構成。`homTotalIso_hom` により前向き射は `homTotalMap` そのもの。
- `HomologicalAlgebra.ProductTotalHomNaturality`（49行）：二重複体の射に関する `homTotalMap_naturality`、および `ProductTotal.functor ⋙ homFunctor P` と `homFunctor P` を行に適用した積 Tot の全関手の自然同型。
- `CosimplicialTotalization.HomTotalComparison`（90行）：一般比較と前回の `homDiagramTotalIso` を合成し、`productTotalFunctor A ⋙ homFunctor P ≅ homDiagramFunctor P ⋙ productTotalFunctor A` を構成。`homTotalNatIso_hom_component` で前向き射の各成分が前回の `homTotalComponent` **そのもの**であることを証明した。

鍵待ち中にさらに2本を追加した。

- `HomologicalAlgebra.ComplexHomPrecompose`（38行）：前合成と後合成の可換性、既存の Hom 関手間の `homPrecomposeNatTrans`。
- `HomologicalAlgebra.ProductTotalHomPrecompose`（53行）：一般の二重複体について、比較鎖写像と試験対象の前合成の可換性、およびそれを全関手上の自然変換の等式とする `homTotalNatIso_precompose`。

さらに `CosimplicialTotalization.HomTotalParameters`（54行）で、試験対象の前合成を全余単体図式へ適用する `homDiagramPrecompose` と、余単体版の `homTotalNatIso_precompose` を証明した。§24 の成分公式と今回の指定成分の等式で全関手上の自然変換の等式へ戻している。これで一般二重複体版・余単体版のどちらも、入力図式の射と試験対象の射の双方について同じ比較射を追跡できる。

### 25.2 残りと見積もり

次は正規化・重み付き end との比較と、同じ高次成分を持つ dg nerve の join 錐。今回は通常の複体圏の自然同型であり、native 極限性はまだ証明していない。`dgNerve_isLimitCone_iff_homTargetPointedRestriction` に入れるには実際の指定錐とその Hom 試験の比較が必要で、通常の複体の極限保存で代用しない。その後に半自由出力・D(A) への輸送、全パラメーターの指定錐の族、加群版入口を残す。

次工程で再確認した入口は `Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/BousfieldKan.lean` の `bousfieldKanHolimFunctor`・`bousfieldKanEvaluation` と、同節 `CoherentConeNativeComparison.lean` の指定錐からの native 切断比較。後者は docstring にもあるとおり BK の比較 q′ との一致を含まない。従って Hom–Tot 同型だけからその一致を推論せず、重み付き end と指定成分を照合する工程を残す。

残りの主な規模のリスクは、射列で添字づけた錐の高次成分と、余単体次数で添字づけた Tot 成分を結ぶ部分にある。3b-1 と同様に、既存の指定錐・Hom 判定を再利用し、存在だけの別の頂点への置き換えを避ける。G10 の停止点2には未到達。

### 25.3 検証と登録待ち

先の6本は鍵付き対象ビルド成功（2,298 jobs）、累計28本360宣言・標準三公理のみの監査を通過し、`08f80bda6` にコミット済み。最後の `HomTotalParameters` も個別検査は成功。先の検証の終了・鍵解放を確認してから、同じ `--wait 3600`・一回1,700秒の上限で最後の1本と累計29本の監査に並び直した。最後の対象ビルドも成功（2,299 jobs）、累計29本の一時監査は **364宣言、標準三公理のみ**。最後の1本は `54a7630b0` にコミットした。今回7本の宣言数は23, 19, 8, 12, 3, 3, 4。`sorry`・独自公理0。

ログは `/private/tmp/isw2-g10-build-9.log` と `/private/tmp/isw2-g10-build-10.log`、最終監査は `/private/tmp/AuditISW2G10TwentyNine.lean`。両方とも終了コード0を確認し、鍵は解放済み。整理券は常に一枚。新規ファイルの style longLine の警告、および依存ファイルの既存 linter メッセージ以外に検査上の問題はない。

基準 `997fc2dfe` からの Lean 差分は新規29本だけ。既存の数学宣言・drafts・入口・正式監査は変更していない。ルートビルドは実行していない。停止点2の検収・取り込みを求める報告ではない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.ProductTotalHomMap
SerrePositivity.HomologicalAlgebra.ProductTotalHomIso
SerrePositivity.HomologicalAlgebra.ProductTotalHomNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalComparison
SerrePositivity.HomologicalAlgebra.ComplexHomPrecompose
SerrePositivity.HomologicalAlgebra.ProductTotalHomPrecompose
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalParameters
```


## 26. 3b-2 続行：積全複体への横ホモトピーの移送

### 26.1 検証済みの区切り

新規6本・325行を追加し、累計35本・2,193行。コードコミット `6036adcba`。
`ProductTotalHorizontalComponents` と `ProductTotalHorizontalHomotopy` で、指定積射影による横ホモトピーの成分とその方程式を証明した。縦微分の二項は隣接横次数の符号で相殺する。`CochainProductTotalizationHomotopy` は横の非負余鎖次数を整数へ零延長し、同じ二射と鎖ホモトピー同値を積全複体へ移す。内部次数の有界性・積の完全性・収束の仮定はない。

`ComplexOppositeHomotopy` は添字を保ち形を反転する反対化へ指定ホモトピーを移す。重みの鎖複体に反変な線形 end を適用する準備であり、次数の符号を反転する余鎖複体の反対化とは区別する。`FreePresheafLinearHom` は自由前層の線形 Yoneda 評価と重みの射への自然性、`FunctorComplexExchange` は複体値図式から図式値複体への逆向きの交換関手と両比較同型。

6本の鍵付き対象ビルド成功（1,545 jobs）。累計35本の一時監査は **427宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒の上限で実行し、終了コード0と鍵の解放を確認した。ログ `/private/tmp/isw2-g10-build-11.log`、監査 `/private/tmp/AuditISW2G10ThirtyFive.lean`。既存の数学宣言・drafts・入口・正式監査は変更していない。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.FreePresheafLinearHom
SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalComponents
SerrePositivity.HomologicalAlgebra.ProductTotalHorizontalHomotopy
SerrePositivity.HomologicalAlgebra.CochainProductTotalizationHomotopy
SerrePositivity.HomologicalAlgebra.ComplexOppositeHomotopy
```

### 26.2 続行中の部分

線形 end の全関手族、標準単体重みから元の余単体図式への自然同型、その鎖分解を積全複体へ移す部分を作業中。これらの未検証分はコミットに含めていない。通常の複体圏の比較だけでは native な指定錐の極限性をまだ得ていない。§25.2 の残り（正規化・BK との指定成分比較・native 錐・D(A) への輸送・全射と指定錐の族）を続ける。停止点2には未到達。見込み5,000–7,200行・上限8,400行は据え置く。

11-12 夜の指示を確認した。停止点2の報告後は承認待ちを挟まず、3b-4 の BE 模型の実現・Tot・U との比較へ進む。3b-3 は③-aの担当。3b-4 の開始時には coherent な図式の厳密化への依存を紙で記し、依存待ちまたは承認を要する判断では境目の紙の作業に移る。点つき Kan 複体の Tot と⑤aの既存ファイルは対象外。


## 27. 3b-2 続行：標準重みと bar 重みの線形 end

### 27.1 比較の内容

§26 の後に新規7本・521行を検証し、累計42本・2,714行。

- `LinearWeightEnd`：線形重み W と複体値図式 X の end の複体。次数 q の元は W から X の次数 q への自然変換である。係数の後合成と重みの前合成を明示し、全関手族と加法性を証明した。対象・二種類の射を名前付きの部品に分けることで、関手構造の不必要な定義展開を避けている。
- `FreeWeightEndEvaluation`・`StandardWeightEnd`：自由単位重みの恒等射の生成元で 1 を評価する複体自然同型。元の余単体図式の全射と全単体作用素に自然。
- `LinearWeightEndTotalization`：鎖複体の重みを反対化して余鎖の end を取り、積全複体へ送る。元の指定鎖ホモトピー・鎖ホモトピー同値を保持する。有界性は不要。
- `AlternatingFaceOpposite`・`StandardWeightTotalComparison`：重みの交代面複体の反対化と交代余面複体を比較し、標準重みの end の積全複体から元の `productTotalFunctor` への同型を構成した。各横次数の前向き射が指定された自由単位重みの評価そのものであることも照合した。
- `BarWeightEndComparison`：3b-1 の `SimplicialRealization.barStandardWeightHomotopyEquiv` を再利用した。元の積 Tot から bar 重みの線形 end の積全複体への鎖ホモトピー同値を得る。前向き射は `barStandardWeightComparison` の前合成そのもの。新しい任意の持ち上げを前向き射には使っていない。

### 27.2 検証

最初の4本は `4e7023038`。鍵付き対象ビルド（1,974 jobs）と累計39本487宣言の監査が成功。次の3本も鍵付き対象ビルド（2,344 jobs）と累計42本 **512宣言、標準三公理のみ**の監査が成功した。個別検査も成功、`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-12.log`・`isw2-g10-build-13.log`、最終監査 `/private/tmp/AuditISW2G10FortyTwo.lean`。双方とも `--wait 3600`・整理券一枚・一回1,700秒の上限で終了コード0。鍵は解放済み。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.LinearWeightEnd
SerrePositivity.HomologicalAlgebra.FreeWeightEndEvaluation
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightEnd
SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalization
SerrePositivity.HomologicalAlgebra.AlternatingFaceOpposite
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalComparison
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndComparison
```

### 27.3 半分での実測と残り

改定後の見込み5,000–7,200行の下端の半分2,500行も超えたので、停止せず実測を更新する。実測2,714行、残りの見込みは約2,300–4,500行、上限8,400行。係数図式の射を重みの全鎖複体上の自然変換として扱う部分を続けている。

今回の bar は既存の `coefficientBarWeight SimplexCategoryᵒᵖ`。その各値は Under の nerve から作られ、BK の `Over` の nerve と同一だとはまだ主張していない。反対圏・正規化・指定錐の成分を照合して Hom 試験の native 切断比較へ移す部分が残る。指定脚・高次単体を持つ join 錐、その極限性、D(A) への輸送、全射と指定錐の族、加群版入口も未完了。通常の複体の鎖ホモトピー同値をもって G10 の完了とはしない。


## 28. 3b-2 続行：指定比較の全射への自然性と Moore 正規化

### 28.1 完了した追加部分

新規4本・225行、コード `7bd6022f7`。累計46本・2,939行。

- `LinearWeightEndTotalParameters`：係数図式の射を、重みの全鎖複体上の自然変換 `linearWeightEndTotalMap` へ移す。係数と反変重みの全関手族 `linearWeightEndTotalFamily` と、指定重み比較の自然性を構成した。
- `StandardWeightTotalNaturality`：§27 の二重複体比較の係数自然性を、同じ積全複体関手で移す。`standardWeightEndTotalNatIso` は元の `productTotalFunctor` への全関手の自然同型で、各対象の射は既存の `standardWeightEndTotalIso` の射。
- `BarWeightEndNaturality`：固定した先頭頂点比較による前合成を、全係数図式上の自然変換 `barWeightEndTotalComparison` にまとめた。各対象での射は §27 の鎖ホモトピー同値の前向き射そのもので、各対象で擬同型。
- `LinearWeightEndNormalization`：既存の Dold–Kan の `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` を再利用し、Moore 包含の前合成による end の積全複体の鎖ホモトピー同値を構成。係数図式の全射への自然性も証明した。内部次数に有界性を課していない。

### 28.2 main 取り込み後の検証

main `3b806b942` を `b51fcd150` で枝へ取り込んだ（競合なし）。夜の進め方と IS-W2 §10 の分担を作業枝へ反映した。自レーンから既存の数学宣言を変更していない。

その後、新規4本を含む **累計46本すべて**の鍵付き対象ビルドが成功（2,383 jobs）。一時監査は **552宣言、標準三公理のみ**。`sorry`・独自公理0、個別検査も成功。ログ `/private/tmp/isw2-g10-build-14.log`、監査 `/private/tmp/AuditISW2G10FortySix.lean`、全対象一覧 `/private/tmp/isw2-g10-fortysix-modules.txt`。`--wait 3600`・整理券一枚・一回1,700秒の上限で終了コード0を確認し、鍵は解放済み。ルートビルドは行っていない。入口と正式監査への登録は調整役へ残す。

今回の追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalParameters
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalNaturality
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BarWeightEndNaturality
SerrePositivity.HomologicalAlgebra.LinearWeightEndNormalization
```

### 28.3 次の工程

停止点2には未到達。通常の複体上の比較・係数自然性・正規化の計算部品を閉じた段階であり、native な join 錐はまだ構成していない。次は、正規化された線形 bar end の成分を、指定 join 錐の脚と高次単体に照合する。既存の `dgNerve_isLimitCone_iff_homTargetPointedRestriction` と `coherentCone_isLimit_iff_reflectedNativeComparison` は実際の錐を入力に取るので、その入力と切断比較を構成する工程を省略しない。`Under(Δᵒᵖ)` と BK の `Over(Δ)` の反対向きも照合する。

この後に D(A) への輸送・全射と指定錐の族・加群版入口を残す。見込み5,000–7,200行、上限8,400行は据え置き。夜の指示どおり承認待ちは挟まず続行し、停止点2に達したら報告をコミットして3b-4へ進む。


## 29. 3b-2 続行：反対 under と BK over の重みの照合

### 29.1 閉じた比較

新規6本・335行、コード `164e9d61d`。累計52本・3,274行。

- `UnderOppositeOverNerve`：既存の `Under.opEquivOpOver` の厳密な逆関手を nerve に移し、底の全射に自然な同型を構成した。さらに既存の `nerveOppositeIso` と合成し、二重反対圏から戻した `underNerveWeight Jᵒᵖ` が **`bousfieldKanWeight J ⋙ SSet.opFunctor`** と同型であることを示した。over 重みそのものとは区別している。
- `AlternatingReverseSigns`：Fin.rev による交代和の添字替えと、n+1 次元の境界の反転符号 `(-1)^(n+1)` を証明。
- `AlternatingFaceReverse`：次数符号を `ε₀=1`、`εₙ₊₁=(-1)^(n+1) εₙ` として、単体順序反転後の交代面複体から元への同型を構成した。単体的対象の全射に自然で、零次数では恒等射。
- `OverNerveCoefficientWeight`・`DoubleOppositeOverWeight`：重みの各単体の係数余積と二変数の交換を使って線形化し、元の bar 鎖重みと二重反対圏へ移した BK over 鎖重みの符号付き同型を構成した。
- `CosimplicialTotalization.BousfieldKanWeightEndComparison`：元の `productTotalFunctor` から BK over 重みの線形 end の積全複体への自然変換を構成した。各対象での射は、元の bar 比較に上記の鎖同型の前合成を合成した鎖ホモトピー同値の前向き射そのもの。全図式に自然で、各対象で擬同型。

### 29.2 検証と登録待ち

個別検査成功。新規6本の鍵付き対象ビルド成功（2,517 jobs）、累計52本の一時監査は **605宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒の上限で終了コード0を確認し、鍵は解放済み。ログ `/private/tmp/isw2-g10-build-15.log`、監査 `/private/tmp/AuditISW2G10FiftyTwo.lean`、全対象一覧 `/private/tmp/isw2-g10-fiftytwo-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.UnderOppositeOverNerve
SerrePositivity.HomologicalAlgebra.AlternatingReverseSigns
SerrePositivity.HomologicalAlgebra.AlternatingFaceReverse
SerrePositivity.HomologicalAlgebra.OverNerveCoefficientWeight
SerrePositivity.HomologicalAlgebra.DoubleOppositeOverWeight
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BousfieldKanWeightEndComparison
```

### 29.3 native 錐へ残る接続

§28.3 の under/over の向きの照合は閉じた。残りは、正規化した線形 end と Hom 空間の BK 切断比較を結び、同じ頂点・脚・高次単体の join 錐を構成して極限性を示すこと、その D(A) への輸送と全射・指定錐の族、加群版入口である。今回の擬同型だけを native 錐の極限性とはしていない。

調べた既存の入力は `EInfinity/ComplexLimits/NormalizedChainsHom`、`NormalizedChainsHomNaturality`、`NormalizedHomTargetNaturality`、`NormalizedHomZeroEvaluation`。これらは実正規化鎖と Dold–Kan の Hom 同値、始域・標的の自然性、零次数の指定評価を供給する。既存宣言を再利用する候補として確認しただけで、⑤aのファイルは変更していない。通常の複体の Hom 同値から native な全錐の切断比較への移送は引き続き必要。

見込み5,000–7,200行・上限8,400行は据え置く。停止点2には未到達。承認待ちは挟まず続行する。

## 30. 3b-2 続行：積 end の Hom 成分表示

### 30.1 検証済みの部品

コード `3de36dfc2`、新規6本395行。累計58本3,669行。

- `CochainProductTotalComponents`：任意の非負余鎖二重複体について、零延長の指定行同型と積射影、逆の成分 lift、指定積錐の極限性。元の余単体図式に限らないので、正規化した重みの end にも適用できる。
- `CochainProductTotalLinearComponents`：同じ指定射影による、各全次数と成分加群の積の線形同値。
- `ExtendedChainHomRows`：非負鎖重みを負次数へ零延長したものからの斉次射を、元の鎖次数 n の射の族で線形に表示。正の次数は零対象の一意性で処理。
- `ExtendedChainHomDifferential`：その成分表示で Hom 微分を縦横の二項に展開。零鎖次数では横項が実際の零延長によって消える。
- `WeightEndHomSigns`：成分の符号 `(-1)^(n(q+1)) εₙ` の縦・横の漸化式、平方が1、零鎖次数が1を証明。
- `WeightEndHomComponents`：積 end の各次数から、負次数へ延長した同じ重みからの斉次射への符号付き線形同値。

最後の宣言は次数ごとの同値であり、複体同型や native な錐の極限性を主張するものではない。微分の可換性は次の工程。

### 30.2 検証と登録待ち

個別検査と新規6本の鍵付き対象ビルド成功（2,305 jobs）。累計58本の一時監査は **709宣言、標準三公理のみ**。`sorry`・独自公理0。`--wait 3600`、整理券一枚、一回1,700秒上限で終了コード0。鍵は解放済み。ログ `/private/tmp/isw2-g10-build-16.log`、監査 `/private/tmp/AuditISW2G10FiftyEight.lean`、一覧 `/private/tmp/isw2-g10-fiftyeight-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainProductTotalComponents
SerrePositivity.HomologicalAlgebra.CochainProductTotalLinearComponents
SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows
SerrePositivity.HomologicalAlgebra.ExtendedChainHomDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomSigns
SerrePositivity.HomologicalAlgebra.WeightEndHomComponents
```

### 30.3 残り

停止点2には未到達。積全微分と上記の線形同値の可換性、正規化鎖の Hom と BK 切断比較、指定 join 錐と極限性、D(A) への輸送と全射・指定錐の族を残す。`CochainProductTotalDifferential.lean` は個別検査中の未コミット下書き。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

見込み5,000〜7,200行、上限8,400行は据え置き。夜の指示どおり承認待ちは挟まない。停止点2を閉じた後は、3b-3との依存関係を紙に書いてから3b-4のBE模型へ進む。

## 31. 3b-2 続行：積 end–Hom の複体同型と実正規化 BK 比較

### 31.1 閉じた比較

コード `a91223d7f`（5本317行）・`2069f341e`（1本57行）、今回6本374行。累計64本4,043行。

- `CochainProductTotalDifferential`：任意の非負余鎖二重複体の積全微分を、正の横次数の横項と符号付き縦項、零横次数の縦項で表示。零延長の指定行同型を保持する。
- `ExtendedChainHomRowDifferential`：零延長した鎖重みからの Hom 微分を、同じ全次数の成分の族へ戻した二つの公式。評価先の等式に伴う輸送も明示。
- `WeightEndHomEvaluation`：§30の次数同値の各成分は、元の積射影に指定符号を掛けたもの。零鎖次数の評価は変わらない。
- `WeightEndHomDifferential`：この次数同値が微分と可換であることを証明。縦項は `weightEndHomSign_vertical`、横項は `weightEndHomSign_horizontal` で合わせる。
- `WeightEndHomIso`：同じ次数同値を前向きの射に持つ、非有界積 end と線形 Hom 複体の実際の同型。
- `CosimplicialTotalization.NormalizedBousfieldKanHomComparison`：元の積 Tot → 指定 BK over end → Moore 包含による正規化 end → 上記 Hom 同型を合成した鎖ホモトピー同値。前向き射を明示して同じ射であることを証明し、擬同型も得た。重みは図式圏での実 Moore 正規化であり、通常の π₀ の Hom への置き換えではない。

### 31.2 検証と登録待ち

全6本の個別検査成功。先の5本の鍵付き対象ビルド（2,310 jobs）と累計63本の監査 **754宣言、標準三公理のみ**、最後の1本の鍵付き対象ビルド（2,539 jobs）と累計64本の監査 **766宣言、標準三公理のみ**が成功。`sorry`・独自公理0。各回 `--wait 3600`、整理券一枚、実行上限1,700秒、終了コード0。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-17.log`・`/private/tmp/isw2-g10-build-18.log`。最終監査 `/private/tmp/AuditISW2G10SixtyFour.lean`、一覧 `/private/tmp/isw2-g10-sixtyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainProductTotalDifferential
SerrePositivity.HomologicalAlgebra.ExtendedChainHomRowDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomEvaluation
SerrePositivity.HomologicalAlgebra.WeightEndHomDifferential
SerrePositivity.HomologicalAlgebra.WeightEndHomIso
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomComparison
```

### 31.3 native 錐への残り

停止点2には未到達。§30で残した end–Hom の微分可換性と複体同型は閉じた。残りは、実正規化鎖から Dold–Kan Hom 空間への比較、指定 join 錐の構成とその制限写像の同値性、D(A) への輸送、全射・指定錐の族と加群版入口。

既存の `Kerodon/LimitsAndColimits/HomotopyLimitsAndColimits/GeneralHomHolimComparison` は、任意の小圏について `weightedCoherentConeSectionsComparison_homotopyEquivalence` と `reflectedHomHolimConeComparison_homotopyEquivalence` を供給する。離散・cospan・tower に限定した旧入口から一般化し直す必要はない。ただしここでの係数は反転した豊穣 Hom なので、今回の線形 BK 重みから移すときに反転と Dold–Kan の比較を明示し、元の指定錐の脚・高次単体と照合する必要がある。`dgNerve_isLimitCone_iff_homTargetPointedRestriction` と `coherentCone_isLimit_iff_reflectedNativeComparison` が要求する実際の join 錐を、この複体比較だけで代用しない。

見込み5,000〜7,200行、上限8,400行は据え置き。既存宣言・⑤aのファイル・入口・公式監査は変更していない。夜の指示どおり承認待ちは挟まず続行する。

## 32. 3b-2 続行：図式圏の Dold–Kan Hom と指定 BK 錐入力

### 32.1 検証済みの進捗

コード `81b5d243d`（8本505行）・`471857f6e`（2本102行）。今回10本607行、累計74本4,650行。

- `NegativeExtendTruncationHom`・`NegativeExtendTruncationNaturality`・`NegativeExtendTruncationTarget`：任意のアーベル圏で、負次数への零延長からの射と smart 切断への射を、同じ包含を使って同定。始域の全鎖射・標的の全複体射への自然性を証明した。既存の加群圏に固定された宣言は変更していない。
- `NormalizedWeightHom`：上記と Dold–Kan 随伴を合成し、図式圏で実 Moore 正規化した重みからの複体射を、元の単体的重みから Γ(truncLE′ H) への射と同定。重み・係数の両自然性を持つ。
- `CopowerUnitHom`・`CopowerUnitHomDiagram`・`CopowerUnitHomBifunctor`：指定余積包含の1で評価する同値を、集合、全図式、全二変数図式へ順に持ち上げた。小さい集合は ULift し、単体方向と添字圏方向の全作用素を保つ。
- `NormalizedLinearWeightHom`：実正規化線形重みからの複体射を、線形化前の集合的重みから Dold–Kan の集合値単体図式への自然変換へ移す同値。単なる次数ごとの写像の族ではない。
- `CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative`：Hom–Tot 比較と正規化 BK 比較で元の Tot への射の零次閉元を移し、実複体射へ戻した。特に元の Tot の恒等射から、頂点を元の Tot とする指定錐の複体代表を構成。
- `CosimplicialTotalization.NormalizedBousfieldKanSetCone`：同じ二重反対圏上の集合的 over 重みを固定し、その線形化が既存の係数重みそのものであることを `rfl` で証明。指定錐代表を、両方向の全作用素を持つ集合的な単体写像へ移した。

最後の宣言は native な join 錐へ渡す入力であり、join 錐やその極限性の宣言ではない。頂点の選び直しはしていない。

### 32.2 検証と登録待ち

全10本の個別検査成功。鍵付き対象ビルドは、8本（1,800 jobs）、錐の複体代表（2,553 jobs）、集合的錐入力（2,577 jobs）が成功。累計監査は順に72本846宣言・73本855宣言・74本 **865宣言、標準三公理のみ**。`sorry`・独自公理0。各回 `--wait 3600`、整理券一枚、一回1,700秒上限、終了コード0。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-19.log`〜`/private/tmp/isw2-g10-build-21.log`。最終監査 `/private/tmp/AuditISW2G10SeventyFour.lean`、一覧 `/private/tmp/isw2-g10-seventyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationHom
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationNaturality
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationTarget
SerrePositivity.HomologicalAlgebra.NormalizedWeightHom
SerrePositivity.HomologicalAlgebra.CopowerUnitHom
SerrePositivity.HomologicalAlgebra.CopowerUnitHomDiagram
SerrePositivity.HomologicalAlgebra.CopowerUnitHomBifunctor
SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHom
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanConeRepresentative
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
```

### 32.3 実測と残りの再見積もり

停止点2には未到達。指定錐を作るための恒等射からの複体代表と集合的入力はできた。一方、図式圏で取った smart 切断・Γ を対象ごとの dg Hom 空間へ照合する部分は、§31時点の一般の Hom 同値とは別工程であることを確認した。既存の加群版だけをそのまま図式版として使わない。

| 残り | 見込み（行） |
| --- | ---: |
| 図式圏の切断・Dold–Kan と対象ごとの Hom 空間の照合、指定評価 | 450〜650 |
| 全 Hom パラメータの BK 切断比較、反転係数と native 制限比較の同定 | 900〜1,300 |
| 指定 join 錐の構成、脚・高次成分の照合、D(A) への輸送 | 500〜850 |
| 全射・指定錐の族、加群版入口、検証の調整 | 400〜650 |

残り2,250〜3,450行、完成見込み **約6,900〜8,100行**（従来5,000〜7,200行から更新）。上限 **8,400行**、現在の残枠3,750行。現時点では上限内の見込みなので承認待ちは挟まない。超えそうになれば、夜の指示どおり検証済みを保存し、その線の Lean を止めて3b-3/3b-4の境目の紙の作業へ移る。

一般の切断比較には§31.3の `GeneralHomHolimComparison` を使う。実際の join 錐への戻しには `CoherentConeSectionSpace.fixedVertexConeSpaceEquiv` / `CoherentConeSections.cosliceSectionCone` が既存だが、必要な指定脚と高次単体の照合はまだ証明していない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 33. 3b-2 続行：点ごとの切断・Γ と指定 BK 錐入力

### 33.1 検証済みの進捗

コード `1d4aefcd3`（7本346行）・`a98934a6a`（3本110行）。今回10本456行、累計84本5,106行。

- `DoldKanGammaMap`・`DoldKanGammaMapNaturality`・`DoldKanGammaDiagram`：Γ の指定余積比較を、単体方向・鎖射・加法関手の自然変換について証明し、図式圏の Γ と各点の Γ を全関手の自然同型で比較した。
- `NegativeExtendTruncationAdjunction`・`FunctorComplexExchangeEquivalence`・`PointwiseExtendComplex`：既存の延長–切断 Hom 同値を随伴へ、成分交換を圏同値へまとめ、零延長を点ごとの評価と交換する全自然同型を構成した。
- `PointwiseTruncationAdjunction`：上の指定零延長比較を左随伴側で移し、右随伴の一意性から切断の比較を得た。比較と余単位の可換性も証明し、任意に選んだ同型で代用していない。
- `PointwiseTruncation`・`PointwiseTruncationGamma`：成分交換の単位・余単位と指定 mate を合成し、図式圏の smart 切断と Γ を点ごとの切断・Γ に結ぶ全関手同型を構成した。
- `PointwiseBousfieldKanSetCone`：§32 の指定 BK 錐入力を同じ頂点のまま、各点の Hom 複体から取った単体集合の全図式へ輸送した。これはまだ native な join 錐ではない。

### 33.2 検証と登録待ち

鍵付き対象ビルド2回（1,629 jobs、2,588 jobs）、累計監査81本915宣言、84本 **935宣言、標準三公理のみ**。両回終了コード0、`sorry`・独自公理0。`--wait 3600`、一枚の整理券、一回1,700秒上限。鍵は解放済み。

ログ `/private/tmp/isw2-g10-build-22.log`・`/private/tmp/isw2-g10-build-23.log`。最終監査 `/private/tmp/AuditISW2G10EightyFour.lean`、一覧 `/private/tmp/isw2-g10-eightyfour-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.DoldKanGammaMap
SerrePositivity.HomologicalAlgebra.DoldKanGammaMapNaturality
SerrePositivity.HomologicalAlgebra.DoldKanGammaDiagram
SerrePositivity.HomologicalAlgebra.FunctorComplexExchangeEquivalence
SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationAdjunction
SerrePositivity.HomologicalAlgebra.PointwiseExtendComplex
SerrePositivity.HomologicalAlgebra.PointwiseTruncationAdjunction
SerrePositivity.HomologicalAlgebra.PointwiseTruncation
SerrePositivity.HomologicalAlgebra.PointwiseTruncationGamma
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBousfieldKanSetCone
```

### 33.3 残り

停止点2には未到達。次は反転した豊穣 Hom を使う既存 native 比較との照合。既存 `AlternatingFaceReverse` の指定符号同型を Moore 包含・射影と合成すれば、反転重みの実正規化を元の正規化へ鎖ホモトピー同値で戻せる。これを指定錐代表に前合成し、単体順序を再反転する経路で進める。反転を恒等射とは扱わない。

その後、指定脚・高次単体の照合、実 join 錐と極限性、D(A) への輸送、全射・指定錐の族が残る。完成見込み約6,900〜8,100行、上限8,400行は据え置き。残枠3,294行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。夜の指示どおり承認待ちは挟まず続行する。

## 34. 3b-2 続行：反転 Hom への指定錐入力

コード `27e0437b2`、新規3本133行。累計87本5,239行。

- `NormalizedMooreReverse`：反転した単体的対象の Moore 正規化から元の正規化へ、指定包含・交代面反転符号同型・指定正規化射影を合成した鎖ホモトピー同値を構成。前向き射を全自然変換として固定し、同じ射である等式を証明した。
- `ReflectedBousfieldKanSetCone`：上の射の負次数延長を指定錐代表に前合成し、反転した BK 重み上の集合的錐入力を得た。
- `ReflectedPointwiseBousfieldKanCone`：点ごとの切断・Γ へ移し、二度の反転を解く指定同型を使い、元の BK 重みから反転 Hom 図式への全自然変換を構成した。

個別検査、鍵付き対象ビルド2,591 jobs、累計87本 **956宣言、標準三公理のみ**の一時監査が成功。`sorry`・独自公理0、終了コード0。`--wait 3600`、一枚の整理券、一回1,700秒上限。ログ `/private/tmp/isw2-g10-build-24.log`、監査 `/private/tmp/AuditISW2G10EightySeven.lean`、一覧 `/private/tmp/isw2-g10-eightyseven-modules.txt`。鍵は解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NormalizedMooreReverse
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBousfieldKanSetCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedPointwiseBousfieldKanCone
```

停止点2には未到達。今回の反転 Hom は Mathlib Γ で書いた点ごとの Hom なので、既存 `doldKanSimplicialHomIso` の逆向きと全図式射への自然性を通じて、`reflectedHomHolimConeComparison` の豊穣 Hom に照合する必要がある。そこから実 join 錐を取り、指定脚・高次単体と制限比較の同定、極限性、D(A) への輸送、全射・指定錐の族を閉じる。反転重み上の射の構成だけを native 錐の極限性とは数えない。

完成見込み約6,900〜8,100行、上限8,400行は据え置き、残枠3,161行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 35. 3b-2 続行：実豊穣 Hom と元の Tot の native coherent 錐

### 35.1 検証済みの進捗

コード `0df2624c7`（3本149行）・`1299dd4e4`（3本138行）。今回6本287行、累計93本5,526行。

- `DiagramComparison.DoldKanClosedPostcomposition`：⑤a の既存 `EInfinity.ComplexLimits.standardDoldKanModuleIso_chainMap` を再利用。標準成分の全単体で鎖写像の作用と同じ閉射の豊穣後合成を照合し、指定 Γ 同型の後合成自然性を証明した。⑤a の既存ファイルは変更していない。
- `DiagramComparison.ComplexDoldKanHomDiagram`：元の複体の Γ Hom と、閉複体射圏の実豊穣 Hom を全関手の自然同型で結んだ。
- `EnrichedBousfieldKanCone`：指定錐入力を元の実反転豊穣 Hom の全図式へ輸送。遷移射を便宜的に定義し直していない。
- `SmallBousfieldKanWeight`：AsSmall で持ち上げた over の射列を元の射列へ戻す全自然変換を構成。係数環の宇宙を0に制限しない。
- `ReflectedWeightedNativeCone`：任意の指定 BK 自然変換を重み付き end の零単体にし、既存の `reflectedHomHolimConeComparison` と `fixedVertexConeSpaceEquiv` で実 join 錐を構成。左端の指定頂点の等式と、元の切断点への往復等式を証明した。
- `NativeCoherentCone`：上記を今回の入力へ適用し、元の積 Tot を頂点とする実 native coherent join 錐を構成。頂点の厳密な等式 `nativeCoherentCone_vertexMap` を証明した。極限性はまだ証明していない。

### 35.2 検証と登録待ち

再利用する既存対象の依存ビルド2回（5,934 jobs、4,260 jobs）、新規対象ビルド2回（6,034 jobs、6,045 jobs）が成功。新規対象の累計監査は90本988宣言、93本 **1,009宣言、標準三公理のみ**。`sorry`・独自公理0、各回終了コード0。鍵は `--wait 3600`、一枚の整理券、一回1,700秒上限、現在解放済み。

依存ログ `/private/tmp/isw2-g10-dependencies-25.log`・`/private/tmp/isw2-g10-dependencies-26.log`、対象ログ `/private/tmp/isw2-g10-build-27.log`・`/private/tmp/isw2-g10-build-28.log`。最終監査 `/private/tmp/AuditISW2G10NinetyThree.lean`、一覧 `/private/tmp/isw2-g10-ninetythree-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPostcomposition
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDoldKanHomDiagram
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBousfieldKanCone
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallBousfieldKanWeight
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedNativeCone
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeCoherentCone
```

### 35.3 残り

停止点2には未到達。実 join 錐と元の頂点は得られた。残りは標準脚・高次成分の照合、全 Hom パラメータの比較と native 制限への同定、極限性、D(A) への輸送、全射・指定錐の族。

`GeneralHomHolimComparison` の比較同値だけでは、元の Tot からの Hom 比較が同値であることにはならない。既存の鎖ホモトピー同値を単体的な全パラメータ比較へ接続し、その射が今回構成した錐からの制限であることを示す必要がある。⑤a の `NormalizedTensorHomBifunctor.normalizedTensorHomDoldKanIso`（正確な宣言は `SerrePositivity.EInfinity.ComplexLimits.normalizedTensorHomDoldKanIso`）が全パラメータ Hom の再利用候補。通常の導来極限の Hom 同値だけで native 極限性を代用しない。

完成見込み約6,900〜8,100行、上限8,400行を現時点では据え置く。残枠2,874行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 36. 3b-2 続行：零次数評価・dg 錐・全 Hom パラメータ

コード `f6cc52ea3`、新規3本138行。累計96本5,664行。

- `NormalizedMooreReverseEvaluation`：指定 Moore 反転比較を非正規化複体の包含後に計算する式を証明。零次数では元の評価を厳密に保つ。標準脚の照合に使う部品であり、native 錐の脚との最終等式はまだ閉じていない。
- `NativeDGCone`：指定 coherent 錐全体を既存 `coherentComparison` で後合成し、同じ strict 図式の実 dg nerve の join 錐を構成。coherent 錐と dg 錐の両方について、頂点が元の積 Tot である等式を証明。
- `ReflectedWeightedHomComparison`：指定 BK 入力に任意の反転豊穣 Hom 単体を前合成する全パラメータ族を構成。既存の豊穣合成と閉射への自然性を使い、全添字射について自然な族を重み付き end への実射にまとめた。点や通常 Hom だけの比較ではない。同値性と native 制限への一致は別の残課題。

個別検査、鍵付き対象ビルド6,048 jobs、累計96本 **1,021宣言、標準三公理のみ**の一時監査が成功。`sorry`・独自公理0、終了コード0。`--wait 3600`、一枚の整理券、一回1,700秒上限。鍵は解放済み。ログ `/private/tmp/isw2-g10-build-29.log`、監査 `/private/tmp/AuditISW2G10NinetySix.lean`、一覧 `/private/tmp/isw2-g10-ninetysix-modules.txt`。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseEvaluation
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone
SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedHomComparison
```

停止点2には未到達。現在の中心課題は、今回の全豊穣 Hom 比較を既存の非有界 Hom–Tot/BK 鎖比較へ照合し、同値性を証明すること。さらに元の錐に対する native 制限との一致（または頂点評価を保つ族による比較）を証明する。Γ の零単体での Hom 同値だけでは全単体の同値性の代わりにならない。標準脚の最終等式、D(A) への輸送、全射・指定錐の族も残る。

完成見込み約6,900〜8,100行、上限8,400行は据え置き、残枠2,736行。既存宣言・⑤aのファイル・入口・公式監査は変更していない。

## 37. 3b-2：指定 Γ 比較の検証と、規模による中間停止

### 37.1 検証済み

コード `2e23f92a7`、新規2本122行。累計 **98本5,786行**。

- `DiagramComparison.TruncatedDoldKanQuasiIso`：実 pinched Hom と Γ の既存の自然比較を使い、非有界複体の指定した擬同型の smart 切断・Γ 像が単体的ホモトピー同値になることを証明した。単位 Hom の指定同型を通すので、別の射に取り替えていない。
- `CosimplicialTotalization.NormalizedBousfieldKanHomSpace`：元の Hom–Tot/BK 比較を鎖ホモトピー同値として保持し、その同じ Γ 像の単体的ホモトピー同値性を証明した。標的は正規化 BK Hom 複体の Γ であり、重み付き切断空間との同定はまだない。

個別検査と鍵付き対象ビルド **4,355 jobs**、累計98本 **1,041宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。鍵は `--wait 3600`、一枚の整理券、一回1,700秒上限、解放済み。ログ `/private/tmp/isw2-g10-build-31.log`、監査 `/private/tmp/AuditISW2G10NinetyEight.lean`、一覧 `/private/tmp/isw2-g10-ninetyeight-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TruncatedDoldKanQuasiIso
SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomSpace
```

既存宣言・⑤aのファイル・入口・公式監査は変更していない。

### 37.2 残る全単体比較と短縮経路の検討

Γ の零単体の随伴同値を全単体へ拡張する際、二つの始域を区別する必要がある。重み W、単体 Δ[n]、係数 Hom 図式 H に対して、切断空間側は `N_A(W × Δ[n])` から H への図式射、Γ Hom 側は `N_A(W) ⊗ N_A(Δ[n])` から H への図式射として現れる。正規化・負次数延長・宇宙持ち上げを含む指定比較と、その n・図式添字への自然性が必要になる。型が似ていることや零単体の一致では同値性を閉じられない。

確認した再利用候補：

1. `EInfinity.ComplexLimits.normalizedTensorHomDoldKanIso` は実テンソル Hom と Γ Hom の全二変数同型を供給する。ただし `N(W × Δ[n])` と正規化テンソルの比較はこの宣言の結論ではない。
2. Kerodon 配置の `DifferentialGradedCategories.normalizedEZHomotopy` と `KST.ProExcision.NormalizedEZHomotopyNaturality` は具体的 AW・shuffle とその自然なホモトピーを供給する。確認した型は `SimplicialObject (ModuleCat ℤ)`。一般 A の自由線形化に移し、今回の Moore 正規化・負次数延長・全パラメータの比較へ接続する仕事が残る。一般 A の鎖写像としては `EInfinity.Shuffle` が再利用候補だが、必要なホモトピー全体への直接適用はまだ確認できていない。
3. `HomotopicalAlgebra.Diagram.WeightedFrameHomNaturality` には全関手の Hom 同型がある。しかし確認した関連フレームの普遍性は模型構造とその比較の仮定を持つ。IS-W2 が禁止する `[ModelCategory SSet]` を追加する近道にはしない。
4. 既存 `coherentCone_isLimit_of_family_lifts` は native 錐を作り直さずに使える。必要なのは指定した全 Hom 族の持ち上げ・頂点評価の等式・制限の同値性。今回の Γ 比較だけでこの三条件が済んだとはしない。`reflectedWeightedHomComparison` の豊穣合成と同じ射になる照合が残る。

従来の完成見込み6,900〜8,100行は、(1) の全二変数同型から切断空間への接続と (4) の指定制限への照合を軽く数えすぎていた。確認済み API に基づく暫定的な残量は次のとおり。下限も完成の保証ではない。

| 未実装のまとまり | 追加見込み |
| --- | ---: |
| 正規化テンソル／積重みの比較、一般 A と全単体への自然性、同じ Γ 比較との照合 | 1,000〜1,600行 |
| 指定豊穣 Hom 合成・native 切断への持ち上げと頂点評価、極限性 | 600〜900行 |
| 標準脚の最終等式、D(A) への輸送 | 400〜700行 |
| 全図式射・指定錐の族・離散加群版入口 | 500〜900行 |
| 残り合計 | **2,500〜4,100行** |

完成見込み **8,286〜9,886行（約8,300〜9,900行）**、現在の上限 **8,400行**、残枠2,614行。上端が上限を超えるため、検証済みを上記コミットへ保存し、**3b-2 の Lean を中間停止する**。これは停止点2ではない。範囲・型を弱めず、上限を独自に引き上げない。夜の指示に従い、承認待ちで紙の作業まで止めず、次節の境目の整理へ移った。

## 38. 夜の代わりの作業：3b-3 と3b-4の境目

以下は型案と依存の整理であり、Lean の宣言や証明の完了報告ではない。3b-3 は③-a、BE 固有の3b-4は③-b。点つき Kan Tot は作らず、⑤aの既存ファイルも変更しない。

### 38.1 ③-a から使う入力

J は Δ・Δᵒᵖ の二つだけに固定する。略記 `I_J = nerve J`、`DA = derivedInfinityCategory A` とする。

| 入力の型案 | 必要な強さ／使用箇所 |
| --- | --- |
| `eval_A,J : StrictDiagramInfinity_A J → Fun(I_J, DA)` とその QCat 同値 | strict 複体図式の objectwise 擬同型による局所化からの実評価。BE 図式を忘却した strict 複体図式を、任意の coherent な D(A) 図式へ比較する段階 |
| `nerve (J ⥤ Complex A)` 上の実評価との全関手同型 | 忘却した元の図式の射・全単体を保持する。対象ごとに選んだ同値だけでは U との比較の正方形にならない |
| 図式の FunctorIso に沿う指定 join 錐／余錐の輸送と往復比較 | 同じ頂点・脚・高次単体を持つ錐の族の輸送。極限性／余極限性の保存と図式射への自然性まで |
| 3b-1から移した実現の全パラメータ比較 | strict な複体図式の実現関手と native な実現錐の族の比較。BE 実現の U 像を全関手として識別する最後の段階 |

G10 の指定 Tot 錐・全図式射の比較は引き続き3b-2の責任。3b-3 の評価同値の証明を G10 だけに依存させる循環は作らない。

### 38.2 BE 側の別の不足を D(A) の厳密化で隠さない

`Fun(I_J, DA)` の厳密化から、`Fun(I_J, CAlg_A)` の厳密化は自動的には出ない。忘却した図式を厳密化しても、BE 作用や coherent な代数射をその持ち上げに回復できたことにはならない。

したがって3b-4の段取りを次のように分ける。

1. **strict BE 図式での模型計算**：`J ⥤ (BarrattEccles.operad A).Algebra` の実現・Tot を置換と指定錐つきで扱う。これは加群値の3b-3を待たず検討できる。既存 `BarrattEccles.Diagram.projectiveModelCategory`・`weakEquivalence_iff` は図式の置換と弱同値判定に使うが、projective 全対象 fibrant を理由に通常 lim を導来 lim と同定しない。
2. **strict 図式の U 比較**：既存 `algebraCAlgSource_underlyingDerivedIso` を実際の `cAlgForgetDerived` との接続に使う。置換前の台の図式と同じ全自然変換を保つ。実現では U が右 Quillen であることだけから保存を結論しない。
3. **任意の coherent BE 図式への拡張**：BE 図式の局所化から `Fun(I_J, CAlg_A)` への比較、または同じ役割を果たす一般定理の BE 模型への適用が別途必要。③-aの加群版の結論だけで済ませない。一般定理が供給されたときの BE 固有の仮定の確認は③-b側とする案。新たな BE 厳密化そのものの範囲・規模が必要なら、実装前に調整役へ判断事項として残す。

3 の入力がない所に来たら、対象ごとの strict 表示の存在を仮定に足して先へ進まない。任意の coherent BE 図式の主張を strict 図式に黙って狭めない。

### 38.3 提案する比較の形と受け渡し

以下の名前は説明用の仮名で、既存宣言名ではない。

- `RealizeBE` と `TotBE` はそれぞれ strict 図式の局所化上の全関手。忘却との比較は `FunctorIso (RealizeBE ≫ U) (U_Diagram ≫ RealizeDA)`、`FunctorIso (TotBE ≫ U) (U_Diagram ≫ TotDA)` の形にする。
- それぞれに指定 join 余錐／錐の族を持たせ、比較同型の成分だけでなく、各脚・高次単体の U 像との両立を渡す。全単体が必要な点は今回の G10 の残課題と同じであり、零単体の Hom 同型で代用しない。
- 3b-3 による図式同型と錐輸送を使う場所は、strict BE 図式の台の模型計算が済んだ後。BE 側の coherent 図式の比較が得られた場合にのみ、その両方向の輸送へ拡張する。
- `EInfinityTheory.ofCosimplicial_forget` へ渡す制限は、余単体環代数を離散 BE 代数へ送った図式に固定する。`nerveMap (cosimplicialCochains A) ≫ strictToD A` との既存の型を保つ。
- `ofCosimplicial_cone` は上と同じ頂点の `TotalizationCone` を返す。別の極限対象を選んで `HasLimit` だけ返す形にしない。制限・係数変更の自然性は⑤aの既存の欄に合わせ、こちらで欄の型を変更しない。

### 38.4 置き場所・再利用・再開順

新規の BE 固有補助は `EInfinity/BarrattEccles/` の新規ファイル（仮案 `DiagramRealizationComparison`、`DiagramTotalizationComparison`、`DiagramForgetConeComparison`）。一般の図式局所化比較は③-aの `Project/DerivedCategories/DiagramComparison/` と役割を分け、一般の native 錐輸送は Kerodon の該当節へ置く。⑤aの `CAlgUnderlyingDerivedComparison`・frame・忘却関手の既存ファイルは読み取りと import の対象だけにする。

再利用候補は `HomotopyWeight` の実現とフレーム比較、`CAlgUnderlyingDerivedComparison` の実 U への全自然同型、3b-1の指定実現余錐、完成後の G10 の指定 Tot 錐。⑤aの報告§21.5にあるとおり、通常の sifted colim の創出や右 Quillen 性だけで導来実現の保存を済ませない。`forget_preservesSifted` を入力にしてその実現部分を証明する循環も作らない。

再開時はまず G10 の規模の判断を反映し、上記§37.2の全単体比較を閉じる。停止点2の後、strict BE 図式の計算を進める。③-aの3b-3の入力が揃うまでは境目を保ち、BE 値の厳密化の不足を加群版の供給済み欄へ押し込まない。今回の紙の整理のためのビルドは不要。鍵は取得していない。

## 39. 中間停止中の紙の確認：EZ の係数変更を短縮する候補

main の IS-W2 §10 までを再確認した。G10 の上限8,400行を変更する追記はまだないため、§37の Lean の中間停止を維持する。前ターンは検証済みコードと境界の報告を保存した進捗であり、鍵待ちではない。

§37.2の一般 A への移送について、再開時に先に試す短縮候補を具体化した。

- Mathlib `Algebra/Homology/Homotopy.lean` の `Functor.mapHomotopy`・`Functor.mapHomotopyEquiv` は加法的関手で実鎖ホモトピーを運ぶ。従って ℤ 上の EZ のホモトピーを `ModuleCat.extendScalars (Int.castRingHom A)` で運ぶ部分に、A の ℤ 上の平坦性を追加する必要はない。擬同型の底変換一般を使う議論とは区別する。
- 本体 `HomologicalAlgebra/CochainTensor/BaseChange.lean` の `cochainTensorBaseChangeIso` と `map_ι_cochainTensorBaseChangeXIso` は、整数コチェイン複体でのテンソルの実底変換同型と各余積成分の式を持つ。負次数延長後のテンソル部分を一から作り直さない候補になる。
- Moore 正規化と底変換の交換は、一般の核の保存を要求する形にしない。Moore 包含・射影と `PInfty` による分裂を加法的関手で運び、A 上の指定された分裂と比較する案を優先する。その後、自由線形化の底変換同型を全単体・全重み添字について照合する。ここはまだ Lean 未検証。
- 残る核心は、得られた射が今回の `normalizedBousfieldKanHomSpaceComparison` と `reflectedWeightedHomComparison` を結ぶ同じ射であること。n ごとの鎖ホモトピー同値だけでは単体的 Hom 比較の同値性を証明したことにならない。n の面・退化への自然性、ホモトピーを全パラメータへ移す比較、native な頂点評価との一致を残件として保つ。

この候補は一般 A の部分の再実装を減らし得るが、上記の未検証の接続を零行とは数えない。§37の完成見込みを下げて Lean を再開するだけの根拠にはまだならない。型・範囲・⑤aのファイルは変更していない。今回は読取りと文書のみで、ビルド・鍵の取得は行っていない。

## 40. 11-13承認後の再開：指定 Moore 分裂の加法関手による移送

ユーザー承認により3b-2の上限を **10,000行**へ変更し、§37の中間停止を解除して Lean を再開した。残りは§37.2の四つのまとまりに限定する。小さな同定補題の追加許容は3本まで、四つの外の新しいまとまりが必要になれば検証済みを保存して停止する。累計約7,900行で止まらずに実測・残量を報告する。型・範囲の弱化、`[ModelCategory SSet]` の追加、⑤aの既存ファイルの変更は行わない。停止点2の後に3b-4のBE部分へ進む。

コード `d18645332`、新規 `SerrePositivity.HomologicalAlgebra.NormalizedMooreMap`（107行）。累計 **99本5,893行**。

§39の短縮候補を先に実装した。Mathlib の `map_PInfty_f` と交代面複体の指定自然同型を使い、加法関手で移した Moore 分裂と、移した単体的対象の元の Moore 分裂の間に自然同型 `normalizedMooreMapNatIso` を構成した。前向き射は移した包含・交代面比較・指定射影の合成、逆射も指定された分裂の合成。包含との等式と全単体的対象の射への自然性を証明した。核の保存・平坦性は要求していない。これは第一のまとまり（正規化テンソル／積重み比較の係数変更）の内部であり、別のまとまりを追加したものではない。

個別検査、鍵付き対象ビルド **1,330 jobs**、累計99本 **1,056宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-32.log`、監査 `/private/tmp/AuditISW2G10NinetyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-ninetynine-modules.txt`。鍵は `--wait 3600`、一枚、一回1,700秒上限、解放済み。入口・公式監査は変更していない。

次は、この同じ自然同型を使って係数拡大で運んだ EZ ホモトピーの始域・終域を照合する。テンソル側では既存 `cochainTensorBaseChangeIso` を再利用する。今回だけで一般AのEZ比較や全単体の重み付き切断比較が完了したとは数えない。停止点2は未完。現在の残枠は4,107行。

## 41. 3b-2 続行：既存 EZ ホモトピーの加法関手による移送

コード `1b07886d0`、新規 `SerrePositivity.HomologicalAlgebra.NormalizedEZMap`（91行）。累計 **100本5,984行**。

第一のまとまりの内部で、§39の `Functor.mapHomotopy` を使う候補を実装した。整数係数の指定 `normalizedEZHomotopy` を加法関手で運び、§40の Moore 比較同型で前後合成して、移した単体的対象の元の Moore 正規化上のホモトピーへ戻した。`mappedNormalizedAlexanderWhitney`・`mappedNormalizedShuffle` は指定された AW・shuffle の像と同じ Moore 同型から構成し、両入力の全単体的射への自然性を証明した。係数拡大は加法関手の特殊例として適用でき、平坦性を要求しない。

結論は AW の後に shuffle を合成した射と恒等の鎖ホモトピーである。この一方の合成のホモトピーだけから、全単体の切断比較が同値と結論していない。テンソル側は移した元の整数テンソルを明示的に保持している。一般 A の正規化テンソルへの同定、積重みの自由線形化との同定、指定豊穣合成への照合は残る。

既存依存の鍵付きビルド **1,846 jobs**、個別検査、新規対象の鍵付きビルド **1,848 jobs**、累計100本 **1,067宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-33.log`・`/private/tmp/isw2-g10-build-34.log`、監査 `/private/tmp/AuditISW2G10Hundred.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundred-modules.txt`。共有鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限。現在解放済み。

次の接続には既存 `mapExtendNatIso`・`NegativeTensor.comparison`・`cochainTensorBaseChangeIso` を使う。今回、新しいまとまり・追加仮定・⑤aの既存ファイルの変更はない。停止点2は未完。10,000行までの残枠4,016行、約7,900行での非停止の中間報告の条件を保持する。

## 42. 3b-2 続行：負次数テンソルと係数拡大の指定比較

コード `90f5fcfe9`、新規 `SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChange`（39行）。累計 **101本6,023行**。

第一のまとまりの内部で、既存 `mapExtendIso`・`NegativeTensor.comparison`・`cochainTensorBaseChangeIso` をそのまま合成した。`negativeTensorBaseChangeIso` は、係数拡大した自然数鎖テンソルを負次数へ延長した複体から、係数拡大した二因子の負次数延長のテンソルへの指定同型。平坦性・有界性を要求せず、コチェインの既存の符号を保持する。

既存依存の鍵付き対象ビルド **1,962 jobs**、個別検査、新規対象の鍵付きビルド **1,965 jobs**、累計101本 **1,088宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-35.log`・`/private/tmp/isw2-g10-build-36.log`、監査 `/private/tmp/AuditISW2G10HundredOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredone-modules.txt`。共有鍵は `--wait 3600`、整理券は一枚、各回1,700秒上限、解放済み。

宇宙の接続を確認した。Mathlib の ModuleCat のモノイダル構造と既存 `cochainTensorBaseChangeIso` は環・加群を同じ宇宙に置く。一方、KST の `chainIntegerTensor` は任意の宇宙の整数加群のための明示的テンソルであり、今回の同型に直接代入できたとはしていない。この差には既存 `Project.DerivedCategories.DGIntegerCoefficientTensor` の `integerCoefficientTensorIso`・`integerCoefficientTensorComparison_naturality`、`simplicialRingIntegerModuleEquivalence` を再利用できる。持ち上げた整数環 `ULift ℤ` への移送を鎖テンソルまで結び、その後に今回の底変換同型を適用する。対象宇宙を0に制限しない。

この接続と、全図式射についての比較の照合はまだ未完。今回、全単体の切断比較や native 極限性を証明済みとは数えない。指定の四まとまりの外への追加、既存宣言・⑤aのファイル・入口・公式監査の変更はない。停止点2は未完、残枠3,977行。約7,900行での中間報告の条件を保持する。

## 43. 3b-2 続行：任意の宇宙の整数鎖テンソルと底変換の接続

コード `ee4e5a1f3`、新規2本247行。累計 **103本6,270行**。

- `DiagramComparison.IntegerCoefficientTensorDegrees`（93行）：既存の `integerCoefficientTensorIso` と余積比較を合成し、元の整数鎖テンソルの全次数を同宇宙の整数係数環のテンソルへ比較した。各二重次数の包含の公式と、元の二つの鎖写像への自然性を証明した。
- `DiagramComparison.IntegerCoefficientTensorDifferential`（154行）：次数が一致しない場合の零包含、第一・第二の部分微分、全微分を照合し、`integerCoefficientChainTensorIso` とその鎖写像への自然性を証明した。さらに `integerNegativeTensorBaseChangeIso` で、同宇宙の整数係数環から A への底変換を§42の比較に接続した。元の `chainIntegerTensor` を使い、宇宙を0に縮めない。

依存対象ビルド **2,126 jobs**、次数比較の対象ビルド **2,127 jobs**、複体同型の対象ビルド **2,211 jobs**と個別検査が成功。累計一時監査は102本1,107宣言、最終103本 **1,132宣言・標準三公理のみ**、いずれも終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-37.log`・`/private/tmp/isw2-g10-build-38.log`・`/private/tmp/isw2-g10-build-39.log`。最終監査 `/private/tmp/AuditISW2G10HundredThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthree-modules.txt`。鍵は `--wait 3600`、同時に一枚、各回1,700秒上限、解放済み。ビルドには長い行のスタイル警告があるがエラーはない。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDegrees
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDifferential
```

第一のまとまりの内部の接続であり、新しいまとまりではない。§41の移送した EZ ホモトピーを今回のテンソル同型で挟み、負次数の比較へ移す段と、自由線形化した積重みとの同定・全単体への照合が続く。今回だけで重み付き切断の同値性を証明済みとは数えない。指定の残り三まとまりも保持する。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、上限10,000行まで残枠3,730行。約7,900行での非停止の中間報告を保持する。

## 44. 3b-2 続行：一般 A の元の自由積鎖へ EZ ホモトピーを接続

コード `9f0e3070c`、新規3本234行。累計 **106本6,504行**。

- `DiagramComparison.NegativeEZCoefficient`（83行）：§43の整数テンソル底変換と指定 Moore 同型を合成。一般係数の負次数正規化テンソルへの指定 AW、その逆向きの shuffle、AW の後の shuffle を恒等へ結ぶ元のホモトピーを構成した。
- `DiagramComparison.IntegerCoefficientFree`（72行）：任意の宇宙の整数自由化の指定生成元による随伴を構成し、同宇宙の整数係数移送・係数拡大の随伴を合成。元の `ModuleCat.free A` との全自然同型を得た。指定単位の保存と、その生成元の像が元の A 自由加群の標準生成元である評価式を証明した。
- `DiagramComparison.FreeProductEZ`（79行）：既存 `linearizedTensorIso` と上記自由化比較を Moore 正規化・負次数延長へ送った。元の A 自由化した X×Y の正規化鎖から、X・Y の正規化鎖のテンソルへの AW と、その逆向きの shuffle を構成し、この積の複体上で AW→shuffle と恒等の鎖ホモトピーを証明した。

新規対象の鍵付きビルド **2,239 jobs**・**2,240 jobs**、個別検査が成功。累計一時監査は105本1,172宣言、最終106本 **1,195宣言・標準三公理のみ**、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-40.log`・`/private/tmp/isw2-g10-build-41.log`。最終監査 `/private/tmp/AuditISW2G10HundredSix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredsix-modules.txt`。鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientFree
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductEZ
```

いずれも第一のまとまりの内部。今回の鎖ホモトピーは一方の合成についてのもの。逆順の合成、最終 AW・shuffle の全単体パラメータへの自然性、既存の単位余積による BK 線形化との同定、Γ Hom／重み付き切断比較への照合を完了済みとは数えない。後続の指定 native 制限・極限性、標準脚・D(A) 輸送、全射・錐の族も残る。範囲・型の弱化、⑤aのファイル・既存宣言・入口・公式監査の変更はない。停止点2は未完、残枠3,496行。約7,900行で実測と残りを再見積もりする。

## 45. 3b-2 続行：指定係数 EZ 写像の全単体的射への自然性

コード `5ff48b6fd`、新規4本236行。累計 **110本6,740行**。

- `HomologicalAlgebra.CochainTensorBaseChangeNaturality`（43行）：既存 `cochainTensorBaseChangeIso` の両因子の鎖写像への自然性を標準余積包含で証明した。
- `HomologicalAlgebra.NegativeTensorBaseChangeNaturality`（54行）：零延長の自然同型、既存負次数テンソル比較、上記底変換の自然性を合成し、同じ `negativeTensorBaseChangeIso` の自然性を証明した。
- `DiagramComparison.CoefficientTensorNaturality`（73行）：整数係数移送と、最後に元の Moore 正規化へ戻す同型を含む自然性を証明した。
- `DiagramComparison.NegativeEZCoefficientNaturality`（66行）：同じ負次数 AW・shuffle の両入力について、任意の二つの単体的射への自然性を証明した。別の自然な写像を定義し直して置換していない。

全て第一のまとまりの「自然性・照合」の内部。四まとまりの外に新しいまとまりや補助的な主題を追加していない。合成の elaboration が200,000 heartbeatsに達した箇所は、比較の引数を明示して段階を分けて解消し、制限値は増やしていない。

依存対象の鍵付きビルド **1,964 jobs**、個別検査、新規対象の鍵付きビルド **2,242 jobs**、累計110本 **1,204宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-42.log`・`/private/tmp/isw2-g10-build-43.log`、最終監査 `/private/tmp/AuditISW2G10HundredTen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredten-modules.txt`。鍵は `--wait 3600`、整理券は同時に一枚、各回1,700秒上限、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CochainTensorBaseChangeNaturality
SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChangeNaturality
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientTensorNaturality
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficientNaturality
```

次は自由積鎖への最後の輸送に自然性を通し、元の重み付き切断比較と照合する。逆順の合成や全単体空間の同値性を今回の自然性だけで結論していない。指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・錐の族も保持する。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、残枠3,260行。約7,900行での非停止の中間報告の条件を保持する。

## 46. 3b-2 続行：元の自由積鎖上の指定 AW・shuffle の自然性

コード `12db1050c`、新規1本125行。累計 **111本6,865行**。

`DiagramComparison.FreeProductComparisonNaturality` で、指定自由化同型・積の係数同型・その二因子テンソルの自然性を証明した。その同じ同型で輸送した `freeProductAlexanderWhitney` と `freeProductShuffle` が、任意の二つの単体的集合の射に自然であることを証明した。元の自由正規化鎖の射を明記し、別の比較写像への取り替えはしていない。第一のまとまりの「自然性・照合」の内部である。

個別検査、鍵付き対象ビルド **2,246 jobs**、累計111本 **1,219宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-44.log`、監査 `/private/tmp/AuditISW2G10HundredEleven.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredeleven-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductComparisonNaturality
```

逆順の EZ 合成、BK 線形化で使う単位加群の余積との同定、全単体パラメータの Hom／重み付き切断比較との照合は残る。指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も完了済みとは数えない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。停止点2は未完、残枠3,135行。約7,900行で実測と残りの見込みを報告する。

## 47. 3b-2 続行：指定余積と自由線形重みの同定

コード `e02b135b5`、新規2本137行。累計 **113本7,002行**。

- `HomologicalAlgebra.CopowerUnitFree`（83行）：小さい添字集合 S の単位加群の指定余積と `ModuleCat.free A (ULift S)` の同型を構成した。両方向の指定生成元の像、逆射との合成、全添字写像への自然性を証明した。係数の宇宙は任意のまま。
- `HomologicalAlgebra.NormalizedLinearWeightFree`（54行）：同じ自然同型を図式圏と単体方向へ運び、既存 `linearizedSimplicialWeight` と自由線形化の比較を得た。重みの全自然変換への自然性、および同じ Moore 正規化・負次数延長による複体の同型を構成した。

第一のまとまりの既存線形化との照合であり、四まとまりの外の主題を追加していない。図式圏の正規化と点ごとの自由積比較の最終照合や、全単体 Hom／切断比較の同値性まで済んだとは数えない。

個別検査と鍵付き対象ビルド **1,835 jobs**、累計113本 **1,239宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-45.log`、監査 `/private/tmp/AuditISW2G10HundredThirteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CopowerUnitFree
SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightFree
```

次の確認候補：実際の全単体比較の第二因子は標準単体である。既存 `EInfinity.ComplexLimits.normalizedSimplexChainContraction`・`normalizedSimplexTensorContraction` を使い、指定 AW と増大写像の両立から必要な同値を得られるか確認する。この候補は未証明であり、一方の EZ ホモトピーだけで結論したものではない。⑤aの既存ファイルには変更を加えない。

指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,998行。約7,900行で実測と残量を報告する。

## 48. 標準単体の収縮による短縮候補の検査

§47末尾の候補を、既存の型と個別 Lean 検査で確認した。`freeNegativeChains (SSet.uliftFunctor.obj Δ[n])` は既存 `BarrattEccles.normalizedFunctor` の値と定義的に一致する。`normalizedSimplexCochainContraction` と `normalizedSimplexTensorContraction` はそのまま適用でき、順方向も `(𝟙 K ⊗ augmentation) ≫ ρ_K` と定義的に一致する。依存対象の鍵付きビルド **2,395 jobs** が成功し、個別検査も終了コード0。ログ `/private/tmp/isw2-g10-dependencies-46.log`・`/private/tmp/isw2-free-simplex-contraction-2.log`。鍵は解放済み。

ただし、これで第一のまとまりの全単体比較を閉じることはできない。各 n での鎖ホモトピー同値は、各 n の鎖写像の集合の全単射ではない。また、重みの図式方向の end を取る比較には、その方向で両立するホモトピーが要る。頂点を選んだ収縮を n ごとに適用しただけでは、必要な全単体の切断空間の比較や、その指定豊穣合成との一致は得られない。これらの橋を省略して同値性を主張しない。

今回の試作は既存定義の包み直しだけで、上記の不足を解消しないため、本体には残さない。個別検査を通した試作は `/private/tmp/isw2-free-simplex-contraction-tested.lean` に保存した。新規登録対象なし、累計 **113本7,002行**のまま。次は、正規化 shuffle→AW の合成の直接の照合を検討する。既存の `normalizedEZHomotopy` が供給する逆順（AW→shuffle）のホモトピーと取り違えない。停止点2は未完であり、四つのまとまり・10,000行上限・約7,900行での中間報告の条件は維持する。

## 49. 3b-2 続行：shuffle→AW の異なる二重次数の成分の消滅

コード `d9f60a395`、新規1本67行。累計 **114本7,069行**。

`DiagramComparison.ShuffleCutNormalization` で、既存格子路の両因子を AW で切断した写像がともに単射なら、切断点が元の第一次数 p に一致することを次元の不等式から証明した。切断点が異なる場合は少なくとも一因子が非単射になる。Mathlib の `degeneracy_comp_PInfty` と元の Moore 分裂を使って、その作用素と実 Moore 射影との合成が零であること、したがって正規化された実整数テンソル成分が零であることを証明した。第一のまとまりの合成の照合に属する。

個別検査、鍵付き対象ビルド **1,846 jobs**、累計114本 **1,245宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-47.log`、監査 `/private/tmp/AuditISW2G10HundredFourteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfourteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutNormalization
```

これは異なる切断点の成分の消滅であり、対角成分や正規化 shuffle→AW 全体の恒等式まで完了したものではない。対角では非退化の格子路の一意性・符号の確認、対角側の Moore 射影を挟む合成との照合が残る。全単体 Hom／切断比較、指定 native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も保持する。停止点2は未完、残枠2,931行。約7,900行で実測と残量を報告する。

## 50. 3b-2 続行：対角に残る格子路の一意性と符号

コード `213ae49a6`、新規1本76行。累計 **115本7,145行**。

`DiagramComparison.ShuffleCutDiagonal` で、最初の p 本を水平にした格子路 `initialShuffle` を定義した。対角の前半の切断が単射なら自己単射は恒等なので、終点の値と濃度から格子路がこれに一致することを証明した。また、この格子路の逆転数が零、shuffle 符号が +1 であることを証明した。第一のまとまりの対角成分の照合に属する。

個別検査、鍵付き対象ビルド **1,847 jobs**、累計115本 **1,255宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-48.log`、監査 `/private/tmp/AuditISW2G10HundredFifteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfifteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutDiagonal
```

残るのは指定格子路の両切断の恒等式、全成分の合成と途中の Moore 射影の照合である。正規化 shuffle→AW 全体の恒等式、全単体 Hom／切断比較、native 極限性などを完了済みとは数えない。停止点2は未完、残枠2,855行。約7,900行で実測と残量を報告する。

11-13 昼の B3 凍結予告を受領した。検証済みを上記コードと本報告に保存する。18時の確定連絡で凍結となれば、その後は枝へのコミットを控え、翌朝の main 取り込み・改名表の追従を一括レーンの B4 手順に従って行う。現時点で凍結の確定や改名の先行適用はしていない。

## 51. 3b-2 続行：指定格子路の両切断の恒等式

コード `b16fcbc8a`、新規1本88行。累計 **116本7,233行**。

`DiagramComparison.ShuffleCutValues` で、指定格子路の水平部分の初期 x ステップ、垂直部分の初期 x ステップの濃度を、それぞれ Fin x への明示的な全単射から計算した。この計算により、`awFront ≫ initialShuffle.left` と `awBack ≫ initialShuffle.right` が、それぞれの単体の恒等射であることを証明した。第一のまとまりの対角成分の照合である。

個別検査、鍵付き対象ビルド **1,848 jobs**、累計116本 **1,267宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-49.log`、監査 `/private/tmp/AuditISW2G10HundredSixteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredsixteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券で順番待ちし、取得後は1,700秒上限でビルド・監査の間だけ使用、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutValues
```

次は、有限和の非対角消滅・対角の一意性・符号・両切断の恒等式を同じ成分の合成へまとめる。正規化 shuffle と AW の間に挟まる対角側の Moore 射影の照合も必要であり、成分の計算だけで最終合成の恒等式が済んだとは数えない。全単体 Hom／切断比較、native 極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,767行。約7,900行で実測と残量を報告する。凍結予告は受領済みだが、今回のコミット時点では確定連絡は未受領。

## 52. 3b-2 続行：実 shuffle 成分と正規化切断の合成

コード `22a357334`、新規1本73行。累計 **117本7,306行**。

`DiagramComparison.ShuffleCutSum` で、対角切断の符号付き和を唯一の初期水平格子路へ簡約し、二因子の元の Moore 射影になる式を証明した。さらに、これを既存の `shuffleBidegree` と実際の切断写像との合成に結び、対角の合成は二因子の射影、非対角の合成は零となる式を証明した。第一のまとまりの成分の合成の照合である。

個別検査、鍵付き対象ビルド **1,849 jobs**、累計117本 **1,277宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-50.log`、監査 `/private/tmp/AuditISW2G10HundredSeventeen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredseventeen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutSum
```

次は切断点の和と標準余積包含を介して全テンソルへの式へまとめる。また、正規化 shuffle と AW の間に挟まる対角側の Moore 射影の照合が残る。この段階の成分の式から、正規化合成全体や全単体切断空間の同値性が済んだとは数えない。native 極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も残る。停止点2は未完、残枠2,694行。約7,900行で実測と残量を報告する。

## 53. 3b-2 続行：指定正規化 EZ の両方向の鎖ホモトピー同値

コード `8a91a1d27`、新規1本105行。累計 **118本7,411行**。

`DiagramComparison.ShuffleAWProjected` で、標準包含と AW の有限和を使い、元の鎖写像について `shuffle ≫ alexanderWhitney ≫ 二因子のMoore射影 = 二因子のMoore射影` を証明した。正規化した逆順合成に挟まる対角側の Moore 射影は、既存 `homotopyPInftyToId` で恒等へ結び、その後はこの等式と元の Moore 分裂を使った。これにより `normalizedShuffleAWHomotopy`、さらに既存の順方向のホモトピーと合わせた `normalizedSpecifiedEZEquiv` を構成した。hom・inv は既存の `normalizedAlexanderWhitney`・`normalizedShuffle` そのものである。

第一のまとまりの整数係数での逆順合成の不足が閉じた。射影を厳密に消すための追加の組合せ論は不要だった。一般 A への移送は既存 `Functor.mapHomotopy`、Moore 比較、係数テンソル比較で進める。ホモトピーの図式方向の両立や、全単体の指定切断比較への接続まで今回済んだとは数えない。

個別検査、鍵付き対象ビルド **1,872 jobs**、累計118本 **1,288宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-51.log`、監査 `/private/tmp/AuditISW2G10HundredEighteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredeighteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWProjected
```

全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,589行。約7,900行で実測と残量を報告する。型の弱化、模型構造の追加、⑤aの既存ファイルの変更はない。

## 54. 3b-2 続行：一般係数の指定自由積 EZ 同値

コード `6bfbd68d8`、新規1本66行。累計 **119本7,477行**。

`DiagramComparison.CoefficientEZEquivalence` で、§53の逆順ホモトピーを `Functor.mapHomotopy` により任意の加法関手へ移した。同じ Moore 比較、負次数延長、係数テンソル同型、最後の自由化同型を使い、既存 `freeProductAlexanderWhitney`・`freeProductShuffle` を hom・inv とする `freeProductEZEquiv` を構成した。任意の可換環 A で、積の A 自由正規化鎖と二因子の正規化鎖のテンソルの間の両方向の鎖ホモトピー同値であり、平坦性は要求しない。第一のまとまりの一般係数への移送である。

個別検査、鍵付き対象ビルド **2,246 jobs**、累計119本 **1,319宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-52.log`、監査 `/private/tmp/AuditISW2G10HundredNineteen.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundrednineteen-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientEZEquivalence
```

次はホモトピーの図式方向の両立と、元の全単体 Hom／切断比較への接続である。既存 KST の `ChainHomotopySquare` と `MooreHomotopyNaturality.moorePInftyHomotopy_naturality` が逆順ホモトピーの自然性にも使えることを確認したが、その自然性の証明は今回完了済みとは数えない。native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族も残る。停止点2は未完、残枠2,523行。約7,900行で実測と残量を報告する。

## 55. 3b-2 続行：指定逆順 EZ ホモトピーの自然性

コード `1934ab94f`、新規1本79行。累計 **120本7,556行**。

`DiagramComparison.ShuffleAWHomotopyNaturality` で、Moore 収縮への前合成（包含・shuffle）と後合成（AW・射影）の自然性を証明した。既存 KST の Moore 収縮の自然性と `ChainHomotopySquare` の合成則を完全修飾で参照し、実際の `normalizedShuffleAWHomotopy` の両入力の任意の射への自然性を、各次数のホモトピー成分の等式として証明した。第一のまとまりの図式方向の両立である。

最終合成の自動推論が200,000 heartbeatsに達した箇所は、射と中間の四角形を明示して分割し解消した。制限値は変更していない。

依存対象の鍵付きビルド **1,852 jobs**、個別検査、新規対象の鍵付きビルド **1,879 jobs**、累計120本 **1,322宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-dependencies-53.log`・`/private/tmp/isw2-g10-build-54.log`、監査 `/private/tmp/AuditISW2G10HundredTwenty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwenty-modules.txt`。鍵は `--wait 3600`、一枚の整理券、各回1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWHomotopyNaturality
```

次はこの自然性を一般係数・負次数延長へ運び、図式の重みの比較へつなぐ。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,444行。約7,900行で実測と残量を報告する。

## 56. 3b-2 続行：図式圏の指定整数 EZ 鎖ホモトピー同値

コード `9b1857680`、新規2本135行。累計 **122本7,691行**。

- `HomologicalAlgebra.PointwiseChainHomotopy`（56行）：各点の指定鎖ホモトピーと次数を一つ上げる成分の自然性から、図式圏の鎖ホモトピーを構成した。各点の成分は元のものと定義的に一致する。
- `DiagramComparison.DiagramIntegerEZ`（79行）：任意の添字圏について、積を正規化した側・二因子の正規化テンソル側の複体値図式と、指定 AW・shuffle の全図式射を構成した。既存の順方向および§55の逆方向の自然性を使い、元の成分交換関手を通して、図式圏における両方向の鎖ホモトピー同値 `integerEZDiagramEquiv` を構成した。

第一のまとまりの図式方向の両立を実装した。点ごとの同値の存在だけで図式の end での同値を結論したものではない。一般係数の元の正規化模型・積重みへの同定と、全単体 Hom／切断比較への接続は残る。

個別検査、鍵付き対象ビルド **1,888 jobs**、累計122本 **1,346宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-55.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentytwo-modules.txt`。鍵は `--wait 3600`、一枚の整理券で順番待ちし、取得後は1,700秒上限でビルド・監査の間だけ使用、解放済み。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.PointwiseChainHomotopy
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramIntegerEZ
```

native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残る。停止点2は未完、残枠2,309行。約7,900行で実測と残量を報告する。

## 57. 3b-2 続行：一般係数の元の正規化テンソル図式への輸送

コード `7f567da87`、新規2本142行。累計 **124本7,833行**。

- `DiagramComparison.DiagramCoefficientEZ`（74行）：図式圏の同値を加法的係数変更へ運び、積側を既存 Moore 全自然同型で係数変更後の元の正規化へ戻した。指定ホモトピーの負次数延長も構成した。
- `DiagramComparison.NegativeEZTargetDiagram`（68行）：元の一般係数の負次数正規化テンソルの図式を構成し、既存係数テンソル同型の全自然性を適用した。図式交換と延長の指定同型を使い、標的をこの図式に戻した同値を構成した。

第一のまとまりの一般係数・全図式への輸送である。積重みの自由化との最終同定、指定 AW・shuffle の各点との照合、全単体 Hom／切断比較への接続を完了済みとは数えない。

個別検査、鍵付き対象ビルド **2,263 jobs**、累計124本 **1,393宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-56.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyFour.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentyfour-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramCoefficientEZ
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZTargetDiagram
```

### 57.1 約7,900行の非停止の中間報告

11-13のユーザー指示3に基づく報告。実測 **7,833行**、上限10,000行まで **2,167行**。§37時点の5,786行から2,047行を追加した。追加は第一のまとまりの、一般係数・宇宙・正規化テンソル・両方向の指定 EZ ホモトピー・その図式化に使った。§37で第一のまとまり全体を1,000〜1,600行とした見込みは、この部分だけで超過している。

| 残る承認済みのまとまり | 今回の暫定追加見込み | 現状 |
| --- | ---: | --- |
| 正規化テンソル／積重み、全単体比較と照合の残り | 600〜1,000行 | 両方向の自然な EZ 同値は図式圏まで構成済み。自由化・元の Hom 比較・全単体作用素との最終接続が残る |
| 指定豊穣 Hom 合成・native 制限・極限性 | 600〜900行 | 指定 native 錐と比較族は既存。今回の比較がその制限と同じ射である照合が残る |
| 標準脚の最終等式と D(A) 輸送 | 400〜700行 | 元の脚と raw 錐は既存。極限性確定後の最終照合・輸送が残る |
| 全図式射・指定錐の族・離散加群版入口 | 500〜900行 | strict Tot 側の成分は既存。最終の錐の族と入口が残る |
| 合計 | **2,100〜3,500行** | 完成見込み **9,933〜11,333行** |

下限でも余裕は67行しかなく、10,000行内に収まる保証はない。この報告を停止点2や上限変更の承認とはしない。最新の指示3のとおり、この中間報告自体では承認待ちにせず、既存の全自然同型・指定錐を使う短い接続を優先する。四つの外のまとまりを追加せず、型・範囲の弱化も行わない。10,000行の上限を独自に延長せず、超える変更や範囲外のまとまりが必要になったところで、検証済みを保存して停止する。停止点2は未完。

## 58. 3b-2 続行：元の自由積図式への輸送と延長比較の自然性

コード `b5eb19199`、新規2本118行。累計 **126本7,951行**。

- `DiagramComparison.FreeProductDiagramEZ`（65行）：任意の単体的集合の二図式について、積側とテンソル側の自由化の全自然同型を構成した。§57の図式圏の比較を両側から運び、元の A 自由正規化鎖による積図式とテンソル図式の鎖ホモトピー同値を構成した。
- `DiagramComparison.DiagramExtendNaturality`（53行）：既存 `negativeDiagramExchangeIso` を同じ成分を持つ全自然同型へまとめ、任意の複体値図式射との可換式を証明した。

順方向の各点が元の指定 AW と一致する式は、`rfl` だけでは閉じないことを個別検査で確認した。図式交換・零延長の比較を通るため、後者の自然性を使って照合する。この未証明の等式は本体に残しておらず、試作は `/private/tmp/isw2-free-product-diagram-component-draft.lean` に保存した。今回の同値構成を、この最終成分等式まで済んだものとして数えない。いずれも第一のまとまりの同定・自然性の内部である。

個別検査、鍵付き対象ビルド **2,269 jobs**・**2,264 jobs**、一時監査125本1,415宣言、最終累計126本 **1,426宣言・標準三公理のみ**が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-57.log`・`/private/tmp/isw2-g10-build-58.log`、最終監査 `/private/tmp/AuditISW2G10HundredTwentySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentysix-modules.txt`。鍵は `--wait 3600`、同時に一枚の整理券、各回1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramEZ
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramExtendNaturality
```

約7,900行の中間報告の実測を **7,951行、残枠2,049行**に更新する。残る四まとまりと上限内完了のリスクは§57.1のとおり。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は未完であり、停止点2にはまだ達していない。

## 59. 3b-2 続行：図式 EZ の二射と指定 AW・shuffle の同定

コード `0d3c7567d`、新規2本113行。累計 **128本8,064行**。

- `DiagramComparison.CoefficientDiagramMaps`（45行）：係数 AW・shuffle の全図式射を構成し、既存係数図式同値の hom・inv との等式を証明した。
- `DiagramComparison.FreeProductDiagramMaps`（68行）：元の自由積図式の指定 AW・shuffle を構成し、自由積図式同値の両方向と同定した。図式交換・零延長比較の自然性で中間同型を相殺する。§58で残した照合を、各点だけでなく全図式射の等式として閉じた。

第一のまとまりの同定・自然性の内部。全単体 Hom 比較や native 極限性を、今回の等式だけから結論してはいない。

鍵付き対象ビルド **2,272 jobs**、累計128本 **1,457宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-59.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentyeight-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientDiagramMaps
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramMaps
```

残枠 **1,936行**。全単体 Hom／切断比較、native 制限・極限性、標準脚・D(A) 輸送、全図式射・指定錐の族は残り、停止点2は未完。次のパラメータ方向の自然性は個別検査中であり、このコミットには含めない。B3凍結の予告に従い検証済みだけを保存した。凍結確定後は枝へのコミットを控える。

## 60. 3b-2 続行：重み・単体パラメータ方向の自然性

コード `ef2e57fce`、新規 `DiagramComparison.FreeProductDiagramNaturality` 1本53行。累計 **129本8,117行**。元の自由負次数鎖を図式の自然変換へ作用させ、指定 AW・shuffle が二つの図式の任意の自然変換と可換であることを証明した。第一のまとまりの自然性の内部であり、標準単体の作用素を代入できる形である。

個別検査、鍵付き対象ビルド **2,273 jobs**、累計129本 **1,464宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-60.log`、監査 `/private/tmp/AuditISW2G10HundredTwentyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredtwentynine-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramNaturality
```

残枠 **1,883行**。積重みとテンソル側の余単体的な族、および指定二射を `FreeProductFrames.lean` に下書き中（未コミット）。鎖ホモトピー同値から全単体 Hom 空間への接続、指定豊穣合成・native 極限性、脚・D(A)・錐の族は引き続き未完。停止点2ではない。

## 61. 3b-2 続行：積重み・テンソルの余単体図式と指定二射

コード `d825603b7`、新規 `DiagramComparison.FreeProductFrames` 1本67行。累計 **130本8,184行**。

元の自由負次数鎖の図式関手を使い、任意の余単体的パラメータ P に対して、積を正規化する族と正規化後のテンソルの族を構成した。§60の自然性を使い、指定 AW・shuffle を全余単体作用素と可換な自然変換にした。標準単体を代入する前の全パラメータ形である。第一のまとまりの全単体比較の内部。

個別検査、鍵付き対象ビルド **2,274 jobs**、累計130本 **1,483宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-61.log`、監査 `/private/tmp/AuditISW2G10HundredThirty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirty-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
```

残枠 **1,816行**。同じ二射からの全単体 Hom 比較 `FreeProductHomComparison.lean`（42行）は個別検査済み、対象ビルド・監査待ちであり、このコミットには含めない。標準単体の代入後、テンソル側を既存の Dold–Kan Hom と、積側を重み付き切断空間と同定し、指定射のホモトピー同値性を証明することが残る。次数ごとの鎖ホモトピー同値だけから空間の同値性を結論しない。native 極限性等も未完であり、停止点2には達していない。

## 62. 3b-2 続行：指定二射から全単体 Hom 比較へ

コード `8da07570f`、新規 `DiagramComparison.FreeProductHomComparison` 1本42行。累計 **131本8,226行**。

§61の余単体 AW・shuffle に既存の `cosimplicialHomMap` を適用し、両方向の実際の単体的 Hom 射を構成した。標的の全図式射にも自然であり、全次数の作用が指定図式 AW・shuffle の前合成そのものである等式を保持する。第一のまとまりの指定比較射の構成。空間としての同値性はまだ証明していない。

個別検査、鍵付き対象ビルド **2,276 jobs**、累計131本 **1,488宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-62.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyone-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparison
```

残枠 **1,774行**。`StandardSimplexParameter.lean`（51行）では、持ち上げた標準単体の自由鎖と既存 `normalizedFunctor` の定数図式の全自然同型、およびテンソル族への輸送を個別検査済み。対象ビルド・監査待ちなので未コミット。

次の接続で必要なのは、図式圏の `linearHomComplex` の Γ とテンソル族からの Hom の同定である。点ごとの既存 `tensorHomEquiv` の始域・標的自然性を使い、添字方向の自然性条件を保持して組み立てる。積側を重み付き切断空間に同定する部分、指定射の空間の同値性、豊穣合成・native 極限性、脚・D(A)・錐の族も未完。これらを省略して停止点2としない。

## 63. 3b-2 続行：元の標準単体パラメータとの同定

コード `2d63e090d`、新規 `DiagramComparison.StandardSimplexParameter` 1本51行。累計 **132本8,277行**。

小さい標準単体を宇宙持ち上げした定数図式の自由鎖と、既存 `EInfinity.BarrattEccles.normalizedFunctor` の定数図式を全余単体的に同定した。同じ自然同型をテンソル族へ移した。既存の正規化関手を参照するだけで、⑤aのファイルや模型の構造を変更していない。第一のまとまりのパラメータの同定。

個別検査、鍵付き対象ビルド **2,275 jobs**、累計132本 **1,503宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-63.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtytwo-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
```

残枠 **1,723行**。図式テンソルからの射を自然性条件つきの Hom 射の族へ転置する証明を `DiagramTensorHom.lean` で進めている（未コミット）。図式 Hom 複体との同定、指定比較の空間としての同値性、native 極限性と後続の三まとまりは未完。停止点2ではない。

## 64. 3b-2 続行：自然性条件を保つ図式テンソル–Hom 同値

コード `fb60abd72`、新規 `DiagramComparison.DiagramTensorHom` 1本64行。累計 **133本8,341行**。

図式のテンソルからの射を、各点の Hom 複体への射の族と同定した。族の型には、添字の任意の射について前合成と後合成が一致する条件を含める。既存 `tensorHomEquiv` の始域・標的自然性から両方向を構成し、逆写像の法則とパラメータ複体の全射への自然性を証明した。第一のまとまりの図式 Hom の同定の内部。

個別検査、鍵付き対象ビルド **2,065 jobs**、累計133本 **1,520宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-64.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtythree-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHom
```

残枠 **1,659行**。`DiagramHomCochains.lean` の各次数の評価・組み立て・微分との可換性は個別検査済み。`DiagramHomFamilyLift.lean` で上の族を図式 Hom 複体への鎖写像にする証明を検査中。いずれもまだ未コミット。指定全単体比較の同値性、native 極限性と残る段階は未完であり、停止点2ではない。

## 65. 3b-2 続行：図式 Hom 複体への組み立て

コード `48e70aba5`、新規2本112行。累計 **135本8,453行**。

- `DiagramComparison.DiagramHomCochains`（50行）：図式 cochain の各点での評価、自然性条件つきの族からの組み立て、評価と微分の可換性、各点による外延性を証明した。
- `DiagramComparison.DiagramHomFamilyLift`（62行）：§64の Hom 射の族を、元の図式圏の `linearHomComplex` への鎖写像にした。線形性と微分可換性を各点の元の射から導いた。

第一のまとまりの図式 Hom 同定の内部。小さい添字圏を対象とし、必要な Δ・Δᵒᵖ を含む。指定射の同値性や native 極限性をこれだけで結論しない。

個別検査、鍵付き対象ビルド **2,070 jobs**、累計135本 **1,536宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-65.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyFive.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyfive-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomCochains
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyLift
```

残枠 **1,547行**。`DiagramHomFamilyEquiv.lean`（111行）の各点への評価による逆写像・両合成の法則・図式テンソル–Hom 同値・パラメータ前合成への自然性は個別検査済み、対象ビルド・監査待ち（未コミット）。次に標準単体を代入して既存 `normalizedSimplexHomEquiv` と合成できる。積重み側との同定、空間の同値性、native 極限性、脚・D(A) 輸送、全図式射・指定錐の族は未完。停止点2ではない。

## 66. 3b-2 続行：元の図式 Hom への同値とパラメータ自然性

コード `20b09a216`、新規 `DiagramComparison.DiagramHomFamilyEquiv` 1本111行。累計 **136本8,564行**。

図式 Hom 複体への射を各点に評価する逆写像を構成し、§65の組み立てとの両合成が恒等であることを証明した。§64の転置と合成して、図式テンソルからの射と元の図式 `linearHomComplex` への射を同定し、パラメータ複体の全射による前合成との可換式も証明した。第一のまとまりの図式 Hom の同定の内部。

個別検査、鍵付き対象ビルド **2,071 jobs**、累計136本 **1,557宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-66.log`、監査 `/private/tmp/AuditISW2G10HundredThirtySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtysix-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
```

残枠 **1,436行**。`DiagramTensorDoldKan.lean` で標準単体を代入した全単体同型を検査中。元の自由テンソル族への輸送の型推論が制限に達したため、中間 Hom 同型を指定前合成で明示している。制限値は変更していない。積重み側との同定、空間の同値性、native 極限性と後続の要件は未完で、停止点2ではない。

## 67. 3b-2 続行：図式テンソル Hom と実 Dold–Kan 空間

コード `4daa43593`、新規 `DiagramComparison.DiagramTensorDoldKan` 1本79行。累計 **137本8,643行**。

§66に正規化標準単体を代入し、既存 `normalizedSimplexHomEquiv` と合成して、図式テンソル Hom と元の図式 `linearHomComplex` の実 Dold–Kan 空間との全単体同型を構成した。単体作用素との可換性も証明した。§63の指定同型を前合成して、元の自由テンソル族の Hom へ戻す同型も構成した。第一のまとまりのテンソル側の接続。

上記コミットの個別検査、鍵付き対象ビルド **2,564 jobs**、累計137本 **1,572宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-67.log`、監査 `/private/tmp/AuditISW2G10HundredThirtySeven.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyseven-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorDoldKan
```

残枠 **1,357行**。`FreeChainsAdjunction.lean` で自由加群・Dold–Kan・負次数延長の随伴の合成と図式への持ち上げを個別検査済み（未コミット）。積側は既存の重み付き切断の随伴と合成する。

その接続は持ち上げた添字圏 `AsSmall` も使うため、本枝の新設 `DiagramHomCochains`・`DiagramHomFamilyLift`・`DiagramHomFamilyEquiv`・`DiagramTensorDoldKan` の四本について、添字 `J : Type v` と係数 `A : Type (max u v)` を許す一般化を検査中。`v = 0` で従来の小さい添字圏を含む。main に該当四本が存在しないことを確認済みで、既存の main の宣言・入口・⑤aのファイルは変更しない。この未コミットの一般化を上記監査が検証したとは数えず、再ビルド・再監査する。停止点2は未完。

## 68. 3b-2 続行：自由鎖の随伴と持ち上げ添字への対応

コード `052a11093`、新規 `DiagramComparison.FreeChainsAdjunction` 1本42行。累計 **138本8,685行**。§67で予告した本枝新設四本の宇宙一般化は行数差0。

自由加群・Dold–Kan・負次数延長の既存随伴を合成し、元の自由負次数鎖と実 Dold–Kan 関手の随伴、および図式全体への持ち上げを構成した。四本の一般化は `J : Type v`、`A : Type (max u v)` に変更し、従来の `v = 0` と持ち上げ添字の双方を含む。既存 main の宣言は変更していない。

個別検査、一般化した四本と直接の importer を含む鍵付き対象ビルド **2,570 jobs**、累計138本 **1,579宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-68.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtyeight-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction
```

残枠 **1,315行**。`ProductSectionsHom.lean`（51行）は、この随伴と既存の重み付き切断の随伴を合成して、積重みの Hom と元の切断空間を全単体で同定する。個別検査済みで対象ビルド・監査待ち、未コミット。`NormalizedWeightSectionMap.lean` で両端の同型の間に指定 AW・shuffle を置く射を検査中。空間の同値性や native 極限性を、射を構成しただけで完了とは数えない。停止点2は未完。

## 69. 3b-2 続行：積重み Hom と重み付き切断の全単体同型

コード `007702bd5`、新規 `DiagramComparison.ProductSectionsHom` 1本51行。累計 **139本8,736行**。

持ち上げ標準単体の全自然同型と Yoneda 同型を使い、自由鎖の随伴と既存の重み付き切断の随伴を合成した。積重みの自由鎖からの全単体 Hom を、同じ重み・同じ実 Γ 図式の重み付き切断空間に同定した。第一のまとまりの積側の接続。

個別検査、鍵付き対象ビルド **2,632 jobs**、累計139本 **1,584宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-69.log`、監査 `/private/tmp/AuditISW2G10HundredThirtyNine.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredthirtynine-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用し、解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsHom
```

残枠 **1,264行**。`NormalizedWeightSectionMap.lean` の指定 AW・shuffle による両方向の実単体的射は個別検査済み、対象ビルド・監査待ち。

同値性には、自然な鎖ホモトピーを余単体 Hom の実単体的ホモトピーへ移す接続がなお必要。一般の余単体図式について点ごとの鎖ホモトピーだけで結論してはいけない。直接の経路として、積重みの第二パラメータのグラフを指定 AW に送り、パラメータ鎖への余作用を作る部分を `ProductParameterCoaction.lean` で検査中。余作用の単位則、区間によるホモトピー評価、両端点との等式はこれからで、同値性を証明済みとはしない。既存のモデル圏の frame 比較も確認したが、必要な frame 条件を証明せず適用したり `[ModelCategory SSet]` を追加したりはしない。native 極限性と後続も未完。停止点2ではない。

## 70. 3b-2 続行：指定正規化重み比較の両方向の射

コード `2fc8b73dc`、新規 `DiagramComparison.NormalizedWeightSectionMap` 1本43行。累計 **140本8,779行**。

§67と§69の全単体同型の間に、元の AW・shuffle による指定前合成を置き、図式 Hom 複体の実 Dold–Kan 空間と重み付き切断空間の間の両方向の実単体的射を構成した。逆射の法則やホモトピー同値性を、この構成だけで主張してはいない。

個別検査、鍵付き対象ビルド **2,640 jobs**、累計140本 **1,588宣言・標準三公理のみ**の一時監査が成功。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-70.log`、監査 `/private/tmp/AuditISW2G10HundredForty.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredforty-modules.txt`。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap
```

## 71. 3b-2 続行：積パラメータの指定余作用と凍結前の保存

コード `a09e4c437`、新規 `DiagramComparison.ProductParameterCoaction` 1本55行。累計 **141本8,834行**、上限10,000行まで **1,166行**。

積の第二射影のグラフを自由負次数鎖へ送り、指定 AW と合成してパラメータ鎖への余作用を構成した。重みとパラメータの全図式射に対する自然性を証明した。§37.2の第一のまとまりの内部で、余作用の単位則や鎖ホモトピーから実単体的ホモトピーへの輸送はまだ含まない。

個別検査、鍵付き対象ビルド **2,275 jobs**、累計141本 **1,604宣言・標準三公理のみ**の一時監査の成功をログで確認した。対応するビルド・監査のプロセスは終了している。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-71.log`、監査 `/private/tmp/AuditISW2G10HundredFortyOne.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyone-modules.txt`。鍵は `--wait 3600`、一枚の整理券、1,700秒上限でビルド・監査の間だけ使用。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductParameterCoaction
```

検証済みの Lean は上記まで枝にコミット済み。11-13昼の凍結予告を受領した。確定連絡後は夜の枝へのコミットを控え、翌朝の main 取り込みと改名追従は配布される手順に従う。現時点で凍結確定の連絡は未受領。

停止点2は未完。残るのは、指定全単体比較のホモトピー同値性と指定豊穣 Hom 合成との照合、native 切断・極限性、標準脚と D(A) 輸送、全図式射・指定錐の族・離散加群入口。残枠は小さく、既存の自然な鎖ホモトピーを点ごとに適用しただけで全単体空間の同値性とする短縮はできない。範囲・型は維持し、上限を超えそうな場合は追加実装前に報告する。

## 72. 3b-2：残工程の再点検と上限による中間停止

11-13、§71の保存後に実ソースと既存の極限判定の型を再点検した。登録待ち141本の一覧を現在の作業木の各ファイルに解決して行数を再集計し、**8,834行**を確認した。検証済みコードは `a09e4c437` まで、報告は `e1c96bafc` まで。未コミットの Lean はない。以下は紙の検討であり、新しいビルド・監査の実施を主張しない。

### 72.1 短縮候補の検査

1. `NormalizedBousfieldKanHomSpace.normalizedBousfieldKanHomSpaceComparison_equivalence` は元の Hom–Tot 比較の Γ 像の同値性を既に証明する。ただし終域は正規化 BK Hom 複体の Γ であり、重み付き切断空間ではない。`NormalizedWeightSectionMap` の両方向の射はこの次の接続で、両合成の単体的ホモトピーはまだない。鎖の段階の自然な EZ ホモトピーを得たことと、余単体 Hom 空間でのホモトピーを得たことを混同しない。
2. 直接の経路では `ProductParameterCoaction` の余作用を使い、単位則、区間の評価、両端点の式、全単体への自然性を証明する必要がある。現ファイルの結論はグラフ・余作用・自然性までで、これらの残項を含まない。一般 A の EZ の移送そのものは既存の加法的移送・底変換同型・分裂で済んでおり、作り直さない。
3. `ModelCategoryComparison.frameHomMap_homotopyEquivalence` は別の候補だが、実際の二つの frame の Reedy cofibrancy、両 frame の構造射の弱同値性、比較の各点の弱同値性、標的の fibrancy を要求する。確認した型は `[ModelCategory C]` を持つ一般定理であり、新しい `[ModelCategory SSet]` を足す必要があるという意味ではない。しかし今回の図式圏と frame に対する必要条件の証明が自動的に供給されるわけではなく、現時点では短い完成経路を確認できていない。
4. `coherentCone_isLimit_of_family_lifts` の型を再確認した。必要なのは各試験対象での実切断への族 `a`、頂点評価が `coherentCosliceFiberComparison` そのものになる式 `ha`、同じ族の制限が同値である証明 `he`。`EnrichedBousfieldKanCone` の自然変換と空間間の抽象的な同値だけではこの三入力を満たさない。指定豊穣合成との照合を省けない。
5. `dgModuleResolvedInfinity_isLimitCone_of_raw` は raw の実極限性を仮定として D(A) 側へ運べる。この定理を再利用して輸送自体を作り直す必要はないが、raw 極限性の入力と、元の頂点・標準脚の同定は別途必要。全図式射・指定錐の族・離散加群入口も3b-2の責任として残す。

### 72.2 残量と停止理由

§37.2の四つのまとまりを維持した再見積もり。これは実装量の予測であり、数学的な下限でも完成の保証でもない。第二〜第四のまとまりは、既存の錐・輸送定理を再利用する前提の従来見込みを維持する。第一は一般 A の移送と両端の Hom 同定が済んだ分を除いた。

| 残るまとまり | 今あるもの／残る結論 | 追加見込み |
| --- | --- | ---: |
| 正規化テンソル／積重み | 両端の全単体同型・AW/shuffle の射・自然な鎖ホモトピーはある。実単体的ホモトピーと指定比較の最終照合が残る | 400〜700行 |
| 指定豊穣 Hom と native 極限性 | 指定錐と豊穣 Hom 図式はある。上記 `a`・`ha`・`he` と同じ制限の照合が残る | 600〜900行 |
| 標準脚と D(A) 輸送 | 既存の輸送定理を使う。元の標準脚の最終式と入力の接続が残る | 400〜700行 |
| 全図式射・指定錐の族・離散加群入口 | 点ごとの完成から全射・同じ錐の族への組み立てと入口が残る | 500〜900行 |
| 合計 | | **1,900〜3,200行** |

完成見込みは **10,734〜12,034行**、承認済み上限は **10,000行**、残枠は **1,166行**。上限を超えそうなときは検証済みを保存して止めるという条件に達したため、**3b-2 の追加 Lean はここで中間停止する**。上限を使い切るための補助宣言追加は行わない。新しい第五のまとまりを要求しているのではなく、承認済み四まとまりの残量が枠を超える見込みである。

これは停止点2ではない。範囲・型を弱めず、全図式射を3b-3に移さず、⑤aのファイルを変更せず、上限を独自に変更しない。検証済み部分はすべて保存済みで、凍結前の取り込みに利用できる。再開には、この残工程と規模について調整が必要。

### 72.3 代わりの紙の作業：3b-4への受け渡しの現状

§38の境目は維持する。今回完成した自由鎖・正規化・全単体 Hom の部品は加群の比較であり、BE 作用を持つ Tot を構成したものではない。3b-4の U 比較に渡すものは、G10 が完成した際の同じ頂点・脚・高次単体を持つ指定 Tot 錐の族である。現状の `normalizedWeightSectionMap` を代用品として渡さない。

再開後は上表の順でG10を閉じ、停止点2の検証後に§38.2の1・2（strict BE 模型と実 U の比較）へ進む。③-aの3b-3が必要なのは coherent な図式へ拡張する際の評価同値と錐の輸送である。加群値の評価同値から BE 値の厳密化を無条件に推論しない。この紙の整理では鍵を取得せず、BE の新規 Lean も開始していない。

## 73. 3b-2 再開：型つきの残補題一覧（11-13、ユーザー承認）

§72の中間停止を解除する。今回の指示により、停止条件は下記一覧の外の新しい数学と外枠12,500行。現在141本8,834行。既存構成の照合だけの追加は3本までとし、追加時はこの報告に型を書く。下記は紙の宣言案で、証明済み・Leanで全体を elaboration 済みという意味ではない。名前空間の省略・局所略記を以下に固定する。単なる存在や零単体で代用せず、指定射・全単体・全図式射を結論に含める。実装中に型の意味を変更する必要が判明した場合も、その変更を黙って行わない。

### 73.1 共通の記法と第一のまとまり（A01〜A12）

この節では DiagramComparison、CategoryTheory、MonoidalCategory、CosimplicialHom の名前を開く。`A : Type u`、`[CommRing A]`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`、`Q : J ⥤ CochainComplex (ModuleCat A) ℤ`、`φ : simplicialRingCoefficient.{u} →+* A`。以下の略記は型を短く書くためだけのもの。

```lean
local notation "D" => J ⥤ CochainComplex (ModuleCat A) ℤ
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)
local notation "P" => standardParameterForCoefficients A J
local notation "N" => freeNegativeChainsDiagramFunctor A J
local notation "FP" => freeProductFrame A W P
local notation "FT" => freeTensorFrame A W P
local notation "AW" => freeProductFrameAW A W P φ
local notation "SH" => freeProductFrameShuffle A W P φ
local notation "NP" => P ⋙ N
local notation "Γ" => truncatedDoldKanFunctor A
```

A01は既存の図式 EZ 同値の指定射を取り出す。添字を後で `SimplexCategory × J` として使い、点ごとの存在を選び直さない。

```lean
-- A01a,b：任意の添字図式 X,Y について。AW・shuffle は既存の指定射。
def freeProductDiagramAWShuffleHomotopy (X Y : J ⥤ SSet.{u}) :
  Homotopy
    ((E).map (freeProductDiagramAW φ X Y ≫ freeProductDiagramShuffle φ X Y))
    (𝟙 ((E).obj (N.obj (X ⊗ Y))))
def freeProductDiagramShuffleAWHomotopy (X Y : J ⥤ SSet.{u}) :
  Homotopy
    ((E).map (freeProductDiagramShuffle φ X Y ≫ freeProductDiagramAW φ X Y))
    (𝟙 ((E).obj (N.obj X ⊗ N.obj Y)))

-- A02：余単体方向と J 方向を同時に含む鎖ホモトピー。
-- EE は Δ ⥤ D を、Δ ⥤ J ⥤ ModuleCat A 値の複体へ交換する関手。
-- 具体的に whiskeringRight Δ D (CochainComplex (J ⥤ ModuleCat A) ℤ)
-- の E 像の後に functorToComplexOfFunctors Δ (J ⥤ ModuleCat A) (.up ℤ)。
def freeProductFrameAWShuffleHomotopy :
  Homotopy (EE.map (AW ≫ SH)) (𝟙 (EE.obj FP))
def freeProductFrameShuffleAWHomotopy :
  Homotopy (EE.map (SH ≫ AW)) (𝟙 (EE.obj FT))

-- A03：正規化された単体の増大写像。全単体で自然な ε。
def standardParameterAugmentation : NP ⟶ 𝟙_ (SimplexCategory ⥤ D)

-- A04：両 frame のパラメータ余作用。
def productFrameCoaction : FP ⟶ FP ⊗ NP
def tensorFrameCoaction : FT ⟶ FT ⊗ NP
-- productFrameCoaction.app n は既存 freeProductParameterCoaction φ W (P.obj n)。
-- tensorFrameCoaction は第二因子の対角 AW と associator によるもの。

-- A05：単位則。δ の名前を上の二つにそれぞれ固定した二宣言。
theorem productFrameCoaction_counit :
  productFrameCoaction ≫ (𝟙 FP ⊗ₘ standardParameterAugmentation) ≫
    (ρ_ FP).hom = 𝟙 FP
theorem tensorFrameCoaction_counit :
  tensorFrameCoaction ≫ (𝟙 FT ⊗ₘ standardParameterAugmentation) ≫
    (ρ_ FT).hom = 𝟙 FT
```

A06〜A08は鎖ホモトピーから単体的ホモトピーへの具体的接続。単なる各 n の鎖ホモトピー同値から空間の同値性を主張しない。

```lean
-- I := N.obj ((Functor.const J).obj (Δ[1] : SSet.{u}))。
-- endpoint ε は正規化した 0→1 または 1→1 の頂点と Δ[0] の単位同型で定義。
def normalizedIntervalEndpoint (ε : Fin 2) : 𝟙_ D ⟶ I

-- A06：同じ鎖ホモトピーの区間による評価。R,S : D。
def normalizedIntervalHom (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) : R ⊗ I ⟶ S
theorem normalizedIntervalHom_endpoints (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
  (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint 0) ≫
      normalizedIntervalHom f g h = f ∧
  (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint 1) ≫
      normalizedIntervalHom f g h = g
-- 自然性も必要：a:R'→R,b:S→S'。h' は h を E.map a,b で前後合成したもの。
theorem normalizedIntervalHom_naturality
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
  (a ⊗ₘ 𝟙 I) ≫ normalizedIntervalHom f g h ≫ b =
    normalizedIntervalHom (a ≫ f ≫ b) (a ≫ g ≫ b) h'

-- A07：F,G : Δ ⥤ D。δ の自然性は NatTrans の型に含む。
def frameHomHomotopyOfChainHomotopy (F G : SimplexCategory ⥤ D)
    (δ : F ⟶ F ⊗ NP)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation) ≫ (ρ_ F).hom = 𝟙 F)
    (f g : F ⟶ G) (h : Homotopy (EE.map f) (EE.map g)) (Q : D) :
  SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)

-- A08：指定二射の両合成のホモトピー（Q に関する NatTrans の成分）。
def freeProductHomComparison_homotopy (Q : D) :
  SSet.Homotopy
    ((freeProductHomReverse A W P φ).app Q ≫
      (freeProductHomComparison A W P φ).app Q) (𝟙 _)
def freeProductHomReverse_homotopy (Q : D) :
  SSet.Homotopy
    ((freeProductHomComparison A W P φ).app Q ≫
      (freeProductHomReverse A W P φ).app Q) (𝟙 _)

-- A09：元の指定比較そのものの同値性。
theorem normalizedWeightSectionMap_equivalence :
  IsSimplicialHomotopyEquivalence (normalizedWeightSectionMap A W Q φ)
```

A10〜A12は同じ指定 Hom 比較の自然性と、BK の持ち上げ・反転への接続。後者の照合を新しい数学として数え直さないため初めから一覧に含める。

```lean
-- A10：Q の全射で可換。Hmap f は Γ.map (図式 linearHom の後合成 f)。
-- Smap f は weightedSectionsFunctor W が Q⋙Γ の全射を写したもの。
theorem normalizedWeightSectionMap_naturality (f : Q ⟶ Q') :
  Hmap f ≫ normalizedWeightSectionMap A W Q' φ =
    normalizedWeightSectionMap A W Q φ ≫ Smap f
-- A11：重みの全射 w:W'→W による前合成。Hpre,Spre はそれぞれ
-- 図式 linearHom と weightedSections の指定前合成（新しい選択ではない）。
theorem normalizedWeightSectionMap_weight_naturality (w : W' ⟶ W) :
  Hpre w ≫ normalizedWeightSectionMap A W' Q φ =
    normalizedWeightSectionMap A W Q φ ≫ Spre w

-- A12：X : CosimplicialObject (Complex A)、T : Complex A。
-- HΓ := Γ.obj (normalizedBousfieldKanHom ((homDiagramFunctor T).obj X))。
-- F := liftedClosedDiagram X、t := ForgetEnrichment.of (Complex A) T。
-- Hol := bousfieldKanHolim (simplicialHomDiagram F t ⋙ SSet.opFunctor)。
def normalizedBKReflectedSectionsMap (X : CosimplicialObject (Complex A))
    (T : Complex A) : HΓ.op ⟶ Hol
theorem normalizedBKReflectedSectionsMap_equivalence (X) (T) :
  IsSimplicialHomotopyEquivalence (normalizedBKReflectedSectionsMap X T)
```

A12の射はA09の射に、既存の二重 opposite・AsSmall・ULift・Γ Hom 同型を順に合成する。任意の同値を選んで型だけ合わせることは禁止。反転と持ち上げの各交換はこのA12の構成内で明示する。

### 73.2 第二のまとまり：指定豊穣 Hom と native 極限性（B01〜B08）

`X : CosimplicialObject (Complex A)`、`F := liftedClosedDiagram X`、`z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)`、`φX := liftedEnrichedBousfieldKanCone X`、`c := nativeCoherentCone X`、`hz := nativeCoherentCone_vertex X`。`C := ClosedCategory A (Complex A)`。`U := SSet.uliftFunctor.{u+1,u}`。`x : C` を全試験対象とする。`q x := reflectedWeightedHomComparison F z φX x`。

```lean
-- B01：実 Hom 同型、既存 Hom–Tot 比較、A12 を合成した指定射。
def gammaReflectedBKComparison (X) (x : C) :
  (SimplicialCategory.sHom x z).op ⟶
    bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)
-- B02：実豊穣合成との等式。型だけの同値で代用しない。
theorem gammaReflectedBKComparison_eq (X) (x : C) :
  gammaReflectedBKComparison X x = q x
-- B03：同じ指定射の同値性。
theorem reflectedBKComparison_equivalence (X) (x : C) :
  IsSimplicialHomotopyEquivalence (q x)

-- B04：coherentCone_isLimit_of_family_lifts の a。
def nativeTotConeFamilyLift (X) (x : C) :
  U.obj (SimplicialCategory.sHom x z).op ⟶
    coherentConeSectionSpace c.val (coherentNerveVertex x)
-- B05：同定 ha（頂点の同じ実比較）。
theorem nativeTotConeFamilyLift_apex (X) (x : C) :
  nativeTotConeFamilyLift X x ≫ coherentConeApexEvaluation c z hz x =
    coherentCosliceFiberComparison x z
-- B06：制限の同定。右辺は既存の全 BK→native 比較との合成。
theorem nativeTotConeFamilyLift_restriction (X) (x : C) :
  nativeTotConeFamilyLift X x ≫ coneSectionRestriction c (coherentNerveVertex x) =
    U.map (q x) ≫ reflectedHomHolimConeComparison F x
-- B07：he。一般の reflectedHomHolimConeComparison の既存同値性を再利用。
theorem nativeTotConeFamilyLift_equivalence (X) (x : C) :
  IsSimplicialHomotopyEquivalence
    (nativeTotConeFamilyLift X x ≫ coneSectionRestriction c (coherentNerveVertex x))
-- B08：元の指定錐の native 極限性。
theorem nativeCoherentCone_isLimit (X) : IsLimitCone (nativeCoherentCone X)
theorem nativeDGCone_isLimit (X) : IsLimitCone (nativeDGCone X)
```

B04で別の錐を選ばず、指定余錐の合成の全単体を切断へ送る。B06の右辺の同値性だけを証明してB04・B05を省くことはしない。

### 73.3 第三のまとまり：標準脚と D(A) 輸送（C01〜C07）

以下 `K := (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))`、`R := complexSemifreeResolutionInfinity A`、`DA := derivedInfinityCategory A`。`v n` は K の n の指定頂点（AsSmall・ULift による像）。`standardLeg X n` は `standardZeroLeg A X ≫ X.map (SimplexCategory.const _ _ 0)` という、頂点0を選ぶ標準脚。最後の定数射の実API名は実装時に合わせるが、0以外を選ぶ仕様には変えない。

```lean
-- C01：raw dg 錐の全脚の実一次単体。edgeMk は閉射の dg 辺。
theorem nativeDGCone_standardLeg (X) (n : SimplexCategory) :
  (derivedConeLeg (nativeDGCone X) (v n)).edge =
    (dgClosedEdge A (Complex A) ((complexToClosed A).map (standardLeg X n))).edge
-- C02：R による同じ実錐の輸送（raw 極限性から、既存の出力分解判定を適用）。
def nativeDerivedDiagram (X) : K ⟶ DA := nativeDGDiagram X ≫ R
def nativeDerivedCone (X) : JoinCone (nativeDerivedDiagram X) :=
  mapJoinCone R (nativeDGCone X)
theorem nativeDerivedCone_isLimit (X) : IsLimitCone (nativeDerivedCone X)
-- C03：元の Tot の指定分解を頂点とする。
theorem nativeDerivedCone_vertex (X) :
  (nativeDerivedCone X).vertex =
    R.app (Opposite.op ⦋0⦌) (Simplex.vertex ((productTotalFunctor A).obj X))
-- C04：同じ標準脚を輸送する。
theorem nativeDerivedCone_standardLeg (X) (n) :
  (derivedConeLeg (nativeDerivedCone X) (v n)).edge =
    R.app (Opposite.op ⦋1⦌)
      (dgClosedEdge A (Complex A) ((complexToClosed A).map (standardLeg X n))).edge
-- C05：nativeDGDiagram の元の strict 図式との照合。
-- kappa : K ≅ (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)
-- は AsSmall と ULift の既存指定同型。
theorem nativeDerivedDiagram_strict (X) :
  nativeDerivedDiagram X = kappa.hom ≫
    (SSet.uliftFunctor.{u+1,0}).map (nerveMap X) ≫ complexOrdinaryDerivedSource A
-- C06：kappa で引き戻した元の図式上の指定錐とその極限性。
def strictDerivedTotCone (X) :
  JoinCone ((SSet.uliftFunctor.{u+1,0}).map (nerveMap X) ≫ complexOrdinaryDerivedSource A)
theorem strictDerivedTotCone_isLimit (X) : IsLimitCone (strictDerivedTotCone X)
-- C07：全 join 射を保持する輸送の式（脚だけの同定ではない）。
theorem strictDerivedTotCone_pullback (X) :
  joinMap (𝟙 Δ[0]) kappa.hom ≫ (strictDerivedTotCone X).val =
    (nativeDerivedCone X).val
```

C05の universe の表記は実ソース X の対象宇宙と hom 宇宙を区別して elaboration 時に固定する。普通の図式を無関係な図式同型で置換する内容ではない。もし厳密等式が成立せず指定 FunctorIso による輸送が必要であれば、型の変更として報告する。

### 73.4 第四のまとまり：全図式射・指定錐の族・離散入口（D01〜D08）

`B := nerve (CosimplicialObject (Complex A))`、`K₀ := (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)`、`jX : Δ[0] ⟶ B := SSet.yonedaEquiv.symm (nerveVertex X)`。`evalFamily : K₀ ⊗ B ⟶ DA` は評価関手 `(n,X) ↦ X.obj n` の nerve と積・ULift の既存同型、`complexOrdinaryDerivedSource A` の合成。`totFamily : B ⟶ DA := nerveMap (productTotalFunctor A) ≫ complexOrdinaryDerivedSource A`。

```lean
-- D01：同じ指定全錐の全パラメータ族。
def derivedTotConeFamily : (join (Δ[0] : SSet.{u+1}) K₀) ⊗ B ⟶ DA
-- D02：両端を全パラメータで固定する。
theorem derivedTotConeFamily_boundaries :
  (joinInl Δ[0] K₀ ⊗ₘ 𝟙 B) ≫ derivedTotConeFamily =
      (λ_ B).hom ≫ totFamily ∧
  (joinInr Δ[0] K₀ ⊗ₘ 𝟙 B) ≫ derivedTotConeFamily = evalFamily
-- D03：各点で同じ全高次単体の錐へ戻る。
theorem derivedTotConeFamily_at (X) :
  (ρ_ (join Δ[0] K₀)).inv ≫ (𝟙 _ ⊗ₘ jX) ≫ derivedTotConeFamily =
    (strictDerivedTotCone X).val
-- D04：図式射に対応する族の頂点辺は productTotalFunctor.map f の像そのもの。
theorem derivedTotConeFamily_map {X Y} (f : X ⟶ Y) :
  totFamily.app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk ((productTotalFunctor A).map f)).edge
```

D01の単体的射の型が全パラメータの単体作用素・合成も含む。D04だけを証明して族の代わりにしない。離散化では既存 `discreteTotalCochainNatIso` の成分を使い、交代余面複体を頂点とする同じ錐を輸送する。

```lean
-- M : CosimplicialObject (ModuleCat.{u} A)。
-- disc := discreteDiagramFunctor A、Coch := discreteCochainFunctor A。
-- discreteModuleSource := nerveMap (HomologicalComplex.single _ (.up ℤ) 0)
--   ≫ complexOrdinaryDerivedSource A（必要な宇宙同型は固定）。
-- D05：離散加群版の指定錐。
def cosimplicialModuleCone (M) :
  JoinCone ((SSet.uliftFunctor.{u+1,0}).map (nerveMap M) ≫ discreteModuleSource)
theorem cosimplicialModuleCone_isLimit (M) : IsLimitCone (cosimplicialModuleCone M)
-- D06：頂点は同じ交代余面複体の像。
theorem cosimplicialModuleCone_vertex (M) :
  (cosimplicialModuleCone M).vertex =
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (Coch.obj M))
-- D07：離散入力についても全図式射・全高次単体を保持する錐族。
-- Bm := nerve (CosimplicialObject (ModuleCat.{u} A))。
def cosimplicialModuleConeFamily : (join (Δ[0] : SSet.{u+1}) K₀) ⊗ Bm ⟶ DA
theorem cosimplicialModuleConeFamily_at (M) :
  (ρ_ (join Δ[0] K₀)).inv ≫
    (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) ≫ cosimplicialModuleConeFamily =
      (cosimplicialModuleCone M).val
-- 境界は D02 の evalFamily を離散化し、頂点は nerveMap Coch≫strictToD。
theorem cosimplicialModuleConeFamily_boundaries :
  (joinInl Δ[0] K₀ ⊗ₘ 𝟙 Bm) ≫ cosimplicialModuleConeFamily =
      (λ_ Bm).hom ≫ nerveMap Coch ≫ complexOrdinaryDerivedSource A ∧
  (joinInr Δ[0] K₀ ⊗ₘ 𝟙 Bm) ≫ cosimplicialModuleConeFamily = discreteEvalFamily
-- D08：G10 のホモロジー入口（整数次数の零延長を明記）。
def cosimplicialModuleCone_homology (M) (i : ℤ) :
  derivedInfinityHomology A i (cosimplicialModuleCone M).vertex ≃ₗ[A]
    (Coch.obj M).homology i
```

D08は入口表の `.homology' i` という紙の略記を、既存の整数次数への零延長 `discreteCochainFunctor` に固定して書いたもの。自然数次数には既存の extend のホモロジー同型で戻す。入口の型を黙って弱めない。

### 73.5 実装順・管理

A01から順に進める。A06・A07の区間評価は第一のまとまりに初めから含めた数学であり、後で「同定だけの追加」に数えない。A12/B01/B02も指定豊穣合成との照合として初めから含める。細部の universe・binder・既存 API 名の elaboration は検証対象で、未検証の型案を検収済み宣言と数えない。一覧外の新しい数学が必要なら、その型と漏れた理由を保存して止める。照合だけの追加枠は現在0/3。

行数は外枠12,500行だけで管理する。§72の予測だけを理由に再び止めない。停止点2で§37.2・§72.2の四行と実測を照合し、閉じた後は§38.2の1・2へ進む。凍結確定の連絡はこの記録時点で未受領。確定後はコミットを控え、型案・依存の紙の確認を続ける。

## 74. 一覧A01の検証と、A02の添字交換の照合

A01の二宣言を `DiagramComparison.FreeProductDiagramHomotopies` に実装し、`43f92578d` に保存した。新規1本36行、累計 **142本8,870行**。個別検査、鍵付き対象ビルド **2,273 jobs** と累計 **1,623宣言・標準三公理のみ**の一時監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-74.log`、監査 `/private/tmp/AuditISW2G10HundredFortyTwo.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortytwo-modules.txt`。`--wait 3600`、一枚の整理券、実行1,700秒上限で検証の間だけ鍵を使用した。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramHomotopies
```

A02のため、既存の積添字の構成と二重図式の構成の**成分の並べ替えだけ**の補題を追加する。追加枠 **1/3**。新しいホモトピーの存在定理ではなく、仮定のホモトピーの同じ成分を二重に評価する。型は以下（`J,K,C` は圏、`C` は Preadditive、`c : ComplexShape ι`）。

```lean
local notation "E₁" => functorToComplexOfFunctors (J × K) C c
local notation "E₂" =>
  (Functor.obj (Functor.whiskeringRight J (K ⥤ HomologicalComplex C c)
    (HomologicalComplex (K ⥤ C) c)) (functorToComplexOfFunctors K C c) ⋙
    functorToComplexOfFunctors J (K ⥤ C) c)

def curriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c}
    (f g : F ⟶ G)
    (h : Homotopy ((E₁).map (Functor.uncurry.map f))
      ((E₁).map (Functor.uncurry.map g))) :
    Homotopy ((E₂).map f) ((E₂).map g)
```

置き場所 `HomologicalAlgebra/CurriedDiagramHomotopy.lean`。この記録時点では個別検査中、未コミット・累計には未算入。A02ではこれを `Δ × J` の同じ AW・shuffle のホモトピーへ適用し、各パラメータで存在を選び直さない。停止点2は未完。新しい数学の一覧外追加はない。

## 75. A02の同じ成分の添字交換を検証

§74の `HomologicalAlgebra.CurriedDiagramHomotopy` は `72beb3083` に保存。57行、累計 **143本8,927行**。個別検査、鍵付き対象ビルド **1,227 jobs**、累計 **1,630宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-75.log`、監査 `/private/tmp/AuditISW2G10HundredFortyThree.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortythree-modules.txt`。鍵は指定どおり `--wait 3600`、一枚、1,700秒上限。A02全体を完了とは数えない。

追加登録対象：

```text
SerrePositivity.HomologicalAlgebra.CurriedDiagramHomotopy
```

もう一つ、A02に必要な既存二構成の照合を追加する（追加枠 **2/3**）。重みの射影は `frameWeightDiagram W := CategoryTheory.Prod.snd SimplexCategory J ⋙ W` と固定し、同型の各成分は恒等。

```lean
def freeProductFrameUncurryIso (A : Type u) [CommRing A]
    {J : Type v} [Category.{w} J]
    (W : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u})) :
  Functor.uncurry.obj (freeProductFrame A W P) ≅
    freeNegativeChainsDiagram (A := A)
      (frameWeightDiagram W ⊗ Functor.uncurry.obj P)
```

自然性は自由鎖の合成則とテンソルの合成則だけで証明する。同型の存在に新しい数学を使わない。`DiagramComparison.FreeProductFrameUncurry`（39行）は個別検査済み、対象ビルド・監査中、未コミットで上の累計に未算入。検証中のファイルは変更しない。

## 76. 積frameの同定を検証、A02の両合成へ

`DiagramComparison.FreeProductFrameUncurry` は `4b718e6b8` に保存。39行、累計 **144本8,966行**。個別検査、鍵付き対象ビルド **2,275 jobs**、累計 **1,634宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-76.log`、監査 `/private/tmp/AuditISW2G10HundredFortyFour.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyfour-modules.txt`。鍵は `--wait 3600`、一枚、実行1,700秒上限、検証の間だけ取得。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameUncurry
```

A02の前向き合成 `freeProductFrameAWShuffleHomotopy` は個別検査済み。`Δ × J` 上のA01を、この指定同型で前後から合成し、§74の添字交換で戻した。全パラメータについて一つの鎖ホモトピーになっている。`FreeProductFrameHomotopies.lean` は逆順も含めて検査中で、まだコミット・累計算入していない。

逆順に用いるテンソル側の照合も明記する。追加枠 **3/3**。A02の証明内の局所同型 `e₀` として実装するが、枠から除外はしない。

```lean
-- A : Type u、[CommRing A]、J : Type v、[Category.{w} J]、
-- W : J ⥤ SSet.{u}、P : SimplexCategory ⥤ (J ⥤ SSet.{u})。
e₀ : Functor.uncurry.obj (freeTensorFrame A W P) ≅
  freeNegativeChainsDiagram (A := A) (frameWeightDiagram W) ⊗
    freeNegativeChainsDiagram (A := A) (Functor.uncurry.obj P)
```

各成分は恒等で、自然性はテンソルと自由鎖の合成則のみ。新しい数学ではない。この後、一覧外の数学または追加枠を超える独立した照合宣言が必要になれば、検証済みを保存して型と理由を報告する。A02以降のA03〜D08は未完で、停止点2ではない。

## 77. 一覧A02の全パラメータ・ホモトピーを検証

`DiagramComparison.FreeProductFrameHomotopies` のA02二宣言を `41d84b940` に保存。88行、累計 **145本9,054行**。任意の余単体パラメータ図式について、指定AW・shuffleの両合成が、二重図式の複体で恒等射にホモトピックである。A01を積添字へ適用し、恒等成分の同型と§74の並べ替えで運ぶため、全余単体作用素とJの全射への自然性を含む。これを単体的Hom空間の同値性の完成とはしない。後者はA06〜A09。

個別検査、鍵付き対象ビルド **2,278 jobs**、累計 **1,657宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-77.log`、監査 `/private/tmp/AuditISW2G10HundredFortyFive.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyfive-modules.txt`。共有鍵は `--wait 3600`、一枚の整理券、実行1,700秒上限。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameHomotopies
```

A03 `StandardParameterAugmentation` は既存の `normalizedSimplexCochainContraction_naturality` と `freeStandardSimplexParameterIso` を合成する構成。依存のoleanが未生成だったため依存ソースを含む一時ファイルで個別検査し、成功した。対象ビルド・監査中、未コミット。A04の積側 `ProductFrameCoaction` は個別検査中。いずれも上の検証済み累計には含めない。§73の `liftedStandardSimplexParameter (u := u)` は宇宙を項引数に書いてしまった記法上の誤りであり、実装では係数環と同じ宇宙を型から固定する。数学的な型の変更ではない。追加枠は3/3のまま。

## 78. 一覧A03の標準パラメータ増大写像を検証

`DiagramComparison.StandardParameterAugmentation` を `bf6a100e0` に保存。35行、累計 **146本9,089行**。既存の全単体で自然な正規化単体の増大写像を、指定 `freeStandardSimplexParameterIso` で戻した。⑤aの既存ファイルは変更していない。

依存ソースを含む個別検査、鍵付き対象ビルド **2,352 jobs**、累計 **1,669宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-78.log`、監査 `/private/tmp/AuditISW2G10HundredFortySix.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortysix-modules.txt`。鍵は `--wait 3600`、整理券一枚、実行1,700秒上限で検証の間だけ使用。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
```

## 79. 一覧A04の両frameの指定余作用を検証

`DiagramComparison.ProductFrameCoaction`（39行）と `DiagramComparison.TensorFrameCoaction`（54行）を `f592cd727` に保存。新規2本93行、累計 **148本9,182行**。

積側は既存のパラメータグラフとAW、テンソル側は同じ自由鎖の対角とAW・結合子で構成し、全単体作用素への自然性を証明した。係数環の宇宙を明示する `standardParameterForCoefficients A J` は既存 `liftedStandardSimplexParameter J` の型略記であり、新しい数学の主張ではない。§73の局所記法Pもこの略記に修正した。単位則A05はまだ証明していない。

個別検査、鍵付き対象ビルド **2,278 jobs**、累計 **1,695宣言・標準三公理のみ**の監査が成功、終了コード0。`sorry`・独自公理0。ログ `/private/tmp/isw2-g10-build-79.log`、監査 `/private/tmp/AuditISW2G10HundredFortyEight.lean`、登録待ち一覧 `/private/tmp/isw2-g10-hundredfortyeight-modules.txt`。鍵は `--wait 3600`、一枚、実行1,700秒上限。全検証プロセスは終了し、鍵は解放済み。

追加登録対象：

```text
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.TensorFrameCoaction
```

再開後の一覧の実績は **A01〜A04完了**。独立した照合の追加枠は§74〜76の **3/3**。未コミットのLeanはない。外枠12,500行の残りは3,318行で、行数による中間停止はしない。次はA05の指定余作用の単位則、A06〜A09の区間評価と実単体的Hom比較の同値性へ進む。B01〜D08も引き続き今回の責任であり、停止点2は未完。

A05に再利用できる候補を確認した：`EInfinity.AlexanderWhitney.cochainDiagonal_right_counit` と `cochainCounit_stdSimplex_eq_contraction`。ただし前者の対角と、今回の整数から係数移送した指定AWの一致は型の類似だけでは済ませない。A06の端点に使う零単体の単位同型には既存 `cochainCounit_stdSimplexZero_isIso` が候補となる。これらは現時点の参照候補で、A05・A06の検証完了には数えない。

## 80. A05の展開と、一覧外の右増大写像整合性による停止

A05の積側を `FrameCoactionCounit.lean` の作業木で展開した。各余単体・各図式対象での指定写像の等式へ戻し、正次数は零延長の零性で処理した。負次数は延長の指定同型と Moore 射影の分裂を使って自由生成元での等式へ帰着した。ここまでのスクリプトの残りはその生成元の目標であり、**A05の証明全体は未完**。66行の未検証下書きはコミットせず、検証済み148本9,182行には算入しない。個別検査ログ `/private/tmp/isw2-a05-generators.log` は未解決目標を報告して終了コード1であり、成功した検証とは数えない。

### 80.1 一覧に追加が必要になった数学の補題の型

A05の両単位則への接続に用いる次の二因子AWの法則が、§73の一覧から漏れていた。提案名 `freeProductAlexanderWhitney_right_augmentation`。以下は CategoryTheory、MonoidalCategory、CartesianMonoidalCategory、ComplexLimits、DiagramComparison、Project.DerivedCategories の名前を開いた表記。

```lean
theorem freeProductAlexanderWhitney_right_augmentation
    (A : Type u) [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A)
    (Z : SSet.{u}) (n : SimplexCategory) :
  freeProductAlexanderWhitney φ Z
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) ≫
    (𝟙 (freeNegativeChains (A := A) Z) ⊗ₘ
      (normalizedSimplexCochainContraction A n).hom) ≫
    (ρ_ (freeNegativeChains (A := A) Z)).hom =
    freeNegativeChainsMap (A := A)
      (fst Z ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)))
```

この**主張の型だけ**を `/private/tmp/isw2-a05-right-augmentation-type.lean` の `rightAugmentationStatement : Prop` として elaboration し、終了コード0を確認した（ログ `/private/tmp/isw2-a05-right-augmentation-type2.log`）。証明を与えたわけではなく、公理や `sorry` で埋めてもいない。

内容は、指定AWの第二因子を同じ単体増大写像で潰すと、元の積から第一因子への射影の自由鎖写像そのものになる、という**厳密な等式**。一般のZを許す必要がある。積側A05には `Z = W.obj j × Δ[n]` を代入し、パラメータグラフを前合成する。テンソル側A05には `Z = Δ[n]` を代入し、対角を前合成する。グラフ／対角と第一射影の合成が恒等であること、および結合子の自然性で、それぞれ元のA05へ戻る。

### 80.2 漏れた理由と既存宣言との差

§73では、A05を既存のAW余単位則と係数移送に接続する内部計算として見込み、上の二因子の法則を型つきで独立に列挙しなかった。これは一覧の粒度が不足していた。

確認した既存 `EInfinity.AlexanderWhitney.cochainDiagonal_right_counit` は、`X : SSet.{0}` に対する別の直接構成の対角と、その構成の `cochainCounit` の法則。今回の左辺は、任意の宇宙のZと持ち上げ標準単体の積に対する `freeProductAlexanderWhitney` であり、`normalizedMooreMapIso`・整数テンソルの係数拡大・負次数延長を経由する。`cochainCounit_stdSimplex_eq_contraction` は増大写像の同定に使えるが、二因子AWの上の法則までは結論しない。

上の法則を作らずA05に成分計算を直接埋め込む形も数学的には考えられる。しかし、必要なAWの右増大写像計算を「実装上の同定」として追加枠から外したり、局所補題として黙って隠したりはしない。今回の停止は数学的な不可能性の主張ではなく、**残補題を型つきで列挙してから進めるという新しい規則に対する不足の報告**である。

### 80.3 保存状態と停止条件

検証済みコードは `f592cd727` まで、直前の検証報告は `f9a44613a`。148本9,182行、最後の対象ビルド2,278 jobsと累計1,695宣言・標準三公理のみの監査は§79のとおり。今回、新しく検証済みと呼べるLean宣言は増えていない。ビルドの鍵は取得していない。

ユーザー指示2「一覧にない新しい数学の補題が要ったら、検証済みをコミットして止まり、その型と一覧から漏れた理由を報告」に従い、**A05の追加証明をここで停止する**。照合追加枠は3/3のままで、この法則を4本目の単なる照合とは扱わない。外枠12,500行による停止ではない。停止点2も未完。

上の一補題を第一のまとまりのA05の前提計算として一覧に加える判断を求める。範囲を別の第五のまとまりへ広げる案ではなく、同じ指定余作用と増大写像を保持するための補題である。承認後はこの法則を証明し、A05の両単位則へ接続してからA06以降へ進む。

## 81. A05aの承認を反映、前提計算の枠を開始

11-13のユーザー指示とmainのIS-W2 §13を確認した。§80.1の型をそのまま **A05a** に追加し、停止を解除する。前提計算の枠は照合枠3/3とは別に管理する。外枠12,500行、凍結確定後はコミットを控える規則も維持する。現時点で凍結確定の連絡は未受領。

### 81.1 前提計算1/3：右因子が零次だけに値を持つ場合のAW切断和

提案・実装名 `alexanderWhitneyApp_right_zero_degree`。既存AWの右余単位計算に使う法則で、新しい比較模型を導入しない。

```lean
theorem alexanderWhitneyApp_right_zero_degree
    (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : (AlgebraicTopology.alternatingFaceMapComplex _).obj C ⟶ K)
    (g : (AlgebraicTopology.alternatingFaceMapComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
    alexanderWhitneyApp C D n ≫ (chainIntegerTensorMap f g).f n =
      alexanderWhitneySummand C D n (Fin.last n) ≫ (chainIntegerTensorMap f g).f n
```

名前空間は既存の `Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories` のAW・整数テンソルを開いた表記。置き場所は `DiagramComparison/AWRightAugmentationCut.lean`。最後以外の切断では第二次数 `n-i` が正なので、仮定hgと整数テンソルの零写像則でその項を消す。A05aではMoore射影と増大写像を合成したgに適用する。まず整数係数のこの計算を閉じ、その後に指定係数移送を戻す。

この記録時点では個別検査中、未コミット。§80の未完下書きも引き続き作業木に保持し、検証済み148本9,182行には算入しない。照合枠3/3、前提計算枠1/3。

### 81.2 前提計算2/3：Moore正規化後の最後の切断

1本目を、既存のMoore包含と二因子の射影で挟む法則。`NormalizedAWRightAugmentationCut.lean` で個別検査中。名前空間は§81.1とDoldKanを開く。

```lean
theorem normalizedAlexanderWhitney_right_zero_degree
    (C D : SimplicialObject (ModuleCat.{u} ℤ))
    {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (g : (normalizedMooreComplex _).obj D ⟶ L)
    (hg : ∀ k : ℕ, k ≠ 0 → g.f k = 0) (n : ℕ) :
  (normalizedAlexanderWhitney C D ≫ chainIntegerTensorMap (𝟙 _) g).f n =
    (inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n ≫
      integerTensorMap ((PInftyToNormalizedMooreComplex C).f n)
        (D.map (awBack n (Fin.last n)).op ≫
          (PInftyToNormalizedMooreComplex D ≫ g).f (n - n)) ≫
      ιMapBifunctor ((normalizedMooreComplex _).obj C) L integerTensorBifunctor
        (.down ℕ) n (n - n) n (awDegrees n (Fin.last n))
```

最後の切断では `awFront n (Fin.last n) = 𝟙 _` であり、第二次数は `n-n`。dependentな次数を不必要に書き換えず、元の直和包含の添字をそのまま保持する。前提計算枠2/3、照合枠3/3。A05aの係数移送後の主張はまだ未完。

## 82. A05aの前提計算2本を検証・保存

§81.1・§81.2の型を変更せず、非正規化AWとMoore正規化AWの右零次切断則を証明した。コードコミット **`0fee2038e`**。いずれも既存AWの最後以外の切断を零にし、最後の前面が恒等であることを使う。正規化版は指定された包含・射影・直和包含を保持する。既存の宣言は変更していない。

| 新規モジュール（DiagramComparison/） | 行数 | 内容 |
| --- | ---: | --- |
| AWRightAugmentationCut | 45 | 右因子が零次以外で零のとき、有限切断和は最後の切断に等しい |
| NormalizedAWRightAugmentationCut | 54 | 同じ公式をMoore包含・射影で挟んだ正規化AWの公式 |

### 82.1 検証

個別の結合ソース検査 `/private/tmp/isw2-a05a-normalized-check6.lean` は終了コード0。続いて `with_build_lock.sh --wait 3600` と1700秒の実行上限で、`NormalizedAWRightAugmentationCut` の対象ビルドと累計の一時監査を実行し、終了コード0を確認した。対象ビルド **1,804 jobs**、累計 **150モジュール・1,697宣言、標準三公理のみ**。新規2本にsorry・新公理なし。鍵は検証終了時に返却済み。

- ログ：`/private/tmp/isw2-build82.log`
- 監査：`/private/tmp/AuditISW2G10HundredFifty.lean`
- 対象一覧：`/private/tmp/isw2-g10-hundredfifty-modules.txt`

3b-2の検証済み実測は **9,281行**（§79の9,182行 + 99行）。外枠12,500行まで3,219行。登録すべき追加モジュールは上表の2本であり、入口と公式監査は編集していない。

### 82.2 A05a本体の作業木と残り

`FreeProductAWRightAugmentation.lean` に§80.1と同じ型の証明を開始した。正次数は零延長の零性で閉じ、非正次数は指定の延長項同型・Moore射影の分裂を前合成して、元の自由生成元における等式に帰着した。個別検査 `/private/tmp/isw2-a05a-body1.log` はその負次数の生成元等式が未解決のため終了コード1。**A05aはまだ証明済みではない**。この49行の下書きと、以前の `FrameCoactionCounit.lean` 66行は未コミット・上の検証済み行数に不算入。

次に必要なのは、正規化AWの切断公式を、指定された `normalizedMooreMapIso`・`integerNegativeTensorBaseChangeIso`・自由化比較・負次数延長を通して、同じ `normalizedSimplexCochainContraction` の右増大写像へ接続する成分計算。別の直接AWへの置換や、余単位則を仮定とする型の変更はしていない。A05aが閉じた後にA05の両単位則、A06以降へ進む。停止点2は未完。

前提計算の枠は **2/3**（残り1本）、照合の枠は **3/3** のまま。新しい数学の追加による停止ではなく、承認済みA05aの証明途中の記録。凍結確定の連絡は、この保存時点で未受領。

## 83. 前提計算3/3：係数移送と斉次包含の照合

A05aで整数AWの切断公式を一般Aに移すため、既存の係数移送の成分則を前提計算枠の3本目に追加する。独立の数学的比較を作るのではなく、`integerNegativeTensorBaseChangeIso` の定義に含まれる既存の同型の成分公式を合成する。置き場所は `DiagramComparison/IntegerNegativeTensorCoefficients.lean`。

以下で `F := integerCoefficientExtension φ`、`Kφ := (F.mapHomologicalComplex (.down ℕ)).obj K`、`Lφ := (F.mapHomologicalComplex (.down ℕ)).obj L`。`A : Type u`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A`、`K L : ChainComplex (ModuleCat.{u} ℤ) ℕ` を引数とする。

```lean
theorem integerNegativeTensorBaseChangeIso_ι (i j n : ℕ) (h : i + j = n) :
    (F).map (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫
      ((((F).mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor K L)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (integerNegativeTensorBaseChangeIso K L φ).hom.f (-(n : ℤ)) =
    (ModuleCat.extendScalars φ).map (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
        (integerCoefficientModuleFunctor.obj (K.X i))
        (integerCoefficientModuleFunctor.obj (L.X j)) ≫
      (((Kφ).extendXIso ComplexShape.embeddingDownNat (i := i) (i' := -(i : ℤ)) rfl).inv ⊗ₘ
        ((Lφ).extendXIso ComplexShape.embeddingDownNat (i := j) (i' := -(j : ℤ)) rfl).inv) ≫
      ιTensorObj ((Kφ).extend ComplexShape.embeddingDownNat)
        ((Lφ).extend ComplexShape.embeddingDownNat) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
        (by omega)
```

前提計算枠3/3、照合枠3/3。追加時点では証明・検査中であり、検証済みの150本・9,281行には算入しない。A05aは引き続き未完。

### 83.1 検証と保存

コード **`47d7ebdb1`**、新規1本84行。個別検査 `/private/tmp/isw2-coefficient-cut13.log` は終了コード0。鍵付きの対象ビルド（`--wait 3600`、実行上限1700秒）は **2,239 jobs** で成功し、続く累計監査も終了コード0。累計 **151モジュール・1,700宣言、標準三公理のみ**、検証済み **9,365行**。追加の3宣言にはLeanが生成した補助宣言を含み、手書きの主張は上記の一つ。sorry・新公理なし、既存宣言の変更なし。

- ログ：`/private/tmp/isw2-build83.log`
- 一時監査：`/private/tmp/AuditISW2G10HundredFiftyOne.lean`
- 対象一覧：`/private/tmp/isw2-g10-hundredfiftyone-modules.txt`
- 登録対象の追加：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerNegativeTensorCoefficients`

鍵は検証終了時に返却済み。入口と公式監査は変更していない。外枠12,500行まで3,135行。前提計算枠3/3、照合枠3/3。

A05a本体の作業木では、指定増大写像の零次以外での零性を既存の単一複体の零性から得た。また、射影側の右辺はMoore射影の自然性・零延長の指定同型・自由生成元の写像則で、第一成分の生成元をMoore射影して延長へ戻す式まで整理した（`/private/tmp/isw2-a05a-body8.log`、残る主目標があるため終了コード1）。AW側の係数移送との照合が残る。A05a・A05・停止点2はまだ未完であり、下書きはコミットしていない。

### 83.2 A05a入力のMoore比較の整理

その後、A05aの未コミット下書きで、入力の自由化比較をMoore射影の自然性で射影の前へ移し、`normalizedMooreMapIso` の逆を定義どおりに展開した。包含と射影の合成を既存の `PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap` により正規化冪等射へまとめ、既存 `alternatingMapIso_PInfty` と `PInfty_comp_PInftyToNormalizedMooreComplex` で係数移送前の射影へ戻した。追加の独立した補題は導入していない。

最後の個別検査 `/private/tmp/isw2-a05a-body19.log` は、これらの内部手順にはエラーがなく、負次数の主等式が未解決のため終了コード1。左辺の入力は今や、元の整数Moore射影の係数拡大に対し、元の整数正規化AWの係数拡大を適用する形になった。右辺は第一射影の生成元をMoore射影する明示式。次はAWの切断成分に§81・§83の公式を適用し、同じ右増大写像・右単位子を通した式を右辺と照合する。

`FreeProductAWRightAugmentation.lean` は120行の未完下書きとして作業木に保持する（検証済み9,365行に不算入）。A05a・A05・停止点2は未完。検証済みのコード保存点は引き続き `47d7ebdb1`、前提計算枠3/3・照合枠3/3。凍結確定の連絡は未受領で、未検証コードはコミットしていない。

## 84. A05aを最後の切断へ帰着、余単位の独立補題の追加判断

### 84.1 今回の到達点

A05aの作業木で、整数の正規化AWを非正規化の切断和へ戻し、§83の係数移送の斉次包含公式を適用した。同じ増大写像の零次以外の零性により、右因子の次数が正であるすべての切断成分を消した。有限和を最後の切断 `Fin.last k` だけにする内部計算も通り、A05aの主目標はその一項の等式へ帰着した。`/private/tmp/isw2-a05a-body24.log` はこの段階の主等式だけが未解決で終了コード1。証明全体の成功とは数えない。

最後の切断の値は、係数拡大随伴と既存 `integerTensor_hom_ext` で二つの整数自由生成元に帰着した。入力の自由化比較、前面・後面の純テンソル評価、二つのMoore射影の純テンソル評価は内部の小さい等式として検査を通った。A上の `ULift.module` がφ由来の加群構造と競合していたため、φ由来の `Module simplicialRingCoefficient A` を明記した。切り分け専用 `/private/tmp/isw2-coefficient-pure-probe2.log` は終了コード0。既存の宣言・インスタンスは変更していない。

### 84.2 切り出す主張の型

次の一つを `DiagramComparison/FreeProductAWLastCut.lean` に独立した補題として切り出す案。数学内容は、**指定AWの最後の切断を、同じ係数移送・Moore射影・単体増大写像・右単位子で評価する余単位則**。別の比較模型や新しい第五のまとまりではない。

```lean
theorem freeProductAlexanderWhitney_last_cut_right_augmentation
    (A : Type u) [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
    (Z : SSet.{u}) (n : SimplexCategory) (k : ℕ) :
  let Y := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)
  let F := integerCoefficientExtension φ
  let NC := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Z)
  let ND := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
  let e0 := Functor.isoWhiskerRight (linearizedTensorIso Z Y) F ≪≫
    integerCoefficientSimplicialFreeIso φ (Z ⊗ Y)
  F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
      k (Fin.last k) ≫
      (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace Z))
        (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f k) ≫
    (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).extendXIso
      ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv ≫
    ((negativeMooreTensorCoefficientIso φ (linearizedSpace Z) (linearizedSpace Y)).hom ≫
      (tensorIso (integerCoefficientFreeChainsIso φ Z)
        (integerCoefficientFreeChainsIso φ Y)).hom ≫
      (𝟙 _ ⊗ₘ (normalizedSimplexCochainContraction A n).hom) ≫
      (ρ_ (freeNegativeChains (A := A) Z)).hom).f (-(k : ℤ)) =
    e0.hom.app (Opposite.op ⦋k⦌) ≫
      (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
      (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (Z ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv

```

型だけを `/private/tmp/isw2-a05a-last-cut-type.lean` の命題値の定義として検査し、終了コード0を確認した（ログ `/private/tmp/isw2-a05a-last-cut-type.log`）。これはこの命題の証明ではない。上記の独立宣言はまだ本体に追加していない。

### 84.3 独立補題が必要になった理由と停止

§81〜83では、切断和、Moore正規化後の切断公式、係数移送の斉次包含公式を三つの前提計算として列挙した。しかし最後に残る零次増大写像・右単位子の値の照合を、独立の型として列挙せずA05aの中に展開する見込みだった。

その形で実装を進めると、最後の値の計算の途中で既定の200,000 heartbeatに達する。`/private/tmp/isw2-a05a-body42.log` の一時計測では、係数テンソルの逆比較の値を述べる直前の残量は内部単位518,963（表示上のheartbeatで約519）だった。大きな式全体の書き換えを `conv` で対象箇所に限定し、増大写像の始域も局所名で揃えたが、累計の余裕を確保できていない。計算上限は上げていない。一時的な計測コードは下書きから除去した。

提案は、上記の余単位則を独立に証明し、A05a本体では最後の切断へ帰着した所から適用すること。数学的な不可能性や新たな仮定の必要性ではなく、**型つき一覧の粒度と証明の分割に関する追加判断**である。A05aの型を弱めたり、余単位則を仮定に置いたりはしない。

11-13のユーザー指示（IS-W2 §13）の「法則の補題は、3本まで止まらずに一覧に足してよい」に対し、前提計算枠は既に3/3。照合枠も3/3。この余単位則を4本目の独立補題として黙って追加しないため、ここで追加のLean作業を停止し、上記一補題の追加承認を求める。A05aと同じ第一のまとまりに属し、外枠12,500行の変更は求めない。

### 84.4 保存状態

検証済みの保存点は `47d7ebdb1`、前回の報告は `2acb5b5f3`。**151モジュール・9,365行・1,700宣言、標準三公理のみ**は§83の検収結果から変わらない。今回、新しく完成した本体宣言はないため、鍵付きビルド・監査を成功したとは報告しない。ビルドの鍵は取得しておらず、待機中の整理券もない。

A05aの下書き `FreeProductAWRightAugmentation.lean` は296行、以前の `FrameCoactionCounit.lean` は66行。両方未コミット・検証済み行数に不算入。新しい未検証コードをコミットしていない。既存宣言・⑤aのファイル・入口・公式監査は変更していない。凍結確定の連絡は未受領。A05a・A05・停止点2は引き続き未完。

## 85. §14の承認を反映し、A05aの証明を分割

11-13のユーザー指示に従い、§84.2の最後の切断の余単位則を同じ型で `FreeProductAWLastCut.lean` に切り出した。証明の分割は追加枠に算入せず、型を本報告へ記録する。前提計算は一覧の補題ごとに3本、照合枠は全体3/3、外枠12,500行の規則を維持する。計算上限は上げていない。

### 85.1 同じMoore射影計算の部分補題

以下二つはA05aで使っている既存のMoore比較と射影の計算を分けたもの。新しい模型を作らない。

`SerrePositivity/HomologicalAlgebra/NormalizedMooreMapProjection.lean`

```lean
theorem normalizedMooreMapHom_projection :
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex X) ≫
      normalizedMooreMapHom F X =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app X ≫
      PInftyToNormalizedMooreComplex (X ⋙ F)
```

`SerrePositivity/InfinityCategories/Project/DerivedCategories/DiagramComparison/FreeChainsCoefficientProjection.lean`

```lean
theorem freeChainsCoefficient_projection {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) :
    ((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map
        (PInftyToNormalizedMooreComplex (linearizedSpace X)) ≫
      normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X) ≫
      (normalizedMooreComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom =
    (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (integerCoefficientExtension φ)).hom.app (linearizedSpace X) ≫
      (alternatingFaceMapComplex (ModuleCat A)).map
        (integerCoefficientSimplicialFreeIso φ X).hom ≫
      PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)
```

第一の型では `{C D : Type*}` に圏・アーベル圏、`F : C ⥤ D` に加法性、`X : SimplicialObject C` を仮定する。第二は型に記載の引数を持つ。名前はそれぞれ `SerrePositivity.HomologicalAlgebra`、`DiagramComparison` の名前空間。結合ソースの個別検査 `/private/tmp/isw2-free-projection-check3.log` は終了コード0。鍵付きの対象ビルド・監査を実行中のため、この記録時点では検証済み151本の実績はまだ更新しない。

### 85.2 最後の切断の証明の現在地

独立した `FreeProductAWLastCut.lean` では、係数テンソルの逆比較とδの純テンソル評価を通過し、二因子のMoore比較・自由化比較・零次増大写像・右単位子の値を照合する主等式が残る。個別検査 `/private/tmp/isw2-last-cut5.log` はその主等式が未解決で終了コード1。A05aの元の下書きとともに未コミットで保持し、A05a・A05・停止点2の完了とは数えない。

### 85.3 負次数成分への同じ計算の分割

最後の切断の証明内で、以下の成分等式を使用する。`F := integerCoefficientExtension φ` とし、`A : Type u`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A` を固定する。これは§85.1を零延長の成分公式で表す同じ内容の部分計算であり、検査中。独立した新しい数学の補題として追加しない。

```lean
have hμ (X : SSet.{u}) (r : ℕ) :
      F.map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
        ((((F.mapHomologicalComplex (.down ℕ)).obj
          ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv) ≫
        (extendMap (normalizedMooreMapHom F (linearizedSpace X)) ComplexShape.embeddingDownNat ≫
          (integerCoefficientFreeChainsIso φ X).hom).f (-(r : ℤ)) =
      (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
        (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r ≫
        (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
```

### 85.4 成分式と生成元評価の独立した分割

§85.3の内部計算とその自由生成元での値は、再利用時に累計heartbeatを消費しないよう `FreeChainsCoefficientDegrees.lean` に分けた。同じA05aの計算の分割である。個別検査 `/private/tmp/isw2-free-degrees2.log` は終了コード0。型は次のとおり（DiagramComparison名前空間）。

```lean
theorem freeChainsCoefficient_degree {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) :
    (integerCoefficientExtension φ).map ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r) ≫
      (((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
        ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv) ≫
      (extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X)) ComplexShape.embeddingDownNat ≫
        (integerCoefficientFreeChainsIso φ X).hom).f (-(r : ℤ)) =
    (integerCoefficientSimplicialFreeIso φ X).hom.app (Opposite.op ⦋r⦌) ≫
      (PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
```

```lean
theorem freeChainsCoefficient_generator_value {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A) (X : SSet.{u}) (r : ℕ) (a : X.obj (Opposite.op ⦋r⦌)) :
    ((integerCoefficientFreeChainsIso φ X).hom.f (-(r : ℤ)))
      ((extendMap (normalizedMooreMapHom (integerCoefficientExtension φ) (linearizedSpace X))
        ComplexShape.embeddingDownNat).f (-(r : ℤ))
        ((((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv)
          ((integerCoefficientExtension φ).map
            ((PInftyToNormalizedMooreComplex (linearizedSpace X)).f r)
            ((integerCoefficientFreeAdjunction φ).unit.app _ a)))) =
    (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
      ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
      ((PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f r (ModuleCat.freeMk a))
```

### 85.5 ここまでの検収

`NormalizedMooreMapProjection` は27行、コード `df8a4ca14`。対象ビルド1,331 jobs、152モジュール・1,702宣言、標準三公理のみ（`/private/tmp/isw2-build85.log`）。`FreeChainsCoefficientProjection` は34行、コード `3a3da1089`。対象ビルド2,242 jobs、153モジュール・1,704宣言、標準三公理のみ（`/private/tmp/isw2-build85b.log`）。どちらも `--wait 3600` の鍵付きビルド・一時監査で終了コード0。検証済み実測は9,426行。入口と公式監査は変更していない。

成分・生成元評価の67行は別の鍵付きビルド・154本の一時監査で検査中。最後の切断とA05aの下書きは引き続き未完・未コミット。追加判断を求める停止ではなく、§14の承認内での証明途中。

### 85.6 最後の切断の残る値

§85.4を独立させた結合検査 `/private/tmp/isw2-last-cut-check9.log` では、両因子への生成元評価の適用を通過した。残る主等式は、第一因子が元のA自由生成元のMoore射影・負次数延長となり、第二因子が同じ標準単体増大写像をそのMoore射影へ適用した形。第二因子の零次の値が1であることと、右単位子・最後の前面の恒等性の照合が残る。この検査は主等式が未解決で終了コード1であり、最後の切断の補題の証明完了とは数えない。A05a・A05・停止点2は未完。

### 85.7 標準単体増大写像の零次の値の分割

最後の切断で残る、同じ増大写像の既存の生成元の値を次の型で `StandardParameterAugmentationValues.lean` に分割する。既存 `normalizedSimplexCochainAugmentation_zero_apply` と `normalizedSimplexChainAugmentation_zero` をMoore零次射影へ接続する同じ計算である。検査中であり、検証済み実績へ算入しない。

```lean
theorem standardParameterAugmentation_moore_generator (A : Type u) [CommRing A]
    (n : SimplexCategory)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋0⦌)) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (normalizedSimplexCochainContraction A n).hom.f 0
      ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl).inv
        ((PInftyToNormalizedMooreComplex W).f 0 (ModuleCat.freeMk a))) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
```

直接の個別検査では既存依存の `.olean` が9本不足したため、必要な既存ソースだけを一時ファイルに結合して検査している。共有鍵の待機は154モジュールの一件のまま。

### 85.8 成分・生成元評価の検収と残り

`FreeChainsCoefficientDegrees`（67行）は `e4d2f29c4` に保存した。鍵付き対象ビルド2,359 jobs、一時監査154モジュール・1,706宣言、標準三公理のみで終了コード0（`/private/tmp/isw2-build85c.log`、`/private/tmp/AuditISW2G10HundredFiftyFour.lean`、対象一覧 `/private/tmp/isw2-g10-hundredfiftyfour-modules.txt`）。検証済み実測 **9,493行**。今回の三つの証明分割で計128行増えた。対象のsorry・新公理なし。既存宣言・⑤aのファイル・入口・公式監査は変更していない。鍵は返却済み。

`StandardParameterAugmentationValues` の結合検査 `/private/tmp/isw2-aug-values-check3.log` は終了コード0。これはまだ対象ビルド・累計監査に含めておらず、上の154本に不算入。

最後の切断の結合検査 `/private/tmp/isw2-last-cut-check11.log` は、前面の恒等射の値で通常の `rw` が定義上の一致を見つけられず、その後の検査でも既定heartbeatに達して終了コード1。零次増大写像の値までの接続を追記したが、最後の切断の補題全体は未完。計算上限は上げず、必要な同じ計算の分割を§14の範囲内で続ける。追加承認を求める停止ではない。A05a・A05・停止点2は未完であり、最後の切断・零次増大写像・A05a・A05の各下書きは未コミット。

## 86. 最後の切断の純テンソル計算を指定単位で分割

§14に従い、前回の長い純テンソル評価を次の三宣言に分ける。`coefficientUnit` は既存の係数拡大随伴の単位への略記。二つの値公式はいずれも既存の定義から `rfl` で証明でき、`/private/tmp/isw2-tensor-values2.log` は終了コード0。同じA05aの証明の分割であり、照合枠や新しい数学の補題の追加としては数えない。型は次のとおり（DiagramComparison名前空間、`{A : Type u}`、`[CommRing A]`、`φ : simplicialRingCoefficient.{u} →+* A` を固定）。

```lean
abbrev coefficientUnit (M : ModuleCat.{u} ℤ) :=
  (simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)).unit.app M
```

```lean
theorem coefficientUnit_tensorMap {M M' N N' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (g : N ⟶ N') (x : M) (y : N) :
    (integerCoefficientExtension φ).map (integerTensorMap f g)
      (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y)) =
    coefficientUnit φ (integerTensor M' N') (f x ⊗ₜ[ℤ] g y)
```

```lean
theorem coefficientUnit_tensorComparison (M N : ModuleCat.{u} ℤ) (x : M) (y : N) :
    (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
      (integerCoefficientModuleFunctor.obj M) (integerCoefficientModuleFunctor.obj N))
      (((ModuleCat.extendScalars φ).map (integerCoefficientTensorIso M N).inv)
        (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y))) =
    TensorProduct.tmul A
      (M := (integerCoefficientExtension φ).obj M)
      (N := (integerCoefficientExtension φ).obj N)
      (coefficientUnit φ M x) (coefficientUnit φ N y)
```

`IntegerCoefficientTensorValues.lean` と§85.7の `StandardParameterAugmentationValues.lean` の対象ビルド・156本の一時監査を、共有鍵 `--wait 3600` で開始した。一つの整理券にまとめており、前回の鍵は返却済み。最後の切断の下書きではこの値公式に置換し、未ビルドの既存依存だけを含む一時結合ソースで個別検査中。全体の成功前にコミットしない。

### 86.1 値の部分補題2本の検収

コード `8dc9fc615`：`IntegerCoefficientTensorValues` 41行、`StandardParameterAugmentationValues` 38行。鍵付き対象ビルド3,963 jobs、累計156モジュール・1,710宣言、標準三公理のみで終了コード0（`/private/tmp/isw2-build86.log`）。一時監査 `/private/tmp/AuditISW2G10HundredFiftySix.lean`、対象一覧 `/private/tmp/isw2-g10-hundredfiftysix-modules.txt`。検証済み実測 **9,572行**。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。鍵は返却済み。

最後の切断の結合検査は、公式の引数・適用箇所を明示しても既定heartbeatで未完。既存 `Unitors` の未ビルド依存を含む50モジュールの結合ソースになっていたため、通常のモジュール境界で検査するために既存 `Unitors` のみの対象ビルドを共有鍵 `--wait 3600` で開始した。これは最後の切断の証明成功を意味せず、A05a・A05・停止点2は未完。

## 87. 承認済みの最後の切断の余単位則を検収

`freeProductAlexanderWhitney_last_cut_right_augmentation` を§84.2と同じ型で証明した。個別検査 `/private/tmp/isw2-last-cut-check19.log` は終了コード0。コード **`7d081b8c5`**（`FreeProductAWLastCut` 169行、`StandardParameterRightUnit` 37行）。鍵付き対象ビルド4,012 jobs、累計 **158モジュール・1,713宣言、標準三公理のみ**で終了コード0（`/private/tmp/isw2-build87.log`、監査 `/private/tmp/AuditISW2G10HundredFiftyEight.lean`、一覧 `/private/tmp/isw2-g10-hundredfiftyeight-modules.txt`）。検証済み実測 **9,778行**。計算上限は既定のまま、sorry・新公理なし。

追加した単位子の部分補題の型は以下。これは同じ最後の切断の計算の分割で、§14により追加枠へ算入しない。

```lean
theorem standardParameter_right_unit (A : Type u) [CommRing A]
    (n : SimplexCategory) (P : CochainComplex (ModuleCat A) ℤ)
    (r : ℕ) (hr : r = 0) (q : ℤ)
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)).obj (Opposite.op ⦋r⦌))
    (x : P.X q) :
    let W := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⋙ ModuleCat.free A
    (ρ_ P).hom.f q (ιTensorObj P (𝟙_ (CochainComplex (ModuleCat A) ℤ)) q (-(r : ℤ)) q
      (by subst r; simp) (x ⊗ₜ[A]
      (normalizedSimplexCochainContraction A n).hom.f (-(r : ℤ))
        ((((normalizedMooreComplex (ModuleCat A)).obj W).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((PInftyToNormalizedMooreComplex W).f r (ModuleCat.freeMk a))))) = x
```

A05aの本体は、最後の切断を適用してMoore冪等射の自然性で戻す末尾へ進んだ。まだ全体の検査成功前であり、A05a・A05・停止点2は未完。本体の未検証下書きはコミットしない。既存宣言・⑤a・入口・公式監査の変更なし。共有鍵は返却済み。凍結確定の連絡はこの時点で未受領。

## 88. A05a・A05を完了し、A06の端点へ

A05aは§80.1の型のまま証明・検証を完了した。コード **`6c529dfaf`**（206行）。最後の切断の余単位則を適用し、Moore冪等射の自然性・自由化比較の逆射との合成・指定射影の冪等性で元の第一射影へ戻した。個別検査 `/private/tmp/isw2-a05a-direct4.log`、鍵付き対象ビルド4,013 jobsと159モジュール・1,714宣言の一時監査が終了コード0（`/private/tmp/isw2-build88.log`）。標準三公理のみ。

A05の積側・テンソル側の指定余作用の両単位則も完了。コード **`e0d0f8e53`**（`FrameCoactionCounit` 80行）。積側はA05aとグラフの第一射影、テンソル側は同じA05aと対角の第一射影・結合子の自然性・右単位子のテンソル公式を用いた。個別検査 `/private/tmp/isw2-frame-counit9.log` と対象ビルド4,015 jobs、160モジュール・1,716宣言の一時監査が終了コード0（`/private/tmp/isw2-build89.log`）。標準三公理のみ。検証済み実測 **10,064行**。監査 `/private/tmp/AuditISW2G10HundredSixty.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixty-modules.txt`。sorry・新公理なし、既存の宣言・⑤a・入口・公式監査の変更なし。

### 88.1 A06の入口：同じ正規化区間の二つの端点

`NormalizedIntervalEndpoints.lean` で零単体の指定増大写像が同型である既存の証明を用い、その逆と二つの頂点包含を合成した。全図式の端点も自然変換として定義した。型は以下（DiagramComparison名前空間）。これはA06の同じ内容の分割。

```lean
def normalizedIntervalEndpointChain (A : Type u) [CommRing A] (ε : Fin 2) :
    𝟙_ (CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChains (A := A)
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))
```

```lean
def normalizedIntervalEndpoint (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    𝟙_ (J ⥤ CochainComplex (ModuleCat A) ℤ) ⟶
      freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌)))
```

個別の結合検査 `/private/tmp/isw2-interval-endpoints-check2.log` は終了コード0。44行の新規モジュールの鍵付き対象ビルドと161本の一時監査を `--wait 3600` で開始した。前の鍵は返却済み。まだ成功前のため、この記録時点では検証済み160本へ算入しない。

A06本体の `normalizedIntervalHom`・両端の評価・前後合成に関する自然性はこれから。既存 `HomologicalComplex.cylinder.desc` とその二端評価、`DifferentialGraded.dgInterval` を確認したが、これらのcylinderで指定された正規化単体区間を置き換えて済ませることはしない。使う場合も指定区間・端点への厳密な比較を保つ。A06〜D08と停止点2は未完。追加承認を求める停止ではなく、承認済みの一覧に沿った進行。

### 88.2 A06の前提計算1/3：端点と増大写像

同じ端点が指定増大写像の切断である法則を、A06の前提計算1本目として追加する。図式版は同じ点ごとの法則を束ねる証明分割。型は以下。個別検査 `/private/tmp/isw2-interval-augmentation1.log` は終了コード0。

```lean
theorem normalizedIntervalEndpointChain_augmentation (A : Type u) [CommRing A] (ε : Fin 2) :
    normalizedIntervalEndpointChain A ε ≫
      (normalizedSimplexCochainContraction A ⦋1⦌).hom = 𝟙 _
```

```lean
theorem normalizedIntervalEndpoint_augmentation (A : Type u) [CommRing A]
    (J : Type v) [Category.{w} J] (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (standardParameterAugmentation A J).app ⦋1⦌ = 𝟙 _
```

共有鍵の同じ待機中の一件へ二本の対象ビルドと162モジュールの監査をまとめた。新しい整理券は発行していない。検証成功までは新規二本をコミット・検証済み実績へ算入しない。

### 88.3 A06本体の次の接続

`normalizedIntervalHom` は指定された `N(Δ[1])` を右因子とする写像として構成する必要がある。内部Homの次数−1コチェインとして同じ鎖ホモトピーを表し、二頂点をf,g、基本1単体をそのコチェインへ送る正規化鎖写像を作り、既存のテンソル–Homの随伴で戻す経路を検討する。図式の自然性は交換関手Eを通したホモトピーの型で与えられており、点ごとの任意選択に置き換えない。

既存cylinderの普遍写像は参考になるが、指定区間とcylinderの別模型の同定を新しい照合として黙って追加しない。照合枠は全体3/3のまま。現在は端点とその増大写像則までであり、上記内部Hom経路の構成・符号・端点評価・前後合成の自然性は未検証。

## 89. A05a・A05完了、A06端点の検収

A06端点と増大写像の切断法則は **`83a842153`** に保存した。`NormalizedIntervalEndpoints` 44行、`NormalizedIntervalEndpointAugmentation` 35行。鍵付き対象ビルド3,979 jobsと162モジュールの一時監査は終了コード0（`/private/tmp/isw2-build90.log`）。累計 **162モジュール・10,143行・1,734宣言、標準三公理のみ**。宣言数にはLean生成の補助宣言も含む。一時監査 `/private/tmp/AuditISW2G10HundredSixtyTwo.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtytwo-modules.txt`。共有鍵は返却済み、待機中の整理券はない。

§85の検証済み154本からの登録対象は、以下の8本（すべて `SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.` の後に続く名前）。入口・公式監査への登録は行っていない。

| モジュール | 行数 | 保存点 |
| --- | ---: | --- |
| IntegerCoefficientTensorValues | 41 | 8dc9fc615 |
| StandardParameterAugmentationValues | 38 | 8dc9fc615 |
| StandardParameterRightUnit | 37 | 7d081b8c5 |
| FreeProductAWLastCut | 169 | 7d081b8c5 |
| FreeProductAWRightAugmentation | 206 | 6c529dfaf |
| FrameCoactionCounit | 80 | e0d0f8e53 |
| NormalizedIntervalEndpoints | 44 | 83a842153 |
| NormalizedIntervalEndpointAugmentation | 35 | 83a842153 |

A05aは承認された型の右増大写像則、A05は積側・テンソル側の両単位則を完了した。A06は指定区間の端点・図式自然性・同じ増大写像に対する切断性まで。A06本体の区間評価、両端の評価、前後合成の自然性、A07以降、B・C・Dの各まとまりは未完であり、停止点2の完了報告ではない。

外枠12,500行まで2,357行。型・範囲を弱めず、計算上限を上げず、sorry・新公理なし。既存宣言と⑤aの既存ファイルの変更なし。照合枠は全体3/3、A06の前提計算は端点増大写像の1/3。その他の今回の分割は§14による同じ証明内容の分割として型を報告した。凍結確定の連絡は本記録時点で未受領。

## 90. A06：同じ区間の低次数境界からコチェイン評価を構成

指定された正規化区間を保持し、同じ線形化Δ[1]の交代面複体から評価を構成した。頂点はx,y、非退化な辺はw、高次は零。条件 `d w = y - x` により一次の鎖写像条件が成り立ち、二次は単調な三頂点の三辺の交代和が零であることから成り立つ。Moore正規化の指定包含を前合成し、既存の零延長・smart切断の随伴で元の正規化コチェイン区間からHへの写像へ戻した。

ホモトピー `h : Homotopy f g` のHomコチェインは `δ h = f-g` の向きなので、辺の値として `-h` を用いる。これにより辺の境界はg−fになる。現在は境界データからの評価までで、ホモトピーからのデータの構成と、Rとのテンソルへの転置、両端評価、自然性は未完。

### 90.1 同じA06の証明分割の型

下記4本は新しい模型の比較を導入せず、A06の構成とその鎖写像条件を分けたもの。追加枠に数えない証明分割として型を記録する。名前空間はDiagramComparison。Boundaryでは `{M N : Type*}` とその加法可換群構造、LowDegreesでは `(A : Type u)` と `[CommRing A]` を固定し、`L := (BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)` と略記する。

`NormalizedIntervalBoundary`

```lean
def intervalVertexValue (x y : N) (i : Fin 2) : N
```

```lean
def intervalEdgeValue (w : M) (i j : Fin 2) : M
```

```lean
theorem interval_vertex_boundary (x y : N) (i j : Fin 2) (hij : i ≤ j) :
    intervalVertexValue x y j - intervalVertexValue x y i =
      if i = 0 ∧ j = 1 then y - x else 0
```

```lean
theorem interval_edge_boundary (d : M →+ N) (x y : N) (w : M) (hw : d w = y - x)
    (i j : Fin 2) (hij : i ≤ j) :
    d (intervalEdgeValue w i j) = intervalVertexValue x y j - intervalVertexValue x y i
```

```lean
theorem interval_triangle_boundary (w : M) (f : Fin 3 →o Fin 2) :
    intervalEdgeValue w (f 1) (f 2) - intervalEdgeValue w (f 0) (f 2) +
      intervalEdgeValue w (f 0) (f 1) = 0
```

`NormalizedIntervalLowDegrees`

```lean
def intervalVertexEvaluation (M : ModuleCat.{u} A) (x y : M) : (L).obj (Opposite.op ⦋0⦌) ⟶ M
```

```lean
def intervalEdgeEvaluation (M : ModuleCat.{u} A) (w : M) : (L).obj (Opposite.op ⦋1⦌) ⟶ M
```

```lean
theorem interval_evaluation_boundary {M N : ModuleCat.{u} A}
    (d : M ⟶ N) (x y : N) (w : M) (hw : d w = y - x) :
    intervalEdgeEvaluation A M w ≫ d =
      (L).map (SimplexCategory.δ (0 : Fin 2)).op ≫ intervalVertexEvaluation A N x y -
      (L).map (SimplexCategory.δ (1 : Fin 2)).op ≫ intervalVertexEvaluation A N x y
```

```lean
theorem interval_evaluation_triangle (M : ModuleCat.{u} A) (w : M) :
    (L).map (SimplexCategory.δ (0 : Fin 3)).op ≫ intervalEdgeEvaluation A M w -
      (L).map (SimplexCategory.δ (1 : Fin 3)).op ≫ intervalEdgeEvaluation A M w +
      (L).map (SimplexCategory.δ (2 : Fin 3)).op ≫ intervalEdgeEvaluation A M w = 0
```

`NormalizedIntervalRawChain`

```lean
def intervalRawChainMap (A : Type u) [CommRing A] (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x) :
    (alternatingFaceMapComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K
```

```lean
def intervalNormalizedChainMap (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (x y : K.X 0) (w : K.X 1)
    (hw : K.d 1 0 w = y - x) :
    (normalizedMooreComplex (ModuleCat A)).obj
      ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj ⦋1⦌)) ⟶ K
```

`NormalizedIntervalCochain`

```lean
def normalizedIntervalCochainMap (A : Type u) [CommRing A]
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0)
    (w : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1)
    (hw : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ H
```

### 90.2 検収と現在地

コード **`1cac2d8b9`**。4本184行（Boundary 39、LowDegrees 67、RawChain 51、Cochain 27）。個別の結合検査 `/private/tmp/isw2-interval-cochain1.log` は終了コード0。鍵付き対象ビルド2,059 jobsと166モジュールの一時監査が終了コード0（`/private/tmp/isw2-build91.log`）。累計 **166モジュール・10,327行・1,758宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSixtySix.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtysix-modules.txt`。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。共有鍵は返却済み。上表の4本を登録対象へ追加する。

次は同じホモトピーの零次コチェインと次数−1成分をsmart切断へ送るデータの構成。そのため `NormalizedIntervalCycleData.lean` の作業木で既存のcyclesへの持ち上げと切断の項同型を使用している。未検証であり、上記実績に算入しない。A06本体と停止点2は未完。計算上限は上げていない。


## 91. A06本体：同じホモトピーから指定正規化区間の図式射を構成

smart切断の零次はcyclesへの持ち上げ、一次は次数−1の項同型で定義した。δh=f−g の規約なので辺には −h を入れる。この内部Homへの区間写像を、既存 `diagramTensorLinearHomEquiv` の逆で戻し、既存 `freeStandardSimplexParameterIso` で同じ自由負鎖の区間へ戻した。点ごとの選択やcylinderへの置換はしていない。

### 91.1 A06の同じ証明の分割の型

以下は一覧A06の構成・境界条件そのものの証明分割（§14）。前提計算枠・照合枠を新しく使わない。最初の二本では `A : Type u`、`[CommRing A]`、CycleDataでは `H : CochainComplex (ModuleCat.{u} A) ℤ` を固定する。Homでは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalCycleData`

```lean
def intervalTruncCycle (z : H.X 0) (hz : H.d 0 1 z = 0) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0
```

```lean
def intervalTruncEdge (w : H.X (-1)) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1
```

```lean
theorem intervalTruncCycle_value (z : H.X 0) (hz : H.d 0 1 z = 0) :
    H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
      (i := 0) (i' := 0) (by simp)
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
      (intervalTruncCycle A H z hz)) = z
```

```lean
theorem intervalTrunc_boundary (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 (intervalTruncEdge A H w) =
      intervalTruncCycle A H y hy - intervalTruncCycle A H x hx
```

```lean
def normalizedIntervalCochainMapOfBoundary
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⟶ H
```


`HomotopyIntervalCochain`

```lean
def homotopyIntervalCochainMap (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ linearHomComplex A R S
```


`NormalizedIntervalHom`

```lean
def normalizedIntervalHom {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    R ⊗ freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))) ⟶ S
```

### 91.2 検収と残り

コード **`959f883a5`**。新規3本140行（CycleData 79、HomotopyIntervalCochain 31、Hom 30）。結合個別検査 `/private/tmp/isw2-homotopy-interval1.log` と本体個別検査 `/private/tmp/isw2-diagram-interval1.log` が通り、鍵付き対象ビルドと一時監査はともに終了コード0。168本時点は2,061 jobs・1,779宣言（`/private/tmp/isw2-build92.log`）、本体追加後は既存の零次切断包含の依存も含め3,993 jobs・1,793宣言（`/private/tmp/isw2-build93.log`）。累計 **169モジュール・10,467行・1,793宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSixtyNine.lean`、対象一覧 `/private/tmp/isw2-g10-hundredsixtynine-modules.txt`。上の3本を登録対象に追加する。共有鍵は返却済み。

A06本体の射はできたが、両端の射がf,gに等しいことと前後合成の自然性は未完。作業木の `NormalizedIntervalVertexValues.lean` で零次生成元の値を照合中。A07以降・B/C/D・停止点2は未完。既存宣言、⑤a、入口、公式監査は変えていない。新公理・sorryなし、計算上限変更なし。A06前提計算は1/3、全体照合枠は3/3のまま。外枠12,500行まで検証済みから2,033行。凍結確定の連絡は未受領。


## 92. A06の指定された両端の厳密等式を完了

零次生成元での評価を、既存のsmart切断Hom回収式とcycles包含で計算した。零単体の増大写像の逆が単位の1を同じ生成元に送ること、元の頂点包含が同じ区間の頂点生成元へ送ることを確認した。内部Homにおける両端等式を、既存テンソル–Hom同値のパラメータ自然性と単位則で図式射の等式へ戻した。指定区間の作り直しも、型の弱化もしていない。

### 92.1 証明分割と前提計算の型

`DiagramTensorUnit` の単位則だけはA06の前提計算 **2/3** として追加する（既存の構成の単位法則）。残りは一覧A06の端点等式の同じ証明分割。照合枠は全体3/3のまま。VertexValuesとEndpointValuesでは `A : Type u`、`[CommRing A]` を固定。DiagramTensorUnitとHomEndpoints後半では `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalVertexValues`

```lean
def normalizedIntervalVertexGenerator (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌)).X 0
```

```lean
theorem normalizedIntervalCochainMapOfBoundary_vertex
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) (ε : Fin 2) :
    (normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw).f 0
      (normalizedIntervalVertexGenerator A ε) = intervalVertexValue x y ε
```


`NormalizedIntervalEndpointValues`

```lean
theorem normalizedIntervalVertexGenerator_map (ε : Fin 2) :
    ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ ε))).f 0
        (normalizedSimplexZeroGenerator A) = normalizedIntervalVertexGenerator A ε
```

```lean
theorem normalizedIntervalEndpointChain_value (ε : Fin 2) :
    (normalizedIntervalEndpointChain A ε).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
        normalizedIntervalVertexGenerator A ε
```

```lean
theorem normalizedIntervalCochainMapOfBoundary_endpoints
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    normalizedIntervalEndpointChain A 0 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨x, hx⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫
      normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw =
        SerrePositivity.DifferentialGraded.unitFromCycle H ⟨y, hy⟩
```


`DiagramTensorUnit`

```lean
theorem diagramTensorLinearHomEquiv_unit {R S : J ⥤ Complex A} (f : R ⟶ S) :
    diagramTensorLinearHomEquiv R S (𝟙_ (Complex A)) ((ρ_ R).hom ≫ f) =
      unitFromCycle (linearHomComplex A ((E).obj R) ((E).obj S))
        ⟨Cochain.ofHom ((E).map f), δ_ofHom ((E).map f)⟩
```


`NormalizedIntervalHomEndpoints`

```lean
theorem homotopyIntervalCochainMap_endpoints (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    normalizedIntervalEndpointChain A 0 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom f, δ_ofHom f⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom g, δ_ofHom g⟩
```

```lean
theorem normalizedIntervalEndpoint_parameter (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (freeStandardSimplexParameterIso A J).hom.app ⦋1⦌ =
      (Functor.const J).map (normalizedIntervalEndpointChain A ε)
```

```lean
theorem normalizedIntervalHom_endpoints {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 0) ≫
      normalizedIntervalHom f g h = f ∧
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 1) ≫
      normalizedIntervalHom f g h = g
```

### 92.2 検収と残り

コード **`c04dbbbbe`**。新規4本290行（VertexValues 71、EndpointValues 102、DiagramTensorUnit 42、HomEndpoints 75）。個別検査 `/private/tmp/isw2-interval-values4.log`、結合検査 `/private/tmp/isw2-interval-endpoint-values2.log`・`/private/tmp/isw2-interval-hom-endpoints2.log` は終了コード0。鍵付き対象ビルドと一時監査も終了コード0（`/private/tmp/isw2-build94.log`：171本・1,806宣言、`/private/tmp/isw2-build95.log`：4,000 jobs・173本・1,810宣言）。累計 **173モジュール・10,757行・1,810宣言、標準三公理のみ**。一時監査 `/private/tmp/AuditISW2G10HundredSeventyThree.lean`、一覧 `/private/tmp/isw2-g10-hundredseventythree-modules.txt`。上の4本を登録対象へ追加する。鍵は返却済み。

A06は本体と指定された両端の厳密等式まで完了。前後合成の自然性は未完で、作業木の `NormalizedIntervalChainNaturality.lean` で同じ自由鎖・正規化鎖評価の後合成を検査中。A07以降・B/C/Dと停止点2は未完。外枠12,500行まで検証済みから1,743行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし、計算上限変更なし。凍結確定の連絡は未受領。


## 93. A06完了：本体・指定両端・全図式射の自然性

同じ自由区間の零次・一次の生成元計算で鎖評価の後合成自然性を示し、既存のsmart切断射のcycles公式・項同型で境界データを移した。既存 `normalizedChainsTruncationHomEquiv_postcomp` でコチェイン評価へ戻し、閉零次射による内部Homの前後合成を適用した。最後に既存テンソル–Homの始域・標的自然性とパラメータ同型の交換則で、元の図式射の自然性を得た。

A06は一覧の型どおり、本体 `normalizedIntervalHom`、指定された二端の厳密等式、全図式射についての前後合成自然性まで完了。ホモトピーの前後合成は右合成の後に左合成をする括弧を採用し、元の `a ≫ f ≫ b` の型に合わせた。新しいホモトピーを選んでいない。

### 93.1 同じA06の証明分割・前提計算の型

`DiagramTensorHomNaturality` の既存同値の前後合成自然性をA06の前提計算 **3/3** として追加。その他は同じ一覧A06の自然性の証明分割（§14）であり、照合枠は全体3/3のまま。最初の四本は `A : Type u` と `[CommRing A]`、HomotopyIntervalNaturalityではさらに `{C : Type v}` と `[Category.{u} C] [Preadditive C] [Linear A C]` を固定する。最後の二本は `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。

`NormalizedIntervalChainNaturality`

```lean
theorem intervalRawChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalRawChainMap A K x y w hw ≫ q =
      intervalRawChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw'
```

```lean
theorem intervalNormalizedChainMap_postcomp {K L : ChainComplex (ModuleCat.{u} A) ℕ} (q : K ⟶ L)
    (x y : K.X 0) (w : K.X 1) (hw : K.d 1 0 w = y - x)
    (hw' : L.d 1 0 (q.f 1 w) = q.f 0 y - q.f 0 x) :
    intervalNormalizedChainMap A K x y w hw ≫ q =
      intervalNormalizedChainMap A L (q.f 0 x) (q.f 0 y) (q.f 1 w) hw'
```


`NormalizedIntervalTruncationNaturality`

```lean
theorem intervalTruncCycle_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (z : H.X 0) (hz : H.d 0 1 z = 0) (hz' : H'.d 0 1 (q.f 0 z) = 0) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 0 (intervalTruncCycle A H z hz) =
      intervalTruncCycle A H' (q.f 0 z) hz'
```

```lean
theorem intervalTruncEdge_naturality {H H' : CochainComplex (ModuleCat.{u} A) ℤ}
    (q : H ⟶ H') (w : H.X (-1)) :
    (truncLE'Map q (ComplexShape.embeddingUpIntLE 0)).f 1 (intervalTruncEdge A H w) =
      intervalTruncEdge A H' (q.f (-1) w)
```


`NormalizedIntervalCochainNaturality`

```lean
theorem normalizedIntervalCochainMapOfBoundary_postcomp
    {H H' : CochainComplex (ModuleCat.{u} A) ℤ} (q : H ⟶ H')
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x)
    (hx' : H'.d 0 1 (q.f 0 x) = 0) (hy' : H'.d 0 1 (q.f 0 y) = 0)
    (hw' : H'.d (-1) 0 (q.f (-1) w) = q.f 0 y - q.f 0 x) :
    normalizedIntervalCochainMapOfBoundary A H x y hx hy w hw ≫ q =
      normalizedIntervalCochainMapOfBoundary A H' (q.f 0 x) (q.f 0 y) hx' hy'
        (q.f (-1) w) hw'
```


`HomotopyIntervalNaturality`

```lean
def intervalHomPrePost {R R' S S' : CochainComplex C ℤ} (a : R' ⟶ R) (b : S ⟶ S') :
    linearHomComplex A R S ⟶ linearHomComplex A R' S'
```

```lean
theorem intervalHomPrePost_ofHom {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f : R ⟶ S) :
    (intervalHomPrePost A a b).f 0 (Cochain.ofHom f) = Cochain.ofHom (a ≫ f ≫ b)
```

```lean
theorem intervalHomPrePost_ofHomotopy {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    (intervalHomPrePost A a b).f (-1) (-Cochain.ofHomotopy h) =
      -Cochain.ofHomotopy ((h.compRight b).compLeft a)
```

```lean
theorem homotopyIntervalCochainMap_naturality {R R' S S' : CochainComplex C ℤ}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S) (h : Homotopy f g) :
    homotopyIntervalCochainMap A f g h ≫ intervalHomPrePost A a b =
      homotopyIntervalCochainMap A (a ≫ f ≫ b) (a ≫ g ≫ b)
        ((h.compRight b).compLeft a)
```


`DiagramTensorHomNaturality`

```lean
theorem diagramTensorLinearHomEquiv_naturality {R R' S S' : J ⥤ Complex A}
    (T : Complex A) (a : R' ⟶ R) (b : S ⟶ S') (t : R ⊗ (Functor.const J).obj T ⟶ S) :
    diagramTensorLinearHomEquiv R' S' T (((a ▷ (Functor.const J).obj T) ≫ t) ≫ b) =
      diagramTensorLinearHomEquiv R S T t ≫ intervalHomPrePost A ((E).map a) ((E).map b)
```


`NormalizedIntervalHomNaturality`

```lean
def normalizedIntervalHomotopyPrePost {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    Homotopy ((E).map (a ≫ f ≫ b)) ((E).map (a ≫ g ≫ b))
```

```lean
theorem normalizedIntervalHom_naturality {R R' S S' : J ⥤ Complex A}
    (a : R' ⟶ R) (b : S ⟶ S') (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (a ⊗ₘ 𝟙 (freeNegativeChainsDiagram (A := A) ((Functor.const J).obj
      ((SSet.uliftFunctor.{max u v,0}).obj (SSet.stdSimplex.{0}.obj ⦋1⦌))))) ≫
        normalizedIntervalHom f g h ≫ b =
      normalizedIntervalHom (a ≫ f ≫ b) (a ≫ g ≫ b)
        (normalizedIntervalHomotopyPrePost a b f g h)
```

### 93.2 検収

コード **`b86733b2c`**（最初の4本228行）・**`38c1d4b8d`**（最後の2本94行）。個別・結合検査は終了コード0（`/private/tmp/isw2-interval-raw-nat2.log`、`/private/tmp/isw2-trunc-nat2.log`、`/private/tmp/isw2-cochain-interval-nat2.log`、`/private/tmp/isw2-hom-interval-nat2.log`、`/private/tmp/isw2-diagram-interval-nat2.log`、`/private/tmp/isw2-interval-hom-nat3.log`）。鍵付き対象ビルドと一時監査も終了コード0。

| 検収 | 対象ビルド | 累計モジュール | 累計宣言 | ログ |
| --- | --- | --- | --- | --- |
| 鎖・切断・コチェイン自然性 | 2,396 jobs | 176 | 1,815 | `/private/tmp/isw2-build96.log` |
| 内部Hom前後合成 | 2,398 jobs | 177 | 1,826 | `/private/tmp/isw2-build97.log` |
| 元の図式射の自然性（A06完了） | 3,999 jobs | 179 | 1,831 | `/private/tmp/isw2-build98.log` |

すべて標準三公理のみ。累計 **179モジュール・11,079行・1,831宣言**。一時監査 `/private/tmp/AuditISW2G10HundredSeventyNine.lean`、対象一覧 `/private/tmp/isw2-g10-hundredseventynine-modules.txt`。上の6本を登録対象に追加する。共有鍵は返却済み。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし、計算上限変更なし。凍結確定の連絡は未受領。

### 93.3 次の一覧項目A07への接続と残り

A07では、全余単体方向の指定ホモトピーを各単体次数で評価し、今の `normalizedIntervalHom` を使う。入力のn単体（`G.obj n ⟶ Q`）と区間のn単体（`⦋n⦌ ⟶ ⦋1⦌`）に対し、指定余作用 `δ.app n`、同じ正規化単体射、区間評価、入力射を順に合成する。単体作用素との可換性にはδの自然性とA06の前後合成自然性、両端にはA05の指定単位則とA06の両端等式を使う。二重図式のホモトピーを次数ごとに独立に選ばない。元の全パラメータの自然な成分を評価して使う。

A07以降、B・C・Dの各まとまり、停止点2は未完。本節はA06完了の途中報告であり、停止点2の検収報告ではない。検証済みは外枠12,500行まで残り1,421行。範囲・型は弱めていない。


## 94. A07完了：指定余作用から全単体Homのホモトピーへ

11-13のユーザー承認で3b-2の外枠は **14,500行**。一覧と§14の補題の数え方は維持する。23時の調整役の連絡で、今回のB3はmainだけの凍結と確定し、この枝は作業・コミットを続けてよい。今夜は対象ビルドと新規モジュールの小さな一時監査だけを実行し、mainは取り込まない。B4は追って指定される改名コマンドを待つ。

A07は、同じ二重図式のホモトピーを積添字へ戻してA06へ入れ、指定区間評価を全余単体方向で自然な射にした。指定余作用、区間の単体、区間評価、入力射を合成した区間射を定義し、その単体自然性・両端を示した。点ごとにホモトピーを選んでいない。

### 94.1 A07の証明分割と前提計算の型

`StandardParameterConstant.standardParameter_constant` だけをA07の前提計算 **1/3** とする（既存の増大写像・端点の余単位則）。残りは一覧A07の同じ構成と端点・単体自然性の証明分割（§14）。照合枠は3/3のまま。FrameIntervalHom中の局所`hm`は既存 `Functor.map_id` の適用であり、新しい法則の証明ではない：

```lean
have hm (W : SimplicialObject (ModuleCat A)) :
    AlgebraicTopology.NormalizedMooreComplex.map (𝟙 W) = 𝟙 _ :=
  (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map_id W
```

型の略記：FrameParameterEvaluation・Endpoints・UnderlyingMapでは `{C : Type u} [Category.{v} C] [MonoidalCategory C]`、`{F G P : SimplexCategory ⥤ C}`。FrameIntervalHom・FrameHomHomotopyは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`D := J ⥤ Complex A`、`P := liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J`、`I := P.obj ⦋1⦌`。EEは§73の二重図式交換関手。UncurriedDiagramHomotopyのE₁・E₂は同ファイルと既存CurriedDiagramHomotopyの定義どおり。すべてのAに`[CommRing A]`を固定。

`UncurriedDiagramHomotopy`

```lean
def uncurriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c} (f g : F ⟶ G)
    (h : Homotopy ((E₂).map f) ((E₂).map g)) :
    Homotopy ((E₁).map (Functor.uncurry.map f)) ((E₁).map (Functor.uncurry.map g))
```


`FrameIntervalHom`

```lean
def frameIntervalHom {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    F ⊗ (Functor.const SimplexCategory).obj I ⟶ G
```

```lean
theorem frameIntervalHom_endpoints {F G : SimplexCategory ⥤ D} (f g : F ⟶ G)
    (h : Homotopy ((EE).map f) ((EE).map g)) :
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ frameIntervalHom f g h = f ∧
    (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ frameIntervalHom f g h = g
```


`FrameParameterEvaluation`

```lean
def frameParameterEvaluation (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) : F.obj n ⟶ G.obj n
```

```lean
theorem frameParameterEvaluation_naturality (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    {m n : SimplexCategory} (s : m ⟶ n) (t : n ⟶ ⦋1⦌) :
    F.map s ≫ frameParameterEvaluation δ k n t =
      frameParameterEvaluation δ k m (s ≫ t) ≫ G.map s
```


`FrameParameterEndpoints`

```lean
theorem frameParameterEvaluation_endpoint
    (δ : F ⟶ F ⊗ P) (α : P ⟶ 𝟙_ (SimplexCategory ⥤ C))
    (hδ : δ ≫ (𝟙 F ⊗ₘ α) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (e : 𝟙_ C ⟶ P.obj ⦋1⦌) (f : F ⟶ G)
    (hk : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map e) ≫ k = f)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) (ht : P.map t = α.app n ≫ e) :
    frameParameterEvaluation δ k n t = f.app n
```


`FrameHomotopyUnderlyingMap`

```lean
def frameHomotopyUnderlyingMap (δ : F ⟶ F ⊗ P)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G) (Q : C) :
    (cosimplicialHom G).obj Q ⊗ (SSet.stdSimplex.{v}.obj ⦋1⦌) ⟶ (cosimplicialHom F).obj Q
```


`StandardParameterConstant`

```lean
theorem standardParameter_constant (n : SimplexCategory) (ε : Fin 2) :
    (liftedStandardSimplexParameter J ⋙ freeNegativeChainsDiagramFunctor A J).map
      (SimplexCategory.const n ⦋1⦌ ε) =
    (standardParameterAugmentation A J).app n ≫ normalizedIntervalEndpoint A J ε
```


`FrameHomHomotopy`

```lean
def frameHomHomotopyOfInterval {F G : SimplexCategory ⥤ D}
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj ((P).obj ⦋1⦌) ⟶ G)
    (f g : F ⟶ G)
    (hk0 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 0)) ≫ k = f)
    (hk1 : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map
      (normalizedIntervalEndpoint A J 1)) ≫ k = g) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)
```

```lean
def frameHomHomotopyOfChainHomotopy (F G : SimplexCategory ⥤ D)
    (δ : F ⟶ F ⊗ P)
    (hδ : δ ≫ (𝟙 F ⊗ₘ standardParameterAugmentation A J) ≫ (ρ_ F).hom = 𝟙 F)
    (f g : F ⟶ G) (h : Homotopy ((EE).map f) ((EE).map g)) (Q : D) :
    SSet.Homotopy ((cosimplicialHomMap f).app Q) ((cosimplicialHomMap g).app Q)
```

### 94.2 検収と登録対象

コード **`9f1fb0f95`**。新規7本339行（UncurriedDiagramHomotopy 34、FrameIntervalHom 73、FrameParameterEvaluation 38、FrameParameterEndpoints 41、FrameHomotopyUnderlyingMap 34、StandardParameterConstant 48、FrameHomHomotopy 71）。個別・結合検査は最終的に終了コード0（`/private/tmp/isw2-frame-interval9.log`、`/private/tmp/isw2-frame-hom-map2.log`、`/private/tmp/isw2-standard-parameter-constant2.log`、`/private/tmp/isw2-frame-hom-homotopy3.log`）。途中の対象ビルド99・100の失敗は、定数区間の恒等射と端点計算の結合順序を明示して修正した。計算上限は上げていない。

鍵付きの最終対象ビルドは **4,008 jobs、終了コード0**（`/private/tmp/isw2-build101.log`）。今夜の連絡に合わせ、監査は新規7モジュールだけ：**58宣言、標準三公理のみ**（`/private/tmp/AuditISW2G10A07.lean`）。既検収179本・1,831宣言と合わせた累計は **186モジュール・11,418行・1,889宣言**。累計対象一覧 `/private/tmp/isw2-g10-hundredeightysix-modules.txt`。上記7本を登録対象へ追加する（共通1本・DiagramComparison6本）。共有鍵は返却済み。

新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り3,082行。A07完了、A08は既存の二つのEZホモトピーをA07へ入れる個別検査が通っており、A09の同じ指定射の同値性へ接続中。A08以降は本節の検収数に未算入。B・C・Dと停止点2は未完。


## 95. A08・A09完了：指定比較自身に同じshuffleの逆を与えた

A08は既存の全余単体AW・shuffleの両合成のEZホモトピーに、A05の指定余作用とA07を適用した。A09は既存 `freeTensorDiagramHomIso`・`freeProductSectionsHomIso` の間でこの二つの実ホモトピーを前後合成し、`normalizedWeightSectionMap` 自身の逆を既存 `normalizedWeightSectionReverse` として与えた。別の同値は選ばず、Kan性や模型圏の仮定も追加していない。

### 95.1 一覧A08・A09の型

A08は `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`W : J ⥤ SSet.{max u v}`、`φ : simplicialRingCoefficient.{max u v} →+* A`、`P := standardParameterForCoefficients A J`。A09は既存入口と同じ `A : Type u`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`、`Q : J ⥤ CochainComplex (ModuleCat A) ℤ`、`φ : simplicialRingCoefficient.{u} →+* A`。いずれも`[CommRing A]`を固定。追加の前提計算枠・照合枠は使っていない。

`FreeProductHomComparisonHomotopies`

```lean
def freeProductHomComparison_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomReverse A W P φ).app Q ≫ (freeProductHomComparison A W P φ).app Q)
      (𝟙 _)
```

```lean
def freeProductHomReverse_homotopy (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    SSet.Homotopy
      ((freeProductHomComparison A W P φ).app Q ≫ (freeProductHomReverse A W P φ).app Q)
      (𝟙 _)
```


`NormalizedWeightSectionEquivalence`

```lean
theorem normalizedWeightSectionMap_equivalence :
    IsSimplicialHomotopyEquivalence (normalizedWeightSectionMap A W Q φ)
```

### 95.2 検収と残り

コード **`c3000d7aa`**。新規2本84行（FreeProductHomComparisonHomotopies 45、NormalizedWeightSectionEquivalence 39）。個別・結合検査 `/private/tmp/isw2-product-hom-homotopies2.log`・`/private/tmp/isw2-weight-section-equiv1.log` は終了コード0。鍵付き対象ビルド **4,400 jobs、終了コード0**、新規2モジュールだけの一時監査 **11宣言、標準三公理のみ**（`/private/tmp/isw2-build102.log`、`/private/tmp/AuditISW2G10A08A09.lean`）。既検収と合わせた累計は **188モジュール・11,502行・1,900宣言**。一覧 `/private/tmp/isw2-g10-hundredeightyeight-modules.txt`。上記2本を登録対象へ追加。鍵は返却済み。

A10の自由テンソルHom同型の標的自然性の型が既定の200,000 heartbeatsに当たったため、既存の図式Homの標的射を明示する `DiagramHomTargetMap` とその転置の特殊化に分けて検査している。計算上限を上げず、既存宣言も変えていない。これは同じ一覧A10の構成・自然性の分割であり、新しい数学のまとまりを足していない。A10以降・B/C/D・停止点2は未完。外枠14,500行まで検証済みから2,998行。新公理・sorryなし、⑤a・入口・公式監査の変更なし。


## 96. A10完了：指定比較の標的の全図式射自然性

Γ側では同じ図式Homの標的射を明示し、切断側では元の`weightedSectionsFunctor`の射を使った。自由テンソルHom同型・自由積Hom同型・指定AW比較の三つの自然性を合成し、一覧A10の等式を閉じた。型推論の200,000 heartbeats超過は、基礎圏と宇宙引数の明示、図式Hom標的射の分離、同型の逆の自然性の相殺による証明で解消した。計算上限は変更していない。

### 96.1 A10の型と前提計算枠

`NormalizedTensorHomTargetNaturality`をA10の前提計算 **1/3**、`ProductSectionsTargetNaturality`の自然性を **2/3** とする。後者の標準単体Hom同型の自然性は、同じ積Hom同型の証明の分割。`DiagramHomTargetMap`と転置の特殊化は同じA10のHmapの構成と既存A06の自然性の特殊化であり、新しい数学ではない。照合枠は全体3/3のまま。

最初のファイルは `A : Type (max u v)`、`J : Type v`、`[SmallCategory J]`、`E := functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。他は既存入口と同じ `A : Type u`、`J : Type u`、`[SmallCategory J]`、`W : J ⥤ SSet.{u}`（すべて`[CommRing A]`）。最後の型では `φ : simplicialRingCoefficient.{u} →+* A`。

`DiagramHomTargetMap`

```lean
def diagramHomTargetMap (P : J ⥤ Complex A) {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P) ((E).obj Q')
```

```lean
theorem diagramTensorLinearHomEquiv_postcomp (P : J ⥤ Complex A)
    {Q Q' : J ⥤ Complex A} (T : Complex A) (t : P ⊗ (Functor.const J).obj T ⟶ Q)
    (f : Q ⟶ Q') :
    diagramTensorLinearHomEquiv P Q' T (t ≫ f) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomTargetMap P f
```


`NormalizedTensorHomTargetNaturality`

```lean
theorem freeTensorDiagramHomIso_target_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (cosimplicialHom (freeTensorFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeTensorDiagramHomIso.{u,u} A Q' W).hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f)
```


`ProductSectionsTargetNaturality`

```lean
theorem liftedStandardSimplexHomIso_naturality {Z Z' : SSet.{u}} (f : Z ⟶ Z') :
    (cosimplicialHom (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})).map f ≫
      (liftedStandardSimplexHomIso Z').hom = (liftedStandardSimplexHomIso Z).hom ≫ f
```

```lean
theorem freeProductSectionsHomIso_target_naturality (W : J ⥤ SSet.{u})
    {Q Q' : J ⥤ CochainComplex (ModuleCat A) ℤ} (f : Q ⟶ Q') :
    (cosimplicialHom (freeProductFrame A W (liftedStandardSimplexParameter J))).map f ≫
      (freeProductSectionsHomIso A W Q').hom =
    (freeProductSectionsHomIso A W Q).hom ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (CochainComplex (ModuleCat A) ℤ) SSet.{u}).obj
        (SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) |>.map f)
```


`NormalizedWeightSectionNaturality`

```lean
theorem normalizedWeightSectionMap_naturality {Q Q' : J ⥤ Complex A} (f : Q ⟶ Q') :
    (truncatedDoldKanFunctor A).map
      (diagramHomTargetMap.{u,u} (freeNegativeChainsDiagram (A := A) W) f) ≫
        normalizedWeightSectionMap A W Q' φ =
    normalizedWeightSectionMap A W Q φ ≫ (weightedSectionsFunctor W).map
      ((Functor.whiskeringRight J (Complex A) SSet.{u}).obj (truncatedDoldKanFunctor A) |>.map f)
```

### 96.2 検収と登録対象

コード **`36b42f9be`**。新規4本174行（DiagramHomTargetMap 32、NormalizedTensorHomTargetNaturality 44、ProductSectionsTargetNaturality 47、NormalizedWeightSectionNaturality 51）。最終結合個別検査 `/private/tmp/isw2-weight-section-nat5.log` は終了コード0。鍵付き対象ビルド **2,655 jobs、終了コード0**、新規4モジュールだけの一時監査 **10宣言、標準三公理のみ**（`/private/tmp/isw2-build103.log`、`/private/tmp/AuditISW2G10A10.lean`）。上記4本を登録対象に追加。累計対象一覧 `/private/tmp/isw2-g10-hundredninetytwo-modules.txt`。

既検収分と合わせて **192モジュール・11,676行・1,910宣言**。外枠14,500行まで残り2,824行。共有鍵は返却済み。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。今夜の監査は新規分だけで、root・大きい累計監査は流していない。A10まで完了、A11以降・B/C/D・停止点2は未完。

### 96.3 次の一覧A11への接続（紙）

A11の切断側は既存 `WeightedRestriction.weightedSectionsPre`（実名前空間はKerodon.LimitsAndColimits.HomotopyLimitsAndColimits）を使う。`weightedSectionsUncurry_comp_pre`が元のパラメータ付き自然変換の前合成との等式を持ち、任意の重みの射に使える。Γ側は `intervalHomPrePost` の後側を恒等射に固定し、前側に元の自由鎖図式の射を入れる。型の具体化は以下（`N := freeNegativeChainsDiagramFunctor A J`、Eは上記交換関手）：

```lean
-- §73 A11。まだ未実装・未検収。
theorem normalizedWeightSectionMap_weight_naturality
    {W W' : J ⥤ SSet.{u}} (w : W' ⟶ W) :
    (truncatedDoldKanFunctor A).map
      (intervalHomPrePost A ((E).map ((N).map w)) (𝟙 ((E).obj Q))) ≫
        normalizedWeightSectionMap A W' Q φ =
      normalizedWeightSectionMap A W Q φ ≫ weightedSectionsPre w (Q ⋙ truncatedDoldKanFunctor A)
```

自由テンソル側には既存 `diagramTensorLinearHomEquiv_naturality` の前側の特殊化、自由積側には元の随伴Homの始域自然性と`weightedSectionsUncurry_comp_pre`、中間のAWには既存 `freeProductDiagramAW_naturality` を使う。別の重みの置換や別のHom同値を選ばず、元の二同型の始域自然性を照合してA10と同じ合成で結ぶ方針。


## 97. A11完了：元の重みの全射に対する指定比較の自然性

今回のgoal「Dまで進めてください」はactiveのまま。前回のgoal turnはA07〜A10の検証済みコード・報告を保存した進捗で、今回は枝がクリーンで`f594ede20`まであることを確かめてA11へ進んだ。

同じ自由鎖関手に重み射を入れ、自由積・自由テンソルのframe射と指定AWの可換性を束ねた。Γ側は同じ図式Homの前合成、切断側は既存`weightedSectionsPre`。自由テンソルHomには既存の転置の始域自然性とパラメータ同型のテンソル交換則、自由積Homには元の随伴Hom回収式と`weightedSectionsUncurry_comp_pre`を使い、一覧A11の指定射自身の等式を閉じた。

### 97.1 一覧A11の分割の型と枠

`NormalizedTensorHomSourceNaturality`はA11の前提計算 **1/3**。`WeightedAdjunctionSourceNaturality`と`ProductSectionsSourceNaturality`は同じ自由積Hom同型の自然性を段に分けたA11の前提計算 **2/3**。他は一覧A11のHpre・frame射の構成と主張の証明分割。照合枠は全体3/3のまま。既存宣言・計算上限は変えていない。

略記：Eは `functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)`。DiagramHomSourceMapは`A : Type (max u v)`・`J : Type v`・`[SmallCategory J]`。FreeFrameWeightMapsは`A : Type u`・`J : Type v`・`[Category.{w} J]`・`N := freeNegativeChainsDiagramFunctor A J`。他は既存入口と同じ`A : Type u`・`J : Type u`・`[SmallCategory J]`。すべての係数環は`[CommRing A]`。

`DiagramHomSourceMap`

```lean
def diagramHomSourceMap {P P' : J ⥤ Complex A} (a : P' ⟶ P) (Q : J ⥤ Complex A) :
    linearHomComplex A ((E).obj P) ((E).obj Q) ⟶ linearHomComplex A ((E).obj P') ((E).obj Q)
```

```lean
theorem diagramTensorLinearHomEquiv_source {P P' Q : J ⥤ Complex A}
    (T : Complex A) (a : P' ⟶ P) (t : P ⊗ (Functor.const J).obj T ⟶ Q) :
    diagramTensorLinearHomEquiv P' Q T ((a ▷ (Functor.const J).obj T) ≫ t) =
      diagramTensorLinearHomEquiv P Q T t ≫ diagramHomSourceMap a Q
```


`FreeFrameWeightMaps`

```lean
def freeProductFrameWeightMap : freeProductFrame A W' P ⟶ freeProductFrame A W P
```

```lean
def freeTensorFrameWeightMap : freeTensorFrame A W' P ⟶ freeTensorFrame A W P
```

```lean
theorem freeProductFrameAW_weight_naturality (φ : simplicialRingCoefficient.{u} →+* A) :
    freeProductFrameWeightMap A a P ≫ freeProductFrameAW A W P φ =
      freeProductFrameAW A W' P φ ≫ freeTensorFrameWeightMap A a P
```


`NormalizedTensorHomSourceNaturality`

```lean
theorem freeTensorDiagramHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) :
    (cosimplicialHomMap (freeTensorFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeTensorDiagramHomIso.{u,u} A Q W').hom =
    (freeTensorDiagramHomIso.{u,u} A Q W).hom ≫ (truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q)
```


`WeightedAdjunctionSourceNaturality`

```lean
theorem weightedSectionsAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (H : J ⥤ SSet.{u}) (s : W ⊗ (Functor.const J).obj K ⟶ H) :
    (weightedSectionsAdjunction W').homEquiv K H ((w ▷ (Functor.const J).obj K) ≫ s) =
      (weightedSectionsAdjunction W).homEquiv K H s ≫ weightedSectionsPre w H
```

```lean
theorem freeWeightedAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)
    (s : (freeNegativeChainsDiagramFunctor A J).obj (W ⊗ (Functor.const J).obj K) ⟶ Q) :
    ((weightedSectionsAdjunction W').comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q
      ((freeNegativeChainsDiagramFunctor A J).map (w ▷ (Functor.const J).obj K) ≫ s) =
    ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q s ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A)
```


`ProductSectionsSourceNaturality`

```lean
theorem freeProductSectionsHomIso_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ) :
    (cosimplicialHomMap (freeProductFrameWeightMap A w (liftedStandardSimplexParameter J))).app Q ≫
      (freeProductSectionsHomIso A W' Q).hom =
    (freeProductSectionsHomIso A W Q).hom ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A)
```


`NormalizedWeightSectionSourceNaturality`

```lean
theorem normalizedWeightSectionMap_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) :
    (truncatedDoldKanFunctor A).map
      (diagramHomSourceMap.{u,u} ((freeNegativeChainsDiagramFunctor A J).map w) Q) ≫
        normalizedWeightSectionMap A W' Q φ =
    normalizedWeightSectionMap A W Q φ ≫ weightedSectionsPre w (Q ⋙ truncatedDoldKanFunctor A)
```

### 97.2 検収・登録対象

コード **`08a27be94`**。新規6本284行（DiagramHomSourceMap 29、FreeFrameWeightMaps 45、NormalizedTensorHomSourceNaturality 56、WeightedAdjunctionSourceNaturality 48、ProductSectionsSourceNaturality 49、NormalizedWeightSectionSourceNaturality 57）。個別・結合検査は終了コード0（`/private/tmp/isw2-tensor-hom-source-nat3.log`、`/private/tmp/isw2-weighted-adj-source2.log`、`/private/tmp/isw2-weight-section-source-nat2.log`）。

鍵付き対象ビルドは、最初の4本 **2,657 jobs**・最後の2本 **2,659 jobs**、どちらも終了コード0（`/private/tmp/isw2-build104.log`・`/private/tmp/isw2-build105.log`）。監査は新規分だけで、前者 **24宣言**・後者 **6宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A11Parts.lean`・`/private/tmp/AuditISW2G10A11Finish.lean`）。共有鍵は返却済み。

累計 **198モジュール・11,960行・1,940宣言**。対象一覧 `/private/tmp/isw2-g10-hundredninetyeight-modules.txt`。上記6本を登録対象へ追加する。外枠14,500行まで残り2,540行。新公理・sorryなし、⑤a・入口・公式監査の変更なし。mainのB3凍結中なので取り込みは行っていない。

### 97.3 報告の型引用の訂正と次

§91〜96の五つの型引用（intervalTruncCycle_value、normalizedIntervalHom、normalizedIntervalHom_naturality、freeTensorDiagramHomIso_target_naturality、normalizedWeightSectionMap_naturality）が名前付き引数の`:=`で途中までになっていたため、既検収ソースの完全な型に直した。Leanの宣言には変更がない。抽出は括弧の深さを見て宣言本体の`:=`と区別する方法にした。

A11まで完了、A12・B/C/D・停止点2は未完。A12では、既存の `normalizedBousfieldKanHom` の二重反対圏の添字と、`liftedClosedDiagram` のAsSmall添字を、同じ`smallBousfieldKanWeightDown`とULift・反転の指定射で接続する。`smallBousfieldKanWeightDown`の現在の宣言は射だけを供給しているため、可逆性の既存道具と同じ射の逆の構成を確認中。これは§73 A12に初めから含めた持ち上げの照合であり、別の同値へ置換しない。


## 98. A12の途中：指定AsSmall重みとHom添字の可逆な移送

既存 `smallBousfieldKanWeightDown` の順射は変更せず、over圏の構造射と全射を元の`AsSmall.up`で持ち上げる逆を構成した。up・downの二合成は厳密な関手の等式で、全次数で同じoverの射列を保つ。その指定重み同型の前合成を、既存`weightedSectionsPre`の二逆則で切断の同型へ送る部品を作った。

同時に、図式複体のAsSmall.downによる制限で、元の線形Hom複体を同じコチェイン成分のup・downで移す同型を作った。微分との可換性は既存`δ_map`による。対象ごとの任意のHom同値は選ばない。

### 98.1 同じ一覧A12の証明分割の型

下記は§73 A12に含めたAsSmall・ULiftとΓ Homの照合の分割であり、一覧外の新しい数学のまとまりではない。前提計算枠・照合枠は追加で使っていない。SmallOverLift・SmallBousfieldKanWeightIsoは`J : Type`・`[SmallCategory J]`、WeightedRestrictionIsoは`I : Type u`・`[SmallCategory I]`・`{W W' : I ⥤ SSet.{u}}`、AsSmallLinearHomは`A : Type u`・`[CommRing A]`・`J : Type`・`[SmallCategory J]`。

`SmallOverLift`

```lean
def smallOverLift (j : AsSmall.{u} J) : Over ((AsSmall.down : AsSmall.{u} J ⥤ J).obj j) ⥤ Over j
```

```lean
theorem smallOverLift_down (j : AsSmall.{u} J) :
    smallOverLift j ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) = 𝟭 _
```

```lean
theorem smallOverDown_lift (j : AsSmall.{u} J) :
    Over.post (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ smallOverLift j = 𝟭 _
```


`SmallBousfieldKanWeightIso`

```lean
instance smallBousfieldKanWeightDown_isIso : IsIso (smallBousfieldKanWeightDown.{u} J)
```

```lean
def smallBousfieldKanWeightIso :
    bousfieldKanWeight (AsSmall.{u} J) ≅
      (AsSmall.down : AsSmall.{u} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{u,0}
```

```lean
theorem smallBousfieldKanWeightIso_hom :
    (smallBousfieldKanWeightIso.{u} J).hom = smallBousfieldKanWeightDown J
```


`WeightedRestrictionIso`

```lean
def weightedSectionsWeightIso (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    weightedSections W' H ≅ weightedSections W H
```

```lean
theorem weightedSectionsWeightIso_hom (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    (weightedSectionsWeightIso e H).hom = weightedSectionsPre e.hom H
```


`AsSmallLinearHom`

```lean
def asSmallComplexRestriction :
    CochainComplex (J ⥤ ModuleCat.{u} A) ℤ ⥤ CochainComplex (AsSmall.{u} J ⥤ ModuleCat.{u} A) ℤ
```

```lean
def asSmallHomCochainEquiv (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) (n : ℤ) :
    Cochain P Q n ≃ₗ[A]
      Cochain ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q) n
```

```lean
def asSmallLinearHomIso (P Q : CochainComplex (J ⥤ ModuleCat.{u} A) ℤ) :
    linearHomComplex A P Q ≅
      linearHomComplex A ((asSmallComplexRestriction A J).obj P) ((asSmallComplexRestriction A J).obj Q)
```

### 98.2 検収と登録対象

コード **`ae5bd1dcf`**（最初の3本103行）・**`7e8efb382`**（AsSmallLinearHom 59行）。個別・結合検査 `/private/tmp/isw2-small-bk-weight-iso2.log`、`/private/tmp/isw2-weighted-restriction-iso1.log`、`/private/tmp/isw2-as-small-linear-hom2.log` は終了コード0。計算上限は上げていない。

鍵付き対象ビルドは **1,686 jobs**・**1,841 jobs**、いずれも終了コード0（`/private/tmp/isw2-build106.log`・`/private/tmp/isw2-build107.log`）。監査は新規分だけ：最初の3本 **13宣言**、最後の1本 **13宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A12Lift.lean`・`/private/tmp/AuditISW2G10A12Hom.lean`）。鍵は返却済み。

累計 **202モジュール・12,122行・1,966宣言**。対象一覧 `/private/tmp/isw2-g10-twohundredtwo-modules.txt`。上記4本を登録対象に追加する（DiagramComparison3本、KerodonのHomotopyLimitsAndColimits1本）。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り2,378行。mainのB3凍結中なので、枝内でのコミットだけを行った。

### 98.3 A12の残りとDまでの継続

A12の指定射・同値性はまだ閉じていない。次は同じ正規化BK Homの係数重みを、既存 `normalizedLinearWeightFreeIso`、`normalizedMooreMapIso`、`pointwiseExtendIso`・`mapExtendIso` の指定射で、AsSmall添字の自由鎖図式へ接続する。そのΓ Homへ既存A09の指定比較を適用し、元のMoore反転と単体集合のop、今回の指定重み同型、既存の実Γ Hom図式の同型で `liftedClosedDiagram` の反転BK Holimへ戻す。射の等式と同値性は別々に検証する。

その後に一覧Bの指定豊穣合成との等式・native切断の族・極限性、Cの標準脚とD(A)への輸送、Dの全図式射・指定錐の族・離散加群入口が残る。goal「Dまで進めてください」はactiveのままで、A11や今回の部品を完了条件に置き換えていない。停止点2の完了報告ではない。


## 99. A12の途中：元の正規化BK係数重みを自由鎖図式へ接続

前回のgoal turnはA11とAsSmallの検証済みコード・報告を保存した進捗。今回の開始時に枝がクリーンで`ffbea99f3`まであることを確認し、§98.3の係数重みの接続を進めた。goal「Dまで進めてください」はactiveのまま。

既存のMoore比較を、加法関手間の自然変換に対して自然な形にした。その指定比較を評価関手で束ね、図式圏の正規化と点ごとの正規化の全自然同型を作った。既存 `pointwiseExtendIso`、`functorComplexExchangeCounitIso`、`normalizedLinearWeightFreeIso` と合成し、係数余積による正規化線形重みから同じ自由負鎖図式への指定同型を得た。最後に元の二重反対圏上の `normalizedBousfieldKanWeight` へ特殊化した。

### 99.1 同じA12の分割と前提計算の型

`normalizedMooreMapHom_functor_naturality`をA12の前提計算 **1/3** とする（既存正規化比較の自然性法則）。他は一覧A12の係数重み照合の同じ証明分割。照合枠は全体3/3のまま。既存宣言と計算上限は変更していない。

最初の二本はHomologicalAlgebra名前空間。NormalizedMooreMapFunctorNaturalityでは`{C D : Type*}`、両Category構造とAbelian構造を固定する。PointwiseNormalizedMooreでは`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`。LinearWeightFreeDiagramIsoはDiagramComparison名前空間、`A : Type u`・`[CommRing A]`・`J : Type v`・`[Category.{w} J]`・`W : J ⥤ SSet.{0}`。最後の特殊化はHA.DerivedCategoryModels.CosimplicialTotalization名前空間。

`NormalizedMooreMapFunctorNaturality`

```lean
theorem normalizedMooreMapHom_functor_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex α (.down ℕ)).app ((normalizedMooreComplex C).obj X) ≫
      normalizedMooreMapHom G X =
    normalizedMooreMapHom F X ≫ (normalizedMooreComplex D).map (Functor.whiskerLeft X α)
```


`PointwiseNormalizedMoore`

```lean
def diagramMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ
```

```lean
def pointwiseMooreFunctor : SimplicialObject (J ⥤ C) ⥤ J ⥤ ChainComplex C ℕ
```

```lean
def pointwiseMooreIso : diagramMooreFunctor J C ≅ pointwiseMooreFunctor J C
```


`LinearWeightFreeDiagramIso`

```lean
def freeLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```

```lean
def normalizedLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```


`NormalizedBKFreeWeight`

```lean
def normalizedBousfieldKanWeightFreeDiagramIso (A : Type u) [CommRing A] :
    (normalizedBousfieldKanWeight (A := A)).extend ComplexShape.embeddingDownNat ≅
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) (bousfieldKanSetWeight.flip ⋙ SSet.uliftFunctor.{u,0}))
```

### 99.2 検収と登録対象

コード **`ff3dbf01a`**（共通2本70行）・**`1e434f076`**（係数重みの2本68行）。個別・結合検査 `/private/tmp/isw2-moore-functor-nat1.log`、`/private/tmp/isw2-pointwise-moore1.log`、`/private/tmp/isw2-bk-free-weight1.log` は終了コード0。

鍵付き対象ビルドは **1,339 jobs**・**2,783 jobs**、どちらも終了コード0（`/private/tmp/isw2-build108.log`・`/private/tmp/isw2-build109.log`）。監査は新規分だけで各 **8宣言**、すべて標準三公理のみ（`/private/tmp/AuditISW2G10A12Moore.lean`・`/private/tmp/AuditISW2G10A12FreeWeight.lean`）。共有鍵は返却済み。

累計 **206モジュール・12,260行・1,982宣言**。対象一覧 `/private/tmp/isw2-g10-twohundredsix-modules.txt`。上記4本を登録対象へ追加する（共通HomologicalAlgebra2本、DiagramComparison1本、HA/CosimplicialTotalization1本）。新公理・sorryなし、既存宣言・⑤a・入口・公式監査の変更なし。外枠14,500行まで残り2,240行。mainのB3凍結中なので、枝だけで作業・コミットした。

### 99.3 残りと次の接続

今回閉じたのは元の正規化BK係数重みから自由鎖図式への同型であり、A12の反転BK比較と同値性そのものではない。次は、この指定同型と§98の`asSmallLinearHomIso`をHom複体へ運び、元のMoore反転ホモトピー同値、AsSmall・ULift・重み付き切断の指定射を通して、A09の同じ比較を反転BK Holimへ戻す。`normalizedMooreReverse`は既存の**鎖ホモトピー同値の順射**であり、根拠なく厳密な同型として扱わない。全射と同値性を元の指定比較についてそれぞれ検査する。

その後のB（指定豊穣合成・native切断の族・極限性）、C（標準脚・D(A)輸送）、D（全図式射・指定錐族・離散加群入口）は未完。目標の完了条件はDまでの検証済み実装のままで、停止点2の完了報告ではない。


## 100. A12の途中：元のΓ Homから同じAsSmall重み付き切断への指定AW比較

mainのみB3で凍結し、各枝のコミットは続けてよいという11-13 23時の連絡に従った。mainの取り込みや入口の登録は行っていない。

元の係数重みの同型を線形Homの始域へ運び、AsSmall制限の指定同型と合成した。そのΓ像の後にA09の元のAW比較を合成し、その同じ比較自身の単体的ホモトピー同値性を示した。これは反転前の接続であり、A12の最終射の代用ではない。

### 100.1 型と数え方

`linearHomSourceIso`はA12の前提計算2/3（既存の前合成の両単位則）。前提計算1/3は§99の正規化自然性。残りはA12の同じ証明の分割。照合枠は全体3/3のまま。LinearHomSourceIsoでは`A : Type u`・`[CommRing A]`・`{C : Type v}`・`[Category.{u} C] [Preadditive C] [Linear A C]`。HAの二本では`A : Type u`・`[CommRing A]`。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearHomSourceIso`

```lean
def linearHomSourceIso {P P' : CochainComplex C ℤ} (e : P ≅ P') (Q : CochainComplex C ℤ) :
    linearHomComplex A P Q ≅ linearHomComplex A P' Q
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallHom`

```lean
def normalizedBKSmallWeight (_A : Type u) : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}
```

```lean
def normalizedBKSmallDiagram (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ Complex A
```

```lean
def normalizedBKSmallHomIso (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHom X ≅
      linearHomComplex A
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (freeNegativeChainsDiagram (A := A) (normalizedBKSmallWeight A)))
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (normalizedBKSmallDiagram A X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallSections`

```lean
def normalizedBKCoefficientMap : ULift.{u} ℤ →+* A
```

```lean
def normalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      weightedSections (normalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A)
```

```lean
theorem normalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKSmallSectionsMap A X)
```

### 100.2 検収と残り

コード **`f181b0655`**（上記3本142行）。鍵付き対象ビルド **4,585 jobs**、新規分のみの小さな監査 **16宣言（4・7・5）・標準三公理のみ**。終了コード0、ログ`/private/tmp/isw2-build110.log`、監査`/private/tmp/AuditISW2G10A12SmallSections.lean`。共有鍵は返却済み。個別結合検査のログもエラーなし。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。

累計 **209モジュール・12,402行・1,998宣言**。一覧`/private/tmp/isw2-g10-twohundrednine-modules.txt`。外枠14,500行まで残り2,098行。登録対象は100.1の3本。累計の監査数は既検証分と今回の新規分の合計であり、大きな一括監査を流したという意味ではない。

A12のMoore反転、二重反対圏と元の添字の移送、実豊穣Homとの指定射の照合は残っている。その後のB・C・Dも未完。目標「Dまで進めてください」は継続する。


## 101. A12完了：指定Moore反転から元の反転豊穣HomのBK endへ

A12の指定型`normalizedBKReflectedSectionsMap`と、その同じ射自身の単体的ホモトピー同値性を閉じた。元のMoore反転の鎖ホモトピー同値を、既存の反変endと指定end–Hom同型で運ぶ。反転側にも同じ自由重みHom同型とA09の実AW比較を適用し、既存の反転end同型、down・二重反対・upによる指定添字移送、元のsmallBousfieldKanWeightDown、既存の実Γ Hom全自然同型を順に合成した。

反転前の切断空間のKan性は仮定にせず、同じ反転end同型と元のBK endの既存Kan性から得た。これにより既存のopのホモトピー同値性と合成則を、その必要なKan性を持つ形で使用した。

### 101.1 同じ一覧A12の証明分割の型

以下6本はA12に初めから含めた反転・AsSmall・ULift・Γ Homの接続の証明分割である。前提計算枠は§100の2/3、照合枠は全体3/3のまま。新しい数学のまとまりは追加していない。`A : Type u`・`[CommRing A]`を固定する（SmallBKIndexSectionsは環に依存せず、同じ小添字の制限を使う）。以下はすべてHA.DerivedCategoryModels.CosimplicialTotalization名前空間。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKHom`

```lean
def reflectedNormalizedBKWeight : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A) ℕ
```

```lean
def reflectedNormalizedBKHom (X : CosimplicialObject (Complex A)) : Complex A
```

```lean
def normalizedBKReverseHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv (normalizedBousfieldKanHom X) (reflectedNormalizedBKHom X)
```

```lean
def normalizedBKReverseSpaceMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      (truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X)
```

```lean
theorem normalizedBKReverseSpaceMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKReverseSpaceMap X)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallHom`

```lean
def reflectedNormalizedBKSmallWeight (_A : Type u) : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}
```

```lean
def reflectedNormalizedBKSmallHomIso (X : CosimplicialObject (Complex A)) :
    reflectedNormalizedBKHom X ≅
      linearHomComplex A
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (freeNegativeChainsDiagram (A := A) (reflectedNormalizedBKSmallWeight A)))
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (normalizedBKSmallDiagram A X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallSections`

```lean
def reflectedNormalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X) ⟶
      weightedSections (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A)
```

```lean
theorem reflectedNormalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (reflectedNormalizedBKSmallSectionsMap A X)
```

```lean
def normalizedBKSmallReflectedComparison (X : CosimplicialObject (Complex A)) :
    ((truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      weightedSections (normalizedBKSmallWeight A)
        ((normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SmallBKIndexSections`

```lean
def smallBKIndexToDouble : AsSmall.{u} SimplexCategory ⥤ AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)
```

```lean
def smallBKIndexFromDouble : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ AsSmall.{u} SimplexCategory
```

```lean
def smallBKIndexSectionsMap {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) :
    weightedSections W H ⟶ weightedSections (F ⋙ W) (F ⋙ H)
```

```lean
theorem smallBKIndexSectionsMap_π {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) (j : J) :
    smallBKIndexSectionsMap F W H ≫ weightedSectionsπ (F ⋙ W) (F ⋙ H) j =
      weightedSectionsπ W H (F.obj j)
```

```lean
def smallBKIndexSectionsIso (W H : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u}) :
    weightedSections W H ≅
      weightedSections (smallBKIndexToDouble ⋙ W) (smallBKIndexToDouble ⋙ H)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKOriginalSections`

```lean
def normalizedBKOriginalSectionsIso (X : CosimplicialObject (Complex A)) :
    weightedSections (normalizedBKSmallWeight A)
      ((normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```

```lean
def normalizedBKOriginalSectionsMap (X : CosimplicialObject (Complex A)) :
    ((truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
```

```lean
theorem normalizedBKOriginalSectionsMap_factor (X : CosimplicialObject (Complex A)) :
    normalizedBKOriginalSectionsMap A X =
      SSet.opFunctor.map (normalizedBKReverseSpaceMap X ≫
        reflectedNormalizedBKSmallSectionsMap A X) ≫
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
        (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) ≪≫
          normalizedBKOriginalSectionsIso A X).hom
```

```lean
instance reflectedNormalizedBKSmallSections_kan (X : CosimplicialObject (Complex A)) :
    SSet.KanComplex (weightedSections (reflectedNormalizedBKSmallWeight A)
      (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A))
```

```lean
theorem normalizedBKOriginalSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKOriginalSectionsMap A X)
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReflectedSections`

```lean
def normalizedBKReflectedHomDiagramIso (X : CosimplicialObject (Complex A)) (T : Complex A) :
    (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙
      (homDiagramFunctor T).obj X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
    simplicialHomDiagram (liftedClosedDiagram X) (ForgetEnrichment.of (Complex A) T) ⋙
      SSet.opFunctor
```

```lean
def normalizedBKReflectedSectionsMap (X : CosimplicialObject (Complex A)) (T : Complex A) :
    ((truncatedDoldKanFunctor A).obj
      (normalizedBousfieldKanHom ((homDiagramFunctor T).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) T) ⋙ SSet.opFunctor)
```

```lean
theorem normalizedBKReflectedSectionsMap_equivalence (X : CosimplicialObject (Complex A))
    (T : Complex A) : IsSimplicialHomotopyEquivalence (normalizedBKReflectedSectionsMap X T)
```

### 101.2 検収・コミット・登録

コード **`5fd7f9b7b`**（反転Hom・自由重みHomの2本88行）、**`296461f29`**（反転切断の1本56行）、**`214d21cc5`**（添字移送とA12最終比較の3本235行）。個別・結合検査`/private/tmp/isw2-reflected-bk-hom2.log`、`/private/tmp/isw2-reflected-bk-small1.log`、`/private/tmp/isw2-bk-enriched-sections4.log`は終了コード0。添字の逆則と最終の合成照合は、引数の指定と同じ等式の証明分割で軽くし、計算上限は変更していない。

鍵付き対象ビルド：

| ログ | jobs | 新規分だけの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build111.log` | 4,535 | 15宣言（9・6） | 0 |
| `/private/tmp/isw2-build112.log` | 4,733 | 5宣言 | 0 |
| `/private/tmp/isw2-build113.log` | 6,474 | 31宣言（8・10・13） | 0 |

いずれも標準三公理のみ。監査ファイルは`AuditISW2G10A12Reverse.lean`・`AuditISW2G10A12ReflectedSections.lean`・`AuditISW2G10A12Final.lean`（すべて`/private/tmp/`）。鍵は返却済み。今回の379行を加え、累計 **215モジュール・12,781行・2,049宣言**。対象一覧`/private/tmp/isw2-g10-twohundredfifteen-modules.txt`。外枠14,500行まで残り1,719行。累計監査数は検証済みの各新規分の合計。大きな監査・rootビルドは行っていない。既存宣言・⑤a・入口・公式監査の変更、新公理、sorryなし。

### 101.3 残り

A01〜A12まで完了。B01のHom–Tot比較との接続、B02の指定豊穣合成との厳密な等式、B03〜B08のnative切断・極限性、Cの標準脚とD(A)輸送、Dの全図式射・指定錐の族・離散加群入口はまだ残る。とくに今回の反転Homは反変endの移送から定めたので、元の錐代表へのMoore反転の前合成との等式はB02の中で検証する。A12の同値性をB02の厳密な等式の代わりにしない。目標「Dまで進めてください」は継続し、停止点2の完了報告ではない。


## 102. B01：実Hom同型・Hom–Tot比較・A12の指定合成

B01の`gammaReflectedBKComparison`を元の型で構成した。任意の試験対象`x : ClosedCategory A (Complex A)`を`ForgetEnrichment.to`で元の複体へ戻し、既存の実Hom同型、同じ`normalizedBousfieldKanHomSpaceComparison`、A12の指定射を合成する。この合成射自身のホモトピー同値性も証明した。これはB03の証明分割であり、実際の豊穣合成`reflectedWeightedHomComparison`とのB02の等式はまだ主張していない。

### 102.1 型

`A : Type u`・`[CommRing A]`。名前空間はHA.DerivedCategoryModels.CosimplicialTotalization。登録対象は`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.GammaReflectedBKComparison`。前提計算枠・照合枠を新たに使っていない。

```lean
def gammaReflectedBKComparison (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)
```

```lean
theorem gammaReflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (gammaReflectedBKComparison X x)
```

### 102.2 検収と残り

コード **`bd740ce50`**（1本60行）。個別検査`/private/tmp/isw2-gamma-bk-comparison3.log`は終了コード0。鍵付き対象ビルド **6,475 jobs**、新規分だけの小さな監査 **13宣言・標準三公理のみ**、終了コード0（`/private/tmp/isw2-build114.log`、`/private/tmp/AuditISW2G10B01.lean`）。鍵は返却済み。

累計 **216モジュール・12,841行・2,062宣言**、一覧`/private/tmp/isw2-g10-twohundredsixteen-modules.txt`。外枠14,500行まで残り1,659行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。mainのB3凍結中のため枝だけでコミットした。

A01〜A12・B01が完了。B02の厳密な等式、B03の実豊穣合成自身の同値性、B04〜B08の指定native切断の族と極限性、CとDは未完。次は、元の錐代表へのMoore反転の前合成と、今回の反変end移送の一致を含め、A09の指定AW比較を実豊穣合成へ照合する。単なる同値な空間への置換はしない。今回の区切りは停止点2ではなく、目標「Dまで進めてください」はactiveのまま。
