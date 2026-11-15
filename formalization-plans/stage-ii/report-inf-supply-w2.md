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


## 103. B02の途中：endで運んだ反転は元の錐代表の前合成そのもの

前回のB01までの検証済みコードから続行した。B02の最初の厳密な照合として、指定符号付きend–Hom同型の重みに関する自然性を示した。既存の積射影の自然性と、負次数への零延長の指定行同型で計算し、同じMoore反転を運んだ順射が元の反転鎖射による前合成に等しいことを得た。閉零次元に適用し、元の恒等射から作った錐代表が反転後も既存の`reflectedBousfieldKanConeRepresentative`そのものへ移ることも確認した。

### 103.1 型と数え方

`weightEndHomIso_source_naturality`をB02の前提計算1/3（既存構成の自然性）とする。その行での公式と、HAの三つの反転の等式は同じ証明の分割。照合枠は全体3/3のまま。計算上限は変更していない。最初のファイルでは`A : Type u`・`[CommRing A]`・`{J : Type}`・`[SmallCategory J]`・`{K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat A) ℕ}`。二本目は`{A : Type u}`・`[CommRing A]`。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomSourceNaturality`

```lean
theorem extendedChainHomRows_precomp (f : K ⟶ L)
    (H : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ) (q : ℤ)
    (z : Cochain (L.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows K H q
      ((intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
        (𝟙 H)).f q z) n = f.f n ≫ extendedChainHomRows L H q z n
```

```lean
theorem weightEndHomIso_source_naturality (f : K ⟶ L) (X : Jᵒᵖ ⥤ Complex A) :
    (linearWeightEndTotalFunctor A X).map f.op ≫ (weightEndHomIso A K X).hom =
      (weightEndHomIso A L X).hom ≫
        intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
          (𝟙 ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).obj X))
```


登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReversePrecomposition`

```lean
theorem normalizedBKReverseHomotopyEquiv_hom (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv X).hom =
      intervalHomPrePost A
        (HomologicalComplex.extendMap
          (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
          ComplexShape.embeddingDownNat)
        (𝟙 ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram X)))
```

```lean
theorem normalizedBKReverseHomotopyEquiv_ofHom (X : CosimplicialObject (Complex A))
    (f : normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat ⟶
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) :
    (normalizedBKReverseHomotopyEquiv X).hom.f 0 (Cochain.ofHom f) =
      Cochain.ofHom (HomologicalComplex.extendMap
        (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ f)
```

```lean
theorem normalizedBKReverseHomotopyEquiv_coneRepresentative (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv
      ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)).hom.f 0
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) =
      Cochain.ofHom (reflectedBousfieldKanConeRepresentative X)
```

### 103.2 検収と残り

コード **`eb59a7350`**（2本125行）。個別検査`/private/tmp/isw2-weight-end-source4.log`・`/private/tmp/isw2-bk-reverse-precomp4.log`は終了コード0。最初の対象ビルド`/private/tmp/isw2-build115.log`は閉零次元の一般的な書き換えの型照合が200,000 heartbeatsに達して失敗。計算上限を上げず、その部分を各次数の直接計算へ分けた。修正後の鍵付き対象ビルド`/private/tmp/isw2-build116.log`は **4,379 jobs・終了コード0**、新規分のみの監査は **5宣言（2・3）・標準三公理のみ**（`/private/tmp/AuditISW2G10B02Reverse.lean`）。共有鍵は返却済み。

累計 **218モジュール・12,966行・2,067宣言**。一覧`/private/tmp/isw2-g10-twohundredeighteen-modules.txt`。外枠14,500行まで残り1,534行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。

B02はまだ未完。今回閉じたのは反転の前合成との厳密な一致であり、残る指定AW比較・Hom–Tot比較と全単体の実豊穣合成との照合を省略しない。B03の元の比較自身の同値性、B04〜B08、C、Dも未完。Dまでの目標はactiveのまま。


## 104. B02の途中：元の線形重みHom同値の後合成自然性

指定錐代表から作る単体写像を後合成へ移すため、既存`normalizedLinearWeightHomEquiv`の標的複体射に関する自然性を示した。既存の延長・切断・Dold–KanのHom同値の後合成則を、同じ二変数の生成元評価へ移すもので、元の指定写像と全単体を保持する。

### 104.1 型と枠

HomologicalAlgebra名前空間。`A : Type u`・`[CommRing A]`・`{D : Type v}`・`[Category.{w} D]`。B02の前提計算 **2/3**（既存構成の後合成自然性）とする。1/3は§103のend–Hom同型の重みに関する自然性。照合枠は全体3/3のまま。

```lean
theorem normalizedLinearWeightHomEquiv_postcomp (W : SimplicialObject (D ⥤ Type))
    {H H' : CochainComplex (D ⥤ ModuleCat A) ℤ}
    (f : ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat ⟶ H) (g : H ⟶ H') :
    normalizedLinearWeightHomEquiv A W H' (f ≫ g) =
      normalizedLinearWeightHomEquiv A W H f ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (D ⥤ ModuleCat A) ℕ ⥤
            SimplicialObject (D ⥤ ModuleCat A)).map
              (truncLE'Map g (ComplexShape.embeddingUpIntLE 0)))
          ((Functor.whiskeringRight D (ModuleCat A) (Type u)).obj (forget (ModuleCat A)))
```

### 104.2 検収・登録対象・残り

コード **`be8447d78`**（32行）。個別検査`/private/tmp/isw2-normalized-weight-target1.log`は終了コード0。鍵付き対象ビルド **1,801 jobs**、新規分のみの監査 **1宣言・標準三公理のみ**、終了コード0（`/private/tmp/isw2-build117.log`、`/private/tmp/AuditISW2G10B02Target.lean`）。共有鍵は返却済み。登録対象は **`SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHomNaturality`**。

累計 **219モジュール・12,998行・2,068宣言**。対象一覧`/private/tmp/isw2-g10-twohundrednineteen-modules.txt`。外枠14,500行まで残り1,502行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。

B02は未完。A09の指定AW比較、既存Hom–Tot比較と、元の標準成分模型の実豊穣合成が全単体で一致する照合が残る。今回の自然性だけでその等式を済ませたとは扱わない。B03〜B08・C・Dも未完で、目標「Dまで進めてください」はactiveのまま。次の区切りはこの全単体の照合である。


## 105. B02の途中：指定正規化・Γ比較と元のDold–Kan Hom随伴の両立

前回は反転代表と後合成自然性を検証・保存できているので、進捗ありとして続けた。B02の全単体の照合に必要な係数移送について、元の正規化比較`normalizedMooreMapIso`と元のΓ余積比較`gammaMapIso`が同じDold–KanのHom随伴を保つことを示した。任意の加法関手を許すので、図式の評価関手にも適用できる。任意の同値を新たに選ぶ証明ではない。

まず、指定余単位の逆射にMoore包含を後合成すると、同じKaroubi模型の`N₁Γ₀.inv`の実鎖射になると示した。Karoubi単位の自然性と正規化射影で打ち消す。次にΓの恒等添字の和因子が既に正規化されている既存補題を使い、二比較の係数移送の計算を余積包含の自然性に短縮した。Moore包含で戻して指定余単位の両立を得て、最後に元のHom随伴の公式と正規化比較の自然性を適用した。

### 105.1 型と数え方

`doldKanHomEquiv_map`をB02の前提計算 **3/3**（既存構成の係数移送則）とする。余単位の具体式、Karoubi模型での同じ式、余単位の順射・逆射の式は、その同じ証明の分割。1/3は§103、2/3は§104。照合枠は全体3/3のまま。これ以上の独立した前提計算や照合を黙って追加しない。同じ一覧B02の証明分割は§14に従う。

すべてHomologicalAlgebra名前空間。`{C : Type u}`・`[Category.{v} C] [Abelian C]`を固定し、係数移送の二本ではさらに`{D : Type u'}`・`[Category.{v'} D] [Abelian D]`を固定する。

登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanCounitMooreInclusion`

```lean
theorem doldKanCounitInv_inclusion (K : ChainComplex C ℕ) :
    (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      inclusionOfMooreComplexMap ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ _).obj K) =
      (N₁Γ₀.inv.app K).f
```


登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanCoefficientCounit`

```lean
theorem doldKanKaroubiCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (N₁Γ₀.inv.app K).f ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app (Abelian.DoldKan.Γ.obj K) =
    (N₁Γ₀.inv.app ((F.mapHomologicalComplex (.down ℕ)).obj K)).f ≫
      (alternatingFaceMapComplex D).map (gammaMapIso F K).hom
```

```lean
theorem doldKanCounitInv_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.inv.app K) ≫
      normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) =
    Abelian.DoldKan.equivalence.counitIso.inv.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).hom
```


登録対象：`SerrePositivity.HomologicalAlgebra.DoldKanHomCoefficient`

```lean
theorem doldKanCounit_map (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    normalizedMooreMapHom F (Abelian.DoldKan.Γ.obj K) ≫
      (normalizedMooreComplex D).map (gammaMapIso F K).inv ≫
      Abelian.DoldKan.equivalence.counitIso.hom.app
        ((F.mapHomologicalComplex (.down ℕ)).obj K) =
    (F.mapHomologicalComplex (.down ℕ)).map (Abelian.DoldKan.equivalence.counitIso.hom.app K)
```

```lean
theorem doldKanHomEquiv_map (F : C ⥤ D) [F.Additive]
    (W : SimplicialObject C) (K : ChainComplex C ℕ)
    (f : (normalizedMooreComplex C).obj W ⟶ K) :
    (Abelian.DoldKan.equivalence : SimplicialObject D ≌ ChainComplex D ℕ).toAdjunction.homEquiv
      (W ⋙ F) ((F.mapHomologicalComplex (.down ℕ)).obj K)
      ((normalizedMooreMapIso F W).inv ≫ (F.mapHomologicalComplex (.down ℕ)).map f) ≫
        (gammaMapIso F K).hom =
    Functor.whiskerRight
      ((Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W K f) F
```

### 105.2 検収・コミット・登録

コード **`62ad24b46`**（最初の2本119行）・**`0d3a623aa`**（Hom随伴の1本72行）。個別・結合検査`/private/tmp/isw2-dk-counit-inclusion1.log`、`/private/tmp/isw2-dk-coeff-counit15.log`、`/private/tmp/isw2-dk-hom-coeff5.log`は終了コード0。途中で大きな型のまま余単位を直接書き換える検査が200,000 heartbeatsに達したが、計算上限を上げず、Karoubi模型の同じ射の計算と包含による照合を分離した。

| 検査 | jobs | 新規分のみの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build118.log` | 1,369 | 10宣言（6・4） | 0 |
| `/private/tmp/isw2-build119.log` | 1,370 | 3宣言 | 0 |

監査は`/private/tmp/AuditISW2G10B02Counit.lean`・`/private/tmp/AuditISW2G10B02HomCoefficient.lean`、どちらも標準三公理のみ。共有鍵は返却済み。新規3本191行を加え、累計 **222モジュール・13,189行・2,081宣言**。対象一覧`/private/tmp/isw2-g10-twohundredtwentytwo-modules.txt`。外枠14,500行まで残り1,311行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は105.1の3本。大きな監査は行っていない。

### 105.3 残り

B02は未完。今回の一般の加法関手に関する式を評価関手に適用し、指定零延長・切断のmateと合わせて、元の図式圏の線形重みHom同値を点ごとの自由鎖随伴へ照合する。その後にA09の指定AW比較と元の実豊穣合成の全単体の照合を閉じる。今回のHom随伴の係数両立だけで、AW合成の一致を証明したとは扱わない。B03〜B08・C・Dも未完。目標「Dまで進めてください」はactiveのままで、停止点2の完了報告ではない。


## 106. B02の途中：実切断同型と元の零延長Hom随伴の両立

前回の指定正規化・Γ比較とHom随伴の両立から続行した。既存の`pointwiseTruncationIso`自身が、図式圏での零延長Hom随伴を点ごとの同じ随伴へ移すことを示した。右随伴の一意性から定めた元のmateの単位則を使い、図式側の調整したHom随伴を元の随伴と指定成分交換の余単位で表す。点ごとの随伴を成分交換から戻すと同じ随伴になることを各成分で確認し、最終の実切断同型についての式を閉じた。

### 106.1 型と数え方

下記4本はB02の係数移送則（§105の前提計算3/3）を元の指定切断mateへ接続する同じ証明の分割。前提計算枠はB02で3/3、照合枠は全体3/3のまま。新たな独立した前提計算や照合を追加していない。名前空間はHomologicalAlgebra、`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`を固定する。

```lean
theorem truncationExchangeMate_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    (diagramTruncationAdjunction J C).homEquiv K X f ≫
        (truncationExchangeMate J C).hom.app X =
      (pointwiseTruncationAdjunction J C).homEquiv K X f
```

```lean
theorem diagramTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    (diagramTruncationAdjunction J C).homEquiv K
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f) =
    (negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f ≫
      ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C)).map
        ((functorComplexExchangeCounitIso J C (.up ℤ)).inv.app H)
```

```lean
theorem pointwiseTruncationHomEquiv_exchange
    (K : ChainComplex (J ⥤ C) ℕ) (X : J ⥤ CochainComplex C ℤ)
    (f : ((complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).obj K) ⟶ X) :
    complexOfFunctorsToFunctorToComplex.map
        ((pointwiseTruncationAdjunction J C).homEquiv K X f) ≫
      (functorComplexExchangeUnitIso J C (.down ℕ)).inv.app
        (X ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor C) =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) X f
```

```lean
theorem pointwiseTruncationIso_homEquiv
    (K : ChainComplex (J ⥤ C) ℕ) (H : CochainComplex (J ⥤ C) ℤ)
    (f : K.extend ComplexShape.embeddingDownNat ⟶ H) :
    complexOfFunctorsToFunctorToComplex.map
        ((negativeExtendTruncationAdjunction (J ⥤ C)).homEquiv K H f) ≫
      (pointwiseTruncationIso J C).hom.app H =
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C)).homEquiv
      (complexOfFunctorsToFunctorToComplex.obj K) (complexOfFunctorsToFunctorToComplex.obj H)
      ((pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app K ≫
        complexOfFunctorsToFunctorToComplex.map f)
```

### 106.2 検収・登録対象・残り

コード **`ed24d69de`**（新規1本97行）。個別検査`/private/tmp/isw2-point-trunc-hom6.log`は終了コード0。鍵付き対象ビルド **1,536 jobs**・終了コード0、新規分だけの監査 **6宣言・標準三公理のみ**（`/private/tmp/isw2-build120.log`、`/private/tmp/AuditISW2G10B02PointwiseTruncation.lean`）。共有鍵は返却済み。

登録対象は **`SerrePositivity.HomologicalAlgebra.PointwiseTruncationHomEquiv`**。累計 **223モジュール・13,286行・2,087宣言**、一覧`/private/tmp/isw2-g10-twohundredtwentythree-modules.txt`。外枠14,500行まで残り1,214行。新公理・sorryなし、計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査は行っていない。

B02はまだ未完。次は§105の`doldKanHomEquiv_map`を評価関手へ適用し、今回の実切断Hom両立と組み合わせて、元の正規化重みHom同値の点ごとの式にする。その後の指定AW比較と実豊穣合成の全単体の照合、B03〜B08・C・Dは残る。目標「Dまで進めてください」はactiveのまま。


## 107. B02の途中：元の正規化重みHomの全図式移送と指定余積生成元の照合

前回の実切断Hom両立は検証・保存できているので、進捗ありとして続行した。指定された正規化比較とΓ比較を、評価関手に適用した係数移送則でつなぎ、図式圏のDold–Kan Hom同値を点ごとの同じ随伴へ移す全自然変換の等式を得た。

さらに、元の`normalizedWeightHomEquiv`が元の零延長随伴とDold–Kan随伴の合成であることを明示し、指定零延長・実切断・Γの比較を通して、点ごとの同じ二随伴に一致させた。最後に、指定余積による正規化Homと自由正規化鎖の同じ随伴を、各単体で元の余積包含の1の像が同じ自由生成元となる既存公式を直接適用して照合した。

### 107.1 型と数え方

以下はB02の同じ係数移送の証明分割。前提計算枠は§105のB02 3/3、照合枠は全体3/3のまま。余積生成元には既存`copowerUnitFreeHom_generator`を証明の中で直接使い、新たな独立した前提計算の宣言を足していない。

最初の2本はHomologicalAlgebra名前空間、`J : Type*`・`[Category* J]`・`C : Type*`・`[Category* C] [Abelian C]`。`normalizedWeightHomEquiv_asAdjunction`はJに依存しない。最後の1本はDiagramComparison名前空間、`A : Type u`・`[CommRing A]`。

登録対象：`SerrePositivity.HomologicalAlgebra.PointwiseDoldKanHomEquiv`

```lean
theorem pointwiseDoldKanHomEquiv
    (W : SimplicialObject (J ⥤ C)) (K : ChainComplex (J ⥤ C) ℕ)
    (f : (normalizedMooreComplex (J ⥤ C)).obj W ⟶ K) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map
        ((Abelian.DoldKan.equivalence : SimplicialObject (J ⥤ C) ≌
          ChainComplex (J ⥤ C) ℕ).toAdjunction.homEquiv W K f) ≫
      (pointwiseGammaIso J C).inv.app K =
    (Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj K)
      ((pointwiseMooreIso J C).inv.app W ≫ complexOfFunctorsToFunctorToComplex.map f)
```


登録対象：`SerrePositivity.HomologicalAlgebra.PointwiseNormalizedWeightHom`

```lean
theorem normalizedWeightHomEquiv_asAdjunction
    (W : SimplicialObject C) (H : CochainComplex C ℤ)
    (f : ((normalizedMooreComplex C).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    normalizedWeightHomEquiv W H f =
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction.homEquiv
        W (H.truncLE' (ComplexShape.embeddingUpIntLE 0))
        ((negativeExtendTruncationAdjunction C).homEquiv _ H f)
```

```lean
theorem pointwiseTruncationGammaIso_hom (H : CochainComplex (J ⥤ C) ℤ) :
    (pointwiseTruncationGammaIso J C).hom.app H =
      (pointwiseGammaIso J C).inv.app (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) ≫
        ((Functor.whiskeringRight J (ChainComplex C ℕ) (SimplicialObject C)).obj
          Abelian.DoldKan.Γ).map ((pointwiseTruncationIso J C).hom.app H)
```

```lean
theorem pointwiseNormalizedWeightHomEquiv
    (W : SimplicialObject (J ⥤ C)) (H : CochainComplex (J ⥤ C) ℤ)
    (f : ((normalizedMooreComplex (J ⥤ C)).obj W).extend ComplexShape.embeddingDownNat ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J C).map (normalizedWeightHomEquiv W H f) ≫
      (pointwiseTruncationGammaIso J C).hom.app H =
    ((Adjunction.whiskerRight J
      (Abelian.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ).toAdjunction).comp
        (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C))).homEquiv
      W.flip (complexOfFunctorsToFunctorToComplex.obj H)
      (((Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
          (ComplexShape.embeddingDownNat.extendFunctor C)).map
        ((pointwiseMooreIso J C).inv.app W) ≫
        (pointwiseExtendIso J C ComplexShape.embeddingDownNat).inv.app
          ((normalizedMooreComplex (J ⥤ C)).obj W) ≫
        complexOfFunctorsToFunctorToComplex.map f)
```


登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CopowerNormalizedFreeHom`

```lean
theorem copowerNormalizedHomEquiv_free (W : SSet.{0}) (H : Complex A)
    (f : ((normalizedMooreComplex (ModuleCat A)).obj
      (W ⋙ uliftFunctor.{u,0} ⋙ ModuleCat.free A)).extend
          ComplexShape.embeddingDownNat ⟶ H) :
    copowerUnitDiagramHomEquiv A W
      ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ _).obj
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))
      (normalizedWeightHomEquiv (W ⋙ copowerFunctor (ModuleCat.of A A)) H
        (HomologicalComplex.extendMap
          ((normalizedMooreComplex (ModuleCat A)).map
            (Functor.isoWhiskerLeft W (copowerUnitFreeNatIso A)).hom)
          ComplexShape.embeddingDownNat ≫ f)) =
    (freeNegativeChainsAdjunction A).homEquiv (W ⋙ uliftFunctor.{u,0}) H f
```

### 107.2 検収・登録・コミット

コード **`4fce28163`**（共通2本105行）・**`51a9f6ae2`**（DiagramComparison1本55行）。個別・結合検査`/private/tmp/isw2-point-dk-hom5.log`、`/private/tmp/isw2-point-normalized-hom4.log`、`/private/tmp/isw2-copower-normalized-free3.log`は終了コード0。型の照合は随伴の単位・後合成の成分を明示し、元の比較射のまま行った。計算上限は変更していない。

| 鍵付き対象ビルド | jobs | 新規分のみの監査 | 終了 |
| --- | ---: | --- | --- |
| `/private/tmp/isw2-build121.log` | 1,641 | 9宣言（3・6） | 0 |
| `/private/tmp/isw2-build122.log` | 2,588 | 2宣言 | 0 |

監査は`/private/tmp/AuditISW2G10B02PointwiseHom.lean`・`/private/tmp/AuditISW2G10B02CopowerHom.lean`、どちらも標準三公理のみ。共有鍵は返却済み。累計 **226モジュール・13,446行・2,098宣言**、一覧`/private/tmp/isw2-g10-twohundredtwentysix-modules.txt`。外枠14,500行まで残り1,054行。新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は107.1の3本。大きな監査は行っていない。

### 107.3 残り

B02は未完。今回閉じた全図式の移送と各単体の指定余積生成元の照合を、既存の`normalizedLinearWeightDiagramIso`の元の射と組み合わせて、図式圏の元の線形重みHom同値をA09の同じ自由鎖随伴へつなぐ。その後の指定AW比較・Hom–Tot比較と実豊穣合成の全単体の照合、B03〜B08・C・Dは残る。今回の一般の随伴の式だけでAW合成の等式を済ませたとは扱わない。目標「Dまで進めてください」はactiveのまま。


## 108. B02の途中：A12の元の比較射と図式自由鎖Hom随伴の厳密な照合

前回の全図式の正規化Hom移送と指定生成元の照合から続行した。まず`freeLinearWeightDiagramIso`の元の順射を評価へ戻した式を示した。成分交換の単位・余単位を打ち消すと、指定零延長比較・Moore比較・交換単位が残る。次に正規化・零延長比較の元の自然性を使い、係数余積から自由加群への指定同型も含め、`normalizedLinearWeightDiagramIso`の元の順射を点ごとの同じ係数移送に同定した。

この評価公式と前回の全図式のHom両立を合成し、元の図式圏の`normalizedLinearWeightHomEquiv`が、A12の同じ比較射の後で、A09が使う同じ`freeNegativeChainsDiagramAdjunction`のHom同値に一致する式を全単体で閉じた。指定余積生成元を各単体で評価しており、比較射を別の同値で置換していない。

### 108.1 型と数え方

下記はB02の同じ係数移送の証明分割。前提計算枠は§105のB02 3/3、照合枠は全体3/3のまま。新しい独立した前提計算・照合の宣言を追加していない。名前空間はDiagramComparison、`A : Type u`・`[CommRing A]`・`{J : Type v}`・`[Category.{w} J]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramEvaluation`

```lean
theorem freeLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    complexOfFunctorsToFunctorToComplex.map (freeLinearWeightDiagramIso A W).hom =
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).hom.app
        ((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)) ≫
      Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).hom.app
        (freeLinearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```

```lean
theorem normalizedLinearWeightDiagramIso_hom_evaluation (W : J ⥤ SSet.{0}) :
    Functor.whiskerRight ((pointwiseMooreIso J (ModuleCat A)).inv.app
        (linearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).inv.app
        ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)) ≫
      complexOfFunctorsToFunctorToComplex.map (normalizedLinearWeightDiagramIso A W).hom =
    Functor.whiskerRight ((pointwiseMooreFunctor J (ModuleCat A)).map
        (linearizedSimplicialWeightFreeIso A W.flip).hom)
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ≫
      (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
        (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}))
```


登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeHomComparison`

```lean
theorem normalizedLinearWeightHomEquiv_freeDiagram (W : J ⥤ SSet.{0})
    (H : CochainComplex (J ⥤ ModuleCat A) ℤ)
    (f : (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J (Type u)).map
        (normalizedLinearWeightHomEquiv A W.flip H
          ((normalizedLinearWeightDiagramIso A W).hom ≫ f)) ≫
      Functor.whiskerRight ((pointwiseTruncationGammaIso J (ModuleCat A)).hom.app H)
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
          (forget (ModuleCat A))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map f)
```

### 108.2 検収と登録

コード **`bbcc4861c`**（2本172行）。個別・結合検査`/private/tmp/isw2-linear-weight-evaluation3.log`・`/private/tmp/isw2-linear-free-hom-comparison3.log`は終了コード0。型の照合は元の随伴の合成単位・後合成・指定生成元評価を明示し、計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build123.log`は **2,594 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02LinearHom.lean`は **9宣言（3・6）・標準三公理のみ**。共有鍵は返却済み。累計 **228モジュール・13,618行・2,107宣言**。直前の226本の一覧を実ファイルから数え直し、13,446行であることも確認した。新しい一覧は`/private/tmp/isw2-g10-twohundredtwentyeight-modules.txt`。外枠14,500行まで残り882行。

新公理・sorryなし、既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は108.1の2本。大きな監査は行っていない。

### 108.3 残り

B02はまだ未完。元の線形重みHomからA09の自由鎖随伴への射の照合は今回閉じた。残るのは、同じAW比較・Hom–Tot比較と、標準成分模型で定めた実豊穣合成の全単体での一致。その後にB03〜B08の指定native切断の族と極限性、Cの標準脚とD(A)輸送、Dの全図式射・指定錐の族・離散加群入口が残る。今回の随伴の照合をAW合成の一致の代用にしない。目標「Dまで進めてください」はactiveのまま。


## 109. B02の途中：実Moore射影を通した標準Hom最上位成分の回収

B3はmainだけの凍結との11-13 23時の連絡に従い、mainを取り込まず、作業枝で検証とコミットを続けた。対象ビルドと新規分だけの監査に限り、大きな監査は実行していない。

### 109.1 部分補題と型

B02の実豊穣合成の成分照合のうち、標準HomをMoore正規化する段を分割した。最上位成分の評価が退化上で消えることを既存の非単射引き戻し公式から示し、Mathlibの既存の退化消滅判定で実射影PInftyを消去する。さらに既存の正規化包含との可換式により、指定射影から正規化最上位評価への合成が元の生の評価になることを示した。射影や比較射を作り直していない。

これはB02の同じ成分照合の証明分割（§14）であり、新しい独立した前提計算や照合の枠を追加しない。前提計算枠はB02 3/3、照合枠は全体3/3のまま。名前空間はDiagramComparison。`{R : Type u}`・`[CommRing R]`・`{D : Type v}`・`[DGCategory R D]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomTopProjection`

```lean
theorem standardTopEval_degeneraciesVanish (x y : D) (n : ℕ) :
    DegeneraciesVanish (n := n) (X := standardModule (R := R) x y)
      (ModuleCat.ofHom (standardTopEval (R := R) x y n))
```

```lean
theorem standardTopEval_PInfty (x y : D) (n : ℕ) :
    (PInfty (X := standardModule (R := R) x y)).f n ≫
      ModuleCat.ofHom (standardTopEval (R := R) x y n) =
    ModuleCat.ofHom (standardTopEval (R := R) x y n)
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomNormalizedTop`

```lean
theorem standardMooreTopMap_inclusion (x y : D) (n : ℕ) :
    standardMooreTopMap (R := R) x y n =
      (inclusionOfMooreComplexMap (standardModule (R := R) x y)).f (n + 1) ≫
        ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

```lean
theorem standardMooreTopMap_projection (x y : D) (n : ℕ) :
    (DoldKan.PInftyToNormalizedMooreComplex (standardModule (R := R) x y)).f (n + 1) ≫
      standardMooreTopMap (R := R) x y n =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

### 109.2 検収と登録

コード **`a3182379a`**（2本117行）。個別検査`/private/tmp/isw2-top-projection5.log`・`/private/tmp/isw2-normalized-top2.log`は終了コード0。零次数の退化消滅の定義は非公開なので、既存の判定定理を使って処理した。計算上限は変更していない。

最終ソースの鍵付き対象ビルド`/private/tmp/isw2-build125.log`は **3,764 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02NormalizedTop.lean`は **4宣言（2・2）・標準三公理のみ**。共有鍵は返却済み。累計 **230モジュール・13,735行・2,111宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirty-modules.txt`。外枠14,500行まで残り765行。

新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は109.1の2本。

### 109.3 残り

B02は未完。今回の式はMoore正規化前後の実評価の照合であり、AW比較・Hom–Tot比較と実豊穣合成の全単体の一致を済ませたとは扱わない。そこから指定native切断の族・極限性（B03〜B08）、標準脚・D(A)輸送（C）、全図式射・指定錐の族・離散加群入口（D）へ進む。停止点2の完了報告ではない。


## 110. B02の途中：指定DK同型と実AW合成の全正次数の評価

### 110.1 同じ成分照合の分割と型

同じ随伴Homの逆写像の式と、Moore射影の既存の自然性を複体の射として合成した。指定DK同型の像を、同じΓのMoore射影・同じ余単位・同じ正次数項同型で評価すると、元の標準Homの最上位成分を回収する。零次数だけの公式で済ませず、任意の正次数を扱う。

これを実標準合成`standardAW`へ適用し、DK像の実評価が元の`awTerm`の全切断点の和となる式を閉じた。標準合成を別のΓ上の演算に置き換えていない。B02の同じ成分照合の証明分割（§14）であり、独立した前提計算・照合の枠を追加しない。B02前提計算3/3・全体照合3/3はそのまま。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardDoldKanProjectedEvaluation`。
名前空間はDiagramComparison、`{R : Type u}`・`[CommRing R]`、後二本は`{D : Type v}`・`[DGCategory R D]`。

```lean
theorem doldKanHomEquiv_projected_eval (W : SimplicialObject (ModuleCat R))
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : (normalizedMooreComplex (ModuleCat R)).obj W ⟶ K) (n : ℕ) :
    (((Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat R) ≌
      ChainComplex (ModuleCat R) ℕ).toAdjunction.homEquiv W K) f).app (Opposite.op ⦋n⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n =
    (DoldKan.PInftyToNormalizedMooreComplex W).f n ≫ f.f n
```

```lean
theorem standardDoldKanModuleIso_positive_projected_eval (x y : D) (n : ℕ) :
    (standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x y)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x y)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x y n).hom =
    ModuleCat.ofHom (standardTopEval (R := R) x y (n + 1))
```

```lean
theorem standardDoldKanAW_positive_projected_eval {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z (n + 1)) (f : StandardSimplex R x y (n + 1)) :
    ((standardDoldKanModuleIso (R := R) x z).hom.app (Opposite.op ⦋n + 1⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex
        (doldKanHomModule (R := R) x z)).f (n + 1) ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app
        (connectiveHomComplex (R := R) x z)).f (n + 1) ≫
      (connectiveHomComplex_positiveIso (R := R) x z n).hom) (standardAW g f) =
    ∑ j : (Finset.univ : Finset (Fin (n + 2))),
      awTerm g.val f.val Finset.univ j (-(n + 1 : ℤ)) (by simp)
```

### 110.2 検収と登録

コード **`7000f0623`**（1本104行）。個別検査`/private/tmp/isw2-dk-projected5.log`は終了コード0。結合則は複体の射のまま整理してから各項へ移し、計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build126.log`は **3,765 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02ProjectedDK.lean`は **4宣言・標準三公理のみ**。共有鍵は返却済み。累計 **231モジュール・13,839行・2,115宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirtyone-modules.txt`、外枠14,500行まで残り661行。

新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。B3中は対象ビルド・新規分の小さな監査だけとし、枝でコミットを続けた。

### 110.3 残り

B02は未完。今回の実AW側の評価を、A09の自由鎖AW比較の切断点ごとの値、同じ自由鎖Hom随伴、Hom–Tot比較へ接続して全単体の等式を閉じる必要がある。単なる正規化後の値の回収だけで元の比較射の等式を済ませたとは扱わない。その後にB03〜B08、C、Dが残る。停止点2の完了報告ではなく、目標「Dまで進めてください」はactiveのまま。


## 111. 3b-2：外枠に近づいた時点の残工程の再検討と中間停止

### 111.1 authoritative state と短い経路の確認

作業枝`math/inf-supply-b`の検証済みコードは`7000f0623`、報告は`8d8f5ba5a`。作業木はclean、対象ビルド126と新規分監査は終了コード0、実行中のビルドはない。231本の一覧から実ファイルを数え直し、**13,839行**であることを確認した。外枠14,500行まで **661行**。

B02で残るのは、A09の自由鎖AWの各切断の値と§110の実標準AWの各切断の値を、指定随伴・Hom–Tot比較を介して同じ全単体の式へ結ぶこと。§110はこのうち実標準AW側を閉じたもので、自由鎖側と同じ射になったとは数えない。

B04〜B06を短く済ませるため、`ReflectedWeightedNativeCone`・`ReflectedWeightedHomComparison`・`CoherentConeNativeComparison`・`CoherentConeFamilyHomotopy`を読み直した。既存の`reflectedCoherentConeFamilyComparison`とその`_evaluation`は、頂点評価を正しくする選んだ切断の族を与える。しかし、その制限が指定`reflectedWeightedHomComparison`との合成に**等しい**というB06の式は、これらから直接は得られない。既存の族をB04に代入してB06をホモトピーの存在に弱めることはしない。指定重み付き入力から全高次単体の族を構成し、頂点評価と制限を同時に照合する工程が残る。

### 111.2 残量と停止理由

§73の型を維持した見込み。これは実装量の予測であり、数学的な行数下限ではない。特にCとDは未着手であるため、§72.2の見込みを根拠なく縮めない。新しい第五のまとまりは要求していない。

| §72.2／§73のまとまり | 現状と残る型 | 追加見込み |
| --- | --- | ---: |
| 正規化テンソル／積重み | A01〜A12完了。残る最終の実合成との照合は以下のB02に数える | 0行 |
| 指定豊穣Homとnative極限性 | B01完了。B02の自由鎖AW・Hom–Totとの全単体の等式、B03、B04〜B06の指定族と両評価、B07〜B08 | 400〜700行 |
| 標準脚とD(A)輸送 | C01〜C07未完。元の標準脚、同じ全join射の輸送、元のstrict図式との照合 | 400〜700行 |
| 全図式射・指定錐の族・離散入口 | D01〜D08未完。全パラメータ族の境界・各点・辺、離散制限、ホモロジー入口 | 500〜900行 |
| 合計 | | **1,300〜2,300行** |

完成見込みは **15,139〜16,139行**。CとDだけの従来見込み900〜1,600行も、残枠661行を超える。B02の小さい計算補題を足し続けて外枠を使い切るのではなく、「超えそうなら検証済みを保存して報告し止める」という条件に従い、**3b-2の追加Leanはここで中間停止する**。

検証済みの分はすべてコミット済みであり、未検証の下書きはない。停止点2ではない。範囲や型を弱めず、Dを3b-3へ移さず、既存宣言・⑤a・mainを変更せず、外枠を独自に引き上げない。再開には残工程と外枠についての調整が必要。目標「Dまで進めてください」は未達成のまま保持する。今回がこの外枠に関する新たな中間停止の最初のターンであり、goalをcompleteやblockedには変更しない。

## 112. 代わりの紙の作業：3b-4の既存strict模型と3b-3の受け渡しの再確認

この節は読み取りと型案のみ。Leanの宣言・新しい模型内部への参照は追加せず、ビルドの鍵も取得していない。B3の連絡に従いmainをmergeしていない。mainの読み取り時のrefは`40faa3892120211786cf463371a356c3fc9de6e1`。

### 112.1 既存部品との重複を避ける

`BarrattEccles/FramedLimit.lean`には、既に任意の小図式の**全関手**`framedLimitFunctor A K`と台の`framedLimitCarrierIso`がある。`FramedLimitCarrierDerivedComparison.lean`には、複体の通常局所化における`carrierFramedLimitComparisonIso`と、元の通常錐との両立`carrierFramedLimitComparisonIso_cone`がある。したがって、3b-4 §38.2の1・2でBEの右frame/endやその通常局所化の対象比較を新規に作り直す必要はない。これらの既存ファイルは⑤a側の部品として変更しない。実装再開時は新規ファイルで橋だけを作る。

ただし、通常局所化の同型や各対象の台の同型だけを、指定native錐の族を保つ∞関手同型と同一視しない。既存`algebraCAlgSource_underlyingDerivedIso`が与えるのは実Uと元の通常忘却の全比較であり、これと上記通常局所化の比較をつなぐ全高次単体の工程が必要。

紙の略記として、`J = Δ`に固定し、次の二つの全単体的射を比較する段を切り出す（ここでは新しいLean宣言として検査した型ではない）。

```lean
F_BE := nerveMap (framedLimitFunctor A J) ≫ algebraCAlgSource A ≫ cAlgForgetDerived A
F_DA := nerveMap (Diagram.forget A J ⋙ ComplexLimits.framedLimitFunctor A J) ≫
  ComplexLimits.complexOrdinaryDerivedSource A
-- 必要な強さ：FunctorIso F_BE F_DA と、同じ指定全錐族の輸送の式。
```

`FreeProbeDerivedLimits.lean`の`cAlgForgetDerived_mapJoinCone_isLimit_of_transport`は、`FreeProbeUnitTransportCondition A`を**明示的に仮定**する。この仮定を無条件の供給済み結果として使わず、⑤a側の供給点を確認する。右Quillen性やprojective図式の全対象fibrant性だけで、通常limを導来limと同定することもしない。

### 112.2 ③-aのR6で使える形と、まだ別の入力

mainを読み取ると、`StrictSemifreeComputedColimitFamily.lean`に`strictSemifreeComputedColimitFamilyIso`と、包含後の同じ全余錐族の比較`strictSemifreeComputedCoconeFamilyIso`がある。`StrictSemifreeRealizationFamily.lean`には、同じ実現全関手の族・頂点・辺の式がある。これらは、§38.1で求めた「3b-1から移したstrict加群図式の全パラメータ比較」に対応する受け取り候補である。B3後のB4で名前と型を引き直して使う。今は枝へ取り込まず、既存ファイルの変更やコピーもしない。

このR6の供給を、任意のcoherent BE図式の厳密化の代わりには使わない。③-aの加群図式の比較は加群値の3b-3であり、BE作用を回復する全coherent図式の比較は§38.2の3として別に残る。strict BE図式の模型計算とそのU比較が済む前から、この追加の厳密化を仮定に押し込んだ主張を作らない。

今回の紙の確認により、3b-4で最初に重複を避ける対象は上記の既存`FramedLimit*`・`CAlgUnderlyingDerivedComparison`、受け取り候補はR6の全余錐族の同型と明確になった。G10（3b-2）は未完のままなので、これを完了扱いして3b-4のLeanへ移ってはいない。


## 113. 11-14の再開承認とBE忘却の無条件版の確認

### 113.1 IS-W2 §16

ユーザー承認とmainの指示書§16を読み取り、3b-2をB02から再開した。外枠は **20,000行**、一覧B01〜B08・C01〜C07・D01〜D08と§14の数え方は維持する。B・Cの完了を停止点**2a**として報告し、承認を待たずDへ進む。D完了は停止点**2b**（3b-2完成）。B完了時に、その実測とAの見込みに対する増分の比率も参考にC・Dを再見積もりして止まらず報告する。

前回の外枠による中間停止は解除した。mainは凍結中なのでmerge・変更・ビルドをせず、自分の枝だけで検証とコミットを続ける。対象ビルドと新規分だけの小さな監査を用いる。

### 113.2 §112の補足：FreeProbeUnitTransportConditionは本体で証明済み

調整役の11-14の連絡を受け、実ファイルを読み直して確認した。

- `EInfinity/BarrattEccles/FreeProbeUnitLocalTransport.lean`の`freeProbeUnitTransportCondition`は、`derivedFreeProbeUnitIntervalMap_transportIso`を使って`FreeProbeUnitTransportCondition A`を証明している。
- `FreeProbeDerivedFreeForget.lean`の`cAlgFreeForgetDerivedAdjunction`は、その定理を`cAlgFreeForgetDerivedAdjunctionOfTransport`へ渡した無条件の随伴。
- 同ファイルの`cAlgForgetDerived_mapJoinCone_isLimit`と`cAlgForgetDerived_hasLimit_postcomp`は、その定理を条件付き版へ代入した無条件版。§112の条件付き版だけの確認を、未供給の障害とは扱わない。

3b-4ではこの**無条件版**を再利用する。BEの実例の`forget_preservesLimits`にも供給済みとの連絡を受領した。既存の`FramedLimit*`や`CAlgUnderlyingDerivedComparison`の再構成は行わない。

これによりBE側の指定native極限錐が得られた後のU像の極限性は、追加のtransport仮定なしで上記定理へ接続できる。一方、元のstrict BE模型計算の指定錐をそのnative錐へ全高次単体とともに接続する工程と、実現側のU保存は、この極限保存定理だけで済ませない。G10（B02以降）の進行順は変えない。


## 114. B02再開後：実AW合成の同じ自由逆随伴を全次数で評価

### 114.1 進捗と型

§16の承認に従いB02を再開した。実標準DK Homへの射を、既存の自由加群・Moore正規化随伴の**同じ合成**で戻す。その逆随伴を指定Moore射影生成元で評価すると、実Γの同じ射影と余単位による評価に一致することを示した。これを指定標準DK同型へ適用し、正次数は元の最上位成分、零次数はcyclesからの包含で元の最上位成分を回収する。

実`standardComposition`に適用した逆随伴について、零次数・全正次数で元の`awTerm`の全切断点の和になる式を閉じた。後の射gを第一因子、前の射fを第二因子とし、元のbraidingと標準合成の順を保持する。これはB02の同じ生成元・成分照合の証明分割（§14）であり、独立した前提計算や照合の枠を追加しない。B02前提計算3/3、照合全体3/3のまま。

下記はDiagramComparison名前空間。一般の式は`{R : Type u}`・`[CommRing R]`、標準Homの式はさらに`{D : Type v}`・`[DGCategory R D]`を固定する。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomProjectedEvaluation`

```lean
def freeMooreChainsAdjunction :
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (ModuleCat R)).obj
      (ModuleCat.free R) ⋙ normalizedMooreComplex (ModuleCat R)) ⊣
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat R) (Type u)).obj
        (forget (ModuleCat R)))
```

```lean
theorem normalizedFreeHomEquiv_symm_projected_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R)) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f n
      ((DoldKan.PInftyToNormalizedMooreComplex (S ⋙ ModuleCat.free R)).f n
        (ModuleCat.freeMk s)) =
    ((DoldKan.PInftyToNormalizedMooreComplex (Abelian.DoldKan.Γ.obj K)).f n ≫
      (Abelian.DoldKan.equivalence.counitIso.hom.app K).f n) (f.app _ s)
```

```lean
def standardDoldKanSpaceMap (x y : D) :
    standardHomSpace (R := R) x y ⟶
      (Abelian.DoldKan.Γ.obj (connectiveHomComplex (R := R) x y)) ⋙
        forget (ModuleCat R)
```

```lean
theorem normalizedFreeStandardHom_positive_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) :
    let g : (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
        connectiveHomComplex (R := R) x y
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeAWProjectedEvaluation`

```lean
def normalizedFreeStandardHom (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) :
    (normalizedMooreComplex (ModuleCat R)).obj (S ⋙ ModuleCat.free R) ⟶
      connectiveHomComplex (R := R) x y
```

```lean
theorem normalizedFreeStandardAW_positive_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n + 1⦌)) (t : T.obj (Opposite.op ⦋n + 1⦌)) :
    let h
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedFreeHomZeroEvaluation`

```lean
theorem mooreProjection_zero_eq (W : SimplicialObject (ModuleCat R)) :
    (DoldKan.PInftyToNormalizedMooreComplex W).f 0 = (mooreDegreeZeroIso W).inv
```

```lean
theorem normalizedFreeHomEquiv_symm_zero_eval (S : SSet.{u})
    (K : ChainComplex (ModuleCat R) ℕ)
    (f : S ⟶ (Abelian.DoldKan.Γ.obj K) ⋙ forget (ModuleCat R))
    (s : S.obj (Opposite.op ⦋0⦌)) :
    (((freeMooreChainsAdjunction (R := R)).homEquiv S K).symm f).f 0
      ((mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)) =
    (gammaDegreeZeroIso K).hom (f.app _ s)
```

```lean
theorem normalizedFreeStandardHom_zero_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (s : S.obj (Opposite.op ⦋0⦌)) :
    (homObject R D x y).iCycles 0
      ((connectiveHomComplex_zeroIso (R := R) x y).hom
        ((normalizedFreeStandardHom S x y f).f 0
          ((mooreDegreeZeroIso (S ⋙ ModuleCat.free R)).inv (ModuleCat.freeMk s)))) =
    standardTopEval (R := R) x y 0 (f.app _ s)
```

```lean
theorem normalizedFreeStandardAW_zero_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y)
    (s : S.obj (Opposite.op ⦋0⦌)) (t : T.obj (Opposite.op ⦋0⦌)) :
    let h
```

### 114.2 検収と登録

コード **`a34bfb003`**（1本117行）・**`8b0cc2644`**（2本157行）、計 **3本274行**。

- 鍵付き対象ビルド127：**4,081 jobs・終了コード0**、新規監査`/private/tmp/AuditISW2G10B02FreeProjected.lean`は **6宣言・標準三公理のみ**。
- 最終ソースの鍵付き対象ビルド129：**4,097 jobs・終了コード0**、新規監査`/private/tmp/AuditISW2G10B02FreeAWZero.lean`は **9宣言（4・5）・標準三公理のみ**。

ログは`/private/tmp/isw2-build127.log`・`/private/tmp/isw2-build129.log`。共有鍵は返却済み。大きな監査・rootビルドは実行していない。再利用する零次数DK公式の成果物が枝になかったので、その依存は上記対象ビルドで補った。

深いΓの型照合が既定の200,000 heartbeatに達した箇所は、同じ随伴と忘却射の型を固定し、合成の適用だけを明示して解消した。計算上限は上げず、既存宣言・⑤a・入口・公式監査・mainを変更していない。新公理・sorryなし。

累計 **234モジュール・14,113行・2,130宣言**。対象一覧は`/private/tmp/isw2-g10-twohundredthirtyfour-modules.txt`。新しい外枠20,000行まで残り5,887行。登録対象は114.1の3本。

### 114.3 次の接続

B02は未完。今回の実合成の逆随伴の切断和を、A09の同じ自由鎖AWと指定tensor–Hom随伴の切断点ごとの式へ接続する。sourceのMoore射影を一般のAWと可換と仮定するのではなく、同じ生成元評価の後で比較し、包含と射影のsplit則を使う経路を検討している。

`FreeTensorCoefficientGeneratorValues.lean`は、最後の切断の既存係数計算を任意の二次数へ分割する検査中の下書き。上のコミット・行数・監査には含めない。B03〜B08・C・Dも未完であり、今回の区切りは停止点2a・2bの完了報告ではない。Bが完了した時点でC・Dの見込みを実測に基づいて出し直す。


## 115. B02の途中：自由鎖AWの任意切断と全切断和の計算

### 115.1 同じ成分照合の分割と型

§114の実合成側の全切断和へ接続するため、A05aで検証した最後の切断の係数計算を、同じ既存構成の任意の二次数・任意の切断点へ分割した。指定係数比較が二因子のMoore射影生成元の純テンソルを、元の負次数延長の純テンソルへ送ることを、既存の斉次包含・係数移送・自由生成元の式から示した。

その式を既存AWの各切断成分へ代入し、対応する前面・後面の射影生成元のテンソルとなる式を閉じた。さらに既存`alexanderWhitneyApp`の有限和の定義から、同じ全切断和の式を得た。始域のMoore射影を勝手に消去せず、整数線形化からの元の成分に対して述べている。

下記はDiagramComparison名前空間、`{A : Type u}`・`[CommRing A]`を固定する。B02の同じ係数・成分計算の証明分割（§14）であり、独立した前提計算や照合の追加ではない。B02前提計算3/3、照合全体3/3はそのまま。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues`

```lean
def freeNegativeGenerator (X : SSet.{u}) (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)) :
    (freeNegativeChains (A := A) X).X (-(n : ℤ))
```

```lean
theorem freeTensorCoefficient_projection_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (i j n : ℕ) (h : i + j = n)
    (x : X.obj (Opposite.op ⦋i⦌)) (y : Y.obj (Opposite.op ⦋j⦌)) :
    let F
```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWCutValues`

```lean
theorem freeProductAlexanderWhitney_cut_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ) (c : Fin (n + 1))
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F
```

```lean
theorem freeProductAlexanderWhitney_sum_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ)
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F
```

### 115.2 検収と登録

コード **`13d1ecc09`**（2本209行）。依存順に結合した個別検査`/private/tmp/isw2-free-aw-cut3.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build130.log`は **4,014 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02FreeAWCuts.lean`は **10宣言（7・3）・標準三公理のみ**。共有鍵は返却済み。

累計 **236モジュール・14,322行・2,140宣言**。一覧は`/private/tmp/isw2-g10-twohundredthirtysix-modules.txt`。外枠20,000行まで残り5,678行。新公理・sorryなし。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査は実行していない。登録対象は115.1の2本。

### 115.3 残り

B02は未完。今回の自由鎖AW側の切断和と、§114の実豊穣合成の逆随伴の切断和を、指定tensor–HomとHom–Totの成分・符号を介して同じ射として照合する。`HomTotalHomogeneousComposition.lean`は、試験対象の次数零の鎖射に限らず任意次数の合成について同じ積射影の成分を合わせる検査中の下書きであり、この検収と累計には含めない。

B03〜B08・C・Dは未完。停止点2a・2bの完了報告ではない。B完了時のC・Dの再見積もりは、Bの実測が揃った所で行う。


## 116. B02の途中：Hom–Tot成分の任意次数合成

### 116.1 同じ成分照合の型

元の`homTotalComponent`は、試験対象の次数零の鎖射だけでなく、**任意の整数次数p・qの斉次射の合成**を、同じ積射影による成分で保つことを示した。微分閉性や有界性を追加していない。B02の全Hom単体の成分照合の分割（§14）であり、独立した前提計算・照合の枠を追加しない。B02前提計算3/3、照合全体3/3のまま。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalHomogeneousComposition`。
名前空間はHA.DerivedCategoryModels.CosimplicialTotalization、`{A : Type u}`・`[CommRing A]`を固定する。

```lean
theorem homTotalComponent_homogeneous_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    homTotalComponent P X (p + q) n (f.comp g rfl) =
      f.comp (homTotalComponent Q X q n g) (by omega)
```

### 116.2 検収と登録

コード **`950678940`**（1本46行）。個別検査`/private/tmp/isw2-homtotal-homogeneous8.log`は終了コード0。依存するcochain成分の等しい整数添字の移送は、既存の成分式を使い、合同を一段ずつ取り整数等式の所でomegaを適用して閉じた。計算上限は変更していない。

鍵付き対象ビルド`/private/tmp/isw2-build131.log`は **2,287 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02HomTotalComposition.lean`は **2宣言・標準三公理のみ**。共有鍵は返却済み。大きな監査・rootビルドは実行していない。

累計 **237モジュール・14,368行・2,142宣言**。一覧は`/private/tmp/isw2-g10-twohundredthirtyseven-modules.txt`、外枠20,000行まで残り5,632行。再開後の追加は6本529行・27宣言。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。登録対象は116.1の1本。未検証下書きは残っていない。

### 116.3 残り

B02は未完。実AWの逆随伴の切断和（§114）、自由鎖AWの各切断と全切断和（§115）、Hom–Totの任意次数合成（本節）を、同じ指定重みとtensor–Homの符号付き成分に接続して最終の射の等式を閉じる。これらの部分公式を、B02の最終等式やB03〜B08のnative極限性の代用にしない。

C・Dも未完。停止点2a・2bの検収ではない。新しい外枠と一覧の中で継続し、B完了時にC・Dを実測に基づいて再見積もりする。BE忘却の無条件版の確認は§113.2に記録済み。


## 117. B02の途中：元のHom–Tot/BK比較の全行を指定標準重み射で表示

### 117.1 同じ比較の因子分解と型

元のMoore包含・over/bar鎖同型の逆射・先頭頂点の標準重み比較を、`normalizedBKStandardWeightMap`にまとめた。元の`normalizedBousfieldKanHomComparison`が、この同じ射の前合成と既存の符号つきend–Hom同型の合成に**厳密に等しい**ことを証明した。

指定標準重みへの逆比較の各成分を、同じ自由単位Yoneda評価の逆射で同定した。積射影の自然性で任意の鎖重みからの前合成へ移し、元の`homTotalNatIso_hom_component`を代入して、元の`homToNormalizedBousfieldKan`の**任意整数次数q・全鎖次数n**での行表示を得た。指定射と元の積成分・符号を保持する。

以下はHA.DerivedCategoryModels.CosimplicialTotalization名前空間。係数環は`A : Type u`・`[CommRing A]`（各宣言によりAは暗黙／明示）。B02の同じ成分照合の証明分割（§14）であり、独立した前提計算・照合を追加しない。B02前提計算3/3・照合全体3/3のまま。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKWeightComparisonComponents`

```lean
theorem barWeightEndTotalComparison_app_standard (X : CosimplicialObject (Complex A)) :
    barWeightEndTotalComparison.app X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          ((alternatingFaceMapComplex _).map
            (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).op
```

```lean
theorem barToBousfieldKanWeightEndComparison_app (X : CosimplicialObject (Complex A)) :
    barToBousfieldKanWeightEndComparison.app X =
      (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
        (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.op
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKStandardWeight`

```lean
def normalizedBKStandardWeightMap :
    normalizedBousfieldKanWeight (A := A) ⟶
      (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A))
```

```lean
theorem normalizedBousfieldKanHomComparison_standardWeight
    (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHomComparison X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          (normalizedBKStandardWeightMap A).op ≫
        (weightEndHomIso A normalizedBousfieldKanWeight (doubleOppositeDiagram X)).hom
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightTotalInverseEvaluation`

```lean
theorem standardWeightEndCochainIso_inv_f (X : CosimplicialObject (Complex A)) (n : ℕ) :
    (standardWeightEndCochainIso X).inv.f n =
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app (doubleOppositeDiagram X)).inv
```

```lean
theorem standardWeightEndTotalIso_inv_component
    (X : CosimplicialObject (Complex A)) (n : ℕ) (q : ℤ) :
    (standardWeightEndTotalIso X).inv.f q ≫
      CochainProductTotal.componentπ
        ((linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
          (Opposite.op ((alternatingFaceMapComplex _).obj
            (standardSimplexWeight (ModuleCat.of A A))))) n q =
    componentπ X n q ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n)
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightHomRows`

```lean
theorem standardWeightHomComparison_rows
    (K : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℕ)
    (g : K ⟶ (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A)))
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (z : ((productTotalFunctor A).obj X).X q) (n : ℕ) :
    extendedChainHomRows K
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) q
      ((weightEndHomIso A K (doubleOppositeDiagram X)).hom.f q
        (((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map g.op).f q
          ((standardWeightEndTotalIso X).inv.f q z))) n =
    weightEndHomSign n q • (g.f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram X)).inv.f (q - n) (componentπ X n q z))
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKRows`

```lean
theorem homToNormalizedBousfieldKan_rows (P : Complex A)
    (X : CosimplicialObject (Complex A)) (q : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) q) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) q
      ((homToNormalizedBousfieldKan P X).f q f) n =
    weightEndHomSign n q • ((normalizedBKStandardWeightMap A).f n ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f (q - n)
        (homTotalComponent P X q n f))
```

### 117.2 検収と登録

コード **`98cae95ee`**（5本267行）。結合検査`/private/tmp/isw2-hom-bk-rows2.log`は終了コード0。最初の一括展開ではkernelの既定の計算上限に達したため、既存の前向き射の定理による対象成分を小補題に分けてから関手の合成則を適用した。計算上限を上げていない。

- 鍵付き対象ビルド132：**2,541 jobs・終了コード0**、監査`/private/tmp/AuditISW2G10B02StandardWeight.lean`は **10宣言（2・8）・標準三公理のみ**。
- 鍵付き対象ビルド133：**2,560 jobs・終了コード0**、監査`/private/tmp/AuditISW2G10B02HomBKRows.lean`は **5宣言（2・1・2）・標準三公理のみ**。

ログ`/private/tmp/isw2-build132.log`・`/private/tmp/isw2-build133.log`。共有鍵は返却済み。累計 **242モジュール・14,635行・2,157宣言**。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査・rootビルドなし。登録対象は117.1の5本。

## 118. B02の途中：指定BK比較の任意次数合成とKoszul符号

### 118.1 同じ行の合成計算と型

斉次射f（閉性を要求しない）の前合成を、元のHom図式の**次数ごとの加群図式**の自然変換にした。cochain合成の線形性・次数零の図式射との結合則だけを使い、これを鎖射だとは主張していない。既存の自由Yoneda後合成則と同じ同型の逆射則から、同じ逆評価がこの前合成と可換なことを示した。

これと§116のHom–Totの任意次数合成、§117の指定行表示を合わせ、元の`homToNormalizedBousfieldKan`の各行の合成に現れる符号が **(-1)^(np)** であることを証明した。符号は同じ`weightEndHomSign`の式から計算し、選び直していない。

以下も同じ名前空間、`{A : Type u}`・`[CommRing A]`。B02の同じ全パラメータ成分計算の分割（§14）。前提計算3/3・照合3/3の枠を追加しない。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomDiagramDegreePrecompose`

```lean
def homDiagramDegreePrecompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) q ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) ⋙
        HomologicalComplex.eval (ModuleCat A) (.up ℤ) r where
  app j
```

```lean
theorem freeUnitWeightEnd_inv_degree_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r)
    (f : Homogeneous P Q p) (n : ℕ) (z : Homogeneous Q (X.obj ⦋n⦌) q) :
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))).inv.f q z ≫
      homDiagramDegreePrecompose X p q r h f =
    ((freeUnitWeightEndNatIso A (Opposite.op ⦋n⦌)).app
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))).inv.f r (f.comp z h)
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomToNormalizedBKComposition`

```lean
theorem homToNormalizedBousfieldKan_rows_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) (p + q)
      ((homToNormalizedBousfieldKan P X).f (p + q) (f.comp g rfl)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (p + q - n) (by omega) f)
```

### 118.2 検収と登録

コード **`c2beef461`**（2本136行）。結合検査`/private/tmp/isw2-bk-hom-composition.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build134.log`は **2,562 jobs・終了コード0**。新規分だけの監査`/private/tmp/AuditISW2G10B02HomBKComposition.lean`は **10宣言（7・3）・標準三公理のみ**。共有鍵は返却済み。

累計 **244モジュール・14,771行・2,167宣言**、外枠20,000行まで残り5,229行。対象一覧は`/private/tmp/isw2-g10-twohundredfortyfour-modules.txt`。新公理・sorryなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。大きな監査・rootビルドなし。登録対象は118.1の2本。

### 118.3 残り

B02は未完。今回の指定Hom/BK行の合成と同じKoszul符号を、既に検証したAWの両切断和・指定tensor–Homへ接続して、元の単体的比較射の等式を閉じる。`NormalizedSimplexFreeAdjunction.lean`はA09の標準単体パラメータ側の随伴を同じ恒等生成元で照合する検査中の下書きであり、今回の検収・累計には含めない。

B03〜B08・C・Dも未完。停止点2a・2bの検収ではない。B完了時にC・Dを実測に基づいて再見積もりし、止まらずに進める。


## 119. B02の途中：元の錐代表との行の合成と標準単体の自由随伴

### 119.1 型と接続

A09の標準単体パラメータの`normalizedSimplexHomEquiv`が、同じ自由鎖随伴の恒等単体の生成元での評価に一致することを示した。二つの零延長・smart切断Hom同値は、同じ逆写像の式で照合した。自由加群・DK・切断の随伴や生成元を選び直していない。

元の`normalizedBousfieldKanRepresentative`のcochainが、同じ`homToNormalizedBousfieldKan`に移した元の閉元そのものであることも確認した。任意次数の行の合成則を指定終次数rで述べてから後の射を恒等射に特殊化し、元の錐代表の**同じcochain行**への前合成の式を得た。零次数の行の終次数`0-n`を無断で`-n`と同一視するのではなく、元の型を保持する。

以下の型は各モジュールの既存名前空間。係数環は`A : Type u`・`[CommRing A]`（暗黙／明示は各宣言のとおり）。既存の随伴・合成の法則と同じB02の証明分割。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexFreeAdjunction`

```lean
theorem normalizedSimplexHomEquiv_freeAdjunction (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    ((freeNegativeChainsAdjunction A).homEquiv
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f).app (Opposite.op n)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n))) =
    normalizedSimplexHomEquiv A H n f
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeComposition`

```lean
theorem homToNormalizedBousfieldKan_rows_comp_of_degree {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q r : ℤ) (h : p + q = r) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) r
      ((homToNormalizedBousfieldKan P X).f r (f.comp g h)) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor Q).obj X))) q
        ((homToNormalizedBousfieldKan Q X).f q g) n ≫
      homDiagramDegreePrecompose X p (q - n) (r - n) (by omega) f)
```

```lean
theorem normalizedBousfieldKanRepresentative_cochain (P : Complex A)
    (X : CosimplicialObject (Complex A)) (f : P ⟶ (productTotalFunctor A).obj X) :
    Cochain.ofHom (normalizedBousfieldKanRepresentative P X f) =
      (homToNormalizedBousfieldKan P X).f 0 (Cochain.ofHom f)
```

```lean
theorem homToNormalizedBousfieldKan_rows_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n =
    ((n : ℤ) * p).negOnePow •
      (extendedChainHomRows normalizedBousfieldKanWeight
        ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
        0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n ≫
      homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f)
```

### 119.2 検収と登録

コード **`afb2a7c53`**（2本147行：70・77）。個別検査`/private/tmp/isw2-simplex-free-adjunction3.log`・`/private/tmp/isw2-bk-cone-composition3.log`は終了コード0。鍵付き対象ビルド`/private/tmp/isw2-build135.log`は **2,899 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02ConeSimplex.lean`は **11宣言（5・6）・標準三公理のみ**。共有鍵は返却済み。

累計 **246モジュール・14,918行・2,178宣言**。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。新公理・sorryなし。大きな監査なし。登録対象は119.1の2本。

## 120. B02の途中：tensor–Hom符号の消去と実dg合成の成分

### 120.1 型と意味

元の指定BK行の任意次数合成の符号`(-1)^(np)`と、tensor逆転置の同じ重み次数に現れる符号`(-1)^((-n)p)`を合わせ、積が1になることを示した。結果は、元の錐代表のcochain行と任意のHomパラメータの**実dg合成`compose`**である。複体の`enrichedComposition`の既存成分式で、通常順の合成とcochain合成も同じ値として計算した。

これは一般の符号つき成分の式で、試験パラメータの閉性や有界性を仮定していない。B02の各AW切断の照合に使う既存構成の合成則。指定単体的射全体の一致は、まだこの一つの成分式で置き換えない。

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKTensorRow`

```lean
theorem homToNormalizedBousfieldKan_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : ((normalizedBousfieldKanWeight (A := A)).X n).obj j) :
    let η := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
      0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n
    let χ := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega)
```

### 120.2 検収と登録

コード **`6c03058df`**（1本75行）。個別検査`/private/tmp/isw2-bk-tensor-row2.log`は終了コード0。最終ソースの鍵付き対象ビルド`/private/tmp/isw2-build136.log`は **2,564 jobs・終了コード0**。新規分のみの監査`/private/tmp/AuditISW2G10B02TensorRow.lean`は **2宣言・標準三公理のみ**。共有鍵は返却済み。

累計 **247モジュール・14,993行・2,180宣言**。一覧は`/private/tmp/isw2-g10-twohundredfortyseven-modules.txt`。外枠20,000行まで残り5,007行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。新公理・sorryなし。大きな監査・rootビルドなし。登録対象は120.1の1本。未検証下書きはない。

B02の最終の単体的射の等式、B03〜B08・C・Dは未完。次は同じパラメータ随伴・成分式を、A09の重み付き切断Hom同型と実合成の全切断和へ組み込み、反転・添字移送を含む元の比較射の等式へ戻す。

## 121. 11-14の一覧の新しい数え方の適用

調整役の連絡とmainの`coordination.md` §2の追記を読み取り確認した。既存の構成の法則（単位・余単位・自然性・係数移送・合成則・貼り合わせ）と証明分割には本数の枠を置かず、型を報告に書く。200行を超えるものは行数も記録する。本報告では引き続き各検収のファイル行数も併記する。

これまでの「前提計算3/3」「照合3/3」は当時の検収の記録として残すが、**今後の停止判定には使わない**。既存の合成を名前で固定した定義や、指定射の成分評価を分割した今回の補題を、新しい独立の構成の導入とは扱わない。既存構成の法則ではない新しい構成・定理、承認済みまとまりの外、外枠に届く所では停止して報告する。B01〜B08・C01〜C07・D01〜D08と停止点2a・2b、外枠20,000行は維持する。

mainは凍結中なので、追記の確認は読み取りだけとしmergeしていない。自分の枝で作業とコミットを続け、鍵は`--wait 3600`でビルド・小監査の間だけ持つ。


## 122. B02の途中：全標準単体の自由随伴評価と図式逆転置

A09の元の比較を、同じAW前合成の自由鎖随伴へ戻す式を全標準単体で証明した。頂点だけの同定ではなく、元のYoneda射・宇宙同型・指定自由随伴を保持している。図式tensor–Homの逆射についても、各点の斉次tensor上のKoszul符号を元の逆転置の成分則で計算した。いずれも既存構成の余単位・評価・合成則で、11-14の新しい数え方に従う。B02の指定単体的射全体の等式は未完。

### 122.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexHomEvaluation`（60行）

```lean
theorem liftedStandardSimplexHomIso_hom_apply (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f =
      f.app (Opposite.op n) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 n)))

theorem normalizedSimplexHomEquiv_via_freeAdjunction (A : Type u) [CommRing A]
    (H : Complex A) (n : SimplexCategory)
    (f : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj n) ⟶ H) :
    (liftedStandardSimplexHomIso ((truncatedDoldKanFunctor A).obj H)).hom.app (Opposite.op n)
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H f) =
    normalizedSimplexHomEquiv A H n f

theorem liftedStandardSimplexHomIso_yoneda (Z : SSet.{u}) (n : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    liftedStandardSimplexIso.{u}.hom.app n ≫
      SSet.yonedaEquiv.symm ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) f) =
    f

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductSectionsHomEvaluation`（61行）

```lean
theorem weightedFreeChainsAdjunction_uncurry (W : J ⥤ SSet.{u})
    (Y : SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) (W ⊗ (Functor.const J).obj Y) ⟶ Q) :
    weightedSectionsUncurry
      (((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv
        Y Q f) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⊗ (Functor.const J).obj Y) Q f

theorem freeProductSectionsHomIso_uncurry (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (n : SimplexCategory) (f : (freeProductFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((freeProductSectionsHomIso A W Q).hom.app (Opposite.op n) f)) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q f

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionEvaluation`（56行）

```lean
theorem normalizedWeightSectionMap_hom_uncurry (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) (n : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A W Q φ).app (Opposite.op n)
          ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q
      (freeProductDiagramAW φ W ((liftedStandardSimplexParameter J).obj n) ≫ f)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorHomComponents`（40行）

```lean
theorem diagramTensorLinearHomEquiv_symm_app
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J) :
    ((diagramTensorLinearHomEquiv P Q T).symm f).app j =
      (tensorHomEquiv (P.obj j) T (Q.obj j)).symm
        ((diagramHomFamilyOfHom P Q T f).val j)

theorem diagramTensorLinearHomEquiv_symm_component
    (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) (j : J)
    (i q n : ℤ) (hn : i + q = n) (y : (P.obj j).X i) (x : T.X q) :
    (((diagramTensorLinearHomEquiv P Q T).symm f).app j).f n
      (HomologicalComplex.ιTensorObj (P.obj j) T i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow • (diagramCochainAt P Q (f.f q x) j).v i n hn y

```

### 122.2 検収と残り

コード **`18d19ebf0`**。鍵付き対象ビルド `/private/tmp/isw2-build137.log` は **2,645 jobs・終了コード0**。新規4本のみの監査 `/private/tmp/AuditISW2G10B02SectionEvaluation.lean` は **9宣言（3・3・1・2）、標準三公理のみ**。共有鍵は返却済み。個別検査の図式逆転置も終了コード0。

新規4本217行、累計 **251モジュール・15,210行・2,189宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftyone-modules.txt`。既存宣言・⑤a・入口・公式監査・mainは変更していない。計算上限を上げず、sorry・新公理0。rootビルド・大きな監査なし。B02、B03〜B08、C、Dは引き続き未完。次は同じtensorパラメータの逆射を各点で展開し、実dg合成の各AW切断和と照合する。

## 123. B02の途中：同じΓパラメータ像の逆転置成分

指定自由tensor Hom同型の逆射を各点で元の図式逆転置へ戻した。標準単体の自由tensor比較は各点の恒等射であり、同じ実Γの射の像を正規化標準単体Hom同値で戻すと元の複体射の後合成となる。この二つの式から、A09へ渡す全パラメータ像の斉次tensor成分を、元の複体射の各次数の作用で計算した。既存構成の自然性・評価・合成則で、新しい数学のまとまりを足していない。

型推論の途中で、恒等tensor則に対象を射として誤って渡したため時間切れが出た。正しい既存則 `tensorHom_id` と `id_whiskerRight` に直し、対象・次数を明記して解消した。計算上限は変更していない。

### 123.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseNaturality`（34行）

```lean
theorem normalizedSimplexHomEquiv_symm_map {K L : Complex A}
    (g : K ⟶ L) (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op n)) :
    (normalizedSimplexHomEquiv A L n).symm
      (((truncatedDoldKanFunctor A).map g).app (Opposite.op n) α) =
      (normalizedSimplexHomEquiv A K n).symm α ≫ g

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorHomInverseEvaluation`（102行）

```lean
theorem freeTensorStandardSimplexIso_hom_app (W : J ⥤ SSet.{u})
    (n : SimplexCategory) (j : J) :
    ((freeTensorStandardSimplexIso A J W).hom.app n).app j = 𝟙 _

theorem freeTensorDiagramHomIso_inv_app (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op n)) (j : J) :
    ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op n) α).app j =
      ((diagramTensorLinearHomEquiv (freeNegativeChainsDiagram (A := A) W) Q
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj n))).symm
        ((normalizedSimplexHomEquiv A
          (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
            ((E).obj Q)) n).symm α)).app j

theorem freeTensorDiagramHomIso_inv_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
        ((E).obj Q))).obj (Opposite.op m)) (j : J)
    (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) α).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (((normalizedSimplexHomEquiv A
            (linearHomComplex A ((E).obj (freeNegativeChainsDiagram (A := A) W))
              ((E).obj Q)) m).symm α).f q x) j).v i n hn y

theorem freeTensorDiagramHomIso_inv_map_component (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (K : Complex A)
    (g : K ⟶ linearHomComplex A ((E).obj
      (freeNegativeChainsDiagram (A := A) W)) ((E).obj Q))
    (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj K).obj (Opposite.op m))
    (j : J) (i q n : ℤ) (hn : i + q = n)
    (y : ((freeNegativeChainsDiagram (A := A) W).obj j).X i)
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X q) :
    (((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m)
      (((truncatedDoldKanFunctor A).map g).app (Opposite.op m) α)).app j).f n
      (HomologicalComplex.ιTensorObj
        ((freeNegativeChainsDiagram (A := A) W).obj j)
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
          (SSet.stdSimplex.obj m)) i q n hn (y ⊗ₜ[A] x)) =
      (i * q).negOnePow •
        (diagramCochainAt (freeNegativeChainsDiagram (A := A) W) Q
          (g.f q (((normalizedSimplexHomEquiv A K m).symm α).f q x)) j).v i n hn y

```

### 123.2 検収と残り

コード **`c055f145c`**（2本136行）。結合個別検査 `/private/tmp/isw2-free-tensor-map-combined.log` は終了コード0。最終ソースの鍵付き対象ビルド `/private/tmp/isw2-build138.log` は **2,567 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02InverseParameter.lean` は **5宣言（1・4）、標準三公理のみ**。鍵は `--wait 3600`、一枚の整理券、実行1,700秒上限で使用し、返却済み。

累計 **253モジュール・15,346行・2,194宣言**。外枠20,000行まで残り4,654行。一覧 `/private/tmp/isw2-g10-twohundredfiftythree-modules.txt`。既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、大きな監査・rootビルドなし。未検証下書きはない。

B02の全単体的射の等式、B03〜B08・C・Dは未完。次は今回の逆転置成分と§120の実dg合成成分を、§115のAW全切断和で照合する。Moore射影を無条件に消すことはせず、元の射影・包含と係数比較を保持する。停止点2a・2bの仕様と一覧は弱めない。

## 124. B02の途中：実標準AW合成の負次数逆随伴を全次数で評価

自由負次数鎖の指定逆随伴を、同じMoore逆随伴の延長とsmart切断包含の合成に分割した。射影生成元の評価は同じΓのMoore射影と余単位を通して計算した。切断包含は、境界外では元の項同型、零次数では既存のcycles包含として保持した。これを元の標準DK同型の成分式に適用し、**自由負次数逆随伴の全次数の生成元像が実標準Homの最上位成分**であることを証明した。

実AW合成への適用では、正次数・零次数を統一して同じ全切断和が得られる。これは§114のMoore側の評価を、今回必要な元の負次数複体の射へ輸送したもの。B02の証明分割と既存構成の合成・評価則であり、別の比較射や新しい数学のまとまりを導入していない。

### 124.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ComplexLimits.TruncationInclusionComponents`（47行）

```lean
theorem truncLEToRestriction_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    (H.truncLE'ToRestriction e).f n ≫ (H.restrictionXIso e hi).hom =
      (H.truncLE'XIso e hi hn).hom

theorem extendedTruncationInclusion_nonboundary (H : Complex A)
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)) [e.IsTruncLE]
    {n : ℕ} {i : ℤ} (hi : e.f n = i) (hn : ¬ e.BoundaryLE n) :
    ((H.truncLE' e).extendXIso e hi).inv ≫
      ((H.truncLEIso e).inv ≫ HomologicalComplex.ιTruncLE H e).f i =
      (H.truncLE'XIso e hi hn).hom

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeHomDecomposition`（114行）

```lean
theorem freeNegativeChainsAdjunction_symm_moore (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv
        ((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ ModuleCat.free A)) H).symm
        (((freeMooreChainsAdjunction (R := A)).homEquiv S
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f)

theorem negativeExtendTruncationAdjunction_symm_inclusion
    (L : ChainComplex (ModuleCat A) ℕ) (H : Complex A)
    (g : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    ((negativeExtendTruncationAdjunction (ModuleCat A)).homEquiv L H).symm g =
      extendMap g ComplexShape.embeddingDownNat ≫
        truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H

theorem freeNegativeChainsAdjunction_symm_inclusion (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) :
    ((freeNegativeChainsAdjunction A).homEquiv S H).symm f =
      extendMap (((freeMooreChainsAdjunction (R := A)).homEquiv S
        (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).symm f)
          ComplexShape.embeddingDownNat ≫
        truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H

theorem freeNegativeChainsAdjunction_symm_generator_eval (S : SSet.{u}) (H : Complex A)
    (f : S ⟶ (truncatedDoldKanFunctor A).obj H) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction A).homEquiv S H).symm f).f (-(n : ℤ))
      (freeNegativeGenerator S n s) =
      (((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (truncationExtendedInclusionOfShape A ComplexShape.embeddingDownNat
          embeddingDownNat_eq_upIntLE_zero H).f (-(n : ℤ)))
        (((DoldKan.PInftyToNormalizedMooreComplex
          (Abelian.DoldKan.Γ.obj (H.truncLE' (ComplexShape.embeddingUpIntLE 0)))).f n ≫
          (Abelian.DoldKan.equivalence.counitIso.hom.app
            (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).f n)
              (f.app (Opposite.op ⦋n⦌) s))

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeStandardHomEvaluation`（92行）

```lean
theorem connectiveHom_negative_inclusion (x y : D) (n : ℕ) :
    (((homObject R D x y).truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso
      ComplexShape.embeddingDownNat (i := n + 1) (i' := -(n + 1 : ℤ)) (by simp)).inv ≫
      (truncationExtendedInclusionOfShape R ComplexShape.embeddingDownNat
        embeddingDownNat_eq_upIntLE_zero (homObject R D x y)).f (-(n + 1 : ℤ)) =
      (connectiveHomComplex_positiveIso (R := R) x y n).hom

theorem freeNegativeStandardHom_generator_eval (S : SSet.{u}) (x y : D)
    (f : S ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) :
    (((freeNegativeChainsAdjunction R).homEquiv S (homObject R D x y)).symm
      (f ≫ standardDoldKanSpaceMap x y)).f (-(n : ℤ))
        (freeNegativeGenerator S n s) =
      standardTopEval (R := R) x y n (f.app _ s)

theorem freeNegativeStandardAW_generator_eval (S T : SSet.{u}) (x y z : D)
    (g : S ⟶ standardHomSpace (R := R) y z)
    (f : T ⟶ standardHomSpace (R := R) x y) (n : ℕ)
    (s : S.obj (Opposite.op ⦋n⦌)) (t : T.obj (Opposite.op ⦋n⦌)) :
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := R) x y z
    (((freeNegativeChainsAdjunction R).homEquiv (S ⊗ T) (homObject R D x z)).symm
      (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
        (freeNegativeGenerator (S ⊗ T) n (s, t)) =
      ∑ c : (Finset.univ : Finset (Fin (n + 1))),
        awTerm (g.app _ s).val (f.app _ t).val Finset.univ c (-(n : ℤ)) (by simp)

```

### 124.2 検収と残り

コード **`2b2d1f50c`**（新規3本253行）。結合個別検査 `/private/tmp/isw2-negative-standard-aw-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build139.log` は **4,164 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02NegativeStandard.lean` は **15宣言（2・8・5）、標準三公理のみ**。共有鍵は `--wait 3600`・一枚の整理券・実行1,700秒上限で使用し、返却済み。

累計 **256モジュール・15,599行・2,209宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftysix-modules.txt`。外枠まで残り4,401行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02、B03〜B08・C・Dは未完。次の照合は、raw AWの各成分の等式を先に示し、**元のMoore包含を前合成して**正規化側の等式へ制限する。包含→射影の合成が恒等である指定分裂則を使い、P∞がAWと可換という未証明の仮定は置かない。

## 125. B02の途中：raw AW成分等式のMoore制限

raw AWの成分の等式を、元のMoore包含の前合成で正規化AWへ制限する式を証明した。係数移送は既存の加法関手と指定Moore比較で行い、包含→射影が恒等となる分裂則を使う。さらに同じ式を元の負次数AWに適用し、指定延長項同型と係数tensor同型を保持した成分の式へ戻した。**AWとP∞の可換性を仮定する必要はない**。B02に含まれる二つの既存射の照合の証明分割・合成則である。

### 125.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.MappedNormalizedAWRestriction`（61行）

```lean
theorem mappedNormalizedAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : B)
    (t : F.obj ((chainIntegerTensor ((normalizedMooreComplex _).obj C)
      ((normalizedMooreComplex _).obj D)).X n) ⟶ T)
    (h : ((normalizedMooreComplex B).obj (simplicialIntegerTensor C D ⋙ F)).X n ⟶ T)
    (hraw : F.map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫ t =
      F.map ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso F (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (mappedNormalizedAlexanderWhitney F C D).f n ≫ t = h

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeAWRestriction`（65行）

```lean
theorem negativeCoefficientAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : ModuleCat A)
    (t : (HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)).X (-(n : ℤ)) ⟶ T)
    (h : ((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).X n ⟶ T)
    (hraw : (integerCoefficientExtension φ).map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex _).obj C)
            ((normalizedMooreComplex _).obj D))).extendXIso ComplexShape.embeddingDownNat
              (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ C D).hom.f (-(n : ℤ)) ≫ t =
      (integerCoefficientExtension φ).map
        ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso (integerCoefficientExtension φ)
          (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeCoefficientAlexanderWhitney φ C D).f (-(n : ℤ)) ≫ t = h

```

### 125.2 検収と残り

コード **`e6a651b2e`**（新規2本126行）。結合個別検査 `/private/tmp/isw2-negative-aw-restrict-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build140.log` は **2,239 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02AWRestriction.lean` は **3宣言（2・1）、標準三公理のみ**。共有鍵は返却済み。

累計 **258モジュール・15,725行・2,212宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftyeight-modules.txt`。既存宣言・⑤a・入口・公式監査・mainの変更なし。計算上限を上げず、sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。B02の最終等式とB03〜B08・C・Dは未完。

次は標準単体Homの逆同値を同じ自由随伴へ戻し、§124の最上位評価をA09のパラメータに直接適用する。raw成分の照合の仮定そのものは、§115の全切断和と§120の実dg合成成分を使って別途閉じる必要があり、今回の制限則だけでB02を完了とは数えない。

## 126. B02の途中：元の標準単体パラメータを指定自由随伴へ戻す

正規化標準単体Hom同値の逆射を、同じ持ち上げ標準単体Hom同型の逆射と自由鎖随伴の逆射の合成に同定した。元の実標準Homから来る全パラメータについて、その逆射の各射影生成元の像が実標準Homの最上位成分になることを、§124の全次数評価へ接続した。これでA09側のパラメータを試験頂点だけでなく全標準単体で扱える。

重いHom対象で逆射則を直接elaborateすると200,000 heartbeatの上限に達したため、同じ逆射則を任意の台単体集合で一つの部分補題に固定して解消した。新しい数学ではなく同じ証明の分割であり、計算上限を上げていない。

### 126.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexInverseAdjunction`（73行）

```lean
theorem normalizedSimplexHomEquiv_symm_freeAdjunction (H : Complex A)
    (n : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj H).obj (Opposite.op n)) :
    (normalizedSimplexHomEquiv A H n).symm α =
      ((freeNegativeChainsAdjunction A).homEquiv
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)) H).symm
        ((liftedStandardSimplexHomIso ((truncatedDoldKanFunctor A).obj H)).inv.app
          (Opposite.op n) α)

theorem liftedStandardSimplexHomIso_inv_hom_apply (Z : SSet.{u}) (m : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶ Z) :
    (liftedStandardSimplexHomIso Z).inv.app (Opposite.op m)
      ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op m) t) = t

theorem normalizedSimplexHomEquiv_symm_standard_generator
    {D : Type v} [DGCategory A D] (x y : D) (m : SimplexCategory)
    (f : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m) ⟶
      standardHomSpace (R := A) x y) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((liftedStandardSimplexHomIso
        ((truncatedDoldKanFunctor A).obj (homObject A D x y))).hom.app (Opposite.op m)
          (f ≫ standardDoldKanSpaceMap x y))).f (-(n : ℤ))
            (freeNegativeGenerator
              ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n (f.app _ s)

```

### 126.2 検収と残り

コード **`3f092fcc9`**（1本73行）。個別検査 `/private/tmp/isw2-simplex-inverse-adjunction3.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build141.log` は **4,197 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02SimplexInverse.lean` は **3宣言・標準三公理のみ**。共有鍵は返却済み。

累計 **259モジュール・15,798行・2,215宣言**。一覧 `/private/tmp/isw2-g10-twohundredfiftynine-modules.txt`。外枠20,000行まで残り4,202行。既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、大きな監査・rootビルドなし。未検証下書きはない。

B02の全体等式とB03〜B08・C・Dは未完で、Dまでの目標は維持する。次の具体的な接続は以下。

1. 実標準Homの前面・後面への引き戻しの最上位成分を、`awTerm`の接頭・接尾集合の成分へ合わせる（`standardPullback_val`・`pullback_component_of_inj`・`awFront`・`awBack`の既存評価則）。
2. §123の自由tensor逆射成分、§120の実dg合成成分、今回のパラメータ評価を§115のraw AW全切断和で照合する。
3. raw等式を§125の指定Moore包含による制限へ渡し、元の正規化側の複体射を同定する。
4. 指定自由随伴とweighted uncurryの単射性で元の全単体的射へ戻し、既存の反転・添字移送の等式を使ってB02を閉じる。

これらはB02の指定された二つの既存比較の照合の内訳であり、raw等式や最後の輸送を検証済みとは数えない。

## 127. B02の途中：AW前面・後面の各切断と全切断和の照合

指定`awFront`・`awBack`の単射性、全頂点の像、接頭・接尾集合の濃度を計算した。既存の単射引き戻しの評価則から、前面・後面の最上位成分を同じ接頭・接尾集合の成分に同定し、既存の異種等号の合成則で`awTerm`がこれらの通常順合成であることを証明した。

各切断のtensor像がこの実合成と一致するという条件を置けば、§115のraw自由AWの全切断和と§124の実標準AWの逆随伴評価が一致する貼り合わせ則も証明した。**切断条件自体はまだ閉じていない**。これをB02の無条件の全体等式の代わりにはしない。すべて既存構成の評価・合成・貼り合わせの法則、または同じ照合の証明分割であり、新しい数学のまとまりは追加していない。

### 127.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces`（152行）

```lean
theorem awFront_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awFront n c).toOrderHom

theorem awBack_injective (n : ℕ) (c : Fin (n + 1)) :
    Function.Injective (awBack n c).toOrderHom

theorem awFront_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (c.val + 1))).image (awFront n c).toOrderHom =
      Finset.univ.filter (· ≤ c)

theorem awBack_univ_image (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ : Finset (Fin (n - c.val + 1))).image (awBack n c).toOrderHom =
      Finset.univ.filter (c ≤ ·)

theorem awFront_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (· ≤ c)).card = c.val + 1

theorem awBack_filter_card (n : ℕ) (c : Fin (n + 1)) :
    (Finset.univ.filter (c ≤ ·)).card = n - c.val + 1

theorem standardTopEval_awFront {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y c.val (standardPullback (awFront n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (· ≤ c)) (-(c.val : ℤ))
        (AWIndex.left_nonempty (Finset.mem_univ c))
        (by rw [awFront_filter_card]; simp)

theorem standardTopEval_awBack {n : ℕ} (f : StandardSimplex R x y n)
    (c : Fin (n + 1)) :
    standardTopEval (R := R) x y (n - c.val) (standardPullback (awBack n c).toOrderHom f) =
      f.val.component (Finset.univ.filter (c ≤ ·)) (-((n - c.val : ℕ) : ℤ))
        (AWIndex.right_nonempty (Finset.mem_univ c))
        (by rw [awBack_filter_card]; simp)

theorem awTerm_univ_top_faces {x y z : D} {n : ℕ}
    (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) (c : Fin (n + 1)) :
    awTerm g.val f.val Finset.univ ⟨c, Finset.mem_univ c⟩ (-(n : ℤ)) (by simp) =
      compose R (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
        (standardTopEval (R := R) y z c.val (standardPullback (awFront n c).toOrderHom g))
        (standardTopEval (R := R) x y (n - c.val)
          (standardPullback (awBack n c).toOrderHom f))
        (by have := c.isLt; omega)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeAWStandardCutComparison`（76行）

```lean
theorem freeProductAW_standard_raw_value
    (φ : simplicialRingCoefficient.{u} →+* A) (W Y : SSet.{u}) (x y z : D)
    (g : W ⟶ standardHomSpace (R := A) y z)
    (f : Y ⟶ standardHomSpace (R := A) x y)
    (t : freeNegativeChains (A := A) W ⊗ freeNegativeChains (A := A) Y ⟶
      homObject A D x z) (n : ℕ)
    (w : W.obj (Opposite.op ⦋n⦌)) (a : Y.obj (Opposite.op ⦋n⦌))
    (hcut : ∀ c : Fin (n + 1),
      t.f (-(n : ℤ))
        (ιTensorObj (freeNegativeChains (A := A) W) (freeNegativeChains (A := A) Y)
          (-(c.val : ℤ)) (-((n - c.val : ℕ) : ℤ)) (-(n : ℤ))
          (by have := awDegrees n c; omega)
          (freeNegativeGenerator W c.val (W.map (awFront n c).op w) ⊗ₜ[A]
            freeNegativeGenerator Y (n - c.val) (Y.map (awBack n c).op a))) =
        compose A (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
          (standardTopEval (R := A) y z c.val
            (standardPullback (awFront n c).toOrderHom (g.app _ w)))
          (standardTopEval (R := A) x y (n - c.val)
            (standardPullback (awBack n c).toOrderHom (f.app _ a)))
          (by have := c.isLt; omega)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace W)
    let E := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) x y z
    t.f (-(n : ℤ))
      ((F.map (alexanderWhitneyApp (linearizedSpace W) (linearizedSpace Y) n ≫
        (chainIntegerTensorMap
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace W))
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C E)).extendXIso
          ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace W) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ W)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
        (coefficientUnit φ (integerTensor ((linearizedSpace W).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator w ⊗ₜ[ℤ] integerGenerator a))) =
      (((freeNegativeChainsAdjunction A).homEquiv (W ⊗ Y) (homObject A D x z)).symm
        (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
          (freeNegativeGenerator (W ⊗ Y) n (w, a))

```

### 127.2 検収と残り

コード **`bb6f33eb2`**（新規2本228行）。結合個別検査 `/private/tmp/isw2-aw-standard-cut-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build142.log` は **4,167 jobs・終了コード0**。新規分だけの監査 `/private/tmp/AuditISW2G10B02AWCuts.lean` は **16宣言（13・3）、標準三公理のみ**。鍵は返却済み。

累計 **261モジュール・16,026行・2,231宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtyone-modules.txt`。外枠まで残り3,974行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。B02、B03〜B08・C・Dは未完。

次は指定重み比較の逆射とMoore反転による前合成を、既存BK行のtensor合成則へ運ぶ。零延長した鎖複体の行表示の始域射自然性で同じ前合成を扱い、§120の実dg合成式を保持する。

## 128. 11-14のレーン目標と一覧の進捗表示

mainの `formalization-plans/stage-ii/lane-goals-2026-11-14.md` の共通規則と③-bを読み取り確認した。mainは凍結中でmergeしていない。B02〜B08、C01〜C07、D01〜D08を順に進め、B完了時にC・Dを再見積もり、B・C完了を停止点2a、D完了を停止点2bとする。2bの後に3b-4の段0（§38.2の1・2）を紙で出し、そこで止まる。既存FramedLimit*・CAlgUnderlyingDerivedComparison・無条件のcAlgForgetDerived_mapJoinCone_isLimitを再利用する。B4の指示が来たら先に従う。

一覧：済み 14／全体 36（うち追加 1）

数える単位は§73のA01〜A12（12項目）、B01〜B08（8）、C01〜C07（7）、D01〜D08（8）、承認追加A05a（1）。A01の二宣言など同じ親IDの複数の宣言は一つの項目にまとめる。A01〜A12とA05a、B01が済み。B02の途中の評価・自然性・合成・貼り合わせの法則と証明分割は分母にも分子にも加えない。B02〜B08・C・Dの22項目は未完。

外枠20,000行、実測16,026行（§127）、計算上限・既存宣言・⑤a・入口・公式監査・mainを変えない規則は維持する。次の対象ビルドから `--class impl --wait 3600` を明記する。

## 129. B02の途中：指定重みの始域射へBK合成則を運ぶ

一覧：済み 14／全体 36（うち追加 1）

零延長した鎖複体からの斉次射の行表示が、同じ始域射による前合成と可換であることを証明した。これにより元のBK行の合成則とtensor符号消去則を任意の指定重み始域射へ運べる。右辺の錐代表も同じ始域射を前合成したもので、別の錐や同値を選んでいない。B02の指定係数比較・Moore反転を通すための既存自然性・合成則で、ID付き一覧の追加ではない。

### 129.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ExtendedChainHomSourceMap`（28行）

```lean
theorem extendedChainHomRows_precomp (L K : ChainComplex C ℕ) (H : CochainComplex C ℤ)
    (σ : L.extend ComplexShape.embeddingDownNat ⟶ K.extend ComplexShape.embeddingDownNat)
    (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows L H q ((Cochain.ofHom σ).comp z (zero_add q)) n =
      (negativeChainRowIso L n).inv ≫ σ.f (-(n : ℤ)) ≫
        (negativeChainRowIso K n).hom ≫ extendedChainHomRows K H q z n

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSourceComposition`（65行）

```lean
theorem homToNormalizedBousfieldKan_rows_source_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows L ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n =
      ((n : ℤ) * p).negOnePow •
        (extendedChainHomRows L
          ((E).obj (doubleOppositeDiagram
            ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
          ((Cochain.ofHom σ).comp
            (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n ≫
          homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f)

theorem homToNormalizedBousfieldKan_tensor_source_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : (L.X n).obj j) :
    let η := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram
        ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
      ((Cochain.ofHom σ).comp
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n
    let χ := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega)

```

### 129.2 検収と残り

コード **`9c2a7c160`**（新規2本93行）。結合個別検査 `/private/tmp/isw2-bk-source-composition-combined2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build143.log` は **2,566 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02BKSourceComposition.lean` は **4宣言（1・3）、標準三公理のみ**。鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **263モジュール・16,119行・2,235宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtythree-modules.txt`。外枠まで残り3,881行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、rootビルド・大きな監査なし。未検証下書きはない。

B02の全体等式とB03〜B08・C・Dは未完。次はA12の実際の反転・係数重み移送のHom成分を、同じ二つの重み射の合成による前合成とAsSmall制限に明示的に分解する。

## 130. B02の途中：A12の実際の全次数の始域移送を評価

一覧：済み 14／全体 36（うち追加 1）

A12で使う `reflectedNormalizedBKSmallHomIso` の順射と `normalizedBKReverseHomotopyEquiv` の順射の全次数成分を、**同じ係数重み同型の逆射とMoore反転の合成によるcochain前合成**、続く指定 `AsSmall` 制限に厳密に同定した。別の同値を選んでいない。自由Moore重みの指定同型を前合成すると、その図式交換同型が相殺され、元の逆係数重み射だけが残る式も証明した。これにより§129のBK行の始域移送則へ渡す射が、実際のA12の射であることを明示できる。

元のHom対象の非公開な余積の別名をまたぐrewriteと自動合同変形では既定heartbeatに達したため、反転のHom成分を先に一つの等式に固定し、明示的な `congrArg` で前合成・AsSmall制限へ運ぶ証明に分割した。計算上限を上げていない。これらはB02内の既存構成の評価・合成則と同じ証明の分割で、ID付き一覧の追加ではない。

### 130.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomSourceCochainEvaluation`（48行）

```lean
theorem intervalHomPrePost_id_apply {P P' Q : CochainComplex C ℤ}
    (σ : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (intervalHomPrePost A σ (𝟙 Q)).f p z =
      (Cochain.ofHom σ).comp z (zero_add p)

theorem linearHomSourceIso_hom_apply {P P' : CochainComplex C ℤ}
    (e : P ≅ P') (Q : CochainComplex C ℤ) (p : ℤ) (z : Cochain P Q p) :
    (linearHomSourceIso A e Q).hom.f p z =
      (Cochain.ofHom e.inv).comp z (zero_add p) :=
  intervalHomPrePost_id_apply A e.inv p z

/-- 二つの閉零次始域射の前合成は同じ合成射の前合成。 -/
theorem zeroSourcePrecomp_comp {P P' P'' Q : CochainComplex C ℤ}
    (a : P'' ⟶ P') (b : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add p)) (zero_add p) =
      (Cochain.ofHom (a ≫ b)).comp z (zero_add p)

theorem zeroSourcePrecomp_comp {P P' P'' Q : CochainComplex C ℤ}
    (a : P'' ⟶ P') (b : P' ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp z (zero_add p)) (zero_add p) =
      (Cochain.ofHom (a ≫ b)).comp z (zero_add p)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKSourceEvaluation`（66行）

```lean
theorem reflectedNormalizedBKSmallHomIso_hom_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (reflectedNormalizedBKHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p z =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom (normalizedLinearWeightDiagramIso A V).inv).comp z (zero_add p))

theorem reflectedNormalizedBKSmallHomIso_reverse_apply (X : CosimplicialObject (Complex A))
    (p : ℤ) (z : (normalizedBousfieldKanHom X).X p) :
    (reflectedNormalizedBKSmallHomIso A X).hom.f p
      ((normalizedBKReverseHomotopyEquiv X).hom.f p z) =
      asSmallHomCochainEquiv A (SimplexCategoryᵒᵖᵒᵖ)
        ((E).obj (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})))
        ((E).obj (doubleOppositeDiagram X)) p
        ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A V).inv ≫
          extendMap (normalizedMooreReverse.app
            (linearizedSimplicialWeight A bousfieldKanSetWeight))
            ComplexShape.embeddingDownNat)).comp z (zero_add p))

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightInverseSource`（39行）

```lean
theorem freeLinearWeightDiagramIso_inverse_source :
    (freeLinearWeightDiagramIso A W).hom ≫ (normalizedLinearWeightDiagramIso A W).inv =
      (normalizedLinearWeightFreeIso A W.flip).inv

theorem freeLinearWeightDiagramIso_inverse_precomp
    {P Q : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (τ : (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ⟶ P) (p : ℤ) (z : Cochain P Q p) :
    (Cochain.ofHom (freeLinearWeightDiagramIso A W).hom).comp
      ((Cochain.ofHom ((normalizedLinearWeightDiagramIso A W).inv ≫ τ)).comp z
        (zero_add p)) (zero_add p) =
      (Cochain.ofHom ((normalizedLinearWeightFreeIso A W.flip).inv ≫ τ)).comp z
        (zero_add p)

```

### 130.2 検収と残り

コード **`d448f63e4`**（新規3本153行）。結合個別検査 `/private/tmp/isw2-reflected-bk-source-inverse-combined2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build144.log` は **4,540 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02ReflectedSource.lean` は **8宣言（3・2・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **266モジュール・16,272行・2,243宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtysix-modules.txt`。外枠20,000行まで残り3,728行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0、rootビルド・大きな監査なし。未検証下書きはない。

B02は引き続き未完。次は、今回明示した同じ始域射を§129の行合成則へ代入し、自由重みの点ごとのMoore・延長・図式交換を通して、§127の各切断条件を閉じる。パラメータ側は§126の実標準Hom最上位評価、実AW側は§127の前面・後面の式を使う。その後、raw成分等式を§125のMoore制限と§122の指定自由随伴・uncurryへ渡し、反転・添字輸送後の全単体的射のB02等式へ戻す。B03〜B08・C・Dは未完、3b-4段0はG10完成後に出す。

## 131. B02の途中：実A12の自由重みの任意の元でのtensor合成式

一覧：済み 14／全体 36（うち追加 1）

A12の実際の逆係数重み射とMoore反転を合成した同じ始域射を、§129のBK行の合成則へ代入した。指定自由重み同型の逆射で元を戻し、負次数項同型と自由重み同型の両逆を相殺することにより、**自由重みの任意の元**についてtensor符号が消えて元の錐代表との実dg合成となることを示した。したがってAW切断の射影自由生成元を直接代入できる。

閉零次cochainの点ごとの成分を異種等号で評価し、右辺を元の実複体射 `σ ≫ normalizedBousfieldKanConeRepresentative X` の成分に直した。さらに終次数を任意の `r`、条件 `p-n=r` で合わせた版を別名に置いた。型を弱めず、同じ自由重み成分式を分割したもの。

指定同型の両逆を直接使う計算を採用したため、点ごとのMoore比較を更に展開する補助ファイルは最終ソースに加えていない。成分の型移送とAW合成則への適用では、計算上限を上げず、対象・全次数を明記し、共通の閉零次成分評価と終次数の輸送を別宣言に分けて検査した。いずれも既存構成の評価・合成則または同じ証明の分割であり、ID付き項目の追加ではない。

### 131.1 登録対象・行数・型

`SerrePositivity.HomologicalAlgebra.ExtendedChainHomIsoEvaluation`（32行）

```lean
theorem extendedChainHomRows_iso_evaluation (L : ChainComplex C ℕ)
    (P H : CochainComplex C ℤ) (e : L.extend ComplexShape.embeddingDownNat ≅ P)
    (q : ℤ) (z : Cochain P H q) (n : ℕ) :
    e.inv.f (-(n : ℤ)) ≫ (negativeChainRowIso L n).hom ≫
      extendedChainHomRows L H q
        ((Cochain.ofHom e.hom).comp z (zero_add q)) n =
      z.v (-(n : ℤ)) (q - n) (by omega)

```

`SerrePositivity.HomologicalAlgebra.CochainOfHomPointEvaluation`（34行）

```lean
theorem cochainOfHom_v_app_heq {F G : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (i j : ℤ) (h : i + 0 = j) (k : J) (x : (F.X i).obj k) :
    HEq (((Cochain.ofHom a).v i j h).app k x) ((a.f i).app k x)

theorem cochainOfHom_comp_v_app_heq {F G H : CochainComplex (J ⥤ ModuleCat A) ℤ}
    (a : F ⟶ G) (b : G ⟶ H) (i j : ℤ) (h : i + 0 = j) (k : J)
    (x : (F.X i).obj k) :
    HEq ((((Cochain.ofHom a).comp (Cochain.ofHom b) (zero_add 0)).v i j h).app k x)
      (((a ≫ b).f i).app k x)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorRow`（134行）

```lean
theorem reflectedBKFreeHom_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let η := (Cochain.ofHom σ).comp
      (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        (((η.v (-(n : ℤ)) (0 - n) (by omega)).app j) w) f (by omega)

theorem reflectedBKFreeHom_tensor_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega)

theorem reflectedBKFreeHom_tensor_component_of_degree (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ) (r : ℤ) (hr : p - n = r)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) r (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega)

```

### 131.2 検収と残り

コード **`6d7d1217b`**（新規3本200行）。最終ソースの結合個別検査 `/private/tmp/isw2-reflected-bk-free-tensor-iso-combined5.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build145.log` は **4,563 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02FreeTensorRow.lean` は **13宣言（2・2・9）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **269モジュール・16,472行・2,256宣言**。一覧 `/private/tmp/isw2-g10-twohundredsixtynine-modules.txt`。外枠20,000行まで残り3,528行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02はまだ未完。次は元の `reversedWeightPointwiseBousfieldKanCone X` を、同じ自由鎖随伴による `σ ≫ r` の像に厳密に同定する。§108の `normalizedLinearWeightHomEquiv_freeDiagram` を元の錐代表に適用し、係数重み同型の両逆を相殺する。これにより今回の右辺を実標準Homの最上位成分へ合わせる。その後、パラメータ側の§126、各切断の§127と全切断和、§125のMoore制限、指定自由随伴・uncurryを通して、元のB02の全単体的射の等式へ戻す。B03〜B08・C・D、G10後の3b-4段0は未完。

## 132. B02の途中：元の反転BK錐入力の逆随伴と最上位成分

一覧：済み 14／全体 36（うち追加 1）

元の `reversedWeightPointwiseBousfieldKanCone X` が、指定係数重み同型の逆射と同じ反転錐代表の自由鎖随伴像であることを、既存の全図式の線形重みHom比較から証明した。自由随伴で逆に戻すと、同じ `σ ≫ normalizedBousfieldKanConeRepresentative X` の像となり、各点・各複体次数で実代表の成分に一致する。さらに元の反転錐入力を同じ標準DK同型で実標準Homへ戻した最上位成分を、同じ実代表の射影自由生成元の像に同定した。全次数（零次数を含む）の式で、錐入力・DK同型を選び直していない。

パラメータ側では、指定持ち上げ標準単体Hom評価の後合成自然性とYonedaパラメータの単位評価を証明した。同じ元の射の全単体の像をそのまま与える。いずれもB02の既存構成の評価・自然性・合成則または同じ証明の分割で、ID付き項目の追加ではない。

### 132.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeAdjunction`（113行）

```lean
theorem reversedWeightPointwiseBousfieldKanCone_freeAdjunction
    (X : CosimplicialObject (Complex A)) :
    reversedWeightPointwiseBousfieldKanCone X =
      (freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
        (V ⋙ SSet.uliftFunctor.{u,0})
        (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))
        ((functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
            (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
          complexOfFunctorsToFunctorToComplex.map
            ((normalizedLinearWeightDiagramIso A V).inv ≫
              reflectedBousfieldKanConeRepresentative X))

theorem reflectedBousfieldKanConeRepresentative_source (X : CosimplicialObject (Complex A)) :
    reflectedBousfieldKanConeRepresentative X =
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ normalizedBousfieldKanConeRepresentative X

theorem reversedWeightPointwiseBousfieldKanCone_free_inverse
    (X : CosimplicialObject (Complex A)) :
    ((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X) =
      (functorComplexExchangeUnitIso (SimplexCategoryᵒᵖᵒᵖ) (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map
          (((normalizedLinearWeightDiagramIso A V).inv ≫
            extendMap (normalizedMooreReverse.app
              (linearizedSimplicialWeight A bousfieldKanSetWeight))
                ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X)

theorem reversedWeightPointwiseBousfieldKanCone_free_inverse_app_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    ((((freeNegativeChainsDiagramAdjunction A (SimplexCategoryᵒᵖᵒᵖ)).homEquiv
      (V ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X))).symm
      (reversedWeightPointwiseBousfieldKanCone X)).app j).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j

theorem freeNegativeChainsDiagramAdjunction_symm_app {J : Type*} [Category* J]
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : W ⟶ Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) (j : J) :
    (((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q).symm f).app j =
      ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm (f.app j)

theorem reversedWeightPointwiseBousfieldKanCone_point_inverse_f
    (X : CosimplicialObject (Complex A)) (j : SimplexCategoryᵒᵖᵒᵖ) (i : ℤ) :
    (((freeNegativeChainsAdjunction A).homEquiv
      ((V ⋙ SSet.uliftFunctor.{u,0}).obj j)
      ((complexOfFunctorsToFunctorToComplex.obj (bousfieldKanConeHomDiagram X)).obj j)).symm
      ((reversedWeightPointwiseBousfieldKanCone X).app j)).f i =
      ((((normalizedLinearWeightDiagramIso A V).inv ≫
        extendMap (normalizedMooreReverse.app
          (linearizedSimplicialWeight A bousfieldKanSetWeight)) ComplexShape.embeddingDownNat) ≫
          normalizedBousfieldKanConeRepresentative X).f i).app j

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation`（59行）

```lean
theorem reflectedBKFreeCone_generator_top (X : CosimplicialObject (Complex A))
    (j : SimplexCategoryᵒᵖᵒᵖ) (n : ℕ)
    (s : ((V ⋙ SSet.uliftFunctor.{u,0}).obj j).obj (Opposite.op ⦋n⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj j
    let g := (reversedWeightPointwiseBousfieldKanCone X).app j ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    (((((normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f
          (-(n : ℤ))).app j) (freeNegativeGenerator ((V ⋙ SSet.uliftFunctor.{u,0}).obj j) n s) =
      standardTopEval (R := A) T Q n (g.app _ s)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LiftedStandardSimplexParameterEvaluation`（48行）

```lean
theorem liftedStandardSimplexHomIso_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory)
    (t : (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n) ⟶ Z) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n) (t ≫ f) =
      f.app (Opposite.op n) ((liftedStandardSimplexHomIso Z).hom.app (Opposite.op n) t)

theorem liftedStandardSimplexHomIso_yoneda_apply (Z : SSet.{u}) (n : SimplexCategory)
    (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z).hom.app (Opposite.op n)
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) = α

theorem liftedStandardSimplexHomIso_yoneda_postcomp {Z Z' : SSet.{u}} (f : Z ⟶ Z')
    (n : SimplexCategory) (α : Z.obj (Opposite.op n)) :
    (liftedStandardSimplexHomIso Z').hom.app (Opposite.op n)
      ((liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm α) ≫ f) =
        f.app (Opposite.op n) α

```

### 132.2 検収と残り

コード **`c5cb92cb3`**（新規3本220行）。錐の結合個別検査 `/private/tmp/isw2-reflected-bk-cone-top-combined2.log`、パラメータの個別検査 `/private/tmp/isw2-lifted-simplex-parameter2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build146.log` は **4,695 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02FreeConeTop.lean` は **10宣言（6・1・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **272モジュール・16,692行・2,266宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventytwo-modules.txt`。外枠まで残り3,308行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02の最終等式とB03〜B08・C・D、G10後の3b-4段0は未完。次はA09の実際のtensor逆射の成分へ、§131の実A12の成分式をAsSmall制限とともに代入する。錐側の今回の最上位評価とパラメータ側の§126・今回のYoneda評価を合わせ、§127の各切断条件と全切断和へ進む。

## 133. B02の途中：実A09 tensor逆射とA12の像の成分

一覧：済み 14／全体 36（うち追加 1）

A09の指定 `freeTensorDiagramHomIso` の逆射へ、実際のHom–Tot比較・Moore反転・指定自由重みHom同型を合成したA12の複体射のΓ像を入れた。全標準単体パラメータ、任意の自由重みの元、任意のパラメータ次数について、そのtensor成分が元の `σ ≫ normalizedBousfieldKanConeRepresentative X` とパラメータcochainの実dg合成になることを証明した。逆転置の符号、AsSmall制限、指定始域射は元のものを保持している。切断条件を仮定していない。

これはB02内の指定射の成分照合で、既存構成の評価・自然性・合成則を合わせた証明分割であり、ID付き項目の追加ではない。

### 133.1 登録対象・型

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorComparison`（90行）

```lean
theorem reflectedBKFreeTensor_inverse_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : ((truncatedDoldKanFunctor A).obj
      (homComplex A P ((productTotalFunctor A).obj X))).obj (Opposite.op m))
    (n : ℕ) (p r : ℤ) (hr : p - n = r)
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ))
    (w : ((freeNegativeChainsDiagram (A := A)
      (reflectedNormalizedBKSmallWeight A)).obj j).X (-(n : ℤ)))
    (x : ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj m)).X p) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m) α)
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    (t.app j).f r (ιTensorObj
      ((freeNegativeChainsDiagram (A := A) (reflectedNormalizedBKSmallWeight A)).obj j)
      ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
        (SSet.stdSimplex.obj m)) (-(n : ℤ)) p r (by omega) (w ⊗ₜ[A] x)) =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj (AsSmall.down.obj j))
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app
          (AsSmall.down.obj j)) w)
        (((normalizedSimplexHomEquiv A (homComplex A P ((productTotalFunctor A).obj X)) m).symm
          α).f p x) (by omega)
```

### 133.2 検収と残り

コード **`00c9e5357`**（1本90行）。個別検査 `/private/tmp/isw2-reflected-bk-free-tensor-comparison2.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build147.log` は **4,573 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02TensorComparison.lean` は **3宣言・標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **273モジュール・16,782行・2,269宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventythree-modules.txt`。外枠まで残り3,218行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

次は自由生成元の前面・後面をこの式に代入し、§132の錐の最上位評価、§126・§132のパラメータ評価、§127のAW各切断成分を合わせる。B02の全体等式とB03〜B08・C・D、G10後の3b-4段0は未完。

## 134. B02の途中：実比較射のAW各切断条件を無条件に閉じる

一覧：済み 14／全体 36（うち追加 1）

元の実標準Hom単体のDK像をA12の指定複体射のΓ像へ送り、A09の実tensor逆射で戻したものについて、**任意の切断点の前面・後面の射影自由生成元の値が、同じ実標準AWの切断項に一致**することを証明した。重みの全単体、元の実標準Homの全標準単体パラメータ、全切断点を含み、切断条件を仮定していない。

実標準Homへの元の射の自然性を前面・後面で評価する法則と、元の実標準Hom単体のDK像の逆正規化Hom同値を全生成元で評価する法則に分割した。§133の無条件のtensor成分、§132の錐の最上位成分、§127の標準AW切断の式を合成して、以前の貼り合わせ則の各切断条件を今回の実射について閉じた。既存構成の評価・自然性・合成則または同じ証明の分割で、ID付き項目の追加ではない。

### 134.1 登録対象・行数・型

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality`（29行）

```lean
theorem standardHomParameter_map {S : SSet.{u}}
    (f : S ⟶ standardHomSpace (R := A) x y) {m n : SimplexCategory}
    (θ : m ⟶ n) (s : S.obj (Opposite.op n)) :
    f.app (Opposite.op m) (S.map θ.op s) =
      standardPullback θ.toOrderHom (f.app (Opposite.op n) s)

```

`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation`（42行）

```lean
theorem normalizedSimplexHomEquiv_native_generator (x y : D) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) x y).obj (Opposite.op m)) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋n⦌)) :
    ((normalizedSimplexHomEquiv A (homObject A D x y) m).symm
      ((standardDoldKanSpaceMap x y).app (Opposite.op m) α)).f (-(n : ℤ))
        (freeNegativeGenerator
          ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) n s) =
      standardTopEval (R := A) x y n
        (((liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α).app
          (Opposite.op ⦋n⦌)) s)

```

`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorCut`（85行）

```lean
theorem reflectedBKFreeTensor_inverse_cut (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (N : ℕ) (c : Fin (N + 1))
    (s : ((reflectedNormalizedBKSmallWeight A).obj j).obj (Opposite.op ⦋N⦌))
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋N⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let S := (reflectedNormalizedBKSmallWeight A).obj j
    let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    (t.app j).f (-(N : ℤ)) (ιTensorObj (freeNegativeChains (A := A) S)
      (freeNegativeChains (A := A) B) (-(c.val : ℤ)) (-((N - c.val : ℕ) : ℤ)) (-(N : ℤ))
      (by have := awDegrees N c; omega)
      (freeNegativeGenerator S c.val (S.map (awFront N c).op s) ⊗ₜ[A]
        freeNegativeGenerator B (N - c.val) (B.map (awBack N c).op a))) =
      awTerm (g.app _ s).val (f.app _ a).val Finset.univ ⟨c, Finset.mem_univ c⟩
        (-(N : ℤ)) (by simp)

```

### 134.2 検収と残り

コード **`f39770010`**（新規3本156行）。結合個別検査 `/private/tmp/isw2-reflected-bk-cut-combined.log` は終了コード0。鍵付き対象ビルド `/private/tmp/isw2-build148.log` は **4,725 jobs・終了コード0**。新規分のみの監査 `/private/tmp/AuditISW2G10B02TensorCut.lean` は **5宣言（1・1・3）、標準三公理のみ**。共有鍵は `--class impl --wait 3600` でビルド・監査の間だけ使用し返却済み。

累計 **276モジュール・16,938行・2,274宣言**。一覧 `/private/tmp/isw2-g10-twohundredseventysix-modules.txt`。外枠まで残り3,062行。計算上限・既存宣言・⑤a・入口・公式監査・mainの変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証下書きはない。

B02の全体等式は引き続き未完。残る主接続は、各切断の有限和をraw係数写像の等式にまとめ、係数移送した積の自由化比較が同じMoore射影生成元を保つ式を使って、§125のMoore包含による制限へ渡すこと。その後に同じ自由随伴・uncurryで全単体的射を戻し、反転・添字の指定輸送を合わせる。B03〜B08・C・DとG10後の3b-4段0は未完。


## 135. B4前の係数単位・積のMoore射影の照合（2026-11-14）

一覧：済み 14／全体 36（うち追加 1）

B02の係数移送の法則と証明分割。新しい数学・構成の追加なし。指定された正のMoore次数を保ち、同じ積の自由化同型が射影生成元を送る式を確認する。

### 135.1 `CoefficientUnitNaturality`（52行）

```lean
theorem coefficientUnit_map_value {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) (x : M) :
    (integerCoefficientExtension φ).map f (coefficientUnit φ M x) =
      coefficientUnit φ N (f x)

theorem coefficientUnit_hom_ext (M : ModuleCat.{u} ℤ) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj M ⟶ N)
    (h : ∀ x : M, f (coefficientUnit φ M x) = g (coefficientUnit φ M x)) : f = g

theorem coefficientUnit_integerTensor_hom_ext (X Y : Type u) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj
      (integerTensor (integerLinearization.obj X) (integerLinearization.obj Y)) ⟶ N)
    (h : ∀ x y, f (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      g (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))) : f = g

```

### 135.2 `ProductChainsCoefficientProjection`（126行）

```lean
theorem productChainsCoefficient_projection (X Y : SSet.{u}) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex S) ≫
      normalizedMooreMapHom F S ≫ (normalizedMooreComplex (ModuleCat A)).map e.hom =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app S ≫
        (alternatingFaceMapComplex (ModuleCat A)).map e.hom ≫
          PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)

theorem productChainsCoefficient_degree (X Y : SSet.{u}) (r : ℕ) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    F.map ((PInftyToNormalizedMooreComplex S).f r) ≫ (normalizedMooreMapHom F S).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv ≫
      (integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)) =
      e.hom.app (Opposite.op ⦋r⦌) ≫
        (PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)).f r ≫
        (((normalizedMooreComplex (ModuleCat A)).obj ((X ⊗ Y) ⋙ ModuleCat.free A)).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv

theorem productChainsCoefficient_simplicial_generator (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    e.hom.app (Opposite.op ⦋r⦌)
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
          (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) = ModuleCat.freeMk (x, y)

theorem productChainsCoefficient_generator_value (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    ((integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)))
      ((((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((normalizedMooreMapHom F S).f r
            (F.map ((PInftyToNormalizedMooreComplex S).f r)
              (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
                ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
                  (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))))) =
      freeNegativeGenerator (X ⊗ Y) r (x, y)

```

### 135.3 検収

コード `76453fce1`。鍵付き対象ビルド149は4,015 jobs・終了コード0。新規分だけの監査は7宣言（3・4）、標準三公理のみ。累計278モジュール・17,116行・2,281宣言。個別結合検査も警告のみで完了。計算上限の変更、sorry・新公理、既存宣言の変更なし。B02は未完。B4の指示を優先し、原ソースを保存して改名前の参照採取に移る。


## 136. B4：採取後の open 方針の保留で停止（2026-11-14 昼）

一覧：済み 14／全体 36（うち追加 1）

### 136.1 固定した原ソースと採取

B4の指示を優先。検証済み2本を `76453fce1`、型・検収を `b4916a73d` にコミットしてから、mainを取り込む前の自worktreeで参照を採取した。基準 `c5c4436c0` 以後の追加・変更Lean（drafts除外）は **278本**。作業木はクリーンで、未検証Lean下書きなし。原ソースを `/private/tmp/isw2-b4/original-sources.tar.gz`、対象全体を同ディレクトリの `files.json` に保存した。

mainの `bulk_namespace.py collect/rewrite` と B3配布表を使った。鍵は `--class impl --wait 3600`、各採取組は `gtimeout --kill-after=3s 280` で制限。最初の8本ずつ二組、その後は独立した8本ずつ四組を一つの鍵の中で採取。索引と原ソースの全バイト一致の検査を維持。整理券は常に一つ。採取順だけを入れ替え、全278本の集合が一致することを検査した。

**48本の採取が完了**（`before-00`〜`before-05`、全て `files.json` あり）。プレビューは最初の二組16本が保留0・ソース差分0。その次の8本のプレビューで下記1件の保留が出たため、ドライバは終了コード1で停止した。後続の採取や残りのプレビューには進んでいない。鍵は返却済み。最初の逐次ドライバは二組目の採取完了後、停止状態から終了して組単位のドライバに切り替えた。このドライバ切り替えの終了137と、保留による終了1は区別している。

### 136.2 保留の内容

対象：`SerrePositivity/InfinityCategories/Project/DerivedCategories/DiagramComparison/DiagramTensorDoldKan.lean` **20行**（UTF-8 byte 1131〜1215）。

```lean
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
```

`review.json` の理由：

```text
explicit opens policy needed for a renamed namespace
```

採取したopenは単純open、解決先は上記と同じ完全名の一つ。配布表の全体 `opens` およびこのモジュールの `module_opens` には、この名前の方針がない。一方、配布表には既存モジュール `SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStandardHom` に限った同じopenを同名のまま保つ方針が既にある。新規利用側へ同じ方針を使ってよいかを自分で推定せず、指示どおり停止した。共有の道具・配布表・Leanソースの手修正はしていない。

再現資料を `formalization-plans/stage-ii/is-w2-b4-20261114/` に保存した：対象全体 `files.json`、保留 `review.json`、該当ファイルの採取元込み索引 `blocked-before-index.json.gz`、固定コミット・件数・配布表ハッシュ等 `summary.json`。他の索引・プレビュー・各採取ログは `/private/tmp/isw2-b4/` に保持している。

### 136.3 再開条件と現在地

**main未取り込み、プレビュー未反映、B4未完了**。指示の「保留が出たら止まって報告」に従い、B4後の対象ビルド・監査はまだ実行していない。原ソースは `b4916a73d` のまま。修正版のopen方針／道具を受け取ったら、同じ移動前ソースとその索引で再プレビューし、未採取分を採取する。保留0と差分確認の後に mainを取り込み、importをmodule-mapで追従し、自分の新規モジュールの対象ビルド・小さい監査を行う。

G10はB02未完、B03〜B08・C・Dも未完。累計278モジュール・17,116行・2,281宣言、外枠まで2,884行。B4が済んだ後に /goal を再開する。B4で計算上限・型・既存宣言・⑤a・入口・公式監査・mainの変更なし。新たなLean数学・構成の追加なし。


## 137. B4完了：承認された恒等open、main取り込み、対象ビルド・小さい監査（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

### 137.1 open の承認と全体照合

調整役の11-14午後の指示（citation-attributes.md §14追記）に従い、二つの確認済み名前空間 `…Project.HomotopyDiagramComparison.CosimplicialHom` と `…Project.DerivedCategories.DiagramComparison` のopenを同名のまま保持した。配布された元の表は保存し、一時の表の `opens` に承認された二つの恒等方針だけを追加した。共有の道具・配布表の変更なし。再プレビューで§136の保留を解消した。

main取り込み前の同じ枝ソースで、**全278本**（drafts除外）の参照採取・原ソースの全バイト一致検査・rewriteを完了。各回は `--class impl --wait 3600` と280秒の上限、一つの整理券。独立した8本ずつ四つの小組を一つの鍵の中で採取し、全ての小組が終了するのを待ってから次へ進めた。索引の漏れ・重複なし、全reviewは**保留0**。通常importの全トークンをmodule-mapと照合し、一致を確認した。

### 137.2 差分と取り込み

プレビュー差分は**7ファイル、7行の追加・7行の削除**、全てimport先の変更。宣言名・型・証明・openのソースは変更していない。

| ファイルの末尾 | importの移動先 |
| --- | --- |
| DoldKanClosedPostcomposition | MappingAndStability/HomSpaces/DGStandardClosedPostcomposition |
| ReflectedNormalizedBKSmallSections | WeightedCones/WeightedSectionsOpposite |
| IntegerCoefficientFree | Tensor/DGSimplicialRingCoefficientComplex |
| IntegerCoefficientTensorDegrees | Tensor/DGIntegerCoefficientTensor |
| IntegerCoefficientTensorValues | Tensor/DGIntegerCoefficientTensor |
| ProductSectionsHom | MappingSpaces/UniverseJoinSimplexShapes |
| TruncatedDoldKanQuasiIso | LocalizationAndRoofs/PinchedChainMapQuasiIso |

main **`2be485f04`** を枝に取り込んだ（merge **`8c65d0319`**、競合なし）。取り込み前に確定した差分だけを `git apply -p0` で反映し、取り込み後の278本全てが取り込み前の最終プレビューと一致することを検査した。取り込み後のソースへの古い索引の流用なし。`git diff --check` も成功。

### 137.3 検収と受け渡し

コード **`93227d091`**。自分の278モジュールを全て指定した鍵付き対象ビルドは **6,570 jobs・終了コード0**。新規モジュールだけを40本ずつ選ぶ小さい監査7組は **[321, 334, 298, 310, 379, 297, 180]、計2,119宣言、全て標準三公理のみ・終了コード0**。rootビルド・公式監査の変更／実行なし。鍵はビルドと監査の間だけ使用し返却済み。

今回の2,119は、同じ全278本を分割して選んだ現在の監査の実測である。既報2,281は逐次の小監査の報告値を加算した累計であり、今回の値とは区別して記録する。278本の集合は従来のG10一覧と完全一致し、ソースはimport7行以外変えていない。過去の加算値との差の原因は今回の検査だけからは確定していない。以後の現在値には今回の全対象の実測を用いる。

証跡は `formalization-plans/stage-ii/is-w2-b4-20261114/`：`approved-identity-opens.json`、`final-review.json`、`final-preview-summary.json`、`applied-preview.diff`、`build-and-audit.log.gz`、更新した `summary.json`。原ソース付きの索引全体と各採取ログは `/private/tmp/isw2-b4/` に保持。登録の照合用の全278モジュールは同フォルダの `files.json`（パスの拡張子を取り、スラッシュをピリオドに置換）である。入口・登録は調整役に委ねる。

**B4は完了**。累計278モジュール・17,116行、外枠まで2,884行。sorry・新公理0、計算上限・型の弱化・ModelCategory SSetの追加・⑤aの変更なし。/goalのB02の残り（raw有限和からMoore制限と全単体的射への接続）に戻る。B03〜B08・C・D、停止点2a・2b、3b-4段0は未完。


## 138. B02：実AW前合成と全標準単体のuncurryの照合（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

B4完了後に /goal を再開。同じraw生成元、Moore射影、指定係数同型を通して、実A09逆射のAW前合成を元の実豊穣合成の逆自由随伴そのものへ同定した。さらに同じ自由随伴とuncurryで、全標準単体パラメータの各添字成分を元の豊穣合成へ戻した。各切断の照合を仮定には残さず、§134の実際の切断等式を代入している。

今回の6宣言はB02の既存構成の法則と証明分割であり、新しい構成・新しい数学の追加ではない。逆射の値の検査は、同じ同型の順方向の全射性で値を表し、順方向uncurry則から戻す形に分割した。elaboration・kernelとも既定の計算上限を維持した。

### 138.1 `FreeProductAWRawCriterion`（81行）

```lean
theorem freeProductAlexanderWhitney_f_eq_of_raw (X Y : SSet.{u}) (n : ℕ)
    (T : ModuleCat A)
    (t : (freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y).X
      (-(n : ℤ)) ⟶ T)
    (h : (freeNegativeChains (A := A) (X ⊗ Y)).X (-(n : ℤ)) ⟶ T)
    (hraw : ∀ x : X.obj (Opposite.op ⦋n⦌), ∀ y : Y.obj (Opposite.op ⦋n⦌),
      ((integerCoefficientExtension φ).map
        ((alexanderWhitney (linearizedSpace X) (linearizedSpace Y)).f n ≫
          (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace X))
            (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)))).extendXIso
              ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ X)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)) ≫ t)
        (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      h (freeNegativeGenerator (X ⊗ Y) n (x, y))) :
    (freeProductAlexanderWhitney φ X Y).f (-(n : ℤ)) ≫ t = h

```

### 138.2 `ReflectedBKFreeTensorAW`（94行）

```lean
theorem reflectedBKFreeTensor_inverse_AW
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let S := (reflectedNormalizedBKSmallWeight A).obj j
    let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    freeProductAlexanderWhitney φ S B ≫ t.app j =
      ((freeNegativeChainsAdjunction A).homEquiv (S ⊗ B) (homObject A (Complex A) P Q)).symm
        ((g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
          standardDoldKanSpaceMap P Q)

```

### 138.3 `NormalizedWeightSectionInverseEvaluation`（81行）

```lean
theorem freeNegativeChainsDiagramAdjunction_hom_symm_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (f : freeNegativeChainsDiagram (A := A) W ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv (W.obj j) (Q.obj j)).symm
      ((((freeNegativeChainsDiagramAdjunction A J).homEquiv W Q) f).app j) = f.app j

theorem normalizedWeightSectionMap_hom_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj m ⟶ Q) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m)
            ((freeTensorDiagramHomIso A Q W).hom.app (Opposite.op m) f)))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫ f.app j

theorem normalizedWeightSectionMap_uncurry_inverse_app
    (W : J ⥤ SSet.{u}) (Q : J ⥤ Complex A)
    (φ : simplicialRingCoefficient.{u} →+* A) (m : SimplexCategory)
    (β : ((truncatedDoldKanFunctor A).obj (linearHomComplex A
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) W))
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj Q))).obj (Opposite.op m)) (j : J) :
    ((freeNegativeChainsAdjunction A).homEquiv
      (W.obj j ⊗ (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) (Q.obj j)).symm
      ((weightedSectionsUncurry
        (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
          ((normalizedWeightSectionMap A W Q φ).app (Opposite.op m) β))).app j) =
    freeProductAlexanderWhitney φ (W.obj j)
      ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)) ≫
        ((freeTensorDiagramHomIso A Q W).inv.app (Opposite.op m) β).app j

```

### 138.4 `ReflectedBKNormalizedSectionsUncurry`（76行）

```lean
theorem reflectedBKNormalizedSections_uncurry
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    (weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) φ).app (Opposite.op m)
            (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
              ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))))).app j =
      (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) P T Q ≫
        standardDoldKanSpaceMap P Q

```

### 138.5 検収と残り

コード **`c6df9240b`**。個別の結合検査 `/private/tmp/isw2-reflected-uncurry-combined7.log` は終了コード0。不要な未使用letを除いた最終4モジュールの鍵付き対象ビルド `/private/tmp/isw2-build150.log` は **4,740 jobs・終了コード0**。新規分のみの監査は **6宣言（1・1・3・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **282モジュール・17,448行**、外枠まで2,552行。現在の全対象監査の基準は§137の278本・2,119宣言で、今回の新規分監査6宣言とは区別して記録する。モジュール一覧 `/private/tmp/isw2-g10-twohundredeightytwo-modules.txt`。計算上限・既存宣言・⑤a・入口・公式監査の変更なし。sorry・新公理0。rootビルド・大きな監査なし。未検証の下書きなし。

B02全体の `gammaReflectedBKComparison_eq` はまだ未完。残りは、今回の全標準単体・各添字のuncurry等式を重み付き切断の全射の等式に戻し、元の反転end・small添字の指定同型・実Hom同型を通して同じnative比較へ運ぶこと。B03〜B08・C・D、停止点2a・2b、3b-4段0も未完。次はこの反転・添字の輸送を接続する。


## 139. B02：全uncurry、指定反転end・small添字の評価と因数分解（2026-11-14 午後）

一覧：済み 14／全体 36（うち追加 1）

§138の全標準単体の式を、持ち上げた恒等単体で評価して元のuncurry全体の各成分の等式へ戻した。反転endについては既存の内部Hom反転評価、small添字については既存のend射影の制限則を使い、同じuncurryが指定の反転・制限を保つ式を得た。元の `gammaReflectedBKComparison` も、既存の因数分解と関手の合成則で同じ反転・AW・添字同型・実Hom同型の合成へ括り直した。新しい構成や数学の追加はなく、全てB02の既存構成の法則・証明分割。

### 139.1 `WeightedSectionsReflectionEvaluation`（50行）

```lean
theorem weightedSectionsOppositeIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsOppositeIso W H).hom)).app i =
    (opTensorIso (W.obj i) S).hom ≫ SSet.opFunctor.map ((weightedSectionsUncurry f).app i)

theorem weightedSectionsReflectedIso_uncurry (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections (W ⋙ SSet.opFunctor) H) (i : I) :
    (weightedSectionsUncurry
      (SSet.opFunctor.map f ≫ (weightedSectionsReflectedIso W H).hom)).app i =
    ((diagramDoubleOppositeIso W).inv.app i ▷ S.op) ≫
      (opTensorIso ((W ⋙ SSet.opFunctor).obj i) S).hom ≫
        SSet.opFunctor.map ((weightedSectionsUncurry f).app i)

```

### 139.2 `SmallBKIndexSectionsEvaluation`（29行）

```lean
theorem smallBKIndexSectionsMap_uncurry {I J : Type u} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ I) (W H : I ⥤ SSet.{u}) {S : SSet.{u}}
    (f : S ⟶ weightedSections W H) (j : J) :
    (weightedSectionsUncurry (f ≫ smallBKIndexSectionsMap F W H)).app j =
      (weightedSectionsUncurry f).app (F.obj j)

```

### 139.3 `ReflectedBKNormalizedSectionsMapEvaluation`（93行）

```lean
theorem reflectedBKNormalizedSections_uncurry_map
    (φ : simplicialRingCoefficient.{u} →+* A) (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P T ≫ (truncatedDoldKanFunctor A).map γ ≫
      normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A Y) φ
    (weightedSectionsUncurry ψ).app j =
      (g ⊗ₘ 𝟙 (standardHomSpace (R := A) P T)) ≫ (β_ _ _).hom ≫
        standardComposition (R := A) P T Q ≫ standardDoldKanSpaceMap P Q

```

### 139.4 `GammaReflectedBKComparisonFactor`（48行）

```lean
theorem gammaReflectedBKComparison_factor (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let ψ := standardDoldKanSpaceMap P ((productTotalFunctor A).obj X) ≫
      (truncatedDoldKanFunctor A).map γ ≫
        normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y) (normalizedBKCoefficientMap A)
    gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P) =
      SSet.opFunctor.map ψ ≫
        (weightedSectionsReflectedIso (normalizedBKSmallWeight A)
          (normalizedBKSmallDiagram A Y ⋙ truncatedDoldKanFunctor A) ≪≫
            normalizedBKOriginalSectionsIso A Y).hom ≫
        (weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).map
          (normalizedBKReflectedHomDiagramIso X P).hom

```

### 139.5 検収と残り

コード **`bded7fe66`**。反転評価は、今回初めて読むB3移動済みの依存の古いキャッシュを更新した対象ビルド151で検査した（1,615 jobs、監査2宣言・標準三公理のみ、終了コード0）。small添字、全uncurry、因数分解もそれぞれ個別検査が終了コード0。その最終4本をまとめた鍵付き対象ビルド `/private/tmp/isw2-build152.log` は **6,548 jobs・終了コード0**、新規分だけの監査は **9宣言（2・1・1・5）、標準三公理のみ**。鍵は `--class impl --wait 3600`、検証の間だけ使用し返却済み。

累計 **286モジュール・17,668行**、外枠まで2,332行。一覧 `/private/tmp/isw2-g10-twohundredeightysix-modules.txt`。sorry・新公理0。計算上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B02の全体等式はまだ未完。今回の評価則と因数分解を通して、元の `reflectedWeightedHomFamily` の同じ成分へ照合する最後の接続を進める。B03〜B08・C・D、停止点2a・2b、3b-4段0は未完。


## 140. B02・B03完了：元の全比較射の等式と同じ射の同値性（2026-11-14 午後）

一覧：済み 16／全体 36（うち追加 1）

型つき一覧B02 `gammaReflectedBKComparison_eq` とB03 `reflectedBKComparison_equivalence` を、§73.2の元の型のまま証明した。全試験対象・全単体・元のTot頂点・同じnative錐入力を保つ。B02では指定反転endとsmall添字の評価を通して実際の `reflectedWeightedHomFamily` そのものに一致させ、切断の普遍性で全射の等式へ戻した。B03はその等式へ既存のΓ比較の同値性を代入した。別の同値な空間／別の射への置換はしていない。

native成分の最後の照合は、実Hom同型の両逆則を先に射の段階で消去し、残った元の錐入力の成分を定義で照合する形に分割した。計算上限・再帰上限は変更していない。前提の追加、ModelCategory SSetの追加、新しい構成／数学の追加なし。

### 140.1 `GammaReflectedBKComparisonUncurry`（70行）

```lean
theorem gammaReflectedBKComparison_uncurry (P : Complex A)
    (X : CosimplicialObject (Complex A)) (j : AsSmall.{u} SimplexCategory) :
    (weightedSectionsUncurry
      (gammaReflectedBKComparison X (ForgetEnrichment.of (Complex A) P))).app j =
    (reflectedWeightedHomFamily (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (liftedEnrichedBousfieldKanCone X) (ForgetEnrichment.of (Complex A) P)).app j

```

### 140.2 `GammaReflectedBKComparisonEquality`（52行）

```lean
theorem gammaReflectedBKComparison_eq (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    gammaReflectedBKComparison X x =
      reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x

theorem reflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x)

```

### 140.3 検収と残り

コード **`b74819308`**。結合個別検査 `/private/tmp/isw2-gamma-equality-combined.log` は終了コード0。最終2本の鍵付き対象ビルド `/private/tmp/isw2-build153.log` は **6,551 jobs・終了コード0**。新規分のみの監査は **3宣言（1・2）、標準三公理のみ**。鍵は `--class impl --wait 3600`、検証中のみ使用し返却済み。

累計 **288モジュール・17,790行**、外枠まで2,210行。一覧 `/private/tmp/isw2-g10-twohundredeightyeight-modules.txt`。sorry・新公理0。既存宣言・⑤a・入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

A01〜A12・A05a・B01〜B03が完了。B04〜B08（指定native切断の族、同じ頂点／制限の照合、極限性）へ進む。Bの残りが済んだ時点で指示どおりC・Dを再見積もりする。C01〜C07・D01〜D08、停止点2a・2b、3b-4段0は未完。これはG10全体の完成報告ではない。


## 141. B04・B05完了：元のTot錐全体上の全Homの族と指定頂点評価（2026-11-14 午後）

一覧：済み 18／全体 36（うち追加 1）

B04の `nativeTotConeFamilyLift` は、元の `nativeCoherentCone X` 全体上の標準coslice切断から、既存の `coherentConeSourceFamily` により構成した。B05の頂点評価は既存の同じ族の評価則へ特殊化し、元の `nativeCoherentCone_vertex X` で正規化した。元の錐・頂点・全Homパラメータ・高次単体を保つ、型つき一覧B04・B05の実装である。制限の式B06は引き続き別に照合する。

### 141.1 型（`NativeTotConeFamilyLift`、47行）

```lean
def nativeTotConeFamilyLift (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
        coherentConeSectionSpace (nativeCoherentCone X).val (coherentNerveVertex x)

theorem nativeTotConeFamilyLift_apex (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫ coherentConeApexEvaluation (nativeCoherentCone X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeCoherentCone_vertex X) x =
    coherentCosliceFiberComparison x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))

```

### 141.2 検収と残り

コード **81185bce8**。今回初めて使う既存 `CoherentConeSourceApex` のoleanが未作成だったため、依存を含む鍵付き対象ビルドで検査した。`/private/tmp/isw2-build154.log` は **6,090 jobs・終了コード0**、新規モジュールのみの監査は **12宣言・標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **289モジュール・17,837行**、外枠まで2,163行。一覧 `/private/tmp/isw2-g10-twohundredeightynine-modules.txt`。sorry・新公理0、ModelCategory SSetの追加なし、計算上限・既存宣言・⑤a・入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B06（同じ族の制限と既存の全BK→native比較との厳密な一致）、B07・B08が残る。既存の `fixedVertexConeSpaceEquiv_cosliceSection`、`coherentConeSourceFamily_restriction_weighted`、`weightedConeEndPrecomposition_evaluation` を使って、元のweightedな錐の点を同じcosliceの前合成へ戻す経路を進める。Bの完了後にC・Dを再見積もりする。C・D、停止点2a・2b、3b-4段0は未完。


## 142. B06：同じTot錐のweighted点・切断と固定点のend作用（2026-11-14 午後）

一覧：済み 18／全体 36（うち追加 1）

元の `nativeCoherentCone X` の正規化したcoslice切断を、指定の `reflectedWeightedConeSectionPoint` の評価へ戻した。さらにその点のYoneda表示と既存BK比較の評価則を使い、同じweightedな切断の表示を得た。B04の同じ族を制限した際の相対uncurryも、その切断に対する既存のcoslice前合成へ同定した。

end作用の側では、既存のパラメータ自然性を全切断に対して証明し、同じweighted錐の点を固定した作用が `reflectedWeightedHomComparison` に一致する式を得た。今回の6宣言はB06の既存構成の単位・自然性・評価則と証明分割であり、新しい構成／数学の追加はない。B06の最終等式には、これらの式のULift・直積の照合がなお残る。


### 142.1 `NativeTotConePointSection`（117行）

```lean
theorem nativeTotCone_cosliceSection (X : CosimplicialObject (Complex A)) :
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (liftedEnrichedBousfieldKanCone X)))

theorem nativeTotCone_point_yoneda (X : CosimplicialObject (Complex A)) :
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    SSet.yonedaEquiv.symm (reflectedWeightedConeSectionPoint F z φ) =
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst (bousfieldKanWeight (AsSmall.{u} SimplexCategory))
          ((Functor.const (AsSmall.{u} SimplexCategory)).obj (Δ[0] : SSet.{u})) ≫ φ)))) ≫
        reflectedHomHolimConeComparison F z

theorem nativeTotCone_cosliceSection_weighted (X : CosimplicialObject (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    coherentConeCosliceSection (nativeCoherentCone X) ≫
      eqToHom (congrArg (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X)) =
    s ≫ weightedCosliceComparison F z

theorem nativeTotConeFamilyLift_restriction_uncurry
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let H := simplicialHomDiagram F z ⋙ SSet.opFunctor
    let φ := liftedEnrichedBousfieldKanCone X
    let e : (Δ[0] : SSet.{u+1}) ⟶
        (SSet.uliftFunctor.{u+1,u}).obj (bousfieldKanHolim H) :=
      SSet.yonedaEquiv.symm (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))
    let s := inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) (Δ[0] : SSet.{u+1})) ≫
      (((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ◁ e) ≫
        (uliftTensorIso (nerve I) (bousfieldKanHolim H)).inv ≫
          (SSet.uliftFunctor.{u+1,u}).map (bousfieldKanWeightedNerveEvaluation H)
    relativeFunctorUncurry (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x)) =
    (s ▷ (SSet.uliftFunctor.{u+1,u}).obj (SimplicialCategory.sHom x z).op) ≫
      weightedCoslicePrecompositionFamily F x z

```

### 142.2 `WeightedSectionParameterNaturality`（75行）

```lean
theorem weightedSectionsParameterMap_precomp (W H H' : I ⥤ SSet.{u})
    {K B : SSet.{u}} (η : H ⋙ tensorRight B ⟶ H')
    (p : K ⟶ weightedSections W H) :
    (p ⊗ₘ 𝟙 B) ≫ weightedSectionsParameterMap W η =
      weightedSectionsLift (weightedSectionParameterTransform (weightedSectionsUncurry p) η)

theorem reflectedWeightedHomComparison_point_precomposition
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (z : C)
    (φ : bousfieldKanWeight I ⟶ simplicialHomDiagram F z ⋙ SSet.opFunctor) (x : C) :
    let p := weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)
    (p ⊗ₘ 𝟙 (SimplicialCategory.sHom x z).op) ≫ weightedConeEndPrecomposition F x z =
      snd (Δ[0] : SSet.{u}) (SimplicialCategory.sHom x z).op ≫
        reflectedWeightedHomComparison F z φ x

```

### 142.3 検収と残り

コード **`7d5fde8b1`**。今回初めて読む既存依存を対象ビルド155・156で作成し、残ったelaborationを個別検査で修正した。最終版の鍵付き対象ビルド `/private/tmp/isw2-build157.log` は **6,107 jobs・終了コード0**、新規分だけの監査は **6宣言（4・2）、標準三公理のみ**。鍵は `--class impl --wait 3600`、ビルドと監査の間だけ使用し返却済み。

累計 **291モジュール・18,029行**、外枠まで1,971行。一覧 `/private/tmp/isw2-g10-twohundredninetyone-modules.txt`。sorry・新公理0。計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。未検証下書きなし。

B06の元の制限の等式は未完。点のYoneda表示には既存 `uliftYonedaMap` がそのまま使えることを確認した。残りは、点を固定したend作用と指定weighted評価をULift直積同型で照合し、同じ相対uncurryの式を戻す接続。B07・B08、C・D、停止点2a・2b、3b-4段0も未完。


## 143. B06：元の指定族の制限の厳密な等式（2026-11-14）

一覧：済み 19／全体 36（うち追加 1）。B06 を完了。B07・B08、C01〜C07、D01〜D08 は未完。

### 143.1 証明と型

`UliftPointTensorEvaluation`（58行）は既存構成の単位・係数移送則。新しい数学のまとまりは追加しない。第0単体への二つの射影の逆則と、その各次数の一意性で証明した。`NativeTotConeRestriction`（79行）は、元の錐の相対uncurryと同じend作用の点評価を照合し、相対uncurryの単射性でB06へ戻す。既存 `uliftYonedaMap` を使い、錐・脚・全高次単体を取り換えていない。

```lean
theorem uliftPointTensorEvaluation (K E Q S : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s ▷ U.obj S =
      (U.obj K ◁ U.map (inv (snd (Δ[0] : SSet.{u}) S) ≫ (p ⊗ₘ 𝟙 S))) ≫
        (uliftTensorIso K (E ⊗ S)).inv ≫
          U.map ((α_ K E S).inv ≫ (f ▷ S)) ≫ (uliftTensorIso Q S).hom

theorem nativeTotConeFamilyLift_restriction
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x) =
    (SSet.uliftFunctor.{u+1,u}).map
      (reflectedWeightedHomComparison (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (liftedEnrichedBousfieldKanCone X) x) ≫
      reflectedHomHolimConeComparison (liftedClosedDiagram X) x

```

### 143.2 検収と残り

鍵付き対象ビルド `/private/tmp/isw2-build158.log` は **6,109 jobs・終了コード0**。今回の二本だけの監査は **2宣言（1・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、対象ビルドと監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **293モジュール・18,166行**、外枠まで1,834行。モジュール一覧 `/private/tmp/isw2-g10-twohundredninetythree-modules.txt`。B07・B08の接続を新規 `NativeTotConeLimit` に準備中（未検証・未コミット）。Bの完了後にC・Dを再見積もりする。


## 144. B07・B08完了：同じ元のTot錐のnative極限性とC・Dの再見積もり（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。A01〜A12・A05a・B01〜B08完了。C・Dは未完で、停止点2a・2bではない。

### 144.1 型と検証

`NativeTotConeLimit`（60行）。B07はB06・B03・既存のULiftホモトピー輸送と一般のBK→native比較の同値性。B08は同じ指定族 `a`、頂点式 `ha`、制限の同値性 `he` を `coherentCone_isLimit_of_family_lifts` に渡す。dg nerveへの移送には既存の同値による極限保存を使う。新しい模型圏の仮定、錐の選び直しなし。

```lean
theorem nativeTotConeFamilyLift_equivalence
    (X : CosimplicialObject (Complex A)) (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (nativeTotConeFamilyLift X x ≫
      coneSectionRestriction (nativeCoherentCone X) (coherentNerveVertex x))

theorem nativeCoherentCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeCoherentCone X)

theorem nativeDGCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDGCone X)

```

既存依存だけの対象ビルド159は4,471 jobs・終了コード0。個別検査後の鍵付き対象ビルド160は **6,810 jobs・終了コード0**、新規一本だけの監査は **3宣言、標準三公理のみ**（`/private/tmp/isw2-build160.log`）。鍵 `--class impl --wait 3600` はビルドと監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **294モジュール・18,226行**、外枠20,000行まで1,774行。モジュール一覧 `/private/tmp/isw2-g10-twohundredninetyfour-modules.txt`。未検証下書きなし。

### 144.2 Bの実測とC・Dの見込み

A完了の§101（12,781行）からB完了までの増分は **5,445行**。§72.2のBの600〜900行という見込みに対し約6.1〜9.1倍、差は+4,545〜+4,845行。§111時点のB残量400〜700行に対しても実測4,387行だった。主な差は、指定AW・随伴・Moore・係数移送と実豊穣合成の厳密等式の照合が、抽象的な同値性から自動では得られなかったこと。

| 残るまとまり | 従来の見込み | B実測を受けた現在の追加見込み | 再利用と不確定箇所 |
| --- | ---: | ---: | --- |
| C：標準脚とD(A)輸送 | 400〜700 | 900〜1,600 | rawの極限性はB08済み。出力分解の既存判定と同じ第0頂点の脚、AsSmall/ULiftのstrict等式・join引き戻しの照合が残る |
| D：全図式射・指定錐の族・離散入口 | 500〜900 | 900〜1,600 | 重みの構成は全図式に自然。実際の全nerve上の族、点での同一join射、離散比較の頂点輸送の最終式は未実装 |
| 合計 | 900〜1,600 | **1,800〜3,200** | 完成見込み20,026〜21,426行 |

単純にBの倍率をC・Dへ掛けるのは過大にもなり得る。Bで作ったHomの照合と全パラメータの評価則を再利用できる分を引いて上表としたが、現外枠に収まる保証はない。指定一覧のCの証明を進め、計算上限・型・範囲は弱めず、外枠到達または一覧外の新しい数学が必要と判明した時点で検証済みを保存して停止する。追加の第五のまとまりは現時点で要求しない。


## 145. C01の途中：同じ錐の実際の脚と指定weighted評価（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。C01の最終等式は未完。以下は既存構成の評価・単位・係数移送・自然性の法則と、C01の証明分割。新しいまとまり・新しい数学の項目は加えない。

### 145.1 型と置き場所

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.JoinConeSectionLeg`（34行）。

```lean
theorem joinCone_section_leg {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (v : K _⦋0⦌) (z : X _⦋0⦌) (h : c.vertex = z) :
    (derivedConeLeg c v).edge = SSet.yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫
        (((coherentConeCosliceSection c ≫ eqToHom (congrArg
          (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
          (Opposite.op ⦋0⦌) v).val))

```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointEvaluation`（46行）。

```lean
theorem uliftPointEvaluation (K E Q : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q) (σ : K _⦋0⦌) :
    let U

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionVertex`（77行）。

```lean
theorem nativeTotCone_cosliceSection_vertex (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegEvaluation`（57行）。

```lean
theorem nativeDGCone_leg_weighted (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardLeg`（34行）。

```lean
def standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (productTotalFunctor A).obj X ⟶ X.obj n

theorem standardLeg_naturality {X Y : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (n : SimplexCategory) :
    (productTotalFunctor A).map f ≫ standardLeg A Y n =
      standardLeg A X n ≫ f.app n

```

### 145.2 検収と残り

鍵付き対象ビルド161は **1,800 jobs・終了コード0**、`JoinConeSectionLeg` の新規分だけの監査は **1宣言、標準三公理のみ**。対象ビルド162は **6,109 jobs・終了コード0**、他の四本の新規分だけの監査は **7宣言（1・1・1・4）、標準三公理のみ**。ログ `/private/tmp/isw2-build161.log`・`/private/tmp/isw2-build162.log`。鍵 `--class impl --wait 3600` は一つの整理券で待ち、ビルドと監査の間だけ保持し返却済み。

累計 **299モジュール・18,474行**、外枠まで1,526行。一覧 `/private/tmp/isw2-g10-twohundredninetynine-modules.txt`。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

残るC01の最終成分は、`standardTopEval` による元の反転BK入力の恒等射頂点での評価と、第0頂点を通る標準脚の閉零射の値との等式に絞れた。既存 `reflectedBKFreeCone_generator_top` で同じ自由生成元の評価へ戻せることを個別検査した。未コミットの作業は、一次coherent単体の比較への簡約 `NativeTotConeLegSimplex`、Moore反転の第0項の単位則 `NormalizedMooreReverseZero`、Hom–Totの零行評価 `HomTotalZeroRow`、最終の `NativeTotConeStandardLeg`。前二者は個別検査済み、後二者は検査・証明中であり、今回の検収・累計には含めない。


## 146. C01の途中：同じ一次単体と零次の単位・係数移送則（2026-11-14）

一覧：済み 21／全体 36（うち追加 1）。C01は未完。今回の四本はC01の証明分割と既存構成の法則のみ。計算上限を上げず、添字の等式の消去・既存の両逆則を局所的に分けて証明した。

### 146.1 型

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeLegSimplex`（48行）。

```lean
theorem nativeDGCone_leg_simplex (X : CosimplicialObject (Complex A))
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋0⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    let s := (weightedNerveSectionFromTransform
      (CartesianMonoidalCategory.fst (bousfieldKanWeight I)
        ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app (Opposite.op ⦋0⦌)
          (σ, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
    (derivedConeLeg (nativeDGCone X) (ULift.up σ)).edge =
      (coherentComparison (R := A) (D := Complex A)).app (Opposite.op ⦋1⦌)
        (weightedConeSimplex F z s.2)
```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseZero`（34行）。

```lean
theorem normalizedMooreReverse_zero_inclusion (W : SimplicialObject C) :
    (normalizedMooreReverse.app W).f 0 ≫ (inclusionOfMooreComplexMap W).f 0 =
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalZeroRow`（43行）。

```lean
theorem homTotalComponent_zero_ofHom (P : Complex A) (X : CosimplicialObject (Complex A))
    (f : P ⟶ (productTotalFunctor A).obj X) :
    homTotalComponent P X 0 0 (Cochain.ofHom f) =
      Cochain.ofHom (f ≫ standardZeroLeg A X)
```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreInverseInclusion`（32行）。

```lean
theorem normalizedMooreMapInv_inclusion :
    normalizedMooreMapInv F X ≫
      (F.mapHomologicalComplex (.down ℕ)).map (inclusionOfMooreComplexMap X) =
    inclusionOfMooreComplexMap (X ⋙ F) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app X
```

### 146.2 検収と残り

鍵付き対象ビルド163は **6,114 jobs・終了コード0**（`/private/tmp/isw2-build163.log`）。新規四本だけの監査は **14宣言（1・4・8・1）、標準三公理のみ**。鍵 `--class impl --wait 3600` は一つの整理券で待ち、対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査の変更なし。rootビルド・大きな監査なし。

累計 **303モジュール・18,631行**、外枠まで1,369行。一覧 `/private/tmp/isw2-g10-threehundredthree-modules.txt`。未コミットは `NativeTotConeStandardLeg` と、その零次係数生成元の計算の分割 `LinearWeightZeroGenerator`。前者は既存 `reflectedBKFreeCone_generator_top` で同じ自由生成元の像へ戻す所まで確認し、後者の係数逆射の法則を証明中。これらは今回の検収・累計に含めない。C01の最終式、C02〜C07、D、停止点2a・2b、3b-4段0は未完。


## 147. C01・C02・C03完了：同じ標準脚・D(A)のnative極限錐・指定頂点（2026-11-14）

一覧：済み 24／全体 36（うち追加 1）。C01・C02・C03完了。C04〜C07・Dは未完であり、停止点2a・2bではない。

### 147.1 証明と再利用

C01は、同じweighted一次単体の比較を既存自由生成元評価へ戻し、係数逆射・Moore反転の零次包含則・元の零行・第0頂点への重み比較・自由単位重みの逆Yoneda評価を合成した。最後のcochainと閉零射の値は、既存 `complexClosedHomEquiv_cochain` と `complexToClosed_map` で照合した。計算上限に当たった深い書き換えは、等式を指定した前後合成へ分割して解消した。上限の引き上げなし。

C02は既存 `dgModuleResolvedInfinity_isLimitCone_of_raw` をそのまま使い、前後の一点係数比較の同値で同じ全join錐を既存D(A)へ送った。`SemifreeRingEvaluationEquivalence` の最終版は既存 `SemifreePointComparison.semifreePointEvaluation_quasiEquivalence` の同じ評価の定義を再利用する薄い接続であり、準同値を作り直していない。C03は同じ後合成の頂点則で、元の積Totの指定半自由分解の頂点を保持する。

### 147.2 型と登録対象

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightZeroGenerator`（89行）。

```lean
theorem normalizedLinearWeightDiagramIso_inv_zero_generator (W : J ⥤ SSet.{0})
    (j : J) (s : (W.obj j) _⦋0⦌) :
    let V := linearizedSimplicialWeight A W.flip
    let N := (normalizedMooreComplex _).obj V
    let e := N.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl
    ((inclusionOfMooreComplexMap V).f 0).app j
      (e.hom.app j (((normalizedLinearWeightDiagramIso A W).inv.f 0).app j
        (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0 (ULift.up s)))) =
      CategoryTheory.Limits.Sigma.ι (fun _ : (W.obj j) _⦋0⦌ => ModuleCat.of A A) s (1 : A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SemifreeRingEvaluationEquivalence`（35行）。

```lean
theorem semifreeRingEvaluationDG_quasiEquivalence :
    QuasiEquivalence (semifreeRingEvaluationDG A)

theorem semifreeRingEvaluationInfinity_isQCatEquivalence :
    IsQCatEquivalence (semifreeRingEvaluationInfinity A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeZeroRow`（44行）。

```lean
theorem normalizedBousfieldKanConeRepresentative_zero_row
    (X : CosimplicialObject (Complex A)) :
    let T := (productTotalFunctor A).obj X
    let H := doubleOppositeDiagram ((homDiagramFunctor T).obj X)
    (negativeChainRowIso (normalizedBousfieldKanWeight (A := A)) 0).inv ≫
      (normalizedBousfieldKanConeRepresentative X).f 0 =
    (normalizedBKStandardWeightMap A).f 0 ≫
      ((freeUnitWeightEndNatIso A (Opposite.op ⦋0⦌)).inv.app H).f 0
        (Cochain.ofHom (standardZeroLeg A X))

```

登録対象：`SerrePositivity.HomologicalAlgebra.FreeWeightEndInverseEvaluation`（43行）。

```lean
theorem freeUnitWeightEndNatIso_inv_generator (j i : J) (f : i ⟶ j)
    (X : Jᵒᵖ ⥤ Complex A) (q : ℤ) (x : (X.obj (op j)).X q) :
    ((((freeUnitWeightEndNatIso A j).inv.app X).f q x).app (op i))
      (Sigma.ι (fun _ : i ⟶ j => ModuleCat.of A A) f (1 : A)) =
    (X.map f.op).f q x

```

登録対象：`SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseExtendZero`（32行）。

```lean
theorem normalizedMooreReverse_extend_zero_inclusion (W : SimplicialObject C) :
    let N := (normalizedMooreComplex C).obj W
    let Nr := (normalizedMooreComplex C).obj (SimplicialObject.opFunctor.obj W)
    (extendMap (normalizedMooreReverse.app W) ComplexShape.embeddingDownNat).f 0 ≫
      (negativeChainRowIso N 0).hom ≫ (inclusionOfMooreComplexMap W).f 0 =
    (negativeChainRowIso Nr 0).hom ≫
      (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj W)).f 0

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKStandardZeroGenerator`（41行）。

```lean
theorem barOverStandard_zero_generator (n : SimplexCategory) :
    let j := op (op n)
    (((barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.f 0 ≫
      ((alternatingFaceMapComplex _).map
        (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).f 0).app j)
      (Sigma.ι (fun _ : (bousfieldKanSetWeight.obj (op ⦋0⦌)).obj j => ModuleCat.of A A)
        (nerveVertex (Over.mk (𝟙 n))) (1 : A)) =
    Sigma.ι (fun _ : op n ⟶ op ⦋0⦌ => ModuleCat.of A A)
      (SimplexCategory.const ⦋0⦌ n 0).op (1 : A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKConeZeroRow`（88行）。

```lean
theorem reflectedBKCone_zero_generator (X : CosimplicialObject (Complex A))
    (n : SimplexCategory) :
    let j := Opposite.op (Opposite.op n)
    let W := (SimplicialObject.opFunctor.obj bousfieldKanSetWeight).flip
    let S := (W ⋙ SSet.uliftFunctor.{u,0}).obj j
    (((((normalizedLinearWeightDiagramIso A W).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f 0).app j)
      (freeNegativeGenerator S 0 (ULift.up (nerveVertex (Over.mk (𝟙 n))))) =
    Cochain.ofHom (standardLeg A X n)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeStandardLeg`（81行）。

```lean
theorem nativeDGCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDGCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (dgClosedEdge A (Complex A)
        ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
          (standardLeg A X n))).edge

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotIndex`（41行）。

```lean
def nativeTotIndexIso :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ≅
      (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)

def strictCosimplicialComplexNerve (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (Complex A)

theorem nativeTotIndexIso_vertex (n : SimplexCategory) :
    nativeTotIndexIso.{u}.hom.app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex (AsSmall.up.obj n))) = ULift.up (nerveVertex n)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotCone`（59行）。

```lean
def nativeDerivedDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      derivedInfinityCategory A

def nativeDerivedCone (X : CosimplicialObject (Complex A)) : JoinCone (nativeDerivedDiagram X)

theorem nativeDerivedCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (nativeDerivedCone X)

theorem nativeDerivedCone_vertex (X : CosimplicialObject (Complex A)) :
    (nativeDerivedCone X).vertex =
      (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
        (Simplex.vertex ((productTotalFunctor A).obj X))

```

### 147.3 検収・実測・残り

初回の係数二本だけのビルド165は5,020 jobs・終了コード0、3宣言・標準三公理のみ。その後に既存準同値の再利用へ整理した**最終版**の鍵付き対象ビルド166は **7,849 jobs・終了コード0**、今回十本だけの監査は **24宣言（1・2・1・1・1・5・1・1・4・7）、標準三公理のみ**。ログ `/private/tmp/isw2-build165.log`・`/private/tmp/isw2-build166.log`。鍵は一つの整理券で `--class impl --wait 3600`、対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0。既存宣言・⑤a・入口・公式監査・mainの変更なし、rootビルド・大きな監査なし。

累計 **313モジュール・19,184行**、外枠まで816行。モジュール一覧 `/private/tmp/isw2-g10-threehundredthirteen-modules.txt`。

C05の宇宙表記は§73.3の許可どおり、複体の対象宇宙u+1とHom宇宙uを分けた。`nerveMap X` は通常のMathlib版だと二つの圏の宇宙を同じに要求するため、そのままの表記を使わず、既存 `nerveAsSmallIso` と `resizedNerveMap (AsSmall.down ⋙ X)` で元のXの全単体を写す `strictCosimplicialComplexNerve` を明示した。元のXを別の図式へ置き換えるものではない。`nativeTotIndexIso` は同じAsSmallの逆と既存 `smallDiagramShapeIso` の合成で、指定次数の頂点の等式も厳密に保つ。C05の最終図式等式自体はまだ未完。

未コミットの作業はC04の一般後合成則 `ConeLegPostcomposition`（個別検査済み）と `NativeDerivedTotLeg`（そのモジュールのビルド待ち）、C05の `ComplexStrictNerveComparison`（証明中）。C04〜C07が済んだ後に停止点2aをまとめ、同じ外枠の中でDへ進む。Dの型・範囲を弱めない。


## 148. C04完了：同じ標準脚のD(A)への実一次単体の像（2026-11-14）

一覧：済み 25／全体 36（うち追加 1）。C01〜C04完了。C05〜C07とDは未完。

### 148.1 型

一般の後合成の評価則はKerodonのLimitsAndColimitsに新規ファイルとして置いた。C04はその法則とC01を同じ元の錐に適用するだけで、錐・頂点・脚を取り換えない。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeLegPostcomposition`（29行）。

```lean
theorem derivedConeLeg_mapJoinCone {K X Y : SSet.{u}} {p : K ⟶ X}
    (f : X ⟶ Y) (c : JoinCone p) (v : K _⦋0⦌) :
    (derivedConeLeg (mapJoinCone f c) v).edge =
      f.app (Opposite.op ⦋1⦌) (derivedConeLeg c v).edge
```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotLeg`（34行）。

```lean
theorem nativeDerivedCone_standardLeg (X : CosimplicialObject (Complex A)) (n : SimplexCategory) :
    (derivedConeLeg (nativeDerivedCone X) (ULift.up (nerveVertex (AsSmall.up.obj n)))).edge =
      (SerrePositivity.EInfinity.ComplexLimits.complexSemifreeResolutionInfinity A).app
        (Opposite.op ⦋1⦌)
        (dgClosedEdge A (Complex A)
          ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map
            (standardLeg A X n))).edge
```

### 148.2 検収と残り

鍵付き対象ビルド167は **7,849 jobs・終了コード0**（`/private/tmp/isw2-build167.log`）。新規二本だけの監査は **2宣言（1・1）、標準三公理のみ**。鍵は `--class impl --wait 3600`、一つの整理券で待ち、対象ビルド・小監査の間だけ保持し返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査・mainの変更なし。rootビルド・大きな監査なし。

累計 **315モジュール・19,247行**、外枠まで753行。一覧 `/private/tmp/isw2-g10-threehundredfifteen-modules.txt`。

C05は、同じ閉零圏のstrict nerveからcoherent比較を通した射と、既存 `closedNerveInclusion` との全単体の等式を `ComplexStrictNerveComparison` に分割して証明中。対象の一致は確認できており、閉零射と高次零成分の照合が残る。新しい図式や比較を選ぶものではない。未コミットの下書きはこの一本だけ。停止点2a・2bと3b-4段0は未完。


## 149. C05完了：元のstrict図式の全単体の厳密等式（2026-11-14）

一覧：済み 26／全体 36（うち追加 1）。C01〜C05完了、C06・C07とDは未完。

### 149.1 型と登録対象

既存構成の評価・単位則とC05の証明分割。新しい図式・比較を選ばず、同じstrict Homの定数単体の正次元成分が零であることを、既存の旗の和に項別に適用した。低次では同じ閉零射を評価する。計算上限の増加なし。各ファイルは200行以内。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardConstantTopEvaluation`（65行）。

```lean
theorem standardTopEval_constant_pos (z : (standardHomSpace (R := R) x y) _⦋0⦌)
    (m : ℕ) (hm : 0 < m) :
    standardTopEval x y m (PinchedHom.constant z m) = 0

theorem standardTopEval_constant_zero (z : (standardHomSpace (R := R) x y) _⦋0⦌) :
    standardTopEval x y 0 (PinchedHom.constant z 0) =
      (standardZeroEquiv (R := R) x y z).val

theorem standardZeroEquiv_homEquiv (x y : ClosedCategory R D) (f : x ⟶ y) :
    standardZeroEquiv (R := R) (D := D) x y
      (SimplicialCategory.homEquiv' x y f) = closedHomEquiv R D x y f

```

登録対象：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictCubeEvaluation`（35行）。

```lean
theorem coherentCubeComponent_orderDiagram_pos {J : Type u} [LinearOrder J]
    (F : J ⥤ ClosedCategory R D) {a b : J} (hab : a < b)
    (S : Finset (Set.Ioo a b)) (hS : 0 < S.card) :
    coherentCubeComponent (enrichedFunctorOfOrderDiagram F) hab S = 0

```

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexStrictNerveComparison`（71行）。

```lean
theorem complexClosedNerve_coherentComparison :
    nerveToCoherent (ClosedCategory A (Complex A)) ≫
      coherentComparison (R := A) (D := Complex A) = closedNerveInclusion A (Complex A)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedDiagramEq`（41行）。

```lean
theorem nativeDerivedDiagram_eq (X : CosimplicialObject (Complex A)) :
    nativeDerivedDiagram X = nativeTotIndexIso.hom ≫ strictCosimplicialComplexNerve X ≫
      complexOrdinaryDerivedSource A

```

### 149.2 検収と残り

コード `5674cfded`。鍵付き対象ビルド168・169・170はそれぞれ **3,755・3,944・7,836 jobs、すべて終了コード0**。新規四本だけの分割監査は **3 + 2 + 1 = 6宣言、標準三公理のみ**（各ログ `/private/tmp/isw2-build168.log`〜`170.log`）。一つの整理券ずつ `--class impl --wait 3600`、ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、既存宣言・⑤a・入口・公式監査・mainの変更なし。

累計 **319モジュール・19,459行**、外枠まで541行。一覧 `/private/tmp/isw2-g10-threehundrednineteen-modules.txt`。C06・C07は同じslice制限の同型と底図式の等式消去で証明中。Dは未着手。外枠と型つき一覧の規則を維持する。


## 150. 停止点2a：B・C完了、同じ元のstrict図式のnative極限錐（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。A・B・C完了。D01〜D08未完。停止点2bと3b-2全体の完成はまだ宣言しない。停止点2aの単独取り込み点はコード `b43d4be81`（C05 `5674cfded`を含む）。

### 150.1 C06・C07の型と登録対象

一般の部分はKerodonに、G10の適用はHAに置いた。slice制限の既存の同型と終頂点の同型不変性、同じ底図式の等式消去のみを使う既存構成の法則。各ファイル200行以内。

登録対象：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SpecifiedConeReindex`（43行）。

```lean
theorem restrictJoinCone_isLimit_of_isIso {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) [IsIso f] (hc : IsLimitCone c) :
    IsLimitCone (restrictJoinCone c f)

def joinConeOfDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : JoinCone q := h ▸ c

/-- 同じ全join射を保つ。 -/
theorem joinConeOfDiagramEq_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) : (joinConeOfDiagramEq h c).val = c.val

theorem joinConeOfDiagramEq_isLimit {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (joinConeOfDiagramEq h c)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StrictDerivedTotCone`（51行）。

```lean
theorem nativeDerivedDiagram_reindex (X : CosimplicialObject (Complex A)) :
    nativeTotIndexIso.inv ≫ nativeDerivedDiagram X =
      strictCosimplicialComplexNerve X ≫ complexOrdinaryDerivedSource A

def strictDerivedTotCone (X : CosimplicialObject (Complex A)) :
    JoinCone (strictCosimplicialComplexNerve X ≫ complexOrdinaryDerivedSource A)

theorem strictDerivedTotCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (strictDerivedTotCone X)

theorem strictDerivedTotCone_pullback (X : CosimplicialObject (Complex A)) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.hom ≫
      (strictDerivedTotCone X).val = (nativeDerivedCone X).val

```

### 150.2 検収と見込みとの差

鍵付き対象ビルド171は **7,841 jobs、終了コード0**。新規二本の小監査は **10宣言（4・6）、標準三公理のみ**。ログ `/private/tmp/isw2-build171.log`。`--class impl --wait 3600`、鍵は対象ビルドと小監査の間だけ保持し返却済み。sorry・新公理0、計算上限の増加、既存宣言、⑤a、入口・公式監査・mainの変更なし。

累計 **321モジュール・19,553行**、外枠まで447行。一覧 `/private/tmp/isw2-g10-threehundredtwentyone-modules.txt`。B完了18,226行からC完了までの増分は **1,327行**。§72.2の400〜700行に対して+627〜+927行、B実測を受けた§144.2の900〜1,600行の範囲内。標準脚の零単体の評価とstrict nerveの全単体の等式を明示する部分に増分が集中した。

| まとまり | §72.2の見込み | 現在の実測・残り |
| --- | ---: | --- |
| A：正規化テンソル／積重み | 残量400〜700行（§72.2） | §72の8,834行から§101の12,781行まで3,947行の増分（全体のA完了時点は12,781行） |
| B：指定豊穣Homとnative極限性 | 600〜900行 | 完了5,445行（A完了からの増分） |
| C：標準脚とD(A)輸送 | 400〜700行 | 完了1,327行 |
| D：全図式射・指定錐の族・離散入口 | 500〜900行 | 未完、§144.2の900〜1,600行を維持 |

予測だけで再停止せず、D01の全族の境界を固定する同じ全関手の部品から進める。D04の辺だけを全族の代用品にしない。外枠到達または一覧外の新しい数学が必要になった時点で検証済みをコミットして止め、3b-4の紙の整理へ移る。


## 151. Dの途中：全境界・指定複体代表の自然性・離散raw錐（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01〜D08は最終の型をまだ閉じていないため、完了数に加えない。以下はD01・D02・D04・D05の既存構成の自然性・合成則と証明分割であり、新しい数学のまとまりを追加しない。

### 151.1 型と登録対象

全評価を同じ全関手で固定し、元の指定BK比較を全図式射に自然にまとめた。零単体だけの族を全錐族と呼ばない。離散の補助錐は `rawCosimplicialModuleCone` と明記し、元の積Totを頂点にする。D06の整数零延長した交代余面複体を頂点にする最終 `cosimplicialModuleCone` は、このraw錐から同じ指定自然同型で移す工程が残る。後で既存宣言の型を変更して頂点を差し替える方針にはしない。

§73.4の `ρ_.inv` と `jX : Δ[0] ⟶ B` の積の紙の略記は、実際のMathlibでは単位対象（定値PUnit）と `Δ[0]` が定義的に一致しないため、そのままでは型が合わない。今回の `strictCosimplicialEvaluationNerve_at` は、既存の標準射影同型 `fst K Δ[0]` の逆を明示した同じ点での評価で述べた。点の選び直しやFunctorIsoへの弱化ではない。D03・D07もこの標準同型を表記に含める。

登録対象：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomTargetNaturality`（89行）。

```lean
theorem extendedChainHomRows_postcomp {H H' : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ}
    (f : H ⟶ H') (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q)
    (n : ℕ) :
    extendedChainHomRows K H' q ((intervalHomPrePost A (𝟙 _) f).f q z) n =
      extendedChainHomRows K H q z n ≫ f.f (q-n)

theorem weightEndHomIso_target_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        intervalHomPrePost A (𝟙 (K.extend ComplexShape.embeddingDownNat))
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f)

theorem weightEndHomIso_target_naturality_postcompose {X Y : Jᵒᵖ ⥤ Complex A}
    (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        SerrePositivity.EInfinity.PowerOperation.linearHomComplexPostcompose A
          (K.extend ComplexShape.embeddingDownNat)
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotFamilyBoundaries`（75行）。

```lean
def strictCosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ nerve (Complex A) where
  app _ := ↾fun p => (p.1.down.prod' p.2) ⋙
    evaluationUncurried SimplexCategory (Complex A)
  naturality _ _ _

theorem strictCosimplicialEvaluationNerve_at (X : CosimplicialObject (Complex A)) :
    inv (fst ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        strictCosimplicialEvaluationNerve A = strictCosimplicialComplexNerve X

def derivedTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

def derivedTotVertexFamily :
    nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

theorem derivedTotVertexFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanComparisonNaturality`（77行）。

```lean
def normalizedBousfieldKanHomFunctor : CosimplicialObject (Complex A) ⥤ Complex A

theorem normalizedBousfieldKanHomComparison_naturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanHomComparison X ≫ normalizedBousfieldKanHomFunctor.map f =
      (productTotalFunctor A).map f ≫ normalizedBousfieldKanHomComparison Y

def normalizedBousfieldKanHomComparisonNatTrans :
    productTotalFunctor A ⟶ normalizedBousfieldKanHomFunctor where
  app X := normalizedBousfieldKanHomComparison X
  naturality _ _ f := (normalizedBousfieldKanHomComparison_naturality f).symm

/-- 同じHom–Tot比較と指定正規化比較を全図式上で合成する。 -/
def homToNormalizedBousfieldKanNatTrans (P : Complex A) :
    productTotalFunctor A ⋙ homFunctor P ⟶
      homDiagramFunctor P ⋙ normalizedBousfieldKanHomFunctor

theorem homToNormalizedBousfieldKanNatTrans_app (P : Complex A)
    (X : CosimplicialObject (Complex A)) :
    (homToNormalizedBousfieldKanNatTrans P).app X = homToNormalizedBousfieldKan P X

theorem homToNormalizedBousfieldKan_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (homFunctor P).map ((productTotalFunctor A).map f) ≫ homToNormalizedBousfieldKan P Y =
      homToNormalizedBousfieldKan P X ≫
        normalizedBousfieldKanHomFunctor.map ((homDiagramFunctor P).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeRepresentativeNaturality`（49行）。

```lean
def normalizedBKConeTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj Y))

theorem normalizedBousfieldKanRepresentative_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    (g : P ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative P X g ≫ normalizedBKConeTargetMap P f =
      normalizedBousfieldKanRepresentative P Y (g ≫ (productTotalFunctor A).map f)

```

登録対象：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteNativeTotCone`（58行）。

```lean
def strictCosimplicialModuleNerve (M : CosimplicialObject (ModuleCat.{u} A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (ModuleCat.{u} A)

def discreteModuleSource : nerve (ModuleCat.{u} A) ⟶ derivedInfinityCategory A

theorem discreteDiagram_strict (M : CosimplicialObject (ModuleCat.{u} A)) :
    strictCosimplicialComplexNerve ((discreteDiagramFunctor A).obj M) ≫
      complexOrdinaryDerivedSource A =
    strictCosimplicialModuleNerve A M ≫ discreteModuleSource A

def rawCosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A)

theorem rawCosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (rawCosimplicialModuleCone A M)

```

### 151.2 検収欄（最終の対象ビルド待ち）

鍵付き対象ビルド172は線形Homの単位則の型推論で失敗し、鍵を返却した。型を明示して修正後の173は **7,845 jobs・終了コード0**、三本だけの小監査は **21宣言（3・7・11）、標準三公理のみ**。これを失敗した172の成功と取り違えない。残る実複体代表の自然性・離散raw錐の個別検査は成功し、最終の二本の対象ビルド174と小監査を `--class impl --wait 3600` の一枚の整理券で待っている。174の確定結果とコードコミットは次節へ記す。

新規五本合計348行、草稿込み累計 **326モジュール・19,901行**、外枠20,000行まで **99行**。一覧 `/private/tmp/isw2-g10-threehundredtwentysix-modules.txt`。どのファイルも200行以内。全錐族の本体・両境界・各点で同じ全join射になる式、離散頂点の移送・全族・ホモロジー入口は未完。


## 152. 代わりの紙の作業：3b-4 §38.2の1・2の型つき段0案（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。これはG10完成後の3b-4を開始したという意味ではなく、外枠に近づいた際の指定された代わりの紙の作業。以下のR番号は**3b-4の提案一覧**であり、G10の36項目には加えない。Leanでelaboration・証明済みの宣言と数えない。既存ファイル、入口、⑤aの欄は変更しない。

### 152.1 既存の道具と、③-aから使う場所

- `EInfinity/BarrattEccles/FramedLimit.lean` の `framedLimitFunctor A K` は既に**全関手**。同じ右frame・一点重みのendを再定義しない。`FramedLimitLocalization.lean` の `framedLimit_inverts` と `localizedFramedLimit` は通常局所化への降下に使う。
- `FramedLimitCarrierDerivedComparison.lean` の `carrierFramedLimitComparisonIso` は台の**通常局所化**における比較。`_cone`・`_forgetCone` は同じ通常錐との両立を照合する入力。これだけでnativeな全join錐族の同型が済んだとは数えない。
- `CAlgUnderlyingDerivedComparison.lean` の `algebraCAlgSource_underlyingDerivedIso A` は実際の `algebraCAlgSource A ≫ cAlgForgetDerived A` と `nerveMap forget ≫ complexOrdinaryDerivedSource A` の**全関手同型**。Uを別の通常忘却関手で代用しない。
- `FreeProbeDerivedFreeForget.lean` の `cAlgForgetDerived_mapJoinCone_isLimit A c hc` は**追加の輸送条件を引数に取らない**既存の定理。ユーザーの11-14の訂正に従い、そのまま使用する。`FreeProbeUnitTransportCondition` を未証明の前提として再導入しない。
- 実現では `HomotopyWeight/{TensorRealization,PointwiseRealization,FrameLifting}` と既存のframe/重みの関手性を使う。右Quillen性や全対象fibrantだけでUの実現保存・通常limによるTotの計算を推論しない。

③-aの3b-3が必要な場所は二つ。(i) strictな複体図式の局所化から `Fun(I_J,D(A))` への全評価と同型を使い、下のR05・R10を局所化上の関手同型へ降ろす所。(ii) 3b-1から3b-3へ移した**全パラメータ実現余錐**とその輸送をR09・R10で使う所。図式ごとの余錐だけで全族の比較を閉じない。R01〜R04のstrict入力・台の通常比較の整理は③-aを待たずにできる。

任意のcoherent **BE値**図式への拡張（§38.2の3）は別の段。加群値の評価同値からBE値の厳密化を得たとは扱わない。そこに来たらBE版の評価同値か一般の模型定理のBEへの適用条件を具体的に受け取る。今回の段0案はその入力を仮定に隠して完成扱いしない。

### 152.2 紙の記法とTot側の型案

`E := (BarrattEccles.operad A).Algebra`、`CA := CAlg_R A`、`DA := derivedInfinityCategory A`、`S := algebraCAlgSource A`、`U := cAlgForgetDerived A`。`J₊ := AsSmall.{u} SimplexCategory`、`J₋ := AsSmall.{u} SimplexCategoryᵒᵖ`、`K± := (SSet.uliftFunctor.{u+1,u}).obj (nerve J±)`、`B± := nerve (J± ⥤ E)` とする。元のΔ・Δᵒᵖとの往復はG10の `nativeTotIndexIso` と同じAsSmall・ULiftの指定同型を使う。

`strictBE : (J± ⥤ E) → (K± ⟶ CA)` は、同じFの全nerveを `resizedNerveMap` で読みSへ後合成する表示。`evalBE± : K± ⊗ B± ⟶ CA` は同じ評価関手の全nerve。`forget± : (J± ⥤ E) ⥤ (J± ⥤ Complex A)` は既存 `Diagram.forget`。`forgetCosimp` はそのΔへの指定AsSmall引き戻し。以下はこの**紙の略記を展開してから検査する型案**。

```lean
-- R01：既存の計算全関手のnerve。新しいend/frameを選ばない。
def strictBETotVertex : B₊ ⟶ CA :=
  nerveMap (BarrattEccles.framedLimitFunctor A J₊) ≫ S

-- R02：同じ計算対象の、全図式射を含む指定錐族。
def strictBETotConeFamily : join (Δ[0] : SSet.{u+1}) K₊ ⊗ B₊ ⟶ CA
theorem strictBETotConeFamily_boundaries :
  (joinInl Δ[0] K₊ ⊗ₘ 𝟙 B₊) ≫ strictBETotConeFamily =
    pointLeftProjection B₊ ≫ strictBETotVertex ∧
  (joinInr Δ[0] K₊ ⊗ₘ 𝟙 B₊) ≫ strictBETotConeFamily = evalBE₊
def strictBETotCone (F : J₊ ⥤ E) : JoinCone (strictBE F)
theorem strictBETotConeFamily_at (F : J₊ ⥤ E) :
  pointRightSection (join Δ[0] K₊) (nerveVertex F) ≫ strictBETotConeFamily =
    (strictBETotCone F).val

-- R03：同じ指定錐そのもののnative極限性。
theorem strictBETotCone_isLimit (F : J₊ ⥤ E) : IsLimitCone (strictBETotCone F)
theorem strictBETotCone_vertex (F : J₊ ⥤ E) :
  (strictBETotCone F).vertex = S.app (Opposite.op ⦋0⦌)
    (nerveVertex ((BarrattEccles.framedLimitFunctor A J₊).obj F))

-- R04：Uの既存の全比較を、同じ評価・錐の全族へ適用。
def strictBETotUnderlyingIso : FunctorIso
  (strictBETotVertex ≫ U)
  (nerveMap forgetCosimp ≫ derivedTotVertexFamily A)
def strictBETotUnderlyingConeFamilyIso : FunctorIso
  (strictBETotConeFamily ≫ U)
  ((𝟙 _ ⊗ₘ nerveMap forgetCosimp) ≫ derivedTotConeFamily)
-- 上の同型の右境界への制限はalgebraCAlgSource_underlyingDerivedIsoの
-- 評価前合成、左境界への制限はstrictBETotUnderlyingIsoそのもの。

-- R05：上記をstrict図式の∞局所化へ降ろした全関手比較。
def strictBETotLocalizedUnderlyingIso : FunctorIso
  (TotBE ≫ U) (ForgetStrictBEInfinity ≫ TotDA)
```

`pointLeftProjection B` は `Δ[0] ⊗ B → B` の指定射影、`pointRightSection L v` は `inv (fst L Δ[0]) ≫ (𝟙 L ⊗ₘ yonedaEquiv.symm v)`。Mathlibの単位PUnitとΔ[0]を混同しない。R02〜R04の同じ全族・境界の等式は省略しない。R04の比較が必要とするG10の `derivedTotConeFamily` は**まだ未完**。

R03でUによる極限保存を使うのは、まず得られたBEの極限錐の**像**の検収。Uが保存するからBEの元の錐が極限だ、と逆向きに推論しない。BEの元の普遍性は既存frameのHom比較・模型の導来普遍性と指定native錐の橋から得る必要がある。

### 152.3 実現側・制限の型案

```lean
-- R06：既存の左frame・cofibrant重み・図式置換からの計算全関手。
def strictBERealizationModel : (J₋ ⥤ E) ⥤ E
def strictBERealizationVertex : B₋ ⟶ CA := nerveMap strictBERealizationModel ≫ S

-- R07：全パラメータの指定余錐と両境界。
def strictBERealizationCoconeFamily : join K₋ (Δ[0] : SSet.{u+1}) ⊗ B₋ ⟶ CA
-- 左境界 = evalBE₋、右境界 = pointLeftProjection B₋ ≫ strictBERealizationVertex。
def strictBERealizationCocone (F : J₋ ⥤ E) : JoinCocone (strictBE F)
theorem strictBERealizationCoconeFamily_at (F : J₋ ⥤ E) :
  pointRightSection (join K₋ Δ[0]) (nerveVertex F) ≫
    strictBERealizationCoconeFamily = (strictBERealizationCocone F).val

-- R08：同じ余錐そのもののnative余極限性。
theorem strictBERealizationCocone_isColimit (F : J₋ ⥤ E) :
  IsColimitCone (strictBERealizationCocone F)

-- R09：台のstrict図式の実現への全比較と同じ余錐の制限。
def strictBERealizationUnderlyingIso : FunctorIso
  (strictBERealizationVertex ≫ U)
  (nerveMap forgetSimplicial ≫ complexRealizationVertexFamily)
def strictBERealizationUnderlyingCoconeFamilyIso : FunctorIso
  (strictBERealizationCoconeFamily ≫ U)
  ((𝟙 _ ⊗ₘ nerveMap forgetSimplicial) ≫ complexRealizationCoconeFamily)
-- 両境界の制限はS≫Uの既存比較とstrictBERealizationUnderlyingIso。

-- R10：strict図式の∞局所化上の全関手比較。
def strictBERealizationLocalizedUnderlyingIso : FunctorIso
  (RealizeBE ≫ U) (ForgetStrictBEInfinity ≫ RealizeDA)
```

R06は「通常colimの台が通常colim」という事実のみで導来実現の台を同定しない。R09の `complexRealizationCoconeFamily` は③-aの3b-3が組み立てる3b-1第四行の全族を要求する。R05・R10に出るstrict図式局所化の実評価は、元の通常図式の射・全単体との指定同型付きで受け取る。BE図式局所化と任意の `Fun(K±,CA)` の評価同値を、加群版のR2から無条件には導かない。

最後にR11として、既存の離散BE埋め込みに制限したR02〜R05が⑤aの `ofCosimplicial_forget`・`TotalizationCone` の**既存の型・同じ指定頂点**へ一致する照合を置く。ここは⑤aの更新後の入口の型を読む段で、欄の型をこちらで変えない。R12は係数変更と指定錐族の制限の両立。必要な全同型の型を⑤aの既存欄に合わせてから確定する。この二つを確定前から完了項目に数えない。

### 152.4 置き場所・見込み・停止境界

| 束 | 提案する新規ファイル | 見込み（行、docstring/import込み） |
| --- | --- | ---: |
| R01〜R03 strict Totの模型・同じnative錐族 | `EInfinity/BarrattEccles/StrictDiagramTotalizationComparison*.lean` | 1,400〜2,300 |
| R04〜R05 TotのU比較・局所化への全輸送 | `.../StrictDiagramTotUnderlying*.lean` | 1,000〜1,800 |
| R06〜R08 strict実現の模型・同じ余錐族 | `.../StrictDiagramRealizationComparison*.lean` | 1,600〜2,800 |
| R09〜R10 実現のU比較・全関手比較 | `.../StrictDiagramRealizationUnderlying*.lean` | 1,200〜2,000 |
| R11〜R12 離散制限・既存入口・係数変更の照合 | `.../StrictDiagramDiscreteCompatibility*.lean` | 500〜900 |
| 合計 | | **5,700〜9,800** |

これは新しい承認済み外枠ではなく、3b-1/G10の実測を踏まえた**紙の提案**。R11・R12の型とBEのnative錐への模型の橋を読んだ後で再見積もりする。一般になった錐の等式移送・族の貼り合わせはKerodon、加群の共通比較はHA/DerivedCategoryModels、BE固有の照合だけを新規BEファイルに置く。既存 `FramedLimit*`、`CAlgUnderlyingDerivedComparison`、⑤aのファイルを変更・再構築しない。点つきKanのTotは作らない。今回この紙のためのBEビルドは行っていない。


## 153. 外枠直前の保存点：停止点2aは完成、Dは未完（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。B4は§137で完了済み。B・Cの停止点2aはコード `b43d4be81`、報告 `ecb21022f`（表の訂正 `fe5555f64`）。その後のD補助五本は **`acfde8f61`**。停止点2b・G10全体の完成は未達成。

### 153.1 最終検収

§151の最終の二本の鍵付き対象ビルド174は **7,850 jobs・終了コード0**、小監査は **12宣言（4・8）、標準三公理のみ**（`/private/tmp/isw2-build174.log`）。173の三本21宣言と合わせ、今回D補助五本の監査は **33宣言**。これは新規五本だけの小監査であり、全段階II・全326本を今回再監査した数字ではない。途中の失敗172は成功に含めない。

鍵は各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限の増加、既存宣言・⑤a・入口・公式監査・mainへの変更なし。rootビルド・大きな監査なし。未検証のLean下書きは残さない。

全累計の対象一覧は永続ファイル `formalization-plans/stage-ii/is-w2-g10-20261114-modules.json` にも保存した。これはG10累計の対象一覧であり、mainへ未登録の差分一覧を自動的に意味しない。今回追加分の登録候補は§149〜§151に列挙した各モジュール。入口・公式監査への登録は調整役に任せる。

### 153.2 外枠と、次に残る具体的な束

現ソースを一覧から再集計して **326モジュール・19,901行**、外枠20,000行まで **99行**。Dの全族の型を弱めたり、既存の部分補題を不自然に圧縮して枠を空けたりはしない。

| 未完の項目 | 次に必要な同じ構成の照合 | 追加見込み |
| --- | --- | ---: |
| D01〜D03 | §151の実複体代表の自然性を、同じΓ・反転・豊穣Hom・BK切断の比較へ運び、元の全join錐を全パラメータで貼り合わせる。両境界と各Xでの**同じ全join射**を閉じる | 350〜650行 |
| D04 | 頂点辺の式は§151で証明済み。D02で全族の左境界をこの同じ `derivedTotVertexFamily` と確定して接続する | 上の束に含む |
| D05〜D06 | `rawCosimplicialModuleCone` を、既存 `discreteTotalCochainNatIso` により**整数零延長した交代余面複体を頂点とする**指定錐へ移す。raw頂点とその頂点の等号を仮定しない | 150〜250行 |
| D07〜D08 | 同じ離散頂点移送を全図式射・全錐族に行い、既存の導来ホモロジー比較へ接続する | 250〜450行 |
| 合計 | | **750〜1,350行** |

99行の残枠では、次のD01の全join族と各点の厳密照合の束を収められない所まで来た。`coordination.md` §2（62〜65行の規模上限・型つき一覧・代わりの紙の作業）とIS-W2 §16の外枠に従い、**検証済みをコミットした上で、この線の追加Leanをここで区切る**。新しい第五のまとまり・範囲の縮小・新しい模型圏仮定を要求しているのではなく、承認済みDの同じ型の工程が残る。数を使い切るための補題追加はしない。

代わりの紙の作業として§152に、3b-4の§38.2の1・2について、既存部品、全関手・同じ指定錐族の型案、③-aの3b-3を使う場所、規模の案を残した。BEの新規Leanや点つきKanのTotは開始していない。この紙をG10や3b-4の検証済み完成と数えない。再開箇所は上表のD01の全族への自然性の輸送であり、B4やB・Cの再実装ではない。


## 154. 再開：D01の指定複体代表から点ごとの実Γまでの全自然性（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01〜D08の最終結論は未完であり、今回の法則・証明分割をIDの完了数へ加えない。前ターンは停止点2aとD補助の検証・コミットという進捗。mainの `d7b418962` を作業枝へfast-forwardで取り込み、IS-W2 §17・§18と /goal 更新を読んで再開した。旧20,000行の停止は解除、G10の外枠は **23,000行**。G10後の3b-4はTot側を先に、外枠15,000行、停止点3b-4a・3b-4bの後に任意coherent BE図式の段0まで進む指示を保持する。

### 154.1 型と登録候補

同じ閉零射によるHom図式の前合成を構成済みの行合成則に特殊化し、元の指定BK錐代表の図式方向と頂点方向の自然性を一致させた。その等式を既存 `normalizedLinearWeightHomEquiv_postcomp` と `pointwiseTruncationGammaIso` の全自然性で移した。新しい比較・点・錐を選び直さず、Moore反転と再反転も元のもの。新しい数学のまとまりではなくD01の既存構成の自然性・合成・係数移送の法則。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeSourceNaturality`（98行）。

```lean
def bousfieldKanHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) where
  app j := homPrecompose f (X.obj ((opOpEquivalence SimplexCategory).functor.obj j))
  naturality i j a

def normalizedBKConeSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor Q).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X))

theorem normalizedBKConeSourceMap_f {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) (q : ℤ) :
    (normalizedBKConeSourceMap f X).f q =
      homDiagramDegreePrecompose X 0 q q (zero_add q) (Cochain.ofHom f)

theorem normalizedBousfieldKanRepresentative_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (f : P ⟶ Q)
    (g : Q ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative Q X g ≫ normalizedBKConeSourceMap f X =
      normalizedBousfieldKanRepresentative P X (f ≫ g)

theorem normalizedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      normalizedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSetConeNaturality`（86行）。

```lean
def bousfieldKanSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplicialObject (SimplexCategoryᵒᵖᵒᵖ ⥤ Type u)

theorem normalizedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      normalizedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

theorem reflectedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      reflectedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y

theorem reflectedBousfieldKanSetCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedBousfieldKanSetCone X ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reflectedBousfieldKanSetCone Y ≫
        (bousfieldKanSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBKConeNaturality`（107行）。

```lean
def pointwiseBKSetHomFunctor :
    CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ ⥤
      SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u}

def pointwiseBKSetHomComparison
    (H : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ)

theorem pointwiseBKSetHomComparison_naturality
    {H H' : CochainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat.{u} A) ℤ} (f : H ⟶ H') :
    (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)).map
        ((bousfieldKanSetHomFunctor A).map f) ≫ pointwiseBKSetHomComparison A H' =
      pointwiseBKSetHomComparison A H ≫ (pointwiseBKSetHomFunctor A).map f

theorem reversedWeightPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reversedWeightPointwiseBousfieldKanCone X ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f) =
      reversedWeightPointwiseBousfieldKanCone Y ≫
        (pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y)

theorem reflectedPointwiseBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    reflectedPointwiseBousfieldKanCone X ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f))
          SimplicialObject.opFunctor =
      reflectedPointwiseBousfieldKanCone Y ≫
        Functor.whiskerRight ((pointwiseBKSetHomFunctor A).map
          (normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y))
          SimplicialObject.opFunctor

```

`pointwiseBKSetHomComparison A H` の推論された型は、`(flipFunctor Δᵒᵖ Δᵒᵖᵒᵖ (Type u)).obj ((bousfieldKanSetHomFunctor A).obj H) ⟶ (pointwiseBKSetHomFunctor A).obj H`。上の紙の表示で型を省いた場合もこの全図式射を意味し、各点のHomの元だけの主張ではない。

### 154.2 検収と継続箇所

コード **`00613f0ed`**。鍵付き対象ビルド175・176・177はそれぞれ **2,759・2,772・2,785 jobs、終了コード0**。各新規一本だけの小監査は **9・8・10宣言、いずれも標準三公理のみ**（合計27は今回三本だけの数字）。ログ `/private/tmp/isw2-build175.log`〜`177.log`。各回 `--class impl --wait 3600`、整理券一枚、対象ビルド・小監査の間だけ保持して返却済み。sorry・新公理0、計算上限の増加、既存宣言、⑤a、入口・公式監査・mainへの変更なし。200行超のファイルなし。

累計 **329モジュール・20,192行**、外枠まで **2,808行**。累計一覧は `is-w2-g10-20261114-modules.json`。D01の全錐族はまだ構成していない。次は同じΓ比較と実豊穣Homの前合成を照合する `DoldKanClosedPrecomposition`（未検証の草稿）と、その比較による同じBK錐の自然性の移送。D02〜D08と3b-4の範囲を削らず継続する。


## 155. D01の途中：実豊穣Hom・native錐の同じ入力・混合係数への接続（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01の全族はまだ未完。以下は既存構成の自然性・単位・合成・係数移送・表示の法則と証明分割で、ID付きの新しい数学を加えない。

### 155.1 型と登録候補

元の閉零射の前合成と標準Hom鎖写像を全単体で同定し、点ごとのΓ比較を実豊穣Homへ戻した。既存の前後作用の全関手則で合成・交換を確認し、その同じ等式を実際のAsSmall添字・指定BK重みへ引き戻した。native錐を作った入力そのものの両作用の一致であり、別の錐を選び直したものではない。

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DoldKanClosedPrecomposition`（79行）。

```lean
theorem standardChainMap_closedPrecomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    Functor.whiskerRight
      (SerrePositivity.EInfinity.ComplexLimits.standardModuleChainMap
        (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)))
      (forget (ModuleCat R)) =
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z)

theorem doldKanSimplicialHomIso_precomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z) ≫
        (doldKanSimplicialHomIso (R := R) x z).hom =
      (doldKanSimplicialHomIso (R := R) y z).hom ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
            (truncLE'Map (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z))
              (ComplexShape.embeddingUpIntLE 0))) (forget (ModuleCat R))

theorem complexDoldKanHomIso_precomposition {A : Type u} [CommRing A]
    {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    eHomWhiskerRight SSet ((SerrePositivity.EInfinity.ComplexLimits.complexToClosed A).map f)
        (ForgetEnrichment.of (Complex A) T) ≫ (complexDoldKanHomIso A P).hom.app T =
      (complexDoldKanHomIso A Q).hom.app T ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
            (truncLE'Map (homPrecompose f T) (ComplexShape.embeddingUpIntLE 0)))
          (forget (ModuleCat A))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKConeNaturality`（111行）。

```lean
def enrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    SimplexCategoryᵒᵖᵒᵖ ⥤ SSet.{u}

def enrichedBKHomIso (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram P X ≅ (pointwiseBKSetHomFunctor A).obj
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X)))

def enrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomDiagram P X ⟶ enrichedBKHomDiagram P Y

def enrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomDiagram Q X ⟶ enrichedBKHomDiagram P X

theorem enrichedBKHomIso_target_naturality (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBKHomTargetMap P f ≫ (enrichedBKHomIso P Y).hom =
      (enrichedBKHomIso P X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeTargetMap P f)

theorem enrichedBKHomIso_source_naturality {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap f X ≫ (enrichedBKHomIso P X).hom =
      (enrichedBKHomIso Q X).hom ≫
        (pointwiseBKSetHomFunctor A).map (normalizedBKConeSourceMap f X)

theorem enrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    enrichedBousfieldKanCone X ≫
        Functor.whiskerRight (enrichedBKHomTargetMap ((productTotalFunctor A).obj X) f)
          SimplicialObject.opFunctor =
      enrichedBousfieldKanCone Y ≫
        Functor.whiskerRight (enrichedBKHomSourceMap ((productTotalFunctor A).map f) Y)
          SimplicialObject.opFunctor

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKHomComposition`（58行）。

```lean
theorem enrichedBKHomTargetMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomTargetMap P (𝟙 X) = 𝟙 (enrichedBKHomDiagram P X)

theorem enrichedBKHomTargetMap_comp (P : Complex A)
    {X Y Z : CosimplicialObject (Complex A)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    enrichedBKHomTargetMap P (f ≫ g) =
      enrichedBKHomTargetMap P f ≫ enrichedBKHomTargetMap P g

theorem enrichedBKHomSourceMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (𝟙 P) X = 𝟙 (enrichedBKHomDiagram P X)

theorem enrichedBKHomSourceMap_comp {P Q T : Complex A} (f : P ⟶ Q) (g : Q ⟶ T)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (f ≫ g) X =
      enrichedBKHomSourceMap g X ≫ enrichedBKHomSourceMap f X

theorem enrichedBKHomSourceMap_targetMap {P Q : Complex A} (f : P ⟶ Q)
    {X Y : CosimplicialObject (Complex A)} (g : X ⟶ Y) :
    enrichedBKHomSourceMap f X ≫ enrichedBKHomTargetMap P g =
      enrichedBKHomTargetMap Q g ≫ enrichedBKHomSourceMap f Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.LiftedBKConeNaturality`（57行）。

```lean
def liftedEnrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} SimplexCategory ⥤ SSet.{u}

def liftedEnrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBKHomDiagram P X ⟶ liftedEnrichedBKHomDiagram P Y

def liftedEnrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    liftedEnrichedBKHomDiagram Q X ⟶ liftedEnrichedBKHomDiagram P X

theorem liftedEnrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBousfieldKanCone X ≫
        liftedEnrichedBKHomTargetMap ((productTotalFunctor A).obj X) f =
      liftedEnrichedBousfieldKanCone Y ≫
        liftedEnrichedBKHomSourceMap ((productTotalFunctor A).map f) Y

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSmallShape`（37行）。

```lean
def smallNativeTotConeDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj
      (join (Δ[0] : SSet.{u}) (nerve (AsSmall.{u} SimplexCategory))) ⟶ dgNerve A (Complex A)

theorem smallNativeTotConeDiagram_restore (X : CosimplicialObject (Complex A)) :
    (uliftConeShapeIso (nerve (AsSmall.{u} SimplexCategory)) 0).inv ≫
      smallNativeTotConeDiagram X = (nativeDGCone X).val

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficientNaturality`（41行）。

```lean
theorem weightedCoherentCoefficient_map (α : H ⟶ H')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (n + 1)) :
    weightedCoherentCoefficient
        (τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor)) j =
      weightedCoherentCoefficient τ j ≫ α.app (σ.obj j)

theorem weightedCoherentCoefficient_dinaturality (α : H ⟶ H'') (β : H' ⟶ H'')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ H' ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ (Functor.whiskerRight β SSet.opFunctor))
    (j : Fin (n + 1)) :
    weightedCoherentCoefficient τ j ≫ α.app (σ.obj j) =
      weightedCoherentCoefficient τ' j ≫ β.app (σ.obj j)

```

### 155.2 検収

実豊穣Homと指定入力の四本はコード **`3c6f9197d`**。対象ビルド178は標準成分表示の書き換えで失敗し、鍵を返却した。表示を明示して修正した179は **5,944 jobs、終了コード0**、小監査 **3宣言**。180は **6,191 jobs、終了コード0**、新規一本 **17宣言**。181は **6,204 jobs、終了コード0**、新規二本 **12宣言（7・5）**。全て標準三公理のみ。失敗した178を成功に数えない。

同じ錐の小さい形状表示と混合係数の二本はコード **`bbc48fcc0`**。対象ビルド182・183は **6,048・2,246 jobs、終了コード0**、新規分の小監査は **4・2宣言、標準三公理のみ**。ログ `/private/tmp/isw2-build179.log`〜`183.log`。各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ鍵を保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限、既存宣言、⑤a、入口・公式監査・mainの変更なし。各ファイル200行以内。

累計 **335モジュール・20,575行**、G10の外枠まで **2,425行**。累計一覧 `is-w2-g10-20261114-modules.json`。

### 155.3 mainの既存R6を再利用するD01の短い組み立て

mainの `StrictCoherentFamily A E K C` は、各パラメータでの**元の全dg nerve図式**と、全高次HA成分に厳密に可換する `StrictSimplexMap`、恒等・合成・全面・退化の整合性から、同じ全パラメータ評価を作る。`StrictCoherentFamilyEvaluation.lean` の `.evaluation` は `nerve C ⊗ (uliftFunctor.obj K) ⟶ dgNerve A E`。これは今回必要な全族の組み立ての既存部品として使える。新しいcollageや全族評価を一から作らない。

`K := join (Δ[0] : SSet.{u}) (nerve (AsSmall.{u} SimplexCategory))`、`C := CosimplicialObject (Complex A)`、`E := Complex A` とし、`.obj X` に今回検証した `smallNativeTotConeDiagram X` をそのまま置く。その形状同型を戻せば、元の `nativeDGCone X` の全join射になることも検証済み。

残る接続は次の順。

1. 各図式射fの元の閉零成分（左頂点は `productTotalFunctor.map f`、右頂点は `f.app n`）を、全HA成分に可換する `StrictSimplexMap` にする。同じ立方体の旗の評価とcoherent比較の前後作用への自然性を使う。新規の草稿 `CubeEvaluationChainNaturality`・`CoherentComparisonStrictNaturality` はこの既存構成の法則の分割。
2. mixedなweighted coneのHomでの自然性には、今回検証済みの `liftedEnrichedBousfieldKanCone_dinaturality` と `weightedCoherentCoefficient_dinaturality` を使う。尾部は元の図式射の自然性、逆方向の空Homは空型の消去。高次成分を通常の辺の自然性だけで代用しない。
3. `StrictSimplexMap.ext` で単位・合成を、同じ引き戻しと `.hext` で全面・退化を確認して `StrictCoherentFamily` へ入れる。既存の `.evaluation` を使い、積の順序と同じ形状同型を戻し、同じ出力分解へ後合成してD01の全族にする。
4. 既存 `orderedSimplexFamily_const` による各点の同じ全単体への復元と、前面・頂点への制限を使ってD02・D03を閉じ、§151の同じ頂点関手とD04を接続する。

この経路はD01の指定された構成の証明分割で、範囲・型の変更ではない。新しい一般の厳密化定理や模型圏仮定は足さない。D05〜D08、続くBEのTot・実現と任意coherent BE図式の段0を保持して継続する。


## 156. D01の途中：同じnative錐の全セル識別と全高次HA写像（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。D01の全族の完成はまだ主張しない。以下は既存構成の係数移送・単位・合成・自然性・表示・貼り合わせの法則と証明分割。

### 156.1 型と登録候補

立方体の符号付き旗和が元のHom鎖写像に可換することから、全豊穣Homの可換式を `coherentComparisonStrictMap` の**全高次HA成分の厳密可換式**へ移した。weighted coneの頂点・尾部・混合・空Homを照合し、元の図式射のTot成分と各次数の成分を持つ `nativeTotWeightedSimplexMap` と、その単位・合成則を閉じた。

さらに、元のnative錐のcoslice切断の**任意次数**の評価と、パラメータ第一射影の係数則を使い、局所weighted単体が元の同じ全join射のセル制限そのものであることを `nativeTotCone_cellMap`・`_cellSimplex` で証明した。ここは辺だけの照合でも、FunctorIsoによる別のセルへの取り換えでもない。

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CubeEvaluationChainNaturality`（56行）。

```lean
theorem standardTopEval_chainMap (f : homObject R D x y ⟶ homObject R E x' y')
    (m : ℕ) (s : StandardSimplex R x y m) :
    standardTopEval x' y' m ((standardModuleChainMap f).app (Opposite.op ⦋m⦌) s) =
      f.f (-(m : ℤ)) (standardTopEval x y m s)

theorem cubeFlagEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeFlagEvaluation e (φ ≫ Functor.whiskerRight (standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeFlagEvaluation e φ)

theorem cubeEvaluation_chainMap {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (f : homObject R D x y ⟶ homObject R E x' y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y) :
    cubeEvaluation e (φ ≫ Functor.whiskerRight (standardModuleChainMap f)
      (forget (ModuleCat R))) = f.f (-(m : ℤ)) (cubeEvaluation e φ)

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoherentComparisonStrictNaturality`（70行）。

```lean
theorem cubeEvaluation_closed_naturality {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    {x y x' y' : D}
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) x')
    (g : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) y')
    (φ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x y)
    (ψ : SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶
      standardHomSpace (R := R) x' y')
    (h : φ ≫ eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) g =
      ψ ≫ eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) y')) :
    compose R (closedHomEquiv R D _ _ g).val (cubeEvaluation e φ) (add_zero (-(m : ℤ))) =
      compose R (cubeEvaluation e ψ) (closedHomEquiv R D _ _ f).val
        (zero_add (-(m : ℤ)))

def coherentComparisonStrictMap {n : ℕ}
    (s t : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (f : ∀ i, s.obj i ⟶ t.obj i)
    (hf : ∀ i j, s.map i j ≫ eHomWhiskerLeft SSet (s.obj i) (f j) =
      t.map i j ≫ eHomWhiskerRight SSet (f i) (t.obj j)) :
    StrictSimplexMap R D (coherentSimplexData s) (coherentSimplexData t) where
  app i := closedHomEquiv R D _ _ (f (.mk (ULift.up i)))
  naturality I a b k hI ha hb hk

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightedConeComparisonStrictMap`（39行）。

```lean
def weightedConeComparisonStrictMap {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : ClosedCategory R D} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor)) :
    StrictSimplexMap R D (coherentSimplexData (weightedConeSimplex F x τ))
      (coherentSimplexData (weightedConeSimplex G y τ'))

```

登録候補：`SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.UliftPointSimplexEvaluation`（47行）。

```lean
theorem uliftPointSimplexEvaluation (K E Q : SSet.{u})
    (p : (Δ[0] : SSet.{u}) ⟶ E) (f : K ⊗ E ⟶ Q)
    {n : ℕ} (σ : K _⦋n⦌) (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let U := SSet.uliftFunctor.{v,u}
    let e := (uliftStdSimplexIso.{u,v} 0).inv ≫ U.map p
    let s := inv (fst (U.obj K) (Δ[0] : SSet.{max u v})) ≫
      (U.obj K ◁ e) ≫ (uliftTensorIso K E).inv ≫ U.map f
    s.app (Opposite.op ⦋n⦌) (ULift.up σ) =
      ULift.up (f.app (Opposite.op ⦋n⦌)
        (σ, p.app (Opposite.op ⦋n⦌) a₀))

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ClosedVertexWhiskering`（56行）。

```lean
theorem closedVertex_whiskerLeft {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet f ≫ eHomWhiskerLeft SSet x g = eHomEquiv SSet (f ≫ g)

theorem closedVertex_whiskerRight {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv SSet g ≫ eHomWhiskerRight SSet f z = eHomEquiv SSet (f ≫ g)

theorem enrichedUnit_whiskering {x y : C} (f : x ⟶ y) :
    eId SSet x ≫ eHomWhiskerLeft SSet x f =
      eId SSet y ≫ eHomWhiskerRight SSet f y

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeHomNaturality`（97行）。

```lean
theorem weightedConeTailHom_naturality {n : ℕ} {F G : Fin (n + 1) ⥤ C}
    (η : F ⟶ G) (i j : Fin (n + 1)) :
    weightedConeTailHom F i j ≫ eHomWhiskerLeft SSet (F.obj i) (η.app j) =
      weightedConeTailHom G i j ≫ eHomWhiskerRight SSet (η.app i) (G.obj j)

def weightedConeHomTargetMap (η : F ⟶ G) (x : C) :
    simplicialHomDiagram F x ⟶ simplicialHomDiagram G x

def weightedConeHomSourceMap {x y : C} (f : x ⟶ y) (G : I ⥤ C) :
    simplicialHomDiagram G y ⟶ simplicialHomDiagram G x

def weightedConeVertexMap {n : ℕ} (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (σ : ComposableArrows I n) (i : Fin (n + 2)) :
    weightedConeObj x (σ ⋙ F) i ⟶ weightedConeObj y (σ ⋙ G) i

theorem weightedConeHom_naturality {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor))
    (i j : Fin (n + 2)) :
    weightedConeHom F x τ i j ≫ eHomWhiskerLeft SSet
        (weightedConeObj x (σ ⋙ F) i) (weightedConeVertexMap η f σ j) =
      weightedConeHom G y τ' i j ≫ eHomWhiskerRight SSet
        (weightedConeVertexMap η f σ i) (weightedConeObj y (σ ⋙ G) j)

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedNerveCoefficientProjection`（32行）。

```lean
theorem weightedNerveCoefficients_fst (B : SSet.{u}) (φ : bousfieldKanWeight I ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ B) :
    weightedNerveCoefficients
        (fst (bousfieldKanWeight I) ((Functor.const I).obj B) ≫ φ) σ a =
      prefixOverWeight σ ≫ Functor.whiskerLeft σ φ

```

登録候補：`SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeCellEvaluation`（31行）。

```lean
theorem coherentConeCosliceSection_cell {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (z : X _⦋0⦌) (h : c.vertex = z) {n : ℕ} (σ : K _⦋n⦌) :
    (((coherentConeCosliceSection c ≫ eqToHom (congrArg
      (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
        (Opposite.op ⦋n⦌) σ)).val =
      joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm σ) ≫ c.val

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplex`（73行）。

```lean
def liftedClosedDiagramMap {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedClosedDiagram X ⟶ liftedClosedDiagram Y

def nativeTotWeightedPrefix (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    simplexPrefixWeight n ⟶ σ ⋙
      simplicialHomDiagram (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) ⋙ SSet.opFunctor

def nativeTotWeightedSimplexData (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) : SimplexData A (Complex A) (n+1)

theorem nativeTotWeightedPrefix_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomTargetMap (liftedClosedDiagramMap f)
            (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))) SSet.opFunctor) =
      nativeTotWeightedPrefix Y σ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight
          (weightedConeHomSourceMap ((complexToClosed A).map ((productTotalFunctor A).map f))
            (liftedClosedDiagram Y)) SSet.opFunctor)

def nativeTotWeightedSimplexMap
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    StrictSimplexMap A (Complex A) (nativeTotWeightedSimplexData X σ)
      (nativeTotWeightedSimplexData Y σ)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedSimplexComposition`（66行）。

```lean
theorem nativeTotWeightedSimplexMap_id (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (𝟙 X) σ = StrictSimplexMap.id (nativeTotWeightedSimplexData X σ)

theorem nativeTotWeightedSimplexMap_comp {X Y Z : CosimplicialObject (Complex A)}
    (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedSimplexMap (f ≫ g) σ =
      (nativeTotWeightedSimplexMap f σ).comp (nativeTotWeightedSimplexMap g σ)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotConeSectionSimplex`（79行）。

```lean
theorem nativeTotCone_cosliceSection_simplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    let I := AsSmall.{u} SimplexCategory
    let F := liftedClosedDiagram X
    let z := ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)
    let φ := liftedEnrichedBousfieldKanCone X
    ((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ)) =
    weightedCosliceSimplex F z
      ((weightedNerveSectionFromTransform
        (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ)).app
          (Opposite.op ⦋n⦌) (σ, a₀))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification`（79行）。

```lean
theorem nativeTotCone_cosliceCell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    (((coherentConeCosliceSection (nativeCoherentCone X) ≫ eqToHom (congrArg
      (fun w : (SimplicialNerve (ClosedCategory A (Complex A))) _⦋0⦌ =>
        sliceUnder (SSet.yonedaEquiv.symm w)) (nativeCoherentCone_vertex X))).app
          (Opposite.op ⦋n⦌) (ULift.up σ))).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ))

theorem nativeTotCone_cellMap (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val =
      (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        (weightedConeSimplex (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
          (nativeTotWeightedPrefix X σ))

theorem nativeTotCone_cellSimplex (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : (nerve (AsSmall.{u} SimplexCategory)) _⦋n⦌)
    (a₀ : (Δ[0] : SSet.{u}) _⦋n⦌) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ)) ≫
        (nativeCoherentCone X).val) =
      weightedConeSimplex (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
        (nativeTotWeightedPrefix X σ)

```

### 156.2 検収・実測

立方体・全coherent比較の二本は **`22125d8a0`**。鍵付き対象ビルド184は **3,790 jobs・終了コード0**、新規一本3宣言の小監査。185は **5,949 jobs・終了コード0**、新規一本5宣言の小監査。184ではmainの既存 `StrictSimplexMap` も必要な依存として対象だけ生成したが、新規監査の数には含めていない。

weighted coneから元の全セルまでの十本は **`e9bdb2d07`**。対象ビルド186・187・188・189はそれぞれ **5,953・6,213・6,273・6,275 jobs、終了コード0**。各新規分の小監査は **10（3・5・2）・15・4（2・1・1）・5（1・1・3）宣言**。全て標準三公理のみ。これらは今回の新規対象だけの分割監査であり、全累計の再監査ではない。ログ `/private/tmp/isw2-build184.log`〜`189.log`。

各回 `--class impl --wait 3600`、整理券一枚、対象ビルドと小監査の間だけ鍵を保持し、各ハンドルの終了コード0を確認して返却済み。sorry・新公理0、計算上限・再帰上限の増加、既存宣言、⑤a、入口・公式監査・mainの変更なし。200行超のファイルなし。

累計 **347モジュール・21,300行**、外枠23,000行まで **1,700行**。累計一覧 `is-w2-g10-20261114-modules.json`。

### 156.3 そのまま継続する接続

D01の残りは、これら同じセルの写像を全面・退化と整合する**全錐形状**での `StrictCoherentFamily` へまとめ、既存 `.evaluation` を同じ形状同型で戻して元の出力分解へ後合成する所。`nativeTotCone_cellSimplex` は頂点を保持する全cosliceセルの識別を与えたが、これだけで任意のjoin単体上の全面・退化の整合性が済んだとは数えない。純粋な左頂点・右面と、重複した左頂点を持つ混合単体も既存の引き戻しとして照合する。新しい全族評価の構成は作り直さない。

その後、元の両境界・各Xでの同じ全join射（D02・D03）、保存済みの頂点辺の式（D04）、離散の整数零延長した交代余面複体への頂点移送・全族・ホモロジー入口（D05〜D08）を閉じる。3b-4の承認済みTot先行の範囲と、さらに実現・任意coherent BE図式の段0までの目標は保持している。今回は中間停止・承認待ち・目標の縮小ではなく、検証済みの保存点。


## 157. D01の全join族と元の同じ指定錐への全単体での復元（2026-11-14）

一覧：済み 28／全体 36（うち追加 1）。以下はD01〜D03の証明の分割と、既存構成の単位・自然性・貼り合わせ・表示の法則。最終D型の導来入口と両境界は引き続き接続中で、IDを先に完了として数えない。

§156の全join形状での構成は、mainの既存R6をさらに短く使い、各セルの `StrictSimplexCategory` 関手評価を既存cosliceの切断に入れて `sliceUnderUncurry` で貼り合わせる形にした。新しい評価原理・厳密化定理を作らず、純粋な左右面と重複した初点を含む全join単体は同じcosliceの既存普遍性で扱う。固定Xで元の `nativeDGCone X` の全射に厳密に戻る等式も示した。頂点や脚だけの照合ではない。

### 157.1 追加した法則・証明分割の型

共通：`A : Type u`、`[CommRing A]`。各型の名前空間・importは同名ソースのとおり。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellFamily`（72行）。

```lean
def nativeTotWeightedCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) (n+1)

def nativeTotWeightedCellFamily {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}) ⟶ dgNerve A (Complex A)

theorem nativeTotWeightedCellFamily_at {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1}))) ≫
      nativeTotWeightedCellFamily A σ =
    (leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (nativeTotWeightedCellFunctor A σ |>.obj X |>.val)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedReindex`（78行）。

```lean
theorem nativeTotWeightedPrefix_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
          (nativeTotWeightedPrefix X σ)

theorem nativeTotWeightedSimplex_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) =
    (coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X σ))).pullback (prependOrderHom α.toOrderHom)

theorem nativeTotWeightedSimplexMap_reindex
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    HEq (nativeTotWeightedSimplexMap f ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))
      ((nativeTotWeightedSimplexMap f σ).pullback (prependOrderHom α.toOrderHom))

theorem nativeTotWeightedCellFunctor_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (prependOrderHom α.toOrderHom)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedApexFamily`（90行）。

```lean
def nativeTotClosedVertexFunctor :
    ClosedCategory A (Complex A) ⥤ StrictSimplexCategory A (Complex A) 0

theorem nativeTotWeightedCellFunctor_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙ strictSimplexPullbackFunctor A (Complex A)
        (SimplexCategory.const ⦋0⦌ ⦋n+1⦌ 0).toOrderHom =
      productTotalFunctor A ⋙ complexToClosed A ⋙ nativeTotClosedVertexFunctor A

def nativeTotApexFamily :
    nerve (CosimplicialObject (Complex A)) ⊗ (Δ[0] : SSet.{u+1}) ⟶
      dgNerve A (Complex A)

theorem nativeTotWeightedCellFamily_apex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ = nativeTotApexFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellNaturality`（41行）。

```lean
theorem nativeTotWeightedCellFamily_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFamily A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      (nerve (CosimplicialObject (Complex A)) ◁
        joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.stdSimplex.map α)) ≫
          nativeTotWeightedCellFamily A σ

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotFunctorCosliceFamily`（81行）。

```lean
def nativeTotFunctorCosliceSimplex {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (sliceUnder (curry (nativeTotApexFamily A))) _⦋n⦌

def nativeTotFunctorCosliceSection :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      sliceUnder (curry (nativeTotApexFamily A))

def nativeTotJoinFamily :
    nerve (CosimplicialObject (Complex A)) ⊗
      join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
          dgNerve A (Complex A)

theorem nativeTotJoinFamily_apex :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotApexFamily A

theorem nativeTotJoinFamily_cell {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinMap (𝟙 (Δ[0] : SSet.{u+1}))
        (SSet.yonedaEquiv.symm (ULift.up σ))) ≫ nativeTotJoinFamily A =
      nativeTotWeightedCellFamily A σ

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinEvaluation`（92行）。

```lean
theorem nativeTotJoin_cell_ext {K L T : SSet.{u+1}} {f g : join K L ⟶ T}
    (hleft : joinInl K L ≫ f = joinInl K L ≫ g)
    (hc : ∀ (n : ℕ) (σ : L _⦋n⦌),
      joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ f =
        joinMap (𝟙 K) (SSet.yonedaEquiv.symm σ) ≫ g) : f = g

theorem nativeTotJoinFamily_at_cell (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
      (lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
        nativeTotJoinFamily A) =
      joinMap (𝟙 (Δ[0] : SSet.{u+1})) (SSet.yonedaEquiv.symm (ULift.up σ) : (Δ[n] : SSet.{u+1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ≫
        (nativeDGCone X).val

theorem nativeTotJoinFamily_at (X : CosimplicialObject (Complex A)) :
    lift (SSet.const (ComposableArrows.mk₀ X))
        (𝟙 (join (Δ[0] : SSet.{u+1})
          ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))))) ≫
      nativeTotJoinFamily A = (nativeDGCone X).val

```

### 157.2 検収・残り

コード `3d090bc59`（二本150行）、`dd4962dd1`（三本212行）、`7e7941572`（一本92行）。対象ビルド191〜195はそれぞれ **6,531・6,532・6,534・6,535・6,536 jobs、終了コード0**。新規分だけの一時監査は **13・4・8（1・7）・9・3宣言**、すべて標準三公理のみ。190の結合則の書き換え失敗は、等式を単体ごとの表示で示してから合成する証明へ直し191で再検証済み。検証中の失敗を成功の数には含めていない。

鍵は各回 `--class impl --wait 3600`、整理券一枚、ビルド・小監査中だけ。全ハンドルの終了コード0を確認して返却済み。大きい累計監査・rootは実行していない。sorry・新公理0、計算・再帰上限の増加、既存宣言・⑤a・入口・公式監査・mainの変更なし。今回200行超のファイルなし。

検証済み累計 **353モジュール・21,754行**、外枠23,000行まで **1,246行**。累計JSONを今回の六本で更新。

次は同じ族を元の添字同型と既存の半自由出力分解へ後合成し、D01の型、D03の指定点制限、D02の両境界を閉じる。D04は既検証の同じ頂点辺の式へ接続する。D05〜D08、BEのTot先行・実現・任意coherent図式の紙の整理まで目標を保持して継続する。


## 158. D01・D03・D04完了、D02の両境界の照合（2026-11-14）

一覧：済み 31／全体 36（うち追加 1）。D01の全導来錐族、D03の元の同じ全指定錐への点制限、D04の図式射の像が対象ビルド・監査まで完了。D02は左境界と右境界の同じセルの照合までで、両境界の最終結論は未完。D05〜D08とBEの範囲を保持する。

D03は§151のとおり、標準零単体の第一射影の逆 `inv (fst J Δ[0])` を使う。紙の `ρ_.inv` はモノイダル単位PUnitの型なので、標準零単体との同型を含むこの表示にした。同様にD02左境界の紙の `λ_.hom` は標準零単体を左因子に持つ第二射影 `snd Δ[0] B` に固定。元の点・全パラメータ・全高次単体・既存の型は変えていない。

### 158.1 型と登録候補

共通：`A : Type u`、`[CommRing A]`。閉零頂点の二法則はmainの既存R6の計算を複体の場合へ同じ式で特殊化したもの。その他も既存構成の単位・合成・自然性・係数移送・貼り合わせの法則と一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamily`（102行）。

```lean
def derivedTotConeFamily :
    join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
        nerve (CosimplicialObject (Complex A)) ⟶ derivedInfinityCategory A

theorem derivedTotConeFamily_at_lift (X : CosimplicialObject (Complex A)) :
    lift (𝟙 (join (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))))
      (SSet.const (ComposableArrows.mk₀ X)) ≫ derivedTotConeFamily A =
        (strictDerivedTotCone X).val

theorem derivedTotConeFamily_at (X : CosimplicialObject (Complex A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex X)) ≫
        derivedTotConeFamily A = (strictDerivedTotCone X).val

theorem derivedTotConeFamily_map {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    (derivedTotVertexFamily A).app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk ((productTotalFunctor A).map f)).edge

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotClosedVertexEvaluation`（94行）。

```lean
lemma nativeTotClosedVertex_pullback_hom (M : ClosedCategory A (Complex A)) {n : ℕ}
    (α : Fin (n + 1) →o Fin 1) (T : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hT : 2 ≤ T.card)
    (ha : a = T.min' (Index.nonempty hT)) (hb : b = T.max' (Index.nonempty hT))
    (hk : k = 2 - (T.card : ℤ)) :
    ((closedNerveSimplex (A := A) (D := Complex A)
      ((Functor.const (Fin 1)).obj M)).pullback α).hom T a b k hT ha hb hk =
        closedNerveHom (𝟙 M) k

lemma nativeTotClosedVertexEvaluation (G : C ⥤ ClosedCategory A (Complex A)) :
    lift (𝟙 (nerve C)) (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) ≫
      strictSimplexFunctorEvaluation A (Complex A)
        (G ⋙ nativeTotClosedVertexFunctor A) =
      nerveMap G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

theorem nativeTotClosedVertexEvaluation_full (G : C ⥤ ClosedCategory A (Complex A)) :
    strictSimplexFunctorEvaluation A (Complex A) (G ⋙ nativeTotClosedVertexFunctor A) =
      fst (nerve C) (Δ[0] : SSet.{u+1}) ≫ nerveMap G ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeLeftBoundary`（77行）。

```lean
theorem nativeTotApexFamily_derived :
    nativeTotApexFamily A ≫ complexSemifreeResolutionInfinity A =
      fst (nerve (CosimplicialObject (Complex A))) (Δ[0] : SSet.{u+1}) ≫
        derivedTotVertexFamily A

theorem derivedTotConeFamily_left :
    (joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
      snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A))) ≫
        derivedTotVertexFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedTailFamily`（99行）。

```lean
def nativeTotTailCellFunctor {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    CosimplicialObject (Complex A) ⥤ StrictSimplexCategory A (Complex A) n

theorem nativeTotWeightedCell_tail (X : CosimplicialObject (Complex A)) {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    ((nativeTotWeightedCellFunctor A σ).obj X).val.pullback
        (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom = ((nativeTotTailCellFunctor A σ).obj X).val

theorem nativeTotWeightedCellFunctor_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (SimplexCategory.δ (0 : Fin (n+2))).toOrderHom =
      nativeTotTailCellFunctor A σ

theorem nativeTotWeightedCellFamily_tail {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1}) (Δ[n] : SSet.{u+1})) ≫
        nativeTotWeightedCellFamily A σ =
      strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ)

```

### 158.2 検収と実測

D01・D03・D04は **`2d6662535`**、左境界は **`9ad43eac1`**、右境界セルは **`13c3e3040`**。鍵付き対象ビルド196・197・198はそれぞれ **8,123・8,125・6,535 jobs、終了コード0**。各新規分だけの小監査は **5・5（3・2）・7宣言**、標準三公理のみ。ログ `/private/tmp/isw2-build196.log`〜`198.log`。各ハンドル終了コード0を確認、整理券一枚、`--class impl --wait 3600`、ビルド・小監査中だけ鍵を保持し返却済み。全体の新しい累計監査ではない。

sorry・新公理0、計算・再帰上限を増やさず、既存宣言・⑤a・入口・公式監査・mainは変更していない。今回も200行超のファイルなし。

検証済み累計 **357モジュール・22,126行**、外枠23,000行まで **874行**。登録候補JSONも同じ四本を追加。

次はD02右境界の対角評価を元の評価関手の全nerveと同定する。現在の `NativeTotTailCellEvaluation` は未検証草稿であり、累計に含めない。続いて両境界、離散の頂点輸送と全族・ホモロジー入口へ進む。


## 159. D02完了と、離散の全頂点輸送への短い経路（2026-11-14）

一覧：済み 32／全体 36（うち追加 1）。D01〜D04が全て対象ビルド・小監査まで完了。D05〜D08はまだ完了と数えない。

右境界の全セルを既存の底の面の法則で読み、閉零射の全射列の対角を元の評価関手のnerveと等置した。零次は閉零合成と `complexToClosed.map_comp`、高次は既存の零成分で示す。既定200,000 heartbeatsで巨大な表示の `change` が詰まった点は、`orderedSimplexFamily` の表示と零次の合成を分割して解消。計算上限は増やしていない。

### 159.1 型と登録候補

共通：`A : Type u`、`[CommRing A]`。既存構成の単位・合成・自然性・係数移送・表示・貼り合わせ則と、一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotTailCellEvaluation`（85行）。

```lean
def nativeTotClosedEvaluationNerve :
    nerve (CosimplicialObject (Complex A)) ⊗
      ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory))) ⟶
        nerve (ClosedCategory A (Complex A))

theorem nativeTotTailCellEvaluation_diagonal {n : ℕ}
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n)
    (d : ComposableArrows (CosimplicialObject (Complex A)) n) :
    (strictSimplexFunctorEvaluation A (Complex A) (nativeTotTailCellFunctor A σ)).app
      (Opposite.op ⦋n⦌) (d, ULift.up (𝟙 ⦋n⦌)) =
    closedNerveSimplex (((σ ⋙ AsSmall.down).prod' d) ⋙
      evaluationUncurried SimplexCategory (Complex A) ⋙ complexToClosed A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotJoinRightBoundary`（55行）。

```lean
theorem nativeTotJoinFamily_right :
    (nerve (CosimplicialObject (Complex A)) ◁
      joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))) ≫
      nativeTotJoinFamily A = nativeTotClosedEvaluationNerve A ≫
        closedNerveInclusion A (Complex A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeRightBoundary`（73行）。

```lean
theorem derivedTotConeFamily_right :
    (joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
        derivedTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DerivedTotConeFamilyBoundaries`（45行）。

```lean
theorem derivedTotConeFamily_boundaries :
    (joinInl (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
      snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (Complex A))) ≫
        derivedTotVertexFamily A ∧
    (joinInr (Δ[0] : SSet.{u+1})
        ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ
      𝟙 (nerve (CosimplicialObject (Complex A)))) ≫ derivedTotConeFamily A =
        derivedTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotFunctorCone`（106行）。

```lean
def rawDiscreteTotFunctorDiagram :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶
      (ihom (nerve (CosimplicialObject (ModuleCat.{u} A)))).obj (derivedInfinityCategory A)

def rawDiscreteTotFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A)

theorem rawDiscreteTotFunctorCone_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    (rawDiscreteTotFunctorCone A).val ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      (rawCosimplicialModuleCone A M).val

theorem rawDiscreteTotFunctorCone_isLimit : IsLimitCone (rawDiscreteTotFunctorCone A)

```

### 159.2 検収・実測

D02の四本は **`d2387aae7`**（258行）。鍵付き対象ビルド199は **8,130 jobs、終了コード0**、新規四本だけの小監査 **7（4・1・1・1）宣言、標準三公理のみ**。raw離散関手圏錐は **`61525eb4c`**（106行）。対象ビルド200は **8,136 jobs、終了コード0**、新規一本の小監査 **8宣言、標準三公理のみ**。ログ `/private/tmp/isw2-build199.log`・`200.log`、全ハンドル終了コード0を確認、鍵返却済み。整理券一枚、`--class impl --wait 3600`、対象ビルド・小監査中だけ鍵を保持。sorry・新公理0、既存宣言・⑤a・入口・公式監査・mainの変更なし。200行超のファイルなし。

検証済み累計 **362モジュール・22,490行**、外枠23,000行まで **510行**。累計JSONを同じ五本で更新。

### 159.3 残る離散四項の短い経路

独立に選んだMごとの錐を後から自然にする方法は使わず、今回のraw全族を一つの関手圏の極限錐へcurryした。各Mで元のraw錐の全join射に戻る式と、既存 `isLimitCone_of_pointwise` による極限性が検証済み。

その一つの錐に、既存 `complexOrdinaryDerivedNatTransIso` を `discreteTotalCochainNatIso.inv` に適用した全関手同型と、既存 `exists_limitCone_vertex_of_invertible` を使い、頂点を `functorVertex (nerveMap discreteCochainFunctor ≫ complexOrdinaryDerivedSource)` に厳密に固定する。これにより同じ頂点の全族とその評価錐を同時に選べる。関手圏の点ごとの極限の逆向きは既存 `isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits` を再利用し、評価した錐の極限性・頂点・全族の両境界・ホモロジー入口へ戻す。一般の頂点輸送・新しい厳密化・新しい模型圏構造を作らない。

このための `DiscreteTotApexTransport` は92行の未検証草稿で累計外。mainの既存 `DerivedNatTransIso`・`LimitConeVertexTransport` の二本が冷たい依存なので、対象だけをビルド201で生成してから照合する。この段階ではD05〜D08の最終結果を主張しない。外枠の残りを追跡し、上限を超える工程が必要になったら検証済みを保存して報告する。


## 160. 停止点2b：G10の完成（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。A01〜A12・A05a、B01〜B08、C01〜C07、D01〜D08が全て完了。停止点2aに加え、全図式射・全高次単体を持つ同じ指定Tot錐の全族、両境界、各図式での同じ全join射への厳密復元、離散入力の交代余面複体への頂点輸送と全族、整数次数への零延長を明記したホモロジー入口まで閉じた。

取り込み用コードの最終点は **`39d5ccd32`**（D05・D06と頂点輸送 **`5e2448beb`**、D01・D03・D04 **`2d6662535`**、D02 **`d2387aae7`** を含む）。停止点2a後に登録する新規40本を `is-w2-stop2b-20261114-modules.json` に分けた。全G10累計は `is-w2-g10-20261114-modules.json`。入口・公式監査・mainへの取り込みは調整役に任せ、こちらでは変更していない。

### 160.1 最後の四本の型

共通：`A : Type u`、`[CommRing A]`。D08は既存 `HasDerivedCategory.standard` をlocal instanceとして使い、追加の仮定にしていない。一般のSSetの模型圏仮定なし。全て既存構成の自然性・単位・合成・係数移送・貼り合わせの法則と、承認済み一覧の証明分割。

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotApexTransport`（93行）。

```lean
theorem discreteTotFunctorVertex_curry_fst {B D : SSet.{u+1}} (F : B ⟶ D) :
    SSet.yonedaEquiv (curry (fst B (Δ[0] : SSet.{u+1}) ≫ F)) = functorVertex F

theorem rawDiscreteTotFunctorCone_vertex :
    (rawDiscreteTotFunctorCone A).vertex =
      functorVertex (nerveMap (discreteTotalFunctor A) ≫ complexOrdinaryDerivedSource A)

def discreteTotCochainDerivedIso :
    FunctorIso (nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A)
      (nerveMap (discreteTotalFunctor A) ≫ complexOrdinaryDerivedSource A)

theorem exists_discreteCochainFunctorCone :
    ∃ c : JoinCone (rawDiscreteTotFunctorDiagram A), IsLimitCone c ∧
      c.vertex = functorVertex (nerveMap (discreteCochainFunctor A) ≫
        complexOrdinaryDerivedSource A)

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleCone`（96行）。

```lean
def discreteCochainFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A)

theorem discreteCochainFunctorCone_isLimit : IsLimitCone (discreteCochainFunctorCone A)

theorem discreteCochainFunctorCone_vertex :
    (discreteCochainFunctorCone A).vertex =
      functorVertex (nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A)

theorem rawDiscreteTotFunctorDiagram_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    evaluateFunctorDiagram (rawDiscreteTotFunctorDiagram A) (ComposableArrows.mk₀ M) =
      strictCosimplicialModuleNerve A M ≫ discreteModuleSource A

theorem discreteCochainFunctorCone_isPointwise :
    IsPointwiseLimitCone (discreteCochainFunctorCone A)

def cosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A)

theorem cosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (cosimplicialModuleCone A M)

theorem cosimplicialModuleCone_vertex (M : CosimplicialObject (ModuleCat.{u} A)) :
    (cosimplicialModuleCone A M).vertex =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((discreteCochainFunctor A).obj M))

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleConeFamily`（146行）。

```lean
theorem moduleConeCurry_evaluateAt {K D : SSet.{u+1}}
    (H : nerve (CosimplicialObject (ModuleCat.{u} A)) ⊗ K ⟶ D)
    (M : CosimplicialObject (ModuleCat.{u} A)) :
    curry H ≫ evaluateFunctorAt (ComposableArrows.mk₀ M) =
      lift (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) (𝟙 K) ≫ H

def cosimplicialModuleConeFamily :
    join (Δ[0] : SSet.{u+1}) ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A

def discreteTotEvaluationFamily :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⊗
      nerve (CosimplicialObject (ModuleCat.{u} A)) ⟶ derivedInfinityCategory A

theorem cosimplicialModuleConeFamily_at_lift (M : CosimplicialObject (ModuleCat.{u} A)) :
    lift (𝟙 _) (SSet.const (ComposableArrows.mk₀ M) : _ ⟶
      nerve (CosimplicialObject (ModuleCat.{u} A))) ≫ cosimplicialModuleConeFamily A =
      (cosimplicialModuleCone A M).val

theorem cosimplicialModuleConeFamily_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    inv (fst (join (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory))) (Δ[0] : SSet.{u+1})) ≫
      (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex M)) ≫ cosimplicialModuleConeFamily A =
        (cosimplicialModuleCone A M).val

theorem cosimplicialModuleConeFamily_boundaries :
    (joinInl (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A =
        snd (Δ[0] : SSet.{u+1}) (nerve (CosimplicialObject (ModuleCat.{u} A))) ≫
          nerveMap (discreteCochainFunctor A) ≫ complexOrdinaryDerivedSource A ∧
    (joinInr (Δ[0] : SSet.{u+1})
      ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ⊗ₘ 𝟙 _) ≫
      cosimplicialModuleConeFamily A = discreteTotEvaluationFamily A

```

登録候補：`SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleConeHomology`（45行）。

```lean
def cosimplicialModuleCone_homology (M : CosimplicialObject (ModuleCat.{u} A)) (i : ℤ) :
    derivedInfinityHomology A i (cosimplicialModuleCone A M).vertex ≃ₗ[A]
      ((discreteCochainFunctor A).obj M).homology i

```

### 160.2 最終検収

- 201は再利用するmainの既存二本の生成のみ：5,714 jobs、終了コード0。新規監査の数には含めない。
- 202：交代余面全頂点への輸送、8,153 jobs、終了コード0、新規一本6宣言・標準三公理のみ。
- 203：D05・D06および既存 `StrictHomology` の生成、10,234 jobs、終了コード0。新規一本だけの小監査10宣言・標準三公理のみ。
- 204：D07・D08、10,236 jobs、終了コード0。**停止点2a後の自レーン新規40モジュールをまとめて小監査し208宣言、標準三公理のみ**。これは全段階IIや全366本の今回の再監査ではない。A・B・Cと前段の依存は各報告の検証済み対象ビルド・監査を引き継ぐ。

ログ `/private/tmp/isw2-build201.log`〜`204.log`、最終監査 `/private/tmp/AuditISW2G10DComplete.lean`。全ハンドルの終了コード0を確認済み、鍵返却済み。各回 `--class impl --wait 3600`、整理券一枚、一回1,700秒、対象ビルド・小監査の間だけ鍵を使用。root・大きい監査は流していない。`git diff --check`成功。sorry・独自公理0、計算・再帰上限の増加なし、既存宣言・⑤a・入口・公式監査・mainの変更なし。今回200行超のファイルなし。未検証のG10草稿を残さない。

最終実測 **366モジュール・22,870行**。外枠23,000行内（残り **130行**）。

### 160.3 §37.2・§72.2の四まとまり：見込みと実測の差

実測は各まとまりを完了した報告の累計間の増分で、共通の前提計算・証明分割・docstring/importを含む。Aは両見積もりの時点で既に途中まであったので、同じ時点からA完了までを比較した。B〜DはそれぞれA・B・C完了時点からの増分。B4の配置・名前空間追従を含む最終ソースの数え直しは上記累計JSON。

| まとまり | §37.2見込み | §72.2見込み | 完了実測と差 |
| --- | ---: | ---: | --- |
| A：正規化テンソル／積重み | 1,000〜1,600 | 400〜700 | §37の5,786→A完了12,781：6,995（+5,395〜+5,995）。§72の8,834→12,781：3,947（+3,247〜+3,547） |
| B：指定豊穣Hom・native極限性 | 600〜900 | 600〜900 | 12,781→18,226：5,445（+4,545〜+4,845） |
| C：標準脚・D(A)輸送 | 400〜700 | 400〜700 | 18,226→19,553：1,327（+627〜+927） |
| D：全図式射・指定全錐族・離散入口 | 500〜900 | 500〜900 | 19,553→22,870：3,317（+2,417〜+2,817） |

主な超過は抽象的な同値から自動では出ない、元のAW/Γ/Moore/豊穣合成の同じ射の照合と、全パラメータの厳密HA写像・元の全joinセルの復元。D後半の離散部分は、既存の関手圏の点ごとの極限判定と全自然同型に沿う頂点輸送を使い、全族を作り直す増分を抑えた。型・範囲を削る短縮はしていない。

### 160.4 そのまま3b-4へ

IS-W2 §18・更新後の/goalに従い、ここで承認待ちにせず、承認済み§152のR01〜R12（外枠15,000行）のTot側から進む。TotのR01〜R05・R11/R12のTot部分が停止点3b-4a、実現のR06〜R10が停止点3b-4b。その後に任意coherent BE図式の段0を報告して止まる。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤aを変えず、無条件の `cAlgForgetDerived_mapJoinCone_isLimit` を使う。点つきKan Totは作らない。3b-4の実測はG10とは別に数える。


## 161. 3b-4開始：R01と同じstrict図式・実U比較の入口（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R01完了。R02・R04は同じ元のstrict図式・全評価と既存U比較を前合成する入口だけで、native全錐族・極限性・台の加群Totへの最終比較が完成したとは数えない。

### 161.1 3b-3との境目・Tot先行の具体化

§152の受け渡しを維持する。R01〜R04のstrict入力について、元のBE right frame/end・全図式射・同じalgebraCAlgSourceを使う。R05でstrict複体図式の∞局所化と全Fun比較を使う所、R09〜R10で③-aの元の実現余錐の全族を使う所が3b-3との境目。加群版のstrict図式評価の同値からBE値の任意coherent図式の厳密化を得たとは扱わない。

R02〜R03の模型側では `FramedLimitCones` のKan錐空間・指定重み、`FramedLimitHomPiZero` の通常局所化Hom、一般 `ModelRightFrameComparison` の実right-frameとpinched Homの全比較を区別して使う。π₀のHom同値や通常局所化の随伴だけをnative全錐の普遍性と取り違えない。既存 `FramedLimit*`・`CAlgUnderlyingDerivedComparison`・⑤aは変更しない。既存の無条件 `cAlgForgetDerived_mapJoinCone_isLimit` は、構成したBE極限錐の像の検収に使い、逆方向に用いない。

### 161.2 R11・R12で合わせる既存の欄

読み取りで確認：`EInfinity/Interface/Theory` の `TotalizationCone D x` は **`{ c : JoinCone D // c.vertex = x ∧ IsLimitCone c }`**。`ofCosimplicial_forget` は全 `FunctorIso`、`ofCosimplicial_restrict` も全 `FunctorIso`。既存の型と指定頂点を変えない。

またBE実例の `Theory.lean` で `discrete` に入るものは **`discreteCAlgUnderEmbedding`**（源は `Under (CommRingCat.of A)`）であり、単にCommAlgCat源の `discreteCAlgEmbedding` で代用しない。既存の全源表示は `nerveMap (commAlgCatEquivUnder ...).inverse ≫ discreteCAlgEmbedding`。従ってR11の元の離散BE図式は、この同じinverseと `discreteAlgebraFunctor` を図式へ後合成したものに固定する。`cosimplicialCochains` は既存の `discreteAlgebraModule`・交代余面・整数次数への零延長の全関手で、今回G10の離散入口に使った全関手との表示の法則を照合する。

R12の係数制限は既存の `coefficientRestriction f`（strict代数）と `barrattEcclesRestrict f`（実CAlg）に固定。`barrattEcclesRestrict_sourceIso` は `algebraCAlgSource T ≫ barrattEcclesRestrict f` と `nerveMap (coefficientRestriction f) ≫ algebraCAlgSource S` の全比較。R12ではこの同じ比較の評価前合成を全錐族の右境界に保ち、左境界をTot頂点の比較に一致させる。R11の最終出口は次の既存欄そのものである（紙、未実装）：

```lean
-- S : Type u, [CommRing S]。FtotはR01を同じUnder→CommAlgCat→BE図式へ制限した全関手。
FunctorIso (Ftot S ≫ cAlgForgetDerived S)
  (nerveMap (cosimplicialCochains S) ≫ complexOrdinaryDerivedSource S)
-- 同じFtotの指定頂点を保持する。
(X : CosimplicialRingAlgebra S) →
  TotalizationCone (cosimplicialNerve X ≫ discreteCAlgUnderEmbedding S)
    (atVertex (Ftot S) (nerveVertex X))
-- S T : Type u, [CommRing S] [CommRing T], f : S →+* T。
FunctorIso
  (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (restrictRingAlgebra f)) ≫ Ftot S)
  (Ftot T ≫ barrattEcclesRestrict f)
```

R11・R12はこの欄と同じ全族の両境界を照合してから完了と数える。ここでは仮定・sorry付きのLean宣言を追加していない。

### 161.3 今回の検証済みの型

共通：`A : Type u`、`[CommRing A]`。

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationComparison`（33行）。

```lean
def strictBETotVertex :
    nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶ CAlg_R A

theorem strictBETotVertex_at (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotVertex A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))

```

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotalizationInput`（74行）。

```lean
def strictBECosimplicialNerve (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶
      nerve (operad A).Algebra

def strictBECosimplicialDiagram (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⟶ CAlg_R A

def strictBECosimplicialEvaluationNerve :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶
        nerve (operad A).Algebra

def strictBECosimplicialEvaluation :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ⊗
      nerve (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⟶ CAlg_R A

theorem strictBECosimplicialEvaluationNerve_at
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    inv (fst ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))
      (Δ[0] : SSet.{u+1})) ≫ (𝟙 _ ⊗ₘ SSet.yonedaEquiv.symm (nerveVertex F)) ≫
        strictBECosimplicialEvaluationNerve A = strictBECosimplicialNerve A F

```

登録候補：`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUnderlyingSource`（44行）。

```lean
def strictBETotUnderlyingSourceIso :
    FunctorIso (strictBETotVertex A ≫ cAlgForgetDerived A)
      (nerveMap (framedLimitFunctor A (AsSmall.{u} SimplexCategory) ⋙
        Operad.Algebra.forget (operad A)) ≫ complexOrdinaryDerivedSource A)

def strictBECosimplicialUnderlyingDiagramIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    FunctorIso (strictBECosimplicialDiagram A F ≫ cAlgForgetDerived A)
      (strictBECosimplicialNerve A F ≫ algebraUnderlyingDerivedSource A)

def strictBECosimplicialUnderlyingEvaluationIso :
    FunctorIso (strictBECosimplicialEvaluation A ≫ cAlgForgetDerived A)
      (strictBECosimplicialEvaluationNerve A ≫ algebraUnderlyingDerivedSource A)

```

### 161.4 検収・実測・次の接続

コード **`03e732bf0`**。R01の最初の対象ビルド205は `.app _` の零単体の次数推論で失敗し、両方の次数を明示して修正。計算上限を増やさず個別検査を通した後、最終対象ビルド206は **9,459 jobs・終了コード0**、三本だけの小監査 **12（2・7・3）宣言、標準三公理のみ**。205を成功の回として数えない。ログ `/private/tmp/isw2-build205.log`・`206.log`、監査 `/private/tmp/AuditISW2BER01Input.lean`。ハンドル終了コード0を確認済み、鍵返却済み。整理券一枚、`--class impl --wait 3600`、対象ビルド・小監査中だけ使用。sorry・独自公理0。

3b-4の検証済みは **3モジュール・151行**、外枠15,000行まで14,849行。登録候補は別の `is-w2-be-20261114-modules.json` に記録し、G10の366本・22,870行と混ぜない。200行超のファイルなし。既存宣言・⑤a・入口・公式監査・mainの変更なし。

次はR02の元のframe計算対象と全図式評価の間のnative全錐族、およびR03の実right-frame Homとpinched Homの同じ制限の比較を接続する。今回のU源比較だけでR04の加群Totとの最終同型が済んだとは数えない。承認待ち・範囲変更・規模による停止ではなく、検証済みの保存点。Tot先行・実現・任意coherent BE図式の段0までの/goalはactiveのまま保持する。


## 162. 同じBE frameの全Hom比較・重み付き錐空間（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R03の実frame比較の準備。R02・R03のnative全錐・極限性を完了とは数えない。

### 162.1 今回の型（既存構成の法則）

共通：`A : Type u`、`[CommRing A]`、`K : Type u`、`[SmallCategory K]`。局所の模型構造は既存 `modelCategory A`。新しい模型構造・重み・置換を作らない。以下の型は各ファイルの同じ変数・openの下で読む。

`StrictDiagramTotModelSource`（100行）：

```lean
def strictBETotModelNerveIso :
    nerve (modelRelativeCategory (operad A).Algebra).category ≅
      nerve (allAlgebraRelativeCategory A).category

theorem strictBETotModelNerveIso_weakEdges :
    (strictBETotModelNerveIso A).inv.app (Opposite.op ⦋1⦌) ''
      weakNerveEdges (allAlgebraRelativeCategory A) =
        weakNerveEdges (modelRelativeCategory (operad A).Algebra)

def strictBETotModelSource :
    nerve (modelRelativeCategory (operad A).Algebra).category ⟶ CAlg_R A

theorem strictBETotModelSource_isLocalization :
    IsLocalization (strictBETotModelSource A)
      (weakNerveEdges (modelRelativeCategory (operad A).Algebra))

theorem strictBETotModelSource_vertex (X : (operad A).Algebra) :
    (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X)) =
      (algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)
```

`StrictDiagramTotRightFrameComparison`（41行）：

```lean
def strictBETotRightFramePinchedEquivalence
    (X : (operad A).Algebra) [IsCofibrant X] (Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj ((rightFrameHom (rightFrameFamily A) X).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))
```

`StrictDiagramTotRightFrameCoherent`（41行）：

```lean
def strictBETotRightFrameCoherentComparison
    (X : (operad A).Algebra) [IsCofibrant X] :
    (FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 0)
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X) (rightFrameFamily A) 6)) ×
      FrameHom.CoherentLocalizationComparison
        (SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A)
```

`StrictDiagramTotTensorFrame`（75行）：

```lean
def strictBETotTensorWeights : SimplexCategory ⥤ (Kᵒᵖᵒᵖ ⥤ SSet.{u})

def strictBETotTensorFrameFamily :
    (K ⥤ (operad A).Algebra)ᵒᵖ ⥤ SimplexCategory ⥤ (operad A).Algebraᵒᵖ

theorem strictBETotTensorFrameFamily_obj (F : K ⥤ (operad A).Algebra) :
    (strictBETotTensorFrameFamily A K).obj (op F) =
      HomotopyWeight.tensorFrame Kᵒᵖ (HomotopyWeight.framedLimitWeight K)
        (rightFrameDiagram A K F) := rfl

/-- 同じ標準零単体の単位則は、全図式射に自然な零次同型を与える。 -/
def strictBETotTensorFrameZeroIso :
    strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        framedLimitOpFunctor A K

def strictBETotTensorFrameZeroIso :
    strictBETotTensorFrameFamily A K ⋙
      (evaluation SimplexCategory (operad A).Algebraᵒᵖ).obj ⦋0⦌ ≅
        framedLimitOpFunctor A K

def strictBETotTensorFrameAugmentation :
    strictBETotTensorFrameFamily A K ⟶
      framedLimitOpFunctor A K ⋙ Functor.const SimplexCategory
```

`StrictDiagramTotTensorFrameProperties`（61行）：

```lean
theorem strictBETotTensorFrame_reedyCofibrant (F : K ⥤ (operad A).Algebra) :
    reedyLeft simplex (cofibrations (operad A).Algebraᵒᵖ)
      (initial.to ((strictBETotTensorFrameFamily A K).obj (op F)))

theorem strictBETotTensorFrame_homotopicallyConstant (F : K ⥤ (operad A).Algebra)
    {n m : SimplexCategory} (α : n ⟶ m) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameFamily A K).obj (op F)).map α)

theorem strictBETotTensorFrameAugmentation_weak
    (F : K ⥤ (operad A).Algebra) (n : SimplexCategory) :
    weakEquivalences (operad A).Algebraᵒᵖ
      (((strictBETotTensorFrameAugmentation A K).app (op F)).app n)

def strictBETotTensorFrameConeIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
      ((strictBETotTensorFrameFamily A K).obj (op F))).obj (op (framedLimitProbe A Y))) ≅
        (framedLimitConeSpace A K Y).obj F
```

`StrictDiagramTotFrameHomComparison`（73行）：

```lean
abbrev strictBETotFrameCommonFamily

def strictBETotFrameHomLeft :
    FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K)) ⟶ FrameOverFunctor.hom (strictBETotFrameCommonFamily A K)

def strictBETotFrameHomRight :
    FrameOverFunctor.hom (strictBETotTensorFrameFamily A K) ⟶
      FrameOverFunctor.hom (strictBETotFrameCommonFamily A K)

theorem strictBETotFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op Y))

theorem strictBETotFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) [IsCofibrant Y] :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op Y))
```

`StrictDiagramTotProbeFrameComparison`（50行）：

```lean
def strictBETotFrameHomLeftSourceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    ((FrameOverFunctor.hom (FrameOverFunctor.resolution (rightFrameFamily A)
      (framedLimitOpFunctor A K))).obj (op (op F))).obj (op Y) ≅
      ((rightFrameHom (rightFrameFamily A) Y).obj ((framedLimitFunctor A K).obj F))

theorem strictBETotProbeFrameHomLeft_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomLeft A K).app (op (op F))).app (op (framedLimitProbe A Y)))

theorem strictBETotProbeFrameHomRight_equivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence
      (((strictBETotFrameHomRight A K).app (op (op F))).app (op (framedLimitProbe A Y)))
```

### 162.2 同じものの比較と未完了の境界

`AsSmall` のmodelRelativeCategoryと、既存のULiftHomによるallAlgebraRelativeCategoryのnerve同型を、同じ対象・射から構成。その逆像の弱辺集合を照合し、既存の全代数の局所化を前合成して同じmodelSourceを得る。既存のmodelRightFramePinchedEquivalence・全targetについてのmodelRightFrameCoherentComparisonへその源を渡す。

同じframedLimitWeightとrightFrameDiagramを実現する全関手を標準単体で評価。零次同型による増大写像・Reedy cofibrant・homotopically constant・増大の弱同値性は既存tensorFrameの法則。`tensorFrameHomIso`は元のframedLimitConeSpaceとの**全単体集合の同型**。計算対象のright frameとこのtensor frameの共通frameを、既存FrameOverFunctorで取る。左右の比較は元の同じ任意probeで無条件に単体的ホモトピー同値。rightFrameHomへの源の同定は`rightFrameHomOpIso`であり、定義的等式で代用しない。

これはπ₀だけの比較ではないが、指定native錐の全制限との最終照合は未完了。元の指定頂点・脚・全単体の錐とnative極限性を次に接続する。既存通常局所化の随伴だけからnative普遍性を結論しない。

### 162.3 検収

モデル源・pinched比較の二本はコード`bad328231`、対象ビルド208 **9,817 jobs・終了0**、二本の小監査**19（9・10）宣言・標準三公理のみ**。207・209は既存の必要依存だけの対象ビルドで、それぞれ9,730・2,423 jobs・終了0。

210は四本の対象ビルド自体は成功したが、合併監査で自動生成された局所instance名の衝突を検出したため、検収成功とは数えない。未コミットの五本の局所instanceに個別の名前を与え、既存検証済み宣言は変更せず修正。最終211は五本の対象ビルド **9,835 jobs・終了0**、BE新規全10本の小監査 **64（2・7・3・9・10・4・10・6・7・6）宣言・標準三公理のみ**。実ハンドル8092の終了0を確認。sorry・独自公理0。計算上限の変更なし。

整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ保持し返却済み。ログ`/private/tmp/isw2-build208.log`・`211.log`、最終監査`/private/tmp/AuditISW2BEFrameComplete.lean`。main・入口・公式監査・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparisonの変更なし。

3b-4の検証済み **10モジュール・592行**（外枠15,000行）。登録候補は `is-w2-be-20261114-modules.json`。200行超の新規ファイルなし。承認待ちの停止ではなく検証済みの保存点で、/goalの続きへ進む。


## 163. 同じ全strict BE図式の評価・頂点・forgetの局所化（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R05の局所化上の源と三つの全関手の因子化を証明分割。R02〜R05の最終結論が済んだとは数えない。

### 163.1 R05の源と、同じ全strict図式の保持

§152の `TotBE`・`ForgetStrictBEInfinity` の源を、元のstrict BE図式のnerveと、その同じobjectwise擬同型の辺集合の `edgeLocalization` とする。元の全図式の評価・元のframedLimitFunctorによる全頂点・同じforgetを、既存局所化の全関手圏の普遍性で延長した。それぞれ元の全strict図式の全射列との指定FunctorIsoを保持する。BE値の任意coherent図式の厳密化や評価比較の同値を主張しない。

forgetの入力は元の `AsSmall.{u} Δ` の図式を指定 `AsSmall.up` でΔへ引き戻し、元の `Operad.Algebra.forget` を後合成するもの。図式の各射は元の同じ成分の `.hom` に厳密に等しい。このobjectwise擬同型は加群図式の既存指定局所化で反転される。R05の `ForgetStrictBEInfinity` の全因子化までを実装し、最終の `TotBE ≫ U` と `ForgetStrictBEInfinity ≫ TotDA` の比較はR02〜R04の同じ全錐の照合から続ける。

### 163.2 検証済みの型

共通：`A : Type u`、`[CommRing A]`。次は各ファイルの変数とopenの下で読む。

`StrictDiagramTotLocalization`（50行）：

```lean
abbrev StrictBETotDiagramNerve : SSet.{u+1}

def strictBETotDiagramWeakEdges : Set ((StrictBETotDiagramNerve A) _⦋1⦌)

theorem strictBETotDiagramWeakEdges_mk₁
    {F G : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ComposableArrows.mk₁ f ∈ strictBETotDiagramWeakEdges A ↔
      ∀ j, QuasiIso (f.app j).hom

def StrictBETotDiagramInfinity : SSet.{u+1}

instance strictBETotDiagramInfinity_quasicategory :
    Quasicategory (StrictBETotDiagramInfinity A)

def strictBETotDiagramLocalization :
    StrictBETotDiagramNerve A ⟶ StrictBETotDiagramInfinity A

theorem strictBETotDiagramLocalization_isLocalization :
    IsLocalization (strictBETotDiagramLocalization A) (strictBETotDiagramWeakEdges A)
```

`StrictDiagramTotEvaluationLocalization`（94行）：

```lean
def strictBETotDiagramFamily : StrictBETotDiagramNerve A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := curry (strictBECosimplicialEvaluation A)

/-- 点での全評価は元の同じ通常評価のnerveに一致。 -/
theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (operad A).Algebra).obj j) ≫ algebraCAlgSource A

theorem strictBETotDiagramFamily_evaluation (j : AsSmall.{u} SimplexCategory) :
    strictBETotDiagramFamily A ≫ evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ j)) =
      nerveMap ((CategoryTheory.evaluation (AsSmall.{u} SimplexCategory)
        (operad A).Algebra).obj j) ≫ algebraCAlgSource A

theorem strictBETotDiagramFamily_inverts :
    InvertsEdges (strictBETotDiagramFamily A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedEvaluation :
    ∃ ev : StrictBETotDiagramInfinity A ⟶
        (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
          (CAlg_R A),
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ ev)
        (strictBETotDiagramFamily A))

def strictBETotLocalizedEvaluation : StrictBETotDiagramInfinity A ⟶
    (ihom ((SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)))).obj
      (CAlg_R A) := (exists_strictBETotLocalizedEvaluation A).choose

/-- 延長の指定全同型は元の全strict評価を保持する。 -/
def strictBETotLocalizedEvaluation_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedEvaluation A)
      (strictBETotDiagramFamily A)

def strictBETotLocalizedEvaluation_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedEvaluation A)
      (strictBETotDiagramFamily A)
```

`StrictDiagramTotVertexLocalization`（57行）：

```lean
theorem strictBETotVertex_inverts :
    InvertsEdges (strictBETotVertex A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedVertex :
    ∃ V : StrictBETotDiagramInfinity A ⟶ CAlg_R A,
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ V) (strictBETotVertex A))

def strictBETotLocalizedVertex : StrictBETotDiagramInfinity A ⟶ CAlg_R A
```

`StrictDiagramTotUnderlyingLocalization`（86行）：

```lean
def strictBETotForgetDiagram :
    (AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) ⥤
      StrictComplexDiagram A .cosimplicial

theorem strictBETotForgetDiagram_map
    {F G : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra} (f : F ⟶ G)
    (j : SimplexCategory) :
    ((strictBETotForgetDiagram A).map f).app j = (f.app (AsSmall.up.obj j)).hom := rfl

/-- 元の全BE図式から、同じ加群図式の指定局所化への写像。 -/
def strictBETotForgetDiagramSource :
    StrictBETotDiagramNerve A ⟶ StrictDiagramInfinity A .cosimplicial

def strictBETotForgetDiagramSource :
    StrictBETotDiagramNerve A ⟶ StrictDiagramInfinity A .cosimplicial

theorem strictBETotForgetDiagramSource_inverts :
    InvertsEdges (strictBETotForgetDiagramSource A) (strictBETotDiagramWeakEdges A)

theorem exists_strictBETotLocalizedForget :
    ∃ U : StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial,
      Nonempty (FunctorIso (strictBETotDiagramLocalization A ≫ U)
        (strictBETotForgetDiagramSource A))

def strictBETotLocalizedForget :
    StrictBETotDiagramInfinity A ⟶ StrictDiagramInfinity A .cosimplicial

def strictBETotLocalizedForget_factor :
    FunctorIso (strictBETotDiagramLocalization A ≫ strictBETotLocalizedForget A)
      (strictBETotForgetDiagramSource A)
```

### 163.3 検収・残り

対象ビルド212：最初の三本 **9,489 jobs・終了0**、BE新規全13本の小監査 **90（2・7・3・9・10・4・10・6・7・6・13・8・5）宣言・標準三公理のみ**。その前の個別検査では `nerve.edgeMk` の像と `edgeOfSimplex` の表示を明示して照合した。計算上限は増やしていない。

213はforgetの輸送で `InvertsEdges` の暗黙引数名を誤り失敗、検収成功とは数えない。`a` に修正し、既存の反転命題を `IsInvertibleEdge` の同じ辺として明示。個別検査の終了0後、最終214は **9,492 jobs・終了0**、BE新規全14本の小監査 **99（2・7・3・9・10・4・10・6・7・6・13・8・5・9）宣言・標準三公理のみ**。実ハンドル51046・93720の終了0を確認、鍵返却済み。sorry・独自公理0。

整理券は同時に一枚だけ、`--class impl --wait 3600`、対象ビルド・小監査の間だけ保持。ログ`/private/tmp/isw2-build212.log`・`214.log`、小監査`/private/tmp/AuditISW2BEUnderlyingLocalization.lean`。公式監査・入口・main・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparisonは変更していない。

3b-4の検証済み **14モジュール・879行**、外枠15,000行まで14121行。新規200行超のファイルなし。登録候補を同じBE用JSONに追記。G10の366本とは分ける。

次はR02〜R03の核心へ戻る。同じ実frameのHom比較と重み付き錐空間の同型は§162で検証済みだが、これだけで元のCAlg図式上の指定native全錐とその極限性は得ていない。全族の錐を独立な点ごとの錐から自然だと仮定したり、通常局所化の随伴の余単位をnativeな全錐の代用にしたりしない。元の実frameの標準射を持つ全錐を構成し、同じ制限射との等式を追跡する。今回の局所化の因子化はこの構成後のR05へ再利用する。保存点であり、承認待ち・外枠・新規数学による停止ではない。/goalはactiveのまま。


## 164. 普遍重み付き錐・元のprobe・実Homの標準点（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R02・R03の既存随伴単位・零次同型の法則を分割。指定native錐・その極限性は未完了。

### 164.1 元の普遍錐を固定する

同じFrameWeightRealizationの随伴の単位を、元の重みで評価する。これが `strictBETotUniversalWeightedCone` で、随伴で戻すと**同じ元の計算対象の恒等射**になる。任意の元の射が表す重み付き錐は、この単位への同じ前合成。元の全計算関手の射の反対は、同じframe族の射の実現のmateそのものでもある。

元の計算対象の同じ `framedLimitProbeComparison` を前合成すると、同じ `framedLimitConeSpace` の具体的な普遍probe錐の零単体が得られる。さらに元の `strictBETotTensorFrameConeIso` は、零次同型にそのprobe比較を合成したHomを、**その同じ零単体**に写す。この同定を単なるπ₀上の等式へ弱めていない。

### 164.2 検証済みの型

共通のunit則の宇宙・圏・余極限の仮定はソースと同じ。BE側は `A : Type u`、`[CommRing A]`、`K : Type u`、`[SmallCategory K]`。

`SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightUnitNaturality`（26行）：

```lean
theorem unit_frame_naturality {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (W : Kᵒᵖ ⥤ SSet.{w}) :
    (adjunction K B').unit.app W ≫ ((homFamily K).map a.op).app ((functor K B').obj W) =
      (adjunction K B).unit.app W ≫ (hom K B).map ((map K a).app W)
```

`SerrePositivity.EInfinity.HomotopyWeight.TensorConeUnitPoint`（36行）：

```lean
theorem tensorFrameHomIso_point (Y : C)
    (f : (FrameWeightRealization.functor K B).obj W ⟶ Y) :
    (((tensorFrameHomIso K W B).hom.app Y).app (Opposite.op ⦋0⦌))
      ((tensorFrameZeroIso K W B).hom ≫ f) =
        conePoint Kᵒᵖ W ((FrameWeightRealization.adjunction K B).homEquiv W Y f)
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalWeightedCone`（67行）：

```lean
def strictBETotUniversalWeightedCone (F : K ⥤ (operad A).Algebra) :
    HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op ((framedLimitFunctor A K).obj F))

theorem strictBETotUniversalWeightedCone_identity (F : K ⥤ (operad A).Algebra) :
    ((FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)).homEquiv
      (HomotopyWeight.framedLimitWeight K)
      (op ((framedLimitFunctor A K).obj F))).symm
        (strictBETotUniversalWeightedCone A K F) = 𝟙 _

theorem strictBETotUniversalWeightedCone_precomp (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    (weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) Y) f =
      strictBETotUniversalWeightedCone A K F ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map f.op

def strictBETotFrameMap {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    rightFrameDiagram A K G ⟶ rightFrameDiagram A K F

theorem strictBETotFrameMap_eq {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotFrameMap A K f = (rightFrameDiagramFamily A K).map f.op

theorem strictBETotFunctor_map_op {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    ((framedLimitFunctor A K).map f).op =
      (FrameWeightRealization.map Kᵒᵖ ((rightFrameDiagramFamily A K).map f.op)).app
        (HomotopyWeight.framedLimitWeight K)
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbeCone`（46行）：

```lean
def strictBETotUniversalProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    HomotopyWeight.framedLimitWeight K ⟶
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).obj
        (op (framedLimitProbe A ((framedLimitFunctor A K).obj F)))

theorem strictBETotUniversalProbeWeightedCone_comparison
    (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalProbeWeightedCone A K F =
      weightedCotensorHomEquiv A K F (HomotopyWeight.weight K)
        (framedLimitProbe A ((framedLimitFunctor A K).obj F))
        (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F))

def strictBETotUniversalProbeConePoint (F : K ⥤ (operad A).Algebra) :
    ((framedLimitConeSpace A K ((framedLimitFunctor A K).obj F)).obj F) _⦋0⦌
```

`SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniversalProbePointComparison`（43行）：

```lean
theorem strictBETotTensorFrameConeIso_universalPoint
    (F : K ⥤ (operad A).Algebra) :
    ((strictBETotTensorFrameConeIso A K F ((framedLimitFunctor A K).obj F)).hom.app
      (Opposite.op ⦋0⦌))
        ((strictBETotTensorFrameZeroIso A K).hom.app (op F) ≫
          (framedLimitProbeComparison A ((framedLimitFunctor A K).obj F)).op) =
      strictBETotUniversalProbeConePoint A K F
```

### 164.3 全自然性の未検証部を区別する

共通の `FrameWeightRealization.unit_frame_naturality` は、既存の `unit_conjugateEquiv_symm` を直接代入して証明済み。一方、それをBE全図式族の評価表示と独立なrightFrameDiagram表示の間で一括照合する特殊化では、定義展開が200,000 heartbeatsに当たった。型・計算上限は変更せず、単位則・同じ全frame族の射・実現の射の表示を小さく分割した。

特殊化の全自然性の未検証部分は `/private/tmp/StrictBETotUniversalWeightedConeNaturality-draft.lean.txt` に残し、成功した宣言・対象ビルドに含めない。残る型は次（同じ元の全frame族の射で、別の比較射を選ばない）：

```lean
theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((rightFrameDiagramFamily A K).map f.op).op).app
          (op ((framedLimitFunctor A K).obj F)) =
      strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K G)).map
          (((framedLimitFunctor A K).map f).op)
```

この未検証部を一覧から除外したり、R02の全族を点ごとの錐だけへ縮めたりしない。次の指定native錐の構成と合わせて閉じる。現時点の `strictBETotUniversalProbeConePoint` をnative join錐の代用にはしない。

### 164.4 検収

215は共通単位則と既存ConePointsの依存だけの対象ビルド **2,325 jobs・終了0**。型照合の途中の個別検査は、未検証部でheartbeat・一時ファイルのインデント・開いた記法の不足を検出した回を成功に数えず、上記の検証済み部を合併した `CheckBETotUniversalProbePointComparison2.lean` の終了0を確認してから対象ビルドした。計算上限は増やしていない。

最終216：新規五本の対象ビルド **4,018 jobs・終了0**、3b-4新規全19本の小監査 **113（2・7・3・9・10・4・10・6・7・6・13・8・5・9・1・1・7・3・2）宣言・標準三公理のみ**。実ハンドル92611・41565の終了0を確認、鍵返却済み。ログ `/private/tmp/isw2-build215.log`・`216.log`、小監査 `/private/tmp/AuditISW2BEUniversalPoint.lean`。sorry・独自公理0。

同時に整理券一枚、`--class impl --wait 3600`。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。新規200行超のファイルなし。これは保存点であり、承認待ちや外枠による停止ではない。

3b-4新規は **19モジュール・1097行**（今回218行、共通二本を含む。外枠15,000行）。登録候補JSONにも共通二本を記録し、BSやG10の登録候補と混ぜない。次は元の試験対象とprobeのnative Homの始点を合わせ、同じ普遍錐・制限射へ接続する。/goalはactive。


## 165. 元の全BE図式と正本Hom∞の全比較・普遍錐の全自然性（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。R02・R03の元の全Hom比較・源移送・単位自然性まで。native join錐・極限性はまだ未完了。

### 165.1 同じ全単体と同じ源を保持する

§164.3で未検証だった `strictBETotUniversalWeightedCone_naturality` は、**報告した型のまま閉じた**。同じ全frame族の対象表示と同じ計算対象の反対表示を小さな等式で正規化してから、既存のmateの単位則を適用した。計算上限は変更していない。独立な二つの構成を同じものだと仮定することも、全自然性を点ごとの等式に置き換えることもしていない。

元のprobe比較の実辺が与える源の頂点同型と、既存の `pinchedPrecomposeEquivalence` を用い、元の任意の試験対象に対する実right-frame Homから同じnative pinched Homへの無条件の全空間同値を得た。その頂点同型の順射は元のprobe辺の同じ類であり、実比較の順射は同じframe比較と同じprobe比較の逆による前合成。

さらに既存 `FrameHom.rightFrameTerminalHomIso`（原本Yonedaの全比較を代入済み）を、既存六辺の全coherent比較と合成。元のright-frame Homの全標的図式から正本 `homInfinityCovariant` への**全FunctorIso**を得た。probe比較の源同型の反転・宇宙持ち上げを元のco-Yonedaで写すことで、こちらも元の任意の試験対象に無条件化。点ごとの逆を選んで自然だと仮定していない。

モデル相対圏のAsSmall表示から元の全代数のnerveへの比較ではHom宇宙が異なるため、その包含を元の全nerve上で直接記述した。指定modelSourceへの合成は、元の `algebraCAlgSource` と**全単体で厳密に等しい**。この一致を使って全Hom∞比較を元の全代数源へ戻し、さらに元の同じstrict BE余単体図式の全nerveへ前合成した。

### 165.2 今回の検証済みの型

共通：`A : Type u`、`[CommRing A]`。普遍錐の全自然性には `K : Type u`、`[SmallCategory K]`。局所の模型とfactorizationは既存と同じ具体的なもの。源cofibrancyを要求する欄と、同じprobeで無条件化した欄を区別する。

`StrictDiagramTotProbeNativeHomComparison`（65行）：

```lean
def strictBETotProbeSourceIso (X : (operad A).Algebra) :
    VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (framedLimitProbe A X)))
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))

theorem strictBETotProbeSourceIso_hom (X : (operad A).Algebra) :
    (strictBETotProbeSourceIso A X).hom = Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (framedLimitProbeComparison A X)).map (algebraCAlgSource A)).toTruncated

def strictBETotProbeNativeHomEquivalence (X Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj
        ((rightFrameHom (rightFrameFamily A) (framedLimitProbe A X)).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))

theorem strictBETotProbeNativeHomEquivalence_hom (X Y : (operad A).Algebra) :
    (strictBETotProbeNativeHomEquivalence A X Y).hom =
      (strictBETotRightFramePinchedEquivalence A (framedLimitProbe A X) Y).hom ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
          (strictBETotProbeSourceIso A X).inv
```

`StrictDiagramTotUniversalWeightedConeNaturality`（45行）：

```lean
theorem strictBETotFrameDiagram_obj (F : K ⥤ (operad A).Algebra) :
    (rightFrameDiagramFamily A K).obj (op F) = rightFrameDiagram A K F

theorem strictBETotFunctor_obj_op (F : K ⥤ (operad A).Algebra) :
    op ((framedLimitFunctor A K).obj F) =
      (FrameWeightRealization.functor Kᵒᵖ
        ((rightFrameDiagramFamily A K).obj (op F))).obj
          (HomotopyWeight.framedLimitWeight K)

theorem strictBETotUniversalWeightedCone_naturality
    {F G : K ⥤ (operad A).Algebra} (f : F ⟶ G) :
    strictBETotUniversalWeightedCone A K F ≫
      ((FrameWeightRealization.homFamily Kᵒᵖ).map
        ((rightFrameDiagramFamily A K).map f.op).op).app
          (op ((framedLimitFunctor A K).obj F)) =
      strictBETotUniversalWeightedCone A K G ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K G)).map
          (((framedLimitFunctor A K).map f).op)
```

`StrictDiagramTotModelSourceComparison`（40行）：

```lean
def strictBETotModelUpNerve :
    nerve (operad A).Algebra ⟶
      nerve (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory
        (operad A).Algebra).category

theorem strictBETotModelSource_up :
    strictBETotModelUpNerve A ≫ strictBETotModelSource A = algebraCAlgSource A
```

`StrictDiagramTotFrameHomInfinity`（43行）：

```lean
def strictBETotFrameHomInfinityIso (X : (operad A).Algebra) [IsCofibrant X] :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject X)
        (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

`StrictDiagramTotProbeHomInfinityComparison`（57行）：

```lean
def strictBETotProbeHomInfinitySourceIso (X : (operad A).Algebra) :
    FunctorIso
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (framedLimitProbe A X))))
      (homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex X)))

def strictBETotProbeFrameHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      (FrameHom.rightFrameHammockCoherentDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
          (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

`StrictDiagramTotAlgebraHomInfinityComparison`（64行）：

```lean
def strictBEAlgebraProbeHomInfinityIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (algebraCAlgSource A) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))

def strictBETotDiagramProbeHomInfinityIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
              (framedLimitProbe A X)) (rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialDiagram A F) ≫
        homInfinityCovariant
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)))
```

### 165.3 検収

217は先頭の整理券で調整役の監査を待ち、同じ実ハンドル39750を生存確認し続けた。再起動・整理券の重複発行なし。最終 **9,818 jobs・終了0**、新規全20本の小監査 **123（§164の113に新規10）宣言・標準三公理のみ**。

218はその終了0・返却後に次の一枚を発行し、残る五本と必要な既存依存だけを対象ビルド。**10,583 jobs・終了0**、新規全25本の小監査 **166（2・7・3・9・10・4・10・6・7・6・13・8・5・9・1・1・7・3・2・10・4・4・10・11・14）宣言・標準三公理のみ**。実ハンドル80009の終了0を確認。鍵返却済み。ログ `/private/tmp/isw2-build217.log`・`218.log`、最終小監査 `/private/tmp/AuditISW2BEHomInfinity.lean`。

個別検査でprobeのcofibrancyを型推論へ渡す必要、AsSmall包含のHom宇宙の違い、Functor.hextの射の異種等式を明示する必要を検出して修正した。既存依存を一時合併した検査では `stdSimplex` の名前衝突があったため一時ファイルだけを完全修飾し、既存ソースを変えなかった。最終218は各実モジュールを独立にビルドし、合併監査も成功した。これにより一時合併検査だけから成功を推測していない。

sorry・独自公理0。計算上限の変更なし。`--class impl --wait 3600`、同時整理券一枚、ビルド・小監査の間だけ鍵を保持。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

3b-4の検証済み **25モジュール・1411行**（今回314行、共通二本を含む。外枠15,000行）。新規200行超のファイルなし。登録候補は同じBE用JSONへ追記。R02・R03のnative錐・極限性を完成とは数えず、次の接続は重み付きframe錐とnative切断の間の比較。/goalはactive。

## 166. 一覧外の数学：選んだ一点重みとnative切断のBK重みの比較（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 12（うち追加 0）。検証済みコードは `98df07409`（§165、25本・1,411行、166宣言、標準三公理のみ）。R02・R03の残りの経路で、以下の数学的補題が必要になったため報告する。Leanの新しい証明・公理・仮定は追加していない。

### 166.1 必要になった追加の型：R03a案

`J := AsSmall.{u} SimplexCategory`、`I := Jᵒᵖᵒᵖ`。元のBE計算対象は選ばれた `HomotopyWeight.framedLimitWeight J` を使う。一方、既存のnative切断との比較は `bousfieldKanWeight I`（各値 `N(I/i)`）を使う。この二つを定義的に同じだと扱えない。必要なのは、同じ一つの重みの射による制限が、全Kan係数図式についてホモトピー同値になること。

追加を提案する主張の型は次のとおり（`J`・`I`は略記せず展開）：

```lean
-- universe u
-- open CategoryTheory
-- open SerrePositivity.EInfinity
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
-- open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

theorem exists_strictBETotWeightComparison :
    ∃ j : bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⟶
        HomotopyWeight.framedLimitWeight (AsSmall.{u} SimplexCategory),
      ∀ (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u}),
        (∀ i, SSet.KanComplex (H.obj i)) →
          IsSimplicialHomotopyEquivalence (weightedSectionsPre j H)
```

向きは `j : BK → W` から `sections(W,H) → sections(BK,H)`。一つの `j` を全Hに使うので、元の係数図式の射に関する自然性は既存 `weightedSectionsPre` の法則で保持できる。元のframe・重み・計算対象は変更せず、重み比較を通して元の普遍錐をnative切断へ送る。`[ModelCategory SSet]` は型に足さない。

型そのものは `/private/tmp/CheckISW2WeightComparisonStatement.lean` に同じPropとして記述し、個別検査の**終了0**を確認した（ログ `/private/tmp/checkISW2WeightComparisonStatement2.log`）。これは定理の証明ではなく、型の検査だけである。本体には追加していない。

### 166.2 なぜ既存構成の法則だけとは数えなかったか

- `HomotopyWeight.weight_cofibrant`・`framedLimitWeight_cofibrant` は選んだ小対象分解の重みの射影cofibrancyを証明する。別の具体的な重み `bousfieldKanWeight` の射影cofibrancyや、その重みとのHom空間の比較はそのままでは得られない。
- `weightedSectionsPre_homotopyEquivalence_of_extensions` は、**全ての成分ごとのanodyneな自然変換に対する延長性**を係数図式に要求する。今回の入力の各値がKanであるだけでは、その強い延長性を代入できない。
- `coneSpace_kanComplex`・`coneSpace_map_boundary_rlp` は、固定した射影cofibrant重みに対する係数方向の法則である。異なる二つの重みを比較する今回の型の証明にはなっていない。
- `YonedaHomotopyWeight`・抽象projective図式モデルの入口は値圏のModelCategory等を仮定する。これをSSetに無条件に代入したり、禁止された `[ModelCategory SSet]` を足したりしない。
- §165の全Hom∞比較は元の正本Hom関手まで接続したが、二つの重みの違いを消す定理ではない。通常局所化の随伴・π₀の同値・忘却Uの極限保存で、この重み比較を代用しない。

このため、随伴単位や全自然性の表示を分割した§164〜165とは異なり、R03aは新しい数学的補題として扱う。§152の一覧は既存frame Homとnative切断の橋を使う所で、この二つの具体的な重みのHom不変性を独立に洗い出していなかった。

### 166.3 証明の見込みと配置

候補の経路は、まず指定されたBK重みについて自由境界による細胞分解を示すこと。次数nの鎖 `i₀ → … → iₙ → i` を、最後の射 `iₙ → i` に関して自由な図式として扱い、非退化な鎖の境界の付加から射影cofibrancyを得る。その中で使う型は次：

```lean
-- open CategoryTheory Limits
(HomotopyWeight.boundaries ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ)).rlp.llp
  (initial.to (bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ)))
```

このPropの型も `/private/tmp/CheckISW2BKWeightStatement.lean` で検査済み。次に既存 `comparison_rlp` を用いて `BK → W` を一つ持ち上げ、両方の重みの射影cofibrancyと各値の可縮性を使って、全Kan係数図式への制限のHom不変性を証明する。この部分もモデル構造を仮定せず、自由境界・ホーンの持ち上げとして書く必要がある。

置き場所の案：共通の細胞・持ち上げの部分は新規 `HomotopicalAlgebra/Diagram/`、指定Δ・二重反対・選んだWへの特殊化は新規 `EInfinity/HomotopyWeight/`。既存のFramedLimit*・⑤a・入口・公式監査は変えない。見込みは細胞の部分300〜700行、重みのHom不変性と指定比較250〜450行、計550〜1,150行。現時点の1,411行と合わせても外枠15,000行には届かないが、行数でなく型つき一覧の停止規則による判断である。

### 166.4 停止の理由と現在地

IS-W2 §18.2が参照する `coordination.md` §2の明文は、**「止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）、まとまりの外のもの、外枠に届くときだけ」**。今回は新しい数学的補題R03aの追加の判断が必要と解した。検証済みの全25本は先にコミットし、対象ビルド218・小監査166宣言の終了0、鍵の返却、作業木に未検証のLean変更がないことを確認してから、この紙の報告を保存した。

**R03aを型つき一覧に追加して進めるか、別の既存の橋を指定してもらう所で当該Lean作業を止める。** R02・R03・R04以降を完成とは数えない。停止点3b-4aにはまだ届いていない。外枠・型・既存界面は変更しない。/goalの全範囲は保持し、complete・paused・blockedには変更していない。

## 167. R03a 承認後：自由細胞と元の骨格の厳密な付着（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 13（うち追加 1）。§166のR03aはユーザー承認・IS-W2 §19により一覧へ追加済み。mainを `2ca5e7878` で取り込み、§19を確認して再開した。R03aそのもの・R02・R03のnative錐の完成とは数えない。

### 167.1 今回閉じた証明分割

BKの単体を「台の射列＋最後の射」に厳密に分解し、退化性が台だけで決まることを示した。非退化細胞の図式は終頂点の表現可能関手の余積である。これに任意の単体集合をテンソルした全関手からの射は標準生成元で一意に決まるため、各終頂点での境界の持ち上げを同じ全図式の射へ束ねられる。

さらに任意の単体集合値図式の骨格を全関手として作り、その塔の余極限が元の図式であることを証明した。BKの非退化細胞のYoneda写像で旧骨格を引き戻すと元の標準境界になる。全自由細胞から連続する二つの元の骨格への射と、その厳密な可換性も証明した。これはR03aの細胞分解の証明分割であり、独立の新しい数学の項目は追加していない。

今回の10本は747行、各200行以下。3b-4の検証済みは **35モジュール・2,158行**（共通を含む、外枠15,000）。当初のR03aの細胞部分300〜700行に対し747行で、余積の添字替え・骨格押し出しの照合がまだ残るため上振れしている。元の重み・型・⑤aの欄は変更しない。

### 167.2 証明分割・既存構成の法則の型

以下は全て今回の新規ファイル内。namespace・universe・変数は各ソースのまま。構成の本体は省略し、主張・構成の型を記録する。R03aの追加以外に一覧の追加は0。

#### BousfieldKanSimplex（84行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev SimplexData (n : ℕ) (i : I)

def overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    ComposableArrows (Over i) n

def simplexData {n : ℕ} {i : I} (s : ComposableArrows (Over i) n) :
    SimplexData I n i := ⟨s ⋙ Over.forget i, (s.obj (Fin.last n)).hom⟩

/-- 復元したover射列の各対象は元の同じ対象。 -/
theorem overSimplex_simplexData_obj {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) (a : Fin (n+1)) :
    (overSimplex I (simplexData I s)).obj a = s.obj a

theorem overSimplex_simplexData_obj {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) (a : Fin (n+1)) :
    (overSimplex I (simplexData I s)).obj a = s.obj a

theorem overSimplex_simplexData {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) : overSimplex I (simplexData I s) = s

theorem simplexData_overSimplex {n : ℕ} {i : I} (s : SimplexData I n i) :
    simplexData I (overSimplex I s) = s

def simplexEquiv (n : ℕ) (i : I) :
    ComposableArrows (Over i) n ≃ SimplexData I n i

theorem simplexData_postcomp {n : ℕ} {i j : I} (f : i ⟶ j)
    (s : ComposableArrows (Over i) n) :
    simplexData I (s ⋙ Over.map f) =
      ⟨(simplexData I s).1, (simplexData I s).2 ≫ f⟩

```

#### BousfieldKanDegenerate（68行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem sigma_delta_eq_of_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) (n+1)) (k : Fin (n+1))
    (t : ComposableArrows I n)
    (ht : (nerve I).σ k t = s ⋙ Over.forget i) :
    (nerve (Over i)).σ k ((nerve (Over i)).δ k.castSucc s) = s

theorem degenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).degenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).degenerate n

theorem nondegenerate_iff_base {n : ℕ} {i : I}
    (s : ComposableArrows (Over i) n) :
    s ∈ (nerve (Over i)).nonDegenerate n ↔
      (s ⋙ Over.forget i) ∈ (nerve I).nonDegenerate n

```

#### BousfieldKanFreeCells（78行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev NondegenerateData (n : ℕ) (i : I)

def nondegenerateEquiv (n : ℕ) (i : I) :
    (nerve (Over i)).nonDegenerate n ≃ NondegenerateData I n i

def freeCellDiagram (n : ℕ) : I ⥤ Type u

def nondegenerateDiagram (n : ℕ) : I ⥤ Type u

def nondegenerateDiagramIso (n : ℕ) :
    nondegenerateDiagram I n ≅ freeCellDiagram I n

```

#### BousfieldKanRepresentableCells（58行）

```lean
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

abbrev cellRepresentables (n : ℕ) (c : (nerve I).nonDegenerate n) : I ⥤ Type u

def freeCellCofan (n : ℕ) : Cofan (cellRepresentables I n)

def freeCellDesc {n : ℕ} {Z : I ⥤ Type u}
    (f : ∀ c, cellRepresentables I n c ⟶ Z) : freeCellDiagram I n ⟶ Z

def freeCellCofanIsColimit (n : ℕ) : IsColimit (freeCellCofan I n)

```

#### SimplicialDiagramSkeleton（102行）

```lean
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory Limits SSet
open scoped Simplicial

theorem skeleton_image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n

def skeletonMap {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u})

@[reassoc] theorem skeletonMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    skeletonMap f n ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f

theorem skeletonMap_id (X : SSet.{u}) (n : ℕ) : skeletonMap (𝟙 X) n = 𝟙 _

theorem skeletonMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    skeletonMap (f ≫ g) n = skeletonMap f n ≫ skeletonMap g n

def skeletonFamily : I ⥤ ℕ ⥤ SSet.{u}

def skeletonFiltration : ℕ ⥤ I ⥤ SSet.{u} := (skeletonFamily I W).flip

/-- 同じ骨格の塔から元の図式重みへの余錐。 -/
def skeletonCocone : Cocone (skeletonFiltration I W)

def skeletonCocone : Cocone (skeletonFiltration I W)

def skeletonCoconeIsColimit : IsColimit (skeletonCocone I W)

```

#### SimplicialCellSkeleton（45行）

```lean
universe u
namespace SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open CategoryTheory SSet
open scoped Simplicial

theorem nondegenerate_preimage_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    (X.skeleton n).preimage (yonedaEquiv.symm c.val) = ∂Δ[n]

theorem nondegenerate_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (yonedaEquiv.symm c.val) ≤ X.skeleton (n+1)

theorem nondegenerate_boundary_range_skeleton {X : SSet.{u}} {n : ℕ}
    (c : X.nonDegenerate n) :
    Subcomplex.range (∂Δ[n].ι ≫ yonedaEquiv.symm c.val) ≤ X.skeleton n

```

#### BousfieldKanCellTensor（107行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellWeight (n : ℕ) : I ⥤ SSet.{u}

def bkCellTensor (n : ℕ) : SSet.{u} ⥤ I ⥤ SSet.{u}

def bkCellGenerator {n : ℕ} (c : (nerve I).nonDegenerate n) (X : SSet.{u}) :
    X ⟶ ((bkCellTensor I n).obj X).obj (c.val.obj (Fin.last n))

theorem bkCellGenerator_naturality {n : ℕ} (c : (nerve I).nonDegenerate n)
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    bkCellGenerator I c X ≫ ((bkCellTensor I n).map f).app (c.val.obj (Fin.last n)) =
      f ≫ bkCellGenerator I c Y

def bkCellDesc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    (bkCellTensor I n).obj X ⟶ Z

theorem bkCellGenerator_desc {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (c : (nerve I).nonDegenerate n) :
    bkCellGenerator I c X ≫ (bkCellDesc I X Z f).app (c.val.obj (Fin.last n)) = f c

theorem bkCellDesc_unique {n : ℕ} (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n)))
    (m : (bkCellTensor I n).obj X ⟶ Z)
    (hm : ∀ c, bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) = f c) :
    m = bkCellDesc I X Z f

theorem bkCellHom_ext {n : ℕ} {X : SSet.{u}} {Z : I ⥤ SSet.{u}}
    {m m' : (bkCellTensor I n).obj X ⟶ Z}
    (h : ∀ c, bkCellGenerator I c X ≫ m.app (c.val.obj (Fin.last n)) =
      bkCellGenerator I c X ≫ m'.app (c.val.obj (Fin.last n))) : m = m'

```

#### BousfieldKanCellLifting（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem bkCellTensor_map_llp (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.I f) :
    (boundaries I).rlp.llp ((bkCellTensor I n).map f)

```

#### BousfieldKanCellAttachment（77行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellSimplex {n : ℕ} (c : (nerve I).nonDegenerate n) :
    (nerve (Over (c.val.obj (Fin.last n)))).nonDegenerate n

abbrev bkSkeleton := skeletonFiltration I (bousfieldKanWeight I)

/-- 全標準細胞から元の重みへの同じYoneda評価。 -/
def bkCellEvaluation (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I

def bkCellEvaluation (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ bousfieldKanWeight I

def bkCellBoundary (n : ℕ) : (bkCellTensor I n).obj (∂Δ[n] : SSet.{u}) ⟶
    (bkSkeleton I).obj n

def bkCellTop (n : ℕ) : (bkCellTensor I n).obj Δ[n] ⟶ (bkSkeleton I).obj (n+1)

theorem bkCellTop_ι (n : ℕ) :
    bkCellTop I n ≫ (skeletonCocone I (bousfieldKanWeight I)).ι.app (n+1) =
      bkCellEvaluation I n

theorem bkCellAttachment_comm (n : ℕ) :
    bkCellBoundary I n ≫ (bkSkeleton I).map (homOfLE (Nat.le_succ n)) =
      (bkCellTensor I n).map ∂Δ[n].ι ≫ bkCellTop I n

```

#### BousfieldKanCellCoproduct（70行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkCellComponentInclusion {n : ℕ} {i : I} (s : NondegenerateData I n i)
    (X : SSet.{u}) : X ⟶ ((bkCellTensor I n).obj X).obj i

def bkCellComponentCofan (n : ℕ) (i : I) (X : SSet.{u}) :
    Cofan (fun _ : NondegenerateData I n i => X)

def bkCellComponentDesc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) :
    ((bkCellTensor I n).obj X).obj i ⟶ Z

@[reassoc] theorem bkCellComponentInclusion_desc {n : ℕ} {i : I} (X Z : SSet.{u})
    (f : NondegenerateData I n i → (X ⟶ Z)) (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s X ≫ bkCellComponentDesc I X Z f = f s

def bkCellComponentCofanIsColimit (n : ℕ) (i : I) (X : SSet.{u}) :
    IsColimit (bkCellComponentCofan I n i X)

theorem bkCellComponentHom_ext {n : ℕ} {i : I} {X Z : SSet.{u}}
    {f g : ((bkCellTensor I n).obj X).obj i ⟶ Z}
    (h : ∀ s : NondegenerateData I n i,
      bkCellComponentInclusion I s X ≫ f = bkCellComponentInclusion I s X ≫ g) : f = g

```

### 167.3 検証と残り

main取り込み後の219は既存の25本を対象ビルドし **10,619 jobs・終了0**、小監査166宣言・標準三公理のみ。220は自由細胞の先行4本を検証し、合計200宣言。import整理と骨格・自由テンソルの3本を加えた221は **1,590 jobs・終了0**、新規全32本の小監査 **231宣言・標準三公理のみ**。222は境界照合・付着・成分余積の3本を対象ビルドし **1,605 jobs・終了0**、新規全35本の小監査 **255宣言・標準三公理のみ**。実ハンドル35419・61534の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build219.log`〜`222.log`、最終小監査 `/private/tmp/AuditISW2BKCells222.lean`。

個別検査ではover圏のeqToHom、退化の最終頂点、Yoneda同値の往復、自由な生成元を評価する型を明示して修正した。計算上限の変更・sorry・独自公理なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。登録候補は同じBE用JSONへ追記した。

次は相対細胞の添字と自由細胞の余積を照合し、同じ骨格の押し出しから全BK重みの射影cofibrancyを得る。その後に同じjを選び、全Kan係数の制限のホモトピー同値を示す。相対細胞の添字替えの下書きは個別検査中で、この検証済み10本のコミットには含めない。全体の/goalは保持し、停止点3b-4aにもまだ届いていない。

## 168. 同じ重み比較の中間定理 R03a.1 の追加（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。IS-W2 §19の「同じまとまりの中で一つの見込みが1,500行以下」の枠を使い、R03aのKan係数への制限の不変性を次の中間定理 **R03a.1** に分けて一覧へ追加する。R03a・R03a.1とも未完了。⑤aの欄の型・元の重み・native錐の型に変更なし。

```lean
-- universe u
-- open CategoryTheory Limits
-- open SerrePositivity.EInfinity
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
-- open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant
    (I : Type u) [SmallCategory I] (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (HomotopyWeight.boundaries I).rlp.llp (initial.to V))
    (hW : (HomotopyWeight.boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)
```

型は `/private/tmp/CheckProjectiveWeightComparison.lean` で個別検査し、終了0。これは型の検査であって証明ではない。前段で個別検査を終えた元のBKの射影cofibrancyと指定された同じjの構成に、このHom不変性と各値の可縮性を合わせるのがR03aの経路。

証明の案：自由ホーンの小対象分解でfを射影anodyneな左射と成分ごとのKan fibrationな右射へ分ける。左射は成分ごとのanodyneでもあるので、hfと二つ組から右射は成分ごとのtrivial Kan fibration。両方の元の重みの射影cofibrancyを使い、右射の切断と同じシリンダーによるホモトピーを取る。左射の制限は、パラメーター境界とのpushout-productの持ち上げでtrivial Kan fibrationとなる。この二つを同じ制限射の合成として合わせ、実際のホモトピー同値を得る。SSet・図式圏のModelCategoryは仮定しない。

見込みは自由ホーンと点ごとの性質250〜400行、相対テンソルの持ち上げと切断空間の照合350〜550行、分解とホモトピー・最終の合成300〜450行、計900〜1,400行。一つの中間定理として1,500行以下で、R01〜R03とR03aの重み比較の同じまとまり。既存構成の法則と証明分割は各型を追記し、200行を超えるファイルは行数も記録する。見込みが1,500を超えると判明した場合・別のまとまりが必要な場合には検証済みを保存して報告する。

前段の223は相対細胞の添字替え・各成分の評価・同じ骨格の押し出しを対象ビルドし、**1,608 jobs・終了0、38モジュール291宣言・標準三公理のみ**。実ハンドル60582の終了0・鍵返却を確認済み。BK全体のcofibrancyと一つの指定比較射の224は同時整理券一枚で待機中であり、その終了前に検証済みとは数えない。

## 169. 元のBK重みの射影cofibrancyと一つの指定比較射（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。§168のR03a.1は§19の枠で追加済み。R03a・R03a.1の完成とは数えない。

### 169.1 検証済みの到達点

元の相対細胞の添字をBK自由細胞の添字に一致させ、全評価で余積の同型を指定した。各成分の評価が、同じ非退化単体のYoneda射そのものであることも閉じた。これによりMathlibの元の相対細胞の押し出しを、BKの同じ自由境界と二つの骨格の押し出しへ輸送し、評価関手で図式全体の押し出しへ戻した。

左持ち上げ性の押し出し・逐次合成に対する安定性と、前段の元の骨格の余極限を使い、**任意の小圏Iについて元のbousfieldKanWeight Iが射影cofibrant**であることを証明した。最後に指定された二重反対化した一点比較の右持ち上げ性から、一つの `bkFramedWeightComparison J : BK(Jᵒᵖᵒᵖ) → framedLimitWeight J` を選び、元の一点比較を厳密に保つ等式を証明した。このjは係数Hに依存しない。まだその切断空間の制限のホモトピー同値は未完了。

### 169.2 今回の証明分割・法則の型

#### BousfieldKanCellReindex（75行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkInitialCellEquiv (n : ℕ) (i : I) :
    relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n ≃
      NondegenerateData I n i

theorem bkInitialCellEquiv_simplex (n : ℕ) (i : I)
    (c : relativeCellComplexOfMono.Cell ((⊥ : (nerve (Over i)).Subcomplex).ι) n) :
    ((nondegenerateEquiv I n i).symm (bkInitialCellEquiv I n i c)).val = c.simplex

def bkCellReindexIsColimit {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    IsColimit (Cofan.mk (((bkCellTensor I n).obj X).obj i)
      (fun a : α => bkCellComponentInclusion I (e a) X))

def bkCellReindexIso {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) :
    (∐ fun _ : α => X) ≅ ((bkCellTensor I n).obj X).obj i

@[reassoc] theorem bkCellReindexIso_ι {n : ℕ} {i : I} {α : Type u}
    (e : α ≃ NondegenerateData I n i) (X : SSet.{u}) (a : α) :
    Sigma.ι (fun _ : α => X) a ≫ (bkCellReindexIso I e X).hom =
      bkCellComponentInclusion I (e a) X

```

#### BousfieldKanCellEvaluation（81行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

@[reassoc] theorem bkCellComponentInclusion_cellDesc {n : ℕ} {i : I}
    (s : NondegenerateData I n i) (X : SSet.{u}) (Z : I ⥤ SSet.{u})
    (f : ∀ c : (nerve I).nonDegenerate n, X ⟶ Z.obj (c.val.obj (Fin.last n))) :
    bkCellComponentInclusion I s X ≫ (bkCellDesc I X Z f).app i =
      f s.1 ≫ Z.map s.2

@[reassoc] theorem bkCellComponentInclusion_map {n : ℕ} {i : I}
    (s : NondegenerateData I n i) {X Y : SSet.{u}} (f : X ⟶ Y) :
    bkCellComponentInclusion I s X ≫ ((bkCellTensor I n).map f).app i =
      f ≫ bkCellComponentInclusion I s Y

theorem bkCellSimplex_map {n : ℕ} {i : I} (s : NondegenerateData I n i) :
    ((bousfieldKanWeight I).map s.2).app (op ⦋n⦌) (bkCellSimplex I s.1).val =
      ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_evaluation {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s Δ[n] ≫ (bkCellEvaluation I n).app i =
      yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_top_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s Δ[n] ≫ (bkCellTop I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton (n+1)).ι =
        yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

@[reassoc] theorem bkCellComponent_boundary_ι {n : ℕ} {i : I}
    (s : NondegenerateData I n i) :
    bkCellComponentInclusion I s (∂Δ[n] : SSet.{u}) ≫ (bkCellBoundary I n).app i ≫
      (((bousfieldKanWeight I).obj i).skeleton n).ι =
        ∂Δ[n].ι ≫ yonedaEquiv.symm ((nondegenerateEquiv I n i).symm s).val

```

#### BousfieldKanSkeletonPushout（81行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.BousfieldKanCells
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkSkeletonInitialIso (n : ℕ) (i : I) :
    (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n : SSet.{u}) ≅
      ((bkSkeleton I).obj n).obj i

@[reassoc] theorem bkSkeletonInitialIso_ι (n : ℕ) (i : I) :
    (bkSkeletonInitialIso I n i).hom ≫ ((nerve (Over i)).skeleton n).ι =
      (skeletonOfMono ((⊥ : (nerve (Over i)).Subcomplex).ι) n).ι

theorem bkCellAttachment_isPushout_app (n : ℕ) (i : I) :
    IsPushout ((bkCellBoundary I n).app i) (((bkCellTensor I n).map ∂Δ[n].ι).app i)
      (((bkSkeleton I).map (homOfLE (Nat.le_succ n))).app i) ((bkCellTop I n).app i)

theorem bkCellAttachment_isPushout (n : ℕ) :
    IsPushout (bkCellBoundary I n) ((bkCellTensor I n).map ∂Δ[n].ι)
      ((bkSkeleton I).map (homOfLE (Nat.le_succ n))) (bkCellTop I n)

```

#### BousfieldKanCofibrant（51行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def bkSkeletonZeroIsInitial : IsInitial ((bkSkeleton I).obj 0)

theorem bkSkeleton_step_llp (n : ℕ) :
    (boundaries I).rlp.llp ((bkSkeleton I).map (homOfLE (Nat.le_succ n)))

def bkSkeletonTransfinite :
    (boundaries I).rlp.llp.TransfiniteCompositionOfShape ℕ (initial.to (bousfieldKanWeight I))

theorem bousfieldKanWeight_cofibrant :
    (boundaries I).rlp.llp (initial.to (bousfieldKanWeight I))

```

#### BousfieldKanChosenComparison（57行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (J : Type u) [SmallCategory J]

abbrev framedLimitWeightComparison := (doubleOpWeights J).map (comparison J)

theorem framedLimitWeightComparison_rlp :
    (boundaries Jᵒᵖᵒᵖ).rlp (framedLimitWeightComparison J)

def bkFramedPointMap : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ (doubleOpWeights J).obj (point J)

def bkFramedComparisonSquare :
    CommSq (initial.to (framedLimitWeight J)) (initial.to (bousfieldKanWeight Jᵒᵖᵒᵖ))
      (framedLimitWeightComparison J) (bkFramedPointMap J)

def bkFramedWeightComparison : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ framedLimitWeight J

theorem bkFramedWeightComparison_point :
    bkFramedWeightComparison J ≫ framedLimitWeightComparison J = bkFramedPointMap J

```

### 169.3 検証・実測と残り

223はこのうち先行3本で **1,608 jobs・終了0、38モジュール291宣言**。224は全体のcofibrancyと一つの比較射の2本を対象ビルドし **1,615 jobs・終了0、新規全40モジュール309宣言・標準三公理のみ**。両方の実ハンドル60582・52517の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build223.log`・`224.log`、小監査 `/private/tmp/AuditISW2BKCells224.lean`。同時整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ鍵を保持。sorry・独自公理・計算上限の変更0。

今回345行、各200行以下。3b-4の検証済みは **40本・2,503行**。R03aの細胞と比較射の構成は累計1,092行で、当初の細胞の見込み300〜700行に対し約1.6倍。元の骨格への全自然な輸送と既存押し出しの四つの射の等式を明示する行数が増えた。Hom不変性は§168の中間定理R03a.1（900〜1,400行）として別に見積もった。全外枠15,000行にはまだ十分余地がある。

次の自由ホーン・相対テンソル・native切断のKan性の新規下書きは個別検査中。この検証済み5本のコミットには含めない。元の重み・既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査は変更していない。/goalはactiveのまま、Hom不変性へ続ける。

## 170. R03a.1前半の検証と見込みの半分での途中報告（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 1／全体 14（うち追加 2）。R03aとR03a.1は未完了。

### 170.1 到達点・検証

自由ホーンの生成族の小対象性と各値の右類を作った。その全生成左類が、各値でanodyneとなることも、既存の余積・押し出し・逐次合成・レトラクトの法則から証明した。自由ホーンの射とパラメーターの単射の相対テンソルは、各値のKan fibrationを持ち上げる。これを同じweightedCornerと元のcurry・uncurryへ転置し、**射影anodyneな重み制限は、各値がKanな係数についてtrivial Kan fibration**となることを示した。射影cofibrantな両重みでは、元の切断空間がKanであることも証明し、実際の単体的ホモトピー同値まで閉じた。

重みの元の射の自由ホーン分解について、左射の各値のanodyne性、中間重みの射影cofibrancy、右射の各値のfibration性・弱同値性を閉じた。**標的の各値がKanの場合**には、右射は各値で境界右持ち上げ性を持つ。この補助で一般の非Kan標的を代用しない。一般の比較への復帰には、両方の重みのホーン置換と同じ指定比較の分解を使う。

225は先行5本で **1,721 jobs・終了0、新規全45本325宣言**。226は分解の2本で **2,612 jobs・終了0、新規全47本334宣言・標準三公理のみ**。実ハンドル76288・48784の終了0・鍵返却を確認済み。ログ `/private/tmp/isw2-build225.log`・`226.log`、小監査 `/private/tmp/AuditISW2BKCells226.lean`。対象のみ、同時整理券一枚、`--class impl --wait 3600`、ビルドと小監査の間だけ鍵を保持。

### 170.2 実測と残りの再見込み（止まらず継続）

今回7本402行、各200行以下。3b-4の検証済みは **47本・2,905行**。初期§152.4の合計5,700〜9,800行の下端の半分2,850行を超えたので、早めに共通規則の途中報告を残す。R03aの細胞と一つの比較射の構成1,092行に対し、R03a.1は現時点402行（見込み900〜1,400行）。重みの同じ区間ホモトピーを元の切断制限へ運ぶ下書きは個別検査中で、検証済みの行数には含めていない。

残りの見込み：R03a.1の切断・区間ホモトピーと分解の最終接続500〜850行、R03aの指定jへの特殊化・可縮性の照合100〜250行、R02〜R03の元のnative錐族と普遍性への最後の接続700〜1,200行、R04〜R05は1,000〜1,800行、実現R06〜R10は2,800〜4,800行、R11〜R12は500〜900行。合計の残り5,600〜9,800行、全体約8,500〜12,700行で、外枠15,000行を維持する。native錐への接続はまだ未実測のため幅を残す。一般のHom不変性をR03a.1へ分けた分で、初期のR01〜R03の1,400〜2,300行は上振れしている。

ここで止まらず、検証済みを保存してR03a.1の残りへ進む。型・範囲・既存の模型・⑤aの欄を弱めていない。SSet/図式圏のModelCategory仮定・sorry・独自公理・計算上限の変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査は変更していない。

### 170.3 証明分割・法則の型

全てR03a.1の証明分割または既存構成の法則。追加の一覧項目は§168以外0。

#### ProjectiveHornGenerators（36行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits
variable (K : Type u) [SmallCategory K]

abbrev horns : MorphismProperty (K ⥤ SSet.{u})

instance horns_smallObjectArgument : (horns K).HasSmallObjectArgument.{u}

theorem horns_rlp : (horns K).rlp =
    ModelGeneration.EvaluationFamily.detected (evaluation K) SSet.modelCategoryQuillen.J.rlp

```

#### ProjectiveHornValues（62行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet
variable (K : Type u) [SmallCategory K]

theorem free_horn_anodyne (k l : K) {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.modelCategoryQuillen.J f) : SSet.anodyneExtensions (((free K k).map f).app l)

theorem horns_evaluation_le (l : K) :
    horns K ≤ SSet.anodyneExtensions.inverseImage (evaluation K l)

theorem anodyne_relativeCells_le :
    Quillen.relativeCells.{u} SSet.anodyneExtensions ≤ SSet.anodyneExtensions

theorem projectiveHorn_anodyne {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : (horns K).rlp.llp f) (l : K) : SSet.anodyneExtensions (f.app l)

```

#### ProjectiveHornCorner（50行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_corner_lifting {V W F G : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (p : F ⟶ G) (hp : ∀ i, Fibration (p.app i)) :
    HasLiftingProperty (weightedCorner j f).ι p

```

#### NativeWeightedSections（52行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

def coneSpaceParameterIso : WeightedCones.tensorDiagram I W ≅ weightedParameterFunctor W

def coneSpaceNativeSectionsIso : WeightedCones.coneSpace I W ≅ weightedSectionsFunctor W

theorem weightedSections_kanComplex_of_projective_cofibrant
    (hW : (boundaries I).rlp.llp (initial.to W))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SSet.KanComplex (weightedSections W H)

```

#### ProjectiveWeightRestriction（89行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped Simplicial SSet.modelCategoryQuillen
variable {I : Type u} [SmallCategory I]

theorem weightedSectionsPre_trivialKanFibration_of_corner_extensions
    {W W' H : I ⥤ SSet.{u}} (j : W ⟶ W')
    (hcorner : ∀ n, ∀ a : (weightedCorner j (boundary n).ι).pt ⟶ H,
      ∃ b : W' ⊗ (Functor.const I).obj (Δ[n] : SSet.{u}) ⟶ H,
        (weightedCorner j (boundary n).ι).ι ≫ b = a) :
    TrivialKanFibration (weightedSectionsPre j H)

theorem weightedSectionsPre_trivialKanFibration_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (horns I).rlp.llp j)
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    TrivialKanFibration (weightedSectionsPre j H)

theorem weightedSectionsPre_homotopyEquivalence_of_projectiveHorn
    {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (hj : (horns I).rlp.llp j)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (weightedSectionsPre j H)

```

#### ProjectiveHornFactorization（55行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHorn_cofibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) : (boundaries I).rlp.llp j

def projectiveHornFactorization {V W : I ⥤ SSet.{u}} (j : V ⟶ W) :
    MorphismProperty.MapFactorizationData (horns I).rlp.llp (horns I).rlp j

theorem projectiveHornFactorization_i_anodyne {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    SSet.anodyneExtensions ((projectiveHornFactorization I j).i.app i)

theorem projectiveHornFactorization_p_fibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    Fibration ((projectiveHornFactorization I j).p.app i)

theorem projectiveHornFactorization_cofibrant {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V)) :
    (boundaries I).rlp.llp (initial.to (projectiveHornFactorization I j).Z)

```

#### ProjectiveHornWeakFactorization（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHornFactorization_i_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    IsWeakHomotopyEquivalence ((projectiveHornFactorization I j).i.app i)

theorem projectiveHornFactorization_p_weak {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i)) (i : I) :
    IsWeakHomotopyEquivalence ((projectiveHornFactorization I j).p.app i)

theorem projectiveHornFactorization_p_boundary_rlp {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : ∀ i, IsWeakHomotopyEquivalence (j.app i))
    (hW : ∀ i, SSet.KanComplex (W.obj i)) (i : I) :
    SSet.modelCategoryQuillen.I.rlp ((projectiveHornFactorization I j).p.app i)

```

## 171. R03a・R03a.1 の完了：同じ一つの重み比較（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。済みはR01・R03a・R03a.1。R02・R03の指定native錐族・極限性は未完了であり、この重み比較をもって完成とは数えない。

### 171.1 一覧の型のまま閉じた内容

**R03a.1** `weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant` は§168の一般の型のまま証明した。元の射影cofibrantな二重み間の成分ごとの弱同値から、全Kan係数図式への元の制限写像の実際の単体的ホモトピー同値を得る。標的重みがKanでない場合も含む。

まず同じ区間パラメーターを持つ全重みの自然変換を、普遍評価に前合成して元の切断空間の区間ホモトピーへ転置し、両端点が元の制限写像に厳密に一致することを示した。境界右類の射の切断を元の標的重みのcofibrancyで取り、始域重みのcofibrancyで区間境界を持ち上げることにより、同じ全重みの区間収縮を作った。これが右射の制限の実際のホモトピー逆を与える。

各値がKanな標的への自由ホーン分解では、前段の射影anodyneな制限とこの境界右類の制限を合成した。一般の標的は、元の標的の終射の自由ホーン分解によるKan置換を使う。元の比較をその左射へ合成して前のKan標的の場合に適用し、Kanな切断空間での二対三則で元の制限へ戻った。一般の非Kan標的へのfibrationを無条件にtrivialと扱っていない。

**R03a** `exists_strictBETotWeightComparison` は§166で承認された型のまま閉じた。元のBK重みの各値が元のover圏の終対象によって弱可縮であることと、指定された一点比較の境界右類から、**選んだ同じjの全成分が弱同値**であることを示した。これと両方の重みの元の射影cofibrancyをR03a.1へ代入した。

存在するjは `strictBETotWeightComparison := bkFramedWeightComparison (AsSmall SimplexCategory)` として一つに固定した。係数H・その全射ごとに選び直さない。元のW・二重反対添字・重みの制限の向きは保持した。高次自然性やnative錐の構成を、この存在主張だけで代用しない。

### 171.2 最終検証

227は区間転置・両端点の1本で **1,622 jobs・終了0、48モジュール347宣言**。228は区間境界・テンソル持ち上げ・切断収縮・一般比較の4本で **2,708 jobs・終了0、52モジュール362宣言**。229は元のjの各値の比較とBE指定比較の2本で **2,772 jobs・終了0、新規全54モジュール368宣言・標準三公理のみ**。実ハンドル34287・45990・89120の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build227.log`〜`229.log`、最終小監査 `/private/tmp/AuditISW2BKCells229.lean`。

一時合併の検査では他のimportが収縮補題を補っていたため、各値の比較を独立に検査して不足した `MonoRightLiftingContraction` の直接importを明示した。最終229は各実モジュールを独立にビルドしてから全新規の小監査を実行した。sorry・独自公理・計算上限の変更0。SSet/図式圏のModelCategory仮定なし。`--class impl --wait 3600`、同時整理券一枚、鍵はビルド・小監査の間だけ。

### 171.3 見込みと実測

今回7本631行、各200行以下。3b-4の検証済みは **54モジュール・3,536行**。登録候補はBE用JSONへ追記し、入口・公式監査の登録は行っていない。

| 追加項目 | 見込み | 実測 | 差 |
| --- | ---: | ---: | ---: |
| R03aのBK細胞・指定比較と最終特殊化 | 550〜1,150 | 1,186 | 上端+36（約3%） |
| R03a.1の一般の重みHom不変性 | 900〜1,400 | 839 | 下端−61 |
| 合計 | 1,450〜2,550 | 2,025 | 範囲内 |

R03aの細胞分解が当初の見込みより大きくなった一方、Hom不変性は既存の二変数随伴輸送・Kan Whitehead・元のホーン小対象性を再利用できたため短く閉じた。R03a.1は§19の1,500行以下の追加の枠を満たした。§170の全体見込み約8,500〜12,700行、外枠15,000行は維持する。

次はR02・R03の元の普遍重み付き錐の点を、同じ全Hom∞比較・R03aを通して指定native錐へ接続する。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。停止点3b-4aにはまだ届いていない。/goalはactiveのまま、そのまま続ける。

### 171.4 今回の証明分割・法則の型

R03a・R03a.1以外の独立の新しい数学の追加は0。

#### WeightedSourceHomotopy（145行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def weightedSourceHomotopySection {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (weightedSections W H ⊗ (Δ[1] : SSet.{u})) ⟶ H

def weightedSourceHomotopyMap {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W) (H : I ⥤ SSet.{u}) :
    weightedSections W H ⊗ (Δ[1] : SSet.{u}) ⟶ weightedSections V H

def weightIntervalZero (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})

def weightIntervalOne (V : I ⥤ SSet.{u}) :
    V ⟶ V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u})

theorem weightedSourceHomotopyMap_zero {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : weightIntervalZero I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₀ ≫ weightedSourceHomotopyMap I T H = weightedSectionsPre f H

theorem weightedSourceHomotopyMap_one {V W : I ⥤ SSet.{u}}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (f : V ⟶ W) (h : weightIntervalOne I V ≫ T = f) (H : I ⥤ SSet.{u}) :
    SSet.ι₁ ≫ weightedSourceHomotopyMap I T H = weightedSectionsPre f H

def weightedSectionsPreHomotopy {V W : I ⥤ SSet.{u}} {f g : V ⟶ W}
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h₀ : weightIntervalZero I V ≫ T = f) (h₁ : weightIntervalOne I V ≫ T = g)
    (H : I ⥤ SSet.{u}) : SSet.Homotopy (weightedSectionsPre f H) (weightedSectionsPre g H)

```

#### WeightIntervalBoundary（92行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open scoped Simplicial

theorem weight_boundaryMap_naturality {X Y E F : SSet.{u}} (r : X ⟶ Y) (t : E ⟶ F)
    (a b : X ⟶ E) (c d : Y ⟶ F) (ha : r ≫ c = a ≫ t) (hb : r ≫ d = b ≫ t) :
    (r ▷ (∂Δ[1] : SSet.{u})) ≫ boundaryMap c d = boundaryMap a b ≫ t

theorem weight_boundaryMap_comp {X E B : SSet.{u}} (a b : X ⟶ E) (p : E ⟶ B)
    (h : a ≫ p = b ≫ p) :
    boundaryMap a b ≫ p = fst X (∂Δ[1] : SSet.{u}) ≫ b ≫ p

def weightIntervalBoundary {V W : I ⥤ SSet.{u}} (f g : V ⟶ W) :
    V ⊗ (Functor.const I).obj (∂Δ[1] : SSet.{u}) ⟶ W

theorem weightIntervalBoundary_lift_zero {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalZero I V ≫ T = f

theorem weightIntervalBoundary_lift_one {V W : I ⥤ SSet.{u}} (f g : V ⟶ W)
    (T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ W)
    (h : (V ◁ (Functor.const I).map ∂Δ[1].ι) ≫ T = weightIntervalBoundary I f g) :
    weightIntervalOne I V ≫ T = g

```

#### ProjectiveWeightTensorLifting（48行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem projectiveWeight_tensor_lifting (W : I ⥤ SSet.{u})
    (hW : (boundaries I).rlp.llp (initial.to W))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] {F G : I ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i)) :
    HasLiftingProperty ((weightedParameterFunctor W).map f) p

```

#### ProjectiveBoundaryContraction（78行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel.LargeParameterHomotopy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def weightIntervalProjection (V : I ⥤ SSet.{u}) :
    V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V

theorem exists_projectiveBoundary_section {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hW : (boundaries I).rlp.llp (initial.to W)) : ∃ s : W ⟶ V, s ≫ p = 𝟙 W

theorem exists_projectiveBoundary_contraction {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (boundaries I).rlp.llp (initial.to V)) (s : W ⟶ V) (hs : s ≫ p = 𝟙 W) :
    ∃ T : V ⊗ (Functor.const I).obj (Δ[1] : SSet.{u}) ⟶ V,
      weightIntervalZero I V ≫ T = p ≫ s ∧ weightIntervalOne I V ≫ T = 𝟙 V

theorem weightedSectionsPre_homotopyEquivalence_of_projectiveBoundary
    {V W : I ⥤ SSet.{u}} (p : V ⟶ W)
    (hp : ∀ i, SSet.modelCategoryQuillen.I.rlp (p.app i))
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W)) (H : I ⥤ SSet.{u}) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre p H)

```

#### ProjectiveWeightComparison（74行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

theorem projectiveHornReplacement_kan (W : I ⥤ SSet.{u}) (i : I) :
    SSet.KanComplex ((projectiveHornFactorization I (terminal.from W)).Z.obj i)

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant_kan_target
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (hWK : ∀ i, SSet.KanComplex (W.obj i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)

theorem weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant
    (V W : I ⥤ SSet.{u}) (f : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V))
    (hW : (boundaries I).rlp.llp (initial.to W))
    (hf : ∀ i, IsWeakHomotopyEquivalence (f.app i))
    (H : I ⥤ SSet.{u}) (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre f H)

```

#### BousfieldKanComparisonValues（53行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

theorem bousfieldKanWeight_isWeaklyContractible (I : Type u) [SmallCategory I] (i : I) :
    IsWeaklyContractible ((bousfieldKanWeight I).obj i)

theorem framedLimitWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((framedLimitWeightComparison J).app i)

theorem bkFramedWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((bkFramedWeightComparison J).app i)

```

#### StrictDiagramTotWeightComparison（41行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

abbrev strictBETotWeightComparison :=
  HomotopyWeight.bkFramedWeightComparison (AsSmall.{u} SimplexCategory)

theorem strictBETotWeightComparison_homotopyEquivalence
    (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u})
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre strictBETotWeightComparison H)

theorem exists_strictBETotWeightComparison :
    ∃ j : bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⟶
        HomotopyWeight.framedLimitWeight (AsSmall.{u} SimplexCategory),
      ∀ (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u}),
        (∀ i, SSet.KanComplex (H.obj i)) →
          IsSimplicialHomotopyEquivalence (weightedSectionsPre j H)

```

## 172. 元のprobe錐から同じBK切断への実写像・指定点の接続（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。R02・R03は未完了。

### 172.1 今回の到達点

§171までの重み比較を、元の普遍probe錐の**同じ零単体**へ適用した。先に既存のconeSpaceとnativeなweightedSectionsの右随伴同型が同じHom転置を運ぶ式を示し、標準零単体のテンソル同型がnativeな第一射影へ移ることを照合した。その結果、元の `conePoint s` が同じ自然変換sのnative切断の零単体へ移ることを、π₀でなく実際の零単体の等式として証明した。

次に指定した一つの `bkFramedWeightComparison K` の前合成で、同じ普遍probe錐を `BK(Kᵒᵖᵒᵖ) →` 元の右frame Hom係数図式へ送った。元のprobe錐空間から同じBK切断空間への実写像 `strictBETotProbeConeBKMap` を定義し、そのホモトピー同値性を各右frameのKan性とR03a.1から証明した。この同じ写像が元の `strictBETotUniversalProbeConePoint` を指定された `strictBETotUniversalBKProbeConePoint` へ送る等式も閉じた。

元のTot頂点・probe・右frame・一点重み・同じ比較jを保っている。まだBK切断の点から**全図式射を含むnative join錐の族**への接続はしていないため、R02・R03・停止点3b-4aの完成とは数えない。Uの極限保存から元のBE錐の極限性を逆算していない。

### 172.2 検証

230は右随伴の点・重み制限の点・元のBK普遍点の3本で **5,055 jobs・終了0、57モジュール380宣言**。231は同じ実写像のホモトピー同値の1本で **5,105 jobs・終了0、新規全58モジュール387宣言・標準三公理のみ**。実ハンドル31290・34664の終了0を確認し、鍵返却済み。ログ `/private/tmp/isw2-build230.log`・`231.log`、最終小監査 `/private/tmp/AuditISW2BKCells231.lean`。対象ビルドのみで、root・公式監査は流していない。

個別検査では、opaqueなendを展開して転置を同一視する代わりに、元のHom同値の両側の逆性を明示した。またKan性を同じ右随伴の全関手評価の型で明示して型クラス探索に渡した。計算上限の変更・sorry・独自公理0。SSetモデル構造の仮定なし。`--class impl --wait 3600`、同時整理券一枚、ビルドと小監査の間だけ鍵を保持した。

今回4本256行、各200行以下。3b-4の検証済み **58本・3,792行**。登録候補は同じBE用JSONへ追記。全体見込み・外枠15,000行は§170〜171のまま。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。

### 172.3 型と残り

今回全て既存の右随伴・前合成・元の右frameの法則の照合。独立の新しい数学の一覧への追加0。次は同じ係数図式を既存の全Hom∞比較の入口へ合わせ、分類された切断から同じnative join錐へ進む。SimplicialHomとそのopを定義的に同一視せず、元の全自然同型・同じ頂点・両境界を保持する。/goalはactiveのまま続ける。

#### NativeWeightedSectionPoints（67行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

theorem coneSpaceNativeSectionsIso_homEquiv (X : SSet.{u}) (H : I ⥤ SSet.{u})
    (f : (WeightedCones.tensorDiagram I W).obj X ⟶ H) :
    (WeightedCones.adjunction I W).homEquiv X H f ≫ (coneSpaceNativeSectionsIso I W).hom.app H =
      weightedSectionsLift ((coneSpaceParameterIso I W).inv.app X ≫ f)

theorem coneSpaceParameterIso_zero :
    (coneSpaceParameterIso I W).inv.app (Δ[0] : SSet.{u}) ≫ (zeroTensorWeightIso I W).hom =
      fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))

theorem coneSpaceNativeSectionsIso_point {H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (((coneSpaceNativeSectionsIso I W).hom.app H).app (Opposite.op ⦋0⦌)) (conePoint I W s) =
      SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s))

```

#### NativeWeightedPointRestriction（46行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

def nativeWeightedPoint {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (weightedSections W H) _⦋0⦌

theorem nativeWeightedPoint_pre {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (s : W ⟶ H) :
    ((weightedSectionsPre j H).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (j ≫ s)

```

#### StrictDiagramTotUniversalBKProbeCone（58行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

abbrev strictBETotProbeCoefficients (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotUniversalBKProbeWeightedCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F)

def strictBETotUniversalBKProbeConePoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌

theorem strictBETotUniversalBKProbeConePoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
        ((((HomotopyWeight.coneSpaceNativeSectionsIso Kᵒᵖᵒᵖ
          (HomotopyWeight.framedLimitWeight K)).hom.app
            (strictBETotProbeCoefficients A K F ((framedLimitFunctor A K).obj F))).app (op ⦋0⦌))
              (strictBETotUniversalProbeConePoint A K F)) =
      strictBETotUniversalBKProbeConePoint A K F

```

#### StrictDiagramTotBKSections（85行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotBKSectionsModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotBKSectionsProbeCofibrant (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

theorem strictBETotProbeCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    SSet.KanComplex ((strictBETotProbeCoefficients A K F Y).obj i)

theorem strictBETotProbeBKRestriction_homotopyEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre (HomotopyWeight.bkFramedWeightComparison K)
      (strictBETotProbeCoefficients A K F Y))

def strictBETotProbeConeBKMap (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    ((framedLimitConeSpace A K Y).obj F) ⟶
      weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ) (strictBETotProbeCoefficients A K F Y)

theorem strictBETotProbeConeBKMap_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (strictBETotProbeConeBKMap A K F Y)

theorem strictBETotProbeConeBKMap_point (F : K ⥤ (operad A).Algebra) :
    ((strictBETotProbeConeBKMap A K F ((framedLimitFunctor A K).obj F)).app (op ⦋0⦌))
      (strictBETotUniversalProbeConePoint A K F) = strictBETotUniversalBKProbeConePoint A K F

```

## 173. 全rightFrameHom係数と同じBK重みの宇宙移送（2026-11-14）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。R02・R03は未完了。

### 173.1 検証済みの到達点

元の右frameの反対圏Homと全Hom∞比較の入口の `rightFrameHom` を、同じ二重反対添字Kᵒᵖᵒᵖの**全射に自然な同型**として束ねた。元の自然同型 `rightFrameHomOpIso` の各成分を使い、各添字で独立に逆を選んでいない。指定されたBK普遍錐を同じ係数同型の逆で全rightFrameHom図式へ送り、同じ零単体の輸送の等式を閉じた。元の係数同型で戻すと、自然変換全体として元のBK普遍錐に戻る。

次のHom∞比較の入口は `rightFrameHammockKanDiagram` のphase0で、これは元のrightFrameHomの**宇宙持ち上げの後にEx∞を施した全図式**。単に同じKan複体だから定義的に等しいとは扱わない。また元の添字Kの宇宙uからmax(u,v)へのAsSmall変更が必要になるため、既存の0宇宙基底版の法則を、同じ明示的なover列のup・downで一般宇宙へ移した。

新規 `BousfieldKanUniverseWeight` は、`bousfieldKanWeight (AsSmall.{v} J)` と `AsSmall.down ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}` の実同型を、元のdownを順射として指定する。単体・構造射・添字の作用を保持し、別の重みを選んでいない。一般になった宇宙変更の法則なのでKerodon/LimitsAndColimits/HomotopyLimitsAndColimits/へ置いた。既存の0宇宙版やG10のファイルは変更していない。

### 173.2 検証・規模

232は係数の同型・点の後合成の2本で **5,107 jobs・終了0、60モジュール397宣言**。233は一般宇宙の重み同型の1本で **1,242 jobs・終了0、新規全61モジュール408宣言・標準三公理のみ**。実ハンドル84787・79978の終了0・鍵返却を確認。ログ `/private/tmp/isw2-build232.log`・`233.log`、小監査 `/private/tmp/AuditISW2BKCells233.lean`。対象ビルドと小監査だけ、`--class impl --wait 3600`、同時整理券一枚。

今回3本173行、各200行以下。3b-4の検証済み **61本・3,965行**。登録候補の同じJSONには一般のKerodonの1本も追加した。sorry・独自公理・計算上限の変更0。SSetモデルの仮定なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの作業木は変更していない。既存構成の係数移送・自然性の法則の照合であり、新しい独立の数学の一覧への追加0。

### 173.3 次の接続（未証明を明記）

次に必要なのは、同じBK切断の宇宙変更を切断空間全体の同型へ移すこと。型の案を一時ファイル `/private/tmp/CheckBKUniverseSectionsType.lean` で検査し、終了0を確認した。これは型の検査だけで、この同型の証明を済みとは数えていない。

```lean
-- universe u v
-- open CategoryTheory
-- open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

def bousfieldKanUniverseSectionsIso (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u}) :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u})
```

候補は、今回の同じBK重みの同型、既存の切断の `uliftSectionsIso`・`bousfieldKanSectionsIso`、またはULiftの全忠実性と元の転置の自然性を使う経路。実際の順射と元の指定点・標準脚の等式を保持して組み立てる。続くEx∞への係数の単位については、既存 `BousfieldKanHomotopyInvariance.bousfieldKanMap_homotopyEquivalence` がKan係数の成分ごとの同値から**同じ係数射が誘導するBK切断写像**のホモトピー同値を与える。ここを新しい係数不変性の定理で作り直す必要はない。

その後、既存 `weightedNerveStraighteningUnitIso` と§165の全Hom∞比較を使い、同じ分類像・cosliceの切断へ移す。`fixedVertexConeSpaceEquiv` に戻す際は元の頂点を指定し、全族の両境界と、極限判定のa・ha・heの同じ頂点評価の等式を省略しない。まだnative join錐族を構成・検証したとは数えない。/goalはactiveのまま、次の同じ宇宙の切断の照合へ続ける。

### 173.4 今回の法則の型

#### NativeWeightedPointMap（28行）

```lean
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

theorem nativeWeightedPoint_map {W F G : I ⥤ SSet.{u}} (s : W ⟶ F) (f : F ⟶ G) :
    ((weightedSectionsMap W f).app (Opposite.op ⦋0⦌)) (nativeWeightedPoint I s) =
      nativeWeightedPoint I (s ≫ f)

```

#### StrictDiagramTotProbeCoefficientsComparison（68行）

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeCoefficientComparisonModel : ModelCategory (operad A).Algebra := modelCategory A

def strictBETotProbeRightHomDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotProbeCoefficientsIso (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    strictBETotProbeRightHomDiagram A K F Y ≅ strictBETotProbeCoefficients A K F Y

def strictBETotUniversalBKRightHomCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F)

theorem strictBETotUniversalBKRightHomCone_back (F : K ⥤ (operad A).Algebra) :
    strictBETotUniversalBKRightHomCone A K F ≫
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).hom =
        strictBETotUniversalBKProbeWeightedCone A K F

def strictBETotUniversalBKRightHomPoint (F : K ⥤ (operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))) _⦋0⦌

theorem strictBETotUniversalBKRightHomPoint_comparison (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (strictBETotProbeCoefficientsIso A K F ((framedLimitFunctor A K).obj F)).inv).app (op ⦋0⦌))
        (strictBETotUniversalBKProbeConePoint A K F) = strictBETotUniversalBKRightHomPoint A K F

```

#### BousfieldKanUniverseWeight（77行）

```lean
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory
variable (J : Type u) [SmallCategory J]

def bousfieldKanUniverseOverLift (j : AsSmall.{v} J) :
    Over ((AsSmall.down : AsSmall.{v} J ⥤ J).obj j) ⥤ Over j

theorem bousfieldKanUniverseOverLift_down (j : AsSmall.{v} J) :
    bousfieldKanUniverseOverLift J j ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) = 𝟭 _

theorem bousfieldKanUniverseOverDown_lift (j : AsSmall.{v} J) :
    Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanUniverseOverLift J j = 𝟭 _

def bousfieldKanUniverseWeightDown : bousfieldKanWeight (AsSmall.{v} J) ⟶
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}

instance bousfieldKanUniverseWeightDown_isIso : IsIso (bousfieldKanUniverseWeightDown.{u,v} J)

def bousfieldKanUniverseWeightIso : bousfieldKanWeight (AsSmall.{v} J) ≅
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u}

```

## 174. 同じBK切断の宇宙変更と指定点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 14（うち追加 2）。

R02〜R03の係数移送の法則として、ULiftとAsSmall.downによる同じ切断空間の比較を構成した。順射は元の普遍評価の転置で、ULiftの全忠実性から各標準単体上で全単射になることを示した。同じBK重みの指定downとの合成が `bousfieldKanUniverseSectionsIso` の順射である。さらに元の自然変換が定める零単体を、同じdownで運んだ自然変換の零単体へ厳密に送ることを示した。新しいKan置換や別の指定点を選んでいない。

7本・366行追加、累計68本・4331行（外枠15,000行）。いずれも200行以下。既存の宇宙変更・切断の普遍性・係数移送の法則で、一覧の追加項目は増やさない。native join錐の族と極限性はまだ未完で、R02/R03を完了とは数えない。

検証：対象ビルド234は1,262 jobs、235は2,346 jobsで成功。235の小監査は68本・434宣言、標準三公理 `propext`・`Classical.choice`・`Quot.sound` のみ。両ログで成功と監査完走を確認し、235のプロセスも終了済み。sorry・新規公理なし。共通入口と本体監査には登録せず、上記manifestを調整役への登録候補とする。

次は同じ零単体をEx∞の係数単位に運び、既存の全Hom∞比較およびcoslice分類との比較へ接続する。元の頂点と脚の照合を残す。

### 174.1 今回の法則と証明分割の型

#### BousfieldKanUniversePoints（43行）

```lean
def bousfieldKanUniverseCone (s : bousfieldKanWeight I ⟶ H) :
    bousfieldKanWeight (AsSmall.{v} I) ⟶ (weightedDiagramUniverse.{u,v} I).obj H

theorem bousfieldKanUniverseSectionsIso_point (s : bousfieldKanWeight I ⟶ H) :
    (((bousfieldKanUniverseSectionsIso.{u,v} I H).hom).app (Opposite.op ⦋0⦌))
      (ULift.up (nativeWeightedPoint I s)) =
        nativeWeightedPoint (AsSmall.{v} I) (bousfieldKanUniverseCone I s)
```

#### BousfieldKanUniverseSections（32行）

```lean
def bousfieldKanUniverseSectionsIso :
    (SSet.uliftFunctor.{max u v,u}).obj (bousfieldKanHolim H) ≅
      bousfieldKanHolim ((AsSmall.down : AsSmall.{v} I ⥤ I) ⋙ H ⋙
        SSet.uliftFunctor.{max u v,u})

theorem bousfieldKanUniverseSectionsIso_hom :
    (bousfieldKanUniverseSectionsIso.{u,v} I H).hom =
      weightedSectionsUniverseComparison I (bousfieldKanWeight I) H ≫
        weightedSectionsPre (bousfieldKanUniverseWeightDown I) ((weightedDiagramUniverse.{u,v} I).obj H)
```

#### WeightedDiagramUniverse（72行）

```lean
def weightedDiagramUniverse : (I ⥤ SSet.{u}) ⥤ (AsSmall.{v} I ⥤ SSet.{max u v})

instance weightedDiagramUniverse_full : (weightedDiagramUniverse.{u,v} I).Full

instance weightedDiagramUniverse_faithful : (weightedDiagramUniverse.{u,v} I).Faithful

def weightedDiagramUniverseTensorIso (W : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (weightedDiagramUniverse.{u,v} I).obj (W ⊗ (Functor.const I).obj A) ≅
      (weightedDiagramUniverse.{u,v} I).obj W ⊗
        (Functor.const (AsSmall.{v} I)).obj ((SSet.uliftFunctor.{max u v,u}).obj A)

@[reassoc] theorem weightedDiagramUniverseTensorIso_inv_parameter (W : I ⥤ SSet.{u})
    {A B : SSet.{u}} (f : A ⟶ B) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁
      (Functor.const (AsSmall.{v} I)).map ((SSet.uliftFunctor.{max u v,u}).map f)) ≫
        (weightedDiagramUniverseTensorIso I W B).inv =
      (weightedDiagramUniverseTensorIso I W A).inv ≫
        (weightedDiagramUniverse I).map (W ◁ (Functor.const I).map f)
```

#### WeightedSectionsUniverseComparison（47行）

```lean
def weightedSectionsUniverseEvaluation :
    (weightedDiagramUniverse.{u,v} I).obj W ⊗
      (Functor.const (AsSmall.{v} I)).obj
        ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) ⟶
          (weightedDiagramUniverse.{u,v} I).obj H

def weightedSectionsUniverseComparison :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ⟶
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)

theorem weightedSectionsUniverseComparison_map_uncurry {A : SSet.{u}}
    (f : A ⟶ weightedSections W H) :
    weightedSectionsUncurry ((SSet.uliftFunctor.{max u v,u}).map f ≫
      weightedSectionsUniverseComparison I W H) =
        (weightedDiagramUniverseTensorIso I W A).inv ≫
          (weightedDiagramUniverse I).map (weightedSectionsUncurry f)
```

#### WeightedSectionsUniverseHomEquiv（42行）

```lean
def weightedSectionsUniverseHomEquiv (A : SSet.{u}) :
    (A ⟶ weightedSections W H) ≃
      ((SSet.uliftFunctor.{max u v,u}).obj A ⟶
        weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
          ((weightedDiagramUniverse.{u,v} I).obj H)) where
  toFun f
```

#### WeightedSectionsUniverseIso（62行）

```lean
def weightedSectionsUniverseSimplexEquiv (n : ℕ) :
    ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌ ≃
      (weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)) _⦋n⦌

theorem weightedSectionsUniverseSimplexEquiv_apply {n : ℕ}
    (s : ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) _⦋n⦌) :
    weightedSectionsUniverseSimplexEquiv I W H n s =
      (weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋n⦌) s

instance weightedSectionsUniverseComparison_isIso :
    IsIso (weightedSectionsUniverseComparison.{u,v} I W H)

def weightedSectionsUniverseIso :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ≅
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H)
```

#### WeightedSectionsUniversePoints（68行）

```lean
@[reassoc] theorem weightedDiagramUniverseTensorIso_zero_fst (W : I ⥤ SSet.{u}) :
    ((weightedDiagramUniverse.{u,v} I).obj W ◁ (Functor.const (AsSmall.{v} I)).map
      (uliftStdSimplexIso.{u,max u v} 0).inv) ≫
        (weightedDiagramUniverseTensorIso I W (Δ[0] : SSet.{u})).inv ≫
          (weightedDiagramUniverse I).map (fst W ((Functor.const I).obj (Δ[0] : SSet.{u}))) =
      fst ((weightedDiagramUniverse.{u,v} I).obj W)
        ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v}))

theorem weightedSectionsUniverseComparison_point {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    ((weightedSectionsUniverseComparison.{u,v} I W H).app (Opposite.op ⦋0⦌))
      (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)))) =
        SSet.yonedaEquiv (weightedSectionsLift
          (fst ((weightedDiagramUniverse.{u,v} I).obj W)
            ((Functor.const (AsSmall.{v} I)).obj (Δ[0] : SSet.{max u v})) ≫
              (weightedDiagramUniverse.{u,v} I).map s))
```

## 175. 分類比較から同じ切断模型への接続 R03b（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 15（うち追加 3）。

IS-W2 §19の同じまとまり・1,500行以下の枠で、次の中間項目 **R03b** を追加する。R02〜R03の、元のBK係数のweighted nerveと同じ頂点のcosliceの引き戻しの分類比較から、その二つの射影の切断空間へ戻す段である。全分類同型だけをnative切断や錐そのものと取り違えないために、元の二つの射影を型に指定する。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

def classifiedLeftFibrationSectionsEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) :
    QCatEquivalence (simplicialSections p) (simplicialSections q)
```

見込みは250〜500行（同じ底を厳密に保つ復元の比較80〜160行、相対関手空間と元の切断模型の照合100〜180行、合成・BEへの適用70〜160行）。既存 `leftStraighteningInfinityReconstruction`、`smallLeftUnstraighteningComparisonOfFunctorIso` と、底上の前合成同値による `relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence` を使う。共通の復元を頂点とする二本の実写像で比較し、元の切断空間の同型を通して戻す。新しいstrictificationやBE模型は作らない。

これは固定された射影の中間比較であり、R02の全図式射の錐族・R03の極限判定のa・ha・heは残す。元の指定BK点の像と、元の図式の標準脚の一致も後で明記する。この比較だけでnative join錐族を完成と数えない。外枠15,000行・⑤aの既存欄の型は変更しない。見込みが1,500行を超える場合や別のまとまりが必要と分かった場合は、検証済みを保存して報告する。

## 176. 同じEx∞係数とnative錐射影の全分類比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 3／全体 15（うち追加 3）。R03bは§175で追加し個別検査中。R02/R03は未完了。

元のraw right-frame Hom係数を同じAsSmall.downとULiftで運び、元のEx∞単位を合成した。Kan係数への単位が誘導する**実際のBK切断写像**のホモトピー同値を、既存BK係数不変性から証明した。元の指定BK点が同じ宇宙変更と同じ単位により送られる零単体の等式も証明した。

この係数図式は、既存の全frame比較の第零Kan図式を指定添字関手で引き戻したものと定義どおり等しい。そのcoherent nerveも既存の全図式の前合成と等しい。これに元の全Hom∞比較とcoslice分類の全同型を合成し、同じweighted nerveと同じ頂点のnative錐射影の**元の二つのleft fibrationの全分類同型**まで接続した。値ごとの同値だけを集めたものではない。

検証：236は対象ビルド10,630 jobs・70本448宣言、237は10,639 jobs・73本482宣言、238は10,636 jobs・74本497宣言。各対象ビルドと小監査が終了0、標準三公理のみ。対象は新規2本・3本・1本を指定し、rootや公式大監査は実行していない。実ハンドル67359・21555・31411の終了0を確認。個別検査で不足していたKanインスタンスと関手的分解を明示し、計算上限は変更しなかった。

今回6本415行、累計74本・4746行。各200行以下。全て既存の係数移送・全比較の合成・貼り合わせの法則で、これら6本による一覧の追加は0。新しい中間項目は別途§175のR03bだけ。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

次はR03bの元の切断模型への復帰、その同じ比較を通じた指定点の像と元の標準脚の照合。native join錐の全族や極限判定のa・ha・heはまだ証明したと数えない。

### 176.1 今回の法則の型

#### BousfieldKanExInfinityUnit（53行）

```lean
def bousfieldKanExInfinityCoefficientUnit (H : I ⥤ SSet.{u}) : H ⟶ H ⋙ exInfinity

theorem bousfieldKanExInfinityUnit_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (bousfieldKanExInfinityCoefficientUnit I H))

theorem bousfieldKanExInfinityUnit_point {H : I ⥤ SSet.{u}}
    (s : bousfieldKanWeight I ⟶ H) :
    ((weightedSectionsMap (bousfieldKanWeight I)
      (bousfieldKanExInfinityCoefficientUnit I H)).app (Opposite.op ⦋0⦌))
        (nativeWeightedPoint I s) = nativeWeightedPoint I
          (s ≫ bousfieldKanExInfinityCoefficientUnit I H)
```

#### StrictDiagramTotProbeKanCoefficients（96行）

```lean
def strictBETotProbeFrameIndex (F : K ⥤ (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ AsSmall.{u+1} (operad A).Algebra

theorem strictBETotProbeKanCoefficients_eq (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj (strictBETotProbeRightHomDiagram A K F Y) ⋙
      exInfinity = strictBETotProbeFrameIndex A K F ⋙
        FrameHom.rightFrameHammockKanDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotProbeRightHomDiagram_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeRightHomDiagram A K F Y).obj i)

theorem strictBETotProbeUniverseCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex (((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
      (strictBETotProbeRightHomDiagram A K F Y)).obj i)

theorem strictBETotProbeBKExInfinityUnit_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap
      (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit (AsSmall.{u+1} Kᵒᵖᵒᵖ)
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F Y))))

def strictBETotUniversalBKExInfinityCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶
      (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
        (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F)) ⋙ exInfinity

theorem strictBETotUniversalBKExInfinityCone_point (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))))).app (op ⦋0⦌))
        (((bousfieldKanUniverseSectionsIso.{u,u+1} Kᵒᵖᵒᵖ
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))).hom).app (op ⦋0⦌)
            (ULift.up (strictBETotUniversalBKRightHomPoint A K F))) =
      HomotopyWeight.nativeWeightedPoint _ (strictBETotUniversalBKExInfinityCone A K F)
```

#### StrictDiagramTotProbeCosliceClassification（63行）

```lean
def strictBEAlgebraProbeCosliceClassificationIso (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C

def strictBETotDiagramProbeCosliceClassificationIso
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : (operad A).Algebra) :
    FunctorIso
      ((SSet.uliftFunctor.{u+2,u+1}).map (strictBECosimplicialNerve A F) ≫
        (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelUpNerve A) ≫
          FrameHom.rightFrameHammockCoherentDiagram
            ((SimplicialLocalization.modelSourceFrameFamily (C
```

#### StrictDiagramTotProbeKanDiagram（53行）

```lean
def strictBETotProbeKanDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ KanObject.{u+1}

theorem strictBETotProbeKanDiagram_frame (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    strictBETotProbeKanDiagram A K F Y = strictBETotProbeFrameIndex A K F ⋙
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotProbeKanDiagram_coherent (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y) =
      (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C
```

#### StrictDiagramTotBKClassification（74行）

```lean
def strictBETotUniverseDiagram (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) ⟶
      (SSet.uliftFunctor.{u+2,u+1}).obj (CAlg_R A)

def strictBETotKanDiagramCosliceIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso (kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y))
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))))

def strictBETotBKClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningCandidate ((weightedNerveKanEnriched (AsSmall.{u+1} Kᵒᵖᵒᵖ)).obj
        ⟨strictBETotProbeKanDiagram A K F Y, trivial⟩).val.hom)
      (strictBETotUniverseDiagram A K F ≫
        leftStraighteningInfinityDiagram (sliceUnderProjection (SSet.yonedaEquiv.symm
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))))
```

#### StrictDiagramTotBKNativeClassification（76行）

```lean
def strictBETotUniverseSourceDiagram (F : K ⥤ (operad A).Algebra) :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶ CAlg_R A

theorem strictBETotUniverseSourceDiagram_lift (F : K ⥤ (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotUniverseSourceDiagram A K F) =
      strictBETotUniverseDiagram A K F

def strictBETotBKNativeClassificationIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    FunctorIso
      (leftStraighteningInfinityDiagram (weightedNerveProjection
        (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget)))
      (leftStraighteningInfinityDiagram (coherentConeProjection
        (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
          (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))))
```

## 177. R03b完了と元のΔ図式上の一つの指定native錐（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。済みはR01・R03a・R03a.1・R03b。R02の全錐族、R03の極限性は未完了。

§175の型のまま `classifiedLeftFibrationSectionsEquivalence` を証明した。元の二つの射影から共通の小さいunstraighteningへの底上の二本の比較を使い、元の切断空間の実際の同値へ戻した。BEでは、同じBK係数の切断から、元のCAlg図式と同じ頂点のnative錐の切断模型への同値を得た。

この比較による**元の普遍BK点の像**を指定頂点の錐との既存全単射で戻して、実際のjoin錐を作った。左境界は元のTot頂点のYoneda射に等しく、同じ切断模型へ戻した点は元のBK点の同じ像に等しい。さらに元のAsSmall・二重反対の指定同型で元のΔ添字に戻した。同型に沿う全図式は `strictBECosimplicialDiagram A F` と厳密に等しく、戻したnative錐 `strictBETotNativeConeAt` の頂点も元のTot頂点そのものである。

**まだ示していないもの**：この一図式の錐の全図式射についての族、元の標準脚の最終照合、元の同じ錐の極限性。そのため `strictBETotNativeConeAt` はR02の全族を完成と数える代用にしない。特にR03の判定のa・ha・heを省略せず、Uの極限保存から逆向きに元のBEの極限性を推論しない。

### 177.1 検証と行数

239：三本の対象ビルド10,639 jobs・終了0、小監査77本527宣言。240：二本の対象ビルド10,642 jobs・終了0、小監査79本539宣言。いずれも標準三公理のみ。実ハンドル35625・74011の終了0を確認、鍵は返却済み。個別検査で元の切断空間のKan性を局所に明示し、計算上限の変更なし。sorry・独自公理0。

今回5本298行、累計79本・5044行（外枠15,000）。各200行以下。R03bの一般形・BEへの適用・元の指定BK点からの錐の組立ては199行で、§175の250〜500行の見込みを51〜301行下回った。添字移送と元のΔ上の錐の照合は別に99行の既存の構成の法則・証明分割で、追加項目には数えない。R03b以外の新しい項目は追加していない。⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparison・共通入口・公式監査・mainは変更していない。

### 177.2 見込みの半分での追記

§170で初期見込みの下端5,700行の半分を報告済み。今回、初期上端9,800行の半分4,900行も超えた。現在5044行。元の重み比較を作り直す必要はなくなり、元の指定BK点から実際の同じ頂点の錐へ到達した。一方、全族の高次自然性と標準脚の照合の部分には未実測の幅が残る。

残りの見込み：R02〜R03の標準脚・全錐族・極限判定の接続1,000〜2,000行、R04〜R05の台のTotと局所化1,000〜1,800行、実現R06〜R10が2,800〜4,800行、R11〜R12が500〜900行。残り約5,300〜9,500行、累計約10,300〜14,500行。外枠15,000は維持するが上側の余裕は小さく、次の接続の実測で更新する。型・範囲を弱めたり、点ごとの錐を全族と読み替えたりしない。

次は、同じ錐の脚の評価と、既存の全自然比較を使った全族の接続。R03bの切断の逆の選択だけで図式射について厳密な自然性が自動的に得られるとは主張しない。指定された全比較に戻して両境界を照合する。

### 177.3 今回の型

#### ClassifiedSectionsComparison（62行）

```lean
theorem simplicialSectionsMap_isQCatEquivalence_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsQCatEquivalence (simplicialSectionsMap f hf)

def classifiedLeftFibrationSectionsEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) :
    QCatEquivalence (simplicialSections p) (simplicialSections q)
```

#### StrictDiagramTotBKNativeSections（55行）

```lean
def strictBETotBKNativeSectionsEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    QCatEquivalence
      (bousfieldKanHolim (strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget))
      (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)))
```

#### StrictDiagramTotUniverseNativeCone（77行）

```lean
def strictBETotUniverseNativeConePoint (F : K ⥤ (operad A).Algebra) :
    (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))) _⦋0⦌

def strictBETotUniverseNativeCone (F : K ⥤ (operad A).Algebra) :
    JoinCone (strictBETotUniverseSourceDiagram A K F)

theorem strictBETotUniverseNativeCone_vertexMap (F : K ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotUniverseNativeCone A K F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))

theorem strictBETotUniverseNativeCone_section (F : K ⥤ (operad A).Algebra) :
    fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))
      ⟨strictBETotUniverseNativeCone A K F, strictBETotUniverseNativeCone_vertexMap A K F⟩ =
        strictBETotUniverseNativeConePoint A K F
```

#### StrictDiagramTotUniverseIndex（44行）

```lean
def strictBETotOpOpNerveIso (K : Type u) [SmallCategory K] : nerve Kᵒᵖᵒᵖ ≅ nerve K

def strictBETotUniverseIndexIso (K : Type u) [SmallCategory K] :
    nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ) ≅ (SSet.uliftFunctor.{u+1,u}).obj (nerve K)

theorem strictBETotUniverseSourceDiagram_index (A : Type u) [CommRing A]
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    strictBETotUniverseSourceDiagram A (AsSmall.{u} SimplexCategory) F =
      (strictBETotUniverseIndexIso (AsSmall.{u} SimplexCategory)).hom ≫
        strictBECosimplicialDiagram A F
```

#### StrictDiagramTotNativeConeAt（55行）

```lean
def strictBETotNativeConeAt (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    JoinCone (strictBECosimplicialDiagram A F)

theorem strictBETotNativeConeAt_vertexMap
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotNativeConeAt A F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F)))

theorem strictBETotNativeConeAt_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex = (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))
```

## 178. 指定分類変換を回収する全切断の三角形（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の全錐族・標準脚・極限性は未完了。

R03bの型は保ち、証明に用いる共通の復元への写像を明示した。従来の `smallLeftUnstraighteningComparisonOfFunctorIso` の公開仕様は底上の比較と前合成同値を与える。指定した分類同型の変換そのものを回収して次の評価を追跡するため、既存 `smallUnstraighteningFunctorHom η.hom` による同じ復元への合成を使用した。代表辺の類が元のη.homに等しい既存回収則を明示している。新しいBE模型・strictification・型の変更はない。

`classifiedLeftFibrationSectionsEquivalence_triangle` は、同じ切断比較を標的の復元へ送ると、元の指定ηを使用する復元射による切断と全関手同型で一致することを証明する。元の後合成の同値の余単位を、同じ元の切断写像で前合成したもの。これをBEのBK切断同型とnative錐切断同型を通して運んだ `strictBETotBKNativeSections_reconstruction` も証明した。零単体・π₀の一致だけで代用していない。

三本166行追加、R03b本体は67→62行。累計82本・5,205行。全て既存構成の回収・余単位・合成の法則と、R03bの証明分割で、追加の一覧項目は0。200行超の新規ファイルなし。main・⑤a・既存FramedLimit*・CAlgUnderlyingDerivedComparison・入口・公式監査は変更していない。修正したR03bはこの枝で追加した未取り込みの宣言であり、型は§175のまま。

検証：依存一本の対象ビルド241は2,561 jobsで終了0。242は新規共通二本と直接importerの指定native錐を再ビルドして10,648 jobs・終了0、小監査81本548宣言。243はBEの回収三角形一本を対象ビルドして10,645 jobs・終了0、小監査82本568宣言。全て標準三公理のみ、sorry・独自公理0。実ハンドル93037・5489・31459の終了0を確認し、鍵は返却済み。既存の回収APIの未ビルド依存で止まった個別検査は成功に数えず、241の後に個別検査と対象ビルドを通した。計算上限は変更していない。

次は元の切断のfiber評価と後合成の厳密な自然性を使い、同じ共通の復元のfiberでこの全三角形を評価する。まだ標準脚そのものとの一致や全図式射の錐族を得たとは数えない。

### 178.1 今回の法則・証明分割の型

#### ClassifiedFibrationTransport（49行）

```lean
def classifiedFibrationTransport :
    E ⟶ smallLeftUnstraightening (leftStraighteningInfinityDiagram q)

theorem classifiedFibrationTransport_projection :
    classifiedFibrationTransport p q η ≫
      smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q) = p

theorem classifiedFibrationTransport_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (classifiedFibrationTransport p q η)

theorem classifiedFibrationTransport_edge_hom :
    SSet.Truncated.HomotopyCategory.homMk
      (smallUnstraighteningHomEdge η.hom).toTruncated = η.hom
```

#### ClassifiedSectionsTriangle（45行）

```lean
def classifiedLeftFibrationSectionsEquivalence_triangle :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
          (leftStraighteningInfinityReconstruction_projection q))
      (simplicialSectionsMap (classifiedFibrationTransport p q η)
        (classifiedFibrationTransport_projection p q η))
```

#### StrictDiagramTotNativeSectionsRecovery（72行）

```lean
def strictBETotBKNativeSections_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsMap (leftStraighteningInfinityReconstruction q)
              (leftStraighteningInfinityReconstruction_projection q))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsMap (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η))
```

## 179. 同じ全切断比較の各次数のfiberでの評価（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の標準脚・全錐族・極限性は未完了。

元の普遍切断を底の指定頂点で制限し、同じ射影のfiberへ持ち上げる `simplicialSectionsFiberEvaluation` を構成した。充填性を仮定せず、元の底上の後合成とこの評価が厳密に可換であることを示した。既存の普遍評価とfiberへの持ち上げの評価・自然性の法則である。

これにより、§178の同じ全切断三角形は各fiberの間の全単体的写像についても関手同型で可換となる。BEへの適用 `strictBETotBKNativeSections_fiber_reconstruction` では、元のBK係数・同じ元の図式・同じ頂点・同じ分類同型を指定した。元のBK切断の像を、native錐の切断へ送ってから共通の復元のfiberへ送る写像と、同じ元の指定分類変換を使って先に共通の復元へ送る写像を全次数で比較する。π₀・零単体だけの比較で代用していない。

検証：244は二本の対象ビルド3,122 jobs・終了0、小監査84本580宣言。245はBEの一本の対象ビルド10,647 jobs・終了0、小監査85本599宣言。いずれも標準三公理のみ、実ハンドル15467・13905の終了0を確認し鍵は返却済み。個別検査で標準単体記法と結合済みの自然性を明示した後に対象ビルドを行った。sorry・独自公理0、計算上限の変更なし。

今回三本177行、累計85本・5,382行。全て既存の評価・後合成・余単位の法則で、追加の一覧項目は0。各200行以下。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。これは標準脚そのものや全図式射のnative錐族・極限性の完了ではない。

### 179.1 次の元の係数での照合

weighted nerveのfiber同型で元の係数H.obj iへ戻し、同じBK重みの恒等射の零単体での評価と合わせる。次は元の構成の評価・単位則として以下を検査する（見込み100〜250行）。まだ証明・検証済みとは数えない。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (I : Type u) [SmallCategory I] (H : I ⥤ SSet.{u})

-- namespace SerrePositivity.EInfinity.HomotopyWeight
-- 元の指定sの零単体を、元の同じ係数へ厳密に戻す。
theorem bousfieldKanSectionsIso_nativeWeightedPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
        (Opposite.op ⦋0⦌)
        (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
          (nativeWeightedPoint I s))) =
      (s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))
```

その後、BEの同じEx∞係数単位と指定BK重み比較へ特殊化し、元の標準脚への正規化を追う。ここでも、R03bの切断同値の逆の選択だけから全図式射の厳密な自然性が自動で出るとは主張しない。

### 179.2 今回の法則の型

#### SectionFiberEvaluation（48行）

```lean
def simplicialSectionsFiberEvaluation (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSections p ⟶ vertexFiber p b

@[reassoc] theorem simplicialSectionsFiberEvaluation_ι (p : E ⟶ B) (b : B _⦋0⦌) :
    simplicialSectionsFiberEvaluation p b ≫ vertexFiberι p b =
      lift (SSet.const b) (𝟙 (simplicialSections p)) ≫ simplicialSectionsEvaluation p

theorem simplicialSectionsFiberEvaluation_naturality
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    simplicialSectionsMap f hf ≫ simplicialSectionsFiberEvaluation q b =
      simplicialSectionsFiberEvaluation p b ≫ vertexFiberMap p q f hf b
```

#### ClassifiedSectionsFiberTriangle（50行）

```lean
def classifiedLeftFibrationSectionsEquivalence_fiber_triangle (b : B _⦋0⦌) :
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b ≫
          vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
            (leftStraighteningInfinityReconstruction_projection q) b)
      (simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b)
```

#### StrictDiagramTotNativeFiberRecovery（79行）

```lean
def strictBETotBKNativeSections_fiber_reconstruction
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra)
    (b : (nerve (AsSmall.{u+1} Kᵒᵖᵒᵖ)) _⦋0⦌) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    let p := weightedNerveProjection H
    let q := coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
    let r := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)
    let η := strictBETotBKNativeClassificationIso A K F Y
    FunctorIso
      (((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv) ≫
            simplicialSectionsFiberEvaluation q b ≫
              vertexFiberMap q r (leftStraighteningInfinityReconstruction q)
                (leftStraighteningInfinityReconstruction_projection q) b)
      ((bousfieldKanSectionsIso H).hom ≫ simplicialSectionsFiberEvaluation p b ≫
        vertexFiberMap p r (classifiedFibrationTransport p q η)
          (classifiedFibrationTransport_projection p q η) b)
```

## 180. 元のBK指定点の係数への厳密な回収と宇宙変更・係数単位（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 15（うち追加 3）。R02/R03の標準脚・全錐族・極限性は未完了。

§179.1の型のまま `bousfieldKanSectionsIso_nativeWeightedPoint_fiber` を証明した。元の指定BK点を切断模型に送り、元の次数のfiberで評価して元の係数へ戻した値は、元の自然変換の恒等射のBK零単体での値に**厳密に等しい**。Kan性・モデル構造の追加なし。

証明は、元のliftとBK切断比較を合成した普遍評価の等式、零次のweighted nerveの初区間の係数計算、元のfiber同型による打ち消しに分割した。不透明なendを展開せず、元の普遍評価・パラメーター自然性・Yonedaの評価・直積の第一射影の法則を使った。

さらに同じAsSmall.down・ULiftで宇宙変更した自然変換と、同じEx∞係数単位を合成した自然変換についても、fiberから回収した値が元の恒等射の値の指定像に等しいことを証明した。BE Totで用いた同じ `strictBETotUniversalBKExInfinityCone` に適用するための一般の係数移送則で、新しい係数・重み・単位を選んでいない。

検証：246は一本の対象ビルド2,606 jobs・終了0、小監査86本602宣言。247は一本の対象ビルド3,376 jobs・終了0、小監査87本605宣言。標準三公理のみ。実ハンドル20536・21339の終了0を確認し、鍵は返却済み。個別検査で零次の係数計算を元の自然変換の型で保持し、AsSmallのup/downを明示してから対象ビルドを通した。sorry・独自公理0、計算上限の変更なし。

二本164行追加、累計87本・5,546行。§179.1の元のfiber回収則は99行で、100〜250行の見込みを1〜151行下回った。宇宙変更と係数単位の評価則は別に65行。全て既存構成の評価・単位・係数移送の法則で、今回の追加の一覧項目は0。200行超の新規ファイルなし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

次は§179の共通の復元のfiberでの全三角形から、元のnative錐のfiberでの比較へ戻す。これはまだ元の標準脚の最終一致・全錐族・極限性の完成ではない。

### 180.1 今回の法則の型

#### BousfieldKanNativeFiberPoint（99行）

```lean
theorem bousfieldKanSectionsMap_lift_evaluation {A : SSet.{u}}
    (η : bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    (nerve I ◁ (weightedSectionsLift η ≫ bousfieldKanSectionsMap H)) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
        weightedNerveSectionFromTransform η

theorem weightedNerveSectionFromTransform_zero_point
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    (weightedNerveSectionFromTransform
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)).app
        (Opposite.op ⦋0⦌) (nerveVertex i, SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) =
    (weightedNerveConstantLift H i).app (Opposite.op ⦋0⦌)
      ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))

theorem bousfieldKanSectionsIso_nativeWeightedPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((weightedNerveFiberIso H i).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i)).app
        (Opposite.op ⦋0⦌)
        (((bousfieldKanSectionsIso H).hom.app (Opposite.op ⦋0⦌))
          (nativeWeightedPoint I s))) =
      (s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))
```

#### BousfieldKanUniverseCoefficientPoint（65行）

```lean
theorem bousfieldKanUniverseCone_identityVertex (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((bousfieldKanUniverseCone.{u,v} I s).app (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
      (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
        ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))

theorem bousfieldKanUniverseExInfinityCone_identityVertex
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((bousfieldKanUniverseCone.{u,v} I s ≫ bousfieldKanExInfinityCoefficientUnit _ _).app
      (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
        (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))

theorem bousfieldKanUniverseExInfinityPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    let H' := (weightedDiagramUniverse.{u,v} I).obj H ⋙ exInfinity
    let s' := bousfieldKanUniverseCone.{u,v} I s ≫ bousfieldKanExInfinityCoefficientUnit _ _
    ((weightedNerveFiberIso H' (AsSmall.up.obj i)).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H')
        (nerveVertex (AsSmall.up.obj i))).app (Opposite.op ⦋0⦌)
          (((bousfieldKanSectionsIso H').hom.app (Opposite.op ⦋0⦌))
            (nativeWeightedPoint (AsSmall.{v} I) s'))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))
```

## 181. 元のfiberへ戻す全切断比較 R03c の追加（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 4／全体 16（うち追加 4）。

IS-W2 §19の、同じまとまり・中間定理一つの見込み1,500行以下の枠で、R02〜R03の中間項目 **R03c** を追加する。§179の三角形は共通の復元のfiberを標的とする。元のnative錐のfiberで同じ脚を比較するため、この共通の復元をfiberの同値で消し、元の切断比較の各次数での作用を保つ。

```lean
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial

-- 元の射影の切断・fiberの既存Kan性を局所インスタンスにする。
theorem exists_classifiedFibrationFiberComparison
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (η : FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram q)) (b : B _⦋0⦌) :
    ∃ e : QCatEquivalence (vertexFiber p b) (vertexFiber q b),
      Nonempty (FunctorIso
        ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
          simplicialSectionsFiberEvaluation q b)
        (simplicialSectionsFiberEvaluation p b ≫ e.hom))
```

見込み140〜280行：元の二本の復元のfiber同値の合成40〜80行、§179の全三角形を同じ同値の逆で後合成して余単位で消す40〜80行、BEへの特殊化と同じBK指定点の像の照合60〜120行。既存 `CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence` を使う。fibersが同値であるだけで終わらず、元の全切断比較との同じ四角形を型に含める。新しいBE模型・重み・係数・strictificationや⑤aの欄の型に触れない。

この項目を足してそのまま証明へ進む。全図式射の錐族や極限性を完成とは数えない。見込みが1,500行を超える場合・別のまとまりが必要な場合・外枠15,000行に届く場合は、検証済みを保存して報告する。

## 182. R03c完了：元のnative錐のfiberと元のraw BK係数の指定点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。済みはR01・R03a・R03a.1・R03b・R03c。R02/R03の標準脚・全錐族・極限性は未完了。

§181の型のまま `exists_classifiedFibrationFiberComparison` を証明した。同じ分類変換を使用する共通の復元への二本の実写像を各fiberで同値にし、一方の逆で戻した。元の切断比較の全三角形も同じ逆で後合成し、余単位で消して、元の二つのfiberの同値と**元の全切断比較の同じ四角形**を得た。fiberが同値であるだけで終わらせていない。

BEでは、元のweighted nerveのfiber同型を合成して、元のBK係数から同じ元の図式・頂点のnative錐のfiberへの `strictBETotNativeFiberEquivalence` を得た。全切断比較との四角形、同じ普遍BK指定点の像も照合した。さらに§180の係数移送の評価則を使い、このnative錐のfiberの指定点と、元のraw BK係数の恒等射での値をULift・Ex∞単位で送った指定像との `VertexIso` を得た。

最後の点の比較は `VertexIso` であり、元の二つの零単体が文字どおり等しいと主張していない。一方、§180の係数回収と宇宙変更・単位の値の計算は厳密な等式である。両者を区別する。これを元の標準脚の最終同定や全図式射の錐族、同じ錐の極限性の完了と数えない。

### 182.1 検証と実測

一般形とBEへの適用を合わせて二本224行。§181の140〜280行の見込みの範囲内（下端より84行増、上端より56行減）。個別検査の後、248で二本の対象ビルド10,651 jobs・終了0、小監査89本651宣言・標準三公理のみ。実ハンドル39993の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。累計89本・5,770行、外枠15,000行。各200行以下。

追加の一覧項目は§181のR03cだけで、ここに含まれるfiber同値の合成・余単位の四角形・同じBK点での評価・raw係数への正規化はその証明分割または既存構成の法則。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

### 182.2 次の接続の注意

元のnative錐の脚を、元のraw frame Homと指定BK重み比較の評価へ戻す接続が具体化した。次は既存のframeから正本Homへの単位の正規化と、元の指定weighted普遍錐の評価に合わせる。元の一点重みへの比較とBK比較の可換式だけから、全ての零次の選択が文字どおり同じだとは推論しない。

極限判定のa・haは、既存 `Project.HomotopyDiagramComparison.coherentConeSourceFamily` と `coherentConeSourceFamily_evaluation` が、同じ錐・同じ頂点について候補を与える。CAlgの既存のcoherent nerve表示との照合はこれからであり、ここでは特殊化済みとは数えない。残るheは、この同じ族の制限写像と元のweighted Hom比較の同値性を結ぶこと。固定した始域ごとの全標的のHom比較を、始域にも自然な全比較と自動的に読み替えない。必要な始域の作用・元のframeの単位との両立を既存APIから明示して進める。

### 182.3 今回の型

#### ClassifiedFibrationFiberComparison（80行）

```lean
def classifiedFibrationFiberEquivalence (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b) (vertexFiber q b)

def classifiedFibrationFiberEquivalence_sectionsIso (b : B _⦋0⦌) :
    FunctorIso
      ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
        simplicialSectionsFiberEvaluation q b)
      (simplicialSectionsFiberEvaluation p b ≫ (classifiedFibrationFiberEquivalence p q η b).hom)

theorem exists_classifiedFibrationFiberComparison (b : B _⦋0⦌) :
    ∃ e : QCatEquivalence (vertexFiber p b) (vertexFiber q b),
      Nonempty (FunctorIso
        ((classifiedLeftFibrationSectionsEquivalence p q η).hom ≫
          simplicialSectionsFiberEvaluation q b)
        (simplicialSectionsFiberEvaluation p b ≫ e.hom))
```

#### StrictDiagramTotNativeFiberComparison（144行）

```lean
def strictBETotNativeFiberEquivalence (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    QCatEquivalence ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i)
      (vertexFiber (coherentConeProjection (strictBETotUniverseSourceDiagram A K F)
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) (nerveVertex i))

def strictBETotNativeFiberEquivalence_sectionsIso (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    let H := strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget
    FunctorIso
      ((strictBETotBKNativeSectionsEquivalence A K F Y).hom ≫
        (coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv ≫
            simplicialSectionsFiberEvaluation _ (nerveVertex i))
      ((bousfieldKanSectionsIso H).hom ≫
        simplicialSectionsFiberEvaluation (weightedNerveProjection H) (nerveVertex i) ≫
          (weightedNerveFiberIso H i).inv ≫ (strictBETotNativeFiberEquivalence A K F Y i).hom)

def strictBETotNativeFiberEquivalence_universalPointIso
    (F : K ⥤ (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex i)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((framedLimitFunctor A K).obj F)))).inv.app (Opposite.op ⦋0⦌))
              (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F ((framedLimitFunctor A K).obj F) i).hom.app
        (Opposite.op ⦋0⦌)) (((strictBETotUniversalBKExInfinityCone A K F).app i).app
          (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))

def strictBETotNativeFiberEquivalence_rawPointIso
    (F : K ⥤ (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    let Y := (framedLimitFunctor A K).obj F
    let j : AsSmall.{u+1} Kᵒᵖᵒᵖ := AsSmall.up.obj i
    VertexIso
      ((simplicialSectionsFiberEvaluation _ (nerveVertex j)).app (Opposite.op ⦋0⦌)
        (((coherentConeSectionsIso (strictBETotUniverseSourceDiagram A K F)
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))).inv.app
            (Opposite.op ⦋0⦌)) (strictBETotUniverseNativeConePoint A K F)))
      (((strictBETotNativeFiberEquivalence A K F Y j).hom.app (Opposite.op ⦋0⦌))
        ((exInfinityUnit.app ((SSet.uliftFunctor.{u+1,u}).obj
          ((strictBETotProbeRightHomDiagram A K F Y).obj i))).app (Opposite.op ⦋0⦌)
            (ULift.up (((strictBETotUniversalBKRightHomCone A K F).app i).app
              (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))))))
```


## 183. 元の同じnative錐の始域族aと頂点評価ha（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R03のhe・極限性、R02の全錐族は未完了。

既存のCAlgの頂点全単射で、元の同じnative錐の頂点を表示する対象を指定し、その頂点の厳密な等式を証明した。この対象と同じ元の錐に、既存 `coherentConeSourceFamily` と `coherentConeSourceFamily_evaluation` を代入して、全始域Homの族aと標準coslice fiber比較に一致する頂点評価haを接続した。

`strictBETotNativeConeAt_isLimit_of_sourceRestriction` は**残りのheを仮定した既存判定の特殊化**であり、R03の無条件の極限性を証明したとは数えない。同じ族の制限写像と、元のweighted Homの同値を比較してheを閉じる仕事が残る。既存のCAlgSimplicialCategory・cAlgVertexEquivだけを使い、新しいCAlg模型や代表の選択を作っていない。

検証：249で新規一本の対象ビルド10,662 jobs・終了0、小監査90本659宣言、標準三公理のみ。実ハンドル45305の終了0を確認、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

新規一本75行、累計90本・5,845行。既存の始域族と判定の特殊化・証明分割で、一覧への追加は0。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

文書の補正：型の抽出で `let H := ...` の代入を宣言本体の始まりと誤認し、一部の再掲が `let H` の途中で切れていた。§177.3・§178.1・§179.2・§180.1・§182.3を現行のソースの完全な型から再掲し直した。これらの再掲のファイル行数は現行版の値で、各節本文の当時の検証・実測とは区別する。数学的な型やこれまでの監査結果は変更していない。

次は元のright frame Homの始域作用を全関手として明示し、元のprobeつき係数の同型の始域自然性を照合する。固定始域ごとの全標的比較を、始域にも自然と仮定してheを閉じない。

### 183.1 今回の既存構成の特殊化の型

```lean
def strictBETotNativeConeSourceObject
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) : CAlgSimplicialCategory A

theorem strictBETotNativeConeSourceObject_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex =
      coherentNerveVertex (strictBETotNativeConeSourceObject A F)

def strictBETotNativeConeSourceFamily
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    (SSet.uliftFunctor.{u+1,u+1}).obj
      (SimplicialCategory.sHom X (strictBETotNativeConeSourceObject A F)).op ⟶
        coherentConeSectionSpace (strictBETotNativeConeAt A F).val (coherentNerveVertex X)

theorem strictBETotNativeConeSourceFamily_evaluation
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) (X : CAlgSimplicialCategory A) :
    strictBETotNativeConeSourceFamily A F X ≫
      coherentConeApexEvaluation (strictBETotNativeConeAt A F) (strictBETotNativeConeSourceObject A F)
        (strictBETotNativeConeSourceObject_vertex A F) X =
      coherentCosliceFiberComparison X (strictBETotNativeConeSourceObject A F)

theorem strictBETotNativeConeAt_isLimit_of_sourceRestriction
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra)
    (he : ∀ X : CAlgSimplicialCategory A,
      IsSimplicialHomotopyEquivalence (strictBETotNativeConeSourceFamily A F X ≫
        coneSectionRestriction (strictBETotNativeConeAt A F) (coherentNerveVertex X))) :
    IsLimitCone (strictBETotNativeConeAt A F)
```

## 184. 元のright frame Homの全始域作用と普遍BK錐の射での正規化（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R03のhe・無条件の極限性、R02の全錐族は未完了。

既存のcoyonedaを同じright frame図式へwhiskeringすることで、`rightFrameHomBifunctor` を二変数の全関手としてまとめた。固定始域での値は元のrightFrameHomそのもの。始域の作用は既存 `MixedFrame.rightSourceMap` の前合成そのものであり、元のrightFrameHomUnitもこの始域の作用について厳密に自然である。

BEでは既存probe関手を前合成し、元のraw Hom係数とweighted Hom係数を全始域で束ねた。元の `strictBETotProbeCoefficientsIso` は全始域の自然同型としても両立する。元のprobe・frame・係数・射を変更していない。

さらに元の射 f : Y → Tot(F) による同じ普遍BK錐の始域作用を、元のweighted Hom同値の同じ射 `framedLimitProbeComparison A Y ≫ f` の像へ正規化した。`strictBETotBKProbeArrowCone_comparison` は元の重み・添字図式間の**自然変換の厳密な等式**。係数同型の始域自然性、既存weightedCotensorHomEquiv_precomp、既存probe比較自然変換の自然性を合成した。新しい数学の項目ではなく、既存構成の係数移送・単位・前合成の法則である。

### 184.1 検証と実測

250：再利用する既存MixedFrameSource一本の依存ビルド1,723 jobs・終了0。251：新規二本と既存FramedLimitComparisonの依存を対象ビルドして5,113 jobs・終了0、小監査92本673宣言。252：普遍BK錐の始域正規化一本を対象ビルドして5,114 jobs・終了0、小監査93本678宣言。全て標準三公理のみ、実ハンドル43038・47206・83040の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

新規三本178行、累計93本・6,023行（外枠15,000）。各200行以下。既存構成の全係数の表示と自然性・単位則なので、追加の一覧項目は0。既存FramedLimit*はimportで使うだけで変更していない。CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainも変更していない。

個別検査では未ビルドの既存API依存を250・251でビルドし、probe自然変換の成分を一般の対象で先に照合した。計算対象の不透明なendを展開して計算上限を上げる方法は取っていない。

### 184.2 まだ必要なcoherentな接続

ここで示したのは元の通常圏の**全始域関手と厳密な自然変換の法則**であり、固定始域ごとの全Hom∞比較を始域にも自然とした結果ではない。nativeな標準族aの制限と元のweighted Hom同値を結ぶheには、同じ単位で正規化された両変数の比較か、それと同等な全パラメーターの評価則が必要である。

次の紙の確認では、今回の二変数raw Hom関手を同じAsSmall・ULift・Ex∞でKan図式にした全coherent入力と、同じCAlg源の二変数 `twistedArrowHomInfinity` の入力を同じ底で揃える。固定始域の制限が既存 `strictBETotProbeFrameHomInfinityIso` とどう一致するかも型に含めて検討する。点ごとのHom同値やπ₀の自然性だけで、全joint比較やheを閉じたと主張しない。新しい中間定理が要ると分かった段階で、§19に従い実際の型と1,500行以内かどうかの見込みを記録する。

### 184.3 今回の既存構成の法則の型

#### RightFrameHomBifunctor（56行）

```lean
def rightFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightFrameHomBifunctor_obj (X : C) :
    (rightFrameHomBifunctor r).obj (Opposite.op X) = rightFrameHom r X

theorem rightFrameHomBifunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightFrameHomBifunctor r).map f.op =
      Functor.whiskerLeft (rightFrameDiagram r) (MixedFrame.rightSourceMap f)

def ordinaryHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightFrameHomUnit_source {X Y : C} (f : X ⟶ Y) :
    ordinaryHomBifunctor.map f.op ≫ rightFrameHomUnit r X =
      rightFrameHomUnit r Y ≫ (rightFrameHomBifunctor r).map f.op
```

#### StrictDiagramTotProbeSourceFunctor（60行）

```lean
def strictBETotProbeRightHomBifunctor :
    (operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u}

def strictBETotProbeRightHomSourceFunctor (F : K ⥤ (operad A).Algebra) :
    (operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u}

theorem strictBETotProbeRightHomSourceFunctor_obj (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    (strictBETotProbeRightHomSourceFunctor A K F).obj (Opposite.op Y) =
      strictBETotProbeRightHomDiagram A K F Y

def strictBETotProbeCoefficientsSourceFunctor (F : K ⥤ (operad A).Algebra) :
    (operad A).Algebraᵒᵖ ⥤ Kᵒᵖᵒᵖ ⥤ SSet.{u}

def strictBETotProbeCoefficientsSourceIso (F : K ⥤ (operad A).Algebra) :
    strictBETotProbeRightHomSourceFunctor A K F ≅ strictBETotProbeCoefficientsSourceFunctor A K F
```

#### StrictDiagramTotUniversalSourceNaturality（62行）

```lean
def strictBETotBKProbeArrowCone (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      Kᵒᵖᵒᵖ ⟶ strictBETotProbeRightHomDiagram A K F Y

theorem strictBETotBKProbeArrowCone_comparison (F : K ⥤ (operad A).Algebra)
    {Y : (operad A).Algebra} (f : Y ⟶ (framedLimitFunctor A K).obj F) :
    strictBETotBKProbeArrowCone A K F f ≫ (strictBETotProbeCoefficientsIso A K F Y).hom =
      HomotopyWeight.bkFramedWeightComparison K ≫
        weightedCotensorHomEquiv A K F (HomotopyWeight.weight K) (framedLimitProbe A Y)
          (framedLimitProbeComparison A Y ≫ f)
```

## 185. 両変数の入力と固定始域の制限の厳密な照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R02の全錐族・標準脚の最終正規化、R03の無条件の極限性は未完了。

元のprobeつきright frame Homの二変数関手をuncurryし、同じAsSmall・ULift・Ex∞による全Kan図式とcoherentな入力を作った。正本側は同じCAlg源の両射影をtwistedArrowHomInfinityの底へ送る。始域の反変性には、同じnerveOppositeIsoの逆を使う。

両入力の始域を固定すると、それぞれ既存の第零frame比較の入力と同じ共変Hom∞に**全単体で厳密に等しい**。反転同型の逆と定値写像の可換則を一般の小圏で証明し、これを使って正本側を照合した。これは既存構成の係数移送・前合成則で、一覧への新規定理の追加は0。二入力を結ぶ全FunctorIsoはまだ証明していない。固定始域ごとの比較をそのまま両変数の比較と見なさない。

### 185.1 検証と実測

253：JointHomInput一本の対象ビルド10,624 jobs・終了0、小監査94本693宣言。254：NerveOppositeConstantとJointHomRestriction二本の対象ビルド10,626 jobs・終了0、小監査96本698宣言。全て標準三公理のみ。実ハンドル91462・76154の終了0を確認し、鍵は返却済み。sorry・独自公理0、計算上限の変更なし。

今回三本の行数は下の型一覧に記載。累計96本・6,170行（外枠15,000）。登録予定一覧を更新した。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 185.2 残る接続の位置

同じ普遍単位で正規化されたjoint比較、または同等の全パラメーター評価則がheへの残る接続である。今回の制限等式は、その比較を構成するときに既存の固定始域比較との両立を明記するための型の照合である。既存の豊穣Yoneda比較とframe比較のどこで始域のcoherenceを作るかを先に確認する。

### 185.3 既存構成の法則と入力の型

#### StrictDiagramTotJointHomInput（119行）

```lean
abbrev strictBETotJointHomIndex

def strictBETotJointRawHom :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u}

def strictBETotJointRawHomKan : strictBETotJointHomIndex A ⥤ KanObject.{u+1}

def strictBETotJointRawHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointHomSourceIndex :
    strictBETotJointHomIndex A ⥤ (AsSmall.{u+1} (operad A).Algebra)ᵒᵖ

def strictBETotJointHomTargetIndex :
    strictBETotJointHomIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointNativeHomInput :
    nerve (strictBETotJointHomIndex A) ⟶ (CAlg_R A).op ⊗ CAlg_R A

def strictBETotJointNativeHomCoherent :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointHomFixSource (X : (operad A).Algebra) :
    AsSmall.{u+1} (operad A).Algebra ⥤ strictBETotJointHomIndex A

theorem strictBETotJointRawHom_fixSource (X : (operad A).Algebra) :
    CategoryTheory.Prod.sectR (Opposite.op X) (operad A).Algebra ⋙ strictBETotJointRawHom A =
      rightFrameHom (rightFrameFamily A) (framedLimitProbe A X)

theorem strictBETotJointRawHomKan_fixSource (X : (operad A).Algebra) :
    strictBETotJointHomFixSource A X ⋙ strictBETotJointRawHomKan A =
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C

theorem strictBETotJointRawHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointRawHomCoherent A =
    FrameHom.rightFrameHammockCoherentDiagram
      ((SimplicialLocalization.modelSourceFrameFamily (C

```

#### NerveOppositeConstant（52行）

```lean
theorem nerveOppositeIso_inv_constant (c : C) (n : ℕ) :
    ((nerveOppositeIso (C

theorem nerveOppositeIso_inv_const {K : SSet.{u}} (c : C) :
    SSet.const (X

```

#### StrictDiagramTotJointHomRestriction（76行）

```lean
theorem strictBETotJointNativeHomInput_fixSource (X : (operad A).Algebra) :
    nerveMap (strictBETotJointHomFixSource A X) ≫ strictBETotJointNativeHomInput A =
      lift (SSet.const (SSet.opObjEquiv.symm
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))))
          (strictBETotModelSource A)

theorem strictBETotJointNativeHomCoherent_fixSource (X : (operad A).Algebra) :
    (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotJointHomFixSource A X)) ≫
      strictBETotJointNativeHomCoherent A =
    (SSet.uliftFunctor.{u+2,u+1}).map (strictBETotModelSource A) ≫
      homInfinityCovariant ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))

```

## 186. 最初の三辺の両変数の全関手同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 16（うち追加 4）。R02・R03の未完了部分は§185と同じ。

元の関手的source frame・right frameの混合Homを始域にも反変な全関手として束ねた。左右の混合比較の始域自然性は、同じaugmentationの自然性と圏の結合則そのものである。BEでは同じprobe関手・標的の次数零置換・uncurry・ULiftを使い、六辺のうち最初の三辺を全両変数の自然変換にした。

各辺の弱同値性には既存のrightFrameHammockFamilyEdge_weakを同じ入力で代入した。全自然変換自身をKan化して全関手圏で反転し、`strictBETotJointFirstSpanComparison` を得た。元の両変数raw Homとsource frame Homの**全関手同型**であり、点ごとの同値の選択ではない。ただし終点はsource frame Homであり、正本Hom∞との全同型はまだ含まない。

### 186.1 検証・実測と累計の訂正

255：二本の対象ビルド10,626 jobs・終了0、小監査98本739宣言・標準三公理のみ。実ハンドル13255の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。

今回二本242行（83＋159）、manifestの全ファイルを再集計した累計98本・6,412行（外枠15,000）。§185の三本は247行（119＋52＋76）、その時点の再集計6,170行は正しい。§184の累計6,023行には100行の過大計上があり、正しくは5,923行だった。以後はmanifestから再集計した値を用いる。過去の報告の検証結果と宣言数は変わらない。

今回の二本は既存比較の自然性・係数移送・合成の法則で、一覧の新規定理の追加には数えない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 186.2 既存構成の法則の型

#### RightMixedBifunctor（83行）

```lean
def rightMixedBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

theorem rightMixedBifunctor_obj (X : C) :
    (rightMixedBifunctor q r).obj (Opposite.op X) = rightMixedFamily (q.atObject X) r

def sourceFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v}

def rightMixedLeftBifunctorMap : sourceFrameHomBifunctor q ⟶ rightMixedBifunctor q r

def rightMixedRightBifunctorMap : rightFrameHomBifunctor r ⟶ rightMixedBifunctor q r

theorem rightMixedLeftBifunctorMap_app (X : C) :
    (rightMixedLeftBifunctorMap q r).app (Opposite.op X) =
      rightMixedLeft (q.atObject X) r

theorem rightMixedRightBifunctorMap_app (X : C) :
    (rightMixedRightBifunctorMap q r).app (Opposite.op X) =
      rightMixedRight (q.atObject X) r
```

#### StrictDiagramTotJointFirstSpan（159行）

```lean
def strictBETotJointFirstSpanBifunctor :
    Fin 4 → ((operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u})

def strictBETotJointFirstSpanUnit :
    strictBETotJointFirstSpanBifunctor A 0 ⟶ strictBETotJointFirstSpanBifunctor A 1

def strictBETotJointFirstSpanRight :
    strictBETotJointFirstSpanBifunctor A 1 ⟶ strictBETotJointFirstSpanBifunctor A 2

def strictBETotJointFirstSpanLeft :
    strictBETotJointFirstSpanBifunctor A 3 ⟶ strictBETotJointFirstSpanBifunctor A 2

def strictBETotJointFirstSpanDiagram (i : Fin 4) :
    ((operad A).Algebraᵒᵖ × (operad A).Algebra) ⥤ SSet.{u+1}

def strictBETotJointFirstSpanEdgeSource : Fin 3 → Fin 4

def strictBETotJointFirstSpanEdgeTarget : Fin 3 → Fin 4

def strictBETotJointFirstSpanEdge (i : Fin 3) :
    strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⟶
      strictBETotJointFirstSpanDiagram A (strictBETotJointFirstSpanEdgeTarget i)

theorem strictBETotJointFirstSpanEdge_weak (i : Fin 3)
    (P : (operad A).Algebraᵒᵖ × (operad A).Algebra) :
    IsWeakHomotopyEquivalence ((strictBETotJointFirstSpanEdge A i).app P)

def strictBETotJointFirstSpanKanDiagram (i : Fin 4) :
    strictBETotJointHomIndex A ⥤ KanObject.{u+1}

def strictBETotJointFirstSpanKanEdge (i : Fin 3) :
    strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeSource i) ⋙ kanObjectForget ⟶
      strictBETotJointFirstSpanKanDiagram A (strictBETotJointFirstSpanEdgeTarget i) ⋙ kanObjectForget

def strictBETotJointFirstSpanCoherent (i : Fin 4) :
    (SSet.uliftFunctor.{u+2,u+1}).obj (nerve (strictBETotJointHomIndex A)) ⟶ SpaceInfinity.{u+1}

def strictBETotJointFirstSpanEdgeIso (i : Fin 3) :
    FunctorIso (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeSource i))
      (strictBETotJointFirstSpanCoherent A (strictBETotJointFirstSpanEdgeTarget i))

theorem strictBETotJointFirstSpanCoherent_zero :
    strictBETotJointFirstSpanCoherent A 0 = strictBETotJointRawHomCoherent A

def strictBETotJointFirstSpanComparison :
    FunctorIso (strictBETotJointRawHomCoherent A) (strictBETotJointFirstSpanCoherent A 3)
```

## 187. R03d：同じ固定始域比較で正規化された両変数比較の追加（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未証明。

IS-W2 §19の承認済みの中間定理の枠により、R01〜R03のまとまりにR03dを追加する。型は次のとおり。両変数の同じ入力の全FunctorIsoを要求し、始域を固定した制限は既存の同じ `strictBETotProbeFrameHomInfinityIso` と一致させる。HEqは§185の二つの制限等式による型の移送を記すためのもので、点ごとの同値や可換性への弱化ではない。

```lean
theorem exists_strictBETotJointHomComparison (A : Type u) [CommRing A] :
  ∃ e : FunctorIso (strictBETotJointRawHomCoherent A) (strictBETotJointNativeHomCoherent A),
    ∀ X : (operad A).Algebra,
      HEq (e.precomp ((SSet.uliftFunctor.{u+2,u+1}).map
        (nerveMap (strictBETotJointHomFixSource A X))))
        (strictBETotProbeFrameHomInfinityIso A X)
```

この主張の型を一時ファイル `/private/tmp/CheckStrictBEJointComparisonType.lean` のPropとして検査し、実ハンドル58644の終了0を確認した。定理の証明や本体への登録はまだしていない。

残りの見込みは950〜1,450行：全パラメーターのaugmentationとroofを同じ底上に置く450〜700行、元の豊穣Yoneda・指定局所化比較へ運ぶ300〜450行、同じ固定始域比較との正規化200〜300行。今回の既存法則242行はこの残りに含めない。全体の外枠は15,000行のまま。

短い経路を先に試す。source frameのaugmentationを全始域と全次数の自然変換として同じ局所化へ送り、弱辺を全関手圏で反転する。その同じ逆と元の射から、両端を変数とする一つの表示された比較を作り、分類に送る。固定始域では既存のframe・Yoneda・同じ局所化二胞体に戻ることを照合する。`FrameLeftRoofPrecompose` の各射の局所化内の等式だけを、全高次の自然性の証明として使わない。

まとまり外の定理、1,500行を超える見込み、⑤aの欄の型への変更が必要と分かった場合は、検証済みをコミットして報告する。今回は同じR03のまとまりで上端1,450行なので、承認を待たずR03dの証明へ進む。

## 188. 全始域・全次数の同じaugmentationの一つの逆（R03dの前半、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

同じ関手的source frameのaugmentationを、全始域と全source次数の積添字でuncurryし、元のprobe比較自然変換と合成した。同じCAlgの指定モデル源へ送った全円柱について、全ての成分の辺の可逆性から円柱自身を全関手圏で反転した。逆を対象・次数ごとに選んでいない。

共通部分はKerodon 4.8の `NerveTransformationInversion` に置いた。既存のnerve円柱と既存の指定辺の点ごとの反転判定を合成した、通常の自然変換の係数移送・反転の法則である。BEの各成分の弱同値性は、元の解消のaugmentationと元のprobe比較の合成則から従う。局所化の反転辺の集合と指定された辺の型は、同じ一単体の一致で合わせた。

### 188.1 検証と実測

256：新規二本の対象ビルド10,628 jobs・終了0、小監査100本754宣言・標準三公理のみ。実ハンドル21505の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。今回143行、累計100本・6,555行（外枠15,000）。R03dの残るjoint表示と分類・固定始域との正規化はまだ証明していない。

この二本はR03dの既存の自然変換・反転則であり、新しい一覧項目は増やさない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 188.2 型

#### NerveTransformationInversion（52行）

```lean
def nerveTransformationPostHomotopy : SSet.Homotopy (nerveMap F ≫ L) (nerveMap G ≫ L)

def nerveTransformationPostIso
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    FunctorIso (nerveMap F ≫ L) (nerveMap G ≫ L)

theorem nerveTransformationPostIso_hom
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (nerveTransformationPostHomotopy η L))

```

#### StrictDiagramTotJointAugmentation（91行）

```lean
abbrev strictBETotJointSourceFrameIndex

def strictBETotJointSourceFrameEvaluation :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointSourceFrameConstant :
    strictBETotJointSourceFrameIndex A ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotJointSourceFrameAugmentation :
    strictBETotJointSourceFrameEvaluation A ⟶ strictBETotJointSourceFrameConstant A

theorem strictBETotJointSourceFrameAugmentation_weak (P : strictBETotJointSourceFrameIndex A) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotJointSourceFrameAugmentation A).app P))

theorem strictBETotJointSourceFrameAugmentation_inverted (P : strictBETotJointSourceFrameIndex A) :
    IsInvertibleEdge ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app P)).map
      (strictBETotModelSource A)).toTruncated

def strictBETotJointSourceFrameAugmentationIso :
    FunctorIso (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫ strictBETotModelSource A)
      (nerveMap (strictBETotJointSourceFrameConstant A) ≫ strictBETotModelSource A)

```

## 189. 元の全source frame射の要素圏と両端の四角形（R03d、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

既存のresolutionHomを二度uncurryし、全始域・全標的・全単体次数のHom係数の要素圏を取った。元の各射の始域を反変な関手、標的を共変な関手として記録した。要素圏の全射について、同じ実際の射が与える可換四角形を証明した。始域のframeの自然性と元の要素圏のmap_valの合成であり、新しい比較射やframeは選んでいない。

257：新規一本の対象ビルド1,126 jobs・終了0、小監査101本761宣言・標準三公理のみ。実ハンドル35588の終了0を確認し、鍵を返却済み。sorry・独自公理0、計算上限変更なし。今回65行、累計101本・6,620行（外枠15,000）。R03dに関係する§188以降の検証済みは208行。

この要素圏は元の係数の表示と自然性の法則なので、新しい一覧項目には数えない。R03dの残りは、同じ全要素圏と同じaugmentationの大域的な逆から正本Hom∞への比較を作り、分類と固定始域の既存比較との一致を示すこと。始域が反変なので、今回の四角形を通常の二つの共変関手の自然変換として扱わない。点ごとのroofのホモトピーだけで全高次自然性を済ませることもしない。

次は同じ両端を持つ全要素の射をtwisted arrowへ送る全写像を組み立てる。厳密なtwisted arrowの同型全体を新たに作る必要があるとはまだ判断していない。まず既存のedgewise重みの標準単体表示と元の可換四角形で必要な写像を作る短い経路を試す。R03dの型と§187の見込みの範囲で進め、追加の中間定理が必要な場合は§19の枠に従って型と見込みを記録する。

既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 189.1 既存構成の表示・自然性の型（65行）

```lean
def sourceFrameArrowCoefficients :
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ) ⥤ Type v

abbrev SourceFrameArrowElements

def sourceFrameArrowParameters : SourceFrameArrowElements Q R ⥤
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ)

def sourceFrameArrowDomain : SourceFrameArrowElements Q R ⥤ Cᵒᵖ

def sourceFrameArrowCodomain : SourceFrameArrowElements Q R ⥤ C

def sourceFrameArrowValue (s : SourceFrameArrowElements Q R) :
    ((sourceFrameArrowDomain Q R).obj s).unop ⟶ (sourceFrameArrowCodomain Q R).obj s

theorem sourceFrameArrowValue_naturality {s t : SourceFrameArrowElements Q R} (f : s ⟶ t) :
    ((sourceFrameArrowDomain Q R).map f).unop ≫ sourceFrameArrowValue Q R s ≫
      (sourceFrameArrowCodomain Q R).map f = sourceFrameArrowValue Q R t

```

## 190. 指定された射列の長い単体と交差射の全自然性（R03d、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03dは未完了。

全要素圏の反変・共変の両端と元の射から、同じ「始域の逆順・零番の射・標的の順序」の長い通常nerveの単体を作った。恒等射と合成を元の両端の関手と圏の合成則で確認した。左右の型の移送はeqToHomによる同じ共役として明示し、元の射を保持する異種等式も証明した。新しい充填・逆・頂点ごとの同値は選んでいない。

元の可換四角形を仮定すると、対角の交差射は元の射であり、基点を零番以外へ移しても同じ交差射になる。この等式から交差射の任意の順序射による再添字付けの厳密な自然性を得た。面・退化の両方を含む。両半分の対象の座標も元の同じedgewiseの座標で照合した。

258：三本の対象ビルド1,556 jobs・終了0、小監査104本808宣言・標準三公理のみ。実ハンドル36320の終了0を確認し、鍵返却済み。sorry・独自公理0、計算上限変更なし。今回294行（151＋50＋93）、累計104本・6,914行（外枠15,000）。R03dの§188以降の検証済みは502行。既存構成の合成・自然性・係数移送則なので一覧項目の追加は0。

射列全体を実際のedgewise重みの再添字付けと照合する `TwistedPairingReindex` は個別検査中で、今回のコミットと検証済みの数には含めない。R03dの全FunctorIso、固定始域の既存比較との一致、he、R03の無条件の極限性はまだ未完了。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 190.1 共通の入力と既存構成の法則の型

以下でI・Cは同じ宇宙の小圏、A : I ⥤ Cᵒᵖ、B : I ⥤ C、h : ∀ i, (A.obj i).unop ⟶ B.obj i。hhは元の可換四角形 `∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j`。σ : Fin (n+1) ⥤ I。CrossNaturalityの三つの補題はhhを明示的な入力に持つ。

#### TwistedPairingSimplex（151行）

```lean
def twistedPairingLeftIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) : Fin (n+1)

def twistedPairingRightIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) : Fin (n+1)

def twistedPairingCross (a b : Fin (n+1)) :
    (A.obj (σ.obj a)).unop ⟶ B.obj (σ.obj b)

theorem twistedPairingCross_left (a b c : Fin (n+1)) (hab : b ≤ a) :
    (A.map (σ.map (homOfLE hab))).unop ≫ twistedPairingCross A B h σ b c =
      twistedPairingCross A B h σ a c

theorem twistedPairingCross_right (a b c : Fin (n+1)) (hbc : b ≤ c) :
    twistedPairingCross A B h σ a b ≫ B.map (σ.map (homOfLE hbc)) =
      twistedPairingCross A B h σ a c

def twistedPairingSimplexObj (i : Fin (n+n+1+1)) : C

theorem twistedPairingSimplexObj_left (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    twistedPairingSimplexObj A B σ i = (A.obj (σ.obj (twistedPairingLeftIndex i hi))).unop

theorem twistedPairingSimplexObj_right (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    twistedPairingSimplexObj A B σ i = B.obj (σ.obj (twistedPairingRightIndex i hi))

theorem twistedPairingTransport_comp {X Y Z U V W : C} (p : X = U) (q : Y = V) (r : Z = W)
    {f : U ⟶ V} {g : V ⟶ W} {k : U ⟶ W} (hk : k = f ≫ g) :
    eqToHom p ≫ k ≫ eqToHom r.symm =
      (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm)

theorem twistedPairingTransport_heq {X Y U V : C} (p : X = U) (q : Y = V) (f : U ⟶ V) :
    HEq (eqToHom p ≫ f ≫ eqToHom q.symm) f

def twistedPairingSimplexMap (i j : Fin (n+n+1+1)) (hij : i ≤ j) :
    twistedPairingSimplexObj A B σ i ⟶ twistedPairingSimplexObj A B σ j

theorem twistedPairingSimplexMap_id (i : Fin (n+n+1+1)) :
    twistedPairingSimplexMap A B h σ i i le_rfl = 𝟙 _

theorem twistedPairingSimplexMap_comp (i j k : Fin (n+n+1+1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    twistedPairingSimplexMap A B h σ i k (hij.trans hjk) =
      twistedPairingSimplexMap A B h σ i j hij ≫ twistedPairingSimplexMap A B h σ j k hjk

def twistedPairingSimplex : Fin (n+n+1+1) ⥤ C
```

#### TwistedPairingCrossNaturality（50行）

```lean
theorem twistedPairingCross_diagonal (i : Fin (n+1)) :
    twistedPairingCross A B h σ i i = h (σ.obj i)

theorem twistedPairingCross_changeBase (p a b : Fin (n+1)) (hpa : p ≤ a) (hpb : p ≤ b) :
    twistedPairingCross A B h σ a b =
      (A.map (σ.map (homOfLE hpa))).unop ≫ h (σ.obj p) ≫ B.map (σ.map (homOfLE hpb))

theorem twistedPairingCross_reindex {m : ℕ} (α : Fin (m+1) →o Fin (n+1))
    (a b : Fin (m+1)) :
    twistedPairingCross A B h (α.monotone.functor ⋙ σ) a b =
      twistedPairingCross A B h σ (α a) (α b)
```

#### TwistedPairingCoordinates（93行）

```lean
theorem twistedPairingLeftVertex_lt (n : ℕ) (i : Fin (n+1)) :
    (edgewiseLeftVertex n i).val < n+1

theorem twistedPairingRightVertex_not_lt (n : ℕ) (i : Fin (n+1)) :
    ¬ (edgewiseRightVertex n i).val < n+1

theorem twistedPairingLeftIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : (edgewiseLeftVertex n i).val < n+1) :
    twistedPairingLeftIndex (edgewiseLeftVertex n i) hi = i

theorem twistedPairingRightIndex_vertex (n : ℕ) (i : Fin (n+1))
    (hi : ¬ (edgewiseRightVertex n i).val < n+1) :
    twistedPairingRightIndex (edgewiseRightVertex n i) hi = i

theorem twistedPairingSimplex_obj_left (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseLeftVertex n i) = (A.obj (σ.obj i)).unop

theorem twistedPairingSimplex_obj_right (i : Fin (n+1)) :
    (twistedPairingSimplex A B h σ).obj (edgewiseRightVertex n i) = B.obj (σ.obj i)

theorem twistedPairingSimplexMap_left_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (A.map (σ.map (homOfLE (show twistedPairingLeftIndex j hj ≤ twistedPairingLeftIndex i hi
        by dsimp [twistedPairingLeftIndex]; exact Nat.sub_le_sub_left hij _)))).unop

theorem twistedPairingSimplexMap_cross_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (twistedPairingCross A B h σ (twistedPairingLeftIndex i hi) (twistedPairingRightIndex j hj))

theorem twistedPairingSimplexMap_right_heq (i j : Fin (n+n+1+1)) (hij : i ≤ j)
    (hi : ¬ i.val < n+1) (hj : ¬ j.val < n+1) :
    HEq (twistedPairingSimplexMap A B h σ i j hij)
      (B.map (σ.map (homOfLE (show twistedPairingRightIndex i hi ≤ twistedPairingRightIndex j hj
        by dsimp [twistedPairingRightIndex]; exact Nat.sub_le_sub_right hij _))))
```

## 191. 同じtwisted arrowへの全写像と二射影、R03dの半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 17（うち追加 5）。R03d・R02・R03は未完了。

### 191.1 今回の検証済み

元の長い射列が実際のedgewise重みの全順序射と厳密に両立することを証明し、`twistedPairingNerveMap` として一つの全単体写像にした。元の射の四角形を使うのは交差射の基点変更・再添字付けであり、面・退化をすべて含む。

同じ射列の左右の標準区間への全制限も証明した。右は元の標的の射列、左は元の反変の始域の逆反転そのもの。同じnerve反転同型の逆の一般の評価則を合わせ、全写像の右射影がnerveMap B、左射影がnerveMap Aと同じnerveOppositeIso.invの合成であることを、**全写像の厳密な等式**として得た。元の両端の指定底を保つ `twistedPairingNerveMap_projection` が今回の終点。正本Hom∞への全FunctorIsoではまだない。

259：TwistedPairingReindex・TwistedPairingNerve二本、対象ビルド1,559 jobs・終了0、小監査106本821宣言・標準三公理のみ。260：NerveOppositeEvaluation・TwistedPairingRestrictions・TwistedPairingProjections三本、対象ビルド1,572 jobs・終了0、小監査109本829宣言・標準三公理のみ。実ハンドル27277・63636の終了0を確認し、鍵を返却した。sorry・独自公理0、計算上限変更なし。

今回五本375行（159＋48＋32＋69＋67）、累計109本・7,289行（外枠15,000）。R03dの§188以降の検証済みは877行で、§187の見込み950〜1,450行の半分を越えた。既存構成の係数移送・自然性の法則とR03dの証明の分割であり、追加の一覧項目は0。全五本200行以下。

### 191.2 残りの見込みと、先に紙で確認する接続

残りは、全要素圏上で作った同じ射を、全パラメーターを保ってKan係数の分類へ運び、元の固定始域の比較へ正規化すること。次の三点をソースで確認した。

1. `leftStraighteningInfinityDiagram p` は `[LeftFibration p]` を要求する。全source frame Homの要素圏の射影にはこの仮定はないので、そのまま分類に代入できない。
2. `sourceFrameElementsFamily` の元のaugmentationは `nerve (Elementsᵒᵖ)` からHomへ向かう。今回の全要素圏のfiberは `Elements` である。この反対の違いを同一視してaugmentationを使えない。Kan化・反転との全自然性を含む比較が必要。
3. `weightedNerve F` は初区間の重み付き係数の族を持つ。全要素圏のnerveと定義上同じものではない。既存の `Thomason.map_isWeakHomotopyEquivalence` は全空間の弱同値であり、それだけでは同じ底上の全分類比較や指定点の正規化を証明しない。

型の移送・BEへの適用・元の固定始域比較との正規化の残りは、比較の橋を本体の定理として参照できれば350〜550行の暫定見込み。一方、上の1〜3を結ぶ数学的な橋には別に700〜1,100行程度を見込むが、まだ同じ底上の必要な型を確定していない。橋も含めた同じ一まとまりの合計見込みは1,927〜2,527行となり、§187の950〜1,450行は小さかった。

したがって、この線の新しいLeanはここでいったん増やさず、必要な橋の主張を紙で型にする。同じR03のまとまりの**独立した中間定理**として切り出すのが数学的に妥当で、その一つの見込みが1,500行以下なら、IS-W2 §19に従い型と見込みを一覧の追加として記録して進める。単に行数を分けるための補題の分割では、この規則を回避しない。1,500行を超える型、まとまりの外、⑤aの欄の型に関わるものが必要と分かった場合は、検証済みのこのコミットを取り込み点にして型と理由を報告する。

この確認でG10へ戻ったり、R03dの型を点ごとのHom同値・π₀の自然性へ弱めたりしない。無条件のnative極限性を得たとは主張しない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 191.3 今回の型

共通の入力は§190.1のI・C・A・B・h・hh・σ。再添字付けの入力αはSimplexCategory.mk m ⟶ SimplexCategory.mk n。

#### TwistedPairingReindex（159行）

```lean
theorem twistedPairingLeftVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    edgewiseLeftVertex n (twistedPairingLeftIndex i hi) = i

theorem twistedPairingRightVertex_index {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    edgewiseRightVertex n (twistedPairingRightIndex i hi) = i

theorem twistedPairingReindex_left (i : Fin (m+m+1+1)) (hi : i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseLeftVertex n (α.toOrderHom (twistedPairingLeftIndex i hi))

theorem twistedPairingReindex_right (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1) :
    edgewiseWeightReindexOrderHom.{u} α i =
      edgewiseRightVertex n (α.toOrderHom (twistedPairingRightIndex i hi))

theorem twistedPairingReindex_leftIndex (i : Fin (m+m+1+1)) (hi : i.val < m+1)
    (hbi : (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingLeftIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingLeftIndex i hi)

theorem twistedPairingReindex_rightIndex (i : Fin (m+m+1+1)) (hi : ¬ i.val < m+1)
    (hbi : ¬ (edgewiseWeightReindexOrderHom.{u} α i).val < n+1) :
    twistedPairingRightIndex (edgewiseWeightReindexOrderHom.{u} α i) hbi =
      α.toOrderHom (twistedPairingRightIndex i hi)

theorem twistedPairingThinMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ D) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f) (F.map g)

theorem twistedPairingThinUnopMap_heq {D : Type u} [Category.{u} D] {N : ℕ}
    (F : Fin N ⥤ Dᵒᵖ) {a b c d : Fin N} (ha : a = c) (hb : b = d)
    {f : a ⟶ b} {g : c ⟶ d} : HEq (F.map f).unop (F.map g).unop

theorem twistedPairingCross_heq {a b c d : Fin (n+1)} (ha : a = c) (hb : b = d) :
    HEq (twistedPairingCross A B h σ a b) (twistedPairingCross A B h σ c d)

theorem twistedPairingSimplex_reindex :
    (edgewiseWeightReindexOrderHom.{u} α).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      twistedPairingSimplex A B h (α.toOrderHom.monotone.functor ⋙ σ)
```

#### TwistedPairingNerve（48行）

```lean
theorem twistedPairingWeightIso_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.{u}.map α ≫ (edgewiseWeightIso n).hom =
      (edgewiseWeightIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α))

def twistedPairingNerveMap : nerve I ⟶ TwistedArrow (nerve C)
```

#### NerveOppositeEvaluation（32行）

```lean
theorem nerveOppositeIso_inv_apply {n : ℕ} (σ : ComposableArrows Cᵒᵖ n) :
    (nerveOppositeIso (C := C)).inv.app (Opposite.op ⦋n⦌) σ =
      SSet.opObjEquiv.symm (nerveUnreverseChain σ)
```

#### TwistedPairingRestrictions（69行）

```lean
theorem twistedPairingLeftOrder_lt (n : ℕ) (i : Fin (n+1)) :
    (joinLeftOrderHom n n i).val < n+1

theorem twistedPairingLeftIndex_order (n : ℕ) (i : Fin (n+1))
    (hi : (joinLeftOrderHom n n i).val < n+1) :
    twistedPairingLeftIndex (joinLeftOrderHom n n i) hi = i.rev

theorem twistedPairingSimplex_restrict_right :
    (joinRightOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ = σ ⋙ B

theorem twistedPairingSimplex_restrict_left :
    (joinLeftOrderHom n n).monotone.functor ⋙ twistedPairingSimplex A B h σ =
      nerveUnreverseChain (σ ⋙ A)
```

#### TwistedPairingProjections（67行）

```lean
theorem twistedPairingNerveMap_right :
    twistedPairingNerveMap A B h hh ≫ edgewiseRight (nerve C) = nerveMap B

theorem twistedPairingNerveMap_left :
    twistedPairingNerveMap A B h hh ≫ edgewiseLeft (nerve C) =
      nerveMap A ≫ (nerveOppositeIso (C := C)).inv

theorem twistedPairingNerveMap_projection :
    twistedPairingNerveMap A B h hh ≫ twistedArrowProjection (nerve C) =
      lift (nerveMap A ≫ (nerveOppositeIso (C := C)).inv) (nerveMap B)
```

## 192. R03e：通常のGrothendieck構成の厳密なweighted nerve比較（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未証明。

§191.2の橋を紙で分けて確認した。最初に、任意の通常のCat値図式のGrothendieck構成のnerveと、各fiberのnerveからなる図式のweighted nerveとの厳密な同型を、**独立した数学的な中間定理R03e**として追加する。元の底の射影と元のfiberの指定頂点を保つ。IS-W2 §19の同じR01〜R03のまとまりの中の中間定理であり、見込みは500〜900行（1,500行以下）なので、承認を待たず進める。

これはR03dの行数だけを分割するための補題ではない。任意の通常のCat値図式に対する二つの既存の全構成を、底上の厳密な単体集合同型と指定頂点の等式で結ぶ、一つの独立した比較定理。全要素圏の射影を既存のweighted nerveの分類へ接続する最初の段に使う。単なる全空間の弱同値とは区別する。

```lean
theorem exists_grothendieckWeightedNerveIso
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
  ∃ e : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor),
    e.hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F) ∧
    ∀ (i : I) (x : F.obj i),
      e.hom.app (Opposite.op ⦋0⦌) (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x)
```

この型を `/private/tmp/CheckISW2GrothWeightedNerveType.lean` のPropとしてLeanで確認し、実ハンドル74299の終了0を確認した。定理の証明を仮定にしたり本体に未証明で登録したりしていない。

置き場所は `InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckWeightedNerve*.lean`。既存の同名ファイルはない。前向きの単体と自然性150〜250行、逆向きの重み係数からのGrothendieck射列150〜250行、両往復150〜250行、射影・指定点の照合50〜150行、計500〜900行。見込みの半分で実測と残りを報告する。

短い経路として、既存の `SliceTransport/GrothendieckCommaTransport.transport` を再利用する。Grothendieck射列の各初区間を同じ最終基底へのCostructuredArrowに送り、その既存のtransportでfiberへ移す。このprefixのnerveが前向きの重み係数になる。逆は各prefixの最終対象と元の係数の自然性から実射を回収する。元のCat関手の合成の型の移送は、既存のtransportが処理する。

### 192.1 後半にまだ必要な判定

別途、全単体集合値図式Fについて、`Grothendieck (F ⋙ Functor.elementsFunctor)` の同じ底上の射影のcontinuousLeftFibrationReplacementを分類すると、元のFのEx∞のKan図式に全関手同型となる、という候補の型も一時ファイルで確認した。261で既存のContinuousLeftFibrationFilling一本を対象ビルド（1,503 jobs・終了0）してから `/private/tmp/CheckISW2ElementsLeftStraighteningType.lean` を通し、実ハンドル62729の終了0を確認した。この候補はまだ一覧に追加しておらず、証明も存在も主張しない。

R03eだけで後半の相対Kan比較が済むとは扱わない。要素圏の反対と元のaugmentation、同じ底上のKan化、元の指定点の回収を、どの既存の全比較で示すかを別に確認する。必要な独立の中間定理があれば、同じく型と見込みで§19を判定する。R03dの元の全FunctorIsoと固定始域の同じ比較への一致という型は保つ。R03eの証明に進む。

## 193. R03eの前向きprefixと元の最終対象の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

元のGrothendieck射列の各初区間を、同じ最終基底への脚を持つCostructuredArrowの関手へ送った。各射の三角形は元の射列の合成則そのものであり、恒等射・合成も保持する。この関手に既存の `GrothendieckCommaTransport.transport` を後合成してfiberに値を持つprefixを得た。

各対象が元の脚で元のfiber対象を送ったものとなる評価式と、prefixの最終対象が元の同じfiber対象そのものになる厳密な等式を確認した。前向きの指定点の正規化の最初の部分であり、weighted nerveの全係数の自然変換と同型の両往復はまだ作っていない。

262：新規一本の対象ビルド1,168 jobs・終了0、小監査110本840宣言・標準三公理のみ。実ハンドル25109の終了0を確認し、鍵返却済み。sorry・独自公理0、計算上限変更なし。今回65行、累計110本・7,354行（外枠15,000）。R03eは65行／見込み500〜900行であり、まだ半分には達していない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は同じ初区間の包含と既存transport_naturalityを使い、全prefixをsimplexPrefixWeightからの自然変換として束ねる。逆向きはweighted係数の最終対象と元の係数の自然性からGrothendieck射列を回収する。R03dとnative極限性は引き続き未完了。

### 193.1 型（65行）

共通の入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)`。PrefixIndexはF・σを使わない有限添字の包含。

```lean
def grothWeightedPrefixIndex (i : Fin (n+1)) (k : Fin (i.val+1)) : Fin (n+1)

def grothWeightedPrefixArrow (i : Fin (n+1)) :
    Fin (i.val+1) ⥤ CostructuredArrow (Grothendieck.forget F) (σ.obj i).base

def grothWeightedPrefixFiber (i : Fin (n+1)) : Fin (i.val+1) ⥤ F.obj (σ.obj i).base

theorem grothWeightedPrefixFiber_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F σ i).obj k =
      (F.map ((σ.map (homOfLE
        (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))).base)).toFunctor.obj
          (σ.obj (grothWeightedPrefixIndex i k)).fiber

theorem grothWeightedPrefixFiber_last (i : Fin (n+1)) :
    (grothWeightedPrefixFiber F σ i).obj (Fin.last i.val) = (σ.obj i).fiber
```

## 194. R03eの全prefix係数と順向きの単体写像（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

prefixの包含に対する自然性を、既存transportの自然性から示した。これをYonedaで元の重み係数の自然変換にし、任意の面・退化への自然性を保つ順向きの単体集合写像に束ねた。元の基底への射影との等式も厳密に成立する。逆向きの単体の関手性と両往復はまだ残る。

263：新規三本の対象ビルド1,172 jobs・終了0、小監査113本852宣言・標準三公理のみ。実ハンドル66924の終了0を確認し、鍵返却済み。今回164行、累計113本・7,518行（外枠15,000）。R03eは229行／見込み500〜900行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

併せて直近の報告の型抜粋で、`where`で始まる構成の本体まで入っていた箇所を型のみへ直した。宣言や型の変更ではない。R03d・R02の指定錐の族・無条件のnative極限性は未完了のまま。次は元のweighted係数から回収した逆向きの射列と両往復を示す。

### 194.1 型

#### GrothendieckWeightedNervePrefixNaturality（55行）

```lean
theorem grothWeightedPrefixArrow_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedPrefixArrow F σ i ⋙ CostructuredArrow.map (S := Grothendieck.forget F) (σ.map f).base =
      (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ j

theorem grothWeightedPrefixFiber_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ j =
      grothWeightedPrefixFiber F σ i ⋙ (F.map (σ.map f).base).toFunctor
```

#### GrothendieckWeightedNerveCoefficients（43行）

```lean
def grothWeightedNerveCoefficients :
    simplexPrefixWeight n ⟶ (σ ⋙ Grothendieck.forget F) ⋙ (F ⋙ nerveFunctor)

def grothWeightedNerveSimplex : weightedNerveSimplex (F ⋙ nerveFunctor) n

theorem grothWeightedNerveSimplex_base :
    (grothWeightedNerveSimplex F σ).1 = σ ⋙ Grothendieck.forget F
```

#### GrothendieckWeightedNerveForward（66行）

```lean
theorem grothWeightedPrefixArrow_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixArrow F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ (α.toOrderHom i)

theorem grothWeightedPrefixFiber_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) (i : Fin (m.len+1)) :
    grothWeightedPrefixFiber F (α.toOrderHom.monotone.functor ⋙ σ) i =
      (simplexPrefixRestriction α i).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ (α.toOrderHom i)

theorem grothWeightedNerveSimplex_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Grothendieck F) n.len) :
    grothWeightedNerveSimplex F (α.toOrderHom.monotone.functor ⋙ σ) =
      weightedNerveSimplexMap (F ⋙ nerveFunctor) α (grothWeightedNerveSimplex F σ)

def grothWeightedNerveForward : nerve (Grothendieck F) ⟶ weightedNerve (F ⋙ nerveFunctor)

theorem grothWeightedNerveForward_projection :
    grothWeightedNerveForward F ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F)
```

## 195. R03eの逆向きの射列（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは未完了。

各weighted係数のYoneda表示を取り、prefixの最終対象を逆向きのGrothendieck対象とした。係数の自然性は、包含で制限した射列と基底の射に沿って送った射列の厳密な等式である。その最終対象への評価を型の移送に使い、同じ底を持つGrothendieck射を回収した。恒等射・合成則もこの自然性の射への評価と有限順序上の射の一意性から示し、逆向きの全射列に束ねた。

264：新規二本の対象ビルド1,168 jobs・終了0、小監査115本866宣言・標準三公理のみ。実ハンドル19367の終了0を確認し、鍵返却済み。今回118行、累計115本・7,636行（外枠15,000）。R03eは347行／見込み500〜900行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは、両往復と順向き写像の各次数での全単射性、そこからの同じ写像を前向きに持つ単体集合の同型、指定点の等式である。逆向き写像の面・退化との自然性を別に作り直さず、検証済みの順向き自然変換の各成分が可逆であることから全同型を得る。見込みの半分450行に達する前だが、現時点の残りは200〜450行と見積もる。R03d・R02・無条件のnative極限性はまだ閉じていない。

### 195.1 型

#### GrothendieckWeightedNerveInverseData（65行）

```lean
def grothWeightedNerveFiberChain (i : Fin (n+1)) : ComposableArrows (F.obj (s.1.obj i)) i.val

theorem grothWeightedNerveFiberChain_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
      grothWeightedNerveFiberChain F s j =
        grothWeightedNerveFiberChain F s i ⋙ (F.map (s.1.map f)).toFunctor

def grothWeightedNerveInverseObj (i : Fin (n+1)) : Grothendieck F

def grothWeightedNerveInverseIndex {i j : Fin (n+1)} (f : i ⟶ j) : Fin (j.val+1)

theorem grothWeightedNerveInverse_source {i j : Fin (n+1)} (f : i ⟶ j) :
    (F.map (s.1.map f)).toFunctor.obj (grothWeightedNerveInverseObj F s i).fiber =
      (grothWeightedNerveFiberChain F s j).obj (grothWeightedNerveInverseIndex f)

def grothWeightedNerveInverseMap {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedNerveInverseObj F s i ⟶ grothWeightedNerveInverseObj F s j

theorem grothWeightedNerveInverseMap_base {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedNerveInverseMap F s f).base = s.1.map f
```

#### GrothendieckWeightedNerveInverseFunctor（53行）

```lean
theorem grothWeightedNerveInverseMap_id (i : Fin (n+1)) :
    grothWeightedNerveInverseMap F s (𝟙 i) = 𝟙 (grothWeightedNerveInverseObj F s i)

theorem grothWeightedNerveInverseMap_comp {i j k : Fin (n+1)} (f : i ⟶ j) (g : j ⟶ k) :
    grothWeightedNerveInverseMap F s (f ≫ g) =
      grothWeightedNerveInverseMap F s f ≫ grothWeightedNerveInverseMap F s g

def grothWeightedNerveInverseSimplex : ComposableArrows (Grothendieck F) n

theorem grothWeightedNerveInverseSimplex_base :
    grothWeightedNerveInverseSimplex F s ⋙ Grothendieck.forget F = s.1
```

## 196. R03eの半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 5／全体 18（うち追加 6）。R03eは対象ビルド前で未完了。

検証済み347行に、両往復・全同型・指定頂点の作業木の四本259行を加えて606行となり、当初見込み500〜900行の半分450行を超えた。作業木を含む累計は7895行／外枠15,000行。両往復と全同型はまとめた個別検査の実ハンドル11719で終了0。指定頂点はまだ個別検査中であり、四本の対象ビルド・小監査は未実施。この時点で未検証分をコミットしない。

残りは指定頂点の次数零の計算、四本の対象ビルドと小監査である。型は§192のR03eを保持しており、見込み500〜900行以内で閉じる見通し。R03dの後半は、同じ底上のKan分類と元のaugmentationの指定点の照合が引き続き必要であり、R03eだけでnative極限性が得られたとは扱わない。

## 197. R03e完了：同じ射影と指定点を持つ厳密なweighted nerve同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。今回R03eが完了。R02・R03・R03dは未完了。

元のweighted係数から回収した射列のprefixは、元の同じ係数の全射列に一致する。対象は係数の自然性の対象への評価、射は同じ関手等式の射への評価で示し、Yonedaの往復で元のweighted単体へ戻した。逆方向の往復も、元のprefixの最終対象と最終射の評価から、元のGrothendieck射列そのものへ戻る等式として示した。

これらの両往復から順向きの既存全写像の各次数が全単射となり、その同じ全写像を前向きに持つ単体集合の同型を得た。元の底への射影の厳密な等式と、元の各fiber対象の指定頂点が同じconstant liftになる等式を併記し、§192のR03eの型をそのまま閉じた。逆写像の自然性を仮定したり、対象ごとの同値で代用したりしていない。

265：四本の対象ビルド1,570 jobs・終了0、小監査119本885宣言・標準三公理のみ。実ハンドル23927の終了0を確認し、鍵返却済み。直前の全個別検査は実ハンドル32248の終了0。今回260行、累計119本・7,896行／外枠15,000。R03eは607行で、当初見込み500〜900行の範囲内（上端との差−293行）。モジュール実ファイルの再集計で§195・196の二行の誤算も修正した。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

R03dの後半へ進むにあたり、`weightedNerveMap_isPrecompositionEquivalence` の入力には両係数のKan性が要ることを確認した。したがって、一般の `nerve (F.obj i)` からKan化への射にそのまま適用することはできない。continuousLeftFibrationReplacementの単位はleft anodyneで、`continuousLeftFibrationHomIso` は同じ底上の全相対Homを保つが、これだけで元の係数の全分類との同型や指定点の正規化が得られたとはしない。次はR03eを同じ底のOverの同型へ持ち上げる既存構成の法則を使い、相対Kan比較の残りを確認する。§192.1の候補はまだ一覧に加えず、未証明のまま使わない。

### 197.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。単体の法則ではさらに `{n : ℕ}` と `s : weightedNerveSimplex (F ⋙ nerveFunctor) n` または `σ : ComposableArrows (Grothendieck F) n` を用いる。

#### GrothendieckWeightedNerveRecovery（63行）

```lean
theorem grothWeightedPrefixFiber_inverse_obj (i : Fin (n+1)) (k : Fin (i.val+1)) :
    (grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i).obj k =
      (grothWeightedNerveFiberChain F s i).obj k

theorem grothWeightedPrefixFiber_inverse (i : Fin (n+1)) :
    grothWeightedPrefixFiber F (grothWeightedNerveInverseSimplex F s) i =
      grothWeightedNerveFiberChain F s i

theorem grothWeightedNerveSimplex_inverse :
    grothWeightedNerveSimplex F (grothWeightedNerveInverseSimplex F s) = s
```

#### GrothendieckWeightedNerveRetraction（82行）

```lean
theorem grothWeightedNerveFiberChain_forward (i : Fin (n+1)) :
    grothWeightedNerveFiberChain F (grothWeightedNerveSimplex F σ) i =
      grothWeightedPrefixFiber F σ i

theorem grothWeightedNerveInverseObj_forward (i : Fin (n+1)) :
    grothWeightedNerveInverseObj F (grothWeightedNerveSimplex F σ) i = σ.obj i

theorem grothWeightedPrefixFiber_last_map {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedPrefixFiber F σ j).map (homOfLE
      (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from leOfHom f)) =
        eqToHom (by
          rw [grothWeightedPrefixFiber_obj]
          rfl) ≫ (σ.map f).fiber ≫
            eqToHom (grothWeightedPrefixFiber_last F σ j).symm

theorem grothWeightedNerveInverseSimplex_forward :
    grothWeightedNerveInverseSimplex F (grothWeightedNerveSimplex F σ) = σ
```

#### GrothendieckWeightedNerveIso（40行）

```lean
theorem grothWeightedNerveForward_bijective (n : ℕ) :
    Function.Bijective (grothWeightedNerveSimplex F (n := n))

def grothendieckWeightedNerveIso : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor)

theorem grothendieckWeightedNerveIso_projection :
    (grothendieckWeightedNerveIso F).hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F)
```

#### GrothendieckWeightedNerveVertex（75行）

```lean
theorem grothWeightedNerveForward_vertex (i : I) (x : F.obj i) :
    (grothWeightedNerveForward F).app (Opposite.op ⦋0⦌)
      (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
        (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
          (Opposite.op ⦋0⦌) (nerveVertex x)

theorem exists_grothendieckWeightedNerveIso :
    ∃ e : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor),
      e.hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
        nerveMap (Grothendieck.forget F) ∧
      ∀ (i : I) (x : F.obj i),
        e.hom.app (Opposite.op ⦋0⦌) (nerveVertex (⟨i,x⟩ : Grothendieck F)) =
          (weightedNerveConstantLift (F ⋙ nerveFunctor) i).app
            (Opposite.op ⦋0⦌) (nerveVertex x)
```

## 198. 同じ底上の置換同型と元の単位の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。R03e完了、R03d・R02・R03は未完了。

検証済みの同じ射影の等式をOver.isoMkに渡し、R03eを元の同じ底のOverの同型にした。この同型を既存のcontinuousLeftFibrationReplacementに送り、元の指定された置換の単位との厳密な可換性を単位の自然性から示した。いずれも既存構成の同型保存・自然性の法則であり、新しい中間の定理の追加ではない。元の係数からの相対Kan分類が成立したとは主張しない。

266：新規一本の対象ビルド1,517 jobs・終了0、小監査120本888宣言・標準三公理のみ。実ハンドル70589の終了0を確認し、鍵返却済み。個別検査も実ハンドル61213の終了0。今回45行、累計120本・7,941行／外枠15,000。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは§197のとおり、同じ底上のKan分類と元のaugmentationの指定点の回収、それを全共同Hom比較へ接続することである。Kan係数を仮定するweightedNerveMapの既存の前合成同値判定を、一般の非Kanなnerve係数へ適用しない。候補§192.1はなお未証明・未登録。R03dの型・固定始域への一致・元の標準脚の型を保って続ける。

### 198.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckWeightedNerveOver（45行）

```lean
def grothendieckWeightedNerveOverIso :
    Over.mk (nerveMap (Grothendieck.forget F)) ≅ Over.mk (weightedNerveProjection (F ⋙ nerveFunctor))

def grothendieckWeightedNerveReplacementIso :
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F))) ≅
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))

theorem grothendieckWeightedNerveReplacementIso_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        (grothendieckWeightedNerveReplacementIso F).hom.left =
      (grothendieckWeightedNerveOverIso F).hom.left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).left
```

## 199. 底上の同じ置換同型を全分類へ運ぶ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 18（うち追加 6）。R03d・R02・R03は未完了。

前のターンはR03eの完成とOver・置換単位の照合まで進んだため、進捗あり。今回は作業木がcleanであることとコミット4baf71306を確認して継続した。既存の `leftClassification_overIso` を、検証済みの同じ底上の二つの置換同型に適用した。比較は底全体のFunctorIsoであり、fiberごとの同型による代用ではない。同型保存の既存の法則で、一覧の中間の定理の追加ではない。

267：新規一本の対象ビルド3,125 jobs・終了0、小監査121本892宣言・標準三公理のみ。実ハンドル26874の終了0を確認し、鍵返却済み。個別検査は実ハンドル40480の終了0。今回36行、累計121本・7,977行／外枠15,000。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次に必要なCat値図式の相対Kan比較の分類側の候補を一時ファイル `/private/tmp/CheckISW2CatLeftStraighteningType.lean` のPropとして確認した（実ハンドル60059・終了0）。元の置換単位と元の前向きweighted mapの厳密な等式も保持する、より強い全空間の比較の候補は `/private/tmp/CheckISW2GrothKanLiftType.lean` のPropとして確認した（実ハンドル2743・終了0）。いずれもこの時点では未証明で一覧に追加せず、仮定として使わない。まず既存のleft-anodyne単位に沿う相対延長を使い、元の比較を保持する全空間の射を構成する。射の存在だけでは前合成同値性は得られないことを区別する。

### 199.1 型（共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`）

#### GrothendieckWeightedNerveClassification（36行）

```lean
def grothendieckWeightedNerveReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).hom)
```

## 200. R03f：元の単位を固定する相対Kan比較（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03fを追加、未証明。R03d・R02・R03も未完了。

IS-W2 §19の「同じまとまりで一つの見込み1,500行以下」の枠で、次の独立の中間定理R03fを一覧に加える。Cat値図式の各fiberのnerveをKan化することと、そのGrothendieck射影の同じ底上のleft fibration置換を比較する相対版のgroupoid completionである。R03eは厳密な二模型の同型のみで、この相対Kan化を含まないため、既存の構成の法則として数えない。

### 200.1 型

共通の名前空間はGrothendieckWeightedNerveOverと同じ。`exInfinity`・`exInfinityUnit` はTheExInfinityFunctor、`IsPrecompositionEquivalence` はTheHomotopyTheoryOfInfinityCategories.Equivalenceの既存の宣言。

```lean
theorem exists_grothendieckKanCoefficientComparison
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
  let G := (F ⋙ nerveFunctor) ⋙ exInfinity
  let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
  let R := (continuousLeftFibrationReplacement (nerve I)).obj P
  let η : F ⋙ nerveFunctor ⟶ G :=
    Functor.whiskerLeft (F ⋙ nerveFunctor) exInfinityUnit
  ∃ f : R.left ⟶ weightedNerve G,
    f ≫ weightedNerveProjection G = R.hom ∧
    ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
      grothWeightedNerveForward F ≫ weightedNerveMap η ∧
    IsPrecompositionEquivalence f
```

このPropの型は一時ファイルCheckISW2GrothKanLiftType.leanで確認済み（実ハンドル2743、終了0）。本体に未証明の定理や仮定として入れない。元の全空間の射・同じ底・指定された元の単位との等式を保持する。単なる分類像の存在より強い型であり、後で元の指定点への回収を追える形にする。R03dの固定始域比較との一致の型は変えない。

### 200.2 見込みと経路

置き場所は同じFibrationsOverOrdinaryCategories/GrothendieckKan*.lean。見込み900〜1,450行。元の係数の単位からの射と相対延長（約70〜150行）、bar/scaffoldと元のGrothendieck比較の照合（100〜200行）、同じ底上でfiberの全辺を可逆化する比較の検証（500〜750行）、全空間の前合成同値と元の単位の正規化を束ねる部分（150〜350行）を想定する。独立の中間定理としての上端1,450行であり、任意の細分で§19の枠を回避しない。半分の725行で止まらずに実測と残りを報告する。

短縮の候補：元のnerve係数はquasicategoryであるため、`tautScaffold_isPrecompositionEquivalence_of_quasicategory` を使える。前の一般のweightedNerveMapのKan係数用判定との違いはここにある。R03eとこのscaffoldを介して元の射を保持し、各fiberのEx∞単位が全辺を可逆にすることを同じ底の比較として示す。全空間の通常の弱ホモトピー同値だけで相対版を代用しない。相対延長の存在の既存の法則はすでに個別検査を通ったが、それだけでは最後のIsPrecompositionEquivalenceは得られない。fiberごとの可逆化と同じ底上の比較を示す数学が残る。

⑤aの欄、既存FramedLimit*・CAlgUnderlyingDerivedComparison、点つきKanのTot、[ModelCategory SSet]を追加・変更しない。R03fが閉じた後も、元の要素圏の反対・augmentationとの照合とR03dへの接続を別に検収する。

## 201. 元の置換単位を固定したKan係数への相対延長（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03f・R03d・R02・R03は未完了。

元の全Cat図式のnerveに同じEx∞単位を後合成し、R03eの前向き全写像とweightedNerveMapで、同じ底のKan係数への実射を構成した。元の射影との厳密な等式を確認し、既存のleft-anodyne単位に対する相対延長の定理で、その元の単位との合成が元の実射そのものである延長を得た。この存在と二つの等式は既存構成の法則であり、R03fの最後の前合成同値性はまだ証明していない。

268は不足していた既存ContinuousLeftFibrationAnodyneの対象ビルド1,506 jobsまでは成功したが、その後の個別検査でOver対象の暗黙引数の推論に失敗した（実ハンドル95897・終了1）。対象を明示して個別検査16203・終了0を確認し、269で新規一本の対象ビルド1,866 jobs・終了0と小監査122本899宣言・標準三公理のみを確認した。実ハンドル94522の終了0を確認し、鍵返却済み。

今回69行、累計122本・8,046行／外枠15,000。R03fは69行／見込み900〜1,450行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次はquasicategory値nerve係数のtaut scaffoldをR03eへ接続し、元の射を保つbar/scaffold比較を作る。

### 201.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。各係数のKan性は同じEx∞の既存のinstanceにより明示した。

#### GrothendieckKanCoefficientLift（69行）

```lean
abbrev grothendieckKanCoefficients : I ⥤ SSet.{u}

def grothendieckKanCoefficientUnit : F ⋙ nerveFunctor ⟶ grothendieckKanCoefficients F

def grothendieckKanCoefficientMap :
    nerve (Grothendieck F) ⟶ weightedNerve (grothendieckKanCoefficients F)

theorem grothendieckKanCoefficientMap_projection :
    grothendieckKanCoefficientMap F ≫ weightedNerveProjection (grothendieckKanCoefficients F) =
      nerveMap (Grothendieck.forget F)

theorem exists_grothendieckKanCoefficientLift :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F
```

## 202. 元のbar/scaffoldとKan係数への射の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 19（うち追加 7）。R03f・R03d・R02・R03は未完了。

元のCat図式のnerve係数にtaut scaffoldを取り、R03eの同じ逆射を後合成して、barから元のGrothendieck射列への全空間の射を得た。同じ基底への射影を保ち、元のKan係数への実射との合成は、barの元の係数単位の自然変換の後にKan係数のtaut scaffoldを続けた射と厳密に一致する。quasicategory係数用の既存のscaffold定理から、この元のbar→Grothendieck射列の射自身の前合成同値性も得た。Kan性を非Kanなnerve係数へ仮定していない。

270：新規一本の対象ビルド2,389 jobs・終了0、小監査123本904宣言・標準三公理のみ。実ハンドル89697の終了0を確認し、鍵返却済み。個別検査66223も終了0。今回59行、累計123本・8,105行／外枠15,000。R03fは128行／見込み900〜1,450行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りは、係数のEx∞単位のbar上の相対的な性質から、元の単位を固定する延長の前合成同値性を得る部分である。対象ごとの通常の弱同値から全空間の圏同値を直接主張しない。

### 202.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckKanScaffold（59行）

```lean
def grothendieckNerveScaffold :
    simplicialReplacement (F ⋙ nerveFunctor) ⟶ nerve (Grothendieck F)

theorem grothendieckNerveScaffold_projection :
    grothendieckNerveScaffold F ≫ nerveMap (Grothendieck.forget F) =
      simplicialReplacementProjection (F ⋙ nerveFunctor)

theorem grothendieckNerveScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckNerveScaffold F)

theorem grothendieckNerveScaffold_kanCoefficientMap :
    grothendieckNerveScaffold F ≫ grothendieckKanCoefficientMap F =
      simplicialReplacementMap (grothendieckKanCoefficientUnit F) ≫
        tautScaffold (grothendieckKanCoefficients F)
```

## 203. R03f.1：Kan標的へのanodyne射のleft anodyne性（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 6／全体 20（うち追加 8）。R03f.1を追加、未証明。

§19の同じまとまり・見込み1,500行以下の枠で、次の一般補題をR03f.1として加える。R03fのEx∞単位の相対的な持ち上げ性に使う数学的な中間定理であり、既存構成の自然性の法則と混同しない。

```lean
theorem anodyneExtensions_leftAnodyne_of_kanTarget
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) :
  leftAnodyneExtensions f
```

`leftAnodyneExtensions` はTheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrationsの既存の定義。このPropの型は一時ファイルCheckISW2AnodyneKanTargetLeftType.leanで確認済み（実ハンドル37011・終了0）。未証明の宣言や仮定として本体に入れない。

置き場所はKerodon/TheHomotopyTheoryOfInfinityCategories/LeftAndRightFibrations/AnodyneKanTarget.leanを想定する。同名の既存ファイルはない。見込み150〜300行。左ホーンの持ち上げによって、Kan基底上のleft fibrationの全空間もKanであることを既存のkanComplex_of_leftHornFillersに渡せる。一般の持ち上げ問題をY上へ引き戻すと、その射影はKan複体間のleft fibrationであり、既存leftFibration_fibration_of_kanComplexから全ホーンを持ち上げる。hfのanodyne性でその引き戻した射影への持ち上げを得て、元の問題へ戻す。これをleftHornInclusions.rlp.llpとして束ねる。モデル構造の仮定は使わない。

この補題が得られてもbarが係数のleft anodyne射をどのように保つかの検証と、元のR03fの前合成同値性は残る。R03f.1だけをもってR03fまたはR03dの完成とは扱わない。R03f.1の実測は独立に記録し、外枠15,000行にも含める。次はこの型の証明に進む。

## 204. R03f.1完了：Kan標的へのanodyne射はleft anodyne（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 20（うち追加 8）。R03f.1完了。R03f・R03d・R02・R03は未完了。

Kan基底上のleft fibrationについて、基底の左ホーンをKan性で充填し、その充填をleft fibrationで持ち上げた。既存kanComplex_of_leftHornFillersにより全空間もKanとなる。次に任意のleft fibrationへの元の持ち上げ問題をKan標的へ引き戻し、その射影の全ホーン持ち上げ性へanodyne性を適用して元へ戻した。元の射そのものがleftHornInclusions.rlp.llpに属することを証明した。

271：新規一本の対象ビルド1,608 jobs・終了0、小監査124本906宣言・標準三公理のみ。実ハンドル74994の終了0を確認し、鍵返却済み。個別検査66431も終了0。今回61行、累計124本・8,166行／外枠15,000。R03f.1は見込み150〜300行に対して61行（上端との差−239行）。既存のkanComplex_of_leftHornFillersとleftFibration_fibration_of_kanComplexで短縮できた。R03f本体の128行とは独立に記録する。

SSet.modelCategoryQuillenのスコープは、fibrationを全ホーンの右持ち上げ性として読むためにだけ用いる。[ModelCategory SSet]は追加していない。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は同じEx∞単位のleft anodyne性へ適用し、bar上への移送を検討する。

### 204.1 型

#### AnodyneKanTarget（61行）

```lean
theorem leftFibration_total_kanComplex {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) [LeftFibration p] : KanComplex E

theorem anodyneExtensions_leftAnodyne_of_kanTarget
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : leftAnodyneExtensions f
```

## 205. 元のEx∞単位のleft anodyne性への適用（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 20（うち追加 8）。R03f・R03d・R02・R03は未完了。

R03f.1を元の同じexInfinityUnitと既存exInfinityUnit_anodyneへ適用し、その単位自身のleft anodyne性を得た。既存構成の性質の適用であり、一覧の新しい数学的定理には数えない。関手・単位の変更や別のKan模型への置き換えはしていない。

272：新規一本の対象ビルド1,670 jobs・終了0、小監査125本907宣言・標準三公理のみ。実ハンドル72538の終了0を確認し、鍵返却済み。個別検査15355も終了0。今回23行、累計125本・8,189行／外枠15,000。R03f本体の作業は151行、独立のR03f.1は61行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 205.1 型

#### ExInfinityUnitLeftAnodyne（23行）

```lean
theorem exInfinityUnit_leftAnodyne (X : SSet.{u}) :
    leftAnodyneExtensions (exInfinityUnit.app X)
```

## 206. R03f.2：barが各成分のleft anodyne性を保つ（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2を追加、未証明。

同じR03fのまとまりで、§19の見込み1,500行以下の枠により次の独立の中間定理を加える。全ての自然変換に対する一般のbarの保存定理であり、既存の単位の自然性の法則として処理しない。R03f.1のKan標的への判定とは異なる数学である。

```lean
theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
  leftAnodyneExtensions (simplicialReplacementMap η)
```

名前空間はFibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories。`leftAnodyneExtensions` はTheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrationsの既存の性質。型は `/private/tmp/CheckISW2ReplacementLeftType.lean` のPropで確認した（実ハンドル31074・終了0）。未証明の宣言や仮定を本体に登録しない。

見込み650〜1,200行。置き場所は一般の対角の道具がHomotopicalAlgebra/Simplicial/DiagonalLeftAnodyne.lean、bar固有がFibrationsOverOrdinaryCategories/SimplicialReplacementLeftAnodyne*.lean。一般の対角の相対持ち上げ80〜180行、barの行の余積表示と退化のlatchingの相対表示350〜650行、既存のsimplicialReplacementMapへの同定・全移送150〜300行を見込む。半分600行で実測と残りを報告する。独立のbarの保存定理の全体として見積もり、細分で§19の枠を回避しない。

短い経路：既存DiagonalAnodyne.diagonal_map_anodyneは全ホーン用の射の性質を固定しているため、その結論をleft anodyneへ読み替えない。同じ対角の右随伴とrelativeMatchingArrowIsoの証明を、left fibrationと境界内部Homへ適用する。必要なleftAnodyneExtensions_pushoutObjObj_left/rightとleftFibration_pullbackObjObjπは既存のLeftAnodynePushoutProductにある。barの各行は元の基底射列で添字づけた係数の余積であり、BarRowsCoproductの既存の余積表示を再利用する。退化の分裂により相対latchingの非退化部分を係数の同じη.app iの余積へ同定し、left anodyne性を渡す。これをReedy持ち上げと対角の随伴で元の全写像へ戻す。

R03f.2が得られれば、元の係数のEx∞単位に適用し、§202の同じscaffold正方形と§201の元の単位を固定した延長へ接続する。ただし、この時点ではR03fの延長の前合成同値性もR03dの両変数比較も未証明。元の指定点・固定始域の比較の一致という型を保って進める。

## 207. R03f.2の対角の持ち上げと元のbarの行（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

前のターンではR03f.1とEx∞単位への適用が検証済みでコミットされていたため、進捗あり。開始時にcleanな作業木とd4bf795eeを確認した。今回は対角の右随伴の相対matching射を、既存の同じrelativeMatchingArrowIsoで境界内部Homへ同定し、left fibration性を移した。Reedyの持ち上げと元の対角の随伴により、Reedy left anodyneな射の対角そのものがleft anodyneであることを示した。

barの各行は、元の基底射列σで添字づけた同じ係数F(σ(0))の単体集合として構成し、指定された同じ包含を持つ実際の余積であることを確認した。各行の任意の面・退化の写像は、元の基底射列の始点から新たな始点への射による係数の輸送で定義した。恒等射・合成則も元のIとFの関手則から示し、一つの二重単体集合の図式へ束ねた。BarRowsCoproductと同じ余積による考え方を使うが、一般のKerodon側からEInfinityへの依存を追加しないため、同じ宇宙の依存和で直接示した。

273：対角の新規一本の対象ビルド1,635 jobs・終了0、小監査126本909宣言・標準三公理のみ（実ハンドル71484・終了0）。274：行の新規二本の対象ビルド1,172 jobs・終了0、小監査128本931宣言・標準三公理のみ（実ハンドル8005・終了0）。両方とも鍵返却済み。個別検査は10567・74674・68021の終了0を確認した。

今回47＋71＋69＝187行、累計128本・8,376行／外枠15,000。R03f.2は187行／見込み650〜1,200行、まだ半分600行前。元のsimplicialReplacementMapへの対角の同定と、相対latchingが元の各η.app iのleft anodyne性を持つことが残る。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 207.1 型

行の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、固定した行ではさらに `(n : ℕ)`。

#### DiagonalLeftAnodyne（47行）

```lean
theorem relativeMatching_leftFibrations {E B : SSet.{u}} (p : E ⟶ B)
    (hp : leftFibrations p) (n : ℕ) :
    leftFibrations (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p))

theorem diagonal_map_leftAnodyne {A B : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : A ⟶ B)
    (hf : reedyLeft simplexOp leftAnodyneExtensions f) :
    leftAnodyneExtensions (diagonal.map f)
```

#### SimplicialReplacementRows（71行）

```lean
def simplicialReplacementRow : SSet.{u}

def simplicialReplacementRowInclusion (σ : ComposableArrows I n) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRow F n

def simplicialReplacementRowCofan : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))

def simplicialReplacementRowDesc
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) :
    simplicialReplacementRow F n ⟶ s.pt

def simplicialReplacementRowIsColimit : IsColimit (simplicialReplacementRowCofan F n)
```

#### SimplicialReplacementRowReindex（69行）

```lean
def simplicialReplacementRowReindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRow F n.len ⟶ simplicialReplacementRow F m.len

theorem simplicialReplacementRowReindex_id (n : SimplexCategory) :
    simplicialReplacementRowReindex F (𝟙 n) = 𝟙 (simplicialReplacementRow F n.len)

theorem simplicialReplacementRowReindex_comp {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) :
    simplicialReplacementRowReindex F (α ≫ β) =
      simplicialReplacementRowReindex F β ≫ simplicialReplacementRowReindex F α

def simplicialReplacementRows : SimplexCategoryᵒᵖ ⥤ SSet.{u}
```

## 208. 元の係数射・対角同型・退化部分の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

元の係数の自然変換を同じ基底射列の全行に適用し、全ての面・退化との可換性を元の自然性から示した。二重単体集合の対角は、同じ基底射列の係数のYoneda表示だけを変える全同型で元のsimplicial replacementと同定した。元の係数射の対角が、その全同型と指定されたsimplicialReplacementMapを通る同じ射に厳密に一致する等式も示した。

任意の全射作用素が零を零へ送ることから、退化作用素の係数の輸送は同じ始点の等式に沿うeqToHomそのものとなる。各行の任意の基底部分集合を部分複体とし、基底の退化・非退化の二部分が交わらず元の行全体を覆うことを確認した。係数の自然変換は同じ部分を保ち、元の包含と厳密に可換する。この時点では実際の外側のlatchingとの同型性をまだ主張しない。

275：三本の対象ビルド1,296 jobs・終了0、小監査131本947宣言・標準三公理のみ（実ハンドル97624・終了0）。276：部分複体一本の対象ビルド1,174 jobs・終了0、小監査132本956宣言・標準三公理のみ（実ハンドル27094・終了0）。両方とも鍵返却済み。個別検査82533・99836・13226・16512の終了0を確認した。

今回47＋69＋42＋64＝222行、累計132本・8,598行／外枠15,000。R03f.2は409行／見込み650〜1,200行。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。sorry・独自公理0、計算上限変更なし。次は元のlatching図式を同じ退化部分への余錐として読み、その余極限性から相対latchingを非退化成分の同じ係数射へ分離する。

### 208.1 型

共通の入力は `{I : Type u} [SmallCategory I]`。係数は `F G : I ⥤ SSet.{u}`、その射は `η : F ⟶ G`。固定した行では `(n : ℕ)` を用いる。

#### SimplicialReplacementRowMaps（47行）

```lean
def simplicialReplacementRowMap (n : ℕ) :
    simplicialReplacementRow F n ⟶ simplicialReplacementRow G n

theorem simplicialReplacementRowMap_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    simplicialReplacementRowReindex F α ≫ simplicialReplacementRowMap η m.len =
      simplicialReplacementRowMap η n.len ≫ simplicialReplacementRowReindex G α

def simplicialReplacementRowsMap : simplicialReplacementRows F ⟶ simplicialReplacementRows G
```

#### SimplicialReplacementDiagonal（69行）

```lean
def simplicialReplacementDiagonalHom (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ⟶ simplicialReplacement F

def simplicialReplacementDiagonalIso (F : I ⥤ SSet.{u}) :
    diagonal.obj (simplicialReplacementRows F) ≅ simplicialReplacement F

theorem simplicialReplacementDiagonalIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    diagonal.map (simplicialReplacementRowsMap η) ≫ (simplicialReplacementDiagonalIso G).hom =
      (simplicialReplacementDiagonalIso F).hom ≫ simplicialReplacementMap η
```

#### SimplicialReplacementRowDegeneracies（42行）

```lean
theorem simplicialReplacement_epi_zero {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    α.toOrderHom 0 = 0

theorem simplicialReplacement_epi_first {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    (α.toOrderHom.monotone.functor ⋙ σ).obj 0 = σ.obj 0

theorem simplicialReplacement_epi_coefficient {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (σ : ComposableArrows I n.len) :
    F.map (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))) =
      eqToHom (congrArg (fun i => F.obj (σ.obj i)) (simplicialReplacement_epi_zero α).symm)
```

#### SimplicialReplacementRowParts（64行）

```lean
def simplicialReplacementRowPart (F : I ⥤ SSet.{u}) (n : ℕ)
    (P : Set (ComposableArrows I n)) : (simplicialReplacementRow F n).Subcomplex

abbrev simplicialReplacementDegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ)

abbrev simplicialReplacementNondegenerateRow (F : I ⥤ SSet.{u}) (n : ℕ)

theorem simplicialReplacementRowParts_sup (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊔ simplicialReplacementNondegenerateRow F n = ⊤

theorem simplicialReplacementRowParts_inf (F : I ⥤ SSet.{u}) (n : ℕ) :
    simplicialReplacementDegenerateRow F n ⊓ simplicialReplacementNondegenerateRow F n = ⊥

def simplicialReplacementRowPartMap {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (n : ℕ)
    (P : Set (ComposableArrows I n)) :
    (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ simplicialReplacementRowPart G n P

theorem simplicialReplacementRowPartMap_inclusion {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (n : ℕ) (P : Set (ComposableArrows I n)) :
    simplicialReplacementRowPartMap η n P ≫ (simplicialReplacementRowPart G n P).ι =
      (simplicialReplacementRowPart F n P).ι ≫ simplicialReplacementRowMap η n
```

## 209. 実際のlatching余錐と元の全単体の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

元の外側のlatching図式の各脚は、真に低い次数からの基底射列の像を持つため、同じ行の退化部分に厳密に因子分解する。これらの全脚が元の作用素の合成則で自然な余錐となることを示し、実際のlatchingの余極限から同じ退化部分への比較射を得た。

退化基底の既存の非退化表示は、元と同じ次数の全射が恒等射であることにより、真に低い次数の表示へできる。この同じ全射を元のlatchingの対象に戻した。係数は始点の同じ等式に沿って移送し、latchingの脚との合成でその逆の移送と打ち消される。これにより余錐の脚が退化行の元の各単体を係数も含めて厳密に回収することを示した。被覆性だけで余極限性を主張しない。

277：latching余錐一本の対象ビルド1,646 jobs・終了0、小監査133本966宣言・標準三公理のみ（実ハンドル38799・終了0）。この回は夜の共有鍵の順番待ちを同じ一枚の整理券のまま待ち、終了まで確認した。278：表示とlatching対象一本の対象ビルド1,648 jobs・終了0、小監査134本974宣言・標準三公理のみ（実ハンドル7754・終了0）。279：全射性一本の対象ビルド1,649 jobs・終了0、小監査135本975宣言・標準三公理のみ（実ハンドル28495・終了0）。すべて鍵返却済み。個別検査82141・16898・69787の終了0を確認した。

今回64＋50＋46＝160行、累計135本・8,758行／外枠15,000。R03f.2は569行／見込み650〜1,200行。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は元の二つの表示を同じ非退化表示へ戻す一意性を使い、余錐の余極限性を示す。

### 209.1 型

共通入力は `{I : Type u} [SmallCategory I]`。余錐ではさらに `F : I ⥤ SSet.{u}` と `n : ℕ` を用いる。

#### SimplicialReplacementRowLatchingCocone（64行）

```lean
def simplicialReplacementRowLatchingLeg (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    (simplicialReplacementRows F).obj s.obj.left ⟶ simplicialReplacementDegenerateRow F n

theorem simplicialReplacementRowLatchingLeg_inclusion
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowLatchingLeg F n s ≫ (simplicialReplacementDegenerateRow F n).ι =
      (simplicialReplacementRows F).map s.obj.hom

def simplicialReplacementRowLatchingCocone :
    Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F)

def simplicialReplacementLatchingToDegenerate :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ⟶
      simplicialReplacementDegenerateRow F n

theorem simplicialReplacementLatchingToDegenerate_fac
    (s : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    colimit.ι (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) s ≫
      simplicialReplacementLatchingToDegenerate F n = simplicialReplacementRowLatchingLeg F n s
```

#### SimplicialReplacementRowNormalization（50行）

```lean
theorem simplicialReplacement_degenerate_presentation {n : ℕ}
    (σ : ComposableArrows I n) (hσ : σ ∈ (nerve I).degenerate n) :
    ∃ (m : ℕ) (_ : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi α)
      (τ : (nerve I).nonDegenerate m), σ = (nerve I).map α.op τ

def simplicialReplacementLatchingIndexOfEpi {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] : LatchingIndex simplexOp (Opposite.op ⦋n⦌)

theorem simplicialReplacementLatchingIndexOfEpi_hom {m n : ℕ} (hm : m < n)
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] :
    (simplicialReplacementLatchingIndexOfEpi hm α).obj.hom = α.op
```

#### SimplicialReplacementRowLatchingSurjective（46行）

```lean
theorem simplicialReplacementRowLatching_jointly_surjective (q : SimplexCategoryᵒᵖ)
    (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s
```

## 210. R03f.2の半分での実測（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2は未完了。

対象ビルド・小監査済み569行に、既存の非退化表示の次元・単体・全射の一意性を接続した個別検査済み38行を加えて607行となり、上端1,200行の半分600行に達した。38行の個別検査36596は終了0、対象ビルド・小監査280はまだ進行中であり、その分のLeanは未コミットに保つ。作業木を含む累計は8,796行／外枠15,000。

残りは余錐の余極限性、相対latchingの退化・非退化による分離、成分のleft anodyne性と対角への束ね。残り350〜600行、完成時957〜1,207行程度を見込む。元の見込み650〜1,200行の上端付近だが、§19の中間定理一つの1,500行と外枠にはまだ達しない。元の全写像のleft anodyne性を目標のままに保ち、弱同値性や条件つきの判定へ弱めない。新しい型・まとまりの変更はない。

## 211. 同じ非退化表示への因子分解の照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

任意の全射表示の元の単体を既存の非退化表示へ戻し、その二つの合成表示へ既存の次元・単体・全射の一意性を順に適用した。同じ元の非退化表示へ向かう全射γを得て、元の二つの全射についてβ≫γ＝α、元の表示された単体についてX.map γ.op τ＝υという二つの厳密な等式を併記した。既存の非退化表示の一意性の合成・照合であり、R03f.2の同じ証明の分割として扱う。新しい独立の数学的まとまりや仮定を足していない。

280：新規一本の対象ビルド1,649 jobs・終了0、小監査136本976宣言・標準三公理のみ。実ハンドル24681の終了0を確認し、鍵返却済み。個別検査36596も終了0。今回38行、累計136本・8,796行／外枠15,000。R03f.2は607行／見込み650〜1,200行。§210の半分の報告時に未検証だった分も、対象ビルドと小監査まで通った。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次の順序は、元の退化行の余錐の余極限性、相対latchingの分離、各係数のleft anodyne性と元の対角への輸送である。具体的には元のlatching余錐がIsColimitとなることを、§209の全射性と今回の二表示の共通表示で検証する。その後、相対latchingの始域を「標的Gの退化部分と始域Fの非退化部分の余積」へ同定する。相対latching射は、その表示では退化部分上の恒等射と非退化基底射列ごとの同じη.app iの余積となる。ここまでの一意性が全係数も含めて可換することを検収してから、left anodyne性と§207の対角の定理を適用する。余錐の被覆性や基底だけの一意性で余極限性を代用しない。

### 211.1 型（38行）

#### SimplicialReplacementRowCommonPresentation（38行）

```lean
theorem simplicialReplacement_common_nondegenerate_presentation {X : SSet.{u}} {n m k : ℕ}
    (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : X.nonDegenerate m)
    (β : ⦋n⦌ ⟶ ⦋k⦌) [Epi β] (υ : X.obj (Opposite.op ⦋k⦌))
    (h : X.map α.op τ = X.map β.op υ) :
    ∃ (γ : ⦋k⦌ ⟶ ⦋m⦌) (_ : Epi γ), β ≫ γ = α ∧ X.map γ.op τ = υ
```

## 212. 元のlatching余錐の余極限性と同じ退化部分の同型（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 7／全体 21（うち追加 9）。R03f.2・R03f・R03d・R02・R03は未完了。

前のターンは共通の非退化表示まで検証・コミット済みで進捗あり。開始時にcleanな作業木とe36070d9eを確認した。元の退化作用素が分裂単射であることと、同じ全射表示へ元の係数を回収する法則を示した。共通表示の全射を元のlatchingの射とし、その作用素で元の係数の単体を厳密に回収した。

任意の余錐の二つの表示を、同じ非退化基底表示へ係数ごと戻した。その退化作用素の単射性から、元の係数を含む同じ二つの単体が一致する。余錐の自然性により、任意の余錐で元の二表示の値が同じことを示した。元の被覆する脚から各単体の値を取り、この一致を使って自然な降下射・全脚での一致・一意性を構成した。元のlatching余錐のIsColimitと、実際のlatchingの余極限から同じ退化部分への全同型が得られた。

281：二本の対象ビルド1,652 jobs・終了0、小監査138本983宣言・標準三公理のみ（実ハンドル73674・終了0）。282：余錐の値と余極限の二本の対象ビルド1,654 jobs・終了0、小監査140本997宣言・標準三公理のみ（実ハンドル72177・終了0）。両方とも鍵返却済み。個別検査6095・87431・35572・30108の終了0を確認した。

今回49＋46＋70＋97＝262行、累計140本・9,058行／外枠15,000。R03f.2は869行。現状の残りは境界付きの各係数の持ち上げを行全体へ束ねる部分、元の相対latchingへの適用と対角への移送で300〜450行、完成時1,169〜1,319行程度と再見積もりする。当初の上端1,200行より増える可能性があるが、§19の中間定理一つ1,500行以内の見込みである。外枠も保持する。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

残りの短い経路は、相対latchingの大きな射の同型を別に作り直す代わりに、元の相対latchingの持ち上げ問題を直接解く方法である。退化基底成分では指定されたlatching境界の値を保持し、それ以外の成分では元のη.app iのleft anodyne性で持ち上げ、元の余積から行全体へ降下する。境界の制限と両脚が厳密に一致することを検収し、元の相対latching射のleft anodyne性へ戻す。R03f.2の型・範囲を変えず、条件つきの判定へ弱めない。

### 212.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。余錐の法則ではさらに `(n : ℕ)` を用いる。`c` は元のlatching図式の任意の余錐。

#### SimplicialReplacementRowEpiLifts（49行）

```lean
theorem simplicialReplacementRowReindex_mono {m n : SimplexCategory} (α : m ⟶ n) [Epi α] :
    Mono (simplicialReplacementRowReindex F α)

theorem simplicialReplacementRowReindex_lift {m n : SimplexCategory} (α : m ⟶ n) [Epi α]
    (τ : ComposableArrows I n.len) (q : SimplexCategoryᵒᵖ)
    (x : (simplicialReplacementRow F m.len).obj q)
    (h : (nerve I).map α.op τ = x.1) :
    ∃ y : (F.obj (τ.obj 0)).obj q,
      (simplicialReplacementRowReindex F α).app q ⟨τ,y⟩ = x
```

#### SimplicialReplacementRowLatchingRefinement（46行）

```lean
def simplicialReplacementLatchingRefinement (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α]
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) (γ : j.obj.left.unop ⟶ ⦋m⦌)
    (h : j.obj.hom.unop ≫ γ = α) : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j

theorem simplicialReplacementRowLatching_refine (q : SimplexCategoryᵒᵖ)
    (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : (nerve I).nonDegenerate m)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (h : (nerve I).map α.op τ =
      (((simplicialReplacementRows F).map j.obj.hom).app q x).1) :
    ∃ (f : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j)
      (y : (F.obj (τ.val.obj 0)).obj q),
      ((simplicialReplacementRows F).map f.hom.left).app q ⟨τ.val,y⟩ = x
```

#### SimplicialReplacementRowLatchingValues（70行）

```lean
theorem simplicialReplacementRowLatching_value_map
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) {j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌)} (f : j ⟶ k)
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : ((simplicialReplacementRows F).map f.hom.left).app q x = y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y

theorem simplicialReplacementRowLatching_values_eq
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j k : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (y : ((simplicialReplacementRows F).obj k.obj.left).obj q)
    (h : (simplicialReplacementRowLatchingLeg F n j).app q x =
      (simplicialReplacementRowLatchingLeg F n k).app q y) :
    (c.ι.app j).app q x = (c.ι.app k).app q y
```

#### SimplicialReplacementRowLatchingColimit（97行）

```lean
theorem simplicialReplacementRowLatching_exists_value
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    ∃ v : c.pt.obj q, ∀ (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
      (x : ((simplicialReplacementRows F).obj j.obj.left).obj q),
      (simplicialReplacementRowLatchingLeg F n j).app q x = s → (c.ι.app j).app q x = v

def simplicialReplacementRowLatchingValue
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (s : (simplicialReplacementDegenerateRow F n : SSet.{u}).obj q) :
    c.pt.obj q

theorem simplicialReplacementRowLatchingValue_fac
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F))
    (q : SimplexCategoryᵒᵖ) (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q) :
    simplicialReplacementRowLatchingValue F n c q
      ((simplicialReplacementRowLatchingLeg F n j).app q x) = (c.ι.app j).app q x

def simplicialReplacementRowLatchingDesc
    (c : Cocone (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F)) :
    (simplicialReplacementDegenerateRow F n : SSet.{u}) ⟶ c.pt

def simplicialReplacementRowLatchingIsColimit :
    IsColimit (simplicialReplacementRowLatchingCocone F n)

def simplicialReplacementRowLatchingIso :
    colimit (latchingSource simplexOp (Opposite.op ⦋n⦌) ⋙ simplicialReplacementRows F) ≅
      simplicialReplacementDegenerateRow F n
```

## 213. R03f.2完了：元のsimplicial replacementのleft anodyne性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f.2完了。R03f・R03d・R02・R03は未完了。

元の各行と指定部分の包含・係数射・降下の法則を明示した。退化基底成分では元の指定境界の値を固定し、それ以外の成分では元の同じη.app iのleft anodyne性で持ち上げた。元の余積から行全体へ降下させ、元の二つの脚と退化境界の値を厳密な等式で保持する持ち上げを得た。

実際のlatchingと退化部分の同型が、元の係数射と境界比較を厳密に保つことも全ての脚で照合した。元の相対latchingのpushoutの持ち上げ問題では、その逆同型で指定境界を取り出し、行全体の境界付き持ち上げを適用した。pushoutの二つの包含で元の脚を回収することを検収し、元の相対latching射そのもののleft anodyne性を得た。

このReedy left anodyne性を§207の対角の定理へ送り、同じ係数射についての対角同型の自然性で、元のsimplicialReplacementMapそのものへ移した。§206の型を変更せずに閉じた。相対latchingの別の大きな射の同型を作り直す部分は、同じ元のpushoutの直接の持ち上げに置き換えた。元の標的の性質や主張の型を弱める変更ではない。

283：包含の法則・境界の成分・境界付きの行全体の持ち上げ・latching自然性の四本の対象ビルド1,658 jobs・終了0、小監査144本1,014宣言・標準三公理のみ（実ハンドル81758・終了0）。284：元の相対latchingの持ち上げと最後のR03f.2の二本の対象ビルド1,661 jobs・終了0、小監査146本1,017宣言・標準三公理のみ（実ハンドル64724・終了0）。両方とも鍵返却済み。個別検査29337・4919・25258の終了0を確認した。

今回85＋56＋60＋82＋95＋30＝408行、累計146本・9,466行／外枠15,000。R03f.2は1,277行。§206の当初見込み650〜1,200行の上端との差＋77行、§212の再見積もり1,169〜1,319行の範囲内。§19の中間定理一つ1,500行との差−223行である。計算上限の変更なし、sorry・独自公理0。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は元のEx∞単位のbar上のleft anodyne性に適用し、元のscaffoldの同じ正方形と元の置換単位を固定した延長をつなぐ。延長の前合成同値性（R03f）と元の共同Hom比較（R03d）はなお別の未完了項目であり、R03f.2だけでnative極限性が得られたとは扱わない。

### 213.1 型

共通入力は `{I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}`。境界付きの持ち上げの共通入力は以下のとおり。証明でのみ用いる `hη sq hd ha` もincludeで宣言の前提に明示的に含めている。

```lean
(η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) (n : ℕ)
{E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
(a : simplicialReplacementRow F n ⟶ E) (b : simplicialReplacementRow G n ⟶ B)
(d : (simplicialReplacementDegenerateRow G n : SSet.{u}) ⟶ E)
(sq : CommSq a (simplicialReplacementRowMap η n) p b)
(hd : d ≫ p = (simplicialReplacementDegenerateRow G n).ι ≫ b)
(ha : simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫ d =
  (simplicialReplacementDegenerateRow F n).ι ≫ a)
```

#### SimplicialReplacementRowInclusionLaws（85行）

```lean
def simplicialReplacementRowPartInclusion (F : I ⥤ SSet.{u}) (P : Set (ComposableArrows I n))
    (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRowPart F n P

theorem simplicialReplacementRowPartInclusion_inclusion (F : I ⥤ SSet.{u})
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    simplicialReplacementRowPartInclusion n F P σ hσ ≫ (simplicialReplacementRowPart F n P).ι =
      simplicialReplacementRowInclusion F n σ

theorem simplicialReplacementRowPartInclusion_map (η : F ⟶ G)
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    η.app (σ.obj 0) ≫ simplicialReplacementRowPartInclusion n G P σ hσ =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ simplicialReplacementRowPartMap η n P

theorem simplicialReplacementRowInclusion_map (η : F ⟶ G) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowMap η n =
      η.app (σ.obj 0) ≫ simplicialReplacementRowInclusion G n σ

theorem simplicialReplacementRow_hom_ext {E : SSet.{u}}
    (f g : simplicialReplacementRow F n ⟶ E)
    (h : ∀ σ, simplicialReplacementRowInclusion F n σ ≫ f =
      simplicialReplacementRowInclusion F n σ ≫ g) : f = g

theorem simplicialReplacementRowDesc_inclusion
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowDesc F n s = s.inj σ

theorem simplicialReplacementRowPart_hom_ext (P : Set (ComposableArrows I n)) {E : SSet.{u}}
    (f g : (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ E)
    (h : ∀ σ hσ, simplicialReplacementRowPartInclusion n F P σ hσ ≫ f =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ g) : f = g
```

#### SimplicialReplacementRowBoundaryComponents（56行）

```lean
theorem simplicialReplacementRowBoundary_component (σ : ComposableArrows I n) :
    ∃ l : G.obj (σ.obj 0) ⟶ E,
      η.app (σ.obj 0) ≫ l = simplicialReplacementRowInclusion F n σ ≫ a ∧
      l ≫ p = simplicialReplacementRowInclusion G n σ ≫ b ∧
      ∀ hσ : σ ∈ (nerve I).degenerate n,
        l = simplicialReplacementRowPartInclusion n G ((nerve I).degenerate n) σ hσ ≫ d
```

#### SimplicialReplacementRowBoundaryLift（60行）

```lean
theorem simplicialReplacementRowBoundary_lift :
    ∃ l : simplicialReplacementRow G n ⟶ E,
      simplicialReplacementRowMap η n ≫ l = a ∧ l ≫ p = b ∧
      (simplicialReplacementDegenerateRow G n).ι ≫ l = d
```

#### SimplicialReplacementRowLatchingNaturality（82行）

```lean
theorem simplicialReplacementRowLatchingIso_hom (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom = simplicialReplacementLatchingToDegenerate F n

theorem simplicialReplacementRowLatchingIso_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).hom ≫ (simplicialReplacementDegenerateRow F n).ι =
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F)

theorem simplicialReplacementRowLatchingLeg_map {F G : I ⥤ SSet.{u}} (η : F ⟶ G)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) :
    simplicialReplacementRowMap η j.obj.left.unop.len ≫ simplicialReplacementRowLatchingLeg G n j =
      simplicialReplacementRowLatchingLeg F n j ≫
        simplicialReplacementRowPartMap η n ((nerve I).degenerate n)

theorem simplicialReplacementRowLatchingIso_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η) ≫
      (simplicialReplacementRowLatchingIso G n).hom =
    (simplicialReplacementRowLatchingIso F n).hom ≫
      simplicialReplacementRowPartMap η n ((nerve I).degenerate n)

theorem simplicialReplacementRowLatchingIso_inv_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    simplicialReplacementRowPartMap η n ((nerve I).degenerate n) ≫
      (simplicialReplacementRowLatchingIso G n).inv =
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingEvaluation simplexOp (Opposite.op ⦋n⦌)).map (simplicialReplacementRowsMap η)

theorem simplicialReplacementRowLatchingIso_inv_inclusion (F : I ⥤ SSet.{u}) :
    (simplicialReplacementRowLatchingIso F n).inv ≫
      (latchingComparison simplexOp (Opposite.op ⦋n⦌)).app (simplicialReplacementRows F) =
      (simplicialReplacementDegenerateRow F n).ι
```

#### SimplicialReplacementReedyLeftAnodyne（95行）

```lean
theorem simplicialReplacementRowsMap_relative_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (relativeLatchingMap simplexOp (Opposite.op ⦋n⦌)
      (simplicialReplacementRowsMap η))

theorem simplicialReplacementRowsMap_reedy_leftAnodyne :
    reedyLeft simplexOp leftAnodyneExtensions (simplicialReplacementRowsMap η)
```

#### SimplicialReplacementLeftAnodyne（30行）

```lean
theorem simplicialReplacementMap_leftAnodyne
    {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}
    (η : F ⟶ G) (hη : ∀ i, leftAnodyneExtensions (η.app i)) :
    leftAnodyneExtensions (simplicialReplacementMap η)
```

## 214. 元のEx∞係数単位のbar上のleft anodyne性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f・R03d・R02・R03は未完了。

R03f.2を元のgrothendieckKanCoefficientUnitと元のexInfinityUnit_leftAnodyneへ適用した。同じCat図式の同じEx∞単位からのsimplicialReplacementMapそのものがleft anodyneである。既存の単位の性質の適用であり、新しい中間の数学的定理の追加ではない。

285：新規一本の対象ビルド1,948 jobs・終了0、小監査147本1,018宣言・標準三公理のみ。実ハンドル4709の終了0を確認し、鍵返却済み。個別検査99542も終了0。今回29行、累計147本・9,495行／外枠15,000。実ファイルの機械的な再集計で、§213のBoundaryComponentsの一行の誤算を修正した。R03f.2は21本1,277行、§213までの累計は9,466行。主張や型の変更ではない。

元のscaffoldの同じ正方形へこのleft anodyne性をつなぐため、既存のRelativeFunctorOverEquivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalenceを確認した。標的がquasicategoryなら、定義域の充填性や比較射の単射性を課さず、任意のleft fibrationへの同じ相対関手空間の制限が同値である。cofinalFunctorSpace/cofinalFunctorPreは同じfiberと前合成で定義されているため、この既存の定理を同じ構成の定義の照合でcofinal性の検査へ移す短い経路を試す。未検証の照合を仮定として使わない。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 214.1 型（29行）

#### GrothendieckKanBarLeftAnodyne（29行）

```lean
theorem grothendieckKanCoefficientBarMap_leftAnodyne
    {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u}) :
    leftAnodyneExtensions (simplicialReplacementMap (grothendieckKanCoefficientUnit F))
```

## 215. 元の比較射と指定単位を固定する延長のcofinal性（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 21（うち追加 9）。R03f・R03d・R02・R03は未完了。

既存のRelativeFunctorOverEquivalence.relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalenceを、同じfiberと前合成で定義されたcofinalFunctorPreへ照合した。quasicategoryを標的とする元の前合成同値が、その同じ射のleft cofinal性の検査を満たすことを、定義の照合と既存のKan相対関手空間の同値の検出だけで得た。新しい数学的な検出条件を仮定していない。

これを元のbar/scaffold正方形へ適用した。元のEx∞単位のbarの射のleft anodyne性、その後のKan係数のscaffoldの前合成同値性、元のCat係数からGrothendieck射列へのscaffoldの前合成同値性を、同じ厳密な正方形の等式と既存のleft cofinalな射の合成・消去則へ渡した。元のgrothendieckKanCoefficientMapそのもののleft cofinal性が得られた。さらに元の置換単位はleft anodyneなので、その同じ単位との合成が元の比較射に等しい任意の延長もleft cofinalとなる。元の比較の射や単位を取り替えていない。

286：定義の照合一本の対象ビルド1,794 jobs・終了0、小監査148本1,019宣言・標準三公理のみ（実ハンドル97086・終了0）。287：元の比較と延長のcofinal性一本の対象ビルド2,492 jobs・終了0、小監査149本1,021宣言・標準三公理のみ（実ハンドル14853・終了0）。両方とも鍵返却済み。個別検査34355・14467の終了0を確認した。

今回28＋57＝85行、累計149本・9,580行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。cofinal性だけから任意の射の前合成同値性を主張しない。残りは、同じ底上のleft fibration間の射としてその検出を行う部分である。

### 215.1 型

Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### PrecompositionCofinality（28行）

```lean
theorem isLeftCofinal_of_precompositionEquivalence
    {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f) :
    IsLeftCofinal f
```

#### GrothendieckKanComparisonCofinality（57行）

```lean
theorem grothendieckKanCoefficientMap_isLeftCofinal :
    IsLeftCofinal (grothendieckKanCoefficientMap F)

theorem grothendieckKanCoefficientLift_isLeftCofinal :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsLeftCofinal f
```

## 216. R03f.3：同じ底上のleft fibration間のcofinal射の検出（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 8／全体 22（うち追加 10）。R03f.3を追加、未証明。

§19の同じまとまり・一つの見込み1,500行以内の枠により、次の独立の中間定理を加える。任意のcofinal射が圏同値だと主張するものではない。同じ底への二つの射が両方ともleft fibrationであり、元の比較射がその底を厳密に保つことを型に持つ。

```lean
theorem isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : IsLeftCofinal f) :
  IsPrecompositionEquivalence f
```

このPropの型は `/private/tmp/CheckISW2CofinalLeftFibComparisonType.lean` で確認した（実ハンドル83289・終了0）。未証明の宣言や仮定を本体へ入れない。置き場所はKerodon/LimitsAndColimits/Cofinality/LeftFibrationComparison.leanなど、一般の同じ底上の検出の節とする。

見込み250〜650行。既存IsLeftCofinal.restrictDiagramを任意の試験left fibrationと同じ底図式qへ適用すると、同じ底上の相対Homの前合成がホモトピー同値となる。試験標的pで恒等射を戻し、逆向きの実射を取る。試験標的qでの同じ前合成の忠実性を使い、二つの合成を同じ恒等射へ結ぶ。相対HomはKanなので、同じ底上の同値の二つの三角形として扱える。元の底がquasicategoryであるため、二つの全空間もquasicategoryである。相対Homから通常の関手空間への同じ包含で三角形を送り、既存の前合成同値のホモトピー逆の判定へ戻す。必要ならisPrecompositionEquivalence_of_homotopyInverseと、各頂点での垂直な辺の可逆性の既存の判定を使う。

これは同じモデルのままcofinal性を前合成同値へ検出する数学的な部分であり、§215の定義の照合の法則として数えない。独立の定理として一つに見積もり、§19の枠を細分で回避しない。半分325行で実測と残りを報告する。

R03f.3が証明できた後に限り、§201の元の単位を固定する延長へ、元の同じ射影の等式と§215のcofinal性を代入し、R03fの全空間の前合成同値を検収する。これがまだ未証明の間はR03f・R03d・native極限性を完了と扱わない。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤aの欄を変更しない。

## 217. R03f.3とR03fの完了：同じ底と指定単位を保つ比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03f.3・R03fを完了。R03d・R02・R03とnative極限性は未完了。

R03f.3は74行で閉じた（見込み250〜650行、上端との差−576行）。相対Homの前合成を既存のcofinal性の検査へ定義どおり照合し、Kan空間の同値に戻した。試験標的pで恒等射を戻して元の底上の逆向きの射gを取り、単位の同型を得る。この同型を通常の関手空間へ忘れる前に、元の底上の後合成relativeFunctorPostでqへの相対Homへ送った。そこで同じ前合成の充満忠実性から余単位を戻す。最後に二つの相対Homの包含で通常のFunctorIsoへ送り、既存のQCatEquivalenceと前合成同値の判定へ渡した。一般のcofinalな射を同値と扱わず、同じ底上の二つのleft fibrationという仮定を使っている。新しいホモトピーの構成や計算上限の引き上げは不要だった。325行の途中報告点に達する前に全証明が閉じた。

元のgrothendieckKanCoefficientLiftへこの検出を適用し、同じ元の射影と置換単位を固定する任意の延長が前合成同値であることを示した。exists_grothendieckKanCoefficientComparisonは§200のR03fの型どおり、元の比較射を延長し、二つの厳密な等式と元の射自身の前合成同値性を同時に持つ。grothendieckKanCoefficientMapは元のgrothWeightedNerveForwardと元のEx∞係数単位のweightedNerveMapの合成を定義に持ち、取り替えていない。

個別検査LeftFibrationComparison（実ハンドル93403）とGrothendieckKanCoefficientComparison（47447）は終了0。288：検出補題の対象ビルド2,208 jobs・終了0、小監査150本1,023宣言・標準三公理のみ（実ハンドル92698・終了0）。289：元の比較と検出補題の対象ビルド2,636 jobs・終了0、小監査151本1,025宣言・標準三公理のみ（実ハンドル67835・終了0）。鍵は返却済み。今回74＋50＝124行、累計151本・9,704行／外枠15,000。証明のコミットは893ee7a94。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は同じ比較を既存のleftClassification_of_precompositionEquivalenceへ渡し、底全体の分類比較を組み立てる。R03dで要求される元の固定始域比較との等式と、native極限性を先取りして完了としない。

### 217.1 型

補助の相対前合成の照合とR03f.3の適用は既存構成の法則・適用であり、別の数学的な一覧項目は増やしていない。Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### LeftFibrationComparison（74行）

```lean
lemma IsLeftCofinal.relativeFunctorOverPre_isQCatEquivalence
    {T E F B : SSet.{u}} (r : T ⟶ B) [LeftFibration r]
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (hc : IsLeftCofinal f) :
    IsQCatEquivalence (relativeFunctorOverPre r (show Over.mk p ⟶ Over.mk q from Over.homMk f hf))

theorem isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : IsLeftCofinal f) :
    IsPrecompositionEquivalence f
```

#### GrothendieckKanCoefficientComparison（50行）

```lean
theorem grothendieckKanCoefficientLift_isPrecompositionEquivalence :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom →
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsPrecompositionEquivalence f

theorem exists_grothendieckKanCoefficientComparison :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F ∧ IsPrecompositionEquivalence f
```

## 218. 同じKan係数の全図式と元のnative全分類の接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のR03fの存在から一つの底上の比較射を選び、同じ射について射影・単位の二つの厳密な等式と前合成同値性を記録した。これを既存のleftClassification_of_precompositionEquivalenceへ渡し、底全体のnative分類のFunctorIsoを得た。対象ごとに同型を選んだものではない。

native分類とstrict transportの分類の接続には短い既存の経路があった。同じnerve上の射影pに対して、leftStraighteningInfinityDiagram_representationIsoとnerveStraighteningRepresentationIsoの両方を、同じnerveLeftTransportRepresentation pへ適用する。二つの全関手同型の合成だけでnative分類と候補を比較できる。その後、元のweightedNerveStraighteningUnitIsoを合成する。同じEx∞係数をKanObject値へ記録し直してこれを適用し、その同じ全係数図式から元のGrothendieck置換のnative分類への全FunctorIsoができた。この部分は既存の分類移送・単位・合成の法則であり、新しい独立の数学的な一覧項目は増やしていない。

個別検査：GrothendieckKanClassificationの最初の版96770・終了0、native/strict分類の接続61750・終了0、二本を結合した最終版17493・終了0。290：最初の版の対象ビルド3,328 jobs・終了0、小監査152本1,033宣言・標準三公理のみ（実ハンドル79144・終了0）。291：最終版の二本と直接importerの対象ビルド3,329 jobs・終了0、小監査153本1,045宣言・標準三公理のみ（実ハンドル61295・終了0）。鍵返却済み。今回87＋41＝128行、累計153本・9,832行／外枠15,000。

sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。残る正規化では、sourceFrameElementsFamilyのfiberが元のElementsの反対圏であることと、全SourceFrameArrowElementsのfiberの向きを区別する。次に既存のKan係数のedgewise反転比較・Ex∞単位・反転の弱同値保存を全図式へ合成する係数移送の法則を試す。型の案は次のとおり（見込み100〜220行）。

```lean
def kanHomFamilyOppositeComparisonIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent F)
      (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
```

ここで反転するのは値の単体集合のみで、底Cとその全射は保つ。元の係数FへEx∞単位を適用し、その反転と同じEx∞によるKan化を取る。Kan化後の値とその反転の比較には既存kanDiagramOppositeComparisonIsoを使い、同じ二つの自然変換の反転可能性を全関手圏で合成する。単純にFとF.opが厳密に同じとはしない。元のroof比較との等式が証明できるまでR03dを完了と扱わない。

### 218.1 型

Grothendieck側の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### GrothendieckKanClassification（87行）

```lean
def grothendieckKanCoefficientComparison :
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ⟶
        weightedNerve (grothendieckKanCoefficients F)

theorem grothendieckKanCoefficientComparison_projection :
    grothendieckKanCoefficientComparison F ≫
      weightedNerveProjection (grothendieckKanCoefficients F) =
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom

theorem grothendieckKanCoefficientComparison_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        grothendieckKanCoefficientComparison F = grothendieckKanCoefficientMap F

theorem grothendieckKanCoefficientComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckKanCoefficientComparison F)

def grothendieckKanReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
      (leftStraighteningInfinityDiagram
        (weightedNerveProjection (grothendieckKanCoefficients F)))

def grothendieckKanCoefficientDiagram : I ⥤ KanObject.{u}

def grothendieckKanNativeClassificationUnitIso :
    FunctorIso (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram F))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget F)))).hom)
```

#### NativeNerveStraighteningComparison（41行）

```lean
def leftStraighteningInfinityDiagram_nerveCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningCandidate p)

def weightedNerveNativeStraighteningUnitIso
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (leftStraighteningInfinityDiagram (weightedNerveProjection (F ⋙ kanObjectForget)))
```

## 219. 全係数の反転と元の反対要素nerveの終端augmentationの接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§218の係数移送の法則を75行で閉じた（見込み100〜220行）。既存kanDiagramOppositeComparisonIsoでKan化後の値だけを反転し、元のEx∞単位とその反転の全自然変換をKan化した全関手同型を合成した。反転した単位の弱同値性は既存opposite_map_isWeakHomotopyEquivalenceを使う。底の圏や全作用素を変えず、値ごとに逆射を選ばない。

次に、既存nerveOppositeMap_naturalityと同じnerveOppositeIsoを全Cat図式に適用し、元のnerveと反対圏のnerveのKan化の全FunctorIsoを50行で記録した。元の全要素nerveの比較では、既存SimplexNerve.functorとSimplexTerminalNerve.functor、同じoppositeIsoをそのまま使う。これらに同じ全係数図式Fを前合成し、元のaugmentationの自然変換と既存augmentation_localized_isIsoをKan化して、元の全要素nerveの係数から元のFの係数への全FunctorIsoを76行で得た。新しい要素圏や反転模型を構成しておらず、既存構成の単位・自然性・係数移送・合成の法則として記録する。一覧の独立の数学的な項目は増やしていない。

この同型が元の固定始域のroof比較と同じものになるという等式はまだ証明していない。全要素圏のfiberと元の反対要素圏を取り違えず、元の単位・augmentation・roofへ戻る正規化はR03dの残りとして保つ。底全体のFunctorIsoは得られたが、これだけでR03d・R02・R03とnative極限性を完了とは扱わない。

個別検査：KanHomFamilyOpposite70713・終了0、KanNerveOppositeFamily90441・終了0、KanElementsFamily28433・終了0。292は必要な既存二モジュールだけの対象ビルド2,729 jobs・終了0（実ハンドル58640）。293：反転係数の対象ビルド2,802 jobs・終了0、小監査154本1,056宣言・標準三公理のみ（86257・終了0）。294：全Cat図式の反転の対象ビルド2,804 jobs・終了0、小監査155本1,064宣言・標準三公理のみ（85024・終了0）。295：全要素nerveの係数移送の対象ビルド2,934 jobs・終了0、小監査156本1,078宣言・標準三公理のみ（33179・終了0）。いずれも鍵をビルド・小監査の間だけ取り、終了と返却を確認した。

今回75＋50＋76＝201行、累計156本・10,033行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。今後は元の全source frameの要素圏をR03fの同じ底の分類へ接続し、同じ全augmentationの逆からのtwisted pairingと照合する。

### 219.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、全Cat図式の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

#### KanHomFamilyOpposite（75行）

```lean
lemma kanHomFamilyUnit_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (exInfinityUnit.app X)

def kanDiagramExInfinityUnitIso {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (kanHomFamilyCoherent (F ⋙ kanObjectForget))

def kanHomFamilyOppositeUnit {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    F ⋙ SSet.opFunctor ⟶ (kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget

def kanHomFamilyOppositeUnitIso {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((kanHomFamily F ⋙ kanObjectOpFunctor) ⋙ kanObjectForget))

def kanHomFamilyOppositeComparisonIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) :
    FunctorIso (kanHomFamilyCoherent F)
      (kanHomFamilyCoherent (F ⋙ SSet.opFunctor))
```

#### KanNerveOppositeFamily（50行）

```lean
def catNerveOppositeFamilyMap :
    (F ⋙ nerveFunctor) ⋙ SSet.opFunctor ⟶ (F ⋙ Cat.opFunctor) ⋙ nerveFunctor

lemma catNerveOppositeFamilyMap_weak (i : I) :
    IsWeakHomotopyEquivalence ((catNerveOppositeFamilyMap F).app i)

def catNerveOppositeFamilyUnitIso :
    FunctorIso (kanHomFamilyCoherent ((F ⋙ nerveFunctor) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor))

def catNerveOppositeFamilyIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ nerveFunctor))
      (kanHomFamilyCoherent ((F ⋙ Cat.opFunctor) ⋙ nerveFunctor))
```

#### KanElementsFamily（76行）

```lean
abbrev simplexElementsNerveDiagram : I ⥤ SSet.{u}

def simplexElementsOppositeNerveIso :
    (simplexElementsNerveDiagram F) ⋙ SSet.opFunctor ≅ F ⋙ SimplexTerminalNerve.functor

def simplexElementsOppositeNerveKanIso :
    FunctorIso (kanHomFamilyCoherent ((simplexElementsNerveDiagram F) ⋙ SSet.opFunctor))
      (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor))

def simplexElementsOppositeAugmentation : F ⋙ SimplexTerminalNerve.functor ⟶ F

lemma simplexElementsOppositeAugmentation_weak (i : I) :
    IsWeakHomotopyEquivalence ((simplexElementsOppositeAugmentation F).app i)

def simplexElementsOppositeAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (F ⋙ SimplexTerminalNerve.functor))
      (kanHomFamilyCoherent F)

def simplexElementsKanAugmentationIso :
    FunctorIso (kanHomFamilyCoherent (simplexElementsNerveDiagram F))
      (kanHomFamilyCoherent F)
```

## 220. 全要素圏の同じGrothendieck表示と、元の置換の係数移送則（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元の全係数Fの各要素圏を、Homだけ同じ宇宙へ持ち上げてCat値図式にした。そのGrothendieck構成と、Fをuncurryした全二重添字の要素圏は、同じ底・単体次数・ラベルと同じ元の射を並べ直す圏同値である。順方向・逆方向、単位・余単位の全自然性、元の底への二つの射影の厳密な等式を148行で示した。比較を自由な圏同値として選んだものではなく、両方向とも元のラベルと元の底の射・単体作用素を保つ。Grothendieckの合成に含まれる等式輸送は、元の単体次数への射影関手のmap_comp・eqToHom_mapで計算した。同じ二つの既存の構成の表示の照合であり、新しい数学的な一覧項目は増やしていない。

次に、既存の連続left-fibration置換が元のcofinalな底上の射を前合成同値へ送ることを46行で記録した。元の置換単位の自然性を同じ全空間の射の等式として使い、元の単位のleft anodyne性、cofinal性の合成・消去則、検証済みR03f.3の同じ底上の検出を合成した。置換も単位も選び直していない。標的の全空間が準圏である場合の、元の底上の前合成同値を移す版も付けた。この仮定は型に明記し、任意の非準圏の標的で同じ検出ができるとは主張していない。これは元の置換関手・単位の自然性と同じ底上の移送の法則であり、独立の数学的な一覧項目は増やしていない。

個別検査：全要素圏の圏同値と射影の最終版13688・終了0、元の置換の移送則79822・終了0。296：全要素圏のGrothendieck表示の対象ビルド1,125 jobs・終了0、小監査157本1,102宣言・標準三公理のみ（実ハンドル89214・終了0）。297：元の置換の移送則の対象ビルド2,219 jobs・終了0、小監査158本1,104宣言・標準三公理のみ（実ハンドル88369・終了0）。鍵返却済み。

今回148＋46＝194行、累計158本・10,227行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。次は、この同じ圏同値のnerveを同じ底のOverの射とし、元の置換へ送ってR03fの全分類へ接続する。元の固定始域のroof比較との等式は依然R03dの残りであり、native極限性の完了は主張しない。

### 220.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### SimplicialElementsGrothendieck（148行）

```lean
def simplicialElementsCatDiagram : I ⥤ Cat.{u,u}

abbrev SimplicialTotalElements

def simplicialTotalElementsProjection : SimplicialTotalElements F ⥤ I

lemma uliftElements_eqToHom_hom {K : SSet.{u}} {x y : ULiftHom.{u} K.Elements}
    (h : x = y) : (eqToHom h).down.hom = eqToHom (congrArg (fun z => z.obj) h)

def simplicialElementsGrothendieckForward :
    Grothendieck (simplicialElementsCatDiagram F) ⥤ SimplicialTotalElements F

def simplicialElementsGrothendieckObject (X : SimplicialTotalElements F) :
    Grothendieck (simplicialElementsCatDiagram F)

def simplicialElementsGrothendieckHom {X Y : SimplicialTotalElements F} (f : X ⟶ Y) :
    simplicialElementsGrothendieckObject F X ⟶ simplicialElementsGrothendieckObject F Y

def simplicialElementsGrothendieckInverse :
    SimplicialTotalElements F ⥤ Grothendieck (simplicialElementsCatDiagram F)

def simplicialElementsGrothendieckEquivalence :
    Grothendieck (simplicialElementsCatDiagram F) ≌ SimplicialTotalElements F

theorem simplicialElementsGrothendieckForward_projection :
    simplicialElementsGrothendieckForward F ⋙ simplicialTotalElementsProjection F =
      Grothendieck.forget (simplicialElementsCatDiagram F)

theorem simplicialElementsGrothendieckInverse_projection :
    simplicialElementsGrothendieckInverse F ⋙ Grothendieck.forget (simplicialElementsCatDiagram F) =
      simplicialTotalElementsProjection F
```

#### ContinuousLeftFibrationEquivalenceMap（46行）

```lean
theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} (f : X ⟶ Y)
    (hc : IsLeftCofinal f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left

theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} [Quasicategory Y.left]
    (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left
```

## 221. 元の全要素圏の置換単位を保つnative全分類への接続（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§220の同じ圏同値の逆方向のnerveを、同じ底nerve I上のOverの射にした。元の射そのものの前合成同値性は既存nerveQCatEquivalenceに同じ圏同値を渡して得た。次に元のcontinuousLeftFibrationReplacementでこの同じOverの射を送り、元の二つの置換単位との厳密な正方形を、その同じ単位の自然性から得た。§220の置換の移送則と既存leftClassification_of_precompositionEquivalenceを適用し、全要素圏の元の置換のnative分類と同じGrothendieck表示の元の置換のnative分類を、底全体のFunctorIsoで比較した。

これにR03fから得た同じGrothendieck係数の全分類単位を合成した。得られたsimplicialElementsNativeClassificationUnitIsoの始域は、各要素圏のHomを持ち上げた同じCat図式から来るgrothendieckKanCoefficientDiagramであり、終域は元の全二重添字の要素圏の元の置換のnativeな全分類である。元のFそのもののKan化と厳密に同じとは主張していない。Homの宇宙持ち上げを既存の全nerve同型で外し、§219の反対要素nerveの同じaugmentationへつなぐ照合は、次の接続として残す。

同じ底上の圏同値・nerve・置換・分類移送・R03fの既存の構成を合成したものであり、独立の数学的な一覧項目は増やしていない。元の固定始域のroof比較との全FunctorIsoの等式は、依然R03dの残り。元の全augmentationの逆を使ったtwisted pairingと、この同じ全要素分類の単位を同じ底上で照合してから、その制限を元の固定始域比較へ戻す必要がある。各fiberの同値や底全体のFunctorIsoの存在だけで、その正規化の等式まで証明した扱いにはしない。

個別検査の最終版8707・終了0。298：対象ビルド3,336 jobs・終了0、小監査159本1,115宣言・標準三公理のみ（実ハンドル40611・終了0）。鍵返却済み。今回90行、累計159本・10,317行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 221.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### SimplicialElementsClassification（90行）

```lean
def simplicialElementsGrothendieckOverMap :
    Over.mk (nerveMap (simplicialTotalElementsProjection F)) ⟶
      Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F)))

theorem simplicialElementsGrothendieckOverMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckOverMap F).left

def simplicialElementsGrothendieckReplacementMap

theorem simplicialElementsGrothendieckReplacementMap_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫
        (simplicialElementsGrothendieckReplacementMap F).left =
      (simplicialElementsGrothendieckOverMap F).left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).left

theorem simplicialElementsGrothendieckReplacementMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (simplicialElementsGrothendieckReplacementMap F).left

def simplicialElementsGrothendieckReplacementClassificationIso :
    FunctorIso
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (Grothendieck.forget (simplicialElementsCatDiagram F))))).hom)

def simplicialElementsNativeClassificationUnitIso :
    FunctorIso
      (kanDiagramCoherentNerve (grothendieckKanCoefficientDiagram (simplicialElementsCatDiagram F)))
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
```

## 222. 元の全係数図式へ戻したnative全要素分類（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§221の始域に残っていたHomの持ち上げを、元の同じ全射列へup・downを適用する実同型で外した。元の圏の関手への自然性も同じ射列で計算している。元のnerveと同じ宇宙で比較できるため、係数に新たな外側のULiftは入れない。既存のMixedNerveやNerveULiftHomは変更せず、一般の宇宙の表記で同じup・downの法則を56行で記録した。

この同じ実同型を全係数の要素圏に自然に適用し、Kan化の全関手同型へ送った。§219の元の全要素nerveから反対要素nerveの元の終端augmentationへの比較と、§221の元の単位を保つnative全分類比較を合成した。totalElementsNativeClassificationIsoの始域は元のFのkanHomFamilyCoherentそのものであり、終域は同じFをuncurryした全要素圏の元の連続left-fibration置換のnative全分類である。型つきの定義は60行。点ごとの比較への弱化や、異なる置換・augmentationの選択はしていない。既存構成の宇宙・係数移送と合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

元の単位と元の反対要素augmentationを使っているが、その比較が元の固定始域のroof比較の全FunctorIsoと同じになるというR03dの正規化は、まだ証明していない。今回の全分類の接続の存在を、その等式の代用にはしない。

個別検査：Homの宇宙比較24895・終了0、二本を結合した全係数比較76861・終了0。299：二本と直接importerの対象ビルド3,564 jobs・終了0、小監査161本1,131宣言・標準三公理のみ（実ハンドル75950・終了0）。鍵返却済み。今回56＋60＝116行、累計161本・10,433行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 222.1 型

全係数の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。

#### NerveHomUniverseIso（55行）

```lean
def nerveHomUniverseIso : nerve (ULiftHom.{max u v} C) ≅ nerve C

theorem nerveHomUniverseIso_naturality {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    nerveMap (ULiftHom.down.{v,u,max u v} ⋙ F ⋙ ULiftHom.up) ≫
      (nerveHomUniverseIso D).hom = (nerveHomUniverseIso C).hom ≫ nerveMap F
```

#### TotalElementsNativeClassification（61行）

```lean
def totalElementsNerveCoefficientIso :
    simplicialElementsCatDiagram F ⋙ nerveFunctor ≅ simplexElementsNerveDiagram F

def totalElementsNerveCoefficientKanIso :
    FunctorIso (kanHomFamilyCoherent (simplicialElementsCatDiagram F ⋙ nerveFunctor))
      (kanHomFamilyCoherent (simplexElementsNerveDiagram F))

def totalElementsNativeClassificationIso :
    FunctorIso (kanHomFamilyCoherent F)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve I)).obj
          (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).hom)
```

## 223. BEの元の第三図式への適用と同じ全実射の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

全source-frame Homの両変数の添字をAsSmallで、係数だけをULiftで同じ宇宙に持ち上げた全図式から、同じ元のSourceFrameArrowElementsへのdownを52行で記録した。対象では元の両変数・単体次数とラベルのdownを取り、射では元の両変数の射・単体作用素を保つ。元のパラメーターへの射影の厳密な等式と、回収する実射が元のULiftされたラベルのdownそのものという等式を付けた。新しい全要素や射の模型は選んでいない。

これをBEの元のprobeに関手的source frameを適用した図式と、元の標的置換へ適用した。strictBETotJointSourceCoefficientsは元のstrictBETotJointFirstSpanDiagram A 3のAsSmall.downによる前合成そのものであり、その等式はrflである。元の第三図式から、同じ全要素圏の元の置換のnativeな全分類への全FunctorIsoができた。さらに元のstrictBETotJointFirstSpanComparisonを合成し、両変数raw Homから同じnative全分類への全FunctorIsoを得た。BE固有の適用は72行。既存構成の全係数表示・単位・移送と合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

この比較の終域は元の全source-frame要素圏のnativeな全分類であり、正本の二変数Hom∞そのものへの比較はまだ組み立てていない。次は、回収した同じ実射の全pairingと同じ両端を既存twistedPairingNerveMapへ渡し、元の全augmentationの逆による両端の移送へ進む。元の固定始域のroof比較との全FunctorIsoの等式が閉じるまでR03dの完了としない。

個別検査：全要素のdown11509・終了0、BEへの適用を二本結合した検査67659・終了0。300：対象ビルド10,697 jobs・終了0、小監査163本1,153宣言・標準三公理のみ（実ハンドル11457・終了0）。対象とその依存だけのビルドでありrootビルドや公式の大監査は実行していない。鍵はビルド・小監査の間だけ取り、終了と返却を確認した。

今回52＋72＝124行、累計163本・10,557行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 223.1 型

全source-frame係数の共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。BE側は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### LiftedSourceFrameElements（52行）

```lean
abbrev liftedSourceFrameIndex

def liftedSourceFrameCoefficients : liftedSourceFrameIndex (C := C) ⥤ SSet.{max u v}

def liftedSourceFrameElementsDown :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ SourceFrameArrowElements Q R

theorem liftedSourceFrameElementsDown_parameters :
    liftedSourceFrameElementsDown Q R ⋙ sourceFrameArrowParameters Q R =
      Functor.Elements.π (Functor.uncurry.obj (liftedSourceFrameCoefficients Q R)) ⋙
        (AsSmall.down.prod (𝟭 SimplexCategoryᵒᵖ))

theorem liftedSourceFrameElementsDown_value
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    sourceFrameArrowValue Q R ((liftedSourceFrameElementsDown Q R).obj X) = X.val.down
```

#### StrictDiagramTotJointSourceElements（72行）

```lean
def strictBETotJointSourceFrame :
    (operad A).Algebra ⥤ SimplexCategory ⥤ (operad A).Algebra

def strictBETotJointSourceCoefficients : strictBETotJointHomIndex A ⥤ SSet.{u+1}

theorem strictBETotJointSourceCoefficients_eq :
    strictBETotJointSourceCoefficients A =
      AsSmall.down ⋙ strictBETotJointFirstSpanDiagram A 3

abbrev StrictBETotJointSourceElements

def strictBETotJointSourceElementsProjection :
    StrictBETotJointSourceElements A ⥤ strictBETotJointHomIndex A

def strictBETotJointSourceElementsDown

def strictBETotJointSourceElementsClassificationIso :
    FunctorIso (strictBETotJointFirstSpanCoherent A 3)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom)

def strictBETotJointRawSourceElementsClassificationIso :
    FunctorIso (strictBETotJointRawHomCoherent A)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom)
```

## 224. 同じ全source-frame実射のnative twisted pairingと厳密な両端（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§223で回収した同じ全実射の始域・標的をAsSmallの同じ宇宙へ持ち上げ、任意の全要素の射における同じ反変・共変の四角形を元のsourceFrameArrowValue_naturalityで検証した。元の射の全pairingに既存twistedPairingNerveMapを適用した。同じpairingの二射影は元の始域・標的の全nerve写像そのものであり、既存の全射影式を適用して厳密な等式を得た。64行。

これをBEの同じ元の全source-frame実射へ適用し、元のstrictBETotModelSourceのedgewiseSubdivisionMapを合成した。得られたstrictBETotJointSourceNativePairingは、同じ全要素圏のnerveからTwistedArrow (CAlg_R A)への全単体に自然な写像である。元の始域・標的を同じモデル源へ送った二変数の底への厳密な射影式を、既存twistedArrowProjection_naturalityと元の全pairingの射影式を合成して得た。BE固有の適用は60行。模型の中身を新しく使う構成ではなく、既存の同じモデル源とtwisted pairingの全自然性・係数移送の法則の適用であり、独立の数学的な一覧項目は増やしていない。

このpairingの始域端点は元のsource-frameの各次数の対象であり、まだ元の試験対象Xへ変更していない。§188の元の全augmentationの同じ逆を全要素のパラメーターへ引き戻し、その端点の変更を行う。元の両変数のnative入力への厳密化と元の固定始域のroof比較との等式は、R03dの残りとして保つ。今回のpairingの存在と厳密な射影式だけからR03dやnative極限性の完了を主張しない。

個別検査：元の全pairing5427・終了0、BEへの適用を二本結合した検査1985・終了0。301：対象ビルド10,708 jobs・終了0、小監査165本1,166宣言・標準三公理のみ（実ハンドル18475・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

今回64＋60＝124行、累計165本・10,681行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 224.1 型

一般側の共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。BE側は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### LiftedSourceFramePairing（64行）

```lean
def liftedSourceFrameArrowDomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ (AsSmall.{max u v} C)ᵒᵖ

def liftedSourceFrameArrowCodomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ AsSmall.{max u v} C

def liftedSourceFrameArrowValue
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    ((liftedSourceFrameArrowDomain Q R).obj X).unop ⟶
      (liftedSourceFrameArrowCodomain Q R).obj X

theorem liftedSourceFrameArrowValue_naturality
    {X Y : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)} (f : X ⟶ Y) :
    ((liftedSourceFrameArrowDomain Q R).map f).unop ≫ liftedSourceFrameArrowValue Q R X ≫
      (liftedSourceFrameArrowCodomain Q R).map f = liftedSourceFrameArrowValue Q R Y

def liftedSourceFramePairing :
    nerve (SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) ⟶
      TwistedArrow (nerve (AsSmall.{max u v} C))

theorem liftedSourceFramePairing_projection :
    liftedSourceFramePairing Q R ≫ twistedArrowProjection (nerve (AsSmall.{max u v} C)) =
      CartesianMonoidalCategory.lift
        (nerveMap (liftedSourceFrameArrowDomain Q R) ≫
          (nerveOppositeIso (C := AsSmall.{max u v} C)).inv)
        (nerveMap (liftedSourceFrameArrowCodomain Q R))
```

#### StrictDiagramTotJointSourcePairing（60行）

```lean
def strictBETotJointSourcePairing :
    nerve (StrictBETotJointSourceElements A) ⟶
      TwistedArrow (nerve (AsSmall.{u+1} (operad A).Algebra))

def strictBETotJointSourceNativePairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A)

def strictBETotJointSourceNativePairingBase :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op ⊗ CAlg_R A

theorem strictBETotJointSourceNativePairing_projection :
    strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A) =
      strictBETotJointSourceNativePairingBase A
```

## 225. 元の全augmentationの同じ比較を全実射の始域へ引き戻す（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のnerve反転同型の逆の自然性を、元の順写像の自然性と同じ二つの逆を合成する法則として30行で記録した（reassoc生成の同じ末尾付きの等式を含む）。元の全実射の始域と単体次数を、§188の全augmentationの反対添字へ送る同じ関手を53行で記録した。その添字への評価の引き戻しは元の実射の始域そのものでrfl、定値端の引き戻しは元の試験対象の射影へ戻り、元の定値図式の恒等射の合成則で示した。頂点の同一視だけではなく、全関手の等式である。

同じ反対添字のnerveと元のnerve反転同型の逆を、元の全augmentationのFunctorIsoのopへの前合成に使った。両端は同じ評価・定値の全関手の等式と反転同型の全自然性で、それぞれ元の実射の始域と元の試験対象のnativeな反変の全図式へ厳密に戻る。strictBETotJointSourceAugmentationDomainIsoは元の一つの全augmentationの比較をそのまま引き戻したものであり、逆を各対象や各単体で独立に選ばない。端点比較の適用は89行。既存構成の自然性・単位・反転・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

この同型の逆を元の全pairingへ作用させ、元の試験対象を始域とする同じ正本Hom∞の全比較へ戻す部分はまだ残る。またpairingの標的は元のright-frame置換後なので、元の全標的置換単位の同じ逆による端点比較も必要。元の固定始域のroof比較との全FunctorIsoの等式と、同じ底上のnative Homへの比較の同値性は未証明であり、R03d・R02・R03の完了とは扱わない。

個別検査：反転同型の逆の自然性33516・終了0、元の全augmentationの添字と両端55221・終了0、三本を結合した最終の端点比較79466・終了0。302：対象ビルド10,713 jobs・終了0、小監査168本1,183宣言・標準三公理のみ（実ハンドル77879・終了0）。鍵返却済み。今回30＋53＋89＝172行、累計168本・10,853行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 225.1 型

BE側の共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。反転同型の逆の自然性にはreassoc生成の同じ末尾付きの等式もある。

#### NerveOppositeInverseNaturality（30行）

```lean
theorem nerveOppositeIso_inv_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) :
    nerveMap F.op ≫ (nerveOppositeIso (C := D)).inv =
      (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map (nerveMap F)
```

#### StrictDiagramTotJointSourceParameters（53行）

```lean
def strictBETotJointSourceParameterIndex :
    StrictBETotJointSourceElements A ⥤ (strictBETotJointSourceFrameIndex A)ᵒᵖ

theorem strictBETotJointSourceParameterIndex_evaluation :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameEvaluation A).op =
      FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))

theorem strictBETotJointSourceParameterIndex_constant :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameConstant A).op =
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomSourceIndex A
```

#### StrictDiagramTotJointSourceAugmentationComparison（89行）

```lean
def strictBETotJointSourceNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op

def strictBETotJointSourceOriginalNativeDomain :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op

def strictBETotJointSourceAugmentationInput :
    nerve (StrictBETotJointSourceElements A) ⟶ (nerve (strictBETotJointSourceFrameIndex A)).op

theorem strictBETotJointSourceAugmentationInput_evaluation :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫
        strictBETotModelSource A) = strictBETotJointSourceNativeDomain A

theorem strictBETotJointSourceAugmentationInput_constant :
    strictBETotJointSourceAugmentationInput A ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointSourceFrameConstant A) ≫
        strictBETotModelSource A) = strictBETotJointSourceOriginalNativeDomain A

def strictBETotJointSourceAugmentationDomainIso :
    FunctorIso (strictBETotJointSourceNativeDomain A)
      (strictBETotJointSourceOriginalNativeDomain A)
```

## 226. 元の全標的置換単位の同じ逆による端点の回収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

元のstrictBETotModelSourceが全弱自然変換を全FunctorIsoへ送る法則を41行で記録した。元の局所化の弱辺反転と既存nerveTransformationPostIsoをその同じ自然変換へ適用する。元の全自然変換を別の辺や成分に取り替えず、元のモデル源を保つ。§188の全augmentationで用いた同じ既存の反転手順を、一般の全自然変換に記す係数移送の法則である。

元のrightFrameReplacementと元のrightFrameReplacementUnitを、同じAsSmallのモデル源の添字に記録した。各成分が元のモデル弱同値であることは、同じrightFrameReplacementUnit_trivialCofibrationの第二成分を使う。これを上の同じモデル源の全弱自然変換の反転へ渡し、全標的置換単位自身の全FunctorIsoを得た。元の全実射の標的の関手は、元の全標的射影へこの同じ置換を合成したものとrflで一致する。その同じ全標的単位の比較を元の全標的射影へ前合成し、逆を取ることで、実射の置換後の標的から元の標的への全FunctorIsoを得た。83行。

§225の始域比較と今回の標的比較がそろったが、二つを同じ二変数のnativeな底の比較へまとめる部分と、その比較を元の全pairingの同じ底への射へ厳密化する部分はまだ残る。元の固定始域のroof比較との全FunctorIsoの等式と、同じ底上の比較の同値性も未証明。既存の全単位・弱辺反転・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。型に関する既存の仮定や範囲は弱めていない。

個別検査：全弱自然変換の移送5039・終了0、二本を結合した最終の標的比較11777・終了0。303：対象ビルド10,712 jobs・終了0、小監査170本1,200宣言・標準三公理のみ（実ハンドル58672・終了0）。鍵返却済み。今回41＋83＝124行、累計170本・10,977行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 226.1 型

共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory Aを局所的に使う。全標的置換側は元のmappingCofibrantFactorization Aも局所的に使う。

#### StrictDiagramTotModelWeakTransformation（41行）

```lean
def strictBETotModelWeakTransformationIso
    {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (operad A).Algebra (AsSmall.down.map (η.app j))) :
    FunctorIso (nerveMap F ≫ strictBETotModelSource A) (nerveMap G ≫ strictBETotModelSource A)
```

#### StrictDiagramTotJointTargetReplacement（83行）

```lean
def strictBETotTargetReplacement :
    AsSmall.{u+1} (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra

def strictBETotTargetReplacementUnit :
    𝟭 (AsSmall.{u+1} (operad A).Algebra) ⟶ strictBETotTargetReplacement A

theorem strictBETotTargetReplacementUnit_weak (Y : AsSmall.{u+1} (operad A).Algebra) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotTargetReplacementUnit A).app Y))

def strictBETotTargetReplacementNativeIso :
    FunctorIso (strictBETotModelSource A)
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A)

theorem strictBETotJointSourceCodomain_replacement :
    FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)) =
    strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A ⋙
      strictBETotTargetReplacement A

def strictBETotJointSourceNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A

def strictBETotJointSourceOriginalNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A

def strictBETotJointSourceTargetReplacementIso :
    FunctorIso (strictBETotJointSourceNativeCodomain A)
      (strictBETotJointSourceOriginalNativeCodomain A)
```

## 227. 元の二つの全端点比較を元の二変数native入力へまとめる（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

既存functorHomTensorEquivとその合成則により、二つの全FunctorIsoの同じ順方向・逆方向を直積の二成分として戻し、直積値の全FunctorIsoにする法則を46行で記録した。順逆条件は元の二つの同型の順逆条件と元の二つの射影関手のmap_idへ帰着する。パラメーターの準圏性は要求せず、二つの元の同型を保持する。既存のh Funの直積分解を合成する法則であり、別の数学的な比較の存在を仮定していない。

同じ元のnative pairingの底は、§225・§226の元の始域・標的の全図式の組に厳密に等しい。元の試験対象と元の標的の組は、元の全要素圏からの同じ射影でstrictBETotJointNativeHomInputを前合成したものに厳密に等しい。いずれも全写像の等式を示し、この二つの等式で上の積の同型を移送した。strictBETotJointSourceNativePairingBaseIsoは元の全pairingの底から元の二変数native入力の引き戻しへの全FunctorIsoである。BE固有の適用は60行。既存構成の同じ二つの端点比較・自然性・係数移送・合成の法則として記録し、独立の数学的な一覧項目は増やしていない。

同じ底上の射への補正には既存pathCorrectedFunctorSquareを使えることを確認した。これは指定した元の底のFunctorIsoのpathと、元の成分へのexactComponentIso、およびそのpostcompが元の同型へ戻る等式を保持する。元の二つの端点の逆から作った同じ底の同型をこの既存の補正へ渡し、同じ底上のnative Homの全空間への射を作る。補正後の射の同値性、元の固定始域のroof比較との全FunctorIsoの等式はまだ残る。

個別検査：二同型の積3906・終了0、二本を結合したBEの底の比較29830・終了0。304：必要な既存FunctorHomTensorのみの対象ビルド5,931 jobs・終了0（実ハンドル52371・終了0）。305：二本と直接importerの対象ビルド12,210 jobs・終了0、小監査172本1,217宣言・標準三公理のみ（実ハンドル34181・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

今回46＋60＝106行、累計172本・11,083行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 227.1 型

BE側の共通入力は `(A : Type u) [CommRing A]`、元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。

#### FunctorIsoPairing（46行）

```lean
def functorIsoPair {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    FunctorIso (lift f h) (lift g k)
```

#### StrictDiagramTotJointPairingBaseComparison（60行）

```lean
theorem strictBETotJointSourceNativePairingBase_eq_lift :
    strictBETotJointSourceNativePairingBase A =
      lift (strictBETotJointSourceNativeDomain A) (strictBETotJointSourceNativeCodomain A)

theorem strictBETotJointSourceOriginalNativeEndpoints_eq :
    lift (strictBETotJointSourceOriginalNativeDomain A)
      (strictBETotJointSourceOriginalNativeCodomain A) =
        nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A

def strictBETotJointSourceNativePairingBaseIso :
    FunctorIso (strictBETotJointSourceNativePairingBase A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
```

## 228. 指定された元の端点比較を保つ、同じ底上のnative Homへの実射（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

§227の元の全端点比較の同じ逆を、元のnative pairingの射影へfunctorIsoOfEqで移送し、同じ底のFunctorIsoを指定した。これを既存pathCorrectedFunctorSquareへ渡した。twistedArrowProjectionのleft-fibration性と既存leftFibration_equivalenceLiftingだけを使い、元のpairingを同じ元の二変数native入力の上へ補正した。補正後の射影は元のnative入力の同じ全要素射影による引き戻しに厳密に等しい。

補正後と元のpairingの比較には、指定pathから来る既存exactComponentIsoを使った。そのpostcompは、元の端点比較の逆自身を、同じ厳密な射影の等式のeqToIsoと合成したものに等しい。別の同型を選んだものではなく、この等式をstrictBETotJointSourceCorrectedPairingIso_postcompとして保持する。同じ正本Homの全空間を元のnative入力によるtwistedArrowProjectionのpullbackとして記し、補正後のpairingと元の全要素圏の射影をpullback.liftへ渡した。得られたstrictBETotJointSourceNativeHomMapは、元の全要素圏から同じ元の二変数の底上のnative Hom全空間への実際の全写像である。元の底への射影と補正後のpairingの回収の両方が厳密な等式として成立する。103行。

既存の全端点比較、指定pathの相対持ち上げとpullbackの合成・自然性の法則の適用として記録し、独立の数学的な一覧項目は増やしていない。この全写像がcofinalか、元の置換からの延長が前合成同値かは、今回の存在やpathの等式から先取りしていない。元の固定始域のroof比較との全FunctorIsoの等式もR03dの残り。

個別検査の最終版30336・終了0。306：必要な既存二モジュールのみの対象ビルド1,873 jobs・終了0（実ハンドル82144・終了0）。307：元の指定pathを保つ全写像の対象ビルド12,222 jobs・終了0、小監査173本1,236宣言・標準三公理のみ（実ハンドル30168・終了0）。鍵返却済み。§228までの累計173本・11,186行／外枠15,000。

### 228.1 型

共通入力は `(A : Type u) [CommRing A]`。元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使い、nativeな積の準圏性には既存quasicategory_tensorを適用する。

#### StrictDiagramTotJointPairingCorrection（103行）

```lean
def strictBETotJointSourcePairingBasePathIso :
    FunctorIso
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A))

def strictBETotJointSourcePairingCorrection :
    PathCorrectedFunctorSquare (twistedArrowProjection (CAlg_R A))
      (strictBETotJointSourceNativePairing A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourcePairingBasePathIso A)

def strictBETotJointSourceCorrectedPairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A)

theorem strictBETotJointSourceCorrectedPairing_projection :
    strictBETotJointSourceCorrectedPairing A ≫ twistedArrowProjection (CAlg_R A) =
      nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A

def strictBETotJointSourceCorrectedPairingIso :
    FunctorIso (strictBETotJointSourceCorrectedPairing A) (strictBETotJointSourceNativePairing A)

theorem strictBETotJointSourceCorrectedPairingIso_postcomp :
    (strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (CAlg_R A)) =
      eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A

def strictBETotJointNativeHomTotalSpace : SSet.{u+1}

def strictBETotJointNativeHomProjection :
    strictBETotJointNativeHomTotalSpace A ⟶ nerve (strictBETotJointHomIndex A)

def strictBETotJointSourceNativeHomMap :
    nerve (StrictBETotJointSourceElements A) ⟶ strictBETotJointNativeHomTotalSpace A

theorem strictBETotJointSourceNativeHomMap_projection :
    strictBETotJointSourceNativeHomMap A ≫ strictBETotJointNativeHomProjection A =
      nerveMap (strictBETotJointSourceElementsProjection A)

theorem strictBETotJointSourceNativeHomMap_pairing :
    strictBETotJointSourceNativeHomMap A ≫
      pullback.fst (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A) =
        strictBETotJointSourceCorrectedPairing A
```

## 229. 元の置換単位を固定したnative Homへの延長と終域の全分類（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 22（うち追加 10）。R03d・R02・R03は未完了。

同じ正本Hom全空間の射影のleft-fibration性を、元のtwistedArrowProjectionのleft-fibration性の同じpullbackとして記録した。元の全要素圏のnerveからのstrictBETotJointSourceNativeHomMapを、元の連続left-fibration置換の同じ単位に沿い、既存exists_relativeFunctorExtension_of_leftAnodyneで延長した。exists_strictBETotJointSourceNativeLiftは、元の同じ底への射影の厳密な等式と、元の同じ置換単位との合成がstrictBETotJointSourceNativeHomMapそのものに等しいという厳密な三角形を同時に要求する。別の全写像の存在に取り替えていない。

また同じ正本Hom全空間のnative全分類を、元のstrictBETotJointNativeHomCoherentへつなぐ全FunctorIsoを付けた。既存leftStraighteningInfinityDiagram_baseChangeIsoを元のtwistedArrowProjectionと元の二変数native入力へ適用するだけであり、twistedArrowHomInfinityの定義そのものに戻る。延長と終域の比較を合わせて66行。既存の相対延長・単位・引き戻し・全分類の底変換の法則の適用として記録し、独立の数学的な一覧項目は増やしていない。

これで、raw Homから元の全要素置換の全分類への比較、元のnative Homの全空間の分類から元のnative Hom図式への比較、そしてその間の元の単位を固定した実射が、同じ全二変数の底の上で揃った。ただし中間のこの実射の同値性は未証明。次は元の固定始域の同じ全roof比較を使い、この同じ実射の同値性と、合成した全FunctorIsoの元の固定始域比較との一致を検収する。任意の別の全同型の存在、pointwiseな比較だけ、またはcofinal性を未証明の仮定として置く形へ弱めない。R03d・R02・R03とnative極限性の完了は主張しない。

個別検査：元の単位を固定する延長28513・終了0、終域の底変換比較を含む最終版49885・終了0。308：延長の最初の版の対象ビルド12,223 jobs・終了0、小監査174本1,240宣言・標準三公理のみ（実ハンドル93277・終了0）。309：終域の底変換比較を含む最終版の対象ビルド12,223 jobs・終了0、小監査174本1,245宣言・標準三公理のみ（実ハンドル26554・終了0）。対象とその依存のみで、rootビルドや公式の大監査は実行していない。鍵返却済み。

§228・§229で今回103＋66＝169行、累計174本・11,252行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 229.1 型

共通入力は `(A : Type u) [CommRing A]`。元のmodelCategory AとmappingCofibrantFactorization Aを局所的に使う。strictBETotJointNativeHomProjection_leftFibrationは同じファイル内で局所instanceとして使う。

#### StrictDiagramTotJointSourceNativeLift（66行）

```lean
lemma strictBETotJointNativeHomProjection_leftFibration :
    LeftFibration (strictBETotJointNativeHomProjection A)

theorem exists_strictBETotJointSourceNativeLift :
    let P : Over (nerve (strictBETotJointHomIndex A)) :=
      Over.mk (nerveMap (strictBETotJointSourceElementsProjection A))
    let R := (continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj P
    ∃ f : R.left ⟶ strictBETotJointNativeHomTotalSpace A,
      f ≫ strictBETotJointNativeHomProjection A = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app P).left ≫ f =
        strictBETotJointSourceNativeHomMap A

def strictBETotJointNativeHomClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram (strictBETotJointNativeHomProjection A))
      (strictBETotJointNativeHomCoherent A)
```

## 230. R03g：元のGrothendieck単位のfiber制限の弱同値判定（紙、11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 10／全体 23（うち追加 11）。R03gを追加、未証明。

IS-W2 §19の同じR01〜R03のまとまり・一つの見込み1,500行以内の枠により、元の単位のfiber制限の弱同値判定をR03gとして追加する。共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

```lean
theorem grothendieckFiberUnit_isWeakHomotopyEquivalence (i : I) :
  IsWeakHomotopyEquivalence (grothendieckFiberUnit F i)
```

採用する元のfiber包含を明記する。weightedNerveConstantLift (F ⋙ nerveFunctor) iに、元のstrictなgrothendieckWeightedNerveIso Fのinvを合成したものをgrothendieckFiberInclusion F iとする。この包含に元のcontinuousLeftFibrationReplacementUnitを合成し、同じ底の指定頂点のfiberへvertexFiberLiftした元の実写像がgrothendieckFiberUnit F iである。元の単位・比較・包含を保持し、弱同値になる別の写像の存在への変更はしない。後のroof比較との照合もこの明記した同じ包含と単位を通す。

同じR03fの比較をそのfiberへ制限したgrothendieckFiberComparison F iとの合成が、元のgrothendieckKanCoefficientUnit Fのi成分と元のweightedNerveFiberMapの合成そのものに等しいことを、全単体の厳密な等式grothendieckFiberUnit_comparisonとして個別検査した（実ハンドル16869・終了0）。型だけの一時検査CheckGrothendieckFiberUnitWeakType.leanも終了0（7258）。R03gの証明はまだ仮定にも宣言にもしていない。

見込み150〜350行。元のR03fの同じ比較は前合成同値なので、既存vertexFiberMap_isQCatEquivalence_of_precompositionEquivalenceで同じfiberの比較を同値と検出する。元のEx∞単位はanodyneで弱同値、元のweightedNerveFiberMapはstrictな同型である。上の全単体の厳密な等式を弱同値の合成・消去則へ渡して、元のgrothendieckFiberUnit自身の弱同値性を得る。新しい数学的なfiberの判定として一つに見積もり、既存の構成の法則だけとは数えない。半分175行で実測と残りを報告する。

置き場所はKerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/GrothendieckFiberUnit.lean。R03gの後に、この同じfiberの単位と、元の同じnative Hom写像の合成を元の固定始域のroof比較へ照合する。R03gだけでnative Hom写像の同値性やR03dの全FunctorIsoの正規化が済んだとはしない。検証済み本体の累計は引き続き174本・11,252行／外枠15,000。今回の未検収のLeanは一時ファイル内である。

### 230.1 同じ包含・単位と比較の型（個別検査済み、対象ビルド前）

```lean
abbrev grothendieckReplacement : Over (nerve I)

def grothendieckFiberInclusion (i : I) : nerve (F.obj i) ⟶ nerve (Grothendieck F)

theorem grothendieckFiberInclusion_projection (i : I) :
    grothendieckFiberInclusion F i ≫ nerveMap (Grothendieck.forget F) = SSet.const (nerveVertex i)

def grothendieckFiberUnit (i : I) :
    nerve (F.obj i) ⟶ vertexFiber (grothendieckReplacement F).hom (nerveVertex i)

def grothendieckFiberComparison (i : I) :
    vertexFiber (grothendieckReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i)

theorem grothendieckFiberUnit_comparison (i : I) :
    grothendieckFiberUnit F i ≫ grothendieckFiberComparison F i =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveFiberMap (grothendieckKanCoefficients F) i
```

## 231. R03g完了：同じ元のGrothendieck単位の指定fiber制限は弱同値（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03gを完了。R03d・R02・R03は未完了。

R03gを111行で閉じた（見込み150〜350行、上端との差−239行）。元のstrictなgrothendieckWeightedNerveIsoのinvを通した同じ定値fiberの包含に、元の置換単位を合成し、指定fiberへの元の実写像grothendieckFiberUnitを取った。同じR03fの全比較からのfiber比較grothendieckFiberComparisonは、既存の前合成同値のfiberへの制限によって同値となる。

元の単位のfiber制限とこの同じfiber比較の合成は、元のEx∞係数単位と元のweightedNerveFiberMapの合成そのものに厳密に等しい。この等式は元の全単位の厳密な三角形、元のstrict同型の逆条件、weightedNerveConstantLift_mapの全自然性だけで示した。元のEx∞単位はanodyneであり、既存homotopyEquivalence_pre_of_anodyneとπ₀の全単射で弱同値と検査できる。元のweightedNerveFiberMapはstrictな同型である。弱同値の合成と同じfiber比較の消去により、元のgrothendieckFiberUnit自身の弱同値性が得られた。充填性や弱同値性を新しい仮定として追加していない。途中報告点175行に達する前に全証明が閉じた。

個別検査の最終版59023・終了0。310：対象ビルド3,412 jobs・終了0、小監査175本1,258宣言・標準三公理のみ（実ハンドル51386・終了0）。鍵返却済み。今回111行、累計175本・11,363行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

次は§220・§221の同じ全要素圏とGrothendieck表示の厳密な係数移送と元の置換単位の自然性を使い、この同じfiber単位の弱同値を元の全要素圏のfiberへ戻す。その後に、元の同じnative Hom写像を合成した写像と元の固定始域のroof比較を照合する。R03gだけでnative Hom写像の同値性やR03dの全FunctorIsoの正規化が済んだとはしない。

### 231.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。fiberのKan性は既存のleft-fibrationのfiberのKan性と元のEx∞係数のKan性を局所instanceとして使う。

#### GrothendieckFiberUnit（111行）

```lean
abbrev grothendieckReplacement : Over (nerve I)

def grothendieckFiberInclusion (i : I) : nerve (F.obj i) ⟶ nerve (Grothendieck F)

theorem grothendieckFiberInclusion_projection (i : I) :
    grothendieckFiberInclusion F i ≫ nerveMap (Grothendieck.forget F) = SSet.const (nerveVertex i)

def grothendieckFiberUnit (i : I) :
    nerve (F.obj i) ⟶ vertexFiber (grothendieckReplacement F).hom (nerveVertex i)

def grothendieckFiberComparison (i : I) :
    vertexFiber (grothendieckReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (weightedNerveProjection (grothendieckKanCoefficients F)) (nerveVertex i)

theorem grothendieckFiberUnit_comparison (i : I) :
    grothendieckFiberUnit F i ≫ grothendieckFiberComparison F i =
      (grothendieckKanCoefficientUnit F).app i ≫
        weightedNerveFiberMap (grothendieckKanCoefficients F) i

theorem grothendieckFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (grothendieckFiberComparison F i)

theorem grothendieckFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (grothendieckFiberUnit F i)
```

## 232. R03gを元の全要素圏の同じfiber単位へ係数移送する（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

元のstrictなGrothendieck表示から元の全要素圏への順写像を、§231の同じ指定fiber包含へ合成した。元の全要素射影への射影は同じ頂点で定値となる。この同じ包含に元の全要素圏の置換単位を合成し、同じ指定fiberへの実写像simplicialElementsFiberUnitを取った。

§221の同じ二つの表示の元の置換比較をそのfiberへ制限し、その同じ比較の前合成同値性からfiberの同値性を得た。元の全要素の単位のfiber制限とこの同じfiber比較の合成は、R03gの元のGrothendieck単位のfiber制限そのものに厳密に等しい。等式は、元の置換単位の自然性、元の同じ全要素とGrothendieck表示の厳密な往復、およびfiberの包含後の射の計算だけで示した。この等式と弱同値の消去則で、R03gを元のsimplicialElementsFiberUnit自身の弱同値性へ移した。100行。

R03gの同じ元の写像を既存の厳密な係数表示と元の単位の自然性で移送する法則として記録し、独立の数学的な一覧項目は増やしていない。元のfiber包含は定義で明記し、写像を別の同値の存在へ変更していない。次は元のnative Hom写像と元の単位を固定する延長を、その同じfiber包含へ制限する厳密な三角形を追跡する。元のnative Hom写像のfiber制限の弱同値性と、元の固定始域のroof比較との全同型の一致はまだ残る。

個別検査の最終版86234・終了0。311：対象ビルド3,420 jobs・終了0、小監査176本1,271宣言・標準三公理のみ（実ハンドル97632・終了0）。鍵返却済み。今回100行、累計176本・11,463行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainは変更していない。

### 232.1 型

共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`。fiberのKan性は既存のleft-fibrationのfiberのKan性を局所instanceとして使う。

#### SimplicialElementsFiberUnit（100行）

```lean
abbrev simplicialElementsReplacement : Over (nerve I)

def simplicialElementsFiberInclusion (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ nerve (SimplicialTotalElements F)

theorem simplicialElementsFiberInclusion_projection (i : I) :
    simplicialElementsFiberInclusion F i ≫ nerveMap (simplicialTotalElementsProjection F) =
      SSet.const (nerveVertex i)

def simplicialElementsFiberUnit (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶
      vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i)

def simplicialElementsFiberComparison (i : I) :
    vertexFiber (simplicialElementsReplacement F).hom (nerveVertex i) ⟶
      vertexFiber (grothendieckReplacement (simplicialElementsCatDiagram F)).hom (nerveVertex i)

theorem simplicialElementsFiberUnit_comparison (i : I) :
    simplicialElementsFiberUnit F i ≫ simplicialElementsFiberComparison F i =
      grothendieckFiberUnit (simplicialElementsCatDiagram F) i

theorem simplicialElementsFiberComparison_isQCatEquivalence (i : I) :
    IsQCatEquivalence (simplicialElementsFiberComparison F i)

theorem simplicialElementsFiberUnit_isWeakHomotopyEquivalence (i : I) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit F i)
```

## 233. 元のnative Hom写像と単位を固定する延長のfiber制限（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

元の全要素圏から底上への写像を、既存の同じfiber包含へ制限するsimplicialElementsFiberMapを定義した。元の置換単位を固定する延長について、そのfiberへの制限と元のfiber単位の合成がこの写像に厳密に等しいことを示した。既存の包含・単位・延長の合成則であり、新しい数学的な一覧項目は増やしていない。

BEへの特殊化では同じ全パラメータのstrictBETotJointSourceNativeHomMapを制限した。fiber単位自体の弱同値性はR03gの係数移送から得た。hm・huは元の底射影と元の単位を固定する条件で、§229の実際の延長が満たすものを使う。native Hom写像のfiber制限自身の弱同値性、延長自身の同値性、元の固定始域のroof比較との全FunctorIsoの一致はまだ証明していない。

個別検査は一般版23702・BE版31608とも終了0。312の対象ビルドは12,227 jobsで成功（既存依存を含む対象ビルドでありrootビルドではない）。続く小監査は178本・1,280宣言、標準三公理のみ。ログ/private/tmp/isw2-build312.logの両成功と該当プロセスの終了を確認した。元の実行ハンドルは会話圧縮後に復元できなかったため終了コードを推測して記載しない。鍵を重複取得せず、ビルドを再実行していない。

今回2本101行、累計178本・11,564行／外枠15,000。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。

### 233.1 型

一般版の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})`、BE版は `(A : Type u) [CommRing A]`。BEのmodel構造とfunctorial factorizationは既存の指定された局所instanceを使う。

#### SimplicialElementsFiberMap（43行）

```lean
def simplicialElementsFiberMap {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F)) (i : I) :
    nerve ((simplicialElementsCatDiagram F).obj i) ⟶ vertexFiber p (nerveVertex i)

theorem simplicialElementsFiberUnit_map {E : SSet.{u}} (p : E ⟶ nerve I)
    (h : nerve (SimplicialTotalElements F) ⟶ E)
    (hh : h ≫ p = nerveMap (simplicialTotalElementsProjection F))
    (m : (simplicialElementsReplacement F).left ⟶ E)
    (hm : m ≫ p = (simplicialElementsReplacement F).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (simplicialTotalElementsProjection F)))).left ≫ m = h) (i : I) :
    simplicialElementsFiberUnit F i ≫ vertexFiberMap _ p m hm (nerveVertex i) =
      simplicialElementsFiberMap F p h hh i
```

#### StrictDiagramTotJointSourceNativeFiber（58行）

```lean
def strictBETotJointSourceNativeFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (strictBETotJointNativeHomProjection A) (nerveVertex P)

theorem strictBETotJointSourceFiberUnit_isWeakHomotopyEquivalence (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P)

theorem strictBETotJointSourceNativeFiberUnit_map
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
      vertexFiberMap _ (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) =
        strictBETotJointSourceNativeFiberMap A P
```

## 234. 外枠の再見積もりと次の判断点（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。検証済み213e2858e、178本・11,564行。残り枠は3,436行。

### 234.1 残りの規模

§152.4のR04〜R12だけの当初見込みでも下端4,300行で、残り枠を864行超える。さらにR02・R03のnative比較と標準脚が未完了である。これまでのfiber単位の比較を作ったことでその未完箇所を具体化できたが、これをもって全native Hom比較や標準脚の全自然性が済んだとは扱わない。以下は相互に重複しない残りの仕事の紙の見込みであり、新規Lean項目の無条件な追加承認とはしない。

| 残り | 見込み（行） | 再利用と未検証点 |
|---|---:|---|
| R03d内：指定native fiber写像の弱同値 | 600〜1,400 | R03gと§233の厳密な三角形を使用。元の固定始域roofとの照合は未証明 |
| R03d内：全FunctorIsoと固定始域への制限の等式 | 400〜900 | 全要素の同じ延長を使用。点ごとの同値だけでは閉じない |
| R02・R03：指定native錐族と極限性 | 600〜1,200 | 元の重みの比較と指定Hom同型を接続。脚を作り替えない |
| R04・R05：UのTot比較と局所化への輸送 | 500〜1,100 | G10の全図式射と指定錐族、既存forgetの極限保存を再利用 |
| R06〜R08：strict実現の模型と同じ余錐族 | 1,600〜2,800 | §152の見込みを維持。台の通常colimだけで導来実現とはしない |
| R09・R10：実現のU比較と全関手比較 | 1,000〜1,800 | ③-aの全族と指定輸送を使用。まだ実測していない |
| R11・R12：離散制限と既存入口・係数変更 | 500〜900 | ⑤aの欄を変更せず照合。Totと実現の両部分を含む |
| 合計 | **5,200〜10,100** | 完成時 **16,764〜21,664** |

当初§152の全体5,700〜9,800行に対し、現在の完成見込みは下端で+11,064、上端で+11,864行。主な差は、二変数の指定native Homへの全自然性と、元の固定始域roof比較への正規化を、点ごとの同値の存在に弱めず証明するための一般の分類・fiber単位の道具にある。完成時の新しい外枠の提案は22,000行。上端に対する余裕は336行しかなく、再度の上振れを吸収できると保証しない。Tot側の停止点3b-4aと実現側3b-4bの分割は維持する。

### 234.2 止める根拠と現在の状態

coordination.md §2：『上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）』、夜の進め方も『その線の Lean は止めて決めておいた代わりの紙の作業へ』と指定している。IS-W2 §18は3b-4の外枠15,000行、§19も『外枠15,000行は変えない』。同じまとまり内の1,500行以下の中間定理の追加許可は、この外枠を変更する許可ではない。

したがって、検証済みを213e2858eに保存した上で、この線のLeanの追加を止める。範囲、型、指定脚、全族、固定始域の同型の等式を弱めない。外枠の変更はユーザー判断を要する。停止点3b-4aに達したとの報告ではない。代わりの紙の作業を次節に記録する。

### 234.3 紙：元のnative fiberから元のroofへの未完の橋

次に必要な主張の候補は、既存の指定された写像そのものについての次の型である（ここではLean宣言を追加していない）。

```lean
theorem strictBETotJointSourceNativeFiberMap_isWeakHomotopyEquivalence
    (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

この型を示す際、元のsource coefficientの通常の要素圏のnerveと、元のroofで使う逆向きの要素圏のnerveを同一視してはならない。既存のedgewise/opposite比較とterminal augmentationを通した同じ写像で比較し、その上で元のroofの弱同値性とKanHammockHomInfinityの指定Yoneda比較へ接続する。native Homのpullbackのfiberは、同じ元の頂点のtwisted-arrow fiberへ移す。経路修正のexactComponentIso_postcompで指定された底のpathを追跡する必要があり、任意の同型への置換では固定始域の最終等式を保証できない。

この弱同値が示されれば、§233の等式とR03gの同じfiber単位の弱同値から、元の単位を固定する延長のfiber写像を弱同値と判定できる。両側のleft fibrationのKan fiber上で同値に移し、既存isPrecompositionEquivalence_of_leftFibration_nerve_fibersで同じ全延長の前合成同値性を得る。分類の全同型へ移しても、R03dの固定始域へ制限した全FunctorIsoが元のstrictBETotProbeFrameHomInfinityIsoに等しいことは別途残る。

### 234.4 紙：3b-3との境目を維持する

Totのstrict入力の模型、同じHom分類、指定native錐とその極限性は③-bで閉じる。R05でstrict複体図式の局所化上へ全評価・全指定錐族を輸送する部分は③-aの3b-3の指定された比較を使う。実現側R09・R10も、図式ごとの余錐だけではなく③-aの全パラメータの余錐族とその輸送を使う。任意のcoherentなBE図式の厳密化は今回の実装に含めない。既存FramedLimit*とCAlgUnderlyingDerivedComparisonを作り直さず、無条件cAlgForgetDerived_mapJoinCone_isLimitの保存方向を使う。Uが極限を保存することからBE値の極限性を逆に推論しない。

## 235. 外枠判断待ちの紙：既存APIの証明境界を確認（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。Lean追加なし、実測178本・11,564行のまま。前のターンは検証済み保存と再見積もりの進捗であり、検証待ちではない。現mainのIS-W2末尾も§19・外枠15,000行のままで、外枠変更の承認を確認できていない。

次の既存ソースを読み、§234.3の経路のうち使える結論と不足を分けた。

| 既存ソース（SerrePositivity以下） | 実際の結論 | 接続時の注意 |
|---|---|---|
| EInfinity/FrameHom/FrameLeftRoofPrecompose.lean：frameLeftRoofColimitMap_precompose | 指定された始域射・frame比較に沿うanodyneQ.map後の等式 | 生の二変数の自然変換として使わない。定理はinclude hαも要求する |
| InfinityCategories/Kerodon/FibrationsOfInfinityCategories/ClassificationOfCocartesianFibrations/VertexFiberPullback.lean：vertexFiberPullbackIso_hom_ι | fiber同型の順射を包含すると元の第一射影になる厳密な等式 | native total spaceの第一射影を元のcorrected pairingへ戻す際の指定された方向が使える |
| EInfinity/FrameHom/RightFrameHomInfinityNormalization.lean：rightFrameTerminalHomIso_hom | 終端の実現比較、原本kanHammockHomInfinityIso、指定homInfinityTransportの順の合成に等しい | 比較二胞体c.triangleも同じ入力として保持する。零単体の共役式だけで全同型の等式を結論しない |
| EInfinity/BarrattEccles/StrictDiagramTotProbeHomInfinityComparison.lean：strictBETotProbeFrameHomInfinityIso | 元のframe比較と、同じprobe源の頂点同型をco-Yonedaで写した全標的同型の合成 | 固定始域への最終制限をこの同じ合成へ合わせる必要がある |
| InfinityCategories/Kerodon/FibrationsOfInfinityCategories/FibrationsOverOrdinaryCategories/F1FibrationsLeftFibrationNerveComparison.lean：isPrecompositionEquivalence_of_leftFibration_nerve_fibers | 両射影がleft fibration、底を厳密に保つ全写像について、各対象の指定fiber射がQCat同値なら全射は前合成同値 | native fiber射の弱同値性が未完なのでまだ適用の前提が揃わない |

従って再開時は、元のnative fiber射にvertexFiberPullbackIsoを合成し、包含後の厳密な等式で同じcorrected pairingへの制限を回収する所を最初の検査単位とする。その後、元の指定された底のpathを保持したまま、元のroofとterminal augmentationに沿う比較を組み立てる。anodyneQ上の既存の始域自然性だけで済むと仮定せず、固定始域の全標的同型の合成まで追跡する。この不足を解決したとの数学的主張も、新しい仮定付きのLean入口も追加していない。

今回の紙の整理は§234で指定した代わりの作業。対象ビルド・監査の新しい実行は不要で、鍵は取得していない。外枠変更の質問は一件のまま維持し、重複して送らない。

## 236. §20の承認による再開：同じnative fiber射と同じcorrected pairing（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

ユーザーはIS-W2 §20として外枠22,000行を承認した。/goalの範囲と型は維持し、Tot側R03d・R02〜R05とR11/R12のTot部分を先に閉じて停止点3b-4a、その後は止める指示がなければ実現側へ進む。§19の中間定理の枠も維持する。判断待ちを解いてLeanを再開した。

最初の検査単位は§235のとおり。元のstrictBETotJointSourceNativeFiberMapに、同じnative Hom入力によるvertexFiberPullbackIsoの順射を合成する。包含後の等式は、既存のvertexFiberPullbackIso_hom_ι、元のfiberLiftの包含後の等式、元のnative Hom写像の第一射影の等式を順に合成する。これにより元の同じcorrected pairingへの制限を回収する。既存のpullback・fiber・合成則の照合であり、追加の数学項目としては数えない。native fiber射の弱同値性はこの段では主張しない。

### 236.1 型（既存構成の合成則、共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceNativeFiberPairing（66行）

```lean
def strictBETotJointSourceNativeTwistedFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))

theorem strictBETotJointSourceNativeFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeFiberMap A P ≫
      vertexFiberι (strictBETotJointNativeHomProjection A) (nerveVertex P) =
        simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
          strictBETotJointSourceNativeHomMap A

theorem strictBETotJointSourceNativeTwistedFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeTwistedFiberMap A P ≫
      vertexFiberι (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P)) =
      simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A
```

## 237. 同じfiber制限による指定pathの保持（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

元のstrictBETotJointSourceCorrectedPairingIsoそのものを同じfiber包含へ前合成する。その射影は、元の指定されたstrictBETotJointSourcePairingBasePathIsoと厳密な射影等式の同じ合成を、同じfiber包含へ前合成したものに等しい。既存functorIso_precomp_postcompと元の全同型の射影等式だけによる全同型の合成則であり、新しい数学の項目を増やさない。native fiber射の弱同値性やR03dの最終等式が済んだとは扱わない。

### 237.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceNativeFiberPath（56行）

```lean
def strictBETotJointSourceFiberPairingIso (P : strictBETotJointHomIndex A) :
    FunctorIso
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A)
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceNativePairing A)

theorem strictBETotJointSourceFiberPairingIso_postcomp (P : strictBETotJointHomIndex A) :
    (strictBETotJointSourceFiberPairingIso A P).postcomp
      (twistedArrowProjection (CAlg_R A)) =
      FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P)
```

## 238. 再開の最初の検査単位の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は引き続き未完了。

§236・§237の二本を検証した。元のnative fiber射へ同じvertexFiberPullbackIsoを合成し、包含後に同じ元のcorrected pairingへの制限を厳密に回収する。さらに、そのcorrected pairingと元のpairingの同じ全同型を同じfiber包含へ制限し、射影が元の指定pathをそのまま制限したものと全同型として等しいことを確認した。native fiber射自身の弱同値性、同じ延長の全同値性、固定始域の元の全FunctorIsoへの最終正規化はまだ残る。

検査経過：最初の個別検査では単体記法のscopeとfiberLiftの包含後の簡約を直した。二度目の等式ではpullback.sndと元のnative射影の定義展開を明示した。最終個別検査9358は終了0。313の対象ビルドは12,228 jobsで成功したが、一時監査の先頭で私がimportをmoduleより前に置いて構文エラーを起こした。314ではその先頭を修正し既存交換則の依存も生成したが、合成同型へのprecompの型推論が失敗した。FunctorIso.precompを明示した最終個別検査64620は終了0。

最終315：鍵付き対象ビルド12,233 jobs、小監査180本・1,291宣言、標準三公理のみ。実ハンドル90235・終了0、鍵返却済み。コマンドはwith_build_lock.sh --class impl --wait 3600と1700秒のguardを使用し、一度に一枚の整理券のみ。rootビルドや公式監査の登録は行っていない。既存依存を含む対象ビルドである。名前空間の長いopen行についてstyle警告はあるが、エラーはない。

今回122行（66行・56行）、累計180本・11,686行／承認済み外枠22,000行、残り10,314行。sorry・独自公理0、計算上限変更なし。[ModelCategory SSet]を追加せず、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainを変更していない。追加する数学の一覧項目は増やさず、既存のfiber・pullback・全同型の合成則として型を§236・§237に記載した。

登録候補（調整役の取り込み時用、今回はこちらで登録しない）：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPairing
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPath

次は§234.3・§235のとおり、同じnative fiber射を元の固定始域のroof比較と照合し、その実射自身の弱同値性へ接続する。Tot側の停止点3b-4aはまだ未到達であり、この検収を停止点の完成とはしない。

## 239. R03dの次の接続：同じfiber包含の通常圏での表示（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

前ターンは§236〜§238を検証して1c8716f15へ保存した進捗。今回も§238の次から続ける。mainにIS-W2 §20の追記は入ったが、この確認時点では57705f223はmainの祖先ではないので、取り込み完了後のmergeはまだ行わない（ユーザーはmerge前の続行を承認済み）。

元のroofは固定始域の実際のHom単体のラベルで定義される。§238のfiber包含をこの通常圏のラベルに照合するため、元のGrothendieck表示を経由するfiber包含が通常のGrothendieck.ιと同じnerve射であることを示す。元のweighted nerve同型の逆を別の逆で置き換えず、同じ順射を合成して確認する。既存構成の単位・係数表示の法則であり、数学的な一覧項目は増やさない。見込み80〜180行。共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。

```lean
theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i

theorem grothendieckFiberInclusion_eq_nerveMap (i : I) :
    grothendieckFiberInclusion F i = nerveMap (Grothendieck.ι F i)
```

この照合だけでnative fiber射自身の弱同値性は結論しない。元の通常の要素圏とroofの反対要素圏の規約、同じcorrected pairingの指定path、固定始域の元の全Hom比較の合成順序を、引き続き追跡する。

## 240. 元のfiber包含から元のsource-frameのラベルへ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§239の順射のprefix計算は個別検査90750で終了0。その同じ順射を合成して元の逆を消去し、grothendieckFiberInclusionが通常のGrothendieck.ιのnerveと厳密に等しいことを示した。これを元の全要素圏へ移すと、同じsimplicialElementsFiberInclusionは同じ通常の要素圏の包含のnerveとなる。通常の包含を元のsource-frameのdownへ合成し、同じ底・単体次数と元のHom単体のラベルを厳密に回収する。元のnative pairingへの制限も同じ通常の包含のnerveを通る。

全て、元のfiber包含・係数表示・合成則の照合であり、新しい数学の一覧項目は増やさない。通常の要素圏をroofの反対要素圏と同一視しておらず、弱同値性やR03dの全同型の正規化を完了と数えない。一般版は116行（見込み80〜180行、上端との差−64行）、BEの係数表示の特殊化は62行。一般版の完成形の個別検査31293は終了0。BEの合成検査と対象ビルド・監査は別途以下へ記録する。

### 240.1 型

一般版の共通入力は `{I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})`。Gは同じI上のSSet値の図式。BE版は `(A : Type u) [CommRing A]`。Gを使う宣言には未使用のFは入らない。

#### SimplicialElementsFiberInclusion（116行）

```lean
theorem grothWeightedNerveForward_fiberInclusion (i : I) :
    nerveMap (Grothendieck.ι F i) ≫ grothWeightedNerveForward F =
      weightedNerveConstantLift (F ⋙ nerveFunctor) i

theorem grothendieckFiberInclusion_eq_nerveMap (i : I) :
    grothendieckFiberInclusion F i = nerveMap (Grothendieck.ι F i)

def simplicialElementsFiberFunctor (G : I ⥤ SSet.{u}) (i : I) :
    (simplicialElementsCatDiagram G).obj i ⥤ SimplicialTotalElements G

theorem simplicialElementsFiberInclusion_eq_nerveMap (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberInclusion G i = nerveMap (simplicialElementsFiberFunctor G i)

theorem simplicialElementsFiberFunctor_obj (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).obj = (i, s.obj)

theorem simplicialElementsFiberFunctor_value (G : I ⥤ SSet.{u}) (i : I)
    (s : (simplicialElementsCatDiagram G).obj i) :
    ((simplicialElementsFiberFunctor G i).obj s).val = s.val
```

#### StrictDiagramTotJointSourceFiberElements（62行）

```lean
def strictBETotJointSourceFiberElements (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ⥤
      FrameHom.SourceFrameArrowElements (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))

theorem strictBETotJointSourceFiberElements_parameters (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    ((strictBETotJointSourceFiberElements A P).obj s).obj = (AsSmall.down.obj P, s.obj)

theorem strictBETotJointSourceFiberElements_value (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A))
      ((strictBETotJointSourceFiberElements A P).obj s) = s.val.down

theorem strictBETotJointSourceFiberPairing_eq (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
      strictBETotJointSourceNativePairing A =
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceNativePairing A
```

## 241. 対象ビルドの順番待ち中の照合：roofの余終性の入力範囲（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

316の対象ビルドと小監査を、一枚の整理券で--class impl --wait 3600により待機中。一般版の個別検査は通過したが、一時的な結合検査ではBE側の全importを先に読み込んだ文脈でprefix証明が200,000 heartbeatsに達した。計算上限は上げず、実際のモジュール分割で一般版を先にビルドしてからBEの特殊化を検査する。結合検査の失敗を対象ビルドの成功と扱わない。最終結果は次の検収欄へ記す。

待機中に既存のroof側のAPIを確認した。CofibrantSourceFrameRightKanCofinalityのcofibrantSourceFrameRawRoofMap_isLeftCofinalは、X・YともCofibrantAlgebra Aであり、cofibrantAlgebraRelativeCategoryのhammockを使う。ModelBifibrantFrameRightKanCofinalityのmodelBifibrantSourceFrameRawRoofMap_isLeftCofinalは、X・YともBifibrantObjectであり、modelBifibrantRelativeCategoryのhammockを使う。今回の元の右置換RYを、そのままこれらの入力に読み替えることはできない。元のnative Homの入力と全局所化の比較を保ち、必要な係数移送と端点同型を明示する必要がある。

またcosliceTwistedHomMap_isQCatEquivalenceは任意のquasicategoryの同じ端点での同値で、cosliceTwistedHomMap_ιは元のcosliceからtwisted-arrowへの包含後の等式を与える。ただし今回のroof評価のpinched Homとcoslice fiberの規約を合わせる工程が残る。この同値を引用するだけで§238の実射自身が弱同値になったとはしない。今回のラベル回収と、元のroofとの正規化を接続してから判定する。

## 242. 元のfiber包含とラベルの対象ビルド検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

316が終了した。同じ整理券で共有鍵を待ち、対象ビルド12,230 jobs成功、小監査182本・1,303宣言、標準三公理のみ。実ハンドル88366・終了0、鍵返却済み。一般版とBE特殊化を実際の二モジュールに分けたビルドで通し、一時結合ファイルのtimeoutを解消した。計算上限は変更していない。

今回178行、累計182本・11,864行／外枠22,000行。一般版116行とBE版62行。sorry・独自公理0。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・入口・公式監査・mainの変更なし。R03dのnative fiber射自身の弱同値性はまだ未完了。

登録候補：SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberInclusion、およびSerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberElements。

この検収直後に調整役からtensorFrameHomIso_pointの集約時の重複を通知された。316の小監査は両定義を同時importする検査ではなかったため、これを検出できていない。次の修正ではmainの既存の定義と同時にimportし、宣言名の突合も行う。316の成功を集約での重複不存在の根拠としては使わない。

## 243. 集約時の重複定理の修正と宣言名の突合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

調整役から通知されたtensorFrameHomIso_pointの重複を修正した。TensorConeUnitPointでの宣言を削除し、FrameConeClassesの既存lemmaを再公開する互換入口だけを残した。StrictDiagramTotUniversalProbePointComparisonはFrameConeClassesを直接importし、既存lemmaの暗黙引数Yを呼び出し側で明示する。既存FrameConeClasses側は変更していない。互換入口には宣言がないので、小監査ではこのモジュールの宣言数0を明示的に要求し、補題の実際の定義元がFrameConeClassesであることも検査する。

宣言名の突合は、自分のIS-W2のモジュール一覧と枝で追加したLeanファイル548本（1,728個の名前付き宣言）を対象に、main 7e03e17a7 のEInfinity配下3,749本・13,399個の名前付き宣言と行った。namespace・section・endを追跡し、コメントを除いてdef・lemma・theorem・abbrev等と名前付きinstanceを走査し、同じ完全名が異なるファイルにあるものを検出した。同一ファイルでmainと共通の宣言は重複と数えない。この修正後の対main EInfinityの衝突は0件。

自分のファイル同士にも同じ走査を行い、HAのnormalizedMooreReverse_zero_inclusionをもう1件検出した。NormalizedMooreReverseZeroとNormalizedMooreReverseEvaluationに同じ完全名・同じ型の定理があった。Zero側をEvaluationの再公開だけの互換入口にし、既存Evaluation側は変更しない。直接importerのNormalizedMooreReverseExtendZeroも対象ビルドに含める。修正後の自分の新規ファイル同士の衝突は0件。HAの補題の定義元がNormalizedMooreReverseEvaluationであり、Zero側の宣言数が0であることも小監査で検査する。走査結果は/private/tmp/isw2-declaration-collision-scan.jsonと/private/tmp/isw2-declaration-collision-scan-after-fix.jsonに保存した。

これは名前付き宣言をテキスト走査する確認であり、全importの同時ビルドやLeanの生成する内部名の検査とは区別する。小監査には既存の定義元を明示的にimportして、通知された二つの名前について実際の同時importと定義元も検証する。既存の公式入口・監査、⑤a、mainは変更しない。

317の対象ビルド・小監査は--class impl --wait 3600で同じ整理券のまま待機する。待機中でpayloadのzshがまだ起動していないことをpsで確認してから、追加で見つかったHAの直接importerも同じジョブへまとめた。追加の整理券や鍵の取り直しは行っていない。結果が通るまではこの修正コードをコミットしない。

## 244. R03dの係数移送の下書き：元の固定標的roofの反対圏へ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。この下書きは対象ビルド前なので検証済みの行数・モジュール数には加えない。

重複修正の対象ビルドを待つ間に、既存のULiftHom.equiv、宇宙持ち上げのelementsEquivalence、固定標的のelementsCostructuredEquivalence.rightOpを合成した。元の通常の要素圏は固定標的のroofの反対圏に移る。次数・元の実射のラベル・単体作用素を、同じ関手の厳密な式で回収する。既存の同値と係数移送の合成則であり、数学的な一覧項目を増やさない。見込み80〜150行。元のnative fiber射の弱同値性はまだ結論しない。

UniverseLiftElementsのoleanが未生成だったので、その既存ソースを一時検査へ含めた。別モジュールの宇宙変数vの再宣言が一時結合ファイルだけで重なったため、その一時ファイルの宣言を整理した。最終個別検査37848は終了0。対象ビルドと小監査は、優先する重複修正を検収した後に行う。このLean下書きは重複修正のコミットに含めない。

### 244.1 型

共通入力は `{C : Type u} [Category.{v} C] (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)`。

#### LiftedSourceFrameFiberRoof（53行）

```lean
def liftedSourceFrameFiberRoofEquivalence (P : liftedSourceFrameIndex (C := C)) :
    (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P ≌
      (CostructuredArrow (Q.obj (AsSmall.down.obj P).1.unop)
        (R.obj (AsSmall.down.obj P).2))ᵒᵖ

theorem liftedSourceFrameFiberRoofEquivalence_degree (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).left =
      s.obj.unop

theorem liftedSourceFrameFiberRoofEquivalence_value (P : liftedSourceFrameIndex (C := C))
    (s : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.obj s).unop).hom =
      s.val.down

theorem liftedSourceFrameFiberRoofEquivalence_operator (P : liftedSourceFrameIndex (C := C))
    {s t : (simplicialElementsCatDiagram (liftedSourceFrameCoefficients Q R)).obj P}
    (f : s ⟶ t) :
    (((liftedSourceFrameFiberRoofEquivalence Q R P).functor.map f).unop).left =
      f.down.hom.unop
```

## 245. 同じroofのラベルと元のnative pairingのラベルを照合（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§244の同じ既存同値の合成をBEの同じ全パラメータへ特殊化した。同じroofの射のラベルが、元のstrictBETotJointSourceFiberElementsを経由してnative pairingへ渡したsourceFrameArrowValueと厳密に等しい。次数も同じ元のHom単体の次数である。既存の係数移送・同値の合成則の照合として型を記録し、数学的な一覧項目を増やさない。一般版と合わせた一時個別検査81098は終了0。元のnative fiber射自身の弱同値性はなお未完了。

優先する重複修正の318はまだ鍵の順番待ちで、psによりpayload未起動を確認した。同じジョブへこの二本の対象と小監査を追加した（整理券の追加・取り直しなし）。対象ビルドと監査が通るまでは、この二本もコミットしない。重複修正とこの係数移送は別コミットにする。追加の宣言名はgit grepでもmainのEInfinity配下に存在しないことを確認した。

### 245.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceFiberRoof（58行）

```lean
def strictBETotJointSourceFiberRoofEquivalence (P : strictBETotJointHomIndex A) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P ≌
      (CostructuredArrow ((strictBETotJointSourceFrame A).obj (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))ᵒᵖ

theorem strictBETotJointSourceFiberRoofEquivalence_degree (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).left =
      s.obj.unop

theorem strictBETotJointSourceFiberRoofEquivalence_pairingValue
    (P : strictBETotJointHomIndex A)
    (s : (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) :
    (((strictBETotJointSourceFiberRoofEquivalence A P).functor.obj s).unop).hom =
      FrameHom.sourceFrameArrowValue (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A))
        ((strictBETotJointSourceFiberElements A P).obj s)
```

## 246. 調整役への重複修正の検収報告（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

依頼されたtensorFrameHomIso_pointの重複を削除した。TensorConeUnitPointはFrameConeClassesを再公開する宣言0の互換入口になり、StrictDiagramTotUniversalProbePointComparisonは既存lemmaを直接使う。Kᵒᵖ・重み・frame・元の比較射と暗黙のYを明示して既存lemmaを取り、その成分表示をIso.app_homで合わせた。既存FrameConeClassesは変更していない。途中の317ではYだけを明示した呼び出しでSmallCategoryの推論に失敗し、引数を明示した後は成分表示の差も修正した。最終個別検査7586は終了0。

同名宣言の追加の確認で見つけたHAのnormalizedMooreReverse_zero_inclusionも同様に修正した。NormalizedMooreReverseZeroはNormalizedMooreReverseEvaluationを再公開する宣言0の互換入口となり、既存Evaluation側の証明を使う。直接importerのNormalizedMooreReverseExtendZeroも対象ビルドに含めた。一時結合検査48967は終了0。既存補題の型と内容は維持し、G10の完了項目を弱めていない。

最終の全宣言名走査はmain 7f52c5cd1を対象とし、検査時点の自分の549本・1,732個の名前と、main EInfinityの3,745本・13,373個の名前を照合して、異なるファイル間の衝突0件。その後に追加したBEのroof特殊化の3宣言もgit grepでmainに存在しないことを確認した。自分の550本・1,735個の名前の最終の内部照合も衝突0件。これらはテキストによる名前付き宣言の確認であり、生成される内部名を含むrootの全ビルドとは区別する。

318の最終結果：鍵付き対象ビルド12,245 jobs成功、小監査188モジュール・1,318宣言、標準三公理のみ。実ハンドル88868・終了0、鍵返却済み。--class impl --wait 3600、1700秒guardで同じ一枚の整理券を使った。待機中に個別検査を通過したR03dの二本も同じ対象と監査へまとめた。BEの自分の184本は1,311宣言、残りは既存FrameConeClassesとHAの既存・直接importerの4本である。

小監査は二つの互換入口の宣言数が0であることに加え、tensorFrameHomIso_pointの定義元がFrameConeClasses、normalizedMooreReverse_zero_inclusionの定義元がNormalizedMooreReverseEvaluationであることを明示的に要求して成功した。従って旧い重複宣言の定義元を取り違えた結果を成功としていない。sorry・独自公理0、計算上限の変更なし。既存の定義元二本・公式入口・公式監査・mainは変更していない。

修正対象（この修正のコミットに含む）：

- SerrePositivity/EInfinity/HomotopyWeight/TensorConeUnitPoint.lean
- SerrePositivity/EInfinity/BarrattEccles/StrictDiagramTotUniversalProbePointComparison.lean
- SerrePositivity/HomologicalAlgebra/NormalizedMooreReverseZero.lean

rootとEInfinity集約の全ビルドは実行していない。取り込みの再検収を調整役にお願いする。二つの互換入口は登録済み・登録予定の経路を維持するが、自身の宣言数は0となる。R03dで追加した二本は次節の別コミットとして記録する。

## 247. 同じfiberから元のroofへの係数移送を保存（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03d・R02・R03は未完了。

重複修正は専用コミットe0c5190ecに保存した。その修正と別に、§244・§245の二本を同じ318の対象ビルドと小監査で検収して保存する。一般版53行、BE版58行、計111行。一般版は見込み80〜150行に対して53行（上端との差−97行）。既存の三つの同値の合成で元の通常のfiber要素圏を元の固定標的roofの反対圏へ移し、元の次数・実射ラベル・単体作用素を保持した。同じroofの射のラベルは、元のnative pairingへ渡したsourceFrameArrowValueに厳密に等しい。

検証は§246に記載した318（対象ビルド12,245 jobs、188モジュール1,318宣言、標準三公理のみ、実ハンドル88868・終了0）による。個別検査37848・81098も終了0。BEの自分のモジュール一覧は184本・1,311宣言で、TensorConeUnitPointは既存補題の再公開のみのため自身の宣言0を含む。検証済みの累計は11,953行／外枠22,000行。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。

今回の登録候補：

- SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameFiberRoof
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberRoof

57705f223以後の検証済み新規ファイルは上記二本に加え、§238のStrictDiagramTotJointSourceNativeFiberPairing・StrictDiagramTotJointSourceNativeFiberPath、§242のSimplicialElementsFiberInclusion・StrictDiagramTotJointSourceFiberElementsの計6本。各節の完全なモジュール名を使って登録できる。こちらで公式入口・監査には登録していない。

次は同じ元のfiberの反対要素圏を既存resolutionLeftRoofColimitMapへ送る。この既存の実射の弱同値性には右置換のfibrancyと指定right frame・第一分解が使える（FibrantSourceReducedFirst）。その後に§238の同じnative fiber射と指定pathを、この同じroofの全族の比較へ照合する。ラベルが一致するだけで実射の弱同値性や全FunctorIsoの正規化が済んだとはしない。Tot側の停止点3b-4aは引き続き未到達。

## 248. 元の反対要素圏を同じ実left-roof比較へ移す（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§247の次の検査単位。元の持ち上げたHomの要素圏の反対nerveから、元のsourceFrameElementsFamilyの入力nerveへ、同じULiftの上下だけを使う厳密な同型を取る。その順射を元のresolutionLeftRoofColimitMapに合成する。標的のfibrancy・指定right frame・第一分解は既存の弱同値定理と同じ入力として明示し、その実射の弱同値性を同じ係数同型で移す。新しい弱同値の仮定や[ModelCategory SSet]を置かない。

既存の係数移送と既存の実射の弱同値定理を同じ同型で前合成する法則であり、新しい数学的な一覧項目は増やさない。二本合わせて見込み100〜200行。元のnative fiber射自体の弱同値性をまだ結論していない。元のsame corrected pairingとこの基準roof比較の照合が残る。

### 248.1 型

第一のファイルの共通入力は `(K : SSet.{v})`、wは指定された宇宙の持ち上げ。第二のファイルは `{C : Type u} [Category.{v} C] [ModelCategory C] {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C)`。弱同値定理のYのfibrancy、r、cofを全て明示している。

#### ElementsOppositeUniverseIso（63行）

```lean
def elementsOppositeUniverseIndex :
    (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ⥤
      ULiftHom.{max w v} K.Elementsᵒᵖ

def elementsOppositeUniverseIndexInverse :
    ULiftHom.{max w v} K.Elementsᵒᵖ ⥤
      (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ

def elementsOppositeUniverseNerveIso :
    nerve (ULiftHom.{max w v} ((SSet.uliftFunctor.{w,v}).obj K).Elements)ᵒᵖ ≅
      nerve (ULiftHom.{max w v} K.Elementsᵒᵖ)
```

#### LiftedResolutionLeftRoof（43行）

```lean
def liftedResolutionLeftRoofColimitMap :
    nerve (ULiftHom.{max u v}
      ((SSet.uliftFunctor.{max u v,v}).obj ((cosimplicialHom q.obj).obj Y)).Elements)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences C) X Y

theorem liftedResolutionLeftRoofColimitMap_isWeakHomotopyEquivalence [IsFibrant Y]
    (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C)
      (trivialFibrations C)) :
    IsWeakHomotopyEquivalence (liftedResolutionLeftRoofColimitMap q Y)
```

## 249. 同じBEの反対fiberから元の実roof比較への弱同値（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

厳密な係数同型は最終個別検査46841で終了0。元の実left-roof比較とその弱同値性の係数移送は、一時結合検査10774で終了0。nerveMapの既存の補助入口は対象宇宙を共有する圏の関手を要求するため、今回の同じ上下の関手を全射列へ直接合成して、異なる対象宇宙のnerve間の同じ実写像を定義した。両往復の厳密な等式も各射列で確認した。計算上限は変更しない。

その元の実射をBEの同じ全パラメータPへ特殊化する。元のsource frameはmodelSourceFrameFamilyを同じframedLimitProbeへ適用したもの、標的は同じrightFrameReplacement。元の右置換のfibrancyとrightFrameFamily・mappingCofibrantFactorizationを、既存の弱同値定理の入力へそのまま使う。新しいfibrancyや弱同値性を仮定として追加しない。既存の係数移送・特殊化の法則として型を記録し、数学的な一覧項目は増やさない。特殊化の見込み80〜150行。

これは元のnormal fiberの反対要素圏から同じhammock余極限への基準射についての弱同値性である。元のnative fiber射とこの基準射が同じ比較を表すこと、元の指定pathを保った正規化、固定始域の元の全FunctorIsoとの一致は引き続き残る。R03dを完了とは数えない。

### 249.1 型（共通入力 `(A : Type u) [CommRing A]`）

#### StrictDiagramTotJointSourceRoofComparison（59行）

```lean
def strictBETotJointSourceRoofComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)

theorem strictBETotJointSourceRoofComparison_isWeakHomotopyEquivalence
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofComparison A P)
```

## 250. 同じ反対fiberから元の実roof比較への弱同値の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§248の厳密な同型は最終個別検査46841・終了0、元の実roof比較への係数移送と弱同値性は10774・終了0、BEへの特殊化は21507・終了0。319の鍵付き対象ビルド12,236 jobsと小監査191モジュール・1,336宣言が成功し、標準三公理のみ。実ハンドル16462・終了0、鍵返却済み。--class impl --wait 3600と1700秒guardを使った。二つの互換入口の宣言数0と既存補題の正しい定義元を確認する条件も引き続き検査した。

今回三本165行。一般の厳密な同型63行、既存のroof比較への移送43行、BEへの特殊化59行。§248の二本は見込み100〜200行に対して106行（上端との差−94行）、§249の特殊化は見込み80〜150行に対して59行（上端との差−91行）。検証済みは187本・12,118行／外枠22,000行。自分の187本の宣言数は1,329で、互換入口TensorConeUnitPointの宣言0を含む。小監査全体には既存定義元とHAの直接importer等の4本も加えている。

元のnative fiberの反対要素圏から、同じsource frame・右置換・第一分解を使う元のhammock余極限への実射を回収し、その実射が弱同値であることを既存定理から移した。native fiber射の弱同値性や、元の固定始域の全FunctorIsoへの正規化を完了とはしていない。既存の係数移送の法則として数学的な一覧の項目数は変えない。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。

登録候補：

- SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ElementsOppositeUniverseIso
- SerrePositivity.EInfinity.FrameHom.LiftedResolutionLeftRoof
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofComparison

次の照合では、normal要素圏のnerveから出る元のnative fiber射そのものをopFunctorで反対向きに写し、nerveOppositeIsoで§249の同じ反対要素圏の始域へ合わせる。この係数移送の元の写像を追跡した上で、元の指定pathと同じroofの全族との照合に進む。opによる表示の変更だけで弱同値性が証明されたとはしない。

## 251. 元のnative fiber射そのものの反対表示と弱同値性の反映（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

§250の基準roof射と始域の向きを合わせるため、元のstrictBETotJointSourceNativeTwistedFiberMapそのものをopFunctorで写し、元のnerveOppositeIsoの逆を前合成する。同じnerve反転を戻すと元の実射のop反転を厳密に回収する。この表示を別の同値の存在へ変更しない。

op反転による弱同値保存の既存定理を二度使い、同じop自己同値の単位の自然性と弱同値の消去則で元の射の弱同値性へ戻す。始域・終域のKan性を新しい入力にしない。その反映則と同じnerve反転同型により、反対表示の弱同値性は元のtwisted fiber射の弱同値性と同値となる。さらに元のvertexFiberPullbackIsoの弱同値性を消去し、元のpullbackのnative fiber射自身との同値に戻す。

既存のop保存則・自己同値の単位・pullbackのfiber同型による係数移送の法則であり、新しい数学的な一覧項目は増やさない。二本で見込み100〜180行。反対表示を定義しただけで弱同値と主張せず、§249の同じ基準roof比較との指定pathを保つ照合は引き続き残る。

### 251.1 型

一般版は任意の `{X Y : SSet.{u}} (f : X ⟶ Y)`。BE版の共通入力は `(A : Type u) [CommRing A]`。

#### OppositeWeakHomotopyReflection（36行）

```lean
theorem opposite_map_isWeakHomotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map f) ↔ IsWeakHomotopyEquivalence f
```

#### StrictDiagramTotJointSourceNativeOppositeFiber（84行）

```lean
def strictBETotJointSourceNativeOppositeFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      (vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op

theorem strictBETotJointSourceNativeOppositeFiberMap_recover (P : strictBETotJointHomIndex A) :
    (nerveOppositeIso
      (C := (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)).hom ≫
        strictBETotJointSourceNativeOppositeFiberMap A P =
      SSet.opFunctor.map (strictBETotJointSourceNativeTwistedFiberMap A P)

theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeTwistedFiberMap A P)

theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff_original
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

## 252. 元のnative fiber射の反対表示と弱同値性の同値を検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§251の最終個別検査42295は終了0。op自己同値の単位の成分はIso.app_homで表示を合わせ、その自然性を元のfとopFunctor.mapの二重適用の等式として明記して既存保存則を反映した。元のnative fiberの反対表示と元のtwisted fiber射の弱同値性の同値、さらに同じvertexFiberPullbackIsoを消去して元のpullbackのnative fiber射自身との同値まで示した。

320の鍵付き対象ビルド12,230 jobs成功、小監査193モジュール・1,344宣言、標準三公理のみ。実ハンドル1058・終了0、鍵返却済み。--class impl --wait 3600と1700秒guardを使った。二つの互換入口の宣言数0と既存補題の定義元の検査も維持した。新しい宣言名はgit grepでmainのSerrePositivity全体に存在しないことを確認した。

今回二本120行（一般版36行、BE版84行）、見込み100〜180行に対し上端との差−60行。検証済み189本・12,238行／外枠22,000行。自分の宣言数は1,337で、互換入口の宣言0を含む。小監査全体には既存定義元とHAの直接importer等4本を加えている。既存のop・自己同値の単位・pullbackのfiber同型による係数移送の法則として、数学的な一覧項目は増やさない。

sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。今回の同値は実射の弱同値性を別の射の存在へ弱めていない。反対表示の射自体が弱同値であることを結論するには、§250の同じ実roof比較との指定pathを保つ照合がなお必要である。

登録候補：

- SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.OppositeWeakHomotopyReflection
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeOppositeFiber

次に使う既存のAPIはKanHammockHomPinchedMap_weakとKanHammockHomPinchedMap_app_valで、元のEx∞ hammock Homから同じ局所化頂点のpinched Homへの実射と、その全単体の値を保持している。元の同じ局所化比較・端点の指定pathを追跡し、§250の実roof射と今回のnative射の反対表示を全単体・全族として照合する。零単体の回収やπ₀だけの一致ではR03dの全同型の正規化が済んだとはしない。Tot側の停止点3b-4aはまだ未到達。

## 253. 同じroofから同じ局所化頂点のpinched Homへの比較（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。

元のstrictBETotJointSourceRoofComparisonを、元のAsSmallComparison.colimitIso、同じEx∞単位、元のkanHammockHomPinchedMapへ合成した。元の全モデル相対圏modelRelativeCategoryを使い、cofibrant/bifibrant相対圏へ置き換えていない。この実射の弱同値性は既存の三つの比較の弱同値性を合成して得る。また元の全標的比較asSmallKanHammockHomFamilyMapの同じ成分を使った構成と厳密に等しいことを、元のEx∞単位の自然性で示した。

全単体の値の既存式をBEへ直接展開するとwhnfの200,000 heartbeatsに達したため、上限を変更せず、一般の相対圏で同じ値と同じ全パラメータの式に名前を付けて分割した。最終個別検査1450は終了0。これは証明・elaborationの分割であり、元の全次数・全単体の主張を保持する。二本合わせて見込み150〜260行。既存比較・係数移送・Ex∞単位・同じ評価式の前合成則なので、数学的な一覧項目は増やさない。

### 253.1 名前付き評価式の意味

C・X・Y・T・fは下記の型の通り。名前付き命題の定義は次の全次数・全単体の等式そのものである。

```lean
def KanHammockPinchedValueFormula {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) : Prop :=
  ∀ {n : ℕ} (s : T _⦋n⦌),
    (((f ≫ kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌)) s).val =
      kanHammockPinchedSimplexValue C X Y (f.app (Opposite.op ⦋n⦌) s)
```

BEではfに同じstrictBETotJointSourceRoofKanComparisonを代入する。native fiber射との同一視はまだ残る。

### 253.2 型

一般版の共通入力は `(C : RelativeCategory.{u}) (X Y : C.category)`。BE版は `(A : Type u) [CommRing A]`。

#### KanHammockPinchedSimplexValue（49行）

```lean
def kanHammockPinchedSimplexValue {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    (kanHammockNerve C) _⦋n + 1⦌

theorem kanHammockHomPinchedMap_value {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    ((kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌) s).val =
      kanHammockPinchedSimplexValue C X Y s

def KanHammockPinchedValueFormula {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) : Prop

theorem kanHammockHomPinchedMap_value_family {T : SSet.{u}}
    (f : T ⟶ exInfinity.obj (colimitGraph C.weakEquivalences X Y)) :
    KanHammockPinchedValueFormula C X Y f
```

#### StrictDiagramTotJointSourceRoofPinched（116行）

```lean
abbrev strictBETotJointRoofSourceObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category

abbrev strictBETotJointRoofTargetObject (P : strictBETotJointHomIndex A) :
    (modelRelativeCategory (operad A).Algebra).category

def strictBETotJointSourceRoofKanComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      exInfinity.obj
        (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
          (modelRelativeCategory (operad A).Algebra).weakEquivalences
          (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P))

theorem strictBETotJointSourceRoofKanComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofKanComparison A P)

theorem strictBETotJointSourceRoofKanComparison_unit (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofComparison A P ≫ exInfinityUnit.app _ ≫
      (FrameHom.asSmallKanHammockHomFamilyMap (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)).app
          (strictBETotJointRoofTargetObject A P) =
      strictBETotJointSourceRoofKanComparison A P

def strictBETotJointSourceRoofPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (strictBETotJointRoofTargetObject A P)))

theorem strictBETotJointSourceRoofPinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofPinchedComparison A P)

theorem strictBETotJointSourceRoofPinchedComparison_app_val (P : strictBETotJointHomIndex A) :
    SimplicialLocalization.KanHammockPinchedValueFormula
      (modelRelativeCategory (operad A).Algebra)
      (strictBETotJointRoofSourceObject A P) (strictBETotJointRoofTargetObject A P)
      (strictBETotJointSourceRoofKanComparison A P)
```

## 254. 同じ局所化頂点のpinched Homへの基準射の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§253の最終個別検査1450は終了0。321の鍵付き対象ビルド12,238 jobs、小監査195モジュール・1,363宣言が成功し、標準三公理のみ。実ハンドル73896・終了0、鍵返却済み。--class impl --wait 3600・1700秒guardを使った。新しい宣言名はmainのSerrePositivity全体にないことをgit grepで確認した。二つの互換入口の宣言0と既存補題の定義元の検査も維持している。

今回二本165行（一般の全単体の値の分割49行、BEの基準射116行）。見込み150〜260行に対し上端との差−95行。検証済み191本・12,403行／外枠22,000行。自分の宣言数は1,356で、互換入口の宣言0を含む。監査全体には既存定義元・HAの直接importer等4本も含む。

元の実roof比較から同じ全モデル相対圏のKan hammock Hom・同じ局所化頂点のpinched Homへの実射と、その弱同値性、元の全標的AsSmall比較と同じEx∞単位の厳密な三角形を保存した。全次数・全単体の値の式は名前付き命題の定義でそのまま保持し、elaborationの分割によって計算上限を上げずに検査した。sorry・独自公理0、[ModelCategory SSet]なし、既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainの変更なし。既存の合成・係数移送・証明の分割として一覧の項目数は増やさない。

登録候補：

- SerrePositivity.EInfinity.SimplicialLocalization.KanHammockPinchedSimplexValue
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPinched

次は既存CoherentLocalizationComparison.pinchedEquivalenceを、元のstrictBETotRightFrameCoherentComparisonの同じ第二成分に適用し、同じ指定二胞体の両端の共役として元のCAlg源へ輸送する。probe始域と右置換標的を元のnative fiberの両端へ合わせること、元のnative射と基準roof射との全単体での照合、R03dの元の固定始域の全FunctorIsoへの正規化はなお残る。

## 255. 同じ指定局所化比較と端点同型によるroof基準射の輸送（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

既存のCoherentLocalizationComparison.pinchedEquivalenceを元のstrictBETotRightFrameCoherentComparisonの同じ第二成分に適用する。比較関手と指定二胞体の両端成分への分解は既存の厳密な等式から得る。さらに元のprobe比較と元の全標的右置換単位を使い、基準roof射の両端を元のモデル源の頂点へ合わせる。新しい比較同値や指定経路は選び直さない。既存の合成・係数移送の法則として項目数は増やさない。二本183行。対象ビルド・監査はこれから実行し、成功前にコードをコミットしない。

これは弱同値である基準射の端点を揃える段であり、元のnative fiber射そのものの弱同値性はまだ主張しない。同じnative射との全単体の照合と元の固定始域の全FunctorIsoへの正規化が残る。

共通入力は `(A : Type u) [CommRing A]`。型は以下のとおり。

#### StrictDiagramTotJointSourceRoofNativePinched（84行）

```lean
def strictBETotJointRoofLocalizationComparison (P : strictBETotJointHomIndex A) :
    FrameHom.CoherentLocalizationComparison
      (SimplicialLocalization.hammockLocalizationNerveMap
        (modelRelativeCategory (operad A).Algebra)) (strictBETotModelSource A)

def strictBETotJointSourceRoofNativePinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofSourceObject A P)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (strictBETotJointRoofTargetObject A P)))

theorem strictBETotJointSourceRoofNativePinchedComparison_weak (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNativePinchedComparison A P)

theorem strictBETotJointSourceRoofNativePinchedComparison_normalization
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofNativePinchedComparison A P =
      strictBETotJointSourceRoofPinchedComparison A P ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
          (strictBETotJointRoofLocalizationComparison A P).equivalence.hom _ _ ≫
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofSourceObject A P))))
          ((strictBETotJointRoofLocalizationComparison A P).triangle.toNatIso.app
            (HomotopyCategory.mk (nerveVertex (strictBETotJointRoofTargetObject A P))))).hom
```

#### StrictDiagramTotJointSourceRoofEndpointTransport（99行）

```lean
def strictBETotJointRoofProbeEndpointIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofSourceObject A P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))

theorem strictBETotJointRoofTargetReplacement_vertex (P : strictBETotJointHomIndex A) :
    ((nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A).app
      (Opposite.op ⦋0⦌)) (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)) =
      (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P))

def strictBETotJointRoofTargetEndpointUnitIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P)))

def strictBETotJointSourceRoofNormalizedPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))

theorem strictBETotJointSourceRoofNormalizedPinchedComparison_weak
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNormalizedPinchedComparison A P)
```

## 256. 同じ指定比較と端点輸送の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

322の鍵付き対象ビルド12,241 jobsと小監査197モジュール・1,391宣言が成功し、標準三公理のみ。実ハンドル80601・終了0、鍵返却済み。--class impl --wait 3600、1700秒guardを使用。二つの互換入口の宣言0と既存補題の定義元の検査を維持した。二本の新規宣言名はmain EInfinityとのgit grepで重複なし。sorry・独自公理0、計算上限変更なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainを変更していない。

今回二本183行。検証済み193本・12,586行／外枠22,000行、自分の宣言は1,384。監査には既存定義元等の4モジュールも含む。既存の合成・係数移送の法則で項目数は増やさない。

登録候補：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativePinched
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofEndpointTransport

元のnative fiber射との全単体の比較と、その実射の弱同値性はなお残る。次は元のnative Hom入力の頂点を元のモデル源の二頂点と厳密に合わせ、twisted-arrow fiberの比較の両端を明示する。

## 257. 同じnative入力の端点と既存twisted・pinched比較の単位則（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

元の固定始域則を零単体へ評価して、元のnative Hom入力が元の二つのCAlg源の頂点の対であることを示す。nerveMapの頂点、直積の射影則、零次の定値則を型を分けて適用する。一般のtwisted Homからpinched Homへの比較は、既存のcoslice比較の同じ指定逆とcosliceの右写像空間比較の合成とする。反転したtwisted Homは同じedgewise二射影の同じ指定逆で戻す。元のcoslice・edgewise比較との二つの単位三角形は全FunctorIsoとして保持する。既存比較の合成・単位・係数移送の法則であり、新しい数学の項目は足さない。見込み二本150〜220行。対象ビルド・監査の前にはコードをコミットしない。

既存RoofPrefixFamilyTriangle.native_family_eq_roof_arrowは一般の同じ宇宙の相対圏で、全roof族の区間評価を同じaugmentationの逆と評価の合成と同定する。両端のbifibrancyを追加せず使える。この全族則を、同じfiber要素圏へ運んだroof族に適用し、元の補正pairingが保存する同じ底のpathと合わせるのが次の接続点。いまの二本だけから元のnative射の弱同値性は結論しない。

BEの共通入力は `(A : Type u) [CommRing A]`。一般版は `{C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌)`。

#### StrictDiagramTotJointHomInputVertex（73行）

```lean
theorem strictBETotJointNativeHomInput_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).1.unop)),
       (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).2))

theorem strictBETotJointNativeHomInput_model_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).1.unop))),
       (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).2)))
```

#### TwistedHomPinchedComparison（73行）

```lean
def twistedArrowHomPinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y) (Basic.pinchedHom x y)

def twistedArrowHomOppositePinchedEquivalence :
    QCatEquivalence (twistedArrowHomSpace x y).op (Basic.pinchedHom x y)

theorem twistedArrowHomOppositePinchedEquivalence_hom :
    (twistedArrowHomOppositePinchedEquivalence x y).hom =
      (isQCatEquivalence_of_trivialKanFibration
        (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
      edgewiseRight (twistedArrowHomSpace x y) ≫
      (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
      (cosliceFiberRightMappingEquivalence x y).hom

def twistedArrowHomPinchedEquivalence_coslice :
    FunctorIso (cosliceTwistedHomMap x y ≫ (twistedArrowHomPinchedEquivalence x y).hom)
      (cosliceFiberRightMappingEquivalence x y).hom

def twistedArrowHomOppositePinchedEquivalence_edgewise :
    FunctorIso
      (edgewiseLeft (twistedArrowHomSpace x y) ≫
        (twistedArrowHomOppositePinchedEquivalence x y).hom)
      (edgewiseRight (twistedArrowHomSpace x y) ≫
        (twistedArrowHomPinchedEquivalence x y).hom)
```

## 258. 元のnative実射を元のroofと同じpinched Homへ運ぶ（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

§257の端点の等式で元のnative twisted fiberの反転を元の両端のtwisted Homに合わせ、§257の一般比較を合成する。その同値に元のstrictBETotJointSourceNativeOppositeFiberMapを合成した実射を定義する。新しい弱同値性の前提を置かず、この実射の弱同値性と元のstrictBETotJointSourceNativeFiberMapの弱同値性が同値であることを、既存の反転則と比較の弱同値性の消去則で示す。見込み80〜130行に対し81行の下書き。既存の合成・係数移送・消去則の分割で、項目数は増やさない。

個別の一時結合検査26130は終了0。対象ビルド・小監査はまだなのでコミットしない。323は端点のモデル源表示に既存BEのモデル構造をlocal instanceで明示する前のソースを読み、失敗した。固有名のlocal instanceを追加し、元のジョブの終了を確認して324を一枚の整理券で実行中。計算上限は変更していない。

共通入力は `(A : Type u) [CommRing A]`。

#### StrictDiagramTotJointSourceNativePinched（81行）

```lean
def strictBETotJointNativeFiberPinchedEquivalence (P : strictBETotJointHomIndex A) :
    QCatEquivalence
      (vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op
      (Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))))

def strictBETotJointSourceNativePinchedMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))

theorem strictBETotJointSourceNativePinchedMap_weak_iff_original
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativePinchedMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P)
```

この実射とstrictBETotJointSourceRoofNormalizedPinchedComparisonは同じ始域・標的を持つ。残る中核は、元の補正pairingの指定された底のpathと、元のroof全族のaugmentationを、全パラメータの区間評価で照合すること。既存intervalFamilyHom_eq_imp_homotopyは任意のパラメータに対してこの全評価の等式からホモトピーを与えるので、π₀のみへの弱化を避けられる。現時点ではその等式を示していない。

## 259. 元のnative射を同じpinched標的へ運ぶ既存則の検収（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 23（うち追加 11）。R03dは未完了。

324の対象ビルド10,628 jobs・小監査199モジュール1,409宣言が成功（実ハンドル31286・終了0）。325は元のnative実射の対象ビルド12,248 jobs・小監査200モジュール1,418宣言が成功（実ハンドル30857・終了0）。いずれも標準三公理のみ、鍵返却済み。--class impl --wait 3600、1700秒guardで各一枚の整理券を使い、前のジョブの終了を確認して次へ進めた。既存補題の定義元と二つの互換入口の宣言0の検査も維持。今回の全新規宣言名についてmain SerrePositivity全体とのgit grepで重複がないことを確認した。

今回三本229行（端点75、一般比較と全単位三角形73、同じnative実射81）。前二本の見込み150〜220行に対し148行、第三の見込み80〜130行に対し81行。検証済み196本・12,815行／外枠22,000行、自分の宣言は1,411。sorry・独自公理0、計算上限変更なし、[ModelCategory SSet]なし。既存FramedLimit*・CAlgUnderlyingDerivedComparison・⑤a・公式入口・公式監査・mainを変更していない。

登録候補：

- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInputVertex
- SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomPinchedComparison
- SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativePinched

元の実射と基準roof射の始域・標的が揃い、元の実射の弱同値性を厳密に反映する比較まで検証した。両実射の全族の同定自体は未証明であり、R03d・3b-4aの完了とはしない。次の最小の主張は、両実射を区間写像空間へ送ったintervalFamilyHomの等式。既存RoofPrefixFamilyTriangleの全roof族の式と、元の補正pairingの同じ底のpathとの照合が必要である。

## 260. R03dの同じ実射の全族照合をR03hとして追加（11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03hは未完了。

§19の「同じまとまり・一つの見込み1,500行以下」の枠により、元のnative実射と元のroof基準射の全族の照合をR03hとして追加する。新しいまとまりではなくR03dの元のfiber射自身の弱同値性と固定始域の全比較の正規化に必要な中間の定理。⑤aの欄の型を変えない。型を弱めず、追加の弱同値性・充填性を前提にしない。

型（共通入力 `(A : Type u) [CommRing A]`、`intervalFamilyHom`はKerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories、`pinchedHomToIntervalMappingSpace`はKerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces）：

```lean
theorem strictBETotJointSourceNativePinchedMap_interval_family
    (P : strictBETotJointHomIndex A) :
    intervalFamilyHom
      (strictBETotJointSourceNativePinchedMap A P ≫
        pinchedHomToIntervalMappingSpace _ _) =
    intervalFamilyHom
      (strictBETotJointSourceRoofNormalizedPinchedComparison A P ≫
        pinchedHomToIntervalMappingSpace _ _)
```

この全称命題を/private/tmp/isw2-nativepinched-family-type.leanで#checkし、実ハンドル67282・終了0。これは型の検査であり証明ではない。Lean本体に未証明の宣言・sorryを置いていない。

見込み850〜1,400行。内訳：元のfiber要素圏のroof族をRoofPrefixの同じ族へ運ぶ係数・自然性の照合250〜400行、元の補正pairingを同じcoslice・edgewise比較で区間評価し、保存された底のpathを使う全族の照合300〜600行、同じ局所化三角形・probe・右置換単位での共役と既存roof全族則の合成150〜250行、まとめ150行以内。未確定の中心は二番目であり、1,500行を超える新しい中間定理やまとまりの外のものが要ると分かった場合は、§19どおり検証済みを保存して報告する。

使用する既存の入口：RoofPrefixFamilyTriangle.native_family_eq_roof_arrow（一般の同じ宇宙の相対圏での全roof族）、CoherentLocalizationComparison.pinchedEquivalence_homとtriangle_naturality、pinchedEndpointEquivalence_family、今回のtwistedArrowHomPinchedEquivalence_cosliceとtwistedArrowHomOppositePinchedEquivalence_edgewise、元のstrictBETotJointSourceFiberPairingIso_postcomp（同じ底のpathの保存）。全族の評価の等式を得た後はintervalFamilyHom_eq_imp_homotopyとpinched・区間比較の弱同値性で、元の実射自身の弱同値性に戻す。以降も元の固定始域の全FunctorIsoへの正規化を省かない。

§255〜256のコードは3693013ba、§257〜259のコードは7edd92b76に保存済み。検証済み196本・12,815行／外枠22,000行。停止点3b-4aの完成報告ではない。

## 261. B4′の取り込み前採取を開始（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03hは未完了。B4′もまだ完了ではない。

検証済みLeanは670ef9d75までの履歴に保存済み。B4′開始時の作業木はクリーン。基準391b2a0d2から追加・変更されたLean（drafts除外、存在するソース）は197本。原ソースを/private/tmp/isw2-b4prime-20261115/original-sources.tar.gz、一覧を同ディレクトリfiles.json、元HEADとmainの記録をprovenance.jsonへ保存した。元HEADは670ef9d75、開始時mainはb29addabd。公式指示はmainのcitation-attributes.md §15とbulk-b3prime/B4/README.mdを読んだ。

最初の三本と次の八本、計11本のcollectと指定rewrite.pyによるプレビューが成功。確認済みのreview.jsonは全て空、追加import0、現ソースとの差分0本。自分の検証済み196モジュールのパスにはmodule-map.jsonとの一致0。これは残りの短名束縛の確認の代用にはせず、残りも採取する。

残りは8本以下ずつの組で採取・プレビューする単一の実行ハンドル41644へまとめた。各組で--class impl --wait 3600、鍵取得後280秒guard。前の組の終了・鍵返却の後に次の組を一度だけ出し、失敗や保留で停止する。複数の整理券を同時に出さず、同じ採取の時間切れを取り直すループも使わない。現在は第2組を実行中。mainのmerge・プレビュー反映・取り込み後の対象ビルドと小監査はまだ。古い索引を取り込み後のソースへ流用しない。

R03hの並行する紙と一時検査：元のfiber上の同じroof図式・augmentation・評価、同じ全単体の二列図式、元のAsSmall比較を通した実roof比較とRoofPrefix.familyMapの厳密な等式を一時ファイル/private/tmp/isw2-rooffiberprefix.leanで検査し、ハンドル47381・終了0。既存依存RoofPrefixColumnRoofの326対象ビルド7,211 jobsも成功（ハンドル57972・終了0）。新規本体モジュールを追加・コミットした検収ではないため、検証済み196本・12,815行の数は増やさない。B4′の参照採取中の原ソースも変更していない。B4′完了後にこの同じ型の法則を本体で検査し直し、元のnative pairingが保存する指定された底のpathとの全族照合へ戻る。

## 262. B4′採取19本の検収と、取り込み取り消しに由来する削除の事前確認（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

第2組の8本もcollect・プレビュー成功。19／197本が保留0・追加import0・差分0。第2組は待ち込み660.1秒で成功し鍵を返却した。採取そのものの実測は8本で約2分なので、以降は12本以下の約3〜4分の組、280秒guardを維持する形へまとめ直した。178本を15組へ分け、既済19本との重複・漏れがないことを集合で検査した。

切り替え時には、完了した第2組の次の第3組がまだ鍵待ちで、子のpayloadが起動していないことをpsで確認した。待ちのwrapper96924にだけSIGTERMを送り、既存のsignal handler・finallyによる整理券の片付けを経て、旧runner41644が終了143になった。採取の失敗や時間切れではなく、未起動の待ちだけの意図した取り消しである。その終了を確認してから、新しい単一runner38504を起動した。同時に複数の整理券は出していない。新しい進捗は/private/tmp/isw2-b4prime-20261115/progress-12.json、before-rXX・preview-rXXに記録する。新しい実行も各組一回ずつで、保留や失敗で停止する。mainはまだmergeしていない。

作業木を変えないgit merge-treeの事前確認では、共通祖先57705f223からmain側の取り込み取り消しedf81f92eが効くため、検証済みの自分の176本が削除扱いになった。対象一覧は/private/tmp/isw2-b4prime-20261115/merge-preview-absent-own-files.json。重複修正済みのStrictDiagramTotUniversalProbePointComparison・TensorConeUnitPointとモジュール一覧はmodify/delete、報告は内容競合の候補。最終のmergeでは、取り消しの目的だった重複が既に修正されている元の自分のソースを、検査済みプレビューから保持する必要がある。B3′で移動した別の本体ソース全体へ上書きせず、今回の197本と宣言の所有元表・module-mapに従う。公式入口や監査の取り消された登録は勝手に戻さず、調整役への登録候補に残す。mainの独立した変更は保持する。

鍵待ち中の一時検査では、同じ実roof全族の任意の後合成を、元の全augmentationの逆と評価の像へ戻す式まで検査できた（/private/tmp/isw2-rooffibercolumn.lean、199行、ハンドル26704・終了0）。同じ全FunctorIsoの定値族が元の指定成分に一致する法則も、既存の未ビルドの評価補題を一時結合して検査した（/private/tmp/isw2-constantisofamily-combined.lean、ハンドル53401・終了0）。どちらもプロジェクトのソースは変更しておらず、B4′後の本体の対象ビルド・小監査はまだ。検証済み196本・12,815行の数は維持する。

## 263. B4′採取55本と、同じ全augmentationの一時照合（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

B4′は55／197本の参照採取・プレビューが成功。全てreview.jsonは空、追加import0、原ソースとの差分0本。12本の組r00・r01・r02も280秒guardの範囲内で成功した（待ちを含む経過748.5秒・759.6秒・483.6秒）。同じ単一runner38504を継続し、これから第r03組。mainの実際のmergeはまだ行っていない。

取り込み前の全索引とプレビューをまとめる/private/tmp/isw2-b4prime-20261115/assemble-before.pyを準備した。全197本が重複・欠落なく揃い、全captureのsourceが現原ソースと一致することを検査してから、before-allと新しいpreview-allを作る。MERGE_HEADがあるとき、またはmain取り込み後には動かせないガードを置き、旧索引を取り込み後のソースへ流用しない。事前mergeで消える176本については、全てがedf81f92eの削除対象に含まれることもgit diff-treeと照合した。

R03hの一時検査では、同じroof図式・同じ全単体の二列図式・元のroof比較とRoofPrefix全族の一致・任意の後合成の全roof公式に続き、同じfull augmentationが元の全パラメータのaugmentation自身の引き戻しであることまで検査した。最初の全関手の照合は200,000 heartbeatに達したため上限を変えず、対象・射・一般のfiber包含の単体作用素の法則へ分割した。後者の等式輸送はGrothendieck.ιの元のeqToHomを射影して処理し、別の包含や別のpathに替えていない。最終/private/tmp/isw2-roofparameter2.lean（355行、一時入力全体）は実ハンドル3044・終了0。一般のfiber作用素の独立検査36768も終了0。

同じ元のnerveTransformationPostIsoの順射を元の全自然変換のNerveColumn.homへ戻す法則も/private/tmp/isw2-nervepostisocolumn.leanで検査し、実ハンドル80148・終了0。定値族の法則の検査53401も終了0。全て一時ファイルの個別検査で、プロジェクトには追加・変更していない。検証済み196本・12,815行／外枠22,000行の計数は維持。本体モジュールへの配置と対象ビルド・小監査はB4′後に行う。

以下は通過した一時の型（名称は本体反映時に新規宣言名との重複を確認する）。BE側の共通入力は `(A : Type u) [CommRing A]`、canonicalな既存modelCategory AとmappingCofibrantFactorization Aのlocal instanceのみを使う。既存構成の合成・単位・係数移送・証明分割の法則として一覧の項目数は増やさない。元のnative射とroof射の全族の等式、すなわちR03hそのものはなお未証明。

```lean
abbrev strictBETotJointRoofResolution (P : strictBETotJointHomIndex A)

def strictBETotJointSourceRoofFrameDiagram (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      (modelRelativeCategory (operad A).Algebra).category

def strictBETotJointSourceRoofFrameAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          (framedLimitProbe A (AsSmall.down.obj P).1.unop))

def strictBETotJointSourceRoofFrameEvaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))

lemma strictBETotJointSourceRoofFrameAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameAugmentation A P).app s)

lemma strictBETotJointSourceRoofFrameDiagram_weak
    (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameDiagram A P).map f)

def strictBETotJointSourceRoofFrameZigzag (P : strictBETotJointHomIndex A)

theorem strictBETotJointSourceRoofFrameZigzag_nerve
    (P : strictBETotJointHomIndex A) :
    (elementsOppositeUniverseNerveIso.{u+1,u}
      ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        (strictBETotJointRoofResolution A P).obj).obj
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))).hom ≫
      FrameHom.frameLeftRoofNerveMap (weakEquivalences (operad A).Algebra)
        (strictBETotJointRoofResolution A P).obj
        (strictBETotJointRoofResolution A P).augmentation
        (strictBETotJointRoofResolution A P).augmentation_weakEquivalence
        (fun f => (strictBETotJointRoofResolution A P).homotopicallyConstant f) ≫
      (Hammock.AsSmallComparison.graphIso (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
        LeftRoof.word).hom =
      nerveMap (strictBETotJointSourceRoofFrameZigzag A P)

theorem strictBETotJointSourceRoofKanComparison_prefix
    (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofKanComparison A P =
      SimplicialLocalization.RoofPrefix.familyMap
        (modelRelativeCategory (operad A).Algebra)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFrameAugmentation A P)
        (strictBETotJointSourceRoofFrameAugmentation_weak A P)
        (strictBETotJointSourceRoofFrameEvaluation A P)
        (strictBETotJointSourceRoofFrameDiagram_weak A P)

theorem strictBETotJointSourceRoofPinchedComparison_column_roof
    {E : SSet.{u+1}} [Quasicategory E] (P : strictBETotJointHomIndex A)
    (F : SimplicialLocalization.kanHammockNerve
      (modelRelativeCategory (operad A).Algebra) ⟶ E) :
    let R := modelRelativeCategory (operad A).Algebra
    let V := strictBETotJointSourceRoofFrameDiagram A P
    let p := strictBETotJointSourceRoofFrameAugmentation A P
    let hp := strictBETotJointSourceRoofFrameAugmentation_weak A P
    Arrow.mk
      (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
        ((strictBETotJointSourceRoofPinchedComparison A P ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F _ _) ≫
          SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk
      ((FrameHom.NerveColumn.augmentationIso
        (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F) V p
        (SimplicialLocalization.RoofPrefix.postcomp_augmentation_invertible R V p hp F)).inv ≫
        FrameHom.NerveColumn.hom
          (SimplicialLocalization.hammockLocalizationNerveMap R ≫ F)
          (strictBETotJointSourceRoofFrameEvaluation A P))

def strictBETotJointSourceRoofFullAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop)

theorem strictBETotJointSourceRoofFullAugmentation_app
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        ((strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop ≫
          framedLimitProbeComparison A (AsSmall.down.obj P).1.unop)

theorem strictBETotJointSourceRoofFullAugmentation_original
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointSourceRoofFullAugmentation A P).app s =
      (strictBETotJointSourceFrameAugmentation A).app
        ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤
          strictBETotJointSourceFrameIndex A).obj
            ((AsSmall.down.obj P).1.unop, s.unop.obj.unop))

theorem strictBETotJointSourceRoofFullAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFullAugmentation A P).app s)

def strictBETotJointRoofParameterIndex (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      strictBETotJointSourceFrameIndex A

theorem strictBETotJointRoofParameterIndex_obj (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (strictBETotJointRoofParameterIndex A P).obj s =
      (AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).obj
        ((AsSmall.down.obj P).1.unop, s.unop.obj.unop)

lemma sameSimplicialElementsFiberFunctor_degree {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I)
    {s t : (simplicialElementsCatDiagram G).obj i} (f : s ⟶ t) :
    ((simplicialElementsFiberFunctor G i).map f).hom.2 = f.down.hom

theorem strictBETotJointRoofParameterIndex_map (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    HEq ((strictBETotJointRoofParameterIndex A P).map f)
      ((AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).map
        ((𝟙 (AsSmall.down.obj P).1.unop, f.unop.down.hom.unop) :
          ((AsSmall.down.obj P).1.unop, s.unop.obj.unop) ⟶
            ((AsSmall.down.obj P).1.unop, t.unop.obj.unop)))

theorem strictBETotJointRoofParameterIndex_evaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameEvaluation A =
      strictBETotJointSourceRoofFrameDiagram A P

theorem strictBETotJointRoofParameterIndex_constant (P : strictBETotJointHomIndex A) :
    strictBETotJointRoofParameterIndex A P ⋙ strictBETotJointSourceFrameConstant A =
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop)

theorem strictBETotJointRoofParameterIndex_augmentation
    (P : strictBETotJointHomIndex A) :
    HEq (CategoryTheory.Functor.whiskerLeft (strictBETotJointRoofParameterIndex A P)
      (strictBETotJointSourceFrameAugmentation A))
      (strictBETotJointSourceRoofFullAugmentation A P)

private theorem sameFunctor_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {x y x' y' : C} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f g) : HEq (F.map f) (F.map g)

private theorem sameNatTrans_heq {I C : Type*} [Category I] [Category C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G')
    (ha : ∀ i, HEq (η.app i) (η'.app i)) : HEq η η'
```

定値族の法則（一般の準圏K・X、任意のT）と元の全augmentation同型の順射の法則：

```lean
lemma sameFunctorIso_constant_family {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (T : SSet.{u}) {f g : K ⟶ X} (e : FunctorIso f g) (x : K _⦋0⦌) :
    (constantFunctorCompIso T x f).inv ≫
      (e.precomp (SSet.const x : T ⟶ K)).hom ≫
      (constantFunctorCompIso T x g).hom =
        constantFunctorHomMap T (e.app x).hom

lemma sameNerveTransformationPostIso_column
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q]
    (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom = NerveColumn.hom L η
```

## 264. B4′採取67本と、元の指定augmentation同型の全制限の一時検査（11-15、途中）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。R03d・R03h・B4′は未完了。

B4′は67／197本のcollect・プレビューが成功し、review.jsonは全て空、追加import0、原ソースとの差分0本。r03は待ちを含め720.4秒で成功した。単一runner38504は第r04組を継続中。mainの実際のmerge、プレビュー反映、取り込み後の対象ビルド・小監査はまだ。取り込み前のソースは変えていない。

R03hの一時検査を、元の指定された全augmentationのFunctorIso自身の制限まで進めた。一般のnerve自然変換の全引き戻しが同じ反転同型を保つこと、全自然変換の表示変更がその同型を保つことを先に示し、元のstrictBETotJointSourceFrameAugmentationIsoを同じroofパラメータへ前合成した値が、同じfull augmentationのNerveColumn.augmentationIsoそのものであることをHEqで示した。対象ごとの同型へ置き換えず、同じ全関手同型の値を保存する。

/private/tmp/isw2-nervecolumnprecomp.leanはハンドル61860・終了0、一般の表示変更を含む/private/tmp/isw2-nervepostisoheq.leanは77461・終了0、BEの全制限を結合した/private/tmp/isw2-roofnativeaug.leanは45906・終了0。同じfiber上の全標的入力が元の同じ標的の定値図式・定値nerve写像であることも/private/tmp/isw2-rooftarget.leanで検査し94919・終了0。これらも一時検査だけで本体には未反映。元のnative射と基準roof射の全族の等式（R03h）と、元の固定始域の全FunctorIsoへの正規化は引き続き残る。検証済み196本・12,815行／外枠22,000行の計数は維持する。

使用する取り込み後の小監査の範囲も確認した。現在のAuditISW2BKCells325.leanは自分のモジュール一覧196本を全て含み、追加の既存4本（FrameConeClasses・NormalizedMooreReverseEvaluation・NormalizedMooreReverseExtendZero・NormalizedMooreReverseZero）と合わせて200本である。二つの互換入口の宣言0と既存補題の定義元の検査を維持する。新しい本体の証明分割を反映する際は、その変更後に改めて対象ビルドと小監査を行う。

追加した一時の型は以下のとおり。既存構成の反転・単位・合成・係数移送の法則と証明分割なので一覧の項目数は増やさない。一般版の共通openはNerveColumn・FunctorIso等の既存の定義元に対応し、BE版の共通入力は `(A : Type u) [CommRing A]` と既存のcanonical model/factorizationのみ。

```lean
lemma sameNerveColumn_whiskerLeft
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q) :
    (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor.map
      (NerveColumn.hom L η) = NerveColumn.hom L (CategoryTheory.Functor.whiskerLeft R η)

lemma sameNerveTransformationPostIso_precomp
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    HEq ((nerveTransformationPostIso η L hη).precomp (nerveMap R))
      (nerveTransformationPostIso (CategoryTheory.Functor.whiskerLeft R η) L
        (fun j => hη (R.obj j)))

lemma sameNerveTransformationPostIso_heq
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G') (he : HEq η η')
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated)
    (hη' : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η'.app i)).map L).toTruncated) :
    HEq (nerveTransformationPostIso η L hη) (nerveTransformationPostIso η' L hη')

lemma sameNerveTransformationPostIso_augmentation
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    (V : I ⥤ C) {X : C} (p : V ⟶ (CategoryTheory.Functor.const I).obj X)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map L).toTruncated) :
    nerveTransformationPostIso p L hp = NerveColumn.augmentationIso L V p hp

theorem strictBETotJointSourceRoofFullAugmentation_inverted
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    IsInvertibleEdge ((nerve.edgeMk
      ((strictBETotJointSourceRoofFullAugmentation A P).app s)).map
      (strictBETotModelSource A)).toTruncated

theorem strictBETotJointSourceFrameAugmentationIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P)))
      (FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P))

lemma sameSimplicialElementsFiberFunctor_projection {I : Type u} [SmallCategory I]
    (G : I ⥤ SSet.{u}) (i : I) :
    simplicialElementsFiberFunctor G i ⋙ simplicialTotalElementsProjection G =
      (CategoryTheory.Functor.const _).obj i

theorem strictBETotJointSourceTargetIndex_fiber (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A =
    (CategoryTheory.Functor.const _).obj ((strictBETotJointHomTargetIndex A).obj P)

theorem strictBETotJointSourceTargetIndex_nerve_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A) =
    SSet.const (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))

```

## 265. B4′ の採取の組の調整と、元の同じ標的置換の全制限則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 265.1 B4′ の現況

採取・プレビュー済みは 91／197 ファイル、各 review は空。12 本の組の鍵の実保持は直近で約134〜144秒だったため、未開始の r06 の整理券だけを取り下げ、残り106本を最大20本の6組（s00〜s05）にした。一回の実処理は引き続き gtimeout 280秒、待ちは --class impl --wait 3600、一枚だけ。旧 runner の143はこの未開始の取り下げの終了値で、採取や証明の検証失敗ではない。完了済み91本の索引は保持する。現在の runner は run-remaining-20.py、状況は progress-20.json。197本の全採取後に同じ元ソースから最終の preview-all を作り、それから main を取り込む。元の Lean ソースは変更していない。

### 265.2 同じ元の標的置換を、全関手同型として制限する

B4′ の待ち時間に、一時 Lean ファイルだけで次の既存構成の制限・単位の法則を確認した。元の全標的置換の逆を、同じ fiber 上で同じ標的頂点へ引き戻す全 FunctorIso として同定し、その hom を元の頂点成分の逆の定値族へ同定する。点ごとの同型の存在への置き換えはしていない。依存型の書換えは前合成則と HEq の合成に分け、計算上限は変更していない。

個別検査：isw2-rooftargetiso.lean（最終ログ rooftargetiso4、exit 0）、isw2-rooftargetconstant.lean（最終ログ rooftargetconstant2、exit 0）。既存の未ビルドの共通補題のソースを一時的に結合して検査したもので、本体の新規モジュールの対象ビルド・監査ではない。B4′ 完了後に共通の既存モジュールを import し、新規の法則だけを本体に分割して対象ビルドと小監査を行う。

R03h の本体、すなわち同じ corrected pairing の native fiber 射と元の roof の全 interval 族との等式はまだ残る。今回の二法則を R03h の完了とは数えない。

```lean
theorem strictBETotJointSourceTargetReplacementIso_fiber
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceTargetReplacementIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotTargetReplacementNativeIso A).precomp
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))))).symm

theorem strictBETotTargetReplacementNativeIso_symm_constant_family
    (P : strictBETotJointHomIndex A) :
    (constantFunctorCompIso
      (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (strictBETotTargetReplacementNativeIso A).symm
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
            (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))).hom ≫
      (constantFunctorCompIso
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
        (strictBETotModelSource A)).hom =
      constantFunctorHomMap
        (nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P))
        ((strictBETotTargetReplacementNativeIso A).app
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))).inv
```

## 266. B4′ の151本までの照合と、同じ全関手同型の反転・制限則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 266.1 B4′

現在の採取・プレビュー済みは 151／197。完了した各組の review は空、元のソースとの差分は0。各 compiler capture の source と元ファイルのバイト列も照合した。670ef9d75 以降の枝のコミットに Lean の変更はない。s02 までの採取を終え、同じ runner が s03 の一枚の整理券で継続中（--class impl --wait 3600、実処理280秒）。main の取り込みはまだ行っていない。残りの全採取、同じ原環境での最終プレビューの後に統合する。

取り込み後の検査の準備は、自レーン196本と既存の直接の確認対象4本（FrameConeClasses、NormalizedMooreReverseEvaluation、NormalizedMooreReverseExtendZero、NormalizedMooreReverseZero）の計200本。小監査も同じ200本を対象とし、互換用の二ファイルの宣言数0、および tensorFrameHomIso_point と normalizedMooreReverse_zero_inclusion の元の定義元を確認する。root や公式の監査は変更・実行しない。main 側の revert に由来する自レーンの削除を保持して統合する理由と対象は §262 のとおりで、統合直前に再照合する。

### 266.2 既存の反転と前合成の法則

isw2-opisoprecomp.lean（84行、一時ファイル）を lake env lean で検査し、最終ログ isw2-opisoprecomp13 は exit 0。元の FunctorIso.op の値を、同じ内部 Hom の反転同型による元の像へ端点だけ輸送したものとして同定した。逆射を既存の functorOppositeHomEquiv と合わせ、その既存の前合成則から、同じ全関手同型の反転と制限の両立を HEq で得た。単体ごとの、または点ごとの同型の存在への置き換えではない。

端点の Eq.mp の簡約と同型の共役式を別の小補題に分けた。計算上限は上げていない。以下は既存構成の輸送・前合成の法則とその証明の分割であり、一覧の新しい数学の項目には数えない。B4′ の元のソースには追加しておらず、追従後に本体の新規モジュールへ分けて対象ビルドと小監査を通す。R03h の同じ native 射と roof の全 interval 族の最終等式は未完である。

```lean
private lemma sameEqMp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b

lemma sameVertexIso_op_inv {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : VertexIso x y) :
    e.op.inv = homotopyCategoryOpHomEquiv x y e.hom

lemma sameFunctorIso_op_heq {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    HEq e.op (VertexIso.map (VertexIso.op e)
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom)

lemma sameVertexIso_conjugate_heq {Z : SSet.{u}} {a b a' b' : Z _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') :
    HEq ((eqToIso (congrArg HomotopyCategory.mk ha)).symm ≪≫ e ≪≫
        eqToIso (congrArg HomotopyCategory.mk hb)) e

lemma sameFunctorIso_op_conjugate {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op = (eqToIso (congrArg HomotopyCategory.mk
      (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex f))).symm ≪≫
      VertexIso.map (VertexIso.op e)
        (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso X Y).hom ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHomIso_vertex g))

lemma sameFunctorIso_op_inv {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso f g) :
    e.op.inv = functorOppositeHomEquiv f g e.hom

lemma sameFunctorIso_precomp_inv {A X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) (p : A ⟶ X) :
    (e.precomp p).inv = (SSet.mapHomotopyCategory ((pre p).app Y)).map e.inv

lemma sameFunctorIso_op_precomp {A X Y : SSet.{u}} [Quasicategory Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) (p : A ⟶ X) :
    HEq (e.precomp p).op (e.op.precomp (SSet.opFunctor.map p))
```

## 267. B4′ の191本までの確認と、同じnative augmentationのroofへの制限（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 267.1 B4′

採取とプレビューは 191／197。完了分の review は空、プレビューと元ソースのバイト列の差分は0。最後の s05（6本）を同じ一枚の整理券で継続中。実処理の上限280秒、--class impl --wait 3600を維持している。main はまだ取り込んでいない。統合直前の merge-tree も再確認した（main 58d6a0de9）。予覧で欠ける自レーン176本は全て以前の revert edf81f92e の削除であり、二つの修正済みLeanのmodify/delete、一覧JSON、報告の競合も前回と同じ。main の報告への独立した追記は0。B3′の新配置の変更を保持し、この自レーンの検証済みソースを落とさずに統合する。

### 267.2 元のnative側の全同型を同じroofへ合わせる法則

一時ファイル isw2-nerveleftop.lean と isw2-roofopaugmentation.lean を lake env lean で検査した。最終ログ nerveleftop と roofopaugmentation2 はともに exit 0。後者は検査用に既存の定義・以前の検証済み補題を結合した 821 行で、新しいnative側の部分は 118 行。これは本体の対象ビルドや監査の代用ではない。原環境のLeanソースには変更を入れておらず、本体へ分けた後に対象ビルドと小監査を行う。

元のfiberの反変入力を、同じ leftOp パラメータと既存の nerve 反転で表し、元の strictBETotJointSourceAugmentationDomainIso の全値を保持して制限した。§266の反転・前合成の法則と§264の全augmentationの制限則をつなぎ、同じ全 FunctorIso の fiber 制限が、同じroofのaugmentationIsoを反転して同じ入力へ引き戻したものに HEq で一致するところまで確認した。任意に別の同型を選んだり、点ごとの同値で代用していない。

以下は既存構成の反転・制限・端点輸送の法則と証明の分割であり、一覧の新しい数学には数えない。R03h の最終の interval 族の等式、元のnative fiber射自身の弱同値性、R03d は未完である。

```lean
lemma sameNerveLeftOp_input {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ Dᵒᵖ) :
    nerveMap F ≫ (nerveOppositeIso (C := D)).inv =
      (nerveMap (opOp C) ≫ (nerveOppositeIso (C := Cᵒᵖ)).inv) ≫
        SSet.opFunctor.map (nerveMap F.leftOp)

lemma sameFunctorIso_precomp_of_heq {K X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') (p : K ⟶ X) : HEq (e.precomp p) (e'.precomp p)

lemma sameFunctorIso_op_of_heq {X Y : SSet.{u}} [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') : HEq e.op e'.op

theorem strictBETotJointSourceAugmentationInput_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceAugmentationInput A =
    (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
      (nerveOppositeIso (C := ((simplicialElementsCatDiagram
        (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv) ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointRoofParameterIndex A P))

theorem strictBETotJointSourceAugmentationDomainIso_value :
    HEq (strictBETotJointSourceAugmentationDomainIso A)
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (strictBETotJointSourceAugmentationInput A))

theorem strictBETotJointSourceAugmentationDomainIso_fiber_value
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
          strictBETotJointSourceAugmentationInput A))

theorem strictBETotJointSourceAugmentationDomainIso_fiber_parameter
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotJointSourceFrameAugmentationIso A).precomp
        (nerveMap (strictBETotJointRoofParameterIndex A P))).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv))

theorem strictBETotJointSourceAugmentationDomainIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P)).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv))
```

## 268. B4′ 完了：B3′ の追従と重複修正後の統合検証（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 268.1 原環境の採取・プレビュー

基準391b2a0d2より後の自レーンの追加・変更Lean（draftsを除く）197本を、main取り込み前にcompilerで採取した。Leanの元ソースを固定し、各組のcollectは --class impl --wait 3600、実処理は280秒以内、一枚の整理券で順に実行した。元の検証済みコードのHEADは670ef9d75、最終プレビューのHEADは4723dc1ad（この間は報告だけの変更）。採取済みJSONのsourceと実ソースのバイト列を全件照合した。

最後に197本の索引をまとめ、同じ原環境のソースからmainの bulk-b3prime/B4/rewrite.py と namespace-rewrite-map.json・所有元表を使って preview-all を作り直した。結果は保留0、追加import0、書換え0ファイル・0行。openの個別解消を要する保留も0。古い索引で取り込み後のソースを再採取・再書換えする操作は行っていない。証跡は /private/tmp/isw2-b4prime-20261115/ の before-all、preview-all、preview-all-summary.json。

### 268.2 main の統合

main 58d6a0de9 を自レーンへ統合した。統合コミットは **81683a2ab**。以前の57705f223の取り込みを戻したrevert edf81f92eにより、通常のmerge予覧では自レーンの検証済み176本が削除されるため、削除の由来を全件照合して元の検証済みソースを保持した。二つの修正済みLean（StrictDiagramTotUniversalProbePointComparison、TensorConeUnitPoint）のmodify/delete、一覧JSON、報告の計4競合も解消した。main側の報告・一覧への独立した追記は0と確認した。

最終プレビューと統合後の自レーン197本は全件バイト一致。B3′の配置の変更はmainから入り、自レーンの書換えは0ファイル・0行である。登録候補は既存の **formalization-plans/stage-ii/is-w2-be-20261114-modules.json（196本）** を使用する。

### 268.3 対象ビルド・小監査・重複照合

共有鍵を --class impl --wait 3600 で一回取り、gtimeout 1700秒の中で200モジュールの対象ビルドと小監査を実行した。200本は自レーン196本に、FrameConeClasses・NormalizedMooreReverseEvaluation・NormalizedMooreReverseExtendZero・NormalizedMooreReverseZeroの既存4本を加えたもの。対象モジュールの一覧は一時ディレクトリの postmerge-targets.json。

- 対象ビルド：成功（依存を含む12,346 jobs）。rootのビルドではない。
- 小監査：/private/tmp/AuditISW2BKCells325.lean、200モジュール・**1,418宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。
- TensorConeUnitPoint・NormalizedMooreReverseZeroは宣言数0。tensorFrameHomIso_pointの定義元はFrameConeClasses、normalizedMooreReverse_zero_inclusionの定義元はNormalizedMooreReverseEvaluationと実環境で確認した。既存の定理を使う修正e0c5190ecを含む状態で成功している。
- 宣言名の照合：自レーンのmanifest群等から562ファイル・1778個の名前を取り、mainのEInfinity/3745ファイル・13373個の名前と照合。異なるファイル間の同名宣言は0、自レーン内部も0。これは名前付きのソース宣言の照合で、上の実環境での監査と分けて記録する。
- 自レーン対象のgit diff --check：通過。

ビルドと監査のログは /private/tmp/isw2-b4prime-20261115/build327.log、統合の検収記録は merge-result.json、重複照合は /private/tmp/isw2-b4prime-20261115/declaration-collision-scan.json。

### 268.4 /goal の続き

B4′は完了。R03hの単位・反転・全augmentation制限の個別検査済みの法則を本体の新規ファイルへ分けて検証し、同じnative fiber射と元のroofの全interval族の照合を続ける。R03dの全関手同型と元の固定始域の同型との照合、3b-4aの残りは未完。点ごとの同値で置き換えず、外枠22,000行と型つき一覧の規則を維持する。

## 269. 同じroof・native augmentationの照合則の本体化と、同じ全変換の射（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 269.1 検収

§263〜267の個別検査済みの法則を本体の新規15モジュールへ分けた。元の同じroofのラベル・全augmentation・標的置換単位を保持したまま、元の全関手同型のfiber制限まで照合する。既存のMapHomotopyCategoryComp・FunctorIsoWhiskerCancellation・FunctorIsoVertexEvaluation等はimportして使い、再定義していない。公開importの不足と名前空間のopenを補い、最終の鍵付き対象ビルド330で確認した。

さらに、既存の全straightening関手で同じ底上の射を写す共通1本と、その値を元のraw/native Homの両変数の全変換にするBE1本を追加した。これはR03dの同じ射の定義の部分であり、元の実射を別の射へ置き換えていない。mの弱同値性を仮定していない。元の単位を保つ延長を後で適用し、可逆性と固定始域の元の指定同型との一致を証明する必要が残る。

コードのコミット：**e879e4d7f**。新規17本（共通6・BE11）、**1,345行・90宣言**。既存のLeanの変更は0。登録候補JSONは is-w2-be-20261114-modules.json の **213本**に更新した。入口と公式監査への登録は調整役の取り込み時の対象。

- 鍵：--class impl --wait 3600、一枚の整理券、実処理gtimeout 1700秒。
- 対象ビルド：新規17本、成功（依存を含む12,266 jobs）。
- 小監査：AuditISW2BKCells330.lean、**217モジュール・1,508宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。二つの互換モジュールの宣言数0と既存定理の定義元の検査も継続して成功。
- 宣言名の照合：main d2354cf40に固定し、自レーン579ファイル・1,829個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build330.log、isw2-validation330.json、isw2-declaration-collision-scan330.json。§268の重複照合の証跡はB4′ディレクトリに固定したコピーへリンクを揃えた。

### 269.2 規模と残り

3b-4の実測は **213モジュール・14,160行・1,501宣言**（小監査の既存確認対象4本はこの実測に含めない）。外枠22,000行まで7,840行。既存構成の単位・反転・制限の法則と証明の分割なので、今回の追加を一覧の新しい数学のIDとしては数えない。

§260のR03hの850〜1,400行という見込みは、前提の法則・照合データだけで15本・1,262行になったため、完成までの総増分の見込みとしては低かった。残る主等式の証明は、同じcorrected pairingの全族を同じroofの全族へ合わせる部分で、見込み450〜850行。前提の実測とこの主等式を合わせるとR03hの一群は1,712〜2,112行程度になる。新しい数学の中間の主張自体が1,500行を超える見込みや、別のまとまりが必要になった場合は§19の条件で報告する。

R03hの最終interval族の等式、同じnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の指定同型との一致は未完である。R02・R03・R04・R05、R11・R12のTotの分も引き続き残る。今回の全変換の射を可逆とみなしたり、対象ごとの同値で置き換えたりはしていない。

### 269.3 今回の新しい射の定義の型

以下はR03dの射の定義の分割。§263〜267に記録した法則の型は同じで、今回本体の名前空間へ配置した。privateな端点輸送の補題の型も§263・§266に記録済み。

#### LeftStraighteningDiagramHom

```lean
def leftStraighteningInfinityDiagramHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    FunctorHom (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)
```

#### StrictDiagramTotJointNativeTransformation

```lean
def strictBETotJointSourceNativeTransformation
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom) :
    FunctorHom (strictBETotJointRawHomCoherent A) (strictBETotJointNativeHomCoherent A)
```

### 269.4 新規の登録候補

- `SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoWhisker`（120行）
- `SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveLeftOpInput`（31行）
- `SerrePositivity.EInfinity.FrameHom.NerveColumnWhiskering`（102行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame`（108行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofGraph`（76行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPrefix`（75行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofColumn`（66行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofAugmentation`（75行）
- `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws`（41行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofParameter`（136行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativeAugmentation`（75行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetFiber`（91行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceOppositeAugmentation`（157行）
- `SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily`（46行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetUnit`（64行）
- `SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom`（38行）
- `SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeTransformation`（44行）

## 270. 元の twisted-arrow の三単体の四辺の座標（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 270.1 既存構成の法則の分割

B4′は§268で完了し、§269の検証済み17本も枝に保存済み。/goalの続きとして、元のcorrected pairingの単位を調べるための座標計算を新規1本に分けた。標準三単体の二つの三角形の合成則、既存の同じedgewiseWeightIsoと左右包含・面の式を使う。新しい数学のIDの追加ではなく、既存構成の合成・射影の前提計算である。

同じtwisted-arrowの辺の始点は三単体の内側の辺（1,2）、終点は外側の辺（0,3）。左射影を反転表示から戻すと（0,1）、右射影は（2,3）になる。したがって同じ三単体の合成則を、元のcorrected pairingの代表辺へ適用できる。任意の単体集合についての法則で、[ModelCategory SSet]・Kan性・計算上限の変更はない。

これは元の単位の評価を調べる前提の計算である。R03hの全interval族の等式やR03dの全関手同型はまだ証明していない。個々の頂点での射の等式だけから全変換の一致を結論しない。今後は元の全straightening変換と元の固定始域の同型を、同じ局所化・Yonedaの単位で照合する必要がある。

### 270.2 型

以下は新規ファイルの全13宣言の型。既存の辺・三角形を端点つきで読むdefも含めて記録する。

#### TwistedArrowThreeSimplexCoordinates（183行）

```lean
def twistedSquareStdEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SSet.Edge (X := (Δ[n] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm i) (stdSimplex.obj₀Equiv.symm j)

def twistedSquareStdTriangle (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Edge.CompStruct (twistedSquareStdEdge n i j hij)
      (twistedSquareStdEdge n j k hjk) (twistedSquareStdEdge n i k (hij.trans hjk))

lemma twistedSquareStd_three_composite :
    HomotopyCategory.homMk (twistedSquareStdEdge.{u} 3 0 1 (by decide)) ≫
      HomotopyCategory.homMk (twistedSquareStdEdge 3 1 2 (by decide)) ≫
        HomotopyCategory.homMk (twistedSquareStdEdge 3 2 3 (by decide)) =
      HomotopyCategory.homMk (twistedSquareStdEdge 3 0 3 (by decide))

lemma twistedSquare_three_composite {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C) :
    HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 1 (by decide)).map σ) ≫
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 1 2 (by decide)).map σ) ≫
        HomotopyCategory.homMk ((twistedSquareStdEdge 3 2 3 (by decide)).map σ) =
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 3 (by decide)).map σ)

lemma twistedSquare_source_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2)) =
      (stdSimplex.edge 3 1 2 (by decide)).down.toOrderHom

lemma twistedSquare_target_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2)) =
      (stdSimplex.edge 3 0 3 (by decide)).down.toOrderHom

def twistedSquareThreeSimplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (Δ[3] : SSet.{u}) ⟶ C

lemma twistedSquare_source_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 1 s =
      stdSimplex.map (stdSimplex.edge 3 1 2 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_target_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 0 s =
      stdSimplex.map (stdSimplex.edge 3 0 3 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_left_inclusion :
    (stdSimplex.opIso ⦋1⦌).inv ≫ joinInl (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ (edgewiseWeightIso 1).inv

lemma twistedSquare_right_inclusion :
    joinInr (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ (edgewiseWeightIso 1).inv

lemma twistedSquare_left_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm (SSet.opObjEquiv ((edgewiseLeft C).app _ s)) =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ twistedSquareThreeSimplex s

lemma twistedSquare_right_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm ((edgewiseRight C).app _ s) =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ twistedSquareThreeSimplex s
```

### 270.3 検証

コードのコミット：**b528ea6a1**。新規1本・183行、型を上に記録した名前付き13宣言（生成された定数を含む実環境26宣言）。既存のLeanの変更は0。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後の処理はgtimeout 1700秒。処理終了とともに返却済み。
- 対象ビルド331：新規1本、成功（依存を含む1,555 jobs）。longLineのスタイル警告のみ。計算上限・linterの設定を上げたり無効にしたりしていない。
- 小監査：AuditISW2BKCells331.lean、218モジュール・**1,534宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。二つの互換モジュールの宣言数0と既存の定理の定義元の検査も成功。
- 宣言名：main d2354cf40に固定し、自レーン580ファイル・1,842個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build331.log、isw2-validation331.json、isw2-declaration-collision-scan331.json。

3b-4の実測は**214モジュール・14,343行・1,527宣言**。外枠22,000行まで7,657行。今回は既存の合成則の分割で、一覧のIDの完了数と追加数は変わらない。登録候補は自レーンのJSONだけに追記し、共通の入口と公式監査は変更していない。

登録候補：`SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowThreeSimplexCoordinates`。R03h・R03dの未完の範囲は270.1のとおりで、/goalは継続。

## 271. 元の射影の合成則と、元の単位ラベルの pairing の像（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 271.1 既存の構成の法則の分割

§270の座標計算を、実際の左右射影の辺に接続した。twisted-arrowの頂点を同じ重みの逆で元の辺へ戻し、同じ辺の左射影（反転を戻したもの）、始点の辺、右射影の合成は終点の辺になることを証明する。これは任意の単体集合についての既存の合成則で、Kan性や[ModelCategory SSet]を仮定しない。両端の辺の類が可逆で、外側の辺が元の単位の合成なら、内側の辺の類は恒等射になるという相殺則も分けた。

さらに元の全twisted pairingの零単体は元のラベルの実射そのものであることを計算した。その同じ全pairingを元のモデル源へ後合成する値も保持する。BEの元の単位ラベルを全要素圏の同じ次数0の要素として読み、そのnative pairingの像が、元のsource-frame増大写像・probe比較・標的置換単位の同じ合成になることを照合した。新しい単位や逆は選んでいない。

これはR03d/R03hの証明の前提の合成・単位・射影の法則であり、一覧の新しい数学のIDは追加しない。新規3本（共通2・BE1）、312行。各ファイルは200行以下。既存のLeanの変更は0。

### 271.2 型

全17個の名前付きdef/lemmaの型を記録する。BEのlocal instanceは同じmodelCategory AとmappingCofibrantFactorization Aを使う従来の二つ（代数のModelCategoryと、cofibrations/trivialFibrationsの関手的因子分解）で、SSetの模型構造は足さない。

#### TwistedArrowEdgeComposition（170行）

```lean
lemma twistedSquare_composite_of_edge_coordinates {C : SSet.{u}}
    (σ : (Δ[3] : SSet.{u}) ⟶ C)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : ((twistedSquareStdEdge 3 0 1 (by decide)).map σ).edge = p.edge)
    (ha : ((twistedSquareStdEdge 3 1 2 (by decide)).map σ).edge = a.edge)
    (hr : ((twistedSquareStdEdge 3 2 3 (by decide)).map σ).edge = r.edge)
    (hb : ((twistedSquareStdEdge 3 0 3 (by decide)).map σ).edge = b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b

lemma twistedSquare_mapped_edge_yoneda {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C)
    (i j : Fin 4) (h : i ≤ j) :
    SSet.yonedaEquiv.symm (((twistedSquareStdEdge 3 i j h).map σ).edge) =
      stdSimplex.map (stdSimplex.edge.{u} 3 i j h).down ≫ σ

lemma twistedSquare_composite_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x y z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x y)
    (r : SSet.Edge y z) (b : SSet.Edge q z)
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge) :
    HomotopyCategory.homMk p ≫ HomotopyCategory.homMk a ≫
      HomotopyCategory.homMk r = HomotopyCategory.homMk b

lemma twistedSquare_unit_of_projections {C : SSet.{u}}
    (s : (TwistedArrow C) _⦋1⦌)
    {q x z : C _⦋0⦌} (p : SSet.Edge q x) (a : SSet.Edge x x)
    (r : SSet.Edge x z) (b : SSet.Edge q z)
    [IsIso (HomotopyCategory.homMk p)] [IsIso (HomotopyCategory.homMk r)]
    (hp : SSet.opObjEquiv ((edgewiseLeft C).app _ s) = p.edge)
    (ha : (TwistedArrow C).δ 1 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm a.edge)
    (hr : (edgewiseRight C).app _ s = r.edge)
    (hb : (TwistedArrow C).δ 0 s = (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm b.edge)
    (hu : HomotopyCategory.homMk b = HomotopyCategory.homMk p ≫ HomotopyCategory.homMk r) :
    HomotopyCategory.homMk a = 𝟙 (HomotopyCategory.mk x)

lemma twistedSquare_zero_left_inclusion :
    (stdSimplex.opIso ⦋0⦌).inv ≫ joinInl (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 1 ≫ (edgewiseWeightIso 0).inv

lemma twistedSquare_zero_right_inclusion :
    joinInr (Δ[0] : SSet.{u}).op Δ[0] =
      stdSimplex.δ 0 ≫ (edgewiseWeightIso 0).inv

def twistedArrowVertexEdge {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    SSet.Edge (SSet.opObjEquiv ((edgewiseLeft C).app _ a)) ((edgewiseRight C).app _ a)

lemma twistedArrowVertexEdge_inverse {C : SSet.{u}} (a : (TwistedArrow C) _⦋0⦌) :
    (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (twistedArrowVertexEdge a).edge = a

lemma twistedArrowEdge_composition {C : SSet.{u}} {a b : (TwistedArrow C) _⦋0⦌}
    (s : SSet.Edge a b) :
    HomotopyCategory.homMk (SSet.Edge.ofTruncated (edgeUnop (s.map (edgewiseLeft C)).toTruncated)) ≫
      HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
        HomotopyCategory.homMk (s.map (edgewiseRight C)) =
      HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

#### TwistedPairingZero（60行）

```lean
lemma twistedPairingSimplex_zero (i : I) :
    twistedPairingSimplex A B h (nerveVertex i) = ComposableArrows.mk₁ (h i)

lemma twistedPairingNerveMap_zero
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh).app (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i))

lemma twistedPairingNerveMap_zero_postcomp {D : SSet.{u}} (G : nerve C ⟶ D)
    (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j) (i : I) :
    (twistedPairingNerveMap A B h hh ≫ edgewiseSubdivisionMap G).app
      (Opposite.op ⦋0⦌) (nerveVertex i) =
      (edgewiseWeightIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm (ComposableArrows.mk₁ (h i)) ≫ G
```

#### StrictDiagramTotJointSourceUnitLabel（82行）

```lean
def strictBETotJointUnitIndex (X : (operad A).Algebra) : strictBETotJointHomIndex A

def strictBETotJointSourceUnitLabel (X : (operad A).Algebra) : StrictBETotJointSourceElements A

lemma strictBETotJointSourceNativePairing_vertex (t : StrictBETotJointSourceElements A) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ (SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
          (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A)) t)) ≫
            strictBETotModelSource A

lemma strictBETotJointSourceUnitLabel_value (X : (operad A).Algebra) :
    SerrePositivity.EInfinity.FrameHom.liftedSourceFrameArrowValue
      (strictBETotJointSourceFrame A) (rightFrameReplacement (rightFrameFamily A))
      (strictBETotJointSourceUnitLabel A X) =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
        (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
          framedLimitProbeComparison A X) ≫
          ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌))

lemma strictBETotJointSourceUnitLabel_native_pairing (X : (operad A).Algebra) :
    (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌)
      (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex
        (strictBETotJointSourceUnitLabel A X)) =
      (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm
        (ComposableArrows.mk₁ ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          (((strictBETotJointRoofResolution A (strictBETotJointUnitIndex A X)).augmentation.app ⦋0⦌ ≫
            framedLimitProbeComparison A X) ≫
            ((rightFrameUnit (rightFrameFamily A)).app X).app (Opposite.op ⦋0⦌)))) ≫
              strictBETotModelSource A
```

### 271.3 残る照合と検証

今回の相殺則の仮定を、元のcorrectedPairingIsoの成分の左右射影の式から回収する必要がある。今回のBEの単位ラベルの像は元のoriginal pairingについての式であり、corrected pairingの像が既に恒等射だとみなさない。その後に同じ全straightening変換の単位の像へ接続し、全Yoneda評価による全変換の照合が必要である。頂点ごとの等式を全族の等式として扱わない。

R03hの全interval族の等式、元のnative fiber射自身の弱同値性、R03dの全関手同型と元の固定始域の同型との一致は引き続き未完。今回はこれらの完了を報告する段階ではない。§269の残り450〜850行の見込みには、今回の前提の分割312行も増えた。全族の照合の主証明の検証はまだなく、その見込みで完成を保証しない。外枠22,000行と§19の停止条件を維持する。

コードのコミット：**c9dda3e9d**。新規3本・312行、名前付きdef/lemma17個。実環境の新規3本は15・6・9宣言（生成された定数とlocal instanceを含む）。既存のLeanの変更は0。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド333：新規3本、成功（依存を含む12,249 jobs）。332では本体化の際の二つの有限の場合分けへのrflの適用が欠けていたため失敗し、元の個別検査済みの形へ戻して333で成功した。計算上限を変更していない。
- 小監査：AuditISW2BKCells332.lean、**221モジュール・1,563宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と、既存の定理の定義元の検査も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン583ファイル・1,859個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build333.log、isw2-validation333.json、isw2-declaration-collision-scan332.json。

今回までの検証済みの実測は**217モジュール・14,655行・1,556宣言**。外枠22,000行まで7,345行。監査の生成定数を含む実環境の数は単純加算せず、今回のimport後の集計を用いた（既存OppositeFunctorIsoWhiskerは12→11、ソース変更0。公開宣言の追加・変更ではない）。登録候補JSONだけを更新し、共通の入口と公式監査は変更していない。

登録候補は上記三本。今回の検証の後、同じ成分の合成則をホモトピー圏の元の射へ移す分割を続ける。R03h・R03dは未完で、一覧の完了数は増やしていない。

## 272. 同じ corrected pairing の元の成分に対する合成則（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 272.1 同じ射への接続

§271の左右射影の合成則を、twisted-arrowのホモトピー圏の任意の元の射について述べる形にした。元の射の代表辺を取って同じ三単体の計算を適用し、既存のhomotopyOppositeEquivalenceの同じ関手で反変の辺の類へ戻す。結論には選んだ代表辺を残さず、元の射そのものの左右射影と両端の元の辺だけを使う。既存の構成の合成則の証明の分割であり、一覧の新しい数学のIDは追加しない。

BEでは、元のstrictBETotJointSourceCorrectedPairingIsoの同じ全関手同型の成分を代入した。これにより、同じcorrected pairingの頂点の元の辺に、元の成分の左射影と右射影を合成すると、同じoriginal pairingの頂点の元の辺になる。存在だけの成分へ置き換えていない。全要素の任意のtに対する成分の等式であり、tについての全関手の族の一致を証明したものではない。

次に元の成分の二射影を、既存の全augmentation同型と標的の置換単位の同じ成分へ合わせる必要がある。元の単位ラベルのoriginal pairingの像は§271で検証したが、その像と今回の合成則だけで、まだcorrected pairingの単位の像の恒等性を完了したとしない。元の全straightening変換の単位の評価と、全Yoneda評価による全変換の一致も残る。R03hの全interval族の等式とR03dは引き続き未完。

### 272.2 型

新規2本（共通1・BE1）、96行。名前付きdef/lemmaは2個。BEのlocal instanceは元の代数のModelCategoryと関手的因子分解の同じ二つである。既存のLeanの変更は0。

#### TwistedArrowHomComposition（52行）

```lean
lemma twistedArrowHom_composition {C : SSet.{u}} [Quasicategory C]
    {a b : (TwistedArrow C) _⦋0⦌}
    (f : HomotopyCategory.mk a ⟶ HomotopyCategory.mk b) :
    ((homotopyOppositeEquivalence C).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft C)).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight C)).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

#### StrictDiagramTotJointCorrectionComponent（44行）

```lean
theorem strictBETotJointSourceCorrection_component_composition
    (t : StrictBETotJointSourceElements A) :
    let a := (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let b := (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    ((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b)
```

### 272.3 検証

コードのコミット：**6d1362deb**。新規2本・96行、公開定理2個。実環境の新規二本は1・3宣言（BEのlocal instance二つを含む）。既存のLeanの変更は0。

- 個別検査は両方とも成功。鍵付き対象ビルド334はBE側の単体表記のscopeが欠けていたため失敗した。open scoped Simplicialを補って個別検査を通し、335で対象ビルドと小監査を成功させた。計算上限の変更はない。
- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド335：新規二本、成功（依存を含む12,226 jobs）。
- 小監査：AuditISW2BKCells334Names.lean、**223モジュール・1,567宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存定理の定義元の確認も成功。
- §271の一件の数の差を調べるため、同じ鍵の中で元の218モジュールのimportの組も小監査で再検査した。**1,534宣言・標準三公理のみ**と元の数を再現した。OppositeFunctorIsoWhisker由来として列挙される12個と11個の名前の差は、`VertexIso.map.eq_1`という生成補題一件だけだった。手書きの公開宣言の名前の差は0。実測は今回の実環境の数を使う。
- 宣言名の照合：main a4388efc9に固定し、自レーン585ファイル・1,861個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build335.log、isw2-validation335.json、isw2-opposite-name-difference335.json、isw2-declaration-collision-scan335.json。

3b-4の検証済みの実測は**219モジュール・14,751行・1,560宣言**。外枠22,000行まで7,249行。登録候補は272.2の二本を自レーンのJSONへ追記した。共通の入口・公式監査は変更していない。

元の成分の射影を同じ全augmentation・標的単位の成分へ合わせる所から続ける。全interval族の等式と全関手同型の照合はまだなく、R03h・R03dおよび3b-4aを完了とはしていない。

## 273. 元の補正比較の二射影の全同型と、その同じ成分（2026-11-15）

一覧：済み 36／全体 36（うち追加 1）。3b-4：済み 11／全体 24（うち追加 12）。

### 273.1 全同型の指定値の回収

元のfunctorIsoPairの二射影が、元の二つの全関手同型そのものを回収する法則を証明した。それをBEの元の端点比較へ適用し、端点の型の等式を外して同じ組の値へ照合した。元の補正比較の指定pathを射影すると元の全端点比較を回収する既存の厳密な等式を使い、次を全関手同型のHEqとして得た。

- strictBETotJointSourceCorrectedPairingIsoの左射影は、元のstrictBETotJointSourceAugmentationDomainIsoの同じ逆。
- 同じ補正比較の右射影は、元のstrictBETotJointSourceTargetReplacementIsoの同じ逆。

HEqは端点の図式の表示の等式を扱うために使い、値を点ごとに新たに選んでいない。全パラメータの高次単体を持つ元の同型の値の照合である。さらに元の補正前後のpairingの射影の厳密な等式を四つに分け、それを成分評価に使って、元の同じ補正比較の成分を左右へ写した像も、元の全端点比較の逆の同じ成分にHEqで一致させた。

これは既存の構成の合成・射影・端点輸送・成分評価の法則の分割であり、新しい数学の一覧IDは追加しない。新規4本（共通1・BE3）、347行。全ファイル200行以下。既存のLeanの変更は0。[ModelCategory SSet]や計算上限の変更はない。モデルのinstanceはBE代数の元のものだけを使う。

### 273.2 型

公開def/lemma14個の全型と、privateなEq.mpの輸送の法則を記録する。各BEファイルのlocal instanceは元のmodelCategory A、mappingCofibrantFactorization A、および底の(CAlg_R A).op ⊗ CAlg_R Aの既存のquasicategory_tensorの三つで、ファイルごとに異なる名前にしている。

```lean
private lemma jointPairingProjectionEqMpHeq {α β γ : Sort _} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b
```

#### FunctorIsoPairingProjections（55行）

```lean
lemma functorIsoPair_postcomp_fst {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (fst X Y) = e

lemma functorIsoPair_postcomp_snd {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : T ⟶ X} {h k : T ⟶ Y} (e : FunctorIso f g) (d : FunctorIso h k) :
    (functorIsoPair e d).postcomp (snd X Y) = d
```

#### StrictDiagramTotJointPairingProjectionValues（98行）

```lean
lemma strictBETotJointSourceNativePairingBaseIso_pair_value :
    HEq (strictBETotJointSourceNativePairingBaseIso A)
      (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
        (strictBETotJointSourceTargetReplacementIso A))

lemma strictBETotJointSourceNativePairingBaseIso_symm_fst :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (fst (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm

lemma strictBETotJointSourceNativePairingBaseIso_symm_snd :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (snd (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm
```

#### StrictDiagramTotJointCorrectionProjectionValues（120行）

```lean
lemma strictBETotJointSourceCorrectionIso_projection_value {E : SSet.{u+1}}
    (q : (CAlg_R A).op ⊗ CAlg_R A ⟶ E) :
    HEq (((strictBETotJointSourceCorrectedPairingIso A).postcomp
      (twistedArrowProjection (CAlg_R A))).postcomp q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm q)

lemma strictBETotJointSourceCorrectionIso_left_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm

lemma strictBETotJointSourceCorrectionIso_right_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm

lemma strictBETotJointSourceCorrectedPairing_left :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceOriginalNativeDomain A

lemma strictBETotJointSourceNativePairing_left :
    strictBETotJointSourceNativePairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceNativeDomain A

lemma strictBETotJointSourceCorrectedPairing_right :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceOriginalNativeCodomain A

lemma strictBETotJointSourceNativePairing_right :
    strictBETotJointSourceNativePairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceNativeCodomain A
```

#### StrictDiagramTotJointCorrectionProjectionComponents（74行）

```lean
lemma strictBETotJointSourceCorrectionIso_left_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseLeft (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceAugmentationDomainIso A).symm (nerveVertex t))

lemma strictBETotJointSourceCorrectionIso_right_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseRight (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceTargetReplacementIso A).symm (nerveVertex t))
```

### 273.3 検収と残り

コードのコミット：**37c38f755**。新規4本・347行。公開def/lemma14個、privateな輸送の法則1個、BEのlocal instance9個。実環境の新規四本は2・7・10・5宣言。既存のLeanの変更は0。

個別検査では全型・証明が通った。既存の端点輸送と成分評価の九モジュールを再利用し、必要な依存の対象ビルド336（1,885 jobs）・337（3,392 jobs）を共有鍵で通した。本体化の338では、一時ファイルで共有していたopenの不足を検出し、新規三ファイルで名前空間を明示した。計算上限は変更していない。

- 鍵：--class impl --wait 3600、一枚の整理券、取得後gtimeout 1700秒。検査終了とともに返却済み。
- 対象ビルド339：新規四本、成功（依存を含む12,244 jobs）。
- 小監査：AuditISW2BKCells338.lean、**227モジュール・1,591宣言、propext・Classical.choice・Quot.soundのみ**。sorryAx・追加公理なし。互換二モジュールの宣言数0と既存の定理の定義元の確認も成功。
- 宣言名の照合：main a4388efc9に固定し、自レーン589ファイル・1,875個の名前と、mainのEInfinity/3,745ファイル・13,373個の名前を照合。異なるファイル間の重複0、自レーン内部も0。
- git diff --check：通過。

証跡：/private/tmp/isw2-build339.log、isw2-validation339.json、isw2-declaration-collision-scan339.json。

3b-4の検証済みの実測は**223モジュール・15,098行・1,584宣言**。外枠22,000行まで6,902行。登録候補は273.2の四本を自レーンのJSONへ追記した。共通の入口と公式監査は変更していない。

これで元のcorrected pairingの成分の左右射影が、元の全augmentationと標的単位の同じ成分であることまで接続できた。元の単位ラベルで、それらの成分の像を元の増大写像・probe比較・置換単位の実射の類へ計算する部分が残る。さらに、元の全straightening変換の単位の評価、全Yoneda評価による全変換の一致、R03hの全interval族の等式を閉じる必要がある。成分の一致だけを全族の等式とみなさない。R03h・R03d・3b-4aはまだ完了していない。
