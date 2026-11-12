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
