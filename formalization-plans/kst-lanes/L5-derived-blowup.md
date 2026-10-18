# K-L5：導来 blowup と半直交分解

## 現在地

L5a の模型を固定。L5b の多項式チャート、実際の Away 重なり、O(m) の可逆推移射、
Koszul 基底変換と cochain cocycle を対象ビルド済み。外積模型の単位・積・結合則・
符号付き可換性、反復 cone との比較、導来底変更の dg 準同値を証明済み。
E∩U_i と Ko(A;a)[S] の共通 dg 模型、D(n) の局所模型、各 localHomKFlat を構成済み。
普遍チャートの関係式商と自由多項式表示の環・代数同型、および有限関係族の弱正則性と
Koszul 解消性を証明済み。通常の普遍チャート環への underlying 複体の擬同型を構成済み。
既存の選択付き H⁰ 同型を使う複体比較とは別に、生成元を零へ送る標準添加射を構成済み。
標準 H⁰=R/im d の計算、添加の成分ごとの積・単位保存、係数代数に関する自然性と
普遍チャートへの標準添加射の擬同型性を証明済み。
標準添加を係数変更の単位・外積底変更・零生成元射の合成による dg 関手として構成済み。
空 Koszul の係数制限を通常のチャート環の単一複体へ同定すると、Hom 写像は標準添加射に一致する。
既存 DerivedChartObject から通常の普遍チャートの局所 dg 模型への準同値まで証明済み。
全有限重なりの係数環関手は構成済み。有限座標積の局所化、pivot 変更の代数同型、
pivot の三重 cocycle、制限との自然性を証明済み。微分等式の移送を明示した
チャート dg 関手の三重 cocycle も証明済み。
全有限重なりへの dg 底変更比較と局所準同値性を証明済み。
普遍多項式チャートと L7 の Rees–Proj 標準チャートとの明示環同型を構成済み。
基底係数と斉次比の像、両側逆まで確認済み。
普遍係数の任意環への特殊化、多項式環の tensor 底変更、任意宇宙への ULift 接続を構成済み。
ULift 後も弱正則性と解消性を証明し、標準チャートへの dg 底変更準同値を構成済み。
基底へ制限した Koszul 複体の K-flat 性、多項式 pushout の加群・非有界複体の自然同型、
実導来係数拡大との比較を証明済み。
通常の普遍チャート商は元の自由チャートと基底係数を保つ環同型を持ち、
その実導来底変更が指定係数の Koszul チャートを与える局所同型を構成済み。
係数制限の合成・恒等比較を dg 関手として構成し、三段階の結合整合性を証明済み。
自由 Koszul 模型の環射に沿う dg 関手、その Hom と総外積の係数変更の一致、
二段の合成律と恒等律を証明済み。
自由生成加群の変換と dg 係数変更の自然性を証明済み。
チャート基底変換行列の係数自然性、座標と微分の移送を含むチャート dg 係数変更、
その合成律・恒等律、チャート基底変換との dg 自然性を証明済み。
環射と pivot 変更をまとめた半線形チャート dg 遷移と、その合成則を証明済み。
全有限重なりの実際の環射に沿う dg 遷移を構成し、
環射の等式移送・係数制限の標準比較を含む恒等律と合成律を証明済み。
任意 dg 圏で使える有限重なりの制限合成比較を構成し、
チャート模型上で三段階の結合整合性と左右の単位整合性を証明済み。
共通基底環への制限後の dg 遷移も恒等・合成を保つことを証明済み。
自己 Hom を Mathlib のモノイド対象へ束ね、全非空有限重なりから `Mon (Complex R)` への
実際の関手 `finiteOverlapDGAlgebraDiagram` を構成済み。
全 diagram-module の係数 dg 圏に向け、包含に対応する Hom、単位、合成の候補と
二つの包含があるときの合成公式を構成済み。
一般のモノイド対象の射に沿う乗法の単位・結合則、および係数圏の左右の単位律を証明済み。
係数圏の結合律と dg 圏への組立ては未完了。
その係数図式上の coherent な dg 加群の降下模型と層レベル比較は未完了。
L5b 全体は未完了。L5c〜L5f は未実装。
既存の L11 の検証記録を、Lean の証明済み宣言とは扱わない。

## 目標と所有

導来 blowup の有限チャート模型、射影空間のコホモロジー、KST Lemma3.8〜3.15、
Thm3.7・3.16・3.17 の係数版を証明する。namespace は
`SerrePositivity.KST.DerivedBlowup`、所有ソースは `SerrePositivity/KST/DerivedBlowup/`。
集約は `SerrePositivity/KST/DerivedBlowup.lean`、監査は `scripts/audit_kst_derived_blowup.lean`。
L4 の層・Perf・局所化・MV・Čech、L6 の Koszul と pro 消滅、L7 の古典 blowup は読み取り専用。
K に依存する部分は S1 の界面を明示的な構造体引数として用い、その存在を公理化しない。

## 原典

| 対象 | 原典と頁 | 経路 |
| --- | --- | --- |
| チャートと導来底変更 | KST arXiv:1611.08466v4 Def3.1・Lemma3.6、pp.11–14 | 普遍 blowup の導来底変更を Koszul 模型で具体化 |
| 生成と充満忠実性 | KST Lemma3.8〜3.12、pp.14–17 | 中央平坦係数 H へ拡張 |
| 部分商の同値 | KST Lemma3.13〜3.15、pp.17–18 | L4 の Neeman9.1.5 と接続 |
| 導来 blowup 降下 | KST Thm3.7、p.14、証明p.18 | K0 の局所化界面に対して証明 |
| 射影束・Bass | KST Thm3.16・3.17、p.19 | TT4.1 pp.329–330、6.1 pp.351–354、6.6 p.361、7.5 pp.365–366 |
| 押し出しと消滅 | Thomason1993 Lemme2.3 p.200；KST Lemma3.10・3.11 pp.15–16 | 射影空間の有限 Čech 計算による再証明。原典と異なる経路 |

正本：[KST経路](../k-theory-kst-route.md)、[基盤](../foundations.md)、
[L11検証 §7・§8](L11-paper.md)。

## L5a：Perf の模型と比較

I=Fin(r+1)。U_i の環は Ko(A[S_j : j≠i]; (a_iS_j−a_j)_{j≠i})。
重なりは S_k を可逆化し、S_i=1 と規格化して S_j を S_j/S_k に送る。
全ての有限非空重なりを含む Čech 図式を用いる。基底環上の非導来 tensor ではなく、
局所 K-flat 模型による導来スカラー拡大を用いる。

第一候補を採用する：この環図式上の dg 加群の coherent な homotopy-cartesian section の
dg 圏を導来圏の模型とし、その局所 perfect な充満部分 dg 圏を Perf とする。
各遷移の随伴比較 `R_V ⊗ᴸ_{R_U} M_U → M_V` が擬同型であることを cartesian 条件とする。
単に underlying A 加群の制限射が擬同型である、という条件ではない。
strict な等式での複体の貼り合わせ・三重 cocycle だけの模型は採らない。

具体的には全 diagram-module の dg 圏を使い、図式の射影的／半自由置換を行った後、
objectwise acyclic を dg 商してから cartesian 条件と局所 perfect 条件を課す。
これにより mapping 複体も導来化する。対象だけを coherent にして Hom を通常の等化子で
計算する模型は採らない。局所 K-flat 分解を先行させる順序は L4 §26 と同じ。

比較の定理は二段に分ける：(1) 古典スキームの場合、L4 の T3 の Čech 降下で
層レベル `DqcDGModel` とこの chart-section 模型の Morita 同値を証明する。
(2) 導来チャートでは dg 代数の局所化・導来底変更・射影公式の比較を同じ Čech 図式上で証明する。
古典 truncation の D_qc と導来 D_qc が同じだとは主張しない。
L4 の T3 は現在未供給なので (1) は未証明の定理として工程に残す。
模型の定義に比較同値を仮定として入れない。L5b の環と Koszul 変換はこの比較を待たず構成できる。

O(1) は遷移単元 S_k、O(−1) はその逆を持つ可逆加群。
例外因子 E のチャートは Ko(A;a)[S_j:j≠i]、D(n) は U_i の Koszul に
a_0^n,…,a_r^n を加えたもの。これらの同定は Koszul 列の可逆基底変換で証明する。
H 係数版は中央 A 作用を持つ A 平坦な結合代数を tensor し、導来 tensor との比較を証明する。

## 工程

| 工程 | 内容 | 完成に必要な証拠 |
| --- | --- | --- |
| L5a | 上記の模型・L4との比較の配置 | 設計記載済み。比較の証明完了とはしない |
| L5b Charts | 普遍環・重なり・O(1)・Koszul基底変換・E・D(n) | 実際の環射／複体射とcocycleの証明 |
| L5c ProjectiveSpace | 負捻り消滅、Rp′_*O=A′ | Čech複体の縮約と導来比較 |
| L5d SemiOrthogonal | 3.8〜3.15 | 生成・Hom・部分商同値の証明 |
| L5e Theorem37 | 導来blowup降下 | K0界面からの自然なcartesian比較 |
| L5f ProjectiveBundle | 3.16・3.17 | 射影束分解・Bass完全列・自然分裂 |

## 主要宣言

| 宣言 | ファイル | 状態 |
| --- | --- | --- |
| `ChartIndex`・`ChartRing`・`chartCoordinate`・`chartRelation` | Charts | 対象ビルド済み |
| `normalizeCoordinates_cocycle`・`transitionUnit_cocycle` | Charts | 対象ビルド済み |
| `chartTransition`・`chartTransition_coordinate` | Charts | 対象ビルド済み |
| `chartTransition_cocycle`・`chartTransition_unit_cocycle` | Charts | 対象ビルド済み |
| `chartTransition_relation` | Charts | 対象ビルド済み |
| `UniversalBase`・`UniversalChart`・`projectiveChartInclusion` | UniversalCharts | 対象ビルド済み |
| `universalBaseMap`・`universalBaseMap_X`・`universalMinor_zero` | UniversalCharts | 対象ビルド済み |
| `OverlapRing`・`overlapUnit`・`overlapTransitionBase` | Overlaps | 対象ビルド済み |
| `overlapMap`・`overlapMap_comp`・`overlapEquiv` | Overlaps | 対象ビルド済み |
| `koszulGeneratorMap_cocycle`・`koszulGeneratorMap_inverse`・`koszulGeneratorEquiv` | KoszulBasis | 対象ビルド済み |
| `chartKoszulDifferential`・`koszulGeneratorMap_differential` | KoszulDifferential | 対象ビルド済み |
| `ChartExterior`・`chartExteriorDifferential_sq` | ChartExterior | 対象ビルド済み |
| `chartExteriorMap_cocycle`・`chartExteriorMap_differential`・`chartExteriorEquiv` | ChartExterior | 対象ビルド済み |
| `chartKoszulSequence`・`derivedChartComplex` | ChartComplexes | 対象ビルド済み |
| `exceptionalChartSequence`・`exceptionalChartComplex`・`exceptionalProductSequence` | ChartComplexes | 対象ビルド済み |
| `thickeningChartSequence`・`thickeningChartComplex`・`derivedChartComplex_isZero_X_pos/lt` | ChartComplexes | 対象ビルド済み |
| `exceptionalGeneratorEquiv`・`exceptionalGeneratorMap_differential` | ExceptionalBasis | 対象ビルド済み |
| `exceptionalExteriorEquiv`・`exceptionalExteriorEquiv_differential` | ExceptionalBasis | 対象ビルド済み |
| `exteriorContraction_zero_degree`・`exteriorContraction_mem_degree` | ExteriorGrading | 対象ビルド済み |
| `exteriorDegreeDifferential`・`exteriorDegreeDifferential_sq` | ExteriorGrading | 対象ビルド済み |
| `exteriorKoszulChain`・`exteriorKoszulCochain`・`exteriorKoszulCochainXIso` | ExteriorComplex | 対象ビルド済み |
| `exteriorMap_mem_degree`・`exteriorDegreeMap`・`exteriorContraction_map` | ExteriorDegreeMap | 対象ビルド済み |
| `exteriorKoszulChainMap`・`exteriorKoszulCochainMap`・`exteriorKoszulChainMap_comp` | ExteriorComplexMap | 対象ビルド済み |
| `exteriorKoszulChainIso`・`exteriorKoszulCochainIso` | ExteriorComplexIso | 対象ビルド済み |
| `chartExteriorCochainIso`・`exceptionalExteriorCochainIso` | ChartCochainMaps | 対象ビルド済み |
| `exteriorContraction_mul` | ExteriorLeibniz | 対象ビルド済み |
| `exteriorCochainInclusion`・単射性・次数・微分との適合性 | ExteriorIntegerInclusion / ExteriorIntegerDifferential | 対象ビルド済み |
| `exteriorCochainBilinear`・`exteriorCochainBilinear_d` | ExteriorCochainProduct / ExteriorCochainLeibniz | 対象ビルド済み |
| `exteriorKoszulMultiplication`・`exteriorKoszulMultiplication_component` | ExteriorMultiplication | 対象ビルド済み |
| `exteriorUnitCycle`・`exteriorKoszulUnit`・`exteriorKoszulUnit_inclusion` | ExteriorUnit | 対象ビルド済み |
| `exteriorKoszul_left_unit`・`exteriorKoszul_right_unit` | ExteriorUnitLaws | 対象ビルド済み |
| `exteriorKoszul_assoc` | ExteriorAssociativity | 対象ビルド済み |
| `exteriorKoszulDGCategory`・`ExteriorKoszulObject`・`exteriorKoszulObjectDGCategory` | ExteriorDGCategory | 対象ビルド済み |
| `exteriorCochainInclusion_map`・`exteriorKoszulCochainMap_unit/mul` | ExteriorMapInclusion / ExteriorMapLaws | 対象ビルド済み |
| `exteriorKoszulDGFunctor`・`exteriorKoszulDGFunctor_id/comp` | ExteriorDGFunctor / ExteriorCochainFunctoriality | 対象ビルド済み |
| `chartExteriorDGFunctor`・`exceptionalExteriorDGFunctor` と Hom の可逆性 | ChartDGFunctors | 対象ビルド済み |
| `exteriorHomogeneous_anticomm`・`exteriorCochainBilinear_comm`・`exteriorKoszul_comm` | ExteriorCommutativity | 対象ビルド済み |
| `exteriorKoszulCochain_finite/free/isZero_X_lt` | ExteriorFiniteness | 対象ビルド済み |
| `exteriorCochainZeroIso`・`exteriorKoszulUnit_f_zero_isIso` | ExteriorDegreeZero | 対象ビルド済み |
| `sequenceExteriorCochain` と各項の有限自由性・下限 | ExteriorSequence | 対象ビルド済み |
| `sequenceExteriorCochain_empty_iso` | ExteriorSequence | 空列で反復 cone と比較済み |
| `chartSequenceGeneratorEquiv_differential`・`chartSequenceExteriorIso` | ChartSequenceComparison | 対象ビルド済み |
| `exteriorProduct_decomposition` | ExteriorProductSplit | 対象ビルド済み |
| `exteriorProductLinearEquiv` | ExteriorProductEquiv | 総外積の二成分分解 |
| `exteriorProduct_contract_join`・`exteriorProduct_contract_decomposition` | ExteriorProductDifferential | cone 型微分 (-dx,ax+dy) を証明済み |
| `exteriorProductDegreeEquiv` | ExteriorProductDegree | 第n+1外積の二成分分解 |
| `exteriorProductCochainEquiv` と第一・第二成分の包含公式 | ExteriorProductCochain / ExteriorProductCochainComponents | 全整数次数で証明済み |
| `exteriorProductCochainEquiv_d` | ExteriorProductCochainDifferential | 整数 cochain の cone 型微分 |
| `exteriorToConeXIso`・射影との適合性 | ExteriorConeComponents | 対象ビルド済み |
| `exteriorProductConeIso` | ExteriorConeIso | 生成元追加と mappingCone の複体同型 |
| `sequenceGeneratorEquiv`・`sequenceGeneratorJoin_differential` | SequenceGeneratorSplit | 有限列の末尾の自由生成元分解 |
| `sequenceExteriorSuccIso`・`koszulExteriorIso` | KoszulConeComparison | 全有限列で反復 cone 模型との複体同型 |
| `derivedChartExteriorIso` | KoszulConeComparison | チャート反復 cone と外積複体の比較 |
| `exceptionalChartExteriorIso`・`exceptionalChartProductIso` | ExceptionalConeComparison | 例外因子の二つの反復 cone 表示の比較 |
| `exceptionalChartBaseChangeIso` | ExceptionalConeComparison | E∩U_i の Ko(A;a)[S] 表示の複体比較 |
| `chartBaseChangeExteriorIso` | ChartBaseChangeComparison | 任意のチャート環射に沿う複体の底変更比較 |
| `overlapChartComplexIso` | OverlapComplexComparison | 実際の Away 局所化環での複体同型 |
| `koszulComplex_kFlat`・`sequenceExteriorCochain_kFlat`・`derivedChartComplex_kFlat` | KoszulKFlat | 非有界試験複体に対する K-flat 性 |
| `chartDerivedBaseChangeExteriorIso`・`overlapChartDerivedComplexIso` | ChartDerivedBaseChange | 基底可換環上の導来スカラー拡大比較 |
| `chartExteriorCochainMap_cocycle` | ChartCochainCocycle | 座標等式による移送を明示した三重 cocycle |
| `exteriorBaseChangeEquiv` | ExteriorBaseChange | 2の可逆性を仮定しない総外積の底変更同型 |
| `exteriorToBaseChange_contract`・`exteriorOfBaseChange_contract` | ExteriorBaseChangeContraction | 総外積の底変更と収縮の可換性 |
| `exteriorBaseChangeDegreeInclusion_injective` | ExteriorBaseChangeDegreeInclusion | 平坦性不要の分裂単射 |
| `exteriorDegreeBaseChangeEquiv` | ExteriorBaseChangeDegree | 各同次外積の底変更同型 |
| `exteriorDegreeToBaseChange_d` | ExteriorBaseChangeDegreeDifferential | 同次次数別の微分比較 |
| `exteriorChainBaseChangeIso` | ExteriorChainBaseChange | 自然数次数 chain 複体の底変更同型 |
| `exteriorCochainBaseChangeIso` | ExteriorCochainBaseChange | 整数 cochain 複体の底変更同型 |
| `exteriorBaseChangeCochainInclusion_iso/iso_inv/injective` | ExteriorCochainBaseChangeInclusion | 総外積との比較と単射性 |
| `exteriorCochainBaseChange_unit`・`exteriorCochainBaseChange_mul` | ExteriorBaseChangeUnit / ExteriorBaseChangeMultiplication | 強モノイダル係数変更との単位・積比較 |
| `exteriorKoszulBaseChangeDGFunctor`・`exteriorKoszulBaseChangeDGFunctor_quasiEquivalence` | ExteriorBaseChangeDGFunctor | 既存 DGBaseChange からの dg 準同値 |
| `freeKoszulBaseChangeDGFunctor`・準同値性 | FreeKoszulBaseChange | 自由生成加群の標準底変更 |
| `DerivedChartObject`・`chartBaseChangeDGFunctor`・準同値性 | ChartBaseChangeDGFunctor | 標準チャートへの適用 |
| `overlapChartDGFunctor`・準同値性 | OverlapDGComparison | 実際の Away 局所化環での局所 dg 比較 |
| `chartTwistCochainMap_cocycle`・`chartTwistCochainIso` | TwistTransitions | O(m) の可逆推移射と整数冪の cocycle |
| `ExceptionalChartObject`・`ThickeningChartObject` と underlying 同型 | LocalDGModels | E・D(n) の局所 dg 模型 |
| `exceptionalChartDGFunctor`・`exceptionalPolynomialBaseChangeDGFunctor` と準同値性 | ExceptionalDGComparison | E∩U_i と Ko(A;a)[S] の共通 dg 模型 |
| `derivedChart_localHomKFlat`・`exceptionalChart_localHomKFlat`・`thickeningChart_localHomKFlat` | LocalHomKFlat | 既存の局所 K-flat 条件 |
| `universalRelationIdeal`・`universalPresentationMap`・`universalPresentationEquiv` | UniversalPresentation / UniversalPresentationEquiv | 通常の普遍チャートの商表示と相互逆 |
| `universalSplitEquiv`・`universalSplitMap_relation` | UniversalSplitCoordinates | 独立モニック変数表示への環同型 |
| `universalRelation_fin_isWeaklyRegular`・`universalRelation_fin_isKoszulResolution` | UniversalRegularSequence | 任意の異なる有限関係族の弱正則性と解消性 |
| `universalChartSequence_isKoszulResolution`・`universalPresentationAlgEquiv` | UniversalKoszulResolution | 既存チャート列の解消性と係数代数同型 |
| `universalChartH0Iso`・`universalChartComplexComparison`・擬同型性 | UniversalKoszulResolution | 選択付き H⁰ 同型を経由する underlying 複体の比較 |
| `exteriorKoszulAugmentation`・次数成分・成分の積/単位保存 | ExteriorAugmentation | 生成元を零へ送る標準添加鎖写像 |
| `exteriorBoundary_range`・`exteriorCochainAugmentationComponent_zero` | ExteriorAugmentationBoundary | 境界像と次数0添加の明示式 |
| `exteriorHomologyZeroIso`・`exteriorOpcyclesZeroIso_projection` | ExteriorHomologyZero | H⁰=R/im d の標準同型と射影公式 |
| `exteriorQuotientAugmentation_eq_toSingle`・`exteriorQuotientAugmentation_quasiIso` | ExteriorQuotientAugmentation | 商への標準射と H⁰ 比較の一致 |
| `exteriorKoszulAugmentation_naturality`・`exteriorKoszulAugmentation_quasiIso_of_quotient` | ExteriorAugmentationNaturality | 係数代数の表示変更と擬同型移送 |
| `universalCanonicalAugmentation`・`universalCanonicalAugmentation_quasiIso` | UniversalCanonicalAugmentation | 通常の普遍チャートへの標準添加射と擬同型性 |
| `exteriorAugmentationDGFunctor` | ExteriorAugmentationDGFunctor | 係数変更と零生成元射から構成する標準添加 dg 関手 |
| `emptyKoszulRestrictionIso`・`emptyKoszulRestriction_unit_one` | EmptyKoszulRestriction | 空 Koszul の通常の係数単一複体への比較 |
| `exteriorKoszulAugmentation_unique` | ExteriorAugmentationUniqueness | 単位の1保存による添加鎖写像の一意性 |
| `exteriorAugmentationDGFunctor_map_comparison`・準同値の判定 | ExteriorAugmentationDGComparison | Hom 写像と標準添加鎖写像の一致 |
| `universalChartAugmentationDGFunctor`・準同値性 | UniversalChartDGResolution | 既存 DerivedChartObject の通常の普遍チャートへの局所 dg 準同値 |
| `exteriorDifferentialTransportDGFunctor`・`chartExteriorDGFunctor_cocycle` | ChartDGCocycle | 微分等式の移送を明示した三重 dg cocycle |
| `FiniteOverlapRing`・`finiteOverlapRestriction`・恒等/合成則 | FiniteOverlaps | 座標有限積の局所化と制限射 |
| `finiteOverlapPivotMap`・`finiteOverlapPivotEquiv` | FiniteOverlapTransitions | 任意有限重なりの pivot 変更の代数同型 |
| `finiteOverlapPivotMap_cocycle` | FiniteOverlapCocycle | 任意有限重なり上の環射の三重 cocycle |
| `finiteOverlapPivotMap_restriction`・`finiteOverlapPivotMap_self` | FiniteOverlapNaturality | 制限との自然性と恒等変更 |
| `finiteOverlapRingDiagram` | FiniteOverlapDiagram | 非空有限部分集合から可換 R 代数への実際の関手 |
| `chartTransitionComparisonDGFunctor`・`finiteOverlapChartDGFunctor` と準同値性 | TransitionDGComparison | 任意共通係数環と全有限重なりの局所 dg 比較 |
| `universalCenter_image`・`universalClassicalToChart` | UniversalClassicalCenter | 普遍中心像の正則単項性と L7 の正則持ち上げ |
| `universalClassicalChartEquiv`・係数/比座標の保存 | UniversalClassicalChartEquiv | L7 の Rees–Proj 標準チャートとの明示環同型 |
| `universalSpecialization`・`universalPresentationBaseChangeEquiv` と関係式公式 | UniversalSpecialization | 任意係数への代入と通常の多項式 tensor 比較 |
| `liftedUniversalChartBaseChangeDGFunctor`・準同値性 | LiftedUniversalSpecialization | ULift で任意宇宙へ接続した普遍チャートの dg 底変更 |
| `liftedUniversalChartSequence_isWeaklyRegular/isKoszulResolution` | LiftedUniversalResolution | 宇宙移送後の普遍関係式列の解消性 |
| `polynomialKoszulRestriction_kFlat`・`chartRestrictedExterior_kFlat` | PolynomialKoszulKFlat | 表示環から元の基底へ制限した複体の K-flat 性 |
| `scalarExtensionTensorView`・`scalarRestrictionTensorView` | ScalarTensorView | 束ねた係数拡大・制限と通常の tensor 表示の比較 |
| `polynomialPushoutModuleNatIso`・`polynomialPushoutComplexNatIso` | PolynomialPushoutBaseChange | 普遍基底と表示多項式環を経由する二つの tensor 経路の自然同型 |
| `polynomialDerivedBaseChangeIso` | PolynomialDerivedBaseChange | K-flat 複体の実導来底変更と表示環の項別底変更の比較 |
| `liftedUniversalDerivedChartIso` | UniversalDerivedChartComparison | 普遍チャート解消の実導来底変更と任意係数チャートの局所同型 |
| `liftedUniversalOrdinaryChartEquiv`・係数保存・`liftedUniversalDerivedOrdinaryChartIso` | LiftedUniversalOrdinaryChart | 通常の普遍チャート商そのものの実導来底変更の Koszul 表示 |
| `restrictionCompositionIso`・単位・tensor 整合性・`restrictionCompositionDGFunctor` | RestrictionComposition | 二段の係数制限を合成環射の制限に比較する dg 関手 |
| `restrictionCompositionDGFunctor_assoc` | RestrictionAssociativity | 三段の係数制限比較の結合整合性 |
| `restrictionIdentityIso`・単位・tensor 整合性・`restrictionIdentityDGFunctor` | RestrictionIdentity | 恒等環射による制限と元の dg 圏の標準比較 |
| `freeExteriorScalarMap`・生成元・係数公式・合成律・恒等律 | FreeExteriorScalarMap | 総外積上の係数変更の実際の射とその関手性 |
| `freeKoszulScalarDGFunctor`・`freeKoszulScalarDGFunctor_inclusion` | FreeKoszulScalarDGFunctor | 環射に沿う自由 Koszul dg 関手と総外積への包含公式 |
| `freeKoszulScalarDGFunctor_comp`・`freeKoszulScalarDGFunctor_id` | FreeKoszulScalarComposition | 係数制限の標準比較を明示した dg 係数変更の合成律・恒等律 |
| `freeGeneratorScalarLinearMap`・`freeExteriorScalarMap_natural` | FreeExteriorScalarNaturality | 半線形係数変更と総外積上の生成元変換の自然性 |
| `freeKoszulScalarDGFunctor_natural` | FreeKoszulScalarNaturality | 微分を保つ自由生成元変換の dg 係数自然性 |
| `normalizeCoordinates_scalarMap`・`koszulGeneratorMap_scalarMap` | ChartBasisScalarNaturality | 規格化座標と可逆 Koszul 基底変換行列の係数自然性 |
| `chartScalarDifferential_eq`・`chartScalarDGFunctor`・包含公式 | ChartScalarDGFunctor | 微分移送を含む実際のチャート模型間の dg 係数変更 |
| `chartScalarNormalizedDGFunctor`・包含公式 | ChartScalarNormalization | 規格化と係数変更の順序を比較した dg 関手 |
| `chartExteriorDGFunctor_scalar_natural` | ChartDGScalarNaturality | チャートの可逆基底変換と dg 係数変更の可換図式 |
| `chartScalarDGFunctor_comp`・`chartScalarDGFunctor_id` | ChartScalarComposition | 実際のチャート dg 係数変更の合成律・恒等律 |
| `chartSemilinearDGFunctor`・包含公式 | ChartSemilinearTransition | 環射と pivot 変更をまとめた実際の dg 遷移 |
| `chartSemilinearExterior_comp`・`chartSemilinearDGFunctor_comp` | ChartSemilinearComposition | 二段の異なる係数環を通るチャート遷移の合成律 |
| `finiteOverlapChartMap_coordinates`・`FiniteOverlapKoszulObject`・`finiteOverlapDGTransition`・包含公式 | FiniteOverlapDGTransition | 全有限重なり環上の局所模型と実際の dg 遷移 |
| `finiteOverlapChartMap_ringHom_comp`・`finiteOverlapDGTransition_unit_comp` | FiniteOverlapDGCoherenceData | 有限重なりの合成環射と合成単元の直接射との一致 |
| `restrictionRingHomTransportDGFunctor`・対象公式・外積 Hom の成分公式 | RestrictionRingHomTransport | 環射の等式による dg 制限の移送 |
| `finiteOverlapDGCompositionComparison`・`finiteOverlapDGTransition_comp` | FiniteOverlapDGComposition | 標準制限比較後の全有限重なり dg 遷移の合成律 |
| `finiteOverlapDGIdentityComparison`・`finiteOverlapDGTransition_id` | FiniteOverlapDGIdentity | 標準恒等制限比較後の全有限重なり dg 遷移の恒等律 |
| `finiteOverlapRestrictionCompositionComparison`・対象・制限外積上の成分公式・既存チャート比較との一致 | FiniteOverlapRestrictionComparison | 任意 dg 圏で使える有限重なりの標準制限合成比較 |
| `finiteOverlapDGCompositionComparison_assoc` | FiniteOverlapDGAssociativity | 三段階の有限重なり制限比較の二経路の一致 |
| `finiteOverlapDGLeftIdentityComparison`・成分公式・`finiteOverlapDGCompositionComparison_left_unit`・`finiteOverlapDGCompositionComparison_right_unit` | FiniteOverlapDGUnitCoherence | 有限重なりの制限合成比較の左右の単位整合性 |
| `baseRestrictionDGFunctor`・対象・外積 Hom の成分公式 | BaseRestrictionDGFunctor | 代数射に沿う半線形 dg 関手の共通基底環への係数制限 |
| `finiteOverlapDGTransition_comp_apply`・`finiteOverlapDGTransition_id_apply` | FiniteOverlapTransitionComponents | 元の半線形遷移の各次数の関数としての恒等・合成公式 |
| `FiniteOverlapBaseKoszulObject`・`finiteOverlapBaseDGTransition`・対象・成分公式 | FiniteOverlapBaseDGTransition | 共通基底環上の有限重なり dg 模型と遷移 |
| `finiteOverlapBaseDGTransition_comp`・`finiteOverlapBaseDGTransition_id` | FiniteOverlapBaseDGFunctoriality | 共通基底環上の dg 遷移の恒等・合成則 |
| `dgEndMonoid`・`dgEndMonoidMap` | DGEndMonoid | dg 自己 Hom の Mathlib の複体モノイド対象への接続 |
| `finiteOverlapDGAlgebra`・`finiteOverlapDGAlgebraMap`・恒等・合成則・`finiteOverlapDGAlgebraDiagram` | FiniteOverlapDGAlgebraDiagram | 全非空有限重なりから共通基底環上の dg 代数への実際の関手 |
| `diagramModuleHom`・包含による同定・`diagramModuleId`・`diagramModuleComp`・`diagramModuleComp_on_le` | DiagramModuleHom | 全 diagram-module の係数 dg 圏の Hom・単位・合成の候補と包含上の公式。圏法則は別モジュールで検証 |
| `diagramAlgebraMul`・左単位・恒等遷移・結合則 | DiagramAlgebraMultiplication | モノイド対象の射で係数を送ってから掛ける合成の一般則 |
| `diagramModuleHom_isZero`・`diagramModule_left_unit`・`diagramModule_right_unit` | DiagramModuleUnit | 包含のない Hom の零性と diagram-module 係数圏の左右の単位律 |

`ChartExterior` は総外積代数。`chartExteriorCochain` は次数分解・収縮微分から作った整数次数の複体。
積は既存 tensor 複体からの chain map として装備済み。単位も tensor unit からの chain map として構成済み。
モノイダル圏での左右単位則・結合則を証明済みで、一対象 dg 圏を構成済み。
生成元変換は単位・積・恒等・合成を保つ dg 関手へ持ち上げ済み。
チャートと例外因子の基底変換は Hom の射が可逆な dg 関手として構成済み。
異なる微分の構造を同時に扱う公開対象型は `ExteriorKoszulObject d` とする。
符号付き braiding に関する可換性も証明済み。有限列では各項の有限自由性と振幅 [-n,0] を証明済み。
`derivedChartComplex` は既存の反復 cone 複体であり、一般の有限列で外積模型との比較同型を構成済み。
チャート列の Fin r と ChartIndex の添字比較同型も構成済み。
生成元追加 M×R の外積を二成分へ分解する総外積と同次次数別の線形同型は構成済み。
この二成分の微分が (-dx,ax+dy) になることも証明済み。
整数次数の項と既存 mappingCone の biprod を比較し、生成元追加 M×R の
Koszul 外積複体とスカラー作用の mappingCone の複体同型を構成済み。
有限列の Fin(n+1) の自由生成加群を (Fin n→₀R)×R と比較する帰納法は証明済み。
例外因子の反復 cone 複体を Ko(A;a)[S] の underlying 複体と同定済み。
チャート複体は K-flat と証明済みで、実際の重なり環への導来スカラー拡大後の
underlying 複体の同型を構成済み。共通係数環上の cochain 遷移の三重 cocycle も証明済み。
総外積代数の底変更同型は任意可換環上で構成済みで、収縮微分と可換なことも証明済み。
同次次数への制限は、graded projection を tensor した左逆を使い、平坦性を仮定せず構成済み。
自然数次数の Koszul chain 複体の底変更同型を構成済み。
整数 cochain への零延長とスカラー拡大の比較を構成済み。
その逆同型は強モノイダル係数変更の単位・乗法を保存し、
既存 `DGBaseChange` から Koszul 生成加群の底変更による一対象 dg 圏への dg 準同値を構成済み。
チャートの自由生成加群のスカラー拡大を標準自由生成加群と比較し、
標準チャートと実際の Away 重なりで dg 準同値を構成済み。
例外因子の dg 模型と Ko(A;a) の多項式底変更を共通模型へ送る dg 準同値も構成済み。
O(m) の単元整数冪による推移射と cocycle、および可逆性は cochain レベルで証明済み。
チャート・例外因子・D(n) は既存 `localHomKFlat` を満たす。
普遍チャートの多項式商表示と有限正則関係族の Koszul 解消性は証明済み。
変数再配置で各関係を負の独立モニック一次式へ移し、既存の一般モニック補題を利用する。
既存 Koszul 解消定理の H⁰ 同型は選択を含むため、これを使う旧比較射の積・単位保存は主張しない。
標準添加射を別途構成し、H⁰ と微分像の商の標準同型、成分ごとの積・単位保存、
係数代数に関する自然性、普遍チャートの標準添加射の擬同型性を証明済み。
標準添加の dg 関手を構成し、その Hom と標準添加鎖写像の一致を証明済み。
既存 DerivedChartObject から、通常の普遍チャートを表す空 Koszul 模型の係数制限への
局所 dg 準同値を証明済み。全有限重なりの係数環図式を実際の関手として構成済み。
微分移送を明示した三重 dg cocycle も証明済み。全有限重なりへの dg 底変更比較と局所準同値性を証明済み。
普遍多項式チャートは L7 の Rees–Proj 標準チャートと明示環同型で結び、
基底構造射と斉次比の像も確認済み。
普遍係数の任意環への特殊化、多項式環の tensor 底変更、任意宇宙への ULift 接続を構成済み。
ULift 後も弱正則性と解消性を証明し、標準チャートへの dg 底変更準同値を構成済み。
基底へ制限した Koszul 複体の K-flat 性、多項式 pushout の加群・非有界複体の自然同型、
実導来係数拡大との比較を証明済み。
通常の普遍チャート商は元の自由チャートと基底係数を保つ環同型を持ち、
その実導来底変更が指定係数の Koszul チャートを与える局所同型を構成済み。
係数制限の合成・恒等比較は単位・tensor と整合し、dg 関手として構成済み。
三段階の係数制限比較の結合整合性を証明済み。
自由 Koszul の係数変更 dg 関手は総外積上の係数変更と一致し、
標準制限比較を挟んだ二段の合成律と恒等律を証明済み。
自由生成元変換の係数変更との自然性を総外積・dg 関手の各段階で証明済み。
チャートの具体的な可逆基底変換も係数変更と可換であり、規格化座標・微分の移送を
明示した dg 自然性の可換四角形を構成済み。
実際の座標表示のチャート dg 係数変更の合成律・恒等律も証明済み。
環射と pivot 変更をまとめた半線形 dg 遷移の Hom は、係数変更と明示基底変換で計算できる。
その二段の合成は直接遷移に一致し、合成単元の公式も証明済み。
全有限重なりの実際の環射にこの構成を適用して dg 遷移を構成済み。
環射の合成等式による行先の移送を含む標準制限比較後の合成律と、恒等制限比較後の恒等律を証明済み。
任意 dg 圏に使える有限重なりの標準制限合成比較を構成済み。
チャート外積模型上での三段階の制限比較の結合整合性と、左右の恒等制限との整合性を証明済み。
共通基底環への dg 係数制限後も対象・Hom の元の像を保ち、恒等・合成則を満たす。
一対象 dg 圏の自己 Hom を Mathlib の `Mon (Complex R)` へ接続し、
全非空有限重なりの包含順序圏から dg 代数への実際の関手を構成済み。
この係数図式は加群の厳密な貼り合わせを要求しない。
その上の coherent な dg 加群の降下模型と、層レベルの Dqc・Perf 比較は未完了。
係数 dg 代数図式と局所の導来底変更比較は構成済みだが、
coherent な加群の降下と Dqc・Perf 比較を含む導来 blowup 模型全体の完成とは扱わない。
所有モジュールの全1500定数（生成宣言を含む）の公理監査は標準三公理のみで成功。

次の実装単位は全 diagram-module の係数 dg 圏の結合律と dg 圏への組立て。
その加群圏を objectwise acyclic で導来化し、cartesian・局所 perfect 条件へ接続する。
L4 の T3 を使う層・cartesian dg 加群模型との比較は、この局所計算とは区別して残す。
L5c へはこの比較と L5b の例外因子・重なりの同定を済ませてから進む。

## 保存単位の検査

`lake build SerrePositivity.KST.DerivedBlowup` と
`lake env lean scripts/audit_kst_derived_blowup.lean` を実行する。
監査は所有モジュール内の生成宣言も含む全定数の依存公理を再帰検査し、
`propext`・`Classical.choice`・`Quot.sound` のみを許す。
他レーンの変更をコミットしない。ルート追加は担当集約の import 一行だけとする。
