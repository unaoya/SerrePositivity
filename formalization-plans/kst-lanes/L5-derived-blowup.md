# K-L5：導来 blowup と半直交分解

## 現在地

L5a の模型を固定。L5b の多項式チャート、普遍構造射、局所化環どうしの重なり同型、
O(1) の単元 cocycle、Koszul 生成加群の可逆変換と cocycle を対象ビルド済み。
変換は外積代数全体へ延長し、収縮微分の平方零・変換との可換性を証明した。
例外因子の列と全 a_j の列の可逆基底変換、外積への延長と微分適合も対象ビルド済み。
U_i・E∩U_i・D(n)∩U_i の underlying Koszul 複体と U_i の次数境界を構成済み。
外積の次数低下・平方零から自然数 chain 複体と整数 cochain 複体を構成済み。
微分に適合する生成元写像を複体の射・同型へ延長し、チャートと例外因子に特殊化済み。
同次左因子に対する graded Leibniz 則も証明済み。
整数次数付き複体の乗法を chain map として装備する工程、外積模型と既存反復 cone 模型の比較、有限列挙の順序交換、
普遍チャートと L7 の古典 blowup の同定は未実装であり、L5b 全体は未完了。
L5c〜L5f は未実装。完成は各工程の構成・比較・対象ビルドと全宣言公理監査が揃った時点。
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
整数 cochain への零延長とスカラー拡大の比較、および dg 圏のスカラー拡大比較への装備は未完了。
導来チャートの外積 dg 代数と underlying Koszul 複体は構成済みだが、
局所化と底変更の比較を含むチャート図式全体の完成とは扱わない。
所有モジュールの全567定数（生成宣言を含む）の公理監査は標準三公理のみで成功。

次の実装単位は整数 cochain の底変更同型と dg 圏の底変更比較。
重なり環への導来底変更・dg 関手のチャート cocycle の具体化も残る。
L5c へはこの比較と L5b の例外因子・重なりの同定を済ませてから進む。

## 保存単位の検査

`lake build SerrePositivity.KST.DerivedBlowup` と
`lake env lean scripts/audit_kst_derived_blowup.lean` を実行する。
監査は所有モジュール内の生成宣言も含む全定数の依存公理を再帰検査し、
`propext`・`Classical.choice`・`Quot.sound` のみを許す。
他レーンの変更をコミットしない。ルート追加は担当集約の import 一行だけとする。
