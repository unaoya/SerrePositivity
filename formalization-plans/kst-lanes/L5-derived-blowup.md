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
係数圏の結合律も証明し、全 diagram-module を表す実際の係数 dg 圏を構成済み。
その opposite 上の右 dg 加群として全 diagram-module の加群圏と通常の導来圏を定義済み。
図式全体の標準半自由分解・擬同型増大射と全次数 Hom に対する射影性を構成済み。
射影的 diagram-module の充満 dg 部分圏の H⁰ と全図式の主導来局所化との同値を証明済み。
各有限重なりの局所 dg 模型の係数圏への埋め込みと Hom の可逆性を構成済み。
各有限重なりへの実際の加群評価・導来評価、擬同型保存、局所化の因子分解、
underlying 複体が当該添字での値に一致することを証明済み。
導来評価による局所 perfect 性、その同型不変性と射影的 dg 充満部分圏を定義済み。
全次数自然変換の前後合成、図式の標準単位矢と左右作用の自然性を構成済み。
局所埋め込みから遷移後の局所埋め込みへの指定の単位パラメータ `GradedNatTrans` を構成済み。
その加群への全次数自然な作用を実際の閉加群射として構成し、加群射に関する自然性を証明済み。
指定の導来制限比較と、延長–制限随伴で移した canonical な導来係数拡大比較を構成済み。
主局所化上の両比較の自然変換と、随伴で元の指定射へ戻る等式を証明済み。
指定比較の可逆性による cartesian 条件、局所 perfect 条件との連言、
その射影的充満 dg 候補模型と両条件の同型不変性を構成済み。
この候補模型の H⁰ と cartesian・局所 perfect な主導来部分圏との同値を証明済み。
係数圏の指定単位矢の恒等・合成律と、全包含鎖で使える閉零射関手を構成済み。
各図式加群の underlying 複体図式と恒等・合成律を構成し、
局所加群比較の評価成分がその指定包含写像に一致することを証明済み。
一般の dg 遷移の等式に沿う加群制限の標準単位・合成同型と対象移送の評価を構成済み。
局所チャートへの適用と、指定加群比較の恒等包含に沿う単位条件を証明済み。
局所合成同型の対象移送を含む評価、図式加群上での恒等成分、および制限後の指定比較の評価を証明済み。
入力加群の射を自然変換へ送る underlying 複体図式関手と、各頂点による擬同型判定を証明済み。
一般 dg 遷移の等式に沿う導来制限の標準単位・合成自然同型を構成し、
局所化前の順逆成分との一致を証明済み。
有限重なりの局所導来制限にもこれを適用し、標準単位・合成同型と実加群上の計算経路を構成済み。
局所 dg 代数を `Mon (Complex R)` の一対象表示 `AlgebraVertex` へ正規化する比較を構成済み。
一般の一対象 dg 圏への Hom 恒等関手の dg 準同値性、代数射に関する恒等・合成保存を証明済み。
有限重なりの元の Koszul 模型への dg 準同値と、既存の大域係数圏への埋め込みとの整合性を証明済み。
正規表示での局所遷移の恒等・合成律、指定全次数自然変換、加群評価・標準制限同型・指定加群比較を構成済み。
全 diagram-module の係数圏と係数関手を保持し、局所の同じ dg 代数の表示のみを正規化する。
正規表示の標準制限同型の評価、指定比較と underlying 図式の包含写像の成分一致、
指定加群比較の単位条件・三重整合性を証明済み。
正規表示への導来評価と標準計算同型、局所 perfect 条件と同型不変性を構成済み。
元の Koszul 模型への指定 dg 準同値に沿う導来評価比較を構成し、
各局所 perfect 条件と全有限重なりでの既存局所 perfect 条件との iff を証明済み。
正規表示の指定導来制限比較を主局所化上の自然変換として延長し、
実際の延長–制限随伴から係数拡大比較、随伴公式、全導来射に対する自然性を構成済み。
標準導来制限単位・合成同型の実加群上の順逆成分と、制限の射の計算を構成済み。
正規表示の指定導来制限比較が実加群上で元の指定射の局所化像となることを証明済み。
指定導来制限比較の単位・三重整合性を自然変換の等式と各対象での等式として証明済み。
左随伴一意性で標準係数拡大同型を指定し、指定導来係数拡大比較の単位・合成条件を
対象ごとの等式と自然変換の等式として証明済み。恒等包含の指定比較の可逆性も証明済み。
元の Koszul 模型への dg 比較と局所遷移の可換四角形、指定加群比較の制限後の一致、
全導来対象で指定導来制限比較を正規表示へ制限した射との一致を証明済み。
指定導来制限の可換四角形と恒等成分を構成し、表示変更の準同値に沿う随伴計算により
元の指定係数拡大比較との可逆性の iff を証明済み。
全包含での cartesian 条件と cartesian・局所 perfect 条件の iff、および対象性質の等号を証明済み。
同じ射影的 dg 候補の H⁰ と正規表示の cartesian perfect 部分圏との同値を構成済み。
正規表示の標準加群制限同型自体の四頂点の結合整合性と左右の単位条件も証明済み。
標準導来制限同型自体についても同じ結合・左右単位条件を自然変換の等式として証明済み。
標準導来係数拡大同型と共役対応の一致、制限側の逆の整合性を構成し、
係数拡大側の四頂点の結合整合性と左右の単位条件も証明済み。
補助最小頂点に単位 dg 代数を置く係数図式と元の係数圏からの dg 包含を構成済み。
その補助頂点の共変 representable の制限として、全次数の作用を持つ実際の構造図式加群を構成済み。
各頂点の複体が指定局所代数に等しいこと、通常加群圏と主導来局所化での対象を構成済み。
指定包含単位からの閉零 Yoneda 拡張を構成し、その成分が加群作用で計算されることを証明済み。
共変 representable の包含先への局所制限と regular 代表加群を指定擬同型で比較し、局所 perfect 性を証明済み。
元の係数圏と補助係数圏の局所埋め込みの整合性、raw 加群の反復制限同型を構成済み。
構造図式加群の局所 regular 導来同型と全頂点の局所 perfect 性、
有限重なりの元の Koszul 模型での構造加群の局所 perfect 性を証明済み。
構造加群への直接 Yoneda 比較、その擬同型性、指定単位生成元と加群遷移の整合性を証明済み。
標準射影分解を介する導来延長比較の随伴公式と、代表延長比較の可逆性・随伴像を構成済み。
局所 regular 比較と指定加群遷移の可換式を主導来圏へ送り、
指定導来係数拡大比較が可逆であることから構造加群の cartesian perfect 性を証明済み。
元の Koszul 模型での cartesian perfect 性と、既存の射影的 dg 候補内の指定構造対象、
その H⁰ 比較像から構造図式加群の導来像への指定同型を構成済み。
捻りの大域実現と層レベル構造層との比較は未完了。
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
| `diagramModule_assoc_of_le`・tensor の零性・`diagramModule_assoc` | DiagramModuleAssociativity | 全ての対象での diagram-module 係数圏の結合律 |
| `DiagramModuleCoefficientObject`・`diagramModuleCoefficientDGCategory`・`AllDiagramModules`・`DerivedAllDiagramModules`・`BlowupDiagramCoefficientObject` | DiagramModuleCoefficientCategory | 既存 DGCategory へ接続した全 diagram-module の係数圏・全加群圏・通常の導来局所化 |
| `diagramModuleProjectiveResolution`・半自由性・擬同型・`ProjectiveDiagramModules`・代表・Hom の acyclic 性 | DiagramModuleProjectiveResolution | 各評価の性質ではなく全図式の Hom end に関する標準半自由・射影的置換 |
| `projectiveDiagramModuleInclusion`・`projectiveDiagramModuleToDerived`・充満忠実性・本質的全射性・`projectiveDiagramModuleHomotopyEquivalence` | DiagramModuleProjectiveEnhancement | 射影的 dg 図式加群の実際の H⁰ と主導来局所化の同値 |
| `FiniteOverlapVertexObject`・`finiteOverlapVertexDGFunctor`・Hom の可逆性 | FiniteOverlapVertex | 各有限重なりの局所模型の全図式係数圏への dg 埋め込み |
| `finiteOverlapModuleEvaluation`・擬同型保存・`finiteOverlapDerivedModuleEvaluation`・因子分解・評価値の一致 | FiniteOverlapModuleEvaluation | 各有限重なりへの実際の加群・導来評価と underlying 複体の計算 |
| `diagramLocallyPerfect`・同型不変性・`LocallyPerfectDerivedDiagramModules`・`LocallyPerfectProjectiveDiagramModules` | DiagramLocallyPerfect | 実際の導来評価による局所 perfect 条件。cartesian 条件はまだ課さない |
| `dgGradedWhiskerRight`・`dgGradedWhiskerLeft` | GradedNaturalWhiskering | パラメータ複体に関する全次数自然性を保つ dg 関手による前後合成 |
| `diagramModuleTransitionUnit`・左右作用公式・`diagramModuleTransitionUnit_natural` | DiagramModuleTransitionUnit | 包含に対する指定の単位矢と全 Hom 作用との自然性 |
| `finiteOverlapTransitionGradedNatTrans` | FiniteOverlapTransitionTransformation | 局所埋め込みから遷移後の埋め込みへの指定の全次数自然変換 |
| `transitionModuleParam`・`transitionModuleMorphism`・評価公式 | TransitionModuleAction | 全次数自然変換の加群への実際の閉零作用 |
| `transitionModuleMorphism_natural`・`transitionModuleNatTrans` | TransitionModuleNaturality | 指定作用の全加群射に関する自然性 |
| `finiteOverlapLocalDGTransition`・`finiteOverlapCompositeEvaluationIso`・`finiteOverlapModuleComparison` | FiniteOverlapModuleComparison | 指定の単位矢から反復制限加群への canonical な比較 |
| `finiteOverlapModuleComparisonNatTrans`・自然性 | FiniteOverlapModuleComparisonNaturality | 局所加群比較の実際の自然変換 |
| 導来評価の自然同型・`finiteOverlapDerivedRestrictionComparison`・`finiteOverlapDerivedExtensionComparison`・随伴公式 | FiniteOverlapDerivedComparison | 指定加群比較を主局所化と導来係数拡大へ移す |
| `finiteOverlapDerivedRestrictionNatTrans`・`finiteOverlapDerivedExtensionNatTrans`・両自然性 | FiniteOverlapDerivedNaturality | 主局所化の全射に関する canonical な比較の自然変換 |
| `diagramCartesian`・`diagramCartesianPerfect`・`CartesianPerfectDiagramDGModel` | DiagramCartesianCondition | 指定の導来係数拡大比較の可逆性と局所 perfect 性による候補模型 |
| cartesian・cartesian perfect 条件の同型不変性 | DiagramCartesianIsomorphism | 射影的代表への条件の移送 |
| `cartesianPerfectDiagramToDerived`・完全忠実性・本質的全射性・`cartesianPerfectDiagramHomotopyEquivalence` | DiagramCartesianEnhancement | 指定条件を満たす射影的 dg 模型の H⁰ と主導来部分圏の同値 |
| 指定単位矢の恒等・合成律・`diagramModuleUnitFunctor` | DiagramModuleUnitCoherence | 係数圏内の全包含鎖に対する指定閉零射関手 |
| `diagramModuleUnderlyingDiagram`・値と射の計算・恒等・合成律 | DiagramModuleUnderlyingDiagram | 指定単位矢を加群で送った基底環上の複体図式 |
| `finiteOverlapCompositeEvaluationIso_hom_eval`・`finiteOverlapModuleComparison_eval` | FiniteOverlapComparisonComponents | 局所加群比較と underlying 図式の指定包含写像との成分一致 |
| `transitionRestrictionIdIso`・`transitionRestrictionCompIso`・対象移送の評価 | TransitionRestrictionCoherence | 一般 dg 関手の等式を消去して得る標準制限比較 |
| 局所 dg 遷移の恒等・合成律、`finiteOverlapLocalModuleRestrictionIdIso`・`finiteOverlapLocalModuleRestrictionCompIso`・単位比較の評価 | FiniteOverlapModuleRestrictionCoherence | 局所 dg 遷移の等式と加群制限の標準比較の接続 |
| `finiteOverlapModuleComparison_id` | FiniteOverlapModuleComparisonIdentity | 指定加群比較と標準制限同型による恒等包含の単位条件 |
| `diagramModuleUnderlyingMap`・`diagramModuleUnderlyingFunctor`・擬同型判定 | DiagramModuleUnderlyingFunctor | 加群射を複体図式の自然変換へ送り、全図式の弱同値を各頂点で検出 |
| 合成同型の対象移送付き評価・恒等成分・制限した指定比較の評価 | FiniteOverlapModuleRestrictionCompositionEvaluation | 三重比較に現れる個別の成分計算。一般補題の型の継承で係数構造の再展開を避ける |
| `moduleDerivedIsoExtension`・順逆成分、`transitionDerivedRestrictionIdIso`・`transitionDerivedRestrictionCompIso` | TransitionDerivedRestrictionCoherence | 主局所化上への指定単位・合成自然同型の延長 |
| `finiteOverlapDerivedTransitionRestrictionIdIso`・`finiteOverlapDerivedTransitionRestrictionCompIso`・実加群上の順成分 | FiniteOverlapDerivedRestrictionCoherence | 有限重なりの局所導来制限に沿う標準単位・合成同型と指定計算経路 |
| `AlgebraVertex`・dg 構造・`algebraVertexToOriginal`・Hom 同型 | AlgebraVertex | 複体のモノイド対象の一対象 dg 正規表示 |
| `algebraVertexToOriginalEssSurj`・`algebraVertexToOriginalQuasiEquivalence` | AlgebraVertexComparison | 元の一対象 dg 圏への指定 Hom 恒等準同値 |
| `algebraVertexMap`・合成律・恒等律 | AlgebraVertexFunctor | dg 代数射の正規表示間の dg 関手 |
| `diagramAlgebraVertexEmbedding`・遷移・恒等合成律・指定全次数変換 | DiagramAlgebraVertex | 全図式の同じ係数圏内での正規表示の局所頂点と標準単位矢 |
| `FiniteOverlapAlgebraVertex`・元チャートへの準同値・大域埋め込みの整合性 | FiniteOverlapAlgebraVertexComparison | 正規表示と既存の有限重なり Koszul 模型の dg 比較 |
| 正規表示の加群評価・一段二段制限同型・`diagramAlgebraModuleComparisonNatTrans` | DiagramAlgebraModuleComparison | 元の全図式係数圏上の加群に対する正規表示での canonical な局所比較 |
| 正規表示の標準評価同型の恒等成分・`diagramAlgebraModuleComparison_eval`・任意局所対象での評価 | DiagramAlgebraModuleComparisonComponents | 指定比較の underlying 包含写像による計算 |
| `diagramAlgebraRestrictionIdIso`・`diagramAlgebraRestrictionCompIso`・任意局所加群上の恒等評価 | DiagramAlgebraRestrictionCoherence | 正規表示における標準単位・合成制限同型 |
| `diagramAlgebraModuleComparison_id`・`diagramAlgebraModuleComparison_comp` | DiagramAlgebraModuleComparisonCoherence | 標準制限同型を介する指定加群比較の単位・三重整合性 |
| `diagramAlgebraDerivedEvaluation`・擬同型保存・因子分解・標準自然同型・underlying 評価 | DiagramAlgebraDerivedEvaluation | 正規表示への実際の主導来評価 |
| `diagramAlgebraLocallyPerfect`・同型不変性 | DiagramAlgebraLocallyPerfect | 正規表示での局所 perfect 条件 |
| `finiteOverlapAlgebraDerivedEvaluationComparison`・`finiteOverlapAlgebraPerfect_iff`・全局所条件の iff | FiniteOverlapAlgebraPerfectComparison | 指定 dg 準同値を介する導来評価と既存局所 perfect 条件の一致 |
| `diagramAlgebraDerivedRestrictionNatTrans`・`diagramAlgebraDerivedExtensionComparison`・随伴公式・自然性 | DiagramAlgebraDerivedComparison | 正規表示での canonical な導来比較の構成 |
| 導来制限の生成射・標準単位合成同型の実加群上の順逆成分 | TransitionDerivedRestrictionComputation | 指定導来計算と元の加群射の主局所化像の一致 |
| 標準計算同型の恒等成分・`diagramAlgebraDerivedRestrictionNatTrans_app_Q_map` | DiagramAlgebraDerivedComputation | 正規表示の指定導来比較の主局所化像上での計算 |
| `diagramAlgebraDerivedRestrictionIdIso`・`diagramAlgebraDerivedRestrictionCompIso`・実加群上の順成分 | DiagramAlgebraDerivedRestrictionCoherence | 正規表示での標準導来制限単位・合成同型 |
| 指定導来制限比較の単位・合成自然変換等式と対象ごとの等式 | DiagramAlgebraDerivedComparisonCoherence | 加群比較の単位・三重整合性を主導来圏へ移送した結果 |
| `adjointComparisonIdIso`・`adjointComparisonCompIso`・単位と合成の移送補題 | AdjointComparisonCoherence | 右随伴の指定同型と比較射の整合性から左随伴側の整合性を導く |
| `diagramAlgebraDerivedExtensionComparison_id`・`diagramAlgebraDerivedExtensionComparison_comp`・自然変換等式・恒等包含の可逆性 | DiagramAlgebraDerivedExtensionCoherence | 正規表示の指定導来係数拡大比較の単位・合成条件 |
| `finiteOverlapAlgebraVertexToChart_transition` | FiniteOverlapAlgebraTransitionComparison | 正規表示と元の Koszul 模型の局所遷移の可換四角形 |
| `finiteOverlapAlgebraModuleComparison` | FiniteOverlapAlgebraModuleComparison | 元の指定加群比較を正規表示へ制限した射との一致 |
| 評価計算同型の恒等成分・`finiteOverlapDerivedRestrictionNatTrans_app_Q_map` | FiniteOverlapDerivedComputation | 元の指定導来制限比較を加群比較の局所化像として計算 |
| `finiteOverlapAlgebraDerivedRestrictionComparison_Q`・`finiteOverlapAlgebraDerivedRestrictionComparison` | FiniteOverlapAlgebraDerivedComparison | 全導来対象での指定制限比較の表示変更との整合性 |
| `adjointSquareIso`・`adjointSquare_comparison`・`adjointSquare_comparison_isIso_iff` | AdjointSquareComparison | 表示の随伴四角形から指定比較の整合性と可逆性の iff を導く |
| `finiteOverlapAlgebraDerivedRestrictionSquare`・成分計算 | FiniteOverlapAlgebraDerivedSquare | 局所 dg 表示変更と導来制限の指定可換四角形 |
| `diagramAlgebraCartesian`・`diagramAlgebraCartesianPerfect` | DiagramAlgebraCartesianCondition | 正規表示の指定比較による対象条件 |
| `finiteOverlapAlgebraDerivedExtensionComparison_isIso_iff` | FiniteOverlapAlgebraCartesianComparison | 元の Koszul 模型と正規表示の指定係数拡大比較の可逆性の一致 |
| cartesian・perfect 条件の iff と等号・`finiteOverlapAlgebraCartesianPerfectHomotopyEquivalence` | FiniteOverlapAlgebraCartesianConditions | 既存の大域 dg 候補を保持した正規表示の対象条件と H⁰ 比較 |
| `diagramAlgebraRestrictionCompIso_assoc`・`diagramAlgebraModuleRestriction` | DiagramAlgebraRestrictionAssociativity | 標準局所加群制限同型の四頂点の結合整合性 |
| `diagramAlgebraRestrictionCompIso_left_unit`・`diagramAlgebraRestrictionCompIso_right_unit` | DiagramAlgebraRestrictionUnits | 標準局所加群制限同型の左右の単位整合性 |
| `diagramAlgebraDerivedRestrictionCompIso_assoc` | DiagramAlgebraDerivedRestrictionAssociativity | 標準導来制限同型の四頂点の結合整合性の自然変換等式 |
| `diagramAlgebraDerivedRestrictionCompIso_left_unit`・`diagramAlgebraDerivedRestrictionCompIso_right_unit` | DiagramAlgebraDerivedRestrictionUnits | 標準導来制限同型の左右の単位整合性の自然変換等式 |
| `adjointComparison_conjugate` | AdjointComparisonConjugate | 左随伴一意性で作る指定同型と Mathlib の共役対応の一致 |
| `diagramAlgebraDerivedAdjunction`・標準単位・合成同型の共役公式 | DiagramAlgebraDerivedExtensionConjugate | 指定 graph 随伴での標準係数拡大同型の共役像の同定 |
| 標準制限合成同型の逆の結合・左右単位条件 | DiagramAlgebraDerivedRestrictionInverseCoherence | 係数拡大側へ移す向きの整合性 |
| `diagramAlgebraDerivedExtensionCompIso_assoc` | DiagramAlgebraDerivedExtensionAssociativity | 関手結合子を含む標準係数拡大同型の四頂点整合性 |
| `diagramAlgebraDerivedExtensionCompIso_left_unit`・`diagramAlgebraDerivedExtensionCompIso_right_unit` | DiagramAlgebraDerivedExtensionUnits | 関手単位子を含む標準係数拡大同型の左右の単位整合性 |
| `diagramAlgebraWithBottom`・対象と射の定義 | DiagramAlgebraWithBottom | 元の係数図式に単位 dg 代数を持つ補助最小頂点を加える |
| `diagramAlgebraWithBottom_hom`・`diagramAlgebraBottomInclusion` | DiagramAlgebraBottomInclusion | 元の係数 dg 圏の Hom を保つ補助係数圏への dg 包含 |
| `diagramStructureRawModule`・各頂点の値・`diagramStructureModule`・`derivedDiagramStructureModule` | DiagramStructureModule | 補助頂点の共変 representable の制限による実際の構造図式加群 |
| `diagramModuleTransitionUnit_action`・斉次作用・単位 cycle の合成公式 | DiagramModuleUnitAction | 指定包含単位の局所作用と単位 cycle の合成を計算 |
| `representableUnitMap`・評価公式・斉次作用公式 | RepresentableUnitMap | 全次数自然性を保持する指定閉零 Yoneda 拡張 |
| `rawModuleRestrictionCompIso`・`rawTransitionRestrictionCompIso`・成分公式 | RawRestrictionCoherence | 局所源にのみ small 仮定を要求する raw 加群の制限合成同型 |
| `diagramRepresentableLocalRaw`・`diagramRepresentableLocalRegularMap`・成分計算 | DiagramRepresentableLocalRegular | 共変 representable の包含先への局所制限と regular 代表加群の指定比較 |
| 指定局所 regular 比較の擬同型性・導来同型・局所 perfect 性 | DiagramRepresentableLocalPerfect | 局所代表生成元との比較から導く perfect 性 |
| `diagramStructureLocalComparisonIso`・`diagramStructureLocalRegularDerivedIso`・局所 perfect 性 | DiagramStructureLocalComparison | 実際の構造図式加群の局所評価と局所 regular 加群との指定導来比較 |
| `blowupStructureModule`・`derivedBlowupStructureModule`・cartesian perfect 性 | FiniteOverlapStructureModule | 元の Koszul 有限重なり模型への構造図式加群の適用 |
| `canonicalResolutionExtensionComparison`・随伴公式・射影的始域での可逆性 | ProjectiveExtensionComparison | 標準分解と通常 graph 延長の指定射を結ぶ導来比較 |
| `canonicalRepresentableDerivedExtensionMap`・同型・随伴像の計算 | RepresentableDerivedExtensionComparison | 代表制限比較を随伴像に持つ指定代表延長同型 |
| `representableUnitMap_postcomp`・`representableUnitMap_restrict` | RepresentableUnitNaturality | 指定閉零 Yoneda 拡張の後合成・係数制限自然性 |
| `moduleClosedUnitAction_apply` | ModuleClosedUnitEvaluation | 指定閉零係数射の作用をその cycle の斉次作用へ戻す |
| `diagramStructureLocalUnit`・`diagramStructureLocalRegularMap`・比較式・擬同型性 | DiagramStructureRegularMap | 実際の局所構造加群への直接 Yoneda 比較 |
| 補助包含の単位保存・cycle 保存・`diagramStructureLocalUnit_transition` | DiagramStructureUnitTransition | 構造加群の指定局所生成元と canonical な加群遷移の整合性 |
| `diagramStructureLocalRegularMap_transition` | DiagramStructureRegularTransition | 局所 regular 比較と代表制限比較・指定加群遷移の可換式 |
| `diagramStructureRegularDerivedIso`・制限側と拡大側の指定可換式 | DiagramStructureDerivedRegularTransition | regular 比較と canonical な導来遷移の経路の一致 |
| 指定係数拡大比較の可逆性・構造加群の cartesian perfect 性 | DiagramStructureCartesian | 実際に構成した大域構造図式加群の対象条件 |
| `blowupStructureDGObject`・`blowupStructureDGObjectDerivedIso` | FiniteOverlapStructureEnhancement | 既存の大域 dg 候補内での指定構造対象とその H⁰ 比較 |
| `finiteOverlapTwistUnit`・恒等・加法・逆・cocycle | FiniteOverlapTwistUnits | 共変 frame の向きで全整数の捻り単元 |
| `DiagramHomGauge`・`diagramGaugeDGFunctor` | DiagramHomGauge・DiagramGaugeFunctor | 合成条件を証明した Hom 重み付けによる実際の係数 dg 自己関手 |
| `restrictedScalarUnitIso`・`restrictedForward_eq`・`localForward_smul` | RestrictedScalarIso・RestrictedForwardScalar | 局所係数単元の自己同型と係数制限後の合成計算 |
| `finiteOverlapBaseDGTransition_smul`・`finiteOverlapTwistScalar` | FiniteOverlapTransitionScalar・FiniteOverlapTwistScalar | 半線形な遷移と具体的捻り自己同型 |
| `finiteOverlapTwistGauge`・`finiteOverlapTwistDGFunctor` | FiniteOverlapTwistGauge | 単元 cocycle による Hom 合成保存を証明した具体的自己関手 |
| `finiteOverlapTwistRawModule`・`finiteOverlapTwistModule`・`derivedFiniteOverlapTwistModule` | FiniteOverlapTwistModule | 全次数作用を持つ実際の大域 O(m) と主導来対象 |
| `diagramGaugeDGFunctor_vertex`・`diagramGaugeLocalIso` | DiagramGaugeLocal | 対角恒等性による局所埋め込みとの整合性と raw 制限同型 |
| `finiteOverlapTwistLocalIso`・局所 regular 導来同型・局所 perfect 性 | FiniteOverlapTwistLocal | 正規表示と元の Koszul 表示での O(m) の局所 perfect 条件 |
| `DiagramHomGauge.inverse`・関手の恒等／合成保存・両側逆 | DiagramGaugeInverse | 任意の証明済み gauge の dg 関手レベルでの逆と整合性 |
| `finiteOverlapTwistGauge_zero/add/neg`・`finiteOverlapTwistDGFunctor_zero/add`・両側逆 | FiniteOverlapTwistFunctorCoherence | 整数捻りの加法と逆を大域係数 dg 関手の等式として保持 |
| `finiteOverlapTwistAction`・`finiteOverlapDerivedTwistAction`・構造対象への値・単位／加法／逆比較 | FiniteOverlapTwistAction | 全図式加群圏と主導来圏での指定自然同型による整数捻り作用 |
| `diagramGaugeScale_rightLinear`・斉次積公式・`diagramGaugeRegularIso` | DiagramGaugeRegularIso | 包含の Hom gauge を行先の局所 regular 加群の指定自己同型へ移す |
| `diagramStructureLocalRegularMap_eval/isIso`・`diagramStructureLocalRegularIso` | DiagramStructureRegularIso | 構造加群の直接 regular 比較の具体的成分と通常加群圏での可逆性 |
| `diagramGaugeStructureModule`・直接 regular 比較・成分と可逆性 | DiagramGaugeStructureModule | 同じ定義の捻りを一般係数図式で扱い、Koszul 型の過剰な展開を避ける |
| `finiteOverlapTwistLocalRegularMap`・指定局所同型との可換式・可逆性 | FiniteOverlapTwistRegularMap | 実際の O(m) への直接 Yoneda 比較 |
| 任意の後続 Hom に対する包含単位の作用公式 | DiagramModuleUnitActionGeneral | 重み付けされた包含単位の局所生成元への作用 |
| gauge の包含単位の像・補助始点つき係数圏の像・cycle の像 | DiagramGaugeUnit | 指定閉零係数射の重みを補助 representable まで追跡 |
| `diagramGaugeStructureLocalUnit_transition` | DiagramGaugeStructureUnitTransition | canonical な加群遷移による局所生成元の像 |
| `representableUnitMap_identity/recover` | RepresentableUnitRecovery | 代表加群からの射を単位生成元の像から回収 |
| 重み付き Yoneda 射の同定・`diagramGaugeStructureLocalRegularMap_transition` | DiagramGaugeStructureRegularTransition | 直接 regular 比較と指定加群遷移の可換式 |
| 指定 regular／重み付き導来同型・制限側と拡大側の可換式 | DiagramGaugeStructureDerivedTransition | 指定随伴を通して canonical な比較の経路を一致させる |
| 指定係数拡大比較の可逆性・cartesian perfect 性 | DiagramGaugeStructureCartesian | 一般の gauge で捻った実際の構造加群の対象条件 |
| `derivedFiniteOverlapTwistModule_cartesian/cartesianPerfect` | FiniteOverlapTwistCartesian | 全整数 O(m) の元の Koszul 模型での指定 cartesian perfect 条件 |
| `blowupTwistDGObject`・`blowupTwistDGObjectDerivedIso` | FiniteOverlapTwistEnhancement | 既存の大域 dg 候補内の指定捻り対象とその H⁰ 比較 |
| 捻り射・零／加法比較・指数移送の頂点成分 | FiniteOverlapTwistActionComponents | 全図式加群で指定比較の成分を計算 |
| `finiteOverlapTwistActionAddIso_assoc/zero_left/zero_right` | FiniteOverlapTwistActionCoherence | 整数和の移送を含む加群圏での三段結合と左右単位条件 |
| 導来捻りの生成射・零／加法比較・指数移送の Q 上の計算 | FiniteOverlapDerivedTwistComponents | 主局所化前の指定比較への計算経路 |
| `finiteOverlapDerivedTwistActionAddIso_assoc/zero_left/zero_right` | FiniteOverlapDerivedTwistCoherence | 全ての主導来対象での三段結合と左右単位条件 |

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
所有モジュールの全2849定数（生成宣言を含む）の公理監査は標準三公理のみで成功。

指定の加群比較、主局所化上の制限比較、随伴で移した導来係数拡大比較を構成済み。
全射について自然であり、指定比較の可逆性による cartesian・局所 perfect 条件は同型で保たれる。
射影的候補模型の H⁰ 比較をこの条件へ制限した完全忠実・本質的全射な関手と同値も構成済み。
指定単位矢とその加群作用の underlying 恒等・合成律は証明済み。
標準制限同型を含む加群比較の単位条件も証明済み。
標準局所合成同型の具体的評価と、一般の導来制限の標準単位・合成自然同型も構成済み。
dg 準同値な一対象正規表示での指定加群比較の単位・三重整合性は証明済み。
既存局所 perfect 条件との一致と、正規表示の canonical な導来係数拡大比較の自然性は証明済み。
正規表示の指定導来制限比較の単位・三重整合性は証明済み。
指定導来係数拡大比較の単位・合成条件と恒等包含の可逆性も証明済み。
元の Koszul 模型と正規表示の局所遷移・指定加群比較・指定導来制限比較の整合性は証明済み。
元の指定係数拡大比較と正規表示の比較の可逆性は同値であり、cartesian perfect の対象条件は一致する。
標準局所加群制限同型の四頂点の結合整合性・左右の単位条件も証明済み。
標準導来制限同型自体の四頂点の結合・左右単位条件も自然変換の等式として証明済み。
標準導来係数拡大同型自体の四頂点の結合・左右単位条件も証明済み。
構造図式加群は実際の全次数 dg 加群と主導来対象として構成済み。
構造図式加群の局所 regular 加群との指定導来同型と局所 perfect 性を証明済み。
構造加群の canonical な係数拡大比較の可逆性、元の Koszul 模型での cartesian perfect 性、
既存の大域 dg 候補での指定構造対象とその H⁰ 比較まで構成済み。
有限重なり推移単元の整数冪、係数制限後の scalar 自己同型、
半線形性と局所双線形性から合成保存を証明した係数 dg 自己関手を構成済み。
この自己関手に沿う構造加群の制限として実際の大域 O(m) とその主導来対象を構成済み。
局所埋め込みとの整合性、構造加群への指定局所同型、局所 regular 導来同型、
正規表示と元の Koszul 表示での局所 perfect 性も証明済み。
捻りの零・加法・逆の整合性は大域係数 dg 関手の等式として証明済み。
全図式加群圏と主導来圏での捻り作用、構造対象への作用と指定 O(m) の一致、
標準制限比較を使う単位・加法・逆の自然同型も構成済み。
直接 Yoneda regular 比較の通常加群圏での可逆性、局所生成元に対する指定遷移の作用、
regular 自己同型の重みを含む指定加群遷移の可換式を証明済み。
主局所化と指定延長–制限随伴でこの可換式を移し、O(m) の canonical な
係数拡大比較そのものの可逆性を証明済み。元の Koszul 表示での全整数 O(m) の
cartesian perfect 性、既存の大域 dg 候補内の指定捻り対象とその H⁰ 比較を構成済み。
指定捻り作用の三段加法比較と左右単位条件は、整数和の対象移送を含めて
全図式加群と主導来圏の全対象で証明済み。これは指定自然同型の整合性であり、
∞圏の極限比較や層の降下をこれだけから結論しない。
次の実装単位は一般の cartesian perfect 対象に対する捻り作用の保存、
および coherent な降下との接続。
射影的 dg 模型の H⁰ 比較だけで、dg 商の普遍性や層の降下との比較を済んだとは扱わない。
L4 の T3 を使う層・cartesian dg 加群模型との比較は、この局所計算とは区別して残す。
L5c へはこの比較と L5b の例外因子・重なりの同定を済ませてから進む。

## 保存単位の検査

`lake build SerrePositivity.KST.DerivedBlowup` と
`lake env lean scripts/audit_kst_derived_blowup.lean` を実行する。
監査は所有モジュール内の生成宣言も含む全定数の依存公理を再帰検査し、
`propext`・`Classical.choice`・`Quot.sound` のみを許す。
他レーンの変更をコミットしない。ルート追加は担当集約の import 一行だけとする。
