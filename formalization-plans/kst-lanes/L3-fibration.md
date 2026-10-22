# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使う。(d) は 10-22 コーディネータ回答により、厳密 dg 入力 S 上の ν:S→StableInfinity と K:S→Sp を固定し、ν の像が K-5 VerdierDiagram となる dg Verdier 列を K が fiber 四角形へ送る相対形で述べる。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-23）
### 現在地
- 工程 (a) 完了。K-5 の実核条件から包含の本質像を同定し、cofiber-W と商の可逆性、
  二対三・pushout・pullback・ホモトピーに対する拡大安定性を証明。
- 工程 (b)：全相対 S_n・W 判定・面退化・core 包含・商への射と核四角形を構成。
  W 辺・相対 cofiber 射影は trivial Kan。K-1 で全正有限反復の加法性へ接続。
- 有限 W 列の初期頂点・連続 cofiber 比較は、零長で厳密同型、全長・全正反復で局所化同型。
  全単体的有限積比較は未主張。元の相対 S と W 列 core S の対角・定数列・実押し出しを保持。
- 元の核包含を実核への完全同値へ制限し、K-2 Segal 実現で元の核四角形を homotopy pullback と証明。
  relativeSFibrationFiberIso は実 fiber と core S(D) の局所化同型で、同じ射影は元の包含の実現射。
  quotientSFibrationFiberIsoOfComparison は条件付き。商実現比較の可逆性は未証明で、無条件 K-6(b) は未完。
- Ore・分母輸送・固定分数・可変終点 coslice の既存構成は保持し、新設は Sp 正本へ依頼する。
  全 span 族の評価・全単体被覆・W 反転・降下・同じ分数比較の回収を構成。一般比較同値・span 普遍性は未証明。
  tamme* の lax 専用仮定を一般 Verdier 商へ流用しない。H⁰ の普遍性で全写像空間を代用しない。
- 元の scaffold 埋め込み・二脚・相対三角・係数点と、native 表現の pointedMap の指定点を保持。
  豊穣実現・curry・転置・反転・strict transport の同じ指定成分を、元の点の作用と照合済み。
- 切断の底変換・under 実現・初頂点制限・反転・共通 Hom 解像の指定成分を、元の実図式と照合。
  同じ strict 持ち上げの恒等射評価は、第一射影により元の単体切断の初頂点を厳密に回収する。
- 設計修正：F1 の exists_leftCoherentTransport_directComparison は底上の同値のみを指定し、
  scaffold の指定三角形を残さない。この界面から元の係数点との一致は推論しない。
- scaffoldNerveRepresentationIso は指定 scaffold 三角形を保持し、係数点を元の恒等射評価の同じ fiber 点の
  pointedMap 像へ送ると証明。scaffoldStraighteningRepresentationIso はその指定制限比較を Sp の前合成充満忠実性で戻す。
  新主経路の scaffoldPointedReconstruction は実射・射影・前合成同値・fiber 点計算を構成。
- 指定した全制限比較と降下後の同じ成分を厳密に照合。native 表現の制限点は第一射影した元の同じ fiber 点の像。
  元の単体切断の係数点を、新復元射による同じ初頂点 fiber 点の実像へ接続済み。
- 左右の底変換比較を、像の単体と pullback 対象の初頂点比較へ端点等式も含めて照合。
  元の大域底変換の同じ実図式成分は、第一射影切断を像の単体へ輸送した復元点を、pullback 復元点へ送る。
  全単体切断の等式輸送は全空間値を保ち、初頂点 fiber 点は既存の実底変換同型の像と厳密に一致。
  任意の実 fiber 点を零単体切断で表して同じ点を回収し、元の実図式の同じ指定成分に対する復元像の自然性を証明。
- 新分類比較は、strict・cocartesian 切断の元の係数点を、実底変換した同じ fiber 点の新復元像へ送る。
  既存の coslice 点族は恒等錐で同じ実点を回収。新復元恒等点からの延長は新復元射と全写像空間で自然同型で、前合成同値。
- 既存の分数分類を新比較へ接続。元の恒等 span の strict Kan 比較像は、既存の固定分数評価を経由して
  同じ scaffold 復元恒等点へ送られる。元の coslice 合成は新復元射と全相対写像空間で自然同型で、無条件に前合成同値。
  比較射単体の同値性・span 側の普遍性は未証明。この片側三角形だけからは結論しない。
- 工程 (c)：中央・右 π の k 未満の消滅の下で、左 fiber の同じ消滅 ⇔ πₖ 射影全射を K-5 の実長完全列で証明。
  中央 πⱼ=0 なら右 πⱼ₊₁／射影像 ≃ 左 fiber πⱼ。代表元は元の接続射。零次余核の障害を明示。
- 固定 dg K の実頂点・実辺の整数 π 作用を同じ BF 射と可換に比較し、πⱼ 全射性の同値を証明。
  具体的商射の π₀ 全射性は未証明。K の局所化性を仮定しない。
- 工程 (d) はユーザー指定の相対形：同じ厳密 dg 入力 S 上の ν:S→StableInfinity、K:S→Sp。
  ν の像が K-5 VerdierDiagram となる D β3 の dg 列に (b)(c) を適用し、固定 S• 比較で K へ戻す。定理は未完。
- 工程 (e)：N の冪等完備化の普遍性・安定性・完全性と BGT §9 の入力境界を本文に整理。K-7 本体は別工程。
- 対象 10494 jobs・監査 433 モジュール 2452 宣言・全体 25202 jobs が成功。標準三公理のみ。
  宣言型の ModelCategory・禁止ソース・diff 検査も成功。所有 import 閉包 6701 モジュールは EInfinity を含まない。
### 残り（依存順）
1. 商実現比較を証明し、無条件の連結版 fibration 定理へ接続する（Waldhausen 1.6.4、BGT §7、40–80時間）。
2. 必要な cofinality 条件を厳密 dg 上の固定 K と比較する（BGT §7–8、16–32時間）。
3. ν の像が VerdierDiagram となる dg 列を K が実 Sp fiber 四角形へ送る相対定理（BGT §7–8、16–32時間）。
4. 固定 dg 界面との接続後に、完備化と BGT §9 の非連結化への実入力を確定する（8–16時間、K-7 本体は別）。
### 主要宣言（共通接頭辞 SerrePositivity.KST.Fibration）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、
  weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- relativeSConstruction、relativeSimplicialSConstruction、relativeSimplicialQuotientMap、relativeSimplicialKernelSquare。
- weakStringConstantPostSquare_homotopyPullback、relativeSKernelRealizationSquare_homotopyPullback。
- relativeSFibrationFiberIso、quotientSFibrationFiberIsoOfComparison。
- fractionKanQuotientDiagram_classificationIso、weakQuotientCosliceComparison、weakQuotientCosliceUnit_identity。
- weakSpanKanMappingComparison_value_equivalence_iff、weakIdentityKanMappingComparisonUnitIso。
- leftStraighteningCandidate_classificationIso_pointHom、leftCocartesianKanClassificationIso_pointHom。
- dgKPiComparison、dgKPiComparison_naturality、dgKPiMap_surjective_iff。
- straighteningGlobalBaseChangeValueIso_pointHom、leftStraighteningDiagramBaseChange_heq_globalValue。
- transportUnderJointComponentIso_pointHom、transportUnderJointComponentIso_heq_realizationMap。
- straighteningBaseChangeRightChart_heq_firstVertex、straighteningBaseChangeLeftChart_heq_firstVertex、
  straighteningUnderRealizationChart_eq_joint、straighteningUnderRealizationChart_pointHom。
- firstVertexOppositeChart_pointHom、firstVertexTransportDiagramIso_heq_oppositeChart。
- scaffoldNerveRepresentationIso_pointHom、scaffoldStraighteningRepresentationIso_pre、
  scaffoldPointedReconstruction、scaffoldPointedReconstruction_pointHom。
- scaffoldStraighteningGlobalChart_original_pointHom、firstVertexSectionFiberPoint_val、
  scaffoldPointedReconstruction_coefficient_pointHom。
- scaffoldBaseChangeCoefficientIso_pointHom、scaffoldBaseChangeCoefficientIso_heq_diagramValue、
  straighteningBaseChangeLeftChart_eq_firstVertex、straighteningBaseChangeRightChart_eq_firstVertex。
- baseChangeImageSectionFiberPoint_eq、vertexFiberZeroSection_firstVertex、
  scaffoldVertexBaseChangeIso_eq_diagramValue、scaffoldPointedReconstruction_baseChange_pointHom。
- scaffoldCocartesianBaseChangeClassificationIso_pointHom、coslicePointFamilyAt_recoveryIso、
  scaffoldCoslicePointExtension_reconstructionIso、scaffoldCoslicePointExtension_isPrecompositionEquivalence。
- weakIdentityNativeComparisonImage_scaffold_pointHom、weakCosliceComposite_scaffold_relativeIso、
  weakCosliceComposite_scaffold_functorIso、weakCosliceComposite_isPrecompositionEquivalence。
- firstVertexRestrictionChart_pointHom_strictSection、firstVertexStrictSectionMap_evaluate_fst、
  firstVertexDiagramIso_heq_restrictionChart。
- relativeSectionBaseChangeComponentIso_pointHom、relativeSectionBaseChangeComponentIso_heq_transportMap、
  leftStraighteningSectionJointDiagram_baseChangeIso_pre、leftStraighteningSectionJointDiagram_baseChangeIso_vertex。
- fiberGroup_lowerBound_iff_projection_surjective、connectiveFiber_iff_projection_piZero_surjective、
  fiberCofinalityObstructionEquiv、piZeroCofinalityObstructionEquiv_mk。
### 依存と提供
- 読み取り専用：KST/SConstruction、KST/LocalizingInvariants、KST/Spectra、InfinityCategories/Derived。
- K-S• の固定 K-1/K-2 は L1 §6：加法性、MultiRealizationFunctorIso の正反復、RelativeCofiberLeftFiber、
  RelativeFiberEquivalence と Quillen A。任意 W への制限・底変換・元の射影の照合は K-F が証明する。
- 相対 (d) の追加固定入力三点を K-S•（01a151d3-f75d-7ef2-9d1f-908c85eb1be1）へ依頼済み。
  DGKFixedInterface・DGKFixedSConstruction は読み取り専用で対象ビルドを確認。固定 ν・K と頂点・辺の同定を入力する。
- 商・分数・局所化は Sp 正本。一般 fractionMappingComparison の同値性を Sp に依頼し、L9 受付に登録済み。
- Sp の IsStable は使わない。実 fiber 列・整数長完全列・π 同値検出を使う。提供先は K-7 と K-基盤 2。
### 未コミット
- なし（分数分類の既存界面の接続修正、後合成の指定点・恒等 span の照合・coslice 三角形の7モジュールと集約・監査・本計画）。
### 既知の問題
- 一般分数比較の同値性、span 側の普遍性、商実現比較、具体的商射の π₀ 全射性、相対 Sp 値 K-6 は未完。
- 現在の条件付き fiber 同型や一般の群判定を、具体的 K の局所化性の証明とは数えない。
### 次の一手
- Sp の一般分数比較同値の公開を確認する。固定 dg K の実 π 比較は構成済みだが、具体的商射の π₀ 全射性は未証明。
  元の coslice 合成の片側三角形は無条件に構成済み。反対の span 側の三角形と普遍性へ進む。
  同じ商上の単位を元の span 族へ制限し、既存の W 輸送・指定恒等点と照合する。新しい一般分数補題は Sp へ依頼する。

## 規約
- 配置 `SerrePositivity/KST/Fibration/`、集約 `KST/Fibration.lean`、監査 `scripts/audit_kst_fibration.lean`。
- foundations.md §8 と k-theory-kst-route.md §13（決定 15・16）。H⁰ の Verdier 普遍性で写像空間の比較を代用しない。Sp の IsStable は使わない。
- 原典：Waldhausen 1985 §1.6、BGT 2013 §7〜9、Barwick 2016。

## 冪等完備化・K-7 への入力境界（工程 e）

原典：[BGT §9.1、定義 9.1・9.6](https://arxiv.org/pdf/1001.2282#page=57)。
FκA=(Indω A)κ と ΣκA=FκA/A の列、K(FκA) の消滅、完全列・κ-filtered 余極限の保存を使い、
非連結 K は colimₙ ΩⁿK(ΣκⁿA) で構成する。これらの構成・消滅・余極限の証明は K-7 側。

| 入力 | 検証した正本と K-F の境界 |
| --- | --- |
| 完備化前の商 | Sp の IsVerdierSequence・VerdierSequence。K-F の quotientSFibrationFiberIsoOfComparison は商実現比較の可逆性が未証明の条件付き界面。 |
| 完備化 | N の IsIdempotentCompletion は充満忠実性と retract 条件を保持。IsIdempotentCompletion.pre_isQCatEquivalence は全関手 ∞ 圏の普遍性。H⁰ では代用しない。 |
| 安定・完全性 | N の IsIdempotentCompletion.isStable・isExactFunctor、idem_isStable・idemYoneda_isExactFunctor を使う。元の Idem C は宇宙 u+1、idemYoneda の始域は ulift C。 |
| 零次 cofinality | 厳密 dg 入力の ν と K の指定比較へ接続する。完備化という条件だけでは π₀ 全射性を入力せず、実 K 比較で検査する。K-F の piZeroCofinalityObstructionEquiv は中央 π₋₁=0 の下で、元の射影の余核を左 fiber の π₋₁ と同定する。 |
| K-7 への提供 | 指定射影と点を保つ条件付き相対 S fiber 比較、零次障害・連結性判定。各 suspension 段階の実比較と構造写像の整合性が必要。非連結 K 自体とその局所化性は未構成。 |
