# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使う。(d) は 10-22 コーディネータ回答により、厳密 dg 入力 S 上の ν:S→StableInfinity と K:S→Sp を固定し、ν の像が K-5 VerdierDiagram となる dg Verdier 列を K が fiber 四角形へ送る相対形で述べる。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-23）
### 現在地
- 工程 (a) 完了。K-5 の実核条件から包含の本質像を同定し、cofiber-W と商の可逆性、
  二対三・pushout・pullback・ホモトピーに対する拡大安定性を証明。
- 工程 (b)：全相対 S_n・面退化・core 包含・商への射と核四角形を構成。元の全 Ar 評価・S 後合成の完全性と全成分の零対象検出を証明。
  同じ実 cofiber による相対辺判定と、全 n の二対三・pushout・pullback・拡大安定性を証明。元の S_n(D) 包含は全写像空間で充満忠実で実核像に一致し、同じ cofiber の像条件を回収。W 辺・相対 cofiber 射影は trivial Kan、全正反復の加法性へ接続済み。
- 有限 W 列の初期頂点・連続 cofiber 比較は、零長で厳密同型、全長・全正反復で局所化同型。
  全単体的有限積比較は未主張。元の相対 S と W 列 core S の対角・定数列・実押し出しを保持。
- 元の核包含を実核への完全同値へ制限し、K-2 Segal 実現で元の核四角形を homotopy pullback と証明。
  relativeSFibrationFiberIso は実 fiber と core S(D) の局所化同型で、同じ射影は元の包含の実現射。
  quotientSFibrationFiberIsoOfComparison は条件付き。元の S• 商核四角形を構成し、同じ商実現比較の可逆性を入力すれば homotopy pullback。通常の全錐比較と任意の Kan 四角形の橋渡しにより、同じ Ex∞ coherent 四角形は native な ∞ 引き戻し。元の四頂点・四辺を同じ Ex∞ Kan 値と元の射の coherent な一単体として回収し、同じ相対 S 核の角の終対象性も証明。一回の反復実現への全 Hom の座標読み替えは元の豊穣関手と等しい。指定 Verdier 四角形の包含・商辺と三頂点は厳密一致し、残る角は実終対象間の同型。零値完全関手の実 Kan Hom 部分空間は可縮で、任意の指定部分族を厳密に保つ延長と元の全正反復 S の全 Hom への図式比較を構成。零圏から・零圏への全 Hom の可縮性により、指定 Verdier 四角形は元の StableInfinity の零角付き四角形となる。指定 Verdier 上側二単体の全長 Hom を元の零値部分複体へ読み出し、同じ全長 Hom と元の全正反復 S 像で厳密照合。元の上下二単体の共有対角 δ₁ は厳密一致。下側の全長 Hom も零値族へ読み出し、全正反復 S 像で厳密回収。共有対角の同じ両端で読んだ両二胞体族は直接 path の像が同じ対角頂点で、全関手同型を構成。対角上で恒等の比較と全四角形比較は未証明。商実現比較の可逆性は未証明で、無条件 K-6(b) は未完。
- Ore・分母輸送・固定分数・可変終点 coslice の既存構成は保持し、新設は Sp 正本へ依頼する。
  全 span 族の評価・全単体被覆・W 反転・降下・同じ分数比較の回収を構成。一般比較同値・span 普遍性は未証明。
  tamme* の lax 専用仮定を一般 Verdier 商へ流用しない。H⁰ の普遍性で全写像空間を代用しない。
- 元の scaffold 埋め込み・二脚・相対三角・係数点と、native 表現の pointedMap の指定点を保持。
  豊穣実現・curry・転置・反転・strict transport の同じ指定成分を、元の点の作用と照合済み。
- 切断の底変換・under 実現・初頂点制限・反転・共通 Hom 解像の指定成分を、元の実図式と照合。
  同じ strict 持ち上げの恒等射評価は、第一射影により元の単体切断の初頂点を厳密に回収する。
- F1 の exists_leftCoherentTransport_directComparison は底上の同値だけで指定 scaffold 三角形を残さず、元の係数点との一致は推論しない。
- scaffoldNerveRepresentationIso は指定 scaffold 三角形を保持し、係数点を元の恒等射評価の同じ fiber 点の
  pointedMap 像へ送ると証明。scaffoldStraighteningRepresentationIso はその指定制限比較を Sp の前合成充満忠実性で戻す。
  新主経路の scaffoldPointedReconstruction は実射・射影・前合成同値・fiber 点計算を構成。
- 指定した全制限比較と降下後の同じ成分を厳密に照合。native 表現の制限点は第一射影した元の同じ fiber 点の像。
  元の単体切断の係数点を、新復元射による同じ初頂点 fiber 点の実像へ接続済み。
- 左右の底変換比較の端点等式と切断の全空間値を保持。初頂点 fiber 点は既存の実底変換像と厳密一致。
  任意の実 fiber 点を零単体切断で回収し、元の実図式の同じ指定成分に対する復元像の底変換自然性を証明。
- 新分類比較は、strict・cocartesian 切断の元の係数点を、実底変換した同じ fiber 点の新復元像へ送る。
  既存の coslice 点族は恒等錐で同じ実点を回収。新復元恒等点からの延長は新復元射と全写像空間で自然同型で、前合成同値。
- 既存の分数分類を新比較へ接続。元の恒等 span の strict Kan 比較像は、既存の固定分数評価を経由して
  同じ scaffold 復元恒等点へ送られる。元の coslice 合成は新復元射と全相対写像空間で自然同型で、無条件に前合成同値。
  元の比較に、商上の実右逆と全相対写像空間内の余単位を構成。同じ右逆を全 fiber へ制限し、余単位と本質的全射性を証明。
  同じ比較二胞体の成分の点の射の全射性を、元の strict Kan 比較成分の実本質的全射性へ移送。
  Sp 正本の全終点の充満忠実性を入力すれば元の商上の比較自体が可逆となる。逆順の span 三角形・正本の充満忠実性・無条件の比較同値・span 普遍性は未証明。
- 工程 (c)：中央・右 π の k 未満の消滅の下で、左 fiber の同じ消滅 ⇔ πₖ 射影全射を K-5 の実長完全列で証明。
  中央 πⱼ=0 なら右 πⱼ₊₁／射影像 ≃ 左 fiber πⱼ。代表元は元の接続射。零次余核の障害を明示。
- 固定 dg K の実頂点・実辺の整数 π 作用を同じ BF 射と可換に比較し、πⱼ 全射性の同値を証明。
  元の Verdier 商の三角圏 K₀ 作用は全射で、同じ射の代数的零次余核は零群。
  固定 ν の同じ dg 辺の K₀ 作用を実完全関手と照合し、ν 像が Verdier 列となる厳密 dg 列の全射性を証明。
  既存の厳密 dg K₀ 自然比較と固定頂点・辺の同定で、ν 像が Verdier となる同じ固定 K 商辺の実 π₀ 全射性を証明。
  任意の相対 Verdier 四角形の元の右辺を同じ dg 射として回収し、ν 像の商辺と照合。元の K 右辺の実 π₀ 全射性を証明。
  同じ相対 K 右辺を持つ実 Sp fiber 四角形を構成し、元の BF fiber との群同型で全負整数群の消滅を証明。K(D) との同定は未証明。
  ν(P) が零なら全反復 S・境界商の一点射が局所化可逆で、正段の整数 π 検出により固定 K(P) は零。任意の元の相対 K 四角形の零角を保持する。
- 工程 (d) はユーザー指定の相対形：同じ厳密 dg 入力 S 上の ν:S→StableInfinity、K:S→Sp。
  元の零角・右辺を保持した canonical fiber と K(D) からの実比較辺、全脚の合成三角形を構成。元の四角形の引き戻し性 ⇔ 同じ比較辺の可逆性を証明。
  比較先を同じ dg 右射の BF fiber に比較し、両端の負次数消滅を証明。元の比較の非負次数 π が全単射なら元の K 四角形は引き戻し。非負次数の条件は未証明。
  固定 K の非負次数 π と一段 S• 境界商の π を自然に比較。元の core S•・対角実現・境界商の全 Hom を ν 後合成と照合し、指定 VerdierDiagram の境界商四角形と固定 K の各正段四角形を全高次単体で同定。元の反復実現から境界商への商射は全 Hom に自然で、同じ Ex∞ 商射を成分とする全図式同型を構成。基点忘却後の全正段で同じ Sp 辺の可逆性を検出し、元の実 fiber 錐の極限性も証明。元の相対 K 四角形が引き戻し ⇔ ν 像の元の全正反復 S• 実現の Ex∞ 四角形が引き戻し、まで証明。後者の無条件な引き戻し性は未証明。
- 工程 (e)：N の冪等完備化の普遍性・安定性・完全性と BGT §9 の入力境界を本文に整理。K-7 本体は別工程。
- 対象 10740 jobs・監査 524 モジュール 3031 宣言・全体 25676 jobs が成功。標準三公理のみ。
  宣言型の ModelCategory・禁止ソース・diff 検査も成功。所有 import 閉包 6945 モジュールは EInfinity を含まない。
### 残り（依存順）
1. 商実現比較を証明し、無条件の連結版 fibration 定理へ接続する（Waldhausen 1.6.4、BGT §7、40–80時間）。
2. 証明済みの任意の相対 Verdier 四角形の実 π₀ cofinality・fiber 連結性を、β3 の具体提示へ照合する（BGT §7–8、4–8時間）。
3. 証明済みの固定 K の相対零保存と元の四角形を保持し、dg Verdier 列を実 Sp fiber 四角形へ送る相対定理へ接続する（BGT §7–8、16–32時間）。
4. 固定 dg 界面との接続後に、完備化と BGT §9 の非連結化への実入力を確定する（8–16時間、K-7 本体は別）。
### 主要宣言（共通接頭辞 SerrePositivity.KST.Fibration）
- weakEquivalences、mem_weakEquivalences_iff_invertible、weakEquivalences_twoOfThree、weakEquivalences_pushout_iff、weakEquivalences_pullback_iff、weakEquivalences_extension。
- verdierSStageKernelEquivalence_inclusion、verdierSPostcomp_fullyFaithful、verdierSPostcomp_kernel、relativeSConstruction_mem_edge_iff_cofiber_image。
- weakStringConstantPostSquare_homotopyPullback、relativeSKernelRealizationSquare_homotopyPullback、relativeSFibrationFiberIso、quotientSFibrationFiberIsoOfComparison、quotientSKernelInfinitySquare_isPullback、quotientSKernelInfinitySquare_right、quotientSKernelInfinitySquare_bottom、quotientSKernelInfinitySquare_corner_isTerminal、stableCoreSingleKanEnrichedFunctor_eq、stableMultiSingleKan_edge、quotientSKernelInfinitySquare_right_eq_verdierSingle、quotientSKernelInfinitySquare_bottom_eq_verdierSingle、quotientSKernelCornerIso_verdierSingle、zeroStableHomSpace_isContractibleKan、zeroStableHomFamily_extend、zeroStableHomMultiFamilyIso、verdierDiagramZeroTriangle、stableHomZeroVertex_iff_of_edge、coherentTriangleLongHom、verdierUpperTriangleZeroHomLift_recovery、verdierUpperTriangleZeroHomLift_multi_recovery、verdierTriangle_sharedDiagonal、verdierLowerTriangleZeroHomLift_multi_recovery、verdierNullHomFamily_direct、verdierNullHomFamilyIso、exInfinityCommSqInfinitySquare_isPullback、strictCoherentCone_isLimit_iff_of_transformation、fractionKanQuotientDiagram_classificationIso、weakQuotientCosliceComparison、weakQuotientCosliceUnit_identity。
- weakSpanKanMappingComparison_value_equivalence_iff、weakIdentityKanMappingComparisonUnitIso、leftStraighteningCandidate_classificationIso_pointHom、leftCocartesianKanClassificationIso_pointHom。
- dgKPiComparison、dgKPiComparison_naturality、dgKPiMap_surjective_iff、dgKNativeSBoundaryPiEquiv_naturality、dgKNativePiMap_bijective_iff_sBoundary、dgRelativeVerdierSBoundaryFixedKSquareIso、dgRelativeKPositiveSquare_isPullback_iff、spectrumFiberSquare_evaluation_isPullback、spectrumEdge_isInvertible_of_positive_evaluation、dgRelativeK_isPullback_iff_sBoundary、stableBoundaryQuotientKanIso、verdierMultiBoundaryForget_isPullback_iff、spectrumEdge_isInvertible_of_positive_spaceEvaluation、dgRelativeK_isPullback_iff_multiRealization。
- dgKInputK_preservesRelativeZero、dgRelativeK_zero_corner、dgRelativeKZeroTriangle、dgRelativeFiberVertexComparison、dgRelativeK_isPullback_of_fiberComparison_pi_nonnegative。
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
- verdierKZeroMap_surjective、verdierKZeroCofinalityObstruction_subsingleton、dgNuKZeroMap_surjective_of_verdier。
- dgKPiZeroMap_surjective_of_verdier、dgKBFHomotopyFiber_negative_subsingleton_of_verdier、
  dgKInputFiberSquare、dgRelativePiZeroMap_surjective、dgRelativeFiberSquare_negative_subsingleton。
- weakCosliceComparisonFiber_isEssentiallySurjective、weakSpanKanMappingComparison_value_isEssentiallySurjective、
  weakQuotientMappingComparison_isIso_of_fraction_fullyFaithful。
- relativeSectionBaseChangeComponentIso_pointHom、relativeSectionBaseChangeComponentIso_heq_transportMap、
  leftStraighteningSectionJointDiagram_baseChangeIso_pre、leftStraighteningSectionJointDiagram_baseChangeIso_vertex。
- fiberGroup_lowerBound_iff_projection_surjective、connectiveFiber_iff_projection_piZero_surjective、
  fiberCofinalityObstructionEquiv、piZeroCofinalityObstructionEquiv_mk。
### 依存と提供
- 読み取り専用：KST/SConstruction、KST/LocalizingInvariants、KST/Spectra、InfinityCategories/Derived。
- K-S• の固定 K-1/K-2 は L1 §6：加法性、MultiRealizationFunctorIso の正反復、RelativeCofiberLeftFiber、
  RelativeFiberEquivalence と Quillen A。任意 W への制限・底変換・元の射影の照合は K-F が証明する。
- 相対 (d) の追加固定入力三点を K-S•（01a151d3-f75d-7ef2-9d1f-908c85eb1be1）へ依頼済み。
  DGKFixedInterface・DGKFixedSConstruction は読み取り専用。固定 ν・K の頂点・辺と既存の厳密 dg の K₀ 自然比較・負次数消滅を使う。
- 商・分数・局所化は Sp 正本。一般分数比較の充満忠実性は L9 受付に登録済み。厚い β3 列の実核接続・有限線型図式の局所化も依頼済み。
- Sp の IsStable は使わない。実 fiber 列・整数長完全列・π 同値検出を使う。提供先は K-7 と K-基盤 2。
### 未コミット
- なし（元の共有対角・指定 Verdier 下側二胞体の厳密回収・同じ Hom 内の上下二胞体族の比較の5モジュール、集約・監査・本計画）。
### 既知の問題
- 一般分数比較の同値性、有限線型図式の局所化、span 普遍性、商実現比較、厚い β3 列の実核接続、相対 Sp 値 K-6 は未完。
- 現在の条件付き fiber 同型や一般の群判定を、具体的 K の局所化性の証明とは数えない。
### 次の一手
- verdierNullHomFamily の上下二族を、直接 path の同じ対角頂点上で恒等となる相対比較で結ぶ。零値 Hom 部分空間 Z の可縮性と Functor.PullbackObjObj.ofIsTerminal の相対内部 Hom で、指定部分への制限の実 fiber を可縮とする。zeroStableHomFamily_extend と合わせ、元の商核四角形との全図式比較へ進む。現在の verdierNullHomFamilyIso に対角上恒等性は未主張。Sp の三件の不足 API と商実現比較への接続も確認する。
  元の比較の実右逆・相対余単位・strict Kan 実成分の本質的全射性は構成済み。正本の充満忠実性だけで元の比較の可逆性へ接続できる。
  span 側の逆順三角形と正本の充満忠実性が残る。新しい一般分数補題は Sp へ依頼する。

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
