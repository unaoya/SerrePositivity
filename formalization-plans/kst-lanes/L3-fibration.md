# K-F レーン：K-6 fibration 定理（L3）

> **v2 の位置づけ（2026-10-22 新設）**：foundations.md §6 の K-F。K-S• の L1（∞-S•、加法性、homotopy fiber）と Sp の K-5
> （抽象 Verdier 列、Sp 値局所化不変量）を読み取り専用で使う。(d) は 10-22 コーディネータ回答により、厳密 dg 入力 S 上の ν:S→StableInfinity と K:S→Sp を固定し、ν の像が K-5 VerdierDiagram となる dg Verdier 列を K が fiber 四角形へ送る相対形で述べる。
> 非連結化（K-7、BGT §9）は F1b・N の Ind・冪等完備化の後に別途。

## 引き継ぎ（2026-10-22）
### 現在地
- 工程 (a) 完了。K-5 の IsVerdierSequence の実核条件から包含の本質像を同定し、
  cofiber-W と商の可逆性、二対三・pushout・pullback・ホモトピーに対する拡大安定性を証明。
- 工程 (b)：全相対 S_n・W 判定・面退化・core 包含・商への射と核四角形を構成。
  W 辺・相対 cofiber 射影は trivial Kan。K-1 で全正有限反復の加法性へ接続済み。
- 有限 W 列の初期頂点・連続 cofiber の比較は、零長で厳密同型、全長・全正反復で局所化同型。
  全単体的有限積比較の自然同値は未主張。長い単体の貼合せと元の制限は inner anodyne／trivial Kan。
- 元の相対 S の対角と W 列の core S の対角を比較。全面・全退化・定数列・実押し出しを保持。
  元の核包含を実核への完全同値へ制限し、K-2 Segal 実現で元の核四角形の実現を homotopy pullback と証明。
- 相対 S の実 homotopy fiber と core S(D) の局所化同型 relativeSFibrationFiberIso を構成。
  同じ射影との合成は元の包含の実現射。商側は quotientSFibrationFiberIsoOfComparison で条件付き。
  必要な商実現射影の局所化同型性は未証明。無条件の K-6(b) 完成とは数えない。
- 既存の Ore・分母輸送・固定分数・可変終点 coslice・Kan 図式は保持。新設は Sp 正本へ依頼する。
  元の全 span 族の評価、全単体の被覆、W 反転、商への降下、同じ分数評価・比較の回収は構成済み。
  span 側の表現可能性と一般分数比較の同値性は未証明。tamme* の lax 専用仮定は流用しない。
- 元の商比較二胞体から実比較射を作り、底・恒等錐・相対頂点・指定成分の回収式を保持。
  全写像空間の比較と可縮な選択 fiber を使用。H⁰ の Verdier 普遍性による代用はない。
- native 表現の同じ pointedMap と指定 diagramIso の点作用を計算。指定逆成分を持つ pointed 復元射を構成。
  元の scaffold 埋め込みと universal・taut 両脚の制限を保持し、同じ相対三角から係数点の一致を回収。
- 豊穣実現の二重評価、oppositeRealizationIso と strict transport の反転比較の指定成分は同じ反転点を保つ。
  左解像の実頂点を同じ反転点に同定。候補→native→実分類の同じ指定成分で pointed 復元像を回収。
- cocartesian section→全 section の指定成分は Kan 置換単位上で元の包含の点を回収。
  実分類まで合成すると同じ恒等射評価点の pointed 復元像を回収し、包含後の評価も元の実評価と厳密一致。
- 切断の底変換実現・転置した共同図式・全単体上の同じ指定同型の二重評価を同定。
  元の pullback 切断の指定点は第一射影による同じ像へ移る。大域 straightening の底変換同型を制限すると
  元の全単体上の指定比較を回収。ここには Sp の localizationPre_fullyFaithful と既存の map_preimage を使用。
  任意の実底頂点では、その同じ零単体上の指定制限成分を HEq で回収。
- 実分類写像の底変換と対象図式の同じ成分を、元の共同底変換の二重評価に同定。
  元の大域制限を左右の切断比較と同じ逆切断比較に分解。第一射影像の点は、左右の指定比較を通じて
  同じ大域成分により同じ pullback 切断の点へ移る。左右の切断比較と復元比較の三角形の最終照合は未証明。
- 元の分類・表現同型と同じ逆成分を、初頂点上の指定比較へ Sp の前合成充満忠実性で回収。
  復元射の実 fiber 点をその同じ逆成分で計算。単体→under 切断の元の共同・実現比較は同じ制限像の点を保持し、curry・転置でも成分を保持。
- 元の左右の底変換成分は、それぞれ像の単体・pullback 対象での同じ初頂点切断比較と HEq。
  元の under 実現比較全体と共同 under 比較の指定成分は厳密一致。初頂点切断比較と実 under 制限成分へ分解し、同じ切断点の実制限像を回収。
- 元の初頂点 pullback 比較の指定逆成分は、同じ厳密持ち上げ点を回収。初頂点制限全体の同じ指定成分は
  元の under 制限と厳密持ち上げの合成 firstVertexStrictSectionMap の点像を回収し、実対象図式の初頂点同型とも HEq。
  持ち上げ切断の恒等射評価を第一射影で読むと、元の単体切断の初頂点を厳密に回収する。
- 工程 (c)：中央・右項の π が k 未満で消えると、左 fiber の同じ消滅 ⇔ πₖ 射影全射を K-5 の実長完全列で証明。
  中央 πⱼ=0 なら右 πⱼ₊₁／射影の像 ≃ 左 fiber の πⱼ。代表元では元の接続射。零次余核の障害を明示。
- 固定 dg K の実頂点・実辺の整数 π 作用を、同じ BF スペクトル射の作用と可換に比較。
  実 K 辺の πⱼ 全射性 ⇔ 同じ S• BF 射の πⱼ 全射性を証明。零次にも適用でき、K の局所化性は仮定しない。
- 工程 (d) はユーザーのコーディネータ回答に従う相対形：同じ厳密 dg 入力 S 上の ν:S→StableInfinity、K:S→Sp。
  ν の像が K-5 VerdierDiagram となる D β3 の dg Verdier 列に (b)(c) を適用し、固定 S• 比較で K へ戻す。
  K-S• へ依頼した固定入力は ν、K、頂点・辺での S• スペクトル同定の三点。一般 StableCategory 上の K は依頼しない。
- 工程 (e)：N の冪等完備化の普遍性・安定性・完全性と BGT §9 の入力境界を本文に整理。K-7 本体は別工程。
- 対象 10456 jobs・監査 395 モジュール 2260 宣言・全体 25168 jobs が成功。標準三公理のみ。
  宣言型の ModelCategory・禁止ソース・diff 検査も成功。所有 import 閉包 6663 モジュールは EInfinity を含まない。
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
- leftStraighteningRepresentationIso_inv_value、pointedLeftReconstruction_restriction_pointHom、
  transportUnderJointComponentIso_pointHom、transportUnderJointComponentIso_heq_realizationMap。
- straighteningBaseChangeRightChart_heq_firstVertex、straighteningBaseChangeLeftChart_heq_firstVertex、
  straighteningUnderRealizationChart_eq_joint、straighteningUnderRealizationChart_pointHom。
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
- なし（底変換逆成分・初頂点 pullback 比較・全制限比較・厳密切断と恒等射評価・実図式成分の5モジュール、集約・監査・本計画）。
### 既知の問題
- 一般分数比較の同値性、span 側の普遍性、商実現比較、具体的商射の π₀ 全射性、相対 Sp 値 K-6 は未完。
- 現在の条件付き fiber 同型や一般の群判定を、具体的 K の局所化性の証明とは数えない。
### 次の一手
- Sp の一般分数比較同値の公開を確認する。固定 dg K の実 π 比較は構成済みだが、具体的商射の π₀ 全射性は未証明。
  独立に、元の初頂点制限成分で回収した同じ厳密切断点を opposite 成分へ送り、元の native 表現制限の点と照合して pointed 復元射の指定点へ移す。

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
