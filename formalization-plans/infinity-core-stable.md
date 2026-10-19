# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-19）

### 現在地

- S1〜S7（D7）完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）、完全関手の CommShift・三角性を公開済み。
- D(S) の実零対象・全 fiber/cofiber・cospan の極限と span の余極限を構成。実境界の Q・A の二未知 cochain と微分式から coslice を充填し、cofiber の普遍性を証明済み。
- fiber/cofiber 比較の二脚・対角・ホモトピーと同値性、実 slice/coslice 比較辺を照合。同じ四角形の関手同型輸送から任意四角形の双カルテジアン判定と `derivedInfinityCategory_isStable` を証明済み。
- 通常の h D(S) と二切断の D3 を接続。実 suspension と複体シフトの自然同型・全整数 CommShift・実接続射の符号を照合し、標準 cofiber 列の D3 像を Mathlib の cone 三角形と同定済み。
- 全 distinguished triangle の標準 cofiber 表示から保存・反映・逆関手の三角性を証明。`derivedStableHomotopyEquivalenceIsTriangulated` は単位・余単位のシフト整合性も持つ。通常の導来圏から三角構造を引き戻して済ませていない。 D7 の入口：`Derived/StableTriangulatedEquivalence.lean`、`Derived/StableHomotopyTriangulated.lean`、`Derived/StandardCofiberTriangleImage.lean`。
- β3 の入口：`Derived/DGPretriangulatedStability.lean`・`Stable/UniverseStabilityDescent.lean`・`Stable/UniverseUniversalSquares.lean`。始・終・零対象と普遍錐の宇宙比較は `9c58fe60` に保存済み。今回の新規 12 モジュールで全標準ホーン、正方形の二三角形、span/cospan の錐と実四角形の同型を照合。引き戻し性・押し出し性を保存・反映し、全 fiber/cofiber と零角の判定を降下した。`IsDGPretriangulated A D` の下で元の `dgNerve A D` の安定性まで完成。最新の両集約は 6,327 jobs 成功。両公理監査成功：Derived 475 modules／4,872 宣言、Stable 745 modules／5,987 宣言。標準三公理のみ。
- β3 の入口 F1B/Localization と archive/L4-derived-geometry-log.md §26〜27 を読了。商の nerve・包含・ε による恒等辺の零ホモトピー、指定収縮付き dg 関手の延長と射影の厳密一致を構成済み。
- 収縮対象に入る／出る Hom の全次数の閉元の原始元、Hom 複体の恒等写像の零ホモトピーと非輪状性を証明済み。始点側の次数符号も検証済み。
- 実際の pinched Hom の全境界から真部分集合の成分を回収し、削除右辺の閉性・最上位の原始元による置換で全境界を厳密に充填。零次元も含む `IsContractibleKan` を両方向で証明済み。
- 全面を選ぶ `SelectedFaceAssembly` を全境界へ接続。全真部分集合の方程式から Bianchi で最上位の右辺の閉性を得て、始点の収縮元で解き、全ての面を厳密に保って充填。一次元は零辺で直接充填した。
- 収縮元を持つ任意の dg 対象の実始対象性・零対象性、商包含の指定対象の実零化を公開済み。零対象性から収縮元を回収する逆向きも証明し、任意 dg 関手の `PreservesZeroVertices` を証明済み。
- 商包含の指定充満部分圏上の制限は零対象の定値関手と、関手 ∞ 圏の可逆二胞体で比較済み。任意形状の零図式の比較とその一意性も Stable に公開した。
- 指定対象を実零頂点へ送る dg 関手から、収縮データを回収して商からの dg 関手へ延長し、nerve の射影との厳密な一致を証明済み。全 ∞ 関手圏の普遍性は未証明。この段階の零化・延長は K-flat 性を要求しない。
- 全面の一致から最上位の右辺を同定する補題、全射 Hom 準同型に沿う境界・目標原始元の同時持ち上げを構成。全面を保つ実相対充填を、一次元・零次元も含めて証明済み。
- 対象上全射・全 Hom 上次数ごと全射な準同型の dg 関手の nerve は `TrivialKanFibration`。逆写像・可逆二胞体を持つ `QCatEquivalence` まで公開済み。
- 具体的な cell 分解の第一添加と余極限から増大の各次数全射性を証明し、増大の nerve の明示的 ∞ 圏同値に適用済み。一般部品は DifferentialGraded の公開 API を使用し、KST の import は追加していない。
- 平坦分解後の path 商の nerve、元の nerve からの関手、屋根の比較同型を構成。証明済み K-flat 条件を供給し、元の指定対象の零化・指定部分圏上の定値零関手との可逆二胞体も構成済み。
- 任意の固定 Hom 複体の鎖写像に沿う pinched 線形単体・実写像空間の射を構成。全射準同型なら、零次元を含む全相対境界充填から `TrivialKanFibration` とホモトピー同値を証明済み。
- 実際の `pinchedHomMap (dgNerve.map F)` を端点の等式による同型込みで線形写像と同定。対象上全射性を外した充満忠実性、Hom 複体同型の場合、dg 充満部分圏の包含への適用を公開済み。
- 任意対象族のラベル付き dg 充満像と評価への厳密な分解を構成。dg Yoneda の全 Hom 複体同型から、同一宇宙の代表加群の模型との明示的 ∞ 圏同値を証明済み。
- 自明 Kan fibration の始域・基底の両方向に実 fiber/cofiber を構成し、一般の ∞ 圏同値の安定性の同値不変性と完全性を証明。Yoneda 模型と具体的 cell 分解の安定性の比較、実関手・逆関手の完全性へ適用済み。
- 閉零圏の零対象の恒等成分の消滅から、dg nerve の実零頂点性を証明。全 Hom end を持つ `dgModuleNerve` と具体的零加群の実零対象性を公開済み。
- dg 加群の cone から出る Hom の全次数線形同値・行列微分・二残差からの原始元を構成。実辺・二単体・cone 四角形の四頂点・四辺・零角を照合済み。
- 実 coslice 境界の最初の余錐から対象・三辺・ホモトピーを回収し、全 Hom end の型付き残差を定義。Bianchi から全脚・二三角形の微分条件を証明し、Q・A の二未知成分と微分式へ接続済み。
- 始点・脚・最上位も含む左右の全方程式を証明し、全面と共通面を保って実単体を貼合せ。`dgModuleConeCocone_isColimit`・`dgModuleConeSquare_isPushout` を全 coslice 境界の直接充填で証明済み。
- 任意の辺を閉加群射へ戻し、入力辺を厳密に保つ `dgModuleCofiberSquare`・`dgModuleNerve_cofiber_exists` を構成済み。
- shifted cone の射影・零ホモトピー・実四角形を構成。fiber の逆 Hom 座標の微分 `(da, f a − db)` と実射影・零ホモトピーへの一致、二残差からの原始元を証明済み。
- 実 slice 境界の六残差から二未知成分を定義。左右の全方程式・全面・共通面を保って直接充填。`dgModuleFiberCone_isLimit`・`dgModuleFiberSquare_isPullback`・`dgModuleNerve_fiber_exists` が揃った。
- M→fiber(inr f) と双対の cone(projection f)→N の両実比較の代数的同値性を証明。両方向を比較三単体・join・curry により実 slice/coslice 辺へ昇格し、端点・射影・span/cospan を照合。`dgModuleConeSquare_isPullback`・`dgModuleFiberSquare_isPushout` により標準 cone/fiber 四角形は双方とも双カルテジアン。各辺の双カルテジアンな選択と、実四角形の関手同型による選択独立性から任意の零角の fiber iff cofiber と `dgModuleNerve_isStable` を証明済み。元の nerve の対象宇宙だけを上げた `dgYonedaModuleNerve` を安定な全加群 nerve への実写像として構成し、単体・頂点での作用と実写像空間での充満忠実性まで照合済み。K(D) の同型で閉じた三角的対象条件の零・全整数シフト・cone・fiber の閉性から、条件付き全加群の実 nerve の安定性を証明。表現可能対象の isoClosure による `IsDGPretriangulated` の下で `dgHomotopyRepresentableNerve_isStable` が完成。共通宇宙の元の dg 圏との明示的同値と両方向の完全性、元の nerve の ULift の安定性まで接続済み。元の小さい宇宙への安定性の降下も完成。実四角形の全写像の全単射、頂点・右辺・底辺の一致、引き戻し性・押し出し性の保存・反映から `fiberSquareOfULift`・`cofiberSquareOfULift` を構成。`isStable_of_ulift` と `dgNerve_isStable_of_pretriangulated` を公開した。

### 残り（依存順、時間は推定）

- β3：Drinfeld 商の dg nerve の局所化普遍性、安定性、完全商関手、Verdier 列。Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。1〜2 万行、複数日。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b を読み取り専用で待つ。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`、`suspensionEquivalence`、`pretriangulated_ho`、`isTriangulated_ho`、`exactFunctor_isTriangulated`。
- `derivedInfinityCategory_hasZeroVertex`、`derivedInfinityCategory_fiber_exists`、`derivedInfinityCategory_cofiber_exists`。
- `cofiberBoundaryLiftQ`、`cofiberBoundaryLiftA`、`cofiberBoundaryLiftQ_differential`、`cofiberBoundaryLiftA_differential`。
- `standardCofiberCocone_isColimit`、`cofiberFiberLift_homotopyEquivalence`、`fiberCofiberDesc_homotopyEquivalence`。
- `derived_isPullbackSquare_iff_isPushoutSquare`、`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyBridge`、`derivedStableHomotopyEquivalence`、`derivedHomotopyHom_chainMap_surjective`。
- `derivedSuspensionShiftIso`、`derivedStableHomotopyEquivalenceCommShift`、`derivedStableHomotopyEquivalenceCommShift_one`。
- `semifreeCofiberConnectingToSuspension`、`derivedSemifreeCofiberConnecting_shift`、`derivedCofiberTriangle_mor₃`。
- `derivedStandardCofiberTriangleImageIso`、`derivedStandardCofiberTriangle_distinguished`。
- `derivedDistinguishedTriangle_standard_presentation`、`derivedStableHomotopyEquivalenceFunctorIsTriangulated`。
- `derivedStableHomotopyEquivalenceInverseCommShift`、`derivedStableHomotopyEquivalenceCommShiftCompatible`。
- `derivedStableHomotopyEquivalenceIsTriangulated`、`derivedStableHomotopyInverse_map_distinguished`。
- `dgNerve_contractingElement_id_homotopic_zero`、`dgNerve_contractingElement_id_eq_zeroEdge`。
- `dgQuotientNerve`、`dgQuotientNerveProjection`、`dgQuotientNerve_id_homotopic_zero`、`dgQuotientNerveExtension_projection`。
- `contractingTargetPrimitive_differential`、`contractingSourcePrimitive_differential`、`contractingTargetHomotopy`、`contractingSourceHomotopy`。
- `dgQuotientTargetPinchedHom_isContractibleKan`、`dgQuotientSourcePinchedHom_isContractibleKan`、`dgQuotientKilledVertex_isTerminal`。
- `dgNerve_isZeroVertex_iff_contractingElement`、`dgFunctorNerve_preservesZeroVertices`、`dgQuotientNerveProjection_kills`。
- `zeroDiagramFunctorIso`、`dgQuotientNullFunctorIsoZero`、`dgQuotient_exists_nerve_extension_of_zeroing`。
- `dgFunctor_relative_top_lift`、`dgFunctor_relative_simplex_lift`、`dgFunctor_relative_boundary_lift`。
- `dgNerve_map_trivialKanFibration_of_surjective_quasiIso`、`dgCellAugmentationNerve_trivialKanFibration`、`dgCellResolutionNerveEquivalence`。
- `resolvedDGQuotientNerve`、`resolvedDGQuotientFunctor`、`resolvedDGQuotientRoofIso`、`resolvedDGQuotient_localKFlat`。
- `pinchedHomChainMap_trivialKanFibration`、`pinchedHomChainMap_isSimplicialHomotopyEquivalence`、`dgFunctor_pinchedHomMap_eq`。
- `dgNerve_map_isFullyFaithful_of_surjective_quasiIso`、`dgNerve_map_isFullyFaithful_of_homIso`、`dgFullSubcategoryInclusionNerve_isFullyFaithful`。
- `dgYonedaRepresentableNerveEquivalence`、`representableDGYoneda_evaluation`、`IsQCatEquivalence.isStable_iff`、`isExactFunctor_of_isQCatEquivalence`。
- `dgYonedaRepresentableNerve_isStable_iff`、`dgCellResolutionNerve_isStable_iff`、`dgCellAugmentationNerve_isExactFunctor`。
- `dgNerve_isZeroVertex_of_closed_isZero`、`dgModuleNerveZeroVertex_isZero`、`dgModuleConeHomCoordinates`、`dgModuleConeDescElement_differential`。
- `dgModuleConeBoundaryRhsAB_differential`、`dgModuleConeBoundaryRhsAC_differential_zero`、`dgModuleConeBoundaryLiftQ_differential`、`dgModuleConeBoundaryLiftA_differential`。
- `dgModuleConeBoundaryLeftCandidate_suffix_equation`、`dgModuleConeBoundaryRightCandidate_suffix_equation`、`dgModuleConeBoundaryCandidate_common`。
- `dgModuleConeCocone_isColimit`、`dgModuleConeSquare_isPushout`、`dgModuleCofiberSquare`、`dgModuleNerve_cofiber_exists`。
- `dgModuleFiberCone_isLimit`、`dgModuleFiberSquare_isPullback`、`dgModuleFiberSquareOfMorphism`、`dgModuleNerve_fiber_exists`。
- `dgModuleCofiberFiberLift_isInvertible`、`dgModuleFiberCofiberDesc_isInvertible`、`dgModuleCofiberFiberComparisonSliceEdge_projection`、`dgModuleCofiberFiberComparisonSliceEdge_isInvertible`、`dgModuleConeSquare_isPullback`・`dgModuleFiberSquare_isPushout`・`dgModuleNerve_isStable`・`dgYonedaModuleNerve`・`dgYonedaModuleNerve_isFullyFaithful`・`dgModulePropertyNerve_isStable`・`dgHomotopyRepresentableNerve_isStable`・`dgRepleteYonedaNerveEquivalence`・`dgNerveULift_isStable_of_pretriangulated`・`uliftJoinIso`・`uliftSliceOverIso`・`uliftSliceUnderIso`。 `isTerminalVertex_iff_ulift`・`isInitialVertex_iff_ulift`・`hasZeroVertex_iff_ulift`・`isLimitCone_iff_ulift`・`isColimitCone_iff_ulift`・`hasLimit_iff_ulift`・`hasColimit_iff_ulift`。 `isPullbackSquare_iff_ulift`・`isPushoutSquare_iff_ulift`・`isStable_of_ulift`・`dgNerve_isStable_of_pretriangulated`。

### 依存と提供

- Core・F1・F1B・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。

### 未コミット

- 今回の所有ファイルだけを保存。自分の未コミットなし。他レーンの変更は取り込んでいない。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルドと両公理監査成功。主要宣言に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零対象性・整合的な制限の零化は完成。分解の nerve の同値と平坦商への関手は完成。全 ∞ 関手圏の普遍性、商の安定性、完全性と Verdier 列は未完。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β3：次の一工程は前三角 dg 圏の平坦商の前三角性と商関手の完全性。元の dg nerve の安定性は今回完成し、宇宙比較の再実装は不要。入口は `DGPretriangulatedStability`。`IsDGPretriangulated` は K(D) での表現可能加群の isoClosure の三角的閉性であり、∞ 安定性を仮定しない。`DGRepleteYonedaStability` が ULift の実 Yoneda 同値、`UniverseStabilityDescent` が元の実四角形による降下を供給。既存の DifferentialGraded/Quotient/DerivedComparisonEquivalence の `localQuotientTriaEquivalence` は局所 K-flat 下の tria(D)/tria(S) と tria(D/S) の実三角同値、`localQuotientTriaRepresentableIso` は代表対象の像を計算する。これは導来加群圏上の tria なので、K(D) のホモトピー表現可能性へ戻す際は半自由・cofibrant 条件と比較の充満忠実性を別途照合すること。具体的 cell 分解の augmentation に沿う前三角性の移送も必要。分解の nerve の安定性自体は既存の同値で得られるが、商へ前三角性を渡す部分と混同しない。平坦分解には `ResolvedDGQuotientNerve` と証明済み `resolvedDGQuotient_localKFlat` を使う。商の前三角性を入力へ追加しただけで β3 完了とはしない。全 ∞ 関手圏の局所化普遍性、Verdier 列、β5、β4 は未完。

作成日：2026-10-18。状態：S1〜S7（D7）完了。β3 に進む。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/StableTriangulatedEquivalence.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定、IsStable、実 suspension 由来の全整数シフト、標準 cofiber 三角形の像の同型、全 distinguished triangle の保存・反映、単位・余単位と整合する三角同値 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f を既提供とせず、S7 の coslice の直接充填で標準 cofiber の押し出し性を証明した。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。


## β3：Drinfeld 商と ∞ 圏的 Verdier 商

D7 の後に着手済み。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda の代表模型との同値、前三角 dg 圏の元の dg nerve の安定性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、同じ宇宙の標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明する。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏と安定な充満部分圏について、商の dg nerve の安定性、商関手の完全性、
  零化する完全関手への前合成の同値、Verdier 列を構成する（見積もり 1〜2 万行）。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

β3 の後。L4 §26 の dg 圏分解と既存の dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、α2b の Cat_∞ の極限・lax pullback の実装を待って接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
