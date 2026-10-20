# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-21）

### 現在地

- S1〜S7（D7）完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）、完全関手の全整数 CommShift・三角性を公開済み。
- D(S) の実境界から Q・A と二微分式を構成し、coslice の直接充填で cofiber の普遍性を証明。全 fiber/cofiber・有限極限余極限、任意四角形の双カルテジアン判定と安定性まで完成。
- 実 suspension・複体シフト・接続射の符号を照合し、標準 cofiber 三角形の D3 像を cone 三角形と同定。全 distinguished triangle の保存・反映、逆関手の三角性、単位・余単位のシフト整合性を持つ D3 の三角同値を公開済み。
- β3：F1B の局所化と L4 §26〜27 を読了。商の実零化、平坦分解の実 ∞ 圏同値、dg 加群・前三角 dg 圏・平坦分解後の商の実安定性、商関手の完全性と実分母の反転まで完成。
- 実 Verdier over 上の屋根対応・pinched Hom fiber・商側の両側 fibration を構成。固定商 Hom の商屋根全空間への包含の right cofinality・弱同値を証明。実屋根比較自体の left cofinality と弱ホモトピー同値性まで証明済み。境界固定の有限相対充填・prism・同時輸送は完成。
- 全次元の最後外ホーンから R・K を回収し、dR=0・dK=−最後辺∘R を証明。実 Hom cone の指定閉残差の原始元と Q・A の二未知解を双方向に接続。有限混合次元族に一つの追加実閉分母と全実充填を供給する。
- 全次数の over 単体と実 Verdier 部分圏内の閉始点細分を構成。零面保存、零固定・正番号非零の全順序写像との可換性、全正番号面・退化・共有面の厳密一致を証明。
- `TruncatedJoinConeData f N` と有限頂点からの N=0 の実初期値を構成。錐全体を一つの追加実閉分母で更新し、同じ apex・全面・全正番号退化条件を保つ操作まで完成。
- 次次数の零面 f σ と既存錐の正番号面から実境界写像を貼る。有限族を一つの分母後に同時充填し、その全面・共有面・実 apex を更新済み下次数錐へ厳密に一致させた。基本退化表示の標準錐の一致・全面保存・退化正規化も完成。`dgVerdierTruncatedConeSuccessor_nonempty` は次次数有限なら N+1 の錐を、`dgVerdierTruncatedConeData_nonempty` は各次数有限なら任意有限次数の錐を供給する。
- 次元上界までの切断写像の一意な全次数延長を標準 splitting から構成。切断錐の全順序写像への自然性、実 coslice への切断写像と射影の厳密一致、実 join 写像の左右制限・apex・全低次数単体との一致を証明。`dgVerdierFiniteJoinCone_nonempty` は任意の有限単体集合からの実分母図式に同じ部分圏内の実 join 錐を供給する。`dgVerdierOver_op_isFilteredInfinity` により実分母 over 圏の反転は filtered ∞ 圏。
- 任意の有限商屋根図式と指定元境界を、共通の実分母 fiber 上の厳密な相対問題へ還元。元境界を先に右持ち上げし、その比較像を全境界で固定して商全体を右持ち上げする。二輸送の終端・全底・境界全時刻の一致を証明。共通頂点を同じ実辺の閉分母へ戻し、元・商の pinched Hom 係数正方形と実屋根像を同定した。正次数の還元問題は一つの追加閉分母後に実充填と全境界付き輸送を持つ。二段階輸送も実合成三角形ごと相対構成し、任意の正次数標準単体境界の比較正方形に、元の全境界・全時刻で整合するホモトピー相対充填を供給した。屋根比較の弱同値判定は下記の一般有限対による方法で完成。
- 零次元と空族を含む全次数の有限セル族の同時係数充填を公開。相対骨格の一段更新で、一つの追加閉分母、次骨格の元係数写像、全体商写像、下骨格を全時刻固定する比較を同時に構成した。次骨格・各新セルの厳密な制限、商前合成の自然性・合成則、有限標的の骨格の有限段停止も証明済み。この状態の有限帰納と、一般有限対全体の係数充填まで完成。
- 一般有限係数対の比較を実商屋根へ移し、元・商の細分輸送との全境界・全時刻の一致を証明。相対輸送三角形と共通 fiber への還元を接続し、`dgActualRoofFinitePairs_nonempty` は任意の有限単体集合対 L⊂K の実屋根比較正方形に `RoofHomotopyRelativeFiller` を供給する。有限対の全時刻整合性を使う一般の cofinality 判定まで接続済み。
- 有限対充填から、終対象付き右ファイブレーションへの引き戻し内の有限図式の零ホモトピー span を構成。連続 Kan 置換の有限因子化で全境界を充填し、弱可縮性と Quillen A により left cofinality を証明。`dgRoofCorrespondenceMap_isWeakHomotopyEquivalence`、任意の Kan 標的への前合成の実ホモトピー同値、連続 Kan 置換後の圏同値を公開した。有限パラメータの写像空間の π₀ の全単射も別に証明済み。
- 任意の quasicategory 標的への反転関手 F と任意頂点 z について、実屋根射影の左右 fibration 性、恒等 fiber と Hom(Fx,z) の厳密な同型、固定 Hom 包含の right cofinality・弱同値を証明。標的 slice・実屋根の恒等則・合成則、固定 Hom との厳密な可換性を全次数で公開した。
- `DGInvertingHomDescent` は商の実 Hom 全体への実写像、元の Hom 作用との比較ホモトピー、選択によらないホモトピー一意性を持つ。標的の任意の後合成とのホモトピー自然性を証明。二段降下を可逆 path 置換で空間に束ね、`dgInvertingHomDescentSpace_isContractibleKan` により各対象対の全高次の選択空間が全境界を充填する。異なる対象対の合成との coherent な両立と全関手圏への組み立ては未完。
- 可縮な選択空間全体上の商 Hom 作用を `dgInvertingHomActionFamily` に束ね、元の Hom 作用への制限を `dgInvertingHomActionFamilyRestrictionIso` により一つの関手同型として比較した。各選択点の比較を別々に選ばず、パラメータの全単体で整合する比較を保持する。
- 実屋根頂点を指定端点の実辺 span と相互表示し、元の頂点を厳密に復元。実 Ore 細分の共通対角と二三角形に、合成分母・分子の二三角形を加え、任意の二実屋根頂点に合成データと実合成頂点を供給した。任意の反転関手の下で各屋根の実評価辺と評価三角形が存在し、任意の三評価辺は実合成三角形を持つ。これらを Hom 作用族の比較へ接続する全高次の整合性は未完。
- 指定評価三角形を任意標的の実屋根全空間内の辺へ戻し、その両端・実分母から恒等分母への底の辺・実射側の三角形全体を厳密に保持。商 Hom の任意有限図式の実屋根持ち上げと実比較ホモトピー、各指定頂点の実屋根表示と実比較辺を公開した。`dgInvertingHomActionFamilyRoofEvaluationIso` は商 Hom 作用の値と実屋根の評価値を、全降下選択空間上の一つの関手同型で比較する。
- 有限商 Hom ホモトピーを両端固定で実閉分母後に下降し、比較の両端を全時刻固定することを証明。全 Hom・実 pinched Hom の後合成の自然性、前後合成の交換、可逆な閉辺による後合成の実ホモトピー同値を公開。`dgFiniteOreRefinement_nonempty` は任意有限族の分子と指定右分母に、一つの合成実閉分母・実持ち上げ族・元の Hom 内の全ホモトピーを供給する。
- 標準 DK Hom の AW 合成を実 pinched Hom へ移し、全次元の単位則・結合律と全パラメータ族の結合律・前合成可換性を証明。`DGFiniteRoofOreData.compositeDiagram` は有限同時細分から合成分子の族と実屋根の候補図式を構成し、実分母射影の厳密な定値性を保持する。四三角形族は下記で構成。指定部分に沿う四族全体の同時延長と全関手圏への組み立ては未完。
- 全次元 AW 合成と指定実閉辺の前後合成の厳密一致を証明。標準閉定数を元の閉辺の pinched 頂点の定数族に同定し、全パラメータ族の前後合成まで接続した。二つの実ホモトピーの同時合成は指定部分の全時刻固定を保存する。`DGFiniteOreRefinement.compositionHomotopy` は元の円柱上の写像を厳密に保持して、実 Ore 比較を指定二実閉辺との AW 合成の比較へ直す。
- Dold–Kan 比較の厳密な片側逆を実 slice・区間族の表示へ接続し、F1 の合成 prism を実 dg target slice へ移した。零端は同じ実 AW 合成、一端は第二射、底の射影は第一射の区間族に厳密に一致する。`dgPinchedCompositionFamilyPrism` は任意のパラメータ族について同じ三境界を保持し、任意のパラメータ制限と全時刻で厳密に可換する。
- 実 Ore 比較と第二合成 prism を、同じ底の退化三角形を保って貼り、第一合成 prism と共通対角を持つ実内部二三角形族を構成。Leibniz 内部 Hom の inner fibration により、任意の指定部分の比較三角形と底三角形を同時に固定して延長できる。`dgFiniteRoofCompositionPrisms_exists` は任意有限実屋根二図式に、両入力への実輸送、合成候補、全底付きの内部二族・外部分母分子二族を供給する。
- 任意標的の実屋根全空間から固定 Hom への一つの実評価と、元の屋根から評価の恒等 fiber 包含への実ホモトピーを構成。終対象への底の全錐と全時刻の射影も保持する。Kan 標的への前合成を任意ホモトピーで比較し、`dgInvertingHomFamilyEvaluation_nonempty` はこの同じ全体評価を共有して、任意有限商 Hom 図式の実屋根表示・実比較ホモトピー・全降下選択空間上の一つの評価関手同型を供給する。
- 実 slice prism の全三境界をパラメータ関手圏へ移し、同じ共通対角を持つ四合成関係を証明。実閉辺の定数族を定値関手への像に同定し、反転条件から関手圏内の分母の可逆性を導いた。`dgInvertingFiniteRoofComposition_nonempty` は任意の有限二屋根図式と任意の quasicategory 標的への反転関手に、入力への二輸送・共通細分・四実 prism・三実 pinched Hom 評価族・関手圏内の実合成三角形を供給する。任意の pinched Hom 族と定値関手間の射を、実ホモトピーまで照合済み。任意パラメータへの共通細分の制限は二輸送と Ore 比較の全時刻・合成分母・合成分子・実合成候補を厳密に保持する。共有全体評価との比較と全関手への組み立ては未完。
- 任意の K・quasicategory X に対し、`Fun(K, X_/z)` から `Fun(K,X)_/const z` への実比較同値を、終対象への全切断と底への厳密な可換性付きで構成。普遍 slice 評価の実ホモトピー・恒等錐上の全時刻固定・全後合成の各成分を照合した。`roofFunctorSliceRepresentation_pinched_vertex_arrow` は、どの全切断を選んでも実 pinched Hom 族が元の同じ関手圏の射を表すことを証明する。評価方程式から元の実屋根内の族比較への復元と全関手への組み立ては未完。
- 任意の評価方程式から、指定分母の像を全時刻の底とする実 slice 比較を回収し、始点補正の実三角形を保持した。`dgInvertingRoofFamilyRealization_nonempty` は、元の閉分母から恒等分母への実細分辺と組にして、任意パラメータの実屋根内の比較を構成する。`dgPresentedFamilyEvaluationIso_nonempty` は表示の輸送も含め、指定した同じ実評価族を全降下選択空間上の商 Hom 作用族と一つの関手同型で比較する。商の実合成との照合と全関手への組み立ては未完。
- 商関手自身の任意標的屋根を実商屋根と、標準頂点の輸送・両射影・固定 Hom 包含ごと同定。指定した商内の三評価族を元の商 Hom 二族の実 AW 合成に実ホモトピーで照合し、実屋根の合成候補から同じ AW 合成への二比較と実三角形を構成した。`dgInvertingBinaryAction_comp`・`dgInvertingBinaryAction_triangle_nonempty` は、任意有限二商 Hom 族と任意反転標的について、三対象対の降下選択を独立に動かす任意共通パラメータ上の作用族の合成関係・実三角形を与える。`dgInvertingUnitActionIso`・`dgInvertingUnitAction_id` は任意パラメータの実恒等族の保存を全選択空間上で与える。指定部分の全高次境界を保持する相対整合性と実 ∞ 関手への組み立ては未完。
- `dgRelativeRoofEvaluation_nonempty` は任意単射上の実評価値・比較の全時刻を固定し、指定実分母の同じ全底上で評価を延長する。`dgClosedRoofEvaluationSpace_isContractibleKan` は同じ初期族と全底を持つ全実評価 prism の空間の全境界充填を与える。`dgClosedRoofUniversalFiberEvaluation` はその全空間上で、同じ全円柱・全底を保持する一つの普遍実評価を構成する。部分 prism を指定した全選択空間と全関手への組み立ては未完。
- 入口：D7 は `Derived/StableTriangulatedEquivalence.lean`。β3 は `Derived/DGVerdierConeRefinement.lean`・`Derived/TruncatedConeNextBoundary.lean`・`Derived/DGActualRoofHomotopyFillers.lean`・`Derived/RoofCompatibleTransportComposite.lean`・`Derived/DGActualRoofFiberReduction.lean`・`Derived/DGCoefficientFinitePairs.lean`・`Derived/DGActualRoofFinitePairs.lean`・`Derived/DGActualRoofWeakEquivalence.lean`。

### 残り（依存順、時間は推定）

- β3 完了（2026-10-21）：局所 K-flat 商と平坦分解後の商の全局所化、全零化完全関手 ∞ 圏の普遍性、実安定閉包の包含を左項とする Verdier 列まで証明・監査済み。次は β5。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b の提供済み lax pullback を読み取り専用で使う。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`・`suspensionEquivalence`・`pretriangulated_ho`・`isTriangulated_ho`・`exactFunctor_isTriangulated`。
- `cofiberBoundaryLiftQ_differential`・`cofiberBoundaryLiftA_differential`・`standardCofiberCocone_isColimit`・`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyEquivalenceCommShift`・`derivedStableHomotopyEquivalenceIsTriangulated`。
- `dgModuleNerve_isStable`・`dgRoofCorrespondenceMap`・`dgRoofCorrespondenceFiberIso`・`dgQuotientRoofCorrespondenceProjection_leftFibration`。
- `dgQuotientFixedHomRoofMap_isRightCofinal`・`dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_piZero_surjective`。
- `dgGeneralLastHornTopResidual_differential`・`dgGeneralLastHornConeResidual_closed`・`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary`。
- `dgVerdierTruncatedConeSuccessor_nonempty`・`dgVerdierTruncatedConeData_nonempty`。
- `dgVerdierFiniteJoinCone_nonempty`・`finiteSimplicialOpposite`・`dgVerdierOver_op_isFilteredInfinity`。
- `dgActualRoofFiberReduction_nonempty`・`dgActualRoofClosedCoefficient_square`・`dgActualRoofReducedFiller_exists`。
- `roofRelativeCompositionTriangle_exists`・`roofCompatibleTransportComposite_nonempty`・`RoofCompatibleTransportComposite.boundary`。
- `RoofHomotopyRelativeFiller`・`dgActualRoofHomotopyRelativeFiller_nonempty`。
- `dgQuotientFinite_exists_coefficientFillers`・`dgCoefficientSkeletalStep_nonempty`・`finiteRelativeSkeleton_exists_top`。
- `dgCoefficientSkeletalStage_nonempty`・`dgCoefficientFinitePairs_nonempty`・`dgClosedRoofFinitePairs_nonempty`・`dgActualRoofFinitePairs_nonempty`。
- `HasFiniteHomotopyRelativeFillers.isLeftCofinal`・`isWeaklyContractible_of_finiteNullSpans`。
- `dgRoofCorrespondenceMap_isLeftCofinal`・`dgRoofCorrespondenceMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_precompose_kan`。
- `dgInvertingFixedHomRoofMap_isRightCofinal`・`dgInvertingHomDescent_nonempty`・`DGInvertingHomDescent.homMap_restriction`。
- `dgInvertingHomMap_postcomp`・`dgInvertingHomDescentSpace_isContractibleKan`・`dgInvertingHomActionFamilyRestrictionIso`。
- `dgActualRoofVertexSpan_rightInverse`・`dgActualRoofComposition_nonempty`・`actualRoofEvaluation_compositionTriangle_nonempty`。
- `dgActualRoofEvaluationTargetEdge`・`dgQuotientHomFinite_actualRoofLift`・`dgInvertingHomActionFamilyRoofEvaluationIso`。
- `dgFiniteHomotopyDescent_nonempty`・`pinchedClosedPostcomposition_precomposition`・`dgFiniteOreRefinement_nonempty`・`dgFiniteRoofPresentation_nonempty`・`dgFiniteRoofOreData_nonempty`・`pinchedHomCompositionFamily_assoc`・`DGFiniteRoofOreData.compositeDiagram_projection`・`pinchedHomCompositionFamily_closed_post`・`pinchedHomCompositionHomotopy_fixed`・`DGFiniteOreRefinement.compositionHomotopy_h`。
- `dgCoherentHomComparison_slice`・`dgPinchedCompositionPrism_projection`・`dgPinchedCompositionFamilyPrism_precomp`。
- `homotopyCompositionRelativeOver_fixedLeft_exists`・`dgFiniteOreTrianglePrisms_relative_exists`・`dgFiniteRoofCompositionPrisms_exists`。
- `roofLeftFibration_terminalEvaluation_nonempty`・`dgInvertingHomActionFamilyEvaluationIso`・`dgInvertingHomFamilyEvaluation_nonempty`。
- `pinchedFamilyHom_eq_iff_homotopy`・`dgInvertingFamilyDenominator_isIso`・`dgInvertingFiniteRoofComposition_nonempty`・`dgFiniteRoofOreDataPrecomp_compositeDiagram`。
- `dgNerveOppositeIso`・`dgNerveOppositeIso_naturality`・`dgSemifreeContravariantHomInfinity`・`dgModuleHomSpaceInfinity`・`dgModuleHomSpaceValueEquivalence`・`dgSemifreeHomTargetInfinity`・`dgSemifreeHomSourceInfinity`・`dgMoritaAdjunctionInfinity`・`dgPerfectMoritaRightAdjointInclusionIso`・`dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita`・`dgPerfectExtensionInclusionIso`・`dgAlgebraPerfectInfinityCategory_isStable`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_morita`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso`・`dgModuleDerivedFunctor_isQCatEquivalence_of_classical`・`dgAlgebraExtensionInfinity_isExactFunctor`・`dgModuleDerivedFunctor_comparisonIso`・`dgModuleDerivedFunctor_id_iso`・`dgModuleDerivedFunctor_comp_iso`・`dgAlgebraDerivedInfinityCategory_isStable`・`dgModuleDerivedInfinityCategory_isStable`・`dgSemifreeToProjectiveNerve_isQCatEquivalence`・`dgQuotientNerveProjection_isLocalization`・`dgVerdierExactPrecomposition_isQCatEquivalence`・`dgStableClosureNerve_isStable`・`dgStableClosureInclusion_isExactFunctor`・`dgQuotient_isStableVerdierSequence`・`resolvedDGQuotientFunctor_isLocalization`・`resolvedDGVerdierExactPrecomposition_isQCatEquivalence`・`resolvedDGQuotient_isStableVerdierSequence`。

### 依存と提供

- Core・F1・F1B・F2・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。
- **Sp から D への判定補題要求（2026-10-21、未提供）**：[HA Cor. 1.4.2.27](https://www.math.ias.edu/~lurie/papers/HA.pdf) の (3) ⇒ (1) を F3 の定義で使いたい。正確な要求は、`X : SSet.{u}`、`[Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]`、実関手 `s : X ⟶ loopDiagrams X`、`hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X`、`hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)` から `IsStable X` を得る一般補題。s は実際の普遍 loop 四角形の全単体族であり、安定性を先取りする既存 loopFunctor の使用は避ける。有限余極限・cofiber の存在と任意 ZeroTriangle の fiber/cofiber 同値を結論として証明し、それらを追加仮定にしない。現存の isStable_of_finite_limits_colimits は有限余極限と全四角形の双カルテジアン判定も要求するので代用できない。Sp が自前で証明する場合は Spectra 配下に置き、Stable/ は編集せず後で D が取り込む。Sp への適用には有限極限の包装と実 loop 関手の同値性がなお必要で、要求の記載を証明済みとは数えない。

### 未コミット

- 今回保存：`DGNerveOppositeNaturality`・`DGNerveOppositeIso`・`DGNerveOppositeFunctor`・`DGSemifreeContravariantHomInfinity` の4モジュール。未保存：`DGModuleFunctorResolutionData`・`DGModuleFunctorResolutionHom` は個別ビルド済み。実入力・半自由出力分解・全 Hom の比較差・mapping cocone・全パラメータ複体からの指定二射と比較ホモトピーの実持ち上げまで構成した。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルド成功（9233 jobs）。公理監査は Derived 11702 宣言／1309 モジュール、Stable 12817／1579。許容三公理のみ。今回までの保存対象240新規モジュールは警告なし。Hom 降下・実合成・全選択空間の評価比較の主経路に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零化・平坦模型との比較、前三角性の cell 分解への反映、平坦分解後の商の実安定性と商関手の完全性は完成。局所 K-flat 商の全 ∞ 関手圏の局所化普遍性は完成。零化完全関手圏の普遍性・実安定閉包の Verdier 列まで完成。平坦分解後の元の Hom の平坦性を仮定しない局所化・全零化完全関手 ∞ 圏の同値・Verdier 列も統合・監査完了。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β5：D(A)・Perf(A) の実安定性・完全充満包含・graph tensor・Morita 不変性に加え、全二変数の空間値 Hom と同じ Hom 複体模型との比較、固定入力ごとの複体値 Hom を統合・監査済み。Morita tensor の同じ逆関手を全 h Fun 内の三角式付き右随伴へ昇格し、Perf→D との逆関手比較も完成。全濃度の反転符号と左右切断・削除の添字比較、実全成分の符号付き反転と厳密な二回復元は監査済み。実削除・切断合成、全内部点の微分項、有限和による全 HA 微分式、全単体の反転全単射まで統合・監査済み。全単体作用の自然性、`dgNerveOppositeIso`、dg 関手に関する厳密自然性、実反対 ∞ 圏からの反変 Hom も統合・監査済み。次は個別ビルド済みの出力分解の実 Hom 複体について、入力 Hom への射影の準同型性を、半自由始域による第二 Hom 写像の準同型性と mapping cocone の実計算から証明する。出力分解 dg 圏の合成・nerve 比較を構成し、一般の出力を半自由模型へ運ぶ。D(R) 値の二変数 Hom・一般 tensor–Hom 随伴・一般双加群・Perf の冪等完備性・β4 は残る。
- F1B の `Localization.lean` は定義、`ReflectiveLocalization.lean` は反射的な場合の証明。一般の右分数計算の普遍性は既提供ではない。実 Verdier 添字の余 filtered 性・実屋根の比較・元の固定 Hom との可換性を使い、任意の反転関手の coherent な延長と関手圏全体の充満忠実性・本質的全射性を証明する。各 Hom への延長だけを局所化普遍性としない。F1 の `TransportLocalizationAllBases.lean` は simplex transport の局所化を提供しているので、必要な表示の入口として確認する。
- 屋根の合成と両変数自然性が全高次の図式と整合することを保持する。厳密な閉分母の通常の添字圏を filtered と仮定しない。β3 は移送と Verdier 列まで完了。β5、β4 は未完。

作成日：2026-10-18。状態：S1〜S7（D7）・β3 完了。β5 に進む。
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

D7 の後に完了。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda 模型との同値、前三角 dg 圏と平坦分解後の商の実 dg nerve の安定性、商関手の完全性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、局所 K-flat な場合は同じ宇宙の任意 quasicategory 標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明済み。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏の平坦分解後の商の実安定性と商関手の完全性は完成。
  局所 K-flat 商と平坦分解後の商の零化完全関手 ∞ 圏の同値・実安定閉包の Verdier 列まで完成・監査済み。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

着手済み。非可換 `Mon (Complex R)` の D(A) の定義・実安定性まで完成。L4 §26 の dg 圏分解と dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、提供済みの α2b の Cat_∞ の極限・安定な lax pullback に接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
