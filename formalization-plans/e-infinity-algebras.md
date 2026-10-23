# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：2026-10-23 コーディネータ停止指示による保存区切り。P-1 g は未完了。
  P_Σ の全部分 quasicategory・充満忠実な Yoneda 因子化・sifted 余極限閉性・sifted 密度生成は完了。
  sifted 保存関手からの元の Yoneda 制限そのものの全充満忠実性も完了。
  小さい sifted 余極限を持つ標的への左 Kan 延長存在、元の指定単位の可逆性・全関手同型による回収、全密度余錐像の余極限性まで保存済み。
  前層宇宙変更の全関手・評価／制限との厳密な可換性・小 coherent 余極限保存、全 Hom 錐による余極限判定を保存済み。
  全自然変換空間族と持ち上げた延長の全 Hom 族が、同じ元の Yoneda に沿う実際の右 Kan 延長であることも保存済み。
  前回保存 28b67dcb7 は共同 Yoneda Hom・共同評価の実 left fibration と元の全 twisted arrow からの二射まで。二射の延長・cofinality は未証明。
  **今回の区切り**：充満忠実な元の関手による twisted arrow・共同 Hom・全 Yoneda 制限の自然同型、左右 Kan 制限同型の持ち上げ、全余錐の形状置換の7モジュール21宣言。
  `mapUliftCocone_isColimit_of_quasicategoryShapes` は、小さい quasicategory 添字での保存を任意の小さい添字へ戻す。元の全余錐を厳密な制限で保持する。
  大域 Yoneda 評価・両右 Kan 族の比較本体は未検証で、下記7ファイルを集約・監査から外した。
  N-1 完了（F1b の任意 coherent 余極限定理を使用）。N の部分余極限経路は打ち切り。
  N-2（γ4）は adbdbd14c・963d9e3cf で完了、再監査不要。固定 SM7・豊穣随伴の元の Hom 同型・合成互換を明示した simplicial Quillen 随伴が対象。
  N-3 の指定 Tot・hG・fiber 適用は Sp の既存定理で達成。Sp 全体の安定性の完成とは扱わない。
  F2N-3 は F1b の a7 実証拠の受け渡しだけ残す。F2N-4(a)〜(e)（冪等完備化の普遍性・安定性・compact Ind 比較）は完了。
  N-4 の Bousfield 局所化の存在は P 所有。局所置換が与えられた場合の反射までが N の保存済み範囲。
- **残り**（依存順）：
  1. F1b の a7 公開後、`IndFiniteLimitExchangeInput.exchange` へ実証拠を渡す差し替えを1コミットで保存。HTT 5.3.4、提供後の一工程。
  2. 下記7ファイルを検証・修正し、大域 Yoneda 評価と両右 Kan 族の全自然比較を閉じる。HTT 5.5.8.14〜15、数時間〜（再ビルド時間を除く暫定）。
  3. 元の左 Kan 延長の任意小 sifted 余極限保存、元の制限の本質的全射性・全関手 ∞ 圏の同値。
  4. simplicial Ind 表示、filtered／geometric realization 版、Yoneda の有限余積保存と全余極限保存判定。HTT 5.5.8.14〜15(2)(3)、2〜4 合計30〜80時間（暫定）。
- **主要宣言**（型・全一覧は Lean と各集約・監査が正本）：
  N：`quillenCfDerivedAdjunctionWithComparisons_exists`、`sigmaPresheaf_siftedPresentation`、`sigmaPresheaf_sifted_induction`、
  `sigma_exists_densityLeftKanExtension_with_recovery`、`sigmaSiftedContinuousRestriction_isFullyFaithful`、`isColimitCone_iff_fullHomCone`、
  `presheafUniverseDiagram`、`presheafHomWeightDiagram`、`sigmaUniverseInclusion_isLeftKanExtension`、
  `sigmaHomWeightFamily_isRightKanExtension`、`sigmaLiftedHomFamily_isRightKanExtension`、`sigmaHomWeightFamily_restrictionIso`、
  `sigmaLiftedHomFamily_restrictionIso`、`homWeightEvaluationFamily_liftedIso`。
  今回：`twistedHomFunctorMap`、`twistedArrowFunctorComparison_isPrecompositionEquivalence`、`homInfinityJoint_fullyFaithfulIso`、
  `yonedaInfinityMap_fullyFaithfulRestrictionIso`、`leftKanReflRestrictionIso`、`rightKanReflRestrictionIso`、
  `isColimitCone_iff_restrict_mono_precomposition`、`exists_coconeExtension_of_mono_precomposition`、`mapUliftCocone_isColimit_of_quasicategoryShapes`。
  F2.Compact：`indYoneda_isKappaCompact`、`IsKappaCompact.retract_of_colimit`、`compactIndEquivalence`、`compactIndOmegaEquivalence`。
  F2.Idempotent：`IsIdempotentCompletion.pre_isQCatEquivalence`、`IsIdempotentCompletion.isStable`、`idem_isStable`。
- **依存と提供**：F1・F1B・F2/Ind・F2 集約・P（`F2/Presentable/`）は読み取り専用。`infinity-core-F2.md` も変更しない。
  accessible／presentable 定義は P の公開宣言を待つか入力にする。局所化の存在は P の担当。
  N 所有は `HomotopyLimits/`・既存 N 集約／監査、F2/Compact・F2/Idempotent と各独立集約／監査、本 N 節だけ。README は規約だけ。
- **未コミット**：以下はすべて `SerrePositivity/InfinityCategories/HomotopyLimits/` の `.lean`。未検証の作業中ファイルとして保持し、集約・監査には接続しない。
  `YonedaHomWeightColimits`：元の Yoneda Hom 係数関手の小 coherent 余極限保存、未検証。
  `PresheafElementsLeftKan`：小さい元の圏と全前層の左 Kan 添字・密度全余錐の比較、未検証。
  `PresheafDensityLeftKan`：全前層密度から左 Kan 条件を導く証明、未検証。最後に局所証拠 hcan を明示する形へ整理。
  `YonedaWeightLeftKan`：両関手の左 Kan 条件・制限同型・`yonedaHomWeightDiagram_universeIso`、未検証。
  `YonedaWeightFamilyComparison`：全係数への制限・転置による `yonedaHomWeightFamily_evaluationIso`、未検証。
  `SigmaHomWeightComparison`：両右 Kan 族の制限比較と `sigmaHomWeightFamily_liftedIso`、未検証。
  `PresheafUniverseArbitraryColimits`：検証済みの形状還元を前層宇宙変更へ適用、未検証。
- **既知の問題**：R の F1/PullbackFiber 一時変更は取消済み。所有 import 閉包に他レーン未保存変更がないことを確認して保存する。
  旧未検証対象 session93517 は停止準備で終了コード143にして終了。重複実行しない。新しいチャットで未検証対象を改めてビルドする。
  停止区切りの7対象4272 jobs、N 集約8634 jobs、全5529宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理なし。監査時の所有 import 閉包4990ファイルの SHA は不変。
  compact 独立集約7354 jobs・273宣言、冪等完備化独立集約6793 jobs・609宣言の既存監査は終了コード0、標準三公理のみ。
  `Inputs/Homotopy/KanQuillen.lean` は禁止 import。主経路に `ModelCategory SSet` を仮定しない。新しい sorry・公理・資源上限引き上げ・警告抑制は禁止。
  元の全図式・指定単位・全パラメータ自然性を保持し、点ごとの同値・未証明の存在入力で完成扱いしない。規約は `foundations.md` §8。
- **次の一手**：新しいチャットでは foundations.md §8 と本節を読む。N-2 を再監査せず、P-1 g を再開する。
  最初に `lake build SerrePositivity.InfinityCategories.HomotopyLimits.SigmaHomWeightComparison SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseArbitraryColimits` を実行し、上記7ファイルを検証・修正。
  両対象が通ってから集約・監査へ接続し、N 集約ビルド→全公理監査→所有分だけ保存。未検証のまま `/tmp/n-faithful-density-prepare.py` を実行して再接続しない。
  その後、元の任意小 sifted 図式の指定余錐像の保存へ進む。元の P_Σ 包含の余極限保存と前層宇宙変更の形状還元を使い、全 Hom 比較で延長の保存性を判定する。
  原典：[HTT §5.1.4・§5.3・5.5.8.14〜15](https://www.math.ias.edu/~lurie/papers/HTT.pdf)、[HA 1.1.3.7](https://www.math.ias.edu/~lurie/papers/HA.pdf)（既に本文照合済み）。

### E2a（E2 レーン停止時引き継ぎ、2026-10-23）

- **現在地**：E2a-0〜5 は完了。任意可換環上の実 E・augmentation・AW Hopf、TR と区間切断による N_*(Δ¹) の E 余代数区間、任意始域の acyclicity を含む転送モデル構造・右 Quillen U・全対象 fibrant を提供。
  通常の導来極限・底の比較、関手的 Kan Map^h・局所化 Hom 比較も完了。E2b の実 DK 豊穣圏と既存 CAlg_R の quasicategory 性は完成。
  γ2 d は26e1450c5：DK 1980b Prop.2.2・2.3 の全自由積分解を実 hammock へ移送し、左右比較射自身の弱同値性、既存 Map^h との全高次比較・相対自然性・合成・π₀整合まで完成。再実装しない。
  γ2 e はd0f4d40f0：元の実屋根・次数比較の cofinal 性、全 coslice prism と右 Kan 単位を使い、実 hammock の局所化普遍性と既存 CAlg_R の全関手圏の前合成同値まで完成。再実装しない。
  実 U : CAlg_R A → derivedInfinityCategory A はbcb7c31ac。元の通常忘却との全源比較、各値の擬同型比較を保持。元の代数・底の複体に cofibrancy を要求しない。
  離散入力の全源比較163ea2ef1、既存 D(R) の離散埋め込みとの全比較a7bb3e49c、零次 E 模型・Com 降下bba3bdd16、標準 H⁰ 同型0d5863b91、離散対象の両包含4014b618bは完成。
  自由忘却の実弱 Hom span は0e5b0d5d1。実導来単位・comma 候補はdcdcfc5da。正規化鎖の実 Reedy cofibrancy、tensor/K-projective と既存 D(R) への実弱 Hom span はe60467f07まで完成。
  元の要素圏上の二重 cone・全 slice prism・通常 augmentation 比較、全 HA と実 Δ²⊗K 三角形は完成。全作用素自然性7b84c975e、全三辺1b32cd7a8、全 h Fun の評価三角形2eaf97fe4、元の derived pinched と roof の全族比較ee6e3d6db。
  **今回の保存単位 fee845d09**：BarrattEccles/FreeProbeElementColumn.lean と FreeProbeElementColumnProperties.lean の9公開宣言。元の正規化 Hom の同じ要素圏上の自由 E∞ frame の列、augmentation・評価自然変換、元の随伴単位による両比較公式、全 augmentation・全列射の弱同値性、各対象の cofibrancy。標準単位誘導射自身の弱同値性は未証明。
- **残り**（依存順、再開後の粗い見積もり）：
  1. 同じ列を cofibrant 相対圏へ持ち上げ、元の LeftRoof/SameUniverse で CAlg_R の全 pinched 族へ送る。既存の全族比較と接続して標準単位比較自身の弱同値性を証明。HTT §5.2.4 の写像空間判定への入力、6〜16時間。
  2. 同じ単位 comma 候補の実始対象性から全 ∞ 随伴を構成し、同じ U の任意 coherent ∞ 極限保存へ接続。HTT §5.2.4、6〜14時間。点ごとの Hom 同値だけでは完成扱いしない。
  3. G1′：BS の界面を既存 CAlg_R で述べ直し、上の実 U・離散比較・極限保存を代入。4〜12時間。
- **主要宣言**（namespace は SerrePositivity.EInfinity、型の正本は Lean）：
  `BarrattEccles.operad`、`BarrattEccles.augmentation`、`BarrattEccles.hopf`、`Operad.CoalgebraInterval`、`TableReduction.operadMap`、`IntervalCuts.coalgebraInterval`。
  `BarrattEccles.modelCategory`、`BarrattEccles.forget_isRightQuillen`、`BarrattEccles.isFibrant`、`BarrattEccles.mappingSpace`、`BarrattEccles.mappingSpacePiZeroEquiv`。
  `BarrattEccles.localizedFramedLimit_isRightDerivedFunctor`、`ComplexLimits.localizedFramedLimit_isRightDerivedFunctor`、`BarrattEccles.carrierFramedLimitComparisonNatIso`。
  `BarrattEccles.CAlg_R`、`BarrattEccles.cAlgLocalizationSource_isLocalization`、`BarrattEccles.cAlgLocalizationPrecomposition_isQCatEquivalence`。
  `BarrattEccles.cAlgForgetDerived`、`BarrattEccles.cAlgForgetDerived_sourceIso`、`BarrattEccles.cAlgForgetDerived_valueVertexIso`、`BarrattEccles.cAlgUnderlyingDisc_iff_discreteUnder`。
  `BarrattEccles.discreteCAlgEmbedding`、`BarrattEccles.discreteCAlgUnderEmbedding_forgetIso`、`BarrattEccles.algebraCAlgSource_underlyingDerivedIso`。
  `BarrattEccles.freeProbeDerivedUnit`、`BarrattEccles.derivedFreeProbeUnitEdge`、`BarrattEccles.derivedFreeProbeUnitCommaVertex`、`BarrattEccles.derivedFreeProbeUnitIntervalMap_family`。
  `BarrattEccles.freeDerivedHomToUnderlying_homotopyEquivalence`、`BarrattEccles.freeProbeDerivedUnitNormalizedHom_family`。
  `ComplexLimits.normalizedOrdinaryDerivedHomMap_homotopyEquivalence`、`ComplexLimits.normalizedOrdinaryDerivedHomMap_family`。
  `ComplexLimits.normalizedTensorTriangleFamily_comp`、`ComplexLimits.normalizedTensorDerivedPinchedFamily_eq_roof`、`ComplexLimits.normalizedTensorDerivedPinchedFamily_arrow`、`ComplexLimits.pinchedFamilyPostcomp_arrow`。
  `BarrattEccles.freeProbeElementIndex`、`BarrattEccles.freeProbeElementColumn`、`BarrattEccles.freeProbeElementColumnAugmentation`、`BarrattEccles.freeProbeElementColumnEvaluation`。
  `BarrattEccles.freeProbeElementColumnEvaluation_unit`、`BarrattEccles.freeProbeElementColumnAugmentation_unit`、`BarrattEccles.freeProbeElementColumnAugmentation_weak`、`BarrattEccles.freeProbeElementColumn_map_weak`、`BarrattEccles.freeProbeElementColumn_cofibrant`。
- **依存と提供**：HomotopicalAlgebra の転送・Reedy・HomotopyFunctionComplex、DifferentialGraded、Spectra/SymmetricSequence、CategoryTheory/Simplex を読み取り専用で使用。
  ComonadResolutionOperators・Presentation・SimplicialResolution、Rectification/HomotopyFunctionComplex/LiftSpace、KST の ExInfinityMonoidal・NerveOppositeIso を再利用。
  N の Coherent/Quasicategory・F1/CoherentVertices・CoherentNervePostcomposition・KanSourceReplacement、F1b の KanNerveLeftKanShapeIso・QuillenALeft・CofinalWeakEquivalence、F2 の filtered 弱同値保存を使用。
  E2a のモデル・通常右導来極限・Kan Map^h、実 CAlg_R と既存 D(R) への忘却射・離散比較を提供。所有は EInfinity/**・EInfinity.lean・scripts/audit_einfinity.lean。本節以外の共有計画を巻き込まない。
- **未コミット**：E2 所有のリポジトリ内コードは今回の保存単位までコミット済み。共有計画の他レーンの変更は保持し本節のみコミット。/tmp の試作は集約・監査に未接続。
  /tmp/e2-free-probe-cofibrant-column.lean は CofibrantAlgebra への4定義の試作、終了コード0。/tmp/e2-free-probe-relative-column.lean は Hom 宇宙 ULift も含む拡張の試作。v2 の完了状態は未確認なので成果扱いしない。再開時は正本の9宣言から必要分を再構成する。
- **既知の問題**：fee845d09 は対象ビルド6594 jobs・EInfinity 集約11055 jobs・全公理監査25780宣言・独立例9件が終了コード0、標準3公理のみ。必須9101項目は209個の noinline 配列、各128以下。7187モジュールの import 閉包に他レーンの未コミット依存0件、監査前後の全ソース digest一致。新規モジュールの警告・sorry・追加公理なし。対象ビルド・監査・独立例はすべて終了済み。資源上限変更なし。既存208必須配列の式・順序・run_cmd登録は保持。主経路に ModelCategory SSet・CharZero・元の対象の cofibrancy の入力仮定なし。
  モデル構造は局所選択し大域 instance を追加しない。Inputs/Homotopy/KanQuillen.lean の既存 sorry を import しない。他レーンの作業中依存が閉包に入ったら回避せず停止。
  LeftRoof.Precompose の旧入口は I : Type v・Category.{0} I。同じ宇宙の実圏には LeftRoof.Precompose.SameUniverse を使う。元の要素圏は Type(u+1)・Category.{u} なので、cofibrant 代数の Category.{u+1} と合わせるには ULiftHom.{u+1} を使い、objUp/objDown の宇宙 .{u+1,u+1} を明示する。対象だけの ULift は不要。
  集約 import 後の framedLimitProbeFunctor は複体側と代数側に同名がある。独立例では ComplexLimits.framedLimitProbeFunctor を明示する。必要なら型付き change と明示した始終域で推論を切る。型推論のために maxHeartbeats を上げない。
  Subcomplex は CompleteLattice のみ。有限分配は subcomplex_inf_finsetSup。Limits.Sigma.map は完全修飾。proof-only section 変数は include。
  既存 ThreeArrowPaddingSpan.toOuter_naturality_app のみ理由コメント付き局所 maxHeartbeats 800000。今回追加分は標準上限。監査の公開名抽出では namespace と名前付き section を区別し、必須配列を変更しない。
- **次の一手**：foundations.md §8、本節、上の2新規モジュールを読む。元の要素圏上の列を CofibrantAlgebraRelativeInput の cofibrant 相対圏へ持ち上げる小モジュールを作る。各対象の証明は freeProbeElementColumn_cofibrant、全弱射は freeProbeElementColumn_map_weak、左脚は freeProbeElementColumnAugmentation_weak を使う。
  同じ nerve の全パラメータ K を保持して Hom 宇宙を合わせ、LeftRoof/SameUniverse の元の四列円柱を適用する。評価の単位公式と ee6e3d6db の全 roof 比較を、freeDerivedHomToUnderlying_homotopyEquivalence・freeProbeDerivedUnitNormalizedHom_family・derivedFreeProbeUnitIntervalMap_family に接続し、標準単位比較自身の弱同値性を示す。
  N の HomotopyLimits/CommaInitialAdjunction.lean の exists_qcatAdjunction_of_commaFiberInitial は同じ U の各 unitCommaFiber の実始対象から全 ∞ 随伴を構成。F1B/UnitCommaFiberExtension.lean の unitCommaFiber_isInitialVertex_iff は実境界延長の判定。既存 UnitCommaInitialFromMapping は全 F と単位二胞体を入力に取るため点ごとの候補へ直適用しない。
  全複体 nerve→既存 D(R) の局所化普遍性を先に構成する必要はない。別経路ならその普遍性は未提供であり、dg 加群の dg nerve の局所化で代用しない。γ4 の quillenCfDerivedAdjunctionWithComparisons_exists は固定 SM7・豊穣随伴入力を要求するが実 E∞ DK 模型には未供給。未証明の SM7 を仮定しない。
  今回はコーディネータの停止指示による区切り。このチャットでは続行せず、新チャットで上記から再開する。


## 0. 位置づけ

G1 の界面（perfectoid 化とその性質の束）を述べる場である CAlg_R を、
Ch(R) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏で実現する。
三段で進める。

| 段 | 内容 | 使い先 |
| --- | --- | --- |
| E2a（モデル圏まで） | オペラッド・Barratt–Eccles・E∞-dg 代数・転送モデル構造・右 Quillen な忘却関手・homotopy function complex | 界面の欄を「Alg_E の homotopy 引き戻し」「homotopy 写像空間」で述べる。γ を待たずに G1 の CAlg 版へ昇格できる |
| E2b（∞ 圏化、γ） | Alg_E の cofibrant 対象の単体的豊穣化と coherent nerve、homotopy 極限 = ∞ 極限、Quillen 随伴 = ∞ 随伴 | 界面を Lurie の言葉（quasicategory の引き戻し）で述べる。K 理論の Sp と共有 |
| E2c（BS の続き用） | 余単体的 E∞-dg 代数の Tot と余単体的可換環への E∞ 作用（Berger–Fresse）、単体的可換環のモデル圏と多項式解像度 | BS §4・§7・§8 の構成 |

E1（∞ オペラッド）は採らない。後で HA の定理を文字どおり引用したくなった場合に、
E2b ≃ E1 の比較（HA 4.5.4.7 型の rectification）を任意項目として検討する。

## 1. 既存資産

- `HomotopicalAlgebra/`：Mathlib `ModelCategory` 上の Quillen 随伴（H1）、Under（H2）、
  転送（`Transfer/Recognition.lean`：生成類から Mathlib の `ModelCategory` を構成、acyclicity は明示仮定；
  `Transfer/Right.lean`：右随伴が fibration と弱同値を作る転送）、Smith の定理、
  Bousfield 局所化、Reedy、`HomotopyFunctionComplex/`（frame による導来写像空間）、
  `Monoidal/`（モノイダルモデル圏、monoid axiom）。
- `Spectra/SymmetricSequence/`：対称列と Day 畳み込み（オペラッドの合成積の素材）。
- `DifferentialGraded/Complexes/Cells.lean`：`complexSphere`・`complexDisk`（射影モデル構造の生成 cofibration）。
- `InfinityCategories/Derived/`：semifree の閉性（cone・fiber・直和・テンソル・底変更）。
- Mathlib：`SmallObject`、`CategoryWithCofibrations/Fibrations/WeakEquivalences`、`ModelCategory`。
- 未整備：Ch(A) の非有界射影モデル構造（Mathlib は `CochainComplex.Plus` の injective のみ）、
  オペラッド、対称群作用つき複体。

## 2. E2a の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| E2a-0 | Ch(A) の非有界射影モデル構造：弱同値 = 擬同型、fibration = 各次数全射、生成 cofibration `complexSphere (n+1) → complexDisk n`、生成 trivial cofibration `0 → complexDisk n`。`Transfer/Recognition.lean` で構成 | Hovey, Model Categories 2.3.11 |
| E2a-1 | Ch(A) 上の対称オペラッド：各 arity n の複体 P(n) と Σ_n 右作用、合成、単位。代数、代数の射、自由代数 Sym_P（⊕ (P(n) ⊗ A^{⊗n})_{Σ_n}）、自由 ⊣ 忘却 | Loday–Vallette、Berger–Moerdijk 2003 §1 |
| E2a-2 | Barratt–Eccles オペラッド E：EΣ_n（Σ_n の translation 亜群の nerve）の正規化鎖。各 arity が可縮、Σ-cofibrant（各 E(n) が Σ_n 上自由な次数ごとの基底を持つ）、E → Com | Barratt–Eccles 1974、Berger–Fresse 2004 §1 |
| E2a-3 | Alg_E の完全な転送モデル構造：弱同値・fibration は忘却で作る。AW 対角による E の Hopf 構造と E-coalgebra 区間の抽象界面から全代数の functorial path object を構成し、fibrations.llp ⊆ 弱同値、J-cell acyclicity、`Transfer.Right.rightTransfer` の適用を先に証明。TR : E → χ と区間切断作用で N_*(Δ¹) を界面に代入する。始域の cofibrancy は追加しない | Berger–Moerdijk 2003 命題 4.1・§4.6.3、Berger–Fresse 2004 §3.1（TR は §1.3）。Hinich 4.1.1 は使用しない（正標数で E は Σ-split でない） |
| E2a-4 | U : Alg_E → Ch(A) は右 Quillen、全対象 fibrant、homotopy 引き戻し・homotopy 極限は底で計算。E 代数の H⁰ が可換環であること、離散可換代数は E 代数（E → Com 経由） | 同上 |
| E2a-5 | homotopy function complex Map^h(A, B)（`HomotopyFunctionComplex/` の frame を Alg_E に適用）、π₀ Map^h = Ho(Alg_E) の Hom | Hovey §5、Dwyer–Kan |

## 3. E2b（γ）の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| γ1 | 局所 Kan な単体的圏の coherent nerve は quasicategory（Mathlib `SimplicialNerve` に対して） | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| γ2 | Alg_E の cofibrant 対象の単体的豊穣化（Hopf オペラッド E による B ⊗ N^*(Δ^•) 型、または Dwyer–Kan 単体的局所化）と CAlg_R := N^hc | Berger–Moerdijk 2006、Hinich、Dwyer–Kan |
| γ3 | homotopy 極限 = ∞ 極限、右 Quillen ⇒ ∞ 極限保存、Quillen 随伴 ⇒ ∞ 随伴 | HTT 4.2.4.1、5.2.4.6 |

γ2 の単体的豊穣化が E2b の最大のリスクである。E2a の完了時点で方式を決める。

## 4. 受入基準と記録

dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。
配置は `SerrePositivity/EInfinity/`（E2a）、namespace `SerrePositivity.EInfinity`。
集約ファイルをルートに 1 行で追加する。既存の `HomotopicalAlgebra/`・`Spectra/` は編集せず、
必要な一般補題は新規ファイルに置く。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/e-infinity-algebras-log.md](archive/e-infinity-algebras-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
