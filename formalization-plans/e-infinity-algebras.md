# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  小さい底上の任意の coherent 空間値図式の余極限は `F2.hasColimit_coherentSpaceDiagram` を使用。
  入力は `B : SSet.{u}` と `F : (SSet.uliftFunctor.{u+1,u}).obj B ⟶ SpaceInfinity.{u}`。
  `F2.coherentDiagramTotalCocone_isColimit` は元の全空間余錐の native 余極限性。F2 集約・`infinity-core-F2.md` を正本として読み取り専用で使用する。
  **N の部分余極限経路は打ち切り。** 検証済みコードは保存済みだが、共通 path end 比較・無限骨格の接続や指定余錐の未証明の余極限性を継続しない。
  **進行中は N-2（γ4）。** 通常の随伴と整合する単体的 Hom 同型から、任意の小圏上の strict 表示の native 極限保存を証明済み。
  `K × − ⊣ Map(K,−)` の Hom 同型・零単体・anodyne Kan 置換を含む frame Hom の全次数の照合も完了。
  元の関手的因子分解を使う Quillen frame・標準導来 Hom の比較列は両変数に自然で、左右ともホモトピー同値。`ChosenQuillenDerivedHom` 等を再実装しない。
  固定 mono/anodyne 類による `FixedSimplicialPushoutProduct` から、cofibrant 始域・fibrant 終域の Hom の Kan 性と両変数の trivial Kan 射を証明。
  cf 対応圏の局所 Kan 性・coherent nerve の quasicategory 性・Δ¹ への inner fibration・両端 fiber と元の C/D の cf nerve の同型は完了。両同型の全空間への合成は元の両包含に厳密に一致。
  元の Q(RY)→RY と LX→R_D(LX) の随伴像から実際の左右の候補辺を構成。区間の 0→1 上の射影と、実際の Hom の後合成・前合成の trivial Kan 性を証明。
  左側には `EnrichedAdjunctionHomComposition` の Hom 同型・右変数の豊穣合成互換・元の通常随伴との零単体互換を明示入力。このデータから既存の `SimplicialAdjunctionHomIso` への接続も完了。
  `UpperMissingCylinder`・`UpperMissingCube`・`UpperMissingPath` は上面一つを欠く部分の anodyne 性と Kan 延長を構成。
  `UpperMissingPathCover` は全零座標面と指定外の合成面の正確な被覆・貼り合わせ・全既知面を保持する延長。`PathCubeBoundary` は元の全境界を固定した trivial Kan 持ち上げ。
  `QuillenCfOuterHomFilling` は空洞の Kan 延長と上面の trivial Kan 持ち上げを、元の左右の候補辺の Hom 射に代入。二つの未知写像を元の境界と底の写像を保持して構成する。
  `FinalHornKnownIntervals`・`FinalHornIntervalHom` は実際の最終外側ホーンの既知区間を元の面から回収し、選択独立性・単位・合成・全既知面への制限を照合。
  `FinalHornComposition`・`FinalHornFaceCompatibility` は実際の零座標面と既知合成面の回収を構成し、全ての二面の交わりでの一致を証明。整合性は追加仮定にしない。
  `FinalHornHollow` は元の最終外側ホーンから上面欠損 Path の Hom 写像を貼合せ、端点 Hom の Kan 性から全既知面を固定した延長を構成。`QuillenCfFinalHornHollow` は元の cf 対応圏へ代入済み。
  `PathCubeBoundaryCover` は全零座標面・全合成面による全境界の被覆・貼合せ・指定底写像の trivial Kan 持ち上げ。
  `FinalHornFrontBoundary` は元の最終ホーンから前半未知 Hom [0,penultimate] の全境界を回収。全ての面の交わりでの一致を導き、空境界の小次元も保持。
  `FinalHornLastPath` は最後の隣接 Path の単位同型と、前半 Path から penultimate 合成面への同型を native な Path 合成で照合。
  `FinalHornPostcomposition` は最終既知区間から通常の射を回収し、合成面の式を実際の後合成として照合。
  `FinalHornFaceComposition`・`FinalHornAppend` は同じ既知面内の合成保存と最後の隣接 Path 付加を、零座標面・合成面・結合則を含めて照合。
  `FinalHornBoundaryCompatibility` は後半 Hom の延長の上面と、前半の全境界の後合成可換性を元の既知面から証明。可換性を追加仮定にしない。
  `FinalHornUnknownHom` は端点 Hom の Kan 性と回収した最終区間射の後合成の trivial Kan 性から、二つの未知 Hom を全既知面を固定して構成。penultimate 合成面の式も回収。
  `FinalHornLastEdge` は回収した最終区間射の coherent な辺を元の固定最終辺の像と同定。両端点を含む通常の射のデータと、元の指定辺による後合成の trivial Kan 性の移送も照合。
  `QuillenCfFinalHornBase` は元の相対ホーンの底 Δ¹ の単調性から、penultimate 以前の全頂点が下段の cf 対象であることを導く。
  `QuillenCfFinalHornFixedEdge`・`QuillenCfFinalHornUnknownHom` は元の右 Quillen 候補辺と固定 SM7 から二つの未知 Hom を構成。主定理は相対ホーンの可換正方形と固定最終辺を入力とし、先頭の下段性や ambient 全対象の Hom 条件を追加仮定にしない。
  `FinalHornFillHom`・`FinalHornFilledFunctor` は全頂点対の Hom と単位・全三対象の合成を照合し、元の native な豊穣単体を復元。
  `FinalHornFilledRestriction` は全既知面への制限と元のホーンへの制限を証明。`QuillenCfRightCartesian` は底 Δ¹ の薄さで射影一致を示し、元の右 Quillen 候補辺の `IsCartesianEdge` を相対外側ホーンの全次数で証明。
  `CoherentOppositeEdge`・`InitialHornFiller` は元の初期辺と反対射の辺、前合成と反対圏の後合成を照合し、元の初期ホーンを充填。
  `QuillenCfInitialHornBase` は相対ホーンの全後半頂点の上段性を導く。`QuillenCfLeftCocartesian` は元の前合成の trivial Kan 性と底の薄さから、元の左候補辺の `IsCocartesianEdge` を全次数で証明。
  `IntervalCartesianCriterion`・`QuillenCfBifibration` は標準辺と全定値辺の持ち上げを構成。元の cf 区間射影は CartesianFibration かつ CocartesianFibration。
  **未完了**：両端 fiber 上の導来関手・導来 ∞ 随伴・単位/余単位・三角整合性、一般 coherent 極限保存。
- **残り**（依存順、時間は再開後の概算）：
  1. N-2：F1b の随伴 API へ接続し、導来 ∞ 随伴・単位/余単位・三角整合性と一般 coherent 極限保存。HTT 5.2.4.6、Kerodon §6.2、12〜30時間。
  2. N-3：Sp へ適用し、Tot・hG・fiber 列を Sp の ∞ 極限と照合（Sp レーンと共同）。BF §3、HA §1.4、16〜40時間。
  3. E2b へ γ4 を提供し、Alg_E と忘却関手へ適用。HTT 1.1.5.10・5.2.4.6、16〜40時間。
  4. F2 後半の Bousfield 局所化・P_Σ は I-b。Ind・compact・冪等完備化は F1b 所有（`foundations.md` §6）。
- **主要宣言**（名前のみ）：
  `F2.coherentDiagramTotalCocone_isColimit`、`F2.hasColimit_coherentSpaceDiagram`、
  `HomotopyLimits.SimplicialAdjunctionHomIso`、`HomotopyLimits.strictCoherentCone_map_isLimit_of_adjunctionHomIso`、
  `HomotopyLimits.strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso`、
  `HomotopyLimits.chosenQuillenFrameHomIso`、`HomotopyLimits.chosenQuillenDerivedHomFromLeft_homotopyEquivalence`、
  `HomotopyLimits.chosenQuillenDerivedHomFromRight_homotopyEquivalence`、
  `HomotopyLimits.FixedSimplicialPushoutProduct`、`HomotopyLimits.EnrichedAdjunctionHomComposition`、
  `HomotopyLimits.enrichedAdjunctionHom_toSimplicial`、`HomotopyLimits.quillenCfCollageProjection`、
  `HomotopyLimits.quillenCfBottomFiberIso`、`HomotopyLimits.quillenCfTopFiberIso`、
  `HomotopyLimits.quillenCfBottomFiberIso_hom_ι`、`HomotopyLimits.quillenCfTopFiberIso_hom_ι`、
  `HomotopyLimits.quillenCfRightLiftEdge`、`HomotopyLimits.quillenCfLeftLiftEdge`、
  `HomotopyLimits.quillenCfRightLiftHom_trivialKanFibration`、`HomotopyLimits.quillenCfLeftLiftHom_trivialKanFibration`、
  `HomotopyLimits.upperMissingPathFace_extension`、`HomotopyLimits.pathCubeBoundary_lift`、
  `HomotopyLimits.quillenCfRightHom_twoStageLift`、`HomotopyLimits.quillenCfLeftHom_twoStageLift`、
  `HomotopyLimits.finalHornKnownIntervalHom`、`HomotopyLimits.finalHornKnownIntervalHom_on_face`、
  `HomotopyLimits.finalHornHollowHom_extension_components`、`HomotopyLimits.quillenCfFinalHornHollow_extension`、
  `HomotopyLimits.finalHornFrontBoundaryHom`、`HomotopyLimits.finalHornFrontBoundaryHom_lift`、
  `HomotopyLimits.finalHornFrontThroughIso`、`HomotopyLimits.finalHornFrontThroughIso_hom_ι`、
  `HomotopyLimits.finalHornLastArrow`、`HomotopyLimits.finalHornFrontThroughIso_postcomposition`、
  `HomotopyLimits.finalHornFrontBoundaryHom_postcomposition`、`HomotopyLimits.finalHornUnknownHom_extension`、
  `HomotopyLimits.finalHornFrontHom_postcomposition_composition`、`HomotopyLimits.finalHornLastArrow_edge`、
  `HomotopyLimits.finalHornLastArrow_data_of_fixedEdge`、`HomotopyLimits.quillenCfFinalHorn_prefix_bottom`、
  `HomotopyLimits.quillenCfFinalHornRight_relative_unknownHom_extension`、
  `HomotopyLimits.finalHornFilledFunctor`、`HomotopyLimits.finalHornFiller_restriction`、
  `HomotopyLimits.quillenCfFinalHornRight_hasLift`、`HomotopyLimits.quillenCfRightLiftEdge_isCartesian`、
  `HomotopyLimits.coherentNerveOppositeMap_edge`、`HomotopyLimits.initialHornFiller_of_precomposition`、
  `HomotopyLimits.quillenCfInitialHorn_suffix_top`、`HomotopyLimits.quillenCfInitialHornLeft_hasLift`、
  `HomotopyLimits.quillenCfLeftLiftEdge_isCocartesian`、
  `HomotopyLimits.cartesianFibration_interval_of_lift`、
  `HomotopyLimits.quillenCfCollageProjection_cocartesianFibration`、`HomotopyLimits.quillenCfCollageProjection_cartesianFibration`。
- **依存と提供**：F1・F1b（coherent Hom・随伴）、F2 の coherent 余極限、HomotopyFunctionComplex、Coherent、Stable、KST/Spectra を読み取り専用で使用。
  N の集約は `InfinityCategories/HomotopyLimits.lean`、監査は `scripts/audit_homotopy_limits.lean`。提供先は Sp・E2b。
  型は Lean、運用は `foundations.md` §8。README は規約だけ。実施記録はコミットメッセージ。
- **未コミット**：今回の全基底辺の持ち上げによる両 fibration 構造の2モジュール3宣言、集約・監査、本 N 節を保存。保存後は N 所有の変更なし。他レーンの差分は保存対象外。
  root の迷子 `InfinityCategories/HomotopyLimits/RelativeFreePathBoundary.lean` は修正版を正しい場所へ保存済みの N 旧稿と確認し、削除済み。
- **既知の問題**：N の対象ビルド・全監査に失敗なし。新規モジュールの警告・新規 sorry・追加公理なし。import 閉包に他レーンの未コミット差分なし。一般 γ4 は未完了。
  `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので import しない。主経路に `ModelCategory SSet` を仮定せず、固定 Quillen 類を使う。
  `FixedSimplicialPushoutProduct` と豊穣随伴の合成互換は標準 simplicial model/adjunction の明示入力であり、通常の Quillen 随伴だけから導いたとは扱わない。Sp・E2b への適用時に構成・証明する。
  元の Hom 同型の終域への通常の自然性だけで ∞ 随伴を完成と数えない。Sp の局所 Kan 性・Ω 条件・cofibrancy を保持。
  他レーンの import 閉包が壊れたら回避せず停止。他レーンの作業中変更を保存しない。
- **次の一手**：N-2。両 fibration 構造と両端 fiber の同型から、元の cf nerve 間の導来関手を構成し、F1b の随伴 API へ接続する。元の左右候補辺の外側ホーン持ち上げと全基底辺の lift は再実装しない。
  `/tmp/QuillenCfDerivedTransport.lean` は両側の導来関手と左の輸送 prism の検証済み試作。まず正式化と全監査・保存、次に右の輸送 prism・通常の cf 置換との比較・随伴の単位比較を構成する。試作だけで ∞ 随伴完成と数えない。
  原典は [HTT 5.2.4.4〜6・Remark 5.2.4.7](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=371)（閲覧・本文照合済み）。5.2.4.6 は simplicial model categories と simplicial Quillen adjunction の命題。
  `F1/CartesianEdge` の述語は指定最終/先頭辺を固定した外側ホーンの相対持ち上げ。Hom の trivial Kan 射だけで満たしたとは扱わない。
  最終ホーンでは [0,n+1] と [0,n+2] の二つの Hom が未知。`i` を penultimate とし、後者を上面一つ欠く空洞から延長、その上面を候補辺の後合成に沿って持ち上げて前者を構成する。
  前半の全零座標面と全合成面は `finalHornFrontBoundaryFaceHom`、整合性は `_compatible`、貼合せは `finalHornFrontBoundaryHom`。全境界可換性は `finalHornFrontBoundaryHom_postcomposition` で証明済み。
  `finalHornFrontThroughIso_hom_ι`・`finalHornAppend` は後半上面への包含を native 合成として同定。固定最終辺との同定は `finalHornLastArrow_edge`、両端点込みの通常の射の照合は `_data_of_fixedEdge`。再実装しない。
  `quillenCfFinalHornRight_relative_unknownHom_extension` は元の可換正方形と固定最終辺から二つの Hom を返す。`finalHornFilledFunctor`・`finalHornFiller_restriction` が単体とホーンの制限を復元し、`quillenCfFinalHornRight_hasLift` は底を固定する実際の相対 filler を与える。
  既知区間の面選択は a>0 なら δ0、それ以外は δpenultimate。`finalHornKnownIntervalHom_eq_viaFace`・`_on_subinterval`・`_comp`・`_on_face` を使う。未知二区間を内ホーン用の一つの未知 Hom に置き換えない。
  元の右候補辺の Hom の trivial Kan 性は下段の試験始域についての命題。`quillenCfFinalHorn_prefix_bottom` は相対ホーンの全前半頂点の下段性を証明済み。主定理は先頭への代入を含む。ambient 全対象の Hom 条件を仮定しない。
  一般の最終ホーンの復元は `finalHornFillHom_comp`・`finalHornFilledFunctor_face`・`finalHornFiller_restriction`。二つの未知区間、順序外の空 Hom、等しい頂点の単位、二次元の空境界を全て含む。内ホーンの h0・hn 仮定は使っていない。
  `coherentNerveOppositeMap_edge` は通常の射の op と元の coherent な辺を照合済み。`initialHornFiller_of_precomposition` は元の前合成の trivial Kan 性から初期ホーンの充填を返す。
  `quillenCfInitialHorn_suffix_top` は元の相対初期ホーンの全後半頂点を上段 cf 対象として回収。`quillenCfInitialHornLeft_hasLift` は元の左候補辺を固定した底 Δ¹ 上の相対 filler。`e : EnrichedAdjunctionHomComposition R adj` を保持。
  反対豊穣圏にモデル構造を追加仮定しない。右候補辺の op を元の左候補辺と同一視しない。一般の `finalHornUnknownHom_extension_of_fixedEdge` と `finalHornFiller_restriction` を再利用済み。
  `F1/CocartesianCosliceConverse.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration` と `CartesianOpposite` も使用可能。ただし相対 coslice と通常の豊穣 Hom の射を混同しない。
  F1b の随伴 API への接続では、`QCatFunctorHomCorrespondence` なら任意の quasicategory パラメータ A の整合が必要。`Localization.IsLocalization` は普遍性の定義で、任意 W の局所化の存在定理ではない。
  N-1 の部分余極限・共通 path end 比較、`/tmp/NativeAttachmentShape.lean` 等の草稿は継続しない。

### E2a（既存の引き継ぎ）

- **現在地**：E2a-0（Ch(A) の射影モデル構造）、E2a-1（オペラッド・自由代数随伴）、
  E2a-2（Barratt–Eccles オペラッド・augmentation）まで完了。
  E2a-3 は承認済みの Hopf オペラッド＋区間＋path object 経路で、工程 (1) が完了。
  一般の小さい単体集合の正規化 AW 対角の鎖写像・自然性・余結合性・左右余単位と、
  一般 shuffle 鎖写像の AW 余代数射性を検証し、整数模型へ移送済み。
  `partialComposition_diagonal_tensorμ` が既存 BE 部分合成の余積適合性を与える。
  arity ごとのテンソルオペラッド `Operad.hadamard` を、両単位則・内外等変性・
  入れ子と独立な代入の結合則を含めて構成。頂点の群状元公式から単位保存を証明し、
  `hopfDiagonal` を実際の E → E ⊗ E のオペラッド射に束ねた。
  `BarrattEccles.hopf` はこの対角、既存の E → Com、余結合性・左右余単位則を持つ。
  Σ_n 同変性は対称列の自然性に含まれ、余可換性は要求しない。
  工程 (2) は P-coalgebra・射の圏・忘却関手・オペラッド射に沿う制限を構成済み。
  `CoalgebraInterval` は実際の余代数・二端点・収縮・余演算の保存図式と、
  底の境界 cofibration・収縮の擬同型からなる。区間の制限も構成済み。
  convolution の反復評価とその両変数自然性、各 arity の演算 chain map は構成済み。
  底の Hom(H,B) の `prepathComplex`、定数射と両端点評価の自然性も検証済み。
  単位則・全置換の等変性・代数射の後合成による全演算の保存を検証済み。
  `convolutionAction_comp` で全位置の部分合成則を閉じ、`convolutionAlgebra` を構成。
  前合成・後合成を代数射と `convolutionFunctor`・`convolutionPreNat` へ束ねた。
  `unitCoalgebra ε` は任意の augmentation の単位余代数。`convolutionUnitNatIso` は
  Hom(単位,B) ≅ B を自然な P 代数同型にする。区間の端点・収縮も余代数射に束ねた。
  `prepathAlgebra` は全代数の自己関手と自然な定数・両端点評価を持ち、底の既存の射と厳密に一致。
  `evaluationPair_projectiveFibration` は底の二端点評価の対が射影 fibration であることを示す。
  `constant_quasiIso` と `evaluation_quasiIso` は任意の値域で定数射・両評価の底の擬同型性を示す。
  単位の cofibrancy、端点の鎖ホモトピー逆、符号付き Hom 前合成の移送から導出済み。
  `Algebra.binaryProductIsLimit`・`terminalAlgebraIsTerminal` で積・終対象を底の複体に構成。
  `pathAlgebra` は全代数の good path object。忘却の逆像の弱同値・fibration は局所選択。
  `fibrations_llp_quasiIso` は retraction と逆合成の path から底の擬同型性を示す。
  自由像の `freeGeneratingTrivialCofibrations_cell_acyclicity` は任意の始域で成立。
  一般の極限余極限・自由像の小対象性・転送定理の適用は未完成。
  E2a-3 の工程 (2) の転送と工程 (3)・(4)、E2a-4・5、E2b・G1′ は未完成。
  現在地のコードと検証は本節と同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. 代数の積と終対象を底で構成し、忘却関手との比較から good functorial path object を完成。
     続いてこの path object から底のホモトピー同値性を示し、
     小対象性・一般の極限余極限と転送の適用を閉じる。J-cell acyclicity は構成済み。
     Berger–Moerdijk（BM）2003 命題 4.1・§4.6.3、BF §3.1、24〜60 時間。
  2. TR : E → χ のオペラッド射性を一般に証明し、χ の区間切断作用を Δ¹ に適用する。
     BF §1.3・§3.1 と McClure–Smith の区間切断作用、80〜200 時間。
     着手前にファイル数・主要補題の見積もりを計画に一段落で記す指示が未実施。
     Δ¹ の作用は必要次数 r ≤ n に特殊化してよい。TR 自体は一般に証明する。
  3. 具体区間を抽象界面へ代入して E2a-3 を完成。BM 命題 4.1、BF §3.1、8〜24 時間。
  4. E2a-4：右 Quillen、全対象 fibrant、底での homotopy 引き戻し、H⁰ の可換環構造、
     離散可換代数の E 代数化。BM 命題 4.1、BF §3.1、16〜40 時間。
  5. E2a-5：homotopy function complex と π₀ の Hom 比較。
     Hovey §5・Dwyer–Kan、既存 HomotopyFunctionComplex の具体的適用、12〜24 時間。
  6. E2b：CAlg_R := N^hc と U : CAlg_R → D(R)、離散対象と極限。
     HTT §1.1.5・§5.2.4、γ2・γ4 の適用、16〜40 時間。その後 G1′（界面の述べ直し）。
- **主要宣言**（名前のみ）：
  `SerrePositivity.EInfinity.projectiveModelCategory`、
  `SerrePositivity.EInfinity.Operad.freeAlgebraAdjunction`、
  `SerrePositivity.EInfinity.Operad.Hopf`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.hopf`、
  `SerrePositivity.EInfinity.Operad.Coalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraHom`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict`、
  `SerrePositivity.EInfinity.Operad.convolutionAlgebra`、
  `SerrePositivity.EInfinity.Operad.convolutionFunctor`、
  `SerrePositivity.EInfinity.Operad.convolutionPreNat`、
  `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat`、
  `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso`、
  `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono`、
  `SerrePositivity.EInfinity.homPrecompose_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com、
  E の Hopf 構造、余代数区間の界面、全代数の good path object と J-cell acyclicity。
  Alg_E のモデル構造・右 Quillen U・CAlg は未提供。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：対象ビルド成功（2778 jobs）、公理監査成功（5600 宣言、標準 3 公理のみ）。
  新規 sorry・追加公理・名前衝突はなく、572 モジュールの import 閉包に他レーンの未コミット依存はない。
  今回の宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：工程 (2) の一般の極限余極限と自由像の小対象性を構成する。
  極限は `Algebra.ofJointlyMonicActions` と底の極限錐を使い、忘却が極限を作ることを示す。
  余極限は自由・忘却随伴の代数的表示、filtered 余極限とテンソル冪・coinvariant の保存を使う。
  自由像の I・J の小対象性を得て、`Transfer.Right.rightTransfer` へ
  `freeGeneratingTrivialCofibrations_cell_acyclicity` を渡す。TR・具体区間には未着手。

作成日：2026-10-18。状態：計画。ε の経路として E2（モデル圏）を採用（2026-10-18 決定）。
全体の正本は [infinity-categories.md](infinity-categories.md) §0・§5。

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
