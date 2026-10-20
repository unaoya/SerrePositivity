# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  小さい底上の任意の coherent 空間値図式の余極限は F1b の `F2.hasColimit_coherentSpaceDiagram` を使用する。
  正確な入力は `B : SSet.{u}` と `F : (SSet.uliftFunctor.{u+1,u}).obj B ⟶ SpaceInfinity.{u}`。
  `F2.coherentDiagramTotalCocone_isColimit` は元の全空間余錐そのものの native 余極限性を証明する。
  F2 集約・`infinity-core-F2.md` を正本とし、F2 の coherent 余極限の実装は読み取り専用で使用する。
  `F2.CoherentTotalColimit` の対象ビルド5531 jobsと両公開定理の標準3公理監査を N 側でも確認済み。
  **N の部分余極限経路は打ち切り。** 未構成の共通 path end 比較・無限骨格の接続は継続しない。
  検証済みの同経路のコードは保持するが、そこで構成した指定余錐の余極限性を証明済みとは扱わない。
  最終保存単位は共通 native 根辺の厳密な一致・元の比較との三角形・選択済み end 逆の戻しの8モジュール33宣言。
  **次は N-2（γ4）**。通常の随伴と整合する単体的 Hom 同型から、任意の小圏上の strict 表示の native 極限保存を証明済み。
  γ4 の具体例 `K × − ⊣ Map(K,−)` は通常の随伴・豊穣 Hom 同型・零単体と、両対象の anodyne Kan 置換を含む frame Hom を全単体で照合済み。
  N-2：`AdjunctionFrameHomBifunctor` は独立な始域・終域パラメータの双方に自然な全次数の Hom 同型と、元の augmentation との厳密な両立を構成。
  `QuillenReplacedFrameHom`・`ChosenQuillenFrameHom` は一般の左 Quillen 随伴と元の関手的因子分解を代入し、左像 frame の Reedy cofibrancy・定値性・augmentation の弱同値性と左右の Hom の Kan 性を証明。
  `FixedQuillenFrameInvariance`・`FixedQuillenTargetInvariance` は元の frame の弱比較と fibrant 終域の弱比較を、SSet のモデル構造を仮定せず実際の Hom のホモトピー同値へ移す。相対 latching の境界持ち上げと Reedy/Brown 分解を使用。
  `FixedQuillenFrameComparison` は元の関手上の共通 frame の二つの Hom 自然変換を同じ射でホモトピー同値と証明。現在の Hom 同型は同じ Hom 宇宙の二モデル圏で構成。
  `QuillenLeftFrameAugmentation`・`QuillenDerivedHomComparison` は元の左像 frame の全族を Q⋙L 上へ augment し、LQ の標準 Hom と随伴側の Hom を同じ Kan な二変数関手へ自然に接続。両比較はホモトピー同値。
  `ResolutionHomSourceRestriction` は元の Q→id の比較から右側の二重始域置換を戻し、`ResolutionHomTargetReplacement` は同じ終域置換への後合成を構成。全次数の厳密な式とホモトピー同値を証明。
  `ChosenQuillenDerivedHom` は元の三因子分解を実際に代入し、左 LQ の標準 Hom・右 X から RRY への標準解消 Hom・同じ選択済み標準写像空間への比較列を両変数で自然に構成。
  `FixedSimplicialModelCompatibility` は固定 mono/anodyne 類による標準 pushout-product 条件を明示し、cofibrant 始域・fibrant 終域の豊穣 Hom の Kan 性と両変数の trivial Kan 射を証明。
  `QuillenCfReplacementHom` は元の右像の cofibrant 置換と左像の fibrant 置換が cf であること、および同じ比較射上の Hom の trivial Kan 性を証明。
  `QuillenCfCollage`・`QuillenCfCollageInclusions` は既存の有向豊穣 collage を cf 対象へ制限し、同段・混合・空の逆向き Hom の Kan 性、実際の nerve の quasicategory 性と両側の豊穣包含・nerve 写像を構成。ambient 全体の局所 Kan 性は仮定しない。
  `CoherentThinNerveMap`・`QuillenCfCollageProjection` は元の二段関手を全次数の coherent nerve の射へ延長し、二次切断・頂点の作用を照合。cf 対応圏の Δ¹ への射影、両包含との合成が対応する端点への定値射である厳密な式と inner fibration 性を証明。
  `EnrichedFullSubcategoryRestriction`・`CoherentFullSubcategoryRestriction` は頂点条件を持つ元の coherent な写像を同じ全充満部分圏へ制限し、元の包含との厳密な一致・包含の単射性と fiber の同型を構成。
  `QuillenCfEndpointFiber`・`QuillenCfEndpointEquivalence` は実際の区間射影の両端 fiber を元の C・D の cf 対象圏の coherent nerve と同型で同定。同型の全空間への合成は、構成済みの元の両包含に厳密に一致する。
  `QuillenCfMixedHom`・`QuillenCfRightLift`・`QuillenCfLeftLift` は元の両 cf 置換比較から実際の混合候補辺を構成。元の通常射の回収・区間の 0→1 上の射影・実際の Hom の後合成と前合成を全次数で照合し、左右の同じ Hom 射の trivial Kan 性を証明。
  左側は `EnrichedAdjunctionHomComposition` の Hom 同型・右変数の豊穣合成互換・元の随伴の零単体互換を明示入力に使う。通常の Quillen 随伴からこのデータを導いたとは扱わない。
  `EnrichedAdjunctionHomNaturality` は同じ合成互換から通常の終域への全単体の自然性を導き、零単体を保持して既存の `SimplicialAdjunctionHomIso` へ接続。
  一般の Quillen 随伴からの導来 ∞ 随伴、cf 対応圏の Cartesian・coCartesian 条件、右導来関手の一般 coherent 極限保存は未完了。
- **残り**（依存順、時間は再開後の概算）：
  1. N-2：両 fiber を同定済みの区間射影について、Cartesian・coCartesian の持ち上げ条件を証明。HTT 5.2.4.4〜6、8〜20時間。
  2. N-2：F1b の随伴 API へ比較を入力し、導来 ∞ 随伴の単位・余単位・三角整合性と右 Quillen 関手の ∞ 極限保存。HTT 5.2.4.6、Kerodon §6.2、12〜30時間。
  3. N-3：Sp へ適用し、Tot・hG・fiber 列を Sp の ∞ 極限と照合（Sp レーンと共同）。BF §3、HA §1.4、16〜40時間。
  4. E2b へ γ4 を提供し、Alg_E と忘却関手へ適用。E2a の現状は下記、HTT 1.1.5.10・5.2.4.6、16〜40時間。
  5. F2 後半の Bousfield 局所化・P_Σ は I-b。Ind・compact・冪等完備化は F1b 所有（`foundations.md` §6）。
- **主要宣言**（名前のみ）：
  `F2.coherentDiagramTotalCocone_isColimit`、`F2.hasColimit_coherentSpaceDiagram`、
  `HomotopyLimits.bousfieldKanCoherentCocone_isColimit`、`HomotopyLimits.kanDiagramCoherentNerve_hasColimit`、
  `HomotopyLimits.SimplicialAdjunctionHomIso`、`HomotopyLimits.simplicialAdjunctionHomIso_zero`、
  `HomotopyLimits.representableComparison_adjunction_square`、
  `HomotopyLimits.strictCoherentCone_map_isLimit_of_adjunctionHomIso`、
  `HomotopyLimits.strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso`、
  `HomotopyLimits.kanTensorAdjunctionHomIso`、`HomotopyLimits.kanInternalHom_map_isLimit`、
  `HomotopyLimits.kanReplacedTensorFrameAdjunction_square`、`HomotopyLimits.adjunctionFrameHomBifunctorIso`、
  `HomotopyLimits.adjunctionFrameHomBifunctorIso_augmentation`、`HomotopyLimits.chosenQuillenFrameHomIso`、
  `HomotopyLimits.chosenQuillenFrameHom_leftKan`、`HomotopyLimits.chosenQuillenFrameHom_rightKan`、
  `HomotopyLimits.frameHomMap_trivialKanFibration`、`HomotopyLimits.frameHomMap_homotopyEquivalence`、
  `HomotopyLimits.frameHom_target_homotopyEquivalence`、
  `HomotopyLimits.fixedFrameOverFunctor_homLeft_homotopyEquivalence`、
  `HomotopyLimits.fixedFrameOverFunctor_homRight_homotopyEquivalence`、
  `HomotopyLimits.quillenLeftFrameAugmentation`、`HomotopyLimits.quillenDerivedHomFromLeft`、
  `HomotopyLimits.quillenDerivedHomFromRight`、`HomotopyLimits.quillenDerivedHomMiddle_kanComplex`、
  `HomotopyLimits.resolutionHomSourceRestriction_apply`、`HomotopyLimits.resolutionHomTargetReplacement_apply`、
  `HomotopyLimits.chosenQuillenDerivedHomFromLeft_homotopyEquivalence`、
  `HomotopyLimits.chosenQuillenDerivedHomFromRight_homotopyEquivalence`、
  `HomotopyLimits.chosenQuillenRightTargetReplacement_homotopyEquivalence`、
  `HomotopyLimits.FixedSimplicialPushoutProduct`、`HomotopyLimits.fixedEnrichedHom_kanComplex`、
  `HomotopyLimits.quillenRightReplacementHom_trivialKanFibration`、
  `HomotopyLimits.quillenLeftReplacementHom_trivialKanFibration`、
  `HomotopyLimits.QuillenCfCollageInfinity`、`HomotopyLimits.quillenCfCollageInfinity_quasicategory`、
  `HomotopyLimits.quillenCfCollageBottomNerve`、`HomotopyLimits.quillenCfCollageTopNerve`、
  `HomotopyLimits.quillenCfCollageProjection`、`HomotopyLimits.quillenCfCollageProjection_vertex`、
  `HomotopyLimits.quillenCfCollageProjection_innerFibration`、
  `HomotopyLimits.quillenCfCollageBottom_projection`、`HomotopyLimits.quillenCfCollageTop_projection`、
  `HomotopyLimits.quillenCfBottomFiberIso`、`HomotopyLimits.quillenCfTopFiberIso`、
  `HomotopyLimits.quillenCfBottomFiberIso_hom_ι`、`HomotopyLimits.quillenCfTopFiberIso_hom_ι`、
  `HomotopyLimits.EnrichedAdjunctionHomComposition`、`HomotopyLimits.enrichedAdjunctionHom_toSimplicial`、
  `HomotopyLimits.quillenCfRightLiftEdge`、`HomotopyLimits.quillenCfLeftLiftEdge`、
  `HomotopyLimits.quillenCfRightLiftHom_trivialKanFibration`、
  `HomotopyLimits.quillenCfLeftLiftHom_trivialKanFibration`。
- **依存と提供**：F1・F1b（coherent Hom・随伴）、F2 の coherent 余極限、HomotopyFunctionComplex の frame・局所化、Stable、KST/Spectra を読み取り専用で使用。
  N の集約は `InfinityCategories/HomotopyLimits.lean`、監査は `scripts/audit_homotopy_limits.lean`。提供先は Sp・E2b。
  型は Lean、運用は `foundations.md` §8。README は規約だけとし、実施記録はコミットメッセージ。
- **未コミット**：今回の実際の両混合候補辺・左右の Hom の trivial Kan 性・豊穣合成互換と既存の Hom 自然同型への接続の5モジュール26宣言、集約・監査、本 N 節を保存。保存後は N 所有の変更なし。他レーンのファイルと共有計画の他節は保存対象外。
  root の迷子 `InfinityCategories/HomotopyLimits/RelativeFreePathBoundary.lean` は修正版が正しい場所にコミット済みの N 旧稿と確認し、削除済み。
- **既知の問題**：N の対象ビルド・監査に失敗なし。新規 sorry・追加公理なし。一般 γ4 の構成が未完了。
  `AdjunctionHomLimits.SimplicialAdjunctionHomIso` は y に全単体で自然だが、x の高次豊穣自然性は要求しない。これだけで一般の ∞ 随伴の完成と数えない。
  `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので import しない。SSet の固定 Quillen 類を使い、`ModelCategory SSet` の存在を主経路に仮定しない。
  `FixedSimplicialPushoutProduct` は simplicial model の標準互換条件という明示入力。通常の Quillen 随伴だけからは導かず、Sp・E2b への適用時に証明する。
  Sp の局所 Kan 性・Ω 条件・cofibrancy を保持。一般モデル圏・一般図式の cf 置換と高次整合性は別途証明する。
  他レーンの import 閉包が壊れたら回避せず停止し、他レーンの作業中変更は保存しない。
- **次の一手**：N-2。構成済みの `quillenCfRightLiftEdge`・`quillenCfLeftLiftEdge` の Cartesian・coCartesian 性を外側ホーンの相対持ち上げで証明する。
  原典は [HTT 5.2.4.4〜6・Remark 5.2.4.7](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=371)（閲覧・本文照合済み）。5.2.4.6 は simplicial model categories と simplicial Quillen adjunction の命題で、cf 部分対応圏の nerve が両 fibration になることを示す。
  混合 Hom は Map_C(c,Rd)。右候補辺は元の Q(Rd)→Rd、左候補辺は元の Lc→R_D(Lc) の随伴像で構成済み。両辺と Hom の trivial Kan 比較を再実装しない。左側の豊穣合成互換入力と元の通常随伴との一致を保持する。
  `KST/SConstruction/EnrichedFunctorCollage.lean`・`EnrichedFunctorCollageNerve.lean` は読み取り専用。追加コードは N 所有範囲に置く。
  両端の同型は `quillenCfBottomFiberIso`・`quillenCfTopFiberIso` とその `_hom_ι` で完成済み。fiber 同定・元の包含との照合を再実装しない。
  `F1/CartesianEdge.lean` の `IsCartesianEdge`・`IsCocartesianEdge` は指定最終・先頭辺を固定した外側ホーンの相対持ち上げの定義。Hom の trivial Kan 射だけでこの述語を満たしたとは扱わない。`Coherent/HornHollow.lean` 等の内ホーン証明の端点条件を確認し、外側ホーンへ無条件に流用しない。
  `F1/CocartesianCosliceConverse.isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration` は相対 coslice 制限の trivial Kan 性との同値を提供する。Cartesian 側は反転で使えるか確認する。これは通常の豊穣 Hom 射と別の写像なので、混同しない。
  外側ホーンの実装案（未検証）：最終ホーンでは [0,n+1] と [0,n+2] の二つの Hom が未知。後者の立方体を上面一つ欠く空洞から Kan 延長し、その上面を同じ候補辺の後合成に沿って trivial Kan 持ち上げして前者を構成する。内ホーン用の一つだけの未知 Hom と混同しない。
  最初の小工程は `Coherent/HollowCylinder.lean`・`HollowCube.lean` の Λ[1,1] を使う構成の Λ[1,0] 版を N 所有範囲へ作ること。既存の `HornData`・`HornCells` の回収は外側でも使用可能。
  F1b の Cartesian/coCartesian と随伴 API の接続を調べる。`QCatFunctorHomCorrespondence` を使う場合は任意の quasicategory パラメータ A の整合が必要。普通の対象ごとの Hom 同型だけで随伴完成とは数えない。
  F1b `Localization.lean` の `IsLocalization` は普遍性の定義で、任意 W の局所化の存在までは主張しない。一般モデル圏の ∞ 局所化が既存という前提で証明を進めない。
  今回の標準導来 Hom 比較列は自然変換として保持済み。cf 対応圏・混合 Hom の照合、π₀ の通常導来随伴との一致、右導来関手の coherent 極限保存へ使用する。
  `AdjunctionWeakEquivalence.lean`・`SourceInvariance.lean`・`TargetInvariance.lean` の `ModelCategory SSet` 仮定を主経路へ持ち込まない。固定 Quillen 類の API を使う。
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
