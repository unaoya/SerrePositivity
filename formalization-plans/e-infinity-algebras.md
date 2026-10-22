# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）

- **現在地**：**F2N-4 冪等完備化へ移行（10-22 10:10 ユーザー承認、F1b から移管）。**
  **N-1 完了（F1b の定理を使用、10-20 16:31）。** γ1.5・γ3b と通常の小圏上の γ3c は N 側で完了。
  任意 coherent 空間値図式の余極限は `F2.hasColimit_coherentSpaceDiagram`・`F2.coherentDiagramTotalCocone_isColimit` を読み取り専用で使用。N の部分余極限経路は打ち切り。
  **N-2（γ4）完了。** 固定 SM7・豊穣随伴の元の Hom 同型と合成互換を明示した simplicial Quillen 随伴について証明。
  元の cf 対応圏の coherent nerve、Δ¹ 上の両側 fibration、左右の元の導来関手・標準単位余単位・両三角恒等式、通常の cf 置換との比較を構成。
  `quillenCfDerivedAdjunctionWithComparisons_exists` は同じ単位の ∞ 随伴・両側 fibration・両通常置換との比較・任意 coherent 図式の指定極限保存を集約。添字の quasicategory 性は不要。
  **N-3 の指定された Tot・hG・fiber への適用は Sp の既存定理で達成。** 元の BF 対象・指定辺を保持して読み取り専用で照合。Sp の一般 coherent 極限・全有限極限・安定性の完成とは扱わない。
  **N-4 は休止。残る e・f・g は第 II 段。** 局所同値の強飽和性・任意 coherent 極限での局所対象の閉性、各対象の局所置換が与えられた場合の反射を証明済み。presentable 性からの局所置換の存在は未証明。
  P_Σ の全部分 quasicategory・元の Yoneda の充満忠実な因子化・sifted 余極限閉性を完了。
  **有限余積保存の途中の区切り：P_Σ の元の全区間 Hom の評価自然性まで保存済み（b0ccafbc8）。** 元の Tw の恒等点輸送、同じ選択済み前合成を対角辺とする全三角形族、元の共同評価の四辺を保持した正方形輸送を使用。`sigmaYonedaFiberEvaluation_naturalityIso` は元の Yoneda 辺への前合成後の全評価と、元の標的前層の同じ反変辺の標準輸送を比較。有限余積保存そのもの・sifted 生成・普遍性は未完了。
  **F2N-4(a) 着手。** `IdemShape` は恒等と非恒等冪等元を持つ一対象圏の nerve、`SplitShape` はその二つの形式的像の圏の nerve。通常の Karoubi は添字模型だけに使用。
  `CoherentIdempotent` は元の全 Idem 上の写像。`StrongSplitting` は同じ包含による制限で元の全図式を厳密に回収する写像。元の全図式から得た自己射の冪等性と、強い分裂から同じ二頂点の retract を回収。
  **元の弱い retract の商と実際の分裂三角形の照合を完了。** `WeakShape` は Δ² の長辺を Δ⁰ へ潰す pushout。`weakDiagramEquiv` は全 Ret 図式と同じ二単体・同じ指定点の可換データとの全単射。
  `VertexRetraction.triangle_exists` は元の二射の類を保つ実際の二単体を回収。`RetractionTriangle.weakDiagram` は同じ三角形を元の商へ降ろし、元の二辺・分裂頂点を厳密に回収する。
  `weakComparison` は元の包含・射影の合成二単体を同じ商へ降ろした、強い分裂添字への標準比較。両辺と分裂頂点への一致を証明。
  **Ret の商と元の分裂二単体の像の同定を完了。** 全次数で、同じ像の二単体の単体は、同じ単体か双方が元の長辺を経由すると分類。中央頂点の逆像と単調性を使い、非退化単体だけに制限しない。
  元の商への全射性と核の分類から `weakComparison_mono` を証明。`weakShapeImageIso` は元の商と元の二単体の像の同型で、同型後の包含は `weakComparison` そのもの。inner anodyne 性は以下で証明。
  **HTT 4.4.5.8 の内角 anodyne 補題を完了。** `missingFaceComplex J` は元の単体の頂点像が J を含まない面の合併。元の面の貼付けの交わりを `puncturedFace` と同定し、元の座標の包含を標準ホーンへ矢印同型で照合。
  `missingFaceStage_innerAnodyne` は指定面と内点を含む下方閉じた有限族への元の包含を、実際のホーン pushout の有限合成で証明。最大頂点数の面を除く有限帰納を使用し、全体の存在を入力に仮定しない。
  `missingFaceComplex_innerAnodyne` は i,k∈J・i<j<k・j∉J から元の包含そのものの inner anodyne 性を結論。`alternatingCellBoundary_innerAnodyne` は元の奇数頂点集合 {1,3,…,2m−1} のセル境界について全 m≥2 の同じ包含の inner anodyne 性。Ret の濾過の全被覆性と無限合成も以下で証明。
  **元の交互列の全単体と像の増大列を構成。** `alternatingCell m` は偶数位置 Y・奇数位置 X を持つ元の Δ²ᵐ→SplitShape。長さ零の恒等と正の長さの元の吸収射で全射・恒等・合成を構成し、元の包含・射影・非恒等冪等元を回収。
  `alternatingCell_prefix` は元の先頭部分への制限の全 nerve 単体での厳密な一致。`alternatingCell_one` は保存済みの元の分裂三角形そのもの。
  `retractionStage m` はこの元の全セルの像。元の部分複体としての単調性・全セルの制限と構造射の厳密な可換性を証明。第一段階は `weakRetractionImage` そのもの、`weakShapeStageOneIso_ι` は元の商からの同型後の包含が同じ `weakComparison` であること。全被覆性も以下で証明。
  **奇数頂点を避ける各面の元の因子化と境界の前段階への制限を完了。** `oddFaceCollapse` は隣接する二つの Y を潰す元の順序射。偶奇保存と潰れる二位置を計算し、元の全射・恒等・合成を持つ `oddFaceChain` を証明。
  `alternatingCell_oddFace` は元の奇数頂点の余面を、同じ元の短い交互セルへ厳密に因子化。`alternatingCellBoundary_le_preimage` は元の境界全体が元の前段階の逆像に入る向き。
  `alternatingCellBoundaryLift` は元の全境界から元の前段階への実際の写像。元の包含後に同じ全セルの制限を回収し、`alternatingCellBoundaryLift_square` は元のセルと元の段階包含の正方形の厳密な可換性。全被覆性も以下で証明。
  **元の前段階の逆像＝元のセル境界を完了。** `chainScalar` は元の全 nerve 単体の射を元の二元モノイドの値で比較。X の元の恒等 1 と、異なる奇数位置間の元の冪等元 e を区別し、同じ全セル像の下では奇数位置の違いを潰せないと証明。
  `alternatingCell_odd_injection_exists` は全奇数位置を通る元の単体から、同じ全セル像を持つ列の奇数位置への実際の単射を構成。選んだ元の位置 v と両列の値の一致を保持。`alternatingCell_odd_rank_le` は元の位置数の比較。
  `alternatingCell_stage_preimage m` は全 m≥0 で `(retractionStage m).preimage (alternatingCell (m+1)) = alternatingCellBoundary (m+1)` を全次数で厳密に証明。対象の偶奇だけから単射性を仮定しない。全被覆性・無限合成も以下で証明。
  **元の全セルの核と隣接段階の実際の pushout を完了。** 選んだ奇数位置の順序自己単射は恒等。全奇数位置の一致と元の単調性から、境界外の単体は退化を含め一意と証明。
  `alternatingCell_kernel` は同じ全セル像を持つ二単体を、元から等しい場合か双方が元の境界に入る場合へ分類。元の逆像境界と合わせ、`retractionStage_isPushout` は同じ四射の単体集合の pushout。
  `retractionStageMap_innerAnodyne` は全 m≥1 の元の隣接段階包含の inner anodyne 性。全被覆性・無限合成・`weakComparison` 自身の inner anodyne 性は以下で証明。
  **元の Ret 濾過の全被覆性・無限合成・HTT 4.4.5.6 を完了。** 元の二対象・二元の射を分類し、恒等値の隣接射の潰しは元の全単体と厳密に一致。非退化単体を元の交互セルの面へ入れ、退化も含め第 n+1 段階に収容。
  `retractionStageCocone_isColimit` は元の段階包含を脚とする元の分裂添字の余極限。`weakComparison_innerAnodyne` は元の標準比較そのものを可算無限合成で証明。
  `weakDiagram_extension_exists`・`weakDiagram_strongSplitting_exists` は任意の quasicategory 内で指定した弱い全 retract 図式を厳密に回収。`weakDiagramExtensionSpace_isContractibleKan` は同じ弱い全図式を固定した元の延長空間の可縮性。
  既に指定した全 Idem 図式の分裂空間の可縮性・同じ Idem 図式の余極限や極限との同値は未証明。弱い図式の延長空間の可縮性で代用しない。
  **指定した全 Idem 図式の元の錐・余錐と HTT 4.4.5.9〜10 を完了。** `StrongSplitting.cone`・`.cocone` は元の全図式を厳密に回収し、元の分裂頂点・包含辺・射影辺を保持。任意の後合成とも全錐の等式で整合。
  `idemConeRetraction` は元の右錐から元の全 Idem への厳密な retract。`idemShapeContraction` は元の吸収元の全自然変換から、恒等射と元の一点への定値射の全ホモトピーを構成。
  `idemShape_isWeaklyContractible` は元の Idem に Kan 性を仮定しない弱可縮性。`walkingImage_isInitial`・`walkingImage_isTerminal` は元の分裂対象の通常の添字内での普遍性。
  元の包含の cofinal 性は以下で証明。指定した全 Idem 図式の余錐の普遍性は以下で証明。錐の極限性も以下で証明。通常の添字内の普遍性を任意の quasicategory への像の普遍性で代用しない。
  **HTT 4.4.5.11 の元の包含の cofinal 性を完了。** X からの元の comma の恒等射に始対象を構成。Y からの元の comma は元の射影による圏同型で元の Idem と一致。両 nerve の弱可縮性を元の coslice 引き戻しへ移し、Quillen A を適用。
  `idemInclusion_isRightCofinal` は余極限を計算する向きの元の包含の cofinal 性。`walkingCommaCosliceIso_projection` は同じ元の Idem への射影との厳密な可換性。
  `idemInclusion_mono`・`idemInclusion_rightAnodyne`、`idemCoconeRestriction_trivialKanFibration` を証明。`idemCocone_isColimit_iff_restrict` は任意の全強分裂図式の指定余錐の余極限性を、同じ元の包含への制限で保存・反映。
  元の強い分裂から構成した指定余錐そのものの余極限性は以下で証明。指定した全 Idem 図式の延長空間の可縮性は未証明。
  **元の強い分裂の指定余錐の余極限性を完了。** 元の全分裂添字の全余錐を終対象の一点へ制限すると、元の恒等脚を持つ定値余錐と全写像で一致。任意の quasicategory への像で `splittingDiagramCocone_isColimit` を証明。
  元の Idem への制限は保存済みの指定余錐そのもの。`StrongSplitting.cocone_isColimit`・`.hasColimit` は同じ全 Idem 図式の余極限性と存在を結論。
  `StrongSplitting.postcomposeCocone_isColimit` は任意の後合成でも同じ全余錐が余極限であること。`IsIdempotentComplete.hasColimit` は冪等完備性から全 coherent 冪等図式の余極限の存在への一方向。双対の極限は以下で証明。逆方向・全分裂空間の可縮性は未証明。
  **元の指定錐の双対の極限性を完了。** 双対の左 comma は X で元の恒等射を終対象に持ち、Y で元の Idem と射影による圏同型。`idemInclusion_isLeftCofinal`・`idemInclusion_leftAnodyne` と元の錐制限の自明 Kan 性・極限性の保存反映を証明。
  元の全錐を始対象の一点へ制限した全写像は、元の恒等脚を持つ定値錐と一致。元の Idem への制限は `StrongSplitting.cone` そのもの。`StrongSplitting.cone_isLimit`・`.hasLimit`、任意後合成での同じ錐の極限性、`IsIdempotentComplete.hasLimit` を証明。
  これで強い分裂から同じ全 Idem 図式の余極限・極限の存在への二つの含意を完了。余極限・極限から強い分裂への逆方向と、指定した全 Idem 図式の分裂空間の可縮性は未証明。
  同じホモトピー圏の冪等射を分裂する二つの retract の標準同型と、包含と可換する射の一意性を証明。coherent 分裂空間全体の可縮性の代用にはしない。
  **F2N-4(b)・(c) の対象構成。** 元の前層圏内の Yoneda 像の retract 閉包 `Idem C` を全部分 quasicategory として構成。元の包含と元の Yoneda 因子化は充満忠実、包含後に元の全 Yoneda を厳密に回収。
  元の各頂点は前層圏内で元の指定 Yoneda 対象の retract。閉包の合成・同型不変性・冪等性を証明。`Idem C` の冪等完備性・普遍性はまだ証明していない。
- **残り**（依存順、粗い見積もり）：
  1. F2N-4(a)：強い分裂と同じ全 Idem 図式の余極限・極限の同値、指定した全 Idem 図式の分裂空間の可縮性。HTT 4.4.5.12〜16、15〜40時間。
  2. F2N-4(b)・(c)：前層圏の冪等完備性、retract 閉包への分裂の反映、`Idem C` の冪等完備性、元の因子化による関手 ∞ 圏の普遍性・一意性。HTT 5.1.4.2〜9、25〜70時間。
  3. F2N-4(d)：安定 ∞ 圏の冪等完備化の安定性。元の零対象・有限極限余極限の閉性を証明。HA 1.1.3.7、15〜40時間。
  4. F2N-4(e)：`Ind(C)^ω ≃ Idem(C)`。F1b の F2N-2・F2N-3 の実際の Ind・compact 界面の後。HTT 5.3.4.17・5.3.5、15〜40時間。
  N-4 の局所化・P_Σ の残り e・f・g、E2b の DK/∞ 局所化の普遍性への γ4 の接続、Sp の残る安定性との整合は第 II 段。
- **主要宣言**（namespace `SerrePositivity.InfinityCategories.F2.Idempotent`）：
  `WalkingIdem`、`WalkingSplit`、`IdemShape`、`SplitShape`、`idemInclusion`、`CoherentIdempotent`、`StrongSplitting`、`IsIdempotentComplete`、
  `WeakShape`、`WeakRetractionDiagram`、`weakDiagramEquiv`、`weakComparison`、`RetractionTriangle`、`VertexRetraction.triangle_exists`、`RetractionTriangle.weakDiagram`、
  `idemInclusion_isLeftCofinal`、`idemInclusion_leftAnodyne`、`idemConeRestriction_trivialKanFibration`、`idemCone_isLimit_iff_restrict`、`StrongSplitting.cone_isLimit`、`StrongSplitting.hasLimit`、`StrongSplitting.postcomposeCone_isLimit`、`IsIdempotentComplete.hasLimit`、
  `StrongSplitting.cocone_isColimit`、`StrongSplitting.hasColimit`、`StrongSplitting.postcomposeCocone_isColimit`、`IsIdempotentComplete.hasColimit`、
  `walkingImageCommaIso`、`walkingSourceComma_isInitial`、`walkingComma_isWeaklyContractible`、`walkingCommaCosliceIso_projection`、`idemInclusion_isRightCofinal`、`idemInclusion_rightAnodyne`、`idemCoconeRestriction_trivialKanFibration`、`idemCocone_isColimit_iff_restrict`、
  `StrongSplitting.cone`、`StrongSplitting.cocone`、`StrongSplitting.cone_vertex`、`StrongSplitting.cocone_vertex`、`idemConeRetraction`、`idemConeRetraction_inl`、`idemShapeContraction`、`idemShape_isWeaklyContractible`、
  `walkingSplit_object_cases`、`walkingHom_cases`、`absorbingChainFace_eq`、`identityCollapse_chain_eq`、`retractionStage_contains_simplex`、`retractionStage_iSup_succ`、
  `retractionStageCocone_isColimit`、`weakComparison_innerAnodyne`、`weakComparisonRestriction_trivialKanFibration`、`weakDiagram_extension_exists`、`weakDiagram_strongSplitting_exists`、`weakDiagramExtensionSpace_isContractibleKan`、
  `alternatingCell_kernel`、`retractionStage_isPullback_app`、`retractionStage_isPushout_app`、`retractionStage_isPushout`、`retractionStageMap_innerAnodyne`、
  `chainScalar`、`alternatingCell_equal_indices`、`alternatingCell_odd_injection_exists`、`alternatingCell_odd_rank_le`、`alternatingCell_stage_preimage`、
  `oddFaceCollapse`、`oddFaceChain`、`alternatingCell_oddFace`、`alternatingCellBoundary_le_preimage`、`alternatingCellBoundaryLift`、`alternatingCellBoundaryLift_square`、
  `alternatingCell`、`alternatingCell_prefix`、`alternatingCell_one`、`retractionStage`、`retractionStage_mono`、`retractionStage_one`、`weakShapeStageOneIso_ι`、`retractionStageCell_prefix`、
  `missingFaceStage_inf_face`、`puncturedFace_coordinate_preimage`、`puncturedFace_innerAnodyne`、`missingFaceStage_innerAnodyne`、`missingFaceComplex_innerAnodyne`、`alternatingCellBoundary_innerAnodyne`、
  `walkingRetractionTriangle_kernel`、`weakComparison_mono`、`weakComparison_range`、`weakShapeImageIso`、`weakShapeImageIso_ι`、
  `isVertexRetractOf_iff_retractionTriangle`、`CoherentIdempotent.endomorphism_idem`、`StrongSplitting.vertexRetraction`、`VertexRetraction.isoOfSameIdempotent`、`VertexRetraction.hom_unique`、
  `IsVertexRetractOf`、`retractClosure`、`retractClosure_idempotent`、`IsRetractPresheaf`、`Idem`、`idemInclusionPresheaf`、`idemYoneda`、`idemYoneda_inclusion`、`idemYoneda_isFullyFaithful`、`idemVertex_retract_yoneda`。
  N-1〜4 の保存済み公開名・型は `HomotopyLimits.lean` と `scripts/audit_homotopy_limits.lean` を参照。
- **依存と提供**：F2・F1B・F1 は読み取り専用。新規所有範囲は `InfinityCategories/F2/Idempotent/`・独立集約 `F2/Idempotent.lean`・独立監査 `scripts/audit_f2_idempotent.lean`。
  F1b の F2 集約を変更しない。`infinity-core-F2.md` の表は旧担当表記のまま読み取り専用。移管の正本は上記ユーザー承認。規約は `foundations.md` §8。
- **未コミット**：なし（今回の10モジュール33宣言、独立集約・全監査、本 N 節を保存。他レーンの差分は対象外）。
- **既知の問題**：F2N-4 の集約ビルド4260 jobs・全348宣言監査は終了コード0、標準三公理のみ。新規警告・sorry・追加公理なし。N-4 の既存保存は7604 jobs・全5288宣言監査が終了コード0、標準三公理のみ。
  `Inputs/Homotopy/KanQuillen.lean` は import せず、主経路に `ModelCategory SSet` を仮定しない。固定 SM7・豊穣随伴の合成互換を、通常の Quillen 随伴だけから得たとは扱わない。
  同じ射の類の冪等性だけを coherent 冪等図式と扱わず、ホモトピー圏の分裂の一意性だけを全分裂空間の可縮性と扱わない。存在・普遍性を未証明の入力フィールドに置いて完成とは扱わない。
- **次の一手**：F2N-4(a)：HTT 4.4.5.14 の逆方向へ進む。元の `idemInclusion` の inner fibration 性・写像空間での充満忠実性を実際に証明し、F1B の `exists_kanLeftCanonical_strict_extension_of_local_colimits` へ接続。X での左局所添字は構成済みの終対象を持つ左 comma、Y では元の Idem と射影同型なので、指定した元の図式の余極限から全局所余極限を構成する。元の全図式を厳密に回収する強い分裂を得て、余極限の存在と分裂の同値を証明。続いて極限からの逆方向と 4.4.5.16 の全分裂空間の可縮性。Kan 存在・充満忠実性・全分裂空間の可縮性を未証明の入力として追加しない。完成済みの両 cofinal 性・指定錐と余錐の絶対的な普遍性を再実装しない。
  **N-4 の再開点（第 II 段）**：元の有限離散余極限余錐を反対圏の有限積錐へ移し、`sigmaPresheafVertexFunctor_preservesFiniteProducts` を適用。各脚の Hom 前合成を `sigmaYonedaFiberEvaluation_naturalityIso` で同じ値図式の輸送へ照合し、元の全余錐像の余極限性を写像空間で判定。空添字も含む。その後 sifted 生成・普遍性。HTT 5.5.8.10・11・14・15。
  原典：[HTT §4.4.5・§5.1.4](https://www.math.ias.edu/~lurie/papers/HTT.pdf)（本文照合済み）、HA 1.1.3.7 は安定性着手時に本文照合する。

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
