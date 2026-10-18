# K-L6（pro 切除）

## 所有するもの・借りるもの

- 所有するもの：ℕ 添字の塔、レベル射、Artin–Mazur 型 pro 同型判定。
- 所有するもの：pro-零性、pro-cartesian の最小形式、対角の共終性。
- 所有するもの：KST §4 の切除証明と Appendix A の必要部分。
- 借りるもの：π_n とスペクトルの fiber 列は K-L9。
- 借りるもの：H_* と plus 構成・群完備化は K-L2。
- 借りるもの：K の値域・関手・局所化の界面は K0・K2。
- 借りるもの：Koszul 複体と Artin–Rees の既存証明。
- 借りるもの：§10 の原典検証は K-L11 の成果も参照する。
- 界面が未到着の部分は明示的な引数とし、証明済みとは表示しない。
- 本レーン自身が証明すべき結論を構造体の仮定に隠さない。

## 正本・目標

- 正本は `formalization-plans/k-theory-kst-route.md`。
- 基盤の決定は `formalization-plans/foundations.md` を優先する。
- KST は arXiv:1611.08466v4。
- 第 1 目標は係数つき pro 切除の完全証明。
- 最終用途は KST Thm A を介する定理 3.1 と supportedRankK0_descent。
- 追加公理、引用定理、sorry は導入しない。
- 標準公理 propext・Classical.choice・Quot.sound だけを許す。
- 作業 namespace は `SerrePositivity.KST.ProExcision`。
- Lean 実装は `SerrePositivity/KST/ProExcision/` に限定する。
- 集約は `SerrePositivity/KST/ProExcision.lean`。
- 監査は `scripts/audit_kst_pro_excision.lean`。
- ルートには指定の public import を 1 行だけ追加する。
- 他レーンの変更は読み取り専用とし、コミットに含めない。

## 現在地

- L6a：最小形式を検証済み。塔・レベル射・Artin–Mazur 判定・pro 五項補題・対角共終性を所有する。
- L1 の具体的 fiber 長完全列と π_n の模型同定は K-L9 の入力であり、本レーンで供給済みと表示しない。
- L6b：複体模型・平坦底変換の工程完了。対象ビルドと254宣言の公理監査が成功し、標準三公理のみ。
- Mathlib の SpectralSequence API は本レーンの Lean ソースに残していない。
- Lemma 4.9：既存の Artin–Rees による有限生成係数版に加え、反復 cone 模型での pro-消滅も証明。
- Lemma 4.10：通常の生成イデアル冪商から Koszul cone ホモロジーへの自然なレベル射 `koszul_comparison` を構成。
- `koszul_comparison_isProIso` は Noether 環上の複体に対し、次数ごとのホモロジー有限性だけで成立する。
- 列長帰納法の各段は実際の cone 長完全列と Artin–Rees による冪核の消滅を使う。
- 係数の塔と末尾変数の冪を独立に扱い、二重塔の各行から対角へ pro 同型を移す。
- 反復する通常商と一度の生成イデアル商の同定は、標準全射の核の計算と第一同型定理による。
- 標準全射・核・通常商の同定・cone 比較はいずれも冪遷移に自然。
- `koszulConeTower_obj` により、各段は既存 `koszulComplexOn (a₁ⁿ,…,aᵣⁿ) K`。
- その塔の遷移も既存の mapping cone の可換正方形から作る。右成分は係数遷移、左成分は冪倍した係数遷移。
- 単体環の π とこの複体模型との同定は K-L9 が供給する界面。π 自体の定理の完成は主張しない。
- 平坦ホモロジー底変換、a(n)M の像のテンソル比較、pro-零性・pro 同型の保存は検証済み。
- 以前の頁計算は完成の根拠に数えず、通常の短完全列・cone 境界で再利用する補題だけを残す。
- L6c：借用する π・H_* の明示的な模型界面に対して工程完了。一般のモノイド作用の半直積・単体的半直積・包含と射影の分裂・ψ の単体性を検証済み。
- `grouplikeActionIso`：群状モノイドの頂点による作用のホモトピー不変な像での可逆性を証明。
- 対象ビルドと1318宣言の公理監査は成功し、標準三公理のみ。
- Lemma A.2 の ψ は anodyne 局所化で同型と証明。π による同値性への移送は K-L9 の模型界面。
- Lemma A.4 の相対項の代数部分：同変射の半直積への誘導射、分裂包含の余核、定数射の相対項での零化を実装。F は H_* を受ける明示的な関手引数。
- Prop A.1 の基礎：一般の作用の圏、同変写像からの関手、二重 nerve と対角、正則作用の nerve の実収縮を実装。さらに一般の単体的集合への作用 `SimplicialSetAction` と、`barSetAction` により BH への作用と実際の `coefficientActionBar`=E_BH G を構成。
- Construction A.6：成分 u⁻¹ の自然変換、nerve の実ホモトピー、係数付き自由鎖複体への実鎖ホモトピーに加え、`conjugationLinearizedHomotopy` で非被約 C(H)⊗ℤΔ¹ の実区間ホモトピーを構成。両端条件は全次数で成立。区間関手・nerve の区間写像・自由化したテンソル区間写像について、群準同型との自然性も証明。
- Construction A.5：ユーザーが augmentation 補正を採用し、L6c を再開。非被約 C(H)=ℤBH を保持する。下記の設計確認欄を参照。
- A.5 の代数部分：`tensorMap_augmentation_expansion` と `tensorMap_augmentation_eq_low` を検証。二つの差の消滅から m+m′+1 以下の補正式を得る。AW・shuffle の実ホモトピーと実区間への復元・同変性も完成。
- `LinearizedMHomotopy.cancel_augmentation`：C(ψ)≃C(ψ)+C(φ)−C(e) から C(φ)≃C(e) を区間写像の差で構成。作用の同変性は `cancel_augmentation_equivariant` で接続済み。
- `LinearizedMHomotopy.homologyMap_eq`：m 次ホモトピーから次数 ≤m の交代面写像複体のホモロジー写像の一致を証明。零次を含む。同変 bar への移送は `linearizedActionBarMHomotopy` と Lemma A.4 で検証済み。
- `actionBarComparison`：実際の E_BH G から B(G⋉H) への単体的比較を構成。transport 関手の合成則と全ての単体射への自然性を検証。
- `coefficientBisimplicialBarComparison`：bar 次数と係数次数を分けた二重単体的比較を構成。対角は元の比較と一致する。各行の始域は H^r×G^r と同型。
- Prop A.1 の幾何的模型は完了：`coefficientBarRowComparison_eq_sweep` で行の比較と有限合成を同定し、各行・対角・実際の `actionBarComparison` の anodyne 局所化可逆性を証明。
- `propA1ComparisonIso` は anodyne 射を反転する任意の借用関手 F に対する実際の同型。F(E_BH G) と H_i(G;C(H)) の模型同定は H_* の所有レーンの界面。同変射に関する同型の自然性も証明。
- Lemma A.4 は借用する H_* の界面に対して完了：`HomologicallyMConstant` は Definition A.3 の入力データだけを保持し、線形な区間写像の bar への持ち上げ、その m 次両端条件、複体の低次数比較、A.1 の自然性、相対余核の零化を実際に証明。
- `SimplicialHomologyModel` は任意の対象の複体模型同型と全ての射の自然性を入力する明示的な H_* の界面であり、A.4 の結論や bar の持ち上げは仮定しない。
- A.5 の厳密化：`strictificationHomotopy` は入力射と全次数ホモトピックで、終点と次数 ≤m で厳密に一致する `strictifiedMap` を構成。
- A.5 の非可換な標的：ユーザーが正本 §13-14 の μ:P×Q→H と因子内の入力ホモトピーを使う形を採用（2026-10-18）。設計停止を解除して実装を再開。augmentation 補正も維持する。
- 外部 G の同変性：両端・射影、射と区間写像の加減法を経由し、`strictifiedMap_equivariant`、`strictificationHomotopy_equivariant`、`cancel_augmentation_equivariant` を検証。因子内の入力ホモトピーの同変性を保つ。
- 正規化：`normalizedMap_component_eq` で低次数の一致を Moore 複体へ移送。`normalizedStrictificationHomotopy` は包含と PInfty 射影による実鎖ホモトピー。正規化した二つの差の低次数消滅まで検証。
- μ 版の入力：`GroupProductData`、`EquivariantGroupProductData`、`ConstructionA5Input` は採用済みの因子内入力と全データの外部作用を明示。φ、φ′、φ·φ′ を実群準同型として構成し、両因子の像の可換性と G 同変性を証明。入力の厳密化との接続も検証。A.5 の結論のホモトピーは入力に含めない。
- Construction A.6 の外部作用：`conjugationLinearizedHomotopy_equivariant` は u を固定する作用について実区間写像の同変性を証明。`conjugationEquivariantCylinderMap` は作用 bar の持ち上げへ直接渡せる界面。
- 正規化の全テンソル：`integerTensorBifunctor` を任意の加群宇宙で構成。`chainIntegerTensorMap_eq_zero_low` と `normalizedStrictifiedTensor_eq_low` により、実際の ℕ 次数の正規化全テンソルで m+m′+1 以下の差の消滅と補正和の一致を検証。既存の整数次数 cochain での評価だけに依存しない。
- AW の実成分：`alexanderWhitneyApp` を共有切断点の有限和で構成し、`alexanderWhitneyApp_naturality` を証明。鎖写像性も `alexanderWhitney_comm` で検証済み。shuffle の実鎖写像も構成済みだが、標準鎖ホモトピーも `ezHomotopy` で構成済みであり、AW の構成だけで A.5 完了とはしない。
- 区間ホモトピーの操作：`LinearizedMHomotopy.trans` は線形な加減法で連結し、`precomp` と `postcomp` は端点の自然性から実写像に沿って移送する。最後の対角・μ の適用に使う。
- AW の境界計算：`awInterval_face_before`、`awInterval_face_after`、`awInterval_face_inside` により全ての面の制限公式を検証。`awBoundaryIndexEquiv` と `awBoundaryIndex_sum` は左右の非対角境界項を削除点と削除後の切断点の二重和へ移す。実 AW の微分との接続と対角項の相殺も `alexanderWhitney_comm` で完了。
- AW の実微分：`awTensorTerm_D₁`、`awTensorTerm_D₂` は全複体の実微分を交代境界和へ展開。`alexanderWhitney_source_boundary`、`alexanderWhitney_horizontal_boundary`、`alexanderWhitney_vertical_boundary` まで接続。`awLeftBoundaryTerm`、`awRightBoundaryTerm`、`awDiagonalBoundaryTerm` は具体的な非対角項と対角項を同定。添字の座標の同値も構成済みであり、`awBoundaryCoordinates_sum` で全有限和にまとめ、`alexanderWhitney_comm` を証明済み。
- 標準 AW の鎖写像は完了：`alexanderWhitney` は証明済みの微分可換性を持つ実鎖写像。`alexanderWhitney_naturality` により二つの入力の写像について自然。引用・追加公理・結論を隠す構造体入力は用いていない。
- 正規化 AW：`normalizedAlexanderWhitney` は Moore 複体の包含・標準 AW・両因子の PInfty 射影の合成による実鎖写像。`normalizedAlexanderWhitney_naturality` も証明。
- shuffle：`shuffleBidegree`、`shuffleApp` を逆転数の符号付き格子路の有限和として構成し、両因子の射に関する自然性を証明。`ShuffleIndex` の二つの順序写像は、座標和が頂点番号に一致し、両端を保ち、一歩ごとの水平・垂直の変化を持つ。shuffle の鎖写像性と自然性は `ShuffleChainMap.lean` で検証済み。恒等と AW→shuffle の標準鎖ホモトピーと自然性も `ezHomotopy` で検証済み。
- shuffle の全射性：`discretePath_intermediate` により、一歩の増加が高々1の整数値の路の中間値を最小頂点で証明。`ShuffleIndex.left_surjective` と `right_surjective` は、二つの実順序写像が単体圏の全射であることを検証。
- shuffle の混合面：`swapSteps` の二重適用は恒等。間の頂点を削除した第一・第二写像は交換前後で一致し、`shuffleSwapMixedFace_map` が実テンソル写像の一致を与える。水平・垂直から垂直・水平への交換で逆転数が1増えることを前半ステップ数の和で証明し、`shuffleSwapMixedFace_cancel` で二つの実混合境界項の相殺まで検証。同種ステップの面と端点は下記で検証済み。全有限和への統合は `shuffleBidegree_boundary_pure` と `shuffle_comm` で完了。
- shuffle の一ステップ挿入：`insertHorizontal` と `insertVertical` は実際の水平集合の濃度を保つ構成。挿入を飛ばす頂点包含に沿う第一・第二座標の増分を検証。各因子の通常境界への対応を続行する。
- shuffle の同種ステップと端点の面：`insertHorizontal_left_face`・`insertVertical_right_face` は内部の同種ステップの面を各因子の面へ同定。先頭・末尾も第一・第二因子ごとの実単体写像の等式を検証。`insertHorizontal_inversions`・`insertVertical_inversions` は前半垂直数・後半水平数による増分を計算し、`insertHorizontal_face_sign`・`insertVertical_face_sign` は通常境界の符号を同定。境界添字の分類と全有限和の組み立ても完了し、`shuffle_comm` へ接続済み。
- shuffle の境界添字：`removeHorizontal`・`removeVertical` と挿入の両逆を検証し、位置つき挿入の実同値を構成。`rank_eq_left` は水平ステップの順位と第一座標を同定。`horizontalFacePosition`・`horizontalFaceVertex` は各第一因子の面を実挿入に送り、`horizontalFace_left`・`horizontalFace_right` が面の実写像を同定。補集合による二因子交換で `verticalFace_left`・`verticalFace_right` も検証。境界添字全体の分類と全和への統合は `shuffleBoundaryPartitionEquiv` と `shuffle_comm` で完了。
- shuffle の全混合境界和：`MixedShuffleIndex.swap` は固定点のない対合で、`shuffleMixedWeight_cancel` は面の符号を含む各対の相殺。`shuffleMixed_sum_zero` は全有限和の消滅を実写像について証明。係数群の二倍の単射性を使わず、一般の加法群で成立する有限和の対合による。
- shuffle の純粋境界添字の同値：`horizontalShuffleBoundaryEquiv` は小さい shuffle と第一因子の面から全純粋水平境界への実同値で、`horizontalShuffleBoundary_sum` が有限和を移す。`verticalShuffleBoundaryEquiv`・`verticalShuffleBoundary_sum` は補集合の同値と合成して第二因子の場合を実装。面番号・挿入位置・削除頂点の左右の復元を証明済み。実写像と符号も同定し、全境界の分類と鎖写像性へ接続済み。
- L6c の完成界面：`constructionA5` は μ 版の実 (m+m′+1) 次ホモトピー、`constructionA5_equivariant` は外部 G 同変性、`constructionA5EquivariantCylinderMap` は作用 bar へ渡す束。A.1・A.4・A.6 の H_* の具体模型への特殊化は所有レーンの界面。
- L6d：単体的イデアル模型で Lemma 4.16 の実比較・全行列同変性・係数関手性と A.4 による相対零化を検証済み。一般の非単位図式の標準単位化、Claim 4.15 の一般線形モノイドへの因子化、Prop 4.14 の安定化を続行。L6e〜g は未着手。

## 主要宣言の表

| 宣言 | ファイル | 状態 | 意味 |
| --- | --- | --- | --- |
| tensorMap_augmentation_eq_low | AugmentationTensor.lean | 検証済み | A.5 の右辺の augmentation 補正と次数 m+m′+1 の計算 |
| tensorMap_augmentation_expansion | AugmentationTensor.lean | 検証済み | 差のテンソルの双線形展開 |
| conjugationLinearizedHomotopy | Conjugation.lean | 検証済み | A.6 の C(H)⊗ℤΔ¹ の区間写像と両端条件 |
| LinearizedMHomotopy.cancel_augmentation | AugmentationHomotopy.lean | 検証済み | A.5 の右辺の augmentation 補正の相殺 |
| LinearizedMHomotopy | LinearizedHomotopy.lean | 検証済み | A.3 の零次を含む m 次両端条件、同変性は別条件 |
| linearizedTensorIso | LinearizedTensor.lean | 検証済み | ℤX⊗ℤY と ℤ(X×Y) の単体的同型 |
| conjugationLinearizedHomotopy_naturality | ConjugationNaturality.lean | 検証済み | A.6 の実テンソル区間写像の自然性 |
| LinearizedMHomotopy.homologyMap_eq | MHomotopyHomology.lean | 検証済み | A.4 の非同変複体側、次数 ≤m の一致 |
| coefficientActionBar | BarAction.lean | 検証済み | BH の作用による E_BH G |
| barSetAction | BarAction.lean | 検証済み | 非可換な BH への集合の作用 |
| actionBarComparison | BarTransport.lean | 検証済み | Prop A.1 の単体的比較射（局所化同値性も検証済み） |
| coefficientBisimplicialBarComparison | CoefficientBisimplicialBar.lean | 検証済み | Prop A.1 の二重単体的比較 |
| coefficientBisimplicialBarComparison_diagonal | CoefficientBisimplicialBar.lean | 検証済み | 対角の比較射との一致 |
| coefficientBisimplicialBarRowIso | CoefficientBisimplicialBar.lean | 検証済み | 第 r 行の H^r×G^r への同型 |
| actionNerveEquiv | ActionNerveCoordinates.lean | 検証済み | 作用圏の射列は始点×ラベル列 |
| tupleActionStep_localized_isIso | TupleAction.lean | 検証済み | 指定された座標への群状作用の可逆性 |
| actionBarComparison_localized_isIso | PropA1.lean | 検証済み | Prop A.1 の幾何的比較の対角の局所化同値 |
| propA1ComparisonIso | PropA1.lean | 検証済み | 借用関手 F に対する原典 (A.2) の模型の同型 |
| propA1ComparisonIso_naturality | PropA1Naturality.lean | 検証済み | 同変係数射についての自然性 |
| coefficientBarRowComparison_eq_sweep | BarRowComparison.lean | 検証済み | 行の比較と指定座標作用の有限合成の一致 |
| lemmaA4 | LemmaA4.lean | 検証済み | 同変な m 次ホモトピーから相対項の零化、借用 H_* の界面つき |
| lemmaA4_absolute | LemmaA4.lean | 検証済み | 半直積の絶対項で自明射と一致 |
| linearizedActionBarMHomotopy | LinearizedBarMHomotopy.lean | 検証済み | 同変 m 次ホモトピーの bar への線形な持ち上げ |
| linearizedActionBarCylinderMap | LinearizedBarCylinder.lean | 検証済み | 任意の単体射に自然な線形区間写像 |
| SimplicialHomologyModel | HomologyModel.lean | 界面 | 所有レーンの H_* と複体ホモロジーとの自然同型 |
| LinearizedMHomotopy.strictificationHomotopy | HomotopyStrictification.lean | 検証済み | 入力射と低次厳密化した射の全次数ホモトピー |
| LinearizedMHomotopy.strictifiedMap_equivariant | EquivariantStrictification.lean | 検証済み | 低次厳密化した射の外部 G 同変性 |
| LinearizedMHomotopy.strictificationHomotopy_equivariant | EquivariantStrictification.lean | 検証済み | 厳密化の全次数ホモトピーの同変性 |
| LinearizedMHomotopy.cancel_augmentation_equivariant | EquivariantStrictification.lean | 検証済み | Lemma 4.16 で使う相殺の同変性 |
| LinearizedMHomotopy.normalizedStrictificationHomotopy | NormalizedStrictification.lean | 検証済み | 厳密化前後の正規化した写像の全鎖ホモトピー |
| LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero | NormalizedStrictification.lean | 検証済み | 正規化した差の次数 ≤m の消滅 |
| ConstructionA5Input | GroupProductData.lean | 検証済み | μ と因子内ホモトピーの採用済み入力の型、結論の仮定を含まない |
| GroupProductData.product_apply | GroupProductData.lean | 検証済み | μ(α,β) と φ·φ′ の同定 |
| conjugationEquivariantCylinderMap | ConjugationEquivariance.lean | 検証済み | 固定元の共役ホモトピーの実同変界面 |
| integerTensorBifunctor | IntegerTensorBifunctor.lean | 検証済み | 加群の任意の宇宙での加法的整数テンソル双関手 |
| chainIntegerTensorMap_eq_zero_low | ChainTensorVanishing.lean | 検証済み | ℕ 次数の全テンソルでの m+m′+1 以下の消滅 |
| normalizedStrictifiedTensor_eq_low | ChainTensorVanishing.lean | 検証済み | 正規化した因子内の厳密化から得る実補正式 |
| alexanderWhitneyApp | AlexanderWhitney.lean | 検証済み | 切断点の有限和による実写像、鎖写像性も検証済み |
| alexanderWhitneyApp_naturality | AlexanderWhitney.lean | 検証済み | 二つの単体的整数加群の射に関する成分の自然性 |
| LinearizedMHomotopy.trans | LinearizedHomotopyOperations.lean | 検証済み | 線形な区間写像の連結 |
| LinearizedMHomotopy.precomp | LinearizedHomotopyOperations.lean | 検証済み | 始域の幾何的射による引き戻し |
| LinearizedMHomotopy.postcomp | LinearizedHomotopyOperations.lean | 検証済み | 終域の線形射による移送 |
| awInterval_face_inside | AWFaces.lean | 検証済み | 区間内の面と全単体の削除の交換 |
| awBoundaryIndexEquiv | AWBoundaryIndex.lean | 検証済み | 左右の非対角境界と削除後の切断の明示的な同値 |
| awBoundaryIndex_sum | AWBoundaryIndex.lean | 検証済み | 非対角境界和を削除点×切断点へ移す |
| awTensorTerm_D₁ / awTensorTerm_D₂ | AWTensorDifferential.lean | 検証済み | 全複体の実微分から面の和への展開 |
| alexanderWhitney_source_boundary | AWTensorDifferential.lean | 検証済み | source の境界を削除点×切断点の二重和へ移す |
| alexanderWhitney_horizontal_boundary / alexanderWhitney_vertical_boundary | AWBoundaryExpansion.lean | 検証済み | 全切断点の水平・垂直境界和の展開 |
| awLeftBoundaryCoordinates / awRightBoundaryCoordinates | AWBoundaryCoordinates.lean | 検証済み | 実際の入れ子の境界和の添字の同値 |
| awLeftBoundaryTerm / awRightBoundaryTerm / awDiagonalBoundaryTerm | AWBoundaryTerms.lean | 検証済み | 実境界項と削除後の切断項・対角項の同定 |
| alexanderWhitney_comm | AWChainMap.lean | 検証済み | 実全複体の微分との可換性、非対角和の並べ替えと対角相殺 |
| alexanderWhitney | AWChainMap.lean | 検証済み | 標準 AW の実鎖写像 |
| alexanderWhitney_naturality | AWChainMap.lean | 検証済み | 実鎖写像の二つの入力の射に関する自然性 |
| normalizedAlexanderWhitney | NormalizedAlexanderWhitney.lean | 検証済み | 正規化 Moore 複体の実 AW 鎖写像 |
| normalizedAlexanderWhitney_naturality | NormalizedAlexanderWhitney.lean | 検証済み | 正規化 AW の二つの入力の写像に関する自然性 |
| shuffleApp | Shuffle.lean | 検証済み | 格子路の符号付き和の実成分、鎖写像性は shuffle_comm |
| shuffleApp_naturality | Shuffle.lean | 検証済み | 実成分の二つの入力の写像に関する自然性 |
| ShuffleIndex.coordinates_add / left_step / right_step | ShufflePath.lean | 検証済み | 実格子路の座標と一歩ごとの変化 |
| ShuffleIndex.left_surjective / right_surjective | ShuffleSurjective.lean | 検証済み | 格子路の二つの順序写像が全射であること |
| ShuffleIndex.swapSteps_left_face / swapSteps_right_face | ShuffleSwap.lean | 検証済み | 混合面を削除した二つの単体写像の一致 |
| ShuffleIndex.swapSteps_inversions / swapSteps_sign | ShuffleSwapSign.lean | 検証済み | 隣接する混合ステップの交換による逆転数と符号の変化 |
| shuffleSwapMixedFace_cancel | ShuffleSwapSign.lean | 検証済み | 実テンソル写像の二つの混合境界項の相殺 |
| ShuffleIndex.insertHorizontal / insertVertical | ShuffleInsert.lean | 検証済み | 一つの水平・垂直ステップを挿入する実構成 |
| ShuffleIndex.insertHorizontal_left / insertHorizontal_right / insertVertical_left / insertVertical_right | ShuffleInsert.lean | 検証済み | 挿入を飛ばした頂点における二つの格子路座標の変化 |
| ShuffleIndex.insertHorizontal_left_face / insertVertical_right_face | ShufflePureFace.lean | 検証済み | 同種ステップの内部の面と各因子の面の一致 |
| ShuffleIndex.insertHorizontal_first_left_face / insertHorizontal_last_left_face / insertVertical_first_right_face / insertVertical_last_right_face | ShuffleEndFace.lean | 検証済み | 先頭・末尾の各因子の実面写像の同定 |
| ShuffleIndex.insertHorizontal_inversions / insertVertical_inversions | ShuffleInsertSign.lean | 検証済み | 前半垂直数・後半水平数による逆転数の増分 |
| ShuffleIndex.insertHorizontal_face_sign / insertVertical_face_sign | ShuffleInsertSign.lean | 検証済み | 各因子の通常境界の符号との一致 |
| horizontalInsertionEquiv / verticalInsertionEquiv | ShuffleDelete.lean | 検証済み | 位置つきの挿入と指定ステップを持つ shuffle の実同値 |
| ShuffleIndex.rank_eq_left / horizontalStep_left | ShuffleRank.lean | 検証済み | 列挙した水平ステップの順位と第一座標の一致 |
| ShuffleIndex.horizontalFace_left / horizontalFace_right | ShuffleHorizontalFaceIndex.lean | 検証済み | 第一因子の面番号から挿入への実対応と二つの面写像の一致 |
| ShuffleIndex.verticalFace_left / verticalFace_right | ShuffleTranspose.lean | 検証済み | 第二因子の面番号から挿入への実対応と二つの面写像の一致 |
| MixedShuffleIndex.swap / swap_swap / swap_ne_self | ShuffleMixedSum.lean | 検証済み | 全混合境界添字の固定点のない交換対合 |
| shuffleMixed_sum_zero | ShuffleMixedSum.lean | 検証済み | 面と shuffle の符号を含む全混合境界和の零化 |
| horizontalShuffleBoundaryEquiv / horizontalShuffleBoundary_sum | ShuffleHorizontalBoundary.lean | 検証済み | 全純粋水平境界と小さい shuffle×第一因子の面の実同値と有限和 |
| verticalShuffleBoundaryEquiv / verticalShuffleBoundary_sum | ShuffleVerticalBoundary.lean | 検証済み | 全純粋垂直境界と小さい shuffle×第二因子の面の実同値と有限和 |
| horizontalShuffleFace_map / verticalShuffleFace_map | ShuffleBoundaryMap.lean | 検証済み | 全純粋境界の実テンソル写像の同定 |
| horizontalShuffle_sum / verticalShuffle_sum | ShufflePureSum.lean | 検証済み | 純粋境界和と各因子の通常境界の一致 |
| shuffleBoundaryPartitionEquiv / shuffleBoundaryPartition_sum | ShuffleBoundaryPartition.lean | 検証済み | 零次も含む全境界の水平・垂直・混合への実同値と和の分解 |
| shuffleBidegree_boundary_pure | ShuffleBoundaryDecomposition.lean | 検証済み | 実微分の混合和を消去し二つの純粋和に分解 |
| shuffle / shuffle_comm / shuffle_naturality | ShuffleChainMap.lean | 検証済み | 標準 shuffle の実鎖写像と両因子に関する自然性 |
| normalizedShuffle / normalizedShuffle_naturality | NormalizedShuffle.lean | 検証済み | 非被約 Moore 複体への実 shuffle の移送と自然性 |
| simplexPairExtraDegeneracy / simplexPairLinearExtraDegeneracy | SimplexPairModel.lean | 検証済み | 二つの単体射の対の普遍模型と実 extra degeneracy |
| simplexPairEvaluation / simplexPairEvaluation_map_naturality | SimplexPairEvaluation.lean | 検証済み | 任意の二つの固定単体への単体的評価と入力射の自然性 |
| simplexPairOperation / simplexPairOperation_naturality | SimplexPairOperation.lean | 検証済み | 普遍鎖の整数線形な実テンソル作用素への評価 |
| simplexPairOperation_boundary / simplexPairOperation_modelMap | SimplexPairOperationNaturality.lean | 検証済み | 模型の移送・入力射・交代微分との可換性 |
| simplexPairEvaluation_retraction / simplexPairOperation_injective | SimplexPairFaithfulEvaluation.lean | 検証済み | 普遍模型の評価の左逆と作用素による等式の検出 |
| ezUniversalComposite / ezUniversalDifference | EZUniversalDifference.lean | 検証済み | 実 AW→shuffle 合成と恒等との差の普遍鎖表示 |
| simplexPairFaceSum_faceSum / simplexPairFaceSum_boundary | SimplexPairFaceSum.lean | 検証済み | 二重交代面移送の零性と模型の微分との可換性 |
| ezUniversalDifference_boundary / ezUniversalDifference_zero | EZUniversalBoundary.lean | 検証済み | 比較の普遍な差の境界と非被約零次の零性 |
| ezUniversalHomotopyChain / ezUniversalHomotopyChain_boundary_succ | EZUniversalHomotopyChain.lean | 検証済み | 全次数の普遍充填鎖と境界公式 |
| ezHomotopy / ezHomotopyApp_naturality | EZHomotopy.lean | 検証済み | 恒等と実 AW→shuffle の標準鎖ホモトピーと両入力に関する自然性 |
| chainIntegerTensorHomotopy / chainIntegerTensorMooreRetraction | ChainTensorHomotopy.lean | 検証済み | 二つの鎖ホモトピーの全テンソルへの移送と Moore 収縮 |
| normalizedEZHomotopy | NormalizedEZHomotopy.lean | 検証済み | Moore 複体上の恒等と正規化 AW→shuffle の実鎖ホモトピー |
| moorePInftyHomotopy_naturality | MooreHomotopyNaturality.lean | 検証済み | Moore の実収縮ホモトピーの一段上の成分の自然性 |
| ι_chainIntegerTensorHomotopy | TensorHomotopyComponents.lean | 検証済み | 各二重次数で水平・垂直の実テンソル成分に展開 |
| chainIntegerTensorHomotopyToId_naturality | TensorHomotopyNaturality.lean | 検証済み | 恒等へ至る二つの自然な収縮の全テンソルの自然性 |
| chainIntegerTensorMooreRetraction_naturality | MooreTensorHomotopyNaturality.lean | 検証済み | Moore 収縮の全テンソルの両入力に関する自然性 |
| ChainHomotopySquare / ChainHomotopySquare.compLeft / ChainHomotopySquare.compRight | ChainHomotopySquare.lean | 検証済み | 構成済みホモトピーの自然性の合成則 |
| normalizedEZHomotopy_square | NormalizedEZHomotopyNaturality.lean | 検証済み | 正規化 EZ ホモトピー全体の両入力に関する自然性 |
| integerChainInterval / integerIntervalBoundary_edge | IntegerChainInterval.lean | 検証済み | 二頂点と一辺の実整数鎖区間 |
| integerIntervalWeight_vertices / integerIntervalWeight_triangle | IntegerIntervalWeights.lean | 検証済み | 頂点の差の境界と三頂点の望遠鏡相殺 |
| integerIntervalComparison | IntegerIntervalComparison.lean | 検証済み | ℤΔ¹ の交代面複体から二項整数鎖区間への実鎖写像 |
| integerTensorFreeDesc / integerTensor_free_hom_ext | IntegerTensorFreeDesc.lean | 検証済み | 第二因子の自由基底による降下と純テンソルの外延性 |
| chainHomotopyIntervalBidegree | ChainIntervalEvaluationComponents.lean | 検証済み | 頂点・符号付き辺・高次の零の実成分 |
| chainHomotopyIntervalApp / ι_chainHomotopyIntervalApp | ChainIntervalEvaluation.lean | 検証済み | 全テンソル区間の実降下写像 |
| chainIntervalEndpointEval_comm / chainIntervalEndpointEval_boundary | ChainIntervalEvaluationNaturality.lean | 検証済み | 端点評価の微分可換性と辺の境界の端点の差 |
| chainIntervalEdgeEvalAddHom / chainIntervalEdgeEval_comp / chainIntervalEdgeEval_precomp | ChainIntervalEdgeAdditivity.lean | 検証済み | 辺評価の加法性・整数倍と前後合成 |
| chainIntervalHomotopySign_zero / chainIntervalHomotopySign_succ | ChainIntervalHomotopySigns.lean | 検証済み | 符号付き辺評価の微分等式の代数部分 |
| chainInterval_ι_D₁_succ / chainInterval_ι_D₂_succ | ChainIntervalTensorDifferential.lean | 検証済み | 全テンソルの水平・垂直微分の後の実評価 |
| chainHomotopyInterval / chainHomotopyInterval_comm | ChainIntervalEvaluationChainMap.lean | 検証済み | 鎖ホモトピーによる全テンソル鎖区間からの実鎖写像 |
| chainHomotopyCylinderCore / chainHomotopyCylinderMap / chainHomotopyCylinderReconstruct | ChainHomotopyCylinder.lean | 射の構成済み | AW・区間比較・評価からの実鎖写像と Dold–Kan による実単体的区間射、両端は別工程 |
| integerIntervalComparison_constant_of_pos | IntervalComparisonConstants.lean | 検証済み | 正次数の定数単体の鎖比較での零性 |
| cylinderAWTerm_constant_of_lt | CylinderAWTerms.lean | 検証済み | 最後より前の AW 項の区間の定数単体上の零性 |
| chainHomotopyInterval_naturality | ChainIntervalEvaluationChainNaturality.lean | 検証済み | 端点と鎖ホモトピーの自然な正方形から区間評価の実鎖写像の自然性 |
| chainHomotopyCylinderCore_endpoint₀ / chainHomotopyCylinderCore_endpoint₁ | CylinderAWEndpoints.lean | 検証済み | 最後の AW 項と全和から正規化前の区間の両端を同定 |
| LinearizedHomotopy.ofNormalizedChainHomotopy | NormalizedChainHomotopyReconstruction.lean | 検証済み | 正規化鎖ホモトピーから両端を備えた実単体的区間ホモトピーへの復元 |
| chainHomotopyCylinderReconstruct_naturality | ChainHomotopyCylinderNaturality.lean | 検証済み | 端点と鎖ホモトピーの自然な正方形から実区間射の自然性を導く |
| normalizedMap_eq_low_reflect | NormalizedLowDegreeReflection.lean | 検証済み | P と Q の退化分解による低次数の正規化の一致の反映 |
| linearizedMHomotopyOfChainComparisons | LowChainComparisonReconstruction.lean | 検証済み | 比較先が低次で一致する二つの全鎖比較から実 m 次ホモトピーを構成 |
| normalizedMooreComplex_additive | NormalizedFunctorAdditivity.lean | 検証済み | 包含・交代面複体・射影による正規化 Moore 関手の加法性 |
| normalizedTensorComparisonWithHomotopies / normalizedTensorAugmentationComparison | NormalizedTensorComparison.lean | 検証済み | 単体的テンソルと厳密化した全テンソルの全鎖比較、補正した三項の比較 |
| linearizedTensorAugmentationMHomotopy | TensorAugmentationMHomotopy.lean | 非同変版検証済み | 明示的な前後の射を含む補正式の実 (m+m′+1) 次区間ホモトピー |
| groupProductNerve / groupProductNerve_comp | GroupProductNerve.lean | 検証済み | 非可換群の直積から μ を最後に適用する実 nerve の写像 |
| linearizedGroupProduct / linearizedGroupProduct_comp | LinearizedGroupProduct.lean | 検証済み | μ と対角の自由整数テンソルへの移送と合成群準同型との実等式 |
| normalizedMapReconstruct / normalizedMapReconstruct_comp | NormalizedMapReconstruction.lean | 検証済み | Dold–Kan の実同値からの単体的射の復元と合成則 |
| extraDegeneracy_positive_boundary / extraDegeneracy_fill_cycle | ExtraDegeneracyContraction.lean | 検証済み | 正次数の鎖収縮等式とサイクルの明示的な充填 |
| shuffleBoundary_horizontal_succ / shuffleBoundary_vertical_succ | ShuffleBoundaryDecomposition.lean | 検証済み | 両因子の通常微分への一致と零次の端 |
| obstructionTorusCycle_not_boundary | CommutingImageObstruction.lean | 検証済み | 可換な対 (r²,s) の二次 bar サイクルの非境界性 |
| obstructionHalfTurnBoundingChain_boundary | CommutingImageObstruction.lean | 検証済み | [r²]−[1] の明示的な一次の境界 |
| Tower | Pro.lean | 検証済み | ℕ 上の逆系 |
| LevelHom | Pro.lean | 検証済み | 同じ添字上の可換な射 |
| IsProIso | Pro.lean | 検証済み | eventual inverse の二つの三角形 |
| Tower.map | Pro.lean | 検証済み | 関手による塔の像 |
| LevelHom.map | Pro.lean | 検証済み | 関手によるレベル射の像 |
| IsProIso.map | Pro.lean | 検証済み | 関手による pro 同型保存 |
| diagonal_cofinal | Pro.lean | 検証済み | 二添字の共通上界 |
| IsProZero | Pro.lean | 検証済み | 遷移射の eventual 零性 |
| Tower.reindexHom_isProIso | Pro.lean | 検証済み | 増大する単調再添字 |
| IsProZero.map | Pro.lean | 検証済み | 零射保存関手による保存 |
| IsProEquivalence | Pro.lean | 検証済み | 次数別の pro 同型判定 |
| IsProCartesian | Pro.lean | 検証済み | 与えられた hofib 比較の pro 同値 |
| FiveTermHom.isProIso | FiveLemma.lean | 検証済み | 外側四射が pro 同型なら中央も pro 同型 |
| isProIso_of_mono_epi | ModulePro.lean | 検証済み | 核・余核の eventual 零化から逆射を構成 |
| LevelwiseExactSequence.toTower | ExactSequence.lean | 検証済み | L1 の自然な族を塔に組み立てる |
| ExactTowerSequence.fiveTerm | ExactSequence.lean | 検証済み | 五項部分の抽出 |
| koszulHomologyTower_isProZero | KoszulPro.lean | 検証済み | Lemma 4.9 の環係数版 |
| koszulTensorHomologyTower_isProZero | KoszulPro.lean | 検証済み | Lemma 4.9 の全有限生成加群版 |
| range_lTensor_le_ideal_smul | KoszulPro.lean | 検証済み | 平坦性不要の遷移深度保存 |
| flatTensorHomologyIso | FlatBaseChange.lean | 検証済み | 平坦テンソルとホモロジーの自然同型 |
| ideal_smul_tensor_range | FlatBaseChange.lean | 検証済み | a(n)M のテンソル像 |
| koszul_flatTensor_homology_proZero | FlatBaseChange.lean | 検証済み | 有限生成性を係数変更前にのみ要求 |
| proZero_finite_extension | SpectralPro.lean | 検証済み | 有限拡張の pro-零性 |
| proIso_of_injective_exact_proZero | SpectralPro.lean | 検証済み | edge 比較に使う pro 同型判定 |
| koszulTruncation_initial_isZero | KoszulFiltration.lean | 検証済み | 濾過の初端 |
| koszulTruncation_terminal_isIso | KoszulFiltration.lean | 検証済み | 濾過の終端 |
| truncationFiltrationFunctor | TruncationNaturality.lean | 検証済み | 複体の射に自然な項濾過 |
| adjacentTensorConeHomologyIso | KoszulGraded.lean | 検証済み | 隣接する項濾過の cone のホモロジー計算 |
| totalKoszulTensorIso | TotalKoszul.lean | 検証済み | 全テンソルと既存 Koszul 構成の同型 |
| tensorSplitBoundary_apply_homogeneous | TensorBoundary.lean | 検証済み | テンソル境界の同次純テンソル上の計算 |
| tensorSplitBoundary_eq | TensorBoundary.lean | 検証済み | 全複体射としてのテンソル境界の比較 |
| cutoffBoundary_differential | CutoffBoundary.lean | 検証済み | 項切り詰めの境界は元の微分 |
| cutoffTensorBoundary_differential | CutoffBoundary.lean | 検証済み | テンソル後も元の微分を取り出せる |
| splitBoundary_lift_condition | SplitConnecting.lean | 検証済み | サイクルの持ち上げと分裂境界 |
| splitBoundary_connecting | SplitConnecting.lean | 検証済み | 連結写像の代表元公式 |
| splitBoundary_connecting_eq_shiftMap | SplitConnecting.lean | 検証済み | 連結写像とシフトつき境界の一致 |
| coneCompositeConnecting_quotient | ConeConnecting.lean | 検証済み | 合成 cone の δ と商の連結写像 |
| splitBoundary_differential | CutoffBoundary.lean | 検証済み | 二次数で同型な分裂境界は微分 |
| splitTensorBoundary_differential | CutoffBoundary.lean | 検証済み | 同じ一般境界のテンソル計算 |
| adjacentCutShortComplex | AdjacentCut.lean | 検証済み | 実際の隣接射の短完全模型 |
| adjacentTensorCutShortComplex_shortExact | AdjacentCut.lean | 検証済み | 分裂による全テンソルの短完全性 |
| adjacentTensorCutBoundary_differential | AdjacentCut.lean | 検証済み | 隣接濾過の同次境界計算 |
| intervalCutShortComplex | IntervalCut.lean | 検証済み | 一般区間の実際の商短完全列 |
| tensorFiltrationBoundary | IntervalCut.lean | 検証済み | 実際の区間のシフトつき境界 |
| adjacentGradeBoundary_differential | AdjacentGradeBoundary.lean | 検証済み | 商境界の下端成分は元の微分 |
| adjacentGradeIso | AdjacentGradeBoundary.lean | 検証済み | 標準項同型に合う一項複体模型 |
| singleDegreeBoundary | AdjacentGradeBoundary.lean | 検証済み | 係数射から作るシフトつき一項境界 |
| adjacentGradeBoundary_single | AdjacentGradeBoundary.lean | 検証済み | 商境界と元の微分の複体射としての一致 |
| adjacentTensorGradeBoundary_eq | TensorGradeBoundary.lean | 検証済み | 全テンソルと隣接商境界の比較 |
| adjacentTensorGradeBoundary_single | TensorGradeBoundary.lean | 検証済み | 一項模型でのテンソル微分との一致 |
| flatLeftTensorHomologyIso_map | CoefficientHomology.lean | 検証済み | 平坦テンソルの係数射についてのホモロジー自然性 |
| singleTensorShiftIso_coefficient | SingleTensorNaturality.lean | 検証済み | 一項テンソルのシフト比較の係数自然性 |
| singleTensorHomologyIso_coefficient | SingleTensorNaturality.lean | 検証済み | 一項ホモロジー比較の係数自然性 |
| singleFamilyShift_boundary | SingleShiftCoherence.lean | 検証済み | 一項関手族の隣接境界とシフト加法の整合性 |
| tensorSingleShift_boundary | SingleShiftCoherence.lean | 検証済み | 隣接テンソル境界の正規化は通常の係数射のシフト |
| shiftMap_comparison | ShiftedComparison.lean | 検証済み | 二重シフトの比較を誘導射へ移す |
| singleTensorHomologyIsoAt | ShiftedComparison.lean | 検証済み | 共通係数次数を指定した一項ホモロジー同型 |
| tensorSingleHomology_boundary_at | ShiftedComparison.lean | 検証済み | 隣接境界は共通係数次数で f ⊗ H(K) を誘導 |
| adjacentTensorGradeHomologyIso | GradedHomology.lean | 検証済み | 隣接商のテンソルホモロジーの係数模型 |
| adjacentTensorGradeHomology_differential | GradedHomology.lean | 検証済み | 実際の隣接商境界は P.d ⊗ H(K) を誘導 |
| intervalTensorAdjacentIso | IntervalGradeBoundary.lean | 検証済み | 任意表示の区間の隣接模型への同型 |
| intervalTensorGradeHomology_differential | IntervalGradeBoundary.lean | 検証済み | 正規化前の区間境界の係数微分 |
| IsProZero.of_natIso | KoszulCoefficientSwap.lean | 検証済み | 自然同型による像の塔の pro-零性移送 |
| pointwiseTensorSwapHomologyIso | KoszulCoefficientSwap.lean | 検証済み | 係数の左右交換のホモロジー自然同型 |
| koszulRightTensorHomologyTower_isProZero | KoszulCoefficientSwap.lean | 検証済み | 固定有限生成右係数の Koszul pro-消滅 |
| leftHomologyModelMap_comm | SpectralPageIntervalNaturality.lean | 検証済み | 明示的左ホモロジー模型の写像比較 |
| powerKernelTower_isProZero | PowerKernel.lean | 検証済み | 冪倍遷移を持つ核の pro-消滅 |
| scalarConeHomologyComparison_injective | ScalarConeHomology.lean | 検証済み | 一変数の通常商から cone ホモロジーへの単射 |
| scalarConeHomologyComparison_exact | ScalarConeHomology.lean | 検証済み | 比較射と連結写像の完全性 |
| cone_connecting_naturality | ConeNaturality.lean | 検証済み | 可換正方形に対する cone 連結写像の自然性 |
| powerScalarConeComparison_isProIso | ScalarConePro.lean | 検証済み | 一変数版 Lemma 4.10 |
| BiLevelHom.diagonal_isProIso | BiTower.lean | 検証済み | 行ごとの pro 同型を対角へ移す |
| BiTower.diagonal_isProZero | BiTower.lean | 検証済み | 行ごとの pro-零性を対角へ移す |
| powerKernelTower_isProZero_artinRees | PowerKernelArtinRees.lean | 検証済み | 各標的核を Artin–Rees で零化 |
| scalarCone_homology_finite | ConeFiniteness.lean | 検証済み | 項の有限性を使わない cone ホモロジーの有限性 |
| IsProIso.powerQuotient | PowerQuotient.lean | 検証済み | 動く冪商による pro 同型保存 |
| koszulConeComparison_isProIso | KoszulConeComparison.lean | 検証済み | 列長帰納法による反復商の pro 比較 |
| koszulConeModuleHomologyTower_isProZero | KoszulConeVanishing.lean | 検証済み | KST Lemma 4.9 の cone 模型 |
| iteratedPowerQuotientProjection_ker_ideal | ParameterQuotient.lean | 検証済み | 標準全射の核は生成イデアル倍 |
| parameterQuotientComparison_isProIso | ParameterQuotient.lean | 検証済み | 通常の生成イデアル商と反復商の自然同型 |
| ActionProduct | GroupHomology.lean | 検証済み | 可逆性を要求しないモノイド作用の半直積 |
| actionProductMap | GroupHomology.lean | 検証済み | 同変準同型による半直積の誘導射 |
| actionProductTwist_natural | GroupHomology.lean | 検証済み | Lemma A.2 の台の作用写像の自然性 |
| SimplicialMonoidAction | SimplicialAction.lean | 検証済み | 次数ごとの自己準同型と単体射への自然性 |
| simplicialActionProduct | SimplicialAction.lean | 検証済み | 実際の単体的半直積モノイド |
| simplicialActionProductSection_projection | SimplicialAction.lean | 検証済み | 包含と射影の分裂 |
| simplicialActionProductTwist | SimplicialAction.lean | 検証済み | Lemma A.2 の ψ の台単体写像 |
| actionTranslationHomotopy | ActionTranslations.lean | 検証済み | 辺に沿う作用の実単体的ホモトピー |
| grouplikeActionIso | ActionTranslations.lean | 検証済み | 群状性による各頂点の作用の可逆性 |
| actionFamily_simplex_localized_isIso | ParametrizedAction.lean | 検証済み | 単体上の族の作用を頂点の作用へ収縮 |
| actionFamily_localized_isIso | ActionDescent.lean | 検証済み | 一般の族の作用のセル降下 |
| simplicialActionProductTwist_localized_isIso | ActionTwist.lean | 検証済み | KST Lemma A.2 の局所化模型 |
| simplicialActionProductMap_trivial | ActionMorphisms.lean | 検証済み | 自明射の半直積は基底の射影と包含の合成 |
| relativeModuleMap_zero_of_factor | RelativeModule.lean | 検証済み | 基準像を経由する写像は相対余核で零 |
| relativeBarSection_injective | RelativeBar.lean | 検証済み | 借用する F の下での基底 bar の包含の単射性 |
| relativeBarMap_trivial_zero | RelativeBar.lean | 検証済み | 自明な同変射は相対 bar 項で零 |
| relativeBarMap_zero_of_absolute_eq_trivial | RelativeBar.lean | 検証済み | 絶対項の比較から相対項の零化 |
| actionCategoryMap | ActionCategory.lean | 検証済み | 一般の作用の圏の同変写像による関手性 |
| regularActionObjectNerveContraction | ActionCategory.lean | 検証済み | 正則作用の nerve の実ホモトピー |
| bisimplicialActionBar | ActionBar.lean | 検証済み | モノイド値の作用先に対する二重作用 nerve |
| conjugationNerveHomotopy | Conjugation.lean | 検証済み | KST A.6 の u⁻¹hu と恒等の実 nerve ホモトピー |
| conjugationChainHomotopy | Conjugation.lean | 検証済み | 係数付き自由鎖複体へ移す実鎖ホモトピー |
| no_homotopy_identity_doubleIdentity | AugmentationObstruction.lean | 検証済み | A.5 の非被約な通常和の零次障害の検証 |
| koszul_comparison | KoszulComparison.lean | 検証済み | 通常の生成イデアル冪商から実 Koszul ホモロジーへのレベル射 |
| koszul_comparison_isProIso | KoszulComparison.lean | 検証済み | KST Lemma 4.10 の複体模型 |
| prop414 | Prop414.lean | 予定 | 中心的係数による非可換版 |
| pro_whitehead | Whitehead.lean | 予定 | simple 空間版 |
| claim418 | Serre.lean | 予定 | 相対 Serre SS の帰結 |
| theorem411 | Excision.lean | 予定 | pro 切除 |

| constructionA5 / constructionA5_equivariant | ConstructionA5.lean / ConstructionA5Equivariant.lean | 検証済み | 非可換な μ 版 A.5 の実ホモトピーと外部 G 同変性 |
| constructionA5EquivariantCylinderMap | ConstructionA5Equivariant.lean | 検証済み | 作用 bar に渡す同変な実区間射 |
| linearizedTensorAugmentationMHomotopy_naturality | TensorAugmentationNaturality.lean | 検証済み | augmentation 補正の構成全体の自然性 |
| linearizedGroupProduct_naturality / linearizedDiagonal_naturality | LinearizedGroupProductNaturality.lean | 検証済み | 最後の μ と対角の自然性 |

| vectorRightMultiplication_mulVec / centralMultiplicationIdeal | Prop414.lean | 検証済み | 非可換右乗法の行列同変性と aI の両側性 |
| squareZeroUnit_conjugation / blockColumn_conjugation | BlockConjugation.lean / BlockColumn.lean | 検証済み | 右乗法の順序を保つ実行列の共役公式 |
| matrix_commute_one_add_blockColumn / blockColumnHom | BlockColumnCommute.lean / BlockColumnGroup.lean | 検証済み | μ のための可換性と実 ψ |
| groupZeroMHomotopy / groupZeroMHomotopy_equivariant | GroupZeroMHomotopy.lean | 検証済み | A.5 の第二因子の0次入力と帰納基底 |

| fixedBlockSubgroup / fixedBlockProduct | FixedBlockGroup.lean | 検証済み | 補助列と可換な固定ブロック群と実 μ |
| blockPatternSubring / triangularBlockGroup | BlockPattern.lean | 検証済み | 三角条件と両側イデアルの係数を持つ実群模型 |
| integerUnitizationIdeal / nonUnitalTriangularBlockGroup | IntegerUnitization.lean | 検証済み | 非単位環の整数単位化による係数模型 |
| blockColumnHom_mem_triangularBlockGroup | BlockPatternColumn.lean | 検証済み | ψ の実列の三角ブロック群への所属 |

| triangularBlockGroupMap | BlockPatternNaturality.lean | 検証済み | 係数イデアルを保つ環準同型による実群の射 |
| matrixInsertionHom / matrixInsertionUnits | MatrixInsertion.lean | 検証済み | 補助座標の実挿入と成分の公式 |
| triangularBlockGroupInsertion | BlockInsertion.lean | 検証済み | 三角条件と係数を保つ実ブロック埋め込み |
| triangularBlockInsertionFixedHom | BlockInsertionFixed.lean | 検証済み | ψ(Q) と可換な固定ブロック群への実埋め込み |

| idealBlockColumnHom / triangularBlockProductHom | IdealColumnGroup.lean / TriangularBlockProduct.lean | 検証済み | 同じ実群 H 内に値を持つ ψ と μ:P×Q→H |
| idealVectorRightHom / lastRightColumnHom | IdealRightColumn.lean | 検証済み | イデアル内の右乗法と最後の列の実準同型 |
| groupConjugationMHomotopy | GroupHomotopyOperations.lean | 検証済み | C(f) と C(u⁻¹fu) の実 m 次比較 |

| auxiliaryBlockUnit_conjugation | TriangularConjugation.lean | 検証済み | 同じ実群 H 内の u⁻¹ψ(v)u=ψ(v)φ(v) |
| triangularInsertion_lastRightColumn | RightColumnInsertion.lean | 検証済み | φ の小さい帰納段階への実因子化 |
| lemma416GroupData / lemma416GroupData_product | Lemma416Data.lean | 検証済み | A.5 の因子データと共役への同定 |
| lemma416HomotopyStep / lemma416Homotopy | Lemma416Homotopy.lean | 非同変版検証済み | μ 版 A.5 と A.6 の連結と相殺による全 m の実帰納比較 |

| oneDifferenceTransform / leftMultiplierGroupHom | OneDifferenceTransform.lean / LeftMultiplier.lean | 検証済み | 非単位三角部分の作用から実群の自己射への持ち上げ |
| firstBlockMatrix / firstBlockMatrix_right_absorbed | FirstBlockMatrix.lean / FirstBlockMultiplication.lean | 検証済み | diag(M,1) の実成分と右吸収 |
| triangularBlockMatrixAction | MatrixBlockAction.lean | 検証済み | 一般の行列モノイドによる実三角ブロック群の作用 |

| idealMatrixAction / idealVectorRightHom_equivariant | IdealMatrixAction.lean | 検証済み | イデアル内の列の左作用と右乗法の可換性 |
| lastRightColumnHom_equivariant / auxiliaryBlockColumnHom_equivariant | IdealColumnEquivariance.lean | 検証済み | 実 φ と ψ の全行列同変性 |
| auxiliaryBlockUnit_fixed | AuxiliaryUnitAction.lean | 検証済み | 共役に使う実 u の行列作用による固定性 |
| triangularBlockInsertion_equivariant | MatrixActionInsertion.lean | 検証済み | μ の第一因子の実埋め込みの全行列同変性 |

| lemma416EquivariantGroupData | Lemma416EquivariantData.lean | 検証済み | 実 μ,α,β と全行列作用の同変な A.5 入力 |
| lemma416Homotopy_equivariant | Lemma416Equivariance.lean | 離散版検証済み | 構成済みの全 m の実区間ホモトピーの全行列同変性 |

| constructionA5_functorial | ConstructionA5Functoriality.lean | 検証済み | 異なる群データ間の μ 版 A.5 の実区間の自然性 |
| auxiliaryBlockUnit_functorial / triangularBlockInsertion_functorial | BlockCoefficientMap.lean | 検証済み | u と実埋め込みの係数自然性 |
| lemma416Homotopy_functorial | Lemma416Functoriality.lean | 離散版検証済み | 全 m の構成済み実帰納ホモトピーの (I,a) の射への自然性 |

| SimplicialIdealData / SimplicialIdealData.vertexElement | SimplicialIdealData.lean | 検証済み | 単体的両側イデアルと零次指定元の自然な移送 |
| diagonalGroupMHomotopy | DiagonalGroupHomotopy.lean | 検証済み | 次数ごとの自然な実比較を既存の対角 C(H) へ制限 |
| lemma416 / simplicialLemma416Homotopy_equivariant | Lemma416.lean | 単体的理想模型で検証済み | 実 m 次比較と全行列同変性を A.4 の入力に束ねる |
| lemma416_relative_zero | Lemma416Relative.lean | 検証済み | 群状モノイドの行列表示に沿った相対半直積ホモロジーの零化 |

## L6a：最小 pro 形式

- 原典は KST §4.1、Definition 4.4、Lemma 4.6。
- 正本 §2.6 の最小定義に従い一般の pro 圏全体は構成しない。
- 対象は任意の圏 C に値を持つ ℕ 添字の塔。
- 遷移射は m ≥ n に対して X_m → X_n。
- 同じ添字の遷移は恒等射。
- 二つの遷移の合成は直接の遷移と一致する。
- レベル射 f は f_n : X_n → Y_n と自然性を持つ。
- pro 同型判定は各 n について m ≥ n と g : Y_m → X_n の存在。
- 第一の三角形は f_m ≫ g = X(m,n)。
- 第二の三角形は g ≫ f_n = Y(m,n)。
- 存在する g の族にレベル射としての整合性を要求しない。
- 定数塔の判定が通常の同型と一致することを示す。
- 恒等射が pro 同型であることを示す。
- 合成が pro 同型であることを示す。
- 関手による像は遷移射と自然性を写して定義する。
- L3 は加法性を必要としない一般の関手の補題を先に証明する。
- 有理テンソル関手への適用と完全性の使用を区別する。
- L4 は (m,n) ≤ (max m n,max m n) の明示的証人を使う。
- 単調な共終再添字についても比較射を構成する。
- pro-零性は各 n である m ≥ n の遷移射が零になること。
- 零対象への pro 同型との一致を検証する。
- pro-cartesian はレベルごとに形成した hofib 間の射の pro 同値。
- レベルごとの各射を同値と要求する強すぎる条件は採らない。
- π_n による同値判定は K-L9 の明示的な入力から構成する。
- L1 は fiber 列から得る次数ごとの完全列を自然性込みで塔へ持ち上げる。
- L1 の fiber の存在自体は本レーンで仮定し直さない。
- L2 はレベル完全列を diagram chase し eventual な上界をまとめる。
- L2 では外側四つの同型から中央の eventual 単射・全射を導く。
- レベルごとの同型だけの五項補題で代替しない。
- 保存単位では Pro の対象ビルドと宣言ごとの公理監査を実行する。

## L6b：Koszul と平坦底変換

- 原典は [KST v4](https://arxiv.org/pdf/1611.08466v4) p.23、Lemma 4.9・Lemma 4.10。
- Lemma 4.9 の既存の独立な証明は標的項の有限性・Koszul 座標の零作用・Artin–Rees・冪遷移のイデアル深度を使う。新しい cone 経路は列長帰納法と各段の Artin–Rees による冪核消滅を使う。
- 係数付き複体は既存 koszulComplex に tensor を施したものであり、既存の反復錐モデルとの自然同型を用いて零化イデアルを移す。
- 既存の koszulComplex の次数規約を先に確認する。
- ホモロジーの次数変換を docstring に明記する。
- 有限生成加群と Noether 仮定の使用箇所を分ける。
- Artin–Rees は Ideal.exists_pow_inf_eq_pow_smul を用いる。
- 正次数の Koszul ホモロジーの遷移を構成する。
- 零次数の比較は商加群との同定を使う。
- 有限生成された境界とサイクルへの Artin–Rees を用いる。
- 各次数の消滅指数は固定された標的レベルに依存してよい。
- 複数次数を一様に扱う必要があれば有限性を証明する。
- 係数 H の平坦性は tensor の完全性として使う。
- π_*(B ⊗ H) の比較は複体のホモロジー底変換から得る。
- a(n)M の像と tensor の比較を別補題にする。
- pro-零性の保存には零射保存と関手性を使う。
- 非可換 H の Noether 性を仮定しない。
- 中心的な A 作用だけが必要であることを型で示す。
- 既存 CommutativeAlgebra のソースは変更しない。
- 既存 HomologicalAlgebra も読み取り専用とする。
- 対象 import 閉包のビルド失敗は回避せず報告する。
- 完了時に主要宣言の型と仮定を表へ反映する。

## L6c：群状単体モノイドのホモロジー

- 原典は KST Appendix A。
- 対象は Prop A.1、Lemma A.2・A.4。
- 構成は Construction A.5・A.6。
- G ⋉ H の半直積の作用と積の順序を固定する。
- 群状条件は π₀ が群になる条件として明示する。
- 群ホモロジー H_* の定義自体は K-L2 から借りる。
- bar 構成への比較射は自然性を含めて記述する。
- 相対ホモロジーは絶対ホモロジーと混同しない。
- 次数零の補題と正次数の補題を分ける。
- augmentation とその切断を構成する。
- 有限段階から安定化への移行を明示する。
- filtered 余極限の完全性が必要な場所を記録する。
- 単体次数とホモロジー次数を別の引数とする。
- 行列サイズ n と塔の添字を区別する。
- 自然変換から誘導される chain homotopy を証明する。
- Prop 4.14 が使う相対零化補題まで進める。
- Suslin–Wodzicki の議論を引用定理として登録しない。
- 原典が arguing as in と書く箇所も具体的に証明する。
- 未到着の界面を本レーンの結論で埋めない。
- 完了時に対象ビルドと公理監査を行う。

### L6c の実装する最小模型

- 半直積は G ⋉ H の順とし、(g,h)(g′,h′)=(gg′,h·g(h′))。
- G はモノイド、H は群。作用は群の準同型によるが、各作用が次数ごとに可逆とは仮定しない。
- Mathlib の群同士の `SemidirectProduct`（自己同型への作用）をそのまま使うと仮定が強すぎる。
- 本レーン内に一般のモノイド作用による半直積を構成し、分裂包含・射影・核側の包含を定義する。
- それを次数ごとに適用し、単体的半直積とその自然な写像を作る。
- Lemma A.2 の ψ(g,h)=(g,g(h)) は台単体集合の写像であり、モノイド準同型とは表示しない。
- 群状性は K-L2 の `SimplicialMonoid.IsGrouplike`（π₀ が群）を使う。
- Prop A.1 の φ は二重単体的作用 bar と半直積 bar の比較。各座標に右側の G の積を作用させる。
- H_* 自体は K-L2 が所有する。未供給のモデル同定・ホモトピー不変性は明示入力にする。
- Prop A.1・Lemma A.2・A.4 の結論を仮定する構造体は導入しない。
- Lemma A.2 の証明経路の差分：原典の fibration と頂点ファイバーの比較に代え、標準単体上の収縮、骨格の pushout、順次余極限で作用の可逆性を貼り合わせる。
- この経路では K-L2 の作用の族の降下と共有 `CellularNaturalComparison` の機構を、正則作用から一般の作用へ適用する。
- 作用する各頂点の可逆性は証明済み `grouplikeActionIso` で供給する。原典 Lemma A.2 の結論を仮定しない。
- 最後に台単体集合 G×H と半直積の台の同型で、族の作用を ψ へ移す。
- A.4 の相対項は分裂包含の余核。絶対項の零性とは区別する。
- A.5 は m と m′ の和に1を加えた範囲、A.6 は u⁻¹hu の向きの共役を扱う。
- Appendix A の原典番号と構成の自然性を各宣言に記す。
- 全体ビルド（L6b 区切り）はレーン外の CoherentFlagIso のエラーと ReducedClosedSubscheme.olean 欠落で失敗。
- L6b の対象 import 閉包のビルドと254宣言の公理監査は成功。これらレーン外の依存は修復しない。

## L6d：非可換再記述の紙の検証

- 実装前の紙の検証項目は正本 §10-1。
- 原典は KST Proposition 4.14、Claim 4.15、Lemma 4.16。
- I は結合的で非単位的でもよい単体環。
- a は中心的で各単体次数で乗法が単射。
- φ は右乗法 v ↦ va とする。
- M_{n,n}(I) の作用は左からの行列積である。
- (Mv)a = M(va) は結合律で成り立つ。
- 中心性は aI が両側イデアルであることにも用いる。
- u⁻¹ψ(v)u のブロック行列計算を記録してから実装する。
- 単位化した環における逆行列の具体式を確かめる。
- φ と ψ の定義域・値域を明記する。
- 安定 GL の共役作用を誘導する。
- 原典の可換環という仮定と本実装の差分を明記する。
- 目標は像上での GL(ℤ) の作用の自明性。
- 全ホモロジー上の自明性を主張しない。
- 相対ホモロジーの零化に帰着する。
- Lemma A.4 の適用条件を照合する。
- 紙の検証の未解決点があれば設計変更として報告する。
- 検証結果の報告後は承認待ちせず進む。
- 現時点で紙の検証完了とは扱わない。

## L6e：pro-Whitehead

- 原典は KST Lemma 4.2、Proposition 4.3。
- 参照は Bousfield–Kan III.5.4(ii)・III.6.6。
- 紙の検証項目は正本 §10-4。
- 適用対象は連結 H 空間なので simple 空間版を目標とする。
- π₁ が可換で高次 π への作用が自明という条件を明示する。
- 連結性だけで simple 性を置き換えない。
- π_* pro 同型から H_* pro 同型を導く易しい向きを先に扱う。
- 逆向きには Postnikov 段階と相対 Hurewicz を整理する。
- 次数ごとの指数と全次数一様の指数を混同しない。
- BK の完備化の主張から必要な部分を検証する。
- π_n の具体的構成は K-L9 の責任範囲。
- H_n の具体的構成は K-L2 の責任範囲。
- 本レーンは借用界面への明示的な引数で先へ進む。
- 借用する法則と本レーンが示す結論を区別する。
- Prop 4.8 の適用を見据えた自然性を含める。
- Claim 4.17 の fiber に simple 性がある理由を記録する。
- 基点変更の扱いを曖昧にしない。
- 群とアーベル群の境界次数を区別する。
- 紙の検証を報告してから Lean 実装に入る。
- 現時点では未着手。

## L6f：局所係数つき相対 Serre SS

- 原典は Claim 4.18。
- 比較資料は Geisser–Hesselholt 2006 Lemma 1.2。
- Suslin–Wodzicki Corollary 1.7 との対応も調べる。
- 着手前に必要最小限の形をこの節へ書いて報告する。
- 現時点ではその最小形の検証を完了していない。
- 一般の Serre SS 全体を無条件の仮定に置かない。
- 相対 pair と基底の基本群の作用を明示する。
- E₂ 頁は局所係数の群ホモロジーとして記述する。
- 収束は各総次数の有限濾過として記述する。
- pro-自明な作用とレベルごとの自明な作用を区別する。
- Claim 4.19 から必要な eventual 零化を取り出す。
- 次数ごとに有限個の微分の指数をまとめる。
- 濾過の graded の pro-同型から全体へ移る補題を証明する。
- edge map が目的の比較射と一致することを示す。
- 係数の自明化が自然であることを検証する。
- π₁ の作用を落とした定数係数 SS で代替しない。
- ホモトピー fiber と通常の fiber の比較を明示する。
- 単体モデルの置換に関する自然性を記録する。
- 対象ビルドと公理監査を行う。
- 完了時に入力と結論を主要宣言の表に反映する。

## L6g：主定理と系

- 原典は KST Theorem 4.11、Corollary 4.12・4.13。
- 基底 r = 1 と帰納段階を分離する。
- 非零因子化は正本 §10-2 の紙の検証を先行する。
- R[t] 上の半自由置換を各段階で両立させる。
- 低次数 K は K0・K2 の界面を明示的に受け取る。
- Weibel III.4.3 の負の K の切除への依存を明記する。
- 高次数 K は BĜL⁺ と pro-Whitehead に帰着する。
- Claim 4.17 はホモロジーの pro 同型の主張。
- Claim 4.18 は L6f の結論を用いる。
- Claim 4.19 は Prop 4.14 と ι/σ トリックから導く。
- 帰納段階は定数でない pro-系で記述する。
- Lemma 4.10 の一様性が必要な箇所を点検する。
- Cor 4.12・4.13 は正本 §10-3 の紙の再構成を先行する。
- I の冪と生成元ごとの冪の共終性を明示する。
- Koszul の塔と商環の塔の比較は Prop 4.8 を通す。
- Cor 4.13 の正次数 π の pro-零性を確認する。
- 原典と異なる再構成であることを docstring に書く。
- 主定理の K への依存を循環させない。
- 工程の区切りで全体ビルドを実行する。
- 全工程の終了以外に完了とは報告しない。

## 保存・検証・統合の規約

- 各保存単位で lake build SerrePositivity.KST.ProExcision を実行する。
- 監査は lake env lean scripts/audit_kst_pro_excision.lean。
- 公理出力に sorryAx または追加公理があれば未検証とする。
- 全体ビルドは工程の区切りで実行する。
- ビルドは set -o pipefail を指定し終了コードを確認する。
- 新規・変更宣言に日本語 docstring を付ける。
- docstring は概要／方針／規約／使われ方を含む。
- 数学的法則を持つ構造体はその法則の意味を記す。
- 実施記録はコミットメッセージに置く。
- git commit --only で所有する検証済みファイルだけを含める。
- amend・rebase・reset を使わない。
- ルートの既存変更を自分のコミットに巻き込まない。
- 共有ファイルのステージ差分を確認する。
- 他レーンの import 閉包が壊れたら回避策を作らない。
- その場合は具体的なファイルとエラーを報告する。
- 各工程の完了時に現在地と主要宣言を更新する。
- 各工程の報告後は次の工程に進む。
- 設計変更が必要なら差分と理由を具体的に提案する。
- 未証明の仮定を供給済みと表示しない。
- 本レーンの完成とリポジトリ全体の完成を区別する。


## L6b の反復 cone 経路（再開時の設計）

- ユーザー指定：Kos(a₁,…,aᵣ;K) = Cone(aᵣ : Kos(a₁,…,aᵣ₋₁;K) → Kos(a₁,…,aᵣ₋₁;K))。
- 実際の既存定義 `koszulComplexOn` と `scalarConeFunctor` を使う。
- 長完全列は既存 `ConeLES` の `Cone.exact₁`・`exact₂`・`exact₃` を用いる。
- Lemma 4.9：列長で帰納し、正次数の両側を帰納仮定で消す。
- 境界次数では固定された短い列の零次ホモロジーの有限性を使い、末尾変数の冪核を消す。
- 冪核の遷移は aᵐ⁻ⁿ 倍。反復 cone の本証明では既存 `exists_pow_deep_image_killed` による Artin–Rees を各段へ適用する。
- 一般の Noether 加群の核安定化による一変数比較も、独立な補助補題として保存する。
- 各変数の冪指数は独立に扱い、最後に対角の共終性を使う。
- Lemma 4.10：長完全列から Hⁱ(K)/aⁿ → Hⁱ(Cone(aⁿ,K)) を作る。
- この射は単射であり、その余核は Hⁱ⁺¹(K) 上の aⁿ 倍の核へ入る。
- この核の pro-零性により一変数比較は pro 同型。
- 一変数比較を列長で反復する際、自然性・商への降下・対角への移行を明示する。
- 係数ホモロジーの有限生成性は必要な次数ごとに仮定する。係数複体の項の有限性は要求しない。
- 原典 Lemma 4.10 のスペクトル系列証明とは異なる経路であることを宣言の docstring に明記する。
- 保存済みの区間自然性・核模型は通常の短複体や長完全列として再利用できる部分だけ残す。
- スペクトル対象・頁・収束を前提とする部分は新経路の import と監査から除く。
- この変更はユーザーが明示した設計であり、承認待ちを設けない。
- L6b 完了後は L6c へ進む。

## Mathlib 更新時の再確認

- 固定版：Lean `v4.35.0-rc4`。Mathlib revision は `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`（`lake-manifest.json`）。
- 公開 `SpectralSequence.homologyData` と公開ラッパーの私有証明定数参照に起因する kernel エラーを再確認する。[^mathlib-homologydata]
- 本レーンでは Mathlib 自体を修復せず、版も上げない。
- 版更新時は独立 probe だけを再実行し、成功・失敗を記録する。cone 証明を頁の実装に戻す必要はない。

[^mathlib-homologydata]: 最小再現は `/tmp/kst-l6-public-data-probe.lean`、出力は `/tmp/kst-l6-public-data-probe.log`。公開 `X.spectralSequenceHomologyData ...` の `.left` を `Nonempty` に包むだけで `(kernel) unknown constant '_private.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence.0._proof_27'`。失敗した宣言は保存 Lean ファイルに含めていない。再現コードは次のとおり（旧レーン import を Mathlib 直接 import へ置換して独立実行する）。

```lean
module
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
variable {C J κ : Type} [Category C] [Abelian C] [Preorder J]
variable {c : ℤ → ComplexShape κ} {r₀ : ℤ}
example (data : Abelian.SpectralObject.SpectralSequenceDataCore J c r₀)
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ)
    (X : Abelian.SpectralObject C J) [X.HasSpectralSequence data] :
    Nonempty ((((X.spectralSequence data).page r hr).sc pq).LeftHomologyData) := by
  exact ⟨(X.spectralSequenceHomologyData data r r' hrr' hr
    ((c r).prev pq) pq ((c r).next pq) rfl rfl
    (data.i₀ r' pq) (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq)
    (data.i₃ r pq) (data.i₃ r' pq) rfl rfl rfl rfl rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl (by omega) rfl).left⟩
```

## 設計確認：Construction A.5 の augmentation 補正

- 原典の再確認：[KST v4 PDF](https://arxiv.org/pdf/1611.08466v4)、印刷 p.45–46（PDF 0-based 44–45）。HTML 変換だけでなく PDF 抽出でも同じ式を確認。
- 原典の C(H)=ℤBH は非被約。Definition A.3 の m-ホモトピーは次数 ≤m の両端を指定し、零次も含む。
- A.5 の右辺 C(φ)+C(φ′) を非被約鎖複体の通常の加法として読むと、零次 augmentation が一致しない。
- 検証例：T=H={1}、φ=φ′=e=id、m=m′=0。入力のホモトピーは恒等同士。
- 要求される出力の左辺は H₀=ℤ 上で id、右辺は 2·id。次数 ≤1 のホモトピーがあれば H₀ 上で一致するため矛盾する。
- 自明群の正規化された零次の一項模型 ℤ[0] について、`no_homotopy_identity_doubleIdentity` が同じ障害を Lean で確認する。
- 独立 probe：`/tmp/kst-l6-augmentation-probe.lean`、出力 `/tmp/kst-l6-augmentation-probe.log`。
- 原典の記号が被約写像の和を省略して表している可能性はあるが、その規約は Lean の通常の加法とは区別する必要がある。
- 採用済みの実装文言（2026-10-18 のユーザー指示）：非被約 C(H) を保ち、**A.5 の右辺の augmentation 補正**として **C(φ)+C(φ′)−C(e)** とする。
- テンソル側の対応する文言は f⊗g と f⊗e+e⊗g−e⊗e の比較。
- 証明方針：正規化で (f−e)⊗(g−e) を考え、二つの低次数消滅の和の範囲で零化。AW・shuffle の標準ホモトピーを合成する。
- Lemma 4.16 では C(ψ)≃C(ψ)+C(φ)−C(e) から差を取り、必要な C(φ)≃C(e) が得られる。
- 被約複体 ker ε へ移す別案は採用しない。H_*・相対項との界面を増やさず、非被約模型を維持する。
- 設計確認は採用済み。低次数テンソル消滅、AW・shuffle の比較、m-ホモトピーへの移送の順で実装する。正本 §12 への追記はユーザーが担当し、本レーンから編集しない。
- 他レーンの計画・ソースは変更していない。依存側の修復や追加公理は導入しない。

## C(H) の区間界面

- C(H)=ℤBH は `linearizedSpace (nerve (SingleObj H))` の非被約自由整数加群模型。
- `integerLinearization` は任意の宇宙の集合を有限台整数関数へ送る。H_* は定義しない。
- 固定版 Mathlib の ModuleCat のモノイド構造は環と加群の宇宙を同一に限定するため、整数加群のテンソルは本レーンの `integerTensor`、`simplicialIntegerTensor` で通常の TensorProduct ℤ を明示的に束ねる。
- `linearizedTensorIso` は各次数の有限台関数の標準テンソル同型と、その自然性から構成する。
- `linearizedEndpoint₀`、`linearizedEndpoint₁` は幾何的端点の自由化をこの同型の逆で移したもの。
- `LinearizedHomotopy` は全次数の両端条件、`LinearizedMHomotopy` は次数 ≤m の両端条件。後者の区間写像も全次数の単体的射として保持する。
- Definition A.3 の G 同変性はこれらの非同変な基礎型と別の条件であり、証明済みと表示しない。
- A.5 の右辺の augmentation 補正の相殺は、区間写像 H から定数な ψ+φ の区間写像との差を作る構成である。

## Prop A.1 の比較写像の圏論的な座標

- 作用圏の射は x→y に対し g•x=y とし、合成ラベルは後のラベルを左から掛ける。
- nerve の単体 p と BH の各頂点 x_i に対し、i 番目の比較ラベルを (g_i, x_{i+1} の i→i+1 のラベル) とする。
- これは Fin(n+1)×作用圏から半直積の一対象圏への transport 関手で構成できる。
- transport は (i,x)→(j,y) のラベル g を (g,y(i→j)) へ送る。
- 合成の検証は z=g'•y と z(i→k)=z(j→k)·z(i→j) による。半直積の積は原典の (gg′,h·g(h′)) を維持する。
- 本実装の nerve の射列は原典の語の座標の逆順であるため、作用する積は prefix g_i…g_0 と表示される。原典の逆順の語の添字へ戻すと右側の suffix の積になる。比較写像の docstring にこの規約差を明記する。
- 実際の単体的比較の構成、原典の二重単体的な行の分解、各行の局所化同値、対角の局所化同値の順に確認する。最終の H_* の模型同定は所有レーンの界面。

## Prop A.1 の各行の同値性の分解

- 各行の比較を G^r×H^r 上で読むと、h_j に prefix g_j…g_0 を作用させる。
- i=0,…,r−1 の順に、同じ g_i を座標 j≥i の H 成分だけへ作用させる写像を合成すれば、この prefix 比較になる。
- `maskedTupleAction` は G が H^r の指定された座標だけに作用する通常の単体的モノイド作用。
- 各段は `actionFamily_localized_isIso` を、パラメータ G^r とその第 i 座標への射影に適用したもの。
- したがって G^r の群状性を別に仮定する必要はない。必要なのは元の G の群状性だけ。
- 完全な行の比較との座標等式を証明し、有限合成の可逆性から行の局所化同値を得る。
- 対角への移送には既存 `BisimplicialModel.localized_diagonal_map` を、二重単体的比較を flip して適用する。

## Lemma A.4 の次の持ち上げ

- m 次ホモトピーの区間写像は線形であり、基底単体を一つの基底単体へ送るとは限らない。
- そのため幾何的な SSet の射として持ち上げず、作用 bar の自由整数加群へ線形に持ち上げる。
- 作用 bar の単体を始点と G の語で分解し、G の語を固定した係数の基底包含を使う。
- 任意の単体射に沿う始点の変化は、元の語の始点から像の最初の頂点までの prefix の作用。
- この式と区間写像の G 同変性から、線形に持ち上げた区間写像の単体的自然性を証明する。
- その後、既存の `LinearizedMHomotopy.homologyMap_eq`、A.1 の自然性、相対余核の自明射零化を合成する。
- bar への線形持ち上げの存在や Lemma A.4 の結論を、H_* の界面の仮定に含めない。

## 設計確認：A.5 の非可換標的とホモトピーの値域

### 判明した条件の差

- augmentation 補正 C(φ)+C(φ′)−C(e) は採用済みであり、変更しない。
- しかし「φ と φ′ の像が可換」だけでは、入力の二つの線形ホモトピーを群の積へ送れない。ホモトピーの値が像の部分群内に留まることは、この条件からは従わない。
- 原典の「記号を簡単にするため H を可換とする」という移行は、この点では追加の仮定を使っている。
- 次の紙の反例は m=1、m′=0、要求される範囲は次数 ≤2。零次 augmentation の障害とは独立。

### 紙の反例と有限の Lean 検証

- H=D₈=⟨r,s | r⁴=s²=1, srs=r⁻¹⟩ とし、a=r²、b=s。
- a と b は可換で、a=r s r⁻¹ s は commutator。
- T=ℤ²、φ(i,j)=a^i、φ′(i,j)=b^j。像は可換し、二つの準同型の積も準同型。
- φ は homologically 1-constant。非被約 bar の一次で、[a]−[1] を埋める二次鎖 u を下で明示する。
- 一次の鎖ホモトピーを [i,j] に対し i が奇数なら u、偶数なら0と定める。零次の鎖ホモトピーは0。他のホモトピー成分を0へ拡張し、終点の鎖写像を f−dS−Sd とすると、零次と一次は C(e) と一致する。
- この通常の鎖ホモトピーを Dold–Kan のホモトピー対応で単体的整数加群の区間ホモトピーに戻すと、Definition A.3 の 1 次入力を得る。この Dold–Kan による入力実現は紙の議論であり、保存 Lean ファイルではまだ形式化していない。
- φ′ の0次ホモトピーは C(e) の定数区間写像でよい。分類空間の零次では C(φ′)=C(e)。
- T の二つの生成元が作る二次サイクルは、φ·φ′ で z=[a|b]−[b|a] へ送られる。
- D₁₆→D₈ の中央拡大の正規化された ℤ/2 値二次 cocycle c は c(a,b)−c(b,a)=1。
- 一方、φ、φ′、e のそれぞれの像では、一方の入力が単位となるためこの評価は0。したがって補正した通常和との二次ホモロジー写像は一致しない。
- よって上の入力から、一般の非可換な H に対する2次ホモトピーは得られない。
- `CommutingImageObstruction.lean` が形式的に検証する範囲：全512組の cocycle 則、正規化、a と b の可換性、a の commutator 表示、z の二次境界の零性、全三次境界の c 評価の零性、z の c 評価が1であること、z が三次境界でないこと、および [a]−[1] の明示的な境界。
- u=[r|r⁻¹]+[s|s]−[r|s]−[rs|r⁻¹]−[rsr⁻¹|s]+[1|1] とすると ∂u=[a]−[1]。この等式も同ファイルで kernel 検証。
- これは H_* の定義を新設する証明ではなく、自由整数加群の二次・三次 bar 鎖の有限な検証。
- 独立 probe は `/tmp/kst-l6-dihedral-cocycle-probe.lean`。
- 対応する二次群ホモロジーの非零類は、Domínguez–Segovia, *Extending free actions of finite groups on surfaces*, Topology Appl. 305 (2022), 107898, Corollary 17 の「180度回転と反射のトーラス」にも一致する：[原論文](https://doi.org/10.1016/j.topol.2021.107898)。本文の反例の推論は上記の独立した bar 計算による。

### 採用済み A.5 の正確な形（正本 §13-14）

- 群 P,Q,H、群準同型 μ:P×Q→H、α:T→P、β:T→Q を明示的なデータにする。
- m 次入力は C(α) と C(e_P) の間、m′ 次入力は C(β) と C(e_Q) の間のホモトピーとして与える。H に移した後だけのホモトピーは入力にしない。
- μ の両因子への制限から φ=μ(α,1)、φ′=μ(1,β) を作る。
- 結論は (m+m′+1) 次の C(φ·φ′)≃C(φ)+C(φ′)−C(e_H)。
- 証明は採用済みのとおり、厳密化・正規化・差のテンソルの消滅・AW/shuffle の標準比較を使い、最後に実際の群準同型 μ を適用する。
- 外部 G の同変性は P,Q,H,μ,α,β と入力ホモトピーに持たせる。原典の一般文言との差として docstring と計画に明記する。
- 原典の一般文言からの仮定の変更であり、ユーザーがこの形を採用済み。追加の承認待ちは置かず、実装する。

### Lemma 4.16 での候補と §10-1 の紙の確認

- P=T_{n,m−1}(I)⋉M_{n+m−1,1}(I)、Q=M_{n,1}(I) の加法群、H=T_{n,m}(I)⋉M_{n+m,1}(I)。
- P の帰納段階の埋め込みと Q の ψ による埋め込みを使い、μ(p,v)=p·ψ(v) とする。
- 座標を n、m−1、1、1 に分割すると、P の元はブロック行列
  [[1,X,0,y],[0,U,0,z],[0,0,1,0],[0,0,0,1]]、ψ(v) は [[1,0,v,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]。
- 両積の非自明な交差項は、P が first n 列上で恒等であることと、追加した最後の補助座標の列・行の零性により一致する。この計算は可換な I を要求しない。
- したがって P の全体と ψ(Q) は可換であり、μ は群準同型になる候補。
- α は原典が用いる φ の小さい帰納段階への因子化、β は Q 上の恒等写像。α の (m−1) 次ホモトピーは帰納法で C(P) 内にあり、β は0次の定数区間写像を持つ。
- 採用済み μ 版 A.5 はこの m−1 と0から必要な m 次比較を与える。
- M_{n,n}(I) の作用についても、first n 行の線形作用がこのブロック分解と μ に可換であることを別途実装前に確認する。右乗法 a と aI の両側性は従来の §10-1 の確認を維持する。
- この候補は紙の設計確認段階であり、L6d の非可換群・ブロック行列の実装はまだ行っていない。正本 §12 は本レーンから編集しない。


## A.5 の標準比較ホモトピーの具体化

- AW と shuffle の実鎖写像と自然性、両者の Moore 複体への移送まで検証した。
- 対角での合成 AW→shuffle と恒等の比較は、標準の普遍単体モデルを使う再帰的構成で実装する。
- 二つの単体射 [r]→[N] の対の自由整数加群をモデルとし、両方の列に先頭頂点0を付加する extra degeneracy で収縮する。
- 普遍 N 単体における恒等と合成の差から、既に作った低次のホモトピーの境界を差し引いてサイクルを作り、この収縮で埋める。
- 差の零次は実 AW/shuffle の零次の計算により零。正次数ではサイクル性を両鎖写像の微分可換性と帰納仮定から示す。
- 任意の二つの単体的整数加群の元に、この有限な普遍鎖を評価する。評価は二変数で整数双線形なのでテンソル写像になり、入力の射に自然となる。
- この構成は AW/shuffle の標準鎖ホモトピーを引用せずに実現する方針であり、比較の存在や結論を追加の構造体仮定にはしない。
- Moore 正規化の射影・包含に関する標準の鎖ホモトピーも合成し、最後に単体的区間ホモトピーへ復元する工程は未完。

- 普遍模型による再帰的構成は実装済み。`ezUniversalHomotopyChain_boundary_succ` が全次数で充填の境界公式を証明し、`ezHomotopy` が恒等と実 AW→shuffle の標準鎖ホモトピーを与える。
- `ezHomotopyApp_naturality` により全次数の成分は両入力に自然。標準比較の存在・同変性を仮定として受け取っていない。
- 残る正規化への移送には、両因子の Moore 射影・包含の合成と恒等の標準鎖ホモトピーのテンソルを合成する。単体的区間への復元と最終 μ 適用は未完。

- `normalizedEZHomotopy` により恒等と正規化 AW→shuffle の間の実鎖ホモトピーまで実装済み。両因子の Moore 収縮を `chainIntegerTensorHomotopy` で実際にテンソルへ移して合成する。
- `moorePInftyHomotopy_naturality` は Mathlib の収縮の各成分の自然性を有限段階の帰納法で証明する。テンソルへ移した収縮と正規化 EZ ホモトピー全体の自然性も `normalizedEZHomotopy_square` で接続済み。

- `normalizedEZHomotopy_square` は両入力の任意の射に関する正規化比較ホモトピーの成分の自然性。外部群の作用の各射へ適用することで、採用済み A.5 に必要な比較の同変性を導く。
- L6c の次の主工程は正規化した低次補正式と単体的区間の間の復元。Dold–Kan の充満忠実性を使い、区間の正規化から鎖ホモトピーを実際の単体的区間写像へ戻す。A.5 の完成と表示するのは μ と T の対角への移送・両端・同変性が揃ってから。


## 単体的区間への復元の具体的な工程

- Dold–Kan の充満忠実性に渡す前に、実鎖写像 N(C(X)⊗ℤΔ¹)→N(D) を構成する。
- 中間の整数鎖区間 I は I₀=ℤ{v₀,v₁}、I₁=ℤ{e}、Iₙ=0 (n≥2)、d(e)=v₁−v₀。
- 単体的 Δ¹ の交代面複体から I への比較は、零次で頂点を同定し、一次の単体 f:[1]→[1] を (f(1)−f(0))e に送り、高次数を零にする。
- 二次の微分との可換性は (f(2)−f(1))−(f(2)−f(0))+(f(1)−f(0))=0 の望遠鏡相殺。一次では四通りの頂点の値から終点−始点の公式を検証する。
- 鎖ホモトピー H:f≃g に対し、N(C(X))⊗I から N(D) への評価は v₀ で f、v₁ で g、第一因子の次数 p と辺 e の成分で (−1)^(p+1)H_p とする。
- この符号で、水平微分の符号と d(e)=v₁−v₀ が H の式 f−g=dH+Hd に一致することを紙で確認した。
- 実 AW により K(C(X)⊗ℤΔ¹)→K(C(X))⊗K(ℤΔ¹) とし、第一因子の Moore 射影と区間の比較を合成する。始域には N からの包含を置く。
- 区間の両端では、AW のうち区間次数0の項だけが残るため、第一因子の包含・射影の分裂を使って f と g に一致する。
- 最後に N の充満性で実単体的な区間射へ戻し、忠実性で両端と入力射に関する自然性を検証する。
- 低次数での正規化した射の一致を単体的各次数の一致へ戻す補題も必要。退化分解が次数 n 以下の正規化成分だけを使うことを明示的に証明する。
- この復元はこれから実装する工程であり、最終 A.5 の完成とはまだ表示しない。

- 復元の基礎部：`integerChainInterval` の実二項複体、辺の境界、重みの一次・二次の公式を実装済み。
- `normalizedMapReconstruct` は Mathlib の Dold–Kan の実同値の充満性から鎖写像を実単体的射へ戻す。`normalizedMapReconstruct_map`、`normalizedMap_eq_of_map_eq`、`normalizedMapReconstruct_comp` も証明済み。
- ℤΔ¹ からこの鎖区間への実鎖写像は `integerIntervalComparison` で実装済み。ホモトピーによる全テンソルの評価、両端の公式は未完であり、A.5 の区間復元完了とは表示しない。

- `integerTensorFreeDesc` は第一因子の自由性を要求しないテンソル射を、第二因子の各自由基底に指定した写像から構成する。整数の加法作用と ModuleCat の ℤ 作用の一致は `map_intCast_smul` により証明する。
- `chainHomotopyIntervalBidegree` は頂点上の f,g と辺上の (−1)^(p+1)H_p を実成分として構成済み。`chainHomotopyIntervalApp` は全複体の実余積からの降下写像。
- 次は区間次数 q=0,1,≥2 に分けて微分可換性を証明する。q≥2 の始域の自明性は `integerTensor_punit_hom_zero` により検証済み。まだ鎖区間の評価を実鎖写像に束ねたとは表示しない。

- `chainHomotopyInterval_comm` は q=0,1,≥2 の三場合を合成し、全テンソル区間の実評価の微分可換性を証明する。`chainHomotopyInterval` で実鎖写像へ束ねた。
- 頂点では端点写像の鎖写像性、辺では符号付きホモトピー等式、q≥2 では第二因子の自明性を使う。ホモトピーの評価の鎖写像性を仮定として受け取っていない。
- 次は実単体的区間からの AW と `integerIntervalComparison` の合成、両端・自然性、Dold–Kan による実区間射への復元。

- `chainHomotopyCylinderCore` は AW・区間比較・評価による正規化前の区間からの実鎖写像。`chainHomotopyCylinderMap` は始域の Moore 包含を合成する。
- `chainHomotopyCylinderReconstruct` はこの実鎖写像から Dold–Kan の前像により実単体的区間射を構成する。両端の証明も完成し、`LinearizedHomotopy.ofNormalizedChainHomotopy` へ束ねた。
- `cylinderAWTerm_constant_of_lt` は最後より前の AW 項が端点の定数単体上で零になることを実写像で証明する。最後の項と全和の計算も `CylinderAWEndpoints.lean` で検証済み。
- `chainHomotopyInterval_naturality` により鎖区間評価の実鎖写像自体の自然性は検証済み。復元の同変性は AW・Moore 射影・Dold–Kan の忠実性を通して次に接続する。

- `LinearizedHomotopy.ofNormalizedChainHomotopy` は正規化鎖ホモトピーを両端の等式を持つ非被約な実区間ホモトピーへ復元する。AW・区間比較・評価・Dold–Kan の充満忠実性を実際に合成した。
- `chainHomotopyCylinderReconstruct_naturality` は端点の可換性と構成済み鎖ホモトピーの自然性から復元した射の自然性を証明する。外部群の各作用射へ適用できる。
- 次は低次数の正規化の反映：PInfty と補射影 Q の退化分解から、正規化した射の次数≤m の一致を元の単体的射の同じ範囲の一致へ戻す。
- その後、正規化した差のテンソルの補正式・比較ホモトピー・復元を合成し、最後に群準同型 μ と T の対角を適用して採用済み A.5 を完成させる。

- `normalizedMap_eq_low_reflect` は P の正規化部分の一致と Q の退化分解を次数帰納法で合成し、正規化の低次数の一致を実射の低次数の一致へ反映する。
- `linearizedMHomotopyOfChainComparisons` は N(f)≃R と N(g)≃S、R=S (次数≤m) から実 m 次ホモトピーを構成する。全ホモトピーの差を使い、補正終点 R−S+N(g) を復元するので、単なるホモロジー写像の一致を区間ホモトピーの存在として仮定していない。
- 次は一般のテンソルの augmentation 補正式の実 m 次ホモトピーを、この復元と正規化 EZ 比較・厳密化の比較から合成する。

- `linearizedTensorAugmentationMHomotopy` は一般の非同変なテンソル補正式の実 (m+m′+1) 次ホモトピーを構成済み。前合成 a と後合成 b は明示的な実単体的射。
- 実際に使う二つの全比較の比較先の低次一致は `normalizedStrictifiedTensor_eq_low` により証明する。比較ホモトピーの存在を追加仮定に包んでいない。
- `groupProductNerve` は ComposableArrows の点ごとの関手の積の後に μ の関手を適用する。P,Q,H の可換性を仮定しない。
- `linearizedGroupProduct_comp` は対角と α,β,μ の実合成を C(μ∘(α,β)) へ同定する。最後に μ を適用する採用済み設計を具体化した。
- 次はこの一般テンソル版を μ 版 A.5 の三つの補正項へ特殊化し、構成の自然性から外部 G 同変性を接続する。非同変版だけで L6c 完了とは表示しない。


### A.5 の自然性の接続（2026-10-19）

- μ 版の非同変な実ホモトピー `constructionA5` を構成し、対象ビルド・公理監査に追加した。
- `ChainHomotopySquare` に和・整数倍・恒等比較を加え、一般の二つの鎖ホモトピーの全テンソルの自然性を証明した。
- 標準線形区間の組合せ的ホモトピー、交代面複体への移送、Moore 正規化、厳密化比較の順に自然性を証明した。
- 厳密化比較の端点の同定は等式輸送に代えて零ホモトピーとの連結で明示した。数学的な構成は同じで、自然性の証明で端点同定が零成分であることを直接使える。
- `linearizedMHomotopyOfChainComparisons_naturality` により、二つの低次一致する全鎖比較の差からの実区間復元が自然であることを証明した。
- `normalizedTensorComparisonWithHomotopies_square` と `normalizedTensorAugmentationComparison_square` により、AW・shuffle で挟んだ比較と補正した三項の比較の自然性を証明した。
- この保存単位では1024宣言の監査が標準三公理のみで成功。L6c は未完了であり、対角・μ の自然性および最終的な外部 G 同変性の接続を続ける。


### L6c 工程完了（2026-10-19）

- `linearizedTensorAugmentationMHomotopy_naturality` は構成した実区間ホモトピー全体の自然性。厳密化、正規化、AW・shuffle、差のテンソルの消滅、実区間復元を全て接続した。
- `linearizedDiagonal_naturality` と `linearizedGroupProduct_naturality` により最後の対角と μ の自然性も証明した。
- `constructionA5_equivariant` は採用済みの群 P,Q,H,μ,α,β と入力の同変性だけから外部 G 同変性を導く。G は普通のモノイド、作用は自己準同型による。I や H の可換性を要求しない。
- 非被約 C(H) を保ち、A.5 の右辺の augmentation 補正を保つ。原典の一般文言との差は各 docstring に記載した。
- A.1 の比較射と自然性、A.4 の m 次比較と相対零化、A.6 の実区間比較と固定元を保つ外部作用の同変性は前工程で検証済み。
- 1037宣言の対象ビルド・公理監査が成功、標準三公理のみ。工程区切りの全体ビルドを別途実行する。

### L6d §10-1：実装前の文言と証明方針（2026-10-19）

原典：KST Proposition 4.14、Claim 4.15、Lemma 4.16、App. A.5・A.6。
参照：[KST arXiv v4 §4.3](https://arxiv.org/html/1611.08466v4#S4.SS3)。

1. I は結合的な非単位環、a は中心元。右乗法 φ(v)_i=v_i a を使う。
   左行列作用について (Mv)_i a=Σ_j M_ij(v_j a) は結合律と有限和の分配法則だけで成立し、中心性を使わない。
2. 集合 aI={ax | x∈I} は加法部分群であり、中心性から b(ax)=a(bx)、(ax)b=a(xb)。従って両側イデアル。
   Ia={xa} との同一性も中心性で証明する。左・右乗法の単射性もこの同一性で移せる。
3. 単位化環上の行列で ψ(v)=1+V、u=1+U と置く。V は first n 行・最後の補助列、U は同補助行・追加した最後の列だけに非零成分を持つ。
   U²=V²=UV=0、VU は first n 行・追加列に v_i a を持つ。従って u⁻¹=1−U、u⁻¹ψ(v)u=1+V+VU=ψ(v)φ(v)。可換性は不要。
4. P,Q,H と μ は上記の n,m−1,1,1 のブロック配置を用いる。P の埋め込みと ψ(Q) は交差積が両側とも零なので可換。
   μ(p,q)=embed(p)ψ(q) は群準同型。外部の左行列作用は first n 行の X,y,v のみを変え、U,z と補助元 u を固定する。積の交差項は結合律で可換になる。
5. m=0 は群の nerve の零次の一意な頂点を使う。m>0 は帰納法の入力を C(P) 内に保ち、Q の0次入力と μ 版 A.5 を組み合わせる。
   A.6 の共役比較と連結して C(ψ)≃C(ψ)+C(φ)−C(e) を得た後、`cancel_augmentation` で C(φ)≃C(e) を得る。
6. Prop 4.14 は安定 GL の全ホモロジーへの自明性ではなく、aI から I への像上の作用の自明性を目標とする。
   Claim 4.15 の相対零化を A.4 の明示的 H_* 模型界面へ移し、有限次元から安定化する。

上記は非可換版の文言と紙の計算であり、Lean での Prop 4.14 の完成を主張しない。まず右乗法・両側イデアル・零積による共役公式を実装し、その後ブロック群と帰納法を実装する。


### L6c 区切りの全体ビルド結果（2026-10-19）

- 全体ビルドはルートの import で失敗：`InfinityCategories.F1B.RelativeFunctorHomotopyComposition` と `InfinityCategories.F1.RelativeFunctorVertices` が `SerrePositivity.InfinityCategories.relativeFunctorVertex` を重複定義している。
- K-L6 の対象ビルド・1037宣言の公理監査は成功した。自分の import 閉包の破損ではないため、他レーンの依存は修復せず L6d を続行する。
- ログ：`/tmp/kst-l6-full-build.log`。


### L6d の第一保存単位（2026-10-19）

- `Prop414.lean`：結合的な非単位環上の右乗法・列の右乗法と左行列積の可換性、中心元 a の像 aI の両側イデアル性、右乗法の像との一致、単射性の移送、(I,a) に関する自然性を証明。
- `BlockConjugation.lean`：逆元 1−U を持つ `squareZeroUnit` と、U²=V²=UV=0 による非可換共役公式を証明。
- `BlockColumn.lean`：実行列の単一成分行列の和で補助列を構成し、VU の成分が v_i a になることと共役公式を証明。
- `BlockColumnCommute.lean`：固定列・固定行の条件から P の埋め込みと ψ(Q) の可換性を導く。
- `BlockColumnGroup.lean`：補助列の群準同型 ψ と可換な二つの群準同型からの `commutingProductHom` を構成。
- `GroupZeroMHomotopy.lean`：実0次ホモトピーと外部 G 同変性を証明。A.5 の第二入力と Lemma 4.16 の帰納基底に使う。
- 対象ビルド・1067宣言の公理監査が成功し、標準三公理のみ。L6d 全体は未完了。次は T_{n,m} の実ブロック群、帰納法、相対ホモロジー零化・安定化。


### L6d の実ブロック群模型（2026-10-19）

- `fixedBlockSubgroup` は指定した列と補助行を固定する実行列単位の部分群である。積・逆での閉性を実行列積から証明した。
- `fixedBlockProduct` はこの群と補助列の加法群から行列単位群への実準同型 μ。可換性は固定行・固定列の条件から導いた。
- `blockPatternSubring` は first n 列が零となる狭義三角行列で、全成分が両側イデアル J に入るものからなる非単位部分環。
- `oneDifferenceSubgroup` は単位と逆の 1 からの差が部分環に入る条件で定義した実部分群。逆の条件も定義に明示し、群の閉性を証明した。
- `triangularBlockGroup` と `nonUnitalTriangularBlockGroup` はこの模型による T_{n,m}(I) の群。整数単位化の標準射影の核を係数イデアルとし、元の I の包含の像と同定した。
- `blockColumnHom_mem_triangularBlockGroup` は ψ の実列がこの群に入ることを、三角条件と係数のイデアル所属から証明する。
- `commutingProductHom` の宇宙を各因子で独立に一般化した。数学的な仮定の変更はない。
- この保存単位の対象ビルド・1087宣言の公理監査は標準三公理のみで成功。帰納段階のブロック埋め込みとホモトピーの帰納法は未完了。


### L6d の帰納段階の実挿入（2026-10-19）

- `triangularBlockGroupMap` は係数イデアルを保つ環準同型からの実群準同型。差と逆の差の自然性を証明した。
- `optionMatrixExtensionHom` は恒等成分を一つ加える行列モノイド準同型。加法的・環準同型とはしない。
- `matrixInsertionHom` と `matrixInsertionUnits` は指定点 p に恒等行・列を入れる実準同型。元の成分、補助対角、交差零成分の公式を証明した。
- `triangularBlockGroupInsertion` は三角条件と係数イデアルを保つ実群準同型。単位と逆の両方に対して差の所属を証明した。
- `triangularBlockInsertionFixedHom` はその埋め込みが固定ブロック群に値を持つことを証明する。これで P の全体と ψ(Q) の可換性へ実際に接続できる。
- 対象ビルド・1105宣言の公理監査は標準三公理のみで成功。Q のイデアル内への制限、実 μ、行列作用と帰納ホモトピーは続行中。


### L6d の実 μ と右乗法の群準同型（2026-10-19）

- `idealBlockColumnHom` はイデアル内の列ベクトルから実三角ブロック群への ψ。定義域は乗法タグを付けた加法群であり、H 内の値域所属を証明済み。
- `triangularBlockProductHom` は小さい群の挿入とこの ψ の積による実群準同型 P×Q→H。固定ブロック群内での可換性から乗法保存を導いた。
- `idealRightMultiplication` と `idealVectorRightHom` はイデアル内の右乗法。中心性を要さず、`lastRightColumnHom` で同じ実三角ブロック群の最後の列へ入れる。
- `groupConjugationMHomotopy` は A.6 を任意の群準同型へ前合成した実 m 次ホモトピー。C(f) と C(u⁻¹fu) の両端を自由化の合成則で同定した。
- 対象ビルド・1118宣言の公理監査は標準三公理のみで成功。次は補助元 u の実群所属、共役と μ の積の同定、帰納ホモトピーと外部行列作用。


### L6d の非同変な実帰納ホモトピー（2026-10-19）

- `matrixInsertion_one_add_blockColumn` と `triangularInsertion_lastRightColumn` は小さい右乗法の列の埋め込みを大きい φ に同定する。
- `auxiliaryBlockUnit` と `auxiliaryBlockColumnHom` は同じ実三角ブロック群 H の中にある補助元 u と ψ。`auxiliaryBlockUnit_conjugation` は u⁻¹ψ(v)u=ψ(v)φ(v) を証明する。
- `lemma416GroupData` は実 P,Q,H,μ,α,β。左右の項は大きい φ と ψ、積は u による ψ の共役に等しいことを証明した。
- `lemma416HomotopyStep` は C(P) 内の m 次帰納仮定と C(Q) 内の0次入力に μ 版 A.5 を適用し、A.6 と連結して augmentation 補正を相殺する。
- `lemma416Homotopy` は全ての m に対する非同変な実 m 次ホモトピー。入力は n、周囲の単位環の両側イデアル J、a∈J、m のみであり、帰納法の結論を仮定にしない。中心性もこの非同変部分では不要。
- 対象ビルド・1136宣言の公理監査は標準三公理のみで成功。外部行列作用の同変性、(I,a) に関する関手性と単体環への移送、相対零化・安定化はまだ未完了。


### L6d の実外部行列作用（2026-10-19）

- `oneDifferenceTransform` は非単位部分環の準同型を 1+S の実単位部分群の群準同型へ移す。周囲の環準同型への延長は要求せず、単位と逆の差を明示的に送る。
- `leftMultiplierHom` は xB=x を満たす乗数 B の左乗法を部分環の非単位環準同型にする。`leftMultiplierGroupHom` はその実群への持ち上げ。
- `firstBlockMatrix` は diag(M,1) の実行列。四ブロックの成分、左積の前半・後半の行の式、first n 列が零である元の右吸収を証明。
- `blockPattern_firstBlock_left_mem` は三角性と係数イデアルを保つことを証明。`triangularBlockMatrixEnd` は非可逆な一般の行列 M の作用自己準同型。
- `triangularBlockMatrixAction` は Matrix_n(R)→Monoid.End(T_{n,m}(J)) の実モノイド準同型。単位・積の法則を実成分 1+diag(M,1)(g−1) から証明した。
- これは単位化上の全行列の作用であり、元の I の行列についても乗法の可換性が成り立つ。非単位の行列半群を単位元を持つ G と混同していない。
- 対象ビルド・1157宣言の公理監査は標準三公理のみで成功。Q の列作用、φ・ψ・μ・u と帰納ホモトピーへの同変性の接続を続ける。


### L6d の各実射の行列同変性（2026-10-19）

- `idealMatrixAction` はイデアル内の列ベクトル Q の全行列モノイド作用。`idealVectorRightHom_equivariant` は右乗法との可換性を中心性なしで証明する。
- `firstBlockMatrix_mul_blockColumn` は実補助列への diag(M,1) の左積と列ベクトルへの M の左積の一致。
- `idealBlockColumnHom_equivariant`、`lastRightColumnHom_equivariant`、`auxiliaryBlockColumnHom_equivariant` は実 ψ・φ と作用の同変性。
- `auxiliaryBlockUnit_fixed` は同じ実群 H 内の補助元 u が全行列作用で固定されることを証明する。
- `groupConjugationMHomotopy_equivariant` と前合成・連結の同変性は実区間射のテンソル合成則と加減法から証明した。
- `affineMatrixAction_insertion` と `triangularBlockInsertion_equivariant` は first n 行の外への恒等座標の挿入と全行列作用の可換性。
- 対象ビルド・1183宣言の公理監査は標準三公理のみで成功。次は μ 版入力への束ねと実帰納ホモトピー全体の同変性。


### L6d の離散非可換環上の全行列同変な帰納ホモトピー（2026-10-19）

- `lemma416EquivariantGroupData` は実 P,Q,H の行列作用と実 μ,α,β を採用済み A.5 の同変な入力に束ねる。μ の同変性は実埋め込みと補助列の同変性から導いた。
- `lemma416HomotopyStep_equivariant` は既に構成した実帰納段階の区間射自体の同変性を証明。A.5 と A.6 の区間射の同変性を同じ線形な連結・相殺に適用した。
- `lemma416Homotopy_equivariant` は全 m の実帰納ホモトピーの行列同変性。結論を含む追加構造体・追加公理を導入していない。
- 対象ビルド・1188宣言の公理監査は標準三公理のみで成功。離散環上の非可換な実比較と全行列同変性は検証済みだが、(I,a) の射への関手性、単体環への移送、相対零化・安定化は未完了。


### L6d の実帰納ホモトピーの係数関手性（2026-10-19）

- `strictifiedMap_naturality` と `strictificationHomotopy_naturality` は異なる因子内の入力を結ぶ射に対する厳密化の自然性。
- `linearizedTensorAugmentationMHomotopy_functorial` と `constructionA5_functorial` は異なる群データ間での実区間射の自然性。自己射だけに制限しない。
- `idealVectorMap`、実列・ブロック挿入・補助元の係数自然性、および μ とその積の係数自然性を証明。
- `groupZeroMHomotopy_functorial` と `groupConjugationMHomotopy_functorial` は零次比較と A.6 の実区間の係数自然性。
- `lemma416Homotopy_functorial` は指定元と係数イデアルを保つ全ての周囲環準同型に対する、全 m の構成済み実区間射の自然性。因子内の帰納仮定、A.5、A.6、連結・相殺を同じ構成で比較した。
- 対象ビルド・1218宣言の公理監査は標準三公理のみで成功。次は次数ごとの群の nerve の実比較を対角へ制限する単体環への移送。相対零化・安定化はまだ未完了。


### L6d の単体的イデアル模型での Lemma 4.16 と相対零化（2026-10-19）

- `SimplicialIdealData` は周囲の単体的単位環と面・退化が保つ両側イデアルの族のみを保持する数学的データ。零次の指定元は唯一の [n]→[0] により各次数へ移す。
- `SimplicialIdealData.columnGroup` と `triangularGroup` は各次数の実群を単体的群へ束ねる。`rightColumnMap` は右乗法の実単体射。
- `diagonalGroupMHomotopy` は係数方向に自然な次数ごとの実比較を既存の monoidBar の対角へ制限する。二つの方向の自然性と実両端条件を証明した。
- `simplicialLemma416Homotopy` とその同変性を `lemma416` で A.4 の HomologicallyMConstant に束ねた。結論の実比較や対角への移送を仮定していない。
- `SimplicialIdealData.matrixMonoid` と二つの実作用、右乗法の同変射も単体的に構成した。
- `lemma416_relative_zero` は群状の単体的モノイドからの実行列表示に沿って作用を制限した相対写像の零化。H_* の自然な複体模型は K-L2 の明示的界面。
- 対象ビルド・1252宣言の公理監査は標準三公理のみで成功。一般の非単位単体環の標準単位化からこの模型を得る実装と、Claim 4.15 の一般線形モノイドへの因子化・安定化は続行する。


### L6d の非単位単体環の標準単位化（2026-10-19）

- `integerUnitizationMap` は非単位環準同型の実単位化。整数射影・標準包含・恒等・合成と可換で、核イデアルを保つ。
- `NonUnitalSimplicialRing` は次数ごとの非単位環と面・退化の法則のみを持つ。`standardIdeal` は標準単位化の実単体図式と核イデアルを構成する。
- `nonUnitalLemma416` は一般の非単位単体環の零次元に対する全行列同変な実比較。
- `integerUnitizationIdealAddEquiv` とその自然性、列ごとの加法同型により、核イデアルの列は元の I の列の追加仮定を伴わない表示である。
- 対象ビルド・1269宣言の公理監査は標準三公理のみで成功。Claim 4.15 の ĜL は各次数で可逆な行列に置き換えず、π₀ での可逆性を保つ。比較射と安定化は未完了。


### L6d の非単位環の ĜL と三角群の実包含（2026-10-19）

- `NonUnitalSimplicialRing.hatGLSubmonoid` は標準単位化の行列で、π₀ で可逆かつ整数成分が恒等行列であるもの。次数ごとの逆元を要求しない。
- `hatGLPullback` と `hatGL` は面・退化による両条件の保存を証明した実単体的モノイド。`hatGLRepresentation` は全行列モノイドへの実表現。
- `triangularBlockGroup_fst` は実三角群の整数成分の恒等性を証明する。`triangularHatGLHom` と `triangularHatGLMap` は実単位の π₀ での単位性からの自然な実包含。その各次数の単射性も証明。
- 対象ビルド・1278宣言の公理監査は標準三公理のみで成功。群状性の証明、Claim 4.15 の半直積と相対項の因子化、Prop 4.14 の安定化は未完了。


### L6d の非単位 ĜL の群状性と相対零化（2026-10-19）

- `componentsFst` は標準単位化の成分環から整数環への実準同型。辺の両端の整数成分の一致から商へ降ろし、行列の成分写像との可換性も証明する。
- `hatGLEdgeOfCoefficients` は整数核内の二頂点の係数の辺を核内の一本の辺へまとめる。整数核内の成分比較 `hatGLClassMap` の単射性を証明した。
- `hatGL_inverse_vertex` は成分環の逆行列の係数を零次へ持ち上げ、整数射影と積の恒等式から逆代表が整数核に残ることを証明する。
- `NonUnitalSimplicialRing.hatGL_isGrouplike` は各成分の二側逆を実際に構成する。次数ごとの群性を仮定しない。
- `nonUnitalLemma416_relative_zero` はこの実群状性と実行列表現を A.4 へ渡す。H_* 模型のみが借用界面であり、群状性や零化を仮定にしていない。
- 対象ビルド・1289宣言の公理監査は標準三公理のみで成功。Claim 4.15 の実半直積の因子化と安定化は引き続き未完了。


### L6d の実三角群の最終列分解（2026-10-19）

- `matrixDropLast_mul` と `matrixLastColumn_mul` は最終行が恒等行となる右因子との実積の式を証明する。
- `triangularBlockGroupDropLast` は左上ブロックへの実群準同型。逆のブロックを実逆に使い、元・逆の両方の三角条件と係数イデアル条件を証明する。
- `triangularBlockGroupLastColumn` は係数イデアル内の最終列。単位・積の法則を実行列積から証明した。
- `triangularBlockAffineSplit` は T_{n,m+1} から T_{n,m} と列群の実半直積への準同型。積は v+M v′ の順であり、非可換な係数を保つ。
- `actionProductLift` と section・fiber への制限の等式は、基底とファイバーの実射を作用の交換則で束ねる。外部モノイドの次数ごとの可逆性を仮定しない。
- 対象ビルド・1309宣言の公理監査は標準三公理のみで成功。外部 ĜL を含む実比較射と相対項の因子化、安定化を続行する。


### L6d の単体的な実分解と外部 ĜL のブロック積（2026-10-19）

- `SimplicialIdealData.triangularColumnAction` と `triangularAffineSplitMap` は実三角群の半直積への分解を単体的に束ねる。面・退化との可換性は基底と最終列で実証明した。
- `firstBlockMatrixHom` と `NonUnitalSimplicialRing.hatGLBlockMap` は一般の有限補助 rank に対する単位ブロック和。π₀ での単位性と整数核条件の両方を保つ。
- `triangularBlockMatrixAction_intertwining` は ρ_M(t)diag(M,1)=diag(M,1)t を右吸収の式から証明する。一般の非可逆行列にも成立する。
- `triangularGLProductHom` と `triangularGLProductMap` は外部 ĜL と三角群の半直積から ĜL_{n+m} への実ブロック積。各次数の逆元は仮定せず、全単体射への自然性を証明した。
- 対象ビルド・1318宣言の公理監査は標準三公理のみで成功。最終列を含む二つの実比較の接続、相対項の因子化、安定化は続行する。
