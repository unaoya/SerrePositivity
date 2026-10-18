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
- L6c：一般のモノイド作用の半直積・単体的半直積・包含と射影の分裂・ψ の単体性を検証済み。
- `grouplikeActionIso`：群状モノイドの頂点による作用のホモトピー不変な像での可逆性を証明。
- 対象ビルドと333宣言の公理監査は成功し、標準三公理のみ。
- Lemma A.2 の ψ は anodyne 局所化で同型と証明。π による同値性への移送は K-L9 の模型界面。
- Lemma A.4 の相対項の代数部分：同変射の半直積への誘導射、分裂包含の余核、定数射の相対項での零化を実装。F は H_* を受ける明示的な関手引数。
- Prop A.1 の基礎：一般の作用の圏、同変写像からの関手、二重 nerve と対角、正則作用の nerve の実収縮を実装。
- Construction A.6：成分 u⁻¹ の自然変換、nerve の実ホモトピー、係数付き自由鎖複体への実鎖ホモトピーを構成。
- Construction A.5：ユーザーが augmentation 補正を採用し、L6c を再開。非被約 C(H)=ℤBH を保持する。下記の設計確認欄を参照。
- A.5 の代数部分：`tensorMap_augmentation_expansion` と `tensorMap_augmentation_eq_low` を検証。二つの差の消滅から m+m′+1 以下の補正式を得る。AW・shuffle のホモトピー構成と移送は未完。
- L6c の Prop A.1、Lemma A.4 の m-ホモトピーからの比較、A.5 は未完了。A.6 の C(H) の界面への移送も残る。
- L6d〜g：未着手。

## 主要宣言の表

| 宣言 | ファイル | 状態 | 意味 |
| --- | --- | --- | --- |
| tensorMap_augmentation_eq_low | AugmentationTensor.lean | 検証済み | A.5 の右辺の augmentation 補正と次数 m+m′+1 の計算 |
| tensorMap_augmentation_expansion | AugmentationTensor.lean | 検証済み | 差のテンソルの双線形展開 |
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
