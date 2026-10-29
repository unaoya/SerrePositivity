# CommutativeAlgebra の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/CommutativeAlgebra/` の残りの群（B・C3・D・E・H・X）について、
ファイルの統合、未使用の宣言の削除、Mathlib への置き換え、重複の一本化、Mathlib への提出候補をまとめる。
群ごとの調査（2026-10-29〜30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：群ごとに提案 → ユーザーの承認 → 実装 → 新しいファイル単体のビルド → 区切りで全依存ビルドと監査 → コミット。
規約：Mathlib の確認は固定版（2026-10-07、`.lake/packages/mathlib`）と最新版（2026-10-28、`/tmp/mathlib-latest`）の両方で行った。
提出候補は [mathlib-upstream.md](mathlib-upstream.md) の G 番号の表に移してから扱う。
使われ方：作業を再開するときの手順書。群に着手する前に、この計画を読み直し、宣言の利用状況をもう一度確かめる。

## 1. 状態

| 群 | 内容 | 状態 |
| --- | --- | --- |
| G（G1〜G7） | 冪級数・導分・完備微分・p 基底の持ち上げ・Cohen–Gabber | 完了（bfec81e21 ほか、G7 は 612eae3e3） |
| A（A1〜A6） | adic 完備化 | 完了（f00bad23f・9c41f5f43、abd87dba6・1ed27fe56・cdbefbde9） |
| F（F1〜F4） | 係数体・剰余体拡大・Witt | 完了（9bce1e872・7df4d71bd、audit_f5 は 93d84541e） |
| C1 | 正則列と深さ | 完了（RegularSequence・Depth・Unmixedness・MaximalRegularSequence、候補 G9） |
| C2 | パラメータ系 | 完了（SystemOfParameters/{Basic,Existence,Generators,Finite,Avoidance}、候補 G10） |
| C3 | 正則局所環 | 完了（RegularLocalRing/、HenselianFinite、候補 G11。RegularBaseChange の 2 補題は CLMST の証明が使うので RegularSequence へ移して保持） |
| B1・B2・D・E・H・X | 残り | 計画（§4〜§9） |

C1〜C3 は一回の全依存ビルド（388 モジュール）と監査を通してコミットした（2026-10-30）。

## 2. 作業の決まり

- ビルド：群ごとには新しいファイル単体と直接の利用先だけをビルドする。全依存ビルドは複数の群をまとめて一回にし、通るまでコミットしない（全依存の半分は BhattScholze の重いモジュール）。
- BhattScholze/・CLMST/（別セッションの管轄）：モジュールの統合・改名に伴う import 行の書き換えと、改名・削除した宣言の参照の書き換え（C2 以降）は行ってよい。証明の中身は変えない。BS/CLMST 分は独立したコミットにし、旧→新の対応表をメッセージに書く。
- 監査：`scripts/audit/*.lean` は `python3 scripts/make_area_audits.py` で生成する（手編集しない）。dg・bhatt_scholze の差分が並行セッション由来なら checkout で戻す。`scripts/audit_local_algebra.lean`・`audit_clmst.lean`・`audit_f*.lean`・`audit_axioms.lean` は宣言名を直接書いているので、削除・改名のたびに直す。
- 宣言名：BS/CLMST が多数参照する中心の宣言（各節の「変えない名前」）は改名しない。必要なら `@[deprecated] alias` を経由する。
- 好み：`.choose` より `def` と `@[simp]` 補題。薄い包みは利用が多いときだけ残す。名前空間はファイル名から付けない。docstring は 概要／方針／規約／使われ方。
- 循環 import：統合の前に、旧→新の対応で import のグラフを縮約して閉路を調べる。

## 3. C3 正則局所環（承認済み・保留）

新しいディレクトリ `CommutativeAlgebra/RegularLocalRing/`。

| 新しいファイル | 元のファイル | 主な変更 |
| --- | --- | --- |
| Graded | GradedRegularLift・RegularFromGradedPresentation・RegularGradedPresentation | ほぼ重複する生成元の正則性の補題を一本化 |
| Basic | RegularParametersProof・RegularParameters・RegularLocalQuotient・RegularLocalRing の整域性 | 主定理を `isWeaklyRegular_of_span_eq_maximalIdeal` に一本化（`isWeaklyRegular_of_minimal_generators` を削除）。`spanFinrank_span_range_le` を Mathlib の `Submodule.spanFinrank_span_le_ncard_of_finite` に。整域性を instance に |
| Normality | RegularNormality | なし |
| Dimension | RegularPrimeDimension | 未使用 2 宣言を削除 |
| Criterion | RegularLocalCriterion | 中身は触らない（Nailin Guan の Mathlib コミットの持ち込み。上流の PR が入ったら置き換え） |
| Localization | RegularLocalization | 未使用 `exists_localized_height_koszulResolution` を削除 |
| FlatBaseChange | FlatLocalDimension | 次元の等式を Mathlib の `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`・`Algebra.HasGoingDown.of_flat` で短くできるか試す |

- `RegularLocalRing.lean` は Koszul オイラー標数 `koszulEulerChar_eq_finrank` だけを残す。B2 で `Koszul/RegularEuler` へ移す（§5）ので、C3 と B2 は同時に行う。
- CompleteLocalExtension → `HenselianFinite.lean`。`isLocalRing_finite_domain_of_complete` の仮定を「完備 Noether」から「Henselian」に弱められるか試す。
- RegularBaseChange を削除。`isSMulRegular_tensorProduct_of_flat` は Mathlib の `IsSMulRegular.rTensor` で、`exists_pow_torsion_bound_of_isSMulRegular` は N = 0 で自明。CLMST/TensorIsogeny の参照を書き換える。
- 未使用：`head_ne_zero`、`samuelFunction_succ_eq_add_generator_quotient_of_gradedReesPresentation_injective`、`exists_localized_height_koszulResolution`、`regular_supportCodimension_add_supportDim`、`regular_supportCodimension_toNat`。
- 提出候補 G11：整域性、正則系は正則列、`R/(x)` の正則性、平坦な底変換での正則性、正規性、Hensel の冪等元の持ち上げ。局所化は Guan との調整が要る。

## 4. B1 Hilbert–Samuel・随伴次数・Rees・Hilbert 級数

規模：36 ファイル、約 4300 行。BS/CLMST の import は CLMST の 2 本（`HilbertSamuel`・`HilbertSamuelEquiv`）だけ。

新しいディレクトリ `CommutativeAlgebra/HilbertSamuel/`。

| 新しいファイル | 元のファイル |
| --- | --- |
| PolynomialGrowth | PolynomialGrowth・PolynomialFiniteDifference |
| Graded/Subquotient | GradedSubquotient・GradedLinearMap・GradedShiftMap・GradedSurjection |
| Graded/HilbertSeries | GradedHilbertSeries・GradedCumulativeGrowth・HilbertSerreFinite・HilbertSerre |
| Graded/PolynomialRing | MonomialCounting・PolynomialHilbertSeries・HomogeneousRelationGrowth |
| Basic | HilbertSamuelBasic・SamuelModuleProperties・SamuelSurjection（HilbertSamuelEquiv は CLMST が import するので別に残すか入口にする） |
| AssociatedGraded | AssociatedGraded・ReesModule・ReesModuleGrading |
| ReesPresentation | ReesPresentation・GradedReesSelf・GradedPresentationMap（GradedReesNoetherian は 2 行の包みなので廃止） |
| Polynomial | HilbertSeries・HilbertSamuelPolynomial・SamuelCumulative |
| Dimension | ArtinReesGrowth・SamuelRegularGrowth・SamuelGrowthComparison・HilbertSamuelDimension |
| （入口）HilbertSamuel | HilbertSamuel（CLMST が import するのでモジュール名を残す） |

- 外へ回す：Truncate → PerfectComplex。GradedAdicExactness → Koszul 重複度（B2）。ReesIdealLifts・ReesCoefficientApproximation → Adic。
- Mathlib への置き換え：
  - `isNoetherianRing_gradedReesRing_of_fg` → `isNoetherianRing_reesAlgebra_quotient`（RingTheory/ReesAlgebra.lean）。確度高。
  - 後退差分 → Mathlib の前進差分 `fwdDiff`（Algebra/Group/ForwardDiff.lean、`Polynomial.fwdDiff_iter_degree_eq_factorial` など）。外から使われるのは `backwardDifferenceSeq` と `eventually_iterate_backwardDifferenceSeq_eq_coeff` の 2 つ（利用者は KoszulAdicEuler）。確度高。
  - `(1 - X) * invOneSubPow ℚ 1 = 1` の 4 回の証明 → `PowerSeries.mk_one_mul_one_sub_eq_one` などから 1 行。まず自前の補題を 1 本にする。
  - `adicSubmodule R I M n := I ^ n • ⊤` を `(I.stableFiltration ⊤).N n` に揃え、Mathlib の `Ideal.Filtration` API（Artin–Rees、`Stable`）を直接使う。
  - `length_quotient_map_ringEquiv` を `Module.length_eq_of_surjective` で短く。
  - `isInternal_of_projections` は `DirectSum.Decomposition.ofLinearMap` などで置き換えられる可能性（確度中）。
- 一本化：
  - 射影と可換の補題 4 本（`gradeProjection_succ_comp`・`_add_comp`・`_below_comp`・`_comp`）を、次数を `d` ずらす一般形 1 本に。GradedLinearMap は GradedShiftMap の `d = 1` なので吸収。B2 の GradedKoszulHomology の 2 加群版も同じ形にそろえる。
  - 有理型級数から多項式を作る議論 2 本（`exists_isSamuelPoly_of_hilbertSeries`・`exists_cumulativePoly_of_lengthSeries`）を数列の補題 1 本に。
  - 正値性の補題の二重（`samuelFunction_pos` は `*_of_nontrivial` の特殊例）を解消し、「十分先で正の多項式は最高次係数が正」を PolynomialGrowth の補題に。
  - 存在定理からの同じ経路 3 本を 1 本に。
  - `poly` の `.choose` をやめ、`isSamuelPoly_poly_of_radical` を主 API に。
  - `gradedReesPresentation` の可換図式の二重の証明を一本化。
  - `samuelFunction`・`IsSamuelPoly`・`multiplicity` の加群の universe を `Type*` に一般化。
- 未使用（削除候補）：`HilbertSamuel.multiplicity_pow`（教科書的なので提出するなら残す）、`exists_isSamuelPoly_of_pow_eq_zero`、`natDegree_poly_eq_of_radical_eq`、`IsSamuelPoly.natDegree_lt_quotSMulTop`、`samuelFunction_eq_sum`、`natDegree_le_of_eventually_eval_le_mul_affine`、`HomogeneousRelationGrowth` の 2 つ、`MonomialCounting.natCard_degree_eq_multichoose(_of_finite)`、`ReesModule.directSumReesGradedEquiv` 系 3 つ（GradedModule との接続に使えるので要検討）、`shiftedReesModule_le`、`reesGraded_finite_over_polynomial`、GradedPresentationMap の 2 つ、`HilbertSerreFinite` の 1 変数版 2 つ。instance と `@[simp]` はビルドで確かめるまで残す。
- 変えない名前：`HilbertSamuel.multiplicity`、`HilbertSamuel.multiplicity_span_map_ringEquiv`、名前空間 `SerrePositivity.HilbertSamuel`。
- 提出候補：PolynomialGrowth、`{m // m.degree = n} ≃ Sym σ n`、`MvPolynomial.homogeneousSubmodule` の基底と次元、同次部分加群・商への分解の降下、Hilbert–Serre、Samuel 関数と次元定理（Atiyah–Macdonald 11.14。`stableFiltration` に揃えてから）、正則元の逆像に対する Artin–Rees。
- リスク：Basic と Dimension を一つにすると SystemOfParameters と循環する。Graded/Subquotient が HilbertSerre の重い import を持たないようにする。KST/SchemeLemmas/Blowup が GradedSubquotient を使う（`reesGrade` などは KST に同名の別宣言があるので名前空間を明示）。

- 決定（2026-10-30、ユーザー）：(1) 後退差分を Mathlib の `fwdDiff` に置き換える（B2 の KoszulAdicEuler も合わせて書き換える）。
  (2) `adicSubmodule` を `(I.stableFiltration ⊤).N n` に揃える移行を B1 の中で行う（B2 の Koszul 重複度の証明鎖への波及も合わせて直す）。
  (3) `multiplicity_pow`・`directSumReesGradedEquiv` 系・`natDegree_poly_eq_of_radical_eq` は残す。
  (4) 射影と可換の補題の一本化は、B2 の GradedKoszulHomology の 2 加群版も含めて B1 の作業で同時に行う。
  B1 は C1〜C3 の全依存ビルドとコミットの後に着手する。
- (2) の影響の下調べ（2026-10-30）：`adicSubmodule`（AssociatedGraded で `I ^ n • ⊤` と定義）の利用は 6 ファイル 33 箇所だけ
  （AssociatedGraded 13、ReesModule 8、ReesKoszulEvaluation 5（B2）、GradedReesSelf 3、GradedPresentationMap 2、
  RegularLocalRing/Graded 2（C3））。BS/CLMST の利用はない。Mathlib の `(I.stableFiltration ⊤).N n` は定義上 `I ^ n • ⊤` なので、
  `adicSubmodule` をその abbrev として定義し直せば既存の証明（`change … I ^ (n + 1) • ⊤` など）はほぼそのまま通る見込み。
  ReesModule は既に `stableFiltration` を使っている。そのうえで Artin–Rees などを Mathlib の `Ideal.Filtration` API に寄せる。

## 5. B2 Koszul・有限長・重複度・台の次元

規模：46 ファイル、約 6700 行。BS が KoszulResolution を 5 本で import、CLMST は 6 本。

| 新しいファイル | 元のファイル |
| --- | --- |
| Length/Basic | FiniteLength の一般の節・FiniteLengthValue・QuotientImageLength・FiniteLengthSmulSubquotient・FiniteLocalSupport の `exists_maximal_generators_pow_mem` |
| Length/CommonResidueField | FiniteLength の「剰余体が同じとき」の節・LocalAlgebra の `residueFieldEquiv_of_surjective`・`maximalIdeal_pow_le_map_of_finite`・FiniteLocalSupport の残り |
| Length/Euler | HomologyLength・FiniteLengthComplexEuler |
| Length/QuotientPower | QuotientPowerLength・RegularSequenceLength |
| SupportDimension（既存に統合） | FiniteLength の台の節・LocalAlgebra の台と generic basis の補題・ModuleSupport の `module_support_subset_union_of_exact` |
| Koszul/Basic | Koszul（中身は変えない） |
| Koszul/Resolution | KoszulResolution・RegularSequencePowers の冪の分解・ParameterKoszulGrowth の `isKoszulResolution_mvPowerSeries_X_pow` |
| Koszul/FiniteLength | KoszulFiniteLength |
| Koszul/RegularEuler（新設） | RegularLocalRing の `koszulEulerChar_eq_finrank` |
| KoszulMultiplicity/AdicEuler | AdicModuleProduct・AdicTermEuler・AdicFilteredLength・AdicEulerComparison・KoszulAdicEuler |
| KoszulMultiplicity/Graded | GradedKoszulHomology・GradedKoszul・GradedKoszulEvaluation・GradedKoszulVanishing |
| KoszulMultiplicity/Rees | KoszulReesFinite・ReesKoszulEvaluation・GradedReesKoszulVanishing・ReesKoszulAcyclic |
| KoszulMultiplicity/Formula | KoszulMultiplicityProof・MultiplicityFormulas |
| KoszulMultiplicity/Parameters | ParameterPowerMultiplicity・ParameterLastPowerMultiplicity・KoszulMultiplicityLimit・ParameterPowerLengthBound |
| KoszulMultiplicity/FrobeniusGrowth | ParameterKoszulGrowth（冪級数の補題は PowerSeries へ） |

- LocalAlgebra.lean は廃止（importer 11 本の import 行を書き換え。BS/CLMST はなし）。
- `Koszul/RegularEuler` を作ると、RegularLocalRing の import 閉包（78 モジュール、交点理論を含む）が外れ、整域性しか使わない CLMST/EtaleLocus が軽くなる。RegularLocalRing → ResolutionEvaluation の import は必ず外す。
- Koszul と KoszulResolution は一つのファイルにしない（Koszul の閉包は 2 モジュール、KoszulResolution は Tor などを引く）。BS の再ビルドを避けたければ、この二つは現在のパスに残す。
- 外へ回す：AssociatedPrimeDimension・AssociatedPrimeQuotient → 深さ（C1 の Depth・Unmixedness の隣）。IntegralDimension → 次元・RootTower。SupportHeight・ModuleSupportHeight → KTheory/Adams か Support。ModulePowerTorsionBound → DerivedCompletion。ControlledResolution・TorFiniteLength・KoszulDirectedUnion → HomologicalAlgebra。冪級数の補題 → PowerSeries。多項式の評価の補題 → B1 の PolynomialGrowth。`exists_samuelFunction_le_pow`・`samuelFunction_prod` → B1 の Basic。
- Mathlib への置き換え：`annihilator_le_quotient` → `LinearMap.annihilator_le_of_surjective`。`module_support_subset_zeroLocus_of_annihilator` → `Module.annihilator_le_of_mem_support` で 2 行。`GradedKoszul.toCycles` など → `ShortComplex.moduleCatToCycles`・`moduleCatHomologyIso`。`length_eq_zero_of_isZero` 系・`isFiniteLength_of_isSimpleModule` はインライン化。`residueFieldEquiv_of_surjective` → `RingEquiv.ofBijective (ResidueField.map φ)`。`exists_power_torsion_bound_of_noetherian` → `LinearMap.eventually_iSup_ker_pow_eq`。`length_eq_of_common_residueField` は局所な場合だけ `IsLocalRing.length_restrictScalars` の系にできる。
- 一本化：別名の定理 `HilbertSamuel.multiplicity_parameter_pow`・`HilbertSamuel.multiplicity_eq_chiOrd_koszul` を削除（正本は CLMST が使う `KoszulMultiplicityProof.` 版）。`FiniteLengthComplexEuler.finiteSupport_of_bounded_zero` は CategoryTheory/FiniteSupportBounds の別名なので削除。`reesPolynomialModule` 系の二重（KoszulReesFinite と HilbertSamuelPolynomial）を `reesAlgebra I` 加群一般の版 1 本に。`gradeProjection_*_comp` の二重は B1 と合わせて一本化。長さの ℕ・ℤ 版の重複は ℕ 版を残す。商の長さの移送 2 本を `length_eq_of_semilinear_bijective` から導く。`chiOrd_eq_of_quasiIso` は PerfectComplex/OrdinaryEuler へ。
- 未使用：FiniteFiltrationAnnihilator はファイルごと未使用（`ideal_pow_annihilator_of_finite_filtration` だけ Length/Basic へ移す価値あり）。`length_ker_add_range`（ℕ∞ 版）、`length_le_length_quotient_smul_of_subquotient`、`exists_bound_homologyGrade_eq_bot`、`koszulShortComplex`、`finite_homology_of_variables_zero`、`evaluatedModule_scalarTower`、SupportHeight の 3 つ（`@[simp]` 1 つ）。audit だけが参照：`termLength_cone`・`shortComplex_length_identity`（audit_axioms）、`quotientImageEquiv_mk`（audit_clmst）。
- 変えない名前：`koszulComplex`、`koszulHomologySelf`、`scalarConeFunctor`、`koszulFunctor`、`koszulComplexOn`、`IsKoszulResolution`、`isKoszulResolution_of_isWeaklyRegular`、`torAlgKoszulIso`・`torAlgKoszulEquiv`、`isFiniteLength_of_le_radical_annihilator`、`length_eq_of_common_residueField`、`length_restrictScalars_eq`、`isLocalHom_of_residue_surjective`、`ringKrullDim_eq_of_integral_of_injective`、`length_quotient_sup_span_pow_le`、`KoszulMultiplicityProof.multiplicity_eq_chiOrd_koszul`、`isFiniteLength_koszulHomology_of_isSystemOfParameters`、`HilbertSamuel.multiplicity_eq_rank_of_regular_base`、`HilbertSamuel.multiplicity_parameter_last_pow`。
- 提出候補：Koszul 複体（Mathlib にない。外積代数による定義との設計の調整が要る）、整拡大で Krull 次元が不変（IntegralDimension、すぐ出せる）、台の補題（`support_tensorProduct`、`module_support_subset_union_of_exact` は `Module.support_of_exact` の一般化）、有限長の補題、正則列の冪、`DirectSum.IsInternal` の補題 2 つ、`maximalIdeal_pow_le_map_of_finite`。
- リスク：FiniteLength は importer 27 本のハブなので、分割したら全 importer を一度に書き換える。MultiplicityFormulas の閉包は 106 モジュールで、CLMST/ParameterLength の閉包は 1413 モジュール。軽い利用者に MultiplicityFormulas を import させない。

- 決定（2026-10-30、ユーザー）：B1 と B2 は一続きの作業にし、全依存ビルドも一回にまとめる。
  (1) Koszul.lean と KoszulResolution.lean はパスも中身もそのままにする。B1・B2 で足す補題（冪の分解など）は KoszulResolution を
  import する別のファイル（例 `Koszul/Powers`）に置く。`Koszul/` への移動は、後で BhattScholze 側を再ビルドする別の作業に合わせて行う。
  （計算：B1・B2 だけで BS/CLMST の 192 モジュール（うち BS 72）が再ビルドになる。Koszul・KoszulResolution を動かすか中身を変えると、
  BS の Delta・Andre を中心に 45 モジュール増え、BS は 72 → 117 になる。）
  (2) `koszulEulerChar_eq_finrank` は `Koszul/RegularEuler` を新設して移す。
  (3) 他の群へ回すファイルは、B2 の時点で場所だけ移す（統合は受け入れ先の群のときに）。
  (4) `reesPolynomialModule` の二重の一本化は B1 と同時に行う。

## 6. E 局所化

規模：21 ファイル、約 2300 行。CLMST 約 25 本の import、BS は 1 宣言（`existsUnique_valuation_extension_of_integral_away_bijective`）。

新しいディレクトリ `CommutativeAlgebra/Localization/`。

| 新しいファイル | 元のファイル |
| --- | --- |
| PowerTorsion | LocalizationPowerBound・LocalizationComparisonBounds・LocalizationTorsion・LocalizationInverse・PrincipalCoverNumerators の一様冪の補題 |
| Lattice | LocalizationLattice |
| CommonModel | FiniteCommonLocalizationModel・FiniteCommonLocalizationBounds・FinitePresentationCommonLocalizationModel・FinitePresentationCommonLocalizationBounds・LocalizationComparisonTensorEquiv |
| FiniteAlgebraLift | FiniteAlgebraLocalizationLift |
| Away | PrincipalLocalizationNormalization・DoubleLocalizationTensorComparison・PrincipalCoverNumerators の残り・IntegralAwayExtension・GenericEtale の `awayAlgebra`（一般の可換環で成り立つので移す。GenericEtale が Away を import する向きにして循環を避ける） |
| EtaleAway | EtaleAwayBaseChange・EtaleAwayTensorBaseChange |

- 外へ回す：CoprimeFactorLocalization・LocalizedSurjectiveQuotient → CubicCyclotomic（X）。SemilocalSupport → KTheory/Adams/SemilocalSupport（今は 4 行の再エクスポート）へ本体を移す。LocalizationTelescope → Adic か HomologicalAlgebra/DerivedCompletion。
- Mathlib への置き換え：`IsModuleSTorsion P M` → `Module.IsTorsion' M P`（`iff_localized_zero` は `LocalizedModule.subsingleton_iff`、`iff_tensor_zero` は `IsLocalizedModule.subsingleton_iff`。波及は KTheory 5 本・ModuleSupport・InfinityCategories で BS/CLMST なし）。`exists_pow_smul_zero_of_localized_zero` → `IsLocalizedModule.Away.exists_of_eq`（確度高）、`localizationComparison_ker_power_torsion` もほぼ 1 行。`exists_clear_denominators` → `Module.FinitePresentation.exists_lift_of_isLocalizedModule`。`isLocalizationLattice_span` → `IsLocalization.mem_span_iff`。`IsLocalizationLattice.tensorEquiv` は `IsLocalizedModule.isBaseChange` の包み。`principalLocalizationTower_scalarTower` は `inferInstance`。`awayModuleMap` は `LocalizedModule.map (.powers g) f` と同じと見込まれる（CLMST 10 本が使うので名前は残し、定義の一致をビルドで確かめる）。`existsUnique_valuation_extension_of_integral_away_bijective` は ValuationRing → IsIntegrallyClosed のインスタンス連鎖で一般版だけで足りる見込み（BS が参照）。
- 一本化：一様冪の補題 3 本（任意の乗法的集合の版を本体にし、`exists_uniform_pow_smul_zero` の名前を残す）。共通模型の証明の前半 4 回の重複を `localizationSplitting_maps` と 2 つの instance に括り出す。共通冪の補題 2 本。ker 側の補題を任意の乗法的集合に一般化。EtaleAway を `[IsLocalization.Away g Rg]` の形に（CLMST への波及が大きいので後回し）。
- 未使用：`principalSplitting_exists_finite_common_model`、`principalLocalizationTower_algebraMap`、`principalLocalizationTowerEquiv`、`localizationSplitting_common_model_tensor_squares`、`exists_uniform_pow_smul_zero_of_localization`、`HeightAtLeast.localizedMaximalPointsEquiv`、`IsModuleSTorsion` の補題 7 つ。内部専用のもの（CoprimeFactorLocalization の中間補題 10 個など）は private に。残す価値あり：`localizationComparisonTensorEquiv_tmul`（`@[simp]` を付ける）、`localizationComparisonAwayEquiv`、`isLocalizedModule_of_comparison_power_torsion_coker`。telescope の simp 補題は audit_clmst が名前を書いているので残す。
- 変えない名前：`awayModuleMap`、`exists_uniform_pow_smul_zero`、`etaleAway_tensor_baseChange`、`doubleLocalizationTensorEquiv*`、`principalLocalizationTower_isLocalization`、`localizationComparison_awayMap_bijective_of_power_bounds`、`localizationComparison_ker_power_torsion`、`existsUnique_valuation_extension_of_integral_away_bijective`。
- 提出候補：`finiteAlgebra_exists_away_lift`（有限表示な代数から局所化への写像を主局所化まで下ろす。価値が高い）、有限生成な `Module.IsTorsion'` は一元で零化、`isLocalizedModule_of_comparison_power_torsion_coker`、`IsLocalizationLattice`、localization telescope、`existsUnique_extension_of_integral_away_bijective`、`principalLocalizationTower_isLocalization`。

## 7. D 平坦性・降下・同種写像・冪等元

規模：35 ファイル、約 3100 行。BS 約 20 本・CLMST 約 15 本の import。

| 新しいファイル | 元のファイル |
| --- | --- |
| Adic/Reduction | AdicFaithfulDescent・AdicFaithfulDescentAlgebra・PrincipalAdicFaithfulDescent・PrincipalAdicReductionAlgebra・PrincipalAdicReductionEquiv |
| Adic/ReductionScalarExtension | QuotientScalarExtension（HomologicalAlgebra.BaseChange に依存するので別） |
| CompletelyFlat/Basic | CompletelyFlat・CompletelyFlatEquiv |
| CompletelyFlat/PowerTorsion | CompletelyFlatPowerTorsion・CompletelyFaithfullyFlatPowers・CompletelyFaithfullyFlatTensor・CompletelyFaithfullyFlatInjective |
| CompletelyFlat/Criterion | CompletelyFlatCriterion・CompletelyFlatNilpotent |
| ScalarIsogeny | ScalarIsogenyInverse・ScalarIsogenyTensor・FiniteFreeScalarFactorization・FiniteProductIsogeny・ReducedFiniteFreeIsogeny・FinitePresentationIsogenyLift・PullbackAnnihilator |
| Idempotent | IdempotentAnnihilator・IdempotentImageAnnihilator・IdempotentImageBaseChange・ProductIdempotentQuotient |
| TensorProduct/BaseChange | FiniteProductBaseChange・TensorRingEquiv・PresentationBaseChange |

- 層の順序は Adic/Reduction → HomologicalAlgebra → CompletelyFlat/{Basic,PowerTorsion} → CompletelyFlat/Criterion。Adic/Reduction と Criterion を同じファイルにすると、HomologicalAlgebra の DerivedQuotientBaseChange・RegularPrincipalTor を経て循環する。
- 外へ回す：SeparableBaseChange → FieldTheory（FractionRingBasis と組む）。GenericEtale → エタール（E の Away と調整）。GeometricFiber・GeometricTransitivity → Galois・不変元（`Inputs/Descent` の近く）。FlatTensorFiltration → Adic/Completion。FlatRegularQuotient → 正則列。FinitePresentationTorsionCover・PresentationBaseChange → PowTorsion・LengthAlgebra 寄り。
- 降下定理の扱い（以前の方針「PrincipalAdicFaithfulDescent は並行コピーなので除去」は実態と合わない）：使われているのは主元版（`surjective_algHom_of_principal_residue_baseChange` を BS/Semiperfectoid/Surjectivity が使用、`principalAdicQuotientAlgebra` 52 件など）で、一般イデアル版の定理は外部参照 0 件。降下定理は一般イデアル版 1 本にし、主元版を `Ideal.map_span` を介した系にする。`principalAdicReductionEquiv` は `adicReductionEquivAlgebraQuotient ≪≫ Ideal.quotientEquivAlgOfEq` として定義する。
- Mathlib への置き換え（固定版と最新版に差なし）：`adicReductionMap` → `LinearMap.reduceModIdeal`（確度高、BS/CLMST の参照なし）。`adicQuotientAlgebra` は Mathlib の instance `Ideal.Quotient.algebraQuotientMapQuotient` と定義が同じ（BS 35 件なので deprecated な別名を経由）。`ker_pi_eval_eq_span_one_sub_single` → `RingHom.ker_evalRingHom`。`ideal_map_isIdempotent` → `IsIdempotentElem.map` と `Ideal.mapHom`。`tensorMapOfCompatibleBase` → `Algebra.TensorProduct.mapRingHom`。`quotientTensorReductionEquiv` は `quotTensorEquivQuotSMul` の `extendScalarsOfSurjective`（名前は残し本体を差し替え）。自前の `map_smul'` の証明 4 つ → `extendScalarsOfSurjective`。`baseChangeQuotEquiv` → `TensorProduct.AlgebraTensorModule.tensorQuotientEquiv` から作る（確度中）。`baseChangeIdealQuotientEquiv` はインライン化候補。
- 一本化：`exists_scalar_factorization_through_finiteFree` は `exists_scalar_inverse_of_ker_coker_annihilated` の特殊例。逆向きの一般補題を立てて `tensor_unit_ker_coker_annihilated` を短く。冪ねじれの仮定を `Module.IsTorsionBy` に統一（D3・D5・D6）。IdempotentImageAnnihilator の 4 変種を 2 つに、IdempotentImageBaseChange の 4 補題を 1 つに。`exists_free_quotient_powTorsion_cover` と ModuleCat 版を 1 つに。`tensorAction_mul`・`_one` を `MulSemiringAction` の instance に（確度中）。
- 未使用：`surjective_algHom_of_residue_baseChange`（確認済み）、`surjective_algHom_of_faithfullyFlat_adicReduction`、`surjective_of_faithfullyFlat_adicReduction`（提出候補として残す価値）、`adicReductionMap_comp_mkQ`、`adicAlgebraReductionMap_equiv`、`principalAdicReductionAlgEquiv_toAlgHom`、`power_torsion_lTensor_*`・`power_residue_lTensor_*` の 4 つ、`isCompletelyFlat_principal_ideal_pow`、`isCompletelyFlat_nilpotent_iff_flat`（提出候補）、`flat_of_acyclic_flat_nilpotent_reduction`、`ideal_annihilates_of_pow_annihilates_*` 2 つ、`finrank_perfectBaseChange`、`tensorMapOfCompatibleBase_tmul`、`tensorRingEquivOfCompatibleBase_tmul`。`@[simp]` 4 つは残す。audit_clmst だけが参照：`exists_finite_etale_away_of_separable_minpoly`、FlatTensorFiltration の中間補題 4 つ。
- 変えない名前：`IsCompletelyFaithfullyFlat`（BS 114 件）、`IsCompletelyFlat`、`GenericEtale.awayAlgebra`（CLMST 82 件）、`adicQuotientAlgebra`、`principalAdicQuotientAlgebra`、`IsGeometricallyTransitive`、`quotientModuleFunctor`、`quotientTensorReductionEquiv`、`quotientScalarExtensionEquiv`、`principalAdicReductionEquiv`。
- 提出候補：`surjective_of_faithfullyFlat_adicReduction`（AdicCompletion/Functoriality の隣）、`subsingleton_of_principal_power_torsion_of_reduction`（中山型）、冪零イデアルでは完全平坦 = 平坦（Tor₁ で書き直して）、冪等元の補題 2 つ、`exists_scalar_inverse_of_ker_coker_annihilated`、`range_rTensor_smul_top`、`finitePresentation_free_quotient_ideal_smul`、`AlgHom.pullback` が CommRingCat の pullback、`Algebra.TensorProduct.mapRingEquiv`、分数体の分離性の移送、不変元のノルム、generic étale。`IsCompletelyFlat` の定義は Mathlib の derived tensor が未整備なので時期尚早。
- リスク：CompletelyFlatCriterion を import する BS 11 本は Andre 系の重いモジュール。`adicQuotientAlgebra` を Mathlib の instance に替えると instance 探索の経路が変わる（`erw`・`change` を使う BS の証明はビルドで確認）。Criterion と Nilpotent の閉包は 62〜67 モジュールなので Basic と分ける。

## 8. H perfectoid・完全環・絶対整閉・tilt

規模：75 ファイル、約 6500 行、宣言約 240。BS 25 本・CLMST 33 本の import。

### 8.1 最優先：層の逆転の解消

- CommutativeAlgebra の一部が BhattScholze を import している：PerfectoidIdeal 系（→ `BS.Semiperfectoid.Perfectoidization`）、PerfectoidIdealCompatibleRoots・PerfectoidIdealCover（→ `BS.Semiperfectoid.CompatibleRootPerfectoid`）、AbsolutelyIntegrallyClosedPerfectoidQuotient（→ `BS.Semiperfectoid.Surjectivity`、閉包 71 モジュール）、Perfectoidization（→ `Inputs.Perfectoidization` → BS、閉包 682 モジュール）。
- PerfectoidTorsionQuotient が PerfectoidIdealPowers を import しているため、純可換環論の `IsIntegralPerfectoid.isReduced`・PerfectoidTorsionFrobenius・PerfectoidTorsionTilt まで BS 25 モジュールに依存している。原因は末尾の 1 定理 `perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid`（利用者は CLMST/CyclicTorsionComparison だけ）。これを perfectoidIdeal 側へ移せば依存が切れる。他の H の整理と独立に、小さな単独の変更として先に行える。
- BS に依存する層（P8：PerfectoidIdeal・Perfectoidization・PerfectoidizationMap・PerfectoidIdeal{Functor,Powers,Radical,CompatibleRoots,Cover,Pullback}・PerfectoidIdealCompatibility・AbsolutelyIntegrallyClosedPerfectoidQuotient・PerfectoidizationSupportedQuotient）は CommutativeAlgebra の外、BS と CLMST の間の層（例 `SerrePositivity/PerfectoidIdeal/`）へ出す。BhattScholze/ の中へは移せない。BS の `Almost/Lemma103`・`Almost/SupportedQuotient`・`Perfectoidization/Excision` もこれらを import するので、BS 内部の 2 層に挟まる位置になる。
- P1（普遍性）と P8 を同じファイルにすると循環する（BS `Semiperfectoid.Perfectoidization` が CA `PerfectoidizationFunctor` を import し、CA `PerfectoidIdeal` がその BS を import する）。AbsolutelyIntegrallyClosedPerfectoidQuotient も同様。

### 8.2 統合案（`CommutativeAlgebra/Perfectoid/` ほか）

| 新しいファイル | 元のファイル |
| --- | --- |
| Perfectoid/Defs（または Universal） | IntegralPerfectoid・PerfectoidizationUniqueness・PerfectoidizationFunctor・PerfectoidizationIdentity・PerfectoidizationAlgebraMap・PerfectoidizationQuotient・PerfectoidizationNilpotent（Nilpotent は Torsion の後に置く） |
| Perfectoid/Completion | PerfectoidizationCompletion・PerfectoidDerivedComplete（後者は HomologicalAlgebra を import するので別でもよい） |
| Perfectoid/Fontaine | PerfectoidFrobeniusCriterion・PerfectoidCharacteristicP・PerfectionIdempotents・PerfectoidFrobeniusKernel・PerfectoidFontainePrincipal・PerfectoidFontaineSeparation・TiltRootSeparation・WittPrincipalSeparation・CompatibleRootsTilt・CompatibleRootsPerfectoid |
| Perfectoid/Torsion | WittDistinguishedTorsion・PerfectoidPTorsion・PerfectoidRootTorsion・PerfectoidTorsionRoots・PerfectoidReduced・PerfectoidTorsionQuotient・PerfectoidTorsionFrobenius・PerfectoidTorsionTilt・PerfectoidTorsionPerfectoid・PerfectoidUntiltNaturality |
| Perfection | FrobeniusRootKernels・PerfectionPrincipalKernel・PerfectionKernelLift・PerfectionIdealCorrection・PerfectAnnihilator・PerfectionPrincipalQuotientKernel |
| PerfectRing | PerfectPowerReduced・PerfectRadicalIdeal・PerfectCoefficientTensor |
| PerfectPolynomial | PerfectPolynomial・PerfectPolynomialFlat |
| CompatibleRoot | CompatibleRootIdeal・CompatibleRootFamilyIdeal・CompatibleRootIdealFlat・CompatibleRootIdealTensor・CompatibleRootPerfectQuotient |
| AbsolutelyIntegrallyClosed/Basic | AbsolutelyIntegrallyClosed・AbsolutelyIntegrallyClosedFibers |
| AbsolutelyIntegrallyClosed/Etale | AbsolutelyIntegrallyClosedHenselian・Etale・EtaleCover・EtaleAwayCover |

- 外へ回す：FrobeniusHypersurfaceGrowth・FrobeniusKoszulLimit → B2。PowTorsion・PowTorsionCategory・BoundedPowerTorsionQuotient・FlatPowerTorsion・FlatPowerQuotientTorsion → 冪ねじれ・平坦（D）。PerfectNormality → 体論・正規性。PerfectTorIndependence/Basic → HomologicalAlgebra（CA から HomologicalAlgebra への逆依存を解消）。
- Mathlib への置き換え（固定版と最新版に差なし）：`perfect_pow_pow_bijective` → `bijective_iterateFrobenius`。`perfectPrincipalRoot` → `(iterateFrobeniusEquiv k p n).symm a`、`perfectPrincipalRoot_pow` → `iterate_frobeniusEquiv_symm_pow_p_pow`。`surjective_pow_prime_pow` は 2 行。`principalAnnihilator k a` は `(Ideal.span {a}).annihilator`、`pTorsionIdeal` は `Submodule.torsionBy` か同じ零化イデアル（CLMST が使い自ファイル内 56 箇所なので手間が大きい）。`perfectClosure_lift_of` は `symm_apply_apply`。`tiltRootEvaluation` を `((frobeniusEquiv _ p).symm^[n] x).untilt` で定義し直すと `tiltRootEvaluation_pow` は `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` そのもの。`pTorsionQuotientModPMap` は `modPMap` と定義上同じ。
- 一本化：`isReduced_of_perfectRing_charP` と `isReduced_of_perfectPower`。PerfectoidFrobeniusCriterion の特殊形の入口（N > 1 の一般形へ。BS の PerfectPrismPerfectoid が特殊形を使うので確認）。PerfectoidReduced の特殊化。PerfectoidCharacteristicP の `_of_charP`・`_of_p_eq_zero` の組。互換根の 3 系統（CA `compatibleRootsTilt`・BS `compatibleRootTilt`・`compatibleRoots_pow`・`exists_compatible_pow_roots`）を CompatibleRoot の小さな API に。単項イデアルの零化イデアルの 3 つ。BS の `isIntegralPerfectoid_of_ringEquiv` は本来 IntegralPerfectoid に置くべき補題（BS 側の判断）。
- 未使用：ファイルごと削除できるもの：PerfectoidIdealCompatibility（閉包 682）、AbsolutelyIntegrallyClosedEtaleIntegralCover、PerfectTorIndependence.lean（中身のない入口）。宣言（多くは監査ファイルが名前で参照しているので監査も直す。内部の段は private 化）：AIC の連鎖の中間 3 つと内部専用 5 つ（`henselianLocalRing` は残す）、perfectoidIdeal 系 7 つ、普遍性系 3 つ（`of_completion` は監査 1）、torsion 系 9 つ、Fontaine 系 5 つ（F7 監査の入口）、`bounded_power_torsion_decomposition`、`radicalIdeal_cotangent_subsingleton_of_perfectRing`、`perfection_principal_quotient_zero_branch`。instance `perfectPolynomialAlgebra`・`perfectPolynomialDirectedSystem` はビルドで確認。残すもの：`henselianLocalRing`、`IsAbsolutelyIntegrallyClosed.isAlgClosed`、`perfectPolynomialHomEquiv`、`ker_iterateFrobenius_eq_span`。
- 変えない名前：`IsIntegralPerfectoid`（BS 137 箇所）、`IsPerfectoidization` と `map`・`map_comp`・`map_id`・`map_map`・`lift`、`perfectoidIdeal`、`IsAbsolutelyIntegrallyClosed`、`modPMap`、`untilt_map`、`IsIntegralPerfectoid.isReduced`、`completionLift`・`completionMap`・`isAdicComplete`、`compatibleRootIdeal` 系、`mapAlgHom`、`Perfectoidization`、`coefficientTensorLift`。
- 提出候補：完全環は被約、Perfection の単元判定、完全環上の Witt の単元判定、`Perfection.map` の全射性と核の持ち上げ、完全環のテンソル積の `PerfectRing` instance、冪写像が全射な環の根基イデアルは冪等、分数体の完全性、`ModP` 間の写像と untilt の自然性（Perfectoid/Untilt 向け）、標数 p では ker θ = (p) と生成元の判定（FontaineTheta 向け）、`IsIntegralPerfectoid` の定義と被約性・p ねじれ、`IsAbsolutelyIntegrallyClosed`、`IsAdicComplete` への一意延長の一般化。
- リスク：`IntegralPerfectoid`・`PerfectoidizationFunctor` は BS の大半の祖先で、触ると全面的な再ビルド。P1 の統合は一回にまとめる。監査 audit_clmst・audit_clmst_b3・audit_f6・audit_f7・audit_bhatt_scholze_b5 が宣言名を参照（private 化すると `#print axioms` の対象から消える）。BS セッションの区切りに合わせて行う。

## 9. X どの群にも入っていなかった残り

規模：52 ファイル、約 5500 行（単独 28 本、RootTower/ 18 本、Almost/ 6 本）。

| 小群 | 新しいファイル | 元のファイル |
| --- | --- | --- |
| CubicCyclotomic | Algebra | CubicCyclotomicAlgebra・CubicCyclotomicFiber |
|  | LocalExtension | CubicCyclotomicClosedPoint の生きている部分・CoprimeFactorLocalization・LocalizedSurjectiveQuotient・CubicCyclotomicClosedFiber・CubicCyclotomicLocalFiber・CubicCyclotomicLocalExtension（互いに鎖状に import するので一緒に） |
| RootTower | Basic・MonomialBasis・Stage はそのまま | |
|  | Completion | Completion・CompletionFlat・Restriction |
|  | CompletedRoots | CompletedRoots・CompletedRepresentatives |
|  | ModP | ModPFrobenius・ModPInjectivity・ModPSurjectivity・ModPEquiv・ModPComparisonLength |
|  | Perfectoid | CompletedTilt・CompletedFrobenius・FrobeniusKernel・WittPresentation（CompletedRoots と分けるのは H・Witt の import を CLMST に持ち込まないため） |
|  | Koszul | そのまま（重い。利用者は Paper/Section2/CompletedTower だけなので Paper へ移す案も） |
| Almost | Basic | Zero・Morphism |
|  | Category | Category・TorsionCategory・SerreComparison |
|  | Quotient | そのまま（BS が import） |
| Support | Closed | ClosedSupportGeometry・PrincipalSupport・ModuleClosedSupport（B2 の台の補題・SupportHeight も寄せる案。ClosedSupportGeometry は InfinityCategories・KTheory に広く import されるので、統合先の名前を既存のまま残す手もある） |
| ReducedSpectrum | ReducedSpectrum | FiniteSpectrumPartition・ReducedPrincipalVanishing・ReducedSectionImage（D の IdempotentAnnihilator・ProductIdempotentQuotient と同居の候補） |

- 他の群へ：ConductorQuotient・TraceConductor（`Conductor.lean`）・GaloisNormalization → Paper 層。AlgebraMapCokernel → B。PrincipalMaximalFactorization・RootTower/Restriction の `maximalIdeal_map_le_of_finite_of_injective` → C。LocalResidueLinearMap・MappedPrincipalQuotient → D（後者は PrincipalAdicReduction と同居）。PrincipalAlgebraIsomorphismLocus → E（FiniteAlgebraLift と）。PrincipalQuotientAnnihilator → H。CoefficientTensorAutomorphism → PerfectCoefficientTensor の隣。DerivedSingleTrianglePullback・MinimalGenerators → HomologicalAlgebra。FractionRingBasis → FieldTheory か SeparableBaseChange と。SubmoduleExact → KTheory か LinearAlgebra。
- 削除してその場に書く：QuotientBaseChange（`quotientBaseChangeEquiv` は Mathlib の `TensorProduct.tensorQuotMapSMulEquivTensorQuot` と型が同じ。利用は FlatLocalDimension の 1 か所）、AlgebraAction（`MulSemiringAction.toAlgAut` と `AlgHom.comp_algebraMap` から出る。利用 3 本）。
- Mathlib：GaloisNormalization の `isSeparable_normalClosure` は最新版の instance `IntermediateField.normalClosure.isSeparable` で、Mathlib を上げたら削除。`cubicCyclotomicPolynomial` を `Polynomial.cyclotomic 3 R` の abbrev に（約 30 参照）。MinimalGenerators の `rank` → `spanFinrank`（`TensorProduct.spanFinrank_top_eq_of_residueField`）、`π_surjective` → `IsLocalRing.span_eq_top_of_tmul_eq_basis`。`quotientSmulCokerEquiv` → `DoubleQuot.quotQuotEquivQuotSup` と `quotEquivOfEq`。AlgebraMapCokernel は中身だけ簡単に（CLMST が使うので名前は残す）。
- 一般化：CubicCyclotomic の局所拡大は「monic な f と剰余体での互いに素な分解 f̄ = g·h（g 既約）」だけを使っているので、一般の局所拡大として書き、「3 が単元」の部分だけを特殊に残す。`principalSupport_add` は閉台の族一般の補題。ConductorQuotient と TraceConductor は「共通分母 g で gC ⊆ B」という一つの話。
- 未使用：CubicCyclotomic 系 13 前後（ClosedPoint はファイルの大半が死んでいる）、RootTower 系 8 前後（CompletedTilt の死んだ枝など。audit/shared の assertion も削除）、TraceConductor・ReducedSectionImage・MappedPrincipalQuotient の各 1、Almost 系 6 前後（`IsAlmostZero.bot` などはドット記法での利用を個別に確認）。
- 変えない名前：RootTower の名前空間 `SerrePositivity.Section2`（CLMST で `CompletedTower` 754 箇所、`TowerStage` 181 箇所）。
- 提出候補：LocalResidueLinearMap（剰余体でのテンソルが全単射なら全単射）、整域を仮定しない主極大イデアルの分解、`AdjoinRoot.map_mk`・`map_surjective`、FiniteSpectrumPartition・ReducedPrincipalVanishing、SubmoduleExact、RootTower/MonomialBasis、CoefficientTensorAutomorphism、ConductorQuotient。
- リスク：RootTower/Stage・Completion・CompletionFlat は CLMST の大部分の上流にあり、触ると CLMST 全体が再ビルド。ファイル統合だけで CLMST 約 12 本の import 行が変わる。

- 決定（2026-10-30、ユーザー、X の軽い小群）：
  (1) CubicCyclotomic の局所拡大を「monic な f と剰余体での互いに素な分解 f̄ = g·h（g 既約）による局所拡大」の一般論に書き直す。
  三次円分に固有の部分（3 が単元）だけを特殊に残す。IntersectionMultiplicity・PerfectComplex の約 30 参照への波及も合わせて直す。
  (2) `cubicCyclotomicPolynomial` を `Polynomial.cyclotomic 3 R` の abbrev にする。
  (3) Support の統合先は新しい `Support/Closed`（ClosedSupportGeometry の名前は残さない。InfinityCategories・KTheory の import 行を
  書き換え、その範囲の再ビルドを伴う）。
  (4) CommutativeAlgebra/Almost と LengthAlgebra/Almost* を一つの群として整理する（置き場所はその作業で決める）。
  (5) BhattScholze が import する DerivedSingleTrianglePullback・MappedPrincipalQuotient・CoefficientTensorAutomorphism の移動は、
  BhattScholze 側を再ビルドする別の作業に回す（Koszul・KoszulResolution の移動と同じ扱い）。

## 10. 順序の案

1. B1（BS/CLMST への影響が最小）
2. B2 と C3 を同時に（Koszul オイラー標数の移動と RegularLocalRing の再編が絡む）。C1・C2 の全依存ビルドとコミットもここで合わせる
3. X の軽い小群（CubicCyclotomic・Support・Almost・Conductor と GaloisNormalization の Paper 層への移動、QuotientBaseChange・AlgebraAction の削除）
4. E
5. D
6. H と RootTower（BS/CLMST への影響が最大。BS セッションの区切りに合わせる）。ただし §8.1 の定理 1 本の移動は小さいので、早めに単独で行ってよい

そのあと PerfectComplex、KTheory。群をまたぐ共通の置き換え（`stableFiltration`・`fwdDiff`・`reduceModIdeal`・`Module.IsTorsion'`・`LocalizedModule.map`・Frobenius の反復 API）は、それぞれ該当する群の中で行う。
