# PerfectComplex の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/PerfectComplex/`（124 ファイル、約 9400 行）について、ファイルの統合、
未使用の宣言の削除、Mathlib への置き換え、重複の一本化、Mathlib への提出候補をまとめる。
群ごとの調査（2026-10-30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：作業の決まり（ビルド、BS/CLMST の扱い、監査、改名しない名前）は
[commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行った。提出候補は
[mathlib-upstream.md](mathlib-upstream.md) に移してから扱う。
使われ方：作業を再開するときの手順書。KTheory の計画 [ktheory-refactor-plan.md](ktheory-refactor-plan.md) と
一般化（位数 n の作用、n 重テンソル）を共有するので、両方を合わせて読む。

## 1. 群の分け方

| 群 | 内容 | ファイル数 |
| --- | --- | --- |
| PC1 | 基礎：完全複体、閉台、K₀、Euler 標数、分解、Koszul、長さ | 45 |
| PC2 | テンソル積：二重・三重・六重、shuffle、巡回和 | 36 |
| PC3 | 作用と固有分解：位数 3 の作用（Cubic*）、Fourier、involution（位数 2）、冪等元 | 43 |

BS への依存は三群とも直接・推移的にない。CLMST は PC1 の 11 ファイルに LengthAlgebra 経由で推移的に依存する（§2）。

KTheory へ回すもの（PC1 の IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions）は KTheory の計画で受け入れる。

## 2. PC1 基礎

規模：45 ファイル、5868 行。中身は 6 つの層が混ざっている：(a) 正規化長さ、(b) 自由モデル（論文 Lemma 3.5 の語彙）、
(c) 有限射影ホモトピー圏、(d) 閉台 K₀、(e) Koszul 長さの評価、(f) KTheory に依存するもの。
BS への依存はない。CLMST は直接 import しないが、LengthAlgebra 経由で 11 ファイル（Basic・Closure・K0・NormalizedEuler・
NormalizedLength・NormalizedLengthComap・OrdinaryEuler・QuotientLength・SupProperty・SupPropertyComap・Support）に推移的に依存する。
NormalizedLength を変えると 587 モジュール（うち CLMST 27）、Basic・Support・K0 はそれぞれ約 500 モジュールが再ビルドになる。

### 2.1 統合（45 → 約 15 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換用の import ファイル 4 本：CochainBiproduct・ConeArrowMap・DegreewiseKernelLift・TwoTermScalarMap（利用者は HomologicalAlgebra.Cochain* を直接 import する） |
| Free/Support | Basic（IsSupported、twist）・Support |
| Free/K0 | Closure・K0（IsPerfectSupported、PerfSupp、K0Supported） |
| Free/Euler | Basic の `chiOrd`・`chiLam` の定義・NormalizedEuler・OrdinaryEuler |
| Free/KoszulGeneration | KoszulGeneration（そのまま） |
| Perfect/HomotopyCategory | HomotopyCategory・BaseChange・DegreewiseRetract・BiproductPerfect の strictlyPerfect の部分・ClosedSupportRelations 冒頭の K 射影性の 2 補題 |
| Perfect/FreeComparison | K0Comparison・K0Functoriality |
| Perfect/KoszulTower | KoszulTower（そのまま） |
| ClosedSupport/Basic | ClosedSupport・`HasHomologySupportOn.biprod` |
| ClosedSupport/K0 | ClosedSupportK0・ClosedSupportCongr・ClosedSupportRelations・ConeAdditivity・ClosedSupportBiproduct の `mk_biprod`（`mk_tensor` は PC2 の ClosedSupportCup へ） |
| ClosedSupport/Functoriality | ClosedSupportFunctoriality・ClosedSupportComparison |
| KoszulLength | KoszulLengthBounds・ProjectiveBounds・KoszulAmplitude・MinimalLowerBound |

- 外へ：正規化長さ（NormalizedLength・NormalizedLengthComap・SupProperty・SupPropertyComap・QuotientLength。複体を使っていない）→
  LengthAlgebra（例 `LengthAlgebra/Normalized/`）。IntegerEuler・IntegerEulerIso・CoefficientEuler（KTheory の HomologyEulerBasic・
  SupportedCoefficients を import）と namespace `Adams` の KoszulOneModel・KoszulTensor・KoszulClasses（利用者は KTheory/Adams だけ）→
  KTheory。FiniteProjectiveResolutions（KTheory から 20、InfinityCategories から 4）→ KTheory。AsymptoticLengthBounds・
  ResolutionFamilies → Asymptotic。FinThreeBiproduct（利用者は CubicActionTensorClass だけ）→ §2.3 の一般化か Cubic 側。
- 循環：BiproductPerfect が import している互換ファイル `PerfectComplex.IdempotentDecomposition` を外し、HomotopyCategory と
  ClosedSupport を直接 import すれば閉路は 0（そのままだと IdempotentImage → ClosedSupportRelations で閉路）。

### 2.2 Mathlib との重なり（固定版と最新版で差なし）

- `finiteProjective_exists_retract` の本体 → `Module.Finite.exists_comp_eq_id_of_projective`（RingTheory/Finiteness/Projective.lean）。確度高。
- `strictlyPerfectComplex_isKProjective`（利用 12）・`strictlyPerfectComplex_quasiIso_iff`（利用 9）は
  `CochainComplex.isKProjective_of_projective`・`IsKProjective.quasiIso_iff` の包み。利用が多いので残す。
- `chiOrd`・`lambdaEuler` の交代和は Mathlib の `HomologicalComplex.homologyEulerChar`・`ComplexShape.EulerCharSigns` と同じ形だが、
  Mathlib 側は finrank 専用。符号を `EulerCharSigns` に揃えることはできる。
- `IsPerfectSupported.bounded`（∃ a b）の繰り返しを `IsStrictlyGE`・`IsStrictlyLE`（プロジェクトの `strictlyBoundedComplex`）に統一。
- `HasFiniteProjectiveResolutions` は Mathlib の `ObjectProperty.hasFiniteResolutionOfLength`・`HasProjectiveDimensionLE` で
  言い換えられる可能性（確度中）。
- Mathlib にないもの：三角圏の K₀（プロジェクトの CategoryTheory/TriangulatedK0）、Serre 類についての homological kernel。

### 2.3 一本化（群の中で同じ構成が繰り返されている箇所）

- K₀ のモデルが 3 つ（自由モデル `K0Supported`、列で台を指定した `TriangulatedK0 (SupportedPerfectHomotopy z)`、閉台の
  `K0WithSupport Z`）と比較が 2 つ。基底変更と群作用もそれぞれに書かれている。一般形は K₀ を `K0WithSupport Z` だけにし、
  列の台は Z = V(z)、ひねりは環自己同型に沿った `K0WithSupport.map`、自由モデルは「局所環上では有限自由な代表がとれる」補題に格下げ。
  ただし `K0Supported` は Inputs/Descent の引用（`theorem_3_1_K0`）と Paper/Lemma3_5 の文に現れるので、引用の文言を変える判断が要る。
- 台の条件が 4 つ（IsSupported、`scalarSupported`、HasHomologySupport I、HasHomologySupportOn Z）。本体は HasHomologySupportOn だけにし、
  IsSupported は有限射影複体での同値補題として残す。`HasHomologySupport I` は `HasHomologySupportOn (supportZeroLocus I)` と Iff.rfl
  （外部利用 8）なので abbrev か削除。
- 閉包補題が 4 系統 × 6 操作（iso・shift・zero・mappingCone・baseChange・twist）。「複体の ObjectProperty が iso・シフト・錐で
  閉じていれば三角部分圏と K₀ が得られる」を一度示し、`⊓` で組み合わせる。閉台については Serre 版 homologicalKernel を使う。
  `perfectHomotopySupportedOn` の `IsTriangulatedClosed₃` は既存の `homotopyProperty_isTriangulatedClosed₃` と同じ議論の繰り返し。
- 双積の類の公式が二項版（`mk_biprod`）と Fin 3 専用版（`mk_finThreeBiproduct`）。`[⨁ i, P i] = ∑ i, [P i]`（Fintype 添字）一本に。
- Euler 評価が 4 種類（`chiOrd`・`chiOrdHom`・`integerEuler`・`lambdaEuler`/`chiLam`）。加法的な長さ λ についての `lambdaEuler` 一本にし、
  整数値の版はキャストとの両立補題に。ただし CLMST/SourceEulerEvaluation が `unfold lambdaEuler chiOrd` と `toReal_toENNReal` を
  使っているので、`chiOrd` の定義を変えると壊れる。
- O と o の対が 4 組そのまま複写されている。「v ≤ Σ r·c で c が有限なら O」を一本にし、o は `.trans_isLittleO` で合成する。
- 自由版と直和因子版が並んでいる（`lambdaHomology_koszulComplexOn_le_sum` と `_of_retracts` など）。直和因子版だけを残し、
  自由版は `Retract.ofIso` で導く。`lambdaHomology_ne_top_of_retract` は `ne_top_of_le_ne_top` と `lambdaHomology_le_of_retract` の組合せ。
- Koszul 複体の所属を示す補題が 3 つの K₀ モデルそれぞれにある（`koszulPerfSupp`、`perfectKoszulObj`、`koszulClass`）。
- `strictlyPerfectComplex_biprod` と `HasHomologySupportOn.biprod` は分裂短完全列の特殊例として導ける。
- `NormalizedLength.restrict`・`comap`・`restrictToBase` を一本の `comap` に（CLMST が `lam.comap f _ le_rfl` を使うので旧シグネチャは
  包みとして残す）。単調性の補題群は CategoryTheory/AdditiveLength と CommutativeAlgebra/PowTorsionCategory の組合せと重複。
- `twist` の補題群は `baseChange_smul_iso_twist` を通せば基底変更の補題から導ける。

### 2.4 未使用

- 削除候補：`perfectKoszul_homological_vanishing`、`exists_common_pow_annihilator_of_homologySupport` とそれだけが使う
  `homology_pow_torsion_of_support`、`mk_degreewise_shortExact`、`freeToClosedSupportK0_map`、`scalarClosedSupportK0Equiv_mk`（`@[simp]`）、
  `resolutionFamily_term_iso`、`resolutionFamily_rank_isLittleO`、`perfectK0_smul_mk`。
- 慎重に扱う：rfl の `@[simp]`（`hasHomologySupportOn_zeroLocus`、`restrict_len`、`cochainFinThreeProjection_zero/one/two`）、instance
  （`hasFiniteProjectiveResolutions_regular`、`perfectK0DistribMulAction` は `g • x` の解決に暗黙に使われる）。
- 再利用価値：IntegerEulerIso の後半（`integerEulerEquiv` : K₀^m(R) ≃+ ℤ など）は外部未使用だが定理としてきれい。外部で使われているのは
  `maximalFreeClosedSupportEquiv` と `maximalSupport_hom_ext_koszul`（KTheory）だけ。`integerEuler_mk` は `@[simp]` にする価値あり。

### 2.5 提出候補

1. 加法的な長さ関数についての Euler 標数と、写像錐・短完全列での加法性（Mathlib の EulerCharacteristic.lean を finrank 以外へ一般化）。
2. 有界な有限射影複体（K^b(proj)）の ObjectProperty と `IsTriangulated`、K 射影性・擬同型とホモトピー同値の一致。
3. Serre 類 S とホモロジー関手 H について {X | ∀n, H(X⟦n⟧) ∈ S} が三角部分圏（Mathlib の `homologicalKernel` の一般化）。閉台条件の
   instance がすべてここから出る。
4. 三角圏の K₀（CategoryTheory/TriangulatedK0、別の群の管轄）。
5. 確度中：`Module.support` の閉集合版の補題、`ennreal_isBigO_of_le_sum_nsmul` 型の漸近評価。

### 2.6 リスク

- 変えない名前：CLMST が参照する `NormalizedLength`、`.comap`、`IsPowTorsion.comap`、`lambdaEuler`（6 ファイル 15 箇所）、`chiOrd`、
  `toReal_toENNReal`。
- 監査スクリプトが宣言名を直接書いている：`scripts/audit_triangulated_k0_shift_shared.lean`（`mk_shift`）、
  `scripts/audit_homotopy_cone_representative_shared.lean`（`perfectFreeRepresentative_triangle`・`perfectToFreeK0`・
  `ClosedSupportShortExactAdditive`）、`scripts/audit_clmst.lean`（`HasSup`・`NormalizedLength`）。
- IntegerEuler 系は KTheory.HomologyEulerBasic → ClosedSupportK0 に依存するので、PerfectComplex 側に残したまま統合しない。
- Basic・Support・K0 は約 500 モジュールの上流。統合は一回の全依存ビルドにまとめる。

## 3. PC2 テンソル積

規模：36 ファイル、約 1300 行。うち 21 本は 5〜8 行の互換スタブで、`HomologicalAlgebra/CochainTensor*.lean`（34 本、3435 行）を
再輸出しているだけ。テンソル積の構成そのもの（二重・三重・四重・六重、shuffle、対称性、六角形、回転）は HomologicalAlgebra 側にある。
BS/CLMST は PC2 の 36 本を import しない。参照は HomologicalAlgebra の `cochainTensor` と `cochainTensor_isStrictlyLE` の 2 つだけ
（BS の RootEnvelope/Source・Andre/Envelope/MonicSource・PowerRootEnvelope/Unconditional/Source）。

### 3.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換スタブ 21 本：Tensor・TensorBoundedAbove・TensorCone・TensorDegreeMaps・TensorHomogeneous・TensorScalarCoordinates・TensorShift・TensorShortExact・TensorShuffle・TensorShuffleEquivariance・TensorSingle・TensorSix{Homogeneous,Rotation,Shuffle,ShuffleEquivariance}・TensorSymmetry・TensorTriple・TensorTriple{BaseChange,DegreeMaps,Differential,ShortExact}。利用者の import を HomologicalAlgebra の実体へ張り替える（Tensor.lean は ClosedSupportRelations も再輸出しているので、TensorPerfect と TwoTermScalarMap にその import を足す） |
| Tensor/Perfect（約 160 行） | TensorPerfect・TensorHomotopy・TensorAcyclic・TensorSupport |
| Tensor/CyclicSum（約 290 行） | CochainCyclicThree・TensorTripleCyclicSum{,Perfect,Eigen,Class}（PC3 の CubicAction と一体で動かす案も） |
| ClosedSupportCup | TensorK0・TensorEnlarge・TensorBaseChange（`K0WithSupport.cup`。PC1 の ClosedSupport/K₀ と同居） |

- 外へ：TensorTorComparison → IntegerEuler・IntersectionMultiplicity（唯一の利用者は AdamsVanishing）。TensorResolutionLength →
  NormalizedLength・Asymptotic（テンソル複体の話ではない。利用者は Paper/Section2/TowerApproximation と MinimalLowerBound）。
  RankOneTensorTripleExt → 唯一の利用者 KTheory/Adams/KoszulCubeExt に吸収するか ModuleCat の一般ファイルへ。
- HomologicalAlgebra 側の統合案（HomologicalAlgebra の見直しへ申し送り）：`HomologicalAlgebra/CochainTensor/` に
  Basic（Tensor・Linear・Bounds・Finite・Projective）、Symmetric（Symmetry・Hexagon・Braided）、Shuffle（Shuffle・Homogeneous・
  ShuffleEquivariance・Triple・Six*）、DegreeMaps、ShortExact、BaseChange、Cone・Shift・Single・Acyclic。

### 3.2 Mathlib との重なり（固定版と最新版で差なし）

- 既に Mathlib の単項的構造（Algebra/Homology/Monoidal.lean）の薄い包み（確度高）：`cochainTensor` = `HomologicalComplex.tensorObj`（`⊗`、
  107 ファイル、BS 3）、`cochainTensorMap` = `⊗ₘ`（88）、`cochainTensorIso` = `tensorIso`、`cochainTensorAssociator` = `α_`、
  単位・単位子 = `𝟙_`・`λ_`・`ρ_`、`cochainTensorMap_comp` = `tensorHom_comp_tensorHom`、`cochainTensorMap_id` = `id_tensorHom_id`、
  `cochainTensorMap_add_left` = `MonoidalPreadditive.add_tensor`。`cochainTensor` は BS が使うので残し、それ以外は段階的に記法へ寄せる
  （利用の多いものは `@[deprecated] alias` を経由）。
- `cochainTensorSymmetry` は `β_` そのもの（自前の `cochainTensorSymmetricCategory` インスタンス）。Mathlib に Koszul 符号付きの
  組みひもは HomologicalComplex 上にない。部品（`mapBifunctorFlipIso_hom_naturality`、`totalFlipIso`）で naturality を短くできる（確度中）。
  `cochainTensorSymmetry_inv` は `SymmetricCategory.braiding_swap_eq_inv_braiding` から（確度高）。
- `cochainTensorShuffle P Q T U` は `MonoidalCategory.tensorμ P Q T U` と同じ（確度高）。四変数の `cochainTensorShuffle_symmetry` は、
  Mathlib にある特殊形 `SymmetricCategory.tensorμ_braid_swap` から（P Q P Q）の形が出る（確度中）。
- `cochainTensorSixShuffle` は μ を二回重ねたもの（`tensor_μ`）。`_rotation` は「`tensor C` が組みひも付き」と μ の結合律から出る
  （Mathlib に `(tensor C).Braided` のインスタンスはない）。
- `cochainTensorRotation_cube`（回転の三乗が恒等）は六角形と β² = 1 から。
- `cochainTensorDegreeMap` は `GradedObject.Monoidal.tensorHom` の成分（確度中）。
- 線形性の instance `complexMonoidalPreadditive`・`complexMonoidalLinear` は自前（Mathlib にない）。

### 3.3 一本化

- whisker の ext 補題 4 本（`cochainTensorX_whiskerRight_hom_ext` など）は、余積を保つ関手 G についての一本に（確度高）。
- `apply_ι_of_sum` 型の補題 7 種類を、中間次数を一般の s で書く基本形にそろえる。
- 二重版と三重版の並行（DegreeMaps・ShortExact・ScalarCoordinate・BaseChange）：二重版を「固定した複体との `tensorLeft`・`tensorRight`
  関手」の性質として書き、三重版は合成で得る。短完全列は「次数ごとに分裂する短完全列を加法的関手が保つ」一本に。
- 符号付きの元計算による組みひも・結合子の等式（`cochainTensorShuffle_exchange_sign`、`cochainTensorSixShuffle_rotation_sign`、
  `cochainTensorRotation_cube` など）：元計算が本当に要るのは六角形と β² = 1 だけ。「対称圏で X ↦ X^{⊗n} は対称モノイダル関手で、
  μ は Sₙ 同変」という一般論を一度書けば、二乗・三乗は具体化になる（HomologicalAlgebra 側で約 500 行減る見込み）。
- 台・完全性の補題の組（`*_perfect`・`*_support`）は「strictly perfect で台が Z の複体全体はテンソルと直和で閉じる」を
  ObjectProperty として一度宣言する。

### 3.4 未使用

- 削除候補：`K0WithSupport.cup_enlarge_left`・`_right`、`cup_add_left`・`_right`、`tensorClass_concrete`、
  `moduleRankOne_smul_generator`（private 化でも可）。HomologicalAlgebra の `cochainTensor_d_comp_d`（参照 0）。
- 残す：`K0WithSupport.cup_comm`・`cup_assoc`、`tensorResolutionTorIso`。
- private 化：TensorResolutionLength・TensorTorComparison の証明の段（外部で使うのは `integerEuler_cup_resolutions_of_finiteTensor` など）、
  `cochainTensorScalarNullHomotopy`、cyclic sum の補助の同型。

### 3.5 提出候補

1. Koszul 符号付きの `SymmetricCategory (CochainComplex C ℤ)`（Riou の BifunctorFlip・TotalComplexSymmetry の続き。六角形の証明を
   ModuleCat の元から圏論的な証明へ書き直す必要がある）。価値が最も高い。
2. `MonoidalPreadditive`・`MonoidalLinear (HomologicalComplex C c)` と `smul_tensor` 型の補題。
3. 対称圏 C について `(tensor C).Braided`、四変数の `tensorμ` と組みひもの可換性、巡回回転の三乗が恒等。
4. 組みひも付きモノイダル関手 F について `F.mapHomologicalComplex` も組みひも付きモノイダル。
5. 有界な平坦複体とのテンソルが擬同型を保つ（HomologicalAlgebra の CochainTensorAcyclic）。

### 3.6 リスク

- BS の再ビルドは起きない見込み（推移的閉包は `lake` のグラフで要確認）。HomologicalAlgebra の `cochainTensor`・`cochainTensor_isStrictlyLE`
  は改名しない。
- `cochainTensorShuffle` を `tensorμ` に置き換えると、`change` で書かれた元計算（`_apply_ι` 系）が壊れうる。先に圏論的な等式を用意する。
  利用者は KTheory/Adams の約 15 ファイル（`cochainTensorRotationIso` 13、`cochainTensorShuffle` 10）。
- `set_option backward.isDefEq.respectTransparency false` を統合後のファイルでそろえる。

## 4. PC3 作用と固有分解

規模：43 ファイル、2266 行（Cubic 21 本 1395 行、Involution 9 本 696 行、Idempotent 13 本 175 行。Idempotent のうち 8 本は 5〜6 行の
互換 import ファイル）。土台は `HomologicalAlgebra/CochainIdempotent*`（12 本、779 行）で、この群はその上に完全性・台・K₀ 類を足した層。
利用者は KTheory/Adams（TensorSquare* 11、TensorCube* 8、KoszulCube* 4 など）と PerfectComplex の CochainCyclicThree・TensorTripleCyclicSum*・
BiproductPerfect・ClosedSupportBiproduct・FinThreeBiproduct。BS/CLMST の import・参照はない。

### 4.1 統合（`PerfectComplex/Eigen/`）

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換 import 8 本：IdempotentDecomposition・FiniteSum・Image・ImageFunctor・ImageIso・ImageQuasiIso・ImageShortExact・Sum（利用先は HomologicalAlgebra.CochainIdempotent* を直接 import） |
| Eigen/Idempotent（約 130 行） | IdempotentImagePerfect・IdempotentImageClass・IdempotentImageTrivial・IdempotentTensor |
| Eigen/Involution（約 250 行） | InvolutionDecomposition・Maps・AntiEquivariance・ShortExact・BaseChange・Class・ClassAcyclic・ClassShortExact |
| Eigen/InvolutionTensor（約 250 行） | InvolutionTensor・InvolutionTensorClass |
| Eigen/Cubic（約 400 行） | CubicActionBasic・Projector・Decomposition・Character・Eigenvectors・Transport・BaseChange |
| Eigen/CubicClass（約 300 行） | CubicActionClass・ClassMaps・ShortExact・BiproductClass・ScalarClass・IdentityClass |
| Eigen/CubicTensor（約 300 行） | CubicActionTensor・TensorProjectors・TensorRows・TensorEigen・TensorClass |

- CubicFourierTransform・CubicFourierEigen（184 行）は群外からの参照がない（KoszulCubeFourierOne が import するだけ）。削除候補。ただし
  KTheory 計画 §3.3 は「Fourier 座標を行列 F で計算する」ためにこのファイルを使う案を出しているので、KT2 の作業と合わせて
  「環 R 上の位数 n の巡回群の離散 Fourier 変換」として作り直すか削除するかを決める。
- 外へ：CubicFourierMinorIdentities の残り 4 本（純粋な環の恒等式、KTheory/Adams だけが使う）と `cubicCharacter*` → CommutativeAlgebra の
  CubicCyclotomic（`cube_eq_one_of_cubic_relation` の隣）。`K0WithSupport.mk_eq_zero_of_isZero` → ClosedSupport/K0。
  CochainCyclicThree・TensorTripleCyclicSum*・FinThreeBiproduct は Eigen/ に合流させてよい。HomologicalAlgebra/CochainIdempotent* の統合
  （例 3 本へ）は HomologicalAlgebra の見直しで行う。
- 循環：BiproductPerfect・ClosedSupportBiproduct・FinThreeBiproduct は互換 import を経由してこの群の下層に依存している。Eigen/Idempotent は
  この 3 本に依存させず、CubicClass・InvolutionTensor・CubicTensor は上層に置く。

### 4.2 Mathlib との重なり（固定版と最新版で差なし）

- `cubicCharacter t j := t ^ (j : ℕ)` は `AddChar.zmodChar 3 ht j`（確度中。証明 `ht` を引数に取るので KTheory 12・PC 67 箇所の書き換えが要る）。
- 指標射影の直交性と和が 1（`characterProjector_orthogonal`・`sum_character_projectorMap`）は環 `End K` の `CompleteOrthogonalIdempotents`
  （RingTheory/Idempotents.lean）そのもの。`End K` には `Ring`・`Algebra R` のインスタンスがある。射影はすべて τ の多項式で可換なので
  積の順序は問題にならない。
- `map_invOf_two`・`map_invOf_three` は `map_invOf` と `map_ofNat` から一般形 1 本に（確度高）。
- `scalarMatrixThree` = `Matrix.toLin'`、`cubicVectorRotation` = `LinearMap.funLeft`（どちらも未使用なので削除が先）。三点の Fourier 変換は
  `ZMod.dft` に当たるが係数が ℂ 限定。指標の和の補題 `AddChar.sum_eq_ite`・`IsPrimitiveRoot.geom_sum_eq_zero` は `IsDomain` が要るので
  使えず、「`IsUnit (a - b)` から直交性」という現状の書き方が妥当。
- 自明な指標の射影は `GroupAlgebra.average`。指標で捻った版は Mathlib にない。冪等元の像の擬同型は既に `quasiIso_of_retractArrow` を使っている。

### 4.3 一本化

- `positive`・`negative` を対で書いた補題（naturality・ImageMap・ShortComplex・BaseChangeIso・TensorIso・class）は、射影 e についての
  CochainIdempotent 版の補題を直接使えば各 1 本。
- InvolutionTensor の直交性 4 補題は `CochainIdempotent.tensor` の直交性 1 本に。
- 二項和（Involution 側の `orthogonalSum`）と有限和（Cubic 側の `imageFiniteSumIso`）の二重は有限和に揃え、二項は `Fin 2` で代用。
- CubicActionIdentityClass は ScalarClass の j = 0 版を 7 本並べただけ。`weightedK0Class_of_map_eq_id` 1 本を残す。
- InvolutionClassAcyclic・InvolutionClassShortExact は §4.5 の重み付き類に吸収。
- `change`・`rw` を長く連ねた証明（`positive_tensor_map` など）は `End` 環での `module`・`noncomm_ring` で短く。

### 4.4 未使用

- CubicFourierTransform・CubicFourierEigen 全体（§4.1 の注意つき）、CubicFourierMinorIdentities の `cubicFourierMinor_difference_product`・
  `cubicFourierDeterminant_normalized`、CubicActionIdentityClass の 6 本、`characterShortComplex`・`_shortExact`、`tensorCharacterDecompositionIso`、
  `characterBaseChangeIso_hom_inclusion`。Involution 側：`positiveShortComplex`・`negativeShortComplex` と `_shortExact` 4 本、
  `positive/negativeBaseChangeIso_hom_inclusion`、`positive/negativeTensorIso_hom_inclusion`、`positivePositive` ほか 4 本の abbrev、
  `positiveClass`・`negativeClass`（自ファイル内だけ）。IdempotentTensor の `tensor_image_perfect`・`tensor_image_support`。
- `@[simp]` の `scalar_map` は参照 0 だが simp 集合が変わるのでビルドで確認。`CochainCubicAction.ext` は KoszulCubeFourierModelClass が使うので残す。
  `comapIso`・`comapIso_hom` は `scripts/audit_adams_action_transport.lean` が名前を書いているので残す（KTheory 計画 §4.4 では KT3 の削除で
  利用者がいなくなるとしているので、その時点で監査と合わせて判断）。

### 4.5 位数 n の作用への一般化（KTheory 計画 §5 と共通）

involution（n = 2、固有値 ±1）と cubic action（n = 3、固有値 1・t・t²）は、射影の定義、冪等性、`e ≫ τ = ζ • e`、自然性、直交性、和が 1、
分解の同型、底変換、短完全列、非輪状、擬同型不変、テンソル積の分解、K₀ 類の積公式を一から別々に書いている。`positiveMap = ½(1 + τ)` は
`projectorMap a = ⅓(1 + a²τ + aτ²)` の n = 2 版、`InvolutionClass.k0Class = [正] − [負]` は `weightedK0Class` で E = ℤ・ζ = −1 とした
もの、`InvolutionTensorClass.k0Class_tensor` は `weightedK0Class_tensor` の n = 2 版。

一般形は 3 層：

1. 環の層（CommutativeAlgebra か RingTheory。提出候補）：R 代数 A の元 u で uⁿ = 1、`[Invertible (n : R)]`、ζ について
   `∀ k, 0 < k < n → IsUnit (1 − ζ^k)` のもとで、`eigenProjector u ζ j := ⅟n • Σ_{k<n} ζ^{−jk} • u^k` が
   `CompleteOrthogonalIdempotents` で、`u * e_j = ζ^j • e_j`、可換な u, v について `e_l(u ⊗ v) = Σ_i e_i(u) ⊗ e_{l−i}(v)`。
   KTheory 計画 §3.3 の Lagrange 射影子の一般化と同じもの。A = End K に適用すれば射影子の補題が一括で出る。
2. 複体の作用の層（Eigen/Cyclic）：`structure CochainCyclicAction (n) K where map; pow_eq : map ^ n = 1`。CochainInvolution（n = 2、ζ = −1）と
   CochainCubicAction（n = 3）は `abbrev` で残す（参照は CochainCubicAction が KTheory 38・PC 125、CochainInvolution が KTheory 23・PC 93）。
   `characterProjector`・`decompositionIso`・`baseChange`・`comapIso`・`tensor`・`biprod`・`scalar` をここに置く。
3. K₀ 類の層（Eigen/Class）：冪等元の族 e と重み w について `weightedK0Class e w := Σ_i w i ⊗ [im e_i]`。加法性・非輪状なら 0・同変な
   準同型で不変・二項和・スカラー作用・テンソル積の公式をそれぞれ 1 本で示す。

群内で 600〜800 行の削減が見込める。AntiEquivariance（±1 固有空間を入れ替える作用素）は n = 2 固有で利用 1 箇所なので n = 2 のまま残す。

### 4.6 提出候補

1. 可換環 R 上、位数が R で可逆な有限アーベル群 G と指標 ψ について、指標冪等元 `e_ψ = |G|⁻¹ Σ_g ψ(g)⁻¹ g ∈ R[G]` が冪等で、
   指標値の差が単元なら `CompleteOrthogonalIdempotents`（`GroupAlgebra.average` の一般化、`IsDomain` を仮定しない）。
2. uⁿ = 1 の元の固有射影の多項式表示（1 の G = ZMod n の像）。
3. `map_invOf` の `OfNat` 版。

### 4.7 リスク

- 層の逆転：CubicActionClass が `KTheory.SupportedCoefficients` を import している（PerfectComplex が KTheory に依存）。KTheory 計画 §2.5 と
  合わせて、PerfectComplex と KTheory のどちらを上の層にするかを決める（§5）。
- `set_option backward.isDefEq.respectTransparency false`・`backward.defeqAttrib.useBackward true` はファイルごとに付いている。統合時は
  `section` で範囲を限る。

## 5. 順序の案と PerfectComplex・KTheory の境界

### 5.1 層の境界

現状、PerfectComplex と KTheory は互いに依存している：PerfectComplex の IntegerEuler・IntegerEulerIso・CoefficientEuler・TensorTorComparison・
CubicActionClass が KTheory（HomologyEulerBasic・SupportedCoefficients）を import し、KTheory は PerfectComplex の K0WithSupport・閉台・
完全複体を使う。両計画を合わせた案：

- PerfectComplex を下の層にする。KTheory が持つ `PerfectModuleResolution`・`K0WithSupport.mk_shift` を PerfectComplex へ（KTheory 計画 §2.5）。
- PerfectComplex の IntegerEuler 系・namespace `Adams` の Koszul（KoszulOneModel・KoszulTensor・KoszulClasses）・FiniteProjectiveResolutions を
  KTheory へ（§2.1）。
- CubicActionClass が使う係数（`SupportedCoefficients`）は KTheory の軽い `Coefficients` に分けてあるので（KTheory 計画 §2.1）、
  係数の定義を PerfectComplex 側（ClosedSupport/K0 の隣）へ下ろすか、Eigen/CubicClass を KTheory に上げる。

### 5.2 順序

1. 削除だけで済むもの：互換スタブ・互換 import（PC1 の 4 本、PC2 の 21 本、PC3 の 8 本）、確実な未使用。BS の再ビルドは起きない。
2. PC3 と KTheory の KT2・KT3 の小さな一本化（射影 e の一般補題の 2 回適用化、Positive・Negative の ε 化、Fourier 座標、`kernel.map`）。
3. §5.1 の層の境界の整理（PerfectComplex・KTheory の間のファイルの移動）。
4. PC1 の統合（CLMST の 27 モジュールが再ビルドになる正規化長さの移動は、CommutativeAlgebra の E・D と同じ時期にまとめる）。
5. 位数 n の作用・n 重テンソルへの一般化（§4.5、KTheory 計画 §5）と、HomologicalAlgebra の CochainTensor の Mathlib 化（§3.2）。
   最も大きい工事なので、1〜4 の後に費用対効果を見て判断する。
6. K₀ のモデルの一本化（§2.3。Inputs の引用の文言に関わるので計画判断が要る）。
