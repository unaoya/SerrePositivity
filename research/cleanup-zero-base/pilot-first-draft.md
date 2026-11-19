# 見本の範囲の宣言の整理（ファイルを使わない版、第 1 稿）

2026-11-20、調整役。main `cf88139c3` の手前（`1cb048402`）のビルド済みの環境から、`SerrePositivity/Spectra/General/` と `SerrePositivity/LengthAlgebra/` の全宣言 1,058 件を書き出して作った。Lean のソースは変えていない。

## 作り方

1. 宣言ごとに、主張（型）の中で使う宣言と、証明・中身の中で使う宣言を Lean から採る。
2. 自動生成の宣言（`_proof_1`、`eq_1`、`@[reassoc]` の `_assoc` など）は、元の宣言に畳む。
3. 要の定義（多くの宣言が頼る定義）を選び、グループの名前を付ける。ここだけが人の判断。
4. 各宣言を、それが直接・間接に頼る要の定義のうち、一番上のグループに入れる。今あるファイルは使わない。
5. 「ファイル」の列は、今の置き場所を引くためだけに付けてある。


## Spectra/General（畳んだ後 341 件）

### グループと、グループどうしの依存

| 番号 | グループ | 宣言 | 定義 | 定理 | 行 | 頼るグループ | 今のファイル数 |
| ---: | --- | ---: | ---: | ---: | ---: | --- | ---: |
| 0 | スペクトルの定義と構造射 | 27 | 13 | 14 | 124 | — | 4 |
| 1 | 極限・余極限 | 6 | 5 | 1 | 23 | 0 | 2 |
| 2 | 自由スペクトルと評価 | 52 | 24 | 28 | 305 | 0、1 | 9 |
| 3 | 自由スペクトルの各段の表示 | 23 | 12 | 11 | 138 | 0、2 | 5 |
| 4 | テンソル積と内部 Hom | 13 | 7 | 6 | 32 | 0 | 2 |
| 5 | 基礎圏の作用（テンソル） | 34 | 18 | 16 | 206 | 0、2、4 | 7 |
| 6 | 余テンソル | 22 | 13 | 9 | 89 | 0、2、4、5 | 6 |
| 7 | 写像対象 | 39 | 22 | 17 | 216 | 0、1、2、4、5、6 | 11 |
| 8 | 豊穣（合成・単位・表現可能性） | 69 | 30 | 39 | 657 | 0、2、5、6、7 | 15 |
| 9 | 懸垂の構造射とシフト | 19 | 7 | 12 | 134 | 0、2、4 | 5 |
| 10 | 単体集合の場合とシリンダー | 35 | 16 | 19 | 228 | 0、1、5、6、7 | 6 |
| — | （範囲の定義に頼らない） | 2 | 1 | 1 | 17 | — | 1 |

今のファイル 45 本のうち、二つ以上のグループの宣言が混ざっているものは 18 本。

### 手を入れる候補

| 候補 | 件数 | 行 |
| --- | ---: | ---: |
| どこからも使われない（範囲内・範囲外・対応表のどれにも出ない） | 24 | 77 |
| 範囲内で一か所からしか使われない定理 | 62 | 709 |
| 範囲内で一か所からしか使われない定義・インスタンス | 34 | 191 |
| 補題の主張に名前を付けただけの定義（〜Law） | 15 | 71 |
| 同じ型のインスタンスの重複 | 7（1 組） | 14 |
| tensor／cotensor で名前が対になる宣言 | 19 組 | 434 |
| 範囲の定義に頼らない宣言 | 2 | 17 |

「一か所からしか使われない」は範囲内の数。範囲の外からの使用は、この稿では数えていない。

<details><summary>どこからも使われない宣言</summary>

- `instHasColimitsOfSizeOfHasLimitsOfSize`（インスタンス、2 行、Limits）
- `simplicial_action`（定理、2 行、SimplicialComparison）
- `simplicial_level`（定理、2 行、SimplicialComparison）
- `simplicial_structureMap`（定理、3 行、SimplicialComparison）
- `simplicial_evaluation`（定理、3 行、SimplicialComparison）
- `simplicial_free`（定理、2 行、SimplicialComparison）
- `simplicial_freeAt`（定理、2 行、SimplicialComparison）
- `simplicial_freeForgetAdjunction`（定理、3 行、SimplicialComparison）
- `simplicial_freeAtLevelIsoBlockQuotient`（定理、3 行、SimplicialComparison）
- `simplicial_internalHom`（定理、3 行、SimplicialComparison）
- `simplicial_tensor`（定理、3 行、SimplicialComparison）
- `tensor_eq`（定理、1 行、TensorClosed）
- `simplicial_pointwiseTensor`（定理、2 行、SimplicialComparison）
- `simplicial_pointwiseTensorAssociator`（定理、5 行、SimplicialComparison）
- `simplicial_suspensionFunctor`（定理、3 行、SimplicialSuspensionComparison）
- `cotensorTensor_triangle`（定理、4 行、Cotensor）
- `pointwiseTensorHomEquiv_naturality_target`（定理、5 行、Cotensor）
- `mappingObjectArrowInverse`（定義、4 行、MappingEnrichment）
- `mappingObjectComposition_evaluation`（定理、6 行、MappingEnrichment）
- `simplicial_mappingObject`（定理、3 行、SimplicialComparison）
- `cotensorMappingIso_naturality_target`（定理、5 行、CotensorMappingObject）
- `tensorMappingIso_naturality_target`（定理、5 行、TensorMappingObject）
- `simplicial_adjointStructureMap`（定理、3 行、SimplicialSuspensionComparison）
- `circleTensorQuotient_boundary`（定理、3 行、SuspensionPushout）

</details>

<details><summary>〜Law の定義</summary>

- `pointwiseTensorLeftUnitLaw`（定義、3 行、PointwiseTensorCoherence） ← `pointwiseTensor_left_unit`
- `pointwiseTensorPentagonLaw`（定義、3 行、PointwiseTensorCoherence） ← `pointwiseTensor_pentagon`
- `pointwiseTensorTriangleLaw`（定義、3 行、PointwiseTensorCoherence） ← `pointwiseTensor_triangle`
- `mappingObjectArrowCompositionLaw`（定義、6 行、MappingEnrichment） ← `mappingObjectArrow_composition`
- `mappingObjectArrowEvaluationLaw`（定義、4 行、MappingEnrichment） ← `mappingObjectArrow_evaluation`
- `mappingObjectArrowIdentityLaw`（定義、5 行、MappingEnrichment） ← `mappingObjectArrow_identity`
- `mappingObjectAssociativityEvaluationLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_associativity_evaluation`
- `mappingObjectAssociativityLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_associativity`
- `mappingObjectCompositionEvaluationLaw`（定義、5 行、MappingEnrichment） ← `mappingObjectComposition_evaluation`
- `mappingObjectLeftUnitEvaluationLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_left_unit_evaluation`
- `mappingObjectLeftUnitLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_left_unit`
- `mappingObjectRightUnitEvaluationLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_right_unit_evaluation`
- `mappingObjectRightUnitLaw`（定義、5 行、MappingEnrichment） ← `mappingObject_right_unit`
- `mappingObjectUnitEvaluationLaw`（定義、5 行、MappingEnrichment） ← `mappingObjectUnit_evaluation`
- `mappingObjectArrowCompositionEvaluationLaw`（定義、7 行、MappingEnrichment） ← `mappingObjectArrow_composition_evaluation`

</details>

<details><summary>同じ型のインスタンス</summary>

- 型：`{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.SymmetricCategory`
  - `instEnrichedOrdinaryCategory`（MappingFunctorComparison）
  - `instEnrichedOrdinaryCategory_5`（CotensorMappingPoints）
  - `instEnrichedOrdinaryCategory_6`（EnrichedRepresentability）
  - `instEnrichedOrdinaryCategory_1`（TensorCotensorEnriched）
  - `instEnrichedOrdinaryCategory_4`（TensorMappingPoints）
  - `instEnrichedOrdinaryCategory_3`（EnrichedMappingParameter）
  - `instEnrichedOrdinaryCategory_2`（EnrichedMappingObjects）

</details>

<details><summary>tensor／cotensor の対</summary>

- `tensor`（2 行） ／ `cotensor`（3 行）
- `tensorEnrichedMappingIso`（8 行） ／ `cotensorEnrichedMappingIso`（9 行）
- `tensorEnrichedMappingIso_hom_app`（4 行） ／ `cotensorEnrichedMappingIso_hom_app`（4 行）
- `tensorEnrichedMappingIso_parameter`（10 行） ／ `cotensorEnrichedMappingIso_parameter`（10 行）
- `tensorEnrichedMappingIso_points`（11 行） ／ `cotensorEnrichedMappingIso_points`（19 行）
- `tensorMappingBifunctorIso`（8 行） ／ `cotensorMappingBifunctorIso`（9 行）
- `tensorMappingIso`（4 行） ／ `cotensorMappingIso`（3 行）
- `tensorMappingIso_arrow`（24 行） ／ `cotensorMappingIso_arrow`（33 行）
- `tensorMappingIso_naturality_parameter`（27 行） ／ `cotensorMappingIso_naturality_parameter`（26 行）
- `tensorMappingIso_naturality_source`（28 行） ／ `cotensorMappingIso_naturality_source`（28 行）
- `tensorMappingIso_naturality_target`（5 行） ／ `cotensorMappingIso_naturality_target`（5 行）
- `tensorMappingNatIso`（5 行） ／ `cotensorMappingNatIso`（5 行）
- `tensorMappingNatIso_homEquiv`（9 行） ／ `cotensorMappingNatIso_homEquiv`（8 行）
- `tensorMappingParameterIso`（8 行） ／ `cotensorMappingParameterIso`（9 行）
- `tensorMappingPowerAdjunction`（5 行） ／ `cotensorMappingPowerAdjunction`（4 行）
- `tensorMappingPowerAdjunction_naturality_parameter`（25 行） ／ `cotensorMappingPowerAdjunction_naturality_parameter`（14 行）
- `tensorMappingPowerAdjunction_naturality_source`（17 行） ／ `cotensorMappingPowerAdjunction_naturality_source`（14 行）
- `tensorMappingPowerAdjunction_unit`（15 行） ／ `cotensorMappingPowerAdjunction_unit`（11 行）
- `simplicial_tensor`（3 行） ／ `simplicial_cotensor`（2 行）

</details>

<details><summary>範囲の定義に頼らない宣言</summary>

- `pairing`（定義、5 行、StructureMaps）　主張に出る範囲外の本体の定義：`SymmetricSequence`、`SymmetricSequence.convolution`、`SymmetricSequence.level`
- `pairing_equivariance`（定理、12 行、StructureMaps）　主張に出る範囲外の本体の定義：`FiniteBijection`、`FiniteBijection.of`、`FiniteBijection.permutation`、`FiniteBijection.sumMap`、`FiniteBijection.sumObj`、`SymmetricSequence`、`SymmetricSequence.convolution`、`SymmetricSequence.level`

</details>

### グループごとの全宣言

「頼られる数」は、その宣言に直接・間接に頼る範囲内の宣言の数。「使う所」は直接使う範囲内の宣言の数。

<details><summary>0　スペクトルの定義と構造射（27 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `GeneralSymmetricSpectrum` | 定義 | 3 | 326 | 318 | Basic | Internal modules over Sym(K) in the Day convolution category |
| `forget` | 定義 | 3 | 162 | 17 | Basic | 球面の加群作用を忘れる関手。  |
| `level` | 定義 | 3 | 141 | 67 | Basic | 対称スペクトルの第n段の基点付き単体的集合。  |
| `levelMap` | 定義 | 3 | 72 | 15 | Basic | スペクトルの射の第n段の成分。  |
| `action` | 定義 | 4 | 23 | 9 | Basic | convolutionによる球面対称列の加群作用。  |
| `instHasColimitsOfShapeOfHasLimitsOfSize` | インスタンス | 4 | 17 | 6 | Limits |  |
| `structureMap` | 定義 | 5 | 17 | 9 | StructureMaps | 各次数のSym(K)とスペクトルのレベルから和次数への構造射。  |
| `instHasLimitsOfShape` | インスタンス | 3 | 3 | 3 | Limits |  |
| `forget_faithful` | インスタンス | 2 | 0 | 0 | Basic |  |
| `homMk` | 定義 | 4 | 0 | 0 | Basic | 球面の作用と両立する対称列の射からスペクトルの射を作る。  |
| `instHasColimitsOfSizeOfHasLimitsOfSize` | インスタンス | 2 | 0 | 0 | Limits |  |
| `instHasLimitsOfSize` | インスタンス | 2 | 0 | 0 | Limits |  |
| `underlying` | 定義 | 2 | 0 | 0 | Basic | 対称スペクトルの underlying 対称列。  |
| `action_hom` | 定理 | 4 | 3 | 1 | Basic | スペクトルの射は球面の作用と両立する。  |
| `hom_index_eq` | 定理 | 7 | 2 | 1 | Basic | スペクトルの射の成分は、次数の等式による移送と両立する。  |
| `structureMap_hom` | 定理 | 17 | 2 | 1 | StructureMaps | スペクトルの射の成分は各次数の構造射と両立する。  |
| `action_unit` | 定理 | 4 | 1 | 1 | Basic | 加群作用の単位則。  |
| `hom_ext` | 定理 | 8 | 0 | 0 | Basic | スペクトルの射は各段の成分で決まる。  |
| `levelMap_comp` | 定理 | 3 | 0 | 0 | Basic | 合成の各段の成分は成分の合成。  |
| `levelMap_id` | 定理 | 3 | 0 | 0 | Basic | 恒等射の各段の成分は恒等射。  |
| `simplicial_action` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_forget` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_level` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_structureMap` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |
| `simplicial_type` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `structureMap_equivariance` | 定理 | 12 | 0 | 0 | StructureMaps | 各次数の構造射は左右ブロックの置換と両立する。  |
| `structureMap_unit` | 定理 | 15 | 0 | 0 | StructureMaps | 第0段の構造射は単位子と添字の移送による射。  |

</details>

<details><summary>1　極限・余極限（6 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `forget_createsColimitsOfShape` | インスタンス | 4 | 18 | 3 | Limits |  |
| `forget_createsLimits` | インスタンス | 3 | 17 | 2 | Limits |  |
| `instHasZeroObject` | インスタンス | 1 | 11 | 6 | Zero |  |
| `instHasZeroMorphisms` | インスタンス | 2 | 9 | 9 | Zero |  |
| `forget_createsColimits` | インスタンス | 2 | 0 | 0 | Limits |  |
| `initial_isZero` | 定理 | 11 | 13 | 2 | Zero |  |

</details>

<details><summary>2　自由スペクトルと評価（52 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `freeFunctor` | 定義 | 2 | 233 | 12 | Free |  |
| `freeAt` | 定義 | 3 | 225 | 61 | Evaluation | Cの対象から第n段を生成する自由スペクトル関手F_n。  |
| `evaluation` | 定義 | 3 | 147 | 20 | Evaluation | スペクトルの置換作用を忘れた第n段の評価。  |
| `freeForgetAdjunction` | 定義 | 2 | 140 | 6 | Free |  |
| `freeAtAdjunction` | 定義 | 3 | 135 | 9 | Evaluation | F_nと第n段の評価との随伴。  |
| `freeObj` | 定義 | 2 | 15 | 12 | Free |  |
| `freeAtLevelGenerator` | 定義 | 6 | 9 | 9 | FreeLevels | Sym(K)の段とXから、直和の全単射で指定する自由スペクトルの生成元。  |
| `freeAtGenerator` | 定義 | 3 | 6 | 6 | Evaluation | F_n Xの第n段への生成元の射。  |
| `freeAtHomEquiv` | 定義 | 4 | 6 | 5 | Evaluation | 自由スペクトルの射は第n段への射と同値。  |
| `generator` | 定義 | 2 | 5 | 5 | Free |  |
| `tensorFreePair` | 定義 | 3 | 5 | 3 | TensorFreeAtSum |  |
| `freeAtLift` | 定義 | 3 | 4 | 4 | Evaluation | 第n段で指定した射から自由スペクトルの射への延長。  |
| `lift` | 定義 | 3 | 3 | 3 | Free |  |
| `tensorFreeAtSum` | 定義 | 5 | 3 | 3 | TensorFreeAtSum |  |
| `evaluation_preservesColimitsOfShape` | インスタンス | 5 | 2 | 2 | Limits |  |
| `evaluation_preservesLimitsOfShape` | インスタンス | 4 | 2 | 2 | Limits |  |
| `freeAtLevelInitial` | 定義 | 4 | 2 | 1 | FreeLevels | n未満の段は始対象。  |
| `colimitLevelIso` | 定義 | 3 | 1 | 1 | Limits |  |
| `freePushoutProductSquare` | 定義 | 31 | 1 | 1 | FreePushoutProduct |  |
| `limitLevelIso` | 定義 | 2 | 1 | 1 | Limits |  |
| `freeAt_preservesColimits` | インスタンス | 3 | 0 | 0 | Limits |  |
| `freeHomEquiv` | 定義 | 3 | 0 | 0 | Free |  |
| `freePushoutProductIso` | 定義 | 17 | 0 | 0 | FreePushoutProduct |  |
| `free_preservesColimits` | インスタンス | 2 | 0 | 0 | Limits |  |
| `freeAtHomEquiv_apply` | 定理 | 5 | 4 | 3 | Evaluation | Hom同値はスペクトルの射を生成元へ制限する。  |
| `freeAt_map_underlying` | 定理 | 33 | 3 | 2 | FreeLevelNaturality | 自由スペクトルの入力の射は、自由convolutionの入力の射と一致する。  |
| `tensorFreePair_naturality` | 定理 | 5 | 3 | 1 | TensorFreeAtSum |  |
| `free_unit` | 定理 | 3 | 2 | 1 | Free |  |
| `tensorFreeAtSum_naturality` | 定理 | 13 | 2 | 1 | TensorFreeAtSum |  |
| `freeAtGenerator_eq` | 定理 | 7 | 1 | 1 | Evaluation | 生成元は自由対称列の生成元と、自由Sym(K)加群の生成元との合成。  |
| `freeAtLevel_isZero` | 定理 | 5 | 1 | 1 | FreeLevels | n未満の段は零対象である。  |
| `freeAtLift_unique` | 定理 | 7 | 1 | 1 | Evaluation | 第n段で指定した値を持つ自由スペクトルの射は一意。  |
| `generator_lift` | 定理 | 3 | 1 | 1 | Free |  |
| `colimitLevelIso_ι_hom` | 定理 | 5 | 0 | 0 | Limits |  |
| `freeAtGenerator_lift` | 定理 | 6 | 0 | 0 | Evaluation | 延長は第n段の生成元上で元の射に一致する。  |
| `freeAtLevelGenerator_input` | 定理 | 13 | 0 | 0 | FreeLevelNaturality | 自由スペクトルの入力の射は生成元のXの因子に作用する。  |
| `freeAtLevelGenerator_left_relation` | 定理 | 9 | 0 | 0 | FreeLevels | Sym(K)側のブロックの作用と、生成元の添字の同一視の関係。  |
| `freeAtLevelGenerator_map` | 定理 | 9 | 0 | 0 | FreeLevels | 出力の全単射による作用は生成元の添字への後合成。  |
| `freeAtLevel_hom_ext` | 定理 | 9 | 0 | 0 | FreeLevels | 自由スペクトルの各段からの射は、この生成元上の値で決まる。  |
| `freeAtLevel_hom_ext_standard` | 定理 | 9 | 0 | 0 | FreeLevelInduction | 射の決定にはm−n次Sym(K)からの生成元だけで十分。  |
| `freeAtLift_eq` | 定理 | 11 | 0 | 0 | Evaluation | 延長は、自由対称列への延長と自由Sym(K)加群への延長を順に行う構成。  |
| `freeAtLift_generator` | 定理 | 6 | 0 | 0 | Evaluation | 自由スペクトルの射は生成元での値からの延長に等しい。  |
| `freeAt_underlying` | 定理 | 4 | 0 | 0 | Evaluation | F_n Xのunderlying対称列はSym(K)と自由対称列のconvolution。  |
| `free_counit` | 定理 | 3 | 0 | 0 | Free |  |
| `free_underlying` | 定理 | 2 | 0 | 0 | Free |  |
| `lift_generator` | 定理 | 3 | 0 | 0 | Free |  |
| `limitLevelIso_hom_π` | 定理 | 4 | 0 | 0 | Limits |  |
| `simplicial_evaluation` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |
| `simplicial_free` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_freeAt` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_freeAtAdjunction` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |
| `simplicial_freeForgetAdjunction` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |

</details>

<details><summary>3　自由スペクトルの各段の表示（23 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `freeAtLevelBlockQuotient` | 定義 | 4 | 8 | 8 | FreeLevelQuotient | m−n次Sym(K)とXのtensorの余積を、Sym(K)側の対称群の関係式で割った商。  |
| `freeAtLevelInductionDiagram` | 定義 | 5 | 8 | 7 | FreeLevelInduction | 自由スペクトルの第m段を表す、第二ブロックnの誘導図式。  |
| `freeAtLevelIsoInduction` | 定義 | 4 | 5 | 4 | FreeLevelInduction | 自由スペクトルの各段は誘導図式の余極限。  |
| `freeAtLevelIsoBlockQuotient` | 定義 | 5 | 4 | 4 | FreeLevelQuotient | 自由スペクトルの第m段と、Sym(K)側のブロック作用で割った余等化子との比較。  |
| `freeAtLevelBlockGenerator` | 定義 | 5 | 3 | 3 | FreeLevelQuotient | 全単射の添字に対応する、ブロック商の生成元。  |
| `freeAtLevelDiagram` | 定義 | 4 | 2 | 2 | FreeLevels | 自由スペクトルの第m段の分解図式。  |
| `freeAtLevelInductionAction` | 定義 | 4 | 2 | 1 | FreeLevelNaturality | 自由スペクトルの誘導表示上の、出力の対称群作用。  |
| `freeAtLevelActionIsoInduction` | 定義 | 6 | 1 | 1 | FreeLevelNaturality | 自由スペクトルの各段と誘導表示との、対称群作用を備えた同型。  |
| `freeAtLevelInductionActionFunctor` | 定義 | 4 | 1 | 1 | FreeLevelNaturality | 固定した出力次数の、作用付き誘導表示の関手。  |
| `freeAtLevelActionNatIsoInduction` | 定義 | 8 | 0 | 0 | FreeLevelNaturality | 自由スペクトルの作用付き各段と、誘導表示との自然同型。  |
| `freeAtLevelBlockQuotientIsoInduction` | 定義 | 5 | 0 | 0 | FreeLevelQuotient | 明示的なブロック商と、既存の誘導図式の余極限との比較。  |
| `freeAtLevelIsoColimit` | 定義 | 4 | 0 | 0 | FreeLevels | 自由スペクトルの各段の余極限表示。  |
| `freeAtLevelIsoInduction_input` | 定理 | 11 | 1 | 1 | FreeLevelNaturality | 入力の射に関する誘導表示の自然性。  |
| `freeAtLevelBlockGenerator_relation` | 定理 | 10 | 0 | 0 | FreeLevelQuotient | 商の関係式はSym(K)の置換作用と、添字へのブロック置換の前合成を同一視する。  |
| `freeAtLevelBlockQuotient_isZero` | 定理 | 4 | 0 | 0 | FreeLevelQuotient | n未満の段では、ブロック商も零対象となる。  |
| `freeAtLevelDiagram_obj` | 定理 | 6 | 0 | 0 | FreeLevels | 分解の各項は、Sym(K)と全単射で添字付けたXの余積とのtensor。  |
| `freeAtLevelInductionDiagram_obj` | 定理 | 5 | 0 | 0 | FreeLevelInduction | 誘導図式の各項は、m−n次Sym(K)とXのtensor。  |
| `freeAtLevelIsoBlockQuotient_generator` | 定理 | 8 | 0 | 0 | FreeLevelQuotient | 比較同型は自由スペクトルの生成元を商の生成元へ送る。  |
| `freeAtLevelIsoBlockQuotient_inverse` | 定理 | 7 | 0 | 0 | FreeLevelQuotient | 比較同型の逆は商の生成元を自由スペクトルの生成元へ戻す。  |
| `freeAtLevelIsoInduction_generator` | 定理 | 9 | 0 | 0 | FreeLevelInduction | 比較同型は生成元を誘導図式の標準包含へ送る。  |
| `freeAtLevelIsoInduction_inclusion` | 定理 | 9 | 0 | 0 | FreeLevelInduction | 逆同型は誘導図式の標準包含を自由スペクトルの生成元へ戻す。  |
| `freeAtLevelIsoInduction_output` | 定理 | 8 | 0 | 0 | FreeLevelNaturality | 出力の全単射に関する誘導表示の自然性。  |
| `simplicial_freeAtLevelIsoBlockQuotient` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |

</details>

<details><summary>4　テンソル積と内部 Hom（13 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `tensor` | 定義 | 2 | 195 | 10 | TensorClosed |  |
| `internalHom` | 定義 | 2 | 157 | 11 | TensorClosed |  |
| `internalHomFunctor` | 定義 | 3 | 152 | 9 | TensorClosed |  |
| `tensorInternalHomAdjunction` | 定義 | 3 | 50 | 1 | TensorClosed |  |
| `curry` | 定義 | 3 | 2 | 2 | TensorClosed |  |
| `tensorHomEquiv` | 定義 | 3 | 2 | 2 | TensorClosed |  |
| `uncurry` | 定義 | 3 | 2 | 2 | TensorClosed |  |
| `curry_uncurry` | 定理 | 2 | 0 | 0 | TensorClosed |  |
| `internalHom_eq` | 定理 | 2 | 0 | 0 | TensorClosed |  |
| `simplicial_internalHom` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |
| `simplicial_tensor` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |
| `tensor_eq` | 定理 | 1 | 0 | 0 | TensorClosed |  |
| `uncurry_curry` | 定理 | 2 | 0 | 0 | TensorClosed |  |

</details>

<details><summary>5　基礎圏の作用（テンソル）（34 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `pointwiseTensor` | 定義 | 3 | 180 | 61 | PointwiseTensor |  |
| `tensorFreeZeroPointwiseIso` | 定義 | 3 | 177 | 8 | PointwiseTensor |  |
| `pointwiseTensorFunctor` | 定義 | 3 | 176 | 53 | PointwiseTensor |  |
| `tensorFreeZeroPointwiseNatIso` | 定義 | 3 | 168 | 5 | PointwiseTensor |  |
| `pointwiseTensorBifunctor` | 定義 | 3 | 157 | 70 | PointwiseTensor |  |
| `mappingTensorFunctor` | 定義 | 2 | 138 | 58 | MappingObject |  |
| `mappingTensorNatIso` | 定義 | 4 | 122 | 2 | MappingObject |  |
| `pointwiseTensorUnitNatIso` | 定義 | 3 | 85 | 27 | PointwiseTensor |  |
| `pointwiseTensorAssociator` | 定義 | 3 | 82 | 23 | PointwiseTensor |  |
| `pointwiseTensorPost` | 定義 | 2 | 72 | 21 | PointwiseTensorCoherence |  |
| `pointwiseTensorAssociatorNatIso` | 定義 | 6 | 51 | 24 | PointwiseTensor | The action associator as a natural isomorphism in the spectr |
| `pointwiseTensorUnitIso` | 定義 | 2 | 46 | 9 | PointwiseTensorCoherence |  |
| `pointwiseTensorTriangleLaw` | 定義 | 3 | 36 | 2 | PointwiseTensorCoherence |  |
| `pointwiseTensorLeftUnitLaw` | 定義 | 3 | 34 | 2 | PointwiseTensorCoherence |  |
| `pointwiseTensorPentagonLaw` | 定義 | 3 | 32 | 1 | PointwiseTensorCoherence |  |
| `tensorFreeZeroPointwiseBifunctorIso` | 定義 | 5 | 21 | 2 | PointwiseTensor |  |
| `simplicialVertexNatIso` | 定義 | 7 | 9 | 4 | CircleSuspensionNaturality |  |
| `simplicialIntervalMap` | 定義 | 4 | 7 | 5 | CircleSuspensionNaturality |  |
| `pointwiseTensorAssociator_level` | 定理 | 5 | 63 | 6 | PointwiseTensor |  |
| `pointwiseTensorPost_level` | 定理 | 43 | 63 | 6 | PointwiseTensorCoherence | The parameter map is the ordinary tensor map at every level. |
| `pointwiseTensorAssociator_naturality` | 定理 | 16 | 56 | 3 | PointwiseTensor | Naturality in the spectrum variable is verified on every lev |
| `pointwiseTensorAssociator_parameter_left` | 定理 | 13 | 44 | 5 | PointwiseTensorCoherence |  |
| `pointwiseTensorAssociator_parameter_right` | 定理 | 15 | 44 | 5 | PointwiseTensorCoherence |  |
| `pointwiseTensorUnitIso_level` | 定理 | 5 | 41 | 2 | PointwiseTensorCoherence |  |
| `pointwiseTensor_triangle` | 定理 | 5 | 35 | 4 | PointwiseTensorCoherence |  |
| `pointwiseTensor_left_unit` | 定理 | 5 | 33 | 3 | PointwiseTensorCoherence |  |
| `pointwiseTensor_pentagon` | 定理 | 5 | 31 | 1 | PointwiseTensorCoherence |  |
| `pointwiseTensorAssociator_parameter_naturality` | 定理 | 14 | 28 | 1 | PointwiseTensorCoherence |  |
| `pointwiseTensor_isQuillen` | 定理 | 4 | 3 | 3 | EnrichedModel |  |
| `pointwiseTensor_level` | 定理 | 2 | 0 | 0 | PointwiseTensor |  |
| `simplicial_pointwiseTensor` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `simplicial_pointwiseTensorAssociator` | 定理 | 5 | 0 | 0 | SimplicialComparison |  |
| `simplicial_pointwiseTensorFunctor` | 定理 | 2 | 0 | 0 | SimplicialSuspensionComparison |  |
| `simplicial_suspensionFunctor` | 定理 | 3 | 0 | 0 | SimplicialSuspensionComparison |  |

</details>

<details><summary>6　余テンソル（22 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `homBySequenceCotensorIso` | 定義 | 3 | 80 | 2 | Cotensor |  |
| `cotensor` | 定義 | 3 | 79 | 24 | Cotensor |  |
| `internalHomBifunctor` | 定義 | 3 | 73 | 5 | Cotensor |  |
| `internalHomCotensorIso` | 定義 | 6 | 63 | 2 | Cotensor |  |
| `cotensorFunctor` | 定義 | 3 | 62 | 27 | Cotensor |  |
| `internalHomCotensorNatIso` | 定義 | 4 | 61 | 3 | Cotensor |  |
| `freeZeroTensorCotensorAdjunction` | 定義 | 4 | 49 | 1 | Cotensor |  |
| `pointwiseTensorCotensorAdjunction` | 定義 | 3 | 48 | 14 | Cotensor |  |
| `mappingObjectBifunctor` | 定義 | 3 | 28 | 19 | MappingObject |  |
| `cotensorBifunctor` | 定義 | 3 | 20 | 8 | Cotensor |  |
| `internalHomCotensorBifunctorIso` | 定義 | 5 | 19 | 1 | ParametrizedCotensor | The full contravariant parameter comparison for the cotensor |
| `pointwiseTensorCotensorParametrizedAdjunction` | 定義 | 9 | 18 | 3 | ParametrizedCotensor | Tensor/cotensor representability, including naturality in th |
| `pointwiseTensorHomEquiv` | 定義 | 3 | 18 | 11 | Cotensor |  |
| `mappingTensor_isLeftQuillen` | 定理 | 5 | 17 | 1 | SimplicialCylinder |  |
| `pointwiseTensorHomEquiv_naturality_source` | 定理 | 6 | 10 | 2 | Cotensor |  |
| `pointwiseTensorHomEquiv_naturality_parameter` | 定理 | 6 | 5 | 1 | ParametrizedCotensor | Parameter compatibility for the same tensor/cotensor Hom equ |
| `cotensorTensor_triangle` | 定理 | 4 | 0 | 0 | Cotensor |  |
| `cotensor_hasQuillenPullbackHom` | 定理 | 3 | 0 | 0 | EnrichedModel |  |
| `cotensor_level` | 定理 | 2 | 0 | 0 | Cotensor |  |
| `pointwiseTensorHomEquiv_naturality_target` | 定理 | 5 | 0 | 0 | Cotensor |  |
| `simplicial_cotensor` | 定理 | 2 | 0 | 0 | SimplicialComparison |  |
| `tensorCotensor_triangle` | 定理 | 4 | 0 | 0 | Cotensor |  |

</details>

<details><summary>7　写像対象（39 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `mappingObjectFunctor` | 定義 | 2 | 124 | 72 | MappingObject |  |
| `mappingObjectAdjunction` | 定義 | 4 | 121 | 60 | MappingObject |  |
| `mappingObject` | 定義 | 2 | 80 | 55 | MappingObject |  |
| `mappingObjectHomEquiv` | 定義 | 3 | 41 | 20 | MappingObject |  |
| `mappingObjectUnitEvaluationLaw` | 定義 | 5 | 34 | 1 | MappingEnrichment | 写像対象の単位を作用へ送って評価すると作用の単位比較になるという法則。  |
| `mappingObjectAssociativityEvaluationLaw` | 定義 | 5 | 31 | 1 | MappingEnrichment | 三つの写像対象の反復合成を評価した射が等しいという法則。  |
| `mappingObjectLeftUnitEvaluationLaw` | 定義 | 5 | 31 | 1 | MappingEnrichment | 単位を左因子へ入れた合成の評価が通常の左単位からの評価に一致するという法則。  |
| `mappingObjectRightUnitEvaluationLaw` | 定義 | 5 | 31 | 1 | MappingEnrichment | 単位を右因子へ入れた合成の評価が通常の右単位からの評価に一致するという法則。  |
| `mappingObjectAssociativityLaw` | 定義 | 5 | 30 | 1 | MappingEnrichment | C値写像対象の合成の結合則の等式。  |
| `mappingObjectLeftUnitLaw` | 定義 | 5 | 30 | 1 | MappingEnrichment | 写像対象の左単位則の等式。  |
| `mappingObjectRightUnitLaw` | 定義 | 5 | 30 | 1 | MappingEnrichment | 写像対象の右単位則の等式。  |
| `mappingObjectArrowEvaluationLaw` | 定義 | 4 | 29 | 1 | MappingEnrichment | 通常の射を写像対象の点へ送った後の評価の法則。  |
| `mappingObjectArrowCompositionLaw` | 定義 | 6 | 27 | 1 | MappingEnrichment | 通常の射の合成と写像対象の点の合成が一致するという法則。  |
| `mappingObjectArrowIdentityLaw` | 定義 | 5 | 27 | 1 | MappingEnrichment | 恒等射の対応先は作用の単位比較の転置という法則。  |
| `cotensorMappingPowerAdjunction` | 定義 | 4 | 17 | 8 | CotensorMappingObject | The same power object is represented by left tensor of the p |
| `pointwiseTensorMappingParametrizedAdjunction` | 定義 | 6 | 15 | 2 | ParametrizedMapping | The mapping object represents the action as a full parametri |
| `cotensorMappingHomEquiv` | 定義 | 4 | 5 | 3 | MappingObject | The two represented adjunctions identify the same ordinary m |
| `mappingObjectArrowEquiv` | 定義 | 6 | 2 | 2 | MappingEnrichment | 通常のスペクトル射と写像対象の単位からの射の同値。  |
| `mappingObjectCompositionEvaluationLaw` | 定義 | 5 | 1 | 1 | MappingEnrichment | 合成を作用へ送って評価すると二回の評価に一致するという法則。  |
| `ordinaryHomEquiv` | 定義 | 5 | 1 | 1 | MappingObject | Ordinary maps are the unit-valued points of the mapping obje |
| `mappingObjectArrowInverse` | 定義 | 4 | 0 | 0 | MappingEnrichment | 写像対象の点から通常のスペクトル射を得る。  |
| `mappingObjectCompositionEvaluation` | 定義 | 6 | 0 | 0 | MappingEnrichment | 二つの写像対象をテンソルした作用から、評価を二回適用する射。  |
| `mappingObjectUnit_evaluation` | 定理 | 6 | 33 | 2 | MappingEnrichment | 写像対象の単位は作用の単位比較を表現する。  |
| `mappingObjectArrow_evaluation` | 定理 | 5 | 28 | 1 | MappingEnrichment | 射に対応する点を評価すると、作用の単位比較と元の射の合成になる。  |
| `mappingObjectHomEquiv_naturality_source` | 定理 | 10 | 27 | 7 | ParametrizedMapping | The same Hom equivalence is natural in its spectrum source.  |
| `mappingObjectArrow_identity` | 定理 | 6 | 26 | 1 | MappingEnrichment | 恒等射は写像対象の単位に対応する。  |
| `mappingObjectHomEquiv_naturality_parameter` | 定理 | 5 | 14 | 4 | MappingObject |  |
| `pointwiseTensor_isZero_of_isZero` | 定理 | 7 | 10 | 1 | SuspensionPushout |  |
| `circleTensorPoint_isZero` | 定理 | 3 | 9 | 3 | SuspensionPushout |  |
| `cotensorMappingPowerAdjunction_naturality_source` | 定理 | 14 | 8 | 1 | CotensorMappingSource |  |
| `mappingObjectHomEquiv_naturality_target` | 定理 | 5 | 5 | 1 | MappingObject |  |
| `cotensorMappingPowerAdjunction_naturality_parameter` | 定理 | 14 | 4 | 1 | CotensorMappingParameter |  |
| `cotensorMappingPowerAdjunction_unit` | 定理 | 11 | 4 | 1 | CotensorMappingPoints |  |
| `circleTensor_isLeftQuillen` | 定理 | 8 | 1 | 1 | DerivedSuspensionComparison |  |
| `mappingHom_compatibility` | 定理 | 5 | 0 | 0 | MappingObject |  |
| `mappingObjectArrowEquiv_eq_ordinaryHomEquiv` | 定理 | 2 | 0 | 0 | MappingEnrichment |  |
| `mappingObjectComposition_evaluation` | 定理 | 6 | 0 | 0 | MappingEnrichment | 写像対象の合成は二回の評価を表現する。  |
| `mappingObject_hasQuillenPullbackHom` | 定理 | 5 | 0 | 0 | EnrichedModel |  |
| `simplicial_mappingObject` | 定理 | 3 | 0 | 0 | SimplicialComparison |  |

</details>

<details><summary>8　豊穣（合成・単位・表現可能性）（69 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `mappingObjectArrow` | 定義 | 5 | 33 | 11 | MappingEnrichment | 通常のスペクトル射を写像対象の点へ送る。  |
| `mappingObjectComposition` | 定義 | 6 | 33 | 6 | MappingEnrichment | C値写像対象の合成。後から適用する写像を左因子に置く。  |
| `mappingObjectUnit` | 定義 | 5 | 33 | 3 | MappingEnrichment | 作用の単位比較を転置して得る写像対象の単位。  |
| `mappingObjectEvaluation` | 定義 | 4 | 30 | 4 | MappingEnrichment |  |
| `mappingObjectArrowCompositionEvaluationLaw` | 定義 | 7 | 28 | 1 | MappingEnrichment | 通常の二つの射に対応する点の合成の評価の法則。  |
| `mappingEnrichedOrdinaryCategory` | 定義 | 9 | 25 | 8 | MappingEnrichment | Enrichment compatible with the existing category of Sym(K) m |
| `instEnrichedOrdinaryCategory` | 定義 | 2 | 17 | 9 | MappingFunctorComparison |  |
| `tensorMappingPowerAdjunction` | 定義 | 5 | 17 | 8 | TensorMappingObject | The right adjoint of the parameter functor composed with rig |
| `cotensorMappingAdjunction` | 定義 | 5 | 16 | 7 | CotensorMappingObject | The composite right adjoint is the mapping object of the cot |
| `cotensorMappingParameterIso` | 定義 | 9 | 14 | 4 | CotensorMappingObject | The other associativity comparison, natural in the mapping p |
| `instEnrichedOrdinaryCategory_1` | 定義 | 2 | 14 | 14 | TensorCotensorEnriched |  |
| `mappingEnrichedHomFunctorIso` | 定義 | 14 | 14 | 4 | MappingFunctorComparison | Comparison in both spectrum variables with the chosen enrich |
| `tensorMappingParameterIso` | 定義 | 8 | 14 | 4 | TensorMappingObject | Associativity of the action, natural in an arbitrary mapping |
| `cotensorMappingNatIso` | 定義 | 5 | 13 | 3 | CotensorMappingObject | C-valued cotensor representability, natural in the target sp |
| `spectrumTensorCotensor` | 定義 | 7 | 13 | 13 | TensorCotensorEnriched | The existing C action and cotensor represent Mathlib's enric |
| `tensorMappingNatIso` | 定義 | 5 | 13 | 3 | TensorMappingObject | C-valued tensor representability, natural in the target spec |
| `cotensorMappingIso` | 定義 | 3 | 12 | 8 | CotensorMappingObject |  |
| `tensorMappingIso` | 定義 | 4 | 12 | 8 | TensorMappingObject | The component is an actual C-valued Hom-object isomorphism.  |
| `instEnrichedOrdinaryCategory_2` | 定義 | 2 | 10 | 8 | EnrichedMappingObjects |  |
| `cotensorMappingBifunctorIso` | 定義 | 9 | 6 | 1 | CotensorMappingSource | The cotensor mapping comparison is natural in both spectrum  |
| `tensorMappingBifunctorIso` | 定義 | 8 | 6 | 1 | TensorMappingSource | The tensor mapping comparison is natural in both spectrum va |
| `cotensorEnrichedMappingIso` | 定義 | 9 | 5 | 4 | EnrichedMappingObjects | Cotensor Hom-object representability on the existing enriche |
| `tensorEnrichedMappingIso` | 定義 | 8 | 5 | 4 | EnrichedMappingObjects | Tensor Hom-object representability on the existing enriched  |
| `instEnrichedOrdinaryCategory_3` | 定義 | 2 | 4 | 2 | EnrichedMappingParameter |  |
| `instEnrichedOrdinaryCategory_4` | 定義 | 2 | 3 | 1 | TensorMappingPoints |  |
| `instEnrichedOrdinaryCategory_5` | 定義 | 2 | 3 | 1 | CotensorMappingPoints |  |
| `mappingEnrichedCategory` | 定義 | 7 | 2 | 2 | MappingEnrichment | C-valued enrichment, with the ordinary order of composition  |
| `enrichedModelOrdinaryCategory` | 定義 | 3 | 1 | 1 | EnrichedModel |  |
| `instEnrichedOrdinaryCategory_6` | 定義 | 2 | 1 | 1 | EnrichedRepresentability |  |
| `spectrumEnrichedRepresentability` | 定義 | 9 | 1 | 1 | EnrichedRepresentability | Full Hom-object representability on the existing enriched sp |
| `mappingObject_associativity_evaluation` | 定理 | 12 | 30 | 1 | MappingEnrichment | 反復合成の二つの経路は評価後に一致する。  |
| `mappingObject_left_unit_evaluation` | 定理 | 10 | 30 | 1 | MappingEnrichment | 写像対象の左単位を合成した後の評価を計算する。  |
| `mappingObject_right_unit_evaluation` | 定理 | 10 | 30 | 1 | MappingEnrichment | 写像対象の右単位を合成した後の評価を計算する。  |
| `mappingObject_associativity` | 定理 | 7 | 29 | 2 | MappingEnrichment | C値写像対象の合成は結合則を満たす。  |
| `mappingObject_left_unit` | 定理 | 6 | 29 | 2 | MappingEnrichment | C値写像対象の合成は左単位則を満たす。  |
| `mappingObject_right_unit` | 定理 | 7 | 29 | 2 | MappingEnrichment | C値写像対象の合成は右単位則を満たす。  |
| `mappingObjectArrow_composition_evaluation` | 定理 | 12 | 27 | 1 | MappingEnrichment | 点の合成の評価は、通常の二つの射の合成になる。  |
| `mappingObjectArrow_composition` | 定理 | 8 | 26 | 1 | MappingEnrichment | 通常の射の合成は写像対象の点の合成に対応する。  |
| `mappingObjectComposition_post` | 定理 | 11 | 16 | 1 | MappingFunctorComparison | Postcomposition with an ordinary spectrum map is the existin |
| `mappingObjectComposition_pre` | 定理 | 20 | 16 | 1 | MappingFunctorComparison | Precomposition by an ordinary spectrum map is the existing s |
| `eHomWhiskerLeft_eq_mappingObjectMap` | 定理 | 9 | 15 | 2 | MappingFunctorComparison | The enriched right whiskering agrees on whole objects, not j |
| `eHomWhiskerRight_eq_mappingObjectMap` | 定理 | 9 | 15 | 2 | MappingFunctorComparison | The enriched source whiskering is the existing contravariant |
| `cotensorMappingAdjunction_naturality_source` | 定理 | 14 | 8 | 1 | CotensorMappingSource |  |
| `tensorMappingPowerAdjunction_naturality_source` | 定理 | 17 | 8 | 1 | TensorMappingSource | Changing the spectrum source respects the composite power ad |
| `cotensorMappingIso_naturality_source` | 定理 | 28 | 7 | 1 | CotensorMappingSource | Cotensor mapping comparison is contravariantly natural in it |
| `tensorMappingIso_naturality_source` | 定理 | 28 | 7 | 1 | TensorMappingSource | Tensor mapping-object comparison is contravariantly natural  |
| `cotensorEnrichedMappingIso_hom_app` | 定理 | 4 | 4 | 2 | EnrichedMappingParameter |  |
| `cotensorMappingAdjunction_naturality_parameter` | 定理 | 15 | 4 | 1 | CotensorMappingParameter |  |
| `cotensorMappingNatIso_homEquiv` | 定理 | 8 | 4 | 1 | CotensorMappingObject | The comparison respects transposition for every generalized  |
| `spectrumTensorCotensor_tensorHomEquiv` | 定理 | 10 | 4 | 2 | TensorCotensorEnriched | The enriched-Hom comparison has identity components, so gene |
| `tensorEnrichedMappingIso_hom_app` | 定理 | 4 | 4 | 2 | EnrichedMappingParameter |  |
| `tensorMappingNatIso_homEquiv` | 定理 | 9 | 4 | 1 | TensorMappingObject | The comparison preserves transposition for arbitrary C-value |
| `tensorMappingPowerAdjunction_naturality_parameter` | 定理 | 25 | 4 | 1 | TensorMappingParameter | The right-tensor power adjunction is contravariantly natural |
| `tensorMappingPowerAdjunction_unit` | 定理 | 15 | 4 | 1 | TensorMappingPoints |  |
| `cotensorMappingIso_arrow` | 定理 | 33 | 3 | 1 | CotensorMappingPoints | The cotensor comparison preserves the ordinary point of a ma |
| `cotensorMappingIso_naturality_parameter` | 定理 | 26 | 3 | 1 | CotensorMappingParameter | Cotensor mapping comparison is contravariantly natural in it |
| `tensorMappingIso_arrow` | 定理 | 24 | 3 | 1 | TensorMappingPoints | The tensor comparison sends the ordinary point to the closed |
| `tensorMappingIso_naturality_parameter` | 定理 | 27 | 3 | 1 | TensorMappingParameter | The C-valued tensor mapping comparison is contravariantly na |
| `cotensorEnrichedMappingIso_parameter` | 定理 | 10 | 2 | 1 | EnrichedMappingParameter | Parameter law required by cotensor enriched representability |
| `cotensorEnrichedMappingIso_points` | 定理 | 19 | 2 | 1 | CotensorMappingPoints | Ordinary-point compatibility required by enriched cotensor r |
| `tensorEnrichedMappingIso_parameter` | 定理 | 10 | 2 | 1 | EnrichedMappingParameter | Parameter law required by tensor enriched representability.  |
| `tensorEnrichedMappingIso_points` | 定理 | 11 | 2 | 1 | TensorMappingPoints | Ordinary-point compatibility required by enriched tensor rep |
| `cotensorMappingIso_naturality_target` | 定理 | 5 | 0 | 0 | CotensorMappingObject |  |
| `enrichedHom_hasQuillenPullbackHom` | 定理 | 5 | 0 | 0 | EnrichedModel | SM7 for Mathlib's enriched Hom functor with the chosen ordin |
| `mappingEnrichedCategory_comp` | 定理 | 3 | 0 | 0 | MappingEnrichment |  |
| `mappingEnrichedCategory_id` | 定理 | 2 | 0 | 0 | MappingEnrichment |  |
| `spectrumHomObjectComparison_points` | 定理 | 7 | 0 | 0 | EnrichedRepresentability | Comparing the two represented Hom objects is the chosen ordi |
| `spectrumTensorCotensor_tensorCotensorHomEquiv` | 定理 | 4 | 0 | 0 | TensorCotensorEnriched | The receiver uses the previously constructed tensor/cotensor |
| `tensorMappingIso_naturality_target` | 定理 | 5 | 0 | 0 | TensorMappingObject |  |

</details>

<details><summary>9　懸垂の構造射とシフト（19 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `suspensionMap` | 定義 | 4 | 11 | 11 | Suspension |  |
| `shiftedHom` | 定義 | 3 | 7 | 7 | ShiftedHom |  |
| `shiftedHomStructureIndex` | 定義 | 4 | 7 | 4 | ShiftedHom |  |
| `shiftedHomSuspensionIndex` | 定義 | 5 | 5 | 5 | ShiftedHomSuspension |  |
| `adjointStructureMap` | 定義 | 2 | 4 | 4 | Suspension |  |
| `shiftedHomSuspensionFormula` | 定義 | 8 | 1 | 1 | ShiftedHomSuspension |  |
| `internalHomShiftIso` | 定義 | 7 | 0 | 0 | ShiftedHom |  |
| `shiftedHom_evaluation_index_eq` | 定理 | 8 | 3 | 1 | ShiftedHomSuspension |  |
| `suspensionMap_shiftedIndex` | 定理 | 9 | 3 | 1 | ShiftedHomSuspension |  |
| `shiftedHom_suspensionMap_evaluation` | 定理 | 22 | 2 | 2 | ShiftedHomSuspension |  |
| `simplicial_suspensionMap` | 定理 | 2 | 1 | 1 | SimplicialSuspensionComparison |  |
| `suspensionMap_hom` | 定理 | 12 | 1 | 1 | Suspension |  |
| `uncurry_adjointStructureMap` | 定理 | 2 | 1 | 1 | Suspension |  |
| `adjointStructureMap_naturality` | 定理 | 7 | 0 | 0 | Suspension |  |
| `shiftedHom_adjointStructureMap_formula` | 定理 | 16 | 0 | 0 | ShiftedHomAdjoint |  |
| `shiftedHom_level` | 定理 | 2 | 0 | 0 | ShiftedHom |  |
| `shiftedHom_structureMap_evaluation` | 定理 | 11 | 0 | 0 | ShiftedHom |  |
| `shiftedHom_suspensionMap_eq_formula` | 定理 | 7 | 0 | 0 | ShiftedHomSuspension |  |
| `simplicial_adjointStructureMap` | 定理 | 3 | 0 | 0 | SimplicialSuspensionComparison |  |

</details>

<details><summary>10　単体集合の場合とシリンダー（35 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `simplicialParameterFunctor` | 定義 | 3 | 21 | 12 | SimplicialCylinder |  |
| `simplicialVertexIso` | 定義 | 5 | 18 | 8 | SimplicialCylinder |  |
| `intervalBoundaryTensorMap` | 定義 | 2 | 16 | 8 | SuspensionPushout |  |
| `simplicialIntervalCylinder` | 定義 | 6 | 14 | 4 | SimplicialCylinder |  |
| `simplicialCylinder` | 定義 | 2 | 10 | 8 | SimplicialCylinder |  |
| `circleTensorBasepoint` | 定義 | 2 | 9 | 4 | SuspensionPushout |  |
| `circleTensorQuotient` | 定義 | 2 | 9 | 7 | SuspensionPushout |  |
| `intervalBoundaryCofan` | 定義 | 6 | 9 | 4 | SimplicialCylinder |  |
| `intervalBoundaryCollapse` | 定義 | 3 | 9 | 4 | SuspensionPushout |  |
| `intervalBoundaryCofanIsColimit` | 定義 | 7 | 8 | 2 | SimplicialCylinder |  |
| `intervalBoundaryCoproductIso` | 定義 | 2 | 7 | 2 | SimplicialCylinder |  |
| `circleHomotopySuspensionIso` | 定義 | 6 | 3 | 2 | CircleHomotopySuspension |  |
| `simplicialCotensorNatIso` | 定義 | 6 | 3 | 1 | SimplicialSuspensionComparison |  |
| `simplicialLoopNatIso` | 定義 | 6 | 2 | 2 | SimplicialSuspensionComparison |  |
| `circleSuspensionCofibrantNatIso` | 定義 | 6 | 1 | 1 | CircleSuspensionNaturality |  |
| `derivedSuspensionComparisonIso` | 定義 | 15 | 0 | 0 | DerivedSuspensionComparison |  |
| `simplicialParameter_isLeftQuillen` | 定理 | 4 | 16 | 3 | SimplicialCylinder |  |
| `circleTensor_isPushout` | 定理 | 4 | 7 | 2 | SuspensionPushout |  |
| `intervalBoundaryCollapse_eq_zero` | 定理 | 2 | 7 | 2 | SuspensionPushout |  |
| `circleTensorBasepoint_eq_zero` | 定理 | 2 | 6 | 1 | SuspensionPushout |  |
| `intervalBoundaryCoproductIso_inclusion` | 定理 | 28 | 6 | 1 | SimplicialCylinder |  |
| `circleTensor_cylinder_isPushout` | 定理 | 10 | 5 | 1 | SimplicialCylinder |  |
| `simplicialEndpoint_naturality` | 定理 | 19 | 5 | 2 | CircleSuspensionNaturality |  |
| `simplicialIntervalCylinder_isGood` | 定理 | 5 | 5 | 1 | SimplicialCylinder |  |
| `circleTensor_zeroCylinder_isPushout` | 定理 | 8 | 4 | 2 | CircleHomotopySuspension |  |
| `simplicialCylinder_isGood` | 定理 | 3 | 4 | 2 | SimplicialCylinder |  |
| `circleTensorQuotient_naturality` | 定理 | 6 | 3 | 1 | CircleSuspensionNaturality |  |
| `simplicialCylinder_i₀_naturality` | 定理 | 4 | 3 | 1 | CircleSuspensionNaturality |  |
| `simplicialCylinder_i₁_naturality` | 定理 | 4 | 3 | 1 | CircleSuspensionNaturality |  |
| `circleHomotopySuspensionIso_naturality` | 定理 | 17 | 2 | 1 | CircleSuspensionNaturality |  |
| `circleTensorQuotient_boundary` | 定理 | 3 | 0 | 0 | SuspensionPushout |  |
| `intervalBoundaryTensorMap_cofibration` | 定理 | 7 | 0 | 0 | SimplicialCylinder |  |
| `simplicialVertexNatIso_app` | 定理 | 3 | 0 | 0 | CircleSuspensionNaturality |  |
| `simplicial_suspensionLoopCounit` | 定理 | 10 | 0 | 0 | SimplicialSuspensionComparison |  |
| `simplicial_suspensionLoopUnit` | 定理 | 10 | 0 | 0 | SimplicialSuspensionComparison |  |

</details>

<details><summary>—　（範囲の定義に頼らない）（2 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `pairing` | 定義 | 5 | 19 | 4 | StructureMaps | The canonical Day-convolution generator at a pair of degrees |
| `pairing_equivariance` | 定理 | 12 | 1 | 1 | StructureMaps |  |

</details>


## LengthAlgebra（畳んだ後 380 件）

### グループと、グループどうしの依存

| 番号 | グループ | 宣言 | 定義 | 定理 | 行 | 頼るグループ | 今のファイル数 |
| ---: | --- | ---: | ---: | ---: | ---: | --- | ---: |
| 0 | 正規化長さ | 77 | 3 | 74 | 1118 | — | 8 |
| 1 | 係数の制限と上限 | 20 | 5 | 15 | 313 | 0 | 4 |
| 2 | 零長さの Serre 類と商 | 41 | 21 | 20 | 293 | 0、1 | 4 |
| 3 | 完全複体の Euler 評価 | 12 | 9 | 3 | 61 | 0、2 | 2 |
| 4 | Koszul の有限性と Euler | 47 | 19 | 28 | 479 | 0、1、2、3 | 6 |
| 5 | 根の塔：段と三段階の長さ | 57 | 5 | 52 | 1195 | — | 3 |
| 6 | 根の塔：基底変更 | 49 | 23 | 26 | 482 | 5 | 1 |
| 7 | 根の塔：加法性と塔の長さ | 24 | 6 | 18 | 431 | 0、1、5、6 | 4 |
| 8 | 根の塔：完備と座標 | 17 | 4 | 13 | 335 | 0、1、5、7 | 2 |
| — | （範囲の定義に頼らない） | 36 | 1 | 35 | 542 | — | 13 |

今のファイル 17 本のうち、二つ以上のグループの宣言が混ざっているものは 16 本。

### 手を入れる候補

| 候補 | 件数 | 行 |
| --- | ---: | ---: |
| どこからも使われない（範囲内・範囲外・対応表のどれにも出ない） | 12 | 107 |
| 範囲内で一か所からしか使われない定理 | 139 | 2716 |
| 範囲内で一か所からしか使われない定義・インスタンス | 18 | 108 |
| 補題の主張に名前を付けただけの定義（〜Law） | 0 | 0 |
| 同じ型のインスタンスの重複 | 0（0 組） | 0 |
| tensor／cotensor で名前が対になる宣言 | 0 組 | 0 |
| 範囲の定義に頼らない宣言 | 36 | 542 |

「一か所からしか使われない」は範囲内の数。範囲の外からの使用は、この稿では数えていない。

<details><summary>どこからも使われない宣言</summary>

- `isPowTorsion_quotient_extension`（定理、23 行、Normalized）
- `Section2.isPowTorsion_koszulHomology_of_baseChange`（定理、25 行、Tower）
- `len_ker_quotientToExtension_le`（定理、15 行、Normalized）
- `NormalizedLength.restrict_len`（定理、3 行、Core）
- `LengthAlgebra.extendedQuotientLength_obj`（定理、2 行、Core）
- `LengthAlgebra.quotientLength_obj`（定理、2 行、Core）
- `Section2.stageToStage_apply`（定理、2 行、Basic）
- `Section2.towerLengthFun_koszulHomology_of_baseChange`（定理、21 行、Tower）
- `Section2.towerLengthOn_len`（定理、4 行、Tower）
- `Section2.towerLength_len`（定理、4 行、Tower）
- `RootTowerLength.completedQuotientStageModule`（定義、3 行、Completion）
- `RootTowerLength.coordinateZeroExponent_at`（定理、3 行、Coordinate）

</details>

<details><summary>範囲の定義に頼らない宣言</summary>

- `Section2.exists_fg_quotient_cover_of_finitePresentation`（定理、61 行、Additivity）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `Section2.exists_fg_submodule_map_eq_of_surjective`（定理、13 行、Additivity）　主張に出る範囲外の本体の定義：`Section2.Tower`、`Section2.TowerStage`、`Section2.towerMapRingHom`、`Section2.towerRel`
- `Section2.exists_stage_submodule_and_quotient_equiv`（定理、101 行、Additivity）　主張に出る範囲外の本体の定義：`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMap`、`Section2.towerMapRingHom`、`Section2.towerRel`
- `LengthAlgebra.isPowTorsion_quotientModule_iff`（定理、8 行、Almost）　主張に出る範囲外の本体の定義：`Almost.IsAlmostZero`、`Almost.quotientModule`、`IsPowTorsion`
- `Section2.instCommRingTowerStage`（インスタンス、2 行、BaseChangeApproximation）　主張に出る範囲外の本体の定義：`Section2.TowerStage`
- `Section2.tendsto_const_mul_inv_succ`（定理、5 行、BaseChangeApproximation）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `Section2.tendsto_of_le_add_of_le_add`（定理、9 行、BaseChangeApproximation）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `Section2.div_stageRank_eq`（定理、17 行、Basic）　主張に出る範囲外の本体の定義：`Section2.stageRank`
- `Section2.exists_tower_tensor_family_stage`（定理、31 行、Basic）　主張に出る範囲外の本体の定義：`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMap`、`Section2.towerMapRingHom`、`Section2.towerRel`
- `Section2.isPowTorsion_tower_tensor`（定理、8 行、Basic）　主張に出る範囲外の本体の定義：`IsPowTorsion`、`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMapRingHom`、`Section2.towerMaxIdeal`、`Section2.towerRel`
- `Section2.isScalarTower_towerMap`（定理、6 行、Basic）　主張に出る範囲外の本体の定義：`Section2.TowerStage`、`Section2.towerMap`、`Section2.towerRel`
- `Section2.isScalarTower_towerMap_tower`（定理、6 行、Basic）　主張に出る範囲外の本体の定義：`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMap`、`Section2.towerMapRingHom`、`Section2.towerRel`
- `Section2.length_tensor_towerMap`（定理、17 行、Basic）　主張に出る範囲外の本体の定義：`Section2.TowerStage`、`Section2.stageRank`、`Section2.towerMap`、`Section2.towerRel`
- `Section2.residue_surjective_towerMap`（定理、13 行、Basic）　主張に出る範囲外の本体の定義：`Section2.TowerStage`、`Section2.isLocalRing_towerStage`、`Section2.towerMap`、`Section2.towerRel`
- `Section2.subsingleton_tensorProduct_of_right`（定理、4 行、Basic）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `RootTowerLength.exists_isTorsionBySet_p_pow_tensor`（定理、23 行、Completion）　主張に出る範囲外の本体の定義：`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMapRingHom`、`Section2.towerRel`
- `isPowTorsion_of_cone_of_homologyMap_eq_zero`（定理、10 行、Cone）　主張に出る範囲外の本体の定義：`Cone.cone`、`IsPowTorsion`
- `RootTowerLength.card_coordinateZeroExponent`（定理、7 行、Coordinate）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `RootTowerLength.finiteLength_quotient_maximalIdeal_pow`（定理、10 行、Coordinate）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `RootTowerLength.length_le_card_mul_quotient_of_span`（定理、27 行、Coordinate）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `LengthAlgebra.parameterIdeal_fg`（定理、3 行、Flat）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `LengthAlgebra.parameterIdeal_support`（定理、5 行、Flat）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `LengthAlgebra.parameter_powers_finiteLength`（定理、6 行、Flat）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `isPowTorsion_koszulModuleHomology`（定理、6 行、KoszulModule）　主張に出る範囲外の本体の定義：`IsPowTorsion`、`koszulModuleFunctor`
- `koszulModuleFunctor_snoc_eq`（定理、8 行、KoszulModule）　主張に出る範囲外の本体の定義：`Cone.cone`、`koszulModuleFunctor`、`smulId`
- `IsPowTorsion.comap`（定理、14 行、Normalized）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `isPowTorsion_quotient_extension`（定理、23 行、Normalized）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `isPowTorsion_tensorProduct`（定理、5 行、Normalized）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `isPowTorsion_tensorProduct_of_isFiniteLength`（定理、6 行、Normalized）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `isPowTorsion_tensorProduct_of_isTorsionBySet`（定理、15 行、Normalized）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `LengthAlgebra.quotient_isPowTorsion_of_span_le`（定理、5 行、QuotientBounds）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `NormalizedLength.isPowTorsion_quotient_sup`（定理、7 行、QuotientBounds）　主張に出る範囲外の本体の定義：`IsPowTorsion`
- `ennreal_eq_zero_of_div_pow_bound`（定理、6 行、QuotientBounds）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `ennreal_eq_zero_of_geometric_bound`（定理、8 行、QuotientBounds）　主張に出る範囲外の本体の定義：なし（Mathlib だけ）
- `RootTowerLength.root_stage_normalization`（定理、22 行、StageDecay）　主張に出る範囲外の本体の定義：`Section2.stageRank`
- `Section2.isPowTorsion_koszulHomology_of_baseChange`（定理、25 行、Tower）　主張に出る範囲外の本体の定義：`IsPowTorsion`、`Section2.Tower`、`Section2.TowerStage`、`Section2.instAlgebraTowerStageTower`、`Section2.towerMapRingHom`、`Section2.towerMaxIdeal`、`Section2.towerRel`、`koszulComplex`

</details>

### グループごとの全宣言

「頼られる数」は、その宣言に直接・間接に頼る範囲内の宣言の数。「使う所」は直接使う範囲内の宣言の数。

<details><summary>0　正規化長さ（77 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `NormalizedLength` | 構造 | 21 | 218 | 188 | Core | 環 `C` 上の正規化長さ：`C` 加群に `ℝ≥0∞` の値を対応させる関数で、零加群で `0`、同型で不変、 `J` |
| `NormalizedLength.len` | 定義 | 1 | 212 | 153 | Core | 加群 `M` の長さ `λ(M) ∈ ℝ≥0∞`。すべての `C` 加群に対して定義されるが、加法性は `J` 冪ねじれ |
| `NormalizedLength.ordinary` | 定義 | 17 | 4 | 4 | Core | 通常の長さ `Module.length` は `J = ⊥` の正規化長さである（`ℕ∞` を `ℝ≥0∞` に埋め込 |
| `NormalizedLength.len_add_of_exact` | 定理 | 1 | 174 | 6 | Core | 短完全列 `0 → M₁ →f M₂ →g M₃ → 0` で、中央の `M₂` が `J` のある冪で消えるなら `λ |
| `NormalizedLength.len_congr` | 定理 | 1 | 161 | 42 | Core | 線形同型な加群は同じ長さをもつ。  |
| `NormalizedLength.len_eq_zero_of_subsingleton` | 定理 | 1 | 133 | 17 | Core | 零加群の長さは `0`。  |
| `NormalizedLength.len_eq_add_quotient` | 定理 | 6 | 123 | 7 | Core | `J` 冪ねじれ加群 `M` と部分加群 `N` について `λ(M) = λ(N) + λ(M/N)`（短完全列 `0 |
| `NormalizedLength.len_quotient_le` | 定理 | 5 | 107 | 1 | Core | 商加群の長さはもとの加群の長さ以下。  |
| `NormalizedLength.len_le_of_surjective` | 定理 | 5 | 106 | 11 | Core | `J` 冪ねじれ加群 `M` からの全射 `f : M → N` があれば `λ(N) ≤ λ(M)`（`N ≅ M / |
| `NormalizedLength.len_submodule_le` | 定理 | 4 | 93 | 5 | Core | 部分加群の長さはもとの加群の長さ以下：`λ(N) ≤ λ(N) + λ(M/N) = λ(M)`（値が非負だから）。  |
| `NormalizedLength.len_le_of_injective` | 定理 | 5 | 66 | 8 | Core | `J` 冪ねじれ加群 `N` への単射 `f : M → N` があれば `λ(M) ≤ λ(N)`（`M ≅ im f |
| `LengthAlgebra.module_length_add` | 定理 | 7 | 59 | 3 | Core | 冪ねじれ加群の短完全列における長さの加法性。  |
| `NormalizedLength.len_range_le` | 定理 | 4 | 37 | 4 | Core | `J` 冪ねじれ加群 `M` からの線形写像の像の長さは `λ(M)` 以下。  |
| `NormalizedLength.len_eq_add_ker_range` | 定理 | 7 | 34 | 5 | Core | `J` 冪ねじれ加群 `M` からの線形写像 `f` について `λ(M) = λ(ker f) + λ(im f)`  |
| `NormalizedLength.len_le_add_of_exact` | 定理 | 8 | 25 | 7 | Core | 完全列 `M →f N →g P`（`M`、`N`、`P` は `J` 冪ねじれ）で `λ(N) ≤ λ(M) + λ( |
| `NormalizedLength.len_sup_le` | 定理 | 21 | 15 | 1 | Normalized | `λ(A ⊔ B) ≤ λ(A) + λ(B)`：`A × B → A ⊔ B` は全射で、`λ(A × B) = λ( |
| `NormalizedLength.len_finset_sup_le` | 定理 | 13 | 14 | 3 | Normalized | 有限個の部分加群の和の長さは、長さの和以下。  |
| `lambdaHomology_cone_of_homologyMap_eq_zero` | 定理 | 21 | 9 | 2 | Cone | ホモロジーに零写像を誘導する射の錐では、短完全列から長さの和の公式が得られる。  |
| `NormalizedLength.len_range_eq_zero` | 定理 | 4 | 8 | 2 | Core | `λ(M) = 0` なら `M` からの線形写像の像も長さ `0`。  |
| `NormalizedLength.len_eq_zero_of_exact` | 定理 | 7 | 7 | 2 | Core | 完全列 `M → N → P` で `λ(M) = λ(P) = 0` なら `λ(N) = 0`（`len_le_ad |
| `lambdaHomology_le_cone_prev_of_homologyMap_eq_zero` | 定理 | 10 | 6 | 1 | Cone | ホモロジー上で零となる射では、錐の一つ前の次数が左のホモロジーへ全射する。  |
| `NormalizedLength.len_eq_add_of_exact_of_surjective` | 定理 | 11 | 5 | 1 | Core | 完全列 `M →f N →g P → 0` で `λ(ker f) = 0` なら `λ(N) = λ(M) + λ(P |
| `NormalizedLength.len_ne_top_of_exact` | 定理 | 5 | 5 | 1 | Core | 完全列 `M → N → P` で `λ(M)`、`λ(P)` が有限なら `λ(N)` も有限（`len_le_add |
| `NormalizedLength.len_quotient_le_of_pow_le` | 定理 | 10 | 5 | 2 | QuotientBounds | 巡回商のイデアルを拡大すると、冪ねじれな源の長さ以下になる。  |
| `lambdaHomology_koszulModule_init_ne_top_of_last_homology_action_zero` | 定理 | 20 | 5 | 1 | KoszulModule | 最後の元が前の列のホモロジー上で零なら、全列の負次数の有限性から 前の列の全次数のホモロジー長の有限性が従う。係数加群の |
| `lambdaHomology_shortExact_le` | 定理 | 11 | 5 | 3 | Core | 短完全列の中央のホモロジーの長さは両端の和以下。 ホモロジーの長完全列と、冪ねじれ加群上の長さの劣加法性を使う。  |
| `lambdaHomology_koszulModule_ne_top_of_last_homology_action_zero` | 定理 | 20 | 4 | 2 | KoszulModule | 最後の元が前の列のホモロジー上で零なら、負次数の有限性だけから 全列の全整数次数のホモロジー長が有限となる。零次数も錐の |
| `lambdaHomology_le_cone_of_homologyMap_eq_zero` | 定理 | 11 | 4 | 1 | Cone | ホモロジーに零写像を誘導する射では、右のホモロジーの長さは錐の長さ以下。  |
| `lambdaHomology_shortExact_left_le` | 定理 | 13 | 4 | 2 | Core | 左のホモロジーの長さは、余核の一つ前の次数と中央の同次数の和以下。  |
| `normalizedLength_tor_of_residue` | 定理 | 50 | 4 | 2 | Flat | 剰余体での正次数の長さ零と零次の値から、有限長加群の Tor の長さを計算する。 基底の正則性や Koszul 分解は不 |
| `normalizedLength_tor_pos_eq_zero_iff_residue` | 定理 | 30 | 4 | 2 | Flat | λ-平坦性は剰余体だけで判定できる。零次の長さの有限性は不要。  |
| `NormalizedLength.len_quotient_eq_zero_of_div_pow_covers` | 定理 | 8 | 3 | 1 | QuotientBounds | 一様な冪ねじれ条件と指数的な分母による巡回商の上界から長さ零を得る。  |
| `lambdaEuler_mappingCone_comp` | 定理 | 43 | 3 | 1 | Cone | 合成写像の錐の Euler 評価は、二つの写像の錐の Euler 評価の和。 有界性は最初の錐と合成の錐にだけ要求すれば |
| `lambdaHomology_ne_top_of_cone_of_homologyMap_eq_zero` | 定理 | 8 | 3 | 1 | Cone | 錐のホモロジーの長さが有限なら、右の元のホモロジーの長さも有限。  |
| `lambdaHomology_null_cone` | 定理 | 10 | 3 | 2 | Cone | 零ホモトピックな射の錐の長さ公式。ホモロジー零の一般定理への互換入口。  |
| `LengthAlgebra.koszul_finite_of_homologySelf` | 定理 | 10 | 2 | 1 | Koszul | 非負の homological 次数での有限性から、全 cochain 次数での有限性を得る。  |
| `LengthAlgebra.length_eq_zero_of_finite_of_cyclic_quotient` | 定理 | 27 | 2 | 1 | Almost | 有限生成加群が長さ零の巡回商 R/K の全射像の有限和なら、その長さは零。 加法性を適用するため、巡回商と加群の冪ねじれ |
| `LengthAlgebra.quotient_length_powers_of_flat` | 定理 | 14 | 2 | 2 | Flat | 有限な剰余体での値から、全てのパラメータ冪の商の長さを得る。  |
| `NormalizedLength.len_ker_eq_len_coker` | 定理 | 9 | 2 | 1 | Core | 正規化長さが有限な加群の自己準同型では、核と余核の長さが等しい。 像の長さを加法性の二つの等式から消去する。有限性はこの |
| `NormalizedLength.len_quotient_sup_span_mul_le` | 定理 | 9 | 2 | 1 | QuotientBounds | 一つの関係式を積に置き換えた商の正規化長さは、二つの商の長さの和以下。  |
| `lambdaEuler_eq_zero_homology_length` | 定理 | 9 | 2 | 1 | KoszulModule | 零次以外のホモロジーの長さが零なら、Euler 評価は零次の長さの実数値。 有界性や長さの有限性を要求しない。  |
| `lambdaEuler_scalarCone_pow` | 定理 | 33 | 2 | 1 | Cone | スカラー乗法の正冪の錐の Euler 評価は指数倍。 条件は各正冪の錐にのみ課し、元の複体には長さ・冪ねじれの条件を課さ |
| `lambdaEuler_self_cone_eq_zero_of_homologyMap_eq_zero` | 定理 | 14 | 2 | 1 | Cone | ホモロジー上で零となる自己射の錐は Euler 評価零。 元のホモロジー長の有限性は、錐から導き、未知の仮定として渡さな |
| `lambdaHomology_koszul_null_finite` | 定理 | 23 | 2 | 1 | Cone | 零スカラーの Koszul 構成は、各次数の冪ねじれ性と長さの有限性を保つ。 有界性・射影性を使わず、各段の短完全列だけ |
| `lambdaHomology_shortExact_right_le` | 定理 | 13 | 2 | 1 | Core | 誤差側のホモロジーの長さは、中央の同次数と左の次の次数の和以下。  |
| `lambdaKoszul_algebraMap_cokernel_bounds` | 定理 | 25 | 2 | 2 | KoszulModule | 比較する二つの Koszul ホモロジーの長さを、余核の長さで両方向から抑える。 値は ℝ≥0∞。Noether 性、有 |
| `len_tensorProduct_le_length_mul` | 定理 | 31 | 2 | 1 | Normalized | **組成列による評価**：有限長 `D` 加群 `M` で `λ(C ⊗_D M) ≤ ℓ_D(M) · λ(C ⊗_D |
| `LengthAlgebra.flat_iff_koszul` | 定理 | 10 | 1 | 1 | Flat | 剰余体の Koszul 分解により、λ-平坦性を一つの列で判定する。  |
| `LengthAlgebra.koszul_finite_of_zero_positive` | 定理 | 12 | 1 | 1 | Koszul | 正次数の消滅と零次商の有限性から、一つの Koszul 複体の全次数の有限性を得る。  |
| `LengthAlgebra.length_eq_zero_of_finite_of_first_cyclic_quotient` | 定理 | 50 | 1 | 1 | Almost | 一次の巡回商の長さ零から、有限生成の冪ねじれ almost zero 加群の長さ零を導く。 J M の有限生成性だけに  |
| `LengthAlgebra.length_quotient_le_of_span_le` | 定理 | 6 | 1 | 1 | QuotientBounds | パラメータ商からの全射により、下界に使う商の長さも制御できる。  |
| `NormalizedLength.len_ker_le_len_coker_of_ker_le` | 定理 | 9 | 1 | 1 | Core | 写像 `f` の核を自己準同型 `g` が消すなら、その長さは `g` の余核の長さ以下。 定理2.5では `g` を共 |
| `NormalizedLength.len_ne_top_of_finite_of_powQuotient_ne_top` | 定理 | 34 | 1 | 1 | QuotientBounds | 全ての冪商の長さが有限なら、有限生成な冪ねじれ加群の長さも有限。  |
| `NormalizedLength.len_quotient_sup_span_pow_le` | 定理 | 18 | 1 | 1 | QuotientBounds | 一つの関係式をk乗に置き換えた商の正規化長さは高々k倍。  |
| `lambdaEuler_koszulModule_eq_zero_homology_length` | 定理 | 17 | 1 | 1 | KoszulModule | Koszul ホモロジーの負次数の長さが全て零なら、Euler 評価は零次の長さ。 正次数は複体の項の範囲から消滅する。 |
| `lambdaEuler_koszulModule_eq_zero_of_last_homology_action_zero` | 定理 | 19 | 1 | 1 | KoszulModule | 最後の元が前の列のホモロジー上で零なら、負次数の全列の有限性だけでEuler評価零。 前の列の有限性・冪ねじれ性と全列の |
| `lambdaEuler_koszulModule_last_pow` | 定理 | 22 | 1 | 1 | KoszulModule | 末尾だけを正冪に替える Koszul Euler 評価は、その指数倍。 全正冪のホモロジーの冪ねじれ性と長さの有限性を明 |
| `lambdaHomology_koszulModule_ne_top_of_last_mem_span_sup` | 定理 | 12 | 1 | 1 | KoszulModule | 最後の元が前の列と係数の零化元の生成イデアルに属すれば、 負次数の有限性から全次数のホモロジー長の有限性が従う。  |
| `lambdaHomology_koszul_null_pow` | 定理 | 38 | 1 | 1 | Cone | 実際の Koszul 塔の長さは、共通の錐の係数作用素で計算される。 有限性の確認と数値漸化式の一般論を分離し、無限分解 |
| `lambdaHomology_shortExact_right_ne_top` | 定理 | 11 | 1 | 1 | Core | 中央の同次数と左の次の次数の長さが有限なら、誤差側の長さも有限。  |
| `len_quotient_map_le_length_mul` | 定理 | 11 | 1 | 1 | Normalized | `N = D/H` の形：`λ(C/HC) ≤ ℓ_D(D/H) · λ(C/m_D C)`。  |
| `ordinary_koszul_pow_finite` | 定理 | 11 | 1 | 1 | Koszul | パラメータ商が Artin 環なら、各冪の Koszul ホモロジーの通常の長さは有限。  |
| `LengthAlgebra.cyclic_quotient_pow_length_eq_zero_of_first` | 定理 | 11 | 0 | 0 | Almost | 一次の巡回商の長さ零から、全ての冪の巡回商の長さ零を証明する。  |
| `NormalizedLength.len_quotient_eq_zero_of_geometric_covers` | 定理 | 8 | 0 | 0 | QuotientBounds | 冪ねじれな巡回商を幾何的に小さい巡回商から覆えば、目的の長さは零。  |
| `NormalizedLength.len_quotient_le_mul_of_pow_mem` | 定理 | 9 | 0 | 0 | QuotientBounds | xのk乗が既存の関係式に入るとき、xを追加した商のk倍で元の商を上から評価できる。  |
| `NormalizedLength.nontrivial_ring_of_len_pos` | 定理 | 8 | 0 | 0 | QuotientBounds | 正の長さをもつ加群が存在すれば、係数環は非自明である。  |
| `NormalizedLength.ordinary_len` | 定理 | 3 | 0 | 0 | Core | `(ordinary T).len M = Module.length T M`（`ℝ≥0∞` の値として）。  |
| `lambdaEuler_koszulModule_eq_zero_of_last_mem_span_sup` | 定理 | 12 | 0 | 0 | KoszulModule | 最後の元が前の列と係数の零化元の生成イデアルに属すれば、Euler評価は零。 ホモロジー上の零作用は所属条件から証明し、 |
| `lambdaHomology_koszul_null_binomial` | 定理 | 8 | 0 | 0 | Cone | 零ホモトピックなスカラーの Koszul ホモロジー長の二項係数公式。  |
| `lambdaHomology_shortExact_eq_of_error_zero` | 定理 | 16 | 0 | 0 | Core | 誤差複体の隣接する二次数の長さが零なら、比較するホモロジーの長さは一致。 比較する長さが有限であるという追加仮定は不要。 |
| `lambdaKoszul_algebraMap_cokernel_ne_top` | 定理 | 17 | 0 | 0 | KoszulModule | 比較先の同次数と比較元の次次数が有限なら、余核の Koszul 長も有限。  |
| `lambdaKoszul_algebraMap_eq_of_cokernel_length_zero` | 定理 | 15 | 0 | 0 | KoszulModule | 余核の隣接する二次数の長さが零なら、比較する Koszul ホモロジーの長さは一致。  |
| `lambdaKoszul_algebraMap_target_ne_top_of_last_mem_span_sup` | 定理 | 17 | 0 | 0 | KoszulModule | 余核の負次数の有限性と最後の元の所属から、比較先の零次数を含む全長さも有限になる。  |
| `len_ker_quotientToExtension_le` | 定理 | 15 | 0 | 0 | Normalized | 共通分母による商写像の核の正規化長さの評価。 長さを測る基底 `R` は `D` と別に取れるので、塔上の正規化長さにも |
| `len_quotient_maximalIdeal_pos` | 定理 | 9 | 0 | 0 | Normalized | `0 < λ(C/HC)` で `ℓ(D/H) < ∞` なら `0 < λ(C/m_D C)`（Corollary 2 |
| `length_koszulModule_zero_last_pow` | 定理 | 24 | 0 | 0 | KoszulModule | 負次数の長さ消滅と全次数の有限性のもとで、末尾の正冪の零次長さは指数倍。 実数 Euler 評価から拡張非負実数値へ戻す |
| `normalizedLength_tor_of_isWeaklyRegular` | 定理 | 30 | 0 | 0 | Flat | **有限長加群の `Tor` の正規化長さ**：`z` が `m_A` を生成する弱正則列で、Koszul ホモロジーの |

</details>

<details><summary>1　係数の制限と上限（20 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `NormalizedLength.comap` | 定義 | 21 | 37 | 13 | Normalized | 正規化長さの係数制限：`C` 加群 `M` を `f : Λ →+* C` で `Λ` 加群とみて `lam` で測る。 |
| `NormalizedLength.HasSup` | 定義 | 4 | 21 | 14 | Normalized | 上限の性質 (2.3)：`J` 冪ねじれの `M` について `λ(M)` は有限生成部分加群の長さの上限。  |
| `Section2.completedLengthOf` | 定義 | 7 | 17 | 2 | Completion | 任意の塔上の正規化長さの、p 進完備化への係数制限。 塔上の長さは明示的な引数なので、具体的な加法性の引用に依存しない。 |
| `NormalizedLength.restrict` | 定義 | 11 | 2 | 2 | Core | 加法性の定義域のイデアルの取り替え：`J'` 冪ねじれ加群がつねに `J` 冪ねじれなら、`J` の正規化 長さは `J |
| `NormalizedLength.restrictToBase` | 定義 | 11 | 0 | 0 | Core | 論文の `λ` は `m_D C` 冪ねじれ加群の上で加法的だが、Lemma 3.4・3.5 では `m_A C` 冪ね |
| `NormalizedLength.len_le_iff_fg` | 定理 | 5 | 16 | 3 | Normalized | 上限の性質のもとで、`λ(M) ≤ c` は「すべての有限生成部分加群で `λ ≤ c`」と同値。  |
| `NormalizedLength.len_iSup_eq_zero` | 定理 | 24 | 8 | 3 | Normalized | 部分加群の族で各 `λ(V_i) = 0` なら `λ(⨆ V_i) = 0`。有限生成部分加群は有限個の和に入る。  |
| `NormalizedLength.comap_len` | 定理 | 4 | 6 | 2 | Normalized | `comap` は値を変えない：`C` 加群 `M` の長さは、`Λ` 加群とみた `M` の `lam` での長さ。  |
| `NormalizedLength.exists_fg_lt` | 定理 | 6 | 5 | 1 | Normalized | 上限の性質のもとで、`c < λ(M)` なら `c < λ(N)` となる有限生成部分加群 `N` がある。  |
| `LengthAlgebra.length_eq_zero_of_cyclic_quotient` | 定理 | 34 | 4 | 1 | Almost | 固定した冪で消える almost zero 加群の長さ零を、一つの巡回商の長さ零に還元する。  |
| `LengthAlgebra.length_eq_zero_of_cyclic_quotients` | 定理 | 7 | 3 | 2 | Almost | 各冪に対応する巡回商が長さ零なら、冪ねじれ almost zero 加群はすべて長さ零。  |
| `NormalizedLength.HasSup.comap` | 定理 | 26 | 3 | 1 | Normalized | 正規化長さの上限の性質は、任意の環準同型に沿った係数制限で保たれる。  |
| `LengthAlgebra.quotient_comap_len` | 定理 | 8 | 1 | 1 | Almost | K が加群を零化するとき、構成した商環作用に沿う長さは元の長さと一致する。  |
| `NormalizedLength.len_eq_zero_of_directed_cover` | 定理 | 39 | 1 | 1 | Normalized | 写像の像が有向に増大して全体を覆い、各始域の長さが零へ収束すれば全体の長さは零。 共通の消去冪から全体の冪ねじれを導く。 |
| `Section2.completedLengthOf_restrictScalars` | 定理 | 21 | 1 | 1 | Completion | 直接の係数制限と、完備化を経由する係数制限の長さは一致する。 両立する代数作用から係数制限関手の合成同型を使い、L の同 |
| `LengthAlgebra.length_eq_zero_for_almost_zero_iff` | 定理 | 18 | 0 | 0 | Almost | almost zero の長さ消滅は、冪ごとの巡回商での確認と同値。 外部から必要な消滅定理をこの具体的な商の評価に限定 |
| `NormalizedLength.len_directLimit_eq_zero_of_tendsto` | 定理 | 13 | 0 | 0 | Normalized | 直極限：各 `G_i` が `J^n` で消え、`λ(G_i) → 0` なら `λ(lim→ G_i) = 0`。遷移 |
| `NormalizedLength.len_directSum_eq_zero` | 定理 | 29 | 0 | 0 | Normalized | 直和：各 `V_i` が `J^n` で消え `λ(V_i) = 0` なら `λ(⨁ V_i) = 0`。  |
| `NormalizedLength.len_iSup_of_directed` | 定理 | 22 | 0 | 0 | Normalized | 有向な部分加群の族（増大列）では `λ(⨆ V_i) = ⨆ λ(V_i)`。有限生成部分加群はどれかの `V_i` に |
| `NormalizedLength.restrict_len` | 定理 | 3 | 0 | 0 | Core | `restrict` は値を変えない。  |

</details>

<details><summary>2　零長さの Serre 類と商（41 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `LengthAlgebra.finiteLengthTorsion` | 定義 | 3 | 54 | 39 | Core | 有限の長さをもつ冪ねじれ加群。  |
| `LengthAlgebra.FiniteLengthTorsion` | 定義 | 2 | 46 | 31 | Core | 有限な長さの冪ねじれ加群のアーベル圏。  |
| `LengthAlgebra.instIsClosedUnderQuotientsModuleCatFiniteLengthTorsion` | インスタンス | 5 | 44 | 11 | Core |  |
| `LengthAlgebra.finiteLength` | 定義 | 2 | 42 | 27 | Core | 有限性を確認した対象の実数値の長さ。  |
| `LengthAlgebra.instContainsZeroModuleCatFiniteLengthTorsion` | インスタンス | 7 | 41 | 26 | Core |  |
| `LengthAlgebra.instIsClosedUnderExtensionsModuleCatFiniteLengthTorsion` | インスタンス | 6 | 41 | 1 | Core |  |
| `LengthAlgebra.instIsClosedUnderSubobjectsModuleCatFiniteLengthTorsion` | インスタンス | 5 | 41 | 10 | Core |  |
| `LengthAlgebra.instIsSerreClassModuleCatFiniteLengthTorsion` | インスタンス | 1 | 40 | 10 | Core |  |
| `LengthAlgebra.instIsSerreClassFiniteLengthTorsionZeroAdditiveLengthRealFiniteLength` | インスタンス | 3 | 34 | 21 | Core |  |
| `LengthAlgebra.FiniteLengthQuotient` | 定義 | 2 | 33 | 20 | Core | 有限な長さの冪ねじれ加群を零長さで割ったアーベル圏。  |
| `LengthAlgebra.finiteLengthQuotientFunctor` | 定義 | 4 | 28 | 8 | Core | 有限な長さの商への完全関手。  |
| `LengthAlgebra.torsionLength` | 定義 | 2 | 22 | 19 | Core | 全ての冪ねじれ加群に定義された、無限値を許す長さ。  |
| `LengthAlgebra.quotientLength` | 定義 | 3 | 19 | 9 | Core | 有限商の実数値の長さ。  |
| `LengthAlgebra.instIsSerreClassPowTorsionModuleZeroAdditiveLengthENNRealTorsionLength` | インスタンス | 3 | 14 | 14 | Core |  |
| `LengthAlgebra.instPreservesFiniteColimitsFiniteLengthTorsionFiniteLengthQuotientFiniteLengthQuotientFunctor` | インスタンス | 3 | 14 | 1 | Core |  |
| `LengthAlgebra.instPreservesFiniteLimitsFiniteLengthTorsionFiniteLengthQuotientFiniteLengthQuotientFunctor` | インスタンス | 3 | 14 | 1 | Core |  |
| `LengthAlgebra.LengthQuotient` | 定義 | 2 | 13 | 13 | Core | 無限長も含む冪ねじれ加群を、零長さで割った商。  |
| `LengthAlgebra.lengthQuotientFunctor` | 定義 | 2 | 10 | 7 | Core |  |
| `LengthAlgebra.extendedQuotientLength` | 定義 | 3 | 4 | 3 | Core | 大きな商に降下した非負拡大実数値の長さ。  |
| `LengthAlgebra.instPreservesFiniteColimitsPowTorsionModuleLengthQuotientLengthQuotientFunctor` | インスタンス | 3 | 2 | 1 | Core |  |
| `LengthAlgebra.instPreservesFiniteLimitsPowTorsionModuleLengthQuotientLengthQuotientFunctor` | インスタンス | 3 | 2 | 1 | Core |  |
| `LengthAlgebra.finiteLength_add` | 定理 | 8 | 38 | 4 | Core |  |
| `LengthAlgebra.finiteLength_of_isZero` | 定理 | 5 | 38 | 2 | Core |  |
| `LengthAlgebra.finiteLength_nonneg` | 定理 | 2 | 35 | 1 | Core |  |
| `LengthAlgebra.finiteLength_iso` | 定理 | 5 | 19 | 3 | Core |  |
| `LengthAlgebra.torsionLength_add` | 定理 | 5 | 19 | 2 | Core |  |
| `LengthAlgebra.torsionLength_of_isZero` | 定理 | 5 | 15 | 1 | Core |  |
| `LengthAlgebra.quotientLength_iso` | 定理 | 4 | 14 | 4 | Core |  |
| `LengthAlgebra.quotientLength_add` | 定理 | 4 | 13 | 3 | Core |  |
| `LengthAlgebra.quotientLength_eq_zero_iff` | 定理 | 4 | 13 | 1 | Core |  |
| `LengthAlgebra.torsionLength_iso` | 定理 | 3 | 4 | 1 | Core |  |
| `LengthAlgebra.length_eq_of_almost_iso` | 定理 | 9 | 3 | 1 | Almost | 冪ねじれの almost zero 対象の長さが零なら、almost 圏で同型な対象の長さは一致する。 局所化圏の射を分 |
| `LengthAlgebra.extendedQuotientLength_eq_zero_iff` | 定理 | 4 | 2 | 1 | Core |  |
| `LengthAlgebra.length_eq_of_almost_iso_baseChange` | 定理 | 23 | 2 | 1 | Almost | 商環で almost 同型な冪ねじれ加群の、元の環への係数制限で測った長さは一致する。 元の環で almost zero |
| `LengthAlgebra.normalizedLength_euler_exact_sequence` | 定理 | 44 | 2 | 1 | Core | 元の加群の長さによる Euler 加法性は、有限長さ部分圏での共通定理の適用である。  |
| `LengthAlgebra.length_eq_of_full_almost_iso_baseChange` | 定理 | 13 | 1 | 1 | Almost | 商環の全加群の almost 圏で同型な対象についても、元の長さは一致する。 原典の M^a≃N^a を、冪ねじれ部分圏 |
| `lambdaEuler_shortExact` | 定理 | 26 | 1 | 1 | Cone | 有界な短完全列で、冪ねじれ性と全ホモロジーの長さの有限性を確認すれば Euler 評価は加法的。  |
| `LengthAlgebra.extendedQuotientLength_obj` | 定理 | 2 | 0 | 0 | Core |  |
| `LengthAlgebra.length_eq_of_quotient_almost_iso` | 定理 | 27 | 0 | 0 | Almost | K で零化される元の加群が、商環の全加群の almost 圏で同型なら、元の長さは一致する。 元のイデアル I の冪等性 |
| `LengthAlgebra.quotientLength_obj` | 定理 | 2 | 0 | 0 | Core |  |
| `lambdaKoszul_algebraMap_euler_eq_of_cokernel_euler_zero` | 定理 | 31 | 0 | 0 | KoszulModule | 比較元と余核の全長さが有限で、余核の Euler 評価が零なら、二つの Euler 評価は一致する。  |

</details>

<details><summary>3　完全複体の Euler 評価（12 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `LengthAlgebra.perfectModuleHomology` | 定義 | 5 | 37 | 14 | Perfect | 支持つき有限射影複体の通常のホモロジー関手。  |
| `LengthAlgebra.perfectTorsionHomology` | 定義 | 5 | 9 | 6 | Perfect | 有限性を仮定せず、ホモロジーを冪ねじれ加群の圏へ送る。  |
| `LengthAlgebra.perfectLengthHomology` | 定義 | 4 | 6 | 6 | Perfect | 大きな長さの商に値をもつ実際のホモロジー関手。  |
| `LengthAlgebra.ordinaryBaseEulerK0` | 定義 | 4 | 4 | 4 | KoszulFormula | 基底の通常 Euler 評価。Koszul 生成の正規化に用いる。  |
| `LengthAlgebra.perfectTorsionHomology_additive` | インスタンス | 4 | 4 | 2 | Perfect |  |
| `LengthAlgebra.koszulScalars` | 定義 | 2 | 2 | 2 | Perfect | 有限個のスカラーを自然数添字に延長する。指定された範囲の外は使わない。  |
| `LengthAlgebra.perfectLengthHomology_additive` | インスタンス | 4 | 2 | 1 | Perfect |  |
| `LengthAlgebra.perfectTorsionHomology_isHomological` | インスタンス | 5 | 2 | 1 | Perfect |  |
| `LengthAlgebra.perfectLengthHomology_isHomological` | インスタンス | 4 | 1 | 1 | Perfect |  |
| `LengthAlgebra.perfectModuleHomology_powTorsion` | 定理 | 9 | 10 | 2 | Perfect |  |
| `LengthAlgebra.koszulScalars_fin` | 定理 | 2 | 1 | 1 | Perfect |  |
| `LengthAlgebra.perfectLengthHomology_isZero_iff` | 定理 | 13 | 1 | 1 | Perfect | 商で零であることと、元のホモロジーの長さが零であることの一致。  |

</details>

<details><summary>4　Koszul の有限性と Euler（47 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `LengthAlgebra.KoszulFinite` | 定義 | 3 | 36 | 31 | Koszul | 全ての正の冪について、各次数の Koszul ホモロジーの長さが有限。  |
| `LengthAlgebra.perfectFiniteHomology` | 定義 | 5 | 27 | 7 | Perfect | 有限長さの冪ねじれ加群に値をもつホモロジー関手。  |
| `LengthAlgebra.perfectQuotientHomology` | 定義 | 4 | 24 | 11 | Perfect | 有限長さの商に値をもつホモロジー関手。  |
| `LengthAlgebra.perfectQuotientHomologyShiftIso` | 定義 | 16 | 20 | 15 | Perfect | 第零次関手のシフトと、各次数のホモロジーの自然同型。  |
| `LengthAlgebra.perfectFiniteHomology_additive` | インスタンス | 4 | 16 | 2 | Perfect |  |
| `LengthAlgebra.perfectQuotientHomology_shiftSequence` | インスタンス | 3 | 16 | 6 | Perfect |  |
| `LengthAlgebra.perfectFiniteHomology_isHomological` | インスタンス | 5 | 14 | 1 | Perfect |  |
| `LengthAlgebra.perfectQuotientHomology_additive` | インスタンス | 4 | 14 | 1 | Perfect |  |
| `LengthAlgebra.perfectQuotientHomology_isHomological` | インスタンス | 5 | 13 | 1 | Perfect |  |
| `LengthAlgebra.perfectEulerK0` | 定義 | 6 | 12 | 9 | Perfect | 共通の三角加法性により得られる Euler 準同型。  |
| `LengthAlgebra.perfectBaseChangeEulerK0` | 定義 | 4 | 10 | 7 | Perfect | 三角関手による共通 Euler 評価の引き戻し。  |
| `LengthAlgebra.perfectEuler` | 定義 | 3 | 9 | 3 | Perfect | 有限射影版の Euler 評価は共通のホモロジー的 Euler 評価で定義する。  |
| `LengthAlgebra.koszulEuler` | 定義 | 2 | 8 | 8 | Koszul | Koszul Euler 特性。Koszul 有限性の下で長さの有限交代和となる。  |
| `LengthAlgebra.freeBaseChangeEulerK0` | 定義 | 3 | 6 | 5 | Perfect | 旧有限自由 K₀ 上の評価も、共通 Euler 評価から比較写像で引き戻す。  |
| `koszulModuleAlgebraHomologyIso` | 定義 | 23 | 5 | 2 | KoszulModule | 代数作用から作った係数加群と、環準同型による係数制限の作用を明示的に比較。  |
| `LengthAlgebra.KoszulAcyclic` | 定義 | 4 | 3 | 2 | Koszul | 全ての正の冪について、正の homological 次数の Koszul ホモロジーが長さ零。  |
| `LengthAlgebra.koszulModuleHomologyZeroQuotientIso` | 定義 | 12 | 2 | 1 | KoszulModule | 代数を係数とする第零 Koszul ホモロジーを、係数代数の商を底環へ制限した加群と同定する。 環準同型からの作用と通常 |
| `LengthAlgebra.perfectLengthHomologyShiftIso` | 定義 | 15 | 1 | 1 | Perfect |  |
| `LengthAlgebra.perfectLengthHomology_shiftSequence` | インスタンス | 3 | 1 | 1 | Perfect |  |
| `LengthAlgebra.homology_mem_finiteLengthTorsion` | 定理 | 10 | 29 | 1 | Koszul | 台をもつ有界有限射影複体のホモロジーは、有限な長さの評価先に属する。  |
| `LengthAlgebra.perfectModuleHomology_mem` | 定理 | 14 | 28 | 2 | Perfect | 支持と Koszul 有限性によって、評価先を有限長さの冪ねじれ加群に制限できる。  |
| `LengthAlgebra.perfectQuotientHomology_bounded` | 定理 | 15 | 14 | 1 | Perfect | 各対象ごとの有界性。圏全体に共通の振幅は要求しない。  |
| `LengthAlgebra.perfectQuotientHomology_shift_bounded` | 定理 | 7 | 13 | 3 | Perfect | 共通 Euler 評価に渡すシフト列の有界性。  |
| `LengthAlgebra.perfectEulerK0_mk` | 定理 | 3 | 7 | 1 | Perfect |  |
| `LengthAlgebra.perfectEuler_eq_lambdaEuler` | 定理 | 12 | 7 | 1 | Perfect | 代表複体上で、新しい評価は従来のホモロジーの交代和と一致する。  |
| `LengthAlgebra.perfectBaseChangeEulerK0_free` | 定理 | 7 | 6 | 1 | Perfect | 有限自由モデル上でも、新しい Euler 評価は従来の `chiLam` を再現する。  |
| `LengthAlgebra.freeBaseChangeEulerK0_mk` | 定理 | 3 | 5 | 2 | Perfect |  |
| `LengthAlgebra.freeBaseChangeEulerK0_koszul` | 定理 | 6 | 4 | 1 | KoszulFormula | Koszul 生成元での Euler 評価。  |
| `LengthAlgebra.freeBaseChangeEulerK0_eq_koszulEuler_mul` | 定理 | 10 | 3 | 2 | KoszulFormula | 有限自由モデル上の基底公式。係数は任意の実数値の Koszul Euler 数である。  |
| `LengthAlgebra.exists_surjective_koszulModuleHomology_zero_of_span_le` | 定理 | 23 | 1 | 1 | KoszulModule | 生成イデアルの包含から、代数係数の第零 Koszul ホモロジー間の全射を作る。 商写像を C 線形に作り、S へ制限し |
| `LengthAlgebra.koszulAcyclic_of_flat` | 定理 | 9 | 1 | 1 | Flat | λ-平坦性は全ての正の冪での Koszul 消滅を与える。有限ランクは不要。  |
| `LengthAlgebra.koszulEuler_eq_length_quotient` | 定理 | 16 | 1 | 1 | Koszul | 正の Koszul ホモロジーが長さ零なら、Koszul Euler 数は第零商の長さ。  |
| `LengthAlgebra.perfectBaseChangeEulerK0_comp` | 定理 | 12 | 1 | 1 | Perfect | 三角関手の合成に関する自然同型は、Euler 評価の合成にも降りる。  |
| `LengthAlgebra.perfectBaseChangeEulerK0_eq_koszulEuler_mul` | 定理 | 8 | 1 | 1 | KoszulFormula | 有限射影版の K₀ 上の基底公式。局所環での比較同型を使う。  |
| `length_comap_koszulModuleHomology` | 定理 | 24 | 1 | 1 | KoszulModule | 係数加群の Koszul ホモロジーを二段の係数制限で測る長さは、 係数代数上の Koszul ホモロジーを直接測る長さ |
| `LengthAlgebra.koszulAcyclic_of_cm` | 定理 | 7 | 0 | 0 | Flat | λ-CM 消滅から、一つのパラメータ系の全ての正の冪での消滅を得る。  |
| `LengthAlgebra.koszulEuler_of_flat` | 定理 | 7 | 0 | 0 | Flat | λ-平坦な有限ランクの代数の Koszul Euler 数はそのランク。  |
| `LengthAlgebra.koszulFinite_of_flat` | 定理 | 7 | 0 | 0 | Flat | λ-平坦性と有限ランクから、共通 Euler 理論が必要とする Koszul 有限性を供給する。  |
| `LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul` | 定理 | 9 | 0 | 0 | KoszulFormula | 個々の複体での基底公式。高次消滅は仮定しない。  |
| `LengthAlgebra.lambdaHomology_projective_vanishing` | 定理 | 35 | 0 | 0 | Perfect | 有限射影複体の新交叉型消滅。(Supp) と (Kosₘ) を確認した後は共通定理を使う。 長さの有限性、局所性、ネータ |
| `LengthAlgebra.lambdaKoszul_homology_zero_le_of_span_le` | 定理 | 13 | 0 | 0 | KoszulModule | 列の生成イデアルが大きくなると、第零 Koszul ホモロジーの正規化長さは減少する。 測定イデアルの有限生成性と元の列 |
| `LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient` | 定理 | 22 | 0 | 0 | KoszulModule | 二段の係数制限で測る第零 Koszul ホモロジーの長さは、係数代数の商を 基底環の標準写像で制限した長さと一致する。商 |
| `LengthAlgebra.length_quotient_ne_top_of_koszul_finite` | 定理 | 10 | 0 | 0 | QuotientBounds | Koszul 有限性は、パラメータを消す任意の商の長さの有限性を含意する。  |
| `LengthAlgebra.perfectBaseChangeEulerK0_id` | 定理 | 9 | 0 | 0 | Perfect | 恒等係数変更後の評価は、元の Euler 評価そのものである。  |
| `LengthAlgebra.perfectEuler_conjSum_eq` | 定理 | 34 | 0 | 0 | KoszulFormula | Koszul Euler 数の一致と K₀ の降下だけから、二つの評価の共役和は一致する。  |
| `ordinary_koszulEuler_eq_koszulEulerChar` | 定理 | 12 | 0 | 0 | Koszul | 剰余体が同じ局所係数環では、通常の Koszul Euler 数は基底上の評価に等しい。  |
| `ordinary_koszul_finite_of_maximal_le_radical` | 定理 | 11 | 0 | 0 | Koszul | Noether 局所環でパラメータの根基が極大イデアルを含めば、通常 Koszul 有限性を満たす。  |

</details>

<details><summary>5　根の塔：段と三段階の長さ（57 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `Section2.presentedLength` | 定義 | 8 | 76 | 11 | Basic | 1. 有限表示の段階 `λ**`：段 `n` と有限長 `A_n` 加群 `V` で `M ≃ Λ ⊗_{A_n} V` |
| `Section2.fgLength` | 定義 | 5 | 74 | 28 | Basic | 2. 有限生成の段階 `λ*`：有限表示な全射 `P ↠ N` にわたる `λ**(P)` の下限。  |
| `Section2.stageToStage` | 定義 | 4 | 71 | 9 | Basic | 段 `m` の `ι` 組を段 `m'` へ（各成分に `towerMap m m'`）。`A` 線形。  |
| `Section2.stageToTower` | 定義 | 4 | 70 | 9 | Basic | 段 `m` の `ι` 組を `Λ` の `ι` 組へ（各成分に `towerOf m`）。`A_m` 線形。  |
| `Section2.towerLengthFun` | 定義 | 4 | 63 | 42 | Basic | 3. 一般の加群：`λ_∞(M) = sup{λ*(N) : N ⊆ M 有限生成}`（論文 (2.3)）。  |
| `Section2.stageToStage_smul` | 定理 | 6 | 66 | 3 | Basic |  |
| `Section2.stageToStage_stageToStage` | 定理 | 5 | 66 | 2 | Basic |  |
| `Section2.stageToTower_smul` | 定理 | 4 | 66 | 3 | Basic |  |
| `Section2.stageToTower_stageToStage` | 定理 | 3 | 66 | 3 | Basic |  |
| `Section2.exists_stage_mem_span` | 定理 | 38 | 65 | 2 | Basic | **span 所属の降下**：段 `m` の元の有限族 `w` の `Λ` での像が、`c` の像の張る `Λ` 部分加 |
| `Section2.stageToStage_single` | 定理 | 7 | 65 | 2 | Basic |  |
| `Section2.stageToTower_single` | 定理 | 3 | 65 | 2 | Basic |  |
| `Section2.fgLength_le_of_equiv` | 定理 | 9 | 63 | 1 | Basic | `λ*` は線形同型で単調。  |
| `Section2.fgLength_congr` | 定理 | 4 | 62 | 6 | Basic |  |
| `Section2.stageToTower_apply` | 定理 | 2 | 62 | 1 | Basic |  |
| `Section2.exists_stage_surjective` | 定理 | 119 | 61 | 1 | Basic | **全射の降下**：段 `N` で表示された二つの加群の `Λ` への係数拡大の間に `Λ` 線形な全射があれば、 ある |
| `Section2.fgLength_le_of_surjective` | 定理 | 12 | 60 | 4 | Basic | 全射で得た加群の `λ*` は元の値以下。 有限表示な被覆への全射を合成して下限を比較するので、 有限生成の場合の `λ |
| `Section2.length_div_le_of_surjective` | 定理 | 78 | 60 | 1 | Basic | **降下の値の単調性**：有限長 `V`（段 `n`）、`W`（段 `m`）と `Λ` 線形な全射 `Λ ⊗_{A_m} |
| `Section2.fgLength_tensor` | 定理 | 22 | 59 | 4 | Basic | (S1) **有限段の公式（`λ*` の形）**：有限長の `A_n` 加群 `V` について `λ*(Λ ⊗_{A_n |
| `Section2.fgLength_submodule_le_stage_cover` | 定理 | 78 | 57 | 1 | Basic | A finitely generated submodule of a quotient of a finite-sta |
| `Section2.fgLength_submodule_le` | 定理 | 13 | 56 | 1 | Basic | The raw finite-generation length is monotone on finitely gen |
| `Section2.towerLengthFun_eq_fgLength_of_noetherian` | 定理 | 12 | 55 | 10 | Basic | On a finitely generated module the raw supremum equals its r |
| `Section2.towerLengthFun_le_of_equiv` | 定理 | 6 | 46 | 1 | Basic | `λ_∞` は線形同型で単調。  |
| `Section2.towerLengthFun_congr` | 定理 | 4 | 45 | 12 | Basic |  |
| `Section2.exists_descent` | 定理 | 92 | 44 | 4 | Basic | (S2) **降下**：`m_A` 冪ねじれで有限表示な `Λ` 加群は、ある段 `n` の有限長 `A_n` 加群 ` |
| `Section2.towerLengthFun_le_of_injective` | 定理 | 10 | 43 | 6 | Additivity | 塔上の生の `λ∞` は単射で単調。部分加群の像と線形同型不変性だけで従う。  |
| `Section2.fgLength_quotient_eq_iInf_fg` | 定理 | 17 | 42 | 2 | Additivity | 有限生成加群の商の `λ*` は、分母の有限生成部分による商の値の下限。 有限表示な被覆が有限個の関係式だけを使うことか |
| `Section2.towerLengthFun_tensor_eq_length` | 定理 | 11 | 41 | 3 | Additivity | 有限段から係数拡大した加群の生の上限長さは、その段の正規化した長さに等しい。 証明済みの有限生成一致を使い、旧 C1 の |
| `Section2.towerLengthFun_add_of_stage_exact` | 定理 | 20 | 39 | 1 | Additivity | 有限段の通常の長さの加法性から、根の塔へ係数拡大した加群の生の長さの加法性を導く。 中央の加群が有限長であることだけで、 |
| `Section2.towerLengthFun_submodule_le` | 定理 | 5 | 39 | 3 | Additivity | 生の `λ∞` の部分加群の値は全体の値以下。  |
| `Section2.finitePresentation_submodule_of_fg_of_powTorsion` | 定理 | 38 | 38 | 1 | Additivity | 有限表示な冪ねじれの塔加群の有限生成部分加群は、 共通の有限段で実現できるため、それ自身も有限表示である。  |
| `Section2.towerLengthFun_add_submodule_of_finitePresentation` | 定理 | 33 | 38 | 1 | Additivity | 有限表示な冪ねじれ加群とその有限生成部分加群・商について、生の長さは加法的。 共通の有限段の部分加群の短完全列に帰着する |
| `Section2.towerLengthFun_le_of_surjective` | 定理 | 19 | 38 | 1 | Additivity | 生の `λ∞` は全射で単調。有限生成部分加群の生成元だけを持ち上げればよい。  |
| `Section2.towerLengthFun_quotient_eq_iInf_fg_le` | 定理 | 16 | 38 | 1 | Additivity | 有限生成加群の商の生の長さは、分母の有限生成部分による商の長さの下限に等しい。  |
| `Section2.towerLengthFun_submodule_eq_iSup_fg_le` | 定理 | 22 | 38 | 2 | Additivity | 部分加群の長さは、全体の中の有限生成部分加群で、 その部分加群に含まれるものの長さの上限に等しい。  |
| `Section2.fgLength_le_towerLengthFun_submodule_add_quotient` | 定理 | 19 | 37 | 1 | Additivity | 有限生成の中央加群の値は、任意の部分加群の値と商の値の和以下。 有限生成分母での加法性を明示引数に取り、商の下限公式を適 |
| `Section2.finitePresentation_of_finite_of_injective_into_powTorsion` | 定理 | 13 | 37 | 1 | Additivity | 有限生成加群が有限表示な冪ねじれ加群へ単射で入れば、それ自身も有限表示。  |
| `Section2.towerLengthFun_add_submodule_finitePresentation` | 定理 | 27 | 37 | 2 | Additivity | 有限表示な冪ねじれ加群の任意の部分加群について、 商の下限公式と部分加群の上限公式から加法性を導く。  |
| `Section2.fg_endpoints_add_le_of_exact_of_fg_additivity` | 定理 | 69 | 36 | 1 | Additivity | 完全列の両端の有限生成部分の値の和は、中央全体の値以下。 右端の生成元を持ち上げ、左端の有限生成像と合わせて有限生成の中 |
| `Section2.towerLengthFun_add_kernel_of_submodule_finitePresentation` | 定理 | 68 | 36 | 1 | Additivity | 有限表示な冪ねじれ加群の部分加群から有限生成加群への全射では、 核の長さと像の長さの和が元の長さに等しい。有限生成部分を |
| `Section2.towerLengthFun_le_add_of_exact_of_fg_additivity` | 定理 | 37 | 36 | 1 | Additivity | 一般の完全列の長さの上向き評価を有限生成の中央部分加群へ還元する。 核の有限生成分母による商近似が、核全体の有限生成性を |
| `Section2.towerLengthFun_ne_top_of_finitePresentation` | 定理 | 9 | 36 | 2 | Additivity | 有限表示な冪ねじれ加群の生の正規化長さは有限である。  |
| `Section2.presentedLength_eq_zero_of_subsingleton` | 定理 | 12 | 35 | 1 | Basic | 零加群の `λ**` は `0`：段 `0`、`V = 0` で `ℓ(V)/1 = 0`。  |
| `Section2.towerLengthFun_add_of_exact_of_fg_additivity` | 定理 | 18 | 35 | 1 | Additivity | 一般の短完全列の加法性は、有限生成の中央加群と有限生成部分加群の 正準短完全列の加法性へ還元される。有限生成・有限表示の |
| `Section2.towerLengthFun_add_submodule_of_finite` | 定理 | 66 | 35 | 1 | Additivity | 有限生成な冪ねじれ加群と有限生成部分加群の商の間で、生の長さは加法的。 有限表示な冪ねじれ被覆で二つの部分加群を比較し、 |
| `Section2.fgLength_eq_zero_of_subsingleton` | 定理 | 7 | 34 | 1 | Basic | 零加群の `λ*` は `0`。  |
| `Section2.towerLengthFun_add_of_exact_of_noetherian` | 定理 | 13 | 34 | 2 | Additivity | Noether 局所基底・素数・座標の極大イデアル所属の下で、 一様冪ねじれ加群の任意の短完全列について生の長さは加法的 |
| `Section2.towerLengthFun_eq_zero_of_subsingleton` | 定理 | 5 | 33 | 1 | Basic | 零加群の `λ_∞` は `0`。  |
| `Section2.towerLengthFun_eq_fgLength` | 定理 | 10 | 10 | 1 | Tower | (C1) **有限生成加群で `λ_∞ = λ*`**。有限段の長さで証明済み。 CLMST Prop. 2.2.3 の |
| `Section2.towerLengthFun_tensor` | 定理 | 10 | 9 | 2 | Tower | **(2.2) 有限段の公式**：`λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。(C |
| `Section2.fgLength_le_presentedLength` | 定理 | 8 | 2 | 1 | Basic | 有限表示加群は自分自身で被覆できるため、`λ* ≤ λ**`。 逆向きの不等式や有限段公式はこの定義的な比較には含めない |
| `Section2.presentedLength_eq_fgLength_of_noetherian` | 定理 | 16 | 1 | 1 | Basic | For a finitely presented power-torsion module, the raw prese |
| `Section2.towerLengthFun_tensor_of_finiteLength` | 定理 | 13 | 1 | 1 | Tower | 有限長の段加群では、有限段の公式の冪ねじれ条件は自動的に満たされる。 極大イデアルのある冪が加群を消し、基底の極大イデア |
| `Section2.stageToStage_apply` | 定理 | 2 | 0 | 0 | Basic |  |
| `Section2.towerLengthFun_add_of_exact` | 定理 | 10 | 0 | 0 | Tower | (C2) **加法性**。有限段の長さと近似から証明済み。 `m_A Λ` 冪ねじれ加群の短完全列 `0 → M₁ →  |
| `Section2.towerLengthFun_eq_presentedLength_of_noetherian` | 定理 | 9 | 0 | 0 | Basic | The raw supremum also agrees with the presentation value on  |
| `Section2.towerLengthFun_koszulHomology_of_baseChange` | 定理 | 21 | 0 | 0 | Tower | 有限段から係数拡大された Koszul ホモロジーの正規化長さの公式。  |

</details>

<details><summary>6　根の塔：基底変更（49 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `Section2.TSj` | 定義 | 2 | 54 | 48 | BaseChangeApproximation | `S_j = A_j ⊗_A T`。  |
| `Section2.TS` | 定義 | 2 | 46 | 44 | BaseChangeApproximation | `S = Λ ⊗_A T`。  |
| `Section2.stageMapT` | 定義 | 4 | 41 | 8 | BaseChangeApproximation | `S_j → S`。  |
| `Section2.ιT` | 定義 | 2 | 37 | 14 | BaseChangeApproximation | `T → S_j`。  |
| `Section2.instAlgebraTSjTS` | インスタンス | 2 | 35 | 23 | BaseChangeApproximation |  |
| `Section2.fwdAux` | 定義 | 25 | 29 | 2 | BaseChangeApproximation | `(λ, τ, v) ↦ λ ⊗ τ v`。  |
| `Section2.fwdS` | 定義 | 13 | 27 | 12 | BaseChangeApproximation | `S → (V → Λ ⊗_{A_j} V)`、`λ ⊗ τ ↦ (v ↦ λ ⊗ τ v)`。  |
| `Section2.bwdAux` | 定義 | 5 | 22 | 2 | BaseChangeApproximation | `Λ → (V → S ⊗_{S_j} V)`、`λ ↦ (v ↦ (λ ⊗ 1) ⊗ v)`。  |
| `Section2.fwdT` | 定義 | 3 | 22 | 7 | BaseChangeApproximation | `S ⊗_{S_j} V → Λ ⊗_{A_j} V`。  |
| `Section2.bwdT` | 定義 | 11 | 20 | 4 | BaseChangeApproximation | `Λ ⊗_{A_j} V → S ⊗_{S_j} V`。  |
| `Section2.instCommRingTS` | インスタンス | 1 | 17 | 16 | BaseChangeApproximation |  |
| `Section2.baseChangeTowerEquiv` | 定義 | 9 | 16 | 11 | BaseChangeApproximation | **`S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V`**（`Λ` 線形）。  |
| `Section2.φB` | 定義 | 3 | 15 | 14 | BaseChangeApproximation | `B → S_j`（`B → T → S_j`）。  |
| `Section2.instCommRingTSj` | インスタンス | 1 | 11 | 10 | BaseChangeApproximation |  |
| `Section2.JT` | 定義 | 3 | 10 | 10 | BaseChangeApproximation | `m_A S`。  |
| `Section2.φS` | 定義 | 2 | 10 | 7 | BaseChangeApproximation | `S_j → S`。  |
| `Section2.Fj` | 定義 | 3 | 8 | 6 | BaseChangeApproximation | 係数拡大 `S_j`-加群 → `S`-加群。  |
| `Section2.transMapT` | 定義 | 3 | 7 | 3 | BaseChangeApproximation | 遷移写像 `S_i → S_j`（`i ≤ j`）。  |
| `Section2.tensorResBaseChangeIso` | 定義 | 16 | 5 | 1 | BaseChangeApproximation | **`M ⊗_B G` と係数拡大**：`(S ⊗_{S_j} V) ⊗_B G ≅ S ⊗_{S_j} (V ⊗_B  |
| `Section2.homologyTensorResBaseChangeIso` | 定義 | 9 | 4 | 1 | BaseChangeApproximation | 係数拡大 `S_j → S` はホモロジーと可換（`S` は `S_j` 上平坦）。  |
| `Section2.ψU` | 定義 | 3 | 4 | 4 | BaseChangeApproximation | `B → S`（`B → T → S`）。  |
| `Section2.lenB` | 定義 | 4 | 3 | 3 | BaseChangeApproximation | 段 `j` の加群の `B` 上の長さを `p^{jh}` で割ったもの。  |
| `Section2.tensorFjEquiv` | 定義 | 4 | 3 | 1 | BaseChangeApproximation | `S ⊗_{S_j} V` と係数拡大関手の対象の同一視（定義から等しい）。  |
| `Section2.fwdAux_apply` | 定理 | 2 | 28 | 1 | BaseChangeApproximation |  |
| `Section2.smul_TS_tmul` | 定理 | 5 | 26 | 3 | BaseChangeApproximation |  |
| `Section2.fwdS_tmul` | 定理 | 2 | 24 | 5 | BaseChangeApproximation |  |
| `Section2.fwdS_smul` | 定理 | 21 | 23 | 1 | BaseChangeApproximation | バランス条件：`fwdS (y s) v = fwdS s (y v)`（`y ∈ S_j`）。  |
| `Section2.bwdAux_apply` | 定理 | 2 | 21 | 1 | BaseChangeApproximation |  |
| `Section2.fwdT_tmul` | 定理 | 2 | 21 | 4 | BaseChangeApproximation |  |
| `Section2.bwdT_tmul` | 定理 | 2 | 19 | 2 | BaseChangeApproximation |  |
| `Section2.bwdT_fwdT` | 定理 | 15 | 17 | 1 | BaseChangeApproximation |  |
| `Section2.fwdT_bwdT` | 定理 | 6 | 17 | 1 | BaseChangeApproximation |  |
| `Section2.fwdT_smul` | 定理 | 12 | 17 | 1 | BaseChangeApproximation |  |
| `_private.LengthAlgebra.RootTowerLength.BaseChangeApproximation.0.Section2.stage_scalar_towers` | 定理 | 23 | 10 | 2 | BaseChangeApproximation | `S_j` 加群 `V` に `A_j`、`A`、`T`、`B` の作用を `S_j` 経由で入れる（局所インスタンス用 |
| `Section2.isFiniteLength_TSj` | 定理 | 39 | 8 | 2 | BaseChangeApproximation | 有限生成 `S_j` 加群は `A_j` 上有限長で、`m_A A_j` 冪ねじれ。  |
| `Section2.length_TSj_eq` | 定理 | 15 | 8 | 2 | BaseChangeApproximation | `S_j` 加群の長さは `A_j` 上と `B` 上で等しい（剰余体が共通）。  |
| `Section2.fwdT_lTensor` | 定理 | 18 | 6 | 1 | BaseChangeApproximation | `fwdT` は `S_j` 線形写像と可換。  |
| `Section2.stageMapT_transMapT` | 定理 | 8 | 6 | 2 | BaseChangeApproximation |  |
| `Section2.towerLengthFun_baseChangeT` | 定理 | 15 | 6 | 3 | BaseChangeApproximation | **有限段の公式（`S` の形）**：有限生成 `S_j` 加群 `V` について `λ_∞(S ⊗_{S_j} V)  |
| `Section2.exists_stageMapT` | 定理 | 13 | 5 | 1 | BaseChangeApproximation | `S` の元はある段から来る。  |
| `Section2.flat_TS` | 定理 | 22 | 5 | 1 | BaseChangeApproximation | **`S` は `S_j` 上平坦**：`S ⊗_{S_j} -` は `Λ ⊗_{A_j} -`（`Λ` は `A_j |
| `Section2.length_TSj_ne_top` | 定理 | 11 | 5 | 2 | BaseChangeApproximation | 有限生成 `S_j` 加群の `B` 上の長さは有限。  |
| `Section2.exists_stageMapT_family` | 定理 | 9 | 4 | 1 | BaseChangeApproximation | `S` の有限個の元は共通の段から来る。  |
| `Section2.isPowTorsion_TS` | 定理 | 18 | 4 | 2 | BaseChangeApproximation | `S` は `J` 冪ねじれ（`m_A^a T = 0`）。  |
| `Section2.stageMapT_tmul` | 定理 | 2 | 4 | 1 | BaseChangeApproximation |  |
| `Section2.towerLengthFun_extendScalars_eq` | 定理 | 26 | 4 | 1 | BaseChangeApproximation | `S ⊗_{S_j} W`（`ModuleCat` の係数拡大）と `TS ⊗[TSj] W` の `Λ` 上の同一視。 |
| `Section2.exists_descentT` | 定理 | 23 | 3 | 1 | BaseChangeApproximation | **有限表示な `S` 加群の降下**：`n` 以上のある段 `j` と有限生成 `S_j` 加群 `V` で `P ≃ |
| `Section2.towerLengthFun_homology_tensorRes` | 定理 | 36 | 3 | 1 | BaseChangeApproximation | **有限段の `Tor` の公式**：有限生成 `S_j` 加群 `V` について `λ_∞(H^m((S ⊗_{S_j |
| `Section2.φS_comp_φB` | 定理 | 5 | 3 | 1 | BaseChangeApproximation |  |

</details>

<details><summary>7　根の塔：加法性と塔の長さ（24 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `RootTowerLength.normalizedLength` | 定義 | 9 | 32 | 5 | Additivity | 有限段の長さと近似から証明した法則を持つ、具体的な根の塔の正規化長さ。 基底と座標の仮定を明示し、加法性を文献の引用で埋 |
| `RootTowerLength.completedNormalizedLength` | 定義 | 4 | 15 | 14 | Completion | 証明済みの塔の正規化長さを、p 進完備化への係数制限で測る具体的な長さ。  |
| `Section2.towerLength` | 定義 | 6 | 14 | 8 | Tower | **`λ_∞`**：塔 `Λ` の、`m_A Λ` 冪ねじれ加群の上の正規化長さ。値は `towerLengthFun` |
| `Section2.μT` | 定義 | 6 | 8 | 8 | BaseChangeApproximation | `S` 加群の正規化長さ（`λ_∞` の `Λ → S` に沿った係数制限）。  |
| `Section2.towerLengthOn` | 定義 | 3 | 2 | 2 | Tower | **`λ_D`**：`λ_∞` の `Λ → C` に沿った係数制限。`𝔡 C` 冪ねじれ `C` 加群の上の正規化長さ |
| `Section2.completedTowerLength` | 定義 | 4 | 1 | 1 | Tower | 完備化上の正規化長さ：非完備な塔に制限して測る。  |
| `RootTowerLength.completedNormalizedLength_len` | 定理 | 6 | 11 | 2 | Completion | 完備化上の加群の長さは、非完備な塔へ係数制限した三段階の数値関数。  |
| `RootTowerLength.normalizedLength_len` | 定理 | 4 | 10 | 1 | Additivity | 新しい正規化長さの値は既存の三段階の数値関数と定義上同じ。  |
| `RootTowerLength.normalizedLength_hasSup` | 定理 | 11 | 9 | 2 | Additivity | 証明した有限生成一致から、正規化長さの上限の性質を供給する。 長さの構造そのものも、その性質の証明も未証明の C2 に依 |
| `Section2.towerLength_hasSup` | 定理 | 5 | 5 | 1 | Tower | **上限の性質 (2.3)**：`λ_∞(M) = sup{λ_∞(N) : N ⊆ M 有限生成}`。定義（`λ*`  |
| `Section2.μT_tensor_eq` | 定理 | 16 | 5 | 2 | BaseChangeApproximation | `S ⊗_{S_j} V` 上の `Λ` の作用は、`S` 加群としての係数制限と左因子への作用で一致する。  |
| `Section2.exists_fg_quotient_le` | 定理 | 43 | 4 | 1 | BaseChangeApproximation | **部分加群による近似**：`J` 冪ねじれで `μ(M) < ∞` の `S` 加群 `M` と `ε > 0` につ |
| `Section2.μT_TS_ne_top` | 定理 | 23 | 4 | 1 | BaseChangeApproximation | `μ(S) < ∞`：`S ≃ S ⊗_{S_0} S_0` と有限段の公式。  |
| `Section2.exists_finitePresentation_approx` | 定理 | 51 | 3 | 1 | BaseChangeApproximation | **有限表示による近似**（論文 Lemma 5.4 の証明の `P_ε`）：`J` 冪ねじれで `μ(U) < ∞`  |
| `Section2.μT_pi_ne_top` | 定理 | 12 | 3 | 1 | BaseChangeApproximation | `μ(S^r) < ∞`。  |
| `RootTowerLength.completedNormalizedLength_hasSup` | 定理 | 5 | 2 | 1 | Completion | 完備化への係数制限後も、有限生成部分加群の長さの上限として計算できる。  |
| `Section2.exists_stage_step` | 定理 | 80 | 2 | 1 | BaseChangeApproximation | **近似の一段**：`ε > 0` と `n` について、段 `j ≥ n` と有限生成 `S_j` 加群 `V` があ |
| `RootTowerLength.completedNormalizedLength_quotient_pow_ne_top` | 定理 | 38 | 1 | 1 | Completion | 完備塔の極大イデアルの拡張の冪商は、正規化長さが有限。  |
| `Section2.exists_tower_approximation` | 定理 | 38 | 1 | 1 | BaseChangeApproximation | **論文 Lemma 5.4 の一般的な部分（塔の近似）**：`J` 冪ねじれで `μ(U) < ∞` の `S` 加群 |
| `RootTowerLength.completedNormalizedLength_ne_top_of_finite` | 定理 | 10 | 0 | 0 | Completion | 完備塔上の有限生成な冪ねじれ加群は、正規化長さが有限。 完備塔のNoether性・加群の有限表示性は不要。  |
| `Section2.exists_tower_approximation_B` | 定理 | 42 | 0 | 0 | BaseChangeApproximation | **論文 Lemma 5.4 の一般的な部分（`B` 加群の形）**：`B` 加群の列 `M_n`（`V_n` を `B |
| `Section2.towerLengthOn_eq_completedTowerLength` | 定理 | 7 | 0 | 0 | Tower | 完備化を経由して係数を制限しても、長さ代数の長さは変わらない。  |
| `Section2.towerLengthOn_len` | 定理 | 4 | 0 | 0 | Tower | `λ_D(M)` は `M` を `Λ` 加群とみた `λ_∞(M)`。  |
| `Section2.towerLength_len` | 定理 | 4 | 0 | 0 | Tower |  |

</details>

<details><summary>8　根の塔：完備と座標（17 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `RootTowerLength.coordinateZeroExponent` | 定義 | 4 | 11 | 3 | Coordinate | 残る座標の指数から、指定座標を指数零にした簡約指数を作る。  |
| `RootTowerLength.completedStageModule` | 定義 | 3 | 9 | 2 | Completion | 有限段の完備塔上の作用は、標準代数構造から得られる加群構造に固定する。  |
| `RootTowerLength.coordinateQuotientIdeal` | 定義 | 5 | 2 | 2 | Coordinate | 座標根と m_A^n の像で定まる、有限段の具体的なイデアル。  |
| `RootTowerLength.completedQuotientStageModule` | 定義 | 3 | 0 | 0 | Completion | 有限段の完備塔上の作用を、商とテンソル積の代数構造と同じ加群構造で固定する。  |
| `RootTowerLength.span_coordinateZeroMonomials` | 定理 | 40 | 9 | 1 | Coordinate | 指定座標と基底イデアルの像を含む商は、残る簡約単項式で生成される。  |
| `RootTowerLength.completedNormalizedLength_tensor_eq_length` | 定理 | 25 | 8 | 2 | Completion | 完備塔からの係数制限で測る有限段加群の長さは、通常の段長さを段の階数で割った値。  |
| `RootTowerLength.length_coordinateQuotient_le` | 定理 | 23 | 8 | 1 | Coordinate | 指定座標を零にした商の A 上の長さは、q^(h-1) 個の A/I の長さ以下。  |
| `RootTowerLength.length_stage_coordinateQuotient_le` | 定理 | 11 | 7 | 1 | Coordinate | 局所な有限段の通常の長さにも、同じ単項式数の上界が成り立つ。  |
| `RootTowerLength.completedNormalizedLength_tensor_coordinateQuotient_le` | 定理 | 33 | 6 | 1 | Coordinate | 完備塔へ移した座標商の正規化長さは、基底商の長さを p^m で割った値以下。  |
| `RootTowerLength.completedNormalizedLength_coordinateQuotient_le` | 定理 | 17 | 5 | 2 | Coordinate | 有限長の基底商に対し、完備塔の実際の商でも同じ上界を得る。  |
| `RootTowerLength.completedNormalizedLength_quotient_eq_zero_of_coordinate_roots` | 定理 | 37 | 2 | 1 | Coordinate | 一座標の全ての根と有限長な基底商の関係式を含む商は、正規化長さが零。  |
| `RootTowerLength.completedNormalizedLength_coordinateQuotientIdeal_le` | 定理 | 14 | 1 | 1 | Coordinate | m_A^n と一つの段座標で切った完備塔商の上界。定数は段 m に依存しない。  |
| `RootTowerLength.completedNormalizedLength_module_eq_zero_of_coordinate_roots` | 定理 | 28 | 1 | 1 | Coordinate | 全ての座標根が零化する冪ねじれ加群は、正規化長さ零。  |
| `RootTowerLength.completedNormalizedLength_quotient_eq_length` | 定理 | 11 | 0 | 0 | Completion | 有限段のイデアルを完備塔へ拡張した商の正規化長さは、有限段の通常商長さを 段の階数で割った値。零商も含み、イデアルの追加 |
| `RootTowerLength.completedNormalizedLength_quotient_le_of_coordinate_mem` | 定理 | 34 | 0 | 0 | Coordinate | 完備塔のイデアルが m_A^n と指定された段座標を含めば、その商も同じ上界を満たす。  |
| `RootTowerLength.completedNormalizedLength_quotient_pow_eq_of_coordinateRoot_mul` | 定理 | 44 | 0 | 0 | Coordinate | 差のイデアルを全ての座標根が零化すれば、自然な商間で長さは一致する。  |
| `RootTowerLength.coordinateZeroExponent_at` | 定理 | 3 | 0 | 0 | Coordinate |  |

</details>

<details><summary>—　（範囲の定義に頼らない）（36 件）</summary>

| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `Section2.instCommRingTowerStage` | インスタンス | 2 | 40 | 12 | BaseChangeApproximation | 探索を短くするための直接のインスタンス。  |
| `Section2.isScalarTower_towerMap` | 定理 | 6 | 66 | 1 | Basic | `A → A_n → A_N` は可換（`A_N` を `towerMap n N` で `A_n` 代数とみる）。  |
| `Section2.isScalarTower_towerMap_tower` | 定理 | 6 | 65 | 5 | Basic | `A_n → A_N → Λ` は可換。  |
| `Section2.residue_surjective_towerMap` | 定理 | 13 | 65 | 1 | Basic | `A_n → A_N → k_N` は全射（剰余体はどの段でも `k`）。  |
| `Section2.length_tensor_towerMap` | 定理 | 17 | 64 | 3 | Basic | **段の間の係数拡大の長さ**：`ℓ_{A_N}(A_N ⊗_{A_n} V) = p^{(N−n)h} · ℓ_{A_ |
| `Section2.div_stageRank_eq` | 定理 | 17 | 61 | 2 | Basic | `L / p^{kh} = (p^{(N'−N)h} · (p^{(N−k)h} · L)) / p^{N'h}`（`k |
| `Section2.exists_tower_tensor_family_stage` | 定理 | 31 | 61 | 2 | Basic | A finite family in a base change to the root tower is repres |
| `Section2.exists_fg_quotient_cover_of_finitePresentation` | 定理 | 61 | 43 | 1 | Additivity | 有限表示な被覆を有限生成加群の商へ写す全射は、分母の有限生成部分に既に降りる。 関係式の像と、有限個の生成元を被覆の像へ |
| `Section2.exists_fg_submodule_map_eq_of_surjective` | 定理 | 13 | 41 | 3 | Additivity | 全射の先の有限生成部分加群は、元の有限生成部分加群の像として得られる。  |
| `Section2.exists_stage_submodule_and_quotient_equiv` | 定理 | 101 | 41 | 2 | Additivity | 有限段からの係数拡大の中の有限生成部分加群とその商を、 共通の有限段の部分加群と商として実現する。  |
| `IsPowTorsion.comap` | 定理 | 14 | 38 | 4 | Normalized | `J.map f ≤ J'` なら、`J'` のある冪で消える `C` 加群 `M` は、`f` で `Λ` 加群とみる |
| `Section2.subsingleton_tensorProduct_of_right` | 定理 | 4 | 36 | 1 | Basic | 一方が零加群なら、テンソル積も零加群。  |
| `isPowTorsion_tensorProduct_of_isTorsionBySet` | 定理 | 15 | 17 | 2 | Normalized | `D` 加群 `M` がイデアル `J` の `n` 乗で消えるなら `C ⊗_D M` は `(J C)^n` で消え |
| `Section2.isPowTorsion_tower_tensor` | 定理 | 8 | 11 | 2 | Basic | `m_A A_n` 冪ねじれの `V` について `Λ ⊗_{A_n} V` は `m_A Λ` 冪ねじれ。  |
| `RootTowerLength.card_coordinateZeroExponent` | 定理 | 7 | 9 | 1 | Coordinate | 残る簡約指数の個数。  |
| `RootTowerLength.exists_isTorsionBySet_p_pow_tensor` | 定理 | 23 | 9 | 1 | Completion | 有限長の段加群を塔へ移すと、p のある冪で零化される。  |
| `RootTowerLength.length_le_card_mul_quotient_of_span` | 定理 | 27 | 9 | 1 | Coordinate | I で零化され、有限個の元で生成される加群の長さの一般的な上界。  |
| `ennreal_eq_zero_of_geometric_bound` | 定理 | 8 | 6 | 2 | QuotientBounds | 有限な定数と比率1未満の冪による上界があれば、拡張非負実数値は零。  |
| `isPowTorsion_koszulModuleHomology` | 定理 | 6 | 6 | 5 | KoszulModule | 係数加群に依存せず、台の条件から Koszul ホモロジーの冪ねじれ性を供給する。  |
| `isPowTorsion_of_cone_of_homologyMap_eq_zero` | 定理 | 10 | 5 | 2 | Cone | 錐の冪ねじれ性は、零作用による単射から右のホモロジーへ移る。  |
| `LengthAlgebra.parameter_powers_finiteLength` | 定理 | 6 | 4 | 2 | Flat | 正則パラメータの冪で割った商は有限長。  |
| `RootTowerLength.finiteLength_quotient_maximalIdeal_pow` | 定理 | 10 | 4 | 2 | Coordinate | Noether 局所環の極大イデアルの任意の冪による商は有限長。  |
| `ennreal_eq_zero_of_div_pow_bound` | 定理 | 6 | 4 | 1 | QuotientBounds | 指数的に増大する分母で割った一様な有限上界から零を導く。  |
| `isPowTorsion_tensorProduct` | 定理 | 5 | 4 | 1 | Normalized | `D` 加群 `M` が `m_D^n` で消えるなら `C ⊗_D M` は `(m_D C)^n` で消える。  |
| `NormalizedLength.isPowTorsion_quotient_sup` | 定理 | 7 | 3 | 1 | QuotientBounds | 固定した関係式がJの冪を含めば、それに任意の関係式を加えた商も冪ねじれ。  |
| `isPowTorsion_tensorProduct_of_isFiniteLength` | 定理 | 6 | 3 | 1 | Normalized | 有限長 `D` 加群 `M` について `C ⊗_D M` は `m_D C` 冪ねじれ。  |
| `LengthAlgebra.quotient_isPowTorsion_of_span_le` | 定理 | 5 | 2 | 1 | QuotientBounds | パラメータを消す商は、長さの定義域である冪ねじれ条件を満たす。  |
| `Section2.tendsto_const_mul_inv_succ` | 定理 | 5 | 2 | 1 | BaseChangeApproximation |  |
| `Section2.tendsto_of_le_add_of_le_add` | 定理 | 9 | 2 | 1 | BaseChangeApproximation | 両側から `c_n → 0` で挟まれた列は収束する。  |
| `koszulModuleFunctor_snoc_eq` | 定理 | 8 | 2 | 1 | KoszulModule | 列に末尾の元を追加する係数加群の Koszul 構成は、スカラー乗法の錐。  |
| `LengthAlgebra.isPowTorsion_quotientModule_iff` | 定理 | 8 | 1 | 1 | Almost | 構成した商環作用では、像イデアルの冪ねじれ条件と元の条件は一致する。  |
| `LengthAlgebra.parameterIdeal_fg` | 定理 | 3 | 0 | 0 | Flat | 基底の極大イデアルの像は有限生成。評価先の環に Noether 性は不要。  |
| `LengthAlgebra.parameterIdeal_support` | 定理 | 5 | 0 | 0 | Flat | 極大イデアルの像は基底パラメータの像で支持される。  |
| `RootTowerLength.root_stage_normalization` | 定理 | 22 | 0 | 0 | StageDecay | 三つの倍率と有限段の階数の正規化。零や無限大による除算は使わない。  |
| `Section2.isPowTorsion_koszulHomology_of_baseChange` | 定理 | 25 | 0 | 0 | Tower | 同じ有限長性は、係数拡大後のホモロジーが `m_A Λ` の冪で消えることも与える。  |
| `isPowTorsion_quotient_extension` | 定理 | 23 | 0 | 0 | Normalized | 係数環のイデアルの冪で消える商は、代数を拡大しても同じ冪で消える。 元の商で単位元を消すことから、係数の像がイデアルに入 |

</details>

