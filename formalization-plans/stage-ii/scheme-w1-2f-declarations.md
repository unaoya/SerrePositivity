# SC-W1 段 2f：モジュールと宣言の検収用一覧

数学の採取点：`32d8faeb7`。停止点 2e の数学コミット `bf9767cdc` 以後に追加した、コミット済みの本体 234 本。停止点の到達点と検証は [停止点報告](scheme-w1-2f-report.md)。

ソースに明示した名前付き宣言と docstring の先頭の主張を列挙する。docstring のない補助宣言にはソースの型を表示する。匿名 instance・構造体の生成宣言は一覧外で、公理監査では別途対象に含める。詳細な到達点と対象ビルドは [route](scheme-w1-2f-route.md)。

## AffineBaseChangeCechVanishing

モジュール：`SerrePositivity.AlgebraicGeometry.AffineBaseChangeCechVanishing`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `affineBaseChangeCechHomology_isZero` | アフィンな平坦底変換で正次数の構造層 Čech H のスカラー拡大は消える。 |

## AffineCechHomologyVanishing

モジュール：`SerrePositivity.AlgebraicGeometry.AffineCechHomologyVanishing`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `affineSchemeCechHomology_isZero` | アフィンスキームの準連接係数は有限アフィン被覆の正次数 Čech H が消える。 |

## AffineIsoSectionAlgebraScalar

モジュール：`SerrePositivity.AlgebraicGeometry.AffineIsoSectionAlgebraScalar`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeScalarHom_bijective_of_isIso` | アフィン基底への構造射が同型なら、実際の大域スカラー写像は全単射。 |
| `schemeSectionAlgebra_scalar_surjective_of_isIso` | アフィン基底への同型の、アフィン被覆の切断部分代数へのスカラーは全射。 |

## AffineSectionAlgebraAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.AffineSectionAlgebraAugmentation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `affineSchemeModuleCech_acyclic` | アフィンスキームの準連接係数のアフィン被覆は、任意の基底環上で増大 Čech が完全。 |
| `affineSchemeSectionAlgebraAugmentation_surjective` | アフィン被覆で、代数の実際の増大写像は適合する切断へ全射。 |
| `affineSchemeSectionAlgebraAugmentation_bijective` | アフィン被覆の実際の代数の増大写像は全単射。 |

## AffineSectionAlgebraScalar

モジュール：`SerrePositivity.AlgebraicGeometry.AffineSectionAlgebraScalar`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeSectionAlgebraCech_empty_scalar_surjective` | 空交叉の切断代数へのスカラーは、大域スカラーが全射なら全射。 |
| `affineSchemeSectionAlgebra_scalar_surjective` | アフィン被覆の適合する切断代数へのスカラーは、大域スカラーが全射なら全射。 |

## AugmentedCechCone

モジュール：`SerrePositivity.AlgebraicGeometry.AugmentedCechCone`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `augmentedCechConeTerm` | 増大項、元の零次項、以後の二つの項の直積からなる全複体の各項。 |
| `augmentedCechConeDifferential` | 増大項では指定した写像、その先では既存の cone の微分。 |
| `augmentedCechConeDifferential_squared` | 増大写像がサイクルへ入るなら、明示的な全微分の二乗は零。 |
| `augmentedCechCone` | 各項と微分を指定した、増大項付き cone の全複体。 |
| `augmentedCechCone_acyclic` | 増大項の単射・零次での完全性と、H⁰ の全射・正次数の同型から全複体は acyclic。 |

## AugmentedCechConeMap

モジュール：`SerrePositivity.AlgebraicGeometry.AugmentedCechConeMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `augmentedCechConeMapTerm` | 全複体の各項の射。 |
| `augmentedCechConeMapTerm_differential` | 可換四角と増大写像の自然性により、全複体の各項の射は微分と可換。 |
| `augmentedCechConeMap` | 可換四角と増大写像を保つ射が誘導する、増大項付き全複体の余鎖写像。 |
| `augmentedCechConeMapTerm_comp` | 全複体の各項への写像は成分の合成を保つ。 |
| `augmentedCechConeMapTerm_id` | 全複体の各項への恒等写像。 |

## AwayPowerMap

モジュール：`SerrePositivity.AlgebraicGeometry.AwayPowerMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `awayPowerMap` | 分母の像が b の冪であるとき、実際の Away 局所化の間に誘導される環準同型。 |
| `awayPowerMap_algebraMap` | 局所化の延長は、元の環の写像を保つ。 |
| `awayPowerMap_fraction` | 分母 a^n の分数は、分母 b^(k*n) の分数へ送られる。 |

## AwayPowerMapSemilinear

モジュール：`SerrePositivity.AlgebraicGeometry.AwayPowerMapSemilinear`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `awayPowerMap_scalar` | 局所化の延長も係数の自己準同型と可換。 |
| `awayPowerMapSemilinear` | 局所化の環準同型を、係数自己準同型に関する半線形写像として扱う。 |
| `awayPowerMapSemilinear_apply` | 半線形写像と元の局所化の環準同型の値は一致する。 |

## CechAdditiveExactTransport

モジュール：`SerrePositivity.AlgebraicGeometry.CechAdditiveExactTransport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechAdditiveShortExact_transport` | 指定した加法同型と可換な射への短完全列の移送。 |

## CechAlgebraAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraAugmentation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechAugmentationCochains` | 空交叉から長さ1の各交叉への実際の制限。 |
| `fullAlgebraCechAugmentation_mem` | 大域側から制限した切断族は適合する。 |
| `fullAlgebraCechAugmentation` | 適合する切断の部分代数への実際の増大写像。 |
| `fullAlgebraCechAugmentation_algebraMap` | 増大写像を経由した基底環の写像は、部分代数のスカラー写像そのもの。 |
| `fullAlgebraCechZeroEquiv_symm_apply` | 空タプルへの戻しは、その台への実際の制限。 |
| `fullAlgebraCechAugmentation_eq_differential` | 部分代数への増大の各成分は、既存の増大 Čech 微分の次数零と一致。 |
| `fullAlgebraCechAugmentation_surjective_of_exact` | 増大 Čech が次数零で完全なら、実際の増大の像は適合する切断すべてを含む。 |

## CechAlgebraAugmentationInjective

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraAugmentationInjective`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechAugmentation_injective_of_differential` | Čech の左端が単射なら、実際の代数の増大も単射。 |

## CechAlgebraEqualizerAddMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerAddMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechIntDiagram` | 代数係数図式の加法群を、整数加群の係数図式として扱う。 |
| `fullAlgebraCechCochainsAddMap` | 整数線形な係数写像をタプルごとの加法写像にする。 |
| `fullAlgebraCechCochainsAddMap_face` | 整数線形な係数写像は二つの面の制限と可換。 |
| `fullAlgebraCechEqualizerAddMap` | 整数線形な係数写像が適合切断の加法群に誘導する写像。 |
| `fullAlgebraCechEqualizerAddMap_apply` | 適合切断の加法写像の各成分は指定された係数の射。 |

## CechAlgebraEqualizerMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechCochainsMap` | 係数図式の射が全タプルの切断族に誘導する代数写像。 |
| `fullAlgebraCechCochainsMap_face` | タプル上の係数写像は二つの面の制限と可換。 |
| `fullAlgebraCechEqualizerMap` | 係数図式の射が適合切断の部分代数に誘導する写像。 |
| `fullAlgebraCechEqualizerMap_apply` | 適合切断の写像の各成分は指定された係数の射そのもの。 |
| `fullAlgebraCechEqualizerMap_id` | 適合切断への恒等係数写像は恒等写像。 |
| `fullAlgebraCechEqualizerMap_comp` | 適合切断の写像は係数図式の射の合成を保つ。 |

## CechAlgebraFrobeniusH0

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechFrobeniusH0SystemIso` | 適合切断環の Frobenius 系と、各段の整数係数 Čech H⁰ の系の自然同型。 |
| `algebraCechFrobeniusH0ColimitIso` | Frobenius 係数順極限の Čech H⁰ は、適合切断環の Frobenius 順極限と同型。 |

## CechAlgebraFrobeniusH0Cocycle

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Cocycle`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechFrobeniusH0ColimitIso_inv_of_cocycle` | Frobenius 各段の適合切断に対応する H⁰ 類の零次コサイクルは各成分の標準像。 |

## CechAlgebraFrobeniusH0ColimitNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0ColimitNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `square_inverse` | 可換四角で同型の逆を使っても同じ射の等式が得られる（private）。 |
| `algebraCechFrobeniusH0ColimitIso_naturality` | Čech H⁰ と切断の Frobenius 順極限の比較は、実際の係数代数の射に自然。 |

## CechAlgebraFrobeniusH0Inclusions

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Inclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechFrobeniusH0ColimitIso_ι` | Čech H⁰ 比較に各有限段から入る射を、切断環の系の標準写像で表示する。 |

## CechAlgebraFrobeniusH0Stage

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Stage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechFrobeniusH0ColimitIso_stage` | 各段の適合切断の Čech H⁰ の像は、同じ段の Frobenius 順極限の元となる。 |
| `algebraCechFrobeniusH0ColimitIso_inv_of` | 同じ標準写像の公式を比較の逆向きに述べたもの。 |

## CechAlgebraFrobeniusNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechIntMap` | 代数係数の射を、スカラー制限した整数加群の射として読む。 |
| `fullAlgebraCechEqualizerAddMap_intMap` | 整数線形として適合切断へ送っても、既存の代数写像と同じ関数。 |
| `algebraCechFrobeniusCoefficientNatTrans` | 代数係数の射は、実際の Frobenius 係数系の自然変換を誘導する。 |
| `algebraCechFrobeniusH0SystemIso_naturality` | 各段の H⁰ の同型は、実際の適合切断の写像と係数系の写像を比較する。 |

## CechAlgebraFrobeniusSystem

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusSystem`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCech_primeCast` | 基底環で p が零なら、各交叉の代数でも零。 |
| `algebraCechEqualizer_primeCast` | 基底環で p が零なら、適合切断代数でも零。 |
| `algebraCechIntFrobeniusSystemMap` | 交叉ごとの Frobenius 遷移は整数線形な係数図式の射。 |
| `algebraCechFrobeniusCoefficientFunctor` | 各交叉で同じ実際の Frobenius 順極限を取る係数関手。 |
| `fullAlgebraCechEqualizerAddMap_frobenius` | 適合切断への係数 Frobenius の作用は、切断環自身の同じ Frobenius。 |

## CechAlgebraH0

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraH0`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `algebraCechRingDiagram` | 代数係数の環図式。 |
| `algebraCechModuleDiagram` | 代数係数の加群図式。 |
| `fullAlgebraCechCochainsAlgebra` | 代数係数の全タプルの切断に、成分ごとのスカラー作用を入れる。 |
| `fullAlgebraCechFace` | 二重点での片側の制限を代数準同型として扱う。 |
| `fullAlgebraCechEqualizer` | 適合する切断の部分代数。 |
| `fullAlgebraCechEqualizer_toSubmodule` | 適合する切断の部分加群は、Čech の最初の余境界の核。 |
| `fullAlgebraCechH0Equiv` | 適合する切断の部分代数の加法群と Čech H⁰ の線形同型。 |
| `fullAlgebraCechEqualizer_finite` | Čech H⁰ が有限なら、適合する切断の部分代数も基底環上有限。 |

## CechAlgebraH0Naturality

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraH0Naturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechH0Equiv_kernel` | 適合切断から H⁰ を経由して核へ戻すと、元の切断族になる。 |
| `fullAlgebraCechH0Equiv_naturality` | 環の適合切断から Čech H⁰ への比較は、実際の係数図式の射に自然。 |

## CechAlgebraIntH0Naturality

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraIntH0Naturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `kernel_hom_subtype` | H⁰ と核の比較の後の包含は homologyπ の逆と cycles の包含の合成（private）。 |
| `kernel_naturality_apply` | H⁰ の射と核の比較は実際の零次コチェインの係数写像と可換（private）。 |
| `intH0RingCochainsModule` | 型クラスの構成：`(D : Finset ι ⥤ CommAlgCat.{u} R) (k : ℕ) : Module ℤ (FullRingCechCochains (algebraCechRingDiagram D) k)` |
| `intH0CochainsModule` | 型クラスの構成：`(D : Finset ι ⥤ CommAlgCat.{u} R) (k : ℕ) : Module ℤ (FullCechCochains (algebraCechIntDiagram D) k)` |
| `intH0KernelModule` | 型クラスの構成：`(D : Finset ι ⥤ CommAlgCat.{u} R) : Module ℤ (LinearMap.ker (fullCechDifferential (algebraCechIntDiagram D) 1))` |
| `fullAlgebraCechEqualizer_int_kernel_iff` | 適合条件は、整数係数で計算しても最初の余境界の核。 |
| `fullAlgebraCechIntKernelEquiv` | 適合切断の整数加群と、最初の余境界の核との同型。 |
| `fullAlgebraCechIntH0Equiv` | 適合切断の加法群と整数係数の Čech H⁰ の同型。 |
| `fullAlgebraCechIntH0Equiv_kernel` | 整数係数の H⁰ と核の比較で元の切断族に戻る。 |
| `fullAlgebraCechIntH0Equiv_naturality` | H⁰ の比較は整数線形な係数写像に自然。 |

## CechAlgebraNonemptyEqualizerEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraNonemptyEqualizerEquiv`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechNonemptyCochainsEquiv` | 非空交叉の比較を長さ q+1 の切断族に適用する代数同型。 |
| `fullAlgebraCechNonemptyCochainsEquiv_face` | 切断族の比較は二つの面と可換。 |
| `fullAlgebraCechNonemptyCochainsEquiv_mem_iff` | 非空交叉の比較は適合条件を保ち、かつ反映する。 |
| `fullAlgebraCechNonemptyEqualizerEquiv` | 非空交叉だけの自然な比較から得られる適合切断の代数同型。 |
| `fullAlgebraCechNonemptyEqualizerEquiv_apply` | 適合切断の同型は、各成分で指定された代数同型を適用する。 |

## CechAlgebraSectionEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraSectionEvaluation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechSectionEvaluation` | 適合切断を指定した標準開で評価する代数準同型。 |

## CechAlgebraTensorComparison

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraTensorComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechTensorComparison` | 各項の flat 底変換比較を適合する切断部分代数へ制限した線形同型。 |
| `fullAlgebraCechTensorComparison_tmul` | 部分代数の底変換比較は、純テンソルに各項の比較を適用したもの。 |

## CechAlgebraTensorKernel

モジュール：`SerrePositivity.AlgebraicGeometry.CechAlgebraTensorKernel`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullAlgebraCechTensorKernelEquiv` | 切断部分代数の flat テンソル積と、テンソル化した余境界の核の同型。 |
| `fullAlgebraCechTensorKernelEquiv_tmul` | 核の比較は、切断の純テンソルを同じ成分の純テンソルへ送る。 |

## CechAugmentedSquare

モジュール：`SerrePositivity.AlgebraicGeometry.CechAugmentedSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `CechAugmentedSquare` | 二つの Čech 複体と基底・中心の増大写像を持つ可換な四角形。 |
| `source` | 中心の零次項を加えた複体。 |
| `difference` | 実際の二つの辺の差の余鎖写像。 |
| `augmentation` | 基底の二つの辺の組の増大写像。 |
| `augmentation_cycle` | 可換性とスカラーの閉性により、増大写像は cone のサイクルへ入る。 |
| `totalComplex` | 四角形から作る明示的な増大全複体。 |

## CechAugmentedSquareMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `Map` | 基底・中心・二つの複体の射で全ての辺を保つ四角形の射。 |
| `augmentation` | 四角形の射は基底の増大写像を保つ。 |
| `totalComplexMap` | 可換な四角形の射から、全複体の余鎖写像を作る。 |
| `id` | 四角形の恒等射。 |
| `comp` | 四角形の射の合成。 |
| `totalComplexMap_id` | 全複体への写像は四角形の恒等射を保つ。 |
| `totalComplexMap_comp` | 全複体への写像は四角形の射の合成を保つ。 |

## CechAugmentedSquareSurjectiveMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechAugmentedSquareSurjectiveMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `center_naturality_of_surjective_quotient` | 商が全射なら、中心の辺の可換性は基底・スカラー・制限の可換性から従う。 |
| `Map.ofSurjectiveQuotient` | 基底から中心への全射を使い、三つの辺を保つデータから四角形の射を作る。 |

## CechAugmentedSquareTransport

モジュール：`SerrePositivity.AlgebraicGeometry.CechAugmentedSquareTransport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `transport` | 基底と中心は固定し、二つの複体と実際の辺を同型で移す。 |
| `transportMap` | 移送の実際の四角形の射。 |
| `transportMap_totalComplexMap_component_isIso` | 移送が誘導する全複体の各項の射は同型。 |
| `transportTotalComplexIso` | 二つの複体の同型は、増大項も含めた全複体の同型を与える。 |
| `transport_acyclic` | 元の全複体が acyclic なら、同じ射による移送後の全複体も acyclic。 |

## CechConeHomologyExactness

モジュール：`SerrePositivity.AlgebraicGeometry.CechConeHomologyExactness`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechRefinementCone_cycle_boundary_of_homology` | H⁰ が全射、正次数の H が全単射なら cone の各正次数サイクルは境界。 |

## CechHomologyCycleLifting

モジュール：`SerrePositivity.AlgebraicGeometry.CechHomologyCycleLifting`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `homologyCycleValue` | サイクルの H の類を opcycles に入れると元のサイクルの類になる（private）。 |
| `homologyMapCycleValue` | 短複体の H の射はサイクルの値に中央の成分の射を適用する（private）。 |
| `cechCycles_lift_of_homology_surjective` | H の全射性から、目標のサイクルを境界を除いて持ち上げる。 |
| `cechCycles_boundary_of_homology_injective` | H の単射性から、境界へ移るサイクルを元の境界へ戻す。 |

## CechRingEqualizer

モジュール：`SerrePositivity.AlgebraicGeometry.CechRingEqualizer`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `FullRingCechCochains` | 環係数の全タプル Čech 項。 |
| `fullRingCechFace` | 二重点での片側の制限。 |
| `fullRingCechEqualizer` | 二つの制限が一致する Čech 次数零の部分環。 |
| `mem_fullRingCechEqualizer` | 部分環への所属は、各二重点での一致と同値。 |

## CechScalarCokernelSupport

モジュール：`SerrePositivity.AlgebraicGeometry.CechScalarCokernelSupport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCechScalarCokernel_support_subset_of_isoOffCenter` | 中心外で同型な射の切断代数のスカラー余核の台は中心内。 |

## CechSupportOutsideCenter

モジュール：`SerrePositivity.AlgebraicGeometry.CechSupportOutsideCenter`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCechSupport_subset_of_isoOffCenter` | 中心外で同型な射の正次数 Čech H の台は中心内。 |

## CechZeroTermDifference

モジュール：`SerrePositivity.AlgebraicGeometry.CechZeroTermDifference`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechZeroTermDifferenceComponent` | 零次では二つの制限の差、正次数では元の射の成分。 |
| `cechZeroTermDifference` | 中心の増大写像を差し引いた複体の射。 |
| `shortComplexHomologyMap_eq_of_middle` | 短複体の中央成分の射が等しければ誘導される H の射も等しい（private）。 |
| `cechZeroTermDifference_positive_homology` | 正次数では差の射は元の射と射影の合成と同じ H の射を誘導する。 |
| `cechZeroTermDifference_positive_homology_isIso` | 元の射が正次数の H で同型なら、中心の項を足した差の射もそうなる。 |

## CechZeroTermExtension

モジュール：`SerrePositivity.AlgebraicGeometry.CechZeroTermExtension`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechZeroTermExtensionTerm` | 零次項のみを C⁰ × Q にする。 |
| `cechZeroTermExtensionDifferential` | 零次では第一成分へ射影し、それ以後は元の微分を使う。 |
| `cechZeroTermExtensionDifferential_squared` | 零次項を拡張した微分も二乗零。 |
| `cechZeroTermExtensionDMap` | 指定した線形微分を、元の束ねられた加群の間の射として扱う。 |
| `cechZeroTermExtension` | 零次項に中心の加群を加えた明示的な複体。 |
| `cechZeroTermExtension_d` | 拡張した複体の隣り合う項の微分は指定した線形写像。 |
| `cechZeroTermProjectionComponent` | 元の複体への射影の各次数の射。 |
| `cechZeroTermProjection` | 零次項を拡張した複体から元の複体への射影。 |
| `cechZeroTermProjection_epi` | 射影の各次数の成分は全射。 |
| `cechZeroTermProjection_positive_homology_isIso` | 零次項を加えても、正次数の短複体の H は射影により同型となる。 |

## CechZeroTermExtensionMap

モジュール：`SerrePositivity.AlgebraicGeometry.CechZeroTermExtensionMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechZeroTermExtensionMapComponent` | 零次項の直積拡張への射の各次数の成分。 |
| `cechZeroTermExtensionMap` | 複体と中心の項の射が誘導する、零次項の直積拡張の射。 |
| `cechZeroTermExtensionMap_comp` | 零次項拡張の射は合成を保つ。 |
| `cechZeroTermExtensionMap_id` | 零次項拡張の射は恒等を保つ。 |
| `cechZeroTermExtensionMap_projection` | 元の複体への射影は複体と中心の項の射に自然。 |
| `cechZeroTermDifference_naturality` | 可換な制限と中心の増大写像は、差の余鎖写像の可換四角を与える。 |

## CenterComplementLocalization

モジュール：`SerrePositivity.AlgebraicGeometry.CenterComplementLocalization`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `affineCenterComplement_localization_preimage_top` | 中心外の素点で局所化すると、中心の補開集合の逆像は全空間。 |
| `pullback_localization_isIso_of_centerComplement` | 中心外で同型な射は、中心外の素点での局所化後にも同型。 |

## CochainComplexOfExactness

モジュール：`SerrePositivity.AlgebraicGeometry.CochainComplexOfExactness`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cochainComplexOf_acyclic_of_injective_exact` | 最初の微分が単射で、連続する微分がすべて完全なら、作った複体は acyclic。 |

## ColimitInclusionTransport

モジュール：`SerrePositivity.AlgebraicGeometry.ColimitInclusionTransport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `colimitInclusion_composition` | 標準写像を保つ二つの比較の合成も標準写像を保つ。 |
| `colimitInclusion_natIso` | 自然同型で移した比較も、同じ標準写像を保つ。 |

## ConductorSquareLift

モジュール：`SerrePositivity.AlgebraicGeometry.ConductorSquareLift`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `conductorSquare_lift` | 導手に含まれるイデアルの商で一致する元は、元の環の同じ元から来る。 |
| `conductorSquare_kernel` | 導手の四角形の左の射の核は、元の環準同型の核と同じ。 |

## FiniteSupportConductor

モジュール：`SerrePositivity.AlgebraicGeometry.FiniteSupportConductor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `finiteSupport_exists_pow_map_le_conductor` | 有限環拡大の余核の台が中心内なら、中心のある冪の拡大は導手に含まれる。 |
| `finiteSupport_exists_pow_map_lift` | 中心の冪の拡大の各元は、元の環に持ち上がる。 |

## FiniteSupportPower

モジュール：`SerrePositivity.AlgebraicGeometry.FiniteSupportPower`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `finiteSupport_exists_pow_le_annihilator` | 有限加群の台が有限生成イデアルの零点集合に入れば、その冪が加群を消す。 |
| `finiteQuotientSupport_exists_pow_smul_mem` | 商加群の台が中心に入ると、元の加群の中心の冪倍は部分加群に入る。 |

## FrobeniusCenterSquare

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusCenterSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusCenterSquare_lift` | 中心の正の冪の拡大が像に入れば、指定した中心の Frobenius 四角形で同時に持ち上がる。 |

## FrobeniusConductorSquare

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusConductorSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusConductorSquare_lift` | 導手の商の四角形で一致する順極限の元は、元の環の順極限から同時に持ち上がる。 |
| `frobeniusConductorSquare_quotient_surjective` | 導手の四角形の右側の商写像は、Frobenius 順極限でも全射。 |

## FrobeniusDirectLimit

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimit`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectSystemMap` | 自然数段の間の、実際の Frobenius の反復。 |
| `frobeniusDirectSystem` | Frobenius の反復の有向系の法則。 |
| `frobeniusDirectSystemMap_apply` | Frobenius の反復の値は p の冪乗である。 |
| `FrobeniusDirectLimit` | Frobenius 順極限の環。 |
| `frobeniusDirectLimitOf` | 有限段から Frobenius 順極限への環準同型。 |
| `frobeniusDirectLimitOf_eq_zero_iff` | 有限段の元が零になるのは、ある先の p 乗反復で零になる場合に限る。 |
| `frobeniusDirectLimitOf_eq_iff` | 有限段の二つの元の像は、Frobenius を十分反復して一致する場合に限り等しい。 |
| `frobeniusDirectLimitOf_eq_zero_iff_nilpotent` | 有限段の元は、その元が冪零である場合に限って Frobenius 順極限で零になる。 |

## FrobeniusDirectLimitIntNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitIntNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusIntDirectSystemNatTrans` | 環の射が誘導する整数加群としての反復 Frobenius 系の自然変換。 |
| `frobeniusDirectLimitIntColimitIso_naturality` | Frobenius 順極限の環の射と整数加群の余極限の射は比較同型を介して一致する。 |

## FrobeniusDirectLimitInvariance

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusQuotientPrimeCast` | p が零であることは、零環になる商にも保たれる。 |
| `frobeniusDirectLimitQuotient_bijective` | nil イデアルによる商の実際の射は Frobenius 順極限上で全単射。 |
| `frobeniusDirectLimitQuotientEquiv` | nil イデアルによる商と元の環の Frobenius 順極限の canonical な環同型。 |
| `frobeniusDirectLimitUniversalHomeomorphism_bijective` | 普遍同相な環準同型は Frobenius 順極限上で全単射。 |
| `frobeniusDirectLimitUniversalHomeomorphismEquiv` | 普遍同相が誘導する Frobenius 順極限の canonical な環同型。 |

## FrobeniusDirectLimitMap

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectSystemMap_naturality` | 環の射は各段の Frobenius の反復と可換。 |
| `frobeniusDirectLimitMap` | 実際の環の射が誘導する Frobenius 順極限の環準同型。 |
| `frobeniusDirectLimitMap_of` | 順極限の射を有限段の元で評価する公式。 |
| `frobeniusDirectLimitMap_injective` | 核が nil である環の射は、Frobenius 順極限上で単射になる。 |
| `frobeniusDirectLimitMap_surjective` | 各元のある p 冪が像にある環の射は、Frobenius 順極限上で全射になる。 |
| `frobeniusDirectLimitMap_comp` | Frobenius 順極限の射は環準同型の合成を保つ。 |
| `frobeniusDirectLimitMap_id` | Frobenius 順極限の射は恒等射を保つ。 |

## FrobeniusDirectLimitModuleIso

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIso`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectLimitModuleIso` | 環の同型が誘導する、実際の Frobenius 順極限の整数加群の同型。 |
| `frobeniusDirectLimitModuleIso_of` | 同型の比較は、有限段の元に実際の環の同型を適用する。 |

## FrobeniusDirectLimitModuleIsoNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIsoNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectLimitModuleIso_naturality` | 環の同型の可換四角は、実際の Frobenius 順極限の整数加群でも可換。 |

## FrobeniusFiniteModificationExact

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationExact`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusCenterPair` | 有限変更の四角形の左の加法写像：二つの実際の制限の組。 |
| `frobeniusCenterDifference` | 有限変更の四角形の右の加法写像：二つの実際の制限の差。 |
| `frobeniusCenterDifference_pair` | 中心の四角形の二つの加法写像の合成は零。 |
| `frobeniusFiniteModification_exact` | Spec 全射で中心外が局所全射な有限環拡大の、指定中心の加法群の短完全性。 |

## FrobeniusFiniteModificationSquare

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusFiniteModificationSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusDirectLimitMap_injective_of_surjectiveSpectrum` | Spec 上全射な射は、Frobenius 順極限で単射になる。 |
| `frobeniusFiniteModificationSquare_lift` | 有限環拡大で中心外が局所全射なら、指定中心の四角形で同時に持ち上がる。 |

## FrobeniusPowerCenter

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusPowerCenter`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusPowerCenter_bijective` | 正の冪による商から元の中心による商への実際の射は、Frobenius 順極限で全単射。 |
| `surjectiveSpectrum_comap_map_pow_le_radical` | Spec 全射なら、拡大した正の冪の逆像はその冪の根基に含まれる。 |
| `frobeniusContractedPowerCenter_bijective` | Spec 全射なら、冪の商から拡大の逆像の商への因子写像は Frobenius 順極限で全単射。 |

## FrobeniusQuotientFactor

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusQuotientFactor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `quotientFactor_kernel_nil` | 根基内で中心を大きくした商の因子写像の核は nil。 |
| `frobeniusQuotientFactor_bijective` | 根基内で中心を変更する実際の商写像は、Frobenius 順極限上で全単射。 |

## FrobeniusRingDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusRingDiagram` | 各対象の実際の環の Frobenius 順極限を係数とする図式。 |
| `frobeniusRingDiagramMap` | 実際の環の図式の射が誘導する Frobenius 順極限の自然変換。 |
| `frobeniusRingDiagramMap_id` | 係数図式の恒等射を保つ。 |
| `frobeniusRingDiagramMap_comp` | 係数図式の射の合成を保つ。 |
| `frobeniusRingDiagramIso` | 係数図式の同型は、実際の Frobenius 順極限の係数図式の同型を与える。 |
| `frobeniusRingDiagram_precomp` | 添字の引き戻しと、実際の環ごとの Frobenius 順極限は同じ図式を与える。 |
| `frobeniusRingDiagramMap_precomp` | 環の図式の射も、添字の引き戻しと Frobenius 順極限の交換に整合する。 |
| `frobeniusRingDiagramMap_commutes` | 実際の環の切断の可換四角は、Frobenius 順極限後も同じ可換四角を与える。 |

## FrobeniusRingSequentialDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusRingSequentialDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusRingObjectSystem` | 各対象の環の Frobenius 系と、制限の実際の環準同型。 |
| `frobeniusRingSequentialDiagram` | 同じ系を、Frobenius の各段を外側の添字とする図式にする。 |
| `frobeniusRingObjectColimitIso` | 各環の順極限との比較は、環の図式の制限に自然。 |
| `frobeniusRingSequentialColimitIso` | 図式の順極限は、同じ各環の実際の Frobenius 順極限を係数に持つ図式。 |

## FrobeniusRingSequentialNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusRingSequentialNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusRingObjectSystemMap` | 環の図式の射を、各対象の実際の Frobenius 系の射へ送る。 |
| `frobeniusRingSequentialDiagramMap` | 同じ環の図式の射を、Frobenius 段を外側にした図式の射へ送る。 |
| `frobeniusRingObjectColimitIso_naturality` | 各対象の環の順極限との比較は、実際の環の図式の射に自然。 |
| `frobeniusRingSequentialColimitIso_naturality` | 図式の順極限と実際の環の Frobenius 順極限の比較は、環の図式の射に自然。 |

## FrobeniusSquareLift

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusSquareLift`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusSquare_lift_same_stage` | 同じ有限段の二つの元が順極限の四角形で一致すれば、有限段の持ち上げを使える。 |
| `frobeniusSquare_lift` | 有限段で持ち上げ可能な環の四角形は、Frobenius 順極限でも持ち上げ可能。 |

## FrobeniusThickeningMap

モジュール：`SerrePositivity.AlgebraicGeometry.FrobeniusThickeningMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusThickeningMap` | n から p^e*n への反復 Frobenius の、実際の商環の写像。 |
| `frobeniusThickeningMap_mk` | 厚化を経由する写像は、代表元を p^e 乗に送る。 |
| `frobeniusThickeningPower_le` | 厚い段から元の段へ戻るためのイデアルの包含。 |
| `frobeniusThickeningMap_factor` | 厚化を経由して元の商へ戻すと、その商の反復 Frobenius そのものになる。 |
| `frobeniusThickeningMap_projection` | 元の環から厚化への写像と反復 Frobenius の可換性。 |
| `frobeniusThickeningMap_transition` | 厚化を経由する反復 Frobenius は、厚さを下げる遷移と可換。 |

## FullCechComplexHomExt

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechComplex_hom_ext` | 各次数・各タプルで等しい全タプル Čech 複体の二つの射は等しい。 |

## FullCechH0Compatible

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechH0Compatible`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechDifferential_one_apply` | 最初の余境界は二つの制限の差。 |

## FullCechH0Kernel

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechH0Kernel`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechH0KernelIso` | 全タプル Čech H⁰ と最初の余境界の核の比較。 |

## FullCechH0KernelEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechH0KernelEvaluation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechH0KernelIso_naturality_apply` | H⁰ の写像は零次コサイクルの各成分で元の係数写像に一致する。 |

## FullCechH0KernelNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechH0KernelNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechH0KernelIso_hom_subtype` | H⁰ と核の比較の後の包含は、homologyπ の逆と cycles の包含の合成。 |
| `fullCechH0KernelIso_naturality_subtype` | H⁰ の写像と最初の余境界の核への比較は、実際の零次項の写像と可換。 |

## FullCechH0ZeroTermCochains

モジュール：`SerrePositivity.AlgebraicGeometry.FullCechH0ZeroTermCochains`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechComplex_d` | 通常の Čech 複体の微分は指定したコチェイン微分。 |
| `fullCechH0ZeroTermCochainMap` | H⁰ と中心の項の組を零次コサイクルと中心の項の組へ写す線形写像。 |
| `fullCechH0ZeroTermCochainMap_injective` | H⁰ と中心の項から実際の零次コチェインへの写像は単射。 |
| `fullCechH0ZeroTermCochainMap_cycle` | 上の写像の像は零次項拡張のコサイクル。 |
| `fullCechH0ZeroTermCochainMap_surjective_cycles` | 零次項拡張のすべてのコサイクルは H⁰ と中心の項の組から来る。 |

## LinearDirectLimitCocone

モジュール：`SerrePositivity.AlgebraicGeometry.LinearDirectLimitCocone`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `linearDirectSystemFunctor` | 線形写像の実際の有向系を加群圏の関手にする。 |
| `linearDirectSystemCocone` | 代数的な順極限の標準写像は、実際の有向系の余錐。 |
| `linearDirectSystemIsColimit` | 代数的な順極限の線形写像の普遍性は、加群圏の余極限の普遍性を与える。 |
| `linearDirectLimitColimitIso` | 代数的な順極限と、同じ関手の圏論的な余極限の標準同型。 |

## LinearDirectLimitColimitMap

モジュール：`SerrePositivity.AlgebraicGeometry.LinearDirectLimitColimitMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `linearDirectSystemColimitMap_bijective` | 代数的順極限の比較が全単射なら、同じ射の圏論的余極限も全単射。 |

## LinearDirectLimitComparison

モジュール：`SerrePositivity.AlgebraicGeometry.LinearDirectLimitComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `linearDirectLimitComparison` | 可換な段ごとの線形写像が誘導する、実際の加群の順極限の線形写像。 |
| `linearDirectLimitComparison_of` | 順極限の比較は、有限段では指定した線形写像。 |
| `linearDirectLimitComparison_injective` | 各段の核の元が後の段で消えるなら、順極限の比較は単射。 |
| `linearDirectLimitComparison_surjective` | 標的の各元が後の段で像に入るなら、順極限の比較は全射。 |

## LinearDirectLimitNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.LinearDirectLimitNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `linearDirectLimitColimitIso_ι` | 順極限の比較同型は各有限段からの標準写像を保つ。 |
| `linearDirectSystemNatTrans` | 有向系の段ごとの可換写像を関手間の自然変換として読む。 |
| `linearDirectLimitColimitIso_naturality` | 代数的順極限と圏論的余極限の同型は、有向系の射に自然。 |

## LinearKernelSquareEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.LinearKernelSquareEquiv`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `linearKernelEquivOfCommute` | 可換な正方形の同型を核に制限する。 |
| `linearKernelEquivOfCommute_apply` | 核の比較の順写像は、元の線形同型そのもの。 |
| `linearKernelEquivOfCommute_symm_apply` | 核の比較の逆写像は、元の線形同型の逆そのもの。 |

## LocalizedCokernelSupport

モジュール：`SerrePositivity.AlgebraicGeometry.LocalizedCokernelSupport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cokernel_support_subset_of_localized_surjective` | 中心外で局所化した射が全射なら、その余核の台は中心内にある。 |
| `finiteLocalizedSurjective_exists_pow_map_lift` | 中心外で局所化した有限環拡大が全射なら、中心の冪の拡大は元の環の像に入る。 |

## ModuleCatFilteredExact

モジュール：`SerrePositivity.AlgebraicGeometry.ModuleCatFilteredExact`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `moduleCatFiltered_hasExactColimitsOfShape` | 任意の大きさの係数環上の加群で、同じ宇宙の filtered 余極限は完全。 |

## OpenCoverFrobeniusRefinement

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinement`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechIndexFunctor` | 有限個の開集合の交叉への、反変な添字の関手。 |
| `openCoverCechRingDiagram` | 実際の環の前層を有限交叉上の切断の環の図式に制限する。 |
| `openCoverFrobeniusCechDiagram_eq` | 有限交叉への制限と実際の環ごとの Frobenius 順極限は同じ係数図式を与える。 |
| `openCoverFrobeniusCechCoefficientMap_eq` | 係数の実際の環の射も、有限交叉への制限と Frobenius 順極限の交換に整合する。 |
| `openCoverFrobeniusCechRefinement_naturality` | Frobenius 順極限後の細分の射は、元の環の前層の射に自然。 |
| `openCoverFrobeniusCechRefinement_homologyMap_eq` | Frobenius 順極限後も Čech H 上の細分写像は添字の選択によらない。 |

## OpenCoverFrobeniusRefinementQuasiIso

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinementQuasiIso`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `openCoverIntCechRefinement_quasiIsoAt_of_iso` | 係数前層の同型に沿う、同じ細分写像の Čech H の同型性の移送。 |
| `openCoverFrobeniusCechRefinement_quasiIsoAt` | 有限段の細分が Čech H の同型なら、実際の環の Frobenius 順極限後も同型。 |

## OpenCoverSequentialCech

モジュール：`SerrePositivity.AlgebraicGeometry.OpenCoverSequentialCech`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `openCoverIntCechFunctor` | 交叉への制限と既存の全タプル複体を合成した、整数係数の Čech 関手。 |
| `openCoverIntCechRefinementNatTrans` | 細分の写像は整数係数の前層を動かす自然変換。 |
| `openCoverIntCechFunctorPreservesSequentialColimits` | 有限被覆の整数係数 Čech 関手は自然数順極限を保つ。 |
| `openCoverSequentialCech_refinement_naturality` | 複体の順極限比較は、同じ実際の細分写像と可換。 |
| `openCoverSequentialCech_refinement_quasiIsoAt` | 細分が各有限段の Čech H で同型なら、係数前層の順極限でも同型。 |

## OpenIsomorphismBaseChange

モジュール：`SerrePositivity.AlgebraicGeometry.OpenIsomorphismBaseChange`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `isIso_of_restrict_top` | 全空間への制限が同型なら、元の射も同型。 |
| `pullback_snd_isIso_of_open_preimage_top` | 同型な開部分の逆像が全空間なら、底変換した射は同型。 |

## ProjectiveCechFilteredHomologyInclusions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredHomologyInclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFilteredHomologyIso_ι` | 有限段の Čech H の射は、filtered 比較によって各段の H の標準写像へ送られる。 |

## ProjectiveCechFilteredInclusions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredInclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFilteredComplexIso_ι` | 複体の余極限比較は、有限段からの実際の標準写像を標準写像へ送る。 |
| `projectiveCechFilteredComplexIso_inv_ι` | 逆比較で標準写像を戻すと、有限段の係数から誘導した同じ複体の射となる。 |
| `projectiveCechFilteredHomologyIso_ι_factor` | 有限段の Čech H の写像と filtered 比較を、複体の余極限の H の比較へ分離する。 |

## ProjectiveCechFiniteCenterExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteCenterExact`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSectionAlgebra_localized_surjective` | 中心外では、基底から射影 Čech 切断環への写像の局所化は全射。 |
| `projectiveCechFiniteCenter_exact` | 射影構造射の有限切断環による中心の四角形は Frobenius 順極限で短完全。 |

## ProjectiveCechFrobeniusColimitPositive

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusColimitPositive`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFrobeniusHomologyColimit_closed_bijective` | 正次数の各段の Čech H の圏論的余極限は、実際の閉厚化への制限で全単射に移る。 |
| `projectiveFrobeniusColimitCech_closed_bijective` | Frobenius の係数順極限で作った正次数 Čech H の閉厚化への制限は全単射。 |
| `reesClosedFrobeniusColimitCechHomologyMap_bijective` | 同じ Čech 複体の閉厚化への制限は、正次数の H で全単射を誘導する。 |

## ProjectiveCechFrobeniusDirectLimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusDirectLimit`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ProjectiveCechFrobeniusDirectLimit` | 実際の標準開 Čech H の Frobenius に沿う加群の順極限。 |
| `reesClosedCechFrobeniusDirectLimitMap` | 実際の閉厚化への射影が誘導する、Čech H の Frobenius 順極限の写像。 |
| `reesClosedCechFrobeniusDirectLimitMap_injective` | 中心の冪による零化の下で、閉厚化への Čech H の Frobenius 順極限の射は単射。 |
| `reesClosedCechFrobeniusDirectLimitMap_surjective` | 閉厚化への Čech H の Frobenius 順極限の射は、像の安定化により全射。 |

## ProjectiveCechFrobeniusFunctor

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusFunctor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFrobeniusCoefficientFunctor` | 各標準開で実際の Frobenius の反復を取る自然数の係数図式。 |
| `projectiveCechFrobeniusHomologyDiagramIso` | Frobenius の各段の Čech H は、代数的順極限に使った同じ有向系を与える。 |
| `projectiveCechFrobeniusHomologyColimitIso` | 実際の Frobenius 順極限と、各段の Čech H の圏論的余極限の同型。 |

## ProjectiveCechFrobeniusPositive

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusPositive`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFrobeniusDirectLimit_closed_bijective` | 中心外で同型な射影スキームの正次数の実際の Čech H の Frobenius 順極限は、 閉厚化の同じ順極限へ実際の制限写像によって全単射に移る。 |

## ProjectiveCechIntFiltered

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFiltered`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechFilteredHomologyNatIso` | 2e の filtered 余極限と Čech H の比較を自然同型としてまとめる。 |
| `projectiveIntCechFilteredHomologyNatIso` | 整数係数の Čech H の filtered 余極限比較。 |
| `projectiveIntCechFilteredHomologyIso` | 整数係数の図式ごとの Čech H の filtered 余極限同型。 |

## ProjectiveCechIntFilteredInclusions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFilteredInclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechFilteredHomologyIso_ι` | 整数係数の Čech H の既存の比較は有限段からの標準写像を保つ。 |

## ProjectiveCechIntFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechIntFrobeniusDiagram` | 捻り零の標準開図式の整数線形な反復 Frobenius。 |
| `projectiveCechIntFrobeniusDiagram_zero` | 零回の反復は標準開図式の恒等射。 |
| `projectiveCechIntFrobeniusDiagram_add` | 反復回数の加法は標準開図式の射の合成に対応する。 |

## ProjectiveCechIntFrobeniusHomology

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFrobeniusHomology`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ProjectiveCechIntHomology` | 捻り零の標準開の Čech H を整数加群として読む。 |
| `projectiveCechIntFrobeniusHomology` | 実際の標準開の p^e 乗から誘導される Čech H の反復 Frobenius。 |
| `projectiveCechIntFrobeniusHomology_zero` | Čech H 上の零回の反復は恒等写像。 |
| `projectiveCechIntFrobeniusHomology_add` | Čech H 上で反復回数の加法は写像の合成になる。 |
| `projectiveCechIntFrobeniusHomology_directedSystem` | 実際の Čech H の反復 Frobenius は、自然数段の有向系を与える。 |

## ProjectiveCechIntLift

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLift`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechLiftDiagram` | 整数係数の同じ加群を ULift ℤ の加群として扱う。 |
| `projectiveIntCechLiftRoundtripIso` | ULift ℤ への移送を整数へ戻すと、元の係数図式になる。 |
| `projectiveIntCechLiftHomologyIso` | ULift ℤ に移した Čech H と元の整数係数の Čech H の同型。 |

## ProjectiveCechIntLiftNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLiftNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechLiftFunctor` | 整数係数の図式を ULift ℤ の図式へ移す関手。 |
| `projectiveIntCechLiftRoundtripIso_inv_naturality` | 係数の往復同型の逆は係数図式の射に自然。 |
| `projectiveIntCechLiftHomologyIso_naturality` | ULift ℤ への Čech H の移送は係数図式の射に自然。 |
| `projectiveIntCechLiftHomologyNatIso` | 整数係数の Čech H を同じ宇宙の係数環で計算する自然同型。 |

## ProjectiveCechIntRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntRestriction`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechIntRestrictionComplexIso` | Čech 複体の形成は整数加群への係数制限と交換する。 |
| `projectiveCechIntRestrictionHomologyIso` | Čech H の整数加群への係数制限との比較。 |
| `projectiveCechIntRestrictionComplexIso_naturality` | 整数係数への複体比較は、係数図式の射に自然。 |
| `projectiveCechIntRestrictionHomologyIso_naturality` | 整数係数への Čech H の比較は、係数図式の射に自然。 |

## ProjectiveCechIntSequential

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequential`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechSequentialHomologyNatIso` | 自然数の整数係数 Čech H と順極限の自然同型。 |
| `projectiveIntCechSequentialHomologyIso` | 自然数で添字付けした係数図式ごとの Čech H の順極限同型。 |
| `projectiveIntCechSequentialHomologyIso_naturality` | 順極限の Čech H の比較は実際の係数系の射に自然。 |

## ProjectiveCechIntSequentialInclusions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequentialInclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechSequentialHomologyIso_ι` | 整数係数の Čech H の順極限比較は各自然数段からの標準写像を保つ。 |

## ProjectiveCechScalarConductor

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechScalarConductor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechScalarCokernel_support` | 射影標準開の切断部分代数のスカラー余核の台は中心内。 |
| `projectiveCechScalarCokernel_power_annihilates` | 射影の次数零の切断代数のスカラー余核は、中心のある冪で消える。 |
| `projectiveCechSectionAlgebra_exists_pow_map_lift` | 中心の十分高い冪を切断代数へ拡大したイデアルの元は、基底環に持ち上がる。 |

## ProjectiveCechSectionAlgebra

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionAlgebra`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSectionAlgebra` | 実際の Proj の標準開の適合する切断の部分代数。 |
| `projectiveCechSectionAlgebra_finite` | 標準開の切断の部分代数は基底環上有限。 |

## ProjectiveCechSectionComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSectionAlgebraEquiv` | 標準開の斉次局所化と Proj の構造層から作る適合切断代数の同型。 |
| `projectiveCechSectionAlgebraEquiv_apply` | 適合切断代数の比較の各成分は、実際の標準開の切断への比較。 |
| `projectiveCechSectionAlgebraEquiv_algebraMap` | 切断代数の比較は、四角形の増大写像である基底スカラーを保つ。 |

## ProjectiveCechSectionSpectrum

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSectionSpectrum`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSectionAlgebra_surjectiveSpectrum` | 全射な射影構造射の Čech 切断環は、基底の Spec に全射する。 |
| `projectiveCechSectionAlgebra_primeCast` | 基底環で p が零なら、Čech 切断環でも p は零。 |
| `projectiveCechSectionAlgebra_frobenius_injective` | 全射な射影構造射は、Čech 切断環の Frobenius 順極限への単射を与える。 |

## ProjectiveCechSequentialComplex

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSequentialComplex`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveIntCechLiftComplexNatIso` | 整数係数の複体と、ULift ℤ に移して戻した複体の自然同型。 |
| `projectiveIntFullCechFunctorPreservesSequentialColimits` | 有限被覆の整数係数 Čech 複体は任意の宇宙で自然数順極限を保つ。 |
| `projectiveIntCechSequentialComplexIso` | 係数の自然数順極限の Čech 複体と、各段の複体の順極限との標準同型。 |

## ProjectiveCechSupportGradedPower

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSupportGradedPower`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSupport_graded_power_annihilates` | 中心外で同型な射影スキームの正次数 Čech H の次数表示も、中心のある冪で零化される。 |

## ProjectiveCechSupportPower

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveCechSupportPower`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechSupport_power_annihilates` | 中心外で同型な射影スキームの正次数 Čech H は中心のある冪で消える。 |

## ProjectiveChartFrobeniusRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRestriction`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveChartRingFrobeniusRestriction` | 標準開を狭める実際の環の射が誘導する、Frobenius 系の自然変換。 |
| `projectiveChartFrobeniusRingSystemIso_restriction` | 係数関手と環の Frobenius 系の比較は標準開の制限に自然。 |
| `projectiveChartFrobeniusRingSystemColimit_restriction` | 標準開の制限に関する同じ可換四角形は、系の余極限でも成り立つ。 |
| `projectiveChartFrobeniusRingColimitIso_restriction` | 標準開ごとの環の順極限表示は、実際の標準開環の制限に自然。 |

## ProjectiveChartFrobeniusRingColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRingColimit`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousChart_primeCast` | 基底で零となる p は、次数零局所化の環でも零。 |
| `projectiveChartRingFrobeniusFunctor` | 標準開の環の反復 Frobenius の整数加群の系。 |
| `projectiveChartFrobeniusRingSystemIso` | 同じ標準開の加群の Frobenius 系と、実際の環の Frobenius 系の自然同型。 |
| `projectiveChartFrobeniusRingColimitIso` | 係数図式の順極限の各標準開は、同じ標準開環の Frobenius 順極限と同型。 |

## ProjectiveChartFrobeniusRingStage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRingStage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveChartFrobeniusRingColimitIso_ι` | 各標準開の比較に有限段から入る射は、環の系の同じ標準写像である。 |
| `projectiveChartFrobeniusRingColimitIso_stage` | 有限段の元は実際の斉次局所化の環の同じ Frobenius 標準元へ移る。 |

## ProjectiveChartIteratedFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveChartIteratedFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `iteratedFrobeniusIntGradedAction` | 型クラスの構成：`: SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι` |
| `projectiveChartIteratedFrobenius` | 捻り零の標準開の、実際の反復 Frobenius の半線形自己写像。 |
| `projectiveChartIteratedFrobenius_val` | 標準開の反復 Frobenius の値は、周囲の局所化環の p^e 乗。 |

## ProjectiveFilteredComplexQuasiIso

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredComplexQuasiIso`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveFilteredComplexMap_quasiIsoAt` | 各段で次数 q の H に同型を誘導する射は、filtered 余極限でもそうなる。 |
| `projectiveFilteredComplexMap_quasiIso` | 各段の quasi-isomorphism は filtered 余極限でも quasi-isomorphism。 |

## ProjectiveFilteredComplexStage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredComplexStage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `stage_square_inverse` | 有限段の比較の可換四角で同型の逆を用いた等式が得られる（private）。 |
| `projectiveFilteredComplexStageExactColimits` | 型クラスの構成：`: HasExactColimitsOfShape J (ModuleCat.{u} R)` |
| `projectiveFilteredComplexStageIso` | 短複体の図式を評価すると、同じ有限段の複体の短複体となる。 |
| `projectiveFilteredComplexShortComplexIso_ι` | 有限段からの短複体の射と、複体の余極限の標準写像は比較を介して一致する。 |
| `projectiveFilteredComplexHomologyIso_ι` | 複体の filtered H 比較は、有限段からの標準写像と可換。 |
| `projectiveFilteredComplexHomologyIso_ι_canonical` | 複体の H の比較は、各段の H からの canonical な標準写像を保つ。 |

## ProjectiveFilteredHomologyInclusions

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomologyInclusions`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveFilteredHomologyInclusionsExactColimits` | 型クラスの構成：`: HasExactColimitsOfShape J (ModuleCat.{u} R)` |
| `projectiveFilteredColimitInclusion` | 評価関手から余極限関手への、標準写像の自然変換。 |
| `projectiveFilteredShortComplexHomologyInclusion` | 短複体の H の比較は、有限段からの標準写像と可換。 |
| `projectiveFilteredShortComplexHomologyIso_ι` | 短複体の図式の H の比較は、各段からの標準写像を標準写像へ送る。 |

## ProjectiveFrobeniusCanonicalDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousPerfectChartDiagram` | 各標準開の環の図式から直接作る、自然な Frobenius 順極限の係数図式。 |
| `projectiveFrobeniusRingChartDiagram_isoCanonical` | F8 の環の係数図式は、環の図式から直接作るものと制限も含めて一致する。 |

## ProjectiveFrobeniusCanonicalProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalProjection`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `frobeniusCanonicalProjectionGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedFrobeniusRingChartMap_canonical` | 閉厚化への制限は、実際の代数係数の環の射影に Frobenius を適用した自然変換。 |

## ProjectiveFrobeniusCanonicalScalar

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalScalar`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousChartScalarNatTrans` | 基底環の定数図式から標準開の実際の切断の環図式へのスカラーの自然変換。 |
| `projectivePerfCechScalarAugmentation_canonical` | 係数図式の canonical な比較を介しても、スカラーの増大写像は同じ環の射。 |

## ProjectiveFrobeniusColimitCech

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusColimitCech`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveFrobeniusColimitCechComplex` | 実際の標準開係数の Frobenius 順極限から作る Čech 複体。 |
| `reesClosedFrobeniusColimitCechMap` | 閉厚化への実際の制限を係数の Frobenius 順極限の Čech 複体へ移す。 |
| `reesClosedFrobeniusColimitCechHomologyMap` | 同じ閉厚化の複体の射が誘導する各次数の Čech H の写像。 |
| `projectiveFrobeniusColimitCechHomologyIso` | この複体の Čech H と各段の Čech H の順極限の同型。 |

## ProjectiveFrobeniusRingCechPositive

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingCechPositive`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedFrobeniusRingCechHomologyMap_bijective` | 標準開の環の Frobenius 順極限による Čech H では、閉厚化への制限は正次数で全単射。 |

## ProjectiveFrobeniusRingChartDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingChartDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveFrobeniusRingChartDiagram` | 各標準開の実際の環の Frobenius 順極限を整数加群の係数図式にする。 |
| `projectiveFrobeniusRingChartDiagram_map` | 移した図式の制限は実際の環の制限が誘導する Frobenius 順極限の射。 |
| `projectiveFrobeniusRingChartDiagramIso` | Frobenius 係数順極限と標準開の環の順極限との、標準開に関する自然同型。 |
| `projectiveFrobeniusRingChartCechIso` | Frobenius 係数の Čech 複体は、標準開の実際の環の順極限の Čech 複体と同型。 |

## ProjectiveGradedAwayPowerMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayPowerMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveGradedAwayPowerMap` | 分子の次数条件から、指定次数の局所化の間の半線形写像を得る。 |
| `projectiveGradedAwayPowerMap_val` | 指定次数部分の写像は、周囲の加群局所化の写像の制限。 |

## ProjectiveHomogeneousChartAlgebra

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousAwayAlgebra` | 既存の斉次局所化の加群構造と整合する、基底環上の代数構造。 |
| `homogeneousChartAlgebraBase` | 型クラスの構成：`(f : A) : Algebra R (HomogeneousLocalization.Away G f)` |
| `projectiveHomogeneousChartRestrictionAlgHom` | 標準開の制限を、既存の線形写像と同じ基底環上の代数写像にする。 |
| `projectiveHomogeneousChartAlgebraDiagram` | 標準開の斉次局所化の代数係数図式。 |
| `projectiveHomogeneousChartAlgebraDiagram_forget` | 代数図式の忘却は、既存の斉次局所化の加群図式に一致する。 |

## ProjectiveHomogeneousClosedCenterAdd

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterAdd`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedCenterAddGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousClosedCenterDifference_add` | 切断環側の閉厚化の差写像は加法を保つ。 |

## ProjectiveHomogeneousClosedCenterExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterExact`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `homogeneousClosedCenterExactGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousClosedCenterComparison` | 商切断環から閉厚化の切断環への、実際の Frobenius 順極限の射。 |
| `projectiveHomogeneousClosedCenterDifference` | 閉厚化の切断を右端に持つ差写像。 |
| `projectiveHomogeneousClosedCenter_exact` | 射影構造射の中心の四角形は、切断の Frobenius 順極限で短完全。 |

## ProjectiveHomogeneousClosedCenterMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterMaps`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ringHom_map_sub_explicit` | 環準同型は二つの元の差を保つ（private）。 |
| `homogeneousClosedCenterMapsGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousClosedCenterBaseMap` | 基底の中心の環から閉厚化の適合切断への実際の環準同型。 |
| `projectiveHomogeneousClosedCenterBaseMap_mk` | 基底の中心の元の代表元は、閉厚化の切断の同じスカラーへ送られる。 |
| `projectiveHomogeneousClosedCenterDifference_apply` | 完全列の差写像は、切断の実際の閉厚化への制限と基底の中心からの射の差。 |

## ProjectiveHomogeneousFiniteCenterExact

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFiniteCenterExact`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionAlgebra_surjectiveSpectrum` | 全射な射影構造射の斉次切断代数は、基底の Spec に全射する。 |
| `projectiveHomogeneousSectionAlgebra_localized_surjective` | 中心外では、基底から斉次切断代数への局所化した写像は全射。 |
| `projectiveHomogeneousFiniteCenter_exact` | 斉次切断代数の有限変更の四角形は Frobenius 順極限で短完全。 |

## ProjectiveHomogeneousFrobeniusChartStage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusChartStage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousFrobeniusChartColimitIso` | 実際の標準開環と、斉次代数係数の順極限との係数図式の比較。 |
| `projectiveHomogeneousFrobeniusRingCechIso_inv` | 既存の複体比較の逆は係数図式の比較の逆から誘導される。 |
| `projectiveHomogeneousFrobeniusChartColimitIso_stage` | 斉次代数係数の有限段の元は、実際の標準開環の同じ Frobenius 標準元に移る。 |

## ProjectiveHomogeneousFrobeniusH0

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousFrobeniusCoefficientIso` | 多項式加群と斉次標準開の係数 Frobenius 系の自然同型。 |
| `projectiveHomogeneousFrobeniusRingCechIso` | F6 の標準開環の複体と、斉次代数係数の Frobenius 順極限の複体の同型。 |
| `projectiveHomogeneousFrobeniusRingCechH0Iso` | F6 と同じ標準開環の複体の Čech H⁰ と、切断環の Frobenius 順極限との同型。 |

## ProjectiveHomogeneousFrobeniusH0Stage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0Stage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectivePerfCechH0ScalarClass_stage` | 実際の標準開環の Čech H⁰ のスカラー類は、有限段のスカラー類の像である。 |

## ProjectiveHomogeneousIteratedFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousIteratedFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousChartLinearEquiv_iteratedFrobenius` | 加群のチャートの反復 Frobenius は、斉次局所化の実際の p^e 乗と一致する。 |
| `projectiveProjNativeChart_iteratedFrobenius` | 同じ反復 Frobenius は実際の Proj の標準開の切断の p^e 乗に一致する。 |

## ProjectiveHomogeneousRingDiagramMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingDiagramMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousModuleDiagramMap` | 同じ次数零加群の射を、斉次局所化の線形な係数図式へ移す。 |
| `projectiveHomogeneousModuleDiagramMap_apply` | 移した線形写像は、実際の斉次局所化の環の写像に等しい。 |
| `projectiveHomogeneousRingDiagramMap` | 実際の環の係数図式の射。 |

## ProjectiveHomogeneousScalarCocycle

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousScalarCocycle`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarCocycleGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousSectionAlgebra_algebraMap_apply` | 適合切断代数の基底スカラーは、各標準開で同じ基底スカラー。 |
| `projectiveHomogeneousScalarCechIntH0_cocycle` | 有限段のスカラーの Čech H⁰ 類の零次コサイクルは、各標準開で同じスカラー。 |

## ProjectiveLocalizedIteratedFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedIteratedFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedPowerMap_frobenius` | 反復 Frobenius を延長した局所化の写像は、実際の局所化環の冪写像。 |

## ProjectiveLocalizedPowerMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedPowerMap` | 標準開の加群局所化の間で、分母を冪に送る実際の半線形写像。 |
| `projectiveLocalizedPowerMap_fraction` | 加群局所化の分数の像は、分子 φ(x)、分母 s^(k*n)。 |

## ProjectiveLocalizedPowerNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedPowerMap_naturality` | 係数の可換四角形は、分母を同じ冪に送る局所化の可換四角形を与える。 |

## ProjectiveLocalizedPowerRestriction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerRestriction`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveLocalizedPowerMap_restriction` | 半線形な局所化の写像は、標準開を狭める制限と可換。 |

## ProjectiveNatGradingPowerMap

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveNatGradingPowerMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveNatGradingInt_map_mem_mul` | 自然数次数を k 倍する加法写像は、零延長した整数次数も k 倍する。 |
| `projectiveNatGradingInt_chart_map_mem_mul` | 標準開で分母の指数を k 倍すると、捻りも k 倍になる。 |

## ProjectivePerfCechAugmentedSquare

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechAugmentedSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechAugmentedSquareGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechAugmentedSquare` | F8 の実際のスカラー・中心・閉厚化の射を、可換四角形のデータにまとめる。 |
| `projectivePerfCechAugmentedSquare_totalComplex` | データから作る全複体は、F8 で検証した既存の実際の全複体そのもの。 |
| `projectivePerfCechAugmentedSquare_acyclic` | 自然な四角形のデータとして表した F8 の全複体の acyclicity。 |
| `projectivePerfCechAugmentedSquare_quotient_surjective` | 実際の基底から中心への商写像は、Frobenius 順極限でも全射。 |

## ProjectivePerfCechBlowupSquareTotal

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechBlowupSquareTotal`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechBlowupSquareTotalGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechSquareAugmentation_cone_cycle` | 実際の基底の増大写像は cone の零次サイクルへ入る。 |
| `projectivePerfCechBlowupSquareTotalComplex` | 実際の射影中心の四角形の増大全複体。 |
| `projectivePerfCech_blowupSquare_acyclic` | 射影中心の実際の四角形の増大全複体は acyclic。 |

## ProjectivePerfCechCenterAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterAugmentation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechCenterAugmentationGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveClosedCenterChartMap` | 中心の環から閉厚化の各標準開へ入る実際の環準同型。 |
| `projectiveClosedCenterChartMap_mk` | 中心の代表元は各標準開で同じ基底スカラーとなる。 |
| `projectivePerfCechCenterAugmentation` | 中心の環から各標準開への写像で作る、零次の増大写像。 |

## ProjectivePerfCechCenterCocycle

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterCocycle`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechCenterCocycleGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0CenterClass_of_mk_cocycle` | 有限段の中心の代表元に対する H⁰ 類のコサイクルは実際の増大写像の値。 |
| `projectivePerfCechH0CenterClass_augmentation` | 中心の H⁰ 類の零次コサイクルは、任意の元で実際の増大写像に一致する。 |
| `projectivePerfCechCenterAugmentation_cycle` | 中心の実際の増大写像の像は零次コサイクル。 |

## ProjectivePerfCechH0CenterClass

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0CenterClass`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0CenterClassGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0CenterClass` | 基底の中心の Frobenius 順極限から閉厚化の Čech H⁰ への写像。 |

## ProjectivePerfCechH0CenterStage

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0CenterStage`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechCenterStageGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0CenterClass_of_mk` | 中心の有限段の代表元の H⁰ 類は、閉厚化上の同じスカラーの類である。 |

## ProjectivePerfCechH0DifferenceHom

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0DifferenceHom`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareExactGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0DifferenceHom` | 独立に検証した零・加法保存で束ねた H⁰ の差の加法準同型。 |
| `projectivePerfCechH0DifferenceHom_apply` | 束ねた差写像の台の関数は固定した差写像。 |

## ProjectivePerfCechH0EquivLaws

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0EquivLaws`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareAddGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0Equiv_symm_apply` | 比較の逆加法同型は既存の逆線形写像そのもの。 |
| `projectivePerfCechH0Iso_inv_add` | H⁰ 比較の逆線形写像は加法を保つ。 |

## ProjectivePerfCechH0Evaluation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Evaluation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0EvalGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0CenterEquiv_apply` | 中央項の比較の成分は既存の H⁰ 比較。 |
| `projectivePerfCechH0Iso_inv_sub` | 逆 H⁰ 比較は差を保つ。 |
| `projectivePerfCechH0Iso_inv_hom` | H⁰ 比較の後にその逆を適用すると元のコホモロジー類に戻る。 |
| `projectivePerfCechH0Iso_inv_congr` | 等しい切断の極限の元に逆 H⁰ 比較を適用しても等しい。 |
| `projectivePerfCechH0Iso_inv_eq` | 比較した元との等式から逆比較の値を求める。 |

## ProjectivePerfCechH0PairEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0PairEvaluation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0PairEvalGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0ScalarClass` | 基底の Frobenius 順極限から標準開の Čech H⁰ へ送るスカラーの類。 |
| `projectivePerfCechH0Pair_apply` | 左側の組の写像は、スカラーの H⁰ 類と基底の中心への実際の商写像の組。 |
| `projectivePerfCechH0ScalarClass_of` | 有限段のスカラーは、同じ段の切断代数のスカラーの類へ送られる。 |
| `projectivePerfCechH0Pair_snd_of` | 組の写像の中心側の成分は、有限段で実際の商の元を取る。 |

## ProjectivePerfCechH0ScalarCocycle

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0ScalarCocycle`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectivePerfCechH0ScalarClass_of_cocycle` | 有限段のスカラー類の零次コサイクルは各標準開の実際の同じスカラーである。 |
| `projectivePerfCechH0ScalarClass_cocycle` | 任意の順極限のスカラー類のコサイクルは、各標準開への実際のスカラー写像。 |

## ProjectivePerfCechH0Square

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Square`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareTransferGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0_square_exact` | 射影中心の四角形の、F6 と同じ複体の Čech H⁰ における短完全性。 |

## ProjectivePerfCechH0SquareData

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareData`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0` | F6 の実際の標準開環の Frobenius 複体の Čech H⁰。 |
| `projectivePerfCechH0Equiv` | Čech H⁰ と切断の Frobenius 順極限の比較を、台の加法群の型を明示して読む。 |
| `projectivePerfCechH0CenterEquiv` | 中央項の Čech H⁰ と基底の中心の積を、切断環側の中央項と同定する。 |
| `projectivePerfCechH0Pair` | 基底の Frobenius 順極限から Čech H⁰ と基底の中心への二つの写像の組。 |
| `projectivePerfCechH0Difference` | 閉厚化の Čech H⁰ への差写像。 |

## ProjectivePerfCechH0SquareLaws

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareLaws`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareApplyGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0Difference_map_add` | H⁰ の差写像は加法を保つ。 |

## ProjectivePerfCechH0SquareMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareMaps`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareMapsGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0Difference_apply` | Čech H⁰ の差写像は、実際の閉厚化の制限と基底の中心からの写像の差。 |

## ProjectivePerfCechH0SquareZero

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0SquareZero`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechH0SquareLawsGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0Difference_map_zero` | H⁰ の差写像は零を保つ。 |

## ProjectivePerfCechScalarAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechScalarAugmentation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectivePerfCechScalarAugmentation` | 各標準開への実際のスカラー環準同型から作る零次の増大写像。 |
| `projectivePerfCechH0ScalarClass_augmentation` | H⁰ のスカラー類の零次コサイクルは実際の増大写像に一致する。 |
| `projectivePerfCechScalarAugmentation_cycle` | 実際の増大写像の像は零次コサイクルである。 |

## ProjectivePerfCechSquareAugmentationComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareAugmentationComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquareAugmentationComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0ToSquareCochains` | H⁰ と基底の中心の組を、実際の四角形の零次コチェインへ写す加法準同型。 |
| `projectivePerfCechH0Pair_cochains` | F7 の組の写像をコサイクルへ移すと、実際の基底の増大写像となる。 |
| `projectivePerfCechSquareAugmentation_cycle` | 実際の基底の増大写像の像は、中心の項を加えた複体のコサイクル。 |
| `projectivePerfCechSquareAugmentation_injective` | 実際の四角形の基底の増大写像は単射。 |

## ProjectivePerfCechSquareComplexData

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareComplexData`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquareComplexDataGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechCenterAugmentation_d` | 中心の増大写像は閉厚化の実際の Čech 複体の微分で零になる。 |
| `projectivePerfCechSquareSource` | 射影側の Čech 複体の零次項に、基底の中心の Frobenius 順極限を加える。 |
| `projectivePerfCechSquareDifferenceMap` | 実際の閉厚化への制限と中心からの増大写像の差の余鎖写像。 |
| `projectivePerfCechSquareAugmentation` | 基底から、射影側のスカラーコチェインと基底の中心の元の組への実際の増大写像。 |

## ProjectivePerfCechSquareH0Surjective

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareH0Surjective`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquareH0SurjectiveGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechSquareDifferenceMap_homology_zero_surjective` | F7 の全射性は、実際の差の余鎖写像の H⁰ の全射性を与える。 |

## ProjectivePerfCechSquareKernelComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareKernelComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquareKernelComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechH0Difference_kernel` | H⁰ の差写像を零次コサイクルへ移すと、実際の差の余鎖写像となる。 |

## ProjectivePerfCechSquareLowDegree

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquareLowDegree`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquareLowDegreeGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechSquareDifference_augmentation_zero` | 実際の差の余鎖写像と基底の増大写像の合成は零。 |
| `projectivePerfCechSquareAugmentation_exact` | F7 の短完全性を実際の増大写像と cone の最初の微分の完全性へ移す。 |

## ProjectivePerfCechSquarePositive

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfCechSquarePositive`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfCechSquarePositiveGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePerfCechSquareDifferenceMap_positive_homology_bijective` | 実際の差の射は正次数の Čech H に同型を誘導する。 |

## ProjectivePerfectAffineCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectAffineCechComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectivePerfectAffineCechHomologyIso` | F8 の固定した複体の Čech H と、任意の有限アフィン被覆の実際の Frobenius 係数での比較。 |

## ProjectivePerfectCartesianSquare

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfectCartesianSquareGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)` |
| `projectivePerfectCartesianAugmentedSquare` | F8 の四角形を、実際の Proj と Cartesian な閉厚化 の構造層の係数へ移したもの。 |
| `projectivePerfectCartesianTotalComplexIso` | F8 の実際の全複体と、native な構造層での全複体の同型。 |
| `projectivePerfectCartesianSquare_acyclic` | 実際の構造層の Frobenius 係数へ移した射影四角形の増大全複体は acyclic。 |
| `projectivePerfectCartesianAugmentedSquare_restriction` | 移送した四角形の制限の辺は、実際の構造層の引き戻しそのもの。 |

## ProjectivePerfectCartesianSquareEdges

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianSquareEdges`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfectCartesianEdgesGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)` |
| `projectivePerfectCartesianCenterAugmentation` | 実際の閉厚化の構造射のスカラーで定める、中心の零次コチェインへの増大写像。 |
| `projectivePerfectCartesianAugmentedSquare_center` | 四角形の中心側の辺は、実際の構造射から作った増大写像と同じ。 |
| `projectivePerfectCartesianAugmentedSquare_scalar_apply` | 四角形の基底側のスカラーは、実際の大域スカラーを制限した Frobenius の写像。 |

## ProjectivePerfectNativeCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechSectionRingIso` | 非空の標準開交叉の環の同型。 |
| `projectiveProjCechSectionRingIso_naturality` | 環の切断の同型は、2e の同じ非空交叉の制限と可換。 |
| `projectiveProjPresheaf_primeCast` | 基底の p の零化は、実際の Proj の全ての開集合の切断環で成り立つ。 |
| `projectivePerfectNativeCechCoefficientIso` | 非空交叉で、実際の環の Frobenius 順極限の係数を同定する。 |
| `projectivePerfectNativeCechCoefficientIso_naturality` | 非空交叉の同型は、Frobenius 順極限後も同じ実際の制限写像と可換。 |
| `projectivePerfectNativeCechComplexIso` | F8 の固定した複体と、実際の Proj の構造層の Frobenius 係数の Čech 複体の同型。 |
| `projectivePerfectNativeCechComplexIso_apply` | 複体の比較は各タプルで、同じ非空交叉の環の順極限の同型を適用する。 |

## ProjectivePerfectNativeCechMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechMaps`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechSectionRingIso_map` | 標準開交叉での環の同型は、実際の Proj の appLE に自然。 |
| `projectivePerfectChartMap` | 実際の斉次局所化の環の写像から作る、F8 の固定した係数図式の射。 |
| `projectivePerfectNativeCechMap` | Proj の実際のスキームの射から作る、Frobenius 後の標準開の複体の引き戻し。 |
| `projectivePerfectNativeCechMap_apply` | native な写像の各タプルは、実際の Proj の appLE の環の射の順極限。 |

## ProjectivePerfectNativeCechNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectivePerfectNativeCechCoefficientIso_map` | 非空交叉の係数の比較は、実際の環の射と可換。 |
| `projectivePerfectNativeCechComplexIso_naturality_apply` | 複体の比較の自然性を、固定した次数の各タプルで表す。 |
| `projectivePerfectNativeCechComplexIso_naturality` | 固定した斉次局所化の複体と native な構造層の比較は、実際の環の射に自然。 |

## ProjectivePerfectNativeScalar

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeScalar`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechSectionRingIso_scalar` | 標準開の切断環の比較は、基底環の実際のスカラーと整合する。 |
| `projectivePerfectNativeCechComplexIso_scalar` | native な零次コチェインの増大写像は、基底の実際のスカラーの Frobenius 順極限。 |

## ProjectivePerfectNativeSquare

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeSquare`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfectNativeSquareGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G)` |
| `projectivePerfectNativeAugmentedSquare` | F8 の四角形を、実際の Proj と次数付き商の Proj の構造層の係数へ移したもの。 |
| `projectivePerfectNativeTotalComplexIso` | F8 の実際の全複体と、native な構造層での全複体の同型。 |
| `projectivePerfectNativeSquare_acyclic` | 実際の構造層の Frobenius 係数へ移した射影四角形の増大全複体は acyclic。 |

## ProjectiveProjCechSectionAlgebraEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveProjCechSectionAlgebraEquiv`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjCechSectionAlgEquiv` | 非空の標準開の交叉上の、実際の構造層との代数同型。 |
| `projectiveProjCechSectionAlgEquiv_apply` | 代数同型の線形写像は、既存の Čech 複体の比較そのもの。 |
| `projectiveProjCechSectionAlgEquiv_naturality` | 非空交叉の代数同型は、実際の制限写像と可換。 |

## ProjectiveScalarLocalizationFraction

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveScalarLocalizationFraction`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveScalarLocalizationLinearEquiv_fraction` | 加群の局所化の分母 f^n を、環の局所化の分母 (algebraMap f)^n へ移す。 |

## ProjectiveSequentialComplexQuasiIso

モジュール：`SerrePositivity.AlgebraicGeometry.ProjectiveSequentialComplexQuasiIso`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveSequentialComplexMap_quasiIsoAt` | 各段で次数 q の H に同型を誘導する射は、自然数の順極限でもそうなる。 |
| `projectiveSequentialComplexMap_quasiIso` | 各有限段の quasi-isomorphism は、自然数の順極限でも quasi-isomorphism。 |

## ReesClosedCechIntBounds

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechIntBounds`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCechIntProjection_eventually_injective` | 元の Čech H が中心の冪で零化されれば、十分厚い閉厚化への射影は単射。 |
| `reesClosedCechIntTransition_eventually_lifts` | 十分厚い段からの遷移の像は、元の Čech H の実際の射影から持ち上がる。 |

## ReesClosedCechIntComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechIntComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveCechIntToModuleEquiv` | 元の Čech H の整数係数表示と、係数環上の表示の加法群同型。 |
| `reesClosedCechModuleToRingEquiv` | Rees の閉厚化表示から、実際の商環の Čech H への加法群同型。 |
| `reesClosedCechIntToRingEquiv` | 閉厚化の整数係数表示から、同じ商環の係数環上の Čech H への加法群同型。 |
| `reesClosedCechIntToModuleEquiv` | 閉厚化の整数係数 Čech H と、既存の Rees の閉厚化の Čech H の加法群同型。 |
| `reesClosedCechIntToModuleEquiv_compare` | Rees 表示へ戻して環の商の表示へ送ると、整数への係数制限比較になる。 |
| `reesClosedCechIntToModuleEquiv_projection` | 整数係数の射影は、比較を通すと 2e の Rees の実際の射影になる。 |
| `reesClosedCechIntToModuleEquiv_transition` | 整数係数の遷移も、比較を通すと 2e の Rees の実際の遷移になる。 |
| `reesClosedCechIntTransition_projection` | 閉厚化間の整数係数の遷移と元の対象からの射影の合成は、浅い段への射影。 |

## ReesClosedCechIntFrobeniusBounds

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechIntFrobeniusBounds`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCechIntProjection_frobenius` | 実際の閉厚化への Čech 射影は、同じ厚さでの反復 Frobenius と可換。 |
| `reesClosedCechIntProjection_kernel_eventually_zero` | 中心の冪で元の Čech H が零化されるなら、厚さ 1 の射影の核は反復 Frobenius で消える。 |
| `reesClosedCechIntProjection_frobenius_eventually_lifts` | 閉厚化の Čech H の各元の十分高い Frobenius 反復は、元の対象からの制限の像に入る。 |

## ReesClosedCechIntMaps

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechIntMaps`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ReesClosedCechIntHomology` | 実際の閉厚化の捻り零の Čech H の整数加群表示。 |
| `reesClosedCechIntProjection` | 実際の閉厚化への Čech H の射影を整数線形に読む。 |
| `reesClosedCechIntTransition` | 実際の閉厚化間の Čech H の遷移を整数線形に読む。 |
| `reesClosedCechIntThickening` | 実際の閉厚化を経由する Frobenius の Čech H の整数線形写像。 |
| `reesClosedCechIntThickening_factor` | Čech H で厚化から戻すと、既に構成した反復 Frobenius になる。 |
| `reesClosedCechIntThickening_projection` | Čech H への射影と、厚化を経由する反復 Frobenius は可換。 |

## ReesClosedCechIntThickening

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechIntThickening`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedCechIntThickeningDiagram` | 閉厚化を経由する Frobenius の捻り零の整数線形な図式の射。 |
| `reesClosedCechIntThickeningDiagram_factor` | 厚化から戻すと、同じ閉厚化の整数係数図式の反復 Frobenius になる。 |
| `reesClosedCechIntThickeningDiagram_projection` | 射影後の厚化 Frobenius は、元の図式の反復 Frobenius 後の射影。 |

## ReesClosedCechThickeningFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechThickeningFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedChartThickeningFrobeniusNatTrans` | 実際の標準開の厚化 Frobenius を、係数作用を制限した図式の射にする。 |
| `reesClosedCechThickeningFrobenius` | 実際の閉厚化の Čech H の、厚化を経由する反復 Frobenius。 |

## ReesClosedCechThickeningNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedCechThickeningNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedChartThickeningFrobeniusNatTrans_transition` | 厚化 Frobenius と遷移の四角形は実際の標準開図式で可換。 |
| `reesClosedCechThickeningFrobenius_transition` | 閉厚化の Čech H の厚化 Frobenius は厚さを下げる遷移と可換。 |

## ReesClosedChartThickeningFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedChartThickeningFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesThickeningIntGradedAction` | 型クラスの構成：`(J : Ideal A) : SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι` |
| `reesClosedChartThickeningFrobenius` | 厚化を経由する反復 Frobenius の、実際の標準開の指定次数部分の写像。 |
| `reesClosedChartThickeningFrobenius_val` | 指定次数の厚化 Frobenius は、周囲の実際の局所化の写像の制限。 |

## ReesClosedFrobeniusFunctor

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusFunctor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingProjectionChartMap_transition` | 環の商への射影は、閉厚化の厚さを下げる遷移と可換。 |
| `reesClosedCechIntProjectionDiagram_frobenius` | 閉厚化への実際の制限は、標準開の反復 Frobenius と可換。 |
| `reesClosedFrobeniusCoefficientNatTrans` | 実際の商への制限は Frobenius の係数系の自然変換を与える。 |

## ReesClosedFrobeniusRingCech

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingCech`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedFrobeniusRingChartMap` | 標準開の環の順極限の係数図式上の、閉厚化への実際の制限。 |
| `reesClosedFrobeniusRingChartMap_app` | 閉厚化の図式の射の各成分は、標準開の実際の環の射影が誘導する射。 |
| `reesClosedFrobeniusRingCechMap` | 同じ環の係数図式の制限が誘導する、Čech 複体の射。 |
| `reesClosedFrobeniusRingCechIso_projection` | Čech 複体の二つの表示の同型は、閉厚化への実際の射と可換。 |

## ReesClosedFrobeniusRingColimit

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingColimit`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedChartFrobeniusRingColimitIso_projection` | 各標準開で、係数順極限と環の順極限の比較は閉厚化への制限に自然。 |

## ReesClosedHomogeneousAlgebraProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousAlgebraProjection`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousAlgebraProjectionGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousModuleProjection` | 閉厚化への線形な係数の射を斉次局所化の図式に移したもの。 |
| `reesClosedHomogeneousModuleProjection_apply` | 移した線形写像の各成分は、実際の斉次局所化の環の射影。 |
| `reesHomogeneousAlgebraProjectionSourceAlgebra` | 型クラスの構成：`(f : A) : Algebra R (HomogeneousLocalization.Away G f)` |
| `reesHomogeneousAlgebraProjectionTargetAlgebra` | 型クラスの構成：`(n : ℕ) (f : A ⧸ (I ^ n).map (algebraMap R A)) : Algebra R (HomogeneousLocalization.Away (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) f)` |
| `reesClosedHomogeneousChartAlgProjection` | 閉厚化への斉次局所化の射影を、同じ線形写像を持つ代数写像にする。 |
| `reesClosedHomogeneousAlgebraProjection` | 閉厚化への実際の制限は、斉次標準開の代数図式の自然変換。 |

## ReesClosedHomogeneousProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousProjection`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedGradedRingProjection` | 閉厚化の構造環への実際の次数付き射影。 |
| `reesClosedHomogeneousChartProjection` | 各標準開で閉厚化への制限を与える、斉次局所化の実際の環準同型。 |
| `reesClosedHomogeneousChartProjection_compare` | 商への加群の制限は、同じ標準開の斉次局所化の環の射影に一致する。 |
| `reesClosedChartRingFrobeniusNatTrans` | 閉厚化への標準開環の射影が誘導する Frobenius 系の自然変換。 |
| `reesClosedChartFrobeniusRingSystemIso_projection` | 係数系と環の Frobenius 系の比較は、閉厚化への実際の射影に自然。 |

## ReesClosedHomogeneousSectionTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSectionTransition`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousSectionTransitionGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionTransition` | 閉厚化の間の実際の切断代数の遷移。 |
| `reesClosedHomogeneousSectionTransition_apply` | 切断代数の遷移の成分は、実際の標準開の環の遷移。 |
| `projectiveHomogeneousSectionNatH0Equiv_transition` | 切断代数の遷移は、元の次数付き加群の Čech H⁰ の遷移と可換。 |
| `reesClosedHomogeneousSectionH0Equiv_transition` | 切断代数の遷移は、像の安定化に用いた Rees の Čech H⁰ の遷移と可換。 |

## ReesClosedHomogeneousSections

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSections`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionAlgebra` | 斉次標準開の実際の環の適合する切断の部分代数。 |
| `projectiveHomogeneousSectionH0Equiv` | 斉次標準開の切断代数と Čech H⁰ の線形比較。 |
| `projectiveHomogeneousSectionAlgebra_finite` | 射影有限性から、斉次標準開の適合切断の部分代数は基底環上有限。 |
| `reesHomogeneousSectionsGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionProjection` | 閉厚化の斉次標準開の適合切断代数への実際の制限。 |
| `reesClosedHomogeneousSectionProjection_apply` | 切断代数の制限の各成分は、閉厚化への斉次局所化の環の射影。 |
| `reesClosedHomogeneousSectionH0Equiv_projection` | 切断環の実際の制限は、同じ係数写像から作る Čech H⁰ の写像と可換。 |

## ReesClosedHomogeneousTransition

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousTransition`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousTransitionGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedGradedRingTransition` | 閉厚化の間の実際の次数付き環の因子写像。 |
| `reesClosedHomogeneousChartTransition` | 閉厚化間の遷移が標準開の斉次局所化に誘導する環準同型。 |
| `reesClosedHomogeneousModuleTransition` | 閉厚化間の既存の線形な遷移を斉次局所化の図式に移した射。 |
| `reesClosedHomogeneousModuleTransition_apply` | 移した線形な遷移は、実際の斉次局所化の環準同型と一致する。 |
| `reesHomogeneousTransitionAlgebra` | 型クラスの構成：`(n : ℕ) (f : A ⧸ (I ^ n).map (algebraMap R A)) : Algebra R (HomogeneousLocalization.Away ((projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) f)` |
| `reesClosedHomogeneousChartAlgTransition` | 閉厚化間の斉次局所化の遷移を代数写像として扱う。 |
| `reesClosedHomogeneousAlgebraTransition` | 閉厚化の遷移は斉次標準開の代数図式の自然変換をなす。 |

## ReesClosedLocalizedThickeningFactor

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningFactor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `thickeningFraction` | 厚化の指数を変える Frobenius は局所化の分子・分母を同じ p 冪へ写す（private）。 |
| `reesClosedLocalizedThickeningFrobenius_factor` | 厚化を経由して元の厚さへ戻すと、実際の局所化環の p^e 乗になる。 |
| `reesClosedLocalizedThickeningFrobenius_projection` | 商への射影と厚化 Frobenius の合成は、元の局所化の p^e 乗の射影。 |

## ReesClosedLocalizedThickeningFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingThickeningFrobenius_algebraMap` | 厚化 Frobenius は、任意の係数環の元の像を p^e 乗に送る。 |
| `reesClosedLocalizedThickeningFrobenius` | 実際の閉厚化の標準開の局所化の間の反復 Frobenius。 |
| `reesClosedLocalizedThickeningFrobenius_fraction` | 厚化 Frobenius は分子を p^e 乗、分母の指数を p^e 倍に送る。 |

## ReesClosedLocalizedThickeningNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedLocalizedThickeningNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedLocalizedThickeningFrobenius_transition` | 厚さを下げる実際の線形局所化の射と、厚化 Frobenius は可換。 |

## ReesClosedNativeNonemptyDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedNativeNonemptyDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechNonemptyIndexFunctor` | 非空有限集合の部分圏から、全ての有限集合の圏への包含。 |
| `closedNativeNonemptyDiagramGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeNonemptyRingIso` | 非空交叉の環の係数図式と、実際の Cartesian な閉厚化の切断環の自然同型。 |

## ReesClosedNativeSectionComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedNativeSectionGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeSectionLinearEquiv` | 斉次局所化の商の係数と、実際の閉厚化の切断との R 線形同型。 |
| `reesClosedNativeSectionLinearEquiv_projection` | 線形同型は、斉次局所化の実際の射影を閉厚化の構造層の引き戻しへ送る。 |

## ReesClosedNativeSectionEvaluation

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionEvaluation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedNativeSectionEvaluationGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeSectionRingIso_hom_apply` | 環の同型の関数部分は、2e からの同じ係数の線形同型。 |
| `reesClosedNativeSectionRingIso_naturality_hom` | 閉厚化の環の比較と制限の可換性を、環の圏の等式として使う。 |

## ReesClosedNativeSectionNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedNativeSectionNaturalityGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeSectionLinearEquiv_naturality` | 商の斉次局所化から実際の切断への線形比較は、非空交叉の制限と可換。 |
| `reesClosedNativeSectionRingIso_naturality` | 同じ環の同型は、実際の閉厚化の切断環の制限と可換。 |

## ReesClosedNativeSectionRingIso

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionRingIso`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedNativeSectionRingGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousChartProjection_surjective` | 斉次局所化の実際の商への射影は全射。 |
| `reesClosedNativeSectionRingIso` | 係数の線形同型は、実際の切断の環の同型を与える。 |
| `reesClosedNativeSectionRingIso_projection` | 実際の環の同型は、斉次局所化の射影を同じ構造層の引き戻しへ送る。 |

## ReesClosedPerfectChartMap

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectChartMap`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectChartGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedGradedRingProjection_irrelevant` | 実際の次数付き商は irrelevant ideal の条件を満たし、Proj の射を定める。 |
| `reesClosedHomogeneousRingDiagramMap_eq` | 閉厚化の商の射は、環の係数図式の一般の写像と同じもの。 |
| `reesClosedPerfectChartMap_eq` | 一般の写像の構成は、F8 の実際の閉厚化の係数の制限を与える。 |

## ReesClosedPerfectNativeCenter

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCenter`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectNativeCenterGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeSectionRingIso_scalar` | 閉厚化の環の比較は、元の基底環の実際のスカラーに線形。 |

## ReesClosedPerfectNativeCenterAugmentation

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCenterAugmentation`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectNativeCenterAugGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedNativeSectionRingIso_center` | 中心の環の写像は、実際の閉厚化の構造射から得るスカラーに対応する。 |
| `reesClosedPerfectNativePushedCechIso_center` | 実際の中心の増大写像は、構造射のスカラーの Frobenius 順極限。 |

## ReesClosedPerfectNativeCoefficient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCoefficient`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectNativeCoefficientGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectivePullbackPresheaf_primeCast` | 元の基底の p の零化は、Proj に写るスキームの全ての切断環で成り立つ。 |
| `reesClosedPerfectNativeNonemptyIso` | 非空交叉の環の自然同型に Frobenius の関手を適用した自然同型。 |
| `reesClosedPerfectNativePushedCoefficientIso` | 非空交叉の環の同型が誘導する、実際の Frobenius 順極限の係数の同型。 |
| `reesClosedPerfectNativePushedCoefficientIso_naturality` | 実際の閉厚化の Frobenius 係数の比較は、非空交叉の制限に自然。 |
| `reesClosedPerfectNativePushedCechIso` | 固定した閉厚化の複体と、実際の閉厚化の切断を押し出した係数の複体の同型。 |
| `reesClosedPerfectNativePushedCechIso_apply` | 押し出した切断の複体への比較は、各タプルで同じ係数の同型を使う。 |
| `reesClosedPerfectNativeCechIso` | F8 の固定した閉厚化の複体と、実際の Cartesian な閉厚化の逆像被覆の複体の同型。 |

## ReesClosedPerfectNativeNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectNativeGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedPerfectNativeCechComplexIso_naturality` | 実際の閉厚化の余鎖写像は、native な Proj の実際の引き戻しと比較を介して一致。 |

## ReesClosedPerfectNativeProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeProjection`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `closedPerfectNativeProjectionGradedRing` | 型クラスの構成：`: GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedPerfectNativePushedCoefficientIso_projection` | 実際の閉厚化への係数の制限は、同じ構造層の引き戻しに対応する。 |
| `reesClosedPerfectNativePushedCechIso_naturality_apply` | 固定した次数の各タプルで、閉厚化の制限と比較が可換。 |
| `reesClosedPerfectNativePushedCechIso_naturality` | 押し出した切断の複体への比較は、実際の閉厚化の引き戻しに自然。 |
| `reesClosedPerfectNativeCechIso_naturality` | 実際の Cartesian な閉厚化の逆像被覆への比較は、実際の構造層の引き戻しに自然。 |

## ReesClosedRingGrading

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingGrading`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingLinearEquiv_map_piece` | Rees の商の次数成分を環の商への比較で送ると、元の商環の次数成分になる。 |
| `reesClosedRingGrade_isInternal` | 閉厚化の実際の環の次数成分も内部直和をなす。 |
| `reesClosedRingGradedRing` | 商環の積と、Rees から移した直和分解を合わせた次数付き環構造。 |

## ReesClosedRingThickeningFrobenius

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningFrobenius`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingThickeningFrobenius` | Rees の環の商表示の、厚さ n から p^e*n への Frobenius。 |
| `reesClosedRingThickeningFrobenius_mk` | 実際の商環の厚化 Frobenius は代表元の p^e 乗。 |
| `reesClosedRingThickeningFrobenius_projection` | 元の環から閉厚化への射影と、厚化を経由する反復 Frobenius の可換性。 |
| `reesClosedRingThickeningFrobenius_preservesPiece` | 厚化 Frobenius は、実際の商環の斉次次数を p^e 倍する。 |

## ReesClosedRingThickeningNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingThickeningFrobenius_factor` | 厚化から戻した写像は、Rees の実際の商環上の反復 Frobenius。 |
| `reesClosedRingThickeningFrobenius_transition` | 厚化 Frobenius は、実際の商環の厚さを下げる遷移と可換。 |

## ReesClosedRingThickeningSemilinear

モジュール：`SerrePositivity.AlgebraicGeometry.ReesClosedRingThickeningSemilinear`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesClosedRingThickeningFrobenius_scalar` | 閉厚化の反復 Frobenius は、係数の反復 Frobenius と可換。 |
| `reesClosedRingThickeningFrobeniusSemilinear` | 実際の閉厚化の間の、反復 Frobenius に関する半線形写像。 |
| `reesClosedRingThickeningFrobeniusSemilinear_apply` | 半線形写像の値は、元の商環の写像そのもの。 |

## ReesHomogeneousFrobeniusCoefficientComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousFrobeniusCoefficientComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousFrobeniusCoefficientComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousFrobeniusCoefficientIso_projection` | 閉厚化への実際の射影は、多項式加群と斉次標準開の Frobenius 系の比較と可換。 |
| `projectiveHomogeneousFrobeniusCoefficientColimitIso_projection` | 同じ閉厚化の可換性を係数図式の順極限へ送る。 |

## ReesHomogeneousFrobeniusH0Comparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousFrobeniusH0Comparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousFrobeniusH0ComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousFrobeniusRingCechIso_projection` | 標準開環の複体と斉次代数係数の複体の比較は、閉厚化の実際の射と可換。 |
| `projectiveHomogeneousFrobeniusRingCechH0Iso_projection` | 閉厚化の Čech H⁰ の射は、切断の実際の制限が誘導する Frobenius 順極限の射。 |

## ReesHomogeneousSectionFrobeniusComparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionFrobeniusComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionAlgebra_primeCast` | 基底環で p が零なら、斉次標準開の切断代数でも p は零。 |
| `reesSectionFrobeniusComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionQuotientMap_kernel_nil` | 切断代数の商から閉厚化への比較写像の核は nil。 |
| `reesClosedHomogeneousSectionQuotientMap_power_lifts` | 閉厚化の任意の切断のある Frobenius 冪は、切断代数の商からの比較写像の像に入る。 |
| `reesClosedHomogeneousSectionQuotientMap_frobenius_bijective` | 実際の切断代数の商から閉厚化への比較写像は Frobenius 順極限上で全単射。 |

## ReesHomogeneousSectionH0Comparison

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionH0Comparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `projectiveHomogeneousSectionNatH0Equiv` | 切断代数を、元の次数付き加群で計算した Čech H⁰ と比較する。 |
| `reesSectionComparisonGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `projectiveHomogeneousSectionNatH0Equiv_projection` | 切断代数と次数付き加群の H⁰ の比較は、閉厚化への実際の制限と可換。 |
| `reesClosedHomogeneousSectionH0Equiv` | 閉厚化の切断代数を、Rees の商加群の Čech H⁰ と比較する。 |
| `reesClosedHomogeneousSectionH0Equiv_reesProjection` | Rees の商との比較は、切断代数の制限を元の閉厚化への H⁰ の射へ送る。 |

## ReesHomogeneousSectionImageStabilization

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionImageStabilization`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesSectionImageGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionTransition_range_stabilizes` | 閉厚化の切断代数の遷移の像は、一様に遅らせれば元の切断代数の制限の像に等しい。 |

## ReesHomogeneousSectionKernelBound

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionKernelBound`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesSectionKernelGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionProjection_eq_zero_iff` | 切断環の実際の制限の核は、Rees 側の Čech H⁰ の射の核に対応する。 |
| `reesClosedHomogeneousSectionProjection_kernel_bound` | 閉厚化への切断代数の制限の核の一様な I 進評価。 |
| `reesClosedHomogeneousSectionProjection_kernel_ideal_bound` | 十分厚い閉厚化への制限で消える切断は、基底の指定冪の拡大イデアルに入る。 |

## ReesHomogeneousSectionKernelPower

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionKernelPower`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesSectionKernelPowerGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionProjection_kernel_power` | 制限の核の一様な Frobenius 冪は、基底イデアルの拡大に入る。 |

## ReesHomogeneousSectionPowerLift

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionPowerLift`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesSectionPowerLiftGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionProjection_power_lifts` | 閉厚化の任意の切断の一様に高い Frobenius 冪は、元の切断の制限に持ち上がる。 |

## ReesHomogeneousSectionQuotient

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousSectionQuotient`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `homogeneousSectionQuotientAwayAlgebra` | 型クラスの構成：`(f : A) : Algebra R (HomogeneousLocalization.Away G f)` |
| `projectiveHomogeneousAway_scalar_eq_zero` | 構造環で零になる基底スカラーは斉次局所化でも零になる。 |
| `projectiveHomogeneousSectionAlgebra_scalar_eq_zero` | 構造環で零になる基底スカラーは適合切断代数でも零になる。 |
| `reesSectionQuotientGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesClosedHomogeneousSectionProjection_ideal_le_ker` | 閉厚化への制限は、基底の I^n を切断代数へ拡大したイデアルを消す。 |
| `reesClosedHomogeneousSectionQuotientMap` | 切断代数の商から、実際の閉厚化の切断代数への環準同型。 |
| `reesClosedHomogeneousSectionQuotientMap_mk` | 商からの比較写像は、代表元上で元の切断の制限に一致する。 |

## ReesHomogeneousThickeningDiagram

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousThickeningDiagram`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesHomogeneousThickeningGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesHomogeneousThickeningDiagram` | 厚化を経由する Frobenius の、実際の斉次標準開の整数加群図式の射。 |
| `reesHomogeneousThickeningDiagram_apply` | 厚化の図式の各成分は、既存の整数線形写像を標準開の比較で移したもの。 |
| `reesHomogeneousThickeningDiagram_factor` | 厚化への加法写像を元の厚さへ戻すと、標準開の環の実際の p^e 乗になる。 |
| `reesHomogeneousSectionThickening` | 厚化を経由する Frobenius が適合切断の加法群に誘導する写像。 |
| `reesHomogeneousSectionThickening_apply` | 切断の厚化写像の各成分は整数線形な標準開の写像。 |
| `reesHomogeneousSectionThickening_factor` | 切断の厚化 Frobenius を制限で戻すと、実際の切断環の p^e 乗になる。 |

## ReesHomogeneousThickeningProjection

モジュール：`SerrePositivity.AlgebraicGeometry.ReesHomogeneousThickeningProjection`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `reesThickeningProjectionGradedRing` | 型クラスの構成：`(n : ℕ) : GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)` |
| `reesHomogeneousThickeningDiagram_projection` | 元の標準開から射影した後の厚化写像は、冪乗した後の厚い閉厚化への射影。 |
| `reesHomogeneousSectionThickening_projection` | 射影後の切断の厚化 Frobenius は、元の切断の冪乗後の射影に一致する。 |

## RingDirectLimitIntColimit

モジュール：`SerrePositivity.AlgebraicGeometry.RingDirectLimitIntColimit`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ringDirectSystemIntMap` | 環の有向系の実際の射を整数線形写像として読む。 |
| `ringDirectSystemIntMap_directedSystem` | 整数線形表示でも同じ有向系の法則が成り立つ。 |
| `ringDirectLimitIntColimitIso` | 環の順極限の加法群と、同じ整数加群の有向系の余極限との同型。 |
| `ringDirectLimitIntColimitIso_of` | 比較同型は有限段からの環の標準写像を、同じ余極限の標準写像へ送る。 |

## RingDirectLimitIntNaturality

モジュール：`SerrePositivity.AlgebraicGeometry.RingDirectLimitIntNaturality`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `ringDirectLimitComparison` | 可換な環の射の系から誘導する、実際の環の順極限の射。 |
| `ringDirectLimitComparison_of` | 環の順極限の射は各有限段で指定した環の射に一致する。 |
| `ringDirectLimitIntColimitIso_naturality` | 環の順極限と整数加群の余極限の比較は、有向系の環の射に自然。 |

## SchemeAlgebraCechTensorDifferential

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorDifferential`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `fullCechComplex_d_zero` | 実際の通常の Čech 複体の最初の微分は指定したコチェイン微分（private）。 |
| `schemeAlgebraCechTensorTermEquiv_differential` | 実際の各項の底変換同型は、最初の余境界と可換。 |
| `schemeAlgebraCechTensorEquiv` | 実際の flat な底変換と、適合する切断部分代数の線形比較。 |

## SchemeAlgebraCechTensorScalar

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorScalar`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureCechBaseChangeDiagramRestriction_one` | 実際の底変換の切断の引き戻しは 1 を保つ。 |
| `schemeAlgebraCechTensorEquiv_one` | 実際の flat な切断部分代数の比較は 1 ⊗ 1 を 1 に送る。 |
| `schemeAlgebraCechTensorEquiv_scalar` | 実際の flat な切断部分代数の比較は基底環のスカラー写像と可換。 |

## SchemeAlgebraCechTensorTerms

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeAlgebraCechTensorTerms`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeAlgebraCechTensorTermEquiv` | 実際の底変換の代数係数の各 Čech 項と、通常のテンソル積の比較。 |

## SchemeCechCompatibleSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechCompatibleSections`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCechSingletonSectionsEquiv_face_zero` | 長さ二の第零面は、第二の開集合から二重点への制限。 |
| `schemeCechSingletonSectionsEquiv_face_one` | 長さ二の第一面は、第一の開集合から二重点への制限。 |
| `schemeCechSingletonSectionsEquiv_mem_iff` | 二つの面の equalizer 条件は、層の二重点での適合条件と一致する。 |
| `schemeCechCompatibleSectionsEquiv` | Čech H⁰ に用いる適合切断の部分代数と、層の適合切断の部分環との環の同型。 |

## SchemeCechGlobalSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechGlobalSections`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCechGlobalSectionsEquiv` | 実際の Čech の適合切断の環と、大域切断の環の同型。 |
| `schemeCechGlobalSectionsEquiv_restrict` | 貼り合わせた大域切断の各開集合への制限は、指定された局所切断。 |
| `schemeCechGlobalSectionsEquiv_symm_apply` | 大域切断から Čech の切断族への逆写像は、元の構造層の実際の制限。 |
| `schemeCechGlobalSectionsEquiv_symm_algebraMap` | 貼り合わせの同型の逆は、指定した大域スカラーを元の部分代数のスカラーへ送る。 |
| `schemeCechGlobalSectionsAlgEquiv` | 貼り合わせの環の同型は、指定された基底環上の代数同型でもある。 |

## SchemeCechScalarTensorSurjective

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechScalarTensorSurjective`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCechScalarTensor_surjective` | 構造射が同型になる flat 底変換では、元のスカラー写像のテンソル化は全射。 |

## SchemeCechSectionSpectrum

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechSectionSpectrum`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeToCechSectionSpectrum` | 元のスキームから Čech の適合切断環の Spec への標準射。 |
| `schemeToCechSectionSpectrum_comp` | この標準射と基底スカラーの Spec を合成すると、元の構造射になる。 |
| `schemeCechSectionAlgebra_surjectiveSpectrum` | 構造射が全射なら、基底環から Čech の適合切断環への射は Spec 上で全射。 |

## SchemeCechSingletonSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCechSingletonSections`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `cechOpenIntersection_tuple` | タプルの台による有限交叉は、タプルの各位置での交叉に一致する。 |
| `cechOpenIntersection_tuple_one` | 長さ一のタプルの交叉は、その一つの開集合。 |
| `cechOpenIntersection_tuple_two` | 長さ二のタプルの交叉は、その二つの開集合の交叉。 |
| `schemeCechSingletonSectionsEquiv` | 長さ一の Čech 切断族と、元の被覆上の切断族との環の同型。 |
| `schemeCechSingletonSectionsEquiv_recover` | 元のタプルの切断は、被覆上の切断を長さ一の交叉へ制限して戻せる。 |

## SchemeCompatibleSections

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeCompatibleSections`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeCompatibleSections` | 二重点で一致する切断族の部分環。 |
| `schemeGlobalToCompatibleSections` | 大域切断を各開集合へ制限する環準同型。 |
| `schemeGlobalToCompatibleSections_apply` | 実際の制限準同型の各成分は、構造層の制限そのもの。 |
| `schemeGlobalToCompatibleSections_bijective` | 被覆上の適合する切断は、大域切断から一意に得られる。 |
| `schemeGlobalCompatibleSectionsEquiv` | 一般の開被覆の適合する切断の環と大域切断の環の同型。 |

## SchemeSectionAlgebraCech

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeSectionAlgebra` | 基底環からのスカラーを大域切断経由で開集合に制限した代数構造。 |
| `schemeSectionAlgebraPresheaf` | 実際の構造層を基底環上の代数の前層として扱う。 |
| `schemeSectionAlgebraCechDiagram` | 開被覆の有限交叉上の、実際の切断代数の図式。 |
| `schemeSectionAlgebraCechModuleIso` | 切断代数から忘却した図式と、既存の構造層加群の Čech 図式の比較。 |
| `schemeSectionAlgebraCechH0Equiv` | 実際の切断の部分代数と、構造層の Čech H⁰ の線形同型。 |

## SchemeStructureIntCechRefinement

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructureIntCechRefinement`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `openCoverCechIntRestriction_refinement_quasiIsoAt` | 整数への係数制限は、実際の細分写像の Čech H の同型性を保つ。 |
| `schemeStructureFrobeniusStageIso` | 構造層の実際の環の Frobenius 系の各段は、構造層の整数係数前層と同型。 |
| `schemeStructureFrobeniusCechRefinement_quasiIsoAt` | 構造層の実際の環の Frobenius 順極限後、有限アフィン細分は Čech H の同型。 |

## SchemeStructurePerfectAffineCechPullback

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectAffineCechPullback`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `perfectAffineRefinementIsIso` | 2e のアフィン比較から供給した、Frobenius 後の実際の細分射の同型性。 |
| `schemeStructurePerfectAffineCechPullback_comparison_naturality` | Frobenius 順極限後のアフィン射の実際の引き戻しは、共通アフィン細分の比較と可換。 |

## SchemeStructurePerfectCechComparison

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechComparison`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeStructurePerfectCommonAffineCechHomologyIso` | 実際の構造層の Frobenius 順極限についての、二つの有限アフィン被覆の Čech H の比較。 |

## SchemeStructurePerfectCechPullback

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeStructureRingPullbackCoefficient` | スキームの射による実際の切断環の引き戻しの自然変換。 |
| `schemeStructurePerfectPullbackCoefficient` | 実際の切断環の引き戻しに同じ Frobenius 順極限を適用する。 |
| `schemeStructurePerfectCechPullbackMap` | 実際の構造層の Frobenius 順極限の Čech 複体の引き戻し。 |
| `schemeStructurePerfectCechPullbackMap_refinement` | 引き戻しは Frobenius 順極限後も同じ細分写像と可換。 |

## SchemeStructurePerfectCechRefinedPullback

モジュール：`SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `schemeStructurePerfectCechRefinedPullbackMap` | 逆像への実際の引き戻しと細分の合成。 |
| `schemeStructurePerfectCechRefinedPullbackMap_apply` | 各タプルの写像は、実際の appLE の環準同型の Frobenius 順極限。 |

## SquareLiftTransport

モジュール：`SerrePositivity.AlgebraicGeometry.SquareLiftTransport`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `squareLift_transport` | 共通対象からの単射・全射と右下の単射を通じて、四角形の持ち上げを移す。 |

## SupportFromLocalizedTensor

モジュール：`SerrePositivity.AlgebraicGeometry.SupportFromLocalizedTensor`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `support_subset_of_localizedTensor_subsingleton` | 中心外の各素点でテンソル積が零なら、加群の台は中心内。 |
| `finiteLocalizedTensor_exists_pow_le_annihilator` | 有限加群が中心外の局所化テンソル積で消えれば、中心のある冪が加群を消す。 |

## SurjectiveSpectrumRadical

モジュール：`SerrePositivity.AlgebraicGeometry.SurjectiveSpectrumRadical`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `surjectiveSpectrum_comap_radical_map` | Spec 上全射なら、拡大イデアルの根基の逆像は元のイデアルの根基。 |
| `surjectiveSpectrum_radical_comap_map` | Spec 上全射なら、拡大して戻したイデアルの根基は変わらない。 |

## TensorCokernelVanishing

モジュール：`SerrePositivity.AlgebraicGeometry.TensorCokernelVanishing`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `tensorCokernel_subsingleton_of_surjective` | 写像のテンソル化が全射なら、実際の余核のテンソル積は零。 |
| `cokernel_support_subset_of_localizedTensor_surjective` | 中心外の局所化テンソル積で写像が全射なら、その余核の台は中心内。 |

## TensorExtendScalarsEquiv

モジュール：`SerrePositivity.AlgebraicGeometry.TensorExtendScalarsEquiv`

入口の直接 import 登録：済。

| 宣言 | 主張 |
| --- | --- |
| `tensorExtendScalarTower` | 型クラスの構成：`: IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A))` |
| `tensorExtendScalarsEquiv` | 通常の代数のテンソル積と、圏論的なスカラー拡大の比較。 |
| `tensorExtendScalarsEquiv_tmul` | 比較は純テンソルの二つの因子を保つ。 |
