# DG-W3 統合先の命名案

基点 e14680ad0、計画 main 40ec57e06 §11.1。48 統合先のうち番号付き 9 件を主題で改名する案。対応表の土台 48 群を元に、新しい草案の module に反映した。名前は SerrePositivity.DifferentialGraded. からの相対名。

| 対応表の仮名 | 本名案 | 主題 |
| --- | --- | --- |
| `Derived.BimoduleComposition1` | `Derived.BimoduleComposition.Coherence` | 指定 K-flat 代表の結合比較、三角・五角 coherence とパラメータ族 |
| `Derived.BimoduleComposition2` | `Derived.BimoduleComposition.Resolution` | 導来合成の解像度計算、両単位と結合比較 |
| `Complexes.Perturbation` | `Complexes.Perturbation` | 既存の主題名を維持 |
| `Complexes.TensorCoproduct` | `Complexes.TensorCoproduct` | 既存の主題名を維持 |
| `Complexes.TensorZeroCochain` | `Complexes.TensorZeroCochain` | 既存の主題名を維持 |
| `Complexes.TensorShift` | `Complexes.TensorShift` | 既存の主題名を維持 |
| `Complexes.TensorJoin` | `Complexes.TensorJoin` | 既存の主題名を維持 |
| `Complexes.MaurerCartanCurrying` | `Complexes.MaurerCartanCurrying` | 既存の主題名を維持 |
| `Complexes.HomComplex` | `Complexes.HomComplex` | 既存の主題名を維持 |
| `Complexes.HomLimits` | `Complexes.HomLimits` | 既存の主題名を維持 |
| `Category.Basic` | `Category.Basic` | 既存の主題名を維持 |
| `Functor.QuasiEquivalence` | `Functor.QuasiEquivalence` | 既存の主題名を維持 |
| `Category.Tensor` | `Category.Tensor` | 既存の主題名を維持 |
| `Functor.Closed` | `Functor.Closed` | 既存の主題名を維持 |
| `Module.Basic` | `Module.Basic` | 既存の主題名を維持 |
| `Module.Left2` | `Module.Left.CategoryComparison` | 左加群圏・一対象環の比較と全次数自然性 |
| `Module.Hom1` | `Module.Hom.HomotopyAndOperations` | Hom end のホモトピーと零・自由・cone・shift・直和および射の操作 |
| `Module.Hom2` | `Module.Hom.ConeComparison` | cone・cylinder と全次数 Hom の比較、前後合成 |
| `Module.Hom3` | `Module.Hom.ColimitsAndRightHom` | 余極限・制限の Hom 比較と右 Hom 加群 |
| `Module.ConeConstruction` | `Module.ConeConstruction` | 既存の主題名を維持 |
| `Module.Graded` | `Module.Graded` | 既存の主題名を維持 |
| `Module.ActionLimits` | `Module.ActionLimits` | 既存の主題名を維持 |
| `Module.TensorFree` | `Module.TensorFree` | 既存の主題名を維持 |
| `Module.Disk` | `Module.Disk` | 既存の主題名を維持 |
| `Module.ShiftResolution` | `Module.ShiftResolution` | 既存の主題名を維持 |
| `Module.ConeRotation` | `Module.ConeRotation` | 既存の主題名を維持 |
| `Module.MaurerCartanTriangulated` | `Module.MaurerCartanTriangulated` | 既存の主題名を維持 |
| `Derived.Projective` | `Derived.Projective` | 既存の主題名を維持 |
| `Derived.ScalarExtension` | `Derived.ScalarExtension` | 既存の主題名を維持 |
| `Complexes.Cone` | `Complexes.Cone` | 既存の主題名を維持 |
| `Functor.ModuleValued` | `Functor.ModuleValued` | 既存の主題名を維持 |
| `Functor.ModuleShift` | `Functor.ModuleShift` | 既存の主題名を維持 |
| `Derived.Tensor` | `Derived.Tensor` | 既存の主題名を維持 |
| `Derived.BimoduleTensor` | `Derived.BimoduleTensor` | 既存の主題名を維持 |
| `Derived.Basic` | `Derived.Basic` | 既存の主題名を維持 |
| `Derived.KFlat` | `Derived.KFlat` | 既存の主題名を維持 |
| `Derived.BimoduleMiddle1` | `Derived.BimoduleMiddle.ModelIndependence` | 中間圏比較のモデル計算、解像度独立性と自然な族 |
| `Derived.BimoduleMiddle2` | `Derived.BimoduleMiddle.IteratedModels` | 導来制限の shift・三角性と二段階制限のモデル計算 |
| `Derived.BimoduleMiddle3` | `Derived.BimoduleMiddle.FunctorCoherence` | 中間圏制限の準同値、恒等・合成と反復比較の整合性 |
| `Derived.Functor` | `Derived.Functor` | 既存の主題名を維持 |
| `Module.FreeSphere` | `Module.FreeSphere` | 既存の主題名を維持 |
| `Module.Functor` | `Module.Functor` | 既存の主題名を維持 |
| `Derived.FunctorExtensionAdjunction` | `Derived.FunctorExtensionAdjunction` | 既存の主題名を維持 |
| `Derived.Bimodule` | `Derived.Bimodule` | 既存の主題名を維持 |
| `Derived.LeftUnit` | `Derived.LeftUnit` | 既存の主題名を維持 |
| `Derived.AssociatorLeft` | `Derived.AssociatorLeft` | 既存の主題名を維持 |
| `Derived.AssociatorMiddle` | `Derived.AssociatorMiddle` | 既存の主題名を維持 |
| `Derived.Paired` | `Derived.Paired` | 既存の主題名を維持 |

## 番号付きの群の根拠

### Derived.BimoduleComposition1 → Derived.BimoduleComposition.Coherence

指定 K-flat 代表の結合比較、三角・五角 coherence とパラメータ族。

- `CompositionFamilies` dg合成の自然性に使用するパラメータ付き関手合成
- `BimoduleCompositionAssociatorIndependence` 全導来結合同型の任意解像度計算と選択独立性
- `BimoduleCompositionAssociatorKFlat` 全導来結合同型と既存K-flat結合同型の比較図式
- `BimoduleCompositionAssociatorComponents` 全導来結合同型の成分と二つの後因子に関する同時自然性
- `BimoduleCompositionAssociatorComparison` 導来同型で指定されたK-flat代表と結合同型の比較
- `BimoduleCompositionTriangle` 全導来合成の三角恒等式のK-flat因子での比較
- `BimoduleCompositionTriangleFamily` 三角恒等式の両経路を束ねる全導来自然変換
- `BimoduleCompositionPentagonPaths` 全導来bimodule合成の五角図式の両経路
- `BimoduleCompositionPentagonInner` 五角図式の内側の結合射とK-flat三因子の値比較
- `BimoduleCompositionPentagonComparison` 全導来五角図式の始域と両終域のK-flat比較
- `BimoduleCompositionPentagonShort` 全導来五角図式の短経路のK-flat比較
- `BimoduleCompositionPentagonKFlat` 全導来五角図式の長経路とK-flat三因子の比較
- `BimoduleCompositionFamilies` 任意のパラメータ圏上の導来bimodule合成と結合比較
- `BimoduleCompositionPentagonFamilies` 五角の両経路の任意のパラメータ族に関する自然性
- `BimoduleCompositionPentagon` 全導来bimodule因子上の五角恒等式

### Derived.BimoduleComposition2 → Derived.BimoduleComposition.Resolution

導来合成の解像度計算、両単位と結合比較。

- `BimoduleRestriction` 両dg圏の関手に沿う導来bimodule制限
- `BimoduleRestrictionEvaluation` 両側制限とbimodule値評価の自然比較
- `BimoduleComposition` 両変数の全導来bimodule圏上の合成とK-flat因子での計算
- `BimoduleCompositionResolution` 全導来合成の解像度計算同型と増大射・比較squareの整合性
- `BimoduleCompositionResolutionValues` 指定解像度による導来合成の値の計算と増大squareの整合性
- `BimoduleCompositionRightUnit` 全後因子上の導来bimodule合成の右単位自然同型
- `BimoduleCompositionLeftUnit` 全導来bimodule合成の左単位と解像度に関する自然性
- `BimoduleCompositionLeftUnitComputation` 左単位のK-flat因子での計算と任意解像度による表示
- `BimoduleCompositionPairResolution` 全導来合成の二因子を指定K-flat解像度で計算する比較
- `BimoduleCompositionPairNaturality` 二つの解像度比較squareに関する逐次導来合成の自然性
- `BimoduleCompositionValueNaturality` 導来合成の値の指定解像度計算と後因子の射の整合性
- `BimoduleCompositionInnerNaturality` 合成された後因子の解像度比較の自然性
- `BimoduleCompositionAssociatorResolution` 指定K-flat解像度による全導来合成の結合比較
- `BimoduleCompositionAssociatorNaturality` 解像度比較に関する全導来結合比較の自然性
- `BimoduleCompositionAssociatorFunctors` 全導来結合比較の両辺を束ねる関手族
- `BimoduleCompositionAssociator` 全三因子に自然な導来bimodule合成の結合自然同型
- `BimoduleResolutionLift` 標準bimodule解像度から任意の準同型への持ち上げ

### Module.Left2 → Module.Left.CategoryComparison

左加群圏・一対象環の比較と全次数自然性。

- `Category` Hom end による右 dg 加群圏の豊穣構造
- `Ring` 一対象 dg 環 A の右加群と非有界複体
- `RingDGComparison` 一対象環Aの右dg加群と主dg複体圏の実際のdg比較
- `RingHomotopyComparison` 一対象Aとのdg比較が誘導する実際のH⁰同値
- `LeftRing` 一対象環A上の左dg加群
- `LeftCategory` 全Hom endを持つ左dg加群圏
- `LeftHomElements` 左加群の主Hom endの全次数自然性
- `LeftEquivalence` 左加群閉零圏とopposite上の右加群閉零圏の同値
- `LeftParamNaturality` 左加群の全次数パラメータ付き自然性の評価

### Module.Hom1 → Module.Hom.HomotopyAndOperations

Hom end のホモトピーと零・自由・cone・shift・直和および射の操作。

- `Homotopy` 全次数 Hom end の境界による加群ホモトピーと K(D)
- `QuasiIso` 右 dg 加群の objectwise 準同型
- `Underlying` dg 加群の underlying family
- `ClosedMaps` 全次数自然な chain map 族から閉零加群射を構成する
- `Zero` 全次数の零加群と閉零加群圏の零対象
- `Free` 自由右 dg 加群の関手性
- `Cone` 全次数作用を持つ右 dg 加群の cone 対象
- `ConeDesc` 合成が零となる加群射の全dg自然なcone延長
- `Shift` 右 dg 加群の整数 shift と objectwise 評価
- `LeftZero` 左dg加群圏の零対象と評価による零性の保存
- `LeftQuasiIso` 左dg加群の指定objectwise quasiIso
- `LeftQuasiIsoInverse` 左右加群同値の逆関手による指定準同型クラスの保存・反映
- `Biproduct` objectwise 二項直和の全次数作用と普遍性
- `HomFunctor` 主 dg 加群 Hom end の通常射に対する関手性の成分公式
- `HomWhisker` 元の加群型の全Homに値を持つ通常射の前後合成
- `HomIsoSquare` 可逆な加群射による全Hom可換四角形の逆向き
- `HomSquareComposition` 全Hom可換四角形の恒等と合成
- `HomElementComposition` 主Hom endの斉次合成と通常射による制限の成分

### Module.Hom2 → Module.Hom.ConeComparison

cone・cylinder と全次数 Hom の比較、前後合成。

- `ConeMaps` cone の connecting map と objectwise triangle
- `ConeFunctor` 可換 square の cone 射と関手性
- `ConeGradedSplit` cone付加の全次数作用に関する分裂
- `ConeElements` coneの包含・射影を主Hom endの斉次要素として構成
- `ConeTransportIso` 概要：両端の閉同型を持つ可換四角形から、実 cone の同型を得る。
- `Cylinder` 全 dg 自然な加群 cylinder とホモトピーの延長
- `Precomposition` 前合成の全次数転置と全dg自然なホモトピーの像
- `Postcomposition` 全次数の後合成をHom複体間のcochainへ転置する
- `HomCone` 主Hom endと標準coneの比較射
- `HomConeIso` 主Hom endはconeを複体のconeへ同型に送る
- `HomCycles` 主Hom endの閉次数零要素と加群射の合成
- `HomClosedInsertion` 概要：斉次合成の中間の閉零加群射を、前の Hom の後合成と後の Hom の制限の間で移す。
- `HomRestrictionComposition` 概要：閉零加群射による全次数 Hom の制限は通常順の斉次合成と可換。
- `HomPostcompositionComposition` 概要：全次数の加群 Hom の斉次合成は、閉零射による後合成と両立する。

### Module.Hom3 → Module.Hom.ColimitsAndRightHom

余極限・制限の Hom 比較と右 Hom 加群。

- `EvaluationReflects` 評価による主dg加群圏の同型・余極限の反映
- `TensorSource` 固定複体とのtensorの加群変数での関手性と余極限保存
- `ParamCurry` パラメータ付きHom endの転置と加群変数の自然性
- `ColimitHom` 余極限を源とする主Hom endの極限表示
- `CoproductHom` 余積を源とする全次数Hom endの直積表示
- `RestrictionTensor` 制限とtensor、およびtensor加群の括弧変更
- `RestrictionColimits` dg加群の制限は対象ごとの余極限を保つ
- `RestrictionCoherence` dg加群制限の恒等・合成比較
- `RestrictionGradedSplit` dg加群の制限は全斉次作用に関する分裂を保つ
- `HomotopyCoproduct` 余積からの加群ホモトピーの成分判定
- `HomotopyCoproductUniversal` K(D)のu-small余積と商関手による余積の保存
- `HomRight` 左dg加群から固定終域への右Hom加群
- `HomRightContra` 右Hom加群の左加群変数に関する反変Hom作用
- `HomRightContraMaps` 左加群変数の反変Hom写像と閉零射の比較
- `HomRightFunctor` 右Hom加群の終域変数の関手性
- `HomRightEnriched` 右Hom加群の終域変数のdg関手性

### Derived.BimoduleMiddle1 → Derived.BimoduleMiddle.ModelIndependence

中間圏比較のモデル計算、解像度独立性と自然な族。

- `BimoduleResolutionLiftTensor` 任意の準同型への標準解像度の持ち上げと相対tensor後の増大square
- `BimoduleMiddleComparison` 中間圏の制限後に解像度を取る導来bimodule合成比較
- `BimoduleMiddleHomotopy` ホモトピー可換な増大squareに対する中間圏比較の計算射の整合性
- `BimoduleMiddleNaturality` 解像度の増大squareに沿う中間圏比較の自然性
- `BimoduleMiddleCalculation` 実際の導来中間比較から通常のモデル計算射を回復する
- `BimoduleMiddleComparisonFamily` 指定解像度による導来中間圏比較の前因子に関する自然変換
- `BimoduleMiddleComparisonLocalization` 中間圏の導来合成比較を前因子の全導来圏へ降ろす
- `BimoduleMiddleIndependence` 中間圏の導来比較射の解像度変更に関する整合性
- `BimoduleMiddleSecondFactor` 増大squareから導く中間圏導来比較の後因子自然性
- `BimoduleMiddleKFlatIndependence` 任意の右相対K-flat解像度による中間比較と既存標準比較の一致
- `BimoduleMiddleSemifreeIndependence` 制限後に選ぶsemifree解像度からの中間圏導来比較の独立性
- `BimoduleMiddleSemifreeSecondFactor` 指定semifree解像度と標準解像度による中間圏導来比較の後因子自然性
- `BimoduleMiddleSecondFamily` 中間圏の標準導来比較の後因子自然性を自然変換の等式へ束ねる
- `BimoduleMiddleKFlatFamily` 中間圏比較のsource関手族と右K-flat後因子の準同型局所化への準備
- `BimoduleMiddleFullComparison` 両因子の全導来bimodule圏上の中間dg圏比較自然変換
- `BimoduleModuleEquivalence` 積dg圏上の右加群とbimoduleの主導来圏の比較

### Derived.BimoduleMiddle2 → Derived.BimoduleMiddle.IteratedModels

導来制限の shift・三角性と二段階制限のモデル計算。

- `RestrictionShift` 導来制限の全Homモデルと整合的整数shift
- `RestrictionTriangles` 主K経由の制限と導来制限のshift整合的比較・三角性
- `CompactAdjunctionCoproducts` dg加群導来圏のcompact保存左随伴に対する右随伴の余積保存
- `BimoduleMiddleComparisonComputation` 全導来中間比較を指定K-flatモデルで計算する入口
- `BimoduleMiddleCompositeFamily` 二段階の中間dg圏制限による全導来合成比較のsource
- `BimoduleMiddleCompositePresentation` 二段階中間比較の閉零表示と合成正規化の可換性
- `BimoduleMiddleTransportComputation` 全導来中間比較の表示移送付きモデル計算
- `BimoduleMiddleFullCalculation` 全導来中間比較を任意の指定モデルと出力制限で計算する
- `BimoduleRestrictionModelCalculation` 外側右制限と全導来中間比較を組み合わせた任意モデル計算
- `BimoduleRestrictionSourceNormalization` 外側右制限と中間比較のsource表示の正規化

### Derived.BimoduleMiddle3 → Derived.BimoduleMiddle.FunctorCoherence

中間圏制限の準同値、恒等・合成と反復比較の整合性。

- `BimoduleMiddleQuasiIso` 準同値に沿う制限後モデルの実際のbimodule合成比較の準同型性
- `BimoduleMiddleEquivalence` dg準同値に沿う中間圏比較の全導来自然同型
- `BimoduleMiddleResolvedCoherence` 制限後モデルによるbimodule合成比較の自己・推移整合性
- `BimoduleMiddleIdentity` 恒等dg関手の実際の導来中間比較と制限の恒等自然同型の整合性
- `BimoduleMiddleFunctorComposition` dg関手の合成と指定モデルによる実際の導来中間比較の整合性
- `BimoduleMiddleCanonicalComposition` 標準semifree解像度による導来中間比較のdg関手合成則
- `BimoduleMiddleIdentityFamily` 恒等中間比較の解像度を含まないsource同型を関手族へ束ねる
- `BimoduleMiddleIdentityFull` 恒等中間比較と左右制限のsource正規化の全導来関手族上での一致
- `BimoduleMiddleAugmentedSource` 制限後の指定モデルから二段階の全導来sourceへの増大
- `BimoduleMiddleAugmentedTransport` 指定増大による二段階sourceと移送計算の接続
- `BimoduleMiddleIteratedComputation` 二段階全導来比較を指定K-flatモデルと増大で計算する
- `BimoduleMiddleFullComposition` 中間dg圏制限の合成則を両変数の全導来圏へ降ろす

## private の衝突回避案

AssociatorLeftRestrictionModel の paste_associator を維持し、AssociatorMiddleRestrictionModel は paste_associator_middle、AssociatorSecondMiddleRestrictionModel は paste_associator_second_middle とする。後者の post_paste は post_paste_second_middle とする。元モジュール単位の private_renames で宣言と参照を同時に改名し、共有化は D6 の提案とする。

## D3 後の再照合

611 元には DG-W2(b) で SharedFunctoriality へ移る Functor.ModuleExtensionConjugation と Module.ExtensionRepresentableClosedNaturality、Module.ExtensionRepresentableComposition が含まれる。現状の 48 群・611 元の草案として記録し、D3 完了後にこれら 3 本を統合元から除き、各 import を移動先へ合わせる。残りは 608 元となる見込み。新しく土台へ入る D3 のモジュールはこの対応表の対象外。
