# DG-W2 統合先の命名案（§9-5）

基点 `406c19405`。main `6f2d47f60` の §9 を `git show` で読み、main の merge はしていない。
**Claude の承認待ちの案。Lean ファイルの移動・統合・import 書換えは未適用。**
今回の 78 統合先のうち、番号付きの仮名 30 件を主題を表す名詞句へ変更し、48 件は維持する。
元モジュールの basename と module docstring を確認した。主題で区別できるため `Part1` / `Part2` は使わない。
表中の名前は `SerrePositivity.DifferentialGraded.` からの相対名。対応表のキーと草案の `module` に同じ案を反映した。
基盤側の対象外 48 群は変更しない。対応表の元リストでは §5-0 の未追跡ファイルと §9-1 の OrderSquare を除外し、残りの順序を維持した。草案の依存順も OrderSquare の除去以外は維持する。

## 旧仮名 → 本名（案）

| 旧仮名 | 本名（案） | 主題・命名理由 |
| --- | --- | --- |
| `Endomorphism.Basic` | `Endomorphism.Basic` | 既存の主題名を維持。 |
| `Tensor.Parameter` | `Tensor.Parameter` | 既存の主題名を維持。 |
| `Tensor.BalancedElements` | `Tensor.BalancedElements` | 既存の主題名を維持。 |
| `Tensor.ScalarExtension1` | `Tensor.ScalarExtension.CategoriesAndModules` | dg 圏・加群・全 Hom の係数変更と制限比較 |
| `Tensor.ScalarExtension2` | `Tensor.ScalarExtension.BalancedTensor` | 係数変更随伴と balanced tensor の表示・比較 |
| `Quotient.Path1` | `Quotient.Path.Construction` | 有限 path の構成・連結と ε 消去 cochain |
| `Quotient.Path2` | `Quotient.Path.Evaluation` | 指定収縮による path 評価と内部微分・合成の整合性 |
| `Quotient.Erasure` | `Quotient.Erasure` | 既存の主題名を維持。 |
| `Quotient.Scalar` | `Quotient.Scalar` | 既存の主題名を維持。 |
| `Quotient.Append` | `Quotient.Append` | 既存の主題名を維持。 |
| `Quotient.Composition` | `Quotient.Composition` | 既存の主題名を維持。 |
| `Quotient.DerivedComparison1` | `Quotient.DerivedComparison.Filtration` | 商関手の延長と path 長 filtration・次数層・作用 |
| `Quotient.DerivedComparison2` | `Quotient.DerivedComparison.ColimitCones` | 長さ部分加群の余極限と比較 cone の図式 |
| `Quotient.DerivedComparison3` | `Quotient.DerivedComparison.LocalFlatness` | 局所 K-flat 条件、有限 cell・三角比較と局所 Hom |
| `Quotient.DerivedComparison4` | `Quotient.DerivedComparison.LayerTriangles` | 長さ層の加群・三角形と自由加群の導来延長 |
| `Quotient.DerivedComparison5` | `Quotient.DerivedComparison.Equivalence` | 生成・有限 roof からの完全忠実性、Verdier 比較同値と perfect enhancement |
| `Bimodule.Basic` | `Bimodule.Basic` | 既存の主題名を維持。 |
| `Bimodule.Value` | `Bimodule.Value` | 既存の主題名を維持。 |
| `Perfect.RepresentableHomology` | `Perfect.RepresentableHomology` | 既存の主題名を維持。 |
| `Perfect.Compact1` | `Perfect.Compact.Enhancement` | compact 性の閉性、Perf の本質的小性と小さい dg enhancement |
| `Perfect.Compact2` | `Perfect.Compact.FiniteGeneration` | compact ⇒ Perf の有限 cell 因子分解と有限射影代表・冪等完備性 |
| `Presentation.Category` | `Presentation.Category` | 既存の主題名を維持。 |
| `Presentation.GeneratedHom1` | `Presentation.GeneratedHom.CoefficientClosure` | 係数語の dg 閉包、基数評価と固定基底コードへの持ち上げ |
| `Presentation.GeneratedHom2` | `Presentation.GeneratedHom.SphereLifts` | 提示の非連結和と自由 sphere・行列・代表加群の同時持ち上げ |
| `Bimodule.Tensor` | `Bimodule.Tensor` | 既存の主題名を維持。 |
| `Bimodule.Right` | `Bimodule.Right` | 既存の主題名を維持。 |
| `Tensor.Enriched` | `Tensor.Enriched` | 既存の主題名を維持。 |
| `Tensor.Bimodule1` | `Tensor.Bimodule.Actions` | bimodule tensor の両作用・射・パラメータと中間圏比較 |
| `Tensor.Bimodule2` | `Tensor.Bimodule.KFlatness` | 相対 K-flat 性、cone・shift 閉性と擬同型保存 |
| `Tensor.Fubini` | `Tensor.Fubini` | 既存の主題名を維持。 |
| `Tensor.Associator1` | `Tensor.Associator.Components` | 結合比較の三重生成元・左右作用・全 Hom 自然性と同型成分 |
| `Tensor.Associator2` | `Tensor.Associator.Pentagon` | 五角 coherence と結合比較の射・パラメータ自然性、射影的 K-flat 比較 |
| `Tensor.Associator3` | `Tensor.Associator.Restriction` | 外側・二つの中間圏の制限と結合子の可換 square |
| `Tensor.Triple` | `Tensor.Triple` | 既存の主題名を維持。 |
| `Tensor.Graded` | `Tensor.Graded` | 既存の主題名を維持。 |
| `Tensor.Compose` | `Tensor.Compose` | 既存の主題名を維持。 |
| `Resolution.Basic` | `Resolution.Basic` | 既存の主題名を維持。 |
| `Resolution.Free.Evaluation` | `Resolution.Free.Evaluation` | 既存の主題名を維持。 |
| `Resolution.Cells.Boundary` | `Resolution.Cells.Boundary` | 既存の主題名を維持。 |
| `Resolution.Cells.Append1` | `Resolution.Cells.Append.Recursion` | cell path の連結再帰・prefix・内部単位と cochain 外延性 |
| `Resolution.Cells.Append2` | `Resolution.Cells.Append.BoundaryCompatibility` | 連結と指定境界置換の Leibniz 則・最終微分の整合性 |
| `Resolution.Cells.Length` | `Resolution.Cells.Length` | 既存の主題名を維持。 |
| `Resolution.Cells.Path` | `Resolution.Cells.Path` | 既存の主題名を維持。 |
| `Resolution.FixedObject` | `Resolution.FixedObject` | 既存の主題名を維持。 |
| `Resolution.Cell` | `Resolution.Cell` | 既存の主題名を維持。 |
| `Resolution.Composition` | `Resolution.Composition` | 既存の主題名を維持。 |
| `Morita.Kernel` | `Morita.Kernel` | 既存の主題名を維持。 |
| `Morita.CoherenceCompositionKernel` | `Morita.CoherenceCompositionKernel` | 既存の主題名を維持。 |
| `Morita.CoherenceAssociator` | `Morita.CoherenceAssociator` | 既存の主題名を維持。 |
| `Perfect.Basic` | `Perfect.Basic` | 既存の主題名を維持。 |
| `Perfect.Ring2` | `Perfect.Ring.FiniteProjectiveComparison` | 有界有限射影複体から主 Perf への比較と retract の次数幅帰納 |
| `Perfect.EnhancementOperations` | `Perfect.EnhancementOperations` | 既存の主題名を維持。 |
| `Verdier.Derived` | `Verdier.Derived` | 既存の主題名を維持。 |
| `Endomorphism.Module` | `Endomorphism.Module` | 既存の主題名を維持。 |
| `Endomorphism.Derived1` | `Endomorphism.Derived.Functors` | 再構成 Hom・tensor の導来化、評価と局所生成判定 |
| `Endomorphism.Derived2` | `Endomorphism.Derived.Adjunction` | 射影性と Hom 同値による再構成 tensor–Hom 随伴 |
| `Endomorphism.Scalar1` | `Endomorphism.Scalar.HomComparison` | 実際の係数拡大による全次数 Hom 比較・Yoneda・retract 自然性 |
| `Endomorphism.Scalar2` | `Endomorphism.Scalar.PerfectStability` | Hom 比較の shift・cone 閉性と perfect・射影的加群の保存 |
| `Endomorphism.Scalar3` | `Endomorphism.Scalar.EnhancementComparison` | thick 閉包上の dg 像と enhancement・主 Perf の導来係数変更比較 |
| `Endomorphism.Shift` | `Endomorphism.Shift` | 既存の主題名を維持。 |
| `Endomorphism.Perfect` | `Endomorphism.Perfect` | 既存の主題名を維持。 |
| `Endomorphism.Enhancement` | `Endomorphism.Enhancement` | 既存の主題名を維持。 |
| `Morita.Perfect` | `Morita.Perfect` | 既存の主題名を維持。 |
| `Morita.ScalarExtension1` | `Morita.ScalarExtension.KernelComparison` | kernel の通常・局所化係数変更と導来作用・増大比較 |
| `Morita.ScalarExtension2` | `Morita.ScalarExtension.PerfectSquares` | 出力評価モデルによる kernel 係数変更正方形と Perf 制限 |
| `Morita.CriterionDerivedCoproducts` | `Morita.CriterionDerivedCoproducts` | 既存の主題名を維持。 |
| `Bimodule.DiagonalRestriction` | `Bimodule.DiagonalRestriction` | 既存の主題名を維持。 |
| `Tensor.LeftUnitRestriction` | `Tensor.LeftUnitRestriction` | 既存の主題名を維持。 |
| `Tensor.ResolvedRestriction` | `Tensor.ResolvedRestriction` | 既存の主題名を維持。 |
| `Verdier.Scalar` | `Verdier.Scalar` | 既存の主題名を維持。 |
| `Morita.CriterionPerfTriangulated` | `Morita.CriterionPerfTriangulated` | 既存の主題名を維持。 |
| `Morita.Adjunction1` | `Morita.Adjunction.Construction` | telescope と局所生成による一般 kernel 右随伴の構成・Morita 判定 |
| `Morita.Adjunction2` | `Morita.Adjunction.Coherence` | 実際の右随伴の正方形・合成・係数変更と Perf 逆関手の比較 |
| `Morita.QuasiEquivalenceGraph` | `Morita.QuasiEquivalenceGraph` | 既存の主題名を維持。 |
| `Quotient.DerivedComparisonGraphSquare` | `Quotient.DerivedComparisonGraphSquare` | 既存の主題名を維持。 |
| `Verdier.Comparison` | `Verdier.Comparison` | 既存の主題名を維持。 |
| `Verdier.Karoubi` | `Verdier.Karoubi` | 既存の主題名を維持。 |
| `Verdier.Kernel` | `Verdier.Kernel` | 既存の主題名を維持。 |

## 番号付き 30 群の根拠

以下は各群の元 basename と module docstring の見出し（未記載の元は basename のみ）。各元の本文・宣言名は変更しない。

### Tensor.ScalarExtension1 → Tensor.ScalarExtension.CategoriesAndModules

dg 圏・加群・全 Hom の係数変更と制限比較。

- `RestrictionComparison`：dg関手に沿うbalanced tensorの比較chain map
- `RestrictionComparisonCoherence`：制限tensor比較のdg関手合成に関する整合性
- `ScalarExtensionColimits`：非有界複体の係数変更と余極限
- `ScalarExtensionCoherence`：係数変更の tensor 比較の整合性
- `ScalarExtension`：dg 圏の underived 係数変更
- `ScalarExtensionHom`：係数変更と全次数 Hom の比較
- `ScalarExtensionModule`：dg 加群の対象の係数変更
- `ScalarExtensionCochain`：係数変更と閉性を仮定しない斉次 cochain
- `ScalarExtensionDiagrams`：tensor 式の係数変更を組み立てる比較射
- `ScalarExtensionNaturality`：全次数 Hom の係数変更比較の両変数自然性
- `ScalarExtensionModuleMaps`：dg 加群圏上の係数拡大関手
- `ScalarRestrictionHom`：係数制限による全次数 Hom の比較
- `ScalarRestrictionCategory`：dg 圏の係数制限と係数変更の単位
- `ScalarRestrictionModule`：dg 加群の係数制限
- `ScalarRestrictionNaturality`：全次数 Hom の係数制限比較の自然性

### Tensor.ScalarExtension2 → Tensor.ScalarExtension.BalancedTensor

係数変更随伴と balanced tensor の表示・比較。

- `ScalarRestrictionModuleMaps`：dg 加群圏上の係数制限関手
- `ScalarExtensionAdjunction`：dg 加群圏上の係数拡大と係数制限の随伴
- `ScalarExtensionActions`：係数変更と balanced tensor の左右作用
- `ScalarExtensionPresentation`：balanced tensor の直和表示の係数変更
- `ScalarExtensionBalanced`：相対 balanced tensor の underived 係数変更同型
- `ScalarExtensionBalancedNaturality`：相対 tensor の係数変更同型の両変数自然性
- `ScalarExtensionLeftMaps`：左 dg 加群圏の係数拡大と相対 tensor 双関手の比較
- `ScalarExtensionRing`：一対象環での相対 tensor の係数変更と通常 tensor の比較
- `ScalarExtensionCoendCoherence`：係数変更と相対 tensor の評価単位・パラメータ結合比較

### Quotient.Path1 → Quotient.Path.Construction

有限 path の構成・連結と ε 消去 cochain。

- `Paths`：明示的dg商の有限pathとtensor項
- `PathUniversal`：内部微分を持つpath直和の普遍性と空部分圏の比較
- `PathPrefix`：先頭Homとεを保持する全path直和への包含
- `PathCochainExt`：全path直和を始域とする任意次数cochainの包含による判定
- `PathCochainDesc`：任意次数のpath cochainの全直和への貼合せ
- `PathComposition`：有限path tensor項の連結
- `PrependUnit`：有限pathの先頭Hom合成の左単位則
- `PrependAssociativity`：有限pathの先頭Hom合成の結合則
- `EpsilonAppend`：単一ε pathを連結したときの単位因子の消去
- `EpsilonCochainExt`：標準ε生成元上の評価による次数0 cochainの判定
- `EpsilonDifferential`：収縮記号を消す次数+1 cochain
- `EpsilonTensor`：ε消去cochainのtensorによる拡張
- `EpsilonHomogeneousExt`：任意次数の cochain を標準 ε 生成元上で判定する。

### Quotient.Path2 → Quotient.Path.Evaluation

指定収縮による path 評価と内部微分・合成の整合性。

- `PathGeneration`：元のHomと指定εの反復合成によるpathの生成式
- `ScalarExtension`：明示的 dg 商の最終 Hom の係数変更
- `EpsilonContraction`：指定ε生成元の収縮方程式
- `ContractedFunctor`：指定収縮データを持つdg関手と商からの制限
- `ContractionCochain`：指定収縮元からεの評価cochainを構成する
- `ContractionAction`：指定収縮のHomへの作用と、その微分のε消去表示
- `PathEvaluation`：指定収縮付きdg関手による有限pathの評価
- `PathEvaluationPrepend`：元のHomを先頭合成する操作と有限path評価の整合性
- `PathEvaluationAppend`：指定収縮による評価は任意二pathの連結を保つ
- `EvaluationPrefix`：固定前方Homとεによる評価作用・非空pathの微分入力
- `InternalEvaluation`：指定収縮付きdg関手による全path直和の評価cochain
- `InternalEvaluationPrefix`：全path直和への前方Hom・ε追加と評価の整合性
- `InternalEvaluationPrepend`：全path評価と元のHomによる先頭作用の整合性
- `InternalEvaluationComposition`：全path直和の評価は内部合成を保つ
- `HomogeneousNaturality`：概要：実 Drinfeld 商の全次数自然性は元 Hom と指定 ε で判定できる。
- `PathEvaluationDifferential`：非空path評価の微分を先頭消去と後方微分へ分ける
- `EvaluationErasure`：全path評価のHom微分とε消去作用素の整合性
- `Evaluation`：指定収縮付きdg関手の最終商Hom上の評価chain map
- `EvaluationComposition`：最終Homの評価chain mapの合成保存

### Quotient.DerivedComparison1 → Quotient.DerivedComparison.Filtration

商関手の延長と path 長 filtration・次数層・作用。

- `Extension`：指定収縮付きdg関手の商への延長と制限との一方の往復
- `Reconstruction`：商dg関手を制限データのpath評価から再構成する
- `Universal`：指定収縮データ付きdg関手に関する明示的商の厳密普遍性
- `ParameterExtension`：概要：選択された収縮と整合する全パラメータ変換を、同じ実商へ厳密に延長する。
- `ParameterPostcomposition`：概要：同じ選択収縮の後合成族について、全パラメータの商延長を実構成する。
- `DerivedComparisonFiltration`：最終 dg 商 Hom の path 長 filtration
- `DerivedComparisonFiltrationZero`：長さ filtration の零段と元の Hom の同型
- `DerivedComparisonFiltrationColimit`：最終 dg 商 Hom は長さ部分複体の逐次余極限
- `DerivedComparisonFunctoriality`：指定部分集合を対応させる dg 関手の、明示的商への延長
- `DerivedComparisonColimitQuasiIso`：厳密な複体図式の exact な余極限による擬同型の保存
- `DerivedComparisonGradedProjection`：固定長 path 直和の射影と最終微分との整合性
- `DerivedComparisonGraded`：長さ filtration の随伴次数部分と固定長 path 直和
- `DerivedComparisonFiltrationAction`：長さ filtration と先頭 Hom の全次数作用
- `DerivedComparisonLengthAction`：長さ部分複体への全次数作用の制限
- `FunctorLaws`：概要：固定標準 ε を保つ正本商関手の、厳密な恒等・合成と元 Hom 作用。

### Quotient.DerivedComparison2 → Quotient.DerivedComparison.ColimitCones

長さ部分加群の余極限と比較 cone の図式。

- `DerivedComparisonLengthModule`：商の代表加群の長さ部分加群
- `DerivedComparisonModuleColimit`：制限代表加群を長さ部分加群の逐次余極限として復元する
- `DerivedComparisonConeDiagram`：長さ零段階からの比較 cone の厳密な図式
- `DerivedComparisonConeColimit`：全体への比較 cone は有限長比較 cone の逐次余極限

### Quotient.DerivedComparison3 → Quotient.DerivedComparison.LocalFlatness

局所 K-flat 条件、有限 cell・三角比較と局所 Hom。

- `DerivedComparisonCells`：graph tensor の有限 cell 像
- `DerivedComparisonFlatness`：明示的 dg 商の導来比較に用いる片側の局所 K-flat 仮定
- `DerivedComparisonContraction`：明示的 dg 商が殺す代表対象
- `DerivedComparisonZeroModule`：長さ零段階と代表加群、および商への比較射
- `DerivedComparisonGenerators`：空 path 包含による代表対象上の実際の導来比較
- `DerivedComparisonExtension`：tria(D) 全体から明示的 dg 商の tria への比較
- `DerivedComparisonRestriction`：dg 商の加群を制限したときの S 上の acyclic 性
- `DerivedComparisonTriangulated`：有限 cell の三角モデルによる dg 商比較と Verdier 因子化
- `DerivedComparisonPathFlatness`：片側局所 K-flat 仮定と path の係数複体
- `DerivedComparisonPathModule`：内部 path 項の右 dg 加群構造
- `DerivedComparisonLocalObjects`：商の導来制限の像は指定有限 cell に対して局所的
- `DerivedComparisonHomPresheaf`：制限代表加群への Hom を指定 Verdier 商へ降ろす
- `DerivedComparisonGradedTensor`：固定長 path の両端分解と片側 K-flat 係数
- `DerivedComparisonGradedModule`：固定長 path の直和を右 dg 加群として表す
- `DerivedComparisonLocalHom`：片側 K-flat 条件と S に直交する対象上の Hom 比較

### Quotient.DerivedComparison4 → Quotient.DerivedComparison.LayerTriangles

長さ層の加群・三角形と自由加群の導来延長。

- `DerivedComparisonLayerModule`：長さ filtration の層射影を右 dg 加群射にする
- `DerivedComparisonLayerTriangle`：長さ filtration の層と加群 cone の導来比較
- `DerivedComparisonFreeExtension`：K-flat 係数からの自由加群を一対象環からの導来延長で計算する

### Quotient.DerivedComparison5 → Quotient.DerivedComparison.Equivalence

生成・有限 roof からの完全忠実性、Verdier 比較同値と perfect enhancement。

- `DerivedComparisonAdjointUnit`：代表加群上の導来随伴と実際の比較写像の整合性
- `DerivedComparisonFreeGeneration`：自由右加群の導来像の局所生成
- `DerivedComparisonLayerGeneration`：局所 K-flat 仮定による長さ層と有限長比較 cone の生成
- `DerivedComparisonUnitCone`：商への代表加群比較の cone の局所生成
- `DerivedComparisonFiniteRoof`：比較 cone の有限因子分解性から Verdier 分母を作る
- `DerivedComparisonRepresentableHom`：商内の代表対象への射と制限代表加群への導来 Hom
- `DerivedComparisonHomNormalization`：Verdier Hom 同値と実際の導来延長の射写像
- `DerivedComparisonDerivedLift`：実際の導来延長の Verdier 因子化と代表対象への射写像の全単射性
- `DerivedComparisonFullFaithful`：局所 K-flat 版の実際の導来延長の Verdier 因子化の充満忠実性
- `DerivedComparisonEquivalence`：局所 K-flat 版の tria(D)/tria(S) と tria(D/S) の同値
- `DerivedComparisonPerfect`：局所 K-flat 版の dg 商の perfect enhancement と完備 Verdier 商
- `DerivedComparisonExtensionCoherence`：導来延長とホモトピー有限 cell 上の underived 延長の自然同型
- `DerivedComparisonCanonical`：既存の有限 cell 比較と導来延長による比較の自然同型

### Perfect.Compact1 → Perfect.Compact.Enhancement

compact 性の閉性、Perf の本質的小性と小さい dg enhancement。

- `Compact`：u-small余積に関するdg導来加群のcompact性
- `CompactComparison`：compact性と標準Hom直和比較の全単射性
- `CompactRetracts`：compact dg導来対象のretract・同型閉性
- `CompactShift`：compact dg導来対象の整数shift閉性
- `CompactTriangles`：compact dg導来対象の三角閉性
- `Enhancement`：射影的perfect dg加群による主Perfのenhancement
- `EnhancementLinear`：射影的perfect加群によるH⁰比較の線形性
- `PerfectCompact`：有限cellとそのretractのcompact性
- `Generators`：代表加群の整数shiftによる主導来圏のcompact生成性
- `EssentiallySmall`：主導来圏内のPerfの本質的小性
- `SmallEnhancement`：小さい射影的perfect dg代表系

### Perfect.Compact2 → Perfect.Compact.FiniteGeneration

compact ⇒ Perf の有限 cell 因子分解と有限射影代表・冪等完備性。

- `RingTriangleFiniteModel`：逆回転三角形から有限射影代表を戻す
- `RingRetractFiniteRepresentative`：有限射影複体の導来retractの有限射影代表
- `RingPerfectRepresentatives`：一対象Aの主Perfの全対象の有界有限射影代表
- `CompactConverseTelescope`：compact ⇒ Perf に向けた可算 telescope の有限段階因子分解
- `CompactConverseFactor`：有限 cell を経由する射と compact 性
- `CompactConverseExtensions`：compact な始域からの有限 cell 因子分解の拡大閉性
- `CompactConverseResolutionStages`：標準解像度の有限高さの段階への有限 cell 因子分解
- `CompactConverseSequential`：可算余極限の 1-shift による cokernel 表示
- `CompactConverseSequentialCone`：dg 加群の可算余極限と telescope cone の擬同型
- `CompactConverse`：compact ⇒ Perf：引用なしの標準解像度による証明
- `SmallEnhancementTriangulated`：小さいperfect dg代表系のH⁰三角構造
- `EnhancementIdempotents`：実際の射影的perfect dg enhancement内のホモトピー冪等元の分裂
- `RingPerfectEquivalence`：既存PerfectHomotopyと一対象主Perfの同値、およびホモトピー冪等分裂
- `RingPerfectCoherence`：有限射影の閉零冪等分裂と元の比較同値の導来・shift・三角図式
- `RingKaroubiFactors`：Karoubi実現の元の比較への因子化と整数shiftの整合性

### Presentation.GeneratedHom1 → Presentation.GeneratedHom.CoefficientClosure

係数語の dg 閉包、基数評価と固定基底コードへの持ち上げ。

- `GeneratedHomWords`：概要：指定斉次係数から微分・単位・合成で作る有限語とその実 Hom 評価を与える。
- `GeneratedHomSpan`：概要：指定係数の有限語の線形 span は、単位・微分・合成で閉じた斉次 Hom 族を与える。
- `GeneratedHomComplex`：概要：微分で閉じた係数 span を実 Hom 複体として構成し、元の Hom 複体へ単射で比較する。
- `GeneratedHomUnit`：概要：係数 span の実 Hom 複体の単位を、元の閉単位元から構成する。
- `GeneratedHomComposition`：概要：係数 span の Hom 複体に元の斉次合成を制限する。
- `GeneratedHomCategory`：概要：指定斉次係数の単位・微分・合成閉包を実 dg 圏として構成する。
- `GeneratedHomFunctorLift`：概要：全 Hom 像が指定係数 span に入る dg 関手を、同じ実 dg 係数閉包へ持ち上げる。
- `GeneratedHomWordCardinality`：概要：係数の有限語の個数は、指定生成子・対象ラベルと可算集合の最大で抑えられる。
- `GeneratedHomFreeCover`：概要：係数語の線形 span を固定した κ 個の自由基底で全射に被覆する。
- `GeneratedHomCode`：概要：κ 個以下の指定係数の dg 閉包を既存の小出発提示コードへ符号化する。
- `GeneratedHomCodeFaithful`：概要：係数閉包の固定基底コードの評価は、全 Hom 複体で単射である。
- `GeneratedHomCodeFunctorLift`：概要：指定係数閉包に入る元の出発 dg 関手を固定基底の共通コードへ持ち上げる。
- `GeneratedHomCochainLift`：概要：係数 span に入る斉次射を固定基底コードへ持ち上げ、実評価と閉性を厳密に保持する。
- `GeneratedHomClosedLift`：概要：係数 span に入る元の閉次数零射をコードの実閉射へ持ち上げる。
- `QuotientGeneratorImage`：概要：固定自由加群の商からの線形写像の像が指定 submodule に入ることを基底で判定する。
- `FiniteRowCoefficientBound`：概要：κ個以下の行に有限個ずつ現れる係数の総数をκで抑える。
- `GeneratedHomSourceContainment`：概要：元の出発提示の各 Hom の全像は、固定基底の像を含めるだけで係数閉包に入る。
- `GeneratedHomSourceGenerators`：概要：元の小出発提示の全 Hom 像を含む κ 個以下の指定係数族を構成する。
- `GeneratedHomAugmentedCoefficients`：概要：元の出発提示の全基底像に追加係数を併合し、同じ κ 上界と全 Hom 包含を保つ。
- `GeneratedHomAugmentedCode`：概要：追加κ個以下の斉次係数を含み、元の出発 dg 関手を厳密に因子化するコードを構成する。
- `GeneratedHomAugmentedClosedFamily`：概要：κ個以下の元の閉射を同じ精密化コードへ同時に持ち上げる。

### Presentation.GeneratedHom2 → Presentation.GeneratedHom.SphereLifts

提示の非連結和と自由 sphere・行列・代表加群の同時持ち上げ。

- `EnrichedLawTransport`：概要：Hom 対象の等式と単位・合成の異種等式に沿って豊穣圏の三法則を移す。
- `CategorySigma`：概要：固定基底を共有する dg 圏提示データの非連結和を構成する。
- `CategorySigmaDesc`：概要：各出発提示からの dg 関手を非連結和からの一つの関手へまとめる。
- `CategorySigmaInclusion`：概要：非連結和の各成分を、全 Hom の同型を保持して包含する。
- `CategorySigmaComponents`：概要：非連結和からの共通評価を各成分へ制限すると元の dg 関手に厳密に一致する。
- `GeneratedHomSphereArrowLift`：概要：元の Hom 係数を含むκコードで、任意シフト自由 sphere 間の閉射を持ち上げる。
- `GeneratedHomSphereExtensionComparison`：概要：コード内に持ち上げた任意シフト自由閉射を、実延長の端点同型付きで元の閉射へ比較する。
- `GeneratedHomSphereMatrixLift`：概要：コードの全シフト自由閉射行列を、実延長と直和端点の同型付きで元の行列へ比較する。
- `GeneratedHomAugmentedSphereFamily`：概要：κ個以下の全シフト自由 sphere 間閉射を、一つの係数コードへ同時に持ち上げる。
- `GeneratedHomClosedFamilyRepresentables`：概要：同時に持ち上げた閉射を、実延長した代表加群間の同じ閉射へ比較する。

### Tensor.Bimodule1 → Tensor.Bimodule.Actions

bimodule tensor の両作用・射・パラメータと中間圏比較。

- `BimoduleActions`：相対tensorに残るbimoduleの二作用
- `Bimodule`：多対象dg bimoduleの相対tensor合成
- `BimoduleElements`：bimodule合成の左作用の斉次生成元公式
- `BimoduleValueMaps`：bimodule射の相対tensorへの作用を各値で構成する
- `BimoduleValueElements`：bimodule射による相対tensorの斉次生成元の評価
- `BimoduleMapComponent`：相対tensorの値のmapを固定した成分関数で表示する
- `BimoduleMapLeftAction`：相対tensorの値のmapと外側の左作用の可換式
- `BimoduleMapElementValues`：成分の指定した値を使うtensor mapの生成元評価
- `BimoduleValueHom`：相対tensorの値のmapを固定した成分関数で表示する
- `BimoduleRightElements`：bimodule合成の右作用の斉次生成元公式
- `BimoduleMapRightAction`：相対tensorの値のmapと外側の右作用のKoszul可換式
- `BimoduleMapNaturality`：相対tensorの値のmapの左右全Hom自然性
- `BimoduleMapFamilies`：相対tensorの値のmapを全Hom自然な右加群射へ束ねる
- `BimoduleFunctor`：全Hom自然な閉零bimodule圏上の相対tensor双関手
- `BimoduleParameterValues`：任意パラメータのbimodule変換の相対tensorへの値ごとの作用
- `BimoduleParameterElements`：相対tensorのパラメータ作用のHom複体成分
- `BimoduleParameterLeft`：任意パラメータの相対tensor作用と外側の左dg作用
- `BimoduleParameterRight`：任意パラメータの相対tensor作用と外側の右dg作用
- `BimoduleParameters`：相対tensor合成の各変数の全次数パラメータ付きbimodule変換
- `BimoduleMiddleComparison`：中間dg圏の制限とbimodule合成の値での比較
- `BimoduleMiddleActions`：中間圏のtensor比較と外側の両dg作用の可換性
- `BimoduleMiddleMap`：中間dg圏の制限と合成の全Hom自然なbimodule比較射
- `BimoduleMiddleNaturality`：中間dg圏の合成比較射の両因子に関する自然性

### Tensor.Bimodule2 → Tensor.Bimodule.KFlatness

相対 K-flat 性、cone・shift 閉性と擬同型保存。

- `Cone`：balanced tensorによる標準cone保存と相対K-flatのcone閉性
- `QuasiIsoLeft`：相対K-flat性による左加群変数の準同型保存
- `KFlatCriterion`：相対K-flat性と左準同型保存の同値
- `Shift`：balanced tensorの右加群shift比較と相対K-flatのshift閉性
- `LeftKFlatResolution`：opposite上の相対K-flat性による左加群のK-flat解像度
- `KFlatComparison`：相対K-flat右加群間の準同型のtensorによる保存
- `ProjectiveLeftQuasiIso`：射影的・semifree右加群を固定した左準同型保存
- `BimoduleQuasiIso`：bimodule合成の準同型保存に必要な片側の条件
- `BimoduleKFlatQuasiIso`：右相対K-flat因子間の準同型をbimodule合成が保存する
- `BimoduleRestrictionKFlat`：生成cellの右制限からbimodule解像度の右相対K-flat性への帰着
- `BimoduleSemifreeKFlat`：相手側local HomのK-flat性から得るsemifree bimodule解像度の右相対K-flat性

### Tensor.Associator1 → Tensor.Associator.Components

結合比較の三重生成元・左右作用・全 Hom 自然性と同型成分。

- `TripleFunctors`：三つの閉零bimoduleの反復合成関手
- `AssociatorValues`：bimodule合成の値における結合比較
- `AssociatorGenerators`：実際のbimodule結合比較と三重生成元
- `AssociatorCochainExt`：実際の反復bimodule tensorを源とする全次数cochainの外延性
- `AssociatorElements`：bimodule結合比較の斉次三重生成元での計算
- `AssociatorDegreeExt`：三重生成元による各次数の線形写像の外延性
- `AssociatorLeftAction`：結合比較の左端のdg作用との整合性
- `AssociatorLeftMaps`：反復tensorの左端dg作用の主Homとcochain評価
- `AssociatorRightAction`：両括弧付けの右B作用と三重生成元の符号
- `AssociatorRightMaps`：反復tensorの右B作用の主Homとcochain評価
- `AssociatorParameterExt`：三重生成元によるパラメータ付きHomの自然性の判定
- `AssociatorCochainAction`：左端作用cochainの三重生成元上の計算
- `AssociatorActionDegree`：左作用を適用した三重生成元の結合比較
- `AssociatorComponent`：結合比較と左作用の二段の生成元輸送
- `AssociatorValueHom`：結合比較と左作用の二段の生成元輸送
- `AssociatorLeftActionMap`：結合比較と左作用の二段の生成元輸送
- `AssociatorRightTransport`：結合比較と左作用の二段の生成元輸送
- `AssociatorRightComponentCompatibility`：結合比較のRight作用の三重生成元上の整合性
- `AssociatorRightValueHomNaturality`：結合比較の右B全Hom自然性と右加群同型
- `AssociatorRightNaturality`：結合比較の右B全Hom自然性と右加群同型
- `AssociatorComponentTransport`：結合比較と左作用の二段の生成元輸送
- `AssociatorComponentCompatibility`：結合比較のLeft作用の三重生成元上の整合性
- `AssociatorValueHomNaturality`：結合比較の左端のdg作用との整合性
- `AssociatorLeftNaturality`：結合比較の左端のdg作用との整合性
- `AssociatorBimodule`：結合比較の右加群同型と左作用の全Hom自然性
- `AssociatorTransforms`：結合比較の右加群同型と左作用の全Hom自然性
- `AssociatorIso`：全Hom自然な閉零bimodule圏での結合同型

### Tensor.Associator2 → Tensor.Associator.Pentagon

五角 coherence と結合比較の射・パラメータ自然性、射影的 K-flat 比較。

- `ProjectiveComparison`：射影的/semifree対象間の準同型のtensorによる保存
- `ProjectiveKFlat`：主Homによる射影性から相対K-flat性への橋渡し
- `PentagonLongElements`：五角の三辺からなる経路の四重生成元上の評価
- `PentagonShortElements`：五角の二辺からなる経路の四重生成元上の評価
- `Pentagon`：全Hom自然なbimodule合成の五角coherence
- `AssociatorMapElements`：閉零bimodule射の三変数に関する結合比較の生成元自然性
- `AssociatorMapNaturality`：閉零bimodule射の三変数に関する結合比較の生成元自然性
- `AssociatorNaturality`：閉零bimodule射の三変数に関する結合比較の生成元自然性
- `AssociatorParameterValues`：結合比較の各bimodule変数に関する任意パラメータ自然性
- `AssociatorParameters`：主Hom endにおける結合比較の三変数の任意パラメータ自然性

### Tensor.Associator3 → Tensor.Associator.Restriction

外側・二つの中間圏の制限と結合子の可換 square。

- `OuterUnitRestriction`：外側だけを制限した合成比較と対角の単位子
- `RightRestrictionValueHom`：外側右制限比較の値を固定した成分関数で表示する
- `MiddleRestrictionValueHom`：中間制限比較の値を固定した成分関数で表示する
- `AssociatorLeftRestriction`：外側左作用の制限は通常のbimodule結合子を保つ
- `AssociatorRightRestrictionElements`：外側右制限比較の三重斉次生成元上の計算
- `AssociatorRightRestrictionPathElements`：右制限・結合子の二経路を三重斉次生成元で計算する
- `AssociatorRightRestrictionComponents`：右制限・結合子の二経路の固定成分関数による計算
- `AssociatorRightRestrictionValues`：外側右制限と結合子の、各値の複体における可換square
- `AssociatorRightRestriction`：外側右作用の制限は通常のbimodule結合子を保つ
- `AssociatorMiddleRestrictionElements`：第一中間圏の制限と結合子の斉次生成元計算
- `AssociatorMiddleRestrictionPaths`：第一中間圏の制限と結合子の二経路の計算
- `AssociatorMiddleRestrictionComponents`：第一中間圏の制限と結合子の固定成分関数計算
- `AssociatorMiddleRestrictionValues`：第一中間圏の制限と結合子の値での可換square
- `AssociatorMiddleRestriction`：第一中間圏の制限は通常のbimodule結合子と可換
- `AssociatorSecondMiddleRestrictionElements`：第二中間圏の制限と三重斉次生成元の計算
- `AssociatorSecondMiddleRestrictionPaths`：第二中間圏の制限と結合子の二経路
- `AssociatorSecondMiddleRestrictionComponents`：第二中間圏の制限と結合子の固定成分計算
- `AssociatorSecondMiddleRestrictionValues`：第二中間圏の制限と結合子の値での可換square
- `AssociatorSecondMiddleRestriction`：第二中間圏の制限は通常のbimodule結合子と可換

### Resolution.Cells.Append1 → Resolution.Cells.Append.Recursion

cell path の連結再帰・prefix・内部単位と cochain 外延性。

- `Differential`：指定境界を持つ任意次数cell付加のHom微分
- `PathCochainDesc`：任意次数のpath cochainの全直和への貼合せ
- `InternalComposition`：cell pathの連結を内部Hom直和へ延長した合成
- `Prefix`：先頭Homと任意次数生成元を全path直和に追加する包含
- `PrefixGeneration`：元のHomと生成元の合成から前方path追加を復元する
- `AppendRecursion`：左pathの先頭生成元を残す連結の再帰式
- `AppendPrepend`：任意次数cell path：AppendPrepend
- `AppendRightPrepend`：任意次数cell path：AppendRightPrepend
- `InternalUnits`：cell pathの全直和上の合成の右単位
- `CompositionPrefix`：任意次数cell path：CompositionPrefix
- `CompositionPrepend`：任意次数cell path：CompositionPrepend
- `PrependBoundaryRows`：任意次数cell path：PrependBoundaryRows
- `TensorPathCochainExt`：任意次数cell path：TensorPathCochainExt
- `TensorRightPathCochainExt`：任意次数cellの全合成の微分整合性：TensorRightPathCochainExt
- `TensorTwoPathCochainExt`：二つの全path直和のtensorからの任意次数cochainの判定

### Resolution.Cells.Append2 → Resolution.Cells.Append.BoundaryCompatibility

連結と指定境界置換の Leibniz 則・最終微分の整合性。

- `PrependBoundary`：任意次数cell path：PrependBoundary
- `PrependDifferential`：任意次数cell path：PrependDifferential
- `InternalBoundaryHead`：全path直和に先頭生成元の指定境界を作用させるcochain
- `AppendBoundaryHead`：後続pathの連結と先頭生成元の境界置換の整合性
- `AppendRightAssociativity`：任意次数cell path：AppendRightAssociativity
- `BoundaryRowRecursion`：任意次数cell pathの境界置換：BoundaryRowRecursion
- `PrefixBoundary`：先頭cell追加に対する全境界置換作用素の再帰式
- `AppendLiftCochain`：任意次数cell pathの境界置換：AppendLiftCochain
- `AppendBoundaryRecursion`：非空の左pathの連結後の境界置換の再帰式
- `AppendBoundary`：左有限pathを固定した連結の境界置換Leibniz則
- `CompositionBoundary`：任意次数cellの全合成の微分整合性：CompositionBoundary
- `CompositionDifferential`：任意次数cellの全合成の微分整合性：CompositionDifferential
- `CompositionEvaluation`：cell付加の最終Hom合成：CompositionEvaluation
- `CompositionComparison`：cell付加の最終Hom合成：CompositionComparison

### Perfect.Ring2 → Perfect.Ring.FiniteProjectiveComparison

有界有限射影複体から主 Perf への比較と retract の次数幅帰納。

- `StrictComplexEnhancement`：既存の有界有限射影複体の全Hom dg enhancement
- `StrictComplexEnhancementLinear`：既存PerfectHomotopyの全Hom dg表示における線形性と包含の比較
- `StrictComplexProjective`：既存の有限射影複体から一対象A上の主射影的dg加群へ
- `StrictComplexDerived`：有限射影複体のH⁰から主dg加群導来圏への完全忠実な比較
- `StrictComplexDerivedLinear`：既存PerfectHomotopyから主dg加群導来圏へのA線形完全忠実関手
- `StrictComplexOperations`：既存strictlyPerfectComplexの同型・零対象・次数集中に関する補助API
- `RingBounded`：有界有限射影複体の主導来perfect性
- `RingFiniteCell`：一対象Aの有限cellの評価は実際の有界有限射影複体
- `RingEnhancement`：有限射影複体から主perfect dg enhancementへの実際のdg関手
- `RingFiniteCellImage`：一対象Aの有限cellは有限射影dg複体比較のH⁰本質像に入る
- `RingPerfectComparison`：既存PerfectHomotopyから主PerfへのA線形完全忠実比較
- `RingPerfectTriangulated`：既存PerfectHomotopyから主Perfへの比較のshift・三角整合性
- `RingRetract`：主Perfの対象は既存有限射影ホモトピー圏の比較像のretract
- `RingRetractTopHomology`：有界有限射影複体の導来retractの最上ホモロジー
- `RingKaroubi`：既存PerfectHomotopyのKaroubi包絡と主Perfの比較
- `RingFiniteHomologyCover`：有限生成ホモロジーの有限自由singleによる被覆
- `RingTopTruncation`：射影的上端を取り除く良い切断
- `RingHomologyCoverCone`：有限射影singleによる上端被覆のconeを一段短くする
- `RingDerivedFiniteCover`：導来対象の有限自由上端被覆と有限射影始域からの射の持ち上げ
- `RingRetractTriangle`：retractと補対象の三角形を有限射影複体上のconeで表す
- `RingRetractRangeReduction`：有限射影複体の導来retractを一段短い次数幅へ帰着する
- `RingRetractSingle`：一次数の有限射影複体の導来retract

### Endomorphism.Derived1 → Endomorphism.Derived.Functors

再構成 Hom・tensor の導来化、評価と局所生成判定。

- `DerivedHom`：指定射影的dg加群からのHomの導来化
- `DerivedTensor`：指定dg加群Eとの再構成tensorの導来化
- `DerivedTensorNaturality`：解像度による再構成導来tensor計算の自然性
- `DerivedTensorEvaluation`：再構成導来tensorの各D成分とU12dの導来tensorの自然比較
- `DerivedEvaluation`：U12dの導来tensorからの指定対象を通る評価
- `DerivedScalarTensor`：再構成導来tensorの評価と導来係数変更
- `DerivedLocalizingGeneration`：全主導来対象を余積とconeで生成するための判定

### Endomorphism.Derived2 → Endomorphism.Derived.Adjunction

射影性と Hom 同値による再構成 tensor–Hom 随伴。

- `ActualScalarEnd`：実際に係数変更した加群のEndとのdg比較
- `ActualScalarEvaluation`：実際に係数変更したD上の加群のHomへ向かう導来評価図式
- `HomotopyAdjunction`：指定対象による再構成随伴の主ホモトピー圏への降下
- `ProjectiveCriterion`：主KにおけるHom計算によるホモトピー射影性の判定
- `TensorProjective`：指定射影的dg加群とのtensorによるホモトピー射影性の保存
- `DerivedHomEquiv`：再構成導来tensorと導来Homの射集合の比較
- `DerivedProjectiveHomNaturality`：射影的始域での再構成Hom同値の自然性
- `DerivedHomNaturality`：再構成導来Hom同値の実際の加群射に対する自然性
- `DerivedAdjunction`：指定ホモトピー射影的加群による主導来tensor–Hom随伴
- `DerivedGenerators`：再構成導来随伴による指定対象と正則End加群の比較

### Endomorphism.Scalar1 → Endomorphism.Scalar.HomComparison

実際の係数拡大による全次数 Hom 比較・Yoneda・retract 自然性。

- `IsoLocus`：恒等関手からのshift整合的自然変換の同型性の閉性
- `ScalarEvaluation`：balanced合成評価の係数変更と導来比較射の可換性
- `ScalarHomFactors`：係数変更したHom因子と実際の係数変更dg圏のHomの比較
- `ScalarEvaluationActual`：実際の係数変更先Hom因子との合成評価の可換性
- `ScalarRepresentable`：実際の代表加群と係数変更の一致
- `ScalarModuleHomNaturality`：実際の係数変更加群間のHomへ向かう全次数自然性
- `ScalarModuleHom`：係数変更した実際の加群間の全次数Hom比較
- `ScalarModuleDGFunctor`：実際の係数変更加群圏へ向かうdg関手
- `ScalarYonedaHom`：実際の加群Hom係数変更比較とdg Yoneda評価
- `ScalarYonedaIso`：代表加群を始域とする実際のHom係数変更比較の可逆性
- `ScalarClosedMap`：実際のHom係数変更比較と閉零加群射の一致
- `ScalarHomNaturality`：実際のHom係数変更比較の閉零射に関する両変数自然性
- `ScalarHomRetracts`：実際のHom係数変更比較と始域のretract
- `ScalarModuleHomotopy`：実際の係数拡大による全dg自然な加群ホモトピーの保存
- `ScalarHomElements`：実際の加群係数拡大による全次数Hom要素の合成保存
- `ScalarHomHomotopyRetracts`：実際のHom係数変更比較のH⁰内始域retract閉性
- `ScalarHomElementComponents`：Hom要素の係数拡大と各評価cochainの一致

### Endomorphism.Scalar2 → Endomorphism.Scalar.PerfectStability

Hom 比較の shift・cone 閉性と perfect・射影的加群の保存。

- `ScalarHomShift`：係数変更した全次数Homの反変shift表示
- `ScalarHomCone`：実際のHom係数変更比較のcone・三角形閉性
- `ScalarPerfectHom`：Perfect始域に対する実際の全次数Hom係数変更比較
- `ScalarProjectiveImage`：実際の係数拡大によるperfect射影的加群の射影性保存
- `ScalarShiftCoherence`：実際の加群係数拡大の正規化されたshift比較
- `ScalarShiftAddition`：実際の係数拡大の正規化shift比較の加法整合性
- `ScalarHomotopyShift`：実際の係数拡大の整合的shift比較を主Kへ降ろす
- `ScalarConeTriangles`：実際の係数拡大のcone連結射と三角形の比較
- `ScalarModuleShiftImage`：実際の加群係数拡大と整数shiftの比較同型
- `ScalarPerfectImage`：実際の係数拡大は指定生成集合からのperfect対象を保つ

### Endomorphism.Scalar3 → Endomorphism.Scalar.EnhancementComparison

thick 閉包上の dg 像と enhancement・主 Perf の導来係数変更比較。

- `ThickHomComparison`：指定生成対象のthick閉包上の全Hom擬同型
- `PerfectImage`：指定対象のthick閉包のdg像はperfectに入る
- `HomotopyImage`：加群値dg関手の主Kにおけるthick閉包の像
- `HomotopyShiftCoherence`：正規化shift比較を主ホモトピー圏へ降ろす
- `ProjectiveImage`：指定対象のthick閉包のHom像のホモトピー射影性
- `ProjectiveHomotopyComparison`：射影的主K部分圏を介したU13のambient包含のshift整合性
- `QuasiFullyFaithful`：全Hom擬同型から主H⁰の完全忠実性への比較
- `ShiftConeComparison`：再構成Hom・tensorの評価成分のshift・cone図式
- `PerfectDGComparison`：U13のperfect dg enhancement間の実際の再構成Hom比較
- `ScalarPerfectEnhancement`：実際の係数拡大のU13 enhancementへの制限
- `ScalarDerivedProjectiveComparison`：射影的加群での既存導来係数拡大と実際の係数拡大の一致
- `ScalarDerivedPerfect`：既存の導来係数拡大の主Perfへの制限
- `ScalarEnhancementClosed`：元と係数変更後のenhancementの閉零圏・H⁰を結ぶ実際の関手
- `ScalarEnhancementDerivedComparison`：U13 enhancementの実際の係数拡大と主Perfの導来係数拡大の比較
- `ScalarEnhancementShift`：U13 enhancementの実際の係数変更のshiftと三角性
- `ScalarPerfectShiftTriangles`：受入済みの主Perf係数変更の整合的shift・三角性

### Morita.ScalarExtension1 → Morita.ScalarExtension.KernelComparison

kernel の通常・局所化係数変更と導来作用・増大比較。

- `ScalarExtensionKernel`：実際の通常kernelの係数変更と左右の評価
- `ScalarExtensionKernelTensor`：実際のkernel導来作用とU12f係数変更の評価正方形
- `ScalarExtensionKernelAction`：係数変更した実際のkernel作用へのU12f評価比較
- `ScalarExtensionKernelFunctor`：通常kernelの全Hom自然な閉零射の係数変更
- `ScalarExtensionKernelProduct`：積dg圏のH⁰から主導来kernelへの非flatな係数変更
- `ScalarExtensionKernelBalanced`：kernel作用のunderived係数変更を全Hom作用へ束ねる
- `ScalarExtensionKernelBalancedModule`：係数変更したkernel作用の全Hom自然な加群比較
- `ScalarExtensionKernelBalancedNaturality`：kernel作用のunderived係数変更の入力自然性
- `ScalarExtensionKernelHomotopy`：kernel係数変更比較のH⁰降下と主導来値への接続
- `ScalarExtensionKernelLocalization`：任意可換環上の主導来kernelの係数変更
- `ScalarExtensionKernelLocalizationAugmentation`：主導来kernel係数変更から通常モデルへの自然な増大比較
- `ScalarExtensionKernelMapNaturality`：kernel射に関する実際のunderived係数変更比較の自然性
- `ScalarExtensionKernelDerivedComparison`：kernel係数変更を導来作用へ接続するH⁰増大比較
- `ScalarExtensionKernelHomotopyNaturality`：kernel係数変更比較のH⁰におけるkernel射自然性

### Morita.ScalarExtension2 → Morita.ScalarExtension.PerfectSquares

出力評価モデルによる kernel 係数変更正方形と Perf 制限。

- `ScalarExtensionKernelOutputModels`：出力係数変更の通常モデル上の比較射計算
- `ScalarExtensionKernelEvaluationModels`：kernel評価比較の標準解像度成分
- `ScalarExtensionKernelDerivedNaturality`：導来係数変更の共通モデルと増大比較のkernel射自然性
- `ScalarExtensionKernelBaseChangeNaturality`：kernel射に自然な、実際の作用評価のU12f係数変更比較
- `ScalarExtensionPerfect`：U16d：非flatな導来係数変更の主Perf制限
- `ScalarExtensionPerfectSquares`：U16d：係数変更正方形の実際の主Perf制限と自然性
- `ScalarExtensionKernelPerfectSquare`：実際のkernel導来係数変更正方形のPerf制限
- `ScalarExtensionKernelPerfectNaturality`：実際のPerf係数変更正方形のkernel射自然性
- `ScalarExtensionKernelLocalizedSquare`：局所化したkernel係数変更への実際の作用正方形
- `ScalarExtensionKernelLocalizedComposition`：局所化kernel係数変更の作用正方形と実際のkernel合成
- `ScalarExtensionOutputEvaluation`：出力加群と出力複体の導来係数変更をつなぐ計算モデル
- `ScalarExtensionKernelOutputEvaluation`：kernel出力の導来係数変更と評価の比較

### Morita.Adjunction1 → Morita.Adjunction.Construction

telescope と局所生成による一般 kernel 右随伴の構成・Morita 判定。

- `CriterionPerf`：一般 kernel の Perf 上の Morita 判定
- `CriterionPerfRelativeFullyFaithful`：概要：指定生成集合の全シフト間の Hom 比較をその thick 閉包へ延長する。
- `CriterionPerfGeneratorHomComparison`：概要：指定生成集合の局所 Hom 複体条件を全 Perf の Hom 比較へ延長する。
- `AdjunctionKernelSuccessor`：実際のkernel作用に対する生成元被覆と関係除去
- `AdjunctionKernelSequence`：任意kernelの右随伴を構成する可算近似列
- `AdjunctionKernelTelescope`：一般kernel右随伴の可算telescope
- `AdjunctionKernelGeneratorHom`：一般kernel右随伴の生成元上のHom比較
- `AdjunctionHomTriangles`：右随伴のHom比較を三角形に沿って拡張する
- `AdjunctionHomClosure`：右随伴のHom比較の同型・retract・余積閉性
- `AdjunctionHomGeneration`：生成元のHom比較から全入力の表現可能性へ
- `AdjunctionDerived`：任意kernelの実際の導来右随伴
- `CriterionDerivedFullyFaithful`：Perf上のHom比較を全主導来対象へ広げる二段階の局所化帰納
- `CriterionDerivedEquivalence`：Perf上の同値から全主導来圏へのMorita拡張
- `CriterionDerivedConditions`：Perf判定の十分性を明示した入力とする全導来Morita拡張

### Morita.Adjunction2 → Morita.Adjunction.Coherence

実際の右随伴の正方形・合成・係数変更と Perf 逆関手の比較。

- `AdjunctionSquare`：Morita作用の正方形から実際の右随伴の正方形へ
- `AdjunctionCoherence`：恒等・合成kernelの実際の右随伴の比較
- `AdjunctionScalarExtension`：局所化kernel係数変更と実際のMorita右随伴
- `CoherencePerfectUnit`：実際のPerf作用比較の両単位coherence
- `CoherencePerfectAssociator`：実際のPerf作用比較の結合coherence
- `Criterion`：U16c：三条件のMorita同値と実際の一般右随伴の統合
- `AdjunctionPerfectInverse`：Perf Morita逆関手と一般右随伴の比較

## 衝突・整合性の確認

78 の統合先は一意。既存モジュールとの同名はその統合元に含む場合だけ許し、それ以外は `git ls-files` と現存パスの両方で衝突がないことを確認した。D3 の move 先 33 本とも重複しない。対応表の該当 78 群と草案の元集合は一致し、対象外 48 群は不変。
