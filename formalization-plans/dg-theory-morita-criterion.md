# U16c：一般 kernel の Perf 上の Morita 判定

## 契約と所有範囲

正本は `dg-theory.md` §15.6。一般 kernel の右随伴を使わず、次の三条件を独立に
保持する：各列の perfect 性、表現可能対象間の全 Hom 複体の比較の擬同型性、列の
thick 生成性。通常の Hom 集合の同値だけを第二条件に置き換えない。
新規実装は `Morita/CriterionPerf*` に置く。既存の Kernel、Adjunction、Coherence、
QuasiEquivalence、Perfect、ScalarExtension、CriterionDerived および他担当のファイルを
編集しない。引用・sorry・axiom を追加しない。

## 2026-10-17：前提となる一般 kernel の三角性

`Verdier/KernelActionTriangles.lean` に実際の一般 kernel 作用の shift 構造と
完全三角形保存が公開済みであることを確認した。射影的ホモトピー圏上の実際の tensor
dg 関手を用いた証明であり、グラフ kernel に限定されない。
`Morita/CriterionPerfTriangulated.lean` はその公開経路を提供する。

- `criterionPerfKernelCommShift`、`criterionPerfKernelIsTriangulated` は
  `kernelDerivedTensor` 自身の構造。
- `criterionPerfKernel_map_distinguished` は選んだ shift の下での完全三角形保存。
- `criterionPerfActionCommShift`、`criterionPerfActionIsTriangulated` は
  `kernelColumnsPerfect` だけを追加した実際の Perf 制限の構造。
- `criterionPerfColumns_iff_preservesPerfect` は第一条件と主作用の Perf 保存との同値。

これらに局所 Hom の K-flat 性、係数環の平坦性、一般 kernel の右随伴は不要。
`lake build SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated` 成功
（2778 jobs）。`CriterionPerfTriangulatedChecks` も対象ビルド成功（2779 jobs、警告なし）。
上記6宣言の公理監査はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。

## 未完の受入項目

全 Hom 比較は、通常 kernel の左作用を、源の列の射影置換の増強による前合成へ
続けた実際の複体射として構成する。両方の列を通常のまま Hom に入れた複体を
導来 Hom と同一視しない。全次数の導来 Hom と実際の kernel 作用との整合性、
解像度の選択独立性、thick 帰納による充満忠実性、生成性からの本質的全射、
および同値からの三条件の必要性は引き続き証明する。現時点で判定全体の完了は主張しない。

## 全 Hom 比較と射影解像度の選択独立性

三角性の公開単位は `663412f9`（自分の3ファイルのみであることを直後に確認）。
`CriterionPerfHomComparison.lean` の `criterionPerfHomComparison` は通常 kernel
`P : Bimodule A E D` の左作用
`Hom_D(d,d') → moduleHom(P_d,P_d')` に、源の列の射影解像度の増強による
前合成を続けた実際の chain map。終域は `moduleHom(R_d,P_d')`。
`criterionPerfColumnDerivedHomEquiv` はその終域の H⁰ が主導来圏の列間の射を
計算することを示す。標的の列の射影性も局所 Hom の K-flat 性も不要。

`criterionPerfFullHomQuasiIso` はこの複体射が全対で擬同型になる条件。
`criterionPerfHomComparison_resolution_homotopy` は二つの射影解像度の比較射による
全 Hom 比較のホモトピー可換性を示す。比較射による前合成の擬同型性と合わせ、
`criterionPerfHomComparison_resolution_iff` と `criterionPerfFullHomQuasiIso_iff` は
解像度の選択独立性を全次数で証明する。`criterionPerfHomComparison_projective_iff` は
源の列が既に射影的である場合に限って、通常の左作用の擬同型条件へ簡約する。

検証：`lake build SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparisonChecks`
成功（2786 jobs、警告なし）。主要7宣言は標準3公理のみ。新規 sorry・axiom・引用なし。
一般の主 kernel への条件の定式化、全 shift の実作用との可換性、充満忠実性の
thick 帰納、十分性・必要性の最終定理は未完。

## 厚い生成性と同値の証拠

全 Hom 比較の単位は `7e9e1689`（直後の stat は自分の3ファイルのみ）。
`CriterionPerfGeneration.lean` の `criterionPerfColumnsThickGenerate` は、主 kernel
の列を含む厚い性質が全 perfect 対象を含むという第三条件。列が perfect であることは
この条件に含めず、第一条件として独立に受け取る。

`criterionPerf_image_le_iff_columns` は U13 の `modulePerfect_le_iff_generators` を
使って主作用の像を含む厚い性質を列上で検査する。
`criterionPerfEssImage_retract_closed` は、冪等完備な始域からの充満忠実関手の像が
retract に閉じることを実際に冪等元を分裂して証明する。
`criterionPerf_essSurj_iff_columnsThickGenerate` は列が perfect で制限が充満忠実なら、
第三条件と本質的全射が同値であることを示す。したがって Perf 判定には厚い生成性で
十分であり、無限余積や compact 生成性の追加仮定は不要。

`CriterionPerfEquivalence.lean` の `CriterionPerfEquivalenceWitness` は、Perf 圏の同値
（逆関手・二つの自然同型を含む）と、その関手の包含との合成が主導来作用の制限に
一致する自然同型を保持する。任意の圏同値を kernel 作用と取り違えない。
この証拠から `columnsPerfect` と `columnsThickGenerate` を証明した。
`criterionPerfEquivalenceWitnessOfFullyFaithful` は列の perfect 性・充満忠実性・
厚い生成性からこの証拠を構成する補助定理。**全 Hom 条件から充満忠実性への橋は
まだ受入済みではなく、この補助定理だけを最終 Morita 判定とはしない。**

検証：GenerationChecks（2785 jobs）と EquivalenceChecks（2786 jobs）の対象ビルド成功、
警告なし。計11宣言の監査は標準3公理のみ。右随伴・平坦性・局所 K-flat 条件を使わず、
新規 sorry・axiom・引用なし。

## 全 Hom 条件と実作用の全整数 shift の比較の同値

主作用との全次数接続は `bc671c6a`（直後の stat は自分の4ファイルのみ）。
`CriterionPerfFullHomCriterion.lean` の
`criterionPerfFullHomQuasiIso_iff_representableMaps` は、通常代表 P の列の全 Hom 複体の
比較が全対で擬同型であることと、実際の主作用の全ての整数 shift の表現可能対象間の
射写像が全単射であることの同値。源の shift の計算から始め、既存の主作用の
`CommShift` を使った両変数の同時 shift により、任意の二整数 m,n を扱う。
左辺はあくまで全 Hom 複体の実際の射の擬同型条件であり、射集合の条件を定義に採用していない。

`criterionPerfKernelFullHomQuasiIso_iff_representableMaps` はこの結果を主 kernel に
移し、kernel の同型を作用関手の自然同型として使う。
`criterionPerfKernelFullHomQuasiIso_model_iff` は、任意の通常代表 Q と `Q(Q) ≅ K` に
対して第二条件が同じであることを証明する。初期記録で未主張だった、通常代表の選択
独立性もこれで完了した。射影解像度の選択独立性は先の全次数の補題を再利用する。

検証：`CriterionPerfFullHomCriterionChecks` を最終入口の依存先として対象ビルド。
今回の主要3宣言の公理監査は標準3公理のみ。追加の平坦性条件・引用・sorry・axiom なし。

## 表現可能対象からの二変数の厚い帰納

生成性・同値証拠の単位は `c474f527`（直後の stat は自分の5ファイルのみ）。
`CriterionPerfHomInduction.lean` は U17 の Hom 比較の完全列による議論を、指定した
一つの始域に局所化する。`criterionPerfRelativeHomTargets` は指定族からの射比較の
全単射性を表し、同型・shift・完全三角形・retract で閉じることを証明した。

`CriterionPerfFullyFaithful.lean` の `criterionPerf_hom_bijective_of_representables` は、
全整数 shift の表現可能対象間の実際の射比較から、Perf の両変数での全単射性を導く。
まず shift 閉包した表現可能対象を始域に固定して終域の U13 最小性を適用し、その後
反対圏で同じ議論を使って始域の最小性を適用する。無限余積は使用しない。
`criterionPerfFullyFaithfulOfRepresentables` はこれを実際の主 kernel 作用の Perf 制限の
充満忠実性へ運ぶ。局所 K-flat 条件や右随伴は不要。

検証：`lake build SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomInductionChecks`
成功（2798 jobs、警告なし）。全 Hom 比較・同値証拠と同時 import し、主要8宣言は
標準3公理の範囲内（retract 補題は公理なし、反対圏移送は propext のみ）。
新規 sorry・axiom・引用なし。

最終受入に残るのは、**全 Hom 複体の擬同型条件と、この帰納の入力である全 shift の
実際の主作用の射比較との同定を両方向に証明すること**、およびその橋を使った三条件と
同値証拠との最終必要十分条件。帰納の補助入力を最終第二条件に置き換えることはしない。

## 主 kernel 上の三条件の型

二変数の厚い帰納の単位は `3f6d2b97`（直後の stat は自分の4ファイルのみ）。
`CriterionPerfConditions.lean` は三条件を独立したフィールドに持つ命題を定義する。
第二条件 `criterionPerfKernelFullHomQuasiIso` は、全 Hom 比較が擬同型となる通常代表
`P` と、`Q(P) ≅ K` の存在を要求する。これは通常の射集合条件ではなく、先に定義した
射影置換後の実際の全 Hom 複体の比較条件である。主 kernel の同型での移送も証明した。
存在命題であるため、特定の代表を主 kernel の構造へ固定しない。任意の代表に対する
条件との同値はまだ主張しない。

検証：`CriterionPerfConditionsChecks` の対象ビルド成功（2800 jobs、警告なし）。
厚い帰納・全 Hom 比較・同値証拠を同時 import。今回の主要3宣言は標準3公理のみ。
新規 sorry・axiom・引用なし。三条件から同値への最終定理と、その逆は引き続き未完。

## 閉次数零の作用公式と、全次数の導来 Hom の表示

主 kernel の条件の単位は `ef0d2d17`（直後の stat は自分の3ファイルのみ）。
`CriterionPerfHomComparisonZero.lean` は前合成・dg 関手の全 Hom 射の閉次数零制限を
証明し、`criterionPerfHomComparison_homology_zero` により、全 Hom 比較の H⁰ 写像が
列の左作用を局所化した実際の射に一致することを示す。これはまだ全整数 shift の
主 kernel 作用との同定ではない。

`CriterionPerfHomComparisonDegrees.lean` の
`criterionPerfColumnDerivedShiftedHomEquiv` は、源の列の s-shift からの主導来 Hom を
`moduleHom(R_d,P_d')` の H^(-s) と同定する。源の射影解像度・その増強の局所化同型・
Hom の源 shift の chain 同型・Mathlib の homology shift 同型を実際に合成する。
`criterionPerfRepresentableDerivedShiftedHomEquiv` は対角 bimodule と dg Yoneda を使い、
表現可能対象間の同じ表示を元の dg 圏の Hom 複体の H^(-s) として与える。
列そのものの射影性や係数環の平坦性は不要。

合同検証：TriangulatedChecks、HomComparisonChecks、GenerationChecks、EquivalenceChecks、
HomComparisonDegreesChecks を同時に対象ビルドし成功（2810 jobs、警告なし）。
最後のファイルは ConditionsChecks、HomInductionChecks、HomComparisonZeroChecks も
import する。監査対象は累計41宣言、すべて標準3公理の範囲内。
新規 sorry・axiom・引用なし。自分のパスだけを指定してコミットし、直後に stat を確認する。

残課題：上記の全次数表示の下で、全 Hom 比較の homology map と実際の
`kernelDerivedTensor` の射写像が一致することを証明し、擬同型性と全 shifted Hom の
全単射性との同値を得る。その橋を十分性・必要性に接続する。最終 Morita 判定は未完。

## 実際の主作用への次数零比較の接続

全次数の導来 Hom 計算の単位は `c31e3573`（直後の stat は自分の5ファイルのみ）。
`CriterionPerfYonedaAction.lean` は dg Yoneda の後の通常 tensor が対角との合成と
等しいことを全 Hom 射で証明し、その右単位を閉零関手間の自然同型へ組み立てる。
表現可能加群の射影性から得る相対 K-flat 性だけで、既存の導来増強の自然性を使用。
`criterionPerfYonedaMainDerivedIso` は、指定主局所化の実際の
`kernelDerivedTensor` を列の局所化と同定する自然同型である。
`criterionPerfYonedaMainActionMap` はこの同型による射の移送であり、別の作用関手は
作っていない。閉零射上の計算公式と全 Hom 比較の H⁰ の可換式を証明した。

`CriterionPerfYonedaHomology.lean` は、表現可能加群間の閉零射が全て元の dg 圏の
Yoneda 像であること、表現可能対象間の導来射にもそのような閉零代表が存在することを
証明する。これにより `criterionPerfYonedaMainActionMap_homology_zero_all` は、
代表を指定しない任意の導来射についての主作用と H⁰ 比較の可換式となる。
`criterionPerfHomComparison_quasiIsoAt_zero_iff` は全 Hom 比較の `QuasiIsoAt 0` と
実際の主作用の表現可能対象間の射写像の全単射性との同値。

検証：`lake build SerrePositivity.DifferentialGraded.Morita.CriterionPerfYonedaChecks`
成功（2810 jobs、警告なし）。新たな主要12宣言は全て標準3公理のみ。
新規 sorry・axiom・引用なし。局所 Hom の K-flat 性、列そのものの射影性、一般右随伴を
追加していない。他担当のファイル、共有ルート、正本は編集していない。

残課題を維持する：次数零だけを全 Hom の条件の代用にせず、この可換式を全整数次数へ
延ばす。具体的には、通常 tensor dg 関手の全 Hom 射を源の列の射影増強で前合成した
比較について、源の shift と射影解像度の shift を結ぶ可換図式を証明する。その結果を
`criterionPerfFullyFaithfulOfRepresentables` と同値証拠の必要性へ接続する。
最終的な三条件 ⇔ Perf 同値はまだ主張しない。

## 前合成と源 shift の全次数の可換図式

主作用への H⁰ 接続は `c7b1e3bb`（直後の stat は自分の4ファイルのみ）。
`CriterionPerfResolvedHomShift.lean` の `criterionPerfHomSourceShiftIso_apply` は、
源 shift の chain 同型を shift の次数 -s の包含との豊穣合成として全次数で記述する。
`criterionPerfModuleShiftIn_naturality` はその包含と閉零射の可換性を、全 Hom end の
各評価上で証明する。Koszul 符号と次数の再添字付けは、既存の shift の定義に従う。

`criterionPerfHomPrecompose_apply` は閉零射による Hom の前合成を全次数で記述し、
`criterionPerfHomSourceShiftIso_precompose` は、任意の閉零射 f と任意の標的 T について
`precomp(shift f) ≫ sourceShiftIso = sourceShiftIso ≫ shift(precomp f)` を chain map の
等式として証明する。f の射影性や擬同型性の仮定は不要で、射影解像度の増強にも使える。

検証：`CriterionPerfResolvedHomShiftChecks` の対象ビルド成功（2812 jobs、警告なし）。
主要4宣言は標準3公理のみ。H⁰ の主作用比較と同時 import している。
新規 sorry・axiom・引用なし。tensor dg 関手自身の shift 比較との接続と、最終必要十分
条件は未完のまま保持する。

## dg 関手と射影増強後の比較の全次数 shift

源 shift と前合成の単位は `b46d1445`（直後の stat は自分の3ファイルのみ）。
`CriterionPerfDGFunctorShift.lean` は正規化した shift の射影・包含の合成関係を
任意の加群値 dg 関手が保つことを証明する。`criterionPerfDGFunctor_shiftIn_hom` と
`criterionPerfDGFunctor_shiftIn_inv` は、その関手の shift 同型と次数 -s の包含との
両方向の可換式。`criterionPerfDGFunctorHom_sourceShift` は全 Hom chain map の可換図式。
符号を捨てたり次数零だけで代用したりせず、全整数次数で証明した。

`CriterionPerfResolvedHom.lean` は、関手の像の源の列だけを射影置換した比較と、
正規化 shift 同型を通した増強を持つ解像度の shift を構成する。
`criterionPerfResolvedHomComparison_quasiIso_iff_shifts` により、この比較の擬同型性は
全ての源 shift に対する H⁰ の擬同型性と同値になる。
入力対象の射影性や局所 Hom の K-flat 性は、この全 Hom の図式には不要。

検証：`CriterionPerfDGFunctorShiftChecks` を最終入口の依存先として対象ビルド。
今回の主要11宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。

## 通常 tensor の全 Hom 比較から主作用の全 shift の射比較へ

全次数 shift の単位は `d5806d87`（直後の stat は自分の4ファイルのみ）。
`CriterionPerfResolvedAction.lean` は、任意の射影的入力に対して主作用の計算同型を
既存の自然な導来増強から取り、通常 tensor の Hom 射と主作用の H⁰ 射写像を同定する。
`criterionPerfResolvedAction_quasiIso_iff_sourceShifts` は、源の像だけを射影置換した
全 Hom 比較の擬同型性と、全ての源 shift 上の実際の主作用の射の全単射性との同値。
ここで入力の射影性を使うが、tensor の出力そのものの射影性は仮定しない。

`CriterionPerfTensorHomComparison.lean` は列の射影解像度の増強を右単位同型で戻し、
表現可能入力の tensor の像の射影解像度を与える。全 Hom の右単位自然性から
`criterionPerfTensorHomComparison_square` を chain map の等式として証明した。
Yoneda の chain 同型と右単位による Hom の同型を用い、元の列の全 Hom 比較の擬同型性を
通常 tensor の全 Hom 比較の擬同型性に移送する。最後に
`criterionPerfHomComparison_quasiIso_iff_sourceShifts` が、元の dg 圏の Hom 複体を
始域とする比較と、全ての源 shift 上の主作用の実際の射写像を接続する。

検証：`CriterionPerfResolvedActionChecks` を最終入口の依存先として対象ビルド。
主要12宣言は標準3公理のみ。局所 Hom の K-flat 性・係数環の平坦性・一般右随伴は不要。
新規 sorry・axiom・引用なし。
