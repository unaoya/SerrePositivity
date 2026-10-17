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
