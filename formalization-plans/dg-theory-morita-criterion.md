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
