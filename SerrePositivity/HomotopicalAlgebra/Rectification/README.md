# 中断した任意モデル源の厳密化

このディレクトリは、[棚卸し](../../../formalization-plans/k-theory-generalization-inventory.md#layout-execution)でBとした413本の正規配置である。任意モデル源への一般化は引き続き中断中で、厳密なRMapの完成を表さない。

- 一般道具だけを使う入口：`SerrePositivity.HomotopicalAlgebra.GeneralTools`。
- 共有のモデル圏一般論を使う入口：`SerrePositivity.HomotopicalAlgebra.Foundations`。
- 専用の比較・正規化・選択・小値化も使う入口：`SerrePositivity.HomotopicalAlgebra.Rectification.Foundations`。

一般入口はB・Rectificationの推移的importを持たず、棚卸しA全190本と切り出した一般層14本を保持する。C15本は分類を保留したまま、専用入口からも利用できる。Cのうち一般入口から必要な独立した道具は元の場所に残す。

元の名前空間・公開宣言名・型・証明は保っている。旧Bの413パスは対応する正規モジュールへの`public import`だけを行う互換入口であり、今後も個別の旧importを使える。新規の専用コードはここを直接importする。一般入口から専用層を暗黙に得る利用箇所は、専用入口を明示する。

一般部分を全て切り出した旧モジュールの正規版には、一般層の再公開だけが残るものもある。これは以前の専用入口の公開範囲を保つためで、定義を複製したものではない。

対応表は`scripts/homotopical_generalization_manifest.json`、依存監査は`python3 scripts/audit_homotopical_layout.py`。公理監査は`audit_homotopical_general_tools.lean`、`audit_homotopical_foundations.lean`、`audit_homotopical_rectification.lean`に分け、全てのimportされたプロジェクト宣言を標準3公理のみか確認する。L・E・Sは従来のstage 4監査を維持する。

未追跡の`Simplicial/RelativeFillerComparison.lean`は移動・編集せず、今回の受入対象に含めない。
