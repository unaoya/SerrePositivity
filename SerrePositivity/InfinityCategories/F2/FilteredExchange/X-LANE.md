# X レーン：I-1 a7

- 着手：2026-10-25 13:07:39 JST。
- 絶対上限：2026-10-27 13:07:39 JST（48時間）。
- 所有：このディレクトリ内の新規の葉と
  `scripts/audit_infinity_f2_exchange.lean` のみ。既存ファイルは編集しない。
- 正本の読み取り：foundations.md §6・§8、foundations-progress.md I-1、
  infinity-core-F1.md 冒頭、infinity-core-F1b.md の引き継ぎ・凍結点。
- 順序：a③ Ncomp → a④ 元の普遍三角形 → b 全錐・保存・有限形状帰納・公開。

## 現在地

a③ は未完。a④・b は未着手。一般交換の仮定はまだ除去していない。
凍結点の無条件な二評価因子式を、新規の
`coherentColimitApexZeroCompositeValue_heq_composite_iff` と
`coherentColimitApexZeroCompositeValue_heq_triangle_iff` で元の Ncomp へ接続した。
これは帰着であり、帰着先の指定値の合成則の証明ではない。

新規 `PointedRightFamilyFixedEvaluation` は動く全点への固定射評価と、
その指定点同型の評価作用を同じ固定射の後合成へ値まで同定する。
新規 `PointedValueFamilyTwoStage` は元の第一比較の評価像、元の第二比較、
`coherentKanRightCompositionTransport_movingIso` の像を貼った比較と、
合成射の元の指定比較を同じ型に置く。両比較の一致は未証明。

新規 `CoherentSimplexLastPost*`・`CoherentSimplexAppendMorphism` は、
coherent 単体の最後への指定後合成と、一辺の付け足しを選択なしに構成する。
旧面の全 Hom の厳密な回収と、二回の後合成と合成射の一回の後合成の
全 Hom ごとの一致 `coherentSimplexLastPost_comp` を証明した。
元の合成 prism との照合と Ncomp の指定値への移送はまだ行っていない。

## 次の工程

1. 指定値の合成則を証明する。元の二固定射 f,g に対する
   `pointedHomTwoMorphismEvaluationComparison f g` と
   `pointedHomCompositeMorphismEvaluationComparison f g` の HEq が具体的な残件。
   `coherentColimitApexZeroCompositeValue_heq_triangle_iff` で元の Ncomp を回収する。
2. `pointedRightFamilyEvaluation_comp` は端点の等式であり、指定比較の合成則ではない。
   `pointedValueFamilyTwoStageIso` と `pointedValueFamilyCompositeIso` の等式も
   まだ証明していない。ここを定義や新たな入力仮定で隠さない。
3. 幾何的には元の coherent 合成四角形と実 pointed prism の合成整合が要る。
   左値比較は `pointedHomMorphismValueComparison_heq_prism`、右値比較は
   `pointedValueFamilyTransportIso_at_right` に戻せる。
   比較を新しく選び直さず、同じ指定類で貼る。
   直近の次手：`coherentCompositionSimplex σ τ t` の最後の対象の後合成を
   `coherentSimplexLastPost` に値まで同定する（τ を同じ固定 g で後合成）。
   `coherentCompositionHom_*` の既存の正規化座標と
   `eComp_eHomWhiskerLeft` を使えば元の全 Hom に沿って比較できる。
   この照合を元の合成 prism の固定最終射の高次整合へ接続する。
4. Ncomp が閉じた後だけ、既存の Nlong と
   `spaceCompositionZero_morphism_coherence` から a④ へ進む。

## 検証

- 新規三モジュールを対象ビルドする。
- 専用監査は宣言元が FilteredExchange 以下の全読込宣言・生成宣言を選別し、
  依存公理が propext・Classical.choice・Quot.sound のみであることを検査する。
- 対象ビルド：7199 jobs で通過。
- 再監査：9142 宣言で通過。固定評価補題の証明を既存の
  `functorIsoLiftRight_postcomp_heq_map` を使う形へ整理した後も通過。
- 高次整合の構成：追加六モジュールの対象ビルド 1694 jobs、専用監査
  9193 宣言で通過。既存の三構成の証明と同じく標準三公理のみ。
- 既存集約・既存監査・他レーンのファイルは編集していない。
- 閉じたら公開名を Ind I-2 d へ渡す。上限で未完なら不足をここへ記録して停止する。
