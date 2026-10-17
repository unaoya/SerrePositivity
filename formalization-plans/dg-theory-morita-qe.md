# U16b・U16d：擬同値・Perf・係数変更の担当記録

正本は `dg-theory.md` §15.6。任意可換環、非有界cochain複体、dの次数+1、
ホモトピー次数−1、Mathlib Enrichedの主モデルを維持する。
主導来圏の本体は既存 `dgFunctorDerivedEquivalence` を再利用し、再実装しない。

## 状態と担当境界（2026-10-17）

| 項目 | 状態 |
| --- | --- |
| U16b：導来同値本体・延長/制限・unit/counit | 既存APIあり。`Checks.DGFunctorDerivedEquivalence` ビルド成功、2768 jobs、主要18宣言は標準3公理のみ |
| U16b：実際の随伴shift・三角性・Perf・U13/U14比較 | 接続を実装・検証中 |
| 積dg圏上の擬同値 | 既存 `derivedBimoduleRestrictionEquivalence` の `localHomKFlat A C`・`localHomKFlat A D` を保持する。無条件化しない |
| U16aグラフ作用との計算比較 | 初回確認時はAPI節未作成。その後「U16a 公開 API」節を確認。kernelは右E・左D。通常作用を先に接続し、主導来作用の実装を待って関手自然同型へ進む |
| U16d：Perf・係数変更・合成自然性 | U16a公開APIの「型のみ確定」を確認したため着手可能。`derivedTensorBaseChange` のhPN・hP'を保持する。主導来作用の未実装部分を証明済みとは扱わない |
| 中心作用 | 保留。今回の実装対象にしない |

新規Leanファイルは `Morita/QuasiEquivalence*`・`Perfect*`・`ScalarExtension*` のみ。
他担当のKernel・Adjunction・Coherence・Criterion・Verdier・Quotient系列、
既存Endomorphism/Perfectの公開APIの型は変更しない。
引用は追加しない。DG-MOR等が必要になれば採用せず停止・報告する。

## U16b.1：既存の導来同値のshift・三角性

- `Morita/QuasiEquivalenceTriangles.lean`：既存 `dgFunctorDerivedEquivalence` の順逆に
  既存の導来延長・制限の整数shiftをそのまま使い、同値のCommShiftと三角性を証明した。
  別に選び直した逆関手のshiftで既存の制限shiftを置き換えていない。
- 単位・余単位も元の導来随伴の自然変換であり、それぞれのshift整合性を監査した。
- `Morita.QuasiEquivalenceTrianglesChecks` ビルド成功（2599 jobs、警告なし）。
  主要6宣言の公理は `propext`, `Classical.choice`, `Quot.sound` のみ。

## U16b.2：既存の延長・制限の主Perfへの制限

- `Morita/PerfectQuasiEquivalence.lean`：U13のPerfの最小性と、既存の
  `dgDerivedExtension_representable_essImage`・導来単位を使い、擬同値に沿う制限のPerf保存を証明した。
  任意dg関手の延長のPerf保存は既存 `dgDerivedExtension_perfect` を再利用した。
- 順逆それぞれのPerf保存・反映、実際の制限関手二つと主導来包含の正方形、
  `quasiEquivalencePerfectEquivalence` を構成した。単位・余単位の包含像は元の導来単位・余単位と一致する。
- `Morita.PerfectQuasiEquivalenceChecks` とU16b.1の合同ビルド成功（2601 jobs、警告なし）。
  新規主要10宣言の公理監査は標準3公理のみ。

## U16b.3：主Perf制限のshift・三角同値と包含正方形

- `Morita/PerfectQuasiEquivalenceTriangles.lean`：実際の延長・制限の主Perf制限に
  元の導来関手と整合するshiftを与えた。順逆の包含自然同型・単位・余単位のCommShiftと
  主Perf同値の三角性、順逆それぞれの三角形関手の包含正方形を証明した。
- 単位の整合性は、包含後の単位を元の導来単位・包含自然同型・associatorの合成として計算し、
  忠実な包含で反映した。充満部分圏のshiftを定義展開で同一視していない。
- `Morita.PerfectQuasiEquivalenceTrianglesChecks` ビルド成功（2601 jobs、警告なし）。
  主要12宣言の公理監査は標準3公理のみ。
- コミットは自分のパスだけを指定している。U16b.1直後は別チャットのcommitがHEADになったため、
  自分のhash `33b14987` のstatも個別に照合した。他人のファイルの取り込みはない。

## U16b.4：U16aの通常graph作用と任意射影解像度の計算

- 公開API節で向きと型が固定された `Morita.kernelTensor`・`kernelTensor_graph` を読み取り専用で使う。
  `Morita/QuasiEquivalenceGraph.lean` は任意射影解像度Rに対し、既存導来延長と
  通常graph作用をRで計算した主局所化像の同型を与える。
- この計算にはFの擬同値性・localHomKFlatは不要。元の導来対象がPerfなら計算像もPerfとなる。
  これは主導来kernel作用との関手自然同型の完成を意味しない。後者は公開された主導来作用の実装後に行う。
- `Morita.QuasiEquivalenceGraphChecks` 独立対象ビルド成功（2801 jobs、警告なし）。
  主要2宣言の公理監査は標準3公理のみ。

## U16b.5：U13の小さいdg enhancementのH⁰比較

- `Morita/PerfectEnhancementComparison.lean`：U13の小さい主enhancementのH⁰同値を用い、
  実際の導来延長の主Perf制限を小さいH⁰間へ運んだ。両側のU13比較との自然な正方形、
  そのshift整合性と三角形関手の正方形を証明した。
- 順逆のshift、同値のCommShiftと三角性も監査した。このH⁰の運搬を新しいdg関手の構成とは呼ばない。
  U16bのdg由来の証拠は、元の入力FのHomQuasiIso・H⁰本質的全射と、既存延長・制限の実際の計算である。
- `Morita.PerfectEnhancementComparisonChecks` ビルド成功（2612 jobs、警告なし）。
  主要8宣言の公理監査は標準3公理のみ。

## U16b.6：積dg圏のPerf制限と既存bimodule制限

- `Morita/QuasiEquivalenceProducts.lean`：積dg圏のopposite上のPerfについて、
  既存の実際の制限を順方向とする同値と、主導来包含・`bimoduleRestrictionModuleDerived` の正方形を構成した。
- 擬同値F・Gに加えて、既存 `derivedBimoduleRestrictionEquivalence` と同じ
  `localHomKFlat A C`・`localHomKFlat A D` を明示して受け取る。
  一般のtensorが擬同型を保つことや、積の擬同値の無条件性は仮定しない。
- `Morita.QuasiEquivalenceProductsChecks` ビルド成功（2706 jobs）。
  既存2宣言・新規2宣言の公理監査は標準3公理のみ。
  依存先のdocstring整理による行長警告が再生されたが、自分の新規ファイルに警告・エラーはない。

## U16b.7：U14再構成Hom・tensorとの主Perf/主導来比較

- `Morita/QuasiEquivalenceEndomorphismComparison.lean`：擬同値に沿う実際の導来延長の後に、
  指定されたU14対象GのHomを適用する主Perf同値を構成した。
  その主導来包含正方形は、元の延長と元の再構成Homの合成に自然同型となる。
- 逆経路は元のU14再構成tensorの後の実際の制限であり、選んだ合成同値の逆への自然同型を与えた。
  Hom・tensor両経路の包含正方形は整数shiftと整合し、三角形関手の正方形も構成した。
- 主Perf側にはGのthick生成を明示し、全導来同値にはさらにGのcompact生成を明示した。
  全導来同値の順逆は延長⋙Hom・tensor⋙制限であり、主Perfとの正方形を公開した。
  制限したGのendomorphism代数を無条件に同一視する主張は含めない。
- `Morita.QuasiEquivalenceEndomorphismComparisonChecks` ビルド成功（2655 jobs）。
  主要14宣言の公理監査は標準3公理のみ。自分のファイルの警告・エラーは0件。
