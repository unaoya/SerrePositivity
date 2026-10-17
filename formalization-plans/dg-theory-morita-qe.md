# U16b・U16d：擬同値・Perf・係数変更の担当記録

正本は `dg-theory.md` §15.6。任意可換環、非有界cochain複体、dの次数+1、
ホモトピー次数−1、Mathlib Enrichedの主モデルを維持する。
主導来圏の本体は既存 `dgFunctorDerivedEquivalence` を再利用し、再実装しない。

## 状態と担当境界（2026-10-17）

| 項目 | 状態 |
| --- | --- |
| U16b：導来同値本体・延長/制限・unit/counit | 既存APIあり。`Checks.DGFunctorDerivedEquivalence` ビルド成功、2768 jobs、主要18宣言は標準3公理のみ |
| U16b：実際の随伴shift・三角性・Perf・U13/U14比較 | U16b.1–10で実装・合同ビルド・公理監査済み。主導来graph比較を含め担当範囲を受入済み |
| 積dg圏上の擬同値 | 既存 `derivedBimoduleRestrictionEquivalence` の `localHomKFlat A C`・`localHomKFlat A D` を保持する。無条件化しない |
| U16aグラフ作用との計算比較 | U16b.10でkernel変数の主局所化上の実際の作用との自然同型、随伴・単位・余単位・shift・三角性・Perfを検証済み |
| U16d：Perf・係数変更・合成自然性 | U16d.1–26の明示条件下の実装範囲を受入済み。この受入範囲でU16dを完了とする。保留事項・再開条件・公開入口は「U16d最終受入記録」を参照 |
| 中心作用 | 保留。今回の実装対象にしない |

新規Leanファイルは `Morita/QuasiEquivalence*`・`Perfect*`・`ScalarExtension*` のみ。
他担当のKernel・Adjunction・Coherence・Criterion・Verdier・Quotient系列、
既存Endomorphism/Perfectの公開APIの型は変更しない。
引用は追加しない。DG-MOR等が必要になれば採用せず停止・報告する。

以下の各実装節の「未完」「未受入」は、その単位の検証時点の履歴である。
現在のスコープと完了判定は「U16d最終受入記録」を正とする。

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

## U16d.1：Perf制限の射・自然変換・恒等・合成の関手性

- U16aの公開型が「型のみ確定」以上になったことを確認して着手した。
  `Morita/PerfectFunctoriality.lean` は既存主導来関手TのPerf保存を明示して主Perfへ制限し、
  自然変換・自然同型を制限する。自然変換の恒等・垂直合成を保ち、制限の恒等・合成同型を構成した。
- 二つの自然変換の水平合成と合成比較の可換図式も証明した。
  exactなTのPerf保存を確認するには代表加群の像のPerf性だけで十分であることを、U13の最小性から証明した。
- これはkernelに固有の主導来作用やその合成比較の存在の代用ではない。
  それらが実装された後、同じ保存条件・自然同型をこのアダプタへ適用する。
- `Morita.PerfectFunctorialityChecks` ビルド成功（2455 jobs、警告なし）。
  主要10宣言の公理監査は標準3公理のみ。

## U16d.2：係数変更の二変数モデルと実際のU12f比較

- `Morita/ScalarExtensionTensorModels.lean`：右加群・左加群の積圏上に、balanced tensor後の
  導来係数変更と、両加群の係数変更後のbalanced tensorを二つの実際の関手として構成した。
  既存の自然な比較射を用い、hPN・hP'を満たすモデルの充満部分圏上で自然同型を与えた。
- hPNはA上のbalanced tensorのK-flat性、hP'は係数変更した右加群の相対K-flat性であり、
  φのflatnessや自動的な条件へ置き換えない。モデルの射は両変数の全ての閉零射である。
- 任意射影解像度Pについて、実際の `derivedTensorBaseChange φ D P N hPN hP'` が
  この自然同型と前後の解像度計算同型の合成になる正方形を証明した。
  主導来kernel作用への適用・kernel合成との比較はまだ未完である。
- `Morita.ScalarExtensionTensorModelsChecks` ビルド成功（2903 jobs、警告なし）。
  主要7宣言の公理監査は標準3公理のみ。

## U16d.3：非flatな導来係数変更の主Perf保存

- `Morita/ScalarExtensionPerfect.lean`：任意の環準同型φに対し、既存の実際の
  `ScalarExtension.derivedExtension φ D` が指定生成集合からの主Perfを保存することを証明した。
  U14の射影的perfect代表の係数拡大と、U12fの任意射影解像度計算を再利用している。
- 指定生成集合Sを `scalarPerfectGenerators φ D S` に移す実際の主Perf制限と、
  両主導来包含との自然同型を公開した。φのflatness・HomのlocalHomKFlatは追加しない。
- `Morita.ScalarExtensionPerfectChecks` ビルド成功（3068 jobs、警告なし）。
  主要4宣言の公理監査は標準3公理のみ。

## U16b.8：自然なgraphモデルからの比較の復元

- `Morita/QuasiEquivalenceGraphNaturality.lean`：任意の射影解像度族Rについて、
  通常graph作用による自然なモデルと既存導来延長の前合成との自然同型を構成した。
  元の加群の射と選んだliftに関する計算自然性も明示した。
- 指定関手Kが同じモデルを自然に計算するという自然同型eKを入力すると、
  主局所化の前合成の完全忠実性でKと既存導来延長の自然同型を復元する。
  前合成後の計算式・その式による比較の一意性・Perf保存とPerf上の比較も証明した。
  Fが擬同値ならKの同値性は既存の同値から運び、再実装しない。
- eKは必要な自然性を明示した入力であり、対象ごとの同型だけから作ったとは主張しない。
- `Morita.QuasiEquivalenceGraphNaturalityChecks` ビルド成功（2803 jobs、警告なし）。
  主要9宣言の公理監査は標準3公理のみ。

## U16b.9：公開された実際の通常kernel導来作用へのgraph接続

- U16aが `KernelResolution`・その監査・通常kernelの主導来作用を公開したことを確認した。
  `Morita/QuasiEquivalenceGraphAction.lean` は実際の `kernelDerivedTensorOnBimodule` を使い、
  graph作用と既存 `dgDerivedExtension` の関手自然同型を構成した。
- 既存 `dgFunctorDerivedEquivalence` の順関手はこの実際のgraph作用であることを証明し、
  graph比較のshift整合性・三角性・Perf保存・Perf上の比較を監査した。
  U16b.8の自然モデルから復元した比較も、この実際のgraph自然同型と一致する。
- 通常kernel引数Pに対する主導来作用の比較はここで完了した。
  `Kernel A D E`（kernel変数自体の主局所化）上の作用との比較は、その降下APIの実装後に行う。
- `Morita.QuasiEquivalenceGraphActionChecks` ビルド成功（2805 jobs、警告なし）。
  主要8宣言の公理監査は標準3公理のみ。

## U16d.4：係数変更正方形のPerf制限・自然性・合成整合性

- `Morita/ScalarExtensionPerfectSquares.lean`：主導来圏上の指定された自然な係数変更正方形を入力し、
  U16d.3の実際の非flat係数変更とU16d.1の実際のPerf制限との正方形へ移した。
  主導来包含後の式は元の正方形そのものであり、関手間の自然変換に対する可換式も保つ。
- 二つの主導来係数変更正方形を合成してからPerfへ制限する経路と、
  二つのPerf正方形を合成し、実際のPerf制限の合成同型で比較する経路が一致することを証明した。
- kernel固有の正方形の存在は入力eとして明示する。U12fのhPN・hP'を自動化したり省略したりする結果ではない。
  実際のkernelの評価計算でeを構成する接続は、U16aの該当API実装後に行う。
- `Morita.ScalarExtensionPerfectSquaresChecks` ビルド成功（3071 jobs、警告なし）。
  主要6宣言の公理監査は標準3公理のみ。

## U16d.5：通常kernelの各列のperfect性からの実際のPerf作用

- `Morita/PerfectKernelImage.lean`：dg加群関手の代表加群像がperfectなら、
  finite cellの像がperfectであることを有限操作の帰納法で証明した。
  射影的perfect代表の導来retractを実際の射へ持ち上げ、H⁰で運ぶことでretractにも拡張した。
- 通常kernel Pの各列 `P.rightAt d` の主局所化像がperfectであるという条件の下で、
  公開済みの実際の `kernelDerivedTensorOnBimodule` がPerfを保存することを証明した。
  主Perfへの実際の制限 `perfectKernelAction` と主導来包含との正方形を構成した。
- Yoneda右単位と既存の任意入力射影解像度計算を使用した。
  kernelの射影性、入力への追加flatness、localHomKFlatは仮定しない。
  kernel変数の主局所化上の作用への移送は、その降下APIの実装後に行う。
- `Morita.PerfectKernelImageChecks` ビルド成功（2741 jobs、警告なし）。
  主要6宣言の公理監査は標準3公理のみ。

## U16d.6：実際のkernel作用の評価とU12dの全射自然な比較

- `Morita/PerfectKernelEvaluation.lean`：任意kernelについて全Hom写像・閉零射の評価を計算し、
  通常作用の評価をbalanced tensor関手と自然同型で比較した。
- 同じ計算をH⁰へ降ろしてから入力解像度関手で前合成することで、任意の入力射影解像度族について
  `kernelResolutionDerivedTensor ⋙ moduleDerivedEvaluation` とU12dの導来tensorの自然同型を構成した。
  標準作用 `kernelDerivedTensorOnBimodule` と実際のPerf制限にも適用した。
- 対象ごとの計算ではなく、全ての主導来入力射に自然な関手比較である。
  既存Endomorphismのファイルは読み取り専用で使用し、その評価比較の証明を任意kernelへ一般化した。
- `Morita.PerfectKernelEvaluationChecks` ビルド成功（2750 jobs、警告なし）。
  主要9宣言の公理監査は標準3公理のみ。

## U16d.7：実際のkernel・Perf作用とU12f係数変更の評価正方形

- `Morita/ScalarExtensionKernelTensor.lean`：U16d.6の関手自然同型に導来係数変更を後合成し、
  実際のkernel作用とU12d計算の係数変更後の評価を、全入力射に自然に比較した。
- 任意の入力射影解像度Rと出力評価eについて、hPNとhP'を明示して
  `derivedTensorBaseChange` を接続した。実際のPerf作用からの版も公開した。
  φのflatness・入力の有界性・Homの局所K-flat性は追加していない。
- 係数変更後の終域はU12fの指定した右・左加群の導来tensorである。
  係数変更したkernel全体の主導来作用への束ね上げとkernel合成との比較は残項目として区別する。
- `Morita.ScalarExtensionKernelTensorChecks` ビルド成功（3230 jobs、警告なし）。
  主要5宣言の公理監査は標準3公理のみ。

## U16d.8：U16aのkernel合成比較を受け取る具体的Perfアダプタ

- `Morita/PerfectKernelComposition.lean`：公開型どおりの主導来作用族Actionと、
  実際の通常kernel作用の合成からAction(kernelCompose P Q)への自然同型eCompを明示して受け取る。
- P・Qの各列のperfect性から、合成kernelの作用のPerf保存を証明した。
  実際の二つのPerf作用の合成と、合成kernelの主Perf作用を比較する自然同型を構成し、
  主導来包含後の射が元のeCompの射そのものであることを証明した。
- kernelComposeは右E・左Dの順序を保ち、始域Dの `localHomKFlat A D` を明示する。
  eCompはU16aの不足APIを明示した入力であり、その存在を証明したという主張ではない。
  合成比較の自然性・coherence自体の入力はU16d.1・4と同じ制限で運ぶ。
- `Morita.PerfectKernelCompositionChecks` ビルド成功（2742 jobs、警告なし）。
  主要5宣言の公理監査は標準3公理のみ。

## U16d.9：実際の通常kernelの係数変更と全Hom付き評価

- `Morita/ScalarExtensionKernel.lean`：kernelのdg関手を係数変更し、ambient加群圏から
  実際の係数変更加群圏への既存dg関手と合成して `scalarKernel` を構成した。
- 右評価・値の係数変更との一致に加え、左評価が元の左加群の係数変更と一致することを
  **全Hom作用を含むdg関手の等式**として証明した。単なる成分の同型ではない。
- これは通常kernelの係数変更であり、任意のkernel準同型をunderived係数変更が保つとはしない。
- `Morita.ScalarExtensionKernelChecks` ビルド成功（2628 jobs、警告なし）。
  主要4宣言の公理監査は標準3公理のみ。

## U16d.10：係数変更した実際のkernel作用を終域とする評価比較

- `Morita/ScalarExtensionKernelAction.lean`：U16d.9の全Hom付き左評価等式により、
  U16d.7のU12f終域tensorを、係数変更した実際のkernelの主導来作用の出力評価と同定した。
  実際のPerf作用を始域とする版も構成した。
- hPN・hP'をそのまま明示して受け取る。sourceは出力評価複体の導来係数変更である。
  dg加群の導来係数変更と出力評価の交換を無条件に仮定するものではない。
- `Morita.ScalarExtensionKernelActionChecks` ビルド成功（3235 jobs、警告なし）。
  主要2宣言の公理監査は標準3公理のみ。

## U16b.10：主導来graph kernelの実作用・随伴・Perf・shift・三角比較

- U16a3の `KernelDerivedFunctor` が公開・検証済みとなったため、
  `Morita/QuasiEquivalenceDerivedGraph.lean` で通常kernel版の比較を実際の `kernelDerivedTensor` へ移した。
  `kernelGraph` の主導来作用と既存 `dgDerivedExtension` の関手自然同型を公開した。
- Fが擬同値ならこの主導来graph作用は同値であることを、既存の同値本体から証明した。
  随伴も元の延長–制限随伴を自然同型に沿って運び、単位・余単位の成分式を計算した。
- graph比較は整数shiftに整合し、実際のgraph作用の三角性・Perf保存・Perf上の比較も構成した。
  追加のlocalHomKFlat条件はない。積dg圏の擬同値の条件はU16b.6のまま保持する。
- `Morita.QuasiEquivalenceDerivedGraphChecks` ビルド成功（2808 jobs、警告なし）。
  主要10宣言の公理監査は標準3公理のみ。

## U16d.11：主導来kernelの列と全導来射に自然なPerf作用

- `Morita/PerfectKernelColumns.lean`：列の評価をbimoduleの指定主局所化へ降ろし、
  代表に依存しない `kernelColumnsPerfect` を定義した。
  代表加群への実際の主導来作用はこの列評価と同型になり、列のperfect性と作用のPerf保存の同値を証明した。
- 実際の `kernelDerivedTensor` の主Perf制限と包含正方形を構成した。
  perfectな列を持つ主導来kernelの充満部分圏からPerf作用関手の圏への関手を構成し、
  kernelの任意の主導来射・恒等・合成に対する自然性を証明した。
- 通常kernelの各列の条件はU16d.5の条件と一致する。局所Hom条件を追加していない。
- `Morita.PerfectKernelColumnsChecks` ビルド成功（2746 jobs、警告なし）。
  主要11宣言の公理監査は標準3公理のみ。

## U16d.12：主導来kernelの恒等と合成自然性のPerf制限

- `Morita/PerfectDerivedKernelCoherence.lean`：公開済みの `kernelIdentityIso` を使い、
  主導来対角kernelの各列のperfect性と、実際のPerf作用から恒等関手への自然同型を構成した。
  この恒等比較にはlocalHomKFlatを要求しない。
- 合成では `localHomKFlat A D` を保持し、主導来作用の比較同型 `eComp` を明示して受け取る。
  合成kernelの列のperfect性、Perf上の比較同型、その包含像が元の比較と一致することを証明した。
- 主導来kernelの任意の射による `perfectDerivedKernelMap` を公開した。
  元の合成比較の自然性 `hNat` を明示して受け取り、Perf制限の合成比較の自然性を証明した。
  これはU16aの未公開の合成比較やその自然性の存在証明を代替する主張ではない。
- `Morita.PerfectDerivedKernelCoherenceChecks` ビルド成功（2748 jobs、警告なし）。
  主要6宣言と追加の `perfectDerivedKernelMap` の公理監査は標準3公理のみ。

## U16d.13：U12fの実際の比較同型の左因子自然性

- `Morita/ScalarExtensionTensorNaturality.lean`：指定解像度族、任意の指定右射影解像度、
  相対K-flatな右モデルでの導来tensor計算同型について、左因子の全閉零射に対する自然性を証明した。
  既存の `moduleDerivedTensorLeftFunctor` が与える自然変換を使用する。
- U12fの実際の `derivedTensorBaseChange` 自体の左因子自然性を証明した。
  始点・終点のhPNと、係数変更後の右モデルのhP'を明示し、flat性や局所Hom条件で置き換えていない。
- hPN・hP'を両方保持する左因子の充満部分圏 `scalarTensorLeftModels` 上で、
  実際の導来tensorと実際の導来係数変更からなる二つの関手の自然同型
  `scalarTensorBaseChangeLeftIso` を構成した。その成分は元のU12fの比較同型と一致する。
- `Morita.ScalarExtensionTensorNaturalityChecks` ビルド成功（2905 jobs、警告なし）。
  主要9宣言の公理監査は標準3公理のみ。既存Derived/・Tensor/のソースは編集していない。
- この左因子自然性をkernel全体の作用の自然性と同一視する主張は含めていない。
  kernel作用評価の比較同型のkernel射に関する自然性、および出力dg加群の係数変更との交換は残る。

## U16d.14：実際の主導来kernel合成比較のPerf制限

- U16a6の公開記録と `Morita/CoherenceComposition.lean` を確認し、
  実装・検証済みの `kernelCompositionIso` をU16d.12の比較入力へ適用した。
- `Morita/PerfectDerivedKernelComposition.lean`：各列がperfectな二つのkernelについて、
  実際の主導来合成kernelの各列のperfect性と、実際のPerf作用の合成比較を構成した。
  比較同型eCompを外部から受け取る仮定は不要になった。localHomKFlatは始域Dだけを保持する。
- 包含後の比較射は公開済みの実際の `kernelCompositionIso` の射と一致する。
  kernel射に対する自然性はU16a側でも未完のため、その自然性図式hNatだけを明示して受け取り、
  実際のPerf合成比較の自然性へ移す。hNatや代表選択のcoherenceの無条件性は主張しない。
- `Morita.PerfectDerivedKernelCompositionChecks` ビルド成功（2754 jobs、警告なし）。
  主要4宣言の公理監査は標準3公理のみ。U16a担当ファイルは読み取り専用で利用した。

## U16d.15：kernel作用評価比較のkernel射自然性

- `Morita/PerfectKernelEvaluationNaturality.lean`：U16d.6の実際の評価比較を変更せず、
  そのH⁰成分を計算し、通常kernelの全閉零射に関する自然性を証明した。
- 任意の指定入力解像度族へ前置して全主導来入力へ移し、標準族の実際の作用について
  `kernelDerivedEvaluationIso_naturality` を証明した。
- `kernelDerivedEvaluationIso` は、通常kernelの圏から導来入力上の関手の圏への自然同型であり、
  kernel射と全導来入力射の両方に自然である。追加の局所Hom条件はない。
  U16d.13の左因子自然性を実際のkernel作用評価へ運ぶ際の不足していた比較を埋めた。
- `Morita.PerfectKernelEvaluationNaturalityChecks` ビルド成功（2754 jobs、警告なし）。
  主要6宣言の公理監査は標準3公理のみ。既存のU16d.6および他担当のソースは変更していない。
- 出力dg加群の係数変更と評価を交換する定理は、この比較からは無条件には得られない。

## U16d.16：通常kernelの係数変更の射関手性

- `Morita/ScalarExtensionKernelFunctor.lean`：実際の通常kernelの係数変更を、全Hom自然な
  閉零kernel射に対する `scalarKernelMap` と通常圏の関手 `scalarKernelFunctor` へ拡張した。
  左Dの全Hom自然性には既存の実際のHom係数変更比較の前後合成自然性を用いる。
- 値の評価式と `scalarKernelLeftEvaluationIso` を証明した。後者は左評価と係数変更が
  kernelの任意の閉零射にも自然に交換することを表す。
- `Morita.ScalarExtensionKernelFunctorChecks` ビルド成功（2641 jobs、警告なし）。
  主要4宣言の公理監査は標準3公理のみ。underived係数変更がkernel準同型を無条件に保つとは主張しない。
- U16d.15のコミット `0b816652` の直後のHEADは別担当の `97b86690` に進んでいた。
  自分のコミットIDのstatも照合し、担当4ファイルだけの収録と確認した。履歴変更は行っていない。

## U16d.17：kernel射に自然な実際の作用評価の係数変更

- `Morita/ScalarExtensionKernelBaseChangeNaturality.lean`：固定した入力Mと任意の指定右射影解像度R、
  出力評価eについて、hPN・hP'を満たす通常kernelの充満部分圏 `scalarKernelBaseChangeModels` を定義した。
  hPN・hP'を別のflat性・局所Hom条件で置き換えず保持する。
- 実際の通常kernelの主導来作用の評価を係数変更する関手と、
  実際に係数変更したkernelを導来係数変更後の入力に作用させて評価する関手を定義した。
  U16d.15のkernel評価自然性、U16d.16の左評価自然性、U16d.13のU12f自然同型を合成し、
  この充満部分圏上の自然同型 `scalarKernelBaseChangeIso` を構成した。
- 成分の計算式 `scalarKernelBaseChangeIso_hom_app` では、元のU12fの比較射をそのまま使用する。
  従ってkernelの任意の閉零射に自然な比較であり、kernelごとに独立に同型を選んだものではない。
- `Morita.ScalarExtensionKernelBaseChangeNaturalityChecks` ビルド成功（3241 jobs、警告なし）。
  主要6宣言の公理監査は標準3公理のみ。
- 始域は出力評価の複体の導来係数変更である。出力dg加群の導来係数変更との交換、
  kernel変数の主局所化への係数変更の降下、合成比較との図式は未完であり、ここでは主張しない。

## U16d.18：kernel作用のunderived係数変更をdg加群全体へ束ねる

- `Morita/ScalarExtensionKernelBalanced.lean`：通常のcoend係数変更と全Hom付き左評価比較を合成し、
  実際の係数変更後kernelの値への比較同型を定義した。純粋coend生成元上での値を計算した。
- `Morita/ScalarExtensionKernelBalancedModule.lean`：係数制限側で比較射を構成し、
  既存のKoszul符号付き右作用の生成元公式から、出力dg圏Eの全次数Hom作用との可換性を証明した。
  既存の加群係数変更–制限随伴で戻し、各評価で同型であることから
  実際のdg加群全体の同型 `scalarKernelBalancedIso` を構成した。
- この同型は `moduleExtension φ E (kernelTensor P M)` から
  `kernelTensor (scalarKernel φ P) (rightModule φ M)` へのunderived比較である。
  環準同型のflat性、局所Hom条件、hPN・hP'を要求しない。導来化後の無条件比較は主張しない。
- 二つの監査入口の合同ビルド成功（2644 jobs、警告なし）。主要16宣言の公理監査は標準3公理のみ。
  定義を値成分に整理し、資源上限を変更せず最終ソースを検証した。
- 次はこのunderived加群同型の入力射・kernel射に関する自然性と、導来計算との接続。
  U12fのhPN・hP'を保持し、出力の導来係数変更を通常モデルで計算する条件も別に検証する。

## U16d.19：実際のPerf合成比較の全導来kernel射自然性

- U16a9の公開記録と `kernelCompositionIso_naturality` を確認し、
  `perfectKernelCompositionIso_kernel_naturality` のhNat入力を実際の定理で埋めた。
  両kernelの任意の主導来射について、実際のPerf作用の水平合成と合成kernelの作用の正方形が可換する。
- 必要なlocalHomKFlatは始域Dだけを保持する。E・Bには追加せず、
  両kernelの列のperfect性は明示する。旧来の条件付きアダプタの型は変更していない。
- `Morita.PerfectDerivedKernelCompositionChecks` ビルド成功（2764 jobs、警告なし）。
  追加1宣言と既存4宣言の公理監査は標準3公理のみ。恒等・結合coherenceの完成とは扱わない。

## U16d.20：underived加群比較の入力自然性とH⁰降下

- `Morita/ScalarExtensionKernelBalancedNaturality.lean`：U16d.18の実際の加群同型が
  全閉零入力射に自然であることを証明し、`scalarKernelBalancedNatIso` に束ねた。
  値の比較では既存coend係数変更の両変数自然性と左因子射のtensor自然性を用いる。
- `Morita/ScalarExtensionKernelHomotopy.lean`：既存 `scalarModuleExtensionHomotopy` と
  主H⁰商の普遍性を使い、比較を全H⁰入力射に自然な同型へ降ろした。
  既存の係数変更ホモトピー関手から主導来値へ送る二つの経路も自然同型で比較した。
- 通常入力とH⁰入力の比較は任意環準同型に定義され、局所Hom条件は要求しない。
  これはH⁰上のunderived係数変更比較であり、導来係数変更関手との無条件同一視ではない。
- 二つの監査入口の合同ビルド成功（2797 jobs、警告なし）。主要7宣言の公理監査は標準3公理のみ。
  既存Endomorphism/・Derived/および他担当のソースは編集していない。

## U16d.21：dg加群全体の導来係数変更比較

- `Morita/ScalarExtensionKernelDerivedComparison.lean`：係数変更とkernel作用の既存増大を
  H⁰入力へ降ろし、両側の実際の導来関手から共通の計算モデルへの自然変換を構成した。
  増大比較の存在と可逆性を分離している。
- `scalarKernelDerivedBaseChangeIso` は、通常kernel Pの実際の主導来作用について
  `K_P ⋙ derivedExtension φ E ≅ derivedExtension φ D ⋙ K_(scalarKernel φ P)` を与える。
  全主導来入力射に自然であり、出力は評価ごとの複体ではなくdg加群全体である。
  一般形は出力モデルの増大の可逆性hAugと、標準右解像度族の係数変更後の相対K-flat性hP'を明示して受け取る。
- `scalarKernelDerivedBaseChangeIso_ofKFlatModels` では、出力圏の `localHomKFlat A E` と
  各標準右解像度tensorのhPNからhAugを証明し、hPN・hP'を保持した比較を構成した。
  hEは出力係数変更の増大を反転するための追加の十分条件である。入力Dの局所Hom条件や環準同型のflat性は追加しない。
  hPN・hP'だけから出力の導来係数変更と評価が無条件に交換するとは主張しない。
- 共通モデルへの二つの比較と係数変更同型の可換図式も証明した。
  `Morita.ScalarExtensionKernelDerivedComparisonChecks` ビルド成功（3241 jobs、警告なし）。
  主要15宣言の公理監査は標準3公理のみ。既存Derived/・Tensor/・他担当ソースは編集していない。

## U16d.22：実際の導来係数変更正方形のPerf制限

- `Morita/ScalarExtensionKernelPerfectSquare.lean`：既存の射影モデルの係数変更計算と
  `scalarRepresentable_eq` から、実際の導来係数変更の代表加群での計算を構成した。
  代表入力でのkernel作用の列計算も既存の主導来列評価へ接続した。
- 元のkernelの列のperfect性とU16d.21の実際の導来比較から、係数変更後のkernelの列のperfect性を証明した。
  係数変更後の列のperfect性を独立の仮定として要求していない。
- 実際の `perfectKernelAction` と `scalarExtensionPerfectFunctor` の正方形を構成し、
  主導来包含後の比較射がU16d.21の比較射そのものになる図式を証明した。
  一般形はhAug・hP'、K-flatモデル版は出力hE・hPN・hP'を明示する。
- `Morita.ScalarExtensionKernelPerfectSquareChecks` ビルド成功（3281 jobs、警告なし）。
  主要6宣言の公理監査は標準3公理のみ。既存のEndomorphism/・Perfect/のAPIは変更していない。

## U16d.23：kernel射に関する係数変更比較の通常・H⁰自然性

- `Morita/ScalarExtensionKernelMapNaturality.lean`：左評価の比較、balanced tensorの比較、
  dg加群値の比較および入力に関する自然同型が、通常kernelの全閉零射に自然であることを証明した。
- `Morita/ScalarExtensionKernelHomotopyNaturality.lean`：H⁰比較の通常入力上の成分式を計算し、
  kernel射自然性をH⁰および主導来値のH⁰関手へ降ろした。局所Hom条件・環準同型のflat性は不要。
  U16d.21の増大比較と合成して導来係数変更正方形のkernel射自然性へ接続する準備であり、
  この単位だけでkernel変数の主局所化への係数変更の降下を主張しない。
- 二つの監査入口と公開入口の合同ビルド成功（3438 jobs、終了コード0、警告・エラーなし）。
  主要8宣言の公理監査はすべて標準3公理のみ。検査上限の変更は残していない。
  新規sorry・admit・axiom・引用はなく、他担当ファイルと既存公開APIの型は変更していない。

## U16d.24：実際の導来・Perf係数変更正方形のkernel射自然性

- `Morita/ScalarExtensionKernelDerivedNaturality.lean`：既存kernel増大の自然性をH⁰へ接続し、
  共通計算モデルの射と左右の増大比較のkernel射自然性を証明した。
  右増大比較の可逆性で消去して、U16d.21の実際の導来係数変更同型のkernel射自然性を導いた。
  一般形は両kernelのhAugとhP'を保持し、K-flatモデル版は出力hE・両kernelのhPN・hP'を明示する。
- `Morita/ScalarExtensionKernelPerfectNaturality.lean`：通常kernel射の実際のPerf作用への制限と
  包含図式を構成し、既存のPerf正方形アダプタを適用してU16d.22の実際の正方形の自然性を証明した。
  K-flatモデル版も公開し、係数変更後の列のperfect性は既存の比較から導く。
- 二つの監査入口と公開入口の合同ビルド成功（3440 jobs、終了コード0、警告・エラーなし）。
  主要10宣言の公理はすべて標準3公理のみ。新規sorry・admit・axiom・引用はない。
  この単位は通常kernel間の全閉零射についての結果である。
  kernel変数の主局所化への係数変更の降下、U12fの成分同定とkernel合成図式は引き続き残る。

## U16d.25：主導来kernel変数の非flatな係数変更関手

- `Morita/ScalarExtensionKernelProduct.lean`：積dg圏の右加群表示の値比較を用い、
  標準cylinderの射影がkernelの係数変更後も擬同型になることを証明した。
  その射影だけを反転して全dg自然な境界を同一視し、積上のH⁰から主導来kernelへの関手を構成した。
  underived係数変更による任意擬同型の保存は使っていない。
- `Morita/ScalarExtensionKernelLocalization.lean`：既存の積表示の主導来同値と
  射影解像度関手を合成し、全主導来kernel射に作用する `scalarKernelDerivedExtension` を構成した。
  任意の証明付き積上射影解像度での計算、全閉零kernel射に自然な計算同型、
  解像度族変更の自然同型と自己・推移則も公開した。局所Hom K-flat性も環準同型のflat性も不要。
- 二つの監査入口と公開入口の合同ビルド成功（3442 jobs、終了コード0、警告・エラーなし）。
  主要14宣言の公理は標準3公理のみ。新規sorry・admit・axiom・引用はない。
  主導来kernel係数変更関手そのものの構成と、U16d.21–24のモデル条件付き正方形を
  この関手へ移すことは分けている。後者とU12f成分同定・合成図式は引き続き未完。

## U16d.26：主導来kernel係数変更の通常モデルへの自然な増大

- `Morita/ScalarExtensionKernelLocalizationAugmentation.lean`：任意の積上射影解像度族の
  増大比較を全閉零kernel射に自然な変換とし、U16d.25の主導来kernel係数変更から
  通常kernelの係数変更への実際の自然変換を構成した。成分の解像度計算式も公開した。
- 比較射の構成と可逆性を分離し、係数変更後の積上モデルの増大がkernel擬同型になるhπを
  明示して可逆性を証明した。hπを無条件に使わず、U12fのhPN・hP'で代用していない。
- 監査入口と公開入口のビルド成功（3442 jobs、終了コード0、警告・エラーなし）。
  主要5宣言の公理は標準3公理のみ。新規sorry・admit・axiom・引用はない。

## U16c担当追加（2026-10-17）

- U16d受入後の担当として、一般kernelのMorita判定を主導来圏全体へ広げる。
  右随伴・unit/counitは扱わず、compact生成を明示する。
- Perf判定と作用の三角性は他担当の `Morita/CriterionPerf*` を使用する。
  公開前はその結論を明示した仮定として受け取れる。新規実装は `Morita/CriterionDerived*` に置く。
  他担当のKernel*・Adjunction*・Coherence*・CriterionPerf*は編集しない。
- U14cの `moduleLocalizing_all` は既に多対象dg圏を扱い、perfect対象を含む余積閉三角部分圏の
  全対象への拡張を提供する。これを再利用し、作用の余積保存・局所化帰納・本質的全射へ接続する。
  無限個の生成元の直和のcompact性や、thick生成だけから全導来圏同値を結論する仮定は追加しない。
- 右随伴を使わない拡張では、まずHom比較を局所化帰納で拡張して充満忠実性を得る。
  充満な三角関手の本質的像の三角閉性はMathlibの既存instanceを利用できる。
  本質的像の余積閉性とcompact生成を組み合わせる段階を、右随伴・unit/counitと分離する。
  これは利用APIと証明方針の確認であり、U16cの実装完了を意味しない。

## U16c.1：余積保存・Hom比較の余積閉性と条件付き本質的全射

- 公開入口は `Morita/CriterionDerived.lean`。新規実装はすべて `CriterionDerived*` に置いた。
  U16dの受入状態は変更していない。以下は新担当の条件付き拡張に使う部品であり、
  U16c全体の受入・全主導来圏同値の完成を主張しない。
- `CriterionDerivedCoproducts.lean`：U16aの既存の実際のkernel作用の余積保存を再利用した。
  その証明は射影入力族・tensor・主局所化の余積計算によるもので、一般導来右随伴を使わない。
  余積を保存する関手の本質的像の余積閉性も、離散族の対象選択と余積比較から証明した。
- `CriterionDerivedGeneration.lean`：u-small生成族の各対象のcompact性と、
  u-small余積で閉じる同型閉三角部分圏による全対象の生成を
  `CriterionDerivedCompactGeneration` の別々の成分として明示した。
  充満な三角関手の本質的像がこの生成族を含む場合の本質的全射を証明した。
  U13dのcompact⇒Perfにより、Perf上の本質的全射から同じ結論を得る版と、実際のkernel作用の版を公開した。
  三角性・充満性はこの段階では明示した入力であり、Perf判定から全対象の充満忠実性を導いたことにはしない。
- `CriterionDerivedHomCoproducts.lean`：固定したcompact始域とそのcompactな像について、
  Hom比較の単射性・全射性・全単射性が終域の余積で保たれることを証明した。
  始域側の余積でも同じ三性質を証明した。こちらはcompact性・加法性も不要である。
  生成族の無限直和をcompactと仮定する議論は一切使っていない。
- 三つの監査入口と公開入口の合同ビルド成功（2795 jobs、終了コード0、警告・エラーなし）。
  主要13宣言の公理はすべて標準3公理のみ。新しいsorry・admit・axiom・引用はない。
  他担当のKernel*・Adjunction*・Coherence*・CriterionPerf*は読んだだけで編集していない。
- 次の必須接続は、Hom比較のshift・錐に関する閉性、両変数の局所化帰納による全対象の充満忠実性、
  CriterionPerf*の実際のPerf判定との接続、明示したcompact生成下の全導来圏同値である。
  一般右随伴との一致・unit/counitは他担当に残す。

## U16c.2：Hom比較の錐・shift閉性と全対象の充満忠実性

- `CriterionDerivedHomTriangles.lean`：二つのHom完全列を追い、最初の二頂点とそのshiftの
  Hom比較の全単射性から第三頂点での全単射性を証明した。同型不変性と零対象の場合も公開した。
- `CriterionDerivedHomLocus.lean`：固定始域から全整数shiftへのHom比較が全単射となる
  終域のクラスを定義し、同型・shift・三角形・u-small余積での閉性を証明した。
  余積閉性に使うのは固定始域とその像のcompact性であり、生成族の直和のcompact性ではない。
- `CriterionDerivedFullyFaithful.lean`：明示したcompact生成を用いて終域変数を拡張し、
  次いで始域変数を拡張して全主導来対象間のHom比較の全単射性と充満忠実性を構成した。
  入力は実際の三角関手・余積保存・Perf保存・Perf対象間のHom比較である。
  始域帰納では既存の `brownHomComparison_all` を指定射が恒等射の場合に適用した。
  同補題は指定射だけに関する一般の局所化帰納であり、右随伴・表現対象の存在は入力にも証明にも使わない。
- 三監査入口と公開入口の合同ビルド成功（2842 jobs、終了コード0、警告・エラーなし）。
  主要13宣言の公理は標準3公理のみ。新規sorry・admit・axiom・引用はない。
  実際のPerf同値を入力とする形への接続と、本質的全射を合わせた全導来圏同値への統合を残す。

## U16c.3：実際のPerf同値から全主導来圏同値への拡張

- `CriterionDerivedEquivalence.lean`：実際のPerf制限の同値から、元の関手のPerf対象間の
  Hom比較とPerf対象を含む本質的像を取り出した。U16c.1–2の両変数帰納と本質的全射を統合し、
  両側の明示したcompact生成下での全主導来圏同値を構成した。
- 一般kernel版では、余積保存と三角性を既存の実際の作用のAPIから供給し、順関手を
  `kernelDerivedTensor` そのものに保った。型にPerf制限の同値性と両側のcompact生成を明示する。
  本質的全射の最終段階で全導来関手の充満性を仮定せず、U16c.2で得た充満性を使う。
- `criterionDerivedKernelEquivalenceOfPerfWitness` は、他担当の
  `CriterionPerfEquivalenceWitness` を直接受け取る。列のperfect性と実際の制限の同値性は
  この証拠の公開APIから得る。Perf包含との図式は証拠の元の比較をそのまま保持する。
  一般導来右随伴との一致・unit/counitの比較は構成していない。
- 監査入口と公開入口の合同ビルド成功（2847 jobs、終了コード0、警告・エラーなし）。
  主要10宣言の公理は標準3公理のみ。新規sorry・admit・axiom・引用はない。
- U16cの全7監査入口・公開入口・従来のQuasiEquivalence入口の9対象も合同ビルド成功
  （3477 jobs、終了コード0、警告・エラー0件）。担当36宣言の公理は標準3公理のみ。
  担当15 Leanファイルに新規sorry・admit・axiom・デバッグtraceはない。
- **Perf判定の結論を明示した入力とする全導来拡張本体は実装済み。**
  他担当の記録 `dg-theory-morita-criterion.md` を再確認したところ、三条件の全Hom擬同型比較と
  実際の主作用の全shift射比較の同定、および三条件からPerf同値への最終定理は未完である。
  その最終公開APIからこの拡張への直接の接続は残す。三条件⇒全主導来同値の完成はまだ主張しない。
  U16dの未受入状態も変更していない。

## U16c.4：元の三条件と明示したPerf十分性入力による入口

- `CriterionDerivedConditions.lean`：他担当の `CriterionPerfConditions` を変更せずに受け取り、
  三条件から実際の `CriterionPerfEquivalenceWitness` を与える十分性定理の型を
  `CriterionDerivedPerfSufficiency` として定義した。これは入力命題の名前であり、成立の宣言ではない。
- `criterionDerivedKernelIsEquivalenceOfConditions` と
  `criterionDerivedKernelEquivalenceOfConditions` は、この十分性を `hPerf` として明示して受け取り、
  元の三条件と両側のcompact生成から全主導来圏同値を構成する。順関手が実際のkernel作用であることも証明した。
  `hPerf` の証明を新しいaxiom・引用・暗黙のinstanceで補ってはいない。
- 対象ビルド成功（2851 jobs）。さらに全8監査入口・CriterionDerived入口・従来の
  QuasiEquivalence入口の10対象の合同ビルド成功（3482 jobs、終了コード0、警告・エラー0件）。
  担当40宣言の公理は標準3公理のみ。担当17 Leanファイルに新規sorry・admit・axiom・デバッグtraceはない。

### 条件付き契約の要件監査

| 依頼事項 | 現在の証拠 |
| --- | --- |
| 任意kernelの実際の作用の余積保存 | `criterionDerivedKernelPreservesCoproducts`。射影入力とtensorによる既存証明を再利用し、局所Hom・kernel列の射影性を追加しない |
| 三角性を他担当から使用 | 一般kernelの最終定理で `criterionPerfKernelCommShift`・`criterionPerfKernelIsTriangulated` を使用 |
| Hom比較のshift・錐・余積閉性 | `CriterionDerivedHomLocus` の各instanceとcoproduct補題。Hom完全列を直接使う |
| 両変数の局所化帰納・充満忠実性 | `criterionDerivedHom_fromPerfect_all`・`criterionDerivedHom_all`・`criterionDerivedFullyFaithful` |
| 本質的全射 | `criterionDerivedEssSurj_of_perfectImage`。最終同値では帰納で証明した充満性を供給し、全対象での充満性を追加仮定にしない |
| compact生成を明示 | `CriterionDerivedCompactGeneration`。各生成元のcompact性と、余積閉三角部分圏の最小性を別フィールドで保持し、両側の証拠を最終型に明示 |
| 無限直和のcompact性を使わない | 固定した各perfect始域とその像だけにcompact性を使用。生成族の無限直和のcompact性を仮定する宣言なし |
| 実際のPerf判定の結論との接続 | `criterionDerivedKernelEquivalenceOfPerfWitness` とそのPerf包含図式 |
| Perf判定未完の間の明示した条件付き形式 | `criterionDerivedKernelEquivalenceOfConditions` の `hPerf`。三条件そのものは既存の型のまま |
| 実際の順関手を保持 | `criterionDerivedKernelEquivalenceOfConditions_functor` などは定義的等式 |
| 右随伴・unit/counit比較を担当しない | 一般右随伴の存在・一致・unit/counitを入力にも証明にも使わず、それらとの比較宣言なし |
| 所有境界と記録 | 新規実装はCriterionDerived*、記録は本ファイルのみ。既存Kernel*・Adjunction*・Coherence*・CriterionPerf*、共有ルート、Stage*、READMEは編集していない |

**担当する全導来拡張は、依頼で許可された条件付き形式で検証済み。**
三条件からPerf同値を作る `hPerf` 自体の証明、およびその完成後の仮定を外した直接入口は、
引き続き他担当の最終公開APIを待つ。三条件⇒全導来同値を無条件に証明したとはしない。
U16dの未受入状態、一般右随伴との比較の担当境界も変更しない。

## U16c.5：完成したPerf判定による十分性入力の供給（2026-10-17）

- `CriterionPerf.lean`（コミット `1e5ee4a0`、記録 `dg-theory-morita-criterion.md`）の
  `criterionPerfEquivalenceOfConditions` を再利用し、
  `criterionDerivedPerfSufficiency : CriterionDerivedPerfSufficiency A D E` を証明した。
  Perf側の定理と型・宇宙条件は一致し、変更や条件の追加による調整は不要だった。
- 新公開名は `criterionDerivedKernelIsEquivalenceOfMoritaConditions`、
  `criterionDerivedKernelEquivalenceOfMoritaConditions`、
  `criterionDerivedKernelEquivalenceOfMoritaConditions_functor`。
  三条件と両側のcompact生成から実際の主導来作用の同値を得る。
  `hPerf` は証明済みの補題で供給し、利用者への仮定から外した。
- 従来の `CriterionDerivedPerfSufficiency` と3つの `OfConditions` 宣言の型・証明は変更していない。
  U16c.3–4の「Perf十分性を待つ」は当時の状態であり、この節でその接続を完了した。
  両側のcompact生成は引き続き明示した仮定である。
- 対象2入口のビルド成功（2867 jobs）。新旧8宣言の直接公理監査は標準3公理のみ。
  最終合同監査は末尾参照。CriterionPerf*・共有ルート・Stage*・README・他担当ファイルは編集していない。

## 合同検証と公開入口（2026-10-17）

- 新規10監査対象・公開入口・既存 `Checks.DGFunctorDerivedEquivalence` の12対象を
  合同ビルドし成功（3562 jobs、終了コード0、警告・エラー0件）。95宣言の公理は標準3公理のみ。
- 最終ソースの担当11対象も合同ビルドし成功（3399 jobs、終了コード0、警告・エラー0件）。
  担当監査77件は既存の積擬同値・bimodule制限の2宣言を含み、すべて標準3公理のみ。
- 公開入口での同時import検査により、別ファイルの補助local instanceの自動生成名の衝突を検出した。
  5つの自分のファイルの補助instanceに固有名を付け、再ビルドで解消を確認した。
  公開した定理・関手の名前と型、既存Endomorphism/PerfectのAPIは変更していない。
- 担当の新規21 Leanファイルを走査し、新規sorry・admit・axiomは0件。引用も0件。
  各単位を自分のパスだけで個別コミットし、statを照合した。

## 追加合同検証（2026-10-17、U16b.8–9・U16d.4–5）

- 公開入口に今回の4実装ファイルを加え、新旧14監査対象・公開入口・既存dg擬同値監査の
  16対象を合同ビルドし成功（3571 jobs、終了コード0、警告・エラー0件）。
- 124宣言の公理監査はすべて標準3公理のみ。今回追加した29主要宣言も同じ。
  新しいsorry・axiom・引用はない。U16a担当のファイル・記録は読み取り専用で再利用した。

## 追加合同検証（2026-10-17、U16d.6–8）

- 新旧17監査対象・公開入口・既存dg擬同値監査の19対象の合同ビルドに成功した
  （3577 jobs、終了コード0、警告・エラー0件）。143宣言の公理監査はすべて標準3公理のみ。
- 今回追加した19主要宣言も同じ。実際の通常kernel作用の評価とU12f係数変更の接続、
  局所Hom条件を保った合成比較のPerf制限を含む。kernel変数の降下APIは入力・残項目として区別している。

## 追加合同検証（2026-10-17、U16b.10・U16d.9–12）

- 新旧22監査対象・公開入口・既存dg擬同値監査の24対象の合同ビルドに成功した
  （3590 jobs、終了コード0、警告・エラー0件）。177宣言の公理監査はすべて標準3公理のみ。
- 担当の45 Leanファイルを走査し、sorry・admit・axiomの追加は0件。
  U16bの主導来graph比較・Perf・shift・三角性・U13/U14比較を同時importで確認し、U16bの担当範囲を受入とした。
- U16d.12は `eb2dc737` に自分の5パスだけを明示してコミットし、直後のHEADのstatで一致を確認した。

## 追加合同検証（2026-10-17、U16d.13）

- 新旧23監査対象・公開入口・既存dg擬同値監査の25対象の合同ビルドに成功した
  （3593 jobs、終了コード0、警告・エラー0件）。186宣言の公理監査はすべて標準3公理のみ。
- 新しいsorry・axiom・引用はない。相手の公開記録を再確認し、合成比較は引き続き未公開と確認した。
  全体の未完項目を以下のまま保持する。

## 追加合同検証（2026-10-17、U16d.14–17）

- 新旧27監査対象・公開入口・既存dg擬同値監査の29対象の合同ビルドに成功した
  （3606 jobs、終了コード0、警告・エラー0件）。206宣言の公理監査はすべて標準3公理のみ。
- 担当55 Leanファイルを走査し、新しいsorry・admit・axiomは0件。引用も追加していない。
  実際の主導来合成比較のPerf制限、kernel作用評価の二変数自然性、通常kernelの係数変更関手、
  許容kernelの全閉零射に自然なU12f作用評価比較を同時importで確認した。

## 追加合同検証（2026-10-17、U16d.18）

- 新旧29監査対象・公開入口・既存dg擬同値監査の31対象の合同ビルドに成功した
  （3620 jobs、終了コード0、警告・エラー0件）。222宣言の公理監査はすべて標準3公理のみ。
- 担当59 Leanファイルを走査し、新しいsorry・admit・axiomは0件。デバッグtraceも0件。
  新規引用・既存APIの変更はない。他担当のファイルは編集していない。

## 追加合同検証（2026-10-17、U16d.19）

- 新旧29監査対象・公開入口・既存dg擬同値監査の31対象の合同ビルドに成功した
  （3620 jobs、終了コード0、警告・エラー0件）。223宣言の公理監査はすべて標準3公理のみ。
- 今回の追加宣言と更新されたU16aの実際の自然性APIを、公開入口への同時importで確認した。
  新規sorry・axiom・引用、既存公開APIの型の変更はない。

## 追加合同検証（2026-10-17、U16d.20–22）

- 新旧33監査対象・公開入口・既存dg擬同値監査の35対象の合同ビルドに成功した
  （3630 jobs、終了コード0、警告・エラー0件）。251宣言の公理監査はすべて標準3公理のみ。
- 担当67 Leanファイルを走査し、新しいsorry・admit・axiom、デバッグtraceは0件。
  環準同型のflat性を追加せず、モデルのhAugまたは出力hE・hPNとhP'を公開型に明示した。
  他担当・既存Endomorphism/・Perfect/のAPIの型は変更していない。

## 追加合同検証（2026-10-17、U16d.23–24）

- 新旧37監査対象・公開入口・既存dg擬同値監査の39対象の合同ビルドに成功した
  （3638 jobs、終了コード0、警告・エラー0件）。269宣言の公理監査はすべて標準3公理のみ。
- 担当75 Leanファイルを確認し、実装ソースの新規sorry・admit・axiom、デバッグtraceは0件。
  U16d.23–24はそれぞれ3f2586ef・2ccd8fceに担当6パスだけを明示してコミットし、
  各コミット直後のgit show --stat HEADで担当ファイルのみであることを確認した。
  共有ルート・他担当ファイル・既存Endomorphism/・Perfect/の公開APIは変更していない。

## 追加合同検証（2026-10-17、U16d.25–26）

- 新旧40監査対象・公開入口・既存dg擬同値監査の42対象の合同ビルド成功
  （3644 jobs、終了コード0、警告・エラー0件）。288宣言の公理はすべて標準3公理のみ。
- 担当81 Leanファイルを確認した。共有ルート、他担当のKernel*・Adjunction*・Coherence*・
  CriterionPerf*、既存Endomorphism/・Perfect/の公開APIは変更していない。

## 公開入口と残る接続

公開入口は `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence`。
元のU16b本体 `dgFunctorDerivedEquivalence` とEndomorphism/PerfectのAPIは変更していない。
共有ルート・Stage・README・他担当ファイルは編集していない。

U16bの担当範囲は受入済み。U16dは末尾の最終受入記録に記した範囲を受け入れ、
全体の受入には次の接続を残す。

1. 主導来kernelの列のperfect性とPerf保存の同値、全導来kernel射に自然な制限はU16d.11で完成した。
   実際の恒等作用の制限はU16d.12、実際の合成比較の制限はU16d.14で完成した。
   両kernelの全導来射に対する実際の合成自然性もU16d.19で完成し、hNatの追加仮定は不要になった。
   恒等・合成のcoherenceを同じ制限で移す接続は残る。
   合成に必要な始域dg圏のlocalHomKFlat条件は保持する。
2. 通常kernelの係数変更を全Hom作用込みで定義し、U12fの終域tensorを
   係数変更した実際のkernel作用の評価へ同定した（U16d.9–10）。
   通常kernelの全閉零射に自然な、実際の導来作用の評価の係数変更比較はU16d.15–17で完成した。
   dg加群全体のunderived比較と入力自然性・H⁰降下はU16d.18・20で完成した。
   モデル条件付きの全導来入力射自然なdg加群値の比較と実際のPerf正方形はU16d.21–22で完成した。
   kernel射に関するこの導来・Perf正方形の自然性はU16d.23–24で完成した。
   kernel変数の主局所化への係数変更関手はU16d.25で構成した。
   通常モデルへの自然な増大はU16d.26で構成した。
   この関手へのモデル条件付き正方形の接続、
   既存U12f評価比較との成分同定およびkernel合成との係数変更図式を残す。
   選択した右射影解像度とkernelの左評価ごとのhPN・hP'は明示したままにする。
   U12f比較自体の全左因子射の自然性と許容モデル上の自然同型はU16d.13で完成した。
   U16d.4のPerf係数変更正方形アダプタへの実際の比較の適用はU16d.22で完成した。
   係数変更とkernel合成の整合性への接続は残る。
   現在のU12f比較の始域は出力評価の複体の導来係数変更である。
   これを出力dg加群の導来係数変更の評価と同一視する定理・仮定は別途必要であり、無条件には主張しない。
3. 中心作用は保留。今回の残項目の完了条件には入れない。

U16aの一般右随伴・unit/counit・三角恒等式は既に実装済みである。
上記の未接続項目と、一般右随伴自体の不存在を混同しない。
本担当の全導来拡張は一般右随伴を使わず、その逆関手との比較はU16統合側に残す。
U16aの作用coherenceの進捗と本担当のPerfへの移送は別であり、以下の受入記録を正とする。


## U16d最終受入記録：明示条件下の担当範囲で完了（2026-10-17）

U16d.1–31の実装と監査を照合し、ユーザーのスコープ確定に従い、
**U16d は、表の受入範囲で完了とする。**
保留事項はこの完了の条件に含めない。U16全体の受入判断は統合担当に委ねる。
中心作用は引き続き保留（M9 の手順 9 で形を決める）。

| 受け入れる範囲 | 公開された証拠と適用条件 |
| --- | --- |
| 主導来kernelのPerf保存と射関手性 | `kernelColumnsPerfect_iff_preservesPerfect`、`perfectDerivedKernelActionFunctor`、`perfectDerivedKernelMap`。各kernelの列のperfect性を保持し、kernel変数の全主導来射を扱う |
| 実際の恒等・合成比較のPerf制限 | `perfectDerivedKernelIdentityIso`、`perfectKernelCompositionIso`、`_inclusion`、`_kernel_naturality`。合成は始域の `localHomKFlat A D` と両kernelの列のperfect性を保持。実際の射自然性に追加のhNatは不要 |
| 既存U12fとの評価比較 | `scalarKernelBaseChangeIso` と `_hom_app`。指定右射影モデルについてhPN・hP'を満たす許容kernel上で自然。同型の成分がU12f比較を使うことまで受入れ、出力dg加群全体の比較との成分同定は含めない |
| 通常係数変更のdg加群値比較 | `scalarKernelBalancedIso`、入力自然性・H⁰降下・kernel射自然性。underived比較として受入れ、任意擬同型保存へ読み替えない |
| dg加群値の実際の導来係数変更正方形 | `scalarKernelDerivedBaseChangeIso` と `_kernel_naturality`。一般形のhAug・hP'を保持し、全主導来入力射と通常kernel間の全閉零射の自然性を含む |
| その実際のPerf正方形 | `scalarKernelPerfectDerivedSquare`、`_inclusion`、`_kernel_naturality`。元の列のperfect性とhAug・hP'を保持。係数変更後の列のperfect性は比較から導く |
| K-flatモデルによる十分条件版 | 上記正方形・自然性の `_ofKFlatModels` 版。出力のhE : `localHomKFlat A E`、全標準右解像度tensorのhPN、係数変更後の右モデルのhP'をすべて保持 |
| 主導来kernel変数の係数変更 | `scalarKernelDerivedExtension`、任意解像度計算・解像度変更同型の自己／推移則。局所Hom K-flat性や環準同型のflat性は不要 |
| 通常モデルへの増大比較 | `scalarKernelDerivedExtensionAugmentation` と `_app`。比較射の存在を受入れ、可逆性は `_isIso` のhπ（係数変更後の積上解像度増大のkernel擬同型性）を明示。hPN・hP'でhπを代用しない |

| 局所化kernel係数変更へのモデル条件付き正方形 | `scalarKernelLocalizedDerivedSquare`、`_augmentation`、`scalarKernelLocalized_columnsPerfect`、`scalarKernelLocalizedPerfectSquare`、`_inclusion`（U16d.27）。通常代表Pを指定し、hα・hAug・hP'を保持。増大後に従来の通常モデル比較と一致する |
| 出力加群と評価複体の導来係数変更の比較 | `scalarOutputEvaluationModelIso`、`_augmentation`、`_naturality`、`scalarOutputEvaluationIso`、`_model`、`scalarKernelOutputEvaluationIso`（U16d.28）。評価値のK-flat性と加群側増大の可逆性を分離。hEと全評価のhPNによる十分条件版も受入れ、U12fとの成分の一致は含めない |
| 解像度モデル上の二経路の計算 | `scalarKernelOutputModelComputation`、`scalarKernelOutputLeft_model`、`scalarKernelOutputRight_model` と通常入力版（U16d.29）。元の全導来正方形を実際のbalanced比較・kernel増大に計算する等式。可逆性や局所Hom条件は不要 |
| 実際の合成比較に沿う正方形の貼り合わせ | `scalarKernelLocalizedCompositionSquare`、`_diagram`、`scalarKernelLocalizedCompositionPerfectSquare`、`_inclusion`（U16d.30）。両側の公開kernelCompositionIsoを使用。hD・hD'と両モデルの条件を保持。終域は係数変更した二kernelの合成であり、係数変更関手の合成保存同型を結論しない |
| kernel評価モデルとU12d計算・増大との比較 | `scalarKernelResolutionEvaluation_computation`、`scalarKernelEvaluationAugmentation_relativeKFlat` と閉零代表計算（U16d.31）。任意の右射影解像度族に対応し、増大の比較は入力の相対K-flat性を保持 |

### U16dの最終公開入口と仮定（統合担当向け）

production入口は `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence`。
以下の公開名は名前空間 `SerrePositivity.DifferentialGraded.Morita` に属する。
検証入口は `SerrePositivity.DifferentialGraded.Morita.ScalarExtensionAcceptanceChecks`。
未コミットの出力成分ファイルはどちらにもimportしていない。

共通の契約は任意可換環A、非有界cochain、次数+1のd、次数−1のホモトピー、
Mathlib Enrichedの主モデルである。`A : Type u`、`D : Type v`、`E : Type w` に
`[DGCategory A D]`、`[DGCategory A E]`、`[Small.{u} D]`、`[Small.{u} E]` を保持する。
係数変更は同じ係数宇宙の `A' : Type u`、`[CommRing A']`、`φ : A →+* A'`。
環準同型のflat性・有界性・局所Hom K-flat性を共通の暗黙の仮定にしない。
複体導来圏を評価値に使うAPIでは、`HasDerivedCategory.{z}`・`.{z'}` とその射宇宙を保持する。

| 用途・公開名 | 明示する仮定と実装ファイル（Morita/以下） |
| --- | --- |
| 主kernelの実際のPerf作用：`perfectDerivedKernelAction`、`perfectDerivedKernelActionFunctor` | `kernelColumnsPerfect A D E K`。`PerfectKernelColumns.lean`。全主導来kernel射に自然 |
| 恒等・合成のPerf比較：`perfectDerivedKernelIdentityIso`、`perfectKernelCompositionIso`、`_kernel_naturality` | 恒等は局所Hom条件不要。合成は始域hD : `localHomKFlat A D` と両kernelの列のperfect性。`PerfectDerivedKernelCoherence.lean`・`PerfectDerivedKernelComposition.lean` |
| 通常モデルの全導来係数変更正方形：`scalarKernelDerivedBaseChangeIso`、`_kernel_naturality` | 通常kernel P、hAug（全標準右解像度tensor出力での `derivedExtensionAugmentation` のIsIso）、hP'（全標準右解像度の係数変更後の右相対K-flat性）。`ScalarExtensionKernelDerivedComparison.lean`・`ScalarExtensionKernelDerivedNaturality.lean` |
| 上記のPerf正方形：`scalarKernelPerfectDerivedSquare`、`_inclusion`、`_kernel_naturality` | 元の各列のperfect性とhAug・hP'。係数変更後の列のperfect性は証明から供給。`ScalarExtensionKernelPerfectSquare.lean`・`ScalarExtensionKernelPerfectNaturality.lean` |
| K-flatモデル版：上記の `_ofKFlatModels` | 出力hE : `localHomKFlat A E`、全M,eのhPN（標準右解像度tensorのcomplexKFlat）、hP'。hAugはこの十分条件で供給する |
| 主kernel係数変更：`scalarKernelDerivedExtension` と解像度変更・任意解像度計算 | 追加のflat性・局所Hom条件不要。`ScalarExtensionKernelLocalization.lean` |
| 通常モデルへの増大：`scalarKernelDerivedExtensionAugmentation`、`_isIso` | 変換の存在は無条件。可逆性はhπ（係数変更後の積上解像度の増大がkernel擬同型）を保持。`ScalarExtensionKernelLocalizationAugmentation.lean` |
| 主kernel係数変更への正方形：`scalarKernelLocalizedDerivedSquare`、`scalarKernelLocalizedPerfectSquare` | 通常代表Pとhα（上記増大のP成分のIsIso）、hAug・hP'。hπからhαを供給できる。Perf版は元の列のperfect性も保持。`ScalarExtensionKernelLocalizedSquare.lean` |
| 出力評価との比較：`scalarOutputEvaluationModelIso`、`scalarOutputEvaluationIso`、`scalarKernelOutputEvaluationIso` | 評価値のcomplexKFlatとモデルの加群側増大のIsIso。任意出力Xの版は `X ≅ (moduleToDerived A E).obj N` を指定。kernel版は標準右解像度tensorをNに使う。`ScalarExtensionOutputEvaluation.lean`・`ScalarExtensionKernelOutputEvaluation.lean` |
| 二経路の実際のモデル計算：`scalarKernelOutputLeft_model`・`scalarKernelOutputRight_model` | K-flat性や増大の可逆性は不要。`ScalarExtensionKernelOutputModels.lean` |
| 合成に沿う実際の作用正方形：`scalarKernelLocalizedCompositionSquare`、Perf版 | hDに加え、独立にhD' : `localHomKFlat A' (DGBaseChange φ D)`。両通常モデルの `ScalarKernelLocalizedConditions`（hα・hAug・hP'）。Perf版は元の両kernelの列のperfect性。`ScalarExtensionKernelLocalizedComposition.lean` |
| U12d評価・増大の計算：`scalarKernelResolutionEvaluation_computation`、`scalarKernelEvaluationAugmentation_relativeKFlat` | 前者は任意右射影解像度族、後者は入力の右相対K-flat性。`ScalarExtensionKernelEvaluationModels.lean` |

hπとhPN・hP'は異なる条件であり、相互に無断で代用しない。
`ScalarKernelLocalizedConditions` は比較同型を仮定に隠す構造ではなく、hα・hAug・hP'の三条件を保持する。
導来Morita判定の公開入口・compact生成の仮定は次の「U16統合用」にまとめた通りで、U16dの係数変更条件とは区別する。

### 保留事項と再開条件

以下の接続は**保留**とする。
再開の条件は、**M9 で、Morita 同値と T への係数変更の可換性が必要になった場合**である。
ユーザーの指示があるまで着手しない。既に検証した個別の比較や等式を撤回するものではなく、
受入表を越える統合・整合性の主張を本U16dの完了条件から外す。

| 保留する接続 | 現在の証拠と再開点 |
| --- | --- |
| 作用の整合性のPerfへの移送に関する追加統合 | U16aから移送済みの `perfectKernelCompositionIso_rightUnit`・`_leftUnit`・`_associator`（`CoherencePerfectUnit.lean`・`CoherencePerfectAssociator.lean`、a17b756e）は供給済み。本担当でのM9用の追加図式の照合・統合は保留。元の `perfectKernelCompositionIso`・`perfectDerivedKernelIdentityIso` は上表の範囲で受入済み |
| 局所化した係数変更関手への正方形の追加接続 | 通常代表＋hα・hAug・hP'の `scalarKernelLocalizedDerivedSquare`・Perf版までは受入済み。全主導来kernel射・条件族の自然性などの追加統合は保留。`ScalarExtensionKernelLocalizedSquare.lean`、`ScalarExtensionKernelDerivedNaturality.lean`、`ScalarExtensionKernelLocalizationAugmentation.lean` から再開 |
| U12fとの成分の同定 | 出力評価比較とU12d増大計算は受入済み。既存U12f比較と全dg加群正方形の成分が一致する最終等式は保留。`scalarKernelTensorBaseChange`（`ScalarExtensionKernelTensor.lean`）、`scalarKernelOutputEvaluationIso`、`scalarKernelOutputLeft_model`・`scalarKernelOutputRight_model`、`scalarKernelEvaluationAugmentation_relativeKFlat` が再開点。未コミットファイルの状態は後述 |
| kernelの合成と係数変更の図式の追加比較 | 実際の合成比較に沿う作用正方形の貼り合わせは受入済み。係数変更関手が元の合成kernelを二つの係数変更kernelの合成へ送るkernel同型と、それを通す既存正方形との一致は保留。`scalarKernelLocalizedCompositionSquare`（`ScalarExtensionKernelLocalizedComposition.lean`）、`scalarKernelDerivedExtension`（`ScalarExtensionKernelLocalization.lean`）、`scalarPerfectSquareComposition_eq`（`ScalarExtensionPerfectSquares.lean`）が再開点 |

中心作用は引き続き保留し、**M9 の手順 9 で形を決める**。

### 未コミットの進行中ファイル

`SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelOutputComponents.lean` を削除せず保持する。
対象ビルドは失敗しており、コミット・公開入口へのimport・受入・公理監査の完了には含めない。
出力モデルのbalanced成分における型の照合（`scalarKernelOutputEvaluationModelIso_balanced`）と、
最終U12f成分式のtensor写像の簡約（`scalarKernelOutputEvaluationIso_u12f`）が未解決。
ソースにsorry・admit・axiom・trace_stateは追加していない。
失敗の再現は `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelOutputComponents`。
現在は保留中であり、このコマンドが成功するとは主張しない。

## U16統合用：導来Morita判定の最終公開名と仮定

import入口は `SerrePositivity.DifferentialGraded.Morita.CriterionDerived`。
以下の名前空間はすべて `SerrePositivity.DifferentialGraded.Morita`。

| 公開名 | 結論 |
| --- | --- |
| `criterionDerivedPerfSufficiency A D E` | 完成したPerf判定から旧入力型 `CriterionDerivedPerfSufficiency A D E` を供給 |
| `criterionDerivedKernelIsEquivalenceOfMoritaConditions A D E K hK G hG H hH` | `(kernelDerivedTensor A D E K).IsEquivalence` |
| `criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH` | `DerivedModuleCategory A D ≌ DerivedModuleCategory A E` |
| `criterionDerivedKernelEquivalenceOfMoritaConditions_functor A D E K hK G hG H hH` | 上の同値の順関手が `kernelDerivedTensor A D E K` と定義的に一致 |

最終3宣言の仮定は共通である。

- `A : Type u`、`[CommRing A]`。`D : Type v`、`E : Type w` に
  `[DGCategory A D]`、`[DGCategory A E]`、`[Small.{u} D]`、`[Small.{u} E]`。
  v・wをuへ固定せず、既存の加群・主導来圏の宇宙を保持する。
- 任意の主kernel `K : Kernel A D E` と `hK : CriterionPerfConditions A D E K`。
  三フィールドは `columnsPerfect`、`fullHomQuasiIso`、`columnsThickGenerate`。
  全Hom比較は通常代表の存在を介した既存の条件そのものである。
- `{I : Type z} [Small.{u} I]` と `G : I → DerivedModuleCategory A D`、
  `hG : CriterionDerivedCompactGeneration A D G`。
- `{J : Type z'} [Small.{u} J]` と `H : J → DerivedModuleCategory A E`、
  `hH : CriterionDerivedCompactGeneration A E H`。
  この構造は各生成元の `moduleCompact` と、u-small余積閉・同型閉な三角部分圏による
  全対象の生成を別フィールドに持つ。両側のcompact生成を本定理で自動供給したとはしない。

利用者からのhPerf入力は不要になった。局所Hom K-flat性、係数環のflat性、有界性、
一般導来右随伴の存在を追加仮定にしない。
これは三条件からの**十分性**の入口であり、全導来同値との必要十分条件や、構成した逆同値と
他担当の一般右随伴との一致・unit/counit比較は追加していない。
Perf側の必要十分条件は既存 `criterionPerfMorita_iff` を使う。
旧 `OfConditions` の3宣言（hPerf明示）と `OfPerfWitness` も引き続き使用できる。
U16dの受入範囲・残る接続、U16aのcoherenceの進捗とは独立した全導来拡張である。

## 最終合同検証（2026-10-17、U16c.5・U16d受入照合）

- 担当49公理監査入口と2公開入口の51対象を合同ビルドし成功（3701 jobs、終了コード0）。
  警告・エラー0件。新旧332宣言の公理監査はすべて
  `propext`、`Classical.choice`、`Quot.sound` の範囲内である。
- 対象一覧 `/tmp/serre-u16-final-acceptance-targets.txt`、
  ログ `/tmp/serre-u16-final-acceptance.log`。
  再現方法は同一覧の各行を `lake build` の対象に渡すこと。
  /tmpの一覧がなくても、現行の同担当範囲はリポジトリ内の
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionAcceptanceChecks` で再検査できる。
  一覧はMorita内のQuasiEquivalence*・Perfect*・ScalarExtension*・CriterionDerived*の
  全Checksと `Checks.DGFunctorDerivedEquivalence`、2公開入口から成る。
- 担当98 Leanファイルを走査しsorry・admit・axiomトークン0件。
  新規引用なし。今回の変更はCriterionDerivedの入口・条件・監査と本記録の4パスのみ。
  他担当のCriterionPerf*・Coherence*、共有ルート・Stage*・READMEは変更していない。


## U16d.27：局所化kernel係数変更への実作用・Perf正方形（2026-10-17）

主担当からの確定受渡し `bdc030cb`（U16a）、`fb7a99a6`（実際の右随伴との統合）、
`a17b756e`（Perf作用coherence）を確認した。
残接続(1)には `perfectKernelCompositionIso_rightUnit`・`_leftUnit`・`_associator` が供給済み。
従来の「Perfへのcoherence移送が残る」はこの受渡しで解消し、対応する局所Hom条件を保持して受け入れる。

- `ScalarExtensionKernelLocalizedSquare.lean` は、既存の
  `scalarKernelDerivedExtensionAugmentation` の通常モデルPでの可逆性hαを明示する。
  hαは `scalarKernelDerivedExtensionAugmentation_isIso` のhπから供給できる。
  hπをhPN・hP'から推論する宣言は追加していない。
- `scalarKernelLocalizedActionIso` は、局所化した係数変更kernelの実際の作用を
  通常係数変更モデルの実際の作用へ比較する。
- `scalarKernelLocalizedDerivedSquare` は、hα・従来のhAug・hP'を保持し、
  元の主kernelの作用と `scalarKernelDerivedExtension` の像の作用の正方形を構成する。
  `_augmentation` は通常モデルへ増大した図式が従来の比較そのものに一致する等式である。
- 元の列のperfect性から `scalarKernelLocalized_columnsPerfect` を導き、
  `scalarKernelLocalizedPerfectSquare` と `_inclusion` で実際の主Perf正方形へ制限した。
  係数変更後の列のperfect性を追加仮定にしていない。
- 監査入口と公開入口の合同ビルド成功（3443 jobs、警告・エラー0）。6宣言の公理は標準3公理のみ。
  ログは `/tmp/serre-u16d-27-audit.log`。再現は
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedSquareChecks SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence`。U12f成分同定の受入はまだ行わない。

残接続(2)は、**通常代表を指定しhα・hAug・hP'を明示した正方形**の範囲で接続した。
通常kernel射に関する旧正方形の自然性は保持するが、新しい局所化正方形について
全主導来kernel射の自然性をこの単位だけで主張しない。
残接続(3)のU12f成分同定、(4)の実際のkernel合成との係数変更図式は継続する。
中心作用は保留。U16d全体・U16全体の受入はまだ行わない。


## U16d.28：出力加群の導来係数変更と複体評価の実際の比較

- `ScalarExtensionOutputEvaluation.lean` は、加群側と複体側から共通の通常評価モデルへ
  `scalarOutputModuleEvaluationAugmentation` と `scalarOutputComplexEvaluationAugmentation` を構成した。
  どちらも通常加群の全閉零射に自然な変換であり、比較の可逆性とその条件は別に証明する。
- `scalarOutputEvaluationModelIso` は、評価値のcomplexKFlatと加群側増大のIsIsoを明示し、
  出力加群の導来係数変更の評価と、出力複体の導来係数変更を比較する。
  `_augmentation` で実際の二つの増大の可換図式、`_naturality` で許容モデル間の全閉零射自然性を証明した。
  先にU12f比較を合成して定義した同型ではなく、両方の増大から独立に構成した比較である。
- `scalarOutputEvaluationIso` は指定した計算モデルを持つ任意の主導来出力への比較で、
  `_model` はモデルへの移送図式。`_ofObjectwiseKFlat` は出力hEを保った十分条件版。
- `ScalarExtensionKernelOutputEvaluation.lean` の `scalarKernelOutputEvaluationIso` は、
  標準右解像度tensorを計算モデルにして、kernel出力について比較を供給する。
  各M,eでのhPNと出力モデルの増大のIsIsoを保持し、`_ofKFlatModels` は出力hEと全評価でのhPNを保持する。
  複体導来圏の宇宙z・z'とそのHasDerivedCategoryを明示し、主加群導来圏の宇宙へ固定しない。
- 公理監査入口のビルド成功（3250 jobs、警告・エラー0）。12宣言は標準3公理のみ。
  ログは `/tmp/serre-u16d-output-eval-audit.log`。再現は
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionOutputEvaluationChecks`。
  公開入口との合同ビルドも成功（3445 jobs、警告・エラー0、`/tmp/serre-u16d-28-audit.log`）。
  同じChecksと `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence` を `lake build` に渡す。

残接続(3)の「出力加群の導来係数変更と複体評価を比較する射・同型」は条件を明示して構成した。
**この比較を挿入した全dg加群正方形の成分が既存U12f比較と一致する等式は、引き続き証明中である。**
残接続(4)のkernel合成との係数変更図式も未完。中心作用は保留し、U16d全体の受入は宣言しない。


## U16d.29：導来正方形の左右増大の実際のモデル計算

- `ScalarExtensionKernelOutputModels.lean` は、既存のH⁰・主導来比較の成分を計算し、
  `scalarKernelOutputLeft_closed` と `scalarKernelOutputRight_closed` で通常入力上の増大経路を同定した。
  左経路は実際の `scalarKernelBalancedIso`、右経路は実際の `kernelDerivedTensorAugmentation` を使う。
- `scalarKernelOutputModelComputation` は正方形の共通モデルを標準右解像度で計算する。
  `scalarKernelOutputLeft_model`・`scalarKernelOutputRight_model` は、元の全導来正方形の
  左右の比較をこのモデル上の増大射そのものへ計算する等式である。
  H⁰上の自然性で解像度計算を運び、別の比較射を選び直していない。
- この7宣言はモデル計算の等式であり、K-flat性や増大の可逆性を必要としない。
  可逆性を使う正方形は従来のhAug・hP'を引き続き保持する。
- 監査入口のビルド成功（3244 jobs）。7宣言の公理は標準3公理のみ。
  ログは `/tmp/serre-u16d-output-models-audit.log`。再現は
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelOutputModelsChecks`。
  U12f成分同定はこれらの計算と評価比較を合わせる次の接続であり、この単位では未完とする。


## U16d.30：実際のkernel合成比較を使う係数変更作用図式

- `ScalarExtensionKernelLocalizedComposition.lean` は、hα・hAug・hP'を
  `ScalarKernelLocalizedConditions` の独立した三フィールドとして保持する。
  比較同型や可換図式そのものを仮定として格納していない。
- `scalarKernelLocalizedCompositionSquare` は、U16d.27の実際の二つの正方形を、
  元のkernelの公開 `kernelCompositionIso` と係数変更後のkernelの同じ公開比較で貼り合わせる。
  `scalarKernelLocalizedCompositionSquare_diagram` はこの実際の作用図式の可換等式。
  元の始域DのhDと、係数変更後の始域のhD'を明示し、非flat係数変更からhD'を推論しない。
- `scalarKernelLocalizedCompositionPerfectSquare` と `_inclusion` で、元の二kernelの列のperfect性から
  この実際の作用正方形をPerfへ制限した。係数変更後の列のperfect性はU16d.27から供給する。
- 対象監査入口のビルド成功（3303 jobs、警告・エラー0）。5宣言の公理は標準3公理のみ。
  ログは `/tmp/serre-u16d-composition-audit.log`。再現は
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedCompositionChecks`。

これは**実際のkernel合成と、各kernelを局所化係数変更した作用の図式**として受け入れる。
ただし終域kernelは、二つの係数変更kernelの合成である。
`scalarKernelDerivedExtension` を元の合成kernelに適用した対象とのkernel同型、
およびその同型を通す場合の既存正方形との一致は、この貼合せだけからは主張しない。
従来の残接続(4)のこの比較・整合性は引き続き未完である。
中心作用は保留。U16d全体・U16全体の受入は宣言しない。


## U16d.31：kernel評価比較とU12d計算・増大の成分同定

- `ScalarExtensionKernelEvaluationModels.lean` の
  `scalarKernelResolutionEvaluation_computation` は、任意の右射影解像度族について、
  既存 `perfectKernelResolutionDerivedTensorEvaluationIso` の成分と、実際のkernel計算同型の評価を同定する。
  閉零代表上のH⁰比較とU12d比較の計算を先に証明し、H⁰自然性で解像度へ運んだ。
- `scalarKernelEvaluationAugmentation_relativeKFlat` は、相対K-flat入力における
  実際のkernel増大の評価が、既存U12dの `relativeKFlatTensorComputation` と一致する等式。
  評価比較を別に選び直さず、元のkernel増大と既存の比較そのものを計算している。
- 複体導来圏のHasDerivedCategoryとその射宇宙zは明示したまま保持する。
  元のdg圏の局所Hom K-flat性や環のflat性は追加していない。
- 監査入口のビルド成功（3248 jobs、警告・エラー0）。5宣言は標準3公理のみ。
  ログは `/tmp/serre-u16d-evaluation-models-audit.log`。再現は
  `lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelEvaluationModelsChecks`。
  U12f比較の成分同定へ使う実際の計算補題として受け入れるが、U16d全体の受入は引き続き未完。


## U16dスコープ確定・終了時の再現手順（2026-10-17）

ユーザーの指示により、U16dは「U16d最終受入記録」の表の範囲で完了とする。
同節の保留事項にはユーザーの再開指示があるまで着手しない。
各実装節に残した「未完」「全体未受入」は検証当時の履歴であり、現在のスコープ判定を変更しない。
未コミットの `ScalarExtensionKernelOutputComponents.lean` は保持し、完了した成果に含めない。

リポジトリ直下から次を実行する。/tmpのファイルを必要としない。

```sh
lake build SerrePositivity.DifferentialGraded.Morita.ScalarExtensionAcceptanceChecks SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence SerrePositivity.DifferentialGraded.Morita.CriterionDerived
```

`ScalarExtensionAcceptanceChecks.lean` は、担当のPerf・ScalarExtension・QuasiEquivalence・
CriterionDerivedの54監査入口（既存 `Checks.DGFunctorDerivedEquivalence` を含む）をimportする。
対象3入口の合同ビルドは成功（3713 jobs、終了コード0、警告・エラー0）。
367宣言の公理監査はすべて `propext`、`Classical.choice`、`Quot.sound` の範囲内。
新規sorry・admit・axiom・引用は追加していない。
公開入口と再現監査は保留中の未コミットファイルをimportしていない。
