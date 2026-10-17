# U16b・U16d：擬同値・Perf・係数変更の担当記録

正本は `dg-theory.md` §15.6。任意可換環、非有界cochain複体、dの次数+1、
ホモトピー次数−1、Mathlib Enrichedの主モデルを維持する。
主導来圏の本体は既存 `dgFunctorDerivedEquivalence` を再利用し、再実装しない。

## 状態と担当境界（2026-10-17）

| 項目 | 状態 |
| --- | --- |
| U16b：導来同値本体・延長/制限・unit/counit | 既存APIあり。`Checks.DGFunctorDerivedEquivalence` ビルド成功、2768 jobs、主要18宣言は標準3公理のみ |
| U16b：実際の随伴shift・三角性・Perf・U13/U14比較 | U16b.1–3・5–7で実装・対象ビルド・公理監査済み。主導来graph作用との比較を残し、U16b全体の最終受入はまだ行わない |
| 積dg圏上の擬同値 | 既存 `derivedBimoduleRestrictionEquivalence` の `localHomKFlat A C`・`localHomKFlat A D` を保持する。無条件化しない |
| U16aグラフ作用との計算比較 | 公開API節と実装を確認し、通常kernelの実際の主導来作用との関手自然同型をU16b.9で構成。kernel変数の主局所化上の作用への移送は未完 |
| U16d：Perf・係数変更・合成自然性 | 公開型確定後に着手。U16d.1–5で実際の通常kernelのPerf作用・係数変更正方形の制限と合成整合性を証明。kernel固有の係数変更正方形と合成比較への接続は未完 |
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

## 公開入口と残る接続

公開入口は `SerrePositivity.DifferentialGraded.Morita.QuasiEquivalence`。
元のU16b本体 `dgFunctorDerivedEquivalence` とEndomorphism/PerfectのAPIは変更していない。
共有ルート・Stage・README・他担当ファイルは編集していない。

U16b・U16d全体はまだ未受入であり、次の接続を残す。

1. 通常kernelの実際の主導来graph作用の関手自然同型はU16b.9で完成した。
   U16aの `kernelDerivedTensorFunctor` の実装後、kernel変数の主局所化上の作用へも移送する。
   必要な自然計算と比較の一意性はU16b.8で明示した。
2. 通常kernelの各列のperfect性からのPerf保存と実際の制限はU16d.5で完成した。
   kernel変数の主局所化上の作用へ移し、kernelの恒等・合成自然同型とその自然性・coherenceを同じ制限で移す。
   合成に必要な始域dg圏のlocalHomKFlat条件を消さない。
3. 実際のkernel作用の各評価をU12fのtensor計算と同定し、U16d.2の二変数自然同型を接続する。
   選択した右射影解像度とkernelの左評価ごとのhPN・hP'を明示したままにし、
   U16d.3の実際の係数変更Perf制限との自然な正方形・合成比較を証明する。
4. 中心作用は保留。今回の残項目の完了条件には入れない。

直近のU16a担当記録ではKernelResolution・KernelResolutionChecksまで検証済み。
通常kernelの主導来作用は公開されたが、kernel変数の主局所化上の作用・一般右随伴・
恒等/合成の作用比較は「型のみ確定」と明記されている。
その未実装宣言をimport可能な定理として扱わず、不足する射・同型をsorry・axiomで置かない。
