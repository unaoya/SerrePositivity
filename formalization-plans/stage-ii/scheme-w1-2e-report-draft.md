# SC-W1 段 2e：停止点報告（旧下書きを確定）

2026-11-13 夜。承認済みの射影・Čech 版の範囲で停止点 2e に到達した。数学コミットは **`bf9767cdc`**。
夜の指示に従い、この報告をコミットした後は取り込みを待たず、[2f の段取り](scheme-w1-2f-route.md) の F0〜F3 に進む。main への取り込み、ルート・下流の全ビルドは調整役が行う。

## 1. 完成した範囲と出力

Noether 基底上の有限生成次数付き多項式加群について、標準開の非空有限交叉を指定次数の局所化で計算し、有界な順序付き Čech 複体と全タプルの複体を比較した。単項式の計算から有限生成加群へ移して、各捻り・次数の Čech H の有限性を得た。Rees の次数ごとの直和と H の比較から、核の評価、像の安定化、I 進完備化と各閉厚化の Čech H の互換族との同型を構成した。

構造層では、次数零の計算を実際の Proj の切断へ移した。閉厚化の切断への射の核は Iⁿ 倍であり、Rees の射影と同じ核から canonical な比較を得た。厚化のスキームと遷移は実際の底変換と商環の射から構成している。空交叉を大域切断と同一視せず、正の長さのタプルの非空交叉で複体を比較する。

主な出口：

| 宣言 | 主張・使い方 |
| --- | --- |
| `fullCechOrderedHomologyNatIso` | 有界な順序付き計算と全タプルの Čech H の、図式の射に自然な比較。 |
| `projectiveNatGradedFullCechHomology_finite` | 有限生成次数付き加群の各捻り・次数の Čech H は基底環上有限。 |
| `projectiveProjNativeStandardCechHomology_finite` | 実際の Proj の構造層の標準開 Čech H の有限性。 |
| `projectiveProjNativeAffineCechHomology_finite` | 標準開が被覆する場合、任意の有限アフィン被覆の Čech H の有限性。 |
| `reesAdicProjectiveCechImageRees_finite` | IⁿM の Čech H の像を集めた Rees 加群の有限性。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | 十分厚い閉厚化への制限の核を I の冪で評価する。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | 厚化間の像が元の H からの像へ安定する。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | 加群・任意の捻りに対する Čech 形式関数の同型。 |
| `projectiveProjCechFormalFunctions` | 実際の Proj の構造層の Čech H の完備化と、実際の閉厚化の Čech H の互換族の線形同型。 |
| `projectiveProjCechFormalFunctions_of_apply` | 上の同型は、元の H の元を各閉厚化へ実際に制限する標準写像に一致する。 |

構造層の最後の出口は、R 上の次数付き環 S を有限な変数の多項式環上の有限加群として与える形。射影的なブローアップでは、Rees 代数への有限変数の次数を保つ全射からこの形を供給する。任意のアフィン被覆へ移す際の被覆条件・アフィン性は比較 API の明示した入力である。

## 2. §9 の五つの比較と自然性

| 比較 | 閉じた宣言と到達点 |
| --- | --- |
| 共通アフィン細分 | `schemeModuleCommonAffineCechScalarHomologyIso` が有限共通アフィン細分による同型を構成し、`schemeModuleCechScalarComparison_commonRefinement_independent` が共通細分の選択によらないことを示す。`schemeStructureCommonAffineCechCoefficient_naturality` は係数の射に自然。`schemeStructureAffineCechPullback_comparison_naturality` はアフィン射の実際の引き戻しに自然で、四つの細分の同型性を準連接性から供給し、同型性を追加仮定にしない。 |
| 底変換 | `schemeAffineBaseChangeTensorIso` と左右の入射・純テンソルの式が実際のアフィン切断を同定する。`schemeStructureCechBaseChangeComplexIso`、`schemeStructureCechNativeTensorComplexIso` が逆像被覆の複体を比較する。`schemeStructureCechNativeFlatBaseChangeIso` が flat な H の底変換、`projectiveNativeTensorCechIso_naturality` が加群の射への自然性を与える。複体の切断のテンソル表示に flat は不要、H とテンソル積の交換にだけ要求する。 |
| 閉厚化 | `schemeAffineClosedBaseChangeSectionIso`・`projectiveProjClosedPullbackCoefficient_ker`・`reesAdicNativeClosedCoefficientIso` が実際の Γ の商を比較する。`projectiveProjAdicCechComplexIso_transition` と `_projection`、`projectiveProjAdicCechHomologyIso_transition` と `_projection` が実際の I 進遷移・射影と可換。`projectiveProjAdicCechFamiliesEquiv` で互換族へ移し、上の形式関数に接続した。R/J の係数表示は `reesClosedCoefficientAdicCechIso_module_naturality`・`reesClosedCoefficientAdicCechFormalFunctions_module_naturality` と整合する。閉厚化の引き戻しと共通細分の整合性は前行のアフィン引き戻しの補題が適用できる。 |
| Frobenius | `projectiveHomogeneousChartLinearEquiv_frobenius`・`projectiveProjNativeChart_frobenius`・`gradedOriginalProjNativeChart_frobenius` が次数零の写像を実際の切断の p 乗と照合する。`schemeStructureCommonAffineCechFrobenius_naturality` が共通細分と可換。`reesAdicProjectiveClosedCechFrobenius_projection`・`_transition`・`reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius` は環の商の Frobenius、I 進系、形式関数との可換性を与える。同じ厚化の Frobenius と、厚化の指数を変える因子分解は区別する。後者 n→p^e n と順極限の議論は予定どおり 2f F6 に残す。 |
| filtered colimit | `gradedOriginalProjNativeFilteredHomologyIso` は有限段・極限先の両側で元の Proj の構造層の Čech H を使う。`gradedOriginalProjNativeCechDiagramIso`・`gradedOriginalProjNativeCechComplexIso_naturality` が各段の実際の射と可換、`gradedOriginalProjCechScalarRestrictionIso` が元の基底からのスカラー制限を比較する。`projectiveFilteredComplexHomologyIso_naturality` は任意の複体図式の射に自然、`projectiveNatCechFilteredHomologyIso_naturality` は次数を保つ加群の図式に自然。有限型模型・次数成分の余極限の存在は 2g の入力であり、2e の同型と混同しない。 |

各比較は、係数の写像と制限の可換式から複体・H に移している。共通細分の独立性だけを H の同型と読み替えたり、flat な底変換の補題を R/Iⁿ に適用したりしていない。閉厚化では別に全射と同じ核を証明した。

## 3. 案 (b) と原典の H、宇宙

原典 BST13 Lemma 3.9 は Nisnevich の導来大域切断、BS17 Lemma 4.6(i) は fppf の導来大域切断を用いる。Stacks の有限性・形式関数も層コホモロジー Hⁱ の主張である。この実装は承認された案 (b) に従い、中間結果を **Čech 版**として述べ、最終の affine の構造層の Čech 完全性まで直接つなぐ。導来関手の Hⁱ との比較は作っていない。

有限性・核と像の評価・形式関数・各 H の比較の docstring に原典の番号、Čech 版であること、分離的なスキーム上の準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）がこの比較は形式化しない旨を記載した。被覆によらないことと射への自然性は §2 の宣言で供給する。

最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` と利用側の型は変更していない。2g の二重 Čech には B1 の既存 API を再利用する。

加群を多項式環と同じ宇宙に置くことは、有限加群の `Module.Finite.small` と `Shrink.linearEquiv` で移送でき、BS17 の使い方を制限しない。Mathlib の Proj.map が要求する grading の carrier も環と同じ宇宙に置いた。大きな宇宙の入口が必要になった箇所で移送を接続する方針は承認どおり。

一般の固有射の有限性・Stein 分解・導来関手との比較・Noether 近似模型の構成を完成したとは主張しない。前二つは範囲外、模型の構成は 2g の仕事である。

## 4. 検証と規模

最後の束は **8 モジュール・37 件の名前付き数学宣言・703 行**、入口登録を含め **711 行**。数学コミット `bf9767cdc`。

- 対象と直接 importer：`lake build SerrePositivity.AlgebraicGeometry`、**4,542 jobs 成功**。
- 別実行の監査：`lake env lean scripts/audit_kst_scheme_lemmas.lean`、**8,615 宣言、標準三公理 propext・Classical.choice・Quot.sound のみ**。
- どちらも共有の `scripts/refactor/with_build_lock.sh --wait 3600` を実行中だけ取得し、各実行は 30 分以内。重複の整理券なし。
- 既存の宣言の変更なし。新規ファイルと AlgebraicGeometry の import の追加のみ。sorry・admit・新規公理・計算量上限の引き上げなし。差分の空白検査も通過。

段 2e の累計は **336 モジュール・32,554 行**、入口の差分を含め **32,896 行**。上限 **50,000 行**内。段 2d の報告 `df035c08e` 以後の新規本体を集計し、文書・下書き・他レーンのソースは含めない。途中の半分の報告点での実測と残りの見込みは route に記録済み。

全登録モジュールと、ソースに明示した名前付き数学宣言の一行ずつの主張は [宣言一覧](scheme-w1-2e-declarations.md)。各途中束のコミット・検証・主張の記録は [route](scheme-w1-2e-route.md)。生成宣言と局所インスタンスも標準監査の 8,615 宣言に含む。

作業用の下書きは `scheme-drafts/` に残すが、本体に採用・検証したファイル以外は登録も完成の集計もしていない。古い draft は本体の正本ではない。`.lake/` や `/tmp` に成果を置かない。

## 5. 次の段

2f は F0〜F3（零環を含む Frobenius 順極限の零判定、冪零不変性、普遍同相、有限射の導手の四角形）から始める。F4 以降で H⁰ の等化子部分環、台の冪による零化、Frobenius の厚化間の因子分解を実際の Čech 複体へ接続する。形式関数の同型だけから Frobenius 順極限の同型を読み替えない。

2f の見込みは 3,000〜9,000 行、停止基準 18,000 行。半分の報告点 4,500 行で止まらず実測と残りを報告する。今夜は停止点でも報告待ちで止めず、承認が要る型・範囲・界面の判断や上限が出た場合に、検証済みをコミットして判断点を書き、2g の紙の段取りへ移る。

正式な入口：[scheme-w1-2e-report.md](scheme-w1-2e-report.md)。
