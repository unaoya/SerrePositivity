# SC-W1 段 2e：停止点報告の下書き（未検収）

2026-11-12 09:50 の依頼により作成。**停止点 2e に達したという報告ではない。** ビルド・監査は 10:02 の合図で再開済み。実装中と下書きの結果は検証済みとして数えない。停止点でこの文書を更新し、未完の項目がなくなったことを調整役が確認できる形にする。

## 1. 対象と検証の境界

最新の数学コミットは **`96e18ab78`**。新規 **24 本・65 宣言・1,646 行**、入口込み **1,671 行**。対象と直接 importer は **4,491 jobs で成功**、別実行の監査は **8,160 宣言・標準三公理のみ**。累計は **285 本・28,769 行**、入口込み **29,059 行**。共通細分の独立性・射への自然性、実際の Proj の標準開と Čech 複体の比較、任意の有限アフィン被覆での射影有限性まで検証済み。各宣言の一行の主張は route の同コミットの節。

**停止点ではない。** native な極限の H と旧 NatChart の有限段の H の filtered 比較は通ったが、有限段側を実際の切断へ自然に置き換える接続は残る。scalar を変える grading の carrier の照合を黙って defeq とせず、明示的な比較で閉じる。実際のスキームの底変換・閉厚化のアフィン交叉での Γ のテンソル表示との接続、Frobenius を含む五つの比較の可換性も仕上げる。Noether 近似模型の構成を 2e に移すものではない。

前の数学コミットは **`85d6de297`**。実際の準連接係数のアフィン被覆の完全性と細分の H の同型を、新規 **14 本・64 宣言・1,147 行**で接続した。入口を含む差分は **1,163 行**。対象と直接 importer は **4,466 jobs で成功**、別実行の監査は **7,995 宣言・標準三公理のみ**。各宣言の一行の主張は route の同コミットの節。累計の検証済み本体は **261 本・27,123 行**、入口を含め **27,388 行**。次の 18 本の接続は未検証であり、この集計に含めない。共通細分の独立性の同型への接続、実際の Proj の構造層との R 線形比較、五つの比較同士の整合性が残り、停止点 2e ではない。

BS17 Thm 4.1(i) の経路に必要な、射影の場合の有限性・Rees の核と像の評価・形式関数の **Čech 版**が対象。一般の固有射の有限性、Stein 分解、K 用の段 2c、導来関手の層コホモロジーとの比較は範囲に含めない。

前の検証済み数学コミットは **`ecd5061a5`**（一般のアフィン標準 Čech の完全性、Spec の準連接係数への接続、細分の写像の自然性と選択の独立性、有限標準細分の存在、共通アフィン被覆、cone と B1 の接続）。新規 **27 モジュール・141 宣言**、本体 **2,387 行**、入口を含む git 差分 **2,415 行**。対象と直接 importer は **4,452 jobs で成功**、別実行の監査は **7,890 宣言・標準三公理のみ**。宣言と主張の一行ずつの一覧は `scheme-w1-2e-route.md` の同コミットの節。一般の細分の H の同型には、まだ実際の二重図式へ各交叉の完全性を供給する接続が必要である。今回通ったのは、比較の実際の写像・自然性・選択の独立性と、完全性を前提とする cone の判定まで。動く基底の照合と五つの比較同士の可換性も未完であり、停止点 2e とはしない。段 2e の実測は **247 本・25,976 行**、入口を含め **26,225 行**。

前の検証済み数学コミットは **`eac527fbd`**（固定頂点の縮約と増大完全性、実際のアフィン標準被覆の単元の場合、共通増大項を保つ射の cone の完全性）。新規 **7 モジュール・40 宣言**、本体 **711 行**と入口 7 行。対象と直接 importer は **4,367 jobs で成功**、別実行の監査は **7,650 宣言・標準三公理のみ**。宣言と主張の一行ずつの一覧は `scheme-w1-2e-route.md` の同コミットの節。一般の単位イデアルを生成する標準被覆・任意のアフィン被覆・細分の H の同型はまだ未完で、条件付きの cone の完全性だけを共通細分の完成としない。

前の検証済み数学コミットは **`650650c96`**（斉次局所化と実際の射影標準開・Čech H の filtered colimit 比較、および次数を保つ図式の射への自然性）。新規 **8 モジュール・30 宣言**、本体 **738 行**と入口 8 行を追加。対象と直接 importer は **4,360 jobs で成功**、別実行の監査は **7,579 宣言・標準三公理のみ**。宣言と主張の一行ずつの表は `scheme-w1-2e-route.md` の同コミットの節。動く係数環の各段の標準開との照合と共通細分はまだ未完で、停止点 2e とはしない。

前の検証済み数学コミットは **`df7c1d105`**（固定した有限被覆の Čech 複体・H と filtered colimit の自然な比較、実際の局所化と余極限、指定部分加群と R/P を分けた次数成分の構成）。対象と直接 importer のビルドは **4,352 jobs で成功**。別実行の標準監査は **7,466 宣言・標準三公理のみ**。8 モジュール・43 件の数学宣言を追加した。前の `72c7ff525`・`8e896e65c` は計 10 モジュール・53 件で、実際の Frobenius と閉厚化・I 進系・形式関数の同型との可換性を検証した。各主張は `scheme-w1-2e-route.md` の各束に一行ずつ記録した。旧来の R/J のテンソル表示との照合は `5d5943541`、実際の flat Čech 比較と加群写像への自然性は `ffac3c764`。KL-W1 の追従で main `0f30e1f6c` を `2ed2c017c` に取り込み、68 本の意味参照を採取した結果、保留 0・書き換え 0 本だった。追従報告は `053bbf1b7`。

指定次数のテンソル局所化・係数環変更・各標準開・図式全体の比較は `1b359a90e` にコミット済み。前の whnf timeout は成分の同型と純テンソル公式への分割で解消した。計算量上限は増やしていない。

調整役の 10:02 の合図でビルド・監査を再開し、実際の Frobenius から閉厚化・互換族・形式関数への接続を検証した。上の監査数に未検証の下書きは含めない。`scheme-drafts/` にある残りの下書きも、検証済みとして数えない。

### 規模の途中報告（11-12 夜の新規則）

段 0 の見込み 8,000–25,000 行に対し、報告点を 12,500 行、停止基準を **50,000 行**として扱う。`0e0f9fc07` での検証済み本体は **205 本・22,140 行**、入口登録を含め **22,346 行**。文書・下書き・他レーンのソースは含めない。残りは約 **8,000–19,000 行**、合計約 **30,000–42,000 行**と見込む。主な幅は共通アフィン細分の正次数の H の比較にある。半分の報告点を越えたので一度報告し、停止せず継続する。50,000 行を超えそうになったら、検証済みをコミットして報告し止める。内訳と計測法は `scheme-w1-2e-route.md`。`eac527fbd` の後の実測は新規 **220 本・23,589 行**、入口登録を含め **23,810 行**。

## 2. 射影有限性と形式関数の出力

実装済みの核となる入口は次のとおり。宣言の全一覧と各主張は `scheme-w1-2e-route.md` の各束の表に記録している。停止点では、最終コミットからの宣言一覧を再照合し、この文書または別紙に集約する。ここでは未検証の下書きをその一覧に混ぜない。

| 宣言 | 出力・用途 |
|---|---|
| `projectiveNatGradedFullCechHomology_finite` | Noether 基底上の有限生成次数付き多項式加群の各捻り・次数の Čech H の有限生成性。 |
| `reesAdicProjectiveCechImageRees_finite` | 各 IⁿM の Čech H の像を合わせた Rees 加群の有限性。 |
| `reesAdicProjectiveCechImage_bound`、`reesAdicProjectiveCechImage_cofinal` | 元のコホモロジーの I 進フィルトレーションと、Rees の像のフィルトレーションの比較。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | 厚化への制限の核を I の冪で評価する。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | 実際の閉厚化間の Čech H の像が元の H からの像へ安定する。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | canonical な完備化写像を、実際の閉厚化の Čech H の互換族との同型にする。 |
| `reesClosedCoefficientAdicCechFormalFunctions_module_naturality` | R/J 表示を含む形式関数の比較を、元の次数付き加群の射に自然にする。 |

Rees 次数を移す作用を固定した次数の加群のスカラー作用と混同しない。像の有限性・核の評価・像の安定化を使い、高い I の作用が零であることだけから各 H^q(IⁿM) の零化を導かない。

## 3. §9 の五つの比較の到達点

| 比較 | 現在の検証済み部分 | 未完・下書き | 停止点で必要な証拠 |
|---|---|---|---|
| 共通アフィン細分 | 有界版と全タプル版の比較、B1 の二重 Čech の API。`eac527fbd` により固定頂点の縮約・増大完全性、実際の単元の場合、共通増大項を保つ射の cone の完全性も検証済み。 | 任意の二つの有限アフィン被覆の共通細分について、係数の射に自然な各 H の比較。 | 実際のアフィン交叉の二重図式、交叉上の完全性、全複体への二つの比較とその自然性。B1 の完全性の同値だけを正次数の H の同型と読み替えない。 |
| 底変換 | `1b359a90e`・`ffac3c764` により、実際の指定次数の標準開図式との自然同型、Čech H の flat 比較、元の次数付き加群の射への自然性まで検証済み。変更先 B の Noether 性なしの有限性も供給。 | 共通細分・Frobenius・実際の近似図式との整合性は、それぞれの未完の群で確認する。 | `projectiveTensorChartDiagramIso`、`projectiveNativeTensorCechIso`、`projectiveNativeTensorCechIso_naturality` が具体的な入口。H とテンソル積の交換には flat を要求する。 |
| 閉厚化 | `5d5943541` の R/J テンソル表示との比較に加え、`72c7ff525`・`8e896e65c` で実際の環の商の表示を比較した。Rees の商の射影・厚化間の遷移と、標準開図式・Čech H の具体的な比較が可換であることも検証済み。 | 共通細分・filtered colimit との整合性は、それぞれの未完の群で確認する。指数を移す Frobenius の厚化間の因子写像は、同じ n の閉厚化の Frobenius と区別し、2f の冪による因子分解に接続する。 | `reesClosedTensorChartIso_naturality`、`reesClosedTensorCechIso_naturality`、`reesClosedRingCechIso_projection`、`reesClosedRingCechIso_transition`。二つの閉厚化の表示の比較であり、非 flat な H とテンソル積の交換ではない。 |
| Frobenius | `72c7ff525`・`8e896e65c` で、実際の局所化・標準開・Čech H の Frobenius と代数の射への自然性を検証した。H 自身の I 進商での n→p*n の遷移と完備化、同じ n の実際の閉厚化の H の Frobenius、既存の射影・I 進遷移・互換族・形式関数の同型との可換性も検証済み。 | 共通細分・底変換・filtered colimit の比較同士の整合性は残る。H 自身の I 進商の n→p*n の写像から、厚化の H の間で指数を移す写像まで得たとはしない。 | `projectiveNatGradedCechFrobenius_naturality`、`reesAdicProjectiveClosedCechFrobenius_projection`、`reesAdicProjectiveClosedCechFrobenius_transition`、`reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius`。空の標準開と零環を含む。 |
| filtered colimit | `df7c1d105` の一般の Čech 比較に加え、`650650c96` で指定次数の斉次局所化の余極限同型、整数への零延長・次数付き作用、実際の標準開の図式全体と Čech H の比較・次数を保つ図式の射への自然性を検証。 | 動く係数環 B_j の各段の標準開との係数制限の照合、および共通細分・既存の Frobenius・底変換・閉厚化との比較同士の可換性。 | `projectiveGradedAwayColimitEquiv`、`projectiveNatChartColimitIso`、`projectiveNatCechFilteredHomologyIso`、`projectiveNatCechFilteredHomologyIso_naturality`。共通係数の実際の標準開までの比較だけで、動く係数環の標準開の比較を閉じたとはしない。完備化や無限積との交換は使わない。 |

**この表の未完欄が残る限り、停止点 2e の完成とは報告しない。** 新しい比較の図式が既存の R/J・I 進の自然性と同じ実際の写像を使うことも、検証項目に含める。

## 4. 案 (b) の条件と、原典の Hⁱ

[方針の正本](scheme-w1.md) は §9。以下を停止点で再確認する。

1. **「Čech 版」の明記。** コホモロジーの主張は名前に `Cech` を含め、docstring に原典の Hⁱ の番号と、「分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない」を書く。既存の主要な有限性・Rees の評価・形式関数の入口はこの形。追加する比較も同じ条件で確認する。
2. **被覆によらないこと。** §3 の共通アフィン細分の比較を完成させ、係数の射との自然性を示す。標準被覆を一つ選んで計算が通っただけでは、この条件を満たしたとは数えない。現在は未完。
3. **五つの比較が射に自然であること。** 底変換と閉厚化は実際の加群の射、Frobenius は実際の半線形写像、filtered colimit は近似の遷移写像から作る。自然性を結論として証明し、比較同型の存在を仮定に加えるだけにはしない。
4. **最終出力の型。** このレーンの出口は `SerrePositivity.Cech.AugmentedRingCechExact`。それ自体は affine の構造層の増大 Čech 余脈体の完全性で、途中の Hⁱ の定義の置き換えではない。利用側の型も変えない。現状、この束は出口の定義を編集していない。停止点で main との差と利用側を再確認する。
5. **宇宙。** 有限生成の加群には `Module.Finite.small` と `Shrink.linearEquiv` による移送を使える。多項式環と同じ宇宙の加群で計算したことを一般性の制限にしない。実際に大きい型の入口を追加する箇所では、その移送を明示する。

原典の主張は Čech だけで述べられているわけではない。[BST13 Lemma 3.9](https://arxiv.org/pdf/1307.3763v3#page=12) は Nisnevich の導来大域切断、[BS17 Lemma 4.6(i)](https://arxiv.org/pdf/1507.06490#page=16) は fppf の導来大域切断を使う。Stacks の有限性・形式関数も層コホモロジーの Hⁱ。Stacks 30.2.6 のアフィン被覆の比較だけを、Nisnevich・fppf の全ての比較を形式化した証拠としない。承認された案 (b) では、必要な射影の場合の議論を Čech 版で最終出力まで直接つなぎ、これらの導来関手との比較は作らない。

## 5. 検証と宣言一覧の記入欄

停止点で以下を実行・記入する。現在は予定であり、実行済みとは数えない。

- 最終の数学コミット、登録した全モジュール、各数学宣言と主張を一行ずつ。
- 触った対象と直接 importer のビルド結果。共有鍵 `scripts/refactor/with_build_lock.sh --wait 3600` を一回の実行ごとに返す。
- 別実行の `scripts/audit_kst_scheme_lemmas.lean` の宣言数と公理。
- `sorry`・`admit`・新しい公理・既存の宣言の変更・計算量上限の追加の確認。
- 五つの比較とその自然性の具体的な宣言名。証明メモだけを検証結果としない。
- 最終出力と利用側の型の比較、宇宙の入口、下書きのうち本体に採用しなかったものの記録。

ルート全体と下流のビルド・main への取り込みは調整役が行う。

## 6. 2f の入口

[2f の段取り](scheme-w1-2f-route.md) に、型の案、2e の出力との依存関係、不足する補題と規模を記録した。2e の検収後は Frobenius 順極限・nil 不変性・有限射の導手の計算から入る。H⁰ の実際の等化子部分環と、B/IB→H⁰(E) の Frobenius による比較が次の主要な接続になる。一般の固有射の有限性・Stein 分解・Kollár の商は作らない。


## 11-12 夜：実際の底変換と動く基底の射の比較（d01affd63）

**停止点 2e ではない。** 数学コミット `d01affd63`。26 モジュール・89 宣言、1,928 行（入口登録を含め 1,955 行）。
対象と直接 importer `SerrePositivity.AlgebraicGeometry` は **4,517 jobs 成功**。
別実行の `scripts/audit_kst_scheme_lemmas.lean` は **8,370 宣言、標準三公理のみ**。
どちらも共有鍵 `with_build_lock.sh --wait 3600` を実行中だけ取得した。
既存の宣言は変更せず、新規ファイルと入口の import の追加だけ。sorry・admit・新規公理・計算量上限の追加なし。

到達点：

- 実際の Cartesian なアフィン切断の正方形を元の基底環上のテンソル積と同一視し、左右の入射・純テンソル・制限への自然性を示した。平坦性は不要。
- `schemeStructureCechBaseChangeComplexIso` と `schemeStructureCechNativeTensorComplexIso` は、実際の逆像被覆の通常の Čech 複体を比較する。空交叉の Γ とテンソル積の交換を仮定しない。`schemeStructureCechNativeFlatBaseChangeIso` の H との交換だけに flat を要求する。
- `projectiveProjNativeNatCechComplexIso_naturality` は旧次数零加群の計算と実際の Proj の引き戻しを同じ射として照合する。
- `gradedOriginalProjNativeCechComplexIso`・`gradedOriginalProjCechScalarRestrictionIso`・`gradedOriginalProjNativeCechComplexIso_naturality` は、各段で元の Proj を使ったまま、共通基底上の計算と元の基底のスカラー制限をつなぐ。Mathlib の Proj.map の宇宙の指定に合わせ、射を扱う grading の carrier は環と同じ宇宙に置く。実際の部分加群の次数成分はこの形であり、最終出力の宇宙は変更しない。
- `projectiveHomogeneousChartLinearEquiv_frobenius`・`gradedOriginalProjNativeChart_frobenius` は実際の切断の p 乗と一致する。`schemeStructureCommonAffineCechFrobenius_naturality` は共通アフィン細分の比較と可換で、細分の同型性は準連接性から供給している。

**未完**：各段を実際の元の Proj の Čech H とした filtered 図式全体の比較と、その余極限、I 進の閉厚化・互換族・既存の Rees の形式関数への接続、および比較同士の可換性の最終照合。
`projectiveProjNativeFilteredHomologyIso` の従来の型（極限先の native H と旧有限段の H の余極限）だけを、実際の各段の比較の完成とは数えない。
模型と有限段の存在自体は承認どおり 2g の仕事であり、この束では作っていない。
最終出力 `SerrePositivity.Cech.AugmentedRingCechExact` と利用側の型は変更していない。
今夜は停止点を報告・コミットした後、取り込みを待たず 2f の F0〜F3 へ進む（11-12 夜の指示）。

登録したモジュール：

- `ProjectiveProjRingMapSectionsOfEq`
- `ProjectiveProjNativeCechEvaluation`
- `GradedScalarComponents`
- `GradedOriginalProjSections`
- `SchemeAffinePullbackSections`
- `SchemeScalarMorphism`
- `SchemeAffinePullbackSectionsNaturality`
- `SchemeAffineBaseChangeTensor`
- `SchemeAffineBaseChangeTensorLinear`
- `ModuleCechScalarExtension`
- `SchemeStructureCechBaseChangeCoefficient`
- `ProjectiveProjNativeCechNaturality`
- `SchemeAffineSectionModule`
- `SchemeAffineBaseChangeNativeSections`
- `SchemeStructureCechBaseChangeIso`
- `ProjectiveProjNativeFrobeniusEvaluation`
- `GradedOriginalProjCech`
- `GradedOriginalProjCechScalarRestriction`
- `GradedOriginalProjRingMapSections`
- `GradedOriginalProjScalarNaturality`
- `SchemeStructureCechNativeTensor`
- `GradedOriginalScalarRingMap`
- `SchemeStructureCechComparisonNaturality`
- `GradedOriginalProjCechMaps`
- `GradedOriginalProjCechNaturality`
- `GradedOriginalProjFrobeniusEvaluation`

宣言と主張（一行ずつ。生成宣言は監査に含む）：

| 宣言 | 主張 |
| --- | --- |
| `projectiveProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |
| `projectiveProjNativeNatCechComplexIso_apply` | 実際の構造層への複体の比較は、各タプルで非空交叉の切断の同型。 |
| `projectiveProjNativeCech_intersection_le` | 標準開の交叉は、実際の Proj の射での対応する交叉の逆像に含まれる。 |
| `projectiveProjNativeCechMap_apply` | 実際の Proj の Čech の射は、タプルごとに構造層の appLE に等しい。 |
| `gradedScalarComponents` | 元の次数の carrier を、指定した基底環上の部分加群として扱う。 |
| `mem_gradedScalarComponents` | scalar を指定し直しても、各次数の所属の条件は変わらない。 |
| `gradedScalarComponentsGradedRing` | scalar を指定し直した次数成分は、同じ分解を持つ次数付き環になる。 |
| `gradedScalarToOriginal` | scalar を指定した次数付き環から、元の次数付き環への恒等写像。 |
| `gradedOriginalToScalar` | 元の次数付き環から、scalar を指定した次数付き環への恒等写像。 |
| `gradedScalarAwayIso` | 同じ carrier を持つ二つの grading の斉次局所化は、環として自然に同型。 |
| `gradedScalarAwayIso_val` | 二つの grading の比較は、周囲の通常の局所化の値を保つ。 |
| `gradedScalarAwayIso_awayMap` | carrier の比較は、標準開を狭める斉次局所化の制限と可換。 |
| `gradedOriginalAwayModule` | generic な grading の斉次局所化の R 加群構造。通常の局所化への単射で移す。 |
| `gradedScalarAwayLinearEquiv` | 同じ grading の carrier の比較は、指定した基底環上でも線形。 |
| `gradedScalarComponentsGradedSMul` | 係数環を明示した carrier 上にも、同じ次数付き作用がある。 |
| `gradedSubmoduleScalarRestrictionMemClass` | 大きい基底環の部分加群は、共通の小さい基底環の作用でも閉じる。 |
| `gradedOriginalScalarToZero` | 基底環のスカラーは零次成分に属する。 |
| `gradedOriginalScalarToGlobalSections` | 分母 1 のチャートを通る、基底環から Proj の大域切断への写像。 |
| `gradedOriginalScalarToGlobalSections_restrict` | 大域スカラーの標準開への制限は、同じ定数の斉次分数である。 |
| `gradedOriginalAway_scalar_mul` | 元の基底環の加群作用は、零次成分を通る定数の乗法に一致する。 |
| `gradedOriginalProjAwaySectionLinearEquiv` | 正次数の標準開の構造層の環同型は、元の基底環上でも線形。 |
| `gradedOriginalProjAwaySectionLinearEquiv_pow` | 標準開の切断への実際の比較は冪写像と可換。零環となる開も含む。 |
| `gradedOriginalScalarToGlobalSections_comp` | 共通の基底環の大域スカラーは、元の基底環を通る合成と一致する。 |
| `schemeAffinePullbackSectionIso` | アフィン交叉上の実際の切断は、三つの切断環の canonical な pushout と同型。 |
| `schemeAffinePullbackSectionIso_inl` | pushout の左の写像は、実際の構造層の引き戻し。 |
| `schemeAffinePullbackSectionIso_inr` | pushout の右の写像も、実際の構造層の引き戻し。 |
| `schemeAffinePullbackIntersection_isAffineOpen` | 同じ実際の底変換の交叉はアフィン開である。 |
| `schemeScalarMorphism` | 大域スカラーが定める、Spec R への構造射。 |
| `schemeScalarHom` | Spec R への構造射から得られる、大域スカラー。 |
| `schemeScalarMorphism_appTop` | 構造射に移した大域スカラーを、Γ–Spec の三角恒等式で回収する。 |
| `schemeScalarHom_scalarMorphism` | 構造射を経由しても、大域スカラーの環準同型は変わらない。 |
| `schemeScalarHom_naturality` | 実際の構造射の可換な正方形から、切断の引き戻しの scalar の整合性を得る。 |
| `schemeAffinePullbackSectionIso_naturality` | 底変換の canonical なアフィン切断の比較は、開集合を狭める制限に自然。 |
| `schemeAffineSectionAlgebra` | 構造射を指定したアフィン開の切断を、基底環上の代数として束ねる。 |
| `schemeAffineBaseChangeSections_isPushout` | 実際のアフィン切断の正方形を、元の R と A を頂点に持つ pushout に移す。 |
| `schemeAffineBaseChangeTensorIso` | 実際の底変換のアフィン切断と、元の環上のテンソル積の環同型。 |
| `schemeAffineBaseChangeTensorIso_left` | テンソル積の左の写像は、底変換先の構造射が誘導する scalar の写像。 |
| `schemeAffineBaseChangeTensorIso_right` | テンソル積の右の写像は、元の構造層の実際の引き戻し。 |
| `schemeAffineBaseChangeTensorIso_tmul` | 純テンソルの実際の切断への像は、scalar の像と切断の引き戻しの積。 |
| `schemeAffineBaseChangeSectionsLinearEquiv` | 実際のアフィン底変換の切断の比較は、底変換先の環上で線形。 |
| `moduleCechScalarExtension` | スカラーを制限した係数への射の、図式に自然なテンソル積からの延長。 |
| `moduleCechScalarExtension_one_tmul` | 自然なテンソル積からの射は、1 と元の切断の純テンソルを引き戻す。 |
| `schemeStructureCechBaseChangePullbackCoefficient` | 基底環の変わる構造層の引き戻し。スカラー制限の合成を明示する。 |
| `schemeStructureCechBaseChangeDiagramRestriction` | 実際の基底変更から得る、逆像被覆の係数図式への射。 |
| `schemeStructureCechBaseChangeDiagramMap` | 実際の切断の引き戻しをテンソル積から延長した、自然な係数の射。 |
| `projectiveProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `projectiveProjNativeNatCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |
| `schemeAffineSectionAlgebra_scalar` | 構造射で定める局所のスカラーは、大域スカラーを制限した切断。 |
| `schemeAffineSectionModuleEquiv` | 実際の構造層の係数加群と、構造射で束ねた切断環は同じ加群。 |
| `schemeAffineBaseChangeNativeSectionsEquiv` | アフィン底変換の実際の切断の同型を、元の構造層の係数加群の間で述べる。 |
| `schemeAffineBaseChangeNativeSectionsEquiv_unit` | 実際の切断の同型は、1 と元の切断の純テンソルを構造層の引き戻しへ送る。 |
| `schemeStructureCechBaseChangeSectionIso` | アフィン交叉の切断の同型を、逆像被覆の対応する交叉まで輸送する。 |
| `schemeStructureCechBaseChangeDiagramMap_app` | 自然なテンソル積の射のアフィン交叉での成分は、実際の切断の同型。 |
| `schemeStructureCechBaseChangeDiagramMap_isIso` | 非空アフィン交叉において、実際の係数の底変換の射は同型。 |
| `schemeStructureCechBaseChangeComplexIso` | 実際の底変換の切断の Čech 複体は、係数をテンソル積にした Čech 複体と同型。 |
| `projectiveNatGradedChartZeroFrobenius` | 捻り零の Frobenius は、同じ次数零チャートへの半線形写像。 |
| `projectiveNatGradedChartZeroFrobenius_val` | 捻り零の Frobenius の周囲の局所化への像。 |
| `projectiveHomogeneousChartLinearEquiv_frobenius` | 加群のチャートの Frobenius は、実際の斉次局所化の p 乗に一致する。 |
| `projectiveProjNativeChart_frobenius` | 分数の比較を実際の標準開の切断へ移しても Frobenius は p 乗に一致する。 |
| `gradedOriginalProjCechOpen` | scalar の指定の前の、元の Proj の標準開。 |
| `gradedOriginalProjCechOpen_intersection` | 元の Proj の標準開の交叉は、変数の像の積での標準開。 |
| `gradedOriginalProjCechSectionLinearEquiv` | carrier の正規化前の実際の標準開へ、非空交叉の係数を移す線形同型。 |
| `gradedOriginalProjCechSectionLinearEquiv_naturality` | carrier の正規化前の切断への比較は、標準開を狭める射に自然。 |
| `gradedOriginalProjNativeCechComplexIso` | 共通の係数環上の標準開計算と、元の Proj の Čech 複体の同型。 |
| `gradedOriginalProjCoefficientScalarIso` | 段の基底環での構造層の係数を制限すると、共通の基底環での係数と自然に同型。 |
| `gradedOriginalProjCechScalarRestrictionIso` | 段ごとの基底環の制限と、同じ実際の Proj の Čech 複体の比較。 |
| `gradedOriginalProjRingMapSections_of_eq` | 同じ値の指定された分母を使う、標準開の構造層の引き戻しの自然性。 |
| `gradedOriginalProjRingMapSections_apply` | 元の grading を使う実際の切断への、斉次分数ごとの自然性。 |
| `gradedOriginalProjScalarNaturality_fraction` | 基底環のスカラーの斉次分数は、実際の係数環の写像で保たれる。 |
| `gradedOriginalScalarToGlobalSections_naturality` | Proj の引き戻しは、元の基底環の大域スカラーを保つ。 |
| `schemeStructureCechNativeTensorComplexIso` | 実際のアフィン被覆の逆像の Čech 複体と、元の Čech 複体のテンソル積の同型。 |
| `schemeStructureCechNativeTensorComplexIso_unit_apply` | 複体の比較は、1 と元の cochain の純テンソルを実際の切断の引き戻しへ送る。 |
| `schemeStructureCechNativeFlatBaseChangeIso` | 実際の底変換の構造層の Čech H と、flat なテンソル積の比較。 |
| `gradedOriginalScalarRingMap` | 異なる carrier の次数付き環の射を、共通の基底環の部分加群の次数の射に移す。 |
| `gradedScalarAwayIso_map` | 共通基底への正規化と、実際の斉次局所化の射は可換。 |
| `gradedOriginalScalarRingMap_denominator` | 元の grading の射は、標準開の分母を同じ変数の像の積へ送る。 |
| `gradedOriginalScalarRingMap_powers` | 元の grading の射で標準開の分母の冪を移す包含。 |
| `gradedOriginalChartLinearEquiv_map` | 共通基底の加群でのチャートの射を、元の grading の斉次局所化の射へ戻す。 |
| `schemeStructureCommonAffineCechCoefficient_naturality` | 二つのスカラー作用の間の実際の係数の射に対する、被覆比較の自然性。 |
| `schemeStructureCommonAffineCechFrobenius_naturality` | 実際の構造層の Frobenius は、共通アフィン細分による被覆比較と可換。 |
| `gradedOriginalProjCech_preimageOpen` | 元の grading の Proj の射は、同じ変数の標準開を引き戻す。 |
| `gradedOriginalProjNativeCechMap` | 元の二つの grading の間の、実際の構造層の Čech の引き戻し。 |
| `gradedOriginalProjCech_intersection_le` | 元の grading の標準開の交叉を引き戻す包含。 |
| `gradedOriginalProjNativeCechMap_apply` | 共通基底上での元の Proj の Čech の射は、実際の appLE の引き戻し。 |
| `gradedOriginalProjNativeCechComplexIso_apply` | 共通基底の加群の複体と元の Proj の切断の比較を、タプルごとに計算する。 |
| `gradedOriginalProjNativeCechSection_map` | 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 |
| `gradedOriginalProjNativeCechComplexIso_naturality` | 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。 |
| `gradedOriginalChartLinearEquiv_frobenius` | 共通基底のチャートの Frobenius は、元の grading の斉次局所化の p 乗と一致。 |
| `gradedOriginalProjNativeChart_frobenius` | 共通基底での計算を元の Proj の切断へ戻しても、Frobenius は実際の p 乗。 |

段 2e の検証済み実測：**311 本・30,697 行**、入口を含め **31,014 行**。上限 50,000 行内。未検証の下書きを含めない。


## 11-12 夜：各有限段も元の Proj とする filtered 比較（08a716c57）

数学コミット `08a716c57`。3 本・9 宣言・185 行、入口登録を含め 188 行。
対象と直接 importer のビルドは **4,520 jobs 成功**。別実行の監査は **8,409 宣言、標準三公理のみ**。
共有鍵 `--wait 3600` は実行ごとに返却。既存の宣言の変更、sorry・admit・新規公理・計算量上限の追加なし。

`gradedOriginalProjNativeCechDiagram` は各段の元の Proj の実際の構造層を使う。
`gradedOriginalProjNativeCechDiagram_map` は、その遷移が元の grading の Proj の実際の引き戻しであることを示す。
`gradedOriginalProjNativeFilteredHomologyIso` は、極限先と各段の**両方**で元の Proj の実際の Čech H を使う余極限比較。
模型・環の余極限・次数の照合は 2g が供給する入力であり、比較の同型性そのものを仮定していない。
各段の元の基底環での H へは、前の `gradedOriginalProjCechScalarRestrictionIso` と係数制限の完全性で接続する。

**停止点 2e ではない。** I 進の実際の閉厚化・互換族への接続と、五つの比較同士の自然性の最終照合を続ける。

| 宣言 | 主張 |
| --- | --- |
| `cechDiagramTransport` | 各段の同型に沿って、図式の遷移を移す。 |
| `cechDiagramTransportIso` | 各段の同型は、移した遷移も含めた図式全体の自然同型。 |
| `gradedOriginalRingDiagramModule` | 次数付き環の図式を、共通の多項式環上の加群の図式として扱う。 |
| `gradedOriginalRingDiagramMap` | 元の各段の grading の、環の遷移に沿う次数付き環の射。 |
| `gradedOriginalRingChartDiagram` | 共通基底上の次数零チャートの、遷移を含めた係数図式。 |
| `gradedOriginalProjNativeCechDiagram` | 各段で元の Proj の構造層を使う、実際の Čech 複体の図式。 |
| `gradedOriginalProjNativeCechDiagramIso` | 各段だけでなく、図式全体での次数零チャートと元の Proj の自然同型。 |
| `gradedOriginalProjNativeCechDiagram_map` | 移した図式の遷移は、元の Proj の実際の構造層の引き戻しそのもの。 |
| `gradedOriginalProjNativeFilteredHomologyIso` | 各段と極限先の両方で、元の Proj の実際の構造層を使う filtered Čech H の比較。 |

段 2e の検証済み実測：**314 本・30,882 行**、入口を含め **31,202 行**。上限 50,000 行内。
