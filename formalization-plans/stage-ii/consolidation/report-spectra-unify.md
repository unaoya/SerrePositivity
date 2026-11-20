# SU-W1 段 1　円周を座標とする対称スペクトル

基準は `main` の `84e08e53e`。ここから `refactor/spectra-unify` を作成した。CF-W1 B の2コミットは元の `research/cited-coverage` にある。[宣言ごとの扱いと利用箇所](../../../research/cleanup-zero-base/spectra/stage1.csv)

## 変更前の対応表照合

Lean を編集する前に `research/*-coverage/` 以下の CSV 178本の全列を検索した。具体版の名前空間、一般版の名前空間、両ディレクトリのパスを照合し、対象の具体版を宣言欄で名指しする行は0件だった。Kerodon 7.1.2.1 の注記は一般版の余テンソルに言及している。BS17 の none 検索の候補列には一般版の型とモデル構造の補題など5名があり、対象の具体版の宣言は含まれていない。

利用側も含めた変更前のカーネル宣言 1,130 件について、対応表の宣言名を含む列と完全名で突き合わせた。該当は BS17 の検索候補にある `SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.circleSpectrumLevelModel_monoidal` の1件で、名前・宇宙変数・型を前後で比較する対象に含めた。

## 基本の構成

- `SymmetricSpectrum.{u}` は `GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle` の略記。第 n 段・加群作用・構造射・射の各段の成分では、スペクトル引数から基礎圏と座標が決まる。使うファイルで一般版の必要な名前だけを開いた。
- `freeAt` や `evaluation` のように引数が次数だけの関手は、準同型、極限保存、モデル構造の式に何度も現れる。これらは円周を一度明示する別名を残した。一方、自由・忘却の随伴を具体版として使う箇所は余極限保存の1件で、そこで一般版に円周を渡した。
- 構造射の同変性の具体版は球面冪の置換作用を使って主張される。`sphereSequence_map_permutation` で球面列の写す射に変換すれば一般版の同変性が適用できる。自由スペクトルのブロック商では、座標を固定した生成元と比較同型を残し、後合成した生成元の公式も一般版にそろえた。
- 基本の対象・射・関手を同定していた `simplicial_…` の比較補題11件を除いた。具体版を引数に取る検査は、射の第0成分を実際に計算し、円周の自由関手と評価の間に一般版の随伴を与える。テンソル・内部 Hom・余テンソル・写像対象・懸垂の定義は後段に残した。
- 5ファイルの手書き宣言56件のうち対象は53件で、削除41件・別名11件・具体的な主張を残したもの1件。各ファイルに該当する定義または具体的な主張が残り、空になったファイルは0本。表には自動生成された公開後合成補題4件も別行にした。これらの4件はすべて一般版にある。

### 保留した3件

| 具体版の名前 | 今回の境界 |
|---|---|
| `free_action` | 自由な球面加群の作用を球面の乗法で展開する。B の `Free` にこの等式の比較相手はなく、使う作用名だけを更新した。 |
| `lift_unique` | 延長の一意性は一般化できるが、B の `Free` にこの主張の宣言はない。既存の証明を一般版の Hom 同値と生成元の公式につないだ。 |
| `free_forget_eq_tensorLeft` | 自由・忘却の合成を球面による左テンソル関手と同定する式。テンソルとの比較に属する。 |

### 利用側で必要だった調整

円周をパラメータとして先に部分適用すると、後の入力 X が宇宙を指定する前に 0 が選ばれる箇所があった。ブロック商の誘導表示に `circle.{u}` を渡して入力と同じ宇宙に固定した。評価の極限保存では円周の別名と一般版の評価を順に展開すると、元の合成関手のインスタンスを推論できる。懸垂構造射の自然性を使う側では、B のテンソル射を基点付き単体集合の `smashMap` で表示した等式を元の計算に渡した。

自由関手を原変数に取る既存の自然性補題では、変更前の証明項をそのまま渡すとカーネルが決定的に時間切れになった。上限を引き上げる試行でも再現した。最終版では比較同型を展開し、自由関手の合成が射と対象にどう作用するかを `Functor.comp_map` と `Functor.comp_obj` で明示して、元の自然性補題を適用する。個別の上限変更も内部 Hom 自体の再定義も要しなかった。

次数をずらした内部 Hom の評価公式では、対称列の作用の等式から具体版の式まで簡約する証明が、60 万ハートビートでも時間切れになった。既存の一般版 `GeneralSymmetricSpectrum.shiftedHom_structureMap_evaluation` に円周を渡すと、一般の構造射を使う利用側の型に直接一致し、具体版の主張を保てた。

レベルモデル構造では、単位対象の余ファイブラント性をローカルなインスタンスとして置いても、単位公理の適用時に探索できなかった。既存の `simplicialLevelTensor_unit_isCofibrant` の証明を `unitAxiom_of_cofibrant_unit` に引数として渡し、モデル構造のモジュールが通ることを確認した。

各段のテンソルの単位同型では、成分の式を得るために同型の定義をすべて展開すると、150 万ハートビートでもカーネルが時間切れになった。円周で具体版と一般版の単位同型が一致する等式を `rfl` で作り、それで書き換えてから一般版の成分公式を適用した。元の成分公式と、それを使う三角恒等式・左単位の証明が通った。

段 2 でも、引数から座標が決まる射は一般名を限定して開き、引数を持たずに繰り返し現れる関手には座標を固定した別名を置く方法を使える。式の表示が smash・テンソル・whiskering の間で変わる場所や、比較同型を含む自然性では、`rfl` の比較だけから既存の書き換え証明が通るとは判定できない。実際に利用する型での検査が必要になる。

## 前後の規模と検証

| 範囲 | Lean ファイル数 | ソースの宣言名（前 → 後） | カーネル宣言（前 → 後） | 物理行（前 → 後） |
|---|---:|---:|---:|---:|
| C 全体 | 78 | 663 → 622 | 1,000 → 970 | 6,149 → 5,951 |
| B 全体 | 46 | 344 → 333 | 490 → 479 | 3,699 → 3,661 |
| B・C の外の利用モジュール | 11 | 52 → 52 | 95 → 97 | 1,222 → 1,218 |
| 監査・検査スクリプト | 24 | — | — | 2,002 → 2,003 |

ソースの宣言名は各モジュールの `.ilean` の `decls` を数えた。カーネル宣言には後合成補題、等式補題、コンパイラが抽出した証明も含む。利用側のカーネル宣言の純増2件は自動生成分で、ソースの宣言名は同数。各段のテンソルの Quillen 条件を利用する箇所には、次数 0 の自由関手とスペクトルのテンソルについての既存の証明を明示的に渡した。

表の「直した使用箇所」は計185箇所。各モジュールで変更前と変更後の識別子の解決結果を比べ、残る宣言の中で具体名から一般名へ置き換わった使用を数えた。同じ位置を指す修飾名と短縮名の重複を除き、消した宣言と一緒に消えた使用は数えていない。名前を持たないスクリプトの検査例の変更10箇所は差分で確認した。

対象5モジュールと比較モジュールから逆向きに import をたどった91モジュール（C 78、B 2、その他11）はすべてビルドに成功した。変更前のカーネル宣言1,130件、変更後1,091件を採取した。同じ名前で残る全宣言で推移的公理依存の追加は0件。新たに生成された50件の依存も従来の公理の範囲内だった。`sorryAx` に依存する9宣言の集合は前後で一致する。

対応表の宣言欄で保護される対象は0件。追加で調べた BS17 の検索候補 `circleSpectrumLevelModel_monoidal` はカーネル名・宇宙変数の数が一致した。具体版の圏を推論する途中に現れる球面列とモノイドの項は変わる。変更前に保存した型の全構文を復元し、現在の環境で `Lean.Kernel.check` と `Lean.Kernel.isDefEq` を実行して、前後の型が定義的に等しいことを確かめた。

### 監査・検査

変更した3本はすべて成功した。`check_general_spectra` は円周での評価・自由関手・随伴を検査し、`check_spectra_stage2` は各段の単位・結合の成分と懸垂・ループの段を検査する。`check_simplicial_level` は一般版の射の各段で弱同値とファイブレーションを検査し、28宣言の公理監査にも成功した。この検査では、変更前から解決できなくなっていた `CofibrantlyGenerated` も既存の HA の名前空間から開いた。

逆向きの import で拾ったスクリプトは24本。最終結果は13本成功、変更していない11本は変更前と同じ診断で失敗した。基準版の91モジュールを別の検索パスに用意し、変更前に採取した1,130宣言の名前・型・公理・値が参照する定数が一致することを確認した上で、以前のスクリプトを再実行した。次の11本についてファイル名の絶対パスを除いた診断全文が一致した。

- `check_generated_bifunctor`、`check_many_object_presentability`、`check_many_object_transfer`、`check_model_replacement`、`check_monoidal_level_model`
- `check_ordinary_suspension_stability`、`check_simplicial_monoidal`、`check_spectrum_level_generators`、`check_spectrum_level_model`、`check_spectrum_suspension_geometry`
- `check_kan_quillen_level`（旧名前空間 `SerrePositivity.Inputs.Homotopy` と旧モジュール名を参照）

前二群には `CofibrantlyGenerated` の旧所在を参照するものがある。段1で置き換えた具体名を利用する監査・検査に、新しい失敗はない。ブロック商の生成元と比較同型の別名2行には100文字超のスタイル警告がある。

### 所要時間（11月20日、日本時間）

01:28 頃から指示・基本宣言・文献表を読み、01:31 頃に利用箇所の抽出を終えた。初回の書き換えと表の作成は 01:31–01:38 の約7分。その後は検証と修正を交互に進めた。01:58–04:04 の約2時間6分は⑦の全体ビルドの鍵待ちで、この間に利用箇所の数え方と検証手順を点検した。04:04–04:49 の約45分は利用側の証明・型クラス引数の修正、再ビルド、監査と変更前診断との比較に使った。ビルド試行は 01:30–01:58 にも行ったので、この所要時間には重なりがある。

対象と利用側の最終増分ビルドは14.5秒、変更後のカーネル目録採取は17.6秒。24本のスクリプトの順次実行は約3分。各ビルドと Lean による照合はすべて `--class bulk` で行った。

## 段 2　残存宣言の分類

段 1 のコミット `1b9299036` に指示書を含む `main` の `f3263792f` をマージした（`1452953f9`）。表は段 1 で残した15件を含む。ソースに名前を書く宣言は618件で、段 1 の集計との照合のため `Limits.lean` の無名インスタンス4件も収録した。後合成補題、等式補題、抽出された証明は元の宣言に含めた。[分類表](../../../research/cleanup-zero-base/spectra/stage2.csv)

### 件数と行数

`lines` はソースの各宣言範囲の行数。範囲内の宣言コメント・属性を含む。import、名前空間、共有変数宣言、宣言間の空行なども含めたディレクトリ全体は段 1 の集計で5,951行。

| まとまり | 件数 | 行数 |
|---|---:|---:|
| 基本 | 9 | 33 |
| 自由 | 60 | 338 |
| 各段のテンソル | 91 | 517 |
| テンソル積 | 126 | 565 |
| 内部 Hom | 116 | 773 |
| 余テンソル | 79 | 502 |
| 写像対象 | 101 | 568 |
| 懸垂とループ | 19 | 96 |
| 極限と余極限 | 21 | 71 |
| 合計 | 622 | 3463 |

| 扱いの案 | 件数 | 現在の宣言範囲の行数 |
|---|---:|---:|
| 消す | 394 | 2183 |
| 別名 | 57 | 220 |
| B に一般版を足す | 137 | 896 |
| 固有として残す | 26 | 115 |
| 判断できない | 8 | 49 |

見積もりでは、C の 531 宣言を除き、B に 137 宣言を足すので、B・C 合計で 394 宣言減る。C では削除と移設で 3,079 行減り、別名の定義をすべてコメント付きの一行にできればさらに最大約 106 行減る。移設する B の本体とコメントを現在と同じ長さと仮定すると、B・C 合計の減少は約 2,183〜2,289 行。利用側に追加する引数・型注釈、import の組み替え、B の証明の伸縮は見積もりに含めていない。

### 利用の集計

`Spectra/` 配下を起点に全追跡 Lean ファイルの逆向き import を調べ、そのうち C に届く91モジュール（C 78、B 2、その他11）と監査・検査24本を照合した。C に届くモジュールとスクリプトのソースは段 1 の採取時点と同じ。91モジュールの型と証明の定数参照、およびソース識別子の解決結果を統合し、同じ使用者からの重複参照を除いた。自動生成補題経由の参照は元の宣言に寄せた。

直接の利用の合計は範囲内 3,028、範囲外 156、監査・検査 83。監査はスクリプトごとに数え、成功した13本では識別子を解決済みの索引を使った。段 1 から診断のある11本では、ソース上で名指しした参照を数えた。この11本について、精密化で入る暗黙の参照は未確認。公理依存をモジュール単位で総走査する監査は `bulk_audits` に記載した。`audit_spectra` は622件、`audit_stage4_contract` は import 閉包に入る445件。対応表の宣言名を記録する列に C の宣言を名指しした行は0件。

### 依存関係と実施順

基本型・忘却・評価と、自由関手・生成元の群が先行する。極限・余極限はその後に独立して扱える。各段テンソルの対象と射、釣り合い商・自由テンソル、内部 Hom の順に構成をそろえる。自由関手のモノイダル構造はテンソル積の登録に依存するので、自由関手そのものとは実施時期が異なる。

内部 Hom と零次の自由対象から余テンソルへ進み、余テンソルの関手と各段テンソルの随伴の比較をそろえてから写像対象・豊穣化へ進む。各段テンソルと余テンソルの群は随伴の式を通じて相互に参照する。懸垂の対象と構造射は各段テンソル側で扱え、ループ・単位・余単位は余テンソルの自然同型を必要とする。内部 Hom のシフト公式も懸垂射を参照するため、宣言単位で分ける。具体例は `freeFunctorBraided` が `sphereTensorMonoidalCategory`、`pointwiseTensorCurry` が `cotensor`、`loopFunctor` が `cotensorFunctor` を利用する箇所。

- **カーネルの時間切れ**。余テンソルの随伴、各段の結合子と射、シフトした内部 Hom では、輸送された加群射と座標特殊化を一度に展開すると型の照合が重くなる。既存の成分式で先に書き換えられる箇所は表に記した。
- **インスタンス探索**。自由関手のモノイダル・組紐構造、閉構造、忘却と評価による（余）極限の保存で、具体版の登録と一般版の登録を照合する必要がある。段 1 で既に具体的な証明を渡したモデル構造側の利用もある。
- **宇宙**。極限・余極限は係数圏の対象・射の宇宙と図式の宇宙を持つ。B の極限ファイルでは小さい極限の仮定と図式の宇宙に応じた仮定を区別する。対称列の次数・置換群の和を取る自由構成では、係数圏側の小余極限の仮定も確認する。

### B に一般版を足す案

表の `assumptions` が一般化の仮定、`destination` が足す先。ここでは同じファイルに置く候補をまとめた。宣言名は現在の C での短い名前。

- Basic.lean（3件）　`sphere_action`、`sphere_underlying`、`structureMap_eq_convolutionComponent`。[B の配置先](../../../SerrePositivity/Spectra/General/Basic.lean)
- Cotensor.lean（27件）　`cotensorBifunctor_obj`、`cotensorCurry_formula`、`cotensorCurry_pre`、`cotensorEvaluation_formula`、`cotensorEvaluation_level`、`cotensorFunctor_obj`、`cotensorLevelMap`、`cotensorMap`、`cotensorMap_id`、`cotensorMap_law`、`cotensorPre`、`cotensorPre_level`、`cotensorUncurry_formula`、`cotensor_permutation`、`cotensor_structureMap`、`cotensor_suspensionMap`、`internalHomCotensorBifunctorIso_hom_app`、`internalHomCotensorIso_hom_app`、`internalHomCotensorIso_hom_hom`、`internalHomCotensorIso_inv_app`、`internalHomCotensorIso_inv_freeHom`、`internalHomCotensorIso_inv_hom`、`internalHomCotensorIso_pre`、`internalHomCotensorNatIso_hom_app`、`internalHomCotensorNatIso_inv_app`、`shiftedHomCotensorIso_hom_app`、`shiftedHomCotensorIso_inv_app`。[B の配置先](../../../SerrePositivity/Spectra/General/Cotensor.lean)
- Free.lean（3件）　`free_action`、`free_forget_eq_tensorLeft`、`lift_unique`。[B の配置先](../../../SerrePositivity/Spectra/General/Free.lean)
- FreeLevelQuotient.lean（6件）　`freeAtLevelActionNatIsoBlockQuotient`、`freeAtLevelActionNatIsoBlockQuotient_trans`、`freeAtLevelActionNatIsoPermutation`、`freeAtLevelActionNatIsoPermutation_hom`、`freeAtLevelIsoPermutation`、`freeAtLevelIsoPermutation_generator`。[B の配置先](../../../SerrePositivity/Spectra/General/FreeLevelQuotient.lean)
- Limits.lean（4件）　`evaluation_preservesColimits`、`evaluation_preservesLimits`、`forget_preservesColimits`、`forget_preservesLimits`。[B の配置先](../../../SerrePositivity/Spectra/General/Limits.lean)
- MappingObject.lean（4件）　`mappingTensorFunctor_map`、`pointedMappingSpaceBifunctor_map`、`pointedMappingSpaceBifunctor_obj`、`pointedMappingSpacePre`。[B の配置先](../../../SerrePositivity/Spectra/General/MappingObject.lean)
- PointwiseTensor.lean（11件）　`freeZeroTensorIso`、`pointwiseTensorBifunctor_obj`、`pointwiseTensorCurry_level`、`pointwiseTensorEvaluation_formula`、`pointwiseTensorEvaluation_pre`、`pointwiseTensorMap`、`pointwiseTensorUncurry_pre`、`pointwiseTensor_permutation`、`sphereTensorFreeZeroPointwiseBifunctorIso_app`、`sphereTensorFreeZeroPointwiseIso_post`、`sphereTensorFreeZeroPointwiseNatIso_app`。[B の配置先](../../../SerrePositivity/Spectra/General/PointwiseTensor.lean)
- PointwiseTensorCoherence.lean（1件）　`pointwiseTensorAssociator_inv_level`。[B の配置先](../../../SerrePositivity/Spectra/General/PointwiseTensorCoherence.lean)
- ShiftedHom.lean（40件）　`internalHomFreeAtLevelActionIso`、`internalHomFreeAtLevelActionIso_hom`、`internalHomFreeAtLevelIso`、`internalHomFreeAtLevelIso_eq`、`internalHomFreeAtLevelIso_permutation`、`internalHomFreeAtLevelIso_structureMap`、`internalHomFreeAtLevelIso_suspensionMap`、`internalHomFreeAtLevelZeroIso`、`internalHomFreeAt_structureMap_formula`、`internalHomFreeAt_suspensionMap_formula`、`internalHomFreeZeroLevelIso`、`internalHomFreeZeroLevelIso_structureMap`、`internalHomFreeZeroLevelIso_suspensionMap`、`internalHomShiftIso_hom_app`、`internalHomShiftIso_inv_app`、`shiftedHomLevelMap`、`shiftedHomMap_app`、`shiftedHomStructureFormula`、`shiftedHomStructureFormula_naturality`、`shiftedHomStructureFormula_zero`、`shiftedHomStructureFormula_zero_raw`、`shiftedHomSuspensionFormula_eq_structureFormula`、`shiftedHomSuspensionFormula_naturality`、`shiftedHomSuspensionFormula_zero`、`shiftedHomSuspensionFormula_zero_raw`、`shiftedHomSuspensionIndex_zero`、`shiftedHom_eq_freeShiftModule`、`shiftedHom_index_eq_ihom_map`、`shiftedHom_structureMap`、`shiftedHom_structureMap_eq_component`、`shiftedHom_structureMap_eq_formula`、`shiftedHom_suspensionMap`、`unshiftedHomLevelIso`、`unshiftedHomLevelIso_hom`、`unshiftedHomLevelIso_structureMap`、`unshiftedHomLevelIso_suspensionMap`、`unshiftedHomStructureFormula`、`unshiftedHomStructureFormula_index_eq`、`unshiftedHomSuspensionFormula`、`unshiftedHomSuspensionFormula_index_eq`。[B の配置先](../../../SerrePositivity/Spectra/General/ShiftedHom.lean)
- TensorClosed.lean（23件）　`associator_eq_sphereTensorAssociator`、`homBySequence_underlying`、`internalHomBifunctor_obj`、`internalHomFreeAtIso`、`internalHomFreeAtIso_naturality`、`internalHomFreeIso_hom`、`internalHomFreeIso_inv`、`internalHomFunctor_obj`、`internalHomSphereIso_hom`、`internalHomSphereIso_inv`、`internalHom_underlying`、`leftUnitor_eq_sphereTensorLeftUnit`、`rightUnitor_eq_sphereTensorRightUnit`、`sphereTensorBifunctor_forget`、`sphereTensorDesc_unique`、`sphereTensorMap_hom`、`sphereTensorSymmetry_inv`、`sphereTensorUnit_agree`、`sphereTensor_hom_ext`、`tensorHom_eq_sphereTensorMap`、`tensorRelationLeft_eq`、`tensorRelationRight_eq`、`tensorUnit_eq_sphere`。[B の配置先](../../../SerrePositivity/Spectra/General/TensorClosed.lean)
- TensorFreeAtSum.lean（15件）　`freeAtSmashBifunctor`、`sequenceTensor_underlying`、`sphereTensorFreeAtBifunctor`、`sphereTensorFreeAtLeft`、`sphereTensorFreeAtLeft_naturality`、`sphereTensorFreeAtPair`、`sphereTensorFreeAtPair_naturality`、`sphereTensorFreeAtRight`、`sphereTensorFreeAtRight_naturality`、`sphereTensorFreeAtSumNatIso`、`sphereTensorFreeAtSum_eq`、`sphereTensorFreeLeft_eq`、`sphereTensorFreePair_eq`、`tensorBySequence_action`、`tensorBySequence_underlying`。[B の配置先](../../../SerrePositivity/Spectra/General/TensorFreeAtSum.lean)

### 未使用の宣言

直接の利用と対応表の名指しがない227件では、言い換えの間の一致 58件、他所に同じ内容がある 131件、残す定義の基本補題 20件、理論の主張 18件。
「使われていない途中の段」に入れた宣言は0件。たとえば `shiftedHomSuspensionFormula_eq_structureFormula` は直接の使用者がいないが、懸垂射と構造射の二つの表示の一致を述べる。

### 判断できない宣言

- `cotensorFunctor_map`。余テンソルの射を F₀ X からの内部 Hom との比較で共役した式。B の関手との自然同型だけでは、選んだ順射・逆射の表示まで一致するか決まらない。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/CotensorFunctor.lean#L75)
- `cotensorMap_conjugate`。二変数の射を内部 Hom の反変射と共変射の合成に共役する。二変数比較の選択があるため、B の自然同型で両端の射を先に照合する必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/CotensorMapLevels.lean#L26)
- `freeFunctor_unitIso`。選んだモノイダル関手構造の単位同型と手で作った同型を Iso.ext で比較している。インスタンスを移した場合の標準の向きの扱いを先に決める必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/FreeMonoidal.lean#L46)
- `freeFunctor_tensorIso`。自由関手の登録済み tensorator と構成済みの自由比較との等式。B で登録するモノイダル関手構造の比較射を確定する必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/FreeMonoidal.lean#L51)
- `pointwiseTensorCurry_naturality`。B の随伴を直接特殊化すると具体版の選んだ余テンソル関手への射と型が一致しない。simplicialCotensorNatIso による移送を確かめる必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorAdjunction.lean#L71)
- `pointwiseTensorCurry_naturality_right`。比較では余テンソル関手の射の表示に型の不一致が出た。simplicialCotensorNatIso で射を共役した式まで照合する必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorAdjunction.lean#L78)
- `pointwiseTensorAssociator_module_hom`。運んだ結合子と係数加群の結合子の基礎射を同定する。等号は rfl ではなく逆比較での消去を使い、どちらを標準にするかが利用側に影響する。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorAssociatorLevels.lean#L25)
- `loopFunctor`。円周での両右随伴の比較は simplicialLoopNatIso。指定した自然同型を除かずに単位と余単位まで置換する方法を決める必要がある。。[具体版](../../../SerrePositivity/Spectra/SymmetricSpectrum/SuspensionLoop.lean#L28)

### 型と本体の抜き取り照合

B の円周特殊化を用いた機械照合は150件。29定理で具体版の全引数を持つ型に一般定理を適用でき、47定義で全引数を持つ値の等式が `rfl` で通った。表の `kernel_sample` に記録した。この照合では72件がハートビート上限に達し、2件は余テンソル射の自然性で型が異なった。時間切れの判定には、構成の定義と既存の比較のソースを用いた。

- `sphereTensor` は球面列上の釣り合いテンソルで、一般版も円周のテンソル冪の列上の同じ釣り合いテンソル。比較は `simplicial_tensor`。[`SimplicialComparison.lean`](../../../SerrePositivity/Spectra/General/SimplicialComparison.lean)
- `freeAtLevelIsoBlockQuotient_input` の型は、生成元への入力射とブロック商の比較を合成した式。具体版は `freeAt` の基礎射の式で書き換え、`freeConvolutionLevelIsoBlockQuotient_input` を球面列に適用する。[`FreeLevelQuotientAction.lean`](../../../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelQuotientAction.lean#L55) [一般論](../../../SerrePositivity/Spectra/SymmetricSequence/FreeBlockQuotientMaps.lean#L151)
- `simplicial_suspensionLoopUnit` の左辺は一般の単位に右随伴の自然同型の順射を後合成したもの。余単位では懸垂関手で写した比較の順射を前合成する。証明は右随伴の一意性を使う。[`SimplicialSuspensionComparison.lean`](../../../SerrePositivity/Spectra/General/SimplicialSuspensionComparison.lean#L46)

この段の差分は分類表と本節の2ファイル。比較に使う一時ファイルと採取は bulk 鍵の下で実行し、作業ツリーに追跡対象を追加しなかった。

## 段 3　自由スペクトルと極限・余極限

範囲は段 2 の「自由」と「極限と余極限」の81件。main の c551fdd34 を 89eb8e0f8 で取り込んだ。自由関手のモノイダル・組紐構造と単位比較は指示書の §4 に従いテンソル積の段に回した。[判定表](../../../research/cleanup-zero-base/spectra/stage3.csv)

| 扱い | 段 2 の案 | 今回の扱い |
|---|---:|---:|
| 消す | 42 | 56 |
| 別名 | 25 | 6 |
| B に一般版を足す | 13 | 13 |
| C に残す | 0 | 0 |
| 判断できない | 1 | 0 |
| 対象外 | 0 | 6 |

段 2 の案をこの81件に当てはめると C は 55 件減、B は 13 件増。今回の実測では C は 69 件減、B は 13 件増。自由関手のモノイダル構造の保留と、利用が削除される別名の再判定がこの差を生んだ。宣言の範囲に限ると、C から除いた行は見積もり 322 行に対して 376 行。B の見積もりは元の宣言の 66 行で、実際には一般化の型注釈、import、コメント、改行を含め102行増えた。C の物理行数の減少には、空になった7ファイルのヘッダーと宣言間の行も含む。

別名の候補を、残る使用者が座標をどう推論するかで見直した。今回削除した宣言の間でだけ使っていた別名は一般版へ集約した。極限・余極限のインスタンスの利用者は B の登録を型クラス探索で使う。rewritten_uses は、削除した宣言に依存していた既存の宣言で今回の差分より後も残るものを数える。自動生成補題経由の依存も元の宣言に寄せた。変更は2件で、freePushoutProductSquare と simplicialLevelTensor_unit_isCofibrant が一般版の freeAt_preservesColimits に切り替わった。いずれも型クラス探索による。

| 範囲 | ソース宣言数 | 物理行数 |
|---|---:|---:|
| C | 622 → 553 | 5,951 → 5,328 |
| B | 333 → 346 | 3,661 → 3,763 |
| 利用側 | 158 → 158 | 3,420 → 3,418 |

消したファイルは 7 本。

- `FreeLevelAction.lean`
- `FreeLevelInduction.lean`
- `FreeLevelPermutation.lean`
- `FreeLevelQuotient.lean`
- `FreeLevelQuotientAction.lean`
- `FreeLevels.lean`
- `Limits.lean`

### 確認と調整

忘却の大きさ付き保存では、対応する形の極限または余極限が係数圏に存在することを仮定した。余極限には、Day convolution の閉構造に必要な小極限の仮定も残した。基礎対象の誘導表示への比較は、一般論の n, X, m を具体版の n, m, X の順で受け取るラムダを使って型を照合した。削除・一般化した69件を元の具体版の型で照合した。無名の（余）極限インスタンス4件は、B の登録を明示した例でも通った。ハートビート上限は新設・増加していない。

対象を逆向きに import する 154 モジュールを旧版で、削除ファイルを除く 147 モジュールを新版で検証した。監査・検査36本のうち15本が成功。段 1 で確認した11本と、B の変更で影響範囲に加わった既存失敗10本の終了状態・診断を前後で比較した。うち20本は診断全文が一致した。check_spectrum_level_model の1件は40行目の同じ箇所で同じ200,000ハートビート上限に達し、診断に出る処理名だけ whnf から isDefEq に変わった。カーネル宣言は1,680件から1,577件になった。既存宣言の公理依存の追加は0件で、sorryAx に依存する宣言は前後とも同じ9件。対象81件を直接名指しする対応表は0件。影響範囲の2宣言を挙げた BS17 の検索候補は、カーネル名と型が一致した。

繰り返し円周を明記する6件は一行の別名を維持した。利用側では忘却による極限・余極限の登録元が変わった。TensorQuotient.lean では、以前は一つの import から得ていた一般の極限構成と円周用の評価の別名を、それぞれ import する。

```diff
-public import SerrePositivity.Spectra.SymmetricSpectrum.Limits
+public import SerrePositivity.Spectra.General.Limits
+public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation
```

- `examples` は 20.3 秒。
- `before-inventory` は 14.5 秒。
- `final-build` は 306.6 秒。
- `after-inventory` は 11.3 秒。

開始から検証完了まで約36分（bulk 鍵の待ち時間を含む）。

## 段 4　各段のテンソル

段 2 の「各段のテンソル」の91件を対象とした。main の `62c0d04b0` を `3951b47ae` で取り込んだ。[判定表](../../../research/cleanup-zero-base/spectra/stage4.csv)

| 扱い | 段 2 の案 | 今回の扱い |
|---|---:|---:|
| 消す | 63 | 61 |
| 別名 | 7 | 5 |
| B に一般版を足す | 12 | 10 |
| 固有として残す | 6 | 6 |
| 判断できない | 3 | 0 |
| 余テンソルの段へ | 0 | 2 |
| C に残す | 0 | 7 |

C の削減は、段 2 の案をこの範囲に当てはめた75件に対して実測 71 件。B の追加は見積もり12件に対して実測 10 件。座標を何度も指定する別名だけを残し、次数0の自由テンソルの積の比較は既存の一般版を特殊化した。宣言範囲では C から除く行の見積もりは 444 行、実際に除いた宣言は 396 行。B に足す元宣言の見積もりは 87 行。物理行数には import、モジュールの説明、空行を含む。

| 範囲 | ソース宣言数 | 物理行数 |
|---|---:|---:|
| C | 553 → 482 | 5,328 → 4,822 |
| B | 346 → 356 | 3,763 → 3,817 |
| 利用側 | 74 → 74 | 1,684 → 1,685 |

書き換えた参照は 97 箇所。名前解決済みの型・本体・検査の参照位置を数え、同じ位置の重複を除いた。

### 型の照合

写像対象の結合則と豊穣化の比較で、各段の結合子を展開しながら五角形と単位則を照合するとハートビート上限に達した。作用の二変数関手と自然変換の成分で述べる一般補題を用意し、同じ上限で利用側に適用した。

余テンソルの右随伴の表示に依存する転置の自然性2件を余テンソルの段に回した。別の7件では一般版の証明が通っても旧版の型への適用がカーネルの上限に達した。円周版の証明を残し、試行の結果を判定表に記した。削除した71件は型の照合または利用側のビルドで確認した。

### 利用箇所の前後

短くなった例。一般版の結合子への切り替えで、`SimplicialComparison.lean` の順射比較を使った証明は定義的な等式になった。

```diff
-  apply CategoryTheory.Iso.ext
-  exact (SymmetricSpectrum.pointwiseTensorAssociator_module_hom X Y E).symm
+  rfl
```

変わらない例。`simplicialTensor` は、各段の作用を一般版から開くことで、既存の自由基点追加を記す式がそのまま使える。

```lean
pointwiseTensor (adjoinBasepoint K) E
```

長くなった例。単体的作用の余単位では、随伴とその成分が明示される。

```diff
-  simplicialTensorEvaluation (Δ[0] : SSet.{u}) E
+  (simplicialTensorCotensorAdjunction (Δ[0] : SSet.{u})).counit.app E
```

### 判定

対象と利用側 70 モジュールのビルドを bulk 鍵で確認した。監査・検査29本の成否は段 3 の結果と一致した。13本が成功し、既存の失敗16本は診断全文が一致した。変更した検査は `check_spectra_stage2.lean` の1本で、前後とも成功した。影響範囲のカーネル宣言は750件から712件になり、既存の宣言への公理依存の追加は0件。`sorryAx` に依存する宣言は前後で同じ9件。対象91件を直接名指しする対応表は0件。BS17 の検索候補の型は採取した前後のカーネル型が一致した。

削除した空ファイルは3本。`PointwiseTensorAssociatorLevels.lean`、`PointwiseTensorCoherence.lean`、`SimplicialTensorProductNaturality.lean`。

所要時間は約44分（bulk 鍵の待ち時間を含む）。

## 段 5　テンソル積

main の `eac7d1e57` を `bf121b839` で取り込んだ。段 2 のテンソル積126件と、段 3 から回した自由関手の6件を照合した。[判定表](../../../research/cleanup-zero-base/spectra/stage5.csv)

| 扱い | 段 2 の案 | 今回 |
|---|---:|---:|
| 消す | 93 | 126 |
| 別名 | 9 | 1 |
| B に一般版を足す | 28 | 5 |
| 判断できない | 2 | 0 |
| C に残す | 0 | 0 |

段 2 の案の削減121件に対し、対象132件のうち C から 131 件を除いた。B への追加は案の28件に対し 5 件。一般の加群の補題に球面列を渡して足りるもの、既存の B の自由テンソル比較を使えるもの、定義展開で成立する等式は重複を除いた。自由テンソルの和次数比較は、二つの係数と次数から座標が決まらず、pushout-product で円周の指定を繰り返すため、一行の別名を使う。

対象宣言の範囲で数えると、C の削除の見積もりは 544 行、実測は 581 行。B への追加候補だった元宣言は 121 行。下表の物理行数は import や空行も含む。

段 2 で「内部 Hom」に入っていた `spectrumMonoidalClosed` は §6 の登録条件に従い別途削除した。C のモノイダル・対称・閉の登録と自由関手のモノイダル・組紐の登録の計5件は、一般の加群の登録を円周へ特殊化したものと定義的に一致した。C の登録を一時無効化してから `inferInstance` で得られた登録も `rfl` または `HEq.rfl` で照合した。

| 範囲 | Lean ファイル数 | ソース宣言数 | 物理行数 |
|---|---:|---:|---:|
| C | 68 → 52 | 482 → 350 | 4,822 → 3,743 |
| B | 46 → 46 | 356 → 361 | 3,817 → 3,851 |
| 利用側 | 18 → 18 | 83 → 83 | 1,957 → 1,951 |

対象132件の書き換えは 42 箇所。閉構造の別途削除では写像対象の2箇所を型クラス探索で記述した。段 4 の7件はソースの宣言範囲を変更前と照合した。随伴の展開は段 4 の分も [expanded-names.csv](../../../research/cleanup-zero-base/spectra/expanded-names.csv) に記録した。展開数は差分に現れた式の位置を数え、一つの局所束縛で複数回使う場合は1箇所とした。

逆転置の比較では、具体版の自由対象から加群の一般版に差し替えると従来の書き換えがマッチしなかった。射影と合成した後に生成元の表示を change で揃え、評価の補題を適用した。写像対象の二変数随伴では、変更後の表示で係数圏の宇宙が 0 に推論されたため、自由関手の随伴と作用の二変数関手に宇宙を明示した。上限設定はそのまま。

### 利用箇所の前後

短くなった箇所。基点付き写像対象の関手では、内部 Hom のインスタンスを型クラス探索で得る。

```diff
-  (@CategoryTheory.ihom SymmetricSpectrum.{u} _ _ E
-    (spectrumMonoidalClosed.closed E)) ⋙ evaluation 0
+  ihom E ⋙ evaluation 0
```

同じ式を使う箇所。自由スペクトルの pushout-product の押し出しの頂点を移す比較は、一行の別名で引き続き書ける。

```lean
(sphereTensorFreeAtSum m n A X).symm
```

長くなった箇所。転置と逆転置が互いに逆になる証明で加群の Hom 同値を直接使う。この形の展開は 2 箇所。

```diff
-  (sphereTensorHomEquiv E X F).left_inv f
+  (MonoidalModuleInternalHom.tensorHomEquiv sphereSequence.{u} E X F).left_inv f
```

### 判定

bulk 鍵で対象と利用側 99 モジュールをビルドした。旧型の例は 133 件で通った。監査・検査 30 本は前後とも 15 本が成功し、従来の失敗 15 本の診断は変更前と一致した。影響範囲のカーネル宣言は 1296 → 1110 件。既存の宣言への公理依存の追加は0件、`sorryAx` に依存する宣言は変更前後とも同じ 9 件。対応表の対象宣言の名指しは0件。BS17 の検索候補1件は、旧モノイダル登録を明示した型に変更後の宣言を適用して照合した。

既存の失敗のうち check_general_spectrum_level_monoidal は、同じ箇所で CofibrantlyGenerated の宇宙指定のエラーを出した。別途成功した公理監査の通知だけが、監査対象の追加に伴い26件から30件に変わった。

変更箇所では FreeLeftUncurry.lean の1行に、100文字を超えるという linter の警告が出た。

削除した空ファイルは16本。`FreeMonoidal.lean`、`Tensor.lean`、`TensorAssociator.lean`、`TensorFreeLeft.lean`、`TensorFreePair.lean`、`TensorFreeRight.lean`、`TensorFreeZeroLevels.lean`、`TensorHexagon.lean`、`TensorLeftUnit.lean`、`TensorMonoidal.lean`、`TensorPentagon.lean`、`TensorQuotient.lean`、`TensorRightUnit.lean`、`TensorSymmetric.lean`、`TensorSymmetry.lean`、`TensorTriangle.lean`。

所要時間は約 65 分。bulk 鍵の待ち時間を含む。

## 段 6　内部 Hom

main の `9e8eb98d3` を `7f2e7538b` で取り込んだ。段 2 の「内部 Hom」116件のうち、段 5 で閉構造の登録を削除した後に C に残る115件を対象とした。段 4 で保留した9件は宣言本文と型を照合した。[判定表](../../../research/cleanup-zero-base/spectra/stage6.csv)

| 扱い | 段 2 の案 | 今回 |
|---|---:|---:|
| 消す | 64 | 89 |
| 別名 | 1 | 1 |
| B に一般版を足す | 50 | 25 |
| C に残す | 0 | 0 |

段 2 の案ではこの範囲の C の削減見込みは 114 件、一般版の追加は 50 件だった。実測では削減 114 件、B への追加 25 件。削除宣言の範囲で数えると、見積もり 766 行に対し実測 775 行。下表の物理行数は import と空行も含む。

自由原変数の加群比較とその自然性は、A の `freeHomModuleIso` と `freeHomModuleIso_naturality` に自由対称列の対象と射を渡した。各段での置換と構造射との両立には、既存の自然性と構造射の補題を使った。B には、スペクトルの自由原変数に対する各段の比較、構造射・懸垂・次数零の式とその自然性を置いた。

| 範囲 | Lean ファイル数 | ソース宣言数 | 物理行数 |
|---|---:|---:|---:|
| C | 52 → 42 | 350 → 236 | 3,743 → 2,608 |
| B | 46 → 49 | 361 → 386 | 3,851 → 4,217 |
| 利用側 | 15 → 15 | 73 → 73 | 1,711 → 1,709 |

円周の場合の二変数内部 Hom は、引数がなく係数列を余テンソルの関手と自然比較に繰り返し渡すため一行の別名とした。転置・逆転置・評価の名前を除き、[随伴成分の展開記録](../../../research/cleanup-zero-base/spectra/expanded-names.csv) に追記した。

### 利用箇所の前後

余テンソルの全体比較を第 q 段で評価する書き換えでは、B の各段の比較をそのまま使える。合成同型の等式と各段の射の等式を分け、逆転置でも逆射の基礎射の等式を分けて、既定のカーネル上限で検査した。

```diff
-  rw [internalHomShiftIso_hom_app, shiftedHomCotensorIso_hom_app]
+  rw [shiftedHomCotensorIso_hom_app]
```

次数零の構造射と比較同型の両立では、一般版から同じ名前を開いて使う。

```lean
unshiftedHomLevelIso_structureMap
```

余テンソルへの転置公式では、加群の転置に球面列を渡した。この転置の展開は 1 箇所。

```diff
-  internalHomCurry f
+  MonoidalModuleInternalHom.curryModule sphereSequence.{u} _ f
```

### 判定

bulk 鍵で対象と利用側 54 モジュールをビルドした。旧型の例は 115 件で通った。監査・検査 28 本は前後とも 14 本が成功し、既存の失敗 14 本の落ち方を照合した。影響範囲のカーネル宣言は 753 → 582 件。既存の宣言への公理依存の追加は0件で、`sorryAx` に依存する宣言は 9 → 9 件。対応表の対象宣言の名指しは0件。BS17 の検索候補の型はカーネル型で一致した。

削除した空ファイルは10本。`Closed.lean`、`InternalHom.lean`、`InternalHomFree.lean`、`InternalHomFreeLevels.lean`、`InternalHomFreeNaturality.lean`、`InternalHomFreePermutation.lean`、`InternalHomShift.lean`、`InternalHomShiftNaturality.lean`、`InternalHomShiftZero.lean`、`InternalHomUnderlying.lean`。

自由原変数の評価と左自由因子の逆転置は、一般版を旧型にそのまま適用するとカーネルの既定の上限で照合しにくかった。自由比較の順射、転置と評価、逆転置の射影を個別に確認し、元の型をそれぞれ再構成した。段 2 の検査では構造射の転置に関する2つの式を、B と Mathlib の補題で証明した。

余テンソルの変更箇所では、100文字を超える行の linter 警告が残った。

所要は約81分。bulk 鍵の待ち時間を含む。

## 段 7　余テンソル

main の `629c2a3f0` を `b61f9db0f` で取り込んだ。段 2 の余テンソル79件と段 4 からの9件を対象とした。判断を保留していた余テンソルの2件は79件に含む。[判定表](../../../research/cleanup-zero-base/spectra/stage7.csv)

C の `cotensor` と `cotensorFunctor` は、変更前に B を円周で特殊化した定義との等式を両方とも `rfl` で確認した。対象と関手の定義を先に揃え、構造・評価・射の補題を整理した。点ごとのテンソルとの随伴も B と `rfl` で一致した。

| 扱い | 段 2 の案 | 今回 |
|---|---:|---:|
| 消す | 42 | 67 |
| 別名 | 6 | 2 |
| B に一般版を足す | 31 | 14 |
| 固有として残す | 5 | 5 |
| 判断できない | 4 | 0 |

対象内で C から除く見込みは 73 件で、実測は 81 件。宣言の範囲で数えた見込みは 502 行、実測は 572 行。B の追加は見込み 31 件に対し 14 件。移送した関手の写像、二変数の共役、パラメータ付き随伴の自然性には既存の補題を使い、B にはスペクトルの構造射や各段での評価・転置・射の公式を置いた。

| 範囲 | Lean ファイル数 | ソース宣言数 | 物理行数 |
|---|---:|---:|---:|
| C | 42 → 33 | 236 → 155 | 2,608 → 1,728 |
| B | 49 → 52 | 386 → 400 | 4,217 → 4,505 |
| 利用側 | 10 → 10 | 50 → 50 | 1,122 → 1,119 |

円周を繰り返し指定する余テンソル関手と随伴に別名を使う。基点のない単体集合による構成5件を維持した。[随伴成分の展開記録](../../../research/cleanup-zero-base/spectra/expanded-names.csv)

### 段 4 から持ち越した7件

| 旧宣言 | 旧型の照合 |
|---|---|
| `pointwiseTensorCurry_post` | B の `pointwiseTensorHomEquiv_naturality_parameter` |
| `pointwiseTensorUncurry_pre` | パラメータ付き随伴の `homEquiv_symm_naturality_one` |
| `pointwiseTensorEvaluation_pre` | `whiskerLeft_map_counit` を対象で評価し、等式を反転 |
| `pointwiseTensorEvaluation_formula` | 左随伴を移送した余単位の定義を `rfl` で照合 |
| `pointwiseTensorEvaluation_level` | B の各段の評価公式 |
| `pointwiseTensorUncurry_level` | B の各段の逆転置公式 |
| `pointwiseTensorCurry_level` | B の各段の転置公式 |

7件とも旧型で通り、C の宣言を削除した。保留していた値域の射は移送関手の写像の定義と一致し、両変数の共役は一般の自然同型の公式で得られた。

### 利用箇所の前後

各段の評価法則では、左随伴を移送した余単位の等式を定義から得る。

```diff
-    (pointwiseTensorEvaluation_formula X E) (cotensorEvaluation_level X E q)
+    rfl (cotensorEvaluation_level X E q)
```

円周によるループの定義は同じ式を使う。

```lean
cotensorFunctor (circle : PointedSimplicialSet.{u})
```

通常の単体集合による転置は随伴の Hom 同値を直接使う。この形の展開は 17 箇所。

```diff
-  simplicialTensorCotensorHomEquiv K E F f
+  ((simplicialTensorCotensorAdjunction K).homEquiv E F) f
```

### 判定

bulk 鍵で対象と利用側 34 モジュールをビルドした。旧型の例は 83 件で通った。監査・検査 24 本は前後とも 14 本が成功し、既存の失敗 10 本の診断も一致した。影響範囲のカーネル宣言は 441 → 344 件。既存宣言への公理依存の追加は0件で、`sorryAx` に依存する宣言は 9 → 9 件。対応表で対象宣言を名指しする行は0件。BS17 の検索候補1件はカーネル名と型が一致した。

全体の比較の順射は、同型そのものの等式と各段の式を分けて旧型を照合した。上限設定は変更していない。`CotensorEvaluation.lean` の逆転置の型には行長の警告が1件残った。

削除した空ファイルは 9 本。`Cotensor.lean`、`CotensorAdjunction.lean`、`CotensorCurryNaturality.lean`、`CotensorLevelEvaluation.lean`、`CotensorMapLevels.lean`、`FreeLeftUncurry.lean`、`PointwiseTensorLevelEvaluation.lean`、`PointwiseTensorMapLevels.lean`、`SimplicialCotensorProductNaturality.lean`。

所要は約 23 分。bulk 鍵の待ち時間を含む。

## 段 8　写像対象と懸垂・ループ

main の `fbe3c52b8` を `2e65f1360` で取り込んだ。段 2 の写像対象101件、懸垂とループ19件の計120件を照合した。[判定表](../../../research/cleanup-zero-base/spectra/stage8.csv)

基点付き写像対象とその関手・二変数関手・随伴、基点付きの二つの豊穣構造は、B の円周特殊化と `rfl` で一致した。これを確認して定義を揃えた後、補題と利用箇所を整理した。ループ関手と懸垂との随伴は単位・余単位も含めて `rfl` で一致し、ループ関手を B の `cotensorFunctor` に置き換えた。

| 扱い | 段 2 の案 | 今回 |
|---|---:|---:|
| 消す | 95 | 106 |
| 別名 | 6 | 5 |
| B に一般版を足す | 4 | 0 |
| 固有として残す | 14 | 9 |
| 判断できない | 1 | 0 |

段 2 の案で除く見込みは 99 件で、実測は 106 件。宣言の範囲で数えた見込みは 563 行、実測は 601 行。B の追加候補4件は、既存の写像対象の二変数関手と点ごとのテンソルの関手の定義で足りた。

固有候補14件のうち、基点を忘れた写像対象・前合成とその合成、零次単体との比較、自由基点追加を使う随伴の9件を維持した。豊穣構造そのものと通常圏に接続した豊穣構造は忘却関手に沿う一般の移送を直接利用し、それぞれの定義展開で得られる比較を含めて5件を除いた。14件の帰結と理由は判定表に記録した。

| 範囲 | Lean ファイル数 | ソース宣言数 | 物理行数 |
|---|---:|---:|---:|
| C | 33 → 23 | 155 → 49 | 1,728 → 785 |
| B | 52 → 52 | 400 → 400 | 4,505 → 4,507 |
| 利用側 | 10 → 10 | 50 → 50 | 1,119 → 1,113 |

転置・評価・単位・余単位などの展開式を追記した。[随伴成分の展開記録](../../../research/cleanup-zero-base/spectra/expanded-names.csv)

展開が10箇所を超えた名前は0件だった。

### 利用箇所の前後

懸垂とループの単位の比較では、円周へ特殊化した随伴の成分を直接使うので、展開する定義が減った。

```diff
-  simpa only [simplicialLoopNatIso, SymmetricSpectrum.suspensionLoopUnit,
-    SymmetricSpectrum.suspension, simplicial_suspensionFunctor] using
+  simpa only [simplicialLoopNatIso] using
```

安定化の導来随伴では、円周での随伴の別名をそのまま使う。

```lean
let n := (derivedAdjunction Q Q suspensionLoopAdjunction γ ρ).toEquivalence
```

導来ループ関手の指定に B の余テンソル関手を使う。この名前の展開は 10 箇所。

```diff
-  SymmetricSpectrum.loopFunctor.{u} ⋙ W.Q
+  (GeneralSymmetricSpectrum.cotensorFunctor
+    (K := PointedSimplicialSet.circle.{u}) PointedSimplicialSet.circle) ⋙ W.Q
```

### 判定

bulk 鍵で対象と利用側 22 モジュールをビルドした。削除した宣言は旧型の例 106 件で照合した。監査・検査 24 本は前後とも 14 本が成功し、既存の失敗 10 本のエラーは一致した。影響範囲のカーネル宣言は 324 → 181 件。既存宣言への公理依存の追加は0件で、`sorryAx` に依存する宣言は 9 → 9 件。対応表で対象宣言を名指しする行は0件。BS17 の検索候補1件はカーネル名と型が一致した。

転置と前合成の旧型では、先に随伴と二変数関手を比較してから各成分を照合した。モデル側の Hom の比較では、B の豊穣構造を移送の引数に明示して二つの比較同型と SM7 の型を揃えた。リソースの上限設定は変更していない。更新した API を対称スペクトルの README に反映した。

`check_kan_quillen_level` はソースとエラーが変更前と一致した。削除した `mappingSpaceSimplicialCategory` を候補に挙げる Lean のヒントだけが消えた。

`check_ordinary_suspension_stability` では、既存のエラーのほかに出る正常な公理監査の採取件数が 87 → 88 件になった。

`check_spectrum_suspension_geometry` では、既存のエラーのほかに出る正常な公理監査の採取件数が 97 → 93 件になった。

削除した空ファイルは 10 本。`AdjointStructureMaps.lean`、`InternalHomShiftSuspension.lean`、`MappingSpaceArrowComposition.lean`、`MappingSpaceAssociativity.lean`、`MappingSpaceComposition.lean`、`MappingSpaceEnriched.lean`、`MappingSpaceNaturality.lean`、`MappingSpaceSimplicialEnriched.lean`、`MappingSpaceUnitLaws.lean`、`Suspension.lean`。

所要は約 29 分。bulk 鍵の待ち時間を含む。

### C の現状

C は円周への特殊化を置くディレクトリ。行数は宣言の開始から終端までとし、宣言に付随する文書コメント・属性を含む。名前は完全修飾名。

| ファイル | 宣言数 |
|---|---:|
| [Basic.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/Basic.lean) | 2 |
| [CotensorFunctor.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/CotensorFunctor.lean) | 1 |
| [Evaluation.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/Evaluation.lean) | 4 |
| [Free.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/Free.lean) | 3 |
| [InternalHomFunctor.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/InternalHomFunctor.lean) | 1 |
| [InternalHomShiftStructure.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/InternalHomShiftStructure.lean) | 1 |
| [MappingSpace.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/MappingSpace.lean) | 2 |
| [MappingSpacePointedOrdinary.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/MappingSpacePointedOrdinary.lean) | 1 |
| [MappingSpaceSimplicial.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/MappingSpaceSimplicial.lean) | 5 |
| [MappingSpaceSimplicialOrdinary.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/MappingSpaceSimplicialOrdinary.lean) | 1 |
| [PointwiseTensor.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensor.lean) | 2 |
| [PointwiseTensorAdjunction.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorAdjunction.lean) | 1 |
| [PointwiseTensorAssociator.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorAssociator.lean) | 1 |
| [PointwiseTensorFunctor.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorFunctor.lean) | 1 |
| [PointwiseTensorUnit.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/PointwiseTensorUnit.lean) | 1 |
| [SimplicialTensorCotensor.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/SimplicialTensorCotensor.lean) | 8 |
| [SimplicialTensorNaturality.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/SimplicialTensorNaturality.lean) | 4 |
| [SimplicialTensorProduct.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/SimplicialTensorProduct.lean) | 1 |
| [SimplicialTensorUnit.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/SimplicialTensorUnit.lean) | 1 |
| [Sphere.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/Sphere.lean) | 4 |
| [StructureMaps.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/StructureMaps.lean) | 1 |
| [SuspensionLoop.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/SuspensionLoop.lean) | 2 |
| [TensorFreeAtSum.lean](../../../SerrePositivity/Spectra/SymmetricSpectrum/TensorFreeAtSum.lean) | 1 |
| 合計 | 49 |

| ファイル | 宣言 | 種類 | 行数 | 残した理由の区分 |
|---|---|---|---:|---|
| Basic.lean | `SerrePositivity.SymmetricSpectrum` | `abbrev` | 3 | 型の略記 |
| Basic.lean | `SerrePositivity.SymmetricSpectrum.forget` | `abbrev` | 2 | 別名 |
| CotensorFunctor.lean | `SerrePositivity.SymmetricSpectrum.cotensorFunctor` | `abbrev` | 2 | 別名 |
| Evaluation.lean | `SerrePositivity.SymmetricSpectrum.evaluation` | `abbrev` | 2 | 別名 |
| Evaluation.lean | `SerrePositivity.SymmetricSpectrum.freeAt` | `abbrev` | 2 | 別名 |
| Evaluation.lean | `SerrePositivity.SymmetricSpectrum.freeAtAdjunction` | `abbrev` | 2 | 別名 |
| Evaluation.lean | `SerrePositivity.SymmetricSpectrum.freeAtGenerator` | `abbrev` | 2 | 別名 |
| Free.lean | `SerrePositivity.SymmetricSpectrum.freeObj` | `abbrev` | 2 | 別名 |
| Free.lean | `SerrePositivity.SymmetricSpectrum.freeFunctor` | `abbrev` | 2 | 別名 |
| Free.lean | `SerrePositivity.SymmetricSpectrum.generator` | `abbrev` | 2 | 別名 |
| InternalHomFunctor.lean | `SerrePositivity.SymmetricSpectrum.internalHomBifunctor` | `abbrev` | 2 | 別名 |
| InternalHomShiftStructure.lean | `SerrePositivity.SymmetricSpectrum.structureMap_eq_convolutionComponent` | `lemma` | 6 | その他 |
| MappingSpace.lean | `SerrePositivity.SymmetricSpectrum.pointedMappingSpaceBifunctor` | `abbrev` | 3 | 別名 |
| MappingSpace.lean | `SerrePositivity.SymmetricSpectrum.pointedMappingSpaceParametrizedAdjunction` | `abbrev` | 5 | 別名 |
| MappingSpacePointedOrdinary.lean | `SerrePositivity.SymmetricSpectrum.pointedMappingEnrichedOrdinaryCategory` | `abbrev` | 3 | 別名 |
| MappingSpaceSimplicial.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingSpace` | `def` | 3 | 固有 |
| MappingSpaceSimplicial.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingSpaceBifunctor` | `def` | 5 | 固有 |
| MappingSpaceSimplicial.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingSpaceBifunctor_obj` | `lemma` | 4 | 固有 |
| MappingSpaceSimplicial.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingComposition` | `def` | 7 | 固有 |
| MappingSpaceSimplicial.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingVertexEquiv` | `def` | 5 | 固有 |
| MappingSpaceSimplicialOrdinary.lean | `SerrePositivity.SymmetricSpectrum.mappingSpaceSimplicialCategory_vertexEquiv` | `lemma` | 10 | 固有 |
| PointwiseTensor.lean | `SerrePositivity.SymmetricSpectrum.pointwiseTensorFunctor` | `abbrev` | 2 | 別名 |
| PointwiseTensor.lean | `SerrePositivity.SymmetricSpectrum.sphereTensorFreeZeroPointwiseNatIso` | `abbrev` | 2 | 別名 |
| PointwiseTensorAdjunction.lean | `SerrePositivity.SymmetricSpectrum.pointwiseTensorCotensorAdjunction` | `abbrev` | 3 | 別名 |
| PointwiseTensorAssociator.lean | `SerrePositivity.SymmetricSpectrum.pointwiseTensorAssociatorNatIso` | `abbrev` | 2 | 別名 |
| PointwiseTensorFunctor.lean | `SerrePositivity.SymmetricSpectrum.pointwiseTensorBifunctor` | `abbrev` | 2 | 別名 |
| PointwiseTensorUnit.lean | `SerrePositivity.SymmetricSpectrum.pointwiseTensorUnitNatIso` | `abbrev` | 2 | 別名 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensor` | `def` | 3 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialCotensor` | `def` | 3 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorFunctor` | `def` | 3 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialCotensorFunctor` | `def` | 3 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorParameterFunctor` | `def` | 4 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingSpaceFunctor` | `def` | 4 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorMappingAdjunction` | `def` | 4 | 固有 |
| SimplicialTensorCotensor.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorCotensorAdjunction` | `def` | 4 | 固有 |
| SimplicialTensorNaturality.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorPost` | `def` | 4 | 固有 |
| SimplicialTensorNaturality.lean | `SerrePositivity.SymmetricSpectrum.simplicialCotensorPre` | `def` | 5 | 固有 |
| SimplicialTensorNaturality.lean | `SerrePositivity.SymmetricSpectrum.simplicialMappingSpacePre` | `def` | 4 | 固有 |
| SimplicialTensorNaturality.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorCotensorHomEquiv_post` | `lemma` | 7 | 固有 |
| SimplicialTensorProduct.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorProductNatIso` | `def` | 5 | 固有 |
| SimplicialTensorUnit.lean | `SerrePositivity.SymmetricSpectrum.simplicialTensorUnitNatIso` | `def` | 4 | 固有 |
| Sphere.lean | `SerrePositivity.SymmetricSpectrum.sphere` | `def` | 2 | 固有 |
| Sphere.lean | `SerrePositivity.SymmetricSpectrum.sphere_underlying` | `lemma` | 2 | 固有 |
| Sphere.lean | `SerrePositivity.SymmetricSpectrum.sphere_action` | `lemma` | 2 | 固有 |
| Sphere.lean | `SerrePositivity.SymmetricSpectrum.sphere_structureMap` | `lemma` | 4 | 固有 |
| StructureMaps.lean | `SerrePositivity.SymmetricSpectrum.structureMap_equivariance` | `lemma` | 10 | その他 |
| SuspensionLoop.lean | `SerrePositivity.SymmetricSpectrum.suspensionFunctor` | `abbrev` | 3 | 別名 |
| SuspensionLoop.lean | `SerrePositivity.SymmetricSpectrum.suspensionLoopAdjunction` | `abbrev` | 3 | 別名 |
| TensorFreeAtSum.lean | `SerrePositivity.SymmetricSpectrum.sphereTensorFreeAtSum` | `abbrev` | 2 | 別名 |

## 段 9　円周への特殊化を3ファイルにまとめる

基準は `refactor/spectra-unify` の `3ecc4edca`。C は Lean 23 本・785 行・49 宣言から、3 本・327 行・50 宣言になった。宣言数はソースで名を付けたものを数えた。旧ファイルと新ファイルは[段 9 の対応表](../../../research/cleanup-zero-base/spectra/stage9.csv)に記録した。`loopFunctor` は基準点に存在しないので旧ファイル欄を空欄とした。段 8 で削除する前は `SuspensionLoop.lean` にあった。

| ファイル | 行 | 宣言 | 内容 |
| --- | ---: | ---: | --- |
| `Basic.lean` | 137 | 26 | 円周に固定した型、自由対象と評価、構造射、基点付き作用・内部 Hom・写像対象、懸垂とループ |
| `Sphere.lean` | 42 | 4 | 円周の対称列の正則加群と、その台・対称群作用・構造射 |
| `Simplicial.lean` | 148 | 20 | 基点のない単体集合による作用、写像空間と零次単体の比較、随伴、自然性、単位と直積 |

3 ファイルの区分は案のとおり。写像空間から得た単体的豊穣圏の零次単体を比較する `mappingSpaceSimplicialCategory_vertexEquiv` は、基点のない写像空間の構成と合わせて読めるよう `Simplicial.lean` に置いた。

### ループ関手

`GeneralSymmetricSpectrum.cotensorFunctor` の円周での特殊化を一行の `abbrev loopFunctor` にした。段 8 で展開した 10 箇所のうち、Lean の 9 箇所は `Stable/OrdinarySuspension.lean` に 1、`Stable/SimplicialStability.lean` に 4、`General/SimplicialSuspensionComparison.lean` に 1、`check_ordinary_suspension_stability.lean` に 1、`check_spectra_stage2.lean` に 2 ある。残り 1 箇所は C の README の API 表。[展開記録](../../../research/cleanup-zero-base/spectra/expanded-names.csv)に「戻した」と記録した。

### 使う側の import の変化

- `Foundations.lean` の旧 C import 19 行を `Simplicial` の 1 行に整理した。球面の `Sphere` は従来どおり公開する。`StageTwo.lean` の旧 C import 2 行は `Simplicial` の 1 行にした。
- `ModelCategory/FreePushoutProduct.lean` の旧 C import 4 行は `Basic` の 1 行にした。`ModelCategory/SimplicialHomComparison.lean` は `MappingSpacePointedOrdinary` を `Basic` に、`ModelCategory/SimplicialLevelEnriched.lean` は `SimplicialTensorCotensor` を `Simplicial` に置き換えた。
- `scripts/check_spectra_stage2.lean` は直接使う `SimplicialHomLaws` と `ActionProductComparison` の import を加えた。`InfinityCategories/Project/ModelCategoryComparison/Inputs/SimplicialLevel.lean` には、レベルモデルの import を通じて新しい C が届く。

#### B 側の追従

| ファイル | import の変更 | その他の変更 |
| --- | --- | --- |
| `Spectra/General/SimplicialComparison.lean` | 旧 C の 6 行を `Basic` の 1 行に集約 | 0 行 |
| `Spectra/General/SimplicialSuspensionComparison.lean` | `SuspensionLoop` の 1 行を `Basic` の 1 行に置換 | `loopFunctor` の参照 1 行 |

この 2 本は円周に固有の比較を行い、現在は `Spectra/General` にある。C に移すかどうかは次の B の整理で判断する。段 9 での追従は上の行に限った。

### 検証

bulk 鍵で、新しい C 3 本と逆向き import の閉包にある利用側 13 本をビルドした。C の既存 49 宣言は、移動前後で宣言コマンドの型と本体のソースが一致した。保存した旧環境と変更後の環境を比較すると、ソース上の宣言および方程式補題の既存 117 件はすべて同じカーネル名を持つ。型は 83 件が同一の式で、34 件がカーネルで定義的に等しい。ここには `loopFunctor` を明示した利用側の型も含む。

カーネルの全件数は影響範囲で 268 → 201、C 内で 135 → 70。`loopFunctor` が 1 件増え、Lean が抽出する内部の `_proof_*` 名が 68 件減った。うち 66 件は C 内、2 件は利用側。ファイルをまたいで作られていた補助証明を統合後のファイル内で共有した結果を含む。共通名への公理依存の追加は 0 件。新しい `loopFunctor` の依存は `propext`・`Classical.choice`・`Quot.sound`。影響範囲の `sorryAx` 依存は前後とも同じ 9 件。

監査・検査 24 本の成否は前後で一致した。成功は 14 本、既存の失敗は 10 本。診断の差は `audit_spectra`、`audit_stage4_contract`、`check_level_enriched`、`check_ordinary_suspension_stability` が出力する集計件数で、エラーの内容は一致した。

### 自動生成の補助名

`loopFunctor` がソースで名を付けた宣言の唯一の追加。既存の方程式補題を含め、`_proof_*` 以外の生成物に追加・削除・改名は 0 件。減った 68 件の旧所有ファイルは以下のとおり。パスは `SerrePositivity/Spectra/` から。

| 旧ファイル | 件数 |
| --- | ---: |
| `ModelCategory/SimplicialLevelEnriched.lean` | 1 |
| `Stable/OrdinarySuspension.lean` | 1 |
| `SymmetricSpectrum/CotensorFunctor.lean` | 4 |
| `SymmetricSpectrum/Evaluation.lean` | 3 |
| `SymmetricSpectrum/Free.lean` | 3 |
| `SymmetricSpectrum/InternalHomFunctor.lean` | 4 |
| `SymmetricSpectrum/MappingSpace.lean` | 10 |
| `SymmetricSpectrum/MappingSpacePointedOrdinary.lean` | 4 |
| `SymmetricSpectrum/MappingSpaceSimplicial.lean` | 1 |
| `SymmetricSpectrum/PointwiseTensor.lean` | 4 |
| `SymmetricSpectrum/PointwiseTensorAdjunction.lean` | 4 |
| `SymmetricSpectrum/PointwiseTensorAssociator.lean` | 4 |
| `SymmetricSpectrum/PointwiseTensorFunctor.lean` | 4 |
| `SymmetricSpectrum/PointwiseTensorUnit.lean` | 4 |
| `SymmetricSpectrum/SimplicialTensorNaturality.lean` | 4 |
| `SymmetricSpectrum/SimplicialTensorProduct.lean` | 3 |
| `SymmetricSpectrum/SimplicialTensorUnit.lean` | 3 |
| `SymmetricSpectrum/SuspensionLoop.lean` | 4 |
| `SymmetricSpectrum/TensorFreeAtSum.lean` | 3 |

完全修飾名と短い表記を検索し、本体、現行の監査・検査スクリプト、対応表、blueprint の生成器と生成物で、削除された補助名への文字参照は 0 件だった。過去の比較目録 `scripts/refactor/targets/w2a-2-v3b-comparison.json` には 9 件が計 18 行に残っている。たとえば 4535 行目の `SerrePositivity.SymmetricSpectrum.freeObj._proof_1`。この目録は W2a-2 当時の宣言一覧で、現行の実行や生成で使われていない。main の `0997952dc:formalization-plans/stage-ii/consolidation/cleanup-rules.md` に従い、履歴として保存した。

[証拠目録](../../../evidence/spectra-unify/stage9/manifest.json)の基準点は `3ecc4edca`。外部証拠の `removed-generated-proof-names.txt` に旧名と旧所有ファイルを、`generated-proof-reference-scan.txt` に文字参照の検索結果を保存した。

## 段 10　一般の対称スペクトルの分類

main `17fdb6570` を取り込んだ `4ac20dbd1` を基準にした。[段 10 の分類表](../../../research/cleanup-zero-base/spectra/stage10.csv)は、B の一般側 373 件、円周専用の比較 14 件、C 50 件の計 437 件。比較 14 件は B の 52 ファイルに含まれる。ソースに名前があるコマンドをカーネルの宣言範囲と照合した。自動生成の補題は親へ寄せ、無名の instance は利用者として数えた。論文対応表が名指しする対象宣言は 0 件だった。

### 件数と行数

行数は宣言の先頭から本体の末尾までの空行を除いた行数。共有する import・節・説明・空行を含む実ファイルは、B と比較の合計が 52 本・4,502 行、C が 3 本・327 行。

| まとまり | B | 比較 | C | 件数 | 宣言行 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 基本と構造射 | 23 | 0 | 8 | 31 | 168 |
| 自由スペクトルと各段の表示 | 64 | 0 | 7 | 71 | 357 |
| 極限と余極限 | 16 | 0 | 0 | 16 | 56 |
| 各段のテンソル | 35 | 2 | 10 | 47 | 234 |
| テンソル積 | 13 | 1 | 1 | 15 | 105 |
| 内部 Hom と次数のずらし | 47 | 1 | 1 | 49 | 369 |
| 余テンソル | 31 | 1 | 7 | 39 | 275 |
| 写像対象と豊穣化 | 102 | 1 | 13 | 116 | 827 |
| 懸垂 | 42 | 8 | 3 | 53 | 307 |

| 内容 | B | 比較 | C | 合計 |
| --- | ---: | ---: | ---: | ---: |
| B に固有 | 100 | 0 | 0 | 100 |
| A の包み | 137 | 0 | 2 | 139 |
| Mathlib にある | 56 | 4 | 3 | 63 |
| A に置くべき | 50 | 0 | 0 | 50 |
| 円周・基点付き単体集合に固有 | 30 | 10 | 45 | 85 |

| 扱いの案 | B | 比較 | C | 合計 |
| --- | ---: | ---: | ---: | ---: |
| そのまま | 129 | 0 | 1 | 130 |
| 消す | 180 | 12 | 15 | 207 |
| 別名 | 10 | 0 | 12 | 22 |
| A へ移す | 39 | 0 | 0 | 39 |
| 判断できない | 15 | 2 | 22 | 39 |

既存の相手の主張を並べた結果、258 件を「確かめた」、13 件を「名前と型から推定」とした。個別の相手を指定した行は合計 271 件。「確かめた」には型と本体を読み、既存結果の適用または定義展開で得られることを確認したものを含む。将来の移動・削除を反映したビルドの判定は次の段で行う。

### 案を適用した場合の規模

| 範囲 | 現在の宣言・実ファイル行 | 案を適用した場合 |
| --- | --- | --- |
| B（比較込み） | 387 件・4,502 行 | 約 156 件・2,800〜3,200 行 |
| A（指示書の4領域） | 1,092 件・14,083 行 | 約 1,112 件・14,338〜14,448 行 |
| C | 50 件・327 行 | 35 件・250〜305 行 |

B は「消す」の 192 件と「A へ移す」の 39 件を控除した。「判断できない」は現状の数に含めた。削除・移動案に当たる宣言本体は B と比較で 1,367 行。関連する説明・区切りの集約と新しい一般論を呼ぶ側の追従を幅に含めた。C は削除案 15 件の 26 宣言行と、隣接する宣言説明を整理した場合の概算。

A は移動候補の 39 件・509 宣言行を一件ずつ移す上限と、既存の右随伴比較・輸送・豊穣 Hom の補題に寄せる場合を分けた。段 3〜8 では追加・移動の見積もりが実装時におおむね半分になったため、中心値は約 20 件、追加の宣言行を約 254 行とした。幅には新しい引数やモジュールの説明を含む。右随伴の比較・係数自然性・原変数自然性の三つを作用と余作用に共用できるかが、差の主因になる。

C の基点なし係数と正則加群の案を採る場合は別計算になる。C の削除案を先に実施し、基点なし係数の残り 18 件と球面の残り 2 件を一般化し、C の二変数随伴の入口を B 側に統一すると、C の現行名の入口は概算 14 件になる。B には 20 件を逐一加える上限がある。既存の係数関手や A の正則加群を再利用する場合、8〜12 件程度を追加する見込み。C に互換別名を残す場合は、その別名の数を両端の見積もりに反映する。

### 依存と実施順の案

1. A の既存の内部加群・畳み込みを確認し、B の台・忘却・自由加群、次数評価を揃える。次数付きの自由表示は既存の対称列の余極限・誘導・商の三表示を先に揃える。
2. 次数別の構造射と自由・評価の API を固めてから、極限・余極限、自由対象のテンソル、各段テンソルへ進む。自由第0段テンソルと各段テンソルの同型は係数作用の出発点。
3. 内部 Hom の一般論、自由対象からのシフト表示、シフト0、余テンソルの順に揃える。次数1の懸垂とその転置は構造射に続けて扱う。シフトした懸垂の式がこれを使う。余テンソルの段別の式が揃ってから、各段作用の転置と二変数随伴を照合する。
4. 第0段の写像対象、代表性と豊穣の通常圏、豊穣 Hom の関手比較、作用と余作用の写像対象比較、モデル登録の順に揃える。円周係数のシリンダーから導来懸垂までの比較と C の別名は最後に追従する。

まとまり単位で見ると、写像対象の中に随伴・比較・登録があり、懸垂の中に次数1の定義と派生するモデル比較がある。共通のまとまりを一括で動かすより、宣言の依存で順序を指定する。カーネルで得た主要なまとまり間の辺は以下のとおり。

| 利用側 | 参照先 | 相異なる宣言対 |
| --- | --- | ---: |
| 写像対象と豊穣化 | 各段のテンソル | 209 |
| 写像対象と豊穣化 | 基本と構造射 | 122 |
| 自由スペクトルと各段の表示 | 基本と構造射 | 116 |
| 内部 Hom と次数のずらし | 基本と構造射 | 100 |
| 懸垂 | 基本と構造射 | 73 |
| 各段のテンソル | 基本と構造射 | 66 |
| 余テンソル | 基本と構造射 | 54 |
| 懸垂 | 各段のテンソル | 50 |
| 写像対象と豊穣化 | 余テンソル | 48 |
| 余テンソル | 内部 Hom と次数のずらし | 38 |
| 懸垂 | 写像対象と豊穣化 | 34 |
| 極限と余極限 | 基本と構造射 | 31 |
| 余テンソル | 各段のテンソル | 25 |
| 内部 Hom と次数のずらし | 懸垂 | 19 |

### A へ移す候補と既存の A


- **`CategoryTheory/Monoidal/Mod/Limits.lean`（1 件）**。忘却の極限・余極限の生成と同型の反映は既存。台の零対象から加群の始対象が零であることをまとめた同じ補題は確認できなかった。
  `initial_isZero`（`Zero.lean:25`）。

- **`Spectra/SymmetricSequence/Convolution.lean`（2 件）**。畳み込みの生成自然変換は既存。次数の対へ絞った成分と左右ブロック置換の式をその隣に置く案。
  `pairing`（`StructureMaps.lean:28`）、`pairing_equivariance`（`StructureMaps.lean:34`）。

- **`Spectra/SymmetricSequence/PointwiseTensorModule.lean`（2 件）**。固定係数の加群上の関手と自由第0段からの対象別同型が既存。FunctorTransport の一般の輸送を使い、係数も動かす比較をまとめる。
  `pointwiseTensorBifunctor`（`PointwiseTensor.lean:52`）、`tensorFreeZeroPointwiseBifunctorIso`（`PointwiseTensor.lean:56`）。

- **`Spectra/SymmetricSequence/PointwiseTensorModuleAssociator.lean`（2 件）**。対象別の結合同型と各段の順・逆成分は既存。スペクトル射の変数の自然性と自然同型の束ねを対象別比較の隣に置く。
  `pointwiseTensorAssociator_naturality`（`PointwiseTensor.lean:90`）、`pointwiseTensorAssociatorNatIso`（`PointwiseTensor.lean:107`）。

- **`Spectra/SymmetricSequence/PointwiseTensorMapLevels.lean`（1 件）**。台の成分に関する pointwiseTensorPostLevelLaw は既存。加群の輸送で選んだ係数射に対して同じ各段成分を得るには入力の同定が要る。
  `pointwiseTensorPost_level`（`PointwiseTensorCoherence.lean:37`）。

- **`Spectra/SymmetricSequence/PointwiseTensorCoherence.lean`（1 件）**。五角形と単位の一般式は既存。二つの係数射を同時に動かす結合子の自然性を候補にした。
  `pointwiseTensorAssociator_parameter_naturality`（`PointwiseTensorCoherence.lean:142`）。

- **`CategoryTheory/Enriched/RepresentedMapping.lean`（1 件）**。transportedParametrizedAdjunction、enriched_pre/post、homFunctorIso_ofParametrized が既存。固定した随伴の選び方が同じか照合が要る候補は推定として分けた。
  `pointwiseTensorMappingParametrizedAdjunction`（`ParametrizedMapping.lean:31`）。

- **`CategoryTheory/Enriched/TensorCotensor.lean`（29 件）**。EnrichedRepresentability は同型・自然性・点の両立をフィールドとして要求する。これらを作用の結合子と二変数随伴から組み立てる手順を移動候補にした。右随伴の比較とその自然性は CategoryTheory/Adjunction/Comparison.lean から再利用できる。
  `cotensorMappingParameterIso`（`CotensorMappingObject.lean:24`）、`cotensorMappingNatIso`（`CotensorMappingObject.lean:45`）、`cotensorMappingAdjunction_naturality_parameter`（`CotensorMappingParameter.lean:19`）、`cotensorMappingPowerAdjunction_naturality_parameter`（`CotensorMappingParameter.lean:35`）、`cotensorMappingIso_naturality_parameter`（`CotensorMappingParameter.lean:51`）、`cotensorMappingPowerAdjunction_unit`（`CotensorMappingPoints.lean:18`）、`cotensorMappingIso_arrow`（`CotensorMappingPoints.lean:31`）、`cotensorEnrichedMappingIso_points`（`CotensorMappingPoints.lean:68`）、`cotensorMappingAdjunction_naturality_source`（`CotensorMappingSource.lean:21`）、`cotensorMappingPowerAdjunction_naturality_source`（`CotensorMappingSource.lean:36`）、`cotensorMappingIso_naturality_source`（`CotensorMappingSource.lean:54`）、`cotensorMappingBifunctorIso`（`CotensorMappingSource.lean:83`）、`tensorEnrichedMappingIso`（`EnrichedMappingObjects.lean:29`）、`cotensorEnrichedMappingIso`（`EnrichedMappingObjects.lean:38`）、`tensorEnrichedMappingIso_hom_app`（`EnrichedMappingParameter.lean:23`）、`cotensorEnrichedMappingIso_hom_app`（`EnrichedMappingParameter.lean:28`）、`tensorEnrichedMappingIso_parameter`（`EnrichedMappingParameter.lean:34`）、`cotensorEnrichedMappingIso_parameter`（`EnrichedMappingParameter.lean:45`）、`tensorMappingParameterIso`（`TensorMappingObject.lean:24`）、`tensorMappingPowerAdjunction`（`TensorMappingObject.lean:33`）、`tensorMappingNatIso`（`TensorMappingObject.lean:39`）、`tensorMappingPowerAdjunction_naturality_parameter`（`TensorMappingParameter.lean:19`）、`tensorMappingIso_naturality_parameter`（`TensorMappingParameter.lean:45`）、`tensorMappingPowerAdjunction_unit`（`TensorMappingPoints.lean:18`）、`tensorMappingIso_arrow`（`TensorMappingPoints.lean:36`）、`tensorEnrichedMappingIso_points`（`TensorMappingPoints.lean:63`）、`tensorMappingPowerAdjunction_naturality_source`（`TensorMappingSource.lean:20`）、`tensorMappingIso_naturality_source`（`TensorMappingSource.lean:38`）、`tensorMappingBifunctorIso`（`TensorMappingSource.lean:67`）。

### Mathlib の相手

表の Mathlib 候補は次のとおり。同じ Mathlib 宣言を使う行は一緒に示す。型または既存の式を照合したものと、置換をまだ判定できないものを分けた。

#### 確かめた

- `CategoryTheory.Adjunction.comp`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:563`）。`cotensorMappingAdjunction`（`CotensorMappingObject.lean:34`）、`cotensorMappingPowerAdjunction`（`CotensorMappingObject.lean:40`）。
- `CategoryTheory.Adjunction.homEquiv`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:159`）。`pointwiseTensorHomEquiv`（`Cotensor.lean:69`）、`freeAtHomEquiv`（`Evaluation.lean:41`）、`freeAtLift`（`Evaluation.lean:50`）、`mappingObjectHomEquiv`（`MappingObject.lean:48`）。
- `CategoryTheory.Adjunction.homEquiv_naturality_left`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:230`）。`pointwiseTensorHomEquiv_naturality_source`（`Cotensor.lean:72`）、`mappingObjectHomEquiv_naturality_parameter`（`MappingObject.lean:68`）。
- `CategoryTheory.Adjunction.homEquiv_naturality_right`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:237`）。`pointwiseTensorHomEquiv_naturality_target`（`Cotensor.lean:79`）、`mappingObjectHomEquiv_naturality_target`（`MappingObject.lean:74`）。
- `CategoryTheory.Adjunction.homEquiv_unit`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:180`）。`freeAtHomEquiv_apply`（`Evaluation.lean:62`）。
- `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`（`Mathlib/CategoryTheory/Adjunction/Limits.lean:90`）。`free_preservesColimits`（`Limits.lean:60`）、`freeAt_preservesColimits`（`Limits.lean:63`）。
- `CategoryTheory.Adjunction.left_triangle_components`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:114`）。`tensorCotensor_triangle`（`Cotensor.lean:85`）。
- `CategoryTheory.Adjunction.ofNatIsoRight`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:493`）。`freeZeroTensorCotensorAdjunction`（`Cotensor.lean:60`）。
- `CategoryTheory.Adjunction.rightAdjointUniq`（`Mathlib/CategoryTheory/Adjunction/Unique.lean:102`）。`simplicialCotensorNatIso`（`SimplicialSuspensionComparison.lean:27`）、`simplicialLoopNatIso`（`SimplicialSuspensionComparison.lean:38`）。
- `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`（`Mathlib/CategoryTheory/Adjunction/Unique.lean:127`）。`simplicial_suspensionLoopCounit`（`SimplicialSuspensionComparison.lean:55`）。
- `CategoryTheory.Adjunction.right_triangle_components`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:117`）。`cotensorTensor_triangle`（`Cotensor.lean:89`）。
- `CategoryTheory.Adjunction.unit`（`Mathlib/CategoryTheory/Adjunction/Basic.lean:110`）。`freeAtGenerator`（`Evaluation.lean:46`）。
- `CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`（`Mathlib/CategoryTheory/Adjunction/Unique.lean:112`）。`simplicial_suspensionLoopUnit`（`SimplicialSuspensionComparison.lean:45`）。
- `CategoryTheory.IsModHom.smul_hom`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:188`）。`action_hom`（`Basic.lean:61`）。
- `CategoryTheory.Iso.app`（`Mathlib/CategoryTheory/NatIso.lean:51`）。`cotensorMappingIso`（`CotensorMappingObject.lean:50`）、`pointwiseTensorUnitIso`（`PointwiseTensorCoherence.lean:80`）、`tensorMappingIso`（`TensorMappingObject.lean:45`）。
- `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`（`Mathlib/CategoryTheory/Limits/IsLimit.lean:153`）。`intervalBoundaryCoproductIso`（`SimplicialCylinder.lean:99`）。
- `CategoryTheory.Limits.IsInitial.isZero`（`Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean:569`）。`pointwiseTensor_isZero_of_isZero`（`SuspensionPushout.lean:31`）。
- `CategoryTheory.Limits.IsZero.eq_of_src`（`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:79`）。`circleTensorBasepoint_eq_zero`（`SuspensionPushout.lean:69`）。
- `CategoryTheory.Limits.IsZero.eq_of_tgt`（`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:78`）。`intervalBoundaryCollapse_eq_zero`（`SuspensionPushout.lean:66`）。
- `CategoryTheory.Limits.IsZero.of_iso`（`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:107`）。`freeAtLevelBlockQuotient_isZero`（`FreeLevelQuotient.lean:81`）、`freeAtLevel_isZero`（`FreeLevels.lean:85`）。
- `CategoryTheory.Mod`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:227`）。`GeneralSymmetricSpectrum`（`Basic.lean:28`）、`mk`（`Basic.lean:65`）。
- `CategoryTheory.Mod.Hom.mk'`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:278`）。`homMk`（`Basic.lean:75`）。
- `CategoryTheory.Mod.X`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:229`）。`underlying`（`Basic.lean:37`）。
- `CategoryTheory.Mod.forget`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:347`）。`forget`（`Basic.lean:39`）。
- `CategoryTheory.Mod.hom_ext`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:319`）。`forget_faithful`（`Basic.lean:41`）。
- `CategoryTheory.Mod.regular`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:336`）。`sphere`（`Sphere.lean:29`）、`sphere_underlying`（`Sphere.lean:32`）、`sphere_action`（`Sphere.lean:35`）。
- `CategoryTheory.ModObj.mul_smul_self`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:159`）。`action_assoc`（`Basic.lean:55`）。
- `CategoryTheory.ModObj.one_smul_self`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:154`）。`action_unit`（`Basic.lean:51`）。
- `CategoryTheory.ModObj.smul`（`Mathlib/CategoryTheory/Monoidal/Mod.lean:61`）。`action`（`Basic.lean:47`）。
- `CategoryTheory.MonoidalClosed.uncurry_curry`（`Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:180`）。`uncurry_adjointStructureMap`（`Suspension.lean:39`）。
- `CategoryTheory.NatTrans.app`（`Mathlib/CategoryTheory/NatTrans.lean:56`）。`pointwiseTensorPost`（`PointwiseTensorCoherence.lean:20`）。
- `CategoryTheory.NatTrans.comp_app`（`Mathlib/CategoryTheory/Functor/Category.lean:76`）。`levelMap_comp`（`Basic.lean:95`）。
- `CategoryTheory.NatTrans.id_app`（`Mathlib/CategoryTheory/Functor/Category.lean:73`）。`levelMap_id`（`Basic.lean:91`）。
- `CategoryTheory.NatTrans.naturality`（`Mathlib/CategoryTheory/NatTrans.lean:58`）。`circleTensorQuotient_naturality`（`CircleSuspensionNaturality.lean:62`）、`cotensorMappingIso_naturality_target`（`CotensorMappingObject.lean:63`）、`tensorMappingIso_naturality_target`（`TensorMappingObject.lean:59`）。
- `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_one`（`Mathlib/CategoryTheory/Adjunction/Parametrized.lean:98`）。`pointwiseTensorHomEquiv_naturality_parameter`（`ParametrizedCotensor.lean:41`）。
- `CategoryTheory.preservesColimitIso`（`Mathlib/CategoryTheory/Limits/Preserves/Limits.lean:122`）。`colimitLevelIso`（`Limits.lean:88`）。
- `CategoryTheory.preservesLimitIso`（`Mathlib/CategoryTheory/Limits/Preserves/Limits.lean:54`）。`limitLevelIso`（`Limits.lean:80`）。
- `CategoryTheory.preservesLimitIso_hom_π`（`Mathlib/CategoryTheory/Limits/Preserves/Limits.lean:58`）。`limitLevelIso_hom_π`（`Limits.lean:83`）。
- `CategoryTheory.ι_preservesColimitIso_hom`（`Mathlib/CategoryTheory/Limits/Preserves/Limits.lean:131`）。`colimitLevelIso_ι_hom`（`Limits.lean:92`）。
- `Equiv.apply_symm_apply`（`Mathlib/Logic/Equiv/Defs.lean:247`）。`freeAtGenerator_lift`（`Evaluation.lean:68`）、`curry_uncurry`（`TensorClosed.lean:57`）。
- `Equiv.injective`（`Mathlib/Logic/Equiv/Defs.lean:177`）。`freeAtLift_unique`（`Evaluation.lean:82`）。
- `Equiv.symm`（`Mathlib/Logic/Equiv/Defs.lean:144`）。`mappingObjectArrowInverse`（`MappingEnrichment.lean:89`）。
- `Equiv.symm_apply_apply`（`Mathlib/Logic/Equiv/Defs.lean:249`）。`freeAtLift_generator`（`Evaluation.lean:75`）、`uncurry_curry`（`TensorClosed.lean:54`）。

#### 名前と型から推定

- `CategoryTheory.Limits.PreservesColimitsOfSize`（`Mathlib/CategoryTheory/Limits/Preserves/Basic.lean:97`）。`forget_preservesColimits`（`Limits.lean:70`）。
- `CategoryTheory.Limits.PreservesLimitsOfSize`（`Mathlib/CategoryTheory/Limits/Preserves/Basic.lean:84`）。`forget_preservesLimits`（`Limits.lean:67`）。

### C の残り

型と本体の定数参照を依存として追った。補助証明の参照は親へ寄せ、解決済みのソース参照も加えた。C 50 件について、円周への型・本体の最短経路を表の `coordinate_dependency` に記した。型略記 `SymmetricSpectrum` そのものは、本体で円周を選ぶ。単体係数や正則加群では、型に円周が現れる経路と、構成の引数として円周が必要かどうかを分けて判断した。

- `sphereTensorFreeZeroPointwiseNatIso`、`structureMap_eq_convolutionComponent`、`sphere_structureMap`、`simplicialMappingSpaceBifunctor_obj` の使用者は、範囲内・範囲外・検査で計 0。最初は B の既存同型の別名、二番目と四番目は定義等式。三番目は正則加群の次数付き構造射の式なので、任意の K へ移せるかを判定するまで保留した。
- `sphere_underlying` と `sphere_action` は `rfl`。台を取ることと正則加群の作用を展開することで再現できる。`simplicialTensorCotensorHomEquiv_post` は B の係数自然性へ自由基点追加の射を与える一行で、段 2 検査で参照される。
- `pointedMappingSpaceParametrizedAdjunction` は、字面は `abbrev` だが、自由第0段の随伴を各段テンソル比較で輸送してレコードを構成する。B の `pointwiseTensorMappingParametrizedAdjunction` は同じ両端を `ParametrizedAdjunction.mk'` で結ぶ。円周は座標に入る。モデル側の `ordinarySpectrumMappingAdjunction` と `pointedSpectrumMapping_SM7` が C の構成を使うため、B で統一するなら成分の転置と原変数自然性が既存の利用型で揃うかを確認する。

**基点付き単体集合上の任意の座標。** `Simplicial.lean` の対象の係数は `adjoinBasepoint` の像で、写像空間の側は基点忘却を使う。円周への直接参照は一般構成の座標引数などにある。C の型を `GeneralSymmetricSpectrum PointedSimplicialSet K₀` に置換し、B の作用・余作用・写像対象を引数 `K₀` で使う案。B の `SimplicialCylinder.lean` にある `simplicialParameterFunctor` は既に任意の座標を使う。汎用の係数関手をモデル仮定より前に共通化し、基点なしの写像空間・零次同値・係数の単位と直積の比較を同じ箇所から使う。モデル側の `SimplicialLevelEnriched` と `SimplicialHomComparison` は B の係数 API を直接 import して `K₀ := circle` を指定する。Inputs の豊穣通常圏はこのモデル側の登録を通じて受け取る。安定側では、円周そのものを作用係数とする懸垂・ループとその随伴を、引き続き C の専門名で書ける。

**一般の正則スペクトル。** `sphere = Mod.regular sphereSequence` の台と作用は正則加群の一般式。一般の `(C,K)` では係数を `tensorPowerSequence K` にし、B の `structureMap` に `tensorPowerMultiplication_fac_app` を適用すれば、構造射を `TensorPowers.appendIso` の順射で表示する候補になる。現在の `sphere_structureMap` は球面固有の表示から証明しており、一般表示での置換は推定。球面 4 件には C の外の宣言使用者が見つからず、`sphere` の使用者は同じファイルの 3 補題。C には円周を固定する型、懸垂・ループの名前、球面の置換など円周に根拠がある表示が残る。モデル・安定側で正則加群を使うときは、一般の B の入口に座標を渡す。

### 円周専用の比較ファイル

- **`SimplicialComparison.lean`（6 件）**。6 件とも定義展開で同じ対象や射になる。比較を使う箇所を一般側の式か定義展開で置き換えたうえで、比較モジュールを消す案。`SimplicialLevel.lean` の直接 import を必要な宣言の提供元へ替え、監査が検査しているモジュール名も追従する。
- **`SimplicialSuspensionComparison.lean`（8 件）**。関手の定義等式 2 件と右随伴一意性を使う 4 件は既存の構成で置換する案。単位・余単位は `check_spectrum_suspension_geometry` が参照する。残る構造射とその転置は球面の冪1の表示付きであり、展開で置換できるかを確かめる。独立した表示として残す場合は C の懸垂の隣に移す案。`OrdinarySuspension.lean` はその提供元と必要な一般論を直接 import する。

### 未使用の途中の段と判断を保留した宣言

- `pointwiseTensorMap`（`PointwiseTensor.lean:72`）。係数射からの成分と対象射の関手像を合成した二変数の射。uncurry 側の map に置き換わるかを確認する。

次は「判断できない」の一覧。理由と相手候補は分類表の同じ行にある。

- **B（15 件）**。`hom_index_eq`（`Basic.lean:79`）、`simplicialCylinder_i₀_naturality`（`CircleSuspensionNaturality.lean:76`）、`simplicialCylinder_i₁_naturality`（`CircleSuspensionNaturality.lean:81`）、`lift_unique`（`Free.lean:63`）、`free_forget_eq_tensorLeft`（`Free.lean:70`）、`forget_createsColimits`（`Limits.lean:31`）、`forget_preservesLimits`（`Limits.lean:67`）、`forget_preservesColimits`（`Limits.lean:70`）、`eHomWhiskerRight_eq_mappingObjectMap`（`MappingFunctorComparison.lean:67`）、`mappingEnrichedHomFunctorIso`（`MappingFunctorComparison.lean:77`）、`cotensorMappingHomEquiv`（`MappingObject.lean:59`）、`mappingHom_compatibility`（`MappingObject.lean:63`）、`pointwiseTensorMap`（`PointwiseTensor.lean:72`）、`pointwiseTensorAssociator_parameter_left`（`PointwiseTensorCoherence.lean:156`）、`pointwiseTensorAssociator_parameter_right`（`PointwiseTensorCoherence.lean:170`）。
- **比較（2 件）**。`simplicial_suspensionMap`（`SimplicialSuspensionComparison.lean:65`）、`simplicial_adjointStructureMap`（`SimplicialSuspensionComparison.lean:70`）。
- **C（22 件）**。`evaluation`（`Basic.lean:54`）、`pointedMappingSpaceParametrizedAdjunction`（`Basic.lean:116`）、`simplicialTensor`（`Simplicial.lean:38`）、`simplicialCotensor`（`Simplicial.lean:42`）、`simplicialTensorFunctor`（`Simplicial.lean:46`）、`simplicialCotensorFunctor`（`Simplicial.lean:50`）、`simplicialTensorParameterFunctor`（`Simplicial.lean:54`）、`simplicialMappingSpaceFunctor`（`Simplicial.lean:59`）、`simplicialTensorMappingAdjunction`（`Simplicial.lean:64`）、`simplicialTensorCotensorAdjunction`（`Simplicial.lean:69`）、`simplicialMappingSpace`（`Simplicial.lean:74`）、`simplicialMappingSpaceBifunctor`（`Simplicial.lean:78`）、`simplicialMappingComposition`（`Simplicial.lean:89`）、`simplicialMappingVertexEquiv`（`Simplicial.lean:97`）、`mappingSpaceSimplicialCategory_vertexEquiv`（`Simplicial.lean:103`）、`simplicialTensorPost`（`Simplicial.lean:114`）、`simplicialCotensorPre`（`Simplicial.lean:119`）、`simplicialMappingSpacePre`（`Simplicial.lean:125`）、`simplicialTensorUnitNatIso`（`Simplicial.lean:138`）、`simplicialTensorProductNatIso`（`Simplicial.lean:143`）、`sphere`（`Sphere.lean:29`）、`sphere_structureMap`（`Sphere.lean:38`）。

### 採取範囲と照合

main の取り込みから分類・照合・報告まで約 25 分。

- `Spectra/` を起点に全追跡 Lean の import を読み、逆向きに到達する 9,954 モジュール・スクリプトを洗った。対象の B・C・比較まで import 経路がある現役の本体は 93 モジュール。型・本体のカーネル定数依存と `.ilean` の解決済み参照を合わせ、参照元ごとに一件と数えた。B の行では B と比較を範囲内、C の行では C を範囲内とした。C・ModelCategory・Stable・Inputs は範囲外の列でそれぞれ確認できる。対応表の名指しは宣言欄を照合した。
- 監査・検査の列は宣言名を直接使うスクリプトの本数。名前解決した参照と監査の明示的な完全修飾名を用いた。モジュール全体を列挙する監査の対象指定はコードの利用数に加えていない。36 本から採取し、うち 20 本で採取時に elaboration エラーが出た。そこでは解決済みの参照と明示名までを採り、解決できなかった式の暗黙依存は計数の外にある。
- bulk 鍵で、必要な既存アーティファクトのビルドと採取だけを行った。root 全体のビルドは実施せず、段 10 の差分は分類表・報告と証拠目録。Lean ソース・監査・文献対応表の差分は 0。

[証拠目録](../../../evidence/spectra-unify/stage10/manifest.json)の基準点は `4ac20dbd1`。型・本体を並べた採取、使用者の一覧、依存経路、Mathlib の語と検索結果を外部証拠に保存した。

## 段 11　未使用の宣言と既存補題の当てはめを整理

`main` の `38b8247f6` を `3bad4fc39` で取り込んだ。段10で「消す」とした207件に `stage11` 列を追加し、`消す`、`名前として残す`、`後の段` の判定を記入した。元の列と437行は保持した。[段10・11の分類表](../../../research/cleanup-zero-base/spectra/stage10.csv)

### 再判定と保護した宣言

| 範囲 | 未使用で削除 | 当てはめ・定義展開で削除 | 名前として残す | 後の段 |
|---|---:|---:|---:|---:|
| B | 46 | 39 | 26 | 69 |
| 円周との比較 | 7 | 3 | 0 | 2 |
| C | 5 | 1 | 6 | 3 |
| 計 | 58 | 43 | 32 | 74 |

指示書にある未使用76件に対し、この版の表では、段10の「消す」のうち、本体・監査・検査・対応表に使用者の記録がない行は63件だった。58件を削除し、5件は文献上の構成を指す名前として残した。

未使用の理論の主張5件は `hom_ext`、`pointwiseTensorCurry_level`、`cotensor_structureMap`、`cotensor_suspensionMap`、`tensorFreeAtSumNatIso`。「判断できない」39件と「A へ移す」39件を含め、83件の宣言本文を変更前後で照合した。

### 名前として残した構成

文献上の構成を利用側から指せるよう、現在の名前を残した。同じ候補名でも、一般スペクトル（B）と円周を固定したスペクトル（C）では、それぞれの名前空間の宣言を指す。

| 範囲 | 名前 | 残した理由 |
|---|---|---|
| B | `underlying` | 台の対称列 |
| B | `action` | Sym(K) の作用 |
| B | `internalHomBifunctor` | 内部 Hom の二変数関手 |
| B | `freeAtHomEquiv` | 自由スペクトルの生成次数での普遍性 |
| B | `freeAtGenerator` | 自由スペクトルの生成元 |
| B | `freeAtLift` | 自由スペクトルの普遍性による延長 |
| B | `lift` | 自由内部加群の延長。自由スペクトルの延長の比較で使う |
| B | `freeHomEquiv` | 自由内部加群の普遍性 |
| B | `freeAtLevelGenerator` | 自由スペクトルを段ごとに構成する生成射 |
| B | `mappingObjectEvaluation` | 写像対象の評価射 |
| B | `mappingObjectComposition` | 豊穣圏の合成 |
| B | `mappingObjectUnit` | 豊穣圏の単位 |
| B | `mappingObjectArrowEquiv` | 通常射と写像対象の点との同値 |
| B | `mappingObjectArrow` | 通常射に対応する写像対象の点 |
| B | `mappingTensorFunctor` | スペクトルを固定して係数を動かすテンソル |
| B | `mappingObjectHomEquiv` | 写像対象を特徴づける普遍性 |
| B | `ordinaryHomEquiv` | 豊穣の通常射を読む同値。段11では他の同値との統合を保留 |
| B | `pointwiseTensor` | スペクトルの各段へのテンソル作用 |
| B | `shiftedHom` | 次数をずらした内部 Hom |
| B | `tensor` | スペクトル間の相対テンソル |
| B | `internalHom` | スペクトル間の内部 Hom |
| B | `internalHomFunctor` | 内部 Hom の関手 |
| B | `tensorHomEquiv` | 内部 Hom の普遍性 |
| B | `tensorInternalHomAdjunction` | テンソルと内部 Hom の随伴 |
| B | `curry` | 内部 Hom の転置。テンソル・内部 Hom の式で使う |
| B | `uncurry` | 内部 Hom の逆転置 |
| C | `forget` | 円周スペクトルの忘却関手 |
| C | `freeObj` | 円周の自由スペクトルの対象 |
| C | `freeFunctor` | 円周の自由スペクトルの関手 |
| C | `generator` | 円周で固定した自由内部加群の生成元 |
| C | `freeAtGenerator` | 円周スペクトルの生成次数の生成元 |
| C | `internalHomBifunctor` | 円周スペクトルの内部 Hom の二変数関手 |

### 利用側と次の段

- `simplicial_cotensor` を参照した検査は、余テンソルの定義等式を `rfl` で検査する。
- 各段の極限の射に関する `limitLevelIso_hom_π F n j` は `preservesLimitIso_hom_π (evaluation n) F j` で示す。評価関手が明示される。
- `freeAtGenerator_lift` を使う箇所では、随伴の `homEquiv_unit` で生成射との合成を Hom 同値として書き、`apply_symm_apply` を適用する。式が長くなる一方で、随伴と同値のどの法則を使うかが読める。
- `DisjointUnion.lean` と `FiniteBijection.lean` は import だけだったため削除した。対称列の `Basic.lean`、`Convolution.lean`、`SumCoherence.lean` の3箇所を `SerrePositivity.CategoryTheory.Limits` に付け替えた。6件の比較補題を除いた `SimplicialComparison.lean` は既存の入口として import を公開する。宣言を所有することを要求する監査の一覧から、この入口を2箇所外した。

次は自由スペクトルの生成次数とブロック商の表示をそろえ、次いで各段テンソル・余テンソル・写像対象の比較をまとめて点検する。その後、円周を固定する比較のうち座標に固有の性質を使わないものを任意の座標へ一般化する。球面スペクトルの正則加群としての表示もその段で照合する。

### ファイルと行数

| 範囲 | ファイル数 | ソース行数 | 段10の分類対象の宣言数 |
|---|---:|---:|---:|
| Spectra 全体 | 209 → 207 | 19,582 → 19,037 | 437 → 336 |
| General（円周との比較を含む） | 52 → 52 | 4,502 → 3,987 | 387 → 292 |
| SymmetricSpectrum（C） | 3 → 3 | 327 → 298 | 50 → 44 |

ソース行数は import、コメント、空行も含む。利用側で書き換えた67箇所のうち、本体は41箇所、検査は26箇所。import 3箇所と監査のモジュール一覧2箇所は別に数えた。

### ビルドと宣言の照合

bulk 鍵で Spectra と現役本体の逆 import 閉包をビルドした。変更前9,061、変更後9,059モジュール。前後それぞれ98個の到達点を指定し、成果物の import から全範囲をたどり直した。消した2モジュールを import する現行の成果物は0件。Archive は README に記載されたビルド対象外にある。

カーネル成果物の宣言は全範囲で87,309件から87,201件、Spectra 内で2,626件から2,518件。前後に共通する87,194件で、所有モジュール、カーネル名、宇宙変数と型のハッシュが一致した。選んだ101件のカーネル名はすべて消え、付随する生成物13件も消えた。既存の宣言の公理依存の追加は0件。`sorryAx` 依存は前後で同じ18件。未使用として外した58件は、変更前に保存した項を変更後の環境で型検査し、元の型に一致することも確認した。

新しい内部補助名 `_proof_*` は7件。円筒の比較（`CircleHomotopySuspension`）に2件、写像対象の豊穣圏構造（`MappingEnrichment`）に5件ある。残した `simplicialLoopNatIso` の方程式補題 `eq_1` は、変更後の成果物では未生成だった。前後の環境で生成を要求し、完全名、型のハッシュ、公理依存が一致することを確認した。明示的な生成を求めるコードは検証用のファイルに置いた。

現行の本体、スクリプト、対応表、blueprint の生成器と生成物で、削除した宣言の完全修飾名への文字参照は0件。変更後のカーネル型・値が参照する定数にも該当は0件。監査・検査46本は、前後とも26本が成功し、20本が変更前と同じ診断で失敗した。ファイルの絶対パスと行・列の位置を除いてエラー本文を比較した。公理監査と `sorry` 閉包監査は前後とも通過した。

### 検証で調整した箇所と所要時間

構造射と自由スペクトルの商では、一般補題を使う前に、合成や等式を既存の記法で明示した。豊穣モデルの検査には局所の型クラスを明示した。円周での単位則を直接代入した検査はカーネルの時間切れになったため、同じ検査例の中で一般の圏の単位則を示し、それから円周を代入した。これで元の検査の主張が通る。並行した監査で OS のファイル数上限に当たった箇所は、既存のビルド成果物で監査を直列に実行し直した。

11月20日（日本時間）の bulk 鍵待ちは約3時間43分。変更前のビルドは26.9秒、変更後の全体ビルドは34分23秒。カーネルの採取は前43.1秒・後36.0秒。監査の直列再実行は変更前約40分、変更後約59分で、変更後の時間には環境エラーが出た変更前の公理監査1本の再実行を含む。その後、利用側で修正した検査を再実行した。

ビルド、カーネル照合、監査のログは git の外に置いた。[証拠目録](../../../evidence/spectra-unify/stage11/manifest.json)

## 段12・13　自由スペクトル・写像対象の重複を整理

`main` の `ff254d593` を取り込んだ。自由スペクトルの作用付き自然同型の型に現れる `freeAtLevelInductionActionFunctor` は、11月21日の判断に従って名前を残した。以後の候補にも、残す型に現れる名前を保持する規則を適用した。

段12は `199cabdb3` にコミットした。保護対象105件は両段でソースを照合した。両段の削除対象を名指しする文献対応表の行は0件。

### 段11から復元した補題

| ファイル | 復元した補題 |
|---|---|
| `General/Basic.lean` | `action_assoc`、`action_hom`、`levelMap_comp` |
| `General/Evaluation.lean` | `freeAtHomEquiv_apply`、`freeAtGenerator_lift` |
| `General/FreeLevelQuotient.lean` | `freeAtLevelIsoBlockQuotient_generator`（後合成補題を含む） |
| `General/PointwiseTensorCoherence.lean` | `pointwiseTensorUnitIso_level` |
| `General/SuspensionPushout.lean` | `intervalBoundaryCollapse_eq_zero` |
| `General/TensorFreeAtSum.lean` | `tensorFreePair_naturality` |

`Stable/LocalizingMaps.lean` では、段11で19行になった3つの変更箇所を計5行に戻した。作用の両立式、ブロック商、自由対象のテンソル、境界写像、各段テンソルの単位則を使う箇所でも、等式の書き直しを復元した補題への参照に戻した。


### 段12

37件を照合し、6件を削除、31件を保持した。

Spectra のファイル数は 207 → 207 本、ソース行数は 19,037 → 19,019 行、成果物に記録されたカーネル宣言は 2,518 → 2,519 件。

#### 削除した宣言

| 宣言 | 理由 |
|---|---|
| `freeAtLevelInductionAction` | 利用側は同時に外す作用付き同型の型だけ。 |
| `freeAtLevelActionIsoInduction` | 自然同型の成分に一般の freeConvolutionLevelActionIsoInduction を2行で指定した。 |
| `freeAtLevelDiagram` | 現行の利用箇所がない。対称列に freeConvolutionDiagram がある。 |
| `freeAtLevelInitial` | 匿名の検査1箇所で一般の freeConvolutionLevelInitial を使用。 |
| `limitLevelIso` | 匿名の検査1箇所で preservesLimitIso を使用。 |
| `colimitLevelIso` | 匿名の検査1箇所で preservesColimitIso を使用。 |

#### 主張に現れるので残した定義

| 宣言 | 理由 |
|---|---|
| `freeZeroTensorCotensorAdjunction` | cotensorEvaluation_formula と cotensorEvaluation_level の型に現れる。 |
| `pointwiseTensorHomEquiv` | 保護対象の mappingHom_compatibility の型に現れ、随伴の自然性の式にも使う。 |
| `freeAtLevelInductionDiagram` | freeAtLevelIsoInduction と freeAtLevelIsoInduction_input の型に現れる。 |
| `freeAtLevelIsoInduction` | freeAtLevelIsoInduction_input の型に現れる。モデル構造側でも同じ同型を繰り返し使う。 |
| `freeAtLevelInductionActionFunctor` | freeAtLevelActionNatIsoInduction の型の同型先。11月21日の判断を適用。 |
| `freeAtLevelBlockQuotient` | freeAtLevelBlockGenerator と freeAtLevelIsoBlockQuotient の型に現れる。 |
| `freeAtLevelBlockGenerator` | 今回復元した freeAtLevelIsoBlockQuotient_generator の型に現れる。 |
| `freeAtLevelIsoBlockQuotient` | 今回復元した freeAtLevelIsoBlockQuotient_generator の型に現れる。 |
| `pointwiseTensorAssociator` | pointwiseTensorAssociator_level や保護対象の pointwiseTensorAssociator_parameter_left・right の型に現れる。 |
| `pointwiseTensorPost` | pointwiseTensorPost_level、各種自然性、余テンソルと写像対象の比較の型に現れる。 |
| `pointwiseTensorUnitIso` | 復元した pointwiseTensorUnitIso_level の型に現れる。写像対象の単位と評価にも繰り返し使う。 |
| `pointwiseTensorTriangleLaw` | pointwiseTensor_triangle の型に現れる。 |
| `pointwiseTensorLeftUnitLaw` | pointwiseTensor_left_unit の型に現れる。 |

#### 利用側の可読性または保護対象の証明のために残した宣言

| 宣言 | 理由 |
|---|---|
| `internalHomCotensorNatIso` | 余テンソルの関手、随伴、二変数の自然同型の3箇所で展開が重複する。 |
| `pointwiseTensorHomEquiv_naturality_source` | A へ移す cotensorMappingIso_arrow と cotensorMappingAdjunction_naturality_source の現行証明で使う。 |
| `pointwiseTensorUncurry_level` | 未使用の理論の主張として保護した pointwiseTensorCurry_level の現行証明で使う。 |
| `freeAtLift_unique` | freeAtLift_eq から呼ぶ。一般の単射性を使うには単位と Hom 同値の逆律を用いる証明を呼び出し元に3行以上書く。 |
| `generator_lift` | 判断できない lift_unique の証明で使う。自由加群への延長を生成元で計算する等式を保存する。 |
| `freeAtLevelIsoInduction_input` | 作用付き自然同型で1箇所、モデル構造側で2箇所の計3箇所で同じ自然性を使う。入力射を freeAt_map_underlying で書き換える証明が必要。 |
| `forget_createsLimits` | 忘却関手 forget は定義に包まれている。forget_preservesLimits と initial_isZero の型クラス登録を保護する。 |
| `forget_createsColimitsOfShape` | forget_createsColimits、forget_preservesColimits、initial_isZero の既存の型クラス登録を保護する。 |
| `internalHomCotensorBifunctorIso` | 随伴の輸送と二変数の射の比較に現れる。関手と各成分の自然同型を明示すると展開が3行になる。 |
| `pointwiseTensorHomEquiv_naturality_parameter` | A へ移す cotensorMappingAdjunction_naturality_parameter の現行証明に現れ、検査でも展開が3回重複する。 |
| `pointwiseTensor_level` | 各段の作用を計算する等式。保護した結合子の自然性証明2箇所と匿名の検査2箇所で使う。 |
| `tensorFreeZeroPointwiseIso` | 作用の比較で同じ成分同型を3箇所以上に展開することになる。 |
| `tensorFreeZeroPointwiseNatIso` | 保護対象の二変数比較・作用のパラメータ射などで使い、同じ自然同型を3箇所以上に展開することになる。 |
| `pointwiseTensorUnitNatIso` | 左右単位・写像対象など3箇所以上に展開することになり、保護した豊穣圏の別名の本体にも使う。 |
| `pointwiseTensorAssociator_level` | 保護した結合子の自然性の計算で使う。3箇所以上に展開することになる。 |
| `pointwiseTensorPentagonLaw` | 円周で検査する式には、一般の述語、Sym(K)、結合子と係数射を指定する3行の展開が必要。 |
| `pointwiseTensor_triangle` | 保護した cotensorMappingIso_arrow の証明で使う。同じ計算式の展開も3箇所以上になる。 |
| `pointwiseTensor_left_unit` | 保護した tensorMappingIso_arrow の証明で使う。同じ計算式の展開も3箇所以上になる。 |

bulk 鍵で Spectra と利用側の本体 9,059 モジュールをビルドした。前後に共通する 87,191 件を採取し、残す宣言のカーネル名と型を照合した。内部の補助名は 0 件増え、0 件減った。削除した宣言に付随する生成物は 4 件。削除した名前の現行参照は0件で、公理・`sorryAx` 依存の増加は0件。監査・検査 36 本は成否とエラーの内容が前後で一致し、成功 16 本、既存の失敗 20 本。[証拠目録](../../../evidence/spectra-unify/stage12/manifest.json)

過去の比較目録 `scripts/refactor/targets/w2a-2-v3b-comparison.json` には `limitLevelIso` と `colimitLevelIso` が各6回記録されている。この目録は履歴として保存した。

分類対象のソース宣言は336 → 339件。復元した補題を呼ぶ利用側の参照17箇所を短くした。`open` の名前指定と復元した補題内の参照はこの数の外にある。

段12で削除に伴って置き換えた使用箇所は4箇所。作用付き自然同型の成分1箇所と、始対象・極限・余極限の匿名の検査各1箇所。復元した9件は段11前の成果物にも照合した。


### 段13

37件を照合し、10件を削除、27件を保持した。

Spectra のファイル数は 207 → 207 本、ソース行数は 19,019 → 18,960 行、成果物に記録されたカーネル宣言は 2,519 → 2,509 件。

#### 削除した宣言

| 宣言 | 理由 |
|---|---|
| `enrichedModelOrdinaryCategory` | 局所インスタンスの利用者が段11で消えている。 |
| `mappingObjectCompositionEvaluationLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectUnitEvaluationLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectArrowIdentityLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectLeftUnitLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectRightUnitLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectAssociativityLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectArrowEvaluationLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `mappingObjectArrowCompositionLaw` | 段11の利用側の書き換えにより、現行の利用箇所がない。一般の法則を直接使っている。 |
| `simplicialCotensorNatIso` | 現行の利用箇所がない。既存の随伴から Adjunction.rightAdjointUniq を作れる。 |

#### 主張に現れるので残した定義

| 宣言 | 理由 |
|---|---|
| `cotensorMappingAdjunction` | 保護対象の cotensorMappingAdjunction_naturality_parameter と _source の型に現れる。 |
| `cotensorMappingPowerAdjunction` | 保護対象の cotensorMappingPowerAdjunction_naturality_parameter、_source、_unit の型に現れる。 |
| `cotensorMappingIso` | 保護対象の cotensorMappingIso_arrow と _naturality_source などの型に現れる。 |
| `mappingObjectLeftUnitEvaluationLaw` | mappingObject_left_unit_evaluation の型に現れる。 |
| `mappingObjectRightUnitEvaluationLaw` | mappingObject_right_unit_evaluation の型に現れる。 |
| `mappingObjectAssociativityEvaluationLaw` | mappingObject_associativity_evaluation の型に現れる。 |
| `mappingObjectArrowCompositionEvaluationLaw` | mappingObjectArrow_composition_evaluation の型に現れる。 |
| `shiftedHomStructureIndex` | shiftedHom_structureMap_evaluation や suspensionMap_shiftedIndex の型に現れる。 |
| `intervalBoundaryCoproductIso` | intervalBoundaryCoproductIso_inclusion の型に現れる。 |
| `tensorFreePair` | 復元した tensorFreePair_naturality の型に現れる。 |
| `tensorMappingIso` | 保護対象の tensorMappingIso_arrow、tensorEnrichedMappingIso_hom_app などの型に現れる。 |

#### 利用側の可読性または保護対象の証明のために残した宣言

| 宣言 | 理由 |
|---|---|
| `cotensorMappingNatIso_homEquiv` | 保護対象の cotensorMappingIso_arrow の証明で使う。二つの随伴の同値と同型を明示すると3行以上になる。 |
| `mappingObject_left_unit_evaluation` | 左右の自然性と単位の評価の証明を含む。豊穣圏と豊穣通常圏の証明に展開すると各3行以上になる。 |
| `mappingObject_right_unit_evaluation` | 作用の三角則と評価を組み合わせる証明。豊穣圏と豊穣通常圏の証明に展開すると各3行以上になる。 |
| `mappingObject_associativity_evaluation` | 作用の左右の自然性と五角形を使う。二つの使い手への展開は各3行以上になる。 |
| `mappingObjectArrow_composition_evaluation` | 二つの評価とその自然性の証明を豊穣通常圏の構成に展開すると3行以上になる。 |
| `mappingObjectComposition_post` | eHomWhiskerLeft_eq_mappingObjectMap の証明に主要な比較を展開すると3行以上になる。 |
| `mappingObjectComposition_pre` | 保護対象 eHomWhiskerRight_eq_mappingObjectMap の証明で使う。 |
| `eHomWhiskerLeft_eq_mappingObjectMap` | 保護対象 cotensorEnrichedMappingIso_parameter の証明で使う。 |
| `mappingObjectHomEquiv_naturality_parameter` | 保護対象の余テンソルとテンソルの写像対象比較で、同じ自然性の展開が3箇所以上になる。 |
| `mappingObjectHomEquiv_naturality_target` | 保護対象 cotensorMappingAdjunction_naturality_parameter の証明で使う。 |
| `mappingObjectHomEquiv_naturality_source` | 保護対象の輸送した随伴・二変数の比較で、同じ自然性の展開が3箇所以上になる。 |
| `simplicialLoopNatIso` | 懸垂とループの単位・余単位の検査で同じ右随伴比較を4箇所に使う。 |
| `tensorMappingNatIso_homEquiv` | 保護対象 tensorMappingIso_arrow の証明で使う。写像対象の同値を展開すると3行以上になる。 |
| `sphereTensorFreeAtSum` | モデル構造の自由スペクトルの押し出し積の証明で3箇所以上に現れる。 |
| `pointwiseTensorAssociatorNatIso` | C の保護対象 simplicialTensorProductNatIso の証明で使う。 |
| `pointwiseTensorUnitNatIso` | C の保護対象 simplicialTensorUnitNatIso の証明で使う。 |

bulk 鍵で Spectra と利用側の本体 9,059 モジュールをビルドした。前後に共通する 87,188 件を採取し、残す宣言のカーネル名と型を照合した。内部の補助名は 4 件増え、0 件減った。削除した宣言に付随する生成物は 4 件。削除した名前の現行参照は0件で、公理・`sorryAx` 依存の増加は0件。監査・検査 28 本は成否とエラーの内容が前後で一致し、成功 14 本、既存の失敗 14 本。[証拠目録](../../../evidence/spectra-unify/stage13/manifest.json)

分類対象のソース宣言は339 → 329件。段13で置き換えた使用箇所は0箇所。削除した10件は現行の利用箇所がない。

### 所要時間と検証時の調整

11月21日（日本時間）。段12は再開からコミットまで約21分。取り込み済みの成果物を再利用してビルドした。
段13は 06:01:46 に鍵を申請し、時刻記録の書式エラーを修正して再投入した。検証開始 06:38:20、全体ビルド完了 06:39:51、監査・検査の照合完了 06:44:30。

### 段14の型の一覧案（39件）

型は現在の宣言ヘッダーから採った。名前空間と節変数はリンク先を参照。段14で A 側の相手と型・仮定を並べて照合する。

#### 写像対象と豊穣化（30件）

[cotensorMappingParameterIso](../../../SerrePositivity/Spectra/General/CotensorMappingObject.lean#L24)

```lean
def cotensorMappingParameterIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorLeft X ⋙ mappingTensorFunctor E ≅ mappingTensorFunctor E ⋙ pointwiseTensorFunctor X
```

[cotensorMappingNatIso](../../../SerrePositivity/Spectra/General/CotensorMappingObject.lean#L45)

```lean
def cotensorMappingNatIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    cotensorFunctor X ⋙ mappingObjectFunctor E ≅ mappingObjectFunctor E ⋙ ihom X
```

[cotensorMappingAdjunction_naturality_parameter](../../../SerrePositivity/Spectra/General/CotensorMappingParameter.lean#L19)

```lean
lemma cotensorMappingAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K)
    (g : pointwiseTensor Y (pointwiseTensor Z E) ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        (pointwiseTensorPost f (pointwiseTensor Z E) ≫ g) =
      (cotensorMappingAdjunction Y E).homEquiv Z F g ≫
        (mappingObjectFunctor E).map ((cotensorBifunctor.map f.op).app F)
```

[cotensorMappingPowerAdjunction_naturality_parameter](../../../SerrePositivity/Spectra/General/CotensorMappingParameter.lean#L35)

```lean
lemma cotensorMappingPowerAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Y ⊗ Z) E ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv Z F (pointwiseTensorPost (f ▷ Z) E ≫ g) =
      (cotensorMappingPowerAdjunction Y E).homEquiv Z F g ≫
        (MonoidalClosed.pre f).app (mappingObject E F)
```

[cotensorMappingIso_naturality_parameter](../../../SerrePositivity/Spectra/General/CotensorMappingParameter.lean#L51)

```lean
lemma cotensorMappingIso_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    (mappingObjectFunctor E).map ((cotensorBifunctor.map f.op).app F) ≫
        (cotensorMappingIso X E F).hom =
      (cotensorMappingIso Y E F).hom ≫ (MonoidalClosed.pre f).app (mappingObject E F)
```

[cotensorMappingPowerAdjunction_unit](../../../SerrePositivity/Spectra/General/CotensorMappingPoints.lean#L18)

```lean
lemma cotensorMappingPowerAdjunction_unit (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv (𝟙_ C) F
        (pointwiseTensorPost (ρ_ X).hom E ≫ f) =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f)
```

[cotensorMappingIso_arrow](../../../SerrePositivity/Spectra/General/CotensorMappingPoints.lean#L31)

```lean
lemma cotensorMappingIso_arrow (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : E ⟶ cotensor X F) :
    mappingObjectArrow f ≫ (cotensorMappingIso X E F).hom =
      MonoidalClosed.curry' (cotensorMappingHomEquiv X E F f)
```

[cotensorEnrichedMappingIso_points](../../../SerrePositivity/Spectra/General/CotensorMappingPoints.lean#L68)

```lean
lemma cotensorEnrichedMappingIso_points (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : E ⟶ cotensor X F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((cotensorEnrichedMappingIso X).hom.app (op E)).app F) =
      spectrumTensorCotensor.cotensorHomEquiv X E F f
```

[cotensorMappingAdjunction_naturality_source](../../../SerrePositivity/Spectra/General/CotensorMappingSource.lean#L21)

```lean
lemma cotensorMappingAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor X (pointwiseTensor Z E') ⟶ F) :
    (cotensorMappingAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Z).map f) ≫ g) =
      (cotensorMappingAdjunction X E').homEquiv Z F g ≫
        (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj F)
```

[cotensorMappingPowerAdjunction_naturality_source](../../../SerrePositivity/Spectra/General/CotensorMappingSource.lean#L36)

```lean
lemma cotensorMappingPowerAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (X ⊗ Z) E' ⟶ F) :
    (cotensorMappingPowerAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor (X ⊗ Z)).map f ≫ g) =
      (cotensorMappingPowerAdjunction X E').homEquiv Z F g ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F)
```

[cotensorMappingIso_naturality_source](../../../SerrePositivity/Spectra/General/CotensorMappingSource.lean#L54)

```lean
lemma cotensorMappingIso_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map f.op).app ((cotensorFunctor X).obj F) ≫
        (cotensorMappingIso X E F).hom =
      (cotensorMappingIso X E' F).hom ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F)
```

[cotensorMappingBifunctorIso](../../../SerrePositivity/Spectra/General/CotensorMappingSource.lean#L83)

```lean
def cotensorMappingBifunctorIso (X : C) :
    mappingObjectBifunctor (K := K) ⋙
        (Functor.whiskeringLeft _ _ _).obj (cotensorFunctor X) ≅
      mappingObjectBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj (ihom X)
```

[tensorEnrichedMappingIso](../../../SerrePositivity/Spectra/General/EnrichedMappingObjects.lean#L29)

```lean
def tensorEnrichedMappingIso (X : C) :
    Enriched.tensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X
```

[cotensorEnrichedMappingIso](../../../SerrePositivity/Spectra/General/EnrichedMappingObjects.lean#L38)

```lean
def cotensorEnrichedMappingIso (X : C) :
    Enriched.cotensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X
```

[tensorEnrichedMappingIso_hom_app](../../../SerrePositivity/Spectra/General/EnrichedMappingParameter.lean#L23)

```lean
lemma tensorEnrichedMappingIso_hom_app (X : C) (E F : GeneralSymmetricSpectrum C K) :
    ((tensorEnrichedMappingIso X).hom.app (op E)).app F = (tensorMappingIso X E F).hom
```

[cotensorEnrichedMappingIso_hom_app](../../../SerrePositivity/Spectra/General/EnrichedMappingParameter.lean#L28)

```lean
lemma cotensorEnrichedMappingIso_hom_app (X : C) (E F : GeneralSymmetricSpectrum C K) :
    ((cotensorEnrichedMappingIso X).hom.app (op E)).app F = (cotensorMappingIso X E F).hom
```

[tensorEnrichedMappingIso_parameter](../../../SerrePositivity/Spectra/General/EnrichedMappingParameter.lean#L34)

```lean
lemma tensorEnrichedMappingIso_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerRight C ((pointwiseTensorBifunctor.map f).app E) F ≫
        ((tensorEnrichedMappingIso X).hom.app (op E)).app F =
      ((tensorEnrichedMappingIso Y).hom.app (op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F)
```

[cotensorEnrichedMappingIso_parameter](../../../SerrePositivity/Spectra/General/EnrichedMappingParameter.lean#L45)

```lean
lemma cotensorEnrichedMappingIso_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    eHomWhiskerLeft C E ((cotensorBifunctor.map f.op).app F) ≫
        ((cotensorEnrichedMappingIso X).hom.app (op E)).app F =
      ((cotensorEnrichedMappingIso Y).hom.app (op E)).app F ≫
        (MonoidalClosed.pre f).app (E ⟶[C] F)
```

[pointwiseTensorMappingParametrizedAdjunction](../../../SerrePositivity/Spectra/General/ParametrizedMapping.lean#L31)

```lean
def pointwiseTensorMappingParametrizedAdjunction :
    (pointwiseTensorBifunctor (K := K)).flip ⊣₂ mappingObjectBifunctor
```

[tensorMappingParameterIso](../../../SerrePositivity/Spectra/General/TensorMappingObject.lean#L24)

```lean
def tensorMappingParameterIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorRight X ⋙ mappingTensorFunctor E ≅ mappingTensorFunctor (pointwiseTensor X E)
```

[tensorMappingPowerAdjunction](../../../SerrePositivity/Spectra/General/TensorMappingObject.lean#L33)

```lean
def tensorMappingPowerAdjunction (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensorRight X ⋙ mappingTensorFunctor E ⊣ mappingObjectFunctor E ⋙ ihom X
```

[tensorMappingNatIso](../../../SerrePositivity/Spectra/General/TensorMappingObject.lean#L39)

```lean
def tensorMappingNatIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    mappingObjectFunctor (pointwiseTensor X E) ≅ mappingObjectFunctor E ⋙ ihom X
```

[tensorMappingPowerAdjunction_naturality_parameter](../../../SerrePositivity/Spectra/General/TensorMappingParameter.lean#L19)

```lean
lemma tensorMappingPowerAdjunction_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (Z : C) (E F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Z ⊗ Y) E ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv Z F (pointwiseTensorPost (Z ◁ f) E ≫ g) =
      (tensorMappingPowerAdjunction Y E).homEquiv Z F g ≫
        (MonoidalClosed.pre f).app (mappingObject E F)
```

[tensorMappingIso_naturality_parameter](../../../SerrePositivity/Spectra/General/TensorMappingParameter.lean#L45)

```lean
lemma tensorMappingIso_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map (pointwiseTensorPost f E).op).app F ≫
        (tensorMappingIso X E F).hom =
      (tensorMappingIso Y E F).hom ≫ (MonoidalClosed.pre f).app (mappingObject E F)
```

[tensorMappingPowerAdjunction_unit](../../../SerrePositivity/Spectra/General/TensorMappingPoints.lean#L18)

```lean
lemma tensorMappingPowerAdjunction_unit (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv (𝟙_ C) F
        (pointwiseTensorPost (λ_ X).hom E ≫ f) =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f)
```

[tensorMappingIso_arrow](../../../SerrePositivity/Spectra/General/TensorMappingPoints.lean#L36)

```lean
lemma tensorMappingIso_arrow (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    mappingObjectArrow f ≫ (tensorMappingIso X E F).hom =
      MonoidalClosed.curry' (mappingObjectHomEquiv X E F f)
```

[tensorEnrichedMappingIso_points](../../../SerrePositivity/Spectra/General/TensorMappingPoints.lean#L63)

```lean
lemma tensorEnrichedMappingIso_points (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    (MonoidalClosed.curryHomEquiv' (X := X) (Y := E ⟶[C] F)).symm
        (eHomEquiv C f ≫ ((tensorEnrichedMappingIso X).hom.app (op E)).app F) =
      spectrumTensorCotensor.tensorHomEquiv X E F f
```

[tensorMappingPowerAdjunction_naturality_source](../../../SerrePositivity/Spectra/General/TensorMappingSource.lean#L20)

```lean
lemma tensorMappingPowerAdjunction_naturality_source (X Z : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor (Z ⊗ X) E' ⟶ F) :
    (tensorMappingPowerAdjunction X E).homEquiv Z F
        ((pointwiseTensorFunctor (Z ⊗ X)).map f ≫ g) =
      (tensorMappingPowerAdjunction X E').homEquiv Z F g ≫
        (ihom X).map ((mappingObjectBifunctor.map f.op).app F)
```

[tensorMappingIso_naturality_source](../../../SerrePositivity/Spectra/General/TensorMappingSource.lean#L38)

```lean
lemma tensorMappingIso_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (f : E ⟶ E')
    (F : GeneralSymmetricSpectrum C K) :
    (mappingObjectBifunctor.map ((pointwiseTensorFunctor X).map f).op).app F ≫
        (tensorMappingIso X E F).hom =
      (tensorMappingIso X E' F).hom ≫ (ihom X).map ((mappingObjectBifunctor.map f.op).app F)
```

[tensorMappingBifunctorIso](../../../SerrePositivity/Spectra/General/TensorMappingSource.lean#L67)

```lean
def tensorMappingBifunctorIso (X : C) :
    (pointwiseTensorFunctor (K := K) X).op ⋙ mappingObjectBifunctor ≅
      mappingObjectBifunctor ⋙ (Functor.whiskeringRight _ _ _).obj (ihom X)
```

#### 各段のテンソル（6件）

[pointwiseTensorBifunctor](../../../SerrePositivity/Spectra/General/PointwiseTensor.lean#L46)

```lean
def pointwiseTensorBifunctor : C ⥤ GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K
```

[tensorFreeZeroPointwiseBifunctorIso](../../../SerrePositivity/Spectra/General/PointwiseTensor.lean#L50)

```lean
def tensorFreeZeroPointwiseBifunctorIso :
    (freeAt (K := K) 0) ⋙ curriedTensor (GeneralSymmetricSpectrum C K) ≅
      pointwiseTensorBifunctor
```

[pointwiseTensorAssociator_naturality](../../../SerrePositivity/Spectra/General/PointwiseTensor.lean#L75)

```lean
lemma pointwiseTensorAssociator_naturality (X Y : C)
    {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) :
    (pointwiseTensorFunctor (X ⊗ Y)).map f ≫ (pointwiseTensorAssociator X Y F).hom =
      (pointwiseTensorAssociator X Y E).hom ≫
        (pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Y).map f)
```

[pointwiseTensorAssociatorNatIso](../../../SerrePositivity/Spectra/General/PointwiseTensor.lean#L92)

```lean
def pointwiseTensorAssociatorNatIso (X Y : C) :
    pointwiseTensorFunctor (K := K) (X ⊗ Y) ≅
      pointwiseTensorFunctor Y ⋙ pointwiseTensorFunctor X
```

[pointwiseTensorPost_level](../../../SerrePositivity/Spectra/General/PointwiseTensorCoherence.lean#L24)

```lean
lemma pointwiseTensorPost_level {X Y : C} (f : X ⟶ Y)
    (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorPost f E).hom.app (FiniteBijection.of n) = f ▷ level E n
```

[pointwiseTensorAssociator_parameter_naturality](../../../SerrePositivity/Spectra/General/PointwiseTensorCoherence.lean#L100)

```lean
lemma pointwiseTensorAssociator_parameter_naturality {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensorPost (f ⊗ₘ g) E ≫ (pointwiseTensorAssociator X' Y' E).hom =
      (pointwiseTensorAssociator X Y E).hom ≫ pointwiseTensorPost f (pointwiseTensor Y E) ≫
        (pointwiseTensorFunctor X').map (pointwiseTensorPost g E)
```

#### 基本と構造射（2件）

[pairing](../../../SerrePositivity/Spectra/General/StructureMaps.lean#L28)

```lean
def pairing (F G : SymmetricSequence C) (p q : ℕ) :
    SymmetricSequence.level F p ⊗ SymmetricSequence.level G q ⟶
      SymmetricSequence.level (SymmetricSequence.convolution F G) (p + q)
```

[pairing_equivariance](../../../SerrePositivity/Spectra/General/StructureMaps.lean#L34)

```lean
lemma pairing_equivariance (F G : SymmetricSequence C) (p q : ℕ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    (F.map (FiniteBijection.permutation p σ) ⊗ₘ G.map (FiniteBijection.permutation q τ)) ≫
      pairing F G p q = pairing F G p q ≫ (SymmetricSequence.convolution F G).map
        (FiniteBijection.sumMap (FiniteBijection.permutation p σ)
          (FiniteBijection.permutation q τ))
```

#### 極限と余極限（1件）

[initial_isZero](../../../SerrePositivity/Spectra/General/Zero.lean#L25)

```lean
lemma initial_isZero : IsZero (⊥_ (GeneralSymmetricSpectrum C K))
```

## 段14a　作用から写像対象・豊穣化を組み立てる設計

main `24eff0979` を取り込んだ `c7e3e6762` が調査の基準。現行の Lean、監査、文献対応表は編集せず、段14の設計を型までまとめた。 型案58件は既存の成果物を読み込んで標準入力から精査した。新しい主張は型だけを仮置きし、既存との定義的な一致に依存する3箇所は構成を展開して型を確認した。証明の実装と全体のビルドは後段の作業。[型の一覧](../../../research/cleanup-zero-base/spectra/stage14-types.md) · [宣言ごとの対応](../../../research/cleanup-zero-base/spectra/stage14.csv)

### A が受け取るもの

- モノイダル圏 `V` の通常圏 `M` への左作用を使う。基底の係数二つと対象の自然性、五角形、左右の単位の等式を Mathlib の作用に載せる。B の結合子は `(P ⊗ Q) • X ≅ P • (Q • X)` の順。B の次数別表示は作用を作る側で使う。
- 同じ作用関手 `H` に対して `H.flip ⊣₂ R` と `H ⊣₂ Q` を用意する。写像対象 `R(X,Y)` は B では内部 Hom の第0段、`Q(P,Y)` は各段余テンソル。写像対象への随伴は `MonoidalMappingAdjunction.transportedParametrizedAdjunction` に第0自由対象の随伴と比較を渡す。余テンソル側は既存の `pointwiseTensorCotensorParametrizedAdjunction` を使う。[B の写像対象](../../../SerrePositivity/Spectra/General/MappingObject.lean#L25) · [B の余テンソル随伴](../../../SerrePositivity/Spectra/General/ParametrizedCotensor.lean#L31) · [随伴輸送](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L252)
- 作用の結合子・単位子と `R` の余単位で評価、単位、合成を作る。後から適用する写像を合成の左因子に置き、組紐で Mathlib の因子順へ移す。`MappingUnitLaws` と `RepresentedMappingEnrichment` が既に評価後の単位律・結合律と豊穣圏の構成を持つ。新しい入口ではその仮定を作用の公理から渡す。`enriched_pre/post` と `homFunctorIso_ofParametrized` により、豊穣 Hom の射の作用と `R` を同定する。順射成分は恒等で、通常の射から単位点への同値も同じ選択を使う。[単位の評価](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L180) · [豊穣圏の構成](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L608) · [豊穣 Hom の射](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L804) · [二変数の比較](../../../SerrePositivity/CategoryTheory/Enriched/RepresentedMapping.lean#L910)
- `Enriched.TensorCotensor` に `H`、`Q`、二つの随伴を入れる。写像対象の随伴の右を上の Hom 関手同型で移す。閉性を使うのはここから先の `EnrichedRepresentability`。テンソルでは `S ⊗ P`、余テンソルでは `P ⊗ S` を作用させ、`ActionComparisonAdjunction.rightIso` で左随伴の比較を右に移す。変数ごとの自然性と `S = 𝟙` の単位点の式まで揃えて、元の随伴との互換性を確かめる。`FunctorTransport.transport/iso` は B の提示を作る箇所で再利用する。[表現データ](../../../SerrePositivity/CategoryTheory/Enriched/TensorCotensor.lean#L264) · [右随伴の比較](../../../SerrePositivity/CategoryTheory/Adjunction/Comparison.lean#L39) · [関手の輸送](../../../SerrePositivity/CategoryTheory/FunctorTransport.lean#L19)

### 固定版 Mathlib のソース照合

`lake-manifest.json` の rev と `.lake/packages/mathlib` の HEAD はともに `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。カテゴリ理論以下の Lean ソースを次の語で検索し、該当箇所のクラス・型と構成まで読んだ。

| 検索語 | ソースで確認した構成と使い方 |
|---|---|
| `MonoidalLeftAction`, `MonoidalRightAction`, `curriedAction`, `actionAssocNatIso`, `actionUnitNatIso` | `Mathlib/CategoryTheory/Monoidal/Action/Basic.lean:49,120,325,345,355,434`。左作用の構造と自然性・五角形・左右単位がある。左作用の `curriedAction` と結合・単位の同型を使う。 |
| `ParametrizedAdjunction`, `adjunction of two variables`, `homEquiv_naturality` | `CategoryTheory/Adjunction/Parametrized.lean:19–24,54–76,91–131`。一つのパラメータについての随伴と自然性。冒頭にも二変数の随伴には `F` と `F.flip` の二つが要るとある。二つの既存構造を使う。 |
| `EnrichedCategory`, `EnrichedOrdinaryCategory`, `eHomFunctor`, `enrichedOrdinaryCategorySelf` | `CategoryTheory/Enriched/Basic.lean:59`、`Enriched/Ordinary/Basic.lean:42,164`。通常の Hom と単位点の同値まで定義済み。`Monoidal/Closed/Enrichment.lean` には閉モノイダル圏の自己豊穣化と whiskering の比較がある。 |
| `HasTensors`, `HasCotensors`, `Tensored`, `Cotensored`, `TensorCotensor`, `EnrichedRepresentability`, `tensorHomEquiv`, `cotensorHomEquiv` | `CategoryTheory/Enriched/` と `CategoryTheory/` を検索。B で要る二つの豊穣表現、係数自然性、単位点の一致を束ねた構造は、この探索範囲では見つからなかった。部品は `Monoidal/Closed/Basic.lean:82,242,301,474` の `ihom.adjunction`、`pre`、`internalHomAdjunction₂`、`curryHomEquiv'`。表現を束ねる先は本体の `TensorCotensor` と `EnrichedRepresentability`。 |

### 宣言の照合と B に固有の境界

段10の「写像対象と豊穣化」102件、段12保持31件、段13保持27件、「A へ移す」39件の和集合は149件。段12・13の判断記録、現行ソース、段13のカーネル採取を照合した。写像対象と豊穣化では現行73件のうち51件が一般論の適用で消える候補、20件が一行の適用、2件が B に残る。そのほかは段11で20件、段13で9件が削除済み。C の3件も対象集合に含め、円周での適用として扱った。

| B に残す入力や主張 | この設定で抽象化できない部分 |
|---|---|
| `mappingObjectBifunctor` | 写像対象をスペクトル内部 Hom に `evaluation 0` を後合成して実現する定義。一般論は選んだ `R` を受け取る。 |
| `internalHomCotensorNatIso`、`internalHomCotensorBifunctorIso`、`freeZeroTensorCotensorAdjunction` | 自由第0段、スペクトル内部 Hom、各段余テンソルの具体的な比較。一般論に渡す `Q` とその随伴を作る部分。 |
| `pointwiseTensor_isQuillen` | 左 Quillen な自由第0段とスペクトルの相対テンソルから各段作用の Quillen 性を得る。作用からの豊穣化とは別の仮定を使う。 |
| `simplicialLoopNatIso` | 円周について選んだ二つの懸垂表示とその右随伴の比較。同型の構成には一般の右随伴の一意性を使う。 |

### 見積もりと実装順の案

現行の行数は段13の `.ilean` の宣言名から宣言末尾までを数えた。見出し、ファイルの共通部分、生成物を含まない。「B の行の減少余地」は消える候補の行数に、保持する適用を1行にできた場合の差分を加えた上限。A の行数は既存補題を呼ぶ際の引数と自然性の証明を含む概算。

| まとまり | A の追加案 | B の削除候補・一行化候補 | B の行の減少余地 |
|---|---:|---:|---:|
| 作用と随伴。対称列加群の入力を整え、二つの随伴を揃える | 6型、約95–170行 | 14件・17件 | 163行 |
| 豊穣化。既存の評価と作用の整合を接続する | 13型、約130–220行 | 12件・8件 | 170行 |
| 表現比較。テンソルと余テンソルを一緒に入れる | 26型と局所補題最大10型、約240–420行 | 34件・4件 | 439行 |
| 対称列の畳み込み生成射、零対象 | 3型、約15–35行 | 2件・1件 | 26行 |

A は48型と局所補題最大10型、計約480–845行。B の理論上の上限は62件・798行の減少。段12・13では削除候補を実際に使う型と照合すると保持に回る例があった。今回も、既存の転置との一致や利用側の読みやすさのため半分程度を残す場合を見込み、約30–45宣言・400–600行減を作業時の目安とする。A と B を合算した総行数の純減は見積もりからは確定しない。

段13で採取した本体9,059モジュールの型・本体の直接参照を、削除候補名とその `_assoc` について集計した。今回の取り込み前後で Lean ソースに差はない。範囲内の書き換え候補は `Spectra/ModelCategory` 0箇所、`Spectra/Stable` 0箇所、C 1箇所。`pointedMappingSpaceParametrizedAdjunction` で `GeneralSymmetricSpectrum.mappingTensorNatIso` を使っており、新しい比較の成分に切り替える。3領域のソースも短名と `_assoc` で検索し、この1箇所だけが一致した。削除候補の完全修飾名を現行の文献対応表と blueprint で検索した結果は0件。3領域には関連する B のファイルへの明示 import が5行あり、いずれも保持する入口のファイルを指す。入口の配置を維持する案では import の書き換えは0行。これは現在の直接参照による見積もりで、型クラス推論や透明性による証明の調整を含まない。[C の利用箇所](../../../SerrePositivity/Spectra/SymmetricSpectrum/Basic.lean#L106)

実装は、作用と二つの随伴、豊穣化と Hom 関手、テンソル・余テンソルの表現比較の順に分ける。作用の段で既存の各段テンソルの関手と射が一致することを確かめる。豊穣化では通常 Hom と単位点の同値および Hom 関手比較の成分、表現比較では原変数・係数・単位点の型を検査する。畳み込み生成射と零対象の3件はこの依存順から切り離せる。

### 本体の同形箇所

概念の木の「Z 圏論一般／豊穣圏」と「テンソル・余テンソル」の参照先から、dg、単体的豊穣、モデル圏の豊穣化を追った。現行ソースで `EnrichedCategory`、`EnrichedOrdinaryCategory`、`TensorCotensor`、`cotensorHomEquiv`、`EnrichedRepresentability` の宣言・利用箇所を検索し、以下の型と構成を確認した。[概念の定義](../../../research/cleanup-zero-base/whole/concept-definitions-draft6.md#L1906)

| 箇所 | 共通部分と個別の入力 |
|---|---|
| dg 複体の `complexEnrichment`、`complexEnrichedOrdinary` | Hom 複体、合成、単位点を独立に書いている。`complexEnrichment_eq_closed` が既に閉構造からの Mathlib 自己豊穣化と比較する。一般の作用の入口を試す例にはなる。既存の複体成分の計算と通常射の同値が揃うことの確認が要る。[dg の豊穣化](../../../SerrePositivity/DifferentialGraded/Category/Basic.lean#L555) · [自己豊穣化との一致](../../../SerrePositivity/DifferentialGraded/Complexes/HomLimits.lean#L121) |
| dg 加群の `tensorHomEquiv` と `enrichedTensorHomEquiv` | dg 圏を添字とする相対テンソルを coend として作り、平衡化の条件から転置を作る。係数のテンソルと内部 Hom との随伴は共通部品。相対テンソル自身の普遍性はこの設計の入力としても別に要る。[dg 加群の通常の同値](../../../SerrePositivity/DifferentialGraded/Tensor/Enriched.lean#L314) · [豊穣同値](../../../SerrePositivity/DifferentialGraded/Tensor/Enriched.lean#L759) |
| dg から作る単体的圏の `standardEnrichedCategory` | 単位と合成は Dold–Kan の Hom と Alexander–Whitney 合成で与え、次数ごとに法則を証明する。選んだ通常射を表す二つの作用随伴をこの定義は使っていない。今回の入口への直接の置換は確認できなかった。[単体的豊穣](../../../SerrePositivity/InfinityCategories/Kerodon/ExamplesOfInfinityCategories/DifferentialGradedCategories/Enrichment.lean#L30) |
| Barratt–Eccles の `cotensorHomEquiv` と `algebraHammockEnrichedCategory` | 余テンソルの通常 Hom 同値は右 frame の反対圏での実現随伴。別に hammock colimit の写像空間から豊穣化を作る。右 frame の Hom と hammock Hom を同じ二変数随伴に載せる入力はこれらの定義には現れない。[余テンソルの同値](../../../SerrePositivity/EInfinity/BarrattEccles/Cotensor.lean#L42) · [hammock 豊穣化](../../../SerrePositivity/EInfinity/BarrattEccles/HammockEnrichedCategory.lean#L39) |
| 単体的モデル圏の `simplexTensorHomEquiv` と `tensorHomBifunctorIso` | 既存 `TensorCotensor` の通常 Hom 同値を標準単体で使い、余単体分解の Hom と写像空間を比較する。今回提案した一般論の出力を既に受け取れる形で、標準単体の比較が固有の部分。[単体での評価](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorHom.lean#L27) · [二変数の比較](../../../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SimplicialTensorHom.lean#L67) |
| 固定 Quillen 類の `fixedEnrichedHom_trivialKanFibration` | 既存 `TensorCotensor.tensorHom` の随伴で持ち上げを移す。一般の表現比較を証明し直す箇所はなく、境界・ホーンで Quillen 類を指定する部分が固有。[固定モデル構造との比較](../../../SerrePositivity/InfinityCategories/Project/ModelCategoryComparison/Replacements/FixedSimplicialModelCompatibility.lean#L63) |
| モデル圏の `tensor_iff_cotensor_model`、`tensor_iff_mapping_model`、`derivedHom` | 最初の二つが一般の pushout-product／pullback-Hom 同値を既に与える。B のモデル圏補題は適用で足りる。導来 Hom ではさらに余ファイブレーション・ファイブレーション置換が要る。[一般のモデル圏条件](../../../SerrePositivity/HomotopicalAlgebra/Enriched/TensorCotensor.lean#L30) · [導来 Hom](../../../SerrePositivity/HomotopicalAlgebra/Enriched/DerivedMapping.lean#L32) |
