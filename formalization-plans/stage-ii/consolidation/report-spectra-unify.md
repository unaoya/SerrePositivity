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
