# CF-W1 A の報告

現在地は CF-W1 A の適用完了。

## 段0の基準

IC-2 第2組を `c25e7ef92` で完了し、main `1cb048402` を
`5572d4029` で取り込んだ時点を段0の基準にした。
第2組は77本を移動し、対象ビルドと v3b の813本、引用・タグ43件、
追従した監査3本が通った。v3b の未説明差分は0件。IC-2 は第2組で停止した。

## 別名

本文の有効な `deprecated_alias` は13,641件、`deprecated_alias_util` は2,043件、
`alias` は45件。計15,729宣言、旧名は15,728種類。テスト用の13件は別計とした。
本文の `alias` 45件は以下の4ファイルにあり、共通層・新しい名前空間への
移動後に旧 API を提供している。

| モジュールの末尾 | 件数 |
| --- | ---: |
| `BhattScholze.Perfectoidization.WittPushout` | 5 |
| `BhattScholze.Semiperfectoid.Surjectivity.CompatibleRoot` | 26 |
| `Spectra.ModelCategory.SimplicialGenerators` | 8 |
| `Spectra.ModelCategory.SimplicialMonoidal` | 6 |

`aliases.tsv` に旧名、直接の行き先、宣言のファイル・行、範囲別の出現箇所数・
ファイル数を収めた。`destination-owners.tsv` は別名の RHS と保存済み
`.ilean` の名前・位置が一致する15,518件について、行き先の所有モジュールも示す。
残る224件（テスト用を含む）はソースの RHS を記録し、所有元の照合が
できなかった理由を同表に付けた。

`…IsFullyFaithful.preimageFunctorIso_postcomp` は
`Project.Compatibility.Legacy30` と `Legacy51` に同じ旧名があり、
行き先はそれぞれ `FullyFaithfulFunctorIsoCoherence` と
`FullyFaithfulIsoRecovery`。両方の定義と RHS の所有元を保存済み
`.ilean` で照合した。適用時は所有モジュールを使って行き先を選ぶ。
名前だけの対応表ではこの2件を同じ行き先にできない。

| 走査範囲 | 完全一致の出現箇所 | 完全一致した旧名の種類 |
| --- | ---: | ---: |
| 本文（import と定義左辺を除く） | 272 | 54 |
| scripts（targets 以外） | 675 | 385 |
| blueprint | 0 | 0 |
| research（legacy 台帳以外） | 19,430 | 997 |
| `scripts/refactor/targets/` | 70,550 | 13,728 |
| `legacy-kernel-evidence.json` | 506 | 110 |
| BS drafts | 0 | 0 |

上の表は字面の件数。Lean はコメントを除いて数え、対応表の文章・型表示・
履歴の再掲も出現として数えた。完全名の後にさらに成分が続く箇所は別列に
置いた。JSON キー・値や CSV/TSV のセル全体で旧名を名指しする場所は
`metadata-fields.tsv` にセレクタ付きで示した。legacy 台帳では
`declarations` の旧名キーが31件。旧名で固定されている宣言は、この種の
フィールドを確認して新名に引き継ぐ。過去の比較表や `old` フィールドは
記録として照合する。

別に、本文34,234本と blueprint 94本の保存済み `.ilean` を読み、旧名と
現在のソース範囲が整合する使用箇所を本文で386件（旧名66種類）得た。
このうち163件は所有元も現在の宣言元と一致し、223件は保存成果物の所有元が
現行の宣言元と異なる。後者を現行の所有元による使用数に含めていない。
位置・字面が合わない2,862件を別表に置いた。本文103本と blueprint 81本には
保存成果物がなかった。script と drafts の集計はソースによる。
import 到達性と短い字面で拾った要確認候補は scripts 31件、blueprint 7件、
drafts 0件だった。これらは他の列と重なり得る。いずれの0件も、短名や
フィールド記法を含む利用の不存在を示す値ではない。

## Lake の設定試験

基準コミットの追跡 Lean ファイルを対象に、コメントと Archive を除いて
`set_option` コマンドを数えた。本文の母集団から
`SerrePositivity/LengthAlgebra/` と `SerrePositivity/Spectra/General/`
を除いた。下表は指定の option を値にかかわらず一度も書いていないファイル数。
局所指定の `set_option … in` も、行がある方に含めた。

| option の省略名と試す値 | 本文 34,274本 | blueprint 175本 | scripts 423本 |
| --- | ---: | ---: | ---: |
| `respectTransparency = false` | 7,226 | 175 | 354 |
| `respectTransparency.types = false` | 14,522 | 175 | 370 |
| `defeqAttrib.useBackward = true` | 33,632 | 175 | 421 |

本体の `lakefile.toml` を複製した一時 TOML を `lake -f` で読み込み、
実際の `ModuleSetup` と `run_cmd` の値を照合した。基準値は順に
`true, true, false`。個別指定は3件とも効いた。二つの transparency の
ドット区切りキーは、TOML では親の値と子のキーを同時に定義できない。
ドット全体を一つの引用符で囲むと Lake が一成分の Lean 名として扱う。
併用案の試験だけは `types` を `moreLeanArgs` で渡した。プローブでは
`false, false, true` を確認した。`types` の効果は親側が有効なときに
出るため、個別の試験も行った。

実ファイルは、Lake が渡した option を `--setup` で再現して基準と照合した。
同じソースと既存の依存 `.olean` を使用し、生成物は一時領域に置いた。
本文は領域と option の欠落状況で層別し、ハッシュ順の候補と長いファイルを
含めた。blueprint は別パッケージの設定、scripts は通常の
`lake env lean` の既定で基準を採った。両者には候補の option を明示的に
渡す比較も行った。本体パッケージの `leanOptions` が blueprint の
パッケージ設定や `lake env lean` に自動で渡ることはない。

本文75本、blueprint 23本、scripts の監査10本を選び、bulk 鍵一本と
Lean プロセス一本で、最長24分の塊に分けて照合した。集約入口だけの
大きなファイルは、既に実行した小さな比較を除き、標本から外した。
個別指定は本文の該当行を持たない標本と、blueprint・監査の代表に対して
試した。併用は基準の通った全標本で試した。初回は459回、
Lean の実行時間は合計約95分。初回の一ファイルの上限は100秒。

| 比較 | 本文 | blueprint | scripts |
| --- | ---: | ---: | ---: |
| 基準 | 74/75 | 16/23 | 9/10 |
| `respectTransparency=false` | 55/57 | 11/11 | 8/8 |
| `types=false` | 68/68 | 10/11 | 8/8 |
| `useBackward=true` | 70/70 | 11/11 | 8/8 |
| 併用 | 72/74 | 16/16 | 9/9 |

各セルは成功数／実行数。基準が通らなかった9本の変更側は集計対象外。
本文は `OrdinaryBarUnitTriangles` で旧定数
`SerrePositivity.SimplicialModel.LargeParameterSquare.changeEndpoints`
が見つからなかった。対応する `Legacy08` は同ファイルからの静的 import
閉包に入っておらず、この閉包と第2組の変更ファイルの重なりは0本。
残りは blueprint 7本と `audit_localizing_invariants` の基準側の時間切れ。
変更側が通った試験の警告には基準との差がなかった。

本文では `CubeConnectionPathEvaluation` の32行・50行で、
`respectTransparency=false` 単独と併用により `rw` でゴールが閉じ、
後続の `rfl` がエラーになった。`ParameterPowerLength` では基準が約12秒、
同じ二案が100秒で時間切れ。blueprint の `HTT/Section7_3` では基準が
約71秒、`types=false` 単独が初回で時間切れになった。

再試験では一ファイルの上限を240秒にした。
`CubeConnectionPathEvaluation` は同じ2行のエラーを再現した。
`HTT/Section7_3` は基準約49秒、`types=false` 単独約89秒で両方が通った。
`ParameterPowerLength` は基準約13秒。単独・併用とも約170秒で終了し、
両方で `isDefEq` が heartbeat 上限に達するエラーが9件出た。
一時コピーでは `CubeConnectionPathEvaluation` の2補題に
`set_option backward.isDefEq.respectTransparency true in`、
`ParameterPowerLength` のファイル先頭（import の後）に同じ option の
`true` を加えると、単独・併用の両方が通った。証明の文字列は同じ。

## 段0の判定

- `respectTransparency=false` の一律集約は保留。本文の異なる2本で
  エラーを再現した。局所の `true` で両方を救えることは確認したが、
  全体で必要になる例外の件数は標本からは確定できない。
- `respectTransparency.types=false` は単独の候補。本文68本で通った。
  blueprint の時間切れは再試験で通ったが、同じ塊の基準より約41秒遅い。
  本文で `types` の行も親を `false` にする行もないのは7,237本。
- `defeqAttrib.useBackward=true` は単独の候補。本文70本で通った。
  本文の未指定33,632本に対する標本の結果であり、既存依存成果物を
  固定した型検査として扱う。

検査の一時設定と一時コピーは作業木の外に置いた。A の段0はこの報告で停止。
DI-W1 §4 の9〜11を確認した。

[証拠目録](../../../evidence/ic-w1/cf-w1-a-stage0/manifest.json) の基準は
`5572d40298f053a88445e5a99acbd7764507ba7b`。旧名別の表と位置表、試験の
全結果・ログ・再試験は `~/serre-evidence/ic-w1/cf-w1-a-stage0/` に保存した。

## A の適用（11-20）

現在地は CF-W1 A の適用完了。比較の基準は `84e08e53e`。
判定は指示書の「11-20 追記 3」（`1a9626867`）による。
今回の適用は互換別名の整理。段0で試した Lake の設定集約は見送った。

### 適用差分

`deprecated_alias` 13,641 件、`deprecated_alias_util` 2,043 件、
`alias` 45 件の計 15,729 宣言について、カーネル本体が行き先の定数と
同じ宇宙引数を指すことを照合して削除した。段0で行き先を照合できなかった
本文の分も、この照合で確認した。別名だけになったモジュールは 80 本。
本文の照合不能による保留は 0 件。コマンドの回帰試験用の別名 13 件は
[一覧](../../../evidence/ic-w1/cf-w1-a-apply/retained-test-aliases.tsv)に記録した。

対応表 4 ファイルを更新した。対応表のセル 57 件と
`legacy-kernel-evidence.json` の宣言キー 31 件を追従した。
監査・検査の Lean スクリプトは 48 本を更新した。うち 10 本で
短名・import・監査対象モジュールの追従を追加した。

| 本文の集計 | 前 | 後 |
| --- | ---: | ---: |
| Lean ファイル | 34,337 | 34,257 |
| カーネル宣言（所有モジュールごと） | 376,040 | 360,311 |
| コード行（コメントと空行を除く） | 2,202,852 | 2,166,749 |
| 文字 | 194,320,952 | 189,656,867 |
| 100 文字を超える行 | 518,091 | 496,256 |

### 比較と検査

- 34,337 モジュールについて公開・server・private の保存成果物を比較した。
  削除した 80 モジュールに別名以外の宣言がないことを確認した。残るモジュールの
  型は同じ定数対応表を通して α 同値で一致した。削除した別名を型に含む宣言は
  107 件。旧名が複数の所有モジュールに実在する 4 種類は、
  保存成果物の import と所有元を使って判定した。
- 無名 instance はモジュールとソース位置で 1,295 組を対応させた。改名の
  2 件は現行の本文・監査・対応表に旧名での名指しがなかった。
  改名された instance を型に含む名前付き宣言は 4 件。公開範囲の重複を統合し、
  [改名一覧](../../../evidence/ic-w1/cf-w1-a-apply/renamed-unnamed.tsv)と
  [4 件の一覧](../../../evidence/ic-w1/cf-w1-a-apply/unnamed-in-named-types.tsv)に記録した。
- 変更後の全対象 39,033 ジョブと、通常の root が通った。
  公理・sorry は増加 0 件。変更した監査・検査 48 本が通った。
- blueprint 生成器の linked は前後とも 2,363 件。欠落は 0 件。

[証拠目録](../../../evidence/ic-w1/cf-w1-a-apply/manifest.json)に対応表と検査ログを記録した。
CF-W1 A はこの適用で停止。
