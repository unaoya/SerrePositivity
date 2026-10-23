# R-C 再適用の準備（2026-10-23）

状態：準備完了、main 未適用。「main 空き」のコーディネータ合図を待つ。既存 `refactor/r-c` の実装コミットはそのまま残し、rebase は行わない。

## 計画と件数

`r19-r16.json` は scripts/move_module.py の moves / redirects / symbols / imports / file_symbols 形式。
- R19：2,210本（CatInfinity 290、FilteredExchange 1,920）。旧2,211本のうち `F2/JoinRightRelativeRetraction` は R-A により F1 原本へ統合済みなので移動しない。
- R16：Local*・Sigma*・Sifted* の90本を F2/Presentable へ。
- 計2,300本移動。tool.prepare による更新 Lean ファイルは2,669本（移動先を含む、移動以外369本）。
- `files/` に新規 Lean 集約入口2本と README 2本。全体では2,673ファイルを変更・追加する。
- `HomotopyLimits/UniverseSSetMaps` は R-B 所有で移動対象外。

main の適用済み・未コミット R12（F1 1,714本の再編）を含む作業ツリーを /tmp に複製して検査した。F1 の旧パスへ戻す操作は含まない。移動元2,300本は全て現 main の git index に存在し、移動先は未使用。snapshot 中のソース変更は0。

集約以外2,665ファイルは import モジュール名の置換以外の差が0であることを main 複製の本文と照合した。元 F2 集約の1,099直接 import と、用意した2入口の直接 import の和は完全一致。複数行 import 53箇所を file_symbols のファイル限定規則で処理し、旧 import 0を確認した。F2 集約内の既存の複数行直接 import 36本は、新パスへ置換して残す（tool の行単位 remove では削除されないため）。2入口と同じ閉包に含まれる。

## Cherry-pick 対象（順序）

```
a45c923061b52c53b5a2ec76b0c136778e1182ba  R17
aa124065c222af778162478a12a8accbb5a5e227  R20
0252eb8a6ce6425766971891e187e79cf4c9fbe7  R8 identical declaration sharing
```

R19・R16 の旧コミット自体は cherry-pick しない。R17 の SpaceLimitShapes は新 FilteredExchange 位置へ解決する。R20 の文書と共有化コミットの import コンテキストに衝突があれば main の F1 サブディレクトリ化を維持し、対応表の型・証明の変更を持ち込まない。R20 の使用数・所在は適用後に再採取する。

## 「main 空き」後の適用

1. main の HEAD・index・既存の未コミット差分を記録し、R-A の R12 がコミット済みであることを確認する。今回の source-hashes.json は現準備時点の2,669入力のハッシュなので、差があれば新 main で dry-run を再実行する。main に元からある数学的な未コミット変更を一括ステージしない。
2. `files/` の4本を対応する main パスに新規追加する（既存パスがあれば停止して再評価）。既存ファイルを上書きするペイロードはない。
3. main の `python3 scripts/move_module.py <このディレクトリの絶対パス>/r19-r16.json` で新しい dry-run を確認し、同じコマンドに `--apply` を付ける。
4. 上記3件を順に `git cherry-pick --no-commit` で適用する。先行する自分の import 差分と新規4本だけを index に反映してから行う。他作業の差分を巻き込まない。宣言名・名前空間は shared の明示した共有先以外は保存する。
5. 同じ専有期間に R15（前層密度層）と267互換入口削除を続けてよい。これらは別計画にし、移動・削除前後の本文・依存閉包を照合する。既存の事前調査 archive を使い、今の JSON に未実施分を混ぜない。
6. `scripts/refactor/verify.sh` を実行し、各ビルド・監査の実結果を確認する。スクリプトの最終終了コードだけでは監査全件の成功を意味しないため、ログの全 rc と sorry 閉包結果を確認する。267本削除には HomotopicalAlgebra の各集約・該当監査も追加する。
7. 対象を限定してコミットし、件数・全検証結果・コミットを報告する。

## 証拠

- preflight.json：main HEAD、tool ハッシュ、件数、バンドルハッシュ。
- dry-run.json：移動・更新ファイルの全一覧。適用フラグ false。
- source-hashes.json：この計画が変更・移動する入力全2,669本の準備時ハッシュ。
- cherry-picks.txt：完全なコミットハッシュ。

この準備では main のソース・index・履歴・.lake を変更していない。ビルド・監査は適用後に実行する。
