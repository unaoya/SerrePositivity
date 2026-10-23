# R-C：∞ 圏基盤のリファクタリング

## 引き継ぎ

- 現在地：R17 a45c92306、R19 2c1fa3384、R20 aa124065c、3-1 完全一致部 0252eb8a6 完了。R16 87c6a2711 も90モジュールの移動・全本文保存・旧 import 0と、4集約ビルド・指定4監査の成功を確認済み。
- 残り：取り込み方式を変更。R-A の F1 再編後の main に順次再適用する。R19/R16 の2,300移動 JSON と cherry-pick 3件を準備済み。「main 空き」の合図待ち。R15・267転送入口削除も同じ専有期間に実施可。
- 主要宣言：`SerrePositivity.InfinityCategories.F2.hasSpaceLimitsOfShape`。既存の宣言型・証明は保存。
- 依存と提供：F1 の `hasLimit_coherentSpaceDiagram` を使用。R-A の `scripts/move_module.py` 到着までは機械的変更の対応表を archive に残す。
- 未コミット：再適用計画・ペイロード・dry-run証拠・手順。既存の実装コミットは保存。
- 既知の問題：なし。main の未追跡作業ファイルは取り込まない。
- 次の一手：「main 空き」の合図後、新 main で再 dry-run → JSON --apply → R17/R20/共有化の cherry-pick → R15/267入口削除 → scripts/refactor/verify.sh。rebase と .lake 再クローンは廃止。

## 方針

指定の所有範囲で直接移動・参照置換する。互換シムなし。数学的内容・既存の宣言型・証明は保存し、sorry・公理を追加しない。各項目末に F2・HomotopyLimits の集約ビルドと audit_infinity_f2・audit_infinity_presentable・audit_homotopy_limits・audit_einfinity を実行する。取り込み方式の新指示に従い、rebase は行わず「main 空き」の合図後 main に再適用する。

## 検証

R17：`lake build SerrePositivity.InfinityCategories.F2 SerrePositivity.InfinityCategories.HomotopyLimits` および `lake env lean scripts/{audit_infinity_f2,audit_infinity_presentable,audit_homotopy_limits,audit_einfinity}.lean` を各実行し終了コード0。F2 19,485 宣言、Presentable 852 宣言、EInfinity 25,780 宣言が標準三公理のみ。ログは `/tmp/r-c-r17-*`。

R17 は既存の条件付き宣言の引数・証明を保存し、条件を任意の形について供給する `hasSpaceLimitsOfShape` を無条件の極限存在定理の系として追加した。F1 の既存2ファイルを変更せず利用できる。

準重複に関する追加指示（2026-10-23）：型の異なる組は変更しない。完全一致する宣言のみを共有化し、差分のある組は `archive/refactor-near-duplicates-einfinity-2026-10-23.md` に両ファイル・類似度・型の差・一般化案を記録する。実施は所有レーンの再開後の判断。

R19：Cat*・Lax* とその F2 最上位への依存閉包 290 本を CatInfinity、残る 1,921 本を FilteredExchange へ。既存の4サブディレクトリ集約は位置を保つ。`archive/refactor-r-c-r19-moves.json` に移動・import 変更を保存。複数行 import を含め全移動元のコミット済み本文と照合し、差は import のモジュール名だけ。旧モジュールへの import は0。F2 の既存説明・#check は保存し、新しい2入口を追加。EInfinity にも import 変更があるためビルド対象に含める。

R20：5入力の定義・供給元・一致行／ファイルを現 worktree から再採取し §6 と archive を更新。準重複一覧は同名 EInfinity 33 組と HomotopicalAlgebra 6 組。R8 の元8組の一覧は未保存。ユーザー回答とコーディネータ再計算で現存6組が全てと確定し、全調査の記録として整理した。再調査 `/tmp/r-c-ha-match.py` も6組だけを再同定した。

3-1 の追加検証：`OrdinaryBarFirstAction.output` と `ResolutionBarFirstAction.output` は同じ型・同じ本文。両既存宣言との等式を `rfl` で確認（`/tmp/r-c-ha-output-probe.lean`、終了コード0）、最小 import の probe も通過（`/tmp/r-c-ha-output-minimal-probe.lean`）。局所 Reedy instance・変数を保存して `BarOutput.output` 一箇所に移す準備済み。共有化後は指定四監査に加え `audit_homotopical_rectification` と既存の ordinary/resolution bar 評価チェックも実行する。

3-1 準備：`EInfinity/HomotopyWeight/DoubleOpposite.lean` と `HomotopicalAlgebra/Rectification/HomotopyFunctionComplex/BarOutput.lean` を、通過済みの独立 probe から新規追加。既存モジュールはまだ import しておらず、R19 の依存グラフは変わらない。R19 の四監査後、既存宣言の削除・参照置換を適用する。

R19 検証進捗：主ビルドは15,713 jobsで終了コード0、F2監査も終了コード0（19,486宣言、標準三公理）。Presentable監査は旧 `F2.CoconeParameterPrism` の cached olean と新配置の混在で停止したため、`F2.Presentable` を追加ビルド中。ソースの旧 import は存在せず、互換シムで回避しない。以後の項目ゲート `/tmp/r-c-check-item.sh` は監査が使う4集約すべてを明示ビルドするよう修正済み。

R19/R20 最終検証：主集約（F2・HomotopyLimits・EInfinity）15,713 jobs、追加 Presentable 集約7,750 jobsが成功。`audit_infinity_f2`（19,486宣言）・`audit_infinity_presentable`（852宣言）・`audit_homotopy_limits`・`audit_einfinity`（25,780宣言）は全て終了コード0。公理は標準三公理のみ。最終ログは `/tmp/r-c-r19-audit_{infinity_f2,infinity_presentable,homotopy_limits,einfinity}.log`。最初の Presentable cached olean 失敗は `/tmp/r-c-r19-presentable-stale-cache.log` に分離して保存。

R20 完了：§6 の5入力の定義位置・供給元・使用数を更新し、全一致行を archive に保存。R17・R19 の完了行も正本に反映。R19 と同じ検証済みソース状態で指定4監査が通過し、文書変更はその後のみ。

3-1 実装：EInfinity の `doubleOpWeights`・`framedLimitWeight`・`framedLimitWeight_cofibrant` と HomotopicalAlgebra の `output` を各共有モジュールへ接続し、元の宣言を削除。旧名の参照は0。`archive/refactor-r-c-shared-source-verification.json` に HEAD aa124065c との機械的変更の照合・55ファイルのハッシュを保存。共有宣言の型・本文は保存。

3-1 完全一致部の最終検証：全変更モジュール・4集約・Rectification.Foundations のビルド成功（16,795 jobs）。指定4監査・Rectification監査・bar評価2チェックの7コマンドは全て終了コード0。EInfinity 25,777宣言（重複3宣言分減）、Rectification 14,894宣言・1,040モジュール、標準公理のみ。実行結果・対象一覧・新規モジュールハッシュを `archive/refactor-r-c-shared-validation.json` に保存。

R16：90モジュールの名前空間・宣言型・証明は保存。全移動元の HEAD 0252eb8a6 の本文を git cat-file で読み、import モジュール名の置換以外の差が0であることを照合。旧 import は0。`archive/refactor-r-c-r16-moves.json` に対応を保存。Presentable集約が所有し、従来のHomotopyLimits集約からは当該importを除いた。既存のHL監査の全型チェックを維持するため監査にPresentable importを追加した。

追加項目（2026-10-23 ユーザー指示）：HomotopicalAlgebra/HomotopyFunctionComplex/ のうち Rectification へ単一 import する転送専用267本を、R-A の scripts/move_module.py 到着後に直接参照へ置換して削除する。実体のある同ディレクトリのモジュールは対象外。削除前後で転送専用ノードを除いた各利用元の推移的 import 閉包が一致することを検証し、HomotopicalAlgebra 集約・該当監査と既定の4集約・4監査を通す。到着前は候補一覧と仮想置換後の閉包照合のみ準備する。

所有境界（2026-10-23 追加指示）：HomotopyLimits/UniverseSSetMaps.lean は R-B が Core へ移動するため、R-C は現在位置に残し、R16・その他の移動対象から除外する。

267転送入口の事前調査：単一 Rectification import のみの267本は既存 manifest の同ディレクトリの267移動と完全一致。現 branch の SerrePositivity/ 内からの import は0、scripts/ 内の import は60行・58ファイル（連絡の261本とは現状値が異なる）。58利用元全てで仮想置換後の正規化推移閉包が一致。scripts/ には別途614箇所の旧モジュール名参照（主に監査の required 配列）があるため、削除時は import と区別してモジュール存在チェックも更新する。audit_homotopical_layout.py は旧入口の存在を明示要求するため、削除対象267本だけ直接配置の検査に切り替え、残る146入口の検査を保つ。準備記録は archive/refactor-r-c-forwarders-preflight.json。ソース変更・削除はまだ行っていない。

R15 事前依存調査：PresheafDensity の Ind 内依存閉包は59本。定理本体だけでなくこの前層密度の構成層を移動候補とする。境界には F2/FilteredExchange の一般余錐補助12本と Stable の補助4本があるため、R-A/R-B 取り込み後の配置を再評価する。archive/refactor-r-c-density-preflight.json は現配置の解析のみで、移動は未実施。

R16 最終検証：4集約のビルド16,055 jobsと指定4監査は全て終了コード0。F2 19,486宣言、Presentable 1,479宣言、EInfinity 25,777宣言。標準三公理のみで新規 sorry・公理なし。移動元90本文は import 置換以外の差分0。UniverseSSetMaps は移動・編集していない。ログは /tmp/r-c-r16-*。

取り込み方式変更：formalization-plans/archive/r-c-reapply-2026-10-23/README.md に新手順を固定。本文中の古い rebase 待ち・ツール未到着の記述は当時の実施記録であり、現在の着手条件は冒頭に記した「main 空き」の合図。
