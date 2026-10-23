# R-C：∞ 圏基盤のリファクタリング

## 引き継ぎ

- 現在地：指定資料を確認。`refactor/r-c` を main `c6692be81`（基準タグの後の運用記録を含む）から作成。R17 完了：無条件供給補題を追加し、F2・HomotopyLimits 集約ビルドと指定4監査が通過。
- 残り：R19、EInfinity 19 組・HomotopicalAlgebra 8 組、R16、R20。R15 は R-A 取り込み・合図後の rebase を待つ。
- 主要宣言：`SerrePositivity.InfinityCategories.F2.hasSpaceLimitsOfShape`。既存の宣言型・証明は保存。
- 依存と提供：F1 の `hasLimit_coherentSpaceDiagram` を使用。R-A の `scripts/move_module.py` 到着までは機械的変更の対応表を archive に残す。
- 未コミット：なし（R17 のコミットに本引き継ぎを含む）。
- 既知の問題：なし。main の未追跡作業ファイルは取り込まない。
- 次の一手：R19 のモジュール移動（対応表 `/tmp/r-c-r19-map.json`、適用 `/tmp/r-c-r19.py`）。

## 方針

指定の所有範囲で直接移動・参照置換する。互換シムなし。数学的内容・既存の宣言型・証明は保存し、sorry・公理を追加しない。各項目末に F2・HomotopyLimits の集約ビルドと audit_infinity_f2・audit_infinity_presentable・audit_homotopy_limits・audit_einfinity を実行する。R-A 取り込み後はコーディネータの合図で rebase と .lake の再クローンを行う。

## 検証

R17：`lake build SerrePositivity.InfinityCategories.F2 SerrePositivity.InfinityCategories.HomotopyLimits` および `lake env lean scripts/{audit_infinity_f2,audit_infinity_presentable,audit_homotopy_limits,audit_einfinity}.lean` を各実行し終了コード0。F2 19,485 宣言、Presentable 852 宣言、EInfinity 25,780 宣言が標準三公理のみ。ログは `/tmp/r-c-r17-*`。

R17 は既存の条件付き宣言の引数・証明を保存し、条件を任意の形について供給する `hasSpaceLimitsOfShape` を無条件の極限存在定理の系として追加した。F1 の既存2ファイルを変更せず利用できる。

準重複に関する追加指示（2026-10-23）：型の異なる組は変更しない。完全一致する宣言のみを共有化し、差分のある組は `archive/refactor-near-duplicates-einfinity-2026-10-23.md` に両ファイル・類似度・型の差・一般化案を記録する。実施は所有レーンの再開後の判断。
