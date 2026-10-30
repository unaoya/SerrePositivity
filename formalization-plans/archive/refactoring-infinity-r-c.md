# R-C：main 再適用（2026-10-24）

- 基準：main 312b86690、タグ refactor-stage1-2026-10-24。「main 空き」の合図後、R-C が単独で適用。
- 元の refactor/r-c は保持。rebase は行わず、scripts/move_module.py の dry-run → --apply を項目別に実行。
- R19 65c0881c8：2,210本移動、2,577 Lean 更新。R-A が削除済みの JoinRightRelativeRetraction は除外。
- R16 ba39c0897：90本移動、113 Lean 更新。型・証明・名前空間保存。
- R17 bdf8d1c6a・R20 446304032・共有化 a6a10c52b：指定コミットから cherry-pick。R12 の新 import パスへ衝突解消。
- R15 d5cd974e2：密度層59本・一般補助81本を F1/Yoneda/PresheafDensity へ。新規集約入口を F1 に追加。密度層の F2 直接 import は0。
- 互換入口削除 d2385ea7e：267本削除、60 Lean 更新。614箇所の quoted module 名も直接配置へ。全依存辺・58利用元の正規化推移閉包が一致。既存配置監査成功。
- UniverseSSetMaps と Stable の補助6本の移動は R-B の担当として残す。
- 数学的内容・既存宣言の型・証明は保存。新規 sorry・公理なし。共有化は完全一致した4宣言だけ。型差のある組は一覧に残し所有レーンへ返す。
- main にあった文書差分・未追跡ファイルは保持。未追跡の3ファイルの import 更新は必要な機械的変更だけ行い、元の数学的内容をコミットに混入しない。
- 証拠：archive/r-c-main-2026-10-24/ の計画・静的照合・閉包記録。全29,786 Lean の import 欠落・循環は0。
- 検証完了：verify.sh の2ビルド・24監査が全て成功。main_statement の直接 sorry 閉包は空。HomotopicalAlgebra の3監査・bar評価2件も終了コード0。検証 HEAD は e0ca9ecdb578aaa492d91eda3447d4d0b9f75d3d。
- 完了：main の対象実装と検証記録をコミットし、HEAD・件数・verify.log末尾を報告。R-B は次の占有調整をコーディネータへ依頼できる。

最終件数：延べ2,440移動（元モジュール2,359本）、267入口削除。最終配置で更新・新規の tracked Lean は2,869本。既存未追跡3本の import 更新は別枠で、数学的内容をコミットに取り込んでいない。削除 orphan olean は2,626で移動元＋削除数と一致。
