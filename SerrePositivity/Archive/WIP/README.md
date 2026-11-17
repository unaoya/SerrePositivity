# Archive/WIP：止まったレーンの作業途中ファイル

概要：レーンが停止した時点で main の作業木に未追跡のまま残っていた Lean ファイルを、全文のまま保存する場所（2026-10-31 新設、ユーザー決定）。
方針：ビルドしない（ルートの閉包にも領域の監査にも入らない）。元の場所には置かない（worktree と main の構成を同じにし、`git add -A` の巻き込みを防ぐ）。レーンが再開したら元のパスへ戻して、そのときの import 先に合わせて直す。
規約：`Archive/WIP/<元のパス>` に置く。下の表に由来（レーン・最終更新・元のパス・内容）を記す。
使われ方：再開するレーンの持ち主が読む。整理の対象にはしない。

| ファイル | レーン | 最終更新 | 元のパス | 内容 |
| --- | --- | --- | --- | --- |
| `DifferentialGraded/Morita/ScalarExtensionKernelOutputComponents.lean` | D（dg）、10-25 停止 | 2026-10-17 | `SerrePositivity/DifferentialGraded/Morita/` | kernel 出力評価と U12f 比較の成分計算（6 宣言、sorry なし） |
| `KST/Spectra/PointedParametricUncurryAction.lean` | Sp、10-28 停止 | 2026-10-20 | `SerrePositivity/KST/Spectra/` | uncurry 座標写像と標準族作用の厳密整合（3 宣言） |
| `KST/Spectra/PointedParametricUncurryPre.lean` | Sp | 2026-10-20 | 同上 | 全族入力制限と入力の標準懸垂（2 宣言） |
| `KST/Spectra/PointedUncurryActionTensor.lean` | Sp | 2026-10-20 | 同上 | uncurry 作用とテンソル curry 同型の逆射の同定（2 宣言） |
| `KST/Spectra/PointedUncurryComposition.lean` | Sp | 2026-10-20 | 同上 | uncurry 作用と豊穣合成の整合（1 宣言） |

注意：`scripts/audit_kst_spectra_s3.lean`・`audit_kst_spectra_d3tail.lean` の名前の一覧に KST の 4 本の旧名が残っている（import ではないので監査は通る）。∞ 基盤の束（R75 の段）で外す。


2026-11-17：`HomotopicalAlgebra/Simplicial/RelativeFillerComparison.lean` は消した（AR-W1 の確認で本体の `exists_relative_vertical_homotopy` の pushout-product への適用だけと判定、ユーザー決定）。タグ `archive/archive-u12e-relativefiller-2026-11-17` から取り出せる。