# F2 入口の #check の移動（§10.28）

main f1c5ae6f5 の承認により、F2 の清い入口から届かない1,497件を scripts/audit_infinity_f2_checks.lean に移した。直接 import は769モジュール。旧 #check の全文と順序を保存し、重複除去・宣言名の書換えはしていない。F2.lean は F2.CatInfinity の public import と既存 docstring のみ（module 宣言を含む）。

定義元は既存成果物から decl_snapshot.lean --resolve-modules で照会し、move/split対応表で現在のモジュールへ写した後、現在の入口閉包と照合した。結果は残す0・移す1,497。ルートと InfinityCategories 直下の他の入口には #check はなかった。証拠は .lake/verify/batch-w1w2a/stop2/addendum27/classification.json。

manifest の99→100本への変更は、入口から移した宣言の受入検査を verify に残すためである。探索結果と manifest は100本で一致。verify.sh・verify_runner.py は変更していない。R73（W2b）で FilteredExchange が清くなったら入口へ戻す。

静的検査：直接違反296、禁止閉包 W1=1・W2a/W2b=172。w1+w2aの1,278項目はPASS、増加0。移動元・先の #check 全文と順序、import集合、docstring、manifest一致を照合済み。下流ビルド・保存比較の結果は停止点2の報告に記録する。全体verifyは停止点2の承認後。
