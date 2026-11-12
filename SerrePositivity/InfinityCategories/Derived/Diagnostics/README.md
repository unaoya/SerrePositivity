# Derived の試作・診断入口

C2（2026-11-05）で、本番・正式監査・スクリプトの利用者が 0 の DGKappa 試作の末端 4 本をここへ移した。
16 時間試作の出発提示・自由提示と native dg nerve への接続を保存する。宣言名・型・本体は元のままで、
本番入口や正式監査への一括登録は行わない。前提となる表示の内部部品は元の位置を保つ。

| モジュール | 内容 |
| --- | --- |
| [DGKappaPresentedFreeNativeFunctor](../../Project/DerivedCategories/Diagnostics/DGKappaPresentedFreeNativeFunctor.lean) | 自由表示の全次数作用と native nerve/core |
| [DGKappaPresentedSourceNativeAction](../../Project/DerivedCategories/Diagnostics/DGKappaPresentedSourceNativeAction.lean) | 出発提示の恒等・合成と native nerve |
| [DGKappaPresentedSourceNativeFunctor](../../Project/DerivedCategories/Diagnostics/DGKappaPresentedSourceNativeFunctor.lean) | 出発提示の全次数作用と native nerve/core |
| [DGKappaPresentedSourceShiftAction](../../Project/DerivedCategories/Diagnostics/DGKappaPresentedSourceShiftAction.lean) | 出発提示の整数 shift と native nerve |

今回の限定検査は `lake env lean scripts/refactor/check_cleanup_c2.lean`。
正式監査の登録候補 145 本と HA/Simplicial の孤立入口 121 本の処置は、R60 台帳の記録のまま段階 II へ引き継ぐ。
