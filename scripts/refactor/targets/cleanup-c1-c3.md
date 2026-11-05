# 片付け C1〜C3 — 完了報告

PASS。基点 main `2a9a24cbf`、枝 `codex/if-cleanup-c1-c3`。検証したソースは `1bf7cd46c`。main 作業木での変更・ビルドなし。小さなビルドと該当監査に限定した。

## C1：層の地図

InfinityCategories/README.md の表に Simplicial・Kan/Pointed・StablePresentable・ModelBridge を含む現行の各層と入口・代表監査を記載し、層順序と F1B の straightening 境界を明示した。F1・F1B・F2 のディレクトリ名は維持。空または部分的な入口を層全体の一括 import と混同しない説明を加えた。

`f-namespace-map.json` の確定版は変更していない（SHA256 `0dace9141adf5f24ee010042271f159dd37b335a45f05e25348b26efcc41571a`）。

## C2：利用者 0 の診断入口 4 本

全 Lean 31,447 ファイルと正式監査 102 本で利用者を再計測。本番・スクリプトの import、監査の importModules、モジュール名の文字列参照がすべて 0 の試作の末端を、Derived/Diagnostics/ へ移した。

| モジュール（旧位置は Derived/ 直下） | ソース宣言 |
| --- | ---: |
| DGKappaPresentedFreeNativeFunctor | 3 |
| DGKappaPresentedSourceNativeAction | 3 |
| DGKappaPresentedSourceNativeFunctor | 3 |
| DGKappaPresentedSourceShiftAction | 3 |

4 ファイルとも移動前後の SHA256 が一致。公開名・型・本体・import は保持し、移動前のモジュール名を参照する Lean ソースは残っていない。`f-ledger.json` の 4 行を `moved_diagnostic` / `PASS` とし、元の位置・利用者 0 の証拠・移動先を残した。

本番・正式監査への登録は追加していない。限定監査 `scripts/refactor/check_cleanup_c2.lean` で 12 ソース宣言を #check / #print axioms し、移動先の生成宣言を含む 24 宣言について標準 3 公理だけであることを確認した。正式監査の登録候補 145 本と HA/Simplicial の孤立入口 121 本は段階 II の保守へ残す。利用者がある旧 ε/strict 経路など 20 本も動かしていない。

## C3：旧 G8 を deprecated に

| 旧宣言（SetWeight 以下） | 正本 |
| --- | --- |
| elementsComparison | elementsComparisonNatural |
| elementsComparison_projection | elementsComparisonNatural_projection |
| elementsComparison_isPrecompositionEquivalence | elementsComparisonNatural_isPrecompositionEquivalence |
| sectionsEquivalence | sectionsEquivalenceNatural |
| tensorSpaceFunctor_setWeightHom | tensorSpaceFunctor_setWeightHomNatural |

旧 5 宣言に `since := "2026-11-05"` を指定。Natural 版は旧版を import するため、逆 import による循環を作らず、定義元で移行先と import 先を案内する message 形式の deprecated 属性を使った。旧版の型・本体は一切変更していない。共有する補助宣言は deprecated にしていない。

BS の `report-codex-s4-sieve.md` と `drafts/Sheaves/SetSections.lean`・`SheafGenerators.lean` が Natural 版を明示しており、旧 G8 の実呼び出しはなかった。別の枝や BS の証明は変更していない。Natural 版を正本にすることと、未完の自然性の四角形の証明は区別した。

## 検証

| 検査 | 結果 |
| --- | --- |
| 対象 8 モジュール（診断移動先 4、旧比較 2、Natural、F2 入口） | PASS、10.8 秒 |
| audit_infinity_f2 | PASS、17.0 秒。既存検査数・本番 import 対象集合を保持、deprecated 5 件と正本を追加検査 |
| check_cleanup_c2 | PASS、10.7 秒。移動先 4 本・24 環境宣言、標準 3 公理のみ |
| ファイル同一性・旧比較の宣言保存・README リンク | PASS |

F2 の実コマンド数は前後とも #check 584、#print axioms 77。正式監査の manifest は変更していない。旧比較を保持する定義内の deprecated 警告は意図された互換経路であり、警告抑制は加えていない。変更した Lean ファイルの長行警告は 0。依存先から再表示された既存の長行警告は 2,697 行あり、今回の対象外として保持した。

最初の限定監査では検査用カウンターの型推論が失敗し、`Nat` を明示して再実行した。ライブラリの証明失敗はなく、初回ログも保持した。

機械可読の記録は [cleanup-c1-c3.json](cleanup-c1-c3.json)、ログは `.lake/verify/if-cleanup-c1-c3/`。大きな下流ビルド・全 verify は実行していない。worktree と枝は取り込み確認まで保持する。
