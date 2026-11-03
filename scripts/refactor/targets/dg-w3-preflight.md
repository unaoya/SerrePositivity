# DG-W3 §3.0 再確認

起点：`b23296091`、ブランチ `infra/dg-w3`、専用 worktree `SerrePositivity-dgw1`。
旧調査 `ef951fa5d` の判断と §7 を維持。main の後続コミットは取り込んでいない。

- `python3 -B scripts/refactor/merge_modules.py scripts/refactor/targets/dg-w3-merge-plan.json --area SerrePositivity.DifferentialGraded --check --max-lines 1700`：終了 0。
- 48 統合先・608 元、最大 1,621 行、超過 0、統合先循環 0。601 件の警告は従来どおり匿名 section の閉鎖。
- 全 import グラフの統合前後も非循環。元モジュールの同一性を保った閉包比較で失われる到達先 0。宣言の `uses_modules` による照合は before snapshot 採取後に追記する。
- DG から KST・IC・Asymptotic・PerfectComplex への直接辺・推移的な閉包はいずれも 0。Perfect の 2 本の変更と、`HomologicalAlgebra.Complex.StrictlyPerfect`／Mathlib の `Module.Finite.exists_comp_eq_id_of_projective` への移行を確認。
- 旧調査との差分だけを検査。閉包の増分またはソースに差がある利用元 1,583 本、今回追加確認した供給元 1,169 本。新たな短名衝突候補 0、字句スコープの異常 0。これは静的近似であり、Lean の名前解決の保証ではない。
- 旧候補 `DGNerve/HomotopyCategory.lean` の 4 箇所と universe 順序の重点対象 4 本は、保存比較で引き続き照合する。608 本すべて、元の universe コマンド列が生成 section 内に保持されることを再確認。
- 下流の逆閉包：10,571 本。単独 1.0–1.5 秒/本の参考値は 176.2–264.3 分。実時間は Lake キャッシュの命中状況による。import の書換候補は 830 ファイル。
- 草案の元・統合先と import 和に修正は不要。追加 `downstream_imports` は現時点で 0。

再現用スクリプト、詳細の差分・universe 一覧、層検査の before は `.lake/verify/dg-w3/`。Lean/Lake の実行前に本調査を行った。共有鍵が ∞ 側の before 処理で占有されていたため、DG のビルド処理は鍵の解放待ちに入った。

## 宣言単位の照合と内部ビルドへの移行

23,522 宣言を照合し、失われる参照 0・禁止依存 0。batch の定義元記録は個別環境とハッシュ照合して補正した。D4・D5 と 1 箇所の修飾後、内部 round 2 で停止。詳細は [停止報告](dg-w3-stop-2026-11-02.md)。

## 最終結果

§9〜§12 の処置と保存比較を経て、下流・verify は PASS。詳細は [停止点 3 の報告](dg-w3-final-report.md)。
