# 段階 II の各レーンの開始文（11-05 夜）

作成：段階 II の調整役。ユーザーが新しいチャットの最初に貼る文面。どれも「F-2 の改名表」「main を取り込んでから始める」「coordination.md §2 の規則」を含む。
BS 設計のチャットは置かない（11-05 夜、ユーザー）。BS の設計・検収も調整役が行う。

## ⑤a BS 実装：BS-DOC1 → BS-W11（Codex、新しいチャット）

```
SerrePositivity の段階 II、Bhatt–Scholze 実装の一本目のレーン（⑤a）の Codex として作業してください（目標 A：E3 を消す）。もう一本（⑤b、枝 math/bs-d68）と並行するので、触るファイルが重なりそうなら止めて報告してください。
最初の仕事は formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-doc1.md（BS-DOC1：docstring に論文の番号を書く）です。停止点 1 で報告して待ってください。BS-DOC1 が main に入ったら、次の指示書 formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-w11.md に進みます。W11 は、まず §6 の追記（段階 II の規則、11-05 夜）を読み、次に §0〜§5 を読んでください。前提の規則は BS-W10（bhatt-scholze-codex-w10.md）§0・§3 で、完了例は report-codex-w10.md です。
§6 の 1 のとおり、main の最新（2c5d7e414 以降）から worktree ../SerrePositivity-bs-impl と枝 math/bs-impl を切ってください。F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使います。
drafts（formalization-plans/bhatt-scholze/drafts/）を新規ファイルとして本体へ移しながら、sorry を証明に置き換えます。置き場所は drafts/README.md です。本体に sorry は残さず、閉じられない宣言は drafts に残します。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
停止点ごとに report-codex-w11.md に書いて報告してください。
```

## ⑤b BS 実装：D68 の直接証明（Codex、新しいチャット）

```
SerrePositivity の段階 II、Bhatt–Scholze 実装の二本目のレーン（⑤b）の Codex として作業してください（目標 A：E3 を消す）。
指示書は formalization-plans/bhatt-scholze/instructions/bhatt-scholze-codex-d68.md です。§3 の 1 のとおり、main の最新（2c5d7e414 以降）から worktree ../SerrePositivity-bs-d68 と枝 math/bs-d68 を切ってください。F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使います。
最初の仕事は段 0（紙の筋と順序、Bockstein の照合の確認）で、停止点 0 で報告して待ってください。
もう一本の BS のレーン（⑤a、枝 math/bs-impl）と並行するので、触るファイルが重なりそうなら止めて報告してください。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
```

## ③ ∞ 供給（Codex、新しいチャット。KL-W1 が main に入ってから）

```
SerrePositivity の段階 II、∞ 供給レーンの Codex として作業してください。
指示書は formalization-plans/stage-ii/inf-supply-w1.md です。§0 の準備（main f3fcefe8e 以降から worktree ../SerrePositivity-inf-supply と枝 math/inf-supply を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
最初の仕事は G8 の四角形の残り（infinity-g2-progress.md の末尾）、段 1 の②の完成です。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
停止点ごとに報告してください。
```

## ① ∞ 中核（止めている。K と一緒に後回し、11-07）

```
SerrePositivity の段階 II、∞ 中核レーンの Codex として作業してください。
指示書は formalization-plans/stage-ii/consolidation/inf-core-w1.md です。§1 の準備（main f3fcefe8e 以降から worktree ../SerrePositivity-inf-core と枝 math/inf-core を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
最初の仕事は段 0（M1・M2・M7 の紙の筋）で、停止点 0 で報告して待ってください。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
```

## ⑥ スキーム論（Codex、新しいチャット）

```
SerrePositivity の段階 II、スキーム論レーン（⑥）の Codex として作業してください（BS17 Thm 4.1 (i) に要る代数幾何の土台。K 用の部分は後回し）。
指示書は formalization-plans/stage-ii/scheme-w1.md です。§1 の準備（main の最新（2c5d7e414 以降）から worktree ../SerrePositivity-scheme と枝 math/scheme を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
指示書の §6 の追記（11-07）のとおり、BS17 Thm 4.1 (i) の経路だけを進めます。段 1（公理 (3) の調査）と段 2c は行いません。最初の仕事は段 2a（BS17 の経路に要る範囲の照合と紙の筋）です。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
```
