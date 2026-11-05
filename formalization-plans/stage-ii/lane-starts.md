# 段階 II の各レーンの開始文（11-05 夜）

作成：段階 II の調整役。ユーザーが新しいチャットの最初に貼る文面。どれも「F-2 の改名表」「main を取り込んでから始める」「coordination.md §2 の規則」を含む。
⑤ BS 実装の Codex は、BS 設計が W11 を改名表で追従してから開始文を書いて渡す（調整役は書かない）。

## BS 設計（Claude Code、新しいチャット）

```
あなたは SerrePositivity の Bhatt–Scholze 側（段階 II の目標 A：E3 を消す）の設計役です。
入口は formalization-plans/bhatt-scholze/design-status.md §0 です（0.1 規則、0.2 読む順、0.3 現在地、0.4 ∞ への依頼）。
段階 II の正本は formalization-plans/stage-ii-plan-draft.md（11-05 夜に確定）で、目標 A の進め方は §1.0：drafts（formalization-plans/bhatt-scholze/drafts/、51 本・sorry 893）を BS 実装の Codex が本体の決まった置き場所へ新規ファイルとして移しながら sorry を証明に置き換え、sorry 0 のものから調整役が main に取り込みます。置き場所と順序は drafts/README.md。進み具合は drafts の残り本数と sorry の数で design-status に記録してください。
最初の仕事：F-2 の改名表（scripts/refactor/targets/f-namespace-map.json）で BS-W11 の指示書（bhatt-scholze-codex-w11.md）と drafts の名前を追従し（11-05 時点で drafts の旧名の使用は 0）、BS 実装の Codex への開始文を書いてください。Codex には main（f3fcefe8e 以降）から worktree を一つ切らせ、coordination.md §2 の規則（小さなビルドだけ、main の作業木では作業しない、取り込みは調整役）を守らせます。
∞ への依頼は調整役を通します。G8 の四角形（S4 の生成辺）は ∞ 供給レーン（③）の最初の仕事で、main に入ったら調整役が知らせます。main への直接コミットは git commit --only -- <paths> とし、その後 git show --stat HEAD で確かめてください。
```

## ③ ∞ 供給（Codex、新しいチャット）

```
SerrePositivity の段階 II、∞ 供給レーンの Codex として作業してください。
指示書は formalization-plans/stage-ii/inf-supply-w1.md です。§0 の準備（main f3fcefe8e 以降から worktree ../SerrePositivity-inf-supply と枝 math/inf-supply を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
最初の仕事は G8 の四角形の残り（infinity-g2-progress.md の末尾）、段 1 の②の完成です。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
停止点ごとに報告してください。
```

## ① ∞ 中核（Codex、新しいチャット）

```
SerrePositivity の段階 II、∞ 中核レーンの Codex として作業してください。
指示書は formalization-plans/stage-ii/inf-core-w1.md です。§1 の準備（main f3fcefe8e 以降から worktree ../SerrePositivity-inf-core と枝 math/inf-core を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
最初の仕事は段 0（M1・M2・M7 の紙の筋）で、停止点 0 で報告して待ってください。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
```

## ⑥ K の準備（Codex、新しいチャット）

```
SerrePositivity の段階 II、K の準備レーンの Codex として作業してください。
指示書は formalization-plans/stage-ii/k-prep-w1.md です。§1 の準備（main f3fcefe8e 以降から worktree ../SerrePositivity-k-prep と枝 math/k-prep を切る、F-2 の改名表 scripts/refactor/targets/f-namespace-map.json の新しい名前を使う）から始めてください。
最初の仕事は段 1（公理 (3) の供給経路の再確認。報告だけで Lean は書かない）です。報告の後は段 2（KST §5 のスキーム補題）へ進んでかまいません。
規則は formalization-plans/coordination.md §2 です。小さなビルドだけにし、main の作業木では作業しません。main への取り込みは調整役が行います。
```
