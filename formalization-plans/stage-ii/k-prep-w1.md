# Codex 指示書 KP-W1：K の古典的な準備（公理 (3) の再確認、KST §5 のスキーム補題）

作成：2026-11-05 夜（段階 II の調整役）。宛先：⑥ K の準備レーンの Codex（新しいチャット）。検収：調整役（設計判断はユーザーと決める）。
正本：[段階 II の計画](../stage-ii-plan-draft.md) §2（B-5）・§5.1。K の経路は [infinity-lanes/foundations.md](../infinity-lanes/foundations.md) §3 と [kst-lanes/k-theory-kst-route.md](../kst-lanes/k-theory-kst-route.md)。規則は [coordination.md](../coordination.md) §2 と計画 §4。

## 0. 目的

K 理論の本体（B-3〜B-6）は ∞ 中核の Verdier 商（M1・M2・M7）を待つ。その間に、K に依存しない古典的な部分を進める。
1. **公理 (3)（冪零不変性）の供給経路を決めるための調査**（Lean は書かない）。
2. **KST §5 のスキーム補題と可換環論**（休止中の K-L7 の残り）の Lean。

## 1. 準備

1. main（f3fcefe8e 以降）から worktree `../SerrePositivity-k-prep`（`LEAN_Projects.nosync/` の下）と枝 `math/k-prep` を切る。`source ~/.zshenv` の後、`lake env | grep LAKE_ARTIFACT_CACHE` でキャッシュが効いていることを確かめ、`lake build SerrePositivity.KST.SchemeLemmas` で温める。
2. F-2 で名前空間が変わった宣言は、改名表 `scripts/refactor/targets/f-namespace-map.json` の新しい名前を使う（旧名の deprecated alias は新しいファイルでは使わない）。
3. main の大きな束が入るたびに main を取り込む（調整役が知らせる。衝突は main 側を正に）。

## 2. 段 1：公理 (3) の供給経路の再確認（報告だけ）

**背景**：Thm 3.1 の八公理のうち (3)（冪零不変性）は、v1 の D ブロック（⊗ℚ の五項補題と、離散的な冪零不変性 D9）で供給する予定だった。D9 の Step 2 は D2（連結 dg 代数の GL と、Waldhausen 2.3.2 の ∞-S• 版の比較定理。群完備化と plus 構成）を使う。ところが計画 v2（Land–Tamme 経路、10-19）では L2 の plus 構成を「不要」として凍結した。このため (3) の経路は v2 で未決のまま残った（foundations.md §3 の 4）。

**調べること**（原典と既存コードを読んで報告。Lean は書かない）：
1. Lean 側で公理 (3) が何を要求しているか。`theorem_3_1_K0` と `Section4.supportedRankK0_descent` の型、八公理の形式化（`KST/Descent/` など。L8 の記録 `formalization-plans/archive/L8-descent-log.md` に「公理 (3) の幾何学的な型」がある）から、(3) の正確な主張（どの環・どの K・係数・次数）を書き出す。
2. 候補の経路を比べる。各経路について、要る基盤（既存か、どのレーンが作るか）、引用の有無（**K 理論側は引用なしが段階 II の条件**）、規模の見込みを書く。
   - (a) D9 のまま：D2（GL と plus 構成）を凍結した L2 のコードから使う。L2 の既存コードがどこまであるか（凍結の状態、sorry の有無）。
   - (b) Land–Tamme で処理する：LT の Cor 3.5（冪零不変性。経路の記録 §「LT Thm A.2 の証明で ⊙ を使う箇所」）か、⊙ と pro 切除（B-4）から (3) を得る。⊗ℚ と E = fib(K_ℚ → K[1/p]_ℚ) の形で足りるか。
   - (c) ほかに見つかった経路（Goodwillie の定理は引用になるので、使うなら証明の規模も）。
3. 推奨と、その理由。決められない点はユーザーに聞く形の問いにする。

**止めて報告（停止点 1）**：上の 1〜3 を `formalization-plans/stage-ii/k-prep-axiom3-report.md` に書いて `math/k-prep` にコミットし、要約を報告する。調整役がユーザーと経路を決める。**段 2 はこの報告の後、承認を待たずに始めてよい**（段 2 は (3) の経路に依存しない）。

## 3. 段 2：KST §5 のスキーム補題と可換環論（Lean）

休止中の K-L7 の残り（[kst-lanes/L7-scheme-lemmas.md](../kst-lanes/L7-scheme-lemmas.md) の「残り」）を、依存の順に進める。既存のコードは `KST/SchemeLemmas/`（例：`NoetherianFiniteModuleFlattening.lean`）と `KST/Descent/GenericFiniteFlattening.lean`。

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 2a | 現状の照合：L7 の引き継ぎ（10-19）の後に何が main に入ったか、F-2 の後の名前と置き場所、残りの各項目の前提を確かめ、順序と規模を報告 | **停止点 2a**（報告して承認を待たずに 2b へ進んでよい） |
| 2b | Stacks 051R（多項式商の局所化とテンソル基底変更の比較 → 有限型代数の一般自由性）、続いて Stacks 05FS（Lemma 38.9.2、一般自由性・Noether 帰納法で代数の射影性の存在を完成） | **停止点 2b**：調整役が取り込む |
| 2c | KST Prop 5.2（鳩ノ巣による共通冪、核の消滅、Artin–Rees による交わりの消滅）、Huneke–Swanson 8.1.5・8.2.1 と KST Lemma 5.6 の古典部分（Rees 拡大の整性・有限性から有限射） | **停止点 2c** |
| 2d | Stacks 0811・0810（相対 Noether 正規化と台の次元による devissage → 一般の有限型加群の平坦化）、Stacks 081T（Lemma 38.31.4、Temkin 2008 Lemma 2.1.5：平坦化の中心を strict transform と大域の貼り合わせへ） | **停止点 2d** |

- KST Remark 3.3 と Lemma 5.5 の幾何の入力は、導来 blowup の対象（K 理論レーン）が決まってから。ここでは扱わない。
- 時間の目安は L7 の記録（2b は 10〜25 時間、2c は 12〜28 時間、2d は 24〜60 時間）。条件付きの中心存在を「一般の平坦化の完成」と呼ばない（L7 の注意）。
- 数学的に詰まったら、通ったところまで（ビルドが通り sorry 0 の補題）を報告して止める。未完の Lean は main に入れない（枝 `math/k-prep-wip` に置く）。

## 4. 共通の規則

1. 新しい数学は**新規ファイルだけ**、置き場所は `KST/SchemeLemmas/`（K に依存しない可換環論で一般性のあるものは `CommutativeAlgebra/` の新しい下位ディレクトリ。BS 実装も `CommutativeAlgebra/` に置くので、既存の下位ディレクトリには足さない）。既存の宣言の本文・型・名前は変えない（要るときは止めて報告。処置は判断表の範囲で、保存比較 v3b）。
2. sorry・公理・新しい引用を残さない。Mathlib にあるものは Mathlib を使う（同じ主張を作り直さない）。
3. ビルドは小さなビルドだけ（変更したファイルと直接の importer）。始める前に `ps -axo command= | grep '[l]ake build'` が空で、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること。全ビルド（下流・verify）はしない。
4. 新規モジュールは入口（`KST/SchemeLemmas.lean` など）と該当する監査に登録する（`importModules` を使う監査は `import` 行にも書く）。監査は単独で流す。
5. main の作業木では編集もビルドもしない。main への取り込みは調整役が行う。
6. docstring は日本語の 概要／方針／規約／使われ方。
7. 報告は段ごとに：ビルドの結果、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩、コミット。

## 5. 条件付きの事前承認

段 2 の各段は、「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら、停止点で報告したうえで承認を待たずに次の段へ進んでよい。取り込みは調整役が停止点 2b・2c・2d ごとに行う。
