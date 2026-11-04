# Codex 作業指示書 IF-F：段 F（台帳と整理、R54 の名前空間）― 整理の最後の束

作成：2026-11-04 夜（管理は Claude）。宛先：∞ の整理レーンの Codex（W2c と同じチャット、worktree `../SerrePositivity-ifw0-3`、main 8878743e3 以降から `infra/if-f` を切る）。
計画：[infinity-foundation-plan.md](infinity-foundation-plan.md) §5 段 F（R60・R32・R33・R36・R42・R43・R54）。前提の判断表・停止条件・保存比較 v3b・層検査の 3 条件は W2b・W2c の最終形をそのまま使う。
**二つの段に分ける**：F-1（台帳と小さな整理。下流は小さい）を先に、F-2（R54 の名前空間。∞ の閉包ほぼ全部の再ビルド）を後に。**F-2 の適用はユーザーの判断（§3）の後**。

## 1. F-1：台帳と小さな整理（草案はビルドなし、**停止点 1**）

1. **台帳 R60**：`scripts/refactor/targets/f-ledger.json`。各行に「主経路／診断／archive／一般論を抽出」と理由。対象：Archive の FilteredExchange（W2b の B 1,726 本：archive のままでよいか確認）、F1/Cocartesian、HA/Rectification、ClosureFunctoriality、KST/Comparison・ProExcision、Spectra の休止部分、R32・R33・R36・R42・R43（反例・凍結候補・未登録・監査で被覆されない・転送入口）。
2. **W2c からの持ち越し**：(a) `import all` で復旧した private 参照 15 辺：各辺について「private を外して公開にする」か「参照側を定義元のファイルへ戻す」かを決める（宣言の本文は変えない。公開にする場合は名前の衝突を確かめる）。(b) 段 G への入力（`w2c-stage-g-input.json`、Stable に置けなかった分数）と M16 は台帳に載せるだけ（処置は段 G）。
3. **verify の対象収集の修正**（W2c §8）：監査ファイル中の `importModules` の引数も監査対象のビルドに加える（`verify_runner.py`／準備段）。試験つき、別コミット。
4. R67 の残り（基盤の層だけが使うものの分類し直し）は計画の行のとおり。
5. 草案の報告：台帳の行数と処置の内訳、15 辺の処置、下流の見積もり（F-1 は小さいはず）。

## 2. F-2：R54 の名前空間（草案だけ。適用は §3 の判断の後）

1. **現状の計数**：InfinityCategories の下で、ディレクトリと名前空間が食い違う宣言（例：InfinityCategories の下にある `SerrePositivity.KST.LocalizingInvariants` 176・`KST.Fibration` 150・`KST.SConstruction` 128 の namespace ブロック、W2b・W2c で移した分）を数え、モジュール・宣言の一覧を作る。
2. **付け替えの対応表の草案**：`targets/f-namespace-map.json`。旧名 → 新名（ディレクトリに合わせた名前空間）。旧名は `@[deprecated]` の alias で残す（計画どおり）。BS・KST・論文の層・G1・EInfinity・DG の利用者の数。
3. **F1・F1B・F2 の改名の案**（計画 §3 の 10-28 決定「改名は後で」）：内容に沿う名前（例：F1 → Fibrations、F1B → Localization、F2 → Presentable など）の候補と、改名した場合の影響（モジュール数・import 行・名前空間）。**案を出すだけ**。
4. 下流の見積もり（名前空間だけ変える場合／ディレクトリも改名する場合）。

## 3. ユーザーの判断が要る点（F-2 の草案の後に Claude が整理して尋ねる）

- 名前空間の付け替えの範囲：(i) 移した宣言だけ（KST.* が残っている分）、(ii) InfinityCategories 全体をディレクトリに揃える。
- F1・F1B・F2 のディレクトリ名を改名するか。
- deprecated alias をいつ消すか。

## 4. 手順・禁止事項

- F-1：草案 → 停止点 1 → 適用と内部検証（小さなビルド）→ 下流（小さい見込み）→ verify → 停止点 2 → Claude が取り込み。
- F-2：草案 → 停止点 3（§3 の判断材料）→ 判断の後に別の指示で適用。適用の時期は G1・BS の区切りに合わせる（名前の変更が及ぶため、事前に両者へ main の取り込みと改名表の受け取りを依頼する）。
- 禁止：宣言の本文の変更（§1-2 の private の公開化を除く）、R78（Mathlib への置き換え）、段 G の数学。F-2 の判断の前の名前空間の変更。

## 5. 追記（2026-11-04 夜、F-2 の方針の決定：ユーザー）

§3 の三点はユーザーが次のとおり決めた：
1. **範囲は「移した宣言だけ」**：W2b・W2c で KST から ∞ へ移したのに `SerrePositivity.KST.*` の名前空間が残っている宣言を、置かれたディレクトリに合わせる。InfinityCategories 全体の付け直しはしない。
2. **ディレクトリ名（F1・F1B・F2）は改名しない**。各層の中身は `InfinityCategories/README.md` の表に書く（F-2 の中で更新）。
3. **deprecated alias は段 G の最初の区切りまで残す**（目安 1 か月）。BS・G2・KST が新しい名前へ移ったのを確かめてから、一度にまとめて消す（その束は別に出す）。

したがって §2 の草案は (1) の範囲だけでよい（§2-3 の改名案は不要）。草案（計数、対応表 `f-namespace-map.json`、利用者の数、下流の見積もり）→ 停止点 3 → Claude が承認したら適用（時期は G2・BS の区切りに合わせて Claude が合図）。
