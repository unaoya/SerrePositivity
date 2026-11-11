# 調整（段階 II）

作成：2026-11-05（整理の期間の調整役が書き直した）。整理の期間（段階 I、10-31〜11-05）の暦・待ち条件・経過は [archive/coordination-stage-i.md](archive/coordination-stage-i.md)。
**段階 II の正本は [段階 II の計画](stage-ii-plan-draft.md)**（11-05 夜に確定）。本書はその運用の規則と、各レーンの現状だけを持つ。

## 1. レーン

段階 II のレーンは計画の §5.1 で確定した（11-05 夜）。開始文は調整役が書き、どれにも「F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json`」「main を取り込んでから始める」「本書 §2 の規則」を入れる。

| レーン | 道具 | 担当 | worktree・枝 | 入口 | 状態（11-07） |
| --- | --- | --- | --- | --- | --- |
| 調整役 | Claude Code | 暦・合図・取り込み、検収、BS の設計 | main | 計画・本書・`bhatt-scholze/design-status.md` | — |
| Kerodon の確認 | Codex | 対応表の全項目の確認 | `SerrePositivity-kerodon-review-a`（枝 `research/kerodon-review-a2`）・`-b`・`-c` | `research/kerodon-coverage/codex-review.md` | 全 10 章のやり直しと抜き取りは main（11-10）。-a2・-b は閉じた（11-10）。-c が KL-W1 の段 3 の後に partial・none の一括見直し（§8.2 の 4） |
| HA の確認 | Codex | HA の全項目の対応表（本全体、HA の形式化の検討の材料） | （閉じた） | `research/ha-coverage/codex-review.md` | **完了・閉じた**（11-11）：全 2,866 項目、`review/summary.md`。worktree と枝は削除 |
| HTT の確認 | Codex | HTT の全項目の対応表（本全体、Kerodon の行を参照） | （閉じた） | `research/htt-coverage/codex-review.md` | **完了・閉じた**（11-11）：全 1,730 項目、`review/summary.md`。worktree と枝は削除 |
| K の地図 | Codex | K の文献ごとの全項目の対応表（本論文 §3・§4、KST、Land–Tamme、Tamme、BGT） | （閉じた） | `research/k-coverage/codex-maps.md` | 完了・閉じた（11-11、f15ad120b）。全 17 文献 688 項目、要約 research/k-coverage/maps/summary.md。K の再開時に新しく開く |
| KL-W1 | Codex | ∞ の配置を Kerodon に合わせる | `SerrePositivity-kerodon-layout`・`refactor/kerodon-layout` | `stage-ii/kerodon-layout-w1.md` | 段 1.5 は main。段 1.6（割り当ての見直し）→ 段 2・3（§8、11-10） |
| ③ ∞ 供給 | Codex | G8 の四角形 → G14・G9・G10 | `SerrePositivity-inf-supply`・`math/inf-supply` | `stage-ii/inf-supply-w1.md` | KL-W1 の後 |
| ⑤a BS 実装 | Codex | BS-DOC1 → BS-W11 → BS-W12（BM18 の経路 B） | `SerrePositivity-bs-impl`・`math/bs-impl` | `bhatt-scholze/bhatt-scholze-codex-w16.md` | BS-W14 は main（A1 の二本は ⑤b の停止点 3 の後）。BS-W16（実例の欄、G12・P⁰ を除く）段 0（11-10） |
| ⑤b BS 実装 → ③-b ∞ 供給 b | Codex | BS-D69（停止点 3 で区切り、11-12）→ Δ・Δᵒᵖ の橋（G10、幾何学的実現） | `SerrePositivity-bs-d68`・`math/bs-d68` → `math/inf-supply-b` | `stage-ii/inf-supply-w2.md` | D69 停止点 3 は KL-W1 の後に取り込み。IS-W2 は追従の後に段 0 |
| ⑤c BS 実装 → ③-a ∞ 供給 a | Codex | BS-W17（停止点 5 で区切り、11-12）→ G8 の四角形・G14・G9 | `SerrePositivity-bs-classical`・`math/bs-classical` → `math/inf-supply` | `stage-ii/inf-supply-w1.md` | W17 停止点 5 は KL-W1 の後に取り込み。IS-W1 は追従の後に段 0 |
| ⑥ スキーム論 | Codex | BS17 Thm 4.1 (i) の経路 | `SerrePositivity-scheme`・`math/scheme` | `stage-ii/scheme-w1.md`（§6 で BS17 に絞る） | 2a′（移動）・2b・2d の一部は main、2d 進行中（11-07） |
| ① ∞ 中核 | Codex | Verdier 商（K の入口） | — | `stage-ii/inf-core-w1.md` | **止める**（K と一緒に後回し、11-07） |

後から足すもの（②④⑦、K 理論）と開く条件は計画の §5.1。

**11-11 の変更（ユーザー決定、`k-restart-draft.md` §4）**：① ∞ 中核の再開時期を「③ の後」から「③ の G8 の後、④ と並行」に早める案を検討対象にする。実際に動かすのは E∞ の作り方（HA の方向か）の決定の後。K の実装は ∞ の基盤（KL-W1 → ③ → ①）の後。それまでの紙の作業は `k-restart-draft.md`。

## 2. ビルドの規則

1. 全ビルド（ルート・監査対象・verify・束の下流ビルド）は**機械で一つずつ**。始める前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具 `scripts/refactor/with_build_lock.sh`（DG-W2(a) で作成、infra/dg-w2）が main に入ったら必ず経由する。
2. 束の途中は触ったモジュールだけ `lake build <module>`。下流の全ビルドは束の最後に一回。
3. **Lake の成果物キャッシュを全セッションで共有する（11-01 採用、Mathlib の cache と同じ仕組みのローカル版）。** `~/.zshenv` で `LAKE_ARTIFACT_CACHE=true`・`LAKE_RESTORE_ARTIFACTS=true`・`LAKE_CACHE_DIR=~/.cache/lake` を設定済み。入力（ソースと依存）のハッシュが同じ成果物は、どの worktree で作っても他の worktree の `lake build` が再コンパイルなしで使う（`RESTORE` で `.lake/build` にも復元されるので `lake env lean` の監査もそのまま動く）。
   - 既存の `.lake/build` の中身はキャッシュに入らない。効き始めるのは、この設定の後に `lake build` で作った分から。各 Codex は新しい shell を開くか `source ~/.zshenv` してから `lake` を使う（`lake env | grep LAKE_ARTIFACT_CACHE` で確認）。
   - 古い版が溜まるので、窓の区切りで `lake cache clean`（全消去）か、ディスクを見て判断する。
   - rsync の温め（`warm_build_dir.sh`）は、キャッシュに入っていない成果物が要るときの予備に格下げ。
   - **掃除（11-02 決定）**：`lake cache clean` は空きが 150 GB を切ったときだけ、全ビルドのない時刻に、全 worktree が温まった状態で行い、直後に main で `lake build` を走らせて現行の成果物を登録し直す。定期的な掃除はしない（11-02：22 GB・331,250 本、空き 455 GB）。
4b. **main の作業木の規則（11-04 決定、事故の後）**：main の作業木では Lean の編集もビルドもしない（取り込みと温めは Claude だけ）。main に直接コミットするセッション（BS の記録など）は、必ず `git commit --only <自分のファイル>` で、`git add -A`・`git commit -a` を使わない。11-04 に B4 の未コミットの削除（`Pair/Tower.lean`）が BS の記録コミット 38e6d889a に巻き込まれ、babef8b23 で復元した。
4a. **小さなビルドの規則（11-02 19:40 決定）**：変更したファイルと直接の importer までの小さなビルド（数百本以下）は、**下流ビルド・verify が走っていなければ合図なしで行ってよい**。確認は `ps -axo command= | grep "[l]ake build"` が空であることと、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること（取れなければ待つ）。下流・verify の時間帯（暦 §3）には行わない。全ビルド（下流・verify）は従来どおり暦と合図。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

- **Codex の書き込み先（11-11）**：Codex のチャットは main の作業木で起動していて、隣の worktree への書き込みが毎回承認になる。`~/.codex/config.toml` の `writable_roots` はアプリのチャットに効かなかったので元に戻した。対策は未決（チャットの権限の切り替え、または worktree を開いた新しいチャット）。
- **鍵の取り合い（11-10）**：調査のレーン（Kerodon・HA・HTT・K の地図）の `#check` の一括実行も同じ鍵を使う。調査のレーンは一回の鍵を 10 分以内に収める（モジュールの塊を小さく分け、塊ごとに鍵を取り直す）。実装のレーン（⑤a・⑤b・⑥）は `--wait 0` で諦めず、`--wait 1800` で待つ。

- **昼と夜の分け方（11-10 夜、ユーザーの希望）**：時刻は日本時間。
  - **夜（23 時〜翌 8 時）**：KL-W1 の一括の検査・保存比較・ビルドの束と、段 4（下流ビルドと verify）。この時間帯は KL-W1 が鍵を続けて持ってよい。ほかのレーン（実装・調査）は夜に鍵を取らない（紙の作業や編集は続けてよい。ビルドが要るところで止めて朝に回す）。
  - **夜の目印（11-10 夜に追加）**：KL-W1 は、夜の作業が終わったら（朝 8 時より前でも）`$TMPDIR/serre-night-klw1-done`（中身は終わった時刻と枝の HEAD）を置く。ほかのレーンは、夜でもこのファイルがあればふだんどおり鍵を取ってよい（一回 30 分以内、取り直しのループは使わない）。ファイルは翌朝 8 時に KL-W1 が消す。
  - **昼（8 時〜23 時）**：⑤a・⑤b・⑤c・⑥ と調査のレーンの小さなビルドを優先する。KL-W1 は鍵を使わない作業（改名表の修正、逆向きの import の整理、層の設定、報告）に充て、ビルドが要るときは 10 分以内の小さな対象ビルドだけにする。鍵を取り直すループ（`while rc==75`）は使わない。

- **整理券の鍵（11-11、ユーザー承認）**：`with_build_lock.sh` を書き換えた（main）。待ち手は整理券で並び、鍵が空いたら**順位が一番の整理券だけ**が取る（早い者勝ちをやめた）。順位は（組の順位、待ち始めた時刻）。
  - **組**：`impl`（⑤a・⑤b・⑤c・⑥・調整役の取り込み）、`research`（HA・HTT・Kerodon の `#check`）、`bulk`（KL-W1 の一括の検査・ビルド）。`--class` を省くと worktree 名から推定する（`kerodon-layout` → bulk、`*-review` → research、ほか → impl）ので、**各レーンのコマンドは今までのままでよい**。
  - **昼（JST 8〜23 時）は impl → research → bulk、夜は bulk → impl → research** の順。スクリプトが守らせるので、夜に impl が鍵を取ることを禁じる必要はなくなった（bulk が並んでいなければ impl が通る）。`$TMPDIR/serre-night-klw1-done` の合図は**不要**になった。
  - 取り直しのループは害がなくなった（列の後ろに並び直すだけ）。ただし **一回の塊は 30 分以内**（bulk は昼も夜も）、research は 10 分以内のまま。
  - **繰り上げ（11-11 追加）**：待ちが impl・research は 15 分、bulk は 30 分を超えた整理券は、組に関係なく先頭へ繰り上がる（繰り上がったものどうしは待ち始めの順）。impl の小さなビルドが続いても、research・bulk が飢えない。
  - **昼の bulk は繰り上げない（11-11 11:10 追加）**：昼は bulk の整理券を繰り上げず、impl・research の整理券がないときだけ bulk が取る。昼の bulk の塊は一回 10 分以内（KL-W1 は 5 分以内、11-11 18:10、KL-W1 §14）（10:37〜11:06 に 29 分の束が impl 4 本と research 3 本を止めたため）。夜の繰り上げは従来どおり。
  - **KL-W1 は鍵の外（11-11 22 時、ユーザー判断）**：停止点 3 の報告まで、KL-W1 は鍵を使わず、他のレーンも KL-W1 を待たない（`kerodon-layout-w1.md` §15）。KL-W1 の verify は `VERIFY_JOBS=4 VERIFY_MEMORY_GB=32`。
  - **夜は鍵を二つ（11-11 20 時、ユーザー承認）**：JST 23〜8 時は同時に二つまで通す（`serre-lake-build.lock` と `serre-lake-build.lock.1`）。bulk は同時に一つまで、もう一つは coord・impl・research が順に使う。昼は一つ。古いスクリプトは一つ目しか知らないので、各レーンは main の取り込みで新しいスクリプトにする。メモリ（64 GB）のため、夜に bulk が verify を流すときは `VERIFY_JOBS=4 VERIFY_MEMORY_GB=32` に抑える。
  - **鍵はビルドの間だけ持つ（11-11 17:10 追加）**：一回のビルド（または一回の監査）ごとに鍵を取って放す。編集・証明の検討・報告書きの間は鍵を持たない。鍵の中で「ビルドの会話セッション」（要求が来たときだけビルドする常駐プロセス）を動かす形は禁止（16:45〜 ⑤a の build-session.py が 19 分持ち、その間ほとんどビルドしていなかった）。
  - **coord の組（11-11 17:10 追加）**：調整役の取り込み・登録（main の作業木）は `coord` の組で、昼夜とも常に先頭（繰り上げより前）。worktree 名 `SerrePositivity` から推定する。
  - **持ち主の履歴（11-11 17:10 追加）**：鍵の取得・返却は `$TMPDIR/serre-lake-build.history.jsonl` に一行ずつ追記される（時刻・worktree・組・コマンド）。長い持ち方は後からこれで確かめる。モニターも読んでよい（読むだけ）。
  - **`--wait` の目安（11-11 11:10 改定）**：impl・research・bulk とも `--wait 3600`（繰り上げまで最大 15〜30 分＋前の持ち主の最大 30 分）。同じ worktree から整理券を複数出さない（待ちは一つにまとめる）。
  - **夜の空き（11-11）**：11-10 の夜は 01:08〜06:07 の 5 時間、鍵が空いた。KL-W1 は夜の束が早く終わったら次の段に続ける。止まったときは報告し、空いた鍵は impl が使ってよい（整理券の列が自動で回す）。
  - 列を見る：`zsh scripts/refactor/with_build_lock.sh --status`。
  - 切り替え中は、古い版で待っているプロセスが鍵が空いた瞬間に取ることがある（整理券を持たない）。それらが終われば列は整う。

## 3. 暦

全ビルド（下流・verify）の予定はまだない。各レーンの最初の束が見えたところで書く。

| 時期 | 内容 |
| --- | --- |
| 11-07 | Kerodon の確認（段 1′）。⑤a・⑤b・⑥ 開始。取り込みのたびに調整役がルートのビルド（キャッシュで数分）と監査 |
| 確認の完了後 | KL-W1（∞ の配置を Kerodon に合わせる、`stage-ii/kerodon-layout-w1.md`）。段 3 の後に下流ビルドと verify を一回（暦は段 1 の承認のときに書く）。①③は KL-W1 の取り込みの後に開始 |
| KL-W1 の取り込みの直後（調整役） | 対応表の宣言の場所を書き直す（11-11、ユーザー承認）：HTT・HA・Prisms の表と Kerodon・K の地図の「名前 @ パス:行」を、(1) KL-W1 の改名表で名前を置き換え、(2) Lean の `findDeclarationRanges?` で今のモジュールと行を環境から引き直す。見つからない名前は一覧にして止める（黙って消さない）。道具は `scripts/` に置き、以後の移動でも使う。直したら地図を作り直す |
| 宣言の場所の書き直しの後 | 文献の属性と InfinityCategories/Project の整理（同じ回、`citation-attributes.md` §5）。文献の属性 `@[cite KEY "番号"]` の一括レーン（11-11、ユーザー決定。`stage-ii/citation-attributes.md`）：属性・照会のコマンド・略号表、対応表から属性を自動で付ける（夜の bulk）、地図を属性から作る |
| KL-W1 の取り込みの後（11-12 決定） | 段階 II 後半の構成は `stage-ii/stage-ii-second-half.md`：⑤c → ③-a（G8 系、IS-W1）、⑤b → ③-b（Δ・Δᵒᵖ の橋、IS-W2）、KL-W1 のチャット → 一括、⑤a は経路 A で続行（sifted の一般部分は ③-b）、⑥ はそのまま。⑤∞（BS の ∞ 側）は 3a-2 の後に開く |
| ③の G8 の四角形の取り込み | BS に知らせる（S4 の生成辺）。④を開く |
| 段 G の最初の区切り（目安 12 月上旬） | 保守の束：L1（F-2 の deprecated alias の一括削除）・L2（旧 G8 の削除）。BS・③・KST が新しい名前へ移ったのを確かめてから。担当は①か② |
| ①の M1・M2・M7 の取り込み | L4（分数の一般版）を①の中で。K 理論レーン（B-3〜）を開く |
| ②を開くとき | L3（M16） |
| 余裕のあるとき・該当部分を触るとき | L5（台帳 R60 の大きな処置、R78）、L6（DG の D6〜D8、Asymptotic の商） |

## 4. 各レーンの現状

段階 I のレーン（すべて閉じた）と段階 II のレーン：

| レーン | 状態 |
| --- | --- |
| ∞ 整理（Codex） | 閉じた（C1〜C3 は 05c33bfc0） |
| ∞ 数学 G2 | 閉じた。IF-G2-finish の段 1 と段 2 の途中まで main に入った（408d87457、6f35a986f）。枝 `math/g2` と worktree は削除。残りは `infinity-g2-progress.md` の末尾の節から段階 II の ∞ 供給レーンが再開する |
| BS 設計・BS 実装（段階 I） | 閉じた。段階 II では BS 実装は新しい Codex チャット、設計は調整役が持つ（入口 `bhatt-scholze/design-status.md` §0、drafts の扱いは計画 §1.0） |
| DG・論文の層 | 閉じた |
| 段階 II の新しいレーン（11-07）：⑤a・⑤b・⑥・Kerodon の確認が稼働。① は止めている。③ は KL-W1 の後 | 11-05 夜：計画の確定。開始文は [stage-ii/lane-starts.md](stage-ii/lane-starts.md)、指示書は `stage-ii/`（①IC-W1、③IS-W1、⑥SC-W1）。⑤は W11（§6 の追記）|

## 5. 段階 I から引き継ぐ要点

- 整理の結果：DG 1,592 → 126 本、論文の層の区切りはすべて完了、∞ は中核層間の順序違反 0・直接の禁止辺 0・中核の閉包の KST とモデル圏 150 → 74（残りは M16）、F-2 で KST から移した 730 モジュールの名前空間をディレクトリに合わせた（改名表 `../scripts/refactor/targets/f-namespace-map.json`、旧名は deprecated alias で段 G の最初の区切りまで残す）。
- 主定理の閉包の sorry は 3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- 調整役の引き継ぎは [coordinator-handover-2026-11.md](coordinator-handover-2026-11.md)。
