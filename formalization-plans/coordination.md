# 調整（段階 II）

作成：2026-11-05（整理の期間の調整役が書き直した）。整理の期間（段階 I、10-31〜11-05）の暦・待ち条件・経過は [archive/coordination-stage-i.md](archive/coordination-stage-i.md)。
**段階 II の正本は [段階 II の計画](stage-ii-plan-draft.md)**（11-05 夜に確定）。本書はその運用の規則と、各レーンの現状だけを持つ。

## 1. レーン

段階 II のレーンは計画の §5.1 で確定した（11-05 夜）。開始文は調整役が書き、どれにも「F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json`」「main を取り込んでから始める」「本書 §2 の規則」を入れる。

| レーン | 道具 | 担当 | worktree・枝 | 入口 | 状態（11-07） |
| --- | --- | --- | --- | --- | --- |
| 調整役 | Claude Code | 暦・合図・取り込み、検収、BS の設計 | main | 計画・本書・`bhatt-scholze/design/design-status.md` | — |
| Kerodon の確認 | Codex | 対応表の全項目の確認 | `SerrePositivity-kerodon-review-a`（枝 `research/kerodon-review-a2`）・`-b`・`-c` | `research/kerodon-coverage/codex-review.md` | 全 10 章のやり直しと抜き取りは main（11-10）。-a2・-b は閉じた（11-10）。-c が KL-W1 の段 3 の後に partial・none の一括見直し（§8.2 の 4） |
| HA の確認 | Codex | HA の全項目の対応表（本全体、HA の形式化の検討の材料） | （閉じた） | `research/ha-coverage/codex-review.md` | **完了・閉じた**（11-11）：全 2,866 項目、`review/summary.md`。worktree と枝は削除 |
| HTT の確認 | Codex | HTT の全項目の対応表（本全体、Kerodon の行を参照） | （閉じた） | `research/htt-coverage/codex-review.md` | **完了・閉じた**（11-11）：全 1,730 項目、`review/summary.md`。worktree と枝は削除 |
| K の地図 | Codex | K の文献ごとの全項目の対応表（本論文 §3・§4、KST、Land–Tamme、Tamme、BGT） | （閉じた） | `research/k-coverage/codex-maps.md` | 完了・閉じた（11-11、f15ad120b）。全 17 文献 688 項目、要約 research/k-coverage/maps/summary.md。K の再開時に新しく開く |
| KL-W1 → 一括 | Codex | ∞ の配置を Kerodon に合わせる（**完了**、11-12 に main へ 19f081dcb：root 30,355・監査 103・verify PASS）→ 各レーンの追従の支援 → 一括レーン（`stage-ii/citation-attributes.md`） | `SerrePositivity-kerodon-layout`・`refactor/kerodon-layout` | `stage-ii/bulk/kerodon-layout-w1.md` | 各レーンの改名への追従（K4）を待つ |
| ③ ∞ 供給 | Codex | G8 の四角形 → G14・G9・G10 | `SerrePositivity-inf-supply`・`math/inf-supply` | `stage-ii/inf-supply-w1.md` | KL-W1 の後 |
| ⑤a BS 実装 | Codex | BS-DOC1 → BS-W11 → BS-W12（BM18 の経路 B） | `SerrePositivity-bs-impl`・`math/bs-impl` | `bhatt-scholze/instructions/bhatt-scholze-codex-w16.md` | BS-W14 は main（A1 の二本は ⑤b の停止点 3 の後）。BS-W16（実例の欄、G12・P⁰ を除く）段 0（11-10）。11-12 夜：KL-W1 の追従の merge（未コミット）を `SerrePositivity-bs-impl` に保持したまま、a の続きは一時の worktree `SerrePositivity-bs-impl-a`・枝 `math/bs-impl-a` で進めている（追従が終わったら枝を合流して worktree を消す） |
| ⑤b BS 実装 → ③-b ∞ 供給 b | Codex | BS-D69 **完了**（停止点 3 を 11-12 に main へ、登録 a34a840f7）→ Δ・Δᵒᵖ の橋（G10、幾何学的実現） | `SerrePositivity-bs-d68`・`math/inf-supply-b`（main から） | `stage-ii/inf-supply-b/inf-supply-w2.md` | IS-W2 段 0 |
| ⑤c BS 実装 → ③-a ∞ 供給 a | Codex | BS-W17 **完了**（停止点 5 を 11-12 に main へ）→ G8 の四角形・G14・G9 | `SerrePositivity-bs-classical`・`math/inf-supply`（main から） | `stage-ii/inf-supply-w1.md` | IS-W1 段 0 |
| ⑤d M15・G12 | Codex | M15（descendability）→ G12（CAlg の presentability）。⑤a の M14 と並べるため 11-14 に新設 | `SerrePositivity-bs-m15`・`math/bs-m15` | `bhatt-scholze/instructions/bhatt-scholze-codex-m15.md` |
| ⑥ スキーム論 | Codex | BS17 Thm 4.1 (i) の経路 | `SerrePositivity-scheme`・`math/scheme` | `stage-ii/scheme-w1.md`（§6 で BS17 に絞る） | 2a′（移動）・2b・2d の一部は main、2d 進行中（11-07） |
| ① ∞ 中核 | Codex | Verdier 商（K の入口） | — | `stage-ii/consolidation/inf-core-w1.md` | **止める**（K と一緒に後回し、11-07） |

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
4d. **verify が時間のガードで止まったとき（11-17）**：全監査が成功していて sorry の閉包の段だけが残った場合は、同じ HEAD で `lake env lean scripts/refactor/audit_sorries.lean` を単独で確かめ、二つのログを報告に並べて PASS として扱う（gate は機械では non-gate になる）。昼に長い枠を取り直さない。
4c. **取り込みはまとめて（11-17）**：複数のレーンの停止点が近いときは、同じ夜に取り込んで root＋verify を一回にする（`stage-ii/build-cost-plan.md` B5）。
4b. **main の作業木の規則（11-04 決定、事故の後）**：main の作業木では Lean の編集もビルドもしない（取り込みと温めは Claude だけ）。main に直接コミットするセッション（BS の記録など）は、必ず `git commit --only <自分のファイル>` で、`git add -A`・`git commit -a` を使わない。11-04 に B4 の未コミットの削除（`Pair/Tower.lean`）が BS の記録コミット 38e6d889a に巻き込まれ、babef8b23 で復元した。
4a. **小さなビルドの規則（11-02 19:40 決定）**：変更したファイルと直接の importer までの小さなビルド（数百本以下）は、**下流ビルド・verify が走っていなければ合図なしで行ってよい**。確認は `ps -axo command= | grep "[l]ake build"` が空であることと、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること（取れなければ待つ）。下流・verify の時間帯（暦 §3）には行わない。全ビルド（下流・verify）は従来どおり暦と合図。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](archive/stage-i/dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

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
  - **昼の bulk の塊は 3〜5 分（11-13 追加）**：昼（JST 8〜23 時）の bulk は一回の塊を 3〜5 分に切る（11-12・11-13 の朝、580 秒の塊で実装が 8〜10 分待った）。夜は 30 分以内のまま（夜の待ちは最大 131 秒で問題なし）。
  - **KL-W1 は鍵の外（11-11 22 時、ユーザー判断）**：停止点 3 の報告まで、KL-W1 は鍵を使わず、他のレーンも KL-W1 を待たない（`kerodon-layout-w1.md` §15）。KL-W1 の verify は `VERIFY_JOBS=4 VERIFY_MEMORY_GB=32`。
  - **夜は鍵を二つ（11-11 20 時、ユーザー承認）**：JST 23〜8 時は同時に二つまで通す（`serre-lake-build.lock` と `serre-lake-build.lock.1`）。bulk は同時に一つまで、もう一つは coord・impl・research が順に使う。昼は一つ。古いスクリプトは一つ目しか知らないので、各レーンは main の取り込みで新しいスクリプトにする。メモリ（64 GB）のため、夜に bulk が verify を流すときは `VERIFY_JOBS=4 VERIFY_MEMORY_GB=32` に抑える。
  - **規模の上限の決め方（11-12 夜、ユーザー決定）**：各段の停止の基準は、段 0 の見込みの**上端の 2 倍**（それまでの 1.3 倍から変更。∞ 圏の coherent な比較・全関手版・指定錐の見積もりは段 0 で 2〜3 倍低く出るため）。代わりに、**各段の見込みの半分に達した時点で一度、止まらずに実測と残りの見込みを報告**する。上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）。調整役がすでに明示した上限が 2 倍より高いときは、その上限のまま。
  - **型つきの補題の一覧の数え方（11-14、全レーン共通）**：既存の構成の法則の補題（単位・余単位・自然性・係数移送・合成則・貼り合わせ）と証明の分割は**数を決めない**（型を報告に書き、200 行を超えるものは行数も）。止まって報告するのは、新しい構成・新しい定理（既存の構成の法則でないもの）、まとまりの外のもの、外枠に届くときだけ。IS-W2 §13・§14、BS-W16 §28・§29 の「3 本まで」の枠はこれに置き換える。
  - **一覧の進み具合の一行（11-14、ユーザー承認）**：各レーンは報告のたびに「一覧：済み n／全体 m（うち追加 k）」を一行で書く。全体には後から足した補題（A05a・R01 など）を含め、法則の補題・証明の分割は数えない（一覧の ID のある項目だけ）。調整役はこれで全レーンの進み具合を並べる。
  - **夜の進め方（11-12 夜、ユーザーの希望：夜は報告なしで進める）**：(1) 停止点に届いても止まらず、報告を書いてコミットし次の段へ（取り込みは朝に調整役がまとめて）。(2) 上限を超えそうなときは検証済みをコミットして報告を書き、その線の Lean は止めて決めておいた代わりの紙の作業へ。(3) 承認が要る判断（型・範囲・界面の変更）に当たったら、止まらずに報告に書いて代わりの作業へ。11-12 の夜は ③-a が段 3・4 の後に 3b-3、③-b が 3b-2 の後に 3b-4 の BE の部分、⑤a が D79 の (i)〜(iii)、⑥ が 2e → 2f、KL-W1 が B2 の停止点まで。
  - **鍵はビルドの間だけ持つ（11-11 17:10 追加）**：一回のビルド（または一回の監査）ごとに鍵を取って放す。編集・証明の検討・報告書きの間は鍵を持たない。鍵の中で「ビルドの会話セッション」（要求が来たときだけビルドする常駐プロセス）を動かす形は禁止（16:45〜 ⑤a の build-session.py が 19 分持ち、その間ほとんどビルドしていなかった）。
  - **coord の組（11-11 17:10 追加）**：調整役の取り込み・登録（main の作業木）は `coord` の組で、昼夜とも常に先頭（繰り上げより前）。worktree 名 `SerrePositivity` から推定する。
  - **持ち主の履歴（11-11 17:10 追加）**：鍵の取得・返却は `$TMPDIR/serre-lake-build.history.jsonl` に一行ずつ追記される（時刻・worktree・組・コマンド）。長い持ち方は後からこれで確かめる。モニターも読んでよい（読むだけ）。
  - **`--wait` の目安（11-11 11:10 改定）**：impl・research・bulk とも `--wait 3600`（繰り上げまで最大 15〜30 分＋前の持ち主の最大 30 分）。同じ worktree から整理券を複数出さない（待ちは一つにまとめる）。
  - **夜の空き（11-11）**：11-10 の夜は 01:08〜06:07 の 5 時間、鍵が空いた。KL-W1 は夜の束が早く終わったら次の段に続ける。止まったときは報告し、空いた鍵は impl が使ってよい（整理券の列が自動で回す）。
  - **広く再ビルドを起こす取り込みは夜（11-16 追加、モニターの指摘）**：11-16 14:27 の DAG XIII・NS の取り込みで、`Util/Citation.lean`（直接 896 本が import）の略号表に 4 行足しただけで root がほぼ全部再コンパイルになり、coord が鍵を 65 分以上持って ⑥・③-a・一括・③-b が約 1 時間止まった（load 261、swap 11.3／12.3 GB）。(1) 略号表（`Util/Citation.lean` の生成ブロック）の変更を含む取り込みは夜に回す。(2) 調整役の root ビルドと全監査は、取り込みが狭い範囲（新しいモジュールの追加だけ）なら昼でよいが、土台や多くの本が import するファイルに触るものは夜に回す。取り込みの前に `git diff --name-only` で触るファイルの importer の数を見る。(3) 略号表を import の連鎖から外す設計（キーの検査を別のモジュールか検査スクリプトへ）は台帳 BR54。
  - 列を見る：`zsh scripts/refactor/with_build_lock.sh --status`。
  - 切り替え中は、古い版で待っているプロセスが鍵が空いた瞬間に取ることがある（整理券を持たない）。それらが終われば列は整う。

## 3. 暦

全ビルド（下流・verify）の予定はまだない。各レーンの最初の束が見えたところで書く。

| 時期 | 内容 |
| --- | --- |
| 11-07 | Kerodon の確認（段 1′）。⑤a・⑤b・⑥ 開始。取り込みのたびに調整役がルートのビルド（キャッシュで数分）と監査 |
| 確認の完了後 | KL-W1（∞ の配置を Kerodon に合わせる、`stage-ii/bulk/kerodon-layout-w1.md`）。段 3 の後に下流ビルドと verify を一回（暦は段 1 の承認のときに書く）。①③は KL-W1 の取り込みの後に開始 |
| KL-W1 の取り込みの直後（調整役） | **済（11-12、7d8ae8623）**：改名表で名前と場所を引き直し、新しいファイルで宣言の行を照合した（3,905 件、未解決 187 件は宣言でない記述や別名のもので、文献の属性の一括レーンで扱う）。Lean の環境からの引き直しは属性の段で行う。対応表の宣言の場所を書き直す（11-11、ユーザー承認）：HTT・HA・Prisms の表と Kerodon・K の地図の「名前 @ パス:行」を、(1) KL-W1 の改名表で名前を置き換え、(2) Lean の `findDeclarationRanges?` で今のモジュールと行を環境から引き直す。見つからない名前は一覧にして止める（黙って消さない）。道具は `scripts/` に置き、以後の移動でも使う。直したら地図を作り直す |
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
| ∞ 数学 G2 | 閉じた。IF-G2-finish の段 1 と段 2 の途中まで main に入った（408d87457、6f35a986f）。枝 `math/g2` と worktree は削除。残りは `archive/stage-i/infinity-g2-progress.md` の末尾の節から段階 II の ∞ 供給レーンが再開する |
| BS 設計・BS 実装（段階 I） | 閉じた。段階 II では BS 実装は新しい Codex チャット、設計は調整役が持つ（入口 `bhatt-scholze/design/design-status.md` §0、drafts の扱いは計画 §1.0） |
| DG・論文の層 | 閉じた |
| 段階 II の新しいレーン（11-07）：⑤a・⑤b・⑥・Kerodon の確認が稼働。① は止めている。③ は KL-W1 の後 | 11-05 夜：計画の確定。開始文は [stage-ii/lane-starts.md](stage-ii/lane-starts.md)、指示書は `stage-ii/`（①IC-W1、③IS-W1、⑥SC-W1）。⑤は W11（§6 の追記）|

### 4.1 レーンの閉鎖と作業木の整理（2026-11-17、ユーザー決定）

動いているレーン（③-a `math/inf-supply`・⑥ `math/scheme`・③-b `refactor/organize-einfinity`）はそのまま。それ以外は閉じた。

| 閉じたレーン | 枝・作業木 | 残したもの |
| --- | --- | --- |
| ⑤a BS 実装（W16） | `math/bs-impl`・`SerrePositivity-bs-impl` を削除。タグ `archive/math-bs-impl-2026-11-17`（紙の記録 6 commit と未検証の L23 の下書き） | 報告は `bhatt-scholze/reports/report-codex-w16.md`（現在地）と `archive/reports/` |
| ⑤d M15・G12 | `math/bs-m15`・`codex/paper-coverage`（取り込み済み）・`SerrePositivity-bs-m15` を削除 | 報告は `report-codex-m15.md`。G12 の続きは D81 の後に別の指示書で |
| 一括（KL-W1 のチャット） | `codex/bulk-5inf3a`・`bulk/*`・`refactor/kerodon-layout`（取り込み済み）・`SerrePositivity-kerodon-layout`・`/private/tmp` の比較用の木を削除 | B3′・B5 の残りは再開時に新しい枝で。証拠は `evidence/bulk/` |
| 紙の作業（⑤a・⑤d の P⁰ 系、DAG/NS、本論文の対応表） | `codex/p0-*`・`research/dag13-ns-coverage`・`math/p0-p4-p6` と作業木を削除 | 成果は `research/` と `stage-ii/p0/` |
| 調査（Kerodon の確認） | `research/kerodon-review-c`・作業木を削除。`research/kerodon-review-a` はタグ `archive/research-kerodon-review-a-2026-11-17` を打って削除 | 対応表は `research/kerodon-coverage/` |
| 文書（整理・ブループリント） | `docs/reorg-stage1`・`docs/kerodon-blueprint` は main に入れて削除 | `blueprint/`、`formalization-plans/doc-reorg/` |

**規則**：作業木はレーンごとに一つ、名前はレーン（`SerrePositivity-<レーン>`）。枝は main に入れたら消す。保存比較の「前」の木（`/private/tmp`）は段の終わりに消す。取り込まない枝はタグ（`archive/<枝>-<日付>`）を打ってから消す。`/private/tmp/oe-w1-before-30ae8948f` は ③-b の OE-W1 段 1 の保存比較が終わるまで残す。

**⑧ 引用文献（11-17 新設、ユーザー決定）**：本論文が引用する文献の対応表とブループリント。最初は CLMST（指示書 `stage-ii/cited/clmst-coverage.md`、worktree `SerrePositivity-cited`、枝 `research/cited-coverage`）。紙だけでビルドなし。

**Codex のチャットの開き方（11-17、ユーザー決定）**：新しいレーンの Codex チャットは、調整役が worktree と枝を作った後、**その worktree をカレントディレクトリにして開く**（main の作業木では開かない。11-11 の `writable_roots` は効かず、全アクセスは使わない）。指示書の冒頭に worktree のパスを書き、開始文に「`pwd` が `../SerrePositivity-<レーン>` であることを確かめてから始める」を入れる。main で開いてしまったら閉じて開き直す。動いている三つのレーンは停止点まで今のまま。

**証拠（11-17）**：これからの検証の証拠は git の外 `~/serre-evidence/<レーン>/<段>/`、目録だけ `scripts/docs/evidence_manifest.py` でコミット（`evidence/README.md`）。各レーンには停止点の取り込み時に伝える。

BR55（choose の洗い出し）と ⑤a・⑤d に残っていた課題（M14 の L23 以降、G12 の D81 後の扱い）は、再開するときに新しいレーンとして開く。

## 5. 段階 I から引き継ぐ要点

- 整理の結果：DG 1,592 → 126 本、論文の層の区切りはすべて完了、∞ は中核層間の順序違反 0・直接の禁止辺 0・中核の閉包の KST とモデル圏 150 → 74（残りは M16）、F-2 で KST から移した 730 モジュールの名前空間をディレクトリに合わせた（改名表 `../scripts/refactor/targets/f-namespace-map.json`、旧名は deprecated alias で段 G の最初の区切りまで残す）。
- 主定理の閉包の sorry は 3 つ（E3、`theorem_3_1_K0`、`Section4.supportedRankK0_descent`）。
- 調整役の引き継ぎは [coordinator-handover-2026-11.md](coordinator-handover-2026-11.md)。

- **11-16 16:23 の中断の記録**：DAG XIII・NS の取り込み（cd79e9cc5）の後の root ビルドを 16:23 に止めた（ユーザー判断。略号表の変更でほぼ全体の再ビルドになり、四レーンが約 1 時間待ったため）。それまでに作り直した 12,070 本は共有のキャッシュに残る。**root ビルドは今夜（23 時以降）に coord が続きから流す**。それまで main は「取り込み済み・root 未確認」。各レーンは停止点まで main を取り込まない。
- **11-17 01:44 root の確認**：16:23 に止めた root のビルドを 23:04 から続きで流し、`Build completed successfully (33408 jobs)`（main 5982b238c 以降の内容、cd79e9cc5 の略号表の変更を含む）。main は「取り込み済み・root 確認済み」に戻った。各レーンは停止点で main を取り込んでよい（共有のキャッシュから戻るので、夜に取り込むと速い）。
