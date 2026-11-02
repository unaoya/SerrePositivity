# 三つのレーンの調整（2026-10-31 新設）

概要：∞ 基盤（Codex）・DG の整理（Codex）・論文の層の整理（Claude Code）の三つの作業を、一人の調整役（Claude、長い会話）が管理するための正本。原則、レーン、ビルドの暦（順番待ち）、いまの待ち条件、引き継ぎの手順を置く。
方針：**ビルドは減らし、機械で同時に走らせない。** 下流の再ビルドを起こす変更はレーンごと・窓ごとに一束にし、全ビルドと verify は束の最後に一回。全ビルドは暦の順番で一つずつ。取り込みのたびに main の `.lake/build` を温め、他の worktree はそこから複製する。
規約：各レーンの計画と指示書が細部の正本。本書は順序・待ち条件・連絡の正本で、状態の表は調整役が更新する。日付は絶対表記。
使われ方：調整役が毎回ここを見て次の合図を出す。調整役を交代するときは §6 の手順で引き継ぐ。

## 1. レーン

| レーン | 実施 | 計画 | 指示書 | worktree／ブランチ |
| --- | --- | --- | --- | --- |
| ∞ 基盤 | Codex（∞） | [infinity-foundation-plan.md](infinity-foundation-plan.md) | [IF-W0-3 §10.12〜10.16](infinity-codex-w0-3.md)、`targets/batch-w1w2a.md` | `../SerrePositivity-ifw0-3`、`infra/if-w0-3` |
| DG の整理 | Codex（DG） | [dg-cleanup-plan.md](dg-cleanup-plan.md) | [DG-W2](dg-codex-w2.md) | `../SerrePositivity-dgw1`、`infra/dg-w2` |
| 論文の層 | Claude Code（別セッション、自分で実装） | [refactor-plan.md](refactor-plan.md) | 先方が自分で管理。伝達文 [handover-ct-to-infinity](handover-ct-to-infinity-2026-10-30.md) §8〜§10 | main で作業（凍結中は worktree） |
| BS | 人が主導の別セッション。**設計のみ再開（11-02）**：E3 を消す道筋は stage2 の A 案（[bhatt-scholze-stage2.md](bhatt-scholze/bhatt-scholze-stage2.md) §3）、最初の範囲は A0〜A1。**ビルドなし**（`lake build`・`lake env lean`・監査を行わない）。触るのは `exposition/ja/bs/`・`formalization-plans/bhatt-scholze/` だけで、Lean の骨組みは `formalization-plans/bhatt-scholze/drafts/`（`SerrePositivity/` の外。root からも監査からも届かない）。**コードを書く段階に入るときは暦（§3）に載せてから**（単体の `lake build <module>` でも他の全ビルドと重ねない）。**∞ 層の一般論の設計を含む**（11-02 追加：D(A) 値前層の層化と RΓ。drafts/ 内。∞ 側への依頼は設計書 `infinity-sheaves-design.md` の後で、置き場所と窓は調整役が判断。置き場所は 11-02 に決定：新しい層 `InfinityCategories/Sheaves/`（StablePresentable の上・ModelBridge の下）、F2 の一般論 G4・G6・G8 は `F2/Presentable/`、D(A) への適用は `Derived/`。実装は段 G、開始は W2b の後（[infinity-foundation-plan.md](infinity-foundation-plan.md) 段 G の M12）。**設計段階の到達点（11-02 夕、main 771fc9756、正本 `bhatt-scholze/design-status.md`）**：設計書 3 本（∞ 層・A0・A1）、骨組み（Sheaves・A0・A1・A4・A5・Shared・DerivedGeneral）。BS 発の一般論は計画の M12〜M15（∞ 層＝M12a〜e（S8 空間値の層を含む）、D(A) の t 構造と完備化、P⁰、descendability）と、可換環論の Lemma 10.12（`drafts/A8/Stratification.lean` → 2a の後に `CommutativeAlgebra/UniversalHomeomorphism/`・`EtaleStratification/`、独立した Codex の単位。担当は 2a の後に決める）。**コード段階の注意**：BS が原典の引用（BS17 Thm 4.1・BM18 Thm 1.7・BS17 Lemma 6.3 など）を別々の sorry 定理として `SerrePositivity/` に入れるとき、`make_area_audits.py` の sorry の許可一覧の更新が要る（BS が所有、Claude が確認）。DerivedGeneral 2 本（D(A) の t 構造と Postnikov 切り捨て、導来 (p,d) 完備化の ∞ 関手）は `InfinityCategories/Derived/` 行き、段 G・W2b 後（完備化は 2b 後）＝計画の M13。Shared の一般論 3 本（余単体的環の Alexander–Whitney cup 積、余単体的加群の Bockstein、多項式代数の de Rham 複体）の置き場所は **2b の後に `HomologicalAlgebra/Cosimplicial/`・`CommutativeAlgebra/DeRham/`（新設）**とし、論文の層に名前を予約してもらう。A0-3b・3d・A0-4 は HA/DerivedCompletion の上なので **2b の改名表（HA/DerivedCompletion を含む）を BS へ回す**。統合は BS-W1〜W9 で完了済み（10-26） | [bhatt-scholze/](bhatt-scholze/) | — | 設計のみ。論文の層の 2a・2b は BS の区切りを待たずに暦に入れてよい（`BhattScholze/`・`CLMST/` を動かしても衝突しない）。**2a・2b で `BhattScholze/` のモジュール名・宣言名が変わったら、旧→新の対応表（コミットメッセージのもの）を Claude が BS セッションへ回す** |

連絡はすべてユーザーが貼り付けで中継する。Codex への指示は指示書の追記（§番号）で出し、短い引き渡し文を添える。

## 2. ビルドの規則

1. 全ビルド（ルート・監査対象・verify・束の下流ビルド）は**機械で一つずつ**。始める前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具 `scripts/refactor/with_build_lock.sh`（DG-W2(a) で作成、infra/dg-w2）が main に入ったら必ず経由する。
2. 束の途中は触ったモジュールだけ `lake build <module>`。下流の全ビルドは束の最後に一回。
3. **Lake の成果物キャッシュを全セッションで共有する（11-01 採用、Mathlib の cache と同じ仕組みのローカル版）。** `~/.zshenv` で `LAKE_ARTIFACT_CACHE=true`・`LAKE_RESTORE_ARTIFACTS=true`・`LAKE_CACHE_DIR=~/.cache/lake` を設定済み。入力（ソースと依存）のハッシュが同じ成果物は、どの worktree で作っても他の worktree の `lake build` が再コンパイルなしで使う（`RESTORE` で `.lake/build` にも復元されるので `lake env lean` の監査もそのまま動く）。
   - 既存の `.lake/build` の中身はキャッシュに入らない。効き始めるのは、この設定の後に `lake build` で作った分から。各 Codex は新しい shell を開くか `source ~/.zshenv` してから `lake` を使う（`lake env | grep LAKE_ARTIFACT_CACHE` で確認）。
   - 古い版が溜まるので、窓の区切りで `lake cache clean`（全消去）か、ディスクを見て判断する。
   - rsync の温め（`warm_build_dir.sh`）は、キャッシュに入っていない成果物が要るときの予備に格下げ。
   - **掃除（11-02 決定）**：`lake cache clean` は空きが 150 GB を切ったときだけ、全ビルドのない時刻に、全 worktree が温まった状態で行い、直後に main で `lake build` を走らせて現行の成果物を登録し直す。定期的な掃除はしない（11-02：22 GB・331,250 本、空き 455 GB）。
4a. **小さなビルドの規則（11-02 19:40 決定）**：変更したファイルと直接の importer までの小さなビルド（数百本以下）は、**下流ビルド・verify が走っていなければ合図なしで行ってよい**。確認は `ps -axo command= | grep "[l]ake build"` が空であることと、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること（取れなければ待つ）。下流・verify の時間帯（暦 §3）には行わない。全ビルド（下流・verify）は従来どおり暦と合図。
4. verify は `VERIFY_JOBS=3`（最長の監査が RSS 19 GB）。中間の確認には `VERIFY_CACHE=1`（gate:false）を使ってよい。
5. 土台（HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・DG の Complexes/Category/Module/Functor）に触る変更は、下流ほぼ全部（約 9,000〜20,000 本、単独で 3〜8 時間）を再ビルドする。これを起こす変更は窓ごとに一束。
6. 実測（[verify-build-costs の記録](dg-cleanup-plan.md#5a-再ビルドの費用と規則2026-10-30dg-w1-の実測から)）：DG-W1 の土台 6 本の import 書き換えで 11,250 本・6 時間 57 分（3 セッション同時）、verify 1 時間 49 分。

## 3. 暦（順番待ち）

| # | 作業 | 機械 | 前提 | 状態 |
| --- | --- | --- | --- | --- |
| 1 | main の全ビルド（区切り 1-3 ＋ DG-W1 の後の温め） | 2 時間 09 分（27,854 ジョブ、新規 10,114、エラー 0） | — | **完了**（10-31 19:17〜21:26） |
| 2 | ∞ の束：main を取り込み → `.lake/build` を複製 → before snapshot（対象 1,276 本の閉包）→ R75・R79・W1・W2a を適用（停止点 1）→ 下流ビルド 約 20,000 本（6〜8 時間）→ 保存検査（停止点 2）→ verify（停止点 3） | 約 10 時間 | #1。凍結：HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・InfinityCategories・KST・EInfinity・ルート・それらの監査への他の取り込みを止める | **完了**（11-01：下流ビルド 11 round、補充 83 import、禁止閉包 177 → 166、保存比較 16,412 件一致、verify 100／100） |
| 3 | ∞ の束を main へ取り込み、main を温める | 数分（Lake キャッシュから復元） | #2 PASS | **完了**（11-01 夜、merge。温めはキャッシュからの `lake build`） |
| 4 | DG-W2(b)：main を取り込み → 複製 → D3 の move ＋ 土台でない 9 ディレクトリの統合 ＋ D5 → 内部検証（統合先だけビルド＋保存検査）→ 下流ビルド 約 7,200 本（2〜3 時間）→ verify | 約 4 時間 | #3。統合先の名前は承認済み | **完了**（11-02 昼：D3 move 33・D4 979 → 78・D5、下流 5,750 本 85 分、保存比較 PASS（個別照合 393・未説明 0）、verify 100／100） |
| 5 | DG-W2(b) を main へ取り込み、main を温める | 数分（キャッシュ） | #4 PASS | **完了**（11-02 昼、merge） |
| 6 | 論文の層の区切り 1-4（KTheory・Asymptotic・Paper の再構成、Perfect の 3 宣言を HA へ、`Asymptotic/DGVerdier/` を含める） | 先方の全体ビルド＋verify | #5 の後に**編集と直接 importer までの小さなビルド**は始めてよい（worktree で）。**全体ビルドと verify は #8a（∞ の束）が main に入った後**（11-02 改訂：順序を #8a → #6 に。∞ の束は今日 3〜5 時間、1-4 の全体ビルドは明朝） | 先方が準備完了・時刻待ち。**全ビルド可（11-02 16:45 に合図）**。**完了**（11-02 深夜：verify PASS gate:true bbba9ee39、80 分、監査 100/100。merge b23296091、衝突 0。main の温めはルート 34 秒＋監査対象 6,570 本 42 秒、コンパイル 0） |
| 7 | DG-W3：土台 5 ディレクトリの統合（48 統合先・608 元）＋残りの D5＋層の仕上げ（PerfectComplex の例外を外す、126 本の一覧） | 下流約 16,300 本、単独 4.5〜7 時間＋verify | #6（1-4 の後） | 指示書 作成済み（11-02）：[DG-W3](dg-codex-w3.md)。**事前の静的検査は完了**（11-02 夕、`ef951fa5d`：名前解決の候補 4 箇所・universe 608/608・最大 1,621 行。回答は §7）。開始は 1-4 の後に合図。**開始を合図（11-02 深夜、1-4 取り込み後）**。Perfect の 3 宣言の移動先は `HomologicalAlgebra.Complex.StrictlyPerfect`（名前は同じ）、`DG/Perfect/Basic` は Mathlib の `Module.Finite.exists_comp_eq_id_of_projective` を使い DG → PerfectComplex の辺は 0 なので例外 3 件を外せる |
| 8 | IF-W0-4（完了）→ **IF-W2a-2（R76・R77・R67、下流 11,888 本 1 回）：#5 の直後、1-4 の全体ビルドより先** | IF-W0-4 はほぼビルドなし、IF-W2a-2 は全ビルド 1 回＋verify | #3（IF-W0-4）、IF-W0-4 と DG-W2(b) の後（IF-W2a-2） | **IF-W0-4 完了・取り込み済み**（11-01 夜、bddb9b570：Foundation 103 本・違反 0、runner のメモリ予算。初回は全件未計測で 2 並列・監査 44 分、次回から実測値で並列化）。IF-W2a-2 は草案（停止点 1）を先に、束のビルドは DG-W2(b) の後。**IF-W2a-2 完了・取り込み済み**（11-02 16:40、merge 5c909058e：R76 move 9・R77 95 → 25・R67 move 3、修飾 4・宇宙の明示 2、下流 11,550 本 1 時間 55 分、保存比較 v3b 2,033 宣言一致、verify 100/100 gate:true 39 分 45 秒・RSS 最大 37.5 GB、層検査 CategoryTheory → HotA 直接辺 1 → 0。main の温め 36 秒・29,714 ジョブ） |
| 9 | 論文の層の区切り 2a・2b（CA の perfectoid 部分を BS へ、CLMST の分離、DerivedCompletion 第二層） | 先方の全ビルド 1 回ずつ | BS は設計のみ（Lean は `drafts/` 以下）なので時期は自由。他の全ビルドと重ねない。`BhattScholze/` の改名の旧→新の対応表を Claude が BS セッションへ回す | 先方。準備は 1-4 の後。**準備中（11-03）。全ビルドは 11-05（2a）・11-06（2b）の見込み** |
| 10 | **IF-W2b**（R73 FilteredExchange の三分割：A 約 369 本を正しい層へ・B 約 1,727 本を `Archive/` へ・PiCriterion 33 本を `Derived/` へ、R37 Stable への逆向き辺 127、R38 F2 への逆向き辺 139。終了時に中核の層の順序の直接違反 0） | 草案と内部検証は小さなビルドだけ。**下流の一回ビルド＋verify は DG-W3 の後（見込み 11-04）** | #7（DG-W3）の後に Claude が合図 | 指示書 作成済み（11-02 夕）：[IF-W2b](infinity-codex-w2b.md)。草案は今すぐ |

## 4. いまの待ち条件（10-31 夜）

- ∞ Codex：**IF-W2a-2 完了・取り込み済み**（11-02 16:40、5c909058e）。**IF-W2b**：11-02 深夜に停止点 1 を承認（[§12](infinity-codex-w2b.md)：模擬で直接違反 297 → 21（残りは W2c・DG-W3 の既存分）、禁止モジュール 166 → 150、下流 13,149 本 約 2 時間 11 分）→ 適用と内部検証（小さなビルド）→ 停止点 2 → **下流ビルドと verify は #10 の合図（DG-W3 の後）**。道具の回：runner の既定予算 40 GB とキャッシュ掃除の方針は ∞（IF-W2b §7）、`merge_modules.py` の循環検出と既存の試験の失敗は DG（DG-W3 §8、1-4 待ちの間）。
- DG Codex：**DG-W3 の開始を合図（11-02 深夜）**。main b23296091 から `infra/dg-w3` を切る（道具の回 6020910b6 は main に入っている）。§3.0 の再確認 → 適用 → 内部検証 → 下流約 16,300 本（4.5〜7 時間、鍵）→ verify → 停止点 3（見込み 11-03 午後〜夜）。この間、他の全ビルドなし（∞ W2b は小さな内部ビルドだけ、論文の層は 2a の準備だけ）。
- BS セッション：**2a の取り込みまで `BhattScholze/`・`CLMST/` の Lean に手を入れない**（11-03 決定。設計のみなので実害はないが明示。骨組みは `drafts/` の下だけ）。設計のみ再開（11-02、A 案 A0〜A1）。ビルドなし、Lean は `formalization-plans/bhatt-scholze/drafts/` 以下のみ、所有範囲だけを `--only` で main に直接コミット。コードを書く段階に入るときは BS が暦の空きを相談し、Claude が §3 に載せる。
- 論文の層：**1-4 完了・取り込み済み**（11-02 深夜、b23296091）。**2a・2b の準備中**（11-03 決定、cb6a157d6：worktree `refactor-2a`、2b は別 worktree で並行準備。ディレクトリ 4 本の予約済み）。2a の範囲：CA の BS 依存 6 本と perfectoid イデアル系を BS と CLMST の間の層へ、`Inputs/Perfectoidization`、Perfectoidization* 12 本を `Perfectoid/` に統合（BS のほぼ全部が再ビルド）、CLMST 146 本の整理（基礎約 35 本を CA・HA・LA へ、BS 依存約 30 本を `BhattScholze/` へ、論文側の統合、死んだ 10 本の削除、`prop247_` の改名）、Koszul・IteratedTensor・X 群の移動。**CLMST の論文側の名前（承認 11-03）**：`Prop247/` → `PerfectoidizationIsogeny/`（Descent・Rank・ConstantRank・GeneralRank・Proof・Consequences）、Thm403a → `AllModuleTorVanishing`、Cor404 → `KoszulAnnihilation`、Prop4010 → `CyclicLengthBound`、Prop4014 → `ParameterQuotientLength`、Claim4015 → `ParameterPowerLength`、`CLMST/Inputs/` は節のファイルへ吸収。各ファイルの docstring の規約欄に原典の番号を残す。**全ビルドは 2a・2b を 1 回ずつ、11-05〜06**。小さなビルドは DG-W3（11-03）・∞ W2b（11-04）の下流と verify の時間帯を避ける（Claude が合図）。取り込みのたびに改名表（`BhattScholze/`・`CLMST/`・`HomologicalAlgebra/DerivedCompletion/`、`prop247_` の宣言名を含む）を Claude 経由で BS へ。再開の合図と一緒に伝えること：(1) 2b の改名表は `BhattScholze/` だけでなく `HomologicalAlgebra/DerivedCompletion/` の分も BS セッションへ回す（Claude 経由）。(2) 2b の後に BS の共有一般論が入る新しい下位ディレクトリ `HomologicalAlgebra/Cosimplicial/`・`CommutativeAlgebra/DeRham/`・**`CommutativeAlgebra/UniversalHomeomorphism/`・`CommutativeAlgebra/EtaleStratification/`**（11-02 深夜追加：BS Lemma 10.12、有限表示有限射の有限エタール層別。古典的可換環論で BS 固有でない。Mathlib にはスキームの `UniversallyInjective` と `Spectrum/Prime/Homeomorph` はあるが環準同型の普遍同相の一般論はない（11-02 確認））の名前を予約（HA・CA の層の規則の中では第一層＝一般論の扱い）。凍結解除済み。案内 2 本の削除と README の表の更新は完了（99b57430b、Lean に変更なし）。1-4 の準備をビルドなしで進行中（群の定義・循環の確認・docstring の下書き。DGVerdier の群は DG-W2(b) の後に決める）。1-4 の取り込みとビルドは DG-W2(b)（#4・#5）の後に Claude が時刻を伝える。
- （10-31 決定・実施済み 4eb1f4d6b）main の未追跡 WIP 6 本は `SerrePositivity/Archive/WIP/` に追跡して元の場所から消した（README に由来）。∞ の束の R75 の段で `audit_kst_spectra_s3`・`d3tail` の名前一覧から旧名 4 本を外す。
- （11-01 実施）`~/.zshenv` に Lake キャッシュの 3 変数を設定（ユーザー）。使い終わった worktree `ifw0-1`・`ifw0-2` を削除（ブランチ `infra/if-w0-1`・`if-w0-2` は残してある。パッチは main に取り込み済み）。空き 344 → 447 GB。
- （10-31 決定）調整役の交代は今はしない。#5（DG-W2(b) の取り込み）の後に §6 の目安で再判断。

## 5. 逸脱の記録

- 11-01：∞ の束の停止点 3 で、監査 2 本（`audit_homotopy_limits`・`audit_infinity_f2`）の import が束で動かした定義に届かず FAIL（他の 98 本は成功）。import を直した後の再検証は `VERIFY_CACHE=1`（gate:false）で、成功済みの 98 本はキャッシュの鍵（本文と閉包の olean ハッシュ）が同一なので当たり、2 本だけ実行する。この束ではこれを合否とする（IF-W0-3 §10.36）。

- 11-02：main の温めは既定 target（ルート `SerrePositivity`）だけなので、ルートの閉包外（Spectra・Checks など）の olean は古いまま残る。main で `lake env lean` の探針を走らせると旧 olean（例：`InfinityCategories/ModelBridge/HA/Basic`）が読まれて「environment already contains」で失敗する。探針・監査は worktree で行う。1-4 の取り込み後の温めでは、verify の監査対象の一覧も含めてキャッシュから復元する（数分）。
- 10-31：main の温め（#1）の後、`scripts/audit/dg.lean` は走らせていない（Checks/ の 300 本がルートの閉包外で未ビルドのため。verify の監査対象ビルドで作られる）。∞ の束の verify で確認する。

- 10-31：DG-W1 の取り込み（194a65110）は、区切り 1-3 の後の merge で、merge 後の状態に全 verify を行っていない（領域が重ならず、重なりはルートの import 行だけ）。main の全ビルド（#1）と ∞ の束の verify（#2）で確認する。

## 6. 調整役の引き継ぎ

調整の状態は本書と各計画・指示書・メモリ（`~/.claude/projects/.../memory/`）に全部ある。交代するときは：
1. 本書 §3・§4 を最新にする（調整役）。
2. 新しい調整役は本書 → 各計画の「状態」節 → 指示書の末尾の追記（§10.x など）→ メモリの順に読む。
3. 進行中の合図（誰が何を待っているか）は §4 だけを信じる。会話の記憶は使わない。
