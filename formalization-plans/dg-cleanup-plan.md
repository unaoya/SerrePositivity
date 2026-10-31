# DifferentialGraded/ の整理計画（2026-10-30 新設）

概要：`SerrePositivity/DifferentialGraded/`（2,258 本、148,610 行。dg 圏・dg 加群・Morita・dg 商。M5 は 10-17 に完了、U12e-general は中断）を、
検査の整理・入口の整備・層の逆転の解消・ファイルの統合（1,592 → 126）によって読める形にする。∞ 基盤の整備（[infinity-foundation-plan.md](infinity-foundation-plan.md)）とは独立した作業。
方針：
- 宣言の名前・型・証明・名前空間は変えない。行うのは削除（利用者のない検査）・移動・統合（BS 方式：元のファイルを section で包んで連結し、import を書き換える）・入口の修正。
- 証明や公開 API が変わる作業（重複の統合、Quotient を Cells から導く、Mathlib への置き換え）は段 G 相当（D6・D7）に分け、窓の外で群ごとに「提案 → 承認 → 実装」。
- 管理は Claude、実作業は **∞ 側とは別の Codex セッション**（指示書 DG-Wn）。道具は ∞ 側と共用（`scripts/refactor/` の層検査・分割・保存検査・統合）。
規約：候補は D0〜D7（本書だけの番号。R 番号とは別）。各候補に対象・前提・検証・工数を書く。数値は [調査](archive/dg-survey-2026-10-30.md)（10-30）の時点。
使われ方：DG の整理の正本。指示書 DG-Wn はここから作る。∞ 側との干渉は §5 に従う。

## 1. 決定事項（ユーザー、2026-10-30）

| 決定 |
| --- |
| DG の整理は ∞ 基盤とは独立に進める。計画と管理は Claude、コードは別の Codex セッション |
| `#print axioms` だけの検査 278 本は**消す**（`scripts/audit/dg.lean` が全定数の公理を集めるので重複） |
| 主定理の経路に関わる 5 ディレクトリ（Module・Complexes・Category・Functor・Derived、119 本）も**統合する**（再ビルド 326 本。論文の層のセッションと調整して行う） |
| `Verdier/OrderSquare` 系（論文固有の Asymptotic に依存する 3〜4 本）は **Asymptotic へ上げる** |
| R79 の DG 分（旧計画の案内への docstring 参照 530 本）は **DG の統合（D5）の中で行う**。∞ 側の R79 からは外す |

## 2. 目標と完了条件

| # | 完了条件 | いま |
| --- | --- | --- |
| 1 | `scripts/audit/dg.lean` が追跡中の全モジュールを覆う | 113 本が未監査（10-18 生成のまま） |
| 2 | 検査専用モジュールが `DifferentialGraded/Checks/` に集まり、本番の木に散らばっていない。`#print axioms` だけのものはない | 650 本（Checks/ 410＋散在 240）。print だけ 278 |
| 3 | 入口が一つ（`DifferentialGraded.lean`）で、ルートがそれを import する。Stage* の鎖はない | 入口なし。ルートは DG の 12 本を直接 import。Stage 8 本 |
| 4 | DG が KST・InfinityCategories・Asymptotic・PerfectComplex を import しない（DG の外で使うのは HomologicalAlgebra・CategoryTheory・Mathlib だけ） | KST 13 辺、IC/Derived 1 辺、Asymptotic 1 辺、PerfectComplex 3 辺 |
| 5 | 検査以外のモジュールが約 126 本に統合されている | 1,592 本 |
| 6 | docstring が旧計画の案内を参照していない | 530 本が参照 |
| 7 | DG の内部の層の順序が文書化され、層検査に登録されている | 逆向き 71 本（最良の順序）。強連結成分 2 |

## 3. 候補

### D0 準備（監査の再生成、README）

- `python3 scripts/make_area_audits.py` で `scripts/audit/dg.lean` を再生成する（113 本を覆う）。他の area の差分が出たら、並行セッション由来なので戻して報告する。
- `DifferentialGraded/README.md` を現状（Morita・Perf は完成、入口は D2 で作る集約）に直す。
- 前提：なし。検証：`lake env lean scripts/audit/dg.lean` が通る。工数：1〜2h。

### D1 検査専用モジュールの処置（650 本）

| 種類 | 本数 | 処置 |
| --- | --- | --- |
| `example` で API の形を確かめるもの | 363 | 残す。散らばっているもの（Endomorphism 109・Morita 97・Verdier 20・Perfect 14）を `DifferentialGraded/Checks/<単位>/` へ移す |
| `#print axioms` だけ | 275 | **削除**（決定）。dg.lean の再生成で代替 |
| 宣言を持つもの | 1 | `Checks.Acceptance` の反例 11 個。Checks/ に残す。（名前つき定理を持つ 10 本は U12e 中断の検査で importer が 0 なので、定理を抜き出さずファイルごと Archive へ。10-30 に変更） |
| U12e 中断の検査入口 | 68 | `SerrePositivity/Archive/DifferentialGraded/Checks/U12e/` へ移す。同じ印を持つ本番モジュール 7 本（`Derived/*Restriction*`・`Resolution/*Comparison*` 等）は本番から使われているので対象外 |
| 文書化された受入の入口 | 5 | `Checks/U12eLocal`・`Checks/StageSeven`・`StageEight` はそのまま、`Morita/U16Checks` は `Checks/Morita/` へ、`Verdier/ChecksU17Integration` は動かさず D3 で Asymptotic へ（D2 で Stage の import を付け替える） |
| import だけの検査の集約 | 1 | `Morita/ScalarExtensionAcceptanceChecks` は `Checks/Morita/` へ move（E と同じ扱い） |

- 判定の規則：Checks/ の下、または basename が `Checks?`・`Audit`・`Acceptance` に当たるもの。中身は、コメントを除いた本文に `example` があるか、`#print axioms` 以外のコマンドがあるか、宣言があるか、docstring に `U12e-general（中断）` があるか、で分ける。
- 前提：D0。検証：削除・移動の後に dg.lean を再生成して通る。移した定理の保存検査。工数：8〜16h。

### D2 入口（Stage* の退役、集約の新設）

- `SerrePositivity/DifferentialGraded.lean` を新設し、検査以外・archive 以外の全モジュールを import する（他の area の集約と同じ形）。ルートの `SerrePositivity.lean` は DG の 12 本の直接 import をこれに置き換える。
- Stage One〜Eight を退役（削除）し、それらを import していた検査 6 本と README の build コマンドを `DifferentialGraded.lean` に付け替える。
- import だけの集約 7 本（`Derived/BimoduleLocal`・`Morita/{CriterionDerived, QuasiEquivalence, U16, U16a}`・`Resolution/General`・`Verdier/U17`）は、利用者（検査と DG 内部の数本）を統合先へ向け直して解消する（D4 と同時でもよい）。
- `Complexes/Monoidal`（5 行の殻。DG の外から 6 本が import）は、利用者を `Complexes.HomComplex` と `HomologicalAlgebra.CochainTensorLinear` へ向け直して解消する。
- 前提：D1。検証：ルートのビルド、dg.lean、`layer_check.py --report`（ルート閉包の本数を記録）。工数：4〜8h。

### D3 層の逆転の解消

| 対象 | 処置 |
| --- | --- |
| DG → KST/SConstruction 13 辺 | SConstruction の 26 本（調査 §6.1。群 A 17 本 → `DifferentialGraded/Functor/`（閉共役・Hom の end・Param・Enrichment）、群 B 9 本 → `DifferentialGraded/SharedFunctoriality/`（graph 双加群・加群の延長））を DG へ移す。`Functor/ModuleExtensionConjugation`・`Module/ExtensionRepresentable*` も SharedFunctoriality へ。付け替え 154 辺（SConstruction 118・IC/Derived 22・DG 13・NonConnective 1） |
| Presentation → IC/Derived/DGObjectImage | `DGObjectImage` を `DifferentialGraded/Category/ObjectImage` へ下ろす（利用者 8 本） |
| Verdier/OrderSquare → Asymptotic | `OrderSquare`・`ChecksOrderSquare`・`ChecksU17Integration`（と `U17` の該当部分）を `Asymptotic/DGVerdier/` へ上げる（決定）。論文の層のセッションに知らせる |
| Perfect → PerfectComplex 3 辺 | `finiteProjective_exists_retract`・`strictlyPerfectComplex_biprod` を HomologicalAlgebra へ下ろす（分割の道具）。`strictlyPerfectComplex`・`PerfectHomotopy` の定義の依存は、`strictlyPerfectComplex` を HomologicalAlgebra へ下ろすか、許容するかを D3 の報告で決める |

- 前提：D2。SConstruction の K-S• レーンは停止中。検証：層検査（`layers.json` に DG の規則を加える：DG が import してよいのは DG・HomologicalAlgebra・CategoryTheory・Mathlib）、保存検査、影響する利用者のビルド。工数：16〜32h。

### D4 統合（1,592 → 126）

- 対応表は [dg-consolidation-2026-10-30.json](archive/dg-consolidation-2026-10-30.json)（統合先 → 元のモジュールの連結順）。障害は [同 blockers](archive/dg-consolidation-blockers-2026-10-30.json)。
- 先に解消する障害：`Derived/AssociatorMiddle` の同名 private（`paste_associator` は同一なので共有モジュールへ、`post_paste` は private なので片方を改名）。`Quotient/DerivedComparisonGraphSquare` は Verdier へ。
- 注意：`set_option` の値が食い違う 4 統合先は section ごとに閉じて持つ。`public section` のない 2 本は非公開の section に残す。閉じていない section に `end` を補う。
- 順序：主定理の経路に関わらないディレクトリから（Morita・Endomorphism・Verdier・Quotient・Resolution・Tensor・Bimodule・Perfect・Presentation）。経路に関わる Module・Complexes・Category・Functor・Derived（119 本、再ビルド 326 本）は最後にまとめ、論文の層のセッションと時期を合わせる。
- 前提：D1〜D3、統合の道具（∞ 側の IF-W0-4 で作る `merge_modules.py`）。検証：保存検査（統合先ごとに前後の宣言の集合・型・本体・公理・属性の一致）、外からの 1,188 辺の付け替え、全体 verify。工数：40〜80h。

### D5 docstring の参照の片づけ（R79 の DG 分）

- `dg-theory-u12e-general-inventory.md`（521 本）・`dg-theory-m5-status.md`（9 本）を `git mv` で `formalization-plans/archive/` へ移し、同じコミットで docstring のパスを `formalization-plans/archive/…` に替える。相対パスの深さは保つ。
- D4 の統合と同じ窓で行う（統合で docstring を写すときに書き換えれば、再ビルドが一回で済む）。文書ごとに 1 コミット。案内の削除と README の表の更新は論文の層のコーディネータが行うので、コミットのハッシュを知らせる。
- 前提：D4 と同時。工数：1〜2h。

### D6 証明を変える統合（窓の外）

- 宣言単位の同一 5 組（調査 §5）を一本化する。
- `Quotient/*` を `Resolution/Cells/*` の特殊化として導く（33 対）。
- 群ごとに提案 → 承認 → 実装。

### D7 Mathlib との関係（窓の外）

- Complexes の薄い言い換え（`differential_squared` = `HomComplex.δ_δ` など、標本では 15 中 6）を Mathlib の名前に置き換える。
- 提出候補の整理：Ch(A) の Koszul 符号つき対称モノイダル閉構造、K-flat、semifree・perfect・dg 商、dg の Morita。[mathlib-upstream.md](mathlib-upstream.md) へ。

## 4. 指示書の単位と順序

| 指示書 | 内容 | 再ビルド | 前提 |
| --- | --- | --- | --- |
| DG-W1 | D0 → D1 → D2 | 1 回（約 9,000 本） | 完了（10-31 取り込み待ち） |
| DG-W2 | (a) 道具 `merge_modules.py`（BS の `bhatt-scholze-merge-modules.py` の一般化、保存検査との結合、試験）。ビルドなし。(b) D3 ＋ D4 の土台でない 9 ディレクトリ（Morita・Endomorphism・Verdier・Quotient・Resolution・Tensor・Bimodule・Perfect・Presentation）＋ その分の D5 を**一つの束**で：DG 内部の検証（統合先だけをビルドして保存検査）→ 外からの import の付け替え → 下流の再ビルド 1 回 → verify | 1 回 | DG-W1。`layers.json` に DG の規則を追加。道具は DG の Codex が作る（IF-W0-4 から移管、10-31） |
| DG-W3 | D4 の土台 5 ディレクトリ（Module・Complexes・Category・Functor・Derived）＋ 残りの D5 を一つの束で | 1 回（Paper まで） | DG-W2。論文の層のセッションと時期を合わせる |
| DG-G | D6・D7 | 群ごと | 窓の外 |

（10-31 改訂）以前は D3 を単独の窓（旧 DG-W2）にしていたが、D3 の移動（SConstruction 26 本 → DG）も下流 5,000 本超の再ビルドを起こすので、統合の束に含めて再ビルドを 3 回から 2 回に減らした。束の内部の検証は統合先のビルドと保存検査だけで済み（上流しか要らない）、下流の全ビルドは束の最後に一回でよい。

## 5. ∞ 基盤の整備との干渉と取り決め

- **ファイルの重なり**：DG-W1 は DG・`scripts/audit/dg.lean`・ルートの import 行だけ。∞ 側の W1（R59）もルートの import 行を変えるので、取り込みの順序はコーディネータが決め、後から取り込む側が付け替える。
- **D3 と ∞ 側**：SConstruction の 26 本の移動は、∞ 側の R64（SConstruction の Kan の道具）とは別のファイル。IC/Derived の 22 本の import の書き換えは、∞ 側の R39・R49（Derived からの移動）と同じファイルに当たりうるので、同時には行わず、先に取り込んだ側に合わせて付け替える。
- **R44 と R79**：∞ 側の R44（範囲外）の DG 部分は D3 が担う。R79 の DG 分は D5 が担う（∞ 側の R79 は HA 約 600・CategoryTheory 12・ArrowFactorization 3 に縮む）。
- **再ビルド**：D4 の最後の段（119 本）は主定理の経路の 326 本を再ビルドする。論文の層のセッションの作業の区切りに合わせ、main に入れた直後に全体 verify を通す。
- **窓**：DG の各指示書は、別の worktree で作業し、終わりに main を取り込んで verify（PASS・gate:true）を通してから main に入れる。∞ 側の W1 の取り込みと同じ日には取り込まない。

## 5a. 再ビルドの費用と規則（2026-10-30、DG-W1 の実測から）

実測：DG-W1 の D2 で殻 `Complexes/Monoidal` を消して import を書き換えた（DG の土台 6 本、IC/Derived 2 本、KST/LI 4 本）だけで、再ビルドは **約 9,000 本**（取り込み後の確認ビルドの実測：27,980 ジョブのうち新規ビルド 9,057・再生 1,150、他の 2 セッションのビルドと競合して 6 時間超。途中経過として数えた 2,576 本は過小だった）。意味が同じでも import 行が変われば olean が変わり、下流が連鎖する。DG の土台（Complexes・Category・Module・Functor）に触ると、DG 全体と IC・KST・EInfinity・Paper まで、ルート閉包 23,575 本のうち約 9,000 本が作り直される。

規則：
1. **下流の再ビルドを起こす変更は束にまとめ、窓ごとに一回にする。** D3 と D4 の土台でない 9 ディレクトリと その D5 は DG-W2 の束、D4 の土台 5 ディレクトリと残りの D5 は DG-W3 の束（§4）。束の途中では統合先だけをビルドして保存検査し、下流の全ビルドは束の最後に一回。
2. **土台でないディレクトリの統合は、依存の上から下へ**（Morita・Endomorphism・Verdier・Quotient … の順に、下流の少ないものから）。各束の費用はその下流だけ。
3. **束の途中では触ったモジュールだけを `lake build <module>` で確かめる。** ルート（`lake build SerrePositivity`）と全体 verify は指示書の最後に一回。
4. **取り込みの後、main の `.lake/build` を温める。** worktree で全体 verify を通して main に取り込んだら、main でビルドが走っていないときに worktree の `.lake/build` を main へ rsync する（同じソースなので trace が一致する）。次の worktree はその複製から始まるので、同じ再ビルドを二度払わない。
5. **全ビルドは機械で一つずつ。** 10-31 に dgw1・ifw0-3・main の全ビルドが同時に走り、load average 223（10 コア）、lean プロセス 31 本・34 GB で、どれも単独の 2〜3 倍遅くなった。全ビルドの前に `ps -axo command= | grep '[l]ake build'` で他の全ビルドがないことを確かめる。道具として `scripts/refactor/with_build_lock.sh`（`mkdir` による排他、他の全ビルドが終わるまで待つ）を IF-W0-4 または DG-W2(a) で用意する。
6. **取り込みのたびに main の `.lake/build` を温め、他の worktree はそこから複製する。** 取り込んだ worktree から main へ rsync（終了コード 23・24 で消えたのが書き換え中の出力だけなら受け入れる）。これも `scripts/refactor/warm_build_dir.sh` として用意する。
7. 統合後の大きなファイル（平均 1,200 行）は一行の変更でファイル全体が再エラボレートされる。D4 の対応表を確定するときに 1 ファイルの上限（800 行の案）を決める（§7）。

監査（verify の 85%）の時間は別の問題：最長の監査は RSS 19 GB で、64 GB の機械では 3 並列が上限。並列数を上げるには、監査ごとの RSS を記録してメモリ予算で並べる runner の改良が要る（∞ 側の IF-W0-4 に入れる。見込み 30 分 → 15 分）。

## 6. 検証

- 各指示書の終わりに `scripts/refactor/verify.sh`（全体ビルド・全監査・sorry 閉包）を通す。
- 層検査（`layer_check.py`）に DG の規則（§3 D3）と内部の層の順序（調査 §6.3 の最良の順序）を加え、違反が増えないことを確かめる。
- 保存検査（`decl_snapshot.lean`・`compare_snapshots.py`）：移動・統合の前後で公開宣言の名前・型・本体・公理・属性が一致すること。削除する検査は宣言を持たないことを確かめてから消す。
- コミットは `git commit --only`。並行セッションの未コミットの作業を巻き込まない。

## 7. 未決の点

1. D3 の `strictlyPerfectComplex`・`PerfectHomotopy`（Perfect → PerfectComplex の定義の依存）を HomologicalAlgebra へ下ろすか、許容するか。D3 の報告で決める。
2. D4 の最後の段（主定理の経路の 119 本）を入れる時期。論文の層のセッションの区切りと合わせる。
3. DG の内部の層の順序を、最良の順序（逆向き 71 本）のまま文書化するか、Derived を分割するなどして逆向きを減らすか（証明を変えない範囲で可能かは D3・D4 の後に見る）。
4. D4 の統合先 1 ファイルの上限（800 行の案）。126 本のままだと平均 1,200 行で、増分ビルドの粒度が粗くなる（§5a-5）。

## 8. 根拠

- [archive/dg-survey-2026-10-30.md](archive/dg-survey-2026-10-30.md)：調査の全文。
- [archive/dg-consolidation-2026-10-30.json](archive/dg-consolidation-2026-10-30.json)・[blockers](archive/dg-consolidation-blockers-2026-10-30.json)。
- [refactoring-infinity-r2-b.md](refactoring-infinity-r2-b.md)：R2-B の DG の分類（未登録 555 の内訳）。
- [dg-theory-m5-status.md](dg-theory-m5-status.md)・[dg-theory-u12e-general-inventory.md](dg-theory-u12e-general-inventory.md)：M5 の完了状況と U12e の目録（D5 で archive へ）。
