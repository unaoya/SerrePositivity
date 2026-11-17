# Codex 作業指示書 DG-W1：監査の再生成、検査専用モジュールの処置、入口の新設（D0〜D2）

作成：2026-10-30（DG の整理、管理は Claude）。宛先：Codex（∞ 基盤の IF-Wn を実施しているセッションとは**別のセッション**）。
計画：[dg-cleanup-plan.md](stage-i/dg-cleanup-plan.md) の D0・D1・D2。調査：[archive/dg-survey-2026-10-30.md](dg-survey-2026-10-30.md) §2〜§3。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) の §0（使い捨ての worktree、所有範囲、`git commit --only`、失敗の扱い）に従う。
worktree は `../SerrePositivity-dgw1`、ブランチは `infra/dg-w1`（main の最新から作る）。main の作業木では作業もビルドもしない。他のセッション（∞ 基盤、論文の層、BS）が並行して作業している。

この指示書は **2 か所で止まって報告する**（§6）。

## 1. 目的

| 候補 | 内容 |
| --- | --- |
| D0 | `scripts/audit/dg.lean` を再生成して、追跡中の全 DG モジュール（10-18 以降に増えた 113 本を含む）を監査の対象にする。README を現状に直す |
| D1 | 検査専用モジュール 650 本を処置する：`#print axioms` だけのもの 278 本は削除、`example` によるもの 363 本は `DifferentialGraded/Checks/` に集める、U12e 中断の入口 67 本は Archive へ、名前つきの定理を持つ 10 本は定理を本体へ移す |
| D2 | 入口 `SerrePositivity/DifferentialGraded.lean` を新設し、ルートの直接 import を置き換え、Stage One〜Eight を退役する。殻 `Complexes/Monoidal` と import だけの集約 7 本を解消する |

## 2. 所有範囲

変更・削除・新規作成してよいもの：
- `SerrePositivity/DifferentialGraded/` の下のすべて（ただし D1・D2 で定めた変更に限る。宣言の本文は変えない）。
- `SerrePositivity/DifferentialGraded.lean`（新規）、`SerrePositivity/Archive/DifferentialGraded/`（新規）。
- `SerrePositivity.lean`（ルート）の import 行（DG の 12 本 → `SerrePositivity.DifferentialGraded`）。
- `scripts/audit/dg.lean`（`make_area_audits.py` による再生成のみ。手編集しない）。
- DG の検査・集約を import している DG の外のファイルの **import 行だけ**（調査では `scripts/audit/dg.lean` 以外にはない見込み。あれば報告）。
- `scripts/homotopical_generalization_manifest.json`（削除したモジュールの行を消す）。

それ以外（`.lean` の宣言の本文、他の area、計画文書、`layers.json`）は変更しない。

## 3. 作業

### 3.0 D0

1. `python3 scripts/make_area_audits.py` を実行する。`scripts/audit/dg.lean` 以外に差分が出たら、それは並行セッションの変更なので `git checkout` で戻し、報告に書く。
2. `lake env lean scripts/audit/dg.lean` が終了コード 0 で通ることを確かめる（時間を記録）。
3. `DifferentialGraded/README.md` を現状に直す：Morita（U16）・Verdier（U17）・Perf は完成、入口は D2 で作る `DifferentialGraded.lean`、検査は `Checks/`、U12e-general は中断中で Archive の検査がある、など。宣言名の一覧は書かない（古くなるため）。

### 3.1 D1：検査専用モジュールの分類（止めて報告する点 1 の前）

1. **対象の判定**：次のどちらかに当たるモジュールを「検査」とする。(a) `DifferentialGraded/Checks/` の下。(b) basename が正規表現 `Checks?|Audit|Acceptance` に当たる。期待値 650 本。
2. **種類の判定**（コメントと文字列を除いた本文で）：
   - **P**（print だけ）：`#print` 以外のコマンドがなく、宣言（`theorem`・`lemma`・`def`・`instance`・`example`・`structure` など）がない。期待値 278。
   - **E**（example による検査）：`example` または `#check` を含み、名前つきの宣言がない。期待値約 363。
   - **T**（名前つきの宣言を持つ）：`theorem`・`lemma`・`def`・`instance`・`structure` のどれかがある。期待値 11（`Checks/Acceptance` と `Checks/DG{Associator…,LeftUnit…,RestrictionModel…}` 10 本）。
   - **U**（U12e 中断）：docstring に `U12e-general（中断）` を含む。期待値 67（P・E・T と重なってよい。U が優先）。
   - **K**（文書化された受入の入口、残す）：`Morita/U16Checks`・`Verdier/ChecksU17Integration`・`Checks/U12eLocal`・`Checks/StageSeven`・`Checks/StageEight` の 5 本。
3. **一覧を作る**：`scripts/refactor/targets/dg-w1-checks.json` に、モジュールごとに `{"module", "kind": "P|E|T|U|K", "action": "delete|move|archive|extract|keep", "dest"}` を書く。
   - P → delete。E → move（`DifferentialGraded/Checks/<単位>/<basename>`。`<単位>` は元のディレクトリ名。すでに Checks/ にあるものはそのまま）。U → archive（`SerrePositivity/Archive/DifferentialGraded/Checks/U12e/<basename>`）。T → extract（定理の移し先の案を `dest` に書く。`Checks/Acceptance` の反例は Checks/ に残す）。K → keep。
   - 利用者の確認：delete・archive の対象を import しているモジュールが、`scripts/audit/dg.lean` と他の検査以外にないことを確かめる。あれば一覧に書いて止める。
4. **T の 10 本の定理の移し先の案**：各定理の内容（主張を 1 行）と、それを本来置くべき本番のモジュール（Derived・Tensor など）を読んで決め、報告に書く。
5. **ここで止めて報告する（§6-1）。**

### 3.2 D1：実施（承認の後）

1. T の 10 本：承認された移し先へ、`scripts/refactor/split_module.py`（`--moved` に定理名、`--prune-imports`、`--module-doc`）で定理を移す。前後の保存検査（`decl_snapshot.lean`・`compare_snapshots.py`）を通す。移した後の検査ファイルは、残りの内容で P・E・U に再分類する。
2. P：削除（`git rm`）。
3. E：`git mv` で `Checks/<単位>/` へ。import 行を書き換える（`move_module.py` を使ってよい）。
4. U：`git mv` で `Archive/DifferentialGraded/Checks/U12e/` へ。Archive のモジュールは、どの集約にも監査にも登録しない（ビルドしない）。
5. `scripts/homotopical_generalization_manifest.json` から削除・移動したモジュールの行を直す。
6. `python3 scripts/make_area_audits.py` で `scripts/audit/dg.lean` を再生成し、`lake env lean scripts/audit/dg.lean` が通ることを確かめる。

### 3.3 D2：入口

1. `SerrePositivity/DifferentialGraded.lean` を新設する。先頭は `module`、docstring は概要／方針／規約／使われ方（リポジトリの様式）。`public import` で、DG の検査以外・Archive 以外・Stage* 以外の全モジュールを、名前順に import する（他の area の集約と同じ形）。
2. ルート `SerrePositivity.lean` の DG の 12 本の直接 import を、`public import SerrePositivity.DifferentialGraded` 1 行に置き換える。
3. Stage One〜Eight を削除する。これらを import していた検査（`Checks/{Axioms, StageSeven, StageEight, FreeHomNaturality, Colimits, ModulesAcceptance}`）は `SerrePositivity.DifferentialGraded` を import するように直す。README の build コマンドも直す。
4. 殻 `Complexes/Monoidal`（5 行）を解消する：import している DG の 6 本と DG の外の 6 本（`InfinityCategories/Derived/{DGIntegerCoefficientTensor, TensorArrowConjugation}`・`KST/LocalizingInvariants/{CochainBiprodMapComposition, CochainConnectiveLift, DGAlgebraHomology, DGEndAlgebra}`）の import を `DifferentialGraded.Complexes.HomComplex` と `HomologicalAlgebra.CochainTensorLinear` に向け直し、殻を削除する。**DG の外の 6 本は import 行だけを変える。**
5. import だけの集約 7 本（`Derived/BimoduleLocal`・`Morita/{CriterionDerived, QuasiEquivalence, U16, U16a}`・`Resolution/General`・`Verdier/U17`）は、**この指示書では残す**（D4 の統合で統合先に置き換える）。
6. `python3 scripts/refactor/layer_check.py --report` を実行し、ルートの閉包の本数の前後を記録する（DG の全本番モジュールがルートに入るので増える）。

## 4. 受入条件

1. `lake build SerrePositivity`（ルート）が成功する。`lake build SerrePositivity.DifferentialGraded` が成功する。
2. `lake env lean scripts/audit/dg.lean` が通り、`scripts/audit/dg.lean` の import の本数が「追跡中の DG モジュール − Archive − 削除」と一致する。
3. T の定理の移動について、保存検査が前後で一致する（削除した P・移した E・U については、宣言を持たないこと（P・E）または Archive に全文が残ること（U）を確かめる）。
4. DG の中に、basename が `Checks?|Audit|Acceptance` に当たるモジュールが `DifferentialGraded/Checks/` の外にないこと。
5. `scripts/refactor/verify.sh`（`VERIFY_JOBS=3`、キャッシュなし）が PASS・gate:true。
6. `git status` で、変更が §2 の所有範囲だけであること。
7. 件数の報告：削除 P、移動 E、archive U、定理の移動 T、残した K、Stage の削除、ルートの閉包の前後。

## 5. コミット

三つのコミットにする（D0、D1、D2）。それぞれ `git commit --only` で所有範囲のパスだけを指定する。メッセージの例：

```
chore(dg): regenerate the dg audit and refresh the README (DG-W1 D0)
refactor(dg): dispose of check-only modules — delete print-only, gather example checks, archive U12e (DG-W1 D1)
refactor(dg): add the DifferentialGraded aggregator and retire the Stage chain (DG-W1 D2)

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
```

## 6. 止めて報告する点

1. §3.1 の分類の後（削除・移動の前）：一覧 JSON の件数（P・E・T・U・K）、delete・archive の対象に検査以外の利用者がないことの確認、T の 10 本の定理と移し先の案。Claude が承認してから §3.2 へ。
2. §4 の受入条件をすべて確かめた後（コミットの前）：件数の報告、verify の summary、層検査の前後。Claude が承認してから §5 のコミット。

## 7. 禁止事項

- 宣言の本文・名前・名前空間の変更（T の定理の移動は分割の道具で、本文を変えずに行う）。
- 検査以外のモジュールの削除・統合（統合は D4）。
- `scripts/audit/dg.lean` の手編集、他の area の監査の変更。
- 他のセッションのファイルへの変更（DG の外は import 行だけ）。
- main の作業木での作業・ビルド。

## 8. 追記（2026-10-30、§3.1 の差異報告への回答）

Codex の予備集計（P 275・E 362・T 候補 12・U 68・K 5・未定 1、計 650）を受けて、規則を次のとおり確定する。§3.1〜§3.2・§4 はこの追記が優先する。

1. **無名の instance は T にしない。** `local instance : … := …` のような名前のない instance は検査の準備なので、T の条件は「名前つきの `theorem`・`lemma`・`def`・`structure`・名前つき `instance`」に限る。`Checks/DerivedRing` は `example` を持つので E。
2. **import だけの集約（`Morita/ScalarExtensionAcceptanceChecks`）は E 扱いで move。** 移し先は `Checks/Morita/ScalarExtensionAcceptanceChecks.lean`（集約先の 39 本と同じ単位）。import 行は移動先に合わせて書き換える。利用者は `Morita/U16Checks` と `scripts/audit/dg.lean` だけ。
3. **U は docstring の `U12e-general（中断）` を規則とし、68 本でよい。** 指示書の 67 は調査時の数え方の差。なお同じ印を持つ本番モジュールが 650 の外に 7 本ある（`Derived/{BimoduleEndpointRestriction, BimoduleSimultaneousRestriction, PairedRestrictionCoherence, PairedRestrictionIdentification}`・`Resolution/{CompositionChange, CompositionComparison, DiagonalComparison}`）。これらは本番の `Derived/DiagonalRestriction*` から使われているので D1 の対象ではない。一覧 JSON には含めず、報告に「対象外」として記す。
4. **U∩T の 10 本（`Checks/DGAssociator*`・`DGLeftUnitRestriction`・`DGRestrictionModelCalculation`）は定理を抜き出さず、ファイルごと Archive へ。** 確認した：いずれも importer が 0 で、中断した単位の検査である。Archive に全文が残るので失われない。したがって **§3.2-1 の `split_module.py` による抜き出しは行わない**（extract は `Checks/Acceptance` だけで、それは Checks/ に残す＝実質 keep）。
5. **K の扱い。** K は「削除・Archive しない」の意味で、場所は次のとおり。`Checks/U12eLocal`・`Checks/StageSeven`・`Checks/StageEight` はそのまま。`Morita/U16Checks` は `Checks/Morita/U16Checks.lean` へ move（集約 2 と同時）。**`Verdier/ChecksU17Integration` と `Verdier/ChecksOrderSquare` は動かさない**（D3 で `OrderSquare` と一緒に Asymptotic へ上げる）。この 2 本は §4-4 の例外とする。
6. **件数の期待値は目安。** 合計 650 が合い、各種類が上の規則で説明できれば、実測値（P 275・E 363・T 1（Acceptance）・U 68・K 5）で進めてよい。一覧 JSON の `kind` は P/E/T/U/K、`action` は delete/move/keep/archive（extract は使わない）。

このうえで §6-1 の報告（一覧 JSON の件数、delete・archive 対象の利用者の確認）を出す。定理の移し先の案は不要になった。

## 9. 追記（2026-10-30、§6-1 の報告への回答）

§6-1 の報告（P 272＝delete 271・keep 1、E 304＝move 38・keep 266、T 1、U 68、K 5＝move 1・keep 4、計 650。delete・archive 339 本の利用者は `dg.lean` と他の対象検査だけ）を**承認**する。§3.2（実施）と §3.3（D2）へ進んでよい。

7. **監査の前にビルドする。** `lake env lean scripts/audit/dg.lean` は import 先の olean を作らない。`Module/MaurerCartanTargetHomDifferential` の olean がないのは、そのモジュールが 10-25 のチェックポイント（importer 0）で main の `.lake` で一度もビルドされていなかっただけで、main で `lake build` すると 3.8 秒で通る（確認済み）。手順は、`dg.lean` の `import` 行のモジュールを `lake build` してから `lake env lean` を実行する：
   ```sh
   lake build $(grep '^import ' scripts/audit/dg.lean | sed 's/^import //')
   lake env lean scripts/audit/dg.lean
   ```
   D1 の後の再生成でも同じ順序で行う（削除・移動した分は import 行から消えるので、残りを再ビルドするだけ）。ビルドが失敗するモジュールがあれば、それは本物の不整合なので止めて報告する。
8. **Archive は監査・集約に入らない。** `make_area_audits.py` は `AREAS` に列挙したディレクトリしか見ないので、`SerrePositivity/Archive/` は dg.lean に入らない。D2 の `DifferentialGraded.lean` も Archive と Checks/ を import しない。`lake build` の既定は root の閉包なので、Archive の下はビルドされない（`lake build <module>` を明示したときだけ）。
9. **ルートの全体ビルドは一回だけ。** D2 の殻の削除で DG・IC・KST・EInfinity の約 2,600 本が再エラボレートされる（実測 2,576 本、1 時間超）。これは避けられないが、**繰り返さない**：いま走っている `lake build SerrePositivity` が終わった後は、途中で触ったモジュールだけを `lake build <module>` で確かめ、ルートの再ビルドは §4 の verify.sh（内部でルートと監査対象をビルドする）に任せる。dg.lean の import 先のビルド（§9-7）は、この全体ビルドの後なら再生だけで数十秒で終わる。
10. **verify.sh は `VERIFY_JOBS=3` のまま。** 最長の監査は RSS 19 GB なので、並列数は上げない。

## 10. 追記（2026-10-31、§6-2 の報告への回答：区切り 1-2 の取り込み）

§6-2 の報告（P 272・E 304・T 1・U 68・K 5、Stage 8 本と `Complexes/Monoidal` の削除、新入口 1,598 本、監査 1,910 本、verify PASS・gate:true、層検査で禁止依存の増加なし）を**承認**する。§5 のコミット（D0・D1・D2 の 3 本、`git commit --only`）を行ってよい。

ただし、その verify は基点 ebe775fc6 のもので、その後 main に論文の層の**区切り 1-2**（95c0a6d25・401fbbe6d・82644fcf1：HomologicalAlgebra の第一層の統合。DG 16 本・IC 8 本・KST 6 本・EInfinity 1 本・ルートの import 行を main 側で書き換え済み）が入った。main に入れる前に、次の順で取り込んで verify をやり直す。

11. **コミットの後に main を取り込む。** `git merge main`。衝突は `SerrePositivity.lean`（ルート）だけの見込み（main は HA の import 行、こちらは DG の 12 行 → 1 行）。両方を残す形で解決する（HA の行は main の版、DG の行は `public import SerrePositivity.DifferentialGraded` 1 行）。それ以外に衝突が出たら止めて報告。区切り 1-2 が触った DG の 16 本は D1 で削除・移動した検査と重ならないことを確認済み。
12. **新しく足したファイルの import 行を [handover §9](stage-i/handover-ct-to-infinity-2026-10-30.md) の表で照合する。** 対象は `DifferentialGraded.lean`（DG だけを import するので該当なし）、`Checks/` へ移した 39 本、`Archive/` の 68 本。旧名の `HomologicalAlgebra.*` を import していれば表の新名に替える（Archive も文面は直す）。D2 で向け直した `HomologicalAlgebra.CochainTensorLinear` は区切り 1-2 でも同名のまま。
13. **`.lake/build` を main から温める。** main の `.lake` は区切り 1-2 の後に全体ビルド済み（確認済み）。HA が変わると木のほぼ全部が再ビルドになるので、自分で作り直さず、main でビルドが走っていないことを `ps` で確かめてから
    ```sh
    rsync -a --delete ../SerrePositivity/.lake/build/ .lake/build/
    ```
    で複製する。**main では 10-31 朝の時点でまだ `lake build SerrePositivity …` が走っている**（区切り 1-2 の後の温め直し。残りは CLMST・IntersectionMultiplicity など木の上端）。`ps -axo command= | grep '[l]ake build'` に main のパスのものが出なくなってから rsync する。その上で `lake build SerrePositivity`（D2 の連鎖分だけが再ビルドされる。見込み 1 時間前後）。
15. **（10-31 追記）rsync の終了コード 23 は、消えたのが main で書き換え中の出力だけなら受け入れる。** 2 回の再試行で消えていたのは `Asymptotic/PaperBaseChange`・`Paper/Section4/PaperK0Comparison`・`Asymptotic/RankEulerAdditivity.c` の出力（木の最上端、論文の層セッションがその瞬間に作り直していたもの）だけで、Mathlib の olean は main と同一（8,602 本）であることを確認済み。main の `.lake/build` は VS Code の Lean サーバー（`lake serve`）も書き込むので完全には静まらない。**これ以上 rsync を再試行しない**（再試行のたびに書き込み途中のファイルを拾う危険がある）。そのまま `lake build SerrePositivity` に進む。欠けた出力は lake が作り直す（worktree の `--no-build` では未ビルドの起点が 22 本。その後ろに D2 の連鎖分が続く）。
    - もし `lake build` が olean の読み込み失敗（`failed to read`・`invalid header`・`corrupted` 等）で止まったら、そのモジュールの出力（`.lake/build/lib/lean/<path>.{olean,olean.private,olean.server,ilean,ir,ir.sig,trace,hash}` と `.lake/build/ir/<path>.c`）を削除して再ビルドする。2 回目以降も起きたら止めて報告。
14. **verify.sh を再実行**（`VERIFY_JOBS=3`、キャッシュなし）。PASS・gate:true なら **§6-3 で止めて報告**（merge の衝突の解決内容、§9 表で替えた import 行の数、rsync 後の再ビルド本数と時間、verify の summary）。main への取り込みは Claude が行う（fast-forward できる形にしておく：merge の後に追加のコミットは作らない）。
