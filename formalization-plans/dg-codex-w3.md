# Codex 作業指示書 DG-W3：土台 5 ディレクトリの統合（D4 の残り）＋ D5 の残り＋ 層の仕上げ

作成：2026-11-02（DG の整理、管理は Claude）。宛先：DG の Codex。**開始は、論文の層の区切り 1-4 が main に入った後**（[coordination.md](coordination.md) §3 の #6 の後）に Claude が合図する。
計画：[dg-cleanup-plan.md](dg-cleanup-plan.md) §3 D4・D5、§4 DG-W3、§5a。草案：`infra/dg-w2` の `targets/dg-w3-merge-plan.json`（48 統合先・608 元、命名 9 件は承認済み）、`dg-w3-merge-dryrun.md`、`dg-w3-names.md`。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0、[DG-W2 §12〜§16](dg-codex-w2.md)（Lake キャッシュ、判断表、名前の隠蔽、universe）、[IF-W0-3 §10.31・§10.34〜10.37](infinity-codex-w0-3.md)（判断表、保存比較の個別照合、証明無関係なハッシュ）。
worktree は `../SerrePositivity-dgw1` をそのまま使い、1-4 の取り込み後の main から `infra/dg-w3` を切る。

この束は **DG の土台**（Module・Complexes・Category・Functor・Derived）を触るので、下流は DG の全部と IC・KST・EInfinity・Asymptotic・**Paper（主定理の経路）**まで約 16,300 本（単独 4.5〜7 時間）。全ビルドは束の最後に一回、鍵のもとで。

## 1. 目的（完了条件 5・6・7）

| 項目 | 内容 |
| --- | --- |
| D4（残り） | 土台 5 ディレクトリ 608 元 → 48 統合先（`merge_modules.py`）。`Derived/AssociatorMiddle` の同名 private は草案の `private_renames`（`paste_associator_middle`・`paste_associator_second_middle`・`post_paste_second_middle`）で回避 |
| D5（残り） | 土台の docstring の旧案内参照（`dg-theory-u12e-general-inventory.md`・`dg-theory-m5-status.md`）を `formalization-plans/archive/…` へ。`targets/rewrite_dg_docs.py --plan <この束の計画>` |
| 層の仕上げ | 1-4 で `strictlyPerfectComplex`・`PerfectHomotopy`・`strictlyPerfectComplex_biprod` が HomologicalAlgebra へ下り、`finiteProjective_exists_retract` が Mathlib に置き換わっていれば、DG の import をそれに向け直し、`layers.json` の PerfectComplex の例外 3 辺を外す。DG の内部の層の順序（統合後の 126 本）を `DifferentialGraded/README.md` に表で文書化する（完了条件 7。`layers.json` への内部 tier の登録は、違反 0 で登録できる場合だけ） |

## 2. 所有範囲

- `SerrePositivity/DifferentialGraded/` の下すべて（宣言の本文は変えない。例外は §4 の修飾・heartbeat）。
- DG の外：統合元を import しているファイルの **import 行だけ**（IC・KST・EInfinity・Asymptotic・Paper・scripts の監査）。
- `scripts/refactor/layers.json`（DG の例外の削除、内部 tier の登録）、`scripts/refactor/targets/dg-w3-*`、`DifferentialGraded/README.md`。
- 道具：`merge_modules.py` は自分のものなので必要なら直してよい（試験つき、別コミット）。∞ の道具（`decl_snapshot.lean`・`compare_snapshots.py`・`validate_targets.py`・`layer_check.py`・verify）は変更しない。必要が出たら止めて報告。

## 3. 手順

### 3.0 事前（ビルドなし、止めて報告する点 1）

1. 1-4 後の main を取り込み、草案（48 統合先）を `--check --max-lines 1700` で再確認する。1-4 で DG の import 先が変わっていれば（Perfect の 3 宣言など）草案と `downstream_imports` を更新する。
2. **宣言単位の到達性**（DG-W2 §13-1）：失われる参照 0、DG に残る KST・IC・Asymptotic・PerfectComplex の宣言依存の一覧（Perfect の 3 辺が消えているはず）。
3. **名前の隠蔽の静的洗い出し**（DG-W2 §14 の型）：各統合先について、統合先の import の和で新たに閉包に入る宣言の**短い名前**と、元ファイルの中で `namespace`／`open` の下で無修飾に使われている識別子の衝突候補を列挙する（`lean_source.py` の識別子抽出と snapshot の宣言名で近似。偽陽性は許す）。候補は内部ビルドで確かめる。
4. **`universe`**：`merge_modules.py` の修正（7e1fb1dea）が入っていることを試験で確かめる。
5. 下流の逆閉包と時間の見積もりを更新して報告（短くてよい。Claude の承認は不要。止めるのは 2 で失われる参照が出たとき）。

### 3.1 適用と内部検証

1. `with_build_lock.sh` で鍵 → Lake キャッシュから復元（`lake build` の再生。`warm_build_dir.sh` は予備）→ before snapshot（proof-irrelevant、土台 5 ディレクトリ＋利用元）。
2. D4（48）→ D5（docstring）を適用。コミットは「D4 土台」「D5 土台」。
3. 内部ビルド（統合先 48）。失敗は判断表（DG-W2 §13-2・§14）：禁止辺にならない直接 import の補充／名前の隠蔽は従来の解決先へ完全修飾（保存比較で同一を証明、別コミット「修飾」）／heartbeat の上限（別コミット、D8 に記録）。
4. after snapshot → 保存比較。機械比較の残りは IF-W0-3 §10.34〜10.37 の規則で個別に照合（親への束ね、生成名、Prop インスタンス、pp 比較）。**未説明が 1 件でもあれば止めて報告**（止めて報告する点 2）。

### 3.2 外からの付け替えと下流

1. 外からの import の付け替え（統合元 → 統合先）と監査のモジュール一覧の更新（DG-W2 の 3ec3cae16 と同じ道具）。本体は import 以外が不変であることを行単位で確かめる。
2. 下流ビルド（約 16,300 本）。round の記録、判断表、条件 5 は失敗モジュール数で（IF-W0-3 §10.33）。Paper の 11 本も含む。
3. `layers.json`：PerfectComplex の例外 3 辺を外す（1-4 で解消していれば）。DG の規則で直接違反 0 を確認。内部 tier の登録は §1 の条件で。`layer_check.py --report` の前後（W1／W2a／W2b と DG）で増加 0。
4. `DifferentialGraded/README.md` に、統合後の 126 本の一覧（ディレクトリ・役割・import の向き）を表で書く。
5. verify（`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40`、鍵のもと、他の全ビルドなし）→ PASS・gate:true → **止めて報告する点 3**（最終）：round の表、補充・修飾・heartbeat の件数、保存比較の結果、層検査の前後、コミット一覧、126 本の一覧へのリンク。

## 4. 許す変更（宣言の意味を変えないもの）

- 名前の隠蔽の完全修飾（保存比較で型・本体のハッシュ一致を証明）。
- `set_option maxHeartbeats` の section 内での引き上げ（D8 の候補として記録）。
- 統合先の import の和、見出し、section の包み、`universe` 行の位置（道具が行う）。

## 5. 止めて報告する条件

1. 事前検査で失われる参照がある。
2. 保存比較に未説明の不一致がある。
3. 補充の import が禁止辺になる（DG → KST・IC・Asymptotic・PerfectComplex）。
4. 宣言の本文・型・名前を変えないと直らない。
5. 補充だけの round で失敗モジュール数が減らない。
6. 1-4 の後の main で Perfect の 3 宣言の移動先が分からない（論文の層の対応表を Claude が取り寄せる）。

## 6. 禁止事項

- 宣言の本文・名前・名前空間の変更（§4 以外）。D6・D7・D8（証明を変える整理）。
- ∞ の道具の変更。鍵なしの全ビルド。main の作業木での作業・ビルド。

## 7. 追記（2026-11-02 夕、静的事前調査 `ef951fa5d` への回答）

**受領・承認**：候補 4 箇所（`InfinityCategories/DGNerve/HomotopyCategory.lean` の 34・98・104・109 行）、universe 608/608 で順序保持、`--check` 48 統合先・608 元・最大 1,621 行・超過 0。報告の判断（今は何も変えず、before/after の保存比較で重点照合する）をそのまま採る。開始の合図は変わらず **1-4 が main に入った後**（見込み 11-03 午後）。それまでビルドなし。

1. **`HomotopyCategory` の 4 箇所の見込みと扱い**：Mathlib の `HomotopyCategory V c` は `V` に `Category` と `Preadditive` のインスタンスを要るので、`HomotopyCategory A D`（`A` は `CommRing` の型）では Mathlib 側の候補は elaboration に失敗し、多重定義の解決は従来どおり `DifferentialGraded.HomotopyCategory` に落ちる見込み。したがって失敗も解決先の変化も出ないはずだが、確認は保存比較の型ハッシュ（4 宣言と、それを使う `DGNerve` の下流）で行う。失敗か不一致が出たら `DifferentialGraded.HomotopyCategory` へ完全修飾する。このファイルは DG の外だが、**この 4 箇所に限って §2 の所有範囲の例外として修飾を許す**（別コミット「修飾」、保存比較で同一を証明）。∞ の束 IF-W2a-2 はこのファイルに触れていない（Claude が 11-02 に確認）。
2. **`Complexes.SphereHom` が `Complexes.Perturbation` の import 和に Mathlib の経路を持ち込む件**：統合先の import 和はそのままでよい（元の再分割や import の削減は W3 の範囲外）。同型の事例（統合先の import 和が外側の利用元に新しい短名を届ける）が内部ビルドや下流で現れたら、1 と同じ規則で扱う。
3. **構造体フィールドの 3 出現**（`Presentation/Category.lean` の `differential`）：除外でよい。
4. **universe の 4 本**（`Category.IdempotentTelescope`・`Category.EquivalenceComparison`・`Derived.AssociatorMiddleRestrictionResolved`・`Derived.AssociatorSecondMiddleRestrictionResolved`）：before/after の型ハッシュで回帰確認の対象。宇宙引数の順序差を表示だけの差として処理しない（報告のとおり）。
5. **草案の現在値**（48・608・1,621 行、private_renames 3 箇所）を正とし、旧 `dg-w3-merge-dryrun.md` の値（611 元・1,601 行）は本報告で置き換える。
6. **main の取り込み後の再確認**：∞ の束（IF-W2a-2：CategoryTheory の統合 25 群と Nerve まわりの移動）が今夜 main に入り、翌日 1-4 が入る。`infra/dg-w3` を切ったあと §3.0-1 の `--check` と、**閉包の差分だけ**（新たに届く短名の候補が増えないか）を再確認する。静的検査の全再実行は要らない。
