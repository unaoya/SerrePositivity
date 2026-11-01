# Codex 作業指示書 IF-W2a-2：R76（Nerve まわりを HotA へ）・R77（CategoryTheory の統合）・R67（Inputs/Homotopy）

作成：2026-11-01（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。**開始は IF-W0-4 の後**に Claude が合図する（[coordination.md](coordination.md) §3 の #8）。
計画：[infinity-foundation-plan.md](infinity-foundation-plan.md) の R76・R77・R67 の行、§6 の IF-W2a-2 行。伝達文 [handover §2・§3.2・§6.2](handover-ct-to-infinity-2026-10-30.md)。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。worktree は `../SerrePositivity-ifw0-3`、ブランチ `infra/if-w2a-2`（IF-W0-4 の取り込み後の main から）。
**一束で下流のビルドは一回**（§10.12）。CategoryTheory の基盤は HotA・EInfinity・KST・Spectra・IC の下にあるので、この束の下流はほぼ全部（約 20,000 本）。束の最後に一回だけ全ビルドし、verify を通す。

## 1. 目的

| 項目 | 内容 | 利用者（import の書き換え） |
| --- | --- | --- |
| R76 | CategoryTheory の Nerve まわり 9 本（NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices・SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp）を `HomotopicalAlgebra/Simplicial/` へ移す。CategoryTheory ↔ HotA の相互依存が消える | HotA 26・EInfinity 12・KST 6・CT 4 |
| R77 | CategoryTheory の下位ディレクトリ 104 本（R75 の削除後は 87 本前後）と、∞ 側だけが使うトップ階層の 12 本を、伝達文 §3.2 の統合案（約 35 ファイル：Monoidal/Mod/*・TensorPower/*・Action・Braided、Enriched/*、Adjunction/Comparison、Quiver/*、Simplex/*、Under、Limits）に沿って **`merge_modules.py`（DG-W2(a) の道具。11-01 夜に main へ cherry-pick 済み：80a44df79・aee0d2b12）で統合**する。宣言・名前空間・証明は変えない | Spectra 89・HotA 50・EInfinity 25・KST 18 |
| R67 | `Inputs/Homotopy/`（KanQuillen＝引用の sorry、ResolutionHom、SimplicialLevel）を `InfinityCategories/ModelBridge/Inputs/` へ移し、`make_area_audits.py` の sorry の許可リストと scripts の check 3 本の import を直す。GroupTheory/Coxeter は IF-W0-4 で登録済みなので動かさない | check 3 本 |

## 2. 手順

1. **草案（ビルドなし）**：`targets/w2a-2.json` に R76 の move 9 件、R77 の merge（伝達文 §3.2 の表をそのまま計画に。統合先の名前は表の名前。1,700 行超が出たら報告）、R67 の move 3 件を書く。`merge_modules.py --check --max-lines 1700 --report targets/w2a-2-dryrun.md`、`validate_targets.py`（move の分）。外からの import 辺の内訳と、下流の逆閉包の本数・時間の見積もり。**止めて報告する点 1**。
2. **適用**：承認後、他の全ビルドがないことを確かめ（`with_build_lock.sh`）、main から `.lake/build` を複製（`warm_build_dir.sh`）→ before snapshot（ハッシュ版、§10.18）→ R76 → R77 → R67 の順に適用 → 内部の検証（統合先と移動先だけビルド＋保存検査）→ 外からの import の付け替え → 下流の一回ビルド → 保存検査 → **止めて報告する点 2**。
3. `layer_check.py --report`：基盤の違反（IF-W0-4 で数えた分）が R76 で消えること、CategoryTheory と HotA の相互依存が 0 であること。
4. verify（`VERIFY_JOBS` と予算は IF-W0-4 の既定）→ PASS・gate:true → **止めて報告する点 3**。
5. コミットは R76・R77・R67 で 3 本（R77 は統合先ごとではなく 1 本）。

## 3. 注意

- R77 の統合で Mathlib と重なる宣言の置き換え（伝達文 §3.3、R78）は**行わない**（窓の外、群ごとに提案 → 承認）。
- `Presentation/` は R75 で削除済み。伝達文 §3.2 の表に Presentation 由来の行があれば外す。
- 統合先の module docstring は概要／方針／規約／使われ方の様式で、元の docstring の本文は見出しの下に残す（BS 方式）。
- 束の途中では統合先・移動先だけをビルドする。全ビルドは最後の一回。

## 4. 禁止事項

- 宣言の本文・名前・名前空間の変更。R78 の置き換え。
- 論文の層の側の CategoryTheory（Abelian・Karoubi・TStructure・Triangulated など）への変更。
- 鍵なしの全ビルド。

## 5. 追記（2026-11-01 夜、草案前の不一致への回答）

1. `merge_modules.py`・`with_build_lock.sh`・`warm_build_dir.sh` と試験は DG-W2(a) の commit を main に cherry-pick した（80a44df79・aee0d2b12、新規ファイルのみ）。`infra/if-w2a-2` に main を取り込んでから使う。DG-W2(b) が後で main に merge されるとき同じ内容なので衝突しない。
2. R76 の一覧の `SimplicialChainVertices` は書き誤りで、実在名は `SimplexChainVertices`（§1 を訂正）。

このうえで §2-1 の草案を作り、停止点 1 で報告する。

## 6. 追記（2026-11-02、停止点 1 の回答：循環の解消と保留 2 件）

**承認**：草案（R76 move 9、R77 merge 26 群・95 本、R67 move 3、生成行数最大 926、move の validator PASS、下流 11,888 本・3.3〜5.0 時間）。

1. **循環 `Mod.InternalHom ↔ Mod.Closed`**：`ModuleClosed` が `ModuleInternalHomAction` と `ModuleInternalHomFunctor` の間に挟まるので、伝達文 §3.2 の表の `Monoidal/Mod/Closed`（元 `ModuleClosed` 1 本）を**廃し、`Monoidal/Mod/InternalHom` に含める**。連結順は依存どおり `ModuleInternalHom → ModuleInternalHomAction → ModuleClosed → ModuleInternalHomFunctor`。統合先は 26 → 25 群。行数は 1,700 以下のはず（超えたら報告）。
2. **`FunctorTransport`**：どの統合先にも入れず**単独のまま**（R78 で Mathlib の `Functor.copyObj` に置き換えて消す予定のファイル）。Foundation の登録（トップ階層 12 本）はそのまま。
3. **新しい統合先の Foundation 登録**：`CategoryTheory.Adjunction.Comparison` など、既存の接頭辞に入らない新しい統合先は、この束の中で `layers.json` の Foundation に加える（接頭辞 `SerrePositivity.CategoryTheory.Adjunction` を追加。他に新しい接頭辞ができればそれも）。層検査で Foundation の違反が増えないことを確かめる。
4. **`merge_modules.py --check` が循環を検出しない件**：今は道具を変えない（DG の束が同じ道具を使用中）。束の静的検査では `layer_check.py` のグラフで循環を確かめる（今回と同じ手順）。循環検出の追加は、両方の束が main に入った後の道具の回に回す。

**適用の時期**：下流 11,888 本の束は、**DG-W2(b) が main に入ってから**（coordination.md #5 の後）Claude が合図する。それまでに 1〜3 を草案に反映し、`--check`・validator・循環の再確認を済ませて止める（停止点 1′、報告は短くてよい）。
