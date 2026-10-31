# Codex 作業指示書 IF-W2a-2：R76（Nerve まわりを HotA へ）・R77（CategoryTheory の統合）・R67（Inputs/Homotopy）

作成：2026-11-01（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。**開始は IF-W0-4 の後**に Claude が合図する（[coordination.md](coordination.md) §3 の #8）。
計画：[infinity-foundation-plan.md](infinity-foundation-plan.md) の R76・R77・R67 の行、§6 の IF-W2a-2 行。伝達文 [handover §2・§3.2・§6.2](handover-ct-to-infinity-2026-10-30.md)。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。worktree は `../SerrePositivity-ifw0-3`、ブランチ `infra/if-w2a-2`（IF-W0-4 の取り込み後の main から）。
**一束で下流のビルドは一回**（§10.12）。CategoryTheory の基盤は HotA・EInfinity・KST・Spectra・IC の下にあるので、この束の下流はほぼ全部（約 20,000 本）。束の最後に一回だけ全ビルドし、verify を通す。

## 1. 目的

| 項目 | 内容 | 利用者（import の書き換え） |
| --- | --- | --- |
| R76 | CategoryTheory の Nerve まわり 9 本（NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices・SimplicialChainVertices・ElementsChainLifting・ElementsNaturalPrecomp）を `HomotopicalAlgebra/Simplicial/` へ移す。CategoryTheory ↔ HotA の相互依存が消える | HotA 26・EInfinity 12・KST 6・CT 4 |
| R77 | CategoryTheory の下位ディレクトリ 104 本（R75 の削除後は 87 本前後）と、∞ 側だけが使うトップ階層の 12 本を、伝達文 §3.2 の統合案（約 35 ファイル：Monoidal/Mod/*・TensorPower/*・Action・Braided、Enriched/*、Adjunction/Comparison、Quiver/*、Simplex/*、Under、Limits）に沿って **`merge_modules.py`（DG-W2(a)、main に取り込み済み）で統合**する。宣言・名前空間・証明は変えない | Spectra 89・HotA 50・EInfinity 25・KST 18 |
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
