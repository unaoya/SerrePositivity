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
| `#print axioms` だけ | 278 | **削除**（決定）。dg.lean の再生成で代替 |
| 宣言を持つもの | 11 | 名前つきの定理（10 本の検査に 1〜3 個ずつ）と `Checks.Acceptance` の反例 11 個：定理は Derived・Tensor の本体へ移す（分割の道具で、宣言を変えずに）。反例は Checks/ に残す |
| U12e 中断の検査入口 | 67 | `SerrePositivity/Archive/DifferentialGraded/Checks/U12e/` へ移す。名前つき定理を持つ 10 本は、先に定理を本体へ |
| 文書化された受入の入口 | 5 | `Morita/U16Checks`・`Verdier/ChecksU17Integration`・`Checks/U12eLocal`・`Checks/StageSeven`・`StageEight` は残す（D2 で Stage の import を付け替える） |

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

| 指示書 | 内容 | 前提 |
| --- | --- | --- |
| DG-W1 | D0 → D1 → D2 | ∞ 側の道具（層検査・分割・保存検査）は main にある |
| DG-W2 | D3 | DG-W1。`layers.json` に DG の規則を追加 |
| DG-W3 | D4（経路に関わらない 9 ディレクトリ）＋ D5 | DG-W2、IF-W0-4 の `merge_modules.py` |
| DG-W4 | D4（Module・Complexes・Category・Functor・Derived） | DG-W3。論文の層のセッションと時期を合わせる |
| DG-G | D6・D7 | 群ごと |

## 5. ∞ 基盤の整備との干渉と取り決め

- **ファイルの重なり**：DG-W1 は DG・`scripts/audit/dg.lean`・ルートの import 行だけ。∞ 側の W1（R59）もルートの import 行を変えるので、取り込みの順序はコーディネータが決め、後から取り込む側が付け替える。
- **D3 と ∞ 側**：SConstruction の 26 本の移動は、∞ 側の R64（SConstruction の Kan の道具）とは別のファイル。IC/Derived の 22 本の import の書き換えは、∞ 側の R39・R49（Derived からの移動）と同じファイルに当たりうるので、同時には行わず、先に取り込んだ側に合わせて付け替える。
- **R44 と R79**：∞ 側の R44（範囲外）の DG 部分は D3 が担う。R79 の DG 分は D5 が担う（∞ 側の R79 は HA 約 600・CategoryTheory 12・ArrowFactorization 3 に縮む）。
- **再ビルド**：D4 の最後の段（119 本）は主定理の経路の 326 本を再ビルドする。論文の層のセッションの作業の区切りに合わせ、main に入れた直後に全体 verify を通す。
- **窓**：DG の各指示書は、別の worktree で作業し、終わりに main を取り込んで verify（PASS・gate:true）を通してから main に入れる。∞ 側の W1 の取り込みと同じ日には取り込まない。

## 6. 検証

- 各指示書の終わりに `scripts/refactor/verify.sh`（全体ビルド・全監査・sorry 閉包）を通す。
- 層検査（`layer_check.py`）に DG の規則（§3 D3）と内部の層の順序（調査 §6.3 の最良の順序）を加え、違反が増えないことを確かめる。
- 保存検査（`decl_snapshot.lean`・`compare_snapshots.py`）：移動・統合の前後で公開宣言の名前・型・本体・公理・属性が一致すること。削除する検査は宣言を持たないことを確かめてから消す。
- コミットは `git commit --only`。並行セッションの未コミットの作業を巻き込まない。

## 7. 未決の点

1. D3 の `strictlyPerfectComplex`・`PerfectHomotopy`（Perfect → PerfectComplex の定義の依存）を HomologicalAlgebra へ下ろすか、許容するか。D3 の報告で決める。
2. D4 の最後の段（主定理の経路の 119 本）を入れる時期。論文の層のセッションの区切りと合わせる。
3. DG の内部の層の順序を、最良の順序（逆向き 71 本）のまま文書化するか、Derived を分割するなどして逆向きを減らすか（証明を変えない範囲で可能かは D3・D4 の後に見る）。

## 8. 根拠

- [archive/dg-survey-2026-10-30.md](archive/dg-survey-2026-10-30.md)：調査の全文。
- [archive/dg-consolidation-2026-10-30.json](archive/dg-consolidation-2026-10-30.json)・[blockers](archive/dg-consolidation-blockers-2026-10-30.json)。
- [refactoring-infinity-r2-b.md](refactoring-infinity-r2-b.md)：R2-B の DG の分類（未登録 555 の内訳）。
- [dg-theory-m5-status.md](dg-theory-m5-status.md)・[dg-theory-u12e-general-inventory.md](dg-theory-u12e-general-inventory.md)：M5 の完了状況と U12e の目録（D5 で archive へ）。
