# Codex 作業指示書 BS-D68：Hodge–Tate 比較の多項式の場合を mod p で直接証明する（A1-3）

作成：2026-11-07（段階 II の調整役）。宛先：⑤b BS 実装の Codex（新しいチャット）。検収：調整役。
決定：D68 の改訂（11-05 夜、ユーザー）。結晶比較の黒箱を外し、使う側が要る対象ごとの命題 `HodgeTateIsoStatement` を Čech–Alexander 模型の mod p で直接証明する。∞ 圏の部品は使わない。設計は `a1-design.md` §10、骨組みは drafts（11-07 に書き直し済み）。

## 0. 材料と目標

- 目標の宣言：`hodgeTate_of_deRham_cartier`（drafts/A1/CrystallineInput.lean）。これが示せれば、`hodgeTate_iso_polynomial_Zp`（drafts/A1/HodgeTateComparison.lean）が sorry なしで閉じる。場面は (ℤ_p, (p))、多項式環 F_p[X_1, …, X_r]（有限変数）。
- 六段（a1-design §10.1 の表に宣言名）：
  1. **Lemma 5.4**（BS 著者版）：標数 p の環 k 上の多項式代数 B の Čech 脈体 B^• と Frobenius ひねり B^{•,(1)} について、余単体的可換環 N で N → N ⊗ B^• が擬同型。`frobeniusTwist_cech_quasiIso`（有限変数）と `frobeniusTwist_cech_quasiIso_infinite`（G-A1-15、無限変数。主経路に入る）。
  2. **結晶の橋**：C^•/p → D^•/p が擬同型（`crystallineBridgeModP_isCohomologyIso` など）。D^n ≅ C^n ⊗̂_φ B^n と p ねじれなし。mod p なので導来 Nakayama は要らない。
  3. **余分な δ 座標の収縮**：D_0^•/p → D^•/p が擬同型（G-A1-16、`pdInclusionModP_isCohomologyIso`）。
  4. **pd de Rham の双複体**：Tot D_0^•/p ≃ Ω^•_{F_p[X]}。列は pd の Poincaré 補題（G-A1-7）、j ≥ 1 の行は行の収縮（G-A1-14、[BdJ11, Lemma 2.15–2.17]）。cup 積との両立（`pdDeRhamCohomologyIso_cup`、a1-design §10.3）。
  5. **n 変数の Cartier 同型**（`finitePolynomialCartier`、構造体 `PolynomialCartier`）。
  6. **生成元での照合**：X ↦ X^p、β(X) ↦ [X^{p−1} dX]（`crystallineChain_generators`）。Bockstein との両立の紙の確認（a1-design §8 の 3）が残っているので、段 6 の前に紙で確かめて報告に書く。
- 前提として要る古典的な道具（drafts の Shared と既存の本体）：
  - 多変数の pd 包の自由変数の場合と D^n ≅ C^n ⊗_φ B^n（T2-1。既存の一変数の版は `BhattScholze/Delta/DividedPower/`）
  - extra degeneracy とテンソルでの保存
  - de Rham 複体の土台（drafts/Shared/DeRhamPolynomial.lean）
  - 余単体的な cup 積（drafts/Shared/CosimplicialCupProduct.lean）と Bockstein（drafts/Shared/CosimplicialBockstein.lean）
- Čech–Alexander 模型 C^• の明示形（Rem 4.19、d = p）は drafts/A0/CechAlexander.lean の `cechAlexanderAffine` の古典的な部分を使う。site に関わる部分（A0 の RΓ との比較）は対象外。

## 1. 移し方

drafts の宣言を、`drafts/README.md` の置き場所の表どおりに、本体の**新規ファイル**として移しながら sorry を証明に置き換える。本体に sorry を残さない。閉じられない宣言は drafts に残す。移し終えた drafts のファイルや宣言は消す（drafts のファイルを「移したもの」と「残るもの」に分けてよい）。

- 置き場所の目安：de Rham の土台 → `CommutativeAlgebra/DeRham/`（新設）、余単体的な cup 積・Bockstein → `HomologicalAlgebra/Cosimplicial/`、A1 の本体 → `BhattScholze/` の下（drafts/README の表に従う）。表と違う置き場所が自然なら、停止点で提案する。
- docstring は日本語の 概要／方針／規約／使われ方。論文の項目に当たる宣言は、概要の末尾に `（BS 著者版 Lemma 5.4）` の形で番号を書く（BS-DOC1 と同じ規則）。特別な場合はその範囲を書く（例：`（BS 著者版 Lemma 5.4 の、N が余単体的可換環の場合）`）。
- E3 非依存：新しいファイルとその import から `BhattScholze/Inputs/PerfectoidizationInterface` に届かないこと。監査で `sorryAx` が出たら疑う。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 紙の筋と順序：六段と前提の道具について、移す順序、置き場所、規模の見込み、Mathlib・本体にある材料（Mathlib の Kähler 微分・DividedPowers、本体の一変数 pd 包）を報告する。段 6 の Bockstein の照合を紙で確かめる | **停止点 0**：調整役が順序と置き場所を確かめる |
| 段 1 | 前提の道具（多変数 pd 包、de Rham の土台、cup 積・Bockstein、extra degeneracy） | 停止点 1 |
| 段 2 | 段 1〜3（Lemma 5.4 の有限・無限変数、結晶の橋、余分な δ 座標の収縮） | 停止点 2 |
| 段 3 | 段 4〜6 と `hodgeTate_of_deRham_cartier`・`hodgeTate_iso_polynomial_Zp` | **停止点 3**：調整役が取り込む |

- 型の停止点（停止点 0 の後の各段の最初）は、主張が drafts の型と同じなら報告して承認を待たずに証明へ進んでよい。型を変える必要があれば止める（原典どおりの定義は変えない。避けられない差は報告に書く。調整役がユーザーに相談する）。
- 証明の停止点は、「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら、報告して次の段へ進んでよい。取り込みは調整役が停止点ごとに行う。

## 3. 規則

1. worktree は main から `../SerrePositivity-bs-d68`（`LEAN_Projects.nosync/` の下）、枝 `math/bs-d68`。⑤a（BS-DOC1・BS-W11、枝 `math/bs-impl`）と並行するので、触るファイルが重ならないようにする。重なりそうなら止めて報告する（BS-DOC1 は既存の BS のファイルの docstring を書き換える）。
2. main の大きな束が入るたびに main を取り込む（調整役が知らせる。衝突は main 側を正に）。KL-W1（∞ の配置の整理）が入ったら、改名表で追従する。
3. 新しい数学は新規ファイルだけ。既存の宣言の本文・型・名前は変えない。
4. sorry・公理・新しい引用を残さない。
5. ビルドは小さなビルドだけ（`ps -axo command= | grep '[l]ake build'` と `scripts/refactor/with_build_lock.sh --wait 0`）。全ビルドは調整役の合図で。
6. F-2 の改名表 `scripts/refactor/targets/f-namespace-map.json` の旧名は使わない。
7. 報告は段ごとに：ビルド、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩、コミット。

## 4. 追記（2026-11-07、調整役）：停止点 0 の承認

**承認**：段 0 の報告（順序・置き場所・規模 8,000〜15,000 行・再利用する材料・Bockstein の紙の確認）。段 1 に進んでよい。§2 の条件付きの事前承認のとおり、段 1〜3 は「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら報告して次へ進んでよい。

1. **置き場所**：報告の案どおり（多変数 pd 包は `BhattScholze/Delta/DividedPower/` の新規ファイル、de Rham は `CommutativeAlgebra/DeRham/`、余単体的な extra degeneracy・Alexander–Whitney 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、A1 の本体は `BhattScholze/Prismatic/`）。
2. **段 4 の写像の向き**：drafts の包含の向きを、総複体から第 0 行・第 0 列への二つの射影に直す案を承認。本体に移すときに直し、drafts 側の対応する宣言も同じ向きに直してよい（drafts の編集は `A1/` の該当宣言だけ）。
3. **確認事項 1（承認）**：`HodgeTateIsoStatement` の型を保つため、A0 の affine 模型（Rem 4.19、`cechAlexanderAffine` の古典的な部分）と、A1 の η⁰・η¹・外積への延長・平方零（p = 2 の扱いを含む）を、段 1〜2 の古典的な部分として先に入れる。drafts/README の DAG では `A1/HodgeTateMap` が A2 の `polyCosimplicialAlgebra` を使っている。これが古典的な余単体的代数（∞ を使わない）なら、その定義を古典的な新規ファイルに切り出して使う。∞ の部分（CAlg 値の関手など）に触れる必要が出たら止めて報告する。
4. **確認事項 2（承認）**：共通の入口（`SerrePositivity/BhattScholze.lean`、`CommutativeAlgebra.lean`、`HomologicalAlgebra.lean` など）と監査のスクリプト（`scripts/audit_bhatt_scholze*.lean` など）には登録しない。新規モジュールは直接ビルドし、監査は新しいモジュールを import する一時の監査ファイル（コミットしない）で流す。登録は調整役が取り込みのときにまとめて行う。報告には、登録すべきモジュールの一覧を付ける。
5. 番号の docstring は BS-DOC1 と同じ形（`（BS 著者版 Lemma 5.4 の、N が余単体的可換環の場合）` など）。
