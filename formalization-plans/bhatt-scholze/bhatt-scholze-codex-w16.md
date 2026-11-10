# Codex 作業指示書 BS-W16：界面の実例 `barrattEcclesTheory` の欄を埋める（G12・P⁰ を除く）

作成：2026-11-10（段階 II の調整役）。宛先：⑤a BS 実装の Codex（同じチャット・worktree `../SerrePositivity-bs-impl`・枝 `math/bs-impl`）。検収：調整役。決定：ユーザー（11-10、「BS-W16 でいきましょう」）。設計：`calg-interface-design.md`（D71〜D73）、BS-W14 §3・§5。

## 0. 目標と範囲

BS-W14 で作った界面 `EInfinityTheory` の実例 `barrattEcclesTheory`（drafts `Shared/BarrattEcclesTheory.lean`、sorry 41）のうち、**③（∞ 層など）を待たずに今の模型の側で証明できる欄**を本体で証明する。計画では ④（E∞ の供給）の仕事だったものを、G12 と P⁰ を除いて先に行う。

| 群 | 欄 | 備考 |
| --- | --- | --- |
| **E1** D の側 | `restrictD`・`restrictD_id`・`restrictD_comp`・`restrictD_homologyIso`、`strictToD_homologyIso` | D(S) の係数の制限と、厳密な複体のホモロジーの比較（`ComplexLimits.complexOrdinaryDerivedSource_map_weak` ほか） |
| **E2** 忘却の性質 | `forget_conservative`、`forget_preservesSifted`（HA 3.2.3.1）、`coprodWith`・`coprodWith_cocone`・`coproduct_tensor`（HA 3.2.4.7、強い形）、`discrete_initial` | 模型の側の sifted 余極限（`Operad/AlgebraSiftedColimits`）と忘却のモナド性を ∞ 側へ |
| **E3** 係数（M13） | `restrict`・`baseChange`・`baseChange_adjunction`・`restrict_forget`・`baseChange_forget`・`restrict_id`・`restrict_comp`・`discrete_restrict` | |
| **E4** π₀ と厳密な入力 | `pi0`・`pi0_forget`・`pi0_discrete`・`pi0_restrict`、`ofCosimplicial`・`ofCosimplicial_forget`・`ofCosimplicial_cone`・`ofCosimplicial_restrict`、`ofCdga`・`ofCdga_forget`・`ofCdga_discrete` | Tot の E∞ 構造（G-A1-11、Berger–Fresse・McClure–Smith） |

**範囲の外**：`presentable`（G12、HA 3.2.3.5。③ の後、④）、`powerOp0`（M14、P⁰。④）、descendability（M15、D(R) の側。④）。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 各欄について、今の模型の既存の宣言（`EInfinity/BarrattEccles/`・`Operad/`・`ComplexLimits/`・`HomologicalAlgebra/` ほか）から証明する筋、足りない補題、規模の見込み。③ を待つ欄が他にもあれば挙げる | **停止点 0**：調整役が確かめる |
| 段 1 | E1 | 停止点 1 |
| 段 2 | E2 | 停止点 2 |
| 段 3 | E3 | 停止点 3 |
| 段 4 | E4。最後に、全欄のうち証明済みのものを集めた実例（`barrattEcclesTheory` を、残りの欄 `presentable`・`powerOp0` だけを引数に取る組み立て関数として本体に置く） | **停止点 4**：BS-W16 の区切り |

- 停止点 0 は承認を待つ。段 1〜4 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。
- 欄の型を変える必要があれば止める（界面の型は BS の drafts 33 本が使っている）。

## 2. 規則

- BS-W11 §6・BS-W12 §4 と同じ（新規ファイルだけ、本体に sorry を残さない、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と HA などの番号、小さなビルドだけ）。
- 置き場所：`EInfinity/BarrattEccles/Theory/`（新設）など `EInfinity/` の下。一般の ∞ 圏の補題が要るときは、KL-W1 の段 3 が main に入るまで `InfinityCategories/` には足さず、`EInfinity/` の下に置いて報告に印を付ける（取り込みの後で置き場所を決める）。
- 実例の証明の中では、今の模型のモデル構造（`BarrattEccles.modelCategory` など、構成済みのもの）を使ってよい。欄の型（界面）に `ModelCategory` の仮定を持ち込まない（D71）。満たせない `[ModelCategory SSet]` のような仮定は使わない。
- KL-W1 の段 3 が main に入ったら、調整役が配る改名表と一行のコマンドで、枝の新しいファイルの import と名前を書き換える。
- ビルドの鍵は `with_build_lock.sh --wait 1800`。報告は `report-codex-w16.md`。
