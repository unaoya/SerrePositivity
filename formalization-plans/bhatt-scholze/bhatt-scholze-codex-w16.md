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

## 3. 追記（2026-11-10、調整役）：停止点 0 の承認

**承認**：段 0 の報告（`report-codex-w16.md`、7d3e1f04c）。各欄の経路と規模（E1 約 450〜1,100 行、E2 約 1,400〜3,600 行以上、E3 約 850〜2,100 行、E4 は Tot を除き約 400〜1,000 行、Tot の追加は約 750〜2,000 行）は報告のとおりでよい。段 1 に進んでよい。

1. **E2 の順序**：保存的・始対象を先に。`forget_preservesSifted` と `coproduct_tensor` は互いに依存させず、幾何学的実現の保存を独立に示してから。二つのどちらかが見積もりの上限（各 1,500 行程度）を超えそうなら、そこで止めて報告する（④ に回すかを調整役が決める）。
2. **Tot の群**（`ofCosimplicial_forget`・`_cone`・`_restrict`、余単体的 cdga の版）：同じ frame から native な極限錐を先に作る経路を試してよい。G10 なしで届かない欄は、③ の G10 の後に回す（停止点の報告に印を付けて残す）。③ の G10 の依頼は、この欄に要る「全関手版、射と指定錐までの比較」を含める（調整役が ③ の指示書に追記する）。
3. **段 4 の組み立て**：Tot や sifted などの欄が残る間は、G12・P⁰ だけを引数に取る形にはまだならない。供給できた欄と残りの欄を分け、残りを引数に取る組み立て関数で置いてよい（界面の型は変えない）。
4. **［一般∞］の印の補題**：KL-W1 の取り込みまで `EInfinity/` の下の専用の補助ファイルに置き、移動候補として報告する、で了解。

## 4. 追記（2026-11-10 夜、調整役）：停止点 1・2 の取り込みと、E2 の残りの順序

停止点 1（a93aeb0fe、E1 の 5 欄）と停止点 2（ebf2db804、`forget_conservative`・`discrete_initial`）を main に取り込んだ。

**判断**（§3 の 1）：`forget_preservesSifted`（見積もり約 1,600〜2,700 行）は ④ に回さず、W16 の中で**順序を後ろにする**。誰が行っても同じ規模で、BS の A2・A4 に要り、今の模型の文脈は ⑤a にあるため。次の順で進める。

1. 段 3（E3：係数の拡大と制限、M13）
2. E4 のうち Tot を除く欄（`pi0` の群、`ofCdga` の群）
3. `coprodWith`・`coprodWith_cocone`・`coproduct_tensor`（sifted の保存を仮定にしない）
4. `forget_preservesSifted`：まず幾何学的実現（Δᵒᵖ）について厳密な図式と native な余錐の橋、代数の実現と忘却後の複体の実現の比較、次に filtered と全 sifted へ。上限は約 2,700 行とし、超えそうならそこで止めて報告する。
5. Tot の群（§3 の 2 のとおり）

停止点の区切りは §1 の段に従い、1・2 の後に一度、3・4 の後に一度報告する。
