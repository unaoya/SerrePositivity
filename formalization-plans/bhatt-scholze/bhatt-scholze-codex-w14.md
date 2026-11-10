# Codex 作業指示書 BS-W14：CAlg_R の界面（D71〜D73）

作成：2026-11-10（段階 II の調整役）。宛先：⑤a BS 実装の Codex（同じチャット・worktree `../SerrePositivity-bs-impl`・枝 `math/bs-impl`）。検収：調整役。設計：`calg-interface-design.md`（D71〜D73）。

## 0. 目標

BS が E∞ 代数の ∞ 圏を、構造 `EInfinityTheory` を通してだけ使う形にそろえる。今の Barratt–Eccles の模型はその実例の一つにする。E∞ の作り方（HA の方向か今の模型か）がどちらに決まっても、BS の証明を書き直さずに済むようにする。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 1. 設計 §2 の各欄について、drafts と本体での実際の使い方（どの宣言がどの形で使うか）を集め、欄の型の案を Lean の型で書く（ビルドしない紙の段）。2. 今の模型（`EInfinity/BarrattEccles/` ほか）で、各欄が証明済み・一部・なしのどれかを、宣言名つきで確かめる（設計の「要確認」の欄を埋める）。3. 足りない欄・要らない欄の提案。4. 規模の見込み | **停止点 0**：調整役が欄の型を確かめる |
| 段 1 | 構造 `EInfinityTheory` の定義（`EInfinity/Interface/`）と、実例 `barrattEcclesTheory` の証明済みの欄（本体）、残りの欄（drafts） | 停止点 1：取り込む |
| 段 2 | BS の drafts を `(E : EInfinityTheory)` を引数に取る形へ書き換える。模型の中身に触れていた 8 本（`research/einfinity-route/README.md` §1）を欄を通す形に直す。本体の BS の宣言で CAlg_R を使うものがあれば同様に（今は docstring だけの見込み） | 停止点 2：drafts の書き換えの一覧と、模型の中身への直接の参照が 0 になったことの検査（grep の結果） |

- 停止点 0 は承認を待つ。段 1・2 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0（本体）、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。
- drafts の書き換えは、主張の数学的な内容を変えない（引数の付け替えと、模型の名前を欄の名前に替えるだけ）。内容が変わりそうなら止める。

## 2. 規則

- BS-W11 §6・BS-W12 §4 と同じ（新規ファイルだけ、本体に sorry を残さない、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と原典・HA の番号、小さなビルドだけ）。
- `EInfinity/Interface/` は Barratt–Eccles・hammock・`ModelCategory` を import しない（D71）。実例のファイルだけが模型を import する。
- KL-W1 の段 3 が近く main に入り、`InfinityCategories/` のモジュールの場所と名前空間が変わる。取り込まれたら調整役が改名表と書き換えの手順を知らせるので、枝の新しいファイルの import をその手順で直す。
- ビルドの鍵は `with_build_lock.sh --wait 1800`。
- 報告は `report-codex-w14.md`。
