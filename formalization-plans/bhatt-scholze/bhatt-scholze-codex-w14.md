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

## 3. 追記（2026-11-10、調整役）：停止点 0 の承認

**承認**：段 0 の報告（`report-codex-w14.md`、b99e67aba）。欄の型案、追加の欄（`pi0_discrete`・`pi0_restrict`・`discrete_restrict`・`ofCdga_discrete`・離散対象の認識・指定錐としての `ofCosimplicial` と余単体的 cdga の版）、中核の必須欄にしないもの（§4 の 3）、規模の見込みは報告のとおりでよい。段 1 に進んでよい。確認を求められた点は次のとおりに決める。

1. **D71 の禁止の範囲**：禁止するのは、(a) `EInfinity/Interface/` からの Barratt–Eccles・hammock・`SimplicialLocalization`・`EInfinity` の模型のモジュールの**直接の import**、(b) 模型の API（cofibrant な代表、DK の単体など）を使う宣言、(c) 欄の型に `[ModelCategory _]` などの仮定を置くこと、の三つ。Mathlib を通る推移的な依存（`derivedInfinityCategory` → … → `Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant` など）は禁止しない。主経路の規則（満たせない `ModelCategory` の仮定を置かない）とも両立する。
2. **実例の置き場所**：`EInfinity/BarrattEccles/Theory.lean`（報告の案）。設計 §3 も直す。
3. **中核と全体の分け方**：報告 §4 の 4 のとおり。本体には証明済みの欄だけの `barrattEcclesCore`（と比較）、全欄の `barrattEcclesTheory` は未供給の欄を明示の引数に取る組み立て関数として本体に置くか、完全な値を drafts に置く（どちらでもよい。証明済みの中核を全欄が揃ったものとして公開しない）。
4. **`coproduct_tensor` の強さ**：**強い形**（右因子 `y` ごとの関手の同型 `FunctorIso (coprodWith S y ≫ forget S) (forget S ≫ tensorWith (atVertex (forget S) y))`）で置く。頂点ごとの比較だけでは後から自然性を供給できないため。実例での証明は ④ の仕事でよい。
5. **G1′ の一般版**（`EInfinity/Perfectoidization/` の CAlg 版界面 `PerfectoidizationInterfaceCAlg` ほかを `E : EInfinityTheory` で述べ直したもの）：**W14 に含める**（段 2 の最後、約 180〜350 行）。A9 で E3 を置き換えるときに模型に依らないようにするため。既存の公開宣言は変えず、新しい名前で足し、既存のものはその模型への特殊化として保つ。
6. **A1 の drafts の二本**（`CrystallineInput.lean`・`HodgeTateMap.lean`、⑤b の枝に差分がある）：W14 では**触らない**。⑤b の D68 停止点 3 が main に入った後、調整役の合図で ⑤a が書き換える（それまでの段 2 の報告には「A1 の二本は後回し」と書く）。⑤b には、これらに模型の中身への新しい参照を足さないよう伝える。
7. A1 の `totEInfinity_cohomologyRing : True` の扱いは報告 §4 の 2 のとおり（全次数の cup 積は Tot の専用の条件として、要る段で足す。π₀ や P⁰ から供給した扱いにしない）。

## 4. 追記（2026-11-10、調整役）：drafts の A0・A3 は ⑤c の持ち分

新しいレーン ⑤c（BS-W15、`bhatt-scholze-codex-w15.md`）が、drafts の `A0/`（`CechAlexander.lean` を除く）と `A3/` を書き換える。W14 の段 2 では、この二つ（`A0/CechAlexander.lean` は触ってよい）を触らない。CAlg_R への参照（A0 で 3 か所、A3 で 8 か所）は ⑤c が界面を通す形に直す。段 2 の報告には「A0・A3 は ⑤c」と書く。

## 5. 追記（2026-11-10、調整役）：停止点 1 の取り込みと、欄の追加二つ

停止点 1（b84937905・38474ed61）を main に取り込んだ（8045586dd、登録 3f5bb7c85。`EInfinity.lean` の入口と段階 II の監査、3,678 宣言・標準三公理のみ）。D71 の確認：`EInfinity/Interface/` に模型のモジュールの import と `ModelCategory` は 0 件。

**承認**：報告の欄の追加二つ。どちらも drafts の主張を保つのに要る自然性で、どの実例にも求めてよい性質。

1. `restrictD_homologyIso`：係数の制限とホモロジーの比較を、関手の同型として持つ（頂点ごとの同型だけでは P⁰ の自然性 `powerOperationZero_natural` を述べられない）。
2. `strictToD_homologyIso`：厳密な複体を D(S) に送ったときのホモロジーが元の複体のホモロジーと一致する比較（Tot の `totEInfinity_forget`・`totEInfinity_map_isInvertible` に要る）。今の模型では `ComplexLimits.complexOrdinaryDerivedSource_map_weak` などから供給する。

二つとも D(S) の側の性質なので、将来 D(S) の一般論として証明が揃えば、実例の欄はそれで埋める。段 2 を再開してよい。
