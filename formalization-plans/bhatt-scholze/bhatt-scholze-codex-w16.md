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

## 5. 追記（2026-11-11 夕、調整役）：停止点 3 の取り込み

停止点 3（22438e10b、E3 の八欄と Tot 以外の E4、無条件の `barrattEcclesBaseChange_forget`）を main に取り込んだ。新規 116 モジュールを EInfinity の入口と段階 II の監査に登録した。残りは §4 の順（E2 の余積・テンソルの比較 → sifted の保存 → Tot の群、G10 待ち）と段 4 の実例の組み立て。［一般∞］の印の 5 本（`LocalizedAdjunctionWhiskering`・`LocalizedAdjunctionTriangles`・`LocalizedAdjunctionAssembly`・`LocalizedNerveNatTrans`・`OrdinaryHoComposition`）の置き場所は、KL-W1 の取り込みの後に調整役が決める。

## 6. 追記（2026-11-11 夜、調整役）：`coproduct_tensor` の上限を 2,700 行に上げる

§12.2 の中間停止（ae91ee0fe、新しい見込み 1,750〜2,700 行）を受けて。

- **判断**：`coproduct_tensor` は ④ に回さず、W16 の中で続ける。上限を **約 2,700 行**にする（sifted と同じ、§4 の 4）。理由も sifted と同じで、誰が行っても同じ模型・同じ規模になり、④ はまだ開いていない。報告の内訳（Hopf テンソル代数と包含、二色の自由比較、セル対への移送、全関手版への降下）でよい。
- **native な余積錐（`coprodWith_cocone`）**：見込みに含まれていないので、`coproduct_tensor` の最初の区切りで規模を見積もって報告する。`[ModelCategory SSet]` を要求する版を使わない、という §12.1 の方針でよい。
- **停止の条件**：合計（`coproduct_tensor` と native な錐）が 3,500 行を超えそうなら止める。二色の自由比較で、等変な鎖ホモトピー同値が既存の API から組めないと分かったときも止める。
- **順序**：§4 のとおり（`coproduct_tensor` → sifted → Tot）。今回の三本（`CoproductModel`・`CAlgCoproductFunctor`・`RightFrameCoproduct`）は、次の停止点でまとめて登録する。

## 7. 追記（2026-11-11 夜、調整役）：合計の上限を 4,500 行に上げる

§14 の中間停止（db8aae7da、合計の見込み 3,100〜4,000 行）を受けて。

- **判断**：止めずに続ける。`coproduct_tensor` と native な余積錐の**合計の上限を約 4,500 行**にする。超過の理由は「Hopf テンソル代数と包含」の実測（1,119 行、見込み 400〜650 行）で、残りの部分の見込みは §12.2 のまま、という報告の内訳でよい。BS の A2・A7 が使う欄なので、④ に回しても規模は変わらない。
- **新しい停止条件**：(1) 合計が 4,500 行を超えそうなとき。(2) 実際のセル対への移送が 1,200 行を超えそうなとき。(3) 二色の係数複体の射影解像度・増大・比較射の照合が、既存の API から組めないと分かったとき。
- **取り込み**：今回までの 21 本（§14.4）を途中の取り込みとして main に入れた。次の停止点では、その後の分だけを登録する。
- 順序は §4 のまま（`coproduct_tensor` → sifted → Tot）。

## 8. 追記（2026-11-11 夜、調整役）：セル対 2,000 行・合計 7,000 行（ユーザー承認）

§19 の中間停止（b1299c7c0、セル対の見込み 1,300〜1,800 行）を受けて。§15〜§19 の 29 本を途中の取り込みとして main に入れた。

- **判断**：続ける。上限を、**実際のセル対への移送 約 2,000 行**、**`coproduct_tensor` と native な余積錐の合計 約 7,000 行**（取り込み済みの分を含む全実測で数える）に上げる。二色の係数の等変なホモトピー同値は済んでいて、残りは §19.3 の内訳の組み立て。
- **必ず止める点**：セル対への移送が終わった時点で、§19.3 の各行の見込みと実測の差を報告して止める（規模の理由がなくても止める）。
- **停止条件**：(1) セル対が 2,000 行を超えそうなとき。(2) 合計が 7,000 行を超えそうなとき。(3) §19.2 の不足（入力重みの真の低下、係数微分を残す層の商）が既存の定義を変えずに作れないと分かったとき。
- 順序は §19.3 の末尾のとおり（色付き Schur 分解と自由代数の比較の残り → セル対）。

## 9. 追記（2026-11-11 夜、調整役）：上限を上げずに経路を見直す（ユーザー承認）

§20 の中間停止（bb6179355、合計の見込み 7,100〜8,300 行）を受けて。見込みは夕方から 1,750〜2,700 → 3,100〜4,000 → 5,700〜6,500 → 7,100〜8,300 行と、止まるたびに前の表の外の部分が見つかっている。§20 の六本は途中の取り込みとして main に入れた。

- **判断**：上限は上げない。`coproduct_tensor` の Lean の実装はここで止め、経路を昼に見直す。
- **今夜の作業（Lean は書かない、紙だけ）**：
  1. 経路の比較：(A) 今の経路（自由代数の比較をセル対へ移す）と、(B)「自由代数の場合だけ比較を示し、一般の代数へは sifted 余極限（`forget_preservesSifted` と自由代数による単体的な分解の幾何学的実現）で延ばす」経路。それぞれの不足する主張・再利用・規模の見込み。(B) で §19.3 のセル対の移送が不要になるか、代わりに何が要るか。
  2. sifted の保存の段 0：既存の宣言（`Operad/AlgebraSiftedColimits` ほか）からの筋、不足、規模。
  3. A2（`BaseChangeAndTensor`）・A7 の drafts が `coprodWith`・`coprodWith_cocone`・`coproduct_tensor` をどの形で使うかの洗い出し。強い形（関手全体の自然同型）が要る箇所と、対象ごとの同型や特別な入力（多項式代数・離散な代数など）で足りる箇所を分ける。
- 報告は `report-codex-w16.md` の新しい節。明日の昼に、調整役とユーザーで経路を決める。

## 10. 追記（2026-11-11 夜、調整役）：経路によらない共通部分を今夜進める（ユーザー承認）

§21 の紙の検討（b79fd6aee）を受けて。経路 A／B と sifted の分担は 11-12 の昼に決める（design-status の「未決」）。その間、どちらの経路でも要る部分を進める。

1. 共通部分（§21.2）：(a) 自由代数の比較の残り（§20.2 の五行、任意の cofibrant な入力の複体まで、上限 約 1,550 行、終わったら報告して止まらずに b へ）、(b) native な二項の余積錐 `coprodWith_cocone`（上限 約 670 行、終わったら報告）、(c) 比較が `coprodWith_cocone` の二脚をテンソルの標準射へ送る照合補題（界面の型は変えない）。
2. 段 4 の組み立て関数：証明済みの欄を集め、残りの欄（`coproduct_tensor`・sifted・Tot の群・`presentable`・`powerOp0`）を引数に取る `barrattEcclesTheory` の組み立て（§3 の 3）。
- 入れないもの：セル対（A）、bar の実現（B）、sifted の保存。上限を超えそうなときは報告して止める。

## 11. 追記（2026-11-12 朝、調整役）：a の上限は昼に決める、b・c・組み立てを先に

§22 の停止（ef2169d87、a の見込み 1,742〜2,112 行、上限 1,550 行）を受けて。a の上限は上げず、11-12 の昼の E2 の経路の判断と一緒に決める。それまで a に依らない b（native な余積錐、上限 約 670 行）→ c（既存の厳密な比較 `barrattEcclesCoproductTensorNat` の脚の照合）→ 段 4 の組み立て関数を進める。§22 の五本は、KL-W1 の取り込みの後に改名に追従してから取り込む。

## 12. 追記（2026-11-12、調整役）：E2 の経路の決定（ユーザー決定、`stage-ii/stage-ii-second-half.md`）

1. **`coproduct_tensor` は経路 B**（自由代数の比較を bar 構成と幾何学的実現で延ばす。ユーザー決定 11-12 昼：一般論で処理する）。セル対（経路 A）は行わない。橋（③-b の 3b-1・3b-3・3b-4「U が実現を保つ」）を待たない部分を先に進める：§11 の b・c・組み立て関数 → a（自由比較の残り、上限 約 2,100 行、どちらの経路でも要る）→ B の厳密な前段（Barratt–Eccles 模型の厳密な随伴 F ⊣ U の厳密な bar 図式 B_•(X)・増大・U の下での分裂、上限 約 800 行）。bar を ∞ の図式へ移す比較と実現の同定（§21.4 の 2〜5）は ③-b の取り込みの後。
2. **sifted の一般部分は ③-b へ**：§21.5 の S のうち「厳密な Δᵒᵖ 図式の hocolim と native な錐の橋」「coherent な図式を厳密な計算へ移す比較」「U（忘却）が実現を保つ一般の形」は IS-W2（3b-1・3b-3・3b-4）。⑤a に残るのは BE 固有の部分（代数の実現と台の複体の実現の比較、arity と微分・射の整合、任意の sifted 形状への延長）で、③-b の取り込みの後に 5a-4。
3. **Tot の群**は G10（3b-2）と 3b-4 の後に 5a-5。
4. **界面に欄を足す**：`coproduct_tensor` の同型が `coprodWith_cocone` の二脚をテンソルの標準射へ送る条件を、`EInfinityTheory` の欄として足す（名前は ⑤a が提案、§3 の 3 の組み立て関数ではこの欄も引数に）。drafts 33 本は `E` を受け取るだけなので影響は実例の sorry が一つ増えるだけ。A2 の `derivedPrismaticCohomology_tensor` がこの欄を使う。
5. 止まり方：共通部分（§11）と同じく、超過が 3 割以内なら報告して続け、3 割を超えそうなときだけ止める。
