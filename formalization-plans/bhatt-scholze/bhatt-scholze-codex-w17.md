# Codex 作業指示書 BS-W17：Thm 4.11 の帰着、Construction 4.17、Rem 4.19 の底変換（⑤c）

作成：2026-11-11（段階 II の調整役）。宛先：⑤c BS 古典の Codex（同じチャット・worktree `../SerrePositivity-bs-classical`・枝 `math/bs-classical`）。検収：調整役。決定：ユーザー（11-11、BS-W15 §5）。設計：`a0-design.md` §2.8、`a1-design.md`（Construction 6.1・Prop 6.2・Thm 6.3）、D21・D74・D76。

## 0. 目標と範囲

Prisms の地図で「本体に部品」とされた項目のうち、∞ 圏（③）を待たずに組み立てられ、担当のいなかったものを本体で証明する。**古典的な部分（環・加群・鎖複体の模型）だけ**が範囲で、∞ 圏の対象（`CompleteModules`・`derivedInfinityCategory`・`SSet` への関手）が型に出る宣言は drafts に残す。

| 群 | 原典 | 内容 | drafts |
| --- | --- | --- | --- |
| **H1** Construction 6.1 の古典的な部分 | Constr 6.1、Ex 3.4、Ex 2.21 | `Construction61Hypotheses`、結晶的な被覆 `crystallineCover`・`crystallineCoverMap`（生成元の正則性・完備性・δ 射・イデアルの包含）、`universal61`（K2 の普遍的な向き付き prism が仮定を満たす：Frobenius の平坦性と A₀/d₀ の p ねじれなし）、mod p の Tor 振幅（`torAmplitude_modP_le_one`、`crystallineCoverMap_torAmplitude`） | `A1/HodgeTateComparison.lean` |
| **H2** Prop 6.2・Thm 6.3 への帰着の古典的な入力 | Prop 6.2、Thm 6.3、Thm 4.11 | 被覆の射の保存性・Nakayama（mod p への帰着、d 完備 Nakayama、忠実平坦な Frobenius）のうち、通常の導来圏 `DerivedCategory (ModuleCat A)` か鎖複体の模型で述べられる部分。HT 写像の比較そのもの（`hodgeTate_iso_of_construction61` など、∞ 側に出る型）は drafts に残す | 同上 |
| **H3** Construction 4.17 | Constr 4.17・4.18 | Čech–Alexander の対象 C⁰ が (R/A)_Δ の弱始対象（site では弱終）であること、余積と `cechNerveData` の環の側 | `A0/CechAlexander.lean` |
| **H4** Rem 4.19 の底変換 | Rem 4.19、Prop 3.13 (2) | affine 空間の小さい模型 B₀ = A⟨X₁,…,X_r⟩ の Čech–Alexander 模型と、prism の底変換との項ごとの両立（`cechAlexanderAffine_baseChange` の古典的な部分） | `A0/CechAlexander.lean`、`A0/BaseChange.lean` |

**範囲の外**：`moduleReflection`・`alphaStar`・`baseChangeB`・`baseChangeC` など ∞ 圏の関手が型に出るもの、Lemma 4.20・4.22 の Tot の比較（G10、③ の後）、RΓ_Δ との同一視。

**持ち分**：`A1/HodgeTateComparison.lean` は W17 から ⑤c の持ち分（BS-W15 §5。⑤a の A1 の書き換えは `CrystallineInput`・`HodgeTateMap` だけ）。`A0/CechAlexander.lean`・`A0/BaseChange.lean` は、⑤b（BS-D69 P2 の大きい Čech–Alexander 模型 `bigCechAlexander`）と重なりうる。段 0 で ⑤b の本体（`Prismatic/BigCech*`・`CrystallineCech*`）を読み、重なる宣言は再利用して報告する。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | H1〜H4 の各宣言について、(a) 古典的な部分か ∞ 側か、(b) 本体の既存の宣言（W15 の K1〜K5、⑤b の D68・D69、⑤a の A1）から証明する筋、(c) 足りない補題、(d) 規模の見込み。**最初に D74 の確認**：Construction 6.1 が使う Frobenius の平坦性が、K2 で置いた形（U/p 上の Frobenius が d 完全平坦）で足りるか。足りなければ原典のどこで何が要るかを書く | **停止点 0**：調整役が確かめる |
| 段 1 | H1 | 停止点 1 |
| 段 2 | H2 | 停止点 2 |
| 段 3 | H3・H4 | 停止点 3：BS-W17 の区切り |

- 停止点 0 は承認を待つ。段 1〜3 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。
- drafts の型を変える必要があれば止める。ただし、原典の仮定を落としていて drafts の型が原典より強いと分かったときは、止めて報告する（D76 と同じ扱い。調整役が原典に合わせる）。

## 2. 規則

- BS-W15 §2 と同じ（新規ファイルだけ、本体に sorry を残さない、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と BS 著者版の番号、小さなビルドだけ）。
- 定義は原典どおり（BS は原典どおり）。計算用の模型は定理として置き、定義を置き換えない。
- 置き場所：`BhattScholze/Prism/`・`BhattScholze/Prismatic/`・`BhattScholze/Semiperfectoid/` など。一般の可換環論は `CommutativeAlgebra/`、一般のホモロジー代数は `HomologicalAlgebra/`。`InfinityCategories/` には足さない。KST のディレクトリを直接 import しない。
- 満たせない `[ModelCategory SSet]` のような仮定は使わない。
- KL-W1 の段 3 が main に入ったら、調整役が配る改名表と一行のコマンドで、枝の新しいファイルの import と名前を書き換える。
- ビルドの鍵は `with_build_lock.sh --wait 3600`、整理券は一枚ずつ。報告は `report-codex-w17.md`。

## 3. 追記（2026-11-11、調整役）：停止点 0 の承認

段 0 の報告（`report-codex-w17.md`、8e982b124）を確かめた。H1〜H4 の型案・置き場所・規模（14〜24 本、約 3,700〜7,000 行）は報告のとおりでよい。段 1 に進んでよい。

1. **D74 と Construction 6.1 の仮定（D77）**：原典の Construction 6.1 は「A/p の Frobenius が平坦」を仮定し、普遍的な向き付き prism はこれを満たすと書く。しかし Ex 3.4 が示すのは「d 完全平坦」だけで、原典の中に普通の平坦性の証明はない。6.1 の証明が使うのは式 (6) の中央の射 A/(p,d) → A/(p,d^p) の忠実平坦性だけで、これは d 完全平坦から出る（報告 §1）。そこで次の形にする。
   - drafts の `Construction61Hypotheses` は原典どおり（普通の平坦性）に残す。
   - 本体の補題は、d 完全平坦性（`IsCompletelyFlat (Ideal.span {x}) …`）と A/d の p 正則性を明示的な引数に取る（原典より弱い仮定、一般化）。原典の仮定からこの入力が出ること（平坦 ⇒ d 完全平坦）も一行の補題として置く。
   - drafts の `universal61`（普遍 prism が普通の平坦性を満たすという型）は使わない。普遍の場合は K2 の `universalOrientedPrism_frobenius_isCompletelyFlat` と `universalOrientedPrism_mod_generator_p_regular` を直接入れる。drafts の `universalOrientedPrism_frobenius_flat`・`universal61` と、それに添字づけされた被覆・保存性の利用箇所を、この入力に付け替える型の変更を承認する（⑤c の持ち分の `A1/HodgeTateComparison.lean`）。
2. **HT 比較の結論**：`HodgeTateIsoStatement` の結論は今は古典的な型だが、証明は Lemma 4.20 の Δ の底変換（G10、∞ 側）を通る。W17 は報告のとおりその入力（H2 の保存性・Tor 振幅の鎖複体版）までとする。`hodgeTate_iso_*` の組み立ては G10 の後。
3. **順序**：段 1（H1）・段 2（H2）を先に進める。H3・H4 は、⑤b の BS-D69 の次の停止点の取り込み（`AffineEnvelopeBaseChange`・`AffineEnvelopeCoefficients`・`AffineCechFrameLift`・`BigCechVertexFrame` が main に入る）の後に、main を取り込んでから始める。取り込みは調整役が知らせる。⑤b の枝を直接 merge しない。
4. **H2 の有界性**：上に有界な既存 API だけで済ませない、という報告の注意のとおりでよい。任意の鎖複体の模型で次数を評価し、その模型が導来テンソルを計算することまで示す。
