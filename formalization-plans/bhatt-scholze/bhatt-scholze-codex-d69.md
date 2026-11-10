# Codex 作業指示書 BS-D69：D69 と結晶サイトの、∞ 圏に依らない部分（⑤b）

作成：2026-11-10（段階 II の調整役）。宛先：⑤b BS 実装の Codex（BS-D68 の続き、同じチャット・worktree `../SerrePositivity-bs-d68`・枝 `math/bs-d68`）。検収：調整役。設計：`a1-design.md` §10.4・§10.5（D69：関手としての同型 `deRham_iso_polynomial_universal` を厳密な模型と zigzag から作る、11-07 ユーザー決定）、§11（結晶サイトは必要最小限、RΓ_crys := RΓ(site, O_crys)）。

## 0. 目標と範囲

D69 と結晶サイトのうち、**厳密な模型の側**（環・複体・余単体的対象・サイトの古典的な議論）を本体に入れる。∞ 圏が要る部分（Tot の E∞ 構造、厳密な自然変換から関手 ∞ 圏の辺を作る部品、関手としての同型への組み立て、RΓ_crys の定義と Tot との比較）は、③ と ⑤a の BS-W16（界面の実例の Tot の欄）の後に回し、drafts に残す。

| 部品 | 内容 | 設計 |
| --- | --- | --- |
| **P1** 一般の pd 部品 | J つき pd 包（基底 (k, J, γ)、J B ⊆ K のとき p 完備な pd 包の普遍性と存在。Berthelot I.2.3.1 の p 完備化）、枠の pd Čech 脈体（`pdFrame`・`pdFrameEval`・`pdCechNerve`・`pdCechAugmentation`）、枠の射（`pdCechNerveMap`）、**表示によらないこと**（R̄ を覆う二つの枠の射が交代余面複体の擬同型）、小さい模型との比較（`pdModel_iso_pdCechNerve`） | §10.5.1 |
| **P2** zigzag の厳密な段 | 段 1〜4 の厳密な関手と厳密な自然変換：大きい Čech–Alexander 模型（`bigCechAlexander`、⑤b の既存の affine の模型を使う）、結晶の橋 β（`wittBigBridge`、大きい枠の J つき pd Čech 脈体 `wittBigPdModel`）、D_W → D_0(C)（`wittToSmall`、`wZero_isDPMorphism`）、pd de Rham の余単体的 cdga K(Q)^n と行 0 への射影（`pdDeRhamCDGA`・`pdDeRhamProjection`）。各段について「Poly(C) 上で厳密に自然」と「各対象で交代余面複体（または総複体）の擬同型」を示す | §10.5.2 |
| **P3** 結晶サイトの古典的な部分 | big affine site（対象 (D/p^n → R′ ← R)、p 冪零）、Zariski 位相、O_crys が環の層であること（`crystallineStructure_isSheaf`、Stacks 07JJ の O の場合）、Čech の塔 `pdCechTower` と pro 弱終性 `pdCechTower_proWeaklyTerminal`、R̄ についての引き戻しのサイトの関手 `crysPullbackSite`、多項式の場合の Poincaré 補題の複体の段（Čech–Alexander の複体と持ち上げの de Rham 複体の擬同型、Stacks 07LG の F = O） | §11 |

**範囲の外**（drafts に残す）：`totEInfinityFunctor` と Tot の辺・可逆性、`functorIsoOfPointwiseInvertibleHomotopy` を使う組み立て `bigZigzagIso`・`deRham_iso_polynomial_universal`、`crystallineCohomology`（RΓ(site, O_crys) は Sheaves の `derivedGlobalSectionsCAlg`）とその関手性 `crystallineCohomology_map`・`crystallineCechIso`・`crystallineCohomology_polynomial_deRham` の RΓ の形。

## 1. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 段 0 | 1. P1〜P3 の各宣言について、本体の既存（⑤b の D68 の部品、`Delta/DividedPower/`、`Prismatic/` の affine Čech–Alexander の模型ほか）と drafts の型を洗い、何を新しく書くかを決める。2. 置き場所と規模の見込み。3. ⑤c（BS-W15）の K1（Lemma 2.36・2.38 の多変数・r 元、δ 環の divided power 包絡）との分担の確認。P1 の J つき pd 包（Berthelot）は K1 と別物だが、共通の補題があれば、どちらに置くかを提案する。4. drafts の型を変える必要がある所 | **停止点 0**：調整役が確かめる |
| 段 1 | P1 | 停止点 1 |
| 段 2 | P2 | 停止点 2 |
| 段 3 | P3 | **停止点 3**：BS-D69 の区切り |

- 停止点 0 は承認を待つ。段 1〜3 は BS-W12 §3 と同じ条件（対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない）なら、報告してそのまま次へ進んでよい。取り込みは調整役が停止点ごとに行う。

## 2. 規則

- BS-D68 と同じ（新規ファイルだけ、本体に sorry を残さない、閉じられない宣言は drafts に残す、E3 非依存、入口と監査への登録は調整役、docstring は日本語の 概要／方針／規約／使われ方 と原典・Berthelot・Stacks の番号、小さなビルドだけ）。
- **E∞ の界面（D71）**：CAlg_R の模型の中身（Barratt–Eccles の作用、cofibrant な代表、hammock の単体など）に新しく触れない。drafts の A1 の二本（`CrystallineInput.lean`・`HodgeTateMap.lean`）は、⑤a が界面を通す形に書き換える予定（BS-W14 §3 の 6）。⑤b がこの二本を書き換える必要があるときは、CAlg_R に触れる行には手を付けず、報告に書く（⑤a と調整役が順序を決める）。
- **持ち分**：drafts の `A0/`・`A3/` は ⑤c の持ち分（読むだけ）。
- KL-W1 の段 3 が近く main に入り、`InfinityCategories/` のモジュールの場所と名前空間が変わる。取り込まれたら調整役が改名表と書き換えの手順を知らせる。
- ビルドの鍵は `with_build_lock.sh --wait 1800`。取れないときは少し間を置いて取り直す。
- 報告は `report-codex-d69.md`。
