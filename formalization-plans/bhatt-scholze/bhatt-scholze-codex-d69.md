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

## 3. 追記（2026-11-10、調整役）：停止点 0 の承認

**承認**：段 0 の報告（`report-codex-d69.md`、2b8934248）。既存宣言の洗い出し、P1〜P3 の順序と置き場所、規模（約 8,100〜14,500 行）は報告のとおりでよい。段 1 に進んでよい。段 1〜3 は §1 の条件で、報告してそのまま次へ進んでよい。

1. **表示によらないこと**：古典的な鎖ホモトピー（交代余面複体の擬同型）で先に示してよい。Tot の可逆性は、後でこの擬同型から `totEInfinity_map_isInvertible`（界面の欄）で得る。
2. **係数の違う橋の擬同型**：導来 p 完備な底変換の後で述べてよい（設計 §10.5.2 の段 2・3 の転置と同じ内容）。古典的な複体で書くときは、各項の完備テンソルが導来の底変換を計算すること（平坦性・有界な p 冪ねじれなど）も示し、その仮定を型に書く。
3. **一般の pd 基底の塔を p^{e+2} から取ること**：よい。divided power の収束のための選び方であることを docstring に書く。
4. **⑤c との分担**：⑤c の K1 は正則列に対する具体的な包絡と Frobenius 除算（Lemma 2.36・2.38・Cor 2.39）、⑤b は任意の J つき pd 包（Berthelot）と枠・サイトへの適用。共通の補題が出たら、先に作った側の本体の宣言を使う（同じ補題を二つ作らない）。

## 追記（2026-11-12 朝、調整役）：停止点 3 の範囲

一般の I の δ 座標つき相対分冪包と `withExtraCoords` の同定、その包への η の厳密な射・D68 の η との特殊化の等式（段 0 の報告で足した案）は、停止点 3 に含めず**後回し**にする。§0 の P3 の範囲（サイト・構造層・Čech の塔・引き戻し・Poincaré の複体の比較）で停止点 3（BS-D69 の区切り）とする。E3 の経路の結晶の比較は結晶的な基底の場合で、D68 の η（ℤ_p）で足りる。停止点 3（347ec8a29、報告 7280b7ce5、52 本）は、KL-W1 の取り込みの後に改名に追従してから取り込む。

## 追記（2026-11-12 午後、調整役）：BS-D69 完了

停止点 3（347ec8a29、改名への追従 abf765583）を main に取り込んだ（登録 a34a840f7：47 BS・5 共通、root 30,407 本、段階 II の BS 監査 14,988 宣言で標準三公理のみ）。BS-D69 はここで完了。⑤b のチャットは IS-W2（③-b）へ。後回しの項目（一般の I の η）は design-status に記録済み。
