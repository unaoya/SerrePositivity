# P⁰ を目標にした基盤の整理：計画の下書き

作成：2026-11-16（調整役）。**下書き**（ユーザーの方針 11-16「P⁰ を目標として、そのために無限圏や HA の内容を整理していくことを第一に」を受けた案。各段の担当・外枠は段 0 の報告を見てから決める）。

## 0. 目標と原則

- **目標**：Lurie, DAG XIII Constr 2.2.6 の P⁰ を、原典どおりに定義する（E∞-k 代数 A について A → A のスペクトルの射、忘却 CAlg_k → Sp の自己変換）。Rem 2.2.7（π_0 で x^p、正次数で 0）まで。
- **D81**：CAlg は HA 流（∞-オペラッド・対称モノイダル ∞ 圏）。
- **原典どおり**：定義は HA・HTT・Kerodon・DAG XIII・NS の形で。計算用の模型は比較の定理として（定義の代わりにしない）。
- **整理しながら**：新しいものは Kerodon・HTT・HA の配置に、文献の属性（`@[cite …]`・`@[kerodon …]`）を付けて置く。既存の部品で文献に当たるものは、使う前に正しい場所へ（OE-W1 と同じ手順）。
- 必要な項目の一覧は `research/p0-lurie/p0-map.html`（59 項目、定義に要る 48 項目のうち なし 24・一部 14・鎖の模型 6・済 4）と `research/p0-lurie/` の三つの調査。

## 1. 層（依存の順）

| 層 | 中身 | 主な原典 | 既存の土台 |
|---|---|---|---|
| P1 | ∞-オペラッド、対称モノイダル ∞ 圏（N(Fin_*) 上の余 Cartesian fibration）、Cartesian・余 Cartesian 構造 | HA 2.0.0.7、2.1.1.10、2.4 | Kerodon の余 Cartesian fibration の分類（約 1,000 本）、HTT の対応表 |
| P2 | Alg_O・CAlg、CAlg のテンソルは余積、拡大冪 X^{⊗p} ∈ Fun(BΣ_p, C)、乗法の Σ_p 等変性 | HA 2.1.3.1、3.2.4.7、DAG XIII Constr 2.2.1、Rem 2.2.4 | なし（BE の模型は比較の材料） |
| P3 | D(k) を対称モノイダル ∞ 圏に（モノイダルな局所化）、Mod_k、⊗_k、Mod_{Hk} ≃ D(k)、perfect = compact | HA 4.1.7、4.5.2.1、7.1.2.13、7.2.4.2 | D(A) は安定・presentable が無条件、`tensorWith`、dg の perfect |
| P4 | norm と Tate 構成（有限群 G = C_p でよい）：Fun(BG, C)、Beck–Chevalley、Nm、(−)^{tG}、誘導された作用で 0 | HA 6.1.6.3・6.1.6.7・6.1.6.12、NS I.1、DAG XIII 1.1.5・2.1.3〜2.1.25、HTT 4.3.3.7 | Kerodon の Kan 延長、安定 ∞ 圏の加法性、鎖の段階の `cyclicTateComplex`（比較の材料） |
| P5 | T̂_p と exact 性、Tate 対角：D(k) の道なら T_p ≃ k^{tG} ⊗_k −（Eilenberg–Watts）、Sp の道なら NS III.1 | DAG XIII 2.2.2〜2.2.5、HA 4.8.4.1、NS III.1、HA 1.4.2.23 | `CyclicMixedOrbit` などの組合せの芯 |
| P6 | P⁰ の構成と Rem 2.2.7、Sp への忘却 V_k | DAG XIII 2.2.6〜2.2.7 | `eilenbergMacLaneDerived`、May の演算（一致の比較の材料） |

**経路の選択（段 0 で比べる）**：D(F_p) の中で DAG XIII の順に作る道（Sp は最後に結果を述べる先だけ。D(F_p) は安定・presentable が揃っている）と、Sp の上で NS を追う道（KST の Sp の安定性が条件つき、smash 積・presentable がない）。調査の段階では D(F_p) の道が出発点として強い（`research/p0-lurie/ha-for-ns.md` §4）。

## 2. 段 0（紙）の分担案

- **⑤d**：P1〜P3 の型つきの一覧と見込み。既存の余 Cartesian fibration・D(A) への乗せ方、HA の番号ごとの対応（HA の対応表の none・partial を一件ずつ）、置き場所（`InfinityCategories/HA/` の節）。
- **⑤a**：P4〜P6 の型つきの一覧と見込み。鎖の段階の既存の部品（`cyclicTateComplex` など）との比較をどこで使うか、May の演算との一致を述べるか。経路の比較（D(F_p) か Sp か）。
- 両方とも Lean の追加・ビルドはしない。段 0 の報告を見て、ユーザーが経路・順序・担当・外枠を決める。

## 3. 他のレーン

- ③-a（5∞-1）・一括（5∞-3a）・⑥（2g）は P⁰ と独立。今の停止点まで続け、その時点で P⁰ の基盤へ回すかを決める。
- ③-b は OE-W1（EInfinity の一般の部分を外へ）。これも「整理」の一部で、P4 の Kan 延長・重み付き極限の部品の置き場所が決まる。
- 共有の鍵の負荷：段 0 は紙なので増えない。
