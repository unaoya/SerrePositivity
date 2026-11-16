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

## 4. 記録

- 11-16：段 0 を ⑤d（P1〜P3）・⑤a（P4〜P6）に渡した（ユーザー）。基準の main 79c1315e7。紙だけ、報告をコミットしたら止まる。両方の報告を並べて、経路・順序・担当・外枠をユーザーと決める。

## 5. 段 0 の結果（11-16 午後、取り込み d18dc42db・2ab22b3aa）

- ⑤a（P4〜P6、`stage-ii/report-p0-p4-p6-stage0.md`）：28 項目、補正後 59,600〜101,800 行（P4 21,000〜35,600、P5 23,000〜39,000、P6 15,600〜27,200）。D(F_p) で DAG XIII の順を推奨。
- ⑤d（P1〜P3、`research/p0-lurie/p1-p3-stage0.md`、HA の対応表 326 件を照合）：最小 M 25 項目で補正後 58,400〜113,800 行、E 4 項目 13,800〜27,200、C（Mod_Hk ≃ D(k)）7,000〜16,000。HA の選定節を広く作る差分は 85,000〜186,000。
- 本線（M と P4〜P6）の合計：補正後 約 118,000〜215,600 行。含まないもの：E・C、Sp の基盤（HA 4.8.4.1 を使うための D(k) の Sp 作用）。
- 両方で一致した点：D(F_p) の道、CAlg を BE の局所化で定義しない、May の演算は定義の後の比較だけ、P⁰ は CAlg の射にしない（Warning 2.2.10）。
- 並行の可能性：P4（norm・Tate）は安定 ∞ 圏と Kan 延長だけで作れ、P1〜P3 を待たない。P1-01〜07・10、P2-01 は D(k) を待たない。
- 未決：(i) I03（D(k) の Sp 作用、HA 4.8.4.1 の C 線形性の C）。D(F_p) の道でも Sp の対称モノイダル構造が要る可能性。(ii) 先に置き場所を直すもの（SimplicialLocalization・ProjectiveModel・Tensor/Fixed・TensorPowerRepresentation、OE-W1 と調整）。(iii) 文献の略号 DAGXIII・NS の登録（`research/bibliography.json` と `Util/Citation.lean`）。(iv) 各束の外枠。

## 6. 方針の決定（11-16 夕、ユーザー）

- **文献に忠実に**：目標のために特別な場合だけを示すやり方はしない。定義も定理も原典の一般性で。§5 の「最小 M」・C_p／F_p に限る案は範囲の決め方としては採らない（型と依存の材料として使う）。
- **範囲**：P⁰ への依存をたどって行き当たる節を、節ごとに全項目作る（章を丸ごとではない）。
- **文献ごとに項目を立てる**：HA・HTT・Kerodon・DAG XIII・NS をそれぞれ項目として立てる。同じ内容が複数の文献にあっても重複してよい（例：norm は HA 6.1.6 と NS I.1 の両方）。
- 未決：証明の忠実さの程度、既存の忠実でないもの（KST の Sp、BE の CAlg、May の演算、鎖の段階の Tate）の扱い。
