# K 理論側の参考文献の対応表（2026-11-07）

作成：段階 II の調整役。読み取りだけのエージェント 4 本で調べた（担当：本論文、KST、Land–Tamme と Tamme、K の基盤の文献）。対象は、主定理の K 理論側の二つの sorry（`theorem_3_1_K0`＝論文 Theorem 3.1、`Section4.supportedRankK0_descent`＝論文 Lemma 4.6）を消す経路で使う参考文献の主張。17 文献・208 項目。

- `items.csv` の列：`reference`、`item`、`kind`、`statement`、`status`（`proved`・`partial`・`interface`（仮定として置いている）・`sorry`・`frozen`（凍結コード）・`none`）、`goal`（目標 B に要るか：`required`・`not_required`・`unknown`）、`declarations`、`used_for`、`plan`、`note`、`confidence`。
- 判定の方法：計画書・Lean の宣言名と docstring・原典（arXiv にあるもの）の照合。**Lean を動かしての確認はしていない**。KST/・InfinityCategories/・DifferentialGraded/ に sorry は 0 件なので、未完の部分は `none` か `interface` になる。
- 一覧のページ（非公開の Artifact）：https://claude.ai/artifact/FXYE7BDWZeeXxswJxYRrke
- 文献ごとの全項目の表（11-07 夜〜、Codex）：依頼は `codex-maps.md`、結果は `maps/`。この `items.csv` は書き換えない。
- **11-11 完了**：全 17 文献 688 項目の照合と、上の「K の計画の問題」10 点の照合結果は `maps/summary.md`。新しく分かった点：K の降下の「有限 Zariski Čech 条件」と二つの降下の補題が `[ModelCategory SSet]`（満たせない仮定）を要求する。K の再開時に作り直す。

AR-W1 段6以降、宣言欄には現行本体・固定 Mathlib に実在する宣言の `完全名 @ パス:行` を書く。ルート直下は `_root_.` を付ける。計画、却下した候補、Archive、番号が推定の参照は備考列 `reference_note` に置く。本体の参照がない既存項目もこの備考に経緯を残し、対応の状態を継承する。[再開時の課題](../audit-review/k-restart-issues.md)

## 調査で見つかった、K の計画の問題（要検討）

1. **KST §4 への依存**：段階 II の計画は「KST §4（群ホモロジー）は使わない」とするが、KST §5 は §4 の主張を使う。Prop 5.2 は Cor 4.12（Land–Tamme の pro 切除で供給できる見込み）、Lemma 5.5 は Cor 4.13 と Prop 4.8（KST の証明は凍結した plus 構成 L2 による）。Prop 4.8・Cor 4.13 の供給経路が未決。
2. **K の 1-connectivity**：Land–Tamme Thm 2.32 を K に使うには K が `IsKConnective` を満たすこと（LT Lemma 2.4・Example 2.6(i)）が要るが、どの計画にもなく、LT の証明は plus 構成による（L2 は凍結）。1 と同じく、凍結した plus 構成に行き当たる。
3. **公理 (3)（冪零不変性）**：経路が未決（⑥ の段 1 の調査の対象）。1・2 と合わせて、plus 構成の凍結を見直すかどうかを決める必要がある。
4. **担当のいない部分**：KST §5 の K と pro の結論（Lemma 5.1、Prop 5.2 の K の部分、Claim 5.3、Prop 5.4、Lemma 5.5・5.6、組み立て）は、決定 13 で K-L6 の担当だったが、決定 16 で L6 を凍結して担当がいない。
5. **凍結コードの中の部品**：KST §4 の pro の形式（Def 4.4、Lemma 4.6・4.9・4.10）の実装が、凍結した `KST/ProExcision/` にある。主経路で使うなら、凍結の解除か移設を決める。
6. **経路で要るのに計画にない主張**：Land–Tamme Cor 2.35（本文で「ちょうど KST Thm 4.11」）。前提は Thm 2.32、KST Lemma 4.10、係数版。Lean にない。
7. **非連結 K の局所化不変量への登録**（K-7 e・f）が未完で、Land–Tamme の結論を K に当てはめる口がない。
8. **計画の文書どうしの食い違い**：`k-theory-kst-route.md` §2.3 と D6 に、決定 16 より前の「Land–Tamme の Thm 2.32 は使わない」「⊙ は使わない」が残っている。BGT の番号のずれの疑い（route の「局所化（Thm 2.10、[BGT 9.8]）」。v4 の Thm 9.8 は共表現可能性の定理）。**→ 11-07 夜の K の地図の段 0 で解消**：局所化は BGT v4 §9.3 が Thm 9.8 の帰結として述べており、KST 2.10 の引用はそれを指す。
9. **Lean の型と論文のずれ**：`theorem_3_1_K0` は K₀ だけ・整数形・Noether 局所環で J=(z) の場合で、K₀ は有限自由な複体のモデル。論文の π₀ K と結ぶ補題（自由モデルから perfect への K₀ の単射性）が要る（B-6 の「K₀ のモデルの一本化」）。`supportedRankK0_descent` は Lemma 4.6・Thm 3.1 (3.2)・§4.5 の台の同定を束ねた形。KST の経路の F5 の迂回を採れば Lemma 4.6 自体は要らなくなる可能性がある。
10. 論文の Theorem 3.1 の証明の最初の二段は Goodwillie の定理と Land–Tamme Thm A.2（truncating な不変量の cdh 降下）を使う。計画 v2 はこれを KST の経路（Thm A・Thm 3.7）で置き換える（論文の参考文献に KST はない）。
