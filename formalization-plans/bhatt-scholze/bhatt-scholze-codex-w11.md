# Codex 作業指示書 BS-W11（下書き）：段 1 の古典的単位 ③④——根添加・R₀・付値環・有限エタール・Milnor 四角形・arc site の 1 圏部分

作成：2026-11-03（BS 作業チャット、下書き）。宛先：Codex。**BS-W10 の後に開始**（基準コミットは開始時に記入：main `________`）。
design-status §4 の 7 の段 1 ③④。基盤（∞ 側・HA の 2b 後の名前）を待たない古典的可換環論だけを集めた。前提・ビルドの規則・禁止事項は BS-W10 §0・§3 と同じ。

## 1. 作業 A：根添加の構成（drafts/A5/RootAdjunction.lean → Perfectoidization/Derived/RootAdjunction）

主張は 11-03 に具体化済み（`rootAdjunctionStep`・`rootClosure` とその延長性・完備性・濃度・関手性、`algebraicRootClosure` と mod p の Frobenius 全射、
`polyAlgebra`・`polyRootAlgebra`（perfectoid）・`rootCover`）。
- 完備化は `PrincipalCompletionH0 _ p`（HA/DerivedCompletion/PrincipalKoszulRing。2b で名前が変わるので改名表を見る）。
- `polyRootAlgebra_isIntegralPerfectoid` は既存の一変数 `CompatibleRootPerfectoid`（Semiperfectoid/）の多変数版。既存の証明の構造を写す。
- `algebraicRootClosure_filteredColimit` の主張の形（`CategoryTheory.Limits` の colimit との比較）を決めてから書く。
- **停止点 A-1**：定義と全主張が型検査を通った時点。**A-2**：延長性・完備性・perfectoid 性まで。濃度評価は後回し可（理由付き sorry）。

## 2. 作業 B：Lemma 8.8 の前段と試験付値環（drafts/A6/ArcSite.lean の G-A6-11・G-A6-3、drafts/A6/ArcSheafProperty.lean の G-A6-6）

- G-A6-11：R₀ = ℤ_p[p^{1/p^∞}]^∧ の perfectoid 性（Codex W9 続き 6 の筋：W(F_p[t^{1/p^∞}]^∧_t)/([t] − p) との同型、または `isIntegralPerfectoid_of_compatible_p_roots`
  （p 正則なので使える））、`baseExtension` = completionRing(S ⊗_{ℤ_p} R₀) と濃度、`exists_baseExtension_lift`。
- G-A6-3：p 完備な階数 1 の付値環 V は perfectoid な p 完備階数 1 付値環 W に忠実平坦に埋まる（絶対整閉包の p 完備化、付値の延長）。W の中の p の両立する p 冪根。
  Mathlib の `ValuationRing`・`IsIntegralClosure`・付値の整拡大への延長（要確認：名前）を使う。
- G-A6-6：階数 1 の付値環の tilt・untilt（a = d mod p の四分岐は a6-design §3.1(2)）、untilt の付値環性（Česnavičius–Scholze Prop 2.1.9 の証明と同じ計算）。
- 1c：`valuationRing_milnorSquare`（任意の付値環、𝔭V_𝔭 = 𝔭 から）と、その特殊化 `valuationRing_milnorSquare_perfect`（引用 [BS17, Lemma 6.3] を証明で置き換える）。
- **停止点 B-1**：主張の型。**B-2**：R₀・G-A6-11・1c まで。**B-3**：付値環の tilt・untilt まで。

## 3. 作業 C：有限エタール代数の perfectoid 性（G-A8-6、drafts/A8/IntegralDiscreteness.lean の `isIntegralPerfectoid_of_finiteEtale`）

完全 prism (A,(d)) の商 R 上の有限エタール代数 T は、完備対 (A,(p,d)) に沿って有限エタール A 代数へ持ち上がり、mod p は完全環上の有限エタール環で完全、Frobenius を
持ち上げて完全 δ 環、d の正則性と (p,d) 完備性は有限エタール性（有限射影加群）から保たれ、Thm 3.10 で商は perfectoid（Codex W9 続き 2 の筋）。
Mathlib の `Algebra.Etale`・`Module.Finite`・有限射影加群・エタールの持ち上げ（`Algebra.FormallyEtale` の lift）を使う。
- **停止点 C-1**：型。**C-2**：証明。

## 4. 作業 D：arc site の 1 圏部分（drafts/A6/ArcSite.lean の残り）

`AffCompl`・`AffPerfd`（`CommRingCat` の充満部分圏の `SmallModel`、濃度 ≤ κ）、`IsArcCoverFamily`（既に具体的）、`arcTopology`（sInf）、coverage（底変換・合成・有限積）、
`isSheaf_arc_iff_cech`（S1 の生成系の補題を待つ部分は理由付き sorry）、`exists_perfectoid_arcCover`（作業 A・B の結果から）、`affPerfdInclusion_isCoverDense`
（Mathlib `Functor.IsCoverDense`、型は具体化済み）、`arcTopologyPerfd`（`inducedTopology`）。
- **停止点 D-1**：型。**D-2**：cover-dense まで。

## 5. 報告

BS-W10 §4 と同じ形で `report-codex-w11.md` に追記。各停止点で `git status --short` が作業範囲だけであること、ビルドの実測、残る sorry と理由。

## worktree の規則（11-05、調整役の提案）

- worktree は一度に一つ。作業 B が main に入ったら `bs-w10` の worktree は `git worktree remove` で消す（ブランチは残す）。
- 新しい worktree は `/private/tmp/` ではなく `/Users/sugakubunka/Documents/LEAN_Projects.nosync/` の下に作る（例：`../SerrePositivity-bs-w11`）。/tmp は再起動で消える。
- 停止点の間もこまめにブランチへコミットする。
