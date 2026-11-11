# E∞ の作り方の検討の材料（2026-11-07 夜）

作成：段階 II の調整役（読み取りだけのエージェントの調査を整理）。未決：今の Barratt–Eccles の dg の模型（`EInfinity/`）で CAlg_R を定義したまま進めるか、HA の方向（∞-オペラッドで CAlg(D(R)) を作り、模型と比較する）で作るか。HA の形式化そのものも検討中（`research/ha-coverage/`）。

## 1. BS が CAlg_R をどう使っているか

drafts と `BhattScholze/` で該当語を含む .lean は 42 本（drafts 40、本体 2。本体の 2 本は docstring と Mathlib の名前だけ）。

- **∞ 圏の API だけ（32 本）**：`CAlg_R`/`CAlg_A`（約 220）、忘却 `cAlgForgetDerived`（67）、`cAlgRestrictScalars`（51）、`cAlgBaseChange`（15）、離散環の埋め込み `algebraEmbedding`（約 70）、極限錐の保存、完備化の反射。
- **模型の中身に触れる（8 本）**：二系統にまとまる。
  - (a) cofibrant な代表から取る H⁰ の環：`DerivedGeneral/ScalarRestriction` の `cAlgH0Ring`、`A4/Perfectoidization` の `cAlgH0Algebra`、`A2/DerivedPrismaticCohomology`。π₀ を API にすれば置き換えられる。
  - (b) cdga・余単体的可換環を厳密な射のまま CAlg に送る経路：`Shared/CosimplicialEInfinity`（`totEInfinityFunctor`、`cdgaCAlg`）、`A1/CrystallineInput`（`formsBEFunctor`・`formsCAlg`）、`A1/DeRhamComparisonPoly`（`rootFormsAugmentation`）、`Shared/EInfinityPowerOperation`（P⁰ を Barratt–Eccles の E(p) の作用で作る予定）。

## 2. BS が要る CAlg_R の性質

| 項目 | 内容 | 引用 |
| --- | --- | --- |
| G-A2-4・G-A4-2 | sifted・filtered 余極限、U がそれを保つ | HA 3.2.3.1 |
| — | 余積 ＝ テンソル | HA 3.2.4.7 |
| — | U の極限保存・保存性 | HA 3.2.2.5・3.2.2.6 |
| G12 | 表現可能 | HA 3.2.3.5 |
| M13 系 | 底変換と制限の随伴、自由代数 | — |
| — | H⁰ の環と離散な切断 | HA 7.1.3.15・7.1.3.18 |
| G-A1-11 | Tot C^• の E∞ 構造と RΓ_CAlg ≃ Tot | Berger–Fresse、McClure–Smith |
| M14・G-A4-1 | P⁰ | Lurie DAG XIII Constr 2.2.6、Rem 2.2.7 |
| M15・G-A5-1 | descendability | Mathew |
| — | 平坦性 | HA 7.2.2.10 |

`perfectoidization-interface.md` §5 に、HA 4.5.4.7 を使わず Hinich Thm 4.1.1 で比べる判断がすでにある。

## 3. ∞ 側の土台

InfinityCategories に ∞-オペラッド・N(Fin_*)・operadic nerve・Day 畳み込み・∞ の対称モノイダル圏は 0 件（「対称モノイダル」は 1 圏のものだけ）。前提の部品（余カルテシアン fibration、straightening、presentable）はある。

## 4. 比較定理の文献（調査役が本文で確かめたもの）

- **Hinich, Rectification of algebras and modules**（arXiv:1311.4130、Doc. Math. 20 (2015)）Thm 4.1.1：homotopically sound（admissible かつ Σ-cofibrant、Def 2.4.3・2.4.6）な置き換え R → C_*(O) について、N(Alg_R(C(k)))[W⁻¹] ≃ Alg_O(QC(k))。k は任意の可換環。O = Comm、R = Barratt–Eccles で CAlg(D(k)) との比較。証明は HA 6.2.2.14（Barr–Beck）と HA 3.2.2.6・3.1.3.5・3.2.3.1。Barratt–Eccles の admissibility は論文の中では確かめていない（判定は 2.3.3）。
- **Pavlov–Scholbach, Admissibility and rectification of colored symmetric operads**（arXiv:1410.5675、J. Topol. 11 (2018)）Thm 7.11：比較の同値 ⇔ QO → O が symmetric flat（Barratt–Eccles は QO = O で自動）。Thm 7.5・5.11。Ch(R) で Comm が admissible なのは Q ⊂ R のときだけ。
- **HA 4.5.4.7**：freely powered を仮定。標数 p の Ch(R) では成り立たず、厳密な可換代数には使えない。
- HA 4.1.7.4・Ex. 4.1.7.6：モデル圏の局所化が対称モノイダル。
- Haugseng（arXiv:1909.10042）、Chu–Haugseng（1707.08049）：番号は未確認。
- 未確認：BM03 Thm 3.2 が Ch(R) で Σ-cofibrant なオペラッドを admissible にするか。

## 5. HA の方向で最小限に要る HA の項目

2.0.0.7（対称モノイダル ∞ 圏）、2.1.1.10（∞-オペラッド）、2.1.1.23（operadic nerve）、2.1.2.7、2.1.3.1（Alg）、4.1.7.4・4.1.7.6（D(R) の対称モノイダル構造）、3.1.3.5・3.1.3.13（自由代数）、3.2.2.5・3.2.2.6、3.2.3.1・3.2.3.5、3.2.4.7、比較には上の定理の一つと 6.2.2.14。§2.1.4（preoperad のモデル構造）と Day 畳み込みは必須でない。

## 6. 二経路の規模の見積もり（2026-11-11、読み取りのエージェント。物差しは調整役が実測で確認）

材料：HA の確認レーンの不足一覧（`research/ha-coverage/review/einfinity-gaps.md`、§2.0〜2.1・§3.1〜3.2・§4.1.7・§4.5.4 を照合、ほぼ全部 none）、⑤a の BS-W16 の見積もりと実績。

**物差し（実測、main 40b7d9f35）**：F1/Cocartesian 38,667 行、F2/Presentable 92,214 行、Derived 303,751 行、EInfinity 202,600 行（Hammock 21,607、BarrattEccles 38,332）、Interface 365 行。Barr–Beck・∞-monad・SymmetricMonoidal・∞-operad は InfinityCategories に 0 件。**較正**：⑤a の W16 の実績（Theory/ 6,159 行）は見積もりの上限の約 1.8 倍。

| 行 | (A) HA の方向 | (B) 今の模型 | 共有 |
| --- | --- | --- | --- |
| ∞-オペラッド・対称モノイダル ∞ 圏（2.0〜2.1.1） | 8,000〜20,000 | — | — |
| operadic nerve、Alg/CAlg（2.1.1.23〜2.1.3.1） | 4,000〜12,000 | — | — |
| D(R) のモノイダル ∞ 局所化（4.1.7） | 12,000〜30,000 | — | — |
| 自由代数、operadic 左 Kan 拡張（3.1.3） | 10,000〜25,000 | — | — |
| 極限・保存性・sifted・表現可能（3.2.2〜3.2.3） | 13,000〜35,000 | sifted 1,600〜2,700、G12 3,000〜10,000 | — |
| 余積＝テンソル（3.2.4） | 6,000〜15,000 | 850〜1,450 | — |
| 整流（Hinich 4.1.1／PS 7.11 ＋ Barr–Beck–Lurie） | 25,000〜60,000（最も不確実） | — | 片側に B の W16 の欄が要る |
| P⁰（M14）、descendability（M15） | B と同じ＋輸送 | 2,000〜6,000、3,000〜8,000 | 両経路で共有 |
| B のみ：`baseChange_forget` の残り、Tot（G10 待ち） | — | 500〜1,500、750〜2,000 | A でも模型側の実例として残る |
| **総計** | **約 83,000〜212,000** | 約 12,700〜33,000（較正後の上限 約 60,000） | |

- (A) は全行が外挿（Cocartesian の 1/4〜1/2、Hammock＋ModelBridge＋DGNerve の 1/5〜1/2、Presentable の 1/20〜1/6 などを根拠に置いた）。(B) の sifted・余積・Tot は ⑤a の数字そのまま。
- **A に後で変えても B が無駄にならない部分**：界面 `EInfinityTheory` と drafts 33 本（別の実例を代入するだけ）、W16 の証明済みの欄（Hinich の証明は模型側の sifted 余極限・自由代数・保存性を使うので、整流の入力になる）、P⁰・Tot・M15（A でも模型で計算して輸送）。A 固有は ∞-オペラッド側の約 60,000〜145,000。B 固有で A に戻らないのは G12 の模型経路（3,000〜10,000）だけ。
