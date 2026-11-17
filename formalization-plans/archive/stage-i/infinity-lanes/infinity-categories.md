# ∞ 圏の基盤（α〜ε・Π）：一旦の目標と全体計画

作成日：2026-10-17。状態：G1（BS 側）の計画として有効。**基盤全体の正本は 2026-10-18 から
[foundations.md](foundations.md)**（F1・F2 を含める決定、層の構成、レーンの対応、マイルストーン）。
本文書は G1 の経緯と Π の工程の記録として残す。

## 0. 一旦の目標

**現在地（2026-10-18）：G1 達成。** 採用した型は
`BhattScholze.PerfectoidizationInterface.PerfectoidizationInterfaceE3`（D(R) レベル）で、
原典照合と公開型は [perfectoidization-interface.md](../../../bhatt-scholze/perfectoidization-interface.md) に記録した。
Π2-8・Π3 により、perfectoid 側の唯一の文献入力は
`BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` となる。
旧二入口は公開名・型を保った界面由来の定理となり、CLMST のファイルは変更しない。
差写像の全射性は Π2 の名前で公開する。主定理の未証明依存はこの存在入力と
`Section4.supportedRankK0_descent`・`theorem_3_1_K0` の三件。
以下の CAlg による構造体は当初案であり、採用した E3 の universal は離散時の環の射の普遍性、
limit は Type u の perfectoid 標的への制限付き極限である。
具体的な prismatic perfection と降下の証明、および E2 の表示比較は引き続き別工程である。

2026-10-17 の決定：Bhatt–Scholze §7–§8 と K 理論を ∞ 圏（quasicategory）の基盤に載せる。
その最初の到達点として次を置く。

**目標 G1。** perfectoid 化の具体的定義（BS Def 8.2、Δ_S の perfection）と Cor 8.12 の証明だけを
保留し、それ以外の構成をすべて証明付きで書く。保留分は次の「界面」の存在一つに集約する。

```
structure PerfectoidizationInterface (R : perfectoid 環, p) where
  perfd        : N(C_R) ⟶ CAlg_R            -- C_R：導来 p 完備 R 代数の 1 圏（通常の環）
  unit         : j ⟹ perfd                   -- 各 A に A → A_perfd、自然（単体的ホモトピー）
  coconnective : ∀ A, H^{<0}(perfd A) = 0                               -- Lemma 8.4（2026-10-26 に削除：どの橋も読まないため）
  universal    : ∀ A, ∀ perfectoid T, Map(perfd A, j T) ≃ Map(j A, j T)  -- Prop 8.5
  integral     : ∀ A が R 上整, perfd A は離散で perfectoid               -- Thm 1.17(1)
  excision     : ∀ (A → B, I, arc 条件), perfd の四角形は CAlg_R で引き戻し -- Cor 8.12
```

ここで j : N(C_R) → CAlg_R は通常の環を離散 E∞ 代数として埋め込む関手、
H⁰ : CAlg_R → CRing_R は 0 次コホモロジーの環。各欄の文言は宣言時に原典から写す
（Prop 8.5 を写像空間の形にするか極限の形にするかもそのとき固定する）。

**G1 の帰結。** 現在の二つの仮置き入力
`BhattScholze.Inputs.exists_perfectoidization_of_integral`（Thm 1.17(1) の環版）と
`BhattScholze.Inputs.perfectoidization_excision_isPullback`（Cor 8.12 の H⁰ 版）は、
界面から定理として導く。後者は差写像の全射性まで出る（候補 (a′) の形）。
主定理の公理監査では perfectoid 側の `sorry` が界面の存在一つになる。
K 理論側（定理 3.1・補題 4.6）は別計画 [k-theory-v1.md](../../k-theory-v1.md) で、α・β（と Sp のための γ）を共有する。

**G1 に要る構成。**

| 層 | 構成するもの | 規模（行） |
| --- | --- | --- |
| β | dg nerve（N）、D(S) := N_dg(Semifree(S)) と h D(S) ≌ Mathlib の導来圏（D）、錐による有限極限の計算 | 1 万前後 |
| α | quasicategory の極限、安定 ∞ 圏、fiber 列と長完全列、始対象の cofinality、h の橋 | 1〜2 万 |
| δ | D(S)^⊗（∞ オペラッド経路のときのみ） | 1〜2 万 |
| ε | CAlg_S、U : CAlg_S → D(S) とその極限保存、離散埋め込み j と充満忠実性、H⁰ | 2〜3.5 万（∞ オペラッド）／1〜2 万＋γ（モデル経路） |
| Π | 界面の型、界面から二入力を導く定理、CLMST 側の接続の付け替え | 0.5〜1k |

合計 5〜9 万行。

## 1. レーンと依存関係

```
N（dg nerve）──→ D（D(S)）──→ D4（錐による極限・安定性）──┐
                                  ↑                        │
A1（h の橋）  A2（join・slice・極限）──→ A3（写像空間・同値）──→ A4（安定 ∞ 圏）──→ A5（完全関手）
                                  │                        │
                                  └──→ [δ（D(S)^⊗）] ──→ ε（CAlg_S・U・j・H⁰）──→ Π（界面と橋）
                                                 ↑
                                        （モデル経路なら δ の代わりに γ と E∞ オペラッド）
```

- 今すぐ並列に始められる：N（進行中）、D2（古典的部分。N に依存しない）、A1・A2、V（紙の検証）。
- N の後：D1・D3。A2 の後：A3、δ の検討。A3 の後：A4、D4。
- 検査点 C1（N・D・A1〜A3 完了時）：ε の経路（∞ オペラッド／モデル）を決める。
- ε の後：Π。

## 2. レーン α：quasicategory の一般論

Mathlib（固定版）にあるもの：`SSet`、`Quasicategory`、`KanComplex`、inner fibration、
anodyne extension（`AnodyneExtensions/`、pushout-product）、`ihom`（Fun(K, X) が quasicategory）、
`hoFunctor : SSet ⥤ Cat`（`nerve ⊣ hoFunctor`、有限積保存）、`Quasicategory₂`・`HomotopyCategory₂`、
`QCat.strictBicategory`、π₀（`PiZero.lean`）。
ないもの：join、slice、left/right fibration、trivial Kan fibration の一般論、写像空間、
極限・余極限、圏同値、安定 ∞ 圏。リポジトリにもこれらはない。

| 項目 | 内容 | 原典 | 規模 |
| --- | --- | --- | --- |
| A1 h の橋 | quasicategory で `HomotopyCategory₂ X ≌ hoFunctor.obj X`。ホモトピー X × Δ¹ → Y ↦ 自然変換。`QCat.strictBicategory → Cat` の 2 関手（任意） | HTT 1.2.3、Kerodon 1.4 | 1k |
| A2 join・slice・極限 | 単体集合の join K ⋆ L、Δⁿ ⋆ K、slice X_{/p}・coslice。X が quasicategory なら X_{/p} も quasicategory で X_{/p} → X は right fibration（pushout-join 補題）。始対象・終対象。極限 := X_{/p} の終対象。引き戻し四角形 := Λ²₂ 型図式の極限。極限の一意性（終対象のなす Kan 複体は可縮）。始対象 c を持つ 1 圏上の極限は F(c)（X_{/F} → X_{/F(c)} が trivial Kan fibration） | HTT 1.2.8、2.1.2.1–2.1.2.3、4.1.1、Kerodon 4.3、4.6.7、7.1、7.2 | 4〜7k |
| A3 写像空間と同値 | pinched 写像空間と両端固定模型の比較、quasicategory の写像空間は Kan 複体、可逆辺の特徴づけ（Joyal）、充満忠実＋本質的全射 ⇒ 圏同値、成分が可逆な自然変換は可逆、極限は写像空間で検出される | HTT 1.2.5.1、2.2、4.4.2、Kerodon 4.4、4.6.2、4.6.5、7.1.? | 3〜6k |
| A4 安定 ∞ 圏 | 零対象、fiber・cofiber、安定性の定義、Σ・Ω、h C の三角構造、fiber 列の長完全列 | HA 1.1.1、1.1.2.14、1.1.3 | 5〜8k |
| A5 完全関手 | 零対象と fiber 列を保つ関手、h での三角関手、自然変換 | HA 1.1.4 | 1〜2k |

設計：Joyal モデル構造・straightening は使わない。left/right fibration と trivial Kan fibration は
lifting property で定義し、必要な combinatorics（join の pushout 補題）だけ証明する。
A2 の「始対象の cofinality」は一般の cofinality 定理でなく、直接 trivial Kan fibration を示す。

## 3. レーン β：dg nerve と D(S)

- N（[dg-nerve.md](dg-nerve.md)）：N0 完了、N1〜N6 進行中。
- D：
  - D1 Semifree(S) := `DGFullSubcategory (Complex S) (complexSemifree S)`、
    D(S) := `dgNerve S (Semifree S)`、quasicategory（N2）。
  - D2 `HomotopyCategory S (Semifree S) ≌ DerivedCategory (ModuleCat S)`。
    semifree ⇒ `IsKProjective`（`isKProjective_iff_homComplex_acyclic`、filtration の帰納と
    telescope の Milnor 列。dg 加群版 `Derived/SemifreeProjective.lean` の転送か複体で直接）、
    semifree 解像度の存在（`Module/Semifree/Resolution.lean` の転送か `complexSphere`・`complexDisk`
    で直接）、`complexHomotopyEquivalence` の制限と `Qh_map_bijective` による組み立て。
    N に依存しないので先に始める。
  - D3 `HomotopyCategory₂ (trunc₂ D(S)) ≌ DerivedCategory (ModuleCat S)`（N3 と D2 の合成）。
  - D4（A2・A3 の後）：D(S) の零対象、「四角形が ∞ 引き戻し ⟺ A → fib(B ⊕ C → D) が擬同型」、
    D(S) の安定性、h D(S) の三角構造が Mathlib のものと一致。
- 関手的 semifree 分解、底変更 − ⊗_S T の関手性、N_dg(Semifree) ≃ N_dg(KProj) は D の後の項目。

## 4. レーン δ：D(S)^⊗（∞ オペラッド経路のときのみ）

- 対称モノイダル dg 圏 Semifree(S)^⊗（semifree ⊗ semifree は semifree、単位 S）。
- 「演算子の dg 圏」C^⊗（対象は有限列、Hom 複体は Fin_* の射ごとの Hom のテンソル）と
  N_dg(C^⊗) → N(Fin_*)。cocartesian fibration であること、fiber が N_dg(C^{⊗n})、
  Segal 写像 N_dg(C^{⊗n}) → N_dg(C)^n が同値であること（N_dg(C ⊗ C′) ≃ N_dg(C) × N_dg(C′)、
  shuffle／Eilenberg–Zilber 型の比較。最初の紙検証項目）。
- 代替は Lurie の経路（Ch(S) の ∞ 局所化と HA 4.1.7.4）だが、∞ 局所化の機構が要るので採らない。

## 5. レーン ε：CAlg_S と忘却関手

**決定（2026-10-18）：** 段階 1 として E3（界面を D(R) レベルで述べる迂回。§6 参照）を先に閉じ、
ε の経路は E2（モデル圏、[e-infinity-algebras.md](e-infinity-algebras.md)）を採る。
理由：(1) E3 で G1 の実利（sorry の集約、差写像の全射性）が早く得られる、(2) K 理論が γ を必ず使う、
(3) E1 の δ（dg nerve とテンソル積の両立）は数学的に最も見通しが悪い、(4) BS の他の部分
（§4 の RΓ、§7 の animated 代数と左 Kan 拡張、§8 の Tot）もモデル圏の計算に直接対応する。
E1 は「HA の文との一致」のためだけに後から比較（HA 4.5.4.7 型）を足す選択肢として残す。
以下の二経路の表は比較の記録として残す。

| 経路 | CAlg_S | U と極限保存 | 離散埋め込み j | 必要な前提 |
| --- | --- | --- | --- | --- |
| ∞ オペラッド | CAlg(D(S)) := N(Fin_*) → D(S)^⊗ の ∞ オペラッド射の ∞ 圏（Fun_{N(Fin_*)} の充満部分） | ⟨1⟩ での評価。極限保存は HA 3.2.2.1・3.2.2.5（代数の極限は底で計算） | 可換環 → 可換 dg 代数（次数 0）→ D(S)^⊗ の切断。充満忠実性は HA 7.1.3 相当 | α、β、δ |
| モデル | Ch(S) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏（転送、`HomotopicalAlgebra/Transfer`）を ∞ 圏化（coherent nerve か ∞ 局所化） | 右 Quillen ⇒ homotopy 極限保存 ⇒ ∞ 極限保存（γ の転送層、HTT 4.2.4.1／HA 1.3.4.24） | 次数 0 の可換 dg 代数は E∞ 代数 | α、β、γ、オペラッドの基礎（Mathlib・リポジトリともになし） |

どちらでも H⁰ : CAlg_S → CRing_S と「U ∘ j = 複体への埋め込み」を証明する。
モデル経路は δ を不要にする代わりに γ（K 理論の Sp にも要る）に依存する。

## 6. レーン Π：界面と橋

- Π1（紙）：Lemma 8.4、Prop 8.5、Thm 1.17(1)、Cor 8.12、必要なら Prop 8.13 の文言を原典から写し、
  界面の各欄として過不足なく述べる。Prop 8.5 の形（写像空間か極限か）とサイズの扱いを決める。
  誤った欄は矛盾した公理になるので、一欄ずつ原典と照合する。
- Π2（Lean）：`PerfectoidizationInterface` の型。界面から
  `exists_perfectoidization_of_integral`（`integral` と `universal` と j の充満忠実性）と
  `perfectoidization_excision_isPullback`（U の引き戻し保存 → D4 の錐 → 長完全列と H^{−1} = 0 →
  環の引き戻しと差写像の全射性 → `IsPullback` in `CommRingCat`）を導く。
- Π3：CLMST 側の接続（`KLCanonicalExcisionSquare` の供給元）を界面由来の定理に付け替え、
  旧入力を削除。README・解説・公理監査を更新。

## 7. レーン γ（K 理論側と共有）

γ1（coherent nerve の quasicategory 性、HTT 1.1.5.10）は 2026-10-18 に完了（[e-infinity-algebras.md](e-infinity-algebras.md) §3・§5）。
K 理論の計画は [k-theory-kst-route.md](../kst-lanes/k-theory-kst-route.md) に移行し、その §13 で
γ-B（Sp := Kan 複体の Ω スペクトルの coherent nerve、HT-KQ 不要）を採った。
γ3（homotopy 極限 = ∞ 極限、HTT 4.2.4.1 型）は E2b と K 理論の Sp の双方が使う共有項目で、
K 理論側のレーン L9 と E2b の間で分担を決める。K 理論が ∞ 基盤に求める範囲（F0・F3、F2 は含めない）も同 §13。

## 8. 検査点と完了条件

- C1：N・D1〜D3・A1〜A3 が揃った時点で ε の経路を決める。γ の最初の成果（HTT 1.1.5.10 の状況）も見る。
- G1 完了：Π3 まで終わり、`scripts/audit_axioms.lean` の perfectoid 側の `sorry` が
  界面の存在一つだけになる。K 理論の二入力は別計画。
- 各レーンの受入基準は dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。

## 9. リスク

1. ε が最大。∞ オペラッド経路は HA 第 2〜3 章の combinatorics が大きい。モデル経路は γ の
   HTT 1.1.5.10 が未解決。
2. A2・A3 の Joyal 流の部分（可逆辺、trivial Kan fibration、極限の一意性）。
3. δ のテンソル積との両立（N_dg(C ⊗ C′) と N_dg(C) × N_dg(C′) の比較）。
4. 界面の欄の文言の誤り。Π1 で一欄ずつ照合する。
5. Mathlib の更新（Riou の homotopy groups・Kan–Quillen、McKoen の Fun）を取り込む時期。

## 10. 記録

（各レーンの着手・完了時に追記する。）
