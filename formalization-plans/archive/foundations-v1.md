# 基盤の統合計画：∞ 圏・dg 圏・E∞ 代数・K 理論

作成日：2026-10-18。状態：採用（2026-10-18、F1・F2 を基盤に含める決定を受けて作成）。
この文書は基盤全体の正本であり、各層の詳細は下の個別計画に置く。個別計画の決定が本文書と
矛盾する場合は本文書を優先し、個別計画の該当箇所を直す。

| 個別計画 | 層 |
| --- | --- |
| [infinity-core.md](infinity-core.md) | F0・F1・F2（quasicategory の一般論） |
| [dg-nerve.md](dg-nerve.md)、[derived-infinity-category.md](derived-infinity-category.md) | β（dg 圏と D(S)） |
| [e-infinity-algebras.md](e-infinity-algebras.md) | E（E∞ 代数のモデル圏と γ） |
| [k-theory-kst-route.md](k-theory-kst-route.md) | K（定理 3.1・補題 4.6） |
| [perfectoidization-interface.md](perfectoidization-interface.md)、[infinity-categories.md](infinity-categories.md) | Π（BS の界面）と G1 の経緯 |

## 0. 目的と方針

1. Serre の正値性の主定理に残る四つの入力（BS Thm 1.17(1)、BS Cor 8.12、論文の定理 3.1、補題 4.6）を、
   「BS の命題一つ（perfectoid 化の界面）を除いてすべて証明する」状態に持っていく（G1 と K の第 1 段）。
2. その基盤を、将来の数論幾何の形式化にも使える形で整える。具体的には **F0〜F3 に加えて F1（fibration・
   Yoneda・前層）と F2（空間の ∞ 圏・Ind・presentable・随伴関手定理・局所化）を基盤に含める**（2026-10-18 決定）。
3. 原典は Kerodon に固定し、HTT・HA の番号を併記する。モデル構造は「古典的対象の ∞ 圏化」（coherent nerve、
   γ3）にだけ使い、quasicategory の一般論には使わない。
4. 引用・公理・sorry は、G1 の界面の存在一つを除いて導入しない。

## 1. 層の構成

| 層 | 内容 | 原典 | 担当計画・レーン | 現状（2026-10-18） |
| --- | --- | --- | --- | --- |
| F0 | quasicategory、h、join・slice・極限、写像空間、Joyal の定理、同値、関手 ∞ 圏の極限 | Kerodon 1–4、7.1 / HTT 1–2、4.1、5.1.2 | α（A1〜A3、A6） | A1〜A3d 完了、A3e 進行中、A6 は次 |
| F3 | 安定 ∞ 圏、fiber 列、h の三角構造、完全関手。Sp（γ-B）。D(S)（β） | HA 1.1 / Kerodon なし | α（A4・A5）、L9、D（D7） | D(S)・D4 完了。A4・L9 は着手前 |
| F1 | left/right/cocartesian/cartesian fibration、covariant transport、Cat_∞、**straightening**（Kerodon 5.6）、随伴、局所化、Kan 拡張、twisted arrow と Hom 関手、前層 ∞ 圏と Yoneda | Kerodon 4.2、5、6、7.2–7.3、8 / HTT 2.1–2.4、3、4.3、5.2 | **α2（新設）** | 着手前。left/right fibration の定義は A2d にある |
| F2 | 空間の ∞ 圏 𝒮 = N^hc(Kan)（γ1 済み）とその極限・余極限（γ3）、filtered ∞ 圏と Ind、compact 対象、presentable、随伴関手定理、Bousfield 局所化、P_Σ と sifted 余極限 | Kerodon 9 / HTT 5.3–5.5 | **α3（新設、α2 の後）** | 着手前 |
| F4（任意） | 対称モノイダル ∞ 圏、∞ オペラッド、CAlg | HA 2–4 | 未割当 | E∞ は E（モデル圏）で実現するので当面不要 |
| β | dg nerve（N）、D(S) := N_dg(Semifree(S))、Perf(S)、引き戻しの判定、dg 商と ∞ 局所化の比較、DK 豊穣化と coherent nerve の比較（γ1.5） | HA 1.3 / Kerodon 2.5 | N、D | N0〜N7・γ1 完了、γ1.5 進行中。D1〜D6 完了、D8 進行中 |
| γ | γ1 coherent nerve は quasicategory（済）、γ2 Alg_E の単体的豊穣化、**γ3 homotopy 極限・余極限 = ∞ 極限・余極限（HTT 4.2.4.1）**、Quillen 随伴 = ∞ 随伴 | HTT 1.1.5、2.2、4.2.4、5.2.4 | N（γ1.5 の後に γ3）、E2b | γ3 は F2（𝒮 の余極限）・Sp・E2b の三者が使う共有項目 |
| E | E2a：Ch(S) の射影モデル構造、オペラッド、Barratt–Eccles、Alg_E の転送モデル構造、右 Quillen な U、Map^h。E2b：CAlg_S := N^hc。E2c：Tot と単体的可換環（BS の続き） | Hinich、Berger–Moerdijk、Berger–Fresse | E2a チャット | E2a-0・E2a-1 完了、進行中 |
| Π | perfectoid 化の界面（E3：D(R) レベル）、現在の二入力の導出、CLMST の付け替え | BS §8 | Π2 | Π2-0〜Π2-6 完了、Π2-5 後半・Π2-7 進行中 |
| K | KST 経路。K0 界面（π_* レベル）、K1 ∞-S•、K2 比較定理、A 導来幾何、B pro 切除、C スキーム、D 降下、E 論文 §3、γ-B の Sp、F5、M10 | k-theory-kst-route.md | L1〜L11 | L11・L2・L4・L6・L7・L8・L9 を起動（2026-10-18） |

## 2. 依存関係

```
F0 (α) ──→ F3 安定 (A4) ──→ D7 D(S) 安定、K1 ∞-S•、Sp 安定
   │
   ├──→ F1 (α2) ──→ F2 (α3) ──→ K3 非連結化 (a) BGT、β3 dg 商 = ∞ 局所化、BS §7 animated 環 (P_Σ)
   │                   ↑
   └── γ1 (N 済) ──→ γ3 (N) ──→ 𝒮 の余極限、Sp の ∞ 極限、E2b の U の極限保存
β1 dg nerve (N 済) ──→ β2 D(S) (D 済) ──→ D4 (済) ──→ Π2-7 ──→ G1
E2a ──→ E2b (γ2, γ3) ──→ 界面の CAlg 版への昇格
```

- G1（BS 側）は F1・F2 に依存しない。E3 で閉じ、E2b で昇格する。
- K の第 1 段（定理 3.1、π_* 形）は F0・F3 と γ-B で足りる。F2 は非連結化 (a) と Sp の ∞ 的主張に効く。
- BS §7（animated 環、Construction 7.6）は F2 の P_Σ と γ3（単体的可換環との比較、HTT 5.5.9.3）を使う。

## 3. 決定の変更（2026-10-18）

| 論点 | 旧 | 新 | 影響 |
| --- | --- | --- | --- |
| ∞ 基盤の範囲 | F0・F3 のみ。F2 は入れない（k-theory-kst-route.md §13-1） | **F0〜F3 すべて**。F1 は straightening を含めて Kerodon 5 の範囲、F2 は Kerodon 9 と HTT 5.3–5.5 | α2・α3 を新設 |
| 非連結 K | (b) Schlichting を既定、(a) は比較項目 | **(a) BGT を定義とし、(b) は K0 界面に対する暫定実装**。第 1 段は (b) で閉じてよく、F2 完成後に (a) へ差し替えて比較（§10-14）する | L3 の工程を二段にする |
| straightening | 使わない | F1 で証明する（Kerodon 5.6）。F0・β・G1 の既存成果は使わないまま | α2 の主要項目 |
| γ3 | E2b と K の間で分担未定 | **N が γ1.5 の後に担当**（𝒮・Sp・E2b の三者が使うため早める） | N の次工程 |
| CAlg | E2（モデル圏） | 変更なし。F4 は任意のまま | — |
| E2a-3 の acyclicity（2026-10-19） | Berger–Moerdijk §5／Hinich の filtration 議論で任意の始域の acyclicity を示す | **AW 対角による E の Hopf 構造と、標準区間の正規化鎖 N_*(Δ¹) の E-coalgebra 構造（Berger–Fresse）から全 E 代数の functorial path object を作り、fibration に対する左持ち上げ性 ⇒ 弱同値で転送する**（Berger–Moerdijk 命題 4.1・Berger–Fresse §3.1）。Hinich 4.1.1 の Σ-split は正標数で E に成り立たず、filtration 議論は cellular な始域に限られる。半モデル構造への格下げはしない | E2a-3 に Hopf 構造・区間の E-coalgebra 構造（table reduction E → χ と区間切断）の工程を追加 |

## 4. 現在のレーンと統合後の対応

| チャット | 現在 | 統合後の位置 | 次 |
| --- | --- | --- | --- |
| α | A6 完了（16:46） | F0 → K | F0 の担当範囲は完了（A3f・A3g は任意のまま）。2026-10-18 17:00 から **K-L1（∞-S• 構成、連結 K）**を担当する（k-theory-kst-route.md §5 K1・§8 L1、計画は kst-lanes/L1-s-construction.md） |
| α-S（D チャット、2026-10-18 新設） | — | F3 | 安定 ∞ 圏：零対象、fiber/cofiber 四角形、安定性の定義、Σ・Ω、h の三角構造（HA 1.1.2.14）、fiber 列の長完全列、完全関手。続けて D7（D(S) の安定性、cofiber 四角形の押し出し性を含む）。計画は [infinity-core-stable.md](infinity-core-stable.md) |
| α2（新設） | F1d | F1 | Kerodon 5.1（cocartesian fibration）→ 5.2（transport）→ 5.6（straightening）→ 8（Yoneda・前層）。F1e〜F1g は α2b へ切り出した |
| α2b（Π2 チャット、2026-10-18 新設） | — | F1 | 随伴（Kerodon 6.1〜6.2）、局所化と反射的部分 ∞ 圏（6.3）、Kan 拡張と cofinality の一般形（7.2〜7.3）。straightening に依存しない。計画は [infinity-core-F1b.md](infinity-core-F1b.md) |
| α3（新設、α2 の 5.6 後） | — | F2 | 𝒮 の極限・余極限（γ3 経由）→ filtered・Ind → compact・presentable → 随伴関手定理 → 局所化 → P_Σ |
| N | γ1.5 | β・γ | γ1.5 → γ3 → β3（dg 商 = ∞ 局所化、F2 の後） |
| D | D8 | β | D8 → D7（A4 の後）→ Perf と K1 の接続 |
| E2a | E2a-1 | E | E2a-2〜5 → E2b（γ2 の方式を E2a 完了時に決定） |
| Π2 | Π2-5 後半・Π2-7 | Π | Π2-8・Π3 はユーザー判断 |
| K：L11・L2・L4・L6・L7・L8・L9 | 起動直後 | K | 変更なし。L3 は (b) → (a) の二段 |
| K：L1・L3・L5・L10 | 未着手 | K | L1 は A6 の後。L3 は L1 の後に (b)、F2 の後に (a) |

## 5. マイルストーン

| 番号 | 到達点 | 必要な層 |
| --- | --- | --- |
| G1 | BS 側の sorry が界面一つに集約 | β、F0（極限）、Π |
| K-1a | 定理 3.1（H = A、π_* 形）で `theorem_3_1_K0` を置換 | F0・F3、γ-B、K0〜K2、A〜E |
| K-1b | F5 で `supportedRankK0_descent` を置換 | K-1a、L3 の (b) |
| F1 | straightening と Yoneda | α2 |
| F2 | presentable と随伴関手定理 | α3、γ3 |
| G1′ | 界面を CAlg_R（E2b）で述べ直す | E2a・E2b、γ3 |
| K-1c | 非連結 K を (a) に差し替え、Sp の同値（hG）で定理 3.1 を論文の形に | F2、γ3 |
| BS-7 | animated 環と Construction 7.6、Prop 8.5 の極限形の証明 | F2、E2c、γ3 |

規模の目安：F1 3〜6 万行、F2 4〜8 万行、γ3 1〜2 万行、K 第 1 段 22〜37 万行（k-theory-kst-route.md §5）。

## 6. 運用

- 各レーンは自分の計画ファイル（本文数百行、現在地・主要宣言の表）を持ち、実施記録はコミットメッセージに書く。
- 新設レーンの計画ファイルは `infinity-core.md` の節として置く（α2 は §8、α3 は §9）か、
  長くなれば `infinity-core-F1.md`・`infinity-core-F2.md` に分ける。
- 共有項目（γ3、A6、A2h の二宇宙版）は、使う側が「待つ」のではなく、担当レーンの着手順を上げる。
- 本文書の §1・§4 は状態が変わるたびに書き換える（追記しない）。

## 7. 整理フェーズ（2026-10-19 決定：基盤も継続、レーンは止めない、コーディネータは現チャット）

目的：肥大化した計画ファイル（総計約 9.8 万行）を本文 300 行以内に戻し、各レーンを
区切りごとに新しいチャットで再開する。並列数は 13 から、区切りでの統合により 11 程度に減らす。
停止は一斉ではなく、3〜4 レーンずつの順送り（rolling）で行い、残りは動かし続ける。

手順（レーンごと）：
1. 区切り指示：現在の工程を 1〜2 時間以内に仕上げ、検証・コミットし、計画冒頭に §7.1 の引き継ぎ節を書いて停止。
2. コーディネータが計画本文を機械的に圧縮（引き継ぎ・目標と原典・規約・工程表・主要宣言の表だけ残し、
   残りは `archive/<file>-log.md` へ全文移動）、再開指示文を作る。
3. 新チャットで再開。再開指示は短くし、内容は計画の引き継ぎ節を指す。
4. 全レーンの再開後に、ルートビルド・sorry・instance 仮定・宣言名重複の一括監査と計画ファイルの一括コミット。

順送りの順序（古い・肥大したものから）：第 1 組 K-L1、α2（F1）、N。第 2 組 K-L9、K-L2、α2b。
第 3 組 K-L4、K-L5、K-L6、K-L7、E2a。α-S は D7 完了時、K-L8 は再構成の区切りで。

### 7.1 引き継ぎ節の書式（各計画ファイルの冒頭に置く。100 行以内）

- 現在地：完了した工程と、進行中の工程の到達点（検証済みの範囲だけ）。
- 残り：未完の項目を依存順に箇条書き。各項目に原典の番号と見積もり（時間）。
- 主要宣言：主経路で他レーンが使う公開名と前提（型は Lean を正本とし、名前だけ）。
- 依存と提供：読み取り専用で使う他レーンのモジュール、他レーンへ提供する界面。
- 未コミット：未コミットのファイルと理由。
- 既知の問題：ビルド失敗、名前衝突、instance 仮定、設計上の懸念。
- 次の一手：再開した新チャットが最初にやる一工程。

### 7.2 分担（統合は区切りで行う）

| レーン | 旧 | 範囲 | 統合・後回し |
| --- | --- | --- | --- |
| K-Sp | K-L9 | L9e の完了、L8 への Tot API、γ3 後に Tot・hG が Sp の ∞ 極限である系 | — |
| K-降下 | K-L8 | 実 Tot 上の Čech 降下と定理 3.1（§13-15、Main/Auxiliary 分離済み） | — |
| K-S• | K-L1 | S• と K スペクトル。完了後に同じレーンで L3（fibration 定理・Morita・Bass・非連結 (b)） | L1 → L3 を直列化 |
| K-比較 | K-L2 | Γ・ĜL・plus・K₀/K₁、L1 との ∞-S• 比較 | — |
| K-導来幾何 | K-L4 | T1〜T3、Perf、RHom | — |
| K-blowup | K-L5 | 導来 blowup、ℙʳ、半直交分解、Thm 3.7・3.16・3.17 | — |
| K-pro | K-L6 ＋ K-L7 | pro 切除と §5 の K/pro 本体・古典部分 | L7b 完了時に L7 を L6 へ統合 |
| D | α-S | D7 → Perf と K1 の接続 → D ブロック（⊗ℚ 五項補題、nilinvariance D9） | D ブロックを同じレーンに直列化 |
| N | N | γ3c → γ3 の応用（Sp の極限保存、E2b の U の極限保存）→ β3（F2 後） | — |
| F1 | α2 ＋ α2b | α2：straightening → Yoneda・前層。α2b：B4・B5 の後に F1 の残り（twisted arrow・Hom 関手）を分担し、F1 完了後に両者で F2 | B5 完了時に α2b を F1 へ統合 |
| E2 | E2a | E2a-3（Hopf・区間界面・BF 区間）→ E2a-4・5 → E2b | E2c は後回し |
| 後回し | — | F2 の presentable 以降、L10（M9/F5・M10）、合流点 S1〜S5、β3、E2c | 前提が揃い次第 |
