# 基盤の統合計画（v2）：基盤優先、K は Land–Tamme 経路

作成日：2026-10-19。状態：**採用（2026-10-19、B 案：dg 増強流の Land–Tamme）**。v1 は [archive/foundations-v1.md](archive/foundations-v1.md)。
K 経路の正本 [k-theory-kst-route.md](k-theory-kst-route.md) §13 の決定 16 がこれに対応する。本文書が基盤全体の正本であり、
個別計画と矛盾する場合は本文書を優先する。

## 0. 目的と順序

1. 主目標を「BS と K の両方が要る範囲の ∞ 圏基盤を整備する」ことに置く。基盤が主、応用（BS の述べ直し、
   K の代数幾何）は従。
2. **当面は第 I 段（基盤）だけを進める（2026-10-19 決定）。第 II 段（応用）は I-a・I-b が閉じてから起動する。** 段階は二つ。**第 I 段（基盤）**：F0〜F3、F1、F2-lite、β3・β4、γ、E2、Sp、K の ∞ 圏的基盤（局所化不変量と
   Land–Tamme）。**第 II 段（応用）**：BS の界面を CAlg_R で述べ直す（G1′）、K の代数幾何（Perf(X)、導来 blowup、
   スキーム補題、降下、合流）で二入力を証明する。
3. K 側は KST の pro 切除（ĜL の群ホモロジー、Suslin–Wodzicki）を **Land–Tamme の ⊙ 構成**に置き換える。
   L2 の plus 構成と L6 の群ホモロジーは不要になり、既存コードは Auxiliary として凍結する（削除しない）。
4. 原則は v1 と同じ。原典は Kerodon・HTT・HA、引用・公理・sorry は界面の存在一つを除いて導入しない、
   モデル圏は古典的対象の ∞ 圏化（γ）にだけ使う、計画本文は 300 行以内、実施記録はコミットメッセージ。

## 1. Land–Tamme の実現方式（B 案を採用）

| 案 | 内容 | 要る基盤 | 規模の目安 |
| --- | --- | --- | --- |
| A：HA 流 | 環を E₁ 環スペクトル、加群を Mod_A（HA §4.2）、相対テンソルを bar 構成（HA §4.4）、⊙ を Mod の lax pullback の生成元の自己準同型環として作る | F4（対称モノイダル ∞ 圏・∞ オペラッド、HA §2〜3）、F5（環スペクトルと加群、HA §7.1）、F2 全体（presentable、Pr^L のテンソル積 HA §4.8） | 10〜20 万行。HA §2〜4・7 の形式化そのもの |
| **B：dg 増強流（採用）** | 環・導来環は dg 代数（単体環は Dold–Kan で dg 代数）、Mod_A := D(A) = N_dg(Semifree(A))、相対テンソルは dg の bar・テンソル、Verdier 商は Drinfeld 商、lax pullback は dg の gluing（双加群に沿う貼り合わせ）。∞ 側は安定 ∞ 圏・Verdier 列・半直交分解・局所化不変量の一般論だけ | F0〜F3、F1、F2-lite（Cat_∞・Ind・compact・冪等完備化）、β3〜β5、L3 | 3〜6 万行（L3 を含む）。HA §2〜4 は不要 |

Land–Tamme の主定理（Milnor 四角形に対し、B′ を A′ ⊙_A B に置き換えると任意の局所化不変量で引き戻し）は
Cat^perf 上の形式的な議論（Tamme の lax pullback の分裂と Verdier 列）で証明され、環や加群の ∞ 圏的構成は
「対象の供給」にしか使わない。B 案はその供給を dg 模型で行う。B 案を採ると F4・F5 は BS §7 以降の将来項目に戻る。

## 2. 基盤の項目表（今回必要な範囲）

状態は 2026-10-19 10:30。規模は Lean 行数の目安。

| 層 | 項目 | 原典 | 使う側 | 状態 | 規模 |
| --- | --- | --- | --- | --- | --- |
| F0 | quasicategory、h、join・slice、極限・余極限、写像空間、Joyal、同値、関手 ∞ 圏の極限 | Kerodon 1〜4・7.1 | 全部 | 完了 | — |
| F3 | 安定 ∞ 圏、h の三角構造、長完全列、完全関手（S1〜S6）。D7：D(S) の安定性 | HA 1.1 | K、BS | S1〜S6 完了、D7 残り 3〜6 時間 | — |
| β | dg nerve、D(S)、Perf(S)、h D(S) ≅ 導来圏（β1・β2） | HA 1.3 | BS、K | 完了 | — |
| **β3** | Drinfeld 商の dg nerve = ∞ 圏的 Verdier 商（局所化の普遍性、安定性、Verdier 列） | HA 1.1.4、Drinfeld 2004、Kerodon 6.3 | K（Verdier 列、T2、(3.6)） | 未着手。前提は F1b の局所化 | 1〜2 万 |
| **β4** | dg の gluing（双加群に沿う貼り合わせ）の dg nerve = 安定 ∞ 圏の lax pullback | Tamme 2018 §1、Kuznetsov–Lunts | K（Tamme・LT） | 未着手。前提は F2-lite の Cat_∞ の極限 | 1〜2 万 |
| **β5** | 非可換 dg 代数 A の D(A)・Perf(A)、dg 関手 ⊗_A B・Hom の ∞ 関手化、Morita 不変性、単体環の DK による dg 代数化 | HA 7.1.2（比較の目標のみ） | K（LT の対象供給、L5 の導来環） | 一部（L4 §26 の半自由分解、Perfect）。整理が必要 | 1〜3 万 |
| **β6** | dg 代数のホモトピー論：Postnikov 塔と遷移・連結度、平方零拡大と derivation、Postnikov 層の双加群、cell 分解と持ち上げ、path 対象と homotopy pullback（LT §2.4 の k-connective 条件の dg 模型。10-22 09:40 追加、Sp が所有、配置は `KST/LocalizingInvariants/`） | Land–Tamme 2019 §2.4、Lemma 2.30・Cor. 2.31・Thm. 2.32 | K（pro 切除の連結度条件）、D（β4 の ⊙ の Tor 条件）、K-7 | 進行中（10-22 06:12 着手、約 130 モジュール） | 1〜2 万 |
| γ | γ1 coherent nerve、γ1.5 DK 比較、γ3 homotopy 極限 = ∞ 極限 | HTT 1.1.5、2.2、4.2.4 | 𝒮、Sp、E2b | γ1・γ1.5 完了、γ3 残り僅か | — |
| **γ4** | Quillen 随伴 = ∞ 随伴、右 Quillen 関手の極限保存 | HTT 5.2.4.6 | E2b（U : CAlg_R → D(R)）、Sp | 未着手 | 0.5〜1 万 |
| F1 | cocartesian fibration、transport、straightening、Yoneda・前層（α2）。随伴、局所化、cofinality、Kan 拡張（α2b） | Kerodon 5〜8 | F2-lite、β3、K | straightening 最終段、B4 進行中 | 残り 2〜4 万 |
| **F2-lite** | Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限（引き戻し、Fun(Δ¹,−) による lax pullback）、filtered 余極限と Ind、compact 対象、冪等完備化、Ind(C) の安定性と compact 生成。presentable の一般論と随伴関手定理は K 第 II 段・BS §7 まで後回し | Kerodon 5.5・9、HTT 5.1.4・5.3 | K（Cat^perf、非連結 K、lax pullback）、β4 | 未着手。𝒮 の余極限は γ3 で済み | 3〜5 万 |
| E | E2a-3〜5（転送モデル構造、右 Quillen な U、Map^h）、E2b（CAlg_R := N^hc、U の ∞ 関手化、離散対象） | Berger–Moerdijk、Berger–Fresse、HTT 1.1.5 | BS（G1′） | E2a-2 完了、E2a-3 着手 | 残り 2〜4 万 |
| Sp | Kan 複体の Ω スペクトル（BF 模型）、π_*、fiber 列、有理化、Tot・hG（L9）。γ3 後に Sp の ∞ 極限、安定 ∞ 圏としての Sp | BF 1978、HA 1.4 | K（局所化不変量の値域）、L8 | L9e 進行中 | 残り 1〜3 万 |
| **K-基盤 1** | Cat^perf（冪等完備な小安定 ∞ 圏）、Verdier 列、半直交分解、∞-S• 構成と加法性（L1）、fibration・局所化定理、非連結 K（BGT、Ind の κ-compact 版）、局所化不変量の定義 | BGT 2013、Waldhausen 1985、Barwick 2016 | K | L1 進行中、L3 未着手 | 4〜7 万 |
| **K-基盤 2** | Tamme の lax pullback の分裂定理、Land–Tamme の ⊙ 構成と主定理、pro 版（Tor の pro 消滅から pro 切除） | Tamme 2018、Land–Tamme 2019 §1〜3 | K（公理 (2) の pro 切除部分） | 未着手 | 2〜4 万 |
| F2（後半） | presentable ∞ 圏、随伴関手定理、Bousfield 局所化、P_Σ と sifted 余極限、𝒮 の普遍性 | HTT 5.5、Kerodon 9 | BS §7（animated 環）、K-1c、将来の数論幾何 | 未着手。F2-lite の後（I-b） | 4〜8 万 |
| F4・F5（任意） | 対称モノイダル ∞ 圏・∞ オペラッド、E₁ 環スペクトルと Mod、相対テンソル | HA 2〜4、7.1 | HA 流の Land–Tamme、BS §7 以降 | 後段（I-c）。モデル構造を使わない証明への書き直しが要る | 10〜20 万 |

太字が v1 から追加・前倒しした項目。F4（対称モノイダル ∞ 圏）、F2 の presentable 以降、E2c、β の dg 商以外の
比較は後回しのまま。

## 3. K の証明経路（Land–Tamme 版）

定理 3.1 の八公理のうち、変わるのは (2)（抽象 blowup の降下）の証明だけで、他は v1 と同じ。

1. **K の定義**：K := 非連結 K を Cat^perf 上の局所化不変量として（K-基盤 1）。スキームには Perf(X) を
   dg 増強つきで与える（L4）。E = fib(K_ℚ → K[1/p]_ℚ) は局所化不変量の fiber として局所化不変量。
2. **公理 (1) Zariski Čech 降下**：Thomason の局所化 Perf(X)/Perf_Z(X) ≃ Perf(U)（L4 T2、β3）と
   fibration 定理から。
3. **公理 (2) 抽象 blowup の降下**：KST Thm 3.7（導来 blowup の半直交分解、L5）で導来スキームの
   blowup 四角形に帰着し、冪零 thickening の Milnor 四角形は **Land–Tamme の pro 切除**で処理する。
   ⊙ 環の Tor の pro 消滅は Artin–Rees 型の可換環論（L7）。KST §4 の群ホモロジーは使わない。
4. **公理 (3) 冪零不変性**：v1 の D ブロック（⊗ℚ の五項補題、離散的 nilinvariance D9）のまま。
   LT 採用で供給経路が変わらないかを計画時に再確認する（未決）。
5. **公理 (4)〜(8)**：有限平坦 transfer、有理固定点、平坦化、スキーム補題、(3.6) は v1 と同じ（L7・L8・L4）。
6. **降下の本体**（L8）と **合流**（K0 界面、F5、M10、S1〜S5）は v1 と同じ。

不要になるもの：L2 の Γ・ĜL・plus 構成・古典比較の大半（K₀ の同定だけ L1 で保持）、L6 の L6a〜g。

## 4. BS の経路

G1′（界面を CAlg_R で述べ直す）：E2a-3〜5 → E2b（γ2 の単体的豊穣化、γ4 で U の極限保存）→ 界面の述べ直し。
D(R) での引き戻しの主張は達成済み（G1）。BS-7（animated 環、Construction 7.6）は F2 の P_Σ と E2c が要るので
第 II 段の後。

## 5. 依存

```
F0 ─ F3 ─ D7 ─┐
β1・β2 ────────┼─ β3（Verdier 商）─┐
F1b 局所化 ────┘                    ├─ K-基盤 1（Cat^perf、Verdier 列、S•、fibration、非連結 K）─ K-基盤 2（Tamme、LT）─ K 第 II 段
F1 straightening ─ F2-lite（Cat_∞、Ind、compact）─ β4（gluing = lax pullback）─┘
γ3 ─ γ4 ─ Sp の ∞ 極限 ─┘（局所化不変量の値域）
E2a-3〜5 ─ E2b ─ G1′
```

## 6. レーン（基盤に集中、2026-10-19）

| レーン | 旧チャット | 範囲（I-a → I-b） | 最初の工程 |
| --- | --- | --- | --- |
| F1 | α2 | straightening（空間値は完了。Cat_∞ 値は有限単体底の同値 10-22 06:21 で区切り第 II 段へ）→ **F1-4 前層の極限・余極限 → F1-5 表現可能関手と極限 → F1-3b Hom 関手**（10-22 10:10 変更） | F1-4 |
| F1b → F2 | α2b | B4・B5 → Cat_∞・lax pullback（第 1 部、10-20 07:42 完了）→ **F2-lite 第 2 部（filtered 余極限、Ind、compact、冪等完備化、Ind の安定性）** → F2 後半（presentable、随伴関手定理） | F2N-1 |
| N | N | γ3c → γ4 → Sp への応用（完了）→ N-4 Bousfield 局所化・P_Σ（10-22 に g の区切りで休止）→ **F2N-4 冪等完備化（10-22 10:10 に F1b から移管）** | F2N-4 |
| D | α-S | D7 → β3（Drinfeld 商 = Verdier 商）→ β5（D(A) と ⊗_A）→ β4（gluing = lax pullback） | D7 の完了 |
| E2 | E2a | E2a-3〜5 → E2b（CAlg_R）→ G1′（界面の述べ直し） | E2a-3 (1) |
| Sp | K-L9 | L9e → Sp の ∞ 極限 → 局所化不変量の値域 Sp → K-5・K-8 の抽象部分（10-21）→ K-8 pro 版と **β6（dg 代数のホモトピー論、10-22 追加）** | L9e の収束 |
| D2 | 新設（10-22） | **β4**：双加群に沿う dg gluing の dg 圏、半直交分解、dg nerve と F1b の lax pullback の比較、安定性と完全射影。配置 `InfinityCategories/Derived/Gluing/`。D の β5 は読み取り専用 | gluing dg 圏の構成 |
| K-F | 新設（10-22） | **K-6 fibration 定理**：Verdier 列 D → C → C/D に対する連結 K の fiber 列（Waldhausen 1.6.4、BGT §7〜9）。配置 `KST/Fibration/`。Sp の K-5 と K-S• の S• は読み取り専用 | W の安定性と相対 S• |
| K-基盤 | K-L1 | L1c〜f（∞-S•、加法性、スペクトル）→ L3（fibration 定理、非連結 K = BGT (a)、局所化不変量）→ Tamme・Land–Tamme | L1c の完了 |
| 休止（第 II 段） | K-L4、K-L8、K-L5、K-L7 | 導来幾何（Perf(X)）、降下、導来 blowup、スキーム補題。引き継ぎ節を保持 | — |
| 凍結 | K-L2、K-L6 | Auxiliary として保持。再開しない | — |

並列数は 7。L4 が持っていた dg 圏の一般論（半自由分解、Drinfeld 商、§26）は D レーンの β3・β5 が読み取り専用で使い、
必要な一般化は D レーンが `DifferentialGraded/` ではなく `InfinityCategories/Derived/` 側に置く。

**変更記録（2026-10-22 10:10、ユーザー承認）**：K 側の三本の直列鎖（F1b の Ind 鎖、D の β5 → β4、K-S• の d10 → K-6 → K-7）を短縮するため、
(1) F1 を F1-1d（Cat_∞ 値分類、第 I 段のどのレーンも依存しない）から F1-4・F1-5・F1-3b へ、(2) N を F2N-4（冪等完備化、Ind に依存しない）へ、
(3) 新レーン D2 で β4 を β5 と並列化、(4) 新レーン K-F で K-6 を K-S• と並列化。レーンは 9 本。指示文は [restart-2026-10-22.md](restart-2026-10-22.md)。

## 7. マイルストーン

| 段階 | 番号 | 到達点 | 必要な層 |
| --- | --- | --- | --- |
| I-a | I-1 | F1 完了（straightening、Yoneda、随伴、局所化、Kan 拡張） | α2、α2b |
| I-a | I-2 | D7・β3・β5：D(S) の安定性、Verdier 商、D(A) の ∞ 関手化 | D |
| I-a | I-3 | F2-lite：Cat_∞ の極限、lax pullback、Ind、compact、冪等完備化 | α2b、N |
| I-a | I-4 | K-基盤 1：Cat^perf、∞-S•、fibration 定理、非連結 K、局所化不変量 | K-L1、D（β3）、N（Ind） |
| I-a | I-5 | Sp：∞ 極限と安定 ∞ 圏としての Sp | L9、N（γ3・γ4） |
| I-b | I-6 | K-基盤 2：Tamme の分裂定理、Land–Tamme の ⊙ と主定理 | K-L1、D（β4） |
| I-b | I-7 | G1′：界面を CAlg_R で述べ直す | E2、N（γ4） |
| I-b | I-8 | F2 後半：presentable、随伴関手定理、Bousfield 局所化、P_Σ | α2b、N |
| I-c（任意） | I-9 | F4・F5：対称モノイダル ∞ 圏、環スペクトルと Mod | 未割当 |
| II | II-1 | K-1a：`theorem_3_1_K0` の置換（L4・L5・L7・L8・D ブロック・合流） | I-a・I-b |
| II | II-2 | K-1b：`supportedRankK0_descent` の置換（L10） | II-1 |

規模の目安：I-a の残り 12〜20 万行、I-b 8〜15 万行、第 II 段 15〜25 万行。

## 8. 運用

- 各レーンは自分の計画ファイル（本文 300 行以内）を持ち、冒頭に「引き継ぎ」節（§8.1 の書式、100 行以内）を置く。
  実施記録はコミットメッセージ、長い記録・型一覧は `archive/` に移す。本文への追記は現在地の書き換えだけ。
- レーンの再開は順送り（3〜4 レーンずつ）。再開指示は短くし、内容は計画の引き継ぎ節と本文書を指す。
- 検証は対象ビルドと公理監査に加えて、主経路の宣言に `ModelCategory SSet` 等の instance 仮定が無いことを grep で確認する。
- 停止するのは工程完了・設計変更の提案・所有 import 閉包の破損のときだけ。報告後は承認を待たず次へ進む。

### 8.1 引き継ぎ節の書式

- 現在地：完了した工程と、進行中の工程の到達点（検証済みの範囲だけ）。
- 残り：未完の項目を依存順に箇条書き。各項目に原典の番号と見積もり（時間）。
- 主要宣言：主経路で他レーンが使う公開名（名前だけ。型は Lean が正本）。
- 依存と提供：読み取り専用で使う他レーンのモジュール、他レーンへ提供する界面。
- 未コミット：未コミットのファイルと理由。
- 既知の問題：ビルド失敗、名前衝突、instance 仮定、設計上の懸念。
- 次の一手：再開した新チャットが最初にやる一工程。

## 9. 進捗チェックリスト

本体は [foundations-progress.md](foundations-progress.md)（コーディネータが更新。進捗確認では項目の完了と日時だけを報告する）。
