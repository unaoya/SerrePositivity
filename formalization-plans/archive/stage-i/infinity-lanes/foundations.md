# 基盤の統合計画（v2）：基盤優先、K は Land–Tamme 経路

作成日：2026-10-19。状態：**採用（2026-10-19、B 案：dg 増強流の Land–Tamme）**。v1 は [archive/foundations-v1.md](../../foundations-v1.md)。
K 経路の正本 [k-theory-kst-route.md](../kst-lanes/k-theory-kst-route.md) §13 の決定 16 がこれに対応する。本文書が基盤全体の正本であり、
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

状態は 2026-11-05（段階 II の開始時。調整役の調査、正本は `foundations-progress.md` の小項目の印）。M 番号・A／B 番号は [段階 II の計画](../../../stage-ii-plan-draft.md) と [infinity-foundation-plan.md](../infinity-foundation-plan.md) 段 G。規模は Lean 行数の目安。

| 層 | 項目 | 原典 | 使う側 | 状態 | 規模 |
| --- | --- | --- | --- | --- | --- |
| F0 | quasicategory、h、join・slice、極限・余極限、写像空間、Joyal、同値、関手 ∞ 圏の極限 | Kerodon 1〜4・7.1 | 全部 | 完了 | — |
| F3 | 安定 ∞ 圏、h の三角構造、長完全列、完全関手（S1〜S6）。D7：D(S) の安定性 | HA 1.1 | K、BS | 完了（S1〜S6、D7、一般の安定性判定 D-7 d） | — |
| β | dg nerve、D(S)、Perf(S)、h D(S) ≅ 導来圏（β1・β2） | HA 1.3 | BS、K | 完了 | — |
| **β3** | Drinfeld 商の dg nerve = ∞ 圏的 Verdier 商（局所化の普遍性、安定性、Verdier 列） | HA 1.1.4、Drinfeld 2004、Kerodon 6.3 | K（Verdier 列、T2、(3.6)） | dg 側は完了（D-4・D-9・D-16）。∞ 圏一般の商 M7・関手性 M8 は未着手（B-1） | 1〜2 万 |
| **β4** | dg の gluing（双加群に沿う貼り合わせ）の dg nerve = 安定 ∞ 圏の lax pullback | Tamme 2018 §1、Kuznetsov–Lunts | K（Tamme・LT） | 完了（G-1 a〜f、10-25）。K 側の残りは K-10 d（gluing 商から Verdier 列の供給） | 1〜2 万 |
| **β5** | 非可換 dg 代数 A の D(A)・Perf(A)、dg 関手 ⊗_A B・Hom の ∞ 関手化、Morita 不変性、単体環の DK による dg 代数化 | HA 7.1.2（比較の目標のみ） | K（LT の対象供給、L5 の導来環） | 完了（D-5）。⊗ᴸ の固定テンソルと対称性は IF-G1（7bda72c3c） | 1〜3 万 |
| **β6** | dg 代数のホモトピー論：Postnikov 塔と遷移・連結度、平方零拡大と derivation、Postnikov 層の双加群、cell 分解と持ち上げ、path 対象と homotopy pullback（LT §2.4 の k-connective 条件の dg 模型。10-22 09:40 追加、Sp が所有、配置は `KST/LocalizingInvariants/`） | Land–Tamme 2019 §2.4、Lemma 2.30・Cor. 2.31・Thm. 2.32 | K（pro 切除の連結度条件）、D（β4 の ⊙ の Tor 条件）、K-7 | 一部：a〜e・g 完了、f（平方零摂動の homotopy pullback）・h 未完 | 1〜2 万 |
| **P** | presentable ∞ 圏：accessible・presentable の定義、前層と Ind の presentable 性、極限・余極限、随伴関手定理、Pr^L／Pr^R、Bousfield 局所化の存在、P_Σ の普遍性（10-23 追加、新レーン P） | HTT 5.4〜5.5 | 第 II 段（BS-7 の animated 環、降下）。N-4 e〜g を引き取る | ほぼ完了：P-1 a〜d・f・g、e1〜e5・e8。e6 の全体同値・e7・P-12 は未完 | 150〜300 時間 |
| **K-7（dg 形）** | 非連結 K：Sp の逐次余極限、dg 懸垂 Σ(Perf A) = D(A)^κ／Perf(A)（Drinfeld 商）、反復 Ω^n K(Σ^n) の余極限、連結 K との比較、Verdier 列と Morita（10-23 追加、新レーン K-7） | BGT 2013 §9、Schlichting 2006 | K-基盤 1（局所化不変量としての K） | 一部：a・b・c1〜c3・d1・d2 完了。c4・c5 は凍結、d3〜f は M8(b) の再設計の後 | 80〜160 時間 |
| γ | γ1 coherent nerve、γ1.5 DK 比較、γ3 homotopy 極限 = ∞ 極限 | HTT 1.1.5、2.2、4.2.4 | 𝒮、Sp、E2b | 完了（γ3 は 10-20） | — |
| **γ4** | Quillen 随伴 = ∞ 随伴、右 Quillen 関手の極限保存 | HTT 5.2.4.6 | E2b（U : CAlg_R → D(R)）、Sp | 完了（N-2、10-21） | 0.5〜1 万 |
| F1 | cocartesian fibration、transport、straightening、Yoneda・前層（α2）。随伴、局所化、cofinality、Kan 拡張（α2b） | Kerodon 5〜8 | F2-lite、β3、K | 完了（Ind レーン 10-25）。Cat_∞ 値 straightening の一般の底は休止。M11・M16 が残る | 残り 2〜4 万 |
| **F2-lite** | Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限（引き戻し、Fun(Δ¹,−) による lax pullback）、filtered 余極限と Ind、compact 対象、冪等完備化、Ind(C) の安定性と compact 生成。presentable の一般論と随伴関手定理は K 第 II 段・BS §7 まで後回し | Kerodon 5.5・9、HTT 5.1.4・5.3 | K（Cat^perf、非連結 K、lax pullback）、β4 | 完了（Cat_∞ の極限・lax pullback、冪等完備化、κ-compact、Ind の安定性と compact 生成） | 3〜5 万 |
| E | E2a-3〜5（転送モデル構造、右 Quillen な U、Map^h）、E2b（CAlg_R := N^hc、U の ∞ 関手化、離散対象） | Berger–Moerdijk、Berger–Fresse、HTT 1.1.5 | BS（G1′） | E2-1〜E2-8（G1′）完了。E2c・G12・M14・M15 は未着手 | 残り 2〜4 万 |
| Sp | Kan 複体の Ω スペクトル（BF 模型）、π_*、fiber 列、有理化、Tot・hG（L9）。γ3 後に Sp の ∞ 極限、安定 ∞ 圏としての Sp | BF 1978、HA 1.4 | K（局所化不変量の値域）、L8 | 一部：BF 模型・π_*・L9 系は完了。`sp_isStable` は仮定 `NativeLoopComparison` つき。Sp-2 の B、Sp-6 s2〜s5、I-5 は未完 | 残り 1〜3 万 |
| **K-基盤 1** | Cat^perf（冪等完備な小安定 ∞ 圏）、Verdier 列、半直交分解、∞-S• 構成と加法性（L1）、fibration・局所化定理、非連結 K（BGT、Ind の κ-compact 版）、局所化不変量の定義 | BGT 2013、Waldhausen 1985、Barwick 2016 | K | 一部：∞-S•・加法性・Cat^perf・連結版 fibration（K-6）・半直交分解は完了。非連結 K と局所化不変量への登録は未完（B-3） | 4〜7 万 |
| **K-基盤 2** | Tamme の lax pullback の分裂定理、Land–Tamme の ⊙ 構成と主定理、pro 版（Tor の pro 消滅から pro 切除） | Tamme 2018、Land–Tamme 2019 §1〜3 | K（公理 (2) の pro 切除部分） | 一部：K-8 a〜c・d1〜d6・d8・f′、K-10 a〜c は完了。K-8 d7・e、K-10 d・e は未完（B-4） | 2〜4 万 |
| F2（後半） | presentable ∞ 圏、随伴関手定理、Bousfield 局所化、P_Σ と sifted 余極限、𝒮 の普遍性 | HTT 5.5、Kerodon 9 | BS §7（animated 環）、K-1c、将来の数論幾何 | ほぼ完了（I-8、IF-G1 の G3・G7・G8・G13）。e6・e7、G8 の四角形、G4・G6・G9・G10 が残る（③） | 4〜8 万 |
| F4・F5（任意） | 対称モノイダル ∞ 圏・∞ オペラッド、E₁ 環スペクトルと Mod、相対テンソル | HA 2〜4、7.1 | HA 流の Land–Tamme、BS §7 以降 | 未着手（段階 II の範囲外） | 10〜20 万 |

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

| レーン | 旧レーン | 所有（新構造、2026-10-24） | 残り（依存順） | 最初の工程 |
| --- | --- | --- | --- | --- |
| Ind | F1、F1b | `InfinityCategories/F1/`（Cocartesian/ は休止・Auxiliary）、`F1B/`、`F2/Ind/`・`F2/FilteredExchange/`・`F2/Compact/`・`F2/Idempotent/` | I-1 a7 交換定理（8 時間上限）→ I-2 Ind の安定性・compact 生成 | a7 の `ApexRawTriangleCandidate_eq_universal_iff` 右辺 |
| P | N、P | `F2/Presentable/`、`HomotopyLimits/` | P-1 b 前層の presentable 性 → g P_Σ → c → d 随伴関手定理 → e → f | b の一般の小さい底上の前層 |
| D | D | `Stable/`、`Derived/`（Gluing/ 以外）、`DGNerve/`、`DoldKanComparison/`、`DifferentialGraded/` | D-7 d IsStable の結論 → D-8 K-7 供給 DGKappaConeInput → D-9 β4 共同分、D2 吸収 | D-7 d の loop 同値からの安定性定理 |
| D2 | D2 | `Derived/Gluing/` | G-1 β4 d 実ホモトピー逆 → e → f（⊙ の同定、IsVerdierSequence 供給） | 未接続 CoefficientYonedaInverseChainMap の修正 |
| E2 | E2 | `EInfinity/` | E2-7 g1・g2 → E2-8 G1′ → 停止（BS-7 は第 II 段） | g1 の列の cofibrant 相対圏への持ち上げ |
| Sp | Sp | `KST/Spectra/`、`KST/LocalizingInvariants/`（局所化・分数・Verdier 商 API の正本） | K-9 β6 g → f → h → K-8 e pro 版 → 依頼対応 | β6 g の W source の Γ への前合成 |
| K-S• | K-S• | `KST/SConstruction/`（S• 界面の正本） | K-10 c 商 End → d IsVerdierSequence → e LT 主定理 Cat^perf 版 | c の角から小模型への Yoneda の Morita |
| K-B | K-F、K-7 | `KST/Fibration/`、`KST/NonConnective/` | K-6 c → b → d → e、K-7 c → d → e → f | K-6 c の relabelEnrichedObjects と K-7 c の dgKappaZeroPerfAction_values（独立、初日は並行） |
| R | R-A・R-B・R-C | 常設しない。第 I 段終了時の停止窓で `Core/`・`Coherent/`・`PinchedHom/` を含む移動を行う | KST/Spectra の基盤部分の降格、型の異なる準重複、R21・R4・R5・R10 | — |
| 休止（第 II 段） | K-L4、K-L8、K-L5、K-L7 | 導来幾何（Perf(X)）、降下、導来 blowup、スキーム補題。引き継ぎは各計画の冒頭 | — | — |
| 凍結 | K-L2、K-L6 | Auxiliary として保持。再開しない | — | — |

並列数は 7。L4 が持っていた dg 圏の一般論（半自由分解、Drinfeld 商、§26）は D レーンの β3・β5 が読み取り専用で使い、
必要な一般化は D レーンが `DifferentialGraded/` ではなく `InfinityCategories/Derived/` 側に置く。

**変更記録（2026-10-22 10:10、ユーザー承認）**：K 側の三本の直列鎖（F1b の Ind 鎖、D の β5 → β4、K-S• の d10 → K-6 → K-7）を短縮するため、
(1) F1 を F1-1d（Cat_∞ 値分類、第 I 段のどのレーンも依存しない）から F1-4・F1-5・F1-3b へ、(2) N を F2N-4（冪等完備化、Ind に依存しない）へ、
(3) 新レーン D2 で β4 を β5 と並列化、(4) 新レーン K-F で K-6 を K-S• と並列化。レーンは 9 本。指示文は [restart-2026-10-22.md](../../restart-2026-10-22.md)。

**変更記録（2026-10-23 05:30、ユーザー承認）**：新レーン P（presentable ∞ 圏、第 II 段の先行投資）と K-7（非連結 K の dg 形）を新設。
転用予定：F1 は F2N-5 の後に P へ合流、E2 は G1′ の後に P_Σ・animated 環（BS-7 入口）、D は D-7 の後に K-10 d（gluing 商の Verdier 列供給）、
F1b は a7 の後に P へ合流、N は F2N-3 の後に P へ合流。レーンは一時 11 本、合流後 9〜10 本。指示文は [restart-2026-10-23.md](../../restart-2026-10-23.md)。

**変更記録（2026-10-23 09:50、ユーザー承認 09:33）**：解説 exposition/ja/infinity のリファクタ候補 R1〜R25 を実施する R レーンを新設。正本は refactoring-infinity.md。段階と不変条件は同ファイル §2〜4。

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

**変更記録（2026-10-24 13:50、ユーザー承認）**：全レーン停止中にリファクタ R1〜R25 の大半を完了（タグ refactor-stage1〜3-2026-10-24、R13 は進行中）。
レーンをゼロベースで再設計し 8 本に統合（F1＋F1b → Ind、N＋P → P、K-F＋K-7 → K-B。§6 の表）。進捗チェックリストは v3（foundations-progress.md）。
再開文は restart-2026-10-24.md。一・二段目はコーディネータが固定、三段目はレーンが着手時に提示。

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

**運用追加（2026-10-22 19:50、ユーザー承認）**：安定 ∞ 圏の Verdier 商・分数（Ore 族、分母輸送、亜群化）・任意辺集合の局所化の API は
Sp の `KST/LocalizingInvariants/`（L9-spectra.md「主要宣言：一般局所化・補助成果」）を正本とする。K-F・K-S• は新規の同種補題を自前で作らず、
不足分は Sp に依頼して待つ。既に K-F が `KST/Fibration/` に作った分数・coslice の構成は保持するが、以後の拡張は Sp 側へ寄せる。

**運用追加（2026-10-23 09:50、ユーザー承認 09:33）**：(1) 必要な補題が自レーンの禁止 import 閉包にある場合はコピーせず、上流ファイルの分割を
コーディネータ経由で所有レーンに依頼する。(2) モジュールの移動・改名は旧モジュール名を互換シム（新所在の `public import` と `export` 別名）として残し、
下流の import と宣言名を壊さない。削除・改名の一括整理は第 I 段終了時。(3) R レーンは専用 worktree（`../SerrePositivity-R`、ブランチ `refactor/r-lane`）で作業し、main への取り込みはコーディネータがレーンの停止時間帯に行う（09:55 改訂）。他レーンのファイルは、最終コミットが 48 時間以上前・
未変更・純粋な移動のときだけ変更し、事前にコーディネータへ報告する。稼働中レーンの集約ファイルと監査スクリプトは R が編集しない。

**運用 v3（2026-10-24 13:50、ユーザー承認）**：
(1) チャットは二段目の項目の完了時、または稼働 24 時間ごとに新チャットへ引き継ぐ（引き継ぎ節を更新してコミットし、停止）。
(2) 他レーンのファイルは読むだけ。必要な補題が自レーンの import 閉包の外にある場合はコピーせず、コーディネータ経由で所有レーンに供給または上流ファイルの分割を依頼する。
(3) モジュールの移動・改名・削除はレーンでは行わず、第 I 段終了時などの停止窓で R が `scripts/move_module.py` と `scripts/refactor/verify.sh` で行う。レーンは監査スクリプトの import を自分の変更に合わせて更新する。
(4) API の正本：局所化・分数・Verdier 商は Sp、dg 側の対象供給は D、S• 界面は K-S•。同種の補題を他レーンに新設しない。
(5) 各レーンの検証は自分の集約ビルドと監査。統合検証は停止窓で verify.sh（ルート全体ビルド、監査対象の全ビルド、全監査、sorry 閉包監査）。main でのビルドの競合を避けるため、停止窓では main に書き込むレーンを一つに限定する。
(6) 停止時に残した未追跡の作業中ファイルは、再開時に引き継ぎ節の記録に従って新しい所在へ置き直すか削除する。記録のないものは削除する。

## 9. 進捗チェックリスト

本体は [foundations-progress.md](foundations-progress.md)（コーディネータが更新。進捗確認では項目の完了と日時だけを報告する）。
