# K 理論の再開に向けた紙の作業（たたき台、2026-11-11）

作成：段階 II の調整役。決定：ユーザー（11-11、「K は ∞ 圏の基盤が整ってから着手。それまでに紙の作業 1〜3 を進める」）。材料：K の地図の要約（`research/k-coverage/maps/summary.md`、全 17 文献 688 項目を Lean の型で確認）、K の経路（`kst-lanes/k-theory-kst-route.md`、計画 v2 と決定 1〜16）、段階 II の計画 §2（B-1〜B-6）。

本書は相談用のたたき台。確定したものは K の経路の §13 に決定として足し、本書は残りの論点だけを残す。

## 0. 要約

- K の実装は ∞ 圏の基盤（KL-W1 → ③ → ①）が整ってから。それまでは本書の紙の作業。
- 照合で分かった計画の穴は三つ（§1）。どれも ∞ の基盤が整っても自動的には埋まらない。
- `[ModelCategory SSet]` を仮定する降下の 54 ファイルは、すでに主経路から外れている（決定 15、`Descent.Auxiliary`）。主定理の閉包（1,142 モジュール）に `KST/Descent` は入っていない。作り直しの設計は §2。
- K が ∞ 側に求める部品の一覧は §3。③・① の範囲に入れる。

## 1. 計画の見直し：照合で分かった三つの穴

### 1.1 KST §4 の 4.8・4.13 の供給（要約の問題 1・6）

**何が穴か**：計画 v2（決定 16）は KST §4 の群ホモロジー（Thm 4.11）を Land–Tamme の ⊙ と pro 切除に置き換えた。しかし KST §5 は、4.11 の帰結 4.12 だけでなく、**Prop 4.8**（pro 単体環の同値は K の pro 同値を誘導）と **Cor 4.13**（補集合が通常スキームなら K の pro 比較が同値）も使う（Lemma 5.5 (i)(ii)(iii)）。Land–Tamme 2.35 は 4.11 に対応するが、4.8 と 4.13 は Land–Tamme からは直接出ない。

**候補**

| 案 | 中身 | 利点 | 難点 |
| --- | --- | --- | --- |
| (a) Land–Tamme の係数版から 4.8 を出す | 4.8 は「pro 環の同値 ⇒ K の pro 同値」。Land–Tamme Prop 2.28（connective な環の Postnikov 塔の pro 比較）と 2.31 を、dg 代数の塔に当てて示す。Lean には `postnikovFiniteMap_isProIso_of_connective` と `IsKConnective.invariantLevelMap_piProEquivalence_of_piProEquivalence` の形で部品がある | 決定 16 の方針（群ホモロジーを使わない）と整合 | 4.8 が要るのは**非 connective**（単体環の π₀ への比較）の場合もある。2.31 は `IsKConnective` を仮定するので、§1.2 と絡む |
| (b) 4.13 を「Zariski 降下＋4.8」で出す | KST の原証明そのもの（Thm 4.11 ＋ Thm 2.12） | 新しい議論がない | 4.11 の代わりに (a) の 4.8 を使う形に書き換える必要 |
| (c) Lemma 5.5 の使い方を変えて 4.8・4.13 の必要を減らす | 5.5 (i)(iii) は「導来の厚み Y(n)・D(n) と古典の Y(n)・E(n) の K の pro 比較」。導来 blowup の模型（決定 D3、Koszul cdga の有限 Zariski 図式）では、これを Koszul の塔の pro 同型（4.9・4.10、凍結側にある）から直接出せる可能性がある | 4.8 の一般形が要らなくなる | 紙で確かめていない。L5b の対象（導来 blowup）が確定していない |

**推奨**：(a)＋(c) を紙で確かめる。(a) は §1.2 の結論と一緒に決める。

### 1.2 K の 1 連結性（要約の問題 2）

**何が穴か**：Land–Tamme の Thm 2.32（pro 切除）を K に当てるには、K が「1-connective な不変量」（LT Lemma 2.4、Example 2.6 (i)）であることが要る。Lean の 2.31 は `IsKConnective` を**仮定**しているだけで、K 自身がそれを満たす証明はどの計画にもない。LT の証明は plus 構成（K_1 = GL/E）による。plus 構成は L2 として凍結中。

**候補**

| 案 | 中身 | 難点 |
| --- | --- | --- |
| (a) L2 の一部を凍結解除 | 1 連結性に要るのは「connective な環 A について K(A) → K(π₀A) が 1-connective」で、その証明は K₀・K₁ の比較（Thm 2.16 の n ≤ 1）。L2 の全部（plus 構成との比較 Prop 2.15）は要らない | L2 のどの部分が要るかの切り出し。KST Thm 2.16 は BGT 9.53 にも別証がある |
| (b) BGT 9.53 で K₀・K₁ の比較を出す | 非連結 K を BGT で定義する（決定 2 (a)）なら、9.53 の議論（Waldhausen の S• の低次の計算）が使える | BGT §9.3 の非連結 K の登録（§1.4）が先 |
| (c) 1 連結性を仮定（界面）にして第 1 段を閉じる | `IsKConnective K` を K0 界面の一欄にする | 段階 II の終わり条件（sorry 0、引用なし）に反する。採れない |

**訂正（11-11、BGT v4 の本文で確認）**：(b) は成り立たない。Thm 9.53 の主張は「connective な A∞ 環スペクトル R について、**i ≤ 0** で π_i IK(R) ≅ π_i IK(π₀R)」であり、i = 1 を含まない。しかもその証明は §9.5（EKMM の行列環 M_R・L_R、Prop 9.40 の BGL(R)⁺、Def 9.41）を経由する。つまり plus 構成そのものであり、L2 の凍結部分を避けられない。1 連結性に要るのは i = 1 の比較（K₁(R) ≅ K₁(π₀R)、KST Thm 2.16 の n ≤ 1）なので、BGT は根拠にならない。

**推奨（訂正後）**：(a) L2 の切り出し（K₀・K₁ の比較に要る部分だけ）を本線にする。何が要るかは、Land–Tamme Lemma 2.4・Example 2.6 (i) の証明が K₀・K₁ の計算（KST 2.16）だけで済むか、plus 構成の全体を使うかで決まる。読み取りのエージェントに確かめさせる（§4 の 3）。§3 の ∞ 側への要求「S• 構成の低次の計算」は、その結果しだいで「∞-S• の K₁ の計算（Waldhausen 1.5.9 の ∞ 版）」に絞る。

### 1.3 冪零不変性（公理 (3)、要約の問題 3）

**何が穴か**：論文は E = fib(K_ℚ → K[1/p]_ℚ) の冪零不変性を truncating 性（Goodwillie）から得る。計画 v2 はこれを D9（離散結合環 R と冪零イデアル I について、中間環 R̃ = R[1/p] ×_{S[1/p]} S を挟み、GL の有理ホモロジーの比較で K_ℚ の同型を出す）で置き換えた。D9 の Step 2 は GL・plus と有理ホモロジーの比較を使う。これも L2 の凍結部分に当たる。Lean の `Nilinvariant` は前層に課す条件で、係数つきの L がそれを満たす証明はない。

**候補**

| 案 | 中身 | 難点 |
| --- | --- | --- |
| (a) D9 のまま、L2 の有理ホモロジーの部分を凍結解除 | 決定どおり | §1.2 (a) と同じ切り出しの問題。L2 の規模（plus 構成）が大きい |
| (b) Land–Tamme Thm 3.5（truncating な不変量の冪零不変性）を使う | 論文の経路。E が truncating であることは Goodwillie（K → HC⁻ の相対比較）に依る | Goodwillie を形式化する規模が大きい（計画 v2 が避けた理由） |
| (c) 有理化した K の冪零不変性を、Weibel の「K_ℚ(R) → K_ℚ(R/I) は I 冪零なら同型」（Goodwillie 1986 の有理版）の**代数的な証明**で | 原典は Goodwillie "Relative algebraic K-theory and cyclic homology" Main Theorem。有理の場合は Hochschild・巡回ホモロジーの比較で、位相的な入力が少ない | Goodwillie の定理そのもの。規模は (b) と同程度 |
| (d) ⑥ の BS17 と同じ手で、Zariski 局所的に被約化と同型になるように E の定義を変える | 使う側（論文 Thm 3.1 の証明）が冪零不変性をどこで使うかによる。軌道の議論の V ↪ X ×_S Y（被約化）だけなら、E を「被約化で不変になるように定義し直す」ことで回避できる可能性 | 論文の主張の形が変わる。紙で確かめていない |

**推奨**：(a) と (d) を紙で確かめ、(d) が通るなら採る。(a) は L2 の切り出しの規模しだい。

### 1.4 補足：非連結 K の登録（要約の問題 7）— 訂正（11-11）

**構成そのものは大部分できている**（最初の下書きの「未着手」は誤り）。`KST/NonConnective/`（約 250 ファイル、L10 の K-7）に BGT Def 9.6 の形 `dgNonconnectiveK = colim_n Ω^n K(Σ^n Perf A)` があり、実 Sp 余極限と `IsColimitCone`、全整数 π の余極限、連結比較（`DGNonconnectiveKConnectiveComparison`）、零の保存（`DGNonconnectiveKZero`）、段ごとの Morita 射の保存（`DGNonconnectiveKMorita`）、K-6 の連結版 fibration の末尾への代入（`DGNonconnectiveKFibrationTail`）まで、標準三公理で監査済み（10-28 停止時：266 モジュール・2,950 宣言）。`DGSwindleFixedK` は BGT Lem 9.4 を引く。

**未完なのは L10 の d3〜f**：d3（Sp 安定性への接続、Sp-2 の B の後）、d4（大きい Ind／κ-compact・商／冪等完備化の ∞ 側比較）、e（非連結化の後の Verdier の fiber 性・Morita・filtered 保存）、f（固定 ν への局所化不変量の登録）。L10 は d4〜f を「**∞ 側再設計の後**」と明記している。つまり要約の問題 7 は、**③・① の部品（Ind・κ-compact の ∞ 圏としての扱い、Verdier 商 M1〜M8）を待っている**状態で、K 基盤 1（B-3）の中では最初に片付く。§3 の表の Ind・表現可能（◎）と Verdier 商（①）の行がこれに当たる。

### 1.5 凍結したコードの扱い

| コード | 中身 | 要るか |
| --- | --- | --- |
| L2（`KST/Comparison`、plus 構成との比較） | ĜL、群完備化、Prop 2.15 | §1.2 (a)・§1.3 (a) の切り出し部分だけ。全部は要らない |
| L6（`KST/ProExcision`） | pro 形式（Tower、IsProEquivalence、IsProCartesian）、Koszul の 4.9・4.10、Claim 4.15・Lemma 4.16、Appendix A | **pro 形式と 4.9・4.10 は要る**（決定 D5、§1.1 (c)）。群ホモロジーの部分（4.14〜4.19、App. A）は要らない |

**提案**：L6 のうち pro 形式と Koszul の塔を `KST/ProExcision/` から新しい場所（`KST/Pro/` または `HomologicalAlgebra/Pro/`）に移して凍結解除する。群ホモロジーの部分は Archive へ。L2 は §1.2・§1.3 の結論が出てから切り出す。

## 2. `[ModelCategory SSet]` を仮定する降下の作り直し

### 2.1 現状

- `KST/Descent/` の 54 ファイル（L8 §70〜99）が `[ModelCategory SSet.{0}]` を変数に取る。この instance は合成できない（`kanQuillenModel` は sorry の存在入力からの局所選択で、大域 instance ではない。`research/k-coverage/maps/kst/model-category-evidence.json`）。
- 決定 15（10-19）で主経路から外し、`Descent.Main` は旧 56 モジュールを import しない。`Descent.Auxiliary` が持つ。root の集約は Main だけを public import。主定理の閉包（1,142 モジュール）に `KST/Descent` は 0。
- つまり**今の主経路に穴はない**。作り直すのは、L8 の残り（Tot・homotopy 極限を使う Čech 降下の本体）を主経路の側で書くとき。

### 2.2 何を作り直すか

L8 の引き継ぎ（`kst-lanes/L8-descent.md`）の「残り」がそのまま作り直しの一覧。主経路の Tot・homotopy 極限は L9 の実構成（`CosimplicialTotalization`、`PointedHomotopyLimit`・`PointedWeightedEnd`）と整数次数の π_* で述べる（決定 15）。

| 残り（L8 の見積もり） | 補助側（ModelCategory SSet）でどう示していたか | 主経路での置き換え |
| --- | --- | --- |
| Fubini・引き戻しの交換（Lemma 3.2・3.3） | モデル圏の homotopy 極限の一般論 | ③ の G8・G9（∞ 層の極限の交換）か、L9 の実 Tot の Fubini を直接 |
| extra degeneracy から増大 → 実 Tot の π_* 同型（Lemma 3.2） | 同上 | 余単体的対象の extra degeneracy は 1 圏の議論。BS-W12 の B1（`HomologicalAlgebra/Cech/`、`isCechExact_of_retraction`）と同じ形で Kan 複体の Tot に |
| 随伴の添字変更・細分の各段（Lemma 3.2） | 同上 | ∞ 圏の cofinality（Kerodon 7.2）。③ の範囲 |
| Sp 上の transfer、各次数の局所 rank、有限平坦 Čech 降下（Lemma 3.2） | — | K 固有。B-5 |
| 実 fiber・自然 LES から `NaturalBlowupSequences` への接続（Lemma 3.3、Thm 3.1） | — | B-5 |

**方針の案**：補助側の 54 ファイルは、主経路に取り込まずに **Archive へ移す**（決定 15 では「比較用の補助として保持」だったが、主経路の実 Tot の構成が済んだ今は比較にも要らない）。主経路の残りは、上の表の「置き換え」の列で ③ に頼むものと B-5 で書くものに分ける。

### 2.3 ∞ の基盤に求めるもの（この部分から）

- 余単体的な Kan 複体（点つき）の Tot が ∞ 極限であること（L9 の `CosimplicialTotalization` と ③ の G10 の Kan 複体版）。
- Tot の Fubini と引き戻しの交換。
- cofinality（添字の変更）。

## 3. ∞ の基盤への注文（③・① の範囲に入れるもの）

K の経路 §7 の表（F0〜F3）を、今の ③・① の項目に当てはめ直したもの。BS が要るものと重なるものに ◎、K だけが要るものに ○。

| 部品 | K の使い所 | 今の担当 | 印 |
| --- | --- | --- | --- |
| 関手 ∞ 圏の極限、Fun の極限（HTT 5.1.2.2） | S• 構成の gapped 対象、Thm 3.1 の Sp 値の主張 | ③（G8・G9 の前提） | ◎ |
| 余単体的対象の Δ 上の極限（G10）、Kan 複体版の Tot | §2.3、Čech 降下 | ③（G10。BS-W16 の注意：全関手版、射と指定錐まで） | ◎ |
| ∞ 層と層化、極限の交換（G8・G9・G14） | Zariski 降下、Fubini | ③ | ◎ |
| cofinality（Kerodon 7.2） | 添字の変更、pro 対象の対角（決定 D5） | ③（追加） | ○ |
| Ind・表現可能・κ-compact（F2） | 非連結 K（BGT §9、Calkin 圏 Ind(𝒞)^{ω₁}/𝒞） | ③ の G12 の前提（`F2/Presentable` は本体にある） | ◎ |
| 安定 ∞ 圏の Verdier 商（M1・M2・M7）、商の関手性（M8）、Karoubi 列、Thomason–Neeman | K 基盤 1 の入口（B-3）。局所化不変量の定義 | **①**（止めてある） | ○ |
| 安定 ∞ 圏の Ind と presentable（M9〜M11） | 非連結 K、Thomason–Neeman | ① | ○ |
| hammock 局所化の一般論（M11） | dg 圏の局所化を ∞ 圏に | ①（EInfinity の `SimplicialLocalization` に実装がある。R65 で移す） | ◎（BS の CAlg_R も使う） |
| S• 構成の低次の計算（K₀・K₁、Waldhausen 1.5.9・2.3.2 の ∞ 版） | §1.2 の 1 連結性、K0 界面の項目 6 | **新規**（① の後。K 基盤 1 の一部） | ○ |
| Sp（安定 ∞ 圏としての Sp、Ω スペクトル、fiber 列、長完全列） | K の値域、hG、Tot（決定 3、γ-B） | **担当なし**（`KST/Spectra` に γ の実装。infinity-foundation-plan §108「安定性が無条件になるまで KST/Spectra に置く」） | ○ |
| 対称モノイダル ∞ 圏、E∞（F4） | K では不要 | ④ | — |

**提案**

1. ③ の指示書に、◎ の項目について「K の使い所」を注記として足す（③ の範囲は変えない。G10 の全関手版は BS-W16 の注意で済み）。cofinality（Kerodon 7.2）は ③ の段 5 以降に足す。
2. ① の再開を「③ の後」から「③ の G8 の後、④ と並行」に早める案を検討する。理由：① は BS には要らないので今は止めてあるが、K の再開の前提の中で一番大きい（M1〜M11、約 2〜4 万行）。E∞ の作り方の決定（HA の方向か）が ① の M11（hammock）にも効くので、その決定の後がよい。
3. Sp と S• 構成の低次の計算は、K 基盤 1（B-3）の最初の仕事として、K の再開時に新しいレーンを開く。

## 4. 決定（2026-11-11、ユーザー）

1. §2.2 の「`[ModelCategory SSet]` を仮定する降下の補助側 54 ファイルを Archive へ移す」案を採る。実施は KL-W1 の段 3 の取り込みの後の小さな整理で（`Descent.Auxiliary` の集約と監査の登録を外す。主経路は変えない）。
2. §3 の提案 2（① ∞ 中核の再開を「③ の G8 の後、④ と並行」に早める）を検討対象にする。実際に動かすのは E∞ の作り方の決定（HA の方向か）の後。
3. §1 の紙の確認は読み取りのエージェントに頼む（1.1 (c) と 1.3 (d) を先に）。

## 5. 進め方

1. §1 の三つの穴について、紙で確かめる項目を `k-theory-kst-route.md` §10 の形で書き足す。調整役が BS・KL-W1 の検収の合間に行う（読み取りのエージェントに頼める所は頼む）。
2. §2.2 の「Archive へ移す」案と §3 の提案 1〜3 をユーザーと決める。
3. 決まったものは K の経路 §13 に決定として足す。
