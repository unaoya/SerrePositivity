# K 理論の再開に向けた紙の作業（たたき台、2026-11-11）

作成：段階 II の調整役。決定：ユーザー（11-11、「K は ∞ 圏の基盤が整ってから着手。それまでに紙の作業 1〜3 を進める」）。材料：K の地図の要約（`research/k-coverage/maps/summary.md`、全 17 文献 688 項目を Lean の型で確認）、K の経路（`archive/stage-i/kst-lanes/k-theory-kst-route.md`、計画 v2 と決定 1〜16）、段階 II の計画 §2（B-1〜B-6）。

本書は相談用のたたき台。確定したものは K の経路の §13 に決定として足し、本書は残りの論点だけを残す。

## 0. 要約

- K の実装は ∞ 圏の基盤（KL-W1 → ③ → ①）が整ってから。それまでは本書の紙の作業。
- 照合で分かった計画の穴は三つ（§1）。11-11 に紙で確かめて経路を確定：§1.1 は 4.8 を LT 2.31（Lean 既存）に置き換え、§1.2・§1.3 は L2 の部分解凍（plus 構成・Serre SS・Prop 2.15、240〜640 時間）に収束。どれも ∞ の基盤とは別の、K 基盤 1 の仕事。
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

**結論（確定、11-11、読み取りのエージェントが KST pp.21–24・32–36、LT pp.24–28、Lean の型を照合。鍵の宣言の型は調整役が確認）**：

1. **(c) は「4.8 を不要にする」案としては不成立**。Ko(A; a(n)) → A/a(n) はレベルごとの擬同型ではない（a(n) が正則列でなければ H₁ ≠ 0）。Koszul cdga の模型でも D(n)∩U_i ≅ (E(n)∩U_i) ⊗_A Λ_A(e_1..e_r)（微分 0 の外積代数）で、π_* が余分に出る。遷移が m ≥ 2n で e_j を殺すので pro 同値にはなるが、レベルでは同値でない。したがって「π_* の塔が pro 同値 ⇒ K の塔が pro 同値」という **4.8 の強さは 5.5 (i)(iii) の両方で本質的に要る**。
2. **ただし 4.8 は LT Cor 2.31 に置き換えられ、Lean に既にある**：`IsKConnective.invariantLevelMap_piProEquivalence_of_piProEquivalence`（`KST/LocalizingInvariants/DGAlgebraInvariantPiProEquivalence.lean:36`、`IsPiProEquivalence R (f.map (nonpositiveInclusion R)) → ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ …)`、前提 `IsKConnective R Φ k`）。これは LT Lemma 2.28 (ii) の Postnikov 帰納 ＋ 2.30 で、決定 16（群ホモロジーを使わない）と整合する。前提の `IsKConnective` は §1.2 で供給する。
3. **Lemma 4.1 と 4.10 のスペクトル系列の証明は不要**：`koszul_comparison_isProIso`（`KST/ProExcision/KoszulComparison.lean:38`）は任意の複体 K（ホモロジー有限生成）に対する 4.10 なので、K ＝ 導来チャートの複体 B_i に a(n) と (a_iⁿ) の二通りで当て、H⁰ で (a(n)) = (a_iⁿ) だから商塔がレベル同型、で (iii) のチャート版が出る。(i) は K = A。
4. **下書き (a) の「非 connective な場合」の難点は誤り**：単体環は常に連結で、A → π₀A も連結環同士。非連結なのは K の側だけで、それは `IsKConnective` で処理される。
5. **5.5 (ii) は置き換え不可**：K(X̃)（導来 blowup）と K(tX̃) を結ぶ唯一の箇所で、Thm A の最後で Prop 5.2 に渡すために必須。要るのは、pro 切除 2.32/2.35（⊙、決定 16）を各チャート B_L → π₀B_L に当てる形（仮定「{a(μ)π_iB_L} = 0 (i > 0)」は π_i が有限生成で a 冪で消えることから自明）、fiber の同定（Lemma 4.6 ＝ `IsProCartesian`）、2.31（上の補題）、有限 Čech 図式での pro 版 Zariski 降下（`FiveTermHom.isProIso` の反復）。

**再定式化（新しい数学はない、接続補題だけ）**：Koszul cdga の塔を `Tower (NonpositiveAlgebra R)` に、比較射を `LevelHom` に；`groups R j` の塔と `koszulConeTower` のホモロジー塔のレベル同型（`of_levelwiseIso`、Pro.lean:205）；j ≠ 0 で「始域 pro 零 → 零塔への射は IsProIso」；有限 Zariski 図式ごとの結果を貼る pro 版 Čech；二重添字 (m,n) は `reindexHom_isProIso`・`diagonal_cofinal` で対角に（決定 D5）。

**K 側の最小の入力（§1.1〜1.3 を合わせて）**：
1. `IsKConnective R Φ 1` を K について証明（§1.2 → L2 部分解凍）。
2. pro 切除 2.32/2.35（⊙）を B_L → π₀B_L に当てられる形（決定 16 の B-4 の範囲）。
3. 有限アフィン被覆の Zariski/Čech 降下（Thm 2.12）の pro 版。

### 1.2 K の 1 連結性（要約の問題 2）

**何が穴か**：Land–Tamme の Thm 2.32（pro 切除）を K に当てるには、K が「1-connective な不変量」（LT Lemma 2.4、Example 2.6 (i)）であることが要る。Lean の 2.31 は `IsKConnective` を**仮定**しているだけで、K 自身がそれを満たす証明はどの計画にもない。LT の証明は plus 構成（K_1 = GL/E）による。plus 構成は L2 として凍結中。

**候補**

| 案 | 中身 | 難点 |
| --- | --- | --- |
| (a) L2 の一部を凍結解除 | 1 連結性に要るのは「connective な環 A について K(A) → K(π₀A) が 1-connective」で、その証明は K₀・K₁ の比較（Thm 2.16 の n ≤ 1）。L2 の全部（plus 構成との比較 Prop 2.15）は要らない | L2 のどの部分が要るかの切り出し。KST Thm 2.16 は BGT 9.53 にも別証がある |
| (b) BGT 9.53 で K₀・K₁ の比較を出す | 非連結 K を BGT で定義する（決定 2 (a)）なら、9.53 の議論（Waldhausen の S• の低次の計算）が使える | BGT §9.3 の非連結 K の登録（§1.4）が先 |
| (c) 1 連結性を仮定（界面）にして第 1 段を閉じる | `IsKConnective K` を K0 界面の一欄にする | 段階 II の終わり条件（sorry 0、引用なし）に反する。採れない |

**訂正（11-11、BGT v4 と LT の本文で確認）**：(b) は成り立たない。BGT Thm 9.53 は「connective な R について **i ≤ 0** で π_i IK(R) ≅ π_i IK(π₀R)」であり、証明は §9.5（EKMM の行列環、Prop 9.40 の BGL(R)⁺）を経由する。LT Lemma 2.4 自身も、非正次数を 9.53 で済ませ、正次数は plus 構成（「Ω^∞₀ K(A) ≃ BGL(A)⁺、[BGT13, Lemma 9.39]」）と Serre 類の Whitehead で示す。しかも Def 2.5 の「Λ-1-connective 不変量」は全 n についての (n+1)-連結性なので、**次数 ≤ 1 の比較（KST 2.16）では足りない**。

**結論（確定、11-11）**：1 連結性は **L2 の一部の凍結解除**でしか得られない。要るのは L2 の残り 1〜3（plus 構成の実体：セル添付・π₁ の商・ホモロジー同値）、5（Serre/Hurewicz 型スペクトル系列）、6（Prop 2.15 ＝ Ω^∞K ≃ K₀ × BGL⁺ の ∞-S• との接続、K-L1 待ち）。4・7（K₀/K₁ 比較、Bass）は不要。L2 の見積もり：240〜640 時間。§1.3 と同じ部品なので、まとめて一つの「L2 部分解凍」として扱う（§1.5）。

### 1.3 冪零不変性（公理 (3)、要約の問題 3）

**何が穴か**：論文は E = fib(K_ℚ → K[1/p]_ℚ) の冪零不変性を truncating 性（Goodwillie）から得る。計画 v2 はこれを D9（離散結合環 R と冪零イデアル I について、中間環 R̃ = R[1/p] ×_{S[1/p]} S を挟み、GL の有理ホモロジーの比較で K_ℚ の同型を出す）で置き換えた。D9 の Step 2 は GL・plus と有理ホモロジーの比較を使う。これも L2 の凍結部分に当たる。Lean の `Nilinvariant` は前層に課す条件で、係数つきの L がそれを満たす証明はない。

**候補**

| 案 | 中身 | 難点 |
| --- | --- | --- |
| (a) D9 のまま、L2 の有理ホモロジーの部分を凍結解除 | 決定どおり | §1.2 (a) と同じ切り出しの問題。L2 の規模（plus 構成）が大きい |
| (b) Land–Tamme Thm 3.5（truncating な不変量の冪零不変性）を使う | 論文の経路。E が truncating であることは Goodwillie（K → HC⁻ の相対比較）に依る | Goodwillie を形式化する規模が大きい（計画 v2 が避けた理由） |
| (c) 有理化した K の冪零不変性を、Weibel の「K_ℚ(R) → K_ℚ(R/I) は I 冪零なら同型」（Goodwillie 1986 の有理版）の**代数的な証明**で | 原典は Goodwillie "Relative algebraic K-theory and cyclic homology" Main Theorem。有理の場合は Hochschild・巡回ホモロジーの比較で、位相的な入力が少ない | Goodwillie の定理そのもの。規模は (b) と同程度 |
| (d) ⑥ の BS17 と同じ手で、Zariski 局所的に被約化と同型になるように E の定義を変える | 使う側（論文 Thm 3.1 の証明）が冪零不変性をどこで使うかによる。軌道の議論の V ↪ X ×_S Y（被約化）だけなら、E を「被約化で不変になるように定義し直す」ことで回避できる可能性 | 論文の主張の形が変わる。紙で確かめていない |

**結論（確定、11-11、読み取りのエージェントが論文 §3 の本文と Lean を照合）**：

1. **(d) は不成立**。論文 §3 で冪零不変性を使う箇所は六つあり（§3.1 末の宣言、Lemma 3.3 の被約化、Thm 3.1 の基底の被約化、V ↪ X ×_S Y、V ×_Y Z ↪ X ×_S Z、そして LT Thm A.2 の内部）、幾何の側は L_red(Y) := L(Y_red) で全部通る。壊れるのは**公理 (2) の供給**：計画 v2 は KST Thm A（pro-cartesian、E(Y_n) は実際の無限小 thickening の値）から「"lim" E(Y_n) が定数」で実降下を出すが、これは離散環 R と冪零イデアル I について E(R) ≃ E(R/I)、つまり D9 そのもの。L_red に替えても同じ主張が (2) の供給に残る。
2. **副産物：Lean の公理 (3) は公理 (2) から導ける**。`AbstractBlowupSquare`（`KST/Descent/BlowupGeometry.lean`）は「中心が空や全体の場合も許す」ので、冪零 thickening i : Z ↪ Y の退化した正方形 (Z, Z, Z, Y) が抽象 blowup 正方形になり、`NaturalBlowupSequences` の Mayer–Vietoris 列から `pullback_bijective` が出る。K の再開時に `Nilinvariant` の class を (2) からの定理に落とす（Axioms.lean の公理を一つ減らす）。
3. したがって残る選択肢は (a)（D9 のまま、L2 の plus・Serre SS・Prop 2.15 を解凍）か (b)/(c)（Goodwillie）。**(a) を採る**。§1.2 と同じ L2 の部品で済む。D9 は離散環なので ĜL の dg 部分は不要。
4. Lean 側の使用（確認済み、主経路、sorry 0）：`Nilinvariant.piDescent_iff_reduction` は外側の次元帰納の一段で一回、`piDescent_iff_reducedSource` は軌道論法で三箇所。`piDescent_iff_thickening_baseChange`・`affineReduction_pullback_bijective` は主経路から未使用。

### 1.4 補足：非連結 K の登録（要約の問題 7）— 訂正（11-11）

**構成そのものは大部分できている**（最初の下書きの「未着手」は誤り）。`KST/NonConnective/`（約 250 ファイル、L10 の K-7）に BGT Def 9.6 の形 `dgNonconnectiveK = colim_n Ω^n K(Σ^n Perf A)` があり、実 Sp 余極限と `IsColimitCone`、全整数 π の余極限、連結比較（`DGNonconnectiveKConnectiveComparison`）、零の保存（`DGNonconnectiveKZero`）、段ごとの Morita 射の保存（`DGNonconnectiveKMorita`）、K-6 の連結版 fibration の末尾への代入（`DGNonconnectiveKFibrationTail`）まで、標準三公理で監査済み（10-28 停止時：266 モジュール・2,950 宣言）。`DGSwindleFixedK` は BGT Lem 9.4 を引く。

**未完なのは L10 の d3〜f**：d3（Sp 安定性への接続、Sp-2 の B の後）、d4（大きい Ind／κ-compact・商／冪等完備化の ∞ 側比較）、e（非連結化の後の Verdier の fiber 性・Morita・filtered 保存）、f（固定 ν への局所化不変量の登録）。L10 は d4〜f を「**∞ 側再設計の後**」と明記している。つまり要約の問題 7 は、**③・① の部品（Ind・κ-compact の ∞ 圏としての扱い、Verdier 商 M1〜M8）を待っている**状態で、K 基盤 1（B-3）の中では最初に片付く。§3 の表の Ind・表現可能（◎）と Verdier 商（①）の行がこれに当たる。

### 1.5 凍結したコードの扱い

| コード | 中身 | 要るか |
| --- | --- | --- |
| L2（`KST/Comparison`、plus 構成との比較） | ĜL、群完備化、Prop 2.15 | §1.2 (a)・§1.3 (a) の切り出し部分だけ。全部は要らない |
| L6（`KST/ProExcision`） | pro 形式（Tower、IsProEquivalence、IsProCartesian）、Koszul の 4.9・4.10、Claim 4.15・Lemma 4.16、Appendix A | **pro 形式と 4.9・4.10 は要る**（決定 D5、§1.1 (c)）。群ホモロジーの部分（4.14〜4.19、App. A）は要らない |

**提案（11-11 更新）**：
- L6：pro 形式と Koszul の塔を `KST/ProExcision/` から新しい場所（`KST/Pro/` または `HomologicalAlgebra/Pro/`）に移して凍結解除する。群ホモロジーの部分（4.14〜4.19、App. A）は Archive へ。
- L2：§1.2・§1.3 の結論により、**残り 1〜3・5・6 を一つの束「L2 部分解凍」として K 基盤 1（B-3）の中で行う**（4・7 は不要）。L2 の現状：352 ファイル・32,981 行・sorry 0・`ModelCategory SSet` なし・主経路の外（確認済み）。済んでいるのは Γ・ĜL、群完備化、Lemma 2.13、局所係数ホモロジーの長完全列。見積もり 240〜640 時間（K-L1 の ∞-S• の供給を待つ部分 6 を含む）。

## 2. `[ModelCategory SSet]` を仮定する降下の作り直し

### 2.1 現状

- `KST/Descent/` の 54 ファイル（L8 §70〜99）が `[ModelCategory SSet.{0}]` を変数に取る。この instance は合成できない（`kanQuillenModel` は sorry の存在入力からの局所選択で、大域 instance ではない。`research/k-coverage/maps/kst/model-category-evidence.json`）。
- 決定 15（10-19）で主経路から外し、`Descent.Main` は旧 56 モジュールを import しない。`Descent.Auxiliary` が持つ。root の集約は Main だけを public import。主定理の閉包（1,142 モジュール）に `KST/Descent` は 0。
- つまり**今の主経路に穴はない**。作り直すのは、L8 の残り（Tot・homotopy 極限を使う Čech 降下の本体）を主経路の側で書くとき。

### 2.2 何を作り直すか

L8 の引き継ぎ（`archive/stage-i/kst-lanes/L8-descent.md`）の「残り」がそのまま作り直しの一覧。主経路の Tot・homotopy 極限は L9 の実構成（`CosimplicialTotalization`、`PointedHomotopyLimit`・`PointedWeightedEnd`）と整数次数の π_* で述べる（決定 15）。

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
