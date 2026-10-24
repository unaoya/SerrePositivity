# 進捗チェックリスト v3（foundations.md §9 の本体、8 レーン、2026-10-24 13:50 改訂）

進捗確認では項目の完了（[x] と日時）を報告し、作業中の小項目に「← 今回」、前回の確認時に作業中だった小項目に「← 前回」を付ける（作業中の行は [ ] のまま）。
一段目・二段目はコーディネータが固定（本改訂）。三段目（必要なら四段目）は各レーンが二段目の項目に着手するときに 3〜8 個で提示し、コーディネータがここに固定する。以後は印だけが動く。
v2（10-19〜10-24 13:30）の完了項目は末尾「確定済み」に圧縮して残す。旧チェックリストの全文は git 履歴（4466c8c87 以前）。

**Ind（旧 F1＋F1b。所有：F1/（Cocartesian は休止）、F1B/、F2/Ind・FilteredExchange・Compact・Idempotent）**
- [ ] I-1 F2N-1 a7：一般の coherent filtered 図式に対する filtered 余極限と有限極限の交換の結論（HTT 5.3.3.3。**着手から 8 時間の上限**）
  - [ ] a. ApexRawTriangleCandidate_eq_universal_iff の右辺（元の普遍比較の値＝同じ四因子境界式）
  - [ ] b. 交換の結論の公開：CoherentFilteredLimitExchangeShape・IndFiniteLimitExchangeInput を仮定から定理へ
  - [ ] c. 上限を超えた場合の確定：明示入力のまま第 I 段を進め、差し替え（I-2 d・N-6 c）は第 I 段終了時へ
- [ ] I-2 F2N-5 Ind(C) の安定性と compact 生成（HTT 5.3.5.15、HA 1.1.3.6）
  - [ ] a. 有限 poset の nerve 上の図式の単一 filtered 表示の結論（κ-filtered 性は 10-23 09:32 に証明済み）
  - [ ] b. 小さい安定 C に対する Ind_κ(C) の有限余極限・有限極限の存在（零対象は済み）
  - [ ] c. Ind_κ(C) の安定性（fiber = cofiber）と包含 C → Ind_κ(C) の完全性
  - [ ] d. 交換入力の実証拠への差し替えと、compact 対象の有限余極限閉性（旧 N-6 c）の無条件化（I-1 の後）
  - [ ] e. 冪等完備な C の compact 生成 Ind_κ(C)^κ ≃ C の仕上げと公開界面（K-B の K-7 d へ提供）

**P（旧 N＋P。所有：F2/Presentable、HomotopyLimits）**
- [ ] P-1 presentable ∞ 圏（HTT 5.4〜5.5）
  - [x] a. accessible ∞ 圏と Ind_κ(C₀) との同値、accessible 関手、濃度変更（10-23 08:48）
  - [ ] b. presentable の定義と前層の presentable 性（小さい compact 生成圏、accessibility、Ind_κ(C) の presentable 性、局所小ささ。5.5.1.1、5.5.1.8）
  - [ ] g. P_Σ の普遍性と sifted 余極限による生成（5.5.8.14〜15。N の未接続 7 ファイルを F2/Presentable の新所在へ置き直してから）
  - [ ] c. presentable の小さい極限・余極限（5.5.2.4、5.5.3.13）
  - [ ] d. 随伴関手定理（5.5.2.9）
  - [ ] e. Pr^L と Pr^R の双対性（5.5.3.4）
  - [ ] f. Bousfield 局所化の存在（5.5.4.15。N の局所対象・強飽和性・条件付き反射を再利用）

**D（所有：Stable、Derived（Gluing 以外）、DGNerve、DoldKanComparison、DifferentialGraded）**
- [ ] D-7 Sp への判定補題：HA Cor. 1.4.2.27 (3) ⇒ (1)（a〜c は 10-22 完了）
  - [ ] d. IsStable の結論と Sp の nativeLoop への適用（残りは loop 同値からの安定性定理の結論。excision 格子・懸垂四角形・θ 辺の同定は 10-24 までに完了）
- [ ] D-8 K-7 供給：正則非可算 κ に対する `DGKappaConeInput R D κ` の実例（HTT 5.3.4・5.4.2。D-7 d の後）
  - [ ] a. 射影閉包・可算直和と二項直和の閉性・perfectCovers（43 宣言は 10-23 に構成済み。本体への統合）
  - [ ] b. pretriangulated：選んだ代表系の全 Hom dg 模型の前三角性
  - [ ] c. kappaCompact：各代表の F2.Compact.IsKappaCompact による κ-compact 性
  - [ ] d. covers：全 κ-compact 頂点の代表による被覆
  - [ ] e. DGKappaPerfectInput と dgKappaConeDerivedComparison_isFullyFaithful の供給、K-B への引き渡し
- [ ] D-9 β4 の D 側共同分：平坦 Drinfeld 商と実 Verdier 列の供給（D2 の f と共同）。D2 完了後は Gluing を吸収
- 第 I 段終了時：Derived の型依存の準重複 19 組（archive/refactor-near-duplicates-derived-2026-10-23.md）の統合判断

**D2（所有：Derived/Gluing）**
- [ ] G-1 β4 dg gluing = 安定 ∞ 圏の lax pullback（Tamme 2018 §1。a〜c は 10-22 完了）
  - [ ] d. 比較の充満忠実性・本質的全射性と ∞ 圏的普遍性（未接続 CoefficientYonedaInverseChainMap の修正 → 正本比較の実ホモトピー逆 → 同値）
  - [ ] e. 安定性・完全射影の供給と F2 の laxPullback_isStable・K-8b の半直交分解との整合（Tamme Lemma 8）
  - [ ] f. gluing 内の通常 pullback と Verdier 商 ⊙ の dg 側の同定、K-8 d8 への IsVerdierSequence の供給（D と共同）

**E2（所有：EInfinity）**
- [ ] E2-7 CAlg_R := N^hc、U : CAlg_R → D(R)、離散対象（a〜f は 10-22 完了）
  - [ ] g1. 離散対象：列の cofibrant 相対圏への持ち上げ、CAlg_R の全 pinched 族への送り、標準単位比較自身の弱同値性
  - [ ] g2. 単位 comma 候補の実始対象性から全 ∞ 随伴、U の任意 coherent ∞ 極限保存（HTT §5.2.4）
- [ ] E2-8 G1′：BS の界面を CAlg_R で述べ直し、実 U・離散比較・極限保存を代入。D(R) 版を系として導出
- 完了後は停止。BS-7（animated 環、Construction 7.6）は第 II 段。EInfinity の型が異なる準重複（archive/refactor-near-duplicates-einfinity-2026-10-23.md）は第 I 段終了時

**Sp（所有：KST/Spectra、KST/LocalizingInvariants。局所化・分数・Verdier 商の API の正本）**
- [ ] K-9 β6 dg 代数のホモトピー論（a〜e は 10-22 完了）
  - [ ] g. LT Lemma 2.30・Cor. 2.31：不変量の値の塔の次数ごとの eventual 連結度から π-pro 同値（残り：W source の Γ への前合成以降）
  - [ ] f. homotopy pullback：平方零微分摂動による Postnikov 拡大の普遍性
  - [ ] h. 提供界面の記録（L9-spectra.md「主要宣言」）
- [ ] K-8 K-基盤 2 の抽象部分（a〜c・d1〜d6・d8・f′ は完了、d7 は停止）
  - [ ] e. pro 版：τ≥−n への積の降下と Postnikov 代数切断、pro fiber の連結度判定、Tor の pro 消滅から pro 切除の抽象形（LT §2.4 Lemma 2.30・Cor. 2.31、§3）
- [ ] Sp-6 他レーンからの依頼：K-B の分数比較の充満忠実性、K-S• の S 内零化 2-cell・具体的長方形
- Sp-5 d3（Sp の IsStable）は D-7 d の判定補題で閉じる（Sp は適用のみ）

**K-S•（所有：KST/SConstruction。S• 界面の正本）**
- [ ] K-10 Land–Tamme の ⊙ の dg 側構成と主定理界面（a・b は 10-22 完了）
  - [ ] c. 対角像の商 End と元の右対象 End の比較（残り：角から小模型への Yoneda の Morita 不変性、商 End の同定）
  - [ ] d. β3 の Verdier 列による K-8 d8 の仮定入力 IsVerdierSequence の充足（D2 の f と接続）
  - [ ] e. Land–Tamme 主定理の Cat^perf 版の結論（Sp の K-8 d8 と接続）
- pro 版の dg 側（Tor の環論は L7、第 II 段）

**K-B（旧 K-F＋K-7。所有：KST/Fibration、KST/NonConnective）**
- [ ] K-6 fibration 定理（a は 10-22 完了）
  - [ ] c. cofinality 条件と K-S• の S• 界面との接続（残り：relabelEnrichedObjects による座標読み替え → 商実現比較 → 無条件の連結版）
  - [ ] b. S•(C, W) の相対構成と加法性からの連結版（c と独立。c の後に統合）
  - [ ] d. K(D) → K(C) → K(C/D) の fiber 列（連結版、Sp 値。相対 Verdier 四角形を実 Sp fiber 四角形へ）
  - [ ] e. 冪等完備化と BGT §9 の非連結化への入力の整理
- [ ] K-7 非連結 K（a・b は 10-23 完了。b の I・P は D-8 の供給を待つ明示入力）
  - [ ] c. 反復懸垂と K^{nc}(A) := colim_n Ω^n K(Σ^n Perf A)（dgKappaZeroPerfAction_values → 同じ cone の連結 K の消滅 → 構造射）
  - [ ] d. 連結 K との比較（非負次数の同型、負次数の記述。Ind 側の I-2 e と照合）
  - [ ] e. Verdier 列を fiber 列へ（K-6 使用）、Morita 不変性、filtered 余極限との可換
  - [ ] f. Sp の IsRelativeLocalizingInvariant への登録（固定 dgKInputInfinity・dgKInputNu・dgKInputK）

**R（常設しない。第 I 段終了時の停止窓で実施）**
- [ ] KST/Spectra の基盤部分（BF 模型など）を InfinityCategories へ降ろし、InfinityCategories → KST の import 31 本を解消
- [ ] 型の異なる準重複の統合（D・E2 の差分表に従う）、R21 docstring、R4 粒度、R5 双対化、R10 計算規則
- [ ] 全体の入口・README・監査スクリプトの再点検、解説（exposition/ja/infinity）の基準コミット更新

**第 II 段（予告。第 I 段の K 側と BS 側が閉じてから起動）**
- K の代数幾何：Perf(X) の dg 増強（L4）、導来 blowup（L5）、スキーム補題・可換環論（L7）、降下（L8）、合流（K0 界面）
- BS-7：animated 環（P_Σ と E2c）、Construction 7.6、界面の文献どおりの述べ直し

---

## 確定済み（v2、2026-10-19〜10-24 13:30）

- F1：F1-1 straightening（空間値、a〜c。d の Cat∞ 値は全有限単体底まで、一般底は第 II 段）、F1-2 Yoneda（10-21 05:02）、F1-3・F1-3b twisted arrow と Hom 関手（12:24）、F1-4 前層の極限・余極限（10-22 12:02）、F1-5 表現可能関手による特徴づけ（12:24）、F1-6 F2N-2 Ind_κ(C)（10-23 02:30）、F1-7 c compact 生成の同定（05:31）。
- F1b：F1b-1 B4 Kan 拡張（10-19 22:44）、F1b-2 B5（10-20 01:51）、F1b-3 Cat∞（10-20 05:00）、F1b-4 Cat∞ の極限と lax pullback（10-20 07:42）、F2N-1 a1〜a6。
- N：N-1 γ3c（10-20 16:31）、N-2 γ4（10-21 08:31）、N-3 Sp への適用、N-4 a〜d、N-5 F2N-4 冪等完備化（10-23 05:05）、N-6 F2N-3 κ-compact a〜d（c の無条件化は a7 待ち）。
- P：P-1 a accessible（10-23 08:48）。
- D：D-1〜D-3 D7（10-19）、D-4 β3（10-21 03:28）、D-5 β5（10-22 18:50）、D-7 a〜c（10-22）。K-7 供給の 43 宣言（10-23〜24）。
- D2：G-1 a〜c（10-22）。
- E2：E2-1〜E2-4 E2a-3（10-20 10:04）、E2-5（10-20 22:48）、E2-6（10-20 14:40）、E2-7 a〜f（10-22 15:06）。
- Sp：Sp-1〜Sp-4（10-19）、Sp-5 a〜d2（10-20 23:39）、K-5 抽象部分（10-21 01:55）、K-8 a〜c（10-21 03:00）・d1〜d6・d8（10-22）・f′ 相対版（10-22 22:01）、K-9 a〜e（10-22 08:13）。
- K-S•：K-1・K-2（10-19）、K-3・K-4（10-22 14:37）、K-5 d Cat^perf（10-22）、K-10 a・b（10-22 19:21）。
- K-F：K-6 a（10-22 10:17）。K-7：a Sp の逐次余極限（10-23 07:04）、b dg 懸垂の明示入力版（08:40）。
- R：第 0〜1・5 段、R5 前半、R6・R7・R9 入口、R11、R12（R-A、タグ refactor-stage1-2026-10-24）、R15・R16・R17・R19・R20・完全一致部・互換入口 267 本（R-C、タグ stage2）、R24・Stable↔KST・Derived 準重複・R2・R3・R14・R22・R23（R-B、タグ stage3）。R13（F1B の役割別分類と kan 接頭辞整理）と PinchedInterval・scaffold の原本共用は R-A の最終ラウンドで完了（10-24 17:55、350301807、タグ refactor-stage4-2026-10-24。verify.sh 全緑 17:29）。
