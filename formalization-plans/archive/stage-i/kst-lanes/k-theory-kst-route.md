# K 理論（定理 3.1・補題 4.6）の完全証明計画：KST 経路と現代的な K

作成日：2026-10-18。状態：計画（引き継ぎ用）。Lean の実装はまだない。
作成元：本計画を検討したチャット（stage 4・dg の進捗確認と並行して、2026-10-16〜18 に読み取り専用の調査を実施）。
引き継ぎ先：BS 計画と ∞ 圏基盤を管理しているチャット。本文書はその管理下に移す。

対象とする版：主論文は [`paper/paper.pdf`](../../../../paper/SOURCE.md)（§3 定理 3.1・補題 3.2・3.3、§4 補題 4.2・4.6・定理 4.7）。
Kerz–Strunk–Tamme（KST）は arXiv:1611.08466v4（Invent. Math. 211, 2018）。
Land–Tamme（LT）は arXiv:1808.05559v3（Ann. Math. 190, 2019）。Thomason–Trobaugh（TT）は 1990 年の原論文。
Blumberg–Gepner–Tabuada（BGT）は arXiv:1001.2282。Waldhausen は LNM 1126（1985）。

既存の計画との関係：[k-theory-v1.md](../../k-theory-v1.md) の M3〜M10 の目標は維持する。本計画はその M6〜M10 の経路を
確定し、M4 の扱いを変える。[k-theory-v1.md](../../k-theory-v1.md) §159 の「∞ 圏は導入しない」は、
2026-10-17 の決定（[infinity-categories.md](../infinity-lanes/infinity-categories.md)）で改められており、本計画はその上に書く。
[bs-clmst-citation-elimination.md](../../bs-clmst-citation-elimination.md) は未採用であり、本計画はそれに依存しない。

---

## 0. 引き継ぎメモ（最初に読む）

1. **大前提**（ユーザー指定）：K 理論側（`theorem_3_1_K0`、`supportedRankK0_descent`）は完全に証明する。
   発表時に残してよい引用は BS の命題だけで、最終的には全部外す。主張と証明はできるだけ論文どおりにし、
   迂回は候補として提示して判断を仰ぐ。
2. **確定した経路**：Land–Tamme の ⊙（Milnor 切除）は使わない。cdh 降下は
   「KST Thm A（係数つき）＋ ⊗ℚ の完全性 ＋ 離散結合環の冪零不変性」で得る（§2）。
   K の定義は現代的（安定 ∞ 圏の ∞-S• 構成、dg nerve 経由で dg 圏に適用）。
   非連結化は既定 (a) BGT（Ind 完成後）、保険 (b) dg 側 Schlichting。K に依存する部分は界面に対して書く（§4 D1）。
3. **未決事項**は §9。特に ∞ 基盤の範囲（Ind・presentable まで入れるか）と γ の選択は、
   この計画の K1 と γ の着手に直結する。
4. **着手前に紙で確かめる項目**は §10。P1・P2 の「推測／再構成」部分である。
5. 規模の数字はすべて粗い見積もりで、桁の目安に過ぎない。

---

## 1. 目標と段階

| 段 | 到達点 | 残る引用 |
| --- | --- | --- |
| 第 1 段 a | 定理 3.1 を離散・A 平坦・可換係数 H = A で証明し、`theorem_3_1_K0` を置換 | perfectoid 側の BS のみ |
| 第 1 段 b | 定理 3.1 を離散・A 平坦・非可換係数 H = B_A = ∏M_{s_n}(A) で証明し、補題 4.6 を迂回（F5）して `supportedRankK0_descent` を置換 | 同上 |
| 第 2 段 | 補題 4.6 を原典どおりに形式化し、Goodwillie で E の truncating 性を示し、定理 4.7 を論文どおり（connective な H）に証明 | 同上 |
| 付随 | HT-KQ（`Inputs/Homotopy/KanQuillen`）は γ-B を採れば不要になる | — |

主張の忠実度：定理 3.1 は論文の形（全次数、(3.1) のスペクトルの同値と hG）で述べることを目標にする。
第 1 段では「全次数の π_* 同型 K_n^J(H)_ℚ ≅ (K_n^J(H ⊗ T)_ℚ)^G（n ∈ ℤ）」を主定理とし、
Sp の同値（hG）は γ の後に系として付ける（§9 の未決 3）。補題 4.6・定理 4.7 の主張は論文どおり。

---

## 2. 検証結果の要約（2026-10-16〜18、読み取り専用の調査）

### 2.1 A1：⊙ を避けられるか（原典側）

本文で確認した事項：

- **KST Thm A**：「任意の抽象 blowup 正方形 (1.1)（X Noether、X̃ → X 固有、Y ⊂ X 閉、X̃∖E ≅ X∖Y）について、
  非連結 K の pro-スペクトルの図式 K(X) → "lim"_n K(Y_n)、K(X̃) → "lim"_n K(E_n) は homotopy cartesian」。
  有限次元性・分離性は不要。**K 理論専用**（一般の局所化不変量については述べていない）。
- **Def 4.4**（pro の意味）：pro-スペクトルの射 f が同値 ⇔ 全 i で "lim" π_i が pro-群同型。
  正方形が homotopy cartesian ⇔ 左上が残りのレベルごとの holim と同値。Lemma 4.6：hofib(f′) → hofib(f) が同値と同値。
- 証明の部品：Zariski 降下（Thm 2.12、[CMNN Prop A.13]）、局所化（Thm 2.10、[BGT 9.8]）、
  K_n(A) ≅ K_n(π₀A)（n ≤ 1、Thm 2.16）、導来 blowup（Def 3.1、Lemma 3.6）、導来 blowup 降下（Thm 3.7 = Thomason の一般化）、
  射影束公式・Bass 基本定理（Thm 3.16・3.17）、Koszul ホモロジーの pro-消滅（Lemma 4.9・4.10）、
  **pro-切除（Thm 4.11、K 固有）**、Prop 4.8、抽象 blowup → 実際の blowup の帰着（§5.2、Raynaud–Gruson）、導来 blowup の塔（§5.3–5.4）。
- **LT Thm A.2** の証明で ⊙ を使う箇所は Step 1（閉被覆の Milnor 正方形に Thm 3.3）と Cor 3.5（冪零不変性）のみ。
  truncating の直接使用は Step 2 の導来 thickening の古典化（二か所）。LT は KST Thm A を引用せず再演している。
- **LT Lemma A.1(iii)**：「[KST18, Thm 3.7] の証明は任意の局所化不変量で通用する」。
- EHIK（2020）は LT（2019）より後。「cdh = Nisnevich + Milnor 切除」の形の定理は本文に見当たらない。

A1 の論法（LT Cor A.7 の逆向き）：

1. KST Thm A（係数つき）を正方形 Q と Q ⊗ ℚ（= Q[1/p]）に適用する。
2. ⊗ℚ は pro-アーベル群で完全。Pro(Ab) の五項補題で E = fib(K_ℚ → K[1/p]_ℚ) の正方形も pro-cartesian。
3. E が離散環で冪零不変なら "lim" E(Y_n) は定数 pro-対象 E(Y)。
4. 定数 pro-対象間の同型は元の同型。よって実際の降下。

E を導来環上で評価する必要はない（KST の主張は古典スキームだけで述べられている）。

### 2.2 A1：論文側（定理 3.1 の証明に現れる正方形）

| 箇所 | 正方形 | 判定 |
| --- | --- | --- |
| 補題 3.2 | Zariski 被覆、有限平坦 transfer、分裂 Čech（extra degeneracy） | 正方形は使わない |
| 補題 3.3：閉和 Y = Y₁ ∪ Y₂ | 抽象 blowup（Y₁ → Y は閉埋め込みで固有、Y∖Y₂ 上で同型、中心 Y₂、交わりは Y₁ ×_Y Y₂） | ✓ |
| 補題 3.3：平坦化 blowup {Y′ → Y, Z → Y} | 抽象 blowup | ✓ |
| 定理 3.1：軌道正方形 W = ⊔_I Y → V = (X ×_S Y)_red | 抽象 blowup（切断は閉埋め込み、有限、V∖(V ×_Y Z) 上で同型、G 同変）。Milnor 正方形ではない | ✓ |
| Y → Y_red、V ↪ X ×_S Y、V ×_Y Z ↪ X ×_S Z | 冪零 thickening | 離散の冪零不変性で足りる |
| (3.8) | 非交和上の積、有理 Shapiro | 純ホモトピー論 |

- 現れるスキームはすべて A 上有限型（Noether・有限次元）。
- E を評価する環はすべて H ⊗_A O(U)（U アフィン開）で、**H が A 上平坦なら離散**。
  論文の「B を π₀B に置き換えてよい」は LT B.3 のための主張で、§3 の証明本体では使われない。
- G 同変性は対象ごとの降下で足りる（BG 上の極限は引き戻しと可換）。
- τ 位相（cdh + 有限平坦）の層論は、Tot と引き戻しの Fubini、分裂余単体対象の降下、細分補題で置き換えられる。
  帰納法は「整 → 被約 → 一般」の順で回す。
- 定理 3.1 の証明が使う前層 L の最小公理：(1) Zariski Čech 降下（係数つき）、(2) 抽象 blowup の実降下、
  (3) 冪零 thickening 不変性、(4) 有限平坦 transfer（前層の自然変換、射影公式、trf∘f* = rank）、
  (5) 有理 G 固定点（自明作用で M ≃ M^{hG}、Shapiro）、(6) Fitting 版の平坦化 blowup、
  (7) スキーム補題（分離射の切断は閉埋め込み、等化子は閉、整スキームの真閉部分は次元が下がる、
  点全射な閉埋め込み＋被約 ⇒ 同型、有限 ⇒ 固有）、(8) (3.6) の同定（TT 局所化＋中心局所化の台判定、Y = S, X でのみ必要）。
  不要：Nisnevich、Milnor 切除、hyperdescent、truncating、cdh 層化、Grothendieck 位相。

### 2.3 G1：KST の K 固有部分の非可換・平坦係数への拡張

- LT 自身が Cor A.7 の直後で、KST Thm A の証明で K 固有なのは (i) Nisnevich 降下と導来 blowup 降下（任意の局所化不変量で成立）、
  (ii) KST Thm 4.11 の二つだけと明記。
- 環自身の **Noether 性**を使うのは Lemma 4.9・4.10（Koszul ホモロジーの pro-消滅）だけ。H が A 上平坦なら
  K(M ⊗ H; a(n)) = K(M; a(n)) ⊗ H で移る。
- **可換性**は Prop 4.14 の仮定文と Lemma 4.16 の等式 u⁻¹ψ(v)u = ψ(v)·φ(v) にしか効かない。
  行列計算では ψ(v)u = u + (va; 0) なので、恒等式は右乗法 v ↦ va で成立し、a が中心的なら左右の区別は不要。
  GL のホモロジーの議論（Claims 4.15〜4.19、App. A）は「単位的な環と中心的な非零因子」以外を使わない。
- KST は Thm 4.11 の直前で「Morrow・Geisser–Hesselholt の離散版は Suslin–Wodzicki に基づくが、我々の経路は Tor-unitality を使わない」と明記。
- **注意**：LT Thm 2.32（E₁ 版の pro-切除）は Thm 1.3（⊙）経由なので、置き換えに使わない。
- 係数版に必要な変更：(1) §2 を「B ⊗_A H 型の connective E₁ 環」で述べる、(2) 平坦底変換の補題群
  （π_*(B ⊗ H) = π_*(B) ⊗ H、Koszul ホモロジー・a(n)M・pro-零性の保存）、(3) Prop 4.14・Lemma 4.16 を
  「I 結合的、a 中心的な非零因子」で再述し、非零因子化は Ã_m ⊗ H（R[t] 上半自由置換）で行う、
  (4) Cor 4.12 は本文に証明がないので再構成する、(5) Thm 2.12・3.7 は係数つき局所化不変量として、
  (6) §5 は K(Spec B) → K(B ⊗ H)、K(X) → K(X;H) に置き換えて逐語的に通る、
  (7) ∏M_{s_n}(A) の A 上平坦性（Noether 環上で平坦加群の積は平坦、Chase。出典未確認）。

### 2.4 G2・G3：局所化不変量一般で通る部分と係数の dg レベルでの扱い

- **Perf(X;H) の定義**：D(X;H) := D_qc(H_X-Mod)（H_X = H ⊗_A O_X 加群層の複体で、O_X 加群としてコホモロジーが準連接）、
  Perf(X;H) := D(X;H)^c のアフィン dg 増強。LT Lemma B.2（Perf(X) ⊗ Perf(H) の ∞ 的テンソル）は不要。
  - T1：係数つきコンパクト生成。{P ⊗ H_X : P ∈ Perf(X)} が D(X;H) を生成（自由／忘却随伴、忘却は保存的で余極限を保つ）。O_X の場合は BvdB Thm 3.1.1。
  - T1′：「局所的に有限射影 H ⊗ O(U) 加群の有限複体」との一致（有限被覆の MV 帰納と Neeman Cor 3.2.3）。
  - T2：局所化。Perf_Z(X;H) → Perf(X;H) → Perf(U;H) は冪等完備化を除いて完全（Neeman Thm 2.1 = BvdB 3.2.1、D(X;H)/D_Z ≃ D(U;H)）。
    Toën「Derived Azumaya algebras」§3.2 が非可換 dg 係数で同じ道筋を書いている。
  - T3：切除と Zariski MV（TT 3.19・8.1 の係数版）、有限アフィン被覆の Čech 降下。
- **平坦性の使用箇所**：降下・局所化（T1〜T3）には不要。Hom 計算 RHom_H(P ⊗ H, Q ⊗ H) ≃ RHom_O(P, Q) ⊗_A H
  （Čech 複体 ⊗ H）と、H ⊗ O_X = H ⊗ᴸ O_X の保証に必要。台の判定 (3.6) は compact 性だけで出る。
- **KST §3 の係数版**：生成系を H_X̃、j_*H_E ⊗ O(−k) に取り替えて再証明する。O-線形な計算（基本ファイバー列、Rp′_*O = O、
  Lemma 3.11、3.12〜3.14 の Hom 計算）は ⊗H（平坦）で移り、形式的な部分（3.8、生成判定、Neeman 9.1.5、3.15、Thm 2.10、濾過）は不変量によらない。
- **導来スキーム**：Thm 3.7 が使う導来的道具は導来ファイバー積・アフィン射の底変換・射影公式・f̃* のモノイダル性のみ。
  Perf・K は E₁（dg 代数）構造にしか依存しない。simplicial 可換環は不要（ℤ_(p) 上で cdga ≠ 単体可換環でも支障なし）。
- **Drinfeld Prop 1.6.3**（確認済み）：𝒞 が h-flat なら (𝒜/ℬ) ⊗ 𝒞 ≃ (𝒜 ⊗ 𝒞)/(ℬ ⊗ 𝒞)。LT Lemma 3.12 の dg 版代替として十分。
- **Cor 4.13**（導来環 → π₀ の比較）は K 固有（pro-切除）で、局所化不変量一般では成り立たない。§5 で使うので B に含める。

### 2.5 P1：KST §2・§4 の詳細（K 固有部分）

- **モデルの橋渡し**：Schwede–Shipley の Quillen 同値（SS03 Thm 1.1(3)）は使わない。
  連結 dg 代数 A に対し ĜL_n(A) := ĜL_n(ΓA)（Dold–Kan の Γ、Alexander–Whitney のカップ積；SS03 Prop 2.13 の構成）で直接定義する。
- **Prop 2.15**（Ω^∞K(A) ≃ K₀(π₀A) × BĜL(A)⁺）：KST は [Wal85, 2.3.2] + [BGT13, 9.31/9.32] または [BGT13, 9.39/9.40] を引く。
  Waldhausen 2.3.2 の構成要素（本文確認）：(a) Prop 2.3.5（BĜL_k(R) ≃ |hM_k^n(R)|）、(b) Segal の群完備化＋plus 構成、
  (c) Prop 2.3.3（Thm 1.7.1 球状対象・セル濾過、Hurewicz は Künneth 型 SS；Prop 1.5.9 厳密 cofinality；Thm 1.8.1）。
  推奨：Waldhausen 圏 F(A)（有限生成半自由 dg 加群）に対し 2.3.2 の類似を直接証明し、Perf への cofinality（K_{≥1} 一致、K₀ は冪等元の持ち上げ）で接続する。
- **Thm 2.16**：n = 0, 1 は Prop 2.15・Lemma 2.14、n < 0 は Bass 基本定理（Thm 3.17）で帰納。
  可換性は使わない。dg 版では **dg 代数の Bass 基本定理（自然な分裂）**が別途必要。
- **Lemma 2.13**（Segal 1974 Prop 1.5）、**Lemma 4.2**（Isaksen Thm 7.3 の易しい向き：π_* pro 同型 ⇒ H_* pro 同型）、
  **Prop 4.3**（pro-Whitehead：連結冪零空間の pro-系で H_* pro 同型 ⇒ pro 同値、[BK72 III.5.4(ii), III.6.6]）。
  応用対象はすべて連結 H 空間なので simple 空間版で足りる。難しい向きは Prop 4.8 の BĜL⁺ と Claim 4.17 で必要。
- **Prop 4.8**：pro-単体環の同値 ⇒ K の pro-同値。i ≤ 1 は Thm 2.16、i ≥ 1 は Prop 2.15 と Prop 4.3、Lemma 4.2。
- **Thm 4.11 の全構造**（本文確認）：基底 r = 1：(1) i ≤ 0 は Thm 2.16 + 離散環の負の K の切除 [Wei13, III.4.3]、
  (2) 同値な単体環に替えて a を非零因子に、A(n) ≃ A/aⁿA、(3) F̃(n) = hofib(BĜL(A)⁺ → BĜL′(A/aⁿA)⁺)、Prop 4.3 で Claim 4.17（H_i の pro 同型）に帰着、
  (4) (4.6)：Lemma 4.10 + 2.13、Lemma 4.2 で Claim 4.18 に帰着、(5) Claim 4.18 ⇐ Claim 4.19（π₁BĜL(A) の作用の pro-自明性）
  は **局所係数つき相対 Serre スペクトル系列**（[SW92 Cor 1.7] / [GH06 Lem 1.2]）、(6) Claim 4.19 ⇐ Prop 4.14 + ι/σ トリック。
  帰納段階は Lemma 4.10 のみ。r > 1 では定数でない pro-系版が必要。
  Prop 4.14 は相対ホモロジー H_i(ĜL(aI) ⋉ M_{∞,1}(aI), ĜL(aI)) → … の零化に帰着し、Claim 4.15、Lemma A.4、Lemma 4.16 で終了。
  App. A（Prop A.1、Lemma A.2・A.4、Construction A.5・A.6）は群状単体モノイド G ⋉ H のホモロジーのみ。
- **非可換版**（再構成）：Prop 4.14「I 結合的非単位的単体環、a ∈ I₀ 中心的で各次数で a 倍単射 ⇒ GL(ℤ) は im(H_i(ĜL(aI)) → H_i(ĜL(I))) に自明に作用」。
  Thm 4.11「R 可換、(A_m), (B_m) は結合的単体 R 代数の pro-系（a_i は中心的に作用）、Noether 性は Lemma 4.9 の出力に置換」。
- **Cor 4.12・4.13 の証明**（再構成）：Cor 4.12 は I の生成系 a で {a(n)A} ≅ {Iⁿ}、Thm 4.11（定数 pro-系）、Lemma 4.10 + Prop 4.8 で
  "lim" K(Ko(A; a(n))) ≃ "lim" K(A/Iⁿ)、Lemma 4.6。Cor 4.13 は "lim"_n a(n)π_iA = 0（i > 0）から Thm 4.11 を A → π₀A に適用。
- **Weibel III.4.3**（確認）：K_{−n} = L^nK₀（Def 4.1）、縮約関手（4.1.1）、Mayer–Vietoris 長完全列（Thm 4.3）。結合的単位環で可換性不要。
  dg 側への移植には「基本定理の自然な分裂」と「K₀・K₁ の古典との一致」が要る。
- **GH/Suslin 経路との比較**：GH11 Thm 3.1 は pro-Tor-unitality（Morrow Thm 0.2・Lemma 2.1）を仮定し、Suslin 流の pseudo-free 加群のホモロジー代数を使う。
  **KST 経路（§4.3 + App. A）を推奨**：Tor-unitality 不要、単体／dg 版が直接得られ Cor 4.13 に必要、群ホモロジーの構成が明示的。
  黒箱でない引用：[SW92 Prop 1.5]・[Sus95 Thm 3.5] は「arguing as in」で本文が再現している。
  不可避の重い依存：Prop 2.15（群完備化＋plus 構成）、Prop 4.3（pro-Whitehead）、Serre SS（Claim 4.18）、Bass 基本定理の dg 版。

### 2.6 P2：KST §3・§5 の詳細

- **訂正**：KST の [Tem08] は Temkin, *Desingularization of quasi-excellent schemes in char 0*, Adv. Math. 219 (2008) の Lemma 2.1.5。
  同内容は **Stacks 081T**（固有射 X → S が開 U 上で同型なら、X を支配する U-admissible blowup S′ → S が存在）。
- **導来 blowup のチャート**（再構成）：普遍の場合 A′ = ℤ[T₀..T_r]、I′ = (T)。X̃′ = Proj A′[Y]/(T_iY_j − T_jY_i)、
  U′_i = Spec ℤ[T_i, S^{(i)}_j]（多項式環）、貼り合わせ S^{(k)}_i = (S^{(i)}_k)^{-1}、S^{(k)}_j = S^{(i)}_j(S^{(i)}_k)^{-1}、T_k = T_iS^{(i)}_k。
  O(1) の推移関数は S^{(i)}_k、O(1) = I′O、O(−1) = O(E′)。X̃′ → ℙʳ_ℤ は O(−1) の全空間。
  A へ底変換後：U_i = Spec Ko(A[S^{(i)}]; (a_iS_j − a_j)_{j≠i})（Koszul cdga）、E ∩ U_i ≅ Ko(A; a)[S]、E = ℙʳ_Y、
  D(n) ∩ U_i = Ko(A[S]; (a_iS_j − a_j), a₀ⁿ..a_rⁿ)。貼り合わせは Koszul 複体の基底変換（strict、cocycle 成立）。
- **Thm 3.7 の証明**（Lemma 3.8〜3.15、本文確認）：3.8（アフィン f で生成系が移る）、3.9（Perf(X̃) は O、j_*O_E ⊗ O(−l) で生成；[CHSW08 Lemma 1.2]）、
  3.10（p*, q* 充満忠実；底変換 + [Tho93 Lemme 2.3]）、(3.4) j*j_*O_E ≃ O_E ⊕ O_E(1)[1]、3.11（Hom(O_E, O_E(−k)) = 0、1 ≤ k ≤ r；ℙʳ のコホモロジー）、
  3.12（j_*q* 充満忠実）、3.13・3.14（Neeman Lemma 9.1.5 で部分商への同値）、3.15（j* が逐次商で同値）、最後に Thm 2.10。
  必要な一般命題：(B1)(B2) アフィン射の底変換、(P) 射影公式、(M) f̃* のモノイダル性、(F) 基本ファイバー列 O(1) → O → j_*O_E。
- **Thomason 1993 Lemme 2.3**（原文未入手）：普遍の場合に Rp′_*O_{X̃′}(l) = ⊕_{k≥0} RΓ(ℙʳ, O(k+l)) から Rp′_*O = A′（ℙʳ のコホモロジー消滅）で再構成できる。
- **Thm 3.16・3.17**：TT Thm 4.1・7.3（射影束）、Thm 6.1・6.6・7.5（Bass 基本定理）、Thm 8.1（MV = 局所化 7.4 + 切除 7.1）で確認。
  3.17 の分裂：ℙ¹_X = X[t] ∪ X[t⁻¹]、基底 {[O], [O] − [O(−1)]}、零切断 t = 0 が切断なので分裂単射。非可換 H でも t は中心的なのでそのまま通る。
- **§5**：Prop 5.2（有限の場合：I^N B ⊆ φ(A) は鳩ノ巣、I^N ∩ ker φ = 0 は Artin–Rees；K 固有の入力は Cor 4.12 のみ）、
  Claim 5.3・Prop 5.4（α・β の左逆元論法）、Lemma 5.5(i)(ii)(iii)、Lemma 5.6（Huneke–Swanson Prop 8.1.5・Thm 8.2.1 で有限射 Bl_{(a′)²} → Bl_{(a′(2))}、
  Bl_{Iⁿ} ≅ Bl_I）、導来 blowup の塔 X̃(2ⁿ)、Thm A の組み立て（(5.12)、(5.13)、(5.6)）。
- **pro 形式の最小定義**（提案）：ℕ 添字の塔とレベル射に限定。pro 同型は Artin–Mazur 型判定（∀n ∃m ≥ n ∃g : B_m → A_n で両合成が遷移射）。
  pro-cartesian は「レベルごとの hofib が同値」を定義にする。必要補題：(L1) レベルごと長完全列、(L2) pro 五項補題、(L3) 加法関手（⊗ℚ）の pro 同型保存、
  (L4) ℕ×ℕ 添字の対角の共終性。KST Lemma 4.7（Isaksen）は対角で代替する。

### 2.7 P3：資産の棚卸し（Mathlib 固定版・リポジトリ）

**Mathlib にあるもの**：射のクラス（`IsClosedImmersion`、`IsFinite`、`IsIntegralHom`、`IsProper`、`IsSeparated`、`Flat`、`LocallyOfFinitePresentation`、
`UniversallyClosed`、`Surjective`）、`IsLocallyNoetherian`/`IsNoetherian`、`IsReduced`/`IsIntegral`、Krull 次元、`Proj`/`ProjectiveSpectrum`（固有性つき）、
イデアル層と閉部分スキーム、`Scheme.Modules`（`SheafOfModules`、`IsQuasicoherent`、abelian）、層コホモロジーの Čech と MV、
**切断が閉埋め込み**（`IsClosedImmersion.of_comp`）、**等化子が閉**（`isClosedImmersion_equalizer_ι_left`）、
Artin–Rees（`Ideal.exists_pow_inf_eq_pow_smul`）、Rees 代数、`LaurentPolynomial`、`DerivedCategory`、三角圏・Verdier 局所化、`Karoubi`、
Dold–Kan、`Arrow.cechNerve`、`ExtraDegeneracy`、群ホモロジーと Shapiro、Serre 類、`SpectralSequence`（基礎のみ）。

**Mathlib にないもの**：blowup、相対 ℙⁿ、連接層、D_qc(X)、スキーム上の perfect 複体、コンパクト生成、Neeman の局所化、TT、
Fitting イデアル、イデアルの reduction・整閉包、Koszul 複体（リポジトリにはある）、直積の平坦性（Chase）、pro 対象、三角圏の compact 対象、
K₀・Waldhausen 圏・plus 構成、LHS スペクトル系列、単体的集合の高次ホモトピー群、有理ホモトピー論。

**リポジトリにあるもの**：`CategoryTheory/`（`TriangulatedK0`、`verdierLift`、`karoubiVerdierOrderEquivalence`、`scalarSupported`）、
`PerfectComplex/`（`K0Supported`）、`KTheory/`（G₀、dévissage、`K0Localization`、Adams）、
`Asymptotic/`（`PaperRankQuotient`、`supportedKaroubiEquivalence`、`paperSupportedChangeRing`、`paperTwist`）、
`DifferentialGraded/`（`DGCategory`、`moduleSemifree`、`modulePerfect`、`moduleCompact_iff_perfect`、dg 商 `localPerfectQuotientEquivalence`、
Verdier 比較、Morita `criterionPerfMorita_iff`、`perfectEndomorphismEquivalence`、係数変更、導来 tensor）、
`Spectra/`（`StableModelPresentation`、Σ⊣Ω、導来 tensor 逆関手；**π_n・fiber 列・有理化は未実装**）、
`HomotopicalAlgebra/Diagram/`（hocolim、SSet 値 holim；BG・hG・Tot はない）、`InfinityCategories/`（dg nerve、極限、slice、join）、
`CommutativeAlgebra/`（`koszulComplex`、`IsKoszulResolution`、`ReesModule`、Artin–Rees の応用、正則列、`IsGeometricallyTransitive`）、
`Inputs/Descent.lean`（`theorem_3_1_K0`）、`Paper/Section4/SupportedDescent.lean`（`supportedRankK0_descent`）。

---

## 3. 数学的な経路（確定）

```
KST Thm A（係数つき、K の pro-降下）
   ⇒ ⊗ℚ と Pro(Ab) の五項補題で E = fib(K_ℚ → K[1/p]_ℚ) が pro-cartesian
   ⇒ 離散結合環の冪零不変性で "lim" E(Y_n) が定数
   ⇒ 抽象 blowup 正方形の実降下（E(−;H)、H 離散・A 平坦）
   ＋ Zariski 降下（係数つき）、有限平坦 transfer、有理固定点、平坦化 blowup
   ⇒ 定理 3.1（論文の証明構造：Čech 降下、τ の議論を Čech 計算で、軌道論法）
   ⇒ H = A：theorem_3_1_K0。H = B_A：F5（K₀・K₋₁ の局所化列）で supportedRankK0_descent
```

Goodwillie は第 2 段（補題 4.6 経路、H → π₀H の置換）でのみ必要。

---

## 4. 設計上の決定

| # | 論点 | 決定 | 備考 |
| --- | --- | --- | --- |
| D1 | **K の定義** | 連結 K は小さい安定（冪等完備）∞ 圏の ∞-S• 構成（S_n(𝒞) = Fun(N(Ar[n]), 𝒞) の gapped 対象の core、K(𝒞) = Ω\|ιS•𝒞\|、反復で連結スペクトル）。dg 圏には dg nerve で適用：K(C) := K(N_dg(Perf_dg C))。**非連結化は既定 (a)**：BGT §9（Calkin 圏 Ind(𝒞)^{ω₁}/𝒞）。F2（Ind・presentable）完成が前提。**保険 (b)**：dg 側の Schlichting（Count(C)/C、Eilenberg swindle）で定義し nerve を取る。**K に依存する部分は界面（§5 K0）に対して書き、後から差し込む** | Bass の delooping（TT §6）は定義には使わない（基本定理は定理として証明） |
| D2 | **連結 dg 代数の GL と比較定理** | ĜL_n(A) := ĜL_n(ΓA)（Dold–Kan、Alexander–Whitney）。Waldhausen 2.3.2 の類似 Ω\|ιS•\| ≃ K₀(π₀A) × BĜL(A)⁺ を直接証明（群完備化＋plus 構成、1.7.1・1.8.1・1.5.9 の ∞-S• 版、Perf への cofinality） | KST §4 で必須。M でも C でも避けられない |
| D3 | **導来 blowup のモデル** | Koszul cdga の strict Zariski 図式（§2.6）。O(l) は推移単元。simplicial 可換環は使わない | Perf・K は E₁ 構造しか見ない |
| D4 | **Perf(X;H)** | 有限アフィン被覆上の H ⊗ O 加群の降下データ（層レベル）。T1〜T3 を証明 | LT B.2 不要。H の平坦性は Hom 計算にだけ使う |
| D5 | **pro 形式** | §2.6 の最小定義 | Isaksen 4.7 は対角で代替 |
| D6 | **係数と非可換性** | Prop 4.14・Lemma 4.16 を結合的 I・中心的 a で再述。Noether 性は Lemma 4.9 の出力に置換。非零因子化は R[t] 上の半自由置換。KST §4.3 + App. A を採り、LT Thm 2.32・GH/Suslin の Tor-unitality は使わない | §2.3・§2.5 |
| D7 | **∞ 基盤との接続** | Sp と Sp 内の極限（hG、Tot）は γ から。主張は論文どおりに Sp の同値で述べ、証明は π_* の長完全列で回す | γ-A／γ-B は未決（§9） |
| D8 | **段階** | §1 のとおり | — |
| D9 | **冪零不変性** | 離散結合環 R と冪零両側イデアル I について、中間環 R̃ = R[1/p] ×_{S[1/p]} S（S = R/I）を挟む。Step 2：同じ底 GL(S) 上で 1+M(I) の有理ホモロジー同型と LHS の比較 ⇒ K_ℚ の同型（D2 の比較定理と Serre 類の Whitehead を使う）。Step 3：p 冪零な perfect 複体の圏 Perf(R̃)_{p-nil} ≃ Perf(S)_{p-nil} ⇒ E(R̃) ≃ E(S)。非可換でも p 中心的なら成立 | 2026-10-16 に紙で検証済み |

---

## 5. ブロック（主張の一覧と規模）

規模は Lean の行数の粗い目安。

### K0：局所化不変量の界面（K に依存する部分の共通前提）

`K : dg 圏（または安定 ∞ 圏）→ Sp` と次の性質を構造として束ね、A・B・C・D・F5 はこれに対して書く。

1. 全次数の局所化：Verdier 列（dg 商 = Verdier 商、U15・U17）↦ Sp の fiber 列。
2. Morita 不変性（dg 擬同値・Morita 同値、U16）。
3. filtered 余極限との可換性。
4. K_n(A) ≅ K_n(π₀A)（n ≤ 1、連結 dg 代数）と Ω^∞K(A) ≃ K₀(π₀A) × BĜL(A)⁺（D2 の比較定理）。
5. Bass 基本定理（自然な分裂）。
6. π₀ K(C) ≅ `TriangulatedK0 (H⁰ C)`。

### K1：K の構成（連結部分、∞ 的）　4〜7 万行

- ∞-S• 構成：Fun(N(Ar[n]), 𝒞) の gapped 対象、core（Joyal、α の A3）、単体的 Kan 複体の実現と Ω、反復 S• による連結スペクトル。
- 「gapped 対象 ≃ 第一行」の自明 Kan ファイブレーション（余ファイバーの選択空間の可縮性、HTT 4.3.2.15 型。A2 の極限錐の空間を Fun に延長）。
- 加法性（McCarthy 流の短い証明の ∞ 版を第一候補。Barwick Thm 7.4 は代替）。
- fibration 定理（Verdier 列：w.e. = 錐が D に入る射、Waldhausen 1.6.4 の論法を ∞-S• 上で。Verdier 商は dg 商の nerve で供給し、∞ 的普遍性は使わない）。
- Morita 不変性、filtered 余極限、積。
- 非連結化：(a) BGT（F2 後）または (b) dg 側 Schlichting（§4 D1）。
- dg 圏の Bass 基本定理（自然な分裂）：定理として証明（TT 6.6 の移植、または射影直線の局所化と零切断）。

### K2：比較定理（古典）　2〜4 万行

- Dold–Kan Γ と ĜL、群完備化（Segal–McDuff）、plus 構成（acyclic map、完全正規部分群）、Waldhausen 1.7.1（球状対象・セル濾過、Künneth 型 SS による Hurewicz）、1.8.1、1.5.9 の ∞-S• 版、Perf への cofinality。
- Thm 2.16（n ≤ 1 は K2、n < 0 は Bass 基本定理）。

### A：導来圏・幾何の基盤（KST §2–§3 の局所化不変量一般部分）　4〜6 万行

1. D_qc(X) のコンパクト生成（BvdB 3.1.1、compact = perfect、台つき生成）。
2. T1・T1′：係数つきコンパクト生成と局所 perfect 性との一致。
3. T2：Neeman の局所化（Thm 2.1、Cor 3.2.3）と D(X;H)/D_Z ≃ D(U;H)。
4. T3：切除・MV・有限 Čech 降下（TT 3.19・8.1 の係数版）。
5. 平坦 H での RHom_H(P ⊗ H, Q ⊗ H) ≃ RHom(P, Q) ⊗_A H（Čech）。
6. 導来 blowup の Koszul cdga 図式、底変換（B1・B2）、射影公式（P）、モノイダル性（M）、基本ファイバー列（F）。
7. Thomason 1993 Lemme 2.3（Rp′_*O = A′、ℙʳ 経由）と ℙʳ のコホモロジー消滅（Lemma 3.11）。
8. KST 3.9〜3.15 の係数版 ⇒ Thm 3.7。3.16（射影束）、3.17（Bass、零切断による分裂）。
9. E の Morita 不変性・局所化性の適用（K0 から）。

### B：KST の K 固有部分（係数つき）　4〜6 万行

1. pro 形式（D5）と補題 L1〜L4。
2. Lemma 4.9・4.10（Koszul ホモロジーの pro-消滅）と平坦底変換の補題群。
3. Lemma 2.13（Segal 1974 Prop 1.5）、Lemma 4.2（π_* pro 同型 ⇒ H_* pro 同型）。
4. **Prop 4.3**（pro-Whitehead、simple 空間版。Bousfield–Kan III.5.4・III.6.6）。
5. Prop 4.8。
6. **局所係数つき相対 Serre スペクトル系列**（Claim 4.18、GH06 Lemma 1.2 の形）。
7. App. A（Prop A.1、Lemma A.2・A.4、Construction A.5・A.6）、Prop 4.14・Claim 4.15・Lemma 4.16（結合的 I・中心的 a）、Claims 4.17〜4.19、ι/σ トリック。
8. Thm 4.11（基底 r = 1 と帰納段階、定数でない pro-系版）、Cor 4.12（再構成）、Cor 4.13。
9. 離散環の負の K の切除（Weibel III.4.3、縮約関手）。

### C：KST §5（スキーム論）　1.5〜3 万行

Artin–Rees（Mathlib）、Prop 5.2、Raynaud–Gruson の平坦化（Stacks 081T の形）、Claim 5.3・Prop 5.4、
Huneke–Swanson 8.1.5・8.2.1、Bl_{Iⁿ} ≅ Bl_I、Lemma 5.5・5.6（導来 blowup の塔）、Thm A の組み立て。

### D：KST Thm A から E の降下へ　1〜2 万行（＋ K2 の橋渡し）

⊗ℚ の pro 完全性と五項補題、定数 pro-対象、離散結合環の冪零不変性（D9）。

### E：論文側（定理 3.1 の証明）　2〜3 万行

Zariski 降下（係数つき、T3 から）、有限平坦 transfer・射影公式・加法性（補題 3.2）、有理 G 固定点（自明作用、Shapiro）、
Fitting 版の平坦化 blowup（補題 3.3）、幾何補題（Mathlib にほぼあり）、(3.6) の同定、Čech の機構（Fubini、分裂降下、細分補題）、
定理 3.1 の骨格（公理化した L から先に証明する）。

### γ：Sp　2〜4 万行

π_n、fiber 列と長完全列、有理化（telescope）、BG/Δ 上の holim（hG、Tot）。γ-A／γ-B は未決。

### M9/F5：補題 4.6 の迂回　1〜2 万行

B_S = ∏M_{s_n}(S)（A 上平坦、Chase）、D_S ≃ Perf(B_S)、N_S を Perf(B_t) のフィルター和として、補題 4.2（既存 `supportedKaroubiEquivalence`）、
K₀・K₋₁ の局所化列、定理 3.1 を n ∈ {0, −1} で、五項補題。K₋₁ は K1 の非連結化から。

### M10：統合　0.5〜1 万行

仮定の供給（ℤ_(p) 代数構造、p ∈ J、有限 Krull 次元）、二種類の K₀ の比較、`theorem_3_1_K0`・`supportedRankK0_descent` の置換。

### 第 2 段

補題 4.6 の当てはめ（0.8〜1.5 万）＋ dg U17c・d、Goodwillie（6〜15 万）、定理 4.7 を論文どおりに。

**第 1 段の合計**：およそ 22〜37 万行（M の完全版（Ind 込み）では K1 が 12〜20 万行に増える）。

---

## 6. M（現代的な K）の重い部分

| # | 部品 | 重さ | 対処 |
| --- | --- | --- | --- |
| H1 | 非連結化（BGT §9、Ind・presentable・κ-compact・presentable の Verdier 商） | 最重（10 万行級） | F2 完成まで (b) で逃がすか、界面で分離して待つ |
| H2 | fibration・局所化定理の ∞ 版 | 2〜4 万 | Verdier 商は dg 商の nerve、Waldhausen 1.6.4 の論法 |
| H3 | 加法性 | 2〜3 万 | McCarthy 流 |
| H4 | Fun の極限と gapped ≃ 第一行 | 1〜2 万 | A2 の延長 |
| H5 | 比較定理（K2） | 2〜4 万 | 不可避 |
| H6 | core・可逆辺（A3） | 中 | 計画済み |
| H7 | Sp（γ-B）、Tot・hG、有理化 | 2〜4 万 | HT-KQ 不要 |
| H8 | S• の実現と Ω | 0.5〜1 万 | — |
| H9 | Verdier 商の nerve の整合 | 0.5〜1 万 | ∞ 的普遍性は不要 |

---

## 7. ∞ 基盤への要求（提案）

将来の数論幾何の形式化も見据え、基盤を次の階段で整備する案（未決、§9）。原典は Kerodon（HTT は対応表で併記）。
モデル構造・straightening は使わない。

| 段 | 内容 | K 理論からの要求 |
| --- | --- | --- |
| F0 | quasicategory、Fun、join・slice、極限、写像空間、同値（α の A1〜A5） | A3（core）、Fun の極限、gapped ≃ 第一行 |
| F1 | left/right/cartesian fibration、Yoneda、前層 ∞ 圏 | （非連結化 (a) の前提） |
| F2 | 𝒮、Ind・presentable、随伴関手定理、局所化、κ-compact | **非連結化 (a)** |
| F3 | 安定 ∞ 圏、Sp、t 構造、D(R) | K の値域、D4 の安定性 |
| F4 | 対称モノイダル ∞ 圏、∞-operad、E∞ | K 理論では不要（BS の ε 次第） |

β（dg nerve）への要求：N4（写像空間）、N5（関手性）、dg 商の nerve が Verdier 商であること（ホモトピー圏レベル）。

---

## 8. レーンと合流点（最大並列の案）

| レーン | 内容 | 開始条件 |
| --- | --- | --- |
| L1 | K1a：∞-S• 構成、gapped ≃ 第一行、加法性（連結 K） | A3・Fun の極限の後 |
| L2 | K2：Dold–Kan Γ、群完備化、plus 構成、Waldhausen 2.3.2 の ∞-S• 版 | 即時（古典部分から） |
| L3 | K1b：fibration 定理、Morita、filtered 余極限、dg 圏の Bass 基本定理、非連結化 (a) または (b) | L1 の後、(a) は F2 の後 |
| L4 | A-1：D_qc(X;H)、BvdB、Neeman、切除、MV、Čech（圏のレベル、K に依存しない） | 即時 |
| L5 | A-2：Koszul cdga の導来 blowup、ℙʳ のコホモロジー、半直交分解（圏のレベル）、Thm 3.7・3.16・3.17（K0 に対して） | L4 の型確定後 |
| L6 | B：pro 形式、4.9・4.10、App. A、4.14・4.16、Serre SS、Prop 4.3、Thm 4.11（K に依存する基底は K0 に対して） | 即時 |
| L7 | C：Artin–Rees、081T、Huneke–Swanson、§5 | 即時 |
| L8 | E：定理 3.1 の骨格（公理化した L）、transfer、有理固定点、幾何補題、Čech の機構 | 即時 |
| L9 | γ：Sp、π_n、fiber 列、有理化、holim | γ の判断後 |
| L10 | M9/F5、M10 | L3 の後 |
| L11 | 紙の検証（§10） | 即時 |

合流点：S1（K0 の型確定：全レーンが界面に対して書ける）、S2（A-1・A-2 ⇒ Thm 3.7 まで）、S3（B・C ⇒ KST Thm A 係数つき）、
S4（D・E ⇒ 定理 3.1、H = A）、S5（K1b の非連結化 ⇒ F5 ⇒ `supportedRankK0_descent`）、S6（第 2 段）。

---

## 9. 未決事項（引き継ぎ先で判断）

1. ∞ 基盤の範囲：F0〜F3 を基盤に含めるか。原典を Kerodon に固定するか。(a) の前提。
2. γ：γ-A（stage 4 の coherent nerve、HT-KQ が残る）か γ-B（Kan 複体から Ω スペクトルを直接、HT-KQ 不要）か。
3. 定理 3.1 の Lean の主張の形：全次数の π_* 同型を主とし、Sp の同値（hG）は γ の後に系として付けるか。
4. 保険 (b) の着手判断：F2 の完成見込みが K 理論の他の部品（15〜20 万行）の完成より後になりそうなら着手する。
5. K0（界面）の正確な Lean の型（1〜3 の後）。
6. 補題 4.6 の主張の形（第 2 段）：2026-10-17 に検討済みの案（Noether 性で述べる、H の次数ごと平坦性を結論に加える、
   中心局所化は A 線形性として述べる、G 作用との両立を別補題にする）を引き継ぎ先で確定する。

---

## 10. 着手前に紙で確かめる項目

1. Lemma 4.16 の非可換版（右乗法 φ、M_{n,n}(I) 同変性、aI が両側イデアル）と Prop 4.14 の非可換再記述。
2. R[t] 上の半自由置換による非零因子化が Thm 4.11 の全段で通ること。
3. Cor 4.12・4.13 の証明（§2.5 の再構成の確認）。
4. Prop 4.3 の simple 空間版（Bousfield–Kan III.5.4(ii)・III.6.6 の内容確認）。
5. Waldhausen 2.3.2 の ∞-S• 版（Thm 1.7.1 の Hurewicz を Künneth 型 SS で）。
6. dg 圏（安定 ∞ 圏）の Bass 基本定理（Tabuada／Cisinski–Tabuada の主張の確認、または TT §6 の直接移植）。
7. D4 の降下データ模型が D_qc と一致すること（有限被覆の MV 帰納）。
8. Thomason 1993 Lemme 2.3 の ℙʳ 経由の証明と Lemma 3.11。
9. Isaksen 4.7 を対角で代替できること（Lemma 5.5(ii)(iii) を m について一様に）。
10. Chase の定理（Noether 環上の平坦加群の積は平坦）。
11. McCarthy 流の加法性が ∞-S• でそのまま通ること。
12. fibration 定理の ∞ 版の最小形（Waldhausen 1.6.4 の論法）。
13. gapped ≃ 第一行の自明 Kan ファイブレーション（余ファイバーの選択空間の可縮性）。
14. (a) と (b) の非連結 K の一致（BGT §9 の Schlichting との比較）：(b) を採った場合に後で必要。

原文未入手のもの：Thomason 1993、Suslin 1995、Suslin–Wodzicki 1992、Bousfield–Kan 1972、Raynaud–Gruson 1971、Isaksen 2002、
EKMM、CMNN Prop A.13。いずれも二次文献（KST・LT・GH・CHSW・Stacks）経由で主張を確認している。

---

## 11. 受入基準

1. 各単位は対象ビルドと公開宣言の公理監査（標準 3 公理のみ）を通す。新規 sorry・公理・引用を入れない。
2. docstring は README「Conventions」の形式（概要／方針／規約／使われ方）。原典番号を書く。
3. 主張は論文・KST の番号と対応づけて記録する。原典と異なる証明経路（A1、D9、τ 位相の Čech 計算への置換、
   Prop 4.14・Lemma 4.16 の非可換再記述、Thomason Lemme 2.3 の再構成）は該当箇所に明記する。
4. K に依存する部分は K0 の界面に対して書き、(a)／(b) の差し替えで主張が変わらないことを保つ。
5. 他チャットのファイル（`k-theory.md`、`infinity-categories.md`、`dg-theory*.md`、README の索引）は、本計画の採用時に引き継ぎ先が更新する。

---

## 12. 変更点の明記

- [k-theory-v1.md](../../k-theory-v1.md) §7 の M4（hG・Tot・有理化のモデル圏的実装）は、γ と ∞ 極限に置き換える。
- [k-theory-v1.md](../../k-theory-v1.md) §7 の M7 は「KST Thm A（係数つき）＋ 離散冪零不変性」に置き換え、Land–Tamme の cdh 降下・⊙・Goodwillie は使わない（Goodwillie は第 2 段のみ）。
- [k-theory-v1.md](../../k-theory-v1.md) §7 の M9（補題 4.6）は第 1 段では F5 で迂回し、第 2 段で原典どおりに戻す。
- 2026-10-16 の調査で提案した「π_* ルート（hG・Tot なし）」は、γ が整う前の予備として残す。
- 2026-10-17 の K 理論の設計案（dg レベルの Waldhausen 圏＋Bass delooping）は、2026-10-18 に現代的な定義（D1）へ改めた。

---

## 13. 決定（2026-10-18、引き継ぎ先）

§9 の未決事項について次のとおり決めた。以後この節を優先し、矛盾する記述は本節に合わせて読む。

| # | 論点 | 決定 | 理由 |
| --- | --- | --- | --- |
| 1 | ∞ 基盤の範囲 | **F0〜F3 をすべて含める**（2026-10-18 改訂、[foundations.md](../infinity-lanes/foundations.md) §3）。F0 = α の A1〜A5 ＋ 関手 ∞ 圏の極限（HTT 5.1.2.2）、F3 = A4（安定 ∞ 圏）、γ-B の Sp、β の D(S)。**F1**（cocartesian/cartesian fibration、straightening（Kerodon 5.6）、随伴・局所化、Kan 拡張、Yoneda・前層）は新設レーン α2、**F2**（𝒮、Ind、presentable、随伴関手定理、Bousfield 局所化、P_Σ）は α3 が担当する。原典は Kerodon に固定し、HTT・HA の番号を併記する。モデル構造は coherent nerve（γ3）にだけ使う | 将来の数論幾何の基盤として F1・F2 を整える（ユーザー決定）。K の第 1 段は F0・F3 で閉じるので、F1・F2 は並行して進められる |
| 2 | 非連結化 | **(a) BGT §9 を定義とし、(b) dg 側 Schlichting を K0 界面に対する暫定実装とする**（2026-10-18 改訂）。第 1 段（K-1a・K-1b）は (b) で閉じてよい。F2 の完成後に (a) へ差し替え、両者の一致（§10-14）を示す。K に依存する部分は K0 に対して書く（D1 のまま） | F2 を待たずに第 1 段を進めつつ、最終的な定義は原典（BGT）に合わせる |
| 3 | γ | **γ-B。** Sp := Kan 複体の Ω スペクトル（X_n と X_n ≅ ΩX_{n+1}）の単体的圏の coherent nerve（γ1 により quasicategory）。π_n は Mathlib の `PtSimplex`・`MulStruct` を延長して定義。fiber 列と長完全列、有理化（telescope）、Tot・hG はレベルごとの Kan 複体の構成で与え、それらが Sp の ∞ 極限であることは γ3（HTT 4.2.4.1 型）の後に系として付ける。HT-KQ は不要（主定理経路外のまま残す）。stage 4 の対称スペクトルのモデル構造は後の比較用に保持 | 第 1 段の証明は π_* の長完全列で回るので、Sp の ∞ 的性質は主定理に不要。E2b の γ3 と共有 |
| 4 | 定理 3.1 の主張 | 第 1 段では **全次数の π_* 同型** K_n^J(H)_ℚ ≅ (K_n^J(H ⊗ T)_ℚ)^G（n ∈ ℤ）を主定理とし、Sp の同値（hG）は γ3 の後に系として付ける | §9-3 の提案どおり |
| 5 | K0 の型 | **π_* レベルの界面**：K_n : dg 圏 → Ab（n ∈ ℤ）、Verdier 列（dg 商）の長完全列、Morita 不変性、filtered 余極限との可換、K_n(A) ≅ K_n(π₀A)（n ≤ 1）と Ω^∞K(A) ≃ K₀(π₀A) × BĜL(A)⁺（D2）、Bass 基本定理の自然な分裂、π₀ = `TriangulatedK0`。Sp 値への精密化は γ3 の後。正確な Lean の型は合流点 S1 で L11（紙）と L1 が固定する | 決定 3・4 と整合。A・B・C・D・E・F5 は長完全列しか使わない |
| 6 | (b) の着手 | L3 で非連結化に入る時点で着手。保険ではなく既定 | 決定 2 |
| 7 | 配置と記録 | Lean は `SerrePositivity/KST/<レーン名>/`、namespace `SerrePositivity.KST`。各レーンの計画は `formalization-plans/archive/stage-i/kst-lanes/L<k>-<name>.md`（本文数百行、実施記録はコミットメッセージ）。本計画は全体の正本で、各レーンの着手・完了のみ §8 に反映する | 計画一覧 README の原則 |
| 8 | 補題 4.6 の形（§9-6） | 第 2 段の着手時に確定する | 第 1 段に不要 |
| 9 | Sp の模型（L9c、2026-10-18 改訂） | 対象は点つき Kan 複体の列 X_n と**単射**な構造写像 σ_n : ΣX_n → X_{n+1}（cofibrant）で、随伴 X_n → ΩX_{n+1} が全基点で π_* 同型（Ω スペクトル）。厳密同型 X_n ≅ ΩX_{n+1} は要求しない。Hom はスペクトルの射の単体集合で、単射と Kan 複体の指数が Kan fibration であること、Kan fibration が引き戻しと塔の極限で閉じることから Kan。Sp := coherent nerve。π_n(X) := π_{n+k}(X_k)。置換は写像柱と Kan 置換 | Bousfield–Friedlander の cofibrant–fibrant 模型。厳密極限の Kan 性が示せないため |
| 10 | D2 の ĜL（L2a、2026-10-18 明確化） | ĜL_n(A) := π₀ で可逆な行列のなす M_n(ΓA) の**群状単体的モノイド**（各次数で逆元は不要）。単体的群ではない（反例：R = ℤ[t]、A = R ⊕ R e、de = t で 1+t は π₀ で可逆だが単元でない）。BĜL は群状モノイドの bar 構成、plus 構成は π₁ = GL(π₀A) に適用 | KST 式 (2.2) と Waldhausen の \hat{GL} の定義どおり |
| 12 | K0 界面の補足（L11 の S1.5、2026-10-18） | 決定 5 の π_* レベル界面に加えて、(i) 任意の射の fiber は K_n の核・余核から復元できないので、相対 K は dg 商・支持核の相対構成（U15・U16）か L9 の Ω スペクトル模型の fiber（または L1 の相対 S•）で供給する、(ii) 有限 MV・augmented Čech の降下は群ごとの同型の寄せ集めでなく L9 の π_* と L6 の pro 形式へ渡す、(iii) E レーン用の有限平坦 transfer・射影公式・trf∘f* = [f_*O] は加法性から証明し rank は局所で扱う、(iv) 有理化は Ab の ℚ テンソルの完全性と L9 の telescope の比較で扱う。型の固定は L1 との合流 S1 で、補助名・宇宙・相対構成の選択を決める | Ab 値の K_n と LES だけでは閉じない工程がある（L11 §S1.5） |
| 13 | §5 の K/pro 本体の所有（L7 §14、2026-10-18） | L7 は K 非依存のまま、L7a・L7b と L7c の環論・古典的スキーム射を完成させる。Lemma 5.5・Claim 5.3・Prop 5.4 の K/pro の結論は合流側に置き、**K-L6 が Thm 4.11・Cor 4.12・4.13 の後に担当**する（導来 blowup の対象は K-L5、pro の再添字は L6 自身の宣言を使う）。`X̃`（導来 blowup の underlying scheme）を `affineBlowup I` で定義しない（Remark 3.3 の閉埋め込みは中心の外でのみ同型） | 結論自体が K 理論の主張であり、幾何の入力と本体を混同しない |
| 14 | Construction A.5 の正確な形（L6c、2026-10-18） | (i) 右辺の augmentation 補正 C(φ)+C(φ′)−C(e)（§5 の記録どおり）。(ii) **仮定の明示化**：群 P, Q, H と群準同型 μ : P × Q → H、α : T → P、β : T → Q をデータとし、m 次入力は C(α) と C(e_P)、m′ 次入力は C(β) と C(e_Q) の間のホモトピーとして与える（H へ移した後だけのホモトピーは入力にしない）。φ := μ(α,1)、φ′ := μ(1,β) に対し (m+m′+1) 次で C(φ·φ′) ≃ C(φ)+C(φ′)−C(e_H)。「φ と φ′ の像が可換」だけでは成立しない（D₈ の反例を Lean で検証。中央拡大 D₁₆ → D₈ の二次 cocycle）。(iii) Lemma 4.16 では P = T_{n,m−1}(I) ⋉ M_{n+m−1,1}(I)、Q = M_{n,1}(I)、H = T_{n,m}(I) ⋉ M_{n+m,1}(I)、μ(p, v) = p·ψ(v) で、P と ψ(Q) の可換性は I の可換性を要しない | 原典は「H を可換として記号を簡単にする」際に追加の仮定を使っており、非可換係数ではこの形が必要 |
| 15 | L8 の Čech 降下の主経路（2026-10-19） | **主経路の Tot・homotopy 極限は L9 の実構成（`CosimplicialTotalization`、`PointedHomotopyLimit`・`PointedWeightedEnd`）と整数次数の π_* で述べる。** `ModelCategory SSet` を仮定する L8 §70–99 の条件付き結果（56 ファイル）は比較用の補助として保持し、主経路の完成には数えない。主定理・最小公理の構造体に `ModelCategory SSet`・cofibrant generation・Quillen bifunctor の仮定を入れない。局所 rank・transfer の公式は各整数次数の π_n で供給し、Sp の通常の圏に ℚ 線形性を要求しない | Mathlib に Kan–Quillen モデル構造の instance はなく、決定 1・3 で HT-KQ は主経路外。条件付き結果は instance が無い限り主定理に接続できない（L8 §100 の指摘） |
| 16 | pro 切除の経路（2026-10-19） | **KST §4 の群ホモロジー（ĜL、Suslin–Wodzicki、pro-Whitehead）を Land–Tamme の ⊙ 構成に置換する。** 実現は dg 増強流（B 案、[foundations.md](../infinity-lanes/foundations.md) §1）：環・導来環は dg 代数、Mod_A は D(A) = N_dg(Semifree(A))、Verdier 商は Drinfeld 商（β3）、lax pullback は dg の gluing（β4）、∞ 側は Cat^perf・Verdier 列・半直交分解・局所化不変量（K-基盤 1）と Tamme の分裂定理・LT 主定理（K-基盤 2）。K は非連結 K を局所化不変量として（BGT (a)）定義し、暫定 (b) は使わない。L2 の plus 構成・古典比較と L6 の L6a〜g は不要となり Auxiliary として凍結する（削除しない）。公理 (3) 冪零不変性の供給（D ブロック）は再確認項目 | 基盤を主目標とする方針（foundations.md v2）。HA 流（E₁ 環スペクトルと Mod）は F4・F5 として後段に置く |
| 11 | D4 の D_qc(X;H)（L4a、2026-10-18 改訂） | 定義は層レベル：H_X 加群層の複体の導来圏のうち、忘却後の全コホモロジーが準連接な充満部分圏（BvdB・Neeman の設定）。有限アフィン被覆上の複体の**厳密**な降下データは採らない（複体の厳密貼り合わせは D_qc を復元しない。BvdB 3.1.3 の注意）。dg 増強は H_X 加群層の複体の dg 圏を acyclic で dg 商したもの（Drinfeld、U15 の dg 商）に取り、Perf・D_qc をその充満部分圏とする。アフィン dg 加群圏の Čech ホモトピー極限との比較は定義にせず、必要になった時点の定理とする | 既存の `Dqc`（コホモロジー条件）はそのまま。T1〜T3 は層レベルで BvdB・Neeman の証明が通る |

**着手順（2026-10-18）。** 即時：L11（紙）、L2、L4、L6、L7、L8、L9。L1 は α の A3e と関手 ∞ 圏の極限の後。L3・L5・L10 は §8 の開始条件どおり。
∞ 側のレーン（N・D・α・E2a・Π2）は [infinity-categories.md](../infinity-lanes/infinity-categories.md) の管理のまま。

Sp の安定性の逆関手案は再評価済み（2026-10-21）。HA Cor. 1.4.2.27 の一般判定は妥当だが、BF の構造随伴を厳密な豊穣自然変換にする段階と有限極限の包装・判定の自前証明が未完。移送 API は StrictEnrichedTransformation.functorIso が提供済みで、N への追加要求はない。残り4工程・少なくとも複数日の暫定評価から、旧経路より短いとは判定せず切り替えない。正確な残補題・根拠・見積もりは [L9 引き継ぎ](L9-spectra.md) を正本とする。

### K-5：K-基盤 1 の抽象部分（2026-10-20）

Sp レーンが `KST/LocalizingInvariants/` で、F3 の IsStable・IsExactFunctor に基づく安定 ∞ 圏と完全関手の ∞ 圏、抽象 Verdier 列、Sp 値の局所化不変量と基本補題を担当する。K-S• は SConstruction と具体的 K 関手の側を所有し、双方で相手の実装を変更しない。Verdier 列は充満忠実な完全包含、核と本質像の一致、および cofiber 辺を反転する商の局所化普遍性を含む。D の Drinfeld 商は後で具体例として接続する。局所化不変量の値域は L9-spectra.md の d2 界面だけを使い、Sp の IsStable は要求しない。StableInfinity、抽象 Verdier 列、零化と反転の基本補題、Sp 値不変量の定義と整数 π による同値検出は検証済み。零安定圏と任意抽象列の coherent 四角形提示、その像の実 fiber 性、実 BF fiber の全整数 π 消滅による同値検出も完成。長完全列で使う元の homotopyFiber を左下頂点、元の射を右辺として保持する Sp の実 fiber 四角形を構成し、置換単位の全 prism を保持する錐の輸送によって、その下辺の類と元の homotopyFiberInclusion の一致まで証明した。整数 π は h Sp 上の実関手 piFunctor となり、元の BF 整数 π との自然な比較 piComparison_naturality も供給する。fiber 群の積分解は BF 射の厳密切断から h Sp での切断に拡張した。同じ右辺の任意の二つの fiber 四角形の全図式同型、三対象と二辺を同時に保つ短複体同型、および元の BF 三対象への比較と両射との可換性も構成した。任意の Sp fiber 四角形の全整数次数の接続射と三箇所の完全性、任意抽象 Verdier 列の元の値の群・元の包含と商の誘導準同型への長完全列の移送まで完成した。端の値の全整数 π 消滅から元の包含または商の像の同値性も検出する。coherent な切断付き fiber 列の実 Sp 積同値も完成した。固定標的の cotensor Hom の成分に基本群演算を移し、元の BF 対象の演算を構成する。包含と切断による比較の整数 π 同型性を長完全列から証明し、第一射影を固定する自己同値の逆で補正して、元の包含・指定切断・射影との h Sp での整合性を全て保つ。同じ三対象・両辺の比較により任意の fiber 四角形と任意の抽象 Verdier 列の像へ移送した。積因子は元の fiber・底と同値な BF 表示で、その同値も明示し、積対象は実 ∞ 極限錐の頂点であることを証明する。IsLocalizingInvariant.splitEquivalence・splitLeftFactorIso・splitRightFactorIso と三つの整合式を提供し、K-5 抽象部分は完成。専用対象5687 jobs、59モジュール・719宣言の公理監査、全体19210 jobs が終了コード0。標準三公理のみ、宣言型の ModelCategory 検査も成功。公開名・検証結果・残工程は [L9 計画の K-5 節](L9-spectra.md) に記録する。
