# §2 剰余体と正規化長さ：主張の確認と引用元の照合

2026-10-08 作成。論文 §2（p.4–9）の各主張を正確に書き、引用されている文献の該当箇所を原典で確認した記録。

## 引用元の一覧

| 論文の引用 | 文献 | 確認した版 | 確認方法 |
| --- | --- | --- | --- |
| [6] | Cai–Lee–Ma–Schwede–Tucker, *Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, and an application to local fundamental groups*, Invent. Math. 244 (2026) | arXiv:2209.04046v4（2025-07-03）。論文の番号付けはこの版に従う | arXiv HTML 版で該当番号を照合 |
| [9] | Faltings, *Almost étale extensions*, Astérisque 279 (2002), Appendix 2 | — | 未確認（[6] 経由） |
| [10] | Gabber–Ramero, *Foundations for almost ring theory*, arXiv:math/0409584v13 | — | 未確認（[6] 経由） |
| [17] | Kurano–Shimomoto, *An elementary proof of Cohen–Gabber theorem in the equal characteristic p > 0 case*, Tohoku Math. J. 70 (2018), Theorem 1.1 | arXiv:1510.03573v2 | arXiv HTML 版で Theorem 1.1 を照合 |
| [19] | L. Ma, *Lech's conjecture in dimension three*, Adv. Math. 322 (2017) | arXiv:1609.00095v3 | arXiv HTML 版で Theorem 2.4 と §2.2 を照合 |
| [20] | Monsky, *The Hilbert–Kunz function*, Math. Ann. 263 (1983) | — | 未確認（主張は標準的） |
| [21] | OpenAI, *Lech's multiplicity conjecture*（同リポジトリ、2026-09-23、41ページ）, Theorem 3.1 | openai/math `adc7f124` | PDF を取得して §3 を照合 |
| [24] | Roberts, *Intersection theorems*, MSRI Publ. 15 (1989) | — | 未確認（[19] Theorem 2.4 の形で使用） |
| [4] | Bhatt–Scholze, *Prisms and prismatic cohomology*, Prop. 8.5 | — | 未確認（[6] Notation 4.0.1 経由） |
| Stacks 0AZZ | Koszul の Euler 特性と重複度（Theorem 43.15.5） | — | Stacks で照合。[21] が引用、本論文は番号なしで使用 |

## §2.1 Lemma 2.1（剰余体の拡大）

**主張**：(B, b, k) を完備ネーター局所環、k̄ を k の代数閉包とする。完備ネーター局所環 (B′, b′, k̄) と平坦な局所準同型 B → B′ で bB′ = b′ となるものがある。有限 B 加群 V と a ≥ 1 について

  length_{B′}((V ⊗_B B′)/(b′)^a (V ⊗_B B′)) = length_B(V/b^a V)。

よって加群の次元と有限長が保たれる。B が正則なら B′ も正則。M ⊗ N が有限長の有限 B 加群 M, N について、全ての Tor の長さ（したがって交点重複度）が保たれる。

**証明の要点**：
- 等標数：係数体で B = k[[X₁, …, X_t]]/I と表し、B′ = k̄[[X]]/I k̄[[X]]。平坦性は局所平坦性判定法。
- 混標数：Cohen の構造定理で B = V[[X]]/I（V は一意化元 p、剰余体 k の完備 DVR）。剰余体の単純代数拡大ごとに f ∈ V[X] を持ち上げて V[X]/(f) をとると、p を一意化元とする DVR。k̄ を尽くす塔に沿って合併をとり完備化して V′ を得る。k が完全でなくてよい。B′ = V′[[X]]/I V′[[X]]。
- 長さの保存：組成列を B′ でテンソルすると、平坦性で完全性が保たれ、単純因子は B′/b′ になる。
- 「compare [19, Lemma 2.2]」：Ma の Lemma 2.2 は Lech 予想の帰着（完備化、整域、剰余体を代数閉体に）で、同種の構成への参照。Ma の Lemma 2.2 自体は剰余体拡大の構成を明示的には述べていない（帰着の文脈で使っている）ので、「compare」は構成の典拠ではなく類似例の参照と読むのが正確。

**使う先行研究**：Cohen の構造定理、局所平坦性判定法、剰余体拡大の DVR の構成（標準的）。

**形式化の引用境界（2026-10-11 更新）**：

- `Inputs.exists_complete_flat_local_extension` に、任意の剰余体拡大 `K/k` を持つ
  完備 Noether 平坦局所拡大の存在だけを置いた。`m_B B′ = m_B′` と、剰余体同型が
  `k` 上で両立する条件も明記する。基底 `B` の完備性はこの存在定理には不要。
- 出典は EGA I, 2nd ed., 0, Proposition 6.8.3。
  [Stacks Tag 03C3](https://stacks.math.columbia.edu/tag/03C3) の拡大を完備化する形であり、
  完備化の Noether 性・平坦性まで引用の範囲に含める。Tag 03C3 の本文単独が
  完備 Noether 版を述べているとは扱わない（同ページの Comment #7831 に EGA の参照）。
- 商と係数拡大の `B′` 線形同型を `quotientBaseChangeEquiv` で構成した。
  平坦性を使わず、テンソル積の右完全性から証明している。
- その同型と平坦局所拡大での長さの保存から、任意の加群の Samuel 関数の一致を証明した。
  正則性と Tor の保存にも既存の証明を適用し、`lemma_2_1` 自身の `sorry` を除去した。
  正則性の保存は、証明済みの Hilbert–Samuel 多項式性と、未証明の次元定理に依存する。

## §2.2 Lemma 2.2（正則な正規化基底）

**主張**：(D, d, k) を次元 h > 0 の完備ネーター局所整域、k を標数 p > 0 の完全体とする。有限で generically separable な包含 A ⊆ D で、剰余体に恒等写像を誘導し、

- char D = p なら A = k[[t₁, …, t_h]]
- char D = 0 なら A = W(k)[[t₂, …, t_h]]（t₁ = p とおく）

となるものがある。どちらの場合も t₁, …, t_h は D のパラメータ系かつ A の正則パラメータ系。

**証明と引用の照合**：
- 標数 p：**Kurano–Shimomoto Theorem 1.1（Cohen–Gabber）**。原典の主張：(A, m, k) を次元 d ≥ 0 の等標数 p > 0 の完備局所環、π: A → k を商写像とすると、パラメータ系 y₁, …, y_d と環準同型 φ: k → A で、π∘φ = id_k、φ(k)[[y₁, …, y_d]] ⊂ A が module-finite、かつ dim A/P = d となる任意の極小素イデアル P について Frac(φ(k)[[y]]) → Frac(A/P) が分離的、となるものがある。
  - 照合結果：原典は k の完全性を仮定していない（一般の完備局所環）。D が整域なら極小素イデアルは 0 だけなので、Frac(A) → Frac(D) が分離的。論文の主張はこの特別な場合で、正しく引用されている。「剰余体に恒等写像」は π∘φ = id_k から。
- 混標数：係数環 W(k) ⊆ D（Cohen の構造定理。k が完全なので W(k) が係数環）をとり、p をパラメータ系 p, t₂, …, t_h に延ばす。完備性とパラメータ条件から W(k)[[t₂, …, t_h]] → D は module-finite。核が 0 なのは、両者の次元が h で、正則局所整域 W(k)[[t]] の 0 でないイデアルは次元を下げるから。分離性は標数 0 なので自動。
  - これは [21] §3.3 と同じ議論。CLMST の Notation 4.0.1 でも同じ設定（「Cohen's structure theorem により module-finite extension A = W(k)[[x₂, …, x_d]] ⊆ R がある」）を使っている。

**使う先行研究**：Cohen–Gabber（Kurano–Shimomoto）、Cohen の構造定理（係数環の存在）。

**形式化の引用境界（2026-10-11 更新）**：

| 外部から引用する主張 | このリポジトリで証明する帰結 |
| --- | --- |
| `Inputs.cohen_gabber_normalization`：等標数の有限正規化基底と分数体拡大の分離性 | 標数の分岐、分数体の分離性から採用した最小多項式の分離性への移送 |
| `Inputs.cohen_normalization_mixedCharacteristic`：完全剰余体を持つ混標数環の Witt 冪級数部分環による有限正規化 | 標数零から分数体拡大の分離性、その最小多項式条件への移送 |
| 両引用には、冪級数環の正則性・完備性と標準座標による極大イデアルの生成を含める | 単射な有限整拡大の次元保存、基底の座標の像が `D` のパラメータ系になること |

混標数は係数環の存在だけではなく、外部で証明された **Cohen 正規化の形**
（[Stacks Lemma 10.160.11、Remark 10.160.9](https://stacks.math.columbia.edu/tag/0323)）を
引用する。完全剰余体の Cohen 環を `W(k)` と同定する標準事実もこの引用に含む。
等標数は [Kurano–Shimomoto Theorem 1.1](https://arxiv.org/abs/1510.03573) の整域の場合。
有限性や冪級数環の正則性そのものを今回証明したとはしない。

`lemma_2_2` の直接の `sorry` は除去した。元の公開ステートメントを保ち、
上の引用から全条件をそろえる証明へ変更した。
最小多項式の比較に必要な正規性は `isIntegrallyClosed_of_isRegularLocalRing` を使い、
その先の正則パラメータの正則性には未証明の標準可換環論への依存が残る。

## §2.2 塔（式 (2.1)）と Lemma 2.3

**設定**：Lemma 2.2 の基底 A と、パラメータの両立する p 冪根を固定。Aₙ = A[t₁^{1/pⁿ}, …, t_h^{1/pⁿ}]、Λ = lim→ Aₙ（完備化しない）。混標数ではその p 進完備化 A_∞ も使う。

CLMST の記法との対応：Aₙ は CLMST の Aₙ、Λ は CLMST の A_∞^{nc}（nc = not necessarily p-complete）、A_∞ は CLMST の A_∞（p 進完備化、perfectoid）。CLMST §2.2 の冒頭の設定（A は k[[x₁, …, x_d]] または W(k)[[x₂, …, x_d]]、x₁ = p、k は標数 p の完全体）と一致する。

**Lemma 2.3 の主張**：
- 各 Aₙ は剰余体 k の完備正則局所環。b ≥ a で A_a → A_b はランク p^{(b−a)h} の有限自由。特に A → Aₙ はランク p^{nh}。
- m_A の冪で消される Λ 加群の圏に、非負で加法的な関数 λ_∞ があって、
  1. 有限表示な加群は有限段 Aₙ の有限長加群 Vₙ に降り、λ_∞(Vₙ ⊗_{Aₙ} Λ) = p^{−nh} length_{Aₙ}(Vₙ)（式 (2.2)）
  2. 有限生成な加群の長さは、それに全射する有限表示な加群の長さの下限
  3. 一般の加群では λ_∞(V) = sup{λ_∞(V₀) : V₀ ⊆ V 有限生成}（式 (2.3)）
- 値は ∞ になりうる。混標数では、m_A の固定した冪で消される加群について A_∞ から Λ への制限で同じ長さ。

**CLMST との照合**：
- **Definition 2.2.1（Faltings の正規化長さ）**：3段階で定義。有限表示な M ≅ Mₙ ⊗_{Aₙ} A_∞^{nc}（Mₙ は有限表示な Aₙ 加群で m_A 冪ねじれ、よって有限長）に λ_∞^{**}(M) := (1/p^{nd}) length_A(Mₙ)。有限生成な M に λ_∞^*(M) := inf{λ_∞^{**}(N) : N ↠ M, N 有限表示}。一般に λ_∞(M) := sup{λ_∞^*(N) : N ⊂ M 有限生成}。
  - 論文の 1–3 と一致。ただし CLMST は length_A、論文は length_{Aₙ} で書いている。剰余体が同じなので一致する（論文も Lemma 2.3 の証明でこの点を注記）。
- **Proposition 2.2.3**：λ_∞ は A_∞^{nc}-Mod_{m_A} → ℝ ∪ {∞} の well-defined な関数で、有限生成加群では λ_∞^* と、有限表示加群では λ_∞^{**} と一致。証明の難しい部分（有限生成加群で λ_∞^* = λ_∞）は Gabber–Ramero Lemma 14.5.74 または Shimomoto Lemma 2.2。
- **Proposition 2.2.6(a)**：A_∞^{nc}-Mod_{m_A} の短完全列 0 → M′ → M → M″ → 0 について λ_∞(M) = λ_∞(M′) + λ_∞(M″)。証明は Faltings Appendix 2 の Lemma に委ねている（Shimomoto Prop. 2.8、Gabber–Ramero Theorem 14.5.75 にも）。
- **Proposition 2.2.6(b)**：フィルター系 (Mᵢ) について、(i) 遷移写像が全て単射、または (ii) 全て全射かつ各 λ_∞(Mᵢ) < ∞ なら、λ_∞(colim Mᵢ) = lim λ_∞(Mᵢ)。
- 照合結果：論文が引く「Definition 2.2.1 and Propositions 2.2.3, 2.2.6(a)」は正しい。加法性（最重要）の証明は CLMST では Faltings に委ねられているので、原典は Faltings Appendix 2（または Gabber–Ramero 14.5.75）。

**使う先行研究**：Faltings の正規化長さの形式（Gabber–Ramero、Shimomoto、CLMST の定式化）。

## §2.2 Lemma 2.4（長さ 0 の極限）

**主張**：全ての加群が m_A の固定した冪で消されるとする。長さ 0 の加群の和・直和・有向余極限は長さ 0。増大列の合併について λ_∞(∪ V_a) = sup λ_∞(V_a)。λ_∞(V_a) → 0 の有向系について λ_∞(lim→ V_a) = 0（遷移写像の単射性は不要）。

**証明**：直和の有限個の元は有限部分和に入る。加法性と (2.3)。和と有向余極限は直和の商。増大列では有限生成集合は1つの段に入る。lim→ V_a の有限生成部分加群は、生成元を共通の段に持ち上げれば十分遅い V_a の像に入り、単調性で長さが λ_∞(V_a) 以下。

**照合**：CLMST Prop. 2.2.6(b) は単射か全射の場合しか扱っていないが、論文の第3主張は単射性を仮定しない。論文は自前で証明していて、(2.3) と単調性だけから出る。[21] Lemma 3.2 と同じ主張・同じ証明。

## §2.3 Theorem 2.5（正規化長さの入力）

**主張**：（`notes/lemma-3-4.md`、`notes/section-4.md` でも確認済み）Lemma 2.2 の (D, d, k) と基底 A ⊆ D、塔 Λ について、Λ と両立する作用をもつ D 代数 C_D があって、スカラーの制限で d の冪で消される C_D 加群の上に加法的で非負な長さ λ_D = λ_∞ が定まり、D の任意のパラメータ系 z と v ≥ 1 で

- (2.4) λ_D Hᵢ(z^v; C_D) = 0（i > 0）
- (2.5) λ_D(C_D/(z^v)C_D) = v^h e((z), D)（正で有限）

C_D と λ_D は z によらない。A の正則パラメータ t については (2.6) λ_D(C_D/(t^v)C_D) = v^h rank_A D。Lemma 2.3 の有限段・下限・上限の性質は、C_D 加群でない塔の上の加群にも使える。

### 標数 p の証明の照合

C_D = D_perf = ∪ D^{1/pⁿ}、Λ = A_perf。B_q = Λ ⊗_{A^{1/q}} D^{1/q}（q = pⁿ）。

1. **B_q ⊆ C_D**：Λ は A^{1/q} 上平坦、D^{1/q} はねじれなし、generically separable から K′ ⊗_{K^{1/q}} L^{1/q} は体。[21] §3.2 と同じ。CLMST Theorem 3.0.7 の証明も「generic separateness により A_perf ⊗_{A_e} R^{1/p^e} ⊆ R_perf」と同じ観察を使う。
2. **トレースによる分母 (2.7)**：0 ≠ g ∈ A で gC_D ⊆ B₁、g^{1/q} C_D ⊆ B_q。[21] Lemma 3.3 に自己完結した証明があり、そこでは Polstra–Tucker Lemma 2.3 の conductor bound のトレース双対版と位置づけている。CLMST では Theorem 3.0.7 の証明の中で同種の g を使う。
3. **(2.8) λ_D(C_D/HC_D) = e_HK(H, D)**：λ_∞(V_q) = q^{−h} length(D/H^{[q]})、核の評価 O(q^{−1})、Lemma 2.4、**Monsky の定理**（Hilbert–Kunz 重複度の存在。[19] §2.2 の Definition に「It is well-known that the above limits exist [Mon83, Tuc12, PT18]」）。[21] 式 (3.5) と同一。CLMST Theorem 3.0.7 の後半 e_HK(R, J) = λ_∞(R_perf/JR_perf) と同じ主張（CLMST は完備局所整域、Cohen–Gabber 正規化、A_e = A^{1/p^e} の設定）。
4. **(2.4) の標数 p**：λ_∞ Hᵢ(z; B_q) = q^{−h} length Hᵢ(z^q; D) と、**Roberts の Frobenius ホモロジー定理**。
   - **Ma Theorem 2.4 の原文**：(R, m) を標数 p > 0 の完備局所環、G• を長さ d = dim R の有限自由 R 加群の有界複体でホモロジーが有限長とする。このとき全ての i ≥ 1 で lim_{e→∞} l_R(Hᵢ(F^e(G•)))/p^{ed} = 0。
   - Ma はこれを「[Rob89] の main theorem に初めて現れた。より強い形は Hochster–Huneke [HH93, Theorem 6.2] に tight closure を使って。どちらのアイデアも Dutta [Dut83] に遡る」と注記。
   - 照合結果：論文の「Its hypotheses require precisely a complete characteristic-p ring and a finite-free complex of length its dimension with finite-length homology」は Ma の主張の仮定と一致。K(z; D) は次数 0, …, h の有限自由複体で h = dim D、ホモロジーは有限長（z がパラメータ系）なので適用できる。F^e(K(z; D)) = K(z^{p^e}; D)。
   - 注意：Ma の文脈ではこの定理は Dutta 重複度 χ_∞ と Hilbert–Kunz の関係のために引かれている。論文の χ_C が「Dutta 型の重複度」であるという見方（`notes/section-4.md`）はここと整合する。
5. **(2.5) の標数 p**：Koszul の Euler 特性の公式 Σ(−1)ⁱ length Hᵢ(z^q; D) = q^h e((z), D)。**Stacks Tag 0AZZ = Theorem 43.15.5**：A をネーター局所環、I = (f₁, …, f_r) を定義イデアル、M を有限 A 加群とすると、e_I(M, r) = Σ(−1)ⁱ length_A Hᵢ(K•(f₁, …, f_r) ⊗_A M)。[21] は明示的に引用、本論文は番号なし。パラメータ系 z^q に適用し、重複度の冪の規則 e((z^q)) = q^h e((z)) を使う。
6. **(2.6)**：e((t), D) = rank_A D · e((t), A) = rank_A D（重複度のランク公式と剰余体の一致）。CLMST Prop. 4.0.14 の「In particular」でも同じ式 λ_∞(R_perfd/m_A R_perfd) = e(m_A, R) = rank_A(R) が出る。

### 混標数の証明の照合

2026-10-11：以下の外部結果を名前付きの `sorry` として実装し、定理2.5に接続した。
完備化と普遍性による perfectoid 化を定義し、`Inputs/Perfectoidization.lean` と
`Inputs/PerfectoidTower.lean` に存在・perfectoid 性の引用、`Inputs/CLMST.lean` に
Cor. 4.0.4、Prop. 4.0.10、Prop. 4.0.14 の必要な特殊化を分けた。
Cor. 4.0.4 の引用には Notation 4.0.1 の非零元 `g` の存在も含む。
Prop. 4.0.10 はその証明に従い任意の非零 `g` に対する零の場合で書いた。
適用条件である一様な冪ねじれと、係数制限による長さの一致は `CompletedTower.lean` で証明し、
`MixedLengthAlgebra.lean` で両方の長さの結論へ接続した。外部結果自体は未証明である。

C_D = (D ⊗_A A_∞)_perfd。

- **CLMST Notation 4.0.1**：(R, m) を次元 d の混標数 (0, p) の完備局所整域、剰余体 k は完全。x̄ = p, x₂, …, x_d をパラメータ系。A := W(k)[[x₂, …, x_d]] ⊆ R は Cohen の構造定理で module-finite、剰余体は同じ。A_∞ は A_∞^{nc} の p 進完備化で perfectoid。R_perfd^{A_∞} := (R ⊗_A A_∞)_perfd は Bhatt–Scholze Theorem 10.11 により perfectoid（R ⊗_A A_∞ は A_∞ 上有限で有限表示）。0 ≠ g ∈ A を A[1/g] → R[1/g] が有限エタールになるようにとり、(g)_perfd = ker(A_∞ → (A_∞/g)_perfd)。almost mathematics は (g)_perfd に関して。
  - 論文は「Bhatt–Scholze [4, Proposition 8.5]」を引くが、CLMST 自身は「[BS22, Theorem 10.11]」を引いている。perfectoid 化の構成は §8、perfectoid 性の主張は Theorem 10.11。番号の食い違いは要確認（どちらも Bhatt–Scholze の該当結果を指している可能性が高い）。
  - **Caution 4.0.2**：A_∞ と R_perfd^{A_∞} はパラメータ系 x̄ の取り方に依存する。論文の「C_D と λ_D はパラメータ系 z によらない」は、基底 A（と t）を固定した上で、(2.4)(2.5) が D の任意のパラメータ系 z について成り立つ、という意味で、Caution と矛盾しない。
- **Theorem 4.0.3(a)**：R_perfd^{A_∞} は A 上 g-almost flat、すなわち (g)_perfd · Torᵢ^A(R_perfd^{A_∞}, M) = 0（全ての A 加群 M、i > 0）。
- **Corollary 4.0.4**：(g)_perfd · H^i_m(R_perfd^{A_∞}) = 0（i < d）。よって局所環 Aₙ ⊗_A R の任意のパラメータ系 ȳ について (g)_perfd Hᵢ(ȳ, R_perfd^{A_∞}) = 0（i > 0）。
  - 論文の引用「Corollary 4.0.4 of [6] annihilates positive Koszul homology for every parameter system of Aₙ ⊗_A D by the almost ideal (g)_perfd. At n = 0 this includes every parameter system of D」は正確。
- **Proposition 4.0.10**：M, N ∈ A_∞-Mod_{m_A} が (g)_perfd に関して M^a ≃ N^a なら λ_∞(M) = λ_∞(N)。特に g-almost zero な m_A 冪ねじれ加群は長さ 0。
  - 論文の引用「makes these uniformly m_A-power-torsion homology modules have normalized length zero」は正確。
- **Proposition 4.0.14**：ȳ = y₁, …, y_d を Aₙ ⊗_A R のパラメータ系とすると λ_∞(R_perfd^{A_∞}/(ȳ)R_perfd^{A_∞}) = (1/p^{nd}) e(ȳ, Aₙ ⊗_A R)。特に λ_∞(R_perfd^{A_∞}/m_A R_perfd^{A_∞}) = e(m_A, R) = rank_A(R)。
  - 論文の引用「Proposition 4.0.14, again at n = 0, identifies the length of the parameter quotient with its Hilbert–Samuel multiplicity」は正確。n = 0 で (2.5)。
- **Definition 4.0.8**：e_perfd^{x̄}(J, R) := λ_∞(R_perfd^{A_∞}/J R_perfd^{A_∞})（perfectoid Hilbert–Kunz 重複度）。**Corollary 4.0.18**：m-準素イデアル I について e_perfd^{x̄}(I) ≤ e(I)、I がパラメータ系で生成されるとき等号。これは [21] Theorem 3.1(3) の混標数の不等式 λ(C/HC) ≤ e(H, D) に使われるが、本論文では使わない。
- 論文の「Lemma 2.3 permits restriction to the uncompleted tower throughout」：CLMST の λ_∞ は A_∞^{nc} 加群上で定義され、Prop. 4.0.10 と 4.0.14 の対象は A_∞ 加群。Lemma 2.3 の最後の主張（Λ/p^a Λ ≅ A_∞/p^a A_∞ による同一視）でつなぐ。

### [21]（OpenAI の Lech 論文）Theorem 3.1 との関係

[21] Theorem 3.1 は本論文の Theorem 2.5 とほぼ同じ主張で、
1. 加法性、λ(0) = 0、長さ 0 の直和・和・有向余極限の安定性（本論文の Lemma 2.4 に相当）
2. 任意のパラメータ系 z と a ≥ 1 で λ(C/(z^a)C) = a^h e((z), D)、λ Hᵢ(z^a; C) = 0（i > 0）（本論文の (2.4)(2.5)）
3. H が d-準素なら λ(C/HC) = e_HK(H, D)（標数 p）、≤ e(H, D)（混標数）

を主張する。本論文は「Related normalized-length constructions … appear in [21, Theorem 3.1]. Here we retain the chosen base A ⊆ D and the finite-stage, infimum, and supremum properties on underlying tower modules」と述べていて、違いは (a) 基底 A を固定して (2.6) を主張すること、(b) 塔の上の加群への λ の適用可能性を明示すること（§5.3 の有限近似で必要）。[21] §3 の証明は本論文より詳しく書かれているので、標数 p の定理 2.5 の形式化では [21] §3.2 の記述（Lemma 3.3 のトレース、式 (3.3)–(3.7)）を参照するのがよい。

## Corollary 2.6

`notes/lemma-3-4.md` で確認済み。3つ目の主張 λ_D(C_D/dC_D) > 0 の証明は、D のパラメータイデアル H に対し D/H の組成列を C_D でテンソルして 0 < e(H, D) = λ_D(C_D/HC_D) ≤ length(D/H) λ_D(C_D/dC_D)。(2.5) の v = 1 と右完全性だけを使う。

## 照合で分かったこと（まとめ）

- CLMST の引用番号（Def. 2.2.1、Prop. 2.2.3、2.2.6(a)、Notation 4.0.1、Cor. 4.0.4、Prop. 4.0.10、Prop. 4.0.14）は全て arXiv v4 の番号と一致し、主張の使い方も正確。
- Kurano–Shimomoto Theorem 1.1 の引用は正確（原典はより一般で、k の完全性も整域性も仮定しない）。
- Ma Theorem 2.4 の引用は正確。仮定の確認（完備、標数 p、長さ = 次元の有限自由複体、有限長ホモロジー）も論文の通り。
  2026-10-11 に [arXiv v3 の原文](https://arxiv.org/html/1609.00095v3) を再照合し、
  `Inputs/RobertsFrobenius.lean` に名前付きの引用として実装した。
  cochain 次数は `[-d, 0]`、文献の `H_i` は `H^{-i}`、Frobenius 関手はその環準同型に
  沿う基底変更で表す。Koszul への適用条件と実数値から `ℝ≥0∞` 値への極限の変換は
  `CommutativeAlgebra/FrobeniusKoszulLimit.lean` で証明した。
- Bhatt–Scholze の引用番号（Prop. 8.5 vs CLMST の Theorem 10.11）は要確認。
- Lemma 2.1 の「compare [19, Lemma 2.2]」は類似例の参照で、構成の典拠ではない。
- 本論文は [21] §3 の記述を圧縮したもの。詳しい証明は [21] にある。

## 形式化への含意

- Lemma 2.3 の λ_∞ の構成と加法性は、Faltings Appendix 2 の Lemma が原典。CLMST も証明を委ねているので、形式化するなら Faltings または Gabber–Ramero 14.5.75 を読む必要がある。有限段の長さを p^{−nh} 倍するところまでは初等的で、下限・上限で延ばしたときの加法性が本体。
- 標数 p の Theorem 2.5 は、Monsky（Hilbert–Kunz の存在）、Ma Theorem 2.4（Roberts）、Stacks 0AZZ（Koszul の Euler 特性）、Cohen–Gabber の4つを入力にすれば、残りは [21] §3.2 の初等的な議論（トレース、塔の有限段、Lemma 2.4）。
- 混標数の Theorem 2.5 は CLMST の Cor. 4.0.4、Prop. 4.0.10、Prop. 4.0.14 を入力にする。これらは Bhatt–Scholze の perfectoid 化と almost purity に依存するので、証明せずに引用する（層 3b）。
- 引用する文献：Kurano–Shimomoto Thm 1.1（Cohen–Gabber）、Cohen の構造定理（係数環）、Monsky、Ma Thm 2.4（Roberts）、Stacks 0AZZ（Koszul の Euler 特性）、Faltings Appendix 2（Lemma 2.3）、CLMST（Cor. 4.0.4、Prop. 4.0.10、4.0.14）。どれも入力の束にはせず、名前付きの `sorry` 定理として置く（`PLAN.md` §1.1）。実際に置いた引用の一覧は `section-2-plan.md`。
