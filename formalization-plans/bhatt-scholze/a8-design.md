# A8 の設計：almost purity と整代数の perfectoid 化の離散性（原典 Lemma 10.5、Thm 10.9、Thm 10.11、Lemma 10.12、2026-11-02）

概要：E3 を消す道筋の単位 A8。原典 BS 著者版 §10.2：R perfectoid、J ⊂ R 有限生成、S が V(J) の外で有限エタールな有限表示有限 R 代数なら
S_perfd は離散で perfectoid、S → S_perfd は V(J) の外で同型、R/p^n → S_perfd/p^n は almost 有限射影・almost 不分岐（Thm 10.9、almost purity）。
その J-almost 版（S_perfd が J-almost 連結）を先に示し、そこから **Thm 10.11**：R → S が整写像の p 完備化なら Δ_{S/A,perf} は離散な完全
p 完備 δ-A 代数で、S_perfd は離散な perfectoid 環。これが E3 の欄 `integral`。Thm 10.11 の証明は有限表示有限に帰着し（filtered 余極限）、
Cor 8.14 により連結性を示せばよく、Lemma 10.12 の層別 g_1,…,g_n の長さの帰納法：n = 1 は S_red が有限エタールで perfectoid、n > 1 は
Prop 8.13 と帰納法の仮定で (S/g_1)_perfd が連結、Lemma 10.5 で g_1-almost 連結性に帰着し、Cor 8.12 と Thm 10.9 の J-almost 版で示す。
方針：E3 に要るのは Thm 10.11 と、そのための Thm 10.9 の **J-almost 連結性の部分だけ**（almost 有限射影性・不分岐性は不要）。
その部分は、原典の証明の (1)(2)（Cor 8.12 で整な取り替え、Thm 7.14 で絶対整閉な基底、有限エタール被覆の Zariski 局所分裂、自明な被覆との比較）
だけで示せ、(3)(4)（Σ_r Galois 閉包 [And18b, Lemma 1.9.2]、Prop 10.8 [And18b, Prop 1.9.1]、次数一定の開閉分解）は要らない（§3.2、決定項目 1）。
Lemma 10.12 は古典的な可換環論の独立した単位（A8-3）。§10.1（Def 10.1、Prop 10.2、Lemma 10.3、Rem 10.7）は形式化済み（B5）。
規約：S は離散（E3 の始域）。R は Not 8.1 の perfectoid 環。J-almost は既存の `IsAlmostZero`・`perfectoidIdeal`（Almost/）。Lean の名前は仮。ビルドしない。
使われ方：E3 の `integral`。環の帰結 `exists_perfectoidization_of_integral`・`_of_finite` は界面から証明済み（`Perfectoidization/Derived/IntegralExistence`）。

## 0. 範囲と前提

- 含む：Prop 10.4 の必要な部分（複体の J-almost 零 ⇔ J_perfd ⊗̂^L M = 0）、Lemma 10.5（連結性の判定）、J-almost の基本（根基で不変、
  J-almost ⇔ 全生成元 f_i で (f_i)-almost、忠実平坦な基底変換での反映）、Thm 10.9 の J-almost 連結性、Lemma 10.12、Thm 10.11、E3 の `integral`。
- 含まない：Thm 10.9 の almost 有限射影性・almost 不分岐性、Def 10.6・Prop 10.8（[And18b]）、Rem 10.10・10.13、Prop 10.2・10.4 の圏同値（D14）。
- 前提：A4（Def 8.2、Lemma 8.4）、A5（Prop 8.5 の極限の形、filtered 余極限、G-A6-2 の有限積）、A6（Cor 8.12 `perfectoidization_excision`）、
  A7（Prop 8.13 `perfectoidization_relativeTensor`、Cor 8.14、`perfectoidization_of_perfectoid`）、既存：Thm 7.14（`Semiperfectoid/CompatibleRoot*`）、
  絶対整閉環上の有限エタール代数の分裂（`CommutativeAlgebra/AbsolutelyIntegrallyClosed/Etale`：`finiteEtaleAway_exists_finite_cover` ほか）、
  almost（`Almost/PerfectoidAlmost`・`Lemma103`：`perfectoidIdeal_isAlmostZero_of_completedTensor_isZero`、`lemma103_perfectoidTensor`、
  `perfectoidIdealMod_idempotent`）、Mathlib：`etaleLocus`・`isOpen_etaleLocus`、`Algebra.Etale.iff_exists_algEquiv_prod`（体上）、
  `IsPurelyInseparable`・`separableClosure`、`minimalPrimes`、noetherian 帰納法。

## 1. 原典の項目と形式化の対応

| 原典 | 扱い | Lean の形（§2） | 既存・不足 | 単位 |
| --- | --- | --- | --- | --- |
| Prop 10.4 | 定理（必要な部分）：導来 p 完備な複体 M について、M が J-almost 零（全 H^i が J-almost 零）⇔ J_perfd ⊗̂^L_R M = 0 | `isAlmostZero_iff_completedTensor_isZero` | 加群版は既存（B5）。複体は truncation の帰納 | A8-1 |
| Lemma 10.5 | 定理：p 完備な M が連結 ⇔ M ⊗̂^L R/J_perfd が連結かつ M が J-almost 連結 | `connective_iff_almost` | Prop 10.4、三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M | A8-1 |
| J-almost の基本 | 定理：J-almost は √J で不変；J = (f_1..f_r) で J-almost ⇔ ∀i (f_i)-almost；忠実平坦な perfectoid の基底変換 R → R′ で反映（(JR′)_perfd = J_perfd R′） | `isAlmostZero_radical`、`isAlmostZero_iff_forall_gen`、`isAlmostZero_baseChange_iff` | Rem 10.7 の隣、Prop 8.13 | A8-1 |
| Thm 10.9（J-almost 連結性） | 定理（結論を弱め、証明を短縮）：S 有限 R 代数、S[1/f] が R[1/f] 上有限エタール（f ∈ J の各生成元）⇒ S_perfd は J-almost 連結 | `perfectoidization_almostConnective_of_finiteEtaleAway` | Thm 7.14、`finiteEtaleAway_exists_finite_cover`、Cor 8.12、G-A6-2、`perfectoidization_of_perfectoid` | A8-2 |
| Thm 10.9（残り） | 不要（almost 有限射影・不分岐、V(J) の外の同型、Galois） | — | — | — |
| Def 10.6、Prop 10.8 | 不要（決定項目 1） | — | — | — |
| Lemma 10.12 | 定理（原典どおり）：有限表示有限 R → S（Z_(p) 代数）に層別 g_1..g_n：(1) 単位イデアル、(2) R_i → S_i は有限エタール → 普遍同相、(3) 各 R_i で p = 0 または p 可逆 | `exists_finiteEtaleStratification` | Mathlib（noetherian、極小素イデアル、分離閉包、エタール locus）、G-A8-4〜7 | A8-3 |
| Thm 10.11 | 定理（S 離散、整写像の p 完備化）：Δ_perf 離散、S_perfd 離散で perfectoid | `prismaticPerfection_discrete_of_integral`、`perfectoidization_isIntegralPerfectoid_of_integral` | §3.3 | A8-4 |
| E3 `integral` | 構成（任意の整 S、S^∧ 経由） | `e3Integral` | D41、`completionRing`、filtered 余極限 | A8-4 |

## 2. 定義の形

### 2.1 J-almost（既存の上）と Lemma 10.5

- J ⊂ R 導来 p 完備（E3 では有限生成）、J_perfd := ker(R → (R/J)_perfd)（既存 `perfectoidIdeal`、Thm 7.4 で全射）。M（D(R)、導来 p 完備）が
  J-almost 連結 ⇔ H^i(M) が J-almost 零（∀ i > 0）。
- `isAlmostZero_iff_completedTensor_isZero`（Prop 10.4 の必要部分）：加群版（既存 `perfectoidIdeal_completedTensor_isZero_of_isAlmostZero`・
  `_of_completedTensor_isZero`）を有界な複体に truncation の帰納で、非有界は完備性と truncation の極限・余極限で（原典の "writing any object as a
  limit and colimit of its truncations"）。
- `connective_iff_almost`（Lemma 10.5）：⇒ は ⊗̂ R/J_perfd が連結性を保つ。⇐：三角形 J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M で、M が J-almost 連結なら
  J_perfd ⊗̂ τ^{>0} M = 0（Prop 10.4）、J_perfd ⊗̂ τ^{≤0} M 連結、よって J_perfd ⊗̂ M 連結。注：原典の (R/J)_perfd ⊗̂ M と R/J_perfd ⊗̂ M は
  (R/J)_perfd = R/J_perfd（Thm 7.4）で同じ。

### 2.2 Thm 10.9 の J-almost 連結性（§3.2 の筋で）

- 主張：R perfectoid、S **有限表示有限** R 代数（原典どおり。R 加群として有限表示なので導来 p 完備：脚注 19、既存 `isModuleComplete_of_finitePresentation`）、
  f_1,…,f_r ∈ R、J := (f_1,…,f_r)、各 i で S[1/f_i] が R[1/f_i] 上有限エタール ⇒ S_perfd は J-almost 連結。
  **W9-III-01（致命、2026-11-03 修復）**：以前の「S 有限 R 代数（自動的に導来 p 完備）」は偽。反例：V = ℤ_p[p^{1/p^∞}]^∧、R = ∏_{n≥0} V（perfectoid）、
  I = ⊕ V（有限台）、M = R/I は巡回 R 加群だが、x_k := [(0,…,0,1,p,p²,…)]（n ≥ k で p^{n−k}）は p x_{k+1} = x_k、x_0 = [(1,p,p²,…)] ≠ 0 なので R[1/p] → M が非零、
  M は導来 p 完備でない。S = R × M は有限 R 代数で D(e_0)（e_0 = (1,0,…) ∈ I）上は階数 1 の自明な有限エタールだが非完備。有限性から完備性は出ない。
  Thm 10.11 は有限表示有限に帰着する（§3.3 の 1）ので E3 の始域は狭まらない。
- 原典の Thm 10.9 の仮定「有限表示有限で Spec S → Spec R が V(J) の外で有限エタール」は、V(J) の有限個の主開集合 D(f_i) による被覆で
  この形になる（J の生成元を取り替えてよい：J-almost は √J で不変）。

### 2.3 Lemma 10.12

原典どおりの主張。`UniversalHomeomorphism` は「整・全射（Spec）・radicial（普遍単射）」で定義する（G-A8-4、要確認：Mathlib に相当物があるか）。
Z_(p) 代数の条件 (3) は (1)(2) の層別を (pg_1, g_1, pg_2, g_2, …) で細分して得る（原典）。

### 2.4 Thm 10.11 と E3 の欄

- `prismaticPerfection_discrete_of_integral`・`perfectoidization_isIntegralPerfectoid_of_integral`：S = (整 R 代数)^∧。§3.3。
- `e3Integral (S) (h : Algebra.IsIntegral R S) : IsDiscrete R (e3Perfd S) ∧ IsIntegralPerfectoid (e3H0RingData.ringFunctor.obj S) p`：
  `e3Perfd S = (S^∧)_perfd`（D41）、S^∧ は整写像の p 完備化、Thm 10.11、`e3H0_of_complete`（A4-3）。

## 3. 証明の筋

### 3.1 J-almost の基本

- √J 不変：(R/J)_perfd は perfectoid なので被約、よって (R/J)_perfd = (R/√J)_perfd（普遍性）、J_perfd = (√J)_perfd。
- 生成元：J-almost 零 ⇔ ∀i (f_i)-almost 零。⇐：J_perfd ⊗̂ M = 0 を示す。Q := R/f_1 ⊗̂^L_R ⋯ ⊗̂^L_R R/f_r（animated な完備押し出し）とすると π_0 Q = R/J だが **Q ≠ R/J**（W9-III-03：p ねじれなしの R で f_1 = f_2 = p なら
  R/p ⊗^L R/p ≃ [R/p →0→ R/p] で H^{−1} = R/p ≠ 0、p で零化されるので完備化しても消えない）。Prop 8.5 系 4（perfd は π_0 だけによる）で Q_perfd ≃ (R/J)_perfd、
  Prop 8.13 で (R/J)_perfd ≃ (R/f_1)_perfd ⊗̂_R ⋯（単位と両立）、
  J_perfd ⊗̂ M の消滅を各 (f_i)_perfd ⊗̂ M = 0 から（Lemma 10.3 の形 (R/J)_perfd ⊗̂ J_perfd = 0 と、J_perfd ⊗̂ M → M → (R/J)_perfd ⊗̂ M）。紙 1。
- 忠実平坦な基底変換：R → R′ perfectoid、p 完備忠実平坦。(R′/JR′)_perfd = (R/J)_perfd ⊗̂_R R′（Prop 8.13）⇒ (JR′)_perfd = J_perfd R′（Thm 7.4 の全射性と
  平坦性）。M が J-almost 零 ⇔ M ⊗̂_R R′ が JR′-almost 零（忠実平坦で零性を反映）。

### 3.2 Thm 10.9 の J-almost 連結性（原典 (1)(2) の筋、(3)(4) なし）

1. 一つの生成元 f に帰着（3.1）：S_perfd が (f_i)-almost 連結（∀i）を示せばよい。以下 J = (f)、S[1/f] は R[1/f] 上有限エタール。
2. 基底を絶対整閉に（Thm 7.14、既存）：R → R′ p 完備忠実平坦、R′ perfectoid・絶対整閉。(S ⊗̂_R R′)_perfd = S_perfd ⊗̂_R R′（Prop 8.13）と 3.1 の反映で、
   R′ 上で示せばよい。以下 R は絶対整閉。
3. Zariski 局所分裂（既存 `finiteEtaleAway_exists_finite_cover`）：S[1/f] は R[1/f] 上有限エタールなので、有限個の h_1,…,h_m ∈ R で
   D(f) = ∪ D(f h_j)、各 j で S[1/(f h_j)] ≅ R[1/(f h_j)]^{r_j}（R 代数として）。J′ := (f h_1, …, f h_m) は √J′ = √(f)（D(f) = ∪D(fh_j)）なので
   (f)-almost = J′-almost（3.1）、再び一つの生成元 g := f h_j に帰着：S[1/g] ≅ R[1/g]^r。
4. 自明な被覆との比較（Cor 8.12）：S′ := S と R^r の生成する R[1/g]^r の部分 R 代数（S と R^r の像で生成）。S′ は R 上整（S・R^r が整）、
   S → S′ と R^r → S′ は g の外で同型（両辺とも S′[1/g] = R[1/g]^r）。よって `ArcOutside` の条件（g を殺さない、すなわち g の像が**非零**（可逆とは限らない）な付値環 V への写像の
   一意な延長）を満たす（**W9-III-02**：局所化の同型だけでは出ない。反例：S = V = F_p[t^{1/p^∞}] の t 進完備付値環、S′ = V[1/t]、g = t で id : S → V は S′ に
   延びない。ここでは S → S′ が**整**なので、S → V から S[1/g] = S′[1/g] → Frac(V) を作り、S′ の元は S 上整なので像は V 上整、付値環 V は Frac(V) で整閉なので
   像は V に入る；一意性は Frac(V) への射の一意性と V ↪ Frac(V)。R^r → S′ も同じ。G-A8-3″）。Cor 8.12 の引き戻し四角形で fib(S_perfd → S′_perfd) ≃ fib((S/g)_perfd → (S′/g)_perfd)。右辺は (R/g)_perfd 加群
   （関手性）なので (g)-almost 零。よって S_perfd → S′_perfd は (g)-almost 同型。同様に (R^r)_perfd → S′_perfd も。
5. (R^r)_perfd = R^r（G-A6-2 の有限積と `perfectoidization_of_perfectoid`）は離散。よって S′_perfd、したがって S_perfd は (g)-almost 連結。
   注（**W9-III-01 で修復**）：Cor 8.12 の前提（S・S′・(g) の導来 p 完備性）。S：有限表示有限なので R 加群として有限表示、既存 `isModuleComplete_of_finitePresentation`。
   (g)・gS・gR^r：完備な加群上の乗法写像の像（`isModuleComplete_ker`・`isModuleComplete_coker`）。S′：有限表示とは言えないので構成固有の計算（G-A8-3′）——
   S[1/g] ≅ R[1/g]^r の標準冪等元 e_j と S の有限個の R 加群生成元 s_a について、S′ は R 加群として有限個の e_j s_a で生成される（Σ_j e_j·image(S) は乗法で閉じ、
   両方の像を含む）。よって S′ は有限 R 加群で S → S′、R^r → S′ は整。完備性：R は被約（perfectoid）なので ann(g^N) = ann(g)、R の R[1/g] での像 R̄ = R/ann(g) は
   導来 p 完備（核・余核の閉性）；生成元の分母を払う N で g^N S′ ⊂ R̄^r、g は R[1/g]^r で単元なので S′ ≅ g^N S′（R 加群）、g^N S′ は有限自由加群から R̄^r への
   写像の像で導来 p 完備。既存の `isModuleComplete_pi`・`_ker`・`_coker`（HomologicalAlgebra/DerivedCompletion/ModuleClosure.lean）で供給できる。
   S′ の有限表示性は要らない。

### 3.3 Thm 10.11

1. 整 R 代数 S は有限表示有限 R 代数の filtered 余極限（R[x_1..x_k]/I で I を有限生成部分イデアル（モニック関係を含む）で近似）。perfd は filtered
   余極限と可換（A5-4）、離散性・perfectoid 性は p 完備化した filtered 余極限で保たれる（G-A8-8：perfectoid 環の p 完備化した filtered 余極限は
   perfectoid、p^∞ ねじれ有界なので導来完備化は離散）。以下 S は有限表示有限。
2. Cor 8.14（A7-2）：S_perfd が連結なら離散で perfectoid、Δ_perf も離散で完全 δ 環。連結性を Lemma 10.12 の層別の長さ n で帰納。
3. n = 1：R → S_red は有限エタール（Lemma 10.12 (2) の普遍同相部分が同型：p = 0 なら R[1/g_1] = R は完全（R perfectoid は被約、p = 0 で
   Frobenius 全射）で T_1 も完全、完全環から被約環への普遍同相は同型（G-A8-5）；p 可逆なら構成から同型）。有限エタール R 代数は perfectoid
   （G-A8-6）。S_perfd ≃ (S_red)_perfd：perfectoid 環は被約なので Perfd_{S/} = Perfd_{S_red/}、Prop 8.5 の極限の形（原典は Cor 8.11 の arc 層化、D64）。
   (S_red)_perfd = S_red（`perfectoidization_of_perfectoid`）は離散。
4. n > 1：R_1 := (R/g_1)_perfd（perfectoid、Thm 7.4 で R/g_1 の商）。帰納法の仮定を R_1 → S ⊗_R R_1（有限表示有限、層別は g_2..g_n の像、
   条件は基底変換で保たれる、紙 3）に当てて (S ⊗̂_R R_1)_perfd 連結、Prop 8.13 で (S/g_1)_perfd = S_perfd ⊗̂_R (R/g_1)_perfd = (S ⊗̂_R R_1)_perfd。
   Lemma 10.5（J = (g_1)）で S_perfd の連結性は g_1-almost 連結性に帰着。
5. g_1-almost 連結性：Lemma 10.12 (2) で R[1/g_1] → S[1/g_1] → S_red[1/g_1] の合成は有限エタール（3 と同じ議論で T_1 ≅ S_red[1/g_1]）。
   S′ := R の S_red[1/g_1] における整閉包、S → S′（S_red → S_red[1/g_1] ⊂ S′ の合成）は整 R 代数の射で g_1 の外で同型（S′[1/g_1] = S_red[1/g_1]）。
   Cor 8.12 で S_perfd → S′_perfd は g_1-almost 同型（3.2 の 4 と同じ）。S′_perfd の g_1-almost 連結性：S′ は有限表示有限 R 代数 S″（S″[1/g_1] ≅ S_red[1/g_1]）
   の filtered 余極限（S′ = colim の有限生成部分代数、各々 S_red[1/g_1] を g_1 を可逆にして復元、紙 4）、各 S″ に 3.2（J = (g_1)）、perfd と
   almost 連結性は filtered 余極限で保たれる。

### 3.4 Lemma 10.12

原典の証明を追う：
1. 表示による近似：R → S 有限表示有限 S = R[x_1..x_k]/(h_1..h_m)（モニック関係を含む）。係数を含む有限生成 Z_(p) 部分代数 R_0 ⊂ R と
   S_0 := R_0[x]/(h) で S = S_0 ⊗_{R_0} R。層別は R_0 で作り R へ底変換（(1)(2)(3) は底変換で保たれる。被約商の違いは冪零拡大＝普遍同相で吸収。紙 5）。
2. R_0 noetherian：極小素イデアル 𝔭_1..𝔭_r（有限個）、K := ∏ κ(𝔭_i) は (R_0)_red の全商環。K ⊗ S_0 の被約化は有限被約 K 代数＝有限体拡大の有限積
   L_i、各 κ(𝔭_i) → L_i は分離閉包 M_i を経て κ → M_i 有限エタール（`Etale.iff_exists_algEquiv_prod`・分離拡大）、M_i → L_i 純非分離＝普遍同相
   （`IsPurelyInseparable`）。
3. 広げる：有限エタール性と普遍同相性を全商環から或る D(g_1) に広げる（エタール locus が開（Mathlib `isOpen_etaleLocus`）、有限表示の近似、
   普遍同相の判定 G-A8-4 を有限個の等式で）。これで開層 R_1 = (R_0)_red[1/g_1] → S_1 を得る。
4. noetherian 帰納：R_0/(g_1) → S_0/(g_1) に適用。
5. (3) は (pg_i, g_i) による細分。

## 4. 必要な一般論（G-A8）

| # | 内容 | 既存 | 使う箇所 |
| --- | --- | --- | --- |
| G-A8-1 | Prop 10.4 の複体版（truncation の帰納と極限・余極限）、Lemma 10.5 | 加群版は既存（B5） | A8-1 |
| G-A8-2 | J-almost の基本：√J 不変、生成元ごと（animated テンソル Q → π_0 Q = R/J → Prop 8.5 系 4 → Prop 8.13。離散商の等式ではない、W9-III-03）、忠実平坦な基底変換で反映 | Rem 10.7 の既存の隣 | A8-1、3.2 |
| G-A8-3 | ~~有限 R 加群は導来 p 完備~~（**偽**、W9-III-01 の反例 R = ∏V、R/⊕V）。正：**有限表示** R 加群は導来 p 完備（既存 `isModuleComplete_of_finitePresentation`）；完備な加群の核・余核・有限積（既存 `ModuleClosure`）；主イデアル (g)・gS・gR^r は乗法写像の像 | `HomologicalAlgebra/DerivedCompletion/{FinitePresentationComplete,ModuleClosure}.lean` | 3.2 の 4、Cor 8.12 の前提 |
| G-A8-3′ | 比較環 S′ の有限性（e_j s_a で生成、S → S′・R^r → S′ は整）と導来 p 完備性（R 被約で R̄ = R/ann(g) 完備、S′ ≅ g^N S′ ⊂ R̄^r）。W9-III-01 の修復計算（Codex 第 3 部で ○） | なし | 3.2 の 4 |
| G-A8-3″ | 整写像 S → S′ が g の外で同型（S[1/g] ≅ S′[1/g]）なら `ArcOutside`（Frac(V) へ延長し、整閉性で V へ）。局所化の同型だけでは不成立（W9-III-02 の反例）。界面の「g 非零」を「g 可逆」に弱めない | なし（Mathlib `ValuationRing` の整閉性） | 3.2 の 4 |
| G-A8-4 | 普遍同相（整・Spec 全射・radicial）の定義と、標数 p での判定（像の p 冪、核の冪零）、底変換・合成・冪零拡大 | なし（Mathlib に部分品？要確認） | Lemma 10.12、3.3 |
| G-A8-5 | 完全 F_p 環から被約環への普遍同相は同型 | なし | 3.3 の 3・5 |
| G-A8-6 | perfectoid 環上の有限エタール代数は perfectoid（S/p で相対 Frobenius 同型、W(S^♭) = W(R^♭) のエタール持ち上げ、ker θ_S = d） | なし（要確認：`Prism/Perfectoid` の隣） | 3.3 の 3 |
| G-A8-7 | 層別の底変換不変性（有限エタール・普遍同相・被約商）、全商環からの広げ（noetherian） | Mathlib（部分） | Lemma 10.12 |
| G-A8-8 | perfectoid 環の p 完備化した filtered 余極限は perfectoid で、導来 p 完備化は離散（p^∞ ねじれ有界） | 要確認（`Prism/Perfectoid`） | 3.3 の 1 |
| G-A8-9 | 整 R 代数は有限表示有限 R 代数の filtered 余極限 | Mathlib（`Algebra.FinitePresentation`、要確認） | 3.3 の 1 |

## 5. 原典との差

| 番号 | 原典 | 本書 | 評価 |
| --- | --- | --- | --- |
| D63 | Thm 10.9：almost 有限射影・不分岐・V(J) の外の同型・Galois まで。証明 (3)(4) で Σ_r Galois 閉包（[And18b, Lemma 1.9.2]）と Prop 10.8（[And18b, Prop 1.9.1]）、次数一定の開閉分解 | **J-almost 連結性だけ**を、原典 (1)(2) の議論（Cor 8.12・Thm 7.14・Zariski 局所分裂・自明な被覆 R^r との比較）で示す。(3)(4) と [And18b] は使わない | 結論を弱め、証明を短縮。外部引用が一つ減る。ノート（BS-0 の案）が予想した簡略化。決定項目 1。Codex 第 3 部：W9-III-01〜03 の修復後も (3)(4) を省く方針は維持できる（Galois 作用はこの計算に使われない） |
| D64 | Thm 10.11 の n = 1 で S_perfd ≅ S_red,perfd は Cor 8.11（arc 層化） | perfectoid 環は被約なので Perfd_{S/} = Perfd_{S_red/}、Prop 8.5 の極限の形 | 同じ内容。Cor 8.11 は D55 で述べていない |
| D65 | Lemma 10.12 は Z_(p) 代数の有限表示有限射 | 原典どおり（noetherian 近似は表示で） | 差なし。古典的可換環論の独立単位 |
| D66 | Prop 10.4 は圏同値まで | 必要な「J-almost 零 ⇔ J_perfd ⊗̂ M = 0」だけ（D14 と同じ方針） | 必要な分だけ |
| D67 | S は整写像の p 完備化（Thm 10.11） | E3 の欄は任意の整 S で S^∧ 経由（D41）。Thm 10.11 は原典の形 | 同じ |

## 6. 単位と順序

| 単位 | 内容 | 依存 |
| --- | --- | --- |
| A8-1 | Prop 10.4 の複体版、Lemma 10.5、J-almost の基本（G-A8-1・2） | 既存 Almost/、A7（Prop 8.13） |
| A8-2 | Thm 10.9 の J-almost 連結性（§3.2） | A8-1、A6（Cor 8.12）、A7、既存 Thm 7.14・aic エタール |
| A8-3 | Lemma 10.12（§3.4、G-A8-4・5・7） | Mathlib |
| A8-4 | Thm 10.11（§3.3）、E3 の `integral`、G-A8-6・8・9 | A8-1〜A8-3、A5、A7 |

骨組みは A8-1 → A8-2 → A8-4 → A8-3（A8-3 は独立なので後回し可。Codex 向きの古典的単位）。

## 7. 決定事項

決定（2026-11-02、ユーザー）：1〜5 とも推奨どおり。
- 1：Thm 10.9 は J-almost 連結性だけを原典 (1)(2) の議論で示す。(3)(4) と [And18b] は使わない（D63）。
- 2：Lemma 10.12 は原典の形で独立した古典的単位 A8-3（noetherian 近似は表示で）。
- 3：n = 1 は Perfd_{S/} = Perfd_{S_red/} と Prop 8.5（D64）。
- 4：有限エタール代数が perfectoid であること（G-A8-6）は A8 の中で証明する。
- 5：Prop 10.4 は必要な同値だけ（D66）。

**W9-III（2026-11-03、Codex 第 3 部の推奨 (a) を適用）**：Thm 10.9 の入力は原典どおり**有限表示有限**に戻す（(b)「任意の有限 S を completionRing 経由で残す」は
採らない。E3 の始域は狭まらない：Thm 10.11 は §3.3 の 1 で有限表示有限に帰着する）。S′ の完備性は構成固有の計算 G-A8-3′ で供給。`ArcOutside` の補題には整性を
入れる（G-A8-3″。界面の「g 非零」を「g 可逆」に弱めない）。生成元の式は animated テンソル → π_0 → perfd の比較に置き換える（W9-III-03）。新しい黒箱は不要。

相談した選択肢（記録）：

1. **Thm 10.9 の扱い（D63）**：J-almost 連結性だけを原典 (1)(2) の議論で示し、(3)(4)（Σ_r Galois 閉包、Prop 10.8 [And18b]）は使わない（推奨。
   結論を E3 に要る分に弱め、証明は原典の前半をそのまま使う。既存の `finiteEtaleAway_exists_finite_cover` が使える）／原典どおり (3)(4) も追い、
   Prop 10.8 を [And18b] の引用（`sorry`）で置く。
2. **Lemma 10.12**：原典の形で独立した古典的単位 A8-3 とし、noetherian 近似は表示で行う（推奨。Codex に出せる形）／主張を Thm 10.11 に要る形に
   絞る（絞っても短くならない）。
3. **n = 1 の S_perfd ≅ S_red,perfd（D64）**：Perfd_{S/} = Perfd_{S_red/} と Prop 8.5 で（推奨）／Cor 8.11 を述べて使う（D55 の変更）。
4. **G-A8-6（有限エタール代数は perfectoid）**：A8 の中で証明する（推奨。エタールの Frobenius 持ち上げと Witt ベクトル、初等的）／引用。
5. **Prop 10.4（D66）**：必要な同値だけ（推奨、D14 と同じ）／圏同値まで。

## 8. 紙で確かめる項目

1. 3.1：J-almost ⇔ 生成元ごと（Lemma 10.3 の形で J_perfd ⊗̂ M の消滅を導く段）。Codex 第 3 部で ○（W9-III-03 の訂正 Q → π_0 → perfd の上で）。
2. 3.2 の 4：S′ の R 上の有限性と導来 p 完備性（G-A8-3′）、`ArcOutside` の条件（**整写像**＋局所化で同型 ⇒ 付値環への一意延長、G-A8-3″）、(S′/g)_perfd が (R/g)_perfd 加群であること。Codex 第 3 部：現行の一般補題は ×（W9-III-01・02）、修復計算は ○。
3. 3.3 の 4：層別の条件の底変換（R → R_1 = (R/g_1)_perfd）での保存。
4. 3.3 の 5：S′ を有限表示有限 S″ で近似して S″[1/g_1] ≅ S_red[1/g_1] にできること。
5. 3.4 の 1：被約商の違いを普遍同相で吸収する箇所、(3) の細分。
6. 3.3 の 1：perfectoid の p 完備化した filtered 余極限の perfectoid 性と導来完備化の離散性（G-A8-8）。
