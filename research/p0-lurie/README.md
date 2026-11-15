# P⁰（Lurie の構成）の現状把握と整理

作成：2026-11-15（調整役）。目的：BS Lemma 8.4 が引く P⁰（DAG XIII Construction 2.2.6）を、文献どおりに定義するために何が要るかを整理する。計画の決定はまだしない（ユーザー：まず現状把握と整理、そのうえで文献に沿って基盤を整えながら進める）。

原典の本文は 11-15 に取得して照合した：Lurie, DAG XIII（math.ias.edu/~lurie/papers/DAG-XIII.pdf）§2.1・§2.2、Nikolaus–Scholze, On topological cyclic homology（arXiv:1707.01799）I.1・III.1。BS の引用は [Lur11, Rem 2.2.7]。

## 1. 文献の鎖（定義の順）

### 1.1 Tate 構成（DAG XIII §2.1、NS I.1）

- **群作用つきの対象**：G を有限群、C を ∞ 圏とする。G 作用つきの対象は関手 BG → C（C^{BG} の対象）。
- **homotopy orbit・fixed point**：f : BG → ∗ に沿う左 Kan 延長 f_! と右 Kan 延長 f_*、すなわち colim と lim（NS Def I.1.10 は相対有限 groupoid f : X → Y で一般に）。
- **norm 写像** Nm_G : X_{hG} → X^{hG}（DAG XIII Construction 2.1.18、NS Construction I.1.7）。C が preadditive で BG 添字の極限・余極限を持つときに定義される。通常の圏の nerve なら「Σ_g φ_g」の式で決まる（DAG XIII 2.1.22 の直後の注意）。
- **Tate 構成**：C が安定で BG 添字の極限・余極限を持つとき、X^{tG} := cofib(Nm_G : X_{hG} → X^{hG})（DAG XIII Def 2.1.23、NS Def I.1.13）。
- **誘導された作用では消える**：N = i_! M（自明な部分群からの誘導）なら norm は同値、よって N^{tG} ≃ 0（DAG XIII Ex 2.1.25）。Prop 2.2.3・NS Prop III.1.1 の証明の芯。

### 1.2 拡大冪と Tate 対角（DAG XIII §2.2、NS III.1）

- **拡大冪**（DAG XIII Constr 2.2.1）：単体集合 K の n 次拡大冪 K^{(n)} := (K^n × EΣ_n)/Σ_n。C が対称モノイダル ∞ 圏なら、C を Cat_∞ の可換代数対象と見て θ : C^{(n)} ≃ Sym^n(C) → C がある。対象 C ∈ C について BΣ_n → C が Σ_n 等変な対象 C^{⊗n} を分類し、Sym^n(C) := colim（homotopy orbit）。
- **T̂_η**（Constr 2.2.2）：η : G → Σ_n に対し C ↦ (C^{⊗n})^{tG}。η が Z/p の自分への平行移動なら T̂_p。
- **exact 性**（Prop 2.2.3、NS Prop III.1.1）：C が安定・有限 groupoid 添字の極限と余極限・テンソルが各変数で exact なら T̂_p は exact。証明は (Δ¹)^p の巡回作用で不変な部分図式への分解と、中間の段が誘導された作用で Tate が消えること。
- **可換代数への適用**（Rem 2.2.4）：A ∈ CAlg(C) に対し自然な射 T̂_η(A)[−1] ≃ (A^{⊗n})^{tG}[−1] → (A^{⊗n})_G → Sym^n(A) → A。A について関手的で、自然変換 T̂_η[−1] ∘ θ → θ（θ は忘却 CAlg(C) → C）。
- **T_p（Ex 2.2.5、k 加群の場合）**：LMod_k 上で T̂_p は exact だが filtered 余極限と交換しない。T_p := T̂_p|_{perfect} の左 Kan 延長。T_p は余極限と交換し、自然変換 T_p → T̂_p は perfect な M で同値。HA A.7.1.2.4 により T_p(M) ≃ B ⊗_k M、B ≃ T̂_p(k) ≃ k^{tG}（k ≃ k^{⊗p} に G は自明に作用）。
- **Tate 対角（NS の形）**：Sp 上では Fun^Ex(Sp,Sp) で id → F の自然変換は F(S) の点で決まる（Prop III.1.2、HA 1.4.2.23 と Yoneda）。Tate 対角 Δ_p : id → T_p は S → S_{hC_p} → S^{tC_p} に対応するもの（Def III.1.4）。Lurie の Ex 2.2.5 の T_p と B[−1] の射は、この k 加群版に当たる。

### 1.3 Construction 2.2.6（P⁰ の定義）と性質

k を離散可換環、G = Z/p とする。
- π_i k^{tG} ≃ Ĥ^{−i}(G; k)（Tate コホモロジー）。π_1 k^{tG} ≃ Ĥ^{−1}(G; k) = ker(norm : k → k) = ker(p·)。
- k の標数が p なら 1 ∈ k が π_1 k^{tG} の標準の元を与え、**右 k 加群スペクトルの射 e : k → B[−1]** を誘導する。
- A ∈ CAlg_k に対し、スペクトルの射
  **P⁰ : A ≃ k ⊗_k A → B[−1] ⊗_k A ≃ T_p(A)[−1] → T̂_p(A)[−1] = (A^{⊗p})^{tG}[−1] → (A^{⊗p})_G → Sym^p(A) → A**。
- A について関手的なので、**P⁰ は忘却 CAlg_k → Sp の自己変換**（= 私たちの D79 (i) の型 `FunctorHom (forget ≫ toSpectra) (forget ≫ toSpectra)`）。
- **Rem 2.2.7**：η ∈ π_n A は k[n] → A で表され、P⁰(η) は k[n] → T_p(k[n])[−1] ≃ T̂_p(k[n]) ≃ (k[pn]^{tG})[−1] → k[pn]_G → A^{⊗p}_G → Sym^p(A) → A。n > 0 なら k[n] → k[pn]_G は零ホモトピック（π_n k[pn]_G ≃ H_{n−pn}(G;k) = 0）ので P⁰(η) = 0。n = 0 なら P⁰ : π_0 A → π_0 A は Frobenius x ↦ x^p。
- **Warning 2.2.8**：P⁰ はスペクトルの射で、k 加群スペクトルの射ではない（Frobenius は k 線形でない）。**Warning 2.2.10**：A が離散でないと P⁰ は E∞ の射に持ち上がらないし、環準同型にもならないことがある。
- **Rem 2.2.9**：x ∈ Ĥ^{n−1}(Z/p; k) ごとに P(x) : A → A[n] が作れ、拡張 Steenrod 代数を生成する。

### 1.4 BS Lemma 8.4 が使うこと

1. levelwise Frobenius（単体的余単体的 F_p 代数の）がその実現の上で P⁰ を誘導する。
2. Δ_perf/p は P⁰ が可逆に作用する E∞-F_p 代数。
3. Rem 2.2.7 の消滅で Δ_perf/p ∈ D^{≥0}。
4. H⁰ で P⁰ = x^p だから、φ は H⁰(Δ_perf)/p ⊂ H⁰(Δ_perf/p) の Frobenius を持ち上げる → perfect δ 環 → Lemma 2.34。

1 と「完備化をまたぐ」ことは、P⁰ が CAlg の射すべてについて自然（coherent）で、忘却が実現・Tot・完備化の極限・余極限を保つことから出る。原典はこれを明示していない（`research/p0-lurie/` の 11-15 の議論、⑤a 報告 §412〜§420）。

## 2. 定義に要る数学の部品（原典の順）

| # | 部品 | 原典 | 性質 |
| --- | --- | --- | --- |
| M1 | 安定 ∞ 圏 C（= Mod_k または Sp）と、有限 groupoid（BG）添字の極限・余極限 | 2.1 | ∞ 圏の基盤 |
| M2 | norm Nm : X_{hG} → X^{hG} と Tate 構成 X^{tG}、誘導作用で消えること | 2.1.18・2.1.23・2.1.25 | ∞ 圏の基盤 |
| M3 | 対称モノイダル構造：拡大冪 Sym^n(C) → C、対象の Σ_n 等変な C^{⊗n}、巡回部分群への制限 | 2.2.1・2.2.2 | ∞ 圏の基盤（∞ 対称モノイダル圏） |
| M4 | T̂_p の exact 性 | 2.2.3 / NS III.1.1 | M1〜M3 の上の定理 |
| M5 | 可換代数対象 A に対する (A^{⊗p})_G → Sym^p(A) → A の自然な射 | 2.2.4 | E∞ の構造（CAlg(C)） |
| M6 | T_p = perfect からの左 Kan 延長、T_p ≃ B ⊗_k (−)、B ≃ k^{tG} | 2.2.5、HA A.7.1.2.4 | k 加群の ∞ 圏、Ind・compact、双加群 |
| M7 | π_* k^{tG} = Tate コホモロジー、π_1 の標準の元、右 k 加群の射 e : k → B[−1] | 2.2.6 | 計算 |
| M8 | P⁰ の合成と、CAlg_k → Sp の自己変換としての自然性 | 2.2.6 | M5〜M7 |
| M9 | Rem 2.2.7：π_n（n > 0）で 0、π_0 で x^p | 2.2.7 | 計算（k[n] での評価、H_*(G;k)） |
| M10 | 忘却 CAlg_k → Sp が実現・Tot・完備化の極限・余極限を保つこと（BS が暗黙に使う） | — | ∞ 圏と E∞ の模型 |

## 3. 私たちの枠組みとの対応（所在と不足）

（11-15 の調査：コードの棚卸しは下の §3.2。模型の前提：D75 により E∞ 代数は Barratt–Eccles の厳密な模型の局所化、D(A) は `derivedInfinityCategory`、Sp は KST の Ω スペクトル、V = `eilenbergMacLaneDerived`。）

### 3.1 すぐ分かる大きな不足

- **Sp の模型そのものが弱い**：KST の `Sp` の安定性は `NativeLoopComparison`（未証明）を仮定した条件付きで、presentable 性と一般の ∞ 余極限も未確認。原典は C = Sp または Mod_k を安定 ∞ 圏として使うので、ここが土台の最初の穴。D(A) の方は安定・presentable が済んでいる。

- **M3（∞ 対称モノイダル圏）**：`research/einfinity-route/README.md` §3 のとおり、InfinityCategories に ∞-オペラッド・N(Fin_*)・operadic nerve・Day 畳み込み・∞ の対称モノイダル圏は 0 件。Lurie の構成は C を「Cat_∞ の可換代数対象」として扱うので、文字どおりに追うにはこれが要る。
- **M2（Tate 構成）**：fixed point（極限）はあるが orbit（余極限）・norm・Tate はない（⑤a 報告 §94・§110.4）。
- **M6〜M7**：k^{tG} の計算、右加群の射 e、T_p の Kan 延長はない。鎖の段階の周期解像度と係数の seed（⑤a 旧経路）があるだけ。

### 3.2 コードの棚卸し（11-15、読み取りの調査。パスは `SerrePositivity/` から）

**Sp の模型（KST/Spectra）**

| 宣言 | 場所 | 中身・注意 |
| --- | --- | --- |
| `OmegaSpectrum` | KST/Spectra/OmegaSpectrum | BF 方式の Ω スペクトル（段 `level n : PointedKanComplex`、構造射 `sigma`、`omega_condition` は π_* 同型の条件） |
| `Sp := SimplicialNerve OmegaSpectrum`、`sp_quasicategory` | KST/Spectra/CoherentNerve | 単体的圏の coherent nerve |
| `sp_hasZeroVertex`、`sp_hasFiniteLimits` | SpectrumZeroObject・SpectrumFiniteLimits | 零対象・有限極限 |
| `nativeLoop`、`sp_isStable (hB : NativeLoopComparison)` | SpectrumNativeLoopFunctor・D3TailStability | **安定性は条件付き**。`NativeLoopComparison` の本体は未証明（D3ComparisonOutput に「未証明の B の本体が残る」） |
| `OmegaSpectrum.homotopyLimit`、`homotopyLimitCoherentCone_isLimit` | KanSequenceHomotopyLimit ほか | 厳密な図式の homotopy limit が Sp の ∞ 極限錐 |
| `FilteredOmegaSpectrum` | FilteredOmegaSpectrum | filtered 余極限を段ごとに。**Sp の ∞ 余極限としての普遍性は主張しない**と規約に |
| `SpectrumHo.piFunctor (j : ℤ)` | KST/LocalizingInvariants/SpectrumHomotopyFunctor | 整数次数のホモトピー群 |
| `stableFiberLongExact` | SpectrumFibrationSequence | ファイバー列の長完全列 |

Sp の presentable 性、懸垂関手、一般の ∞ 余極限：該当する宣言なし（未確認）。

**テンソル積**：KST の Sp・OmegaSpectrum にスマッシュ積・対称モノイダル構造は**ない**。`Spectra/SymmetricSpectrum`（`sphereTensorMonoidalCategory`・`sphereTensorSymmetricCategory`、対称スペクトルのスマッシュ積、レベルモデル構造、`StableModelPresentation`）はあるが、KST の Sp とは**接続されていない**（KST が Spectra/ から import するのは点つき単体集合の部品だけ）。

**群作用**

| 宣言 | 場所 | 中身・注意 |
| --- | --- | --- |
| `GroupAction G := Action OmegaSpectrum G`、`diagramFunctor` | KST/Spectra/GroupAction | **厳密な作用**（Mathlib の `Action`）。∞ 圏的な BG → Sp ではない |
| `homotopyFixedPoints`、`homotopyFixedPointsInfinityCone`・`_isLimit` | FixedPointSpectra・FixedPointInfinityLimits | 厳密な作用の homotopy fixed point が Sp の ∞ 極限錐 |
| `homotopyTotalization`、`homotopyTotalizationInfinityCone` | 同上 | 余単体の Tot |
| `GroupActionCochains`・`FreeActionFamily`・`normalizedCohomologyIso` | GroupFunctionCochains・FreeActionEnd・GroupNerveNormalizedCohomology | 関数複体・自由作用の end・BG の正規化 cochain（標数零で正次数消滅） |

native な homotopy orbit・norm・Tate：**なし**（InfinityCategories/・KST/・EInfinity/ を通じて）。「Tate」は鎖の段階の部品にだけ現れる。

**Eilenberg–MacLane と忘却**：`eilenbergMacLaneDerived A : derivedInfinityCategory A ⟶ Sp`（hammock 比較の同値の逆と EM 関手の合成）、`eilenbergMacLaneDerived_homologyIso i`（π/H の自然同型）、`relativeComplexSpectrum`（相対圏から Sp への一般のスペクトル化）。極限・余極限・exact 性の保存は**なし**。界面の `toSpectra`・`_restrict`・`_homologyIso` は欄としてあるが、Assembly での代入は未確認。

**鎖の段階の巡回・周期の部品（EInfinity/PowerOperation、⑤a 旧経路）**：`powerOperationTensorInput`（p 重テンソルと巡回置換、Rep k C_p 値）、`cyclicTateComplex`（両側周期複体）とその完全性・射影性、`powerOperationCompleteResolution`・`cyclicResolutionHomFunctor`、`cyclicPositiveSpectrum`・`boundedCyclicSpectrum`・`projectivePowerSpectrum`（鎖の模型を `relativeComplexSpectrum`・EM で native Sp に送ったもの。**native な orbit・Tate との同定は未着手**と docstring に）、`powerOperationCoefficientSeed`・`powerOperationTateCoefficientClass`（係数複体の H^{-1} の類 1）、`cyclicOrbitProjectiveResolution`（orbit の鎖の模型）、`CyclicMixedOrbit`（非定数な色付けの安定化群は自明：Prop 2.2.3 の芯の組合せ）、`cyclicTateComplex_regularTensor_acyclic`（誘導作用で消える：Ex 2.1.25 の鎖版）。

**対称冪・拡大冪**：`tensorPowerRepresentationFunctor`（置換群の作用つき p 重テンソル、鎖）、`tensorPowerHomotopyEquiv`、BE の厳密な Σ_n 余不変（`arityDiagramCoinvariants`）。D(A)・Sp 上の導来の拡大冪 (X^{⊗p})_{hΣ_p}：**なし**。

### 3.3 棚卸しから分かる不足（原典の部品 M1〜M10 に対して）

| 部品 | 状態 |
| --- | --- |
| M1 安定 ∞ 圏 C | D(A) は安定・presentable（済）。**Sp は安定性が条件付き、presentable 性・一般の余極限は未確認** |
| M2 norm・Tate | fixed point（極限）のみ。orbit・norm・Tate なし。群作用は厳密なものだけ |
| M3 対称モノイダル・拡大冪 | ∞ 対称モノイダル構造なし。D(A) にも Sp にも導来の拡大冪なし。鎖の段階の p 重テンソルと厳密な Σ_n 余不変はある |
| M4 T̂_p の exact 性 | 芯の組合せ（`CyclicMixedOrbit`）と鎖版の消滅はある。∞ 版なし |
| M5 (A^{⊗p})_G → Sym^p A → A | BE の厳密な作用（SimplexCuts・Operad）から取れる見込み。∞ 版なし |
| M6 T_p の Kan 延長、B = k^{tG} | なし。D(A) の Ind・compact の部品（F1/F1B）は使える |
| M7 k^{tG} の計算、e | 鎖版（周期複体の H^{-1} の類）あり。スペクトル版なし |
| M8 P⁰ の合成と自然性 | なし |
| M9 Rem 2.2.7 | May の計算（規格化 ν、D_0 = p 乗）あり。Lurie の構成の上ではない |
| M10 忘却の極限・余極限の保存 | U の極限保存は済（`cAlgForgetDerived_mapJoinCone_isLimit`）。V の保存なし |


## 4. 設計の選択肢（決めない。考える材料）

### 4.1 標的の圏：Sp か Mod_k か
- 原典：P⁰ はスペクトルの射（Warning 2.2.8）。構成の途中は LMod_k で行う（Ex 2.2.5）。
- 私たちの D79 (i)：忘却 CAlg → D(k) → Sp（V = Eilenberg–MacLane）。構成を D(k) = Mod_k の中で行い、最後に V で Sp へ送る形が原典に近い。V に要るのは、構成の各段の極限・余極限を保つこと（M10）。

### 4.2 ∞ 対称モノイダル構造をどう用意するか
- (α) **正面から**：∞-オペラッド（HA 2.1）と Cat_∞ の可換代数対象、Sym^n(C) → C を作る。D75 で「HA の方向は BS の経路から外す」と決めた大きな基盤。規模は `research/einfinity-route` §6 の見積もり（HA 経路 約 83,000 行〜）の一部。
- (β) **BE の厳密な模型で、必要な等変な対象だけ**：A が厳密な BE 代数なら A^{⊗p} は複体の圏で厳密な Σ_p 作用を持ち、operad の作用から (A^{⊗p}) → A が厳密に等変。homotopy orbit・fixed point・Tate は、鎖の段階の導来関手（W ⊗_{G} −、Hom_G(W, −)、周期解像度）で計算できる。各段が厳密な代数の射について厳密に自然で弱同値を保つなら、局所化の普遍性（Fun(C[W⁻¹], D) → Fun(C, D) の充満忠実性）で ∞ 圏の自然変換（coherent）に降りる。
  - 利点：∞ 対称モノイダル圏を作らずに済む。⑤a の旧経路（周期解像度・巡回作用、10,216 行）がそのまま部品になる。
  - 難点：**Tate 対角（T_p → T̂_p、M6）は点ごとの式では作れない**（x ↦ x^{⊗p} は加法的でない）。原典も exact 性と Kan 延長（Yoneda）で作っている。(β) でも M6 は ∞ 圏の議論（perfect な対象上の exact 関手の自然変換と Ind への延長）が要る。D(k) の presentable・compact・Ind の部品はある（F1/F1B）。
  - 忠実さ：構成の各段は原典の対象（orbit・fixed point・norm・Tate・Sym^p）を模型で計算したもの。「模型が原典の ∞ 構成を計算している」ことは、別の定理として示す（導来関手が BG 上の極限・余極限を計算する）。
- (γ) 中間：M2 だけ native（BG 添字の極限・余極限は Kerodon の範囲）に作り、M3 の等変な積は (β) のように厳密な模型から取る。

### 4.3 May の経路（今の M14、30,586 行）との関係
- May の D_i はホモロジーの上の演算で、構成は Lurie の (A^{⊗p})_{hG} の鎖の模型（W ⊗_G A^{⊗p}）そのもの。P⁰ の値は Lurie の P⁰ と π_* の上で一致する（古典的）が、射としての自然性は持たない。
- Lurie の構成を模型で作ったとき、Rem 2.2.7 の計算には May の計算（規格化 ν、D_0 = p 乗）がそのまま使える見込み。BF の一般次元の切断（L09〜L22、BE の作用の法則）は (β) の M5 で使える。

## 5. 考えるべき問い（ユーザーと調整役）

1. 標的を Mod_{F_p} に置き、最後に Sp へ送る形でよいか（原典の順序どおり）。
2. M3 を (α)(β)(γ) のどれで用意するか。(α) は BS の外の大きな基盤だが、HA の方向の課題（D75 で別建て）と合流する。
3. M6（Tate 対角）の ∞ 圏の議論（exact 関手・Yoneda・Ind への Kan 延長）は、どのレーンの基盤か。
4. 「模型が原典の構成を計算している」をどこまで定理にするか（忠実さの基準）。
5. May の 30,586 行の扱い（補完として残す、Rem 2.2.7 の計算に使う）。
