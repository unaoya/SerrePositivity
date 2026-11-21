-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Separation.PerfectlyNormal

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 7.1 Paracompact Spaces" =>
%%%
number := false
tag := "htt-7-1"
%%%

HTT 7.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 7.1.1 Some Point-Set Topology

%%%
number := false
tag := "htt-7-1-1"
%%%

:::proposition "htt_7_1_1_3" (lean := "perfectlyNormalSpace_iff_forall_isClosed_preimage_zero")
*HTT 注意 7.1.1.3*　距離化可能な空間の開集合の表示（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=709)）。対応表の状態：Mathlib にある。

*主張*　距離化可能な空間では任意の開集合が第7.1.1.1項の基底に属し、補集合までの距離を使って開集合を連続関数で表せる。

仮定：距離化可能な X の開集合 U（HTT と一致、Mathlib は既存の PerfectlyNormalSpace instance により適用）。結論：Uᶜ を零点集合とする \[0,1\] 値連続実関数があり、非負性から U=\{f\>0\}（一致）。空の補集合でも同じ存在定理が適用でき、距離の infimum そのものに固定する必要はない。

距離を有界に取り替えると、補集合への距離を区間 $`[0,1]` に値を持つ関数として使える。開集合内の点は補集合から正の距離にあるので、関数の正の値が開集合を復元する。

:::

# 7.1.5 Base Change

%%%
number := false
tag := "htt-7-1-5"
%%%

:::proposition "htt_7_1_5_9" (lean := "ContinuousMap.curry, ContinuousMap.uncurry")
*HTT 注意 7.1.5.9*　局所コンパクト空間と指数法則（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=728)）。対応表の状態：一部（component）。

*主張*　位相空間の列の直極限 $`X=\varinjlim X_i` と局所コンパクトな空間 $`Y` について、$`X\times Y\cong\varinjlim(X_i\times Y)` であり、特に位相的単体との積でも成り立つ。

KB-W2原文・型再照合：仮定：任意の位相空間 A,Z と局所コンパクト Y（HTT の指数法則部分と一致）。結論：連続写像 A×Y→Z と A→C(Y,Z) の currying/uncurrying が互いに逆で、本文の Hom の最初の全単射を与える（結論の一部）。列の direct-limit topology と積の colimit の同じ比較はこれらの型には含まない。

$`Y` との積に対する右随伴は、コンパクト開位相を入れた写像空間である。積を写像空間の変数に移すと、元の直極限の普遍性を適用できる。

:::

# 7.1.6 Higher Topoi and Shape Theory

%%%
number := false
tag := "htt-7-1-6"
%%%

*classifying-shape.html — 4. 一般のエタール ∞ トポス：シェイプ*

どんな ∞ トポスでも $`\Gamma\pi^*` は pro 空間 $`\mathrm{Shape}(\mathcal X)` で表現される（HTT §7.1.6、シェイプの定義）：
$$`\Gamma(\pi^*K)\ \simeq\ \mathrm{Map}\bigl(\mathrm{Shape}(\mathcal X),K\bigr),\qquad\Gamma(B\underline G)\ \simeq\ \coprod_{[\rho]}B\,C_G(\rho)\quad(\rho\colon\pi_1\mathrm{Shape}(X_{\mathrm{et}})\to G,\ X\text{ 連結}).`
§3 の公式は $`\pi_1=\hat{\mathbb Z}` の場合。

- 底 $`X`　／　シェイプ（の $`\pi_1`）　／　$`G` torsor（$`G` 有限群）
- $`\mathrm{Spec}\,\mathbb F_q`　／　$`B\hat{\mathbb Z}`　／　$`G` の共役類（Frobenius の像）
- $`\mathrm{Spec}\,k`　／　$`BG_k`　／　連続準同型 $`G_k\to G` の共役類
- $`\mathrm{Spec}\,\mathbb Z`　／　$`\pi_1=1`（Minkowski）　／　自明なもののみ、$`\Gamma(BG)\simeq BG`
- 種数 $`g` の曲線（$`\mathbb C` 上）　／　曲面群の副有限完備化　／　$`G` 被覆（Riemann の存在定理）
- 局所体 $`K`　／　$`BG_K`　／　連続準同型 $`G_K\to G` の共役類

- $`G` の種類　／　$`\Gamma(B\mathcal G)` の計算
- 有限群（定数）　／　π-有限なのでシェイプの副有限完備化（Artin–Mazur）だけを見る。$`\pi_1^{\mathrm{et}}(X)\to G` の共役類と中心化群（SGA1 の Galois 圏）
- 無限な離散群（定数）　／　シェイプそのものが要る。正規な $`X` では $`\mathbb Z` torsor は自明（局所既約性、$`\mathrm{Spec}\,\mathbb F_q` の「連続性」の一般化）。結節点を持つ 3 次曲線では $`H^1(X,\mathbb Z)=\mathbb Z`（Bhatt–Scholze の pro-étale 基本群が捉える）
- 局所定数な群　／　シェイプ上の局所系（関手 $`\mathrm{Shape}(X)\to\mathcal S`）の切断、ねじれた共役
- 局所定数でない群（$`\mathbb G_m`、代数群）　／　シェイプでは足りず、トポス全体が要る。曲線上の $`\pi_0\Gamma(B\mathbb G_m)=\mathrm{Pic}(X)` は連続的なパラメータを持つ

*体の場合が特別な理由*：$`\mathrm{Spec}\,k` のエタール層は全て Galois 加群、すなわち $`BG_k` 上の局所系なので、$`\mathbb G_m` も含めて全てがシェイプ上の計算に帰着する。有限体の Brauer 群が円周の計算で済んだのはこのため。

*classifying-shape.html — 6. 「空間」と「大域切断が連結」の意味 — 6.2 大域切断はなぜ空間か*

- 層の種類　／　大域切断 $`\Gamma(F)`
- 集合の層　／　集合
- 亜群の層（スタック）　／　亜群
- 空間の層（∞ トポスの対象）　／　空間

∞ トポスの対象は空間の層なので、$`\Gamma(F)=\mathrm{Map}(\ast,F)` は写像空間で空間になる。$`\Gamma(BG)` は「$`G` torsor と同型」の亜群（1-切り詰め）、$`\Gamma(B\mathbf{Pic})` は「$`\mathrm{Mod}` の捻れた形、同値、自然同型、…」の空間（体の場合は 2-切り詰め）。

