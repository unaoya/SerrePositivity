import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.CategoryTheory.Monoidal.Center
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndCardinalChange
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 5.3 Centers and Centralizers" =>
%%%
number := false
tag := "ha-5-3"
%%%

HA 5.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 5.3.1 Centers and Centralizers

%%%
number := false
tag := "ha-5-3-1"
%%%

:::proposition "ha_5_3_1_1" (lean := "Subalgebra.center, Subalgebra.mem_center_iff")
*HA 例 5.3.1.1*　中心と自己作用の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=882)）。対応表の状態：一部（component）。

*主張*　体 $`k` 上の結合代数 $`A` の中心は、$`A` にテンソル積を通じて作用する結合代数の中で普遍的である。

KB-W2型再照合：仮定：体 k 上の通常の結合代数 A（HA と一致。Lean は可換係数半環にまで一般化）。結論：全元と可換な元からなる中心を部分代数として構成する（冒頭の通常の中心の構成に一致する部分）。全代数の A への作用の普遍性と、一般には endomorphism object でないという写像集合の主張は含まれない。

$`B\otimes_k A\to A` が $`A` 上の恒等であれば、$`B` の像は $`A` の各元と可換なので中心へ入る。代数構造を持たない作用のパラメータまで含む自己準同型対象の普遍性は一般には成立しない。例えば、単位 $`k` から中心への代数の射が一意でも、$`A` は複数の代数自己準同型を持ち得る。

:::

:::proposition "ha_5_3_1_18" (lean := "CategoryTheory.Center, CategoryTheory.Center.braidedCategoryCenter")
*HA 例 5.3.1.18*　中心の Eₖ₊₁ 代数構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=888)）。対応表の状態：一部（component）。

*主張*　$`E_k` モノイダル ∞ 圏の中心は $`E_{k+1}` モノイダル ∞ 圏になり、通常のモノイダル圏の $`E_1` の場合には組み紐モノイダルな Drinfeld 中心を回収する。

KB-W2型再照合：仮定：通常のモノイダル圏 C（Lean が強い：k=1 の通常圏の場合）。結論：half-braiding を持つ対象の Drinfeld center とその braided monoidal 構造を構成する（原典の通常圏の場合の中心の構成と braiding に一致する部分）。Cat∞ 内の普遍的 Z\_E₁(C) の nerve との同値と一般の k の Eₖ₊₁ 構造は含まれない。

$`C` をデカルト対称モノイダルな $`\mathrm{Cat}_\infty` 内の $`E_k` 代数として中心を取る。通常圏の場合、その中心も通常圏の nerve であり、$`E_2` 構造を組み紐として読める。

:::

:::definition "ha_5_3_1_19" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting") (uses := "htt_1_1_2_4, htt_2_4_1_1")
*HA 定義 5.3.1.19*　Centers and Centralizers (p. 888)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=888)）。対応表の状態：一部（component）。

*主張*　$`O^\otimes` 上のオペラッドの余デカルト $`S` 族は圏論的ファイブレーションで、$`S` 上で ∞ オペラッドの族をなし、$`S` 方向に余デカルト移送を持つ。

同じq:C⊗→O⊗×SにEquivalenceLifting qを課すことは原文の条件(i)categorical fibrationそのもの。∞-operad familyの条件(ii)と指定方向の持ち上げ(iii)は含まない。

$`C` の像が $`(X,s)` であるとき、$`S` の辺 $`s\to s'` と $`O^\otimes` の恒等射を組み合わせた辺に沿う持ち上げを要求する。

:::

# 5.3.2 The Adjoint Representation

%%%
number := false
tag := "ha-5-3-2"
%%%

:::lemma_ "ha_5_3_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessible.exists_larger")
*HA 補題 5.3.2.12*　単位・テンソルと両立する compact 生成基数（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=902)）。対応表の状態：一部（component）。

*主張*　小余極限を各変数で保つテンソルを持つ可提示対称モノイダル ∞ 圏には、圏と全ての右加群圏がコンパクト生成になり、テンソルと加群作用がコンパクト性を保つ共通の非可算正則基数がある。

KB-W2型再照合：仮定：presentable な準圏 C の accessibility（HA の仮定から従う）。結論：σ=ℵ₀ を指定すると、ある非可算正則 μ に関して C は μ-compact 生成となる（(1) の存在部分に一致）。同じ μ における tensor・単位と全代数の加群の compact 条件 (2)〜(4) は含まれない。

その基数で単位もコンパクトである。基礎の小さい生成圏から始め、単位と生成対象のテンソルの大きさを一斉に抑えられるよう基数を大きく取る。

:::

