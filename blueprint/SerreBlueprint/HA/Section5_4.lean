import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 5.4 Little Cubes and Manifold Topology" =>
%%%
number := false
tag := "ha-5-4"
%%%

HA 5.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::definition "ha_5_4_0_1" (lean := "ChartedSpace, ParacompactSpace, T2Space")
*HA 規約 5.4.0.1*　topological manifold の規約（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=922)）。対応表の状態：Mathlib にある。

*主張*　指定がなければ、多様体は固定次元のパラコンパクトな Hausdorff 位相多様体を指す。

仮定：位相空間 M と固定した有限次元 k（HA と一致）。結論：モデル H=ℝ\^k の ChartedSpace に ParacompactSpace と T2Space を併記すると、本書の paracompact Hausdorff topological k-manifold の条件となる（HA と一致）。滑らかな atlas の互換性や境界は要求しない。

局所的には同じ次元の Euclid 空間による座標を取る。後続の埋め込みの主張ではこの次元をそろえる。

:::

# 5.4.1 Embeddings of Topological Manifolds

%%%
number := false
tag := "ha-5-4-1"
%%%

:::theorem "ha_5_4_1_1" (lean := "isOpenMap_of_hasStrictFDerivAt_equiv")
*HA 定理 5.4.1.1*　局所同相の fiber ごとの判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=923)）。対応表の状態：一部（stronger-hyp）。

*主張*　同じ次元の多様体 $`M,N` に対し、任意の位相空間 $`X` 上の連続単射 $`M\times X\to N\times X` は開写像である。

KB-W2型再照合：仮定：X が一点、M=N=ℝ\^k とし、連続単射 f が各点で可逆な strict Fréchet 微分を持つ（Lean が強い：全点で可逆微分を仮定）。結論：f は開写像（この仮定の下で HA の結論と一致）。任意のパラメータ X、任意の多様体と単なる連続単射の領域不変性は含まれない。

写像が $`X` への射影と可換であることを要求する。パラメータ $`X` は多様体である必要がなく、各切片での定義域不変性を族の開性へ強めている。

:::

:::corollary "ha_5_4_1_3" (lean := "Continuous.homeoOfEquivCompactToT2")
*HA 系 5.4.1.3*　Embeddings of Topological Manifolds (p. 923)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=923)）。対応表の状態：一部（stronger-hyp）。

*主張*　同じ次元の多様体の積 $`M\times X\to N\times X` の間の、$`X` 上の連続全単射は同相写像になる。

KB-W2型再照合：仮定：X が一点で M は compact、N は Hausdorff、f は連続全単射（Lean が強い：M の compact 性）。結論：f とその逆が連続な同相を与える（この仮定で HA の結論と一致）。非 compact な多様体や任意パラメータ X での逆の同時連続性は含まれない。

連続全単射に定義域不変性のパラメータ付き版を適用すると、開写像であることが分かり、逆写像も連続となる。

:::

:::proposition "ha_5_4_1_4" (lean := "ContinuousMap.curry, ContinuousMap.uncurry")
*HA 注意 5.4.1.4*　Embeddings of Topological Manifolds (p. 923)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=923)）。対応表の状態：一部（component）。

*主張*　コンパクト開位相を入れた同次元多様体間の写像空間への連続な族は、積の間のパラメータを保つ連続写像に対応し、埋め込みと同相の族はそれぞれ全体が単射、全単射の場合に対応する。

KB-W2型再照合：仮定：M は局所 compact、X,N は任意の位相空間（HA の多様体の局所 compact 性と一致）。結論：compact-open な C(M,N) への連続写像 X→C(M,N) と X×M→N を curry・uncurry で相互に移す（原典冒頭の分類に積の交換を除き一致する部分）。Emb・Homeo 部分への制限と位相的 monoid・group 構造の比較は含まれない。

コンパクト開位相の随伴には始域の局所コンパクト性を使う。単射の族の像は開き、全単射の族の逆も連続となる。とくに自己埋め込みと自己同相は合成により位相モノイドと位相群をなす。

:::

# 5.4.3 Digression: Nonunital Associative Algebras and their Modules

%%%
number := false
tag := "ha-5-4-3"
%%%

:::proposition "ha_5_4_3_13" (lean := "IsIdempotentElem.iff_eq_one_of_isUnit")
*HA 注意 5.4.3.13*　Digression: Nonunital Associative Algebras and their Modules (p. 936)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=936)）。対応表の状態：一部（component）。

*主張*　準単位 $`u:1\to A` の非単位的加群 $`M` への作用が恒等射にホモトピックであることは、その作用が同値であることで判定できる。

原文末尾が明示するhMでの「可逆な冪等自己射は恒等」という成分に、End(hM)のモノイドと同じ\[ψ\]を入れたIsIdempotentElem.iff\_eq\_one\_of\_isUnitが直接一致する。quasi-unitからψ²=ψを導く前半の議論と∞-moduleの構成は含まない。

準単位の積が準単位にホモトピックなので、誘導する自己射 $`\psi:M\to M` はホモトピー圏で冪等である。冪等かつ可逆なら恒等射になる。

:::

# 5.4.4 Nonunital E\_k-Algebras

%%%
number := false
tag := "ha-5-4-4"
%%%

:::proposition "ha_5_4_4_12" (lean := "Commute.isUnit_mul_iff")
*HA 注意 5.4.4.12*　Nonunital \$E\_\{k\}\$-Algebras (p. 952)（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=952)）。対応表の状態：一部（component）。

*主張*　結合モノイドの可換な二元は、積が可逆であるとき、かつそのときに限り、両方とも可逆である。

KB-W2型再照合：仮定：通常の結合的 monoid M で可換な二元 x,y（HA 冒頭の仮定と一致）。結論：xy が単元であることと x,y が共に単元であることが同値（原典冒頭の結論と一致）。Eₖ 代数の Map の和成分の交わりと u-equivalence の結論は含まれない。

代数の指定の可換な元 $`u,v` の積を $`w` とすると、$`w` を可逆にする写像空間は $`u` と $`v` を各々可逆にする空間の交わりである。このため $`u`-同値または $`v`-同値なら $`w`-同値になる。

:::

