-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.Hausdorff
import SerrePositivity.InfinityCategories.HA.Section5_5_6.KanIntervalPullbackNative
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberwisePullbackKanWeakEquivalence
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredCosliceCofinality

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 5.5 Topological Chiral Homology" =>
%%%
number := false
tag := "ha-5-5"
%%%

HA 5.5 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "ha_5_5_0_1" (lean := "ChartedSpace, ParacompactSpace, T2Space")
*HA 注意 5.5.0.1*　多様体の規約と factorization homology（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=964)）。対応表の状態：Mathlib にある。

*主張*　位相的キラルホモロジーの節でも、多様体は固定次元のパラコンパクト Hausdorff 位相多様体を指す。

仮定：位相空間 M と固定有限次元 k（HA と一致）。結論：モデル ℝ\^k の ChartedSpace、ParacompactSpace、T2Space の三条件で、5.4.0.1 と同じ多様体の規約を表す（HA と一致）。

Ran 空間や切断の構成に進んでも、5.4.0.1 の多様体の規約を適用する。

:::

# 5.5.1 The Ran Space

%%%
number := false
tag := "ha-5-5-1"
%%%

:::definition "ha_5_5_1_1" (lean := "Finset, Finset.Nonempty")
*HA 定義 5.5.1.1*　非空有限部分集合の Ran 空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=964)）。対応表の状態：Mathlib にある。

*主張*　多様体 $`M` の Ran 空間の点は、$`M` の非空な有限部分集合である。

仮定：多様体 M の基礎集合（HA と一致。Lean は任意の型に定義可能）。結論：\{s : Finset M // s.Nonempty\} は M の非空有限部分集合全体を表す（集合としての Ran(M) の原典の定義と一致。位相は次項で扱う）。

点の列や多重集合ではなく有限集合そのものを使う。位相に使う指定の開集合族は、有限集合がその合併に含まれ、各開集合と交わることによって条件を課す。

:::

# 5.5.3 Properties of Topological Chiral Homology

%%%
number := false
tag := "ha-5-5-3"
%%%

:::lemma_ "ha_5_5_3_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isRightCofinal_sliceUnderProjection_of_filtered")
*HA 補題 5.5.3.12*　sifted 圏の coslice 射影の cofinal 判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=982)）。対応表の状態：一部（stronger-hyp）。

*主張*　非空な ∞ 圏が篩状であることは、各対象 $`c` の下の圏から元の圏への終域射影 $`C_{c/}\to C` が左共終であることで判定できる。

KB-W2型再照合：仮定：C は filtered な準圏（Lean が強い：sifted より強い filtered 性）。結論：有限図式 p の coslice の射影が余極限を計算する向きに cofinal となる。特に p を一点 C に取ると CC/→C の cofinal 性を与える（この仮定で原典の sifted なら全 coslice 射影が left cofinal という方向に一致）。一般 sifted C と逆方向の判定は含まれない。

篩状性の対角を使う条件を、一方の対象を固定して比較する。空でないことは別途仮定する。

:::

# 5.5.6 Nonabelian Poincare Duality

%%%
number := false
tag := "ha-5-5-6"
%%%

:::definition "ha_5_5_6_2" (lean := "CompactlySupportedContinuousMap")
*HA 定義 5.5.6.2*　compact support を持つ section の単体集合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=999)）。対応表の状態：一部（component）。

*主張*　基準切断付き Serre ファイブレーションのコンパクト台付き切断の単体集合は、台が指定開集合のコンパクト部分集合に入るパラメータ付き切断からなる。

KB-W2型再照合：仮定：U=M、E=M×K は自明な fibration、基準 section は K の指定零点とし、零単体だけを扱う（Lean が強い：自明束の零次の部分）。結論：C\_c(M,K) は基準点から外れる support の閉包が compact な連続写像の型となる（Γc(M;E) の零単体の部分に一致）。Δn の幾何的実現の全パラメータ、非自明 Serre fibration、Kan 性と N(U(M))⊗ の作用は含まれない。

台は、その外で切断が基準切断と一致する最小の閉集合である。互いに素な開集合のコンパクト台を合わせる操作により、空間のデカルト構造に値を取る開集合オペラッドの代数 $`E_!` が得られる。

:::

:::proposition "ha_5_5_6_10" (lean := "CompactlySupportedContinuousMap.continuousMapEquiv")
*HA 例 5.5.6.10*　Hochschild homology と自由ループ空間（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1001)）。対応表の状態：一部（component）。

*主張*　点付き連結空間の自由ループ空間は、基点付きループ空間を結合代数と見たときの空間値 Hochschild ホモロジーと同値である。

KB-W2型再照合：仮定：M=S¹ は compact、E=X×S¹ は自明束、X の基準点を零とし零単体を扱う（Lean が強い：零次の通常写像の場合）。結論：全連続写像 S¹→X と compact support を持つ写像 S¹→X は同じ台の全単射で対応する（compact な M の Γc の零単体が通常の free loop の点となる部分に一致）。Sing の全単体と Hochschild homology・E₁ loop algebra の同定は含まれない。

円周上の自明束で切断は自由ループになる。円周がコンパクトなので台の制約がなく、局所の代数はループの連結による $`\Omega X` で記述できる。

:::

:::lemma_ "ha_5_5_6_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberwisePullbackKanComparison_isSimplicialHomotopyEquivalence, SerrePositivity.InfinityCategories.HA.Section5_5_6.intervalPullbackCone_isLimit")
*HA 補題 5.5.6.17*　∞ トポスの sifted 余極限と pullback（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=1006)）。対応表の状態：一部（stronger-hyp）。

*主張*　∞ トポスで中央が点付き連結対象である図式 $`X\to Z\leftarrow Y` を引き戻しに送る関手は、篩状余極限を保つ。

KB-W2型再照合：仮定：X=S の場合で添字 B は filtered、coherent な cospan の三つの族を B 上の left fibration で指定（Lean が強い：sifted より強い filtered 性とこの unstraightening 模型）。結論：fiberwise な path pullback の全空間の Kan 模型から、三全空間の Kan 模型の path pullback への標準比較が単体的ホモトピー同値となり、path pullback の錐は元の空間の ∞ 極限となる（filtered な空間値の場合の pullback と余極限の交換に一致する部分）。一般 sifted 添字と任意 ∞ トポスは含まれない。

図式圏では中央の対象に点付き連結性を課すが、左右の対象にはこの条件を課さない。比較はこの図式圏での篩状余極限と、トポスでの引き戻しの間に成り立つ。

:::

