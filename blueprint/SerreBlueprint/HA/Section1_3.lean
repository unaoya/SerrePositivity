-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import SerrePositivity.DifferentialGraded.Category.Basic
import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.ChainMapHomotopyReflection
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.CofiberPushout
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.ComplexEdgeCalculus
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.StandardCofiberSquare
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.ScalarRestrictionNerve
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.ModelCofibrantRelative
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockInvertsEdges
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantLocalization
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GroupoidCompletion
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SmallMarkedFactorization
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPreservation
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComparison
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComparisonEquivalence
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeFlags
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGNerveBasic
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory
import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoproductRealizationColimits
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredClosure
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoproductRealizationPreservation
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
import SerrePositivity.KST.DerivedGeometry.KInjectiveLiftingCriterion

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 1.3 Homological Algebra and Derived Categories" =>
%%%
number := false
tag := "ha-1-3"
%%%

HA 1.3 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 1.3.1 Nerves of Differential Graded Categories

%%%
number := false
tag := "ha-1-3-1"
%%%

*05-gamma-bridges.html — 2. γ1.5：Dold–Kan 豊穣化と dg nerve*

dg 圏 $`D` から ∞ 圏を作る方法は二つある（HA §1.3.1）。

- *dg nerve* $`N_{dg}(D)`：dg 圏から直接作る（第 8 章、DGNerve/）。

- *Dold–Kan 豊穣化の coherent nerve*：Hom 複体を $`\tau_{\ge0}`（コードの規約では $`\tau^{\le0}`）で切断し、Dold–Kan 対応 $`\Gamma` で単体的加群、したがって Kan 複体にする。合成は Alexander–Whitney 写像で与える。こうして得た単体的圏の coherent nerve を取る。

\`\`\`text
def doldKanHomModule (x y : D) : SimplicialObject (ModuleCat.\{u\} R) :=
  (CategoryTheory.Abelian.DoldKan.Γ : ChainComplex (ModuleCat.\{u\} R) ℕ ⥤ \_).obj
    (connectiveHomComplex (R := R) x y)
def doldKanCoherentNerve : SSet.\{max u v\} := SimplicialNerve (ClosedCategory R D)
def coherentComparison : doldKanCoherentNerve (R := R) (D := D) ⟶ dgNerve R D
lemma coherentComparison\_isQCatEquivalence :
    IsQCatEquivalence (coherentComparison (R := R) (D := D))
\`\`\`

場所：DoldKanComparison/ConnectiveHom、CoherentComparison、ComparisonEquivalence。*任意の可換環上の任意の dg 圏*について、比較写像が同値であることが示されている（HA Prop. 1.3.1.17）。Dold–Kan 対応は Mathlib の \`Abelian.DoldKan.Γ\` をそのまま使う。

*証明の方針*：比較写像は頂点の上で全単射なので、本質的全射性は自明である。充満忠実性は、写像空間の比較（coherent nerve 側の pinched Hom → dg nerve 側の pinched Hom）がホモトピー同値であることに帰着する。これを標準的な分解（Resolution\*）を通して示し、第 2 章の判定（充満忠実かつ本質的全射）で結論する。比較写像の各単体は、降順の立方体の評価（Cube\*、AW\*）で具体的に作られている。

二つの模型を持つ理由

dg nerve は D(S) などの dg の対象を扱うのに直接的で、第 8 章ではこちらを主に使う。一方、coherent nerve の側は $`\mathcal S`、Cat\<sub\>∞\</sub\> と同じ枠組みにあり、単体的豊穣の議論（γ4 など）が使える。両者の同値によって、どちらの模型で示した性質も他方に移せる。

*08-dgnerve-derived.html — 1. dg nerve — 主な性質*

- 内容　／　Lean　／　場所
- quasicategory である（HA Prop. 1.3.1.10）　／　\`instQuasicategory\`　／　DGNerve/Quasicategory
- $`h\,N_{dg}(D)\simeq H^0(D)`（ホモトピー圏 = 0 次コホモロジー圏）　／　\`DGNerve.HomotopyComparison.equivalence\`　／　DGNerve/HomotopyCategory
- 右 pinched 写像空間は単体的 $`A` 加群で、$`\pi_0` が $`H^0\mathrm{Hom}`　／　\`piZeroToH0\` など　／　DGNerve/PinchedPiZero ほか
- dg 関手・厳密な自然変換の dg nerve への作用　／　（N6）　／　DGNerve
- 前三角 dg 圏の dg nerve は安定　／　\`dgNerve\_isStable\_of\_pretriangulated\`　／　Derived/DGPretriangulatedStability

*quasicategory 性の方針*：写像空間が単体的 $`A` 加群であることを使い、内ホーンを「線形に」充填する。第 5 章の γ1.5 は、この dg nerve が Dold–Kan 豊穣化の coherent nerve と同値であることを示しており、二つの模型の行き来ができる。

*spectra-k-theory.html — 8. DG 圏の K 理論との比較 — dg nerve（HA §1.3.1）*

ホモロジー的次数。$`n` 単体は対象 $`X_0,\dots,X_n` と、$`I=\{i_-\lt i_m\lt\cdots\lt i_1\lt i_+\}\subseteq[n]`（$`|I|\ge2`）ごとの $`f_I\in\mathrm{Map}_{\mathcal C}(X_{i_-},X_{i_+})_m`（$`m=|I|-2`）で、

$$`df_I=\sum_{j=1}^m(-1)^j\Bigl(f_{I\setminus\{i_j\}}-f_{\{i_j\lt\cdots\lt i_1\lt i_+\}}\circ f_{\{i_-\lt i_m\lt\cdots\lt i_j\}}\Bigr).`

- $`n=2`：$`df_{012}=f_{12}f_{01}-f_{02}`（合成と $`f_{02}` のホモトピー）。$`n=3`：$`f_{0123}` は結合法則の境界を埋める。

- 端点固定の $`f_I` は $`\mathfrak C[\Delta^n]` の立方体 $`(\Delta^1)^{j-i-1}` の胞体と一対一で、$`N_{\mathrm{dg}}(\mathcal C)_n=\mathrm{Fun}_{\mathrm{dg}}(C_*(\mathfrak C[\Delta^n]),\mathcal C)` と見なせる（ホモトピー整合的ナーブの dg 版）。

- 写像空間 $`\simeq\mathrm{DK}(\tau_{\ge0}\mathrm{Map}_{\mathcal C})`、ホモトピー圏 $`H_0(\mathcal C)`、pretriangulated なら安定。

:::definition "ha_1_3_1_1" (lean := "SerrePositivity.DifferentialGraded.DGCategory")
*HA 定義 1.3.1.1*　可換環上の dg 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=80)）。対応表の状態：本体にある。

*主張*　可換環 $`k` 上の dg 圏は、写像対象が $`k` 加群の鎖複体で、合成が複体のテンソル積からの鎖写像となる豊穣圏である。

仮定：可換環 k と対象の型（HA と一致）。結論：DGCategory は Complex k による豊穣圏で、写像複体・鎖写像としての合成・結合則・単位を保持する（鎖次数を −n として一致）。

合成は結合的で、次数零の恒等射を備える。次数 $`p` の $`g` と任意の斉次射 $`f` には $`d(gf)=(dg)f+(-1)^pg(df)` が成り立つ。

:::

:::proposition "ha_1_3_1_2" (lean := "SerrePositivity.DifferentialGraded.differential_unit")
*HA 注意 1.3.1.2*　dg 圏の恒等射の閉性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=80)）。対応表の状態：本体にある。

*主張*　dg 圏の恒等射は次数零のサイクルである。

仮定：dg 圏 C と対象 x（HA と一致。Lean は任意の可換環を許す）。結論：differential A (unitElement A x).val = 0 なので恒等射は閉じている（一致）。

恒等射を自身との合成として Leibniz 則を使うと、その微分が自身の二倍になる。両辺の差を取ると微分が零になる。

:::

:::proposition "ha_1_3_1_3" (lean := "SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerveRestrictScalarsIso")
*HA 注意 1.3.1.3*　dg 圏の係数の制限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=81)）。対応表の状態：本体にある。

*主張*　可換環の準同型 $`k\to k'` に沿ってスカラーを制限すれば、$`k'` 上の dg 圏は $`k` 上の dg 圏になる。

仮定：可換環の準同型 f : S →+\* T と T 上の dg 圏 D（HA と一致）。結論：DGRestrictScalars f D は対象と複体の元を保って S の dg 圏を得る。dgNerveRestrictScalarsIso がこの制限で nerve も保つことを確認する（一致）。

各写像複体の加群構造を制限する。微分と合成はそのまま使え、$`\mathbb Z\to k` を選べば基礎の整数上の dg 圏が得られる。

:::

:::proposition "ha_1_3_1_4" (lean := "SerrePositivity.DifferentialGraded.DGCategory, SerrePositivity.DifferentialGraded.ClosedCategory")
*HA 注意 1.3.1.4*　鎖複体豊穣圏と dg 圏の基礎圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=81)）。対応表の状態：本体にある。

*主張*　可換環 $`k` 上の dg 圏は $`\operatorname{Ch}(k)` 上の豊穣圏で、基礎の通常圏の射は写像複体の次数零のサイクルである。

仮定：可換環 k 上の dg 圏（HA と一致）。結論：dg 圏は鎖複体豊穣圏で、ClosedCategory はモノイド単位から Hom 複体への鎖写像を通常の射とする。これは閉じた次数 0 の元の指定に一致する。

豊穣単位 $`k[0]` から写像複体への鎖写像は次数零のサイクルの選択に等しい。Leibniz 則でそれらは合成に閉じている。

:::

:::proposition "ha_1_3_1_5" (lean := "SerrePositivity.DifferentialGraded.HomotopyCategory, SerrePositivity.DifferentialGraded.homotopyHomologyEquiv")
*HA 注意 1.3.1.5*　dg 圏のホモトピー圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=81)）。対応表の状態：本体にある。

*主張*　dg 圏のホモトピー圏は同じ対象を持ち、Hom は写像複体の零次ホモロジーで、合成は代表の合成から誘導される。

仮定：dg 圏と対象 x, y（HA と一致。Lean は任意の可換環を許す）。結論：HomotopyCategory は境界差で商を取り、その Hom は写像複体の H⁰ と同値（一致）。

次数零のサイクルの差が次数一の境界なら二つを同一視する。Leibniz 則により、この同一視をしても合成が定まる。

:::

:::definition "ha_1_3_1_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback")
*HA 構成 1.3.1.6*　dg nerve の構成（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=81)）。対応表の状態：本体にある。

*主張*　dg nerve の $`n` 単体は、各頂点の対象と、両端を含む各部分列に割り当てた斉次射で、面の項と合成の項を結ぶ微分の式を満たすデータである。

仮定：dg 圏と単体次数 n（HA と一致。Lean は任意の可換環を許す）。結論：頂点列と端点間の全有限部分集合に対する次数 2−card の成分を保持し、HA の削除項と分割合成項の微分方程式を課す。単調写像に沿う引き戻しで退化した辺は単位、高次は零（次数の反転を除き一致）。

部分列に中間頂点が $`m` 個あれば、その成分は次数 $`m` に置く。微分は、中間頂点を消す項と、その頂点で切った二射を合成する項の符号付き差である。単調写像は単射な部分列の成分を制限し、潰れた辺には恒等射、それ以外の潰れた高次成分には零を入れる。

*08-dgnerve-derived.html — 1. dg nerve — 定義（HA Construction 1.3.1.6）*

dg 圏 $`D` の dg nerve $`N_{dg}(D)` の $`n` 単体は、対象 $`x_0,\dots,x_n` と、各部分集合 $`I=\{i_0<\dots<i_r\}\subset[n]`（$`r\ge1`）に対する次数 $`1-r` の射 $`f_I\colon x_{i_0}\to x_{i_r}` の族で、次を満たすものである。

$$`\delta f_I=\sum_{j\in I,\ i_0<j<i_r}\varepsilon(I,j)\,\bigl(f_{I\setminus\{j\}}-f_{I_{\ge j}}\circ f_{I_{\le j}}\bigr),\qquad \varepsilon(I,j)=(-1)^{\#\{k\in I\,:\,j<k\}}.`

たとえば 2 単体では $`\delta f_{012}=f_{12}\circ f_{01}-f_{02}`、つまり $`f_{012}` は合成 $`f_{12}\circ f_{01}` と $`f_{02}` の間のホモトピーである。

\`\`\`text
def dgNerve : SSet.\{max u v\} where
  obj Δ := DGNerve.Simplex A D Δ.unop.len
  map f := ↾fun s =\> s.pullback f.unop.toOrderHom
instance instQuasicategory : SSet.Quasicategory (dgNerve A D)
\`\`\`

場所：DGNerve/Basic、DGNerve/Quasicategory。係数環 $`A` は任意の可換環で、有界性・平坦性・標数の仮定はない。

符号の規約（重要）

コードの微分は次数 +1（cochain）で、合成は通常順 \`compose A g f h\` $`=g\circ f`、Leibniz 則は $`\delta(g\circ f)=\delta g\circ f+(-1)^{|g|}g\circ\delta f`。HA の chain 次数を負に読み替え、HA の $`f_I` は符号を変えずに使う。*Kerodon Construction 2.5.3.1 とは括弧の順序が逆*で、同じ Hom 複体の微分で比べると $`f_I^{\mathrm{Kerodon}}=(-1)^{|I|-2}f_I^{\mathrm{HA}}` となる。原典の式をそのまま混在させないこと。詳細は InfinityCategories/README.md（実質的に dg nerve の規約文書）。

:::

:::proposition "ha_1_3_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangleEquiv")
*HA 例 1.3.1.8*　dg nerve の低次単体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=82)）。対応表の状態：本体にある。

*主張*　dg nerve の頂点は対象、辺は次数零のサイクルであり、二単体は三辺 $`f,g,h` と $`dz=gf-h` を満たす次数一の射 $`z` である。

仮定：dg 圏 C（HA と一致。Lean は任意の可換環を許す）。結論：次数 0 は対象、1 は閉じた次数 0 の射、2 は三つの辺と d(z) = g ∘ f − h を満たす高次成分のデータに同値（一致）。

二単体は二辺の合成と第三辺の差を境界として表す。したがって合成と第三辺がホモトピー圏で等しくなる。

:::

:::proposition "ha_1_3_1_9" (lean := "SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_higher, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_edge")
*HA 注意 1.3.1.9*　基礎圏の nerve の dg nerve への埋め込み（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=82)）。対応表の状態：一部（component）。

*主張*　dg 圏の基礎通常圏の nerve は、二頂点より多い部分列の成分が全て零となる dg nerve の部分単体集合に一致する。

KB-W2型再照合：仮定：dg 圏とその閉次数 0 の基礎圏（HA と一致）。結論：基礎圏の nerve から dg nerve に入り、高次の成分は零で、辺は元の閉零射に対応する。高次の成分が零である全単体を一意に復元する像の逆向きは型にない（Lean が弱い）。

零を入れると二単体の条件は通常圏での合成そのものになる。この包含は頂点と辺の集合において全単射である。

:::

:::proposition "ha_1_3_1_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.instQuasicategory, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hornFilling")
*HA 命題 1.3.1.10*　dg nerve の準圏性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=82)）。対応表の状態：本体にある。

*主張*　任意の dg 圏の dg nerve は準圏である。

仮定：dg 圏（HA と一致。Lean は任意の可換環を許す）。結論：dgNerve が準圏であり、任意の内角に対し単体の充填を与える（一致）。

内角の欠けた合成と高次の成分を dg nerve の微分関係に沿って補うことで、内角充填条件が成り立つ。

:::

:::proposition "ha_1_3_1_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence")
*HA 注意 1.3.1.11*　dg 圏と dg nerve のホモトピー圏の比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=83)）。対応表の状態：一部（component）。

*主張*　dg 圏の写像複体から作ったホモトピー圏は、その dg nerve のホモトピー圏と標準同型である。

同じdg圏のH⁰圏とhNdgの比較equivalenceは、原文の構成する比較関手およびそのHom全単射と本質的全射性の成分を直接与える。対象を厳密に同一にした通常圏の同型という全体の型は含まない。

対象と辺は同じである。二単体の記述により、辺のホモトピーは次数零サイクルの差が次数一からの境界になることと同値で、合成も一致する。

:::

:::proposition "ha_1_3_1_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso")
*HA 注意 1.3.1.12*　dg nerve の右写像空間の Dold–Kan 模型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=83)）。対応表の状態：本体にある。

*主張*　dg nerve の右写像空間は、写像複体の非負切断に Dold–Kan を適用して得る単体的アーベル群の基礎単体集合と同型である。

仮定：dg 圏と対象 x, y（HA と一致。Lean は任意の可換環を許す）。結論：右写像空間の pinched 模型は、Hom 複体の連結切断に Dold–Kan を適用した単体集合を同じ宇宙に持ち上げたものと同型（一致）。

右写像空間では最初の $`n` 単体を $`X`、最後の頂点を $`Y` に固定する。成分の符号を調整すると、その $`n` 単体は $`\Delta^n` の正規化鎖複体から $`\operatorname{Map}_C(X,Y)_*` への鎖写像に対応する。

:::

:::definition "ha_1_3_1_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW")
*HA 構成 1.3.1.13*　Dold–Kan による dg 圏の単体的豊穣化（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=83)）。対応表の状態：一部（component）。

*主張*　dg 圏の基礎単体的圏は対象をそのまま使い、各写像複体を非負に切断して Dold–Kan を施したものを単体的写像対象にする。

KB-W2型再照合：仮定：dg 圏 C（HA の CΔ の構成と一致。Lean は任意の可換環を許す）。結論：基礎圏を単体的に豊穣化し、Hom を切断した Hom 複体の Dold–Kan 模型と比較し、合成を Alexander–Whitney 写像で与える。任意の鎖複体に対する合成関手そのものの lax monoidal 構造は型に含まれない（Lean が弱い）。

非負切断、Dold–Kan、集合への忘却の合成は右 lax モノイダルである。その構造射を写像複体の合成と組み合わせて、単体的圏の合成を定める。

:::

:::proposition "ha_1_3_1_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory_locallyKan")
*HA 注意 1.3.1.14*　dg 圏から得られる単体的圏のファイブラント性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=84)）。対応表の状態：本体にある。

*主張*　dg 圏から得る基礎単体的圏はファイブラントである。

仮定：dg 圏と対象 x, y（HA と一致。Lean は任意の可換環を許す）。結論：対応する単体的圏のすべての写像空間に KanComplex を与える（一致）。

各写像対象が単体的アーベル群の基礎単体集合なので Kan 複体である。

:::

:::definition "ha_1_3_1_15" (lean := "CategoryTheory.SimplicialNerve, CategoryTheory.SimplicialThickening.Path")
*HA 記法 1.3.1.15*　単体的圏のホモトピー整合 nerve（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=84)）。対応表の状態：Mathlib にある。

*主張*　ホモトピーコヒーレント nerve の標準単体の写像対象では、中間頂点を順番に一つずつ加える部分集合の鎖が、各順列に対する単体を定める。

仮定：単体的豊穣圏 C（HA と一致）。結論：各次数で有限全順序の SimplicialThickening から C への豊穣関手を取り、厚化の写像空間は端点を含む部分集合の包含順序の nerve、合成は和集合（一致）。

$`i\le j` では両端 $`i,j` を持つ部分集合の包含順序の nerve を使い、$`i>j` の写像対象は空とする。合成は和集合であり、中間頂点の追加順を順列で指定する。

:::

:::definition "ha_1_3_1_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag")
*HA 構成 1.3.1.16*　ホモトピー整合 nerve から dg nerve への比較写像（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=84)）。対応表の状態：本体にある。

*主張*　dg 圏の基礎単体的圏のコヒーレント nerve から dg nerve への比較は、部分集合の鎖に対応する単体の符号付き和で定まる。

仮定：dg 圏（HA と一致。Lean は任意の可換環を許す）。結論：整合 nerve の単体から順列で符号付きの立方体単体を足し上げる写像を定め、引き戻しと可換な単体的写像にまとめる（一致）。

両端を固定し中間頂点を加える全順列を走らせ、各鎖の像を同じ次数の鎖と見て順列の符号を付けて加える。微分が dg nerve の関係式を満たし、単調写像にも自然なので単体集合の射が得られる。

:::

:::proposition "ha_1_3_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_isQCatEquivalence")
*HA 命題 1.3.1.17*　ホモトピー整合 nerve と dg nerve の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=85)）。対応表の状態：本体にある。

*主張*　基礎単体的圏のコヒーレント nerve から dg nerve への標準比較は ∞ 圏の同値である。

仮定：dg 圏（HA と一致。Lean は任意の可換環を許す）。結論：1.3.1.16 の比較写像 coherentComparison 自体が IsQCatEquivalence を満たす（一致）。

比較は対象をそのまま送り、写像空間では同じ写像複体の非負切断を用いる。写像空間の比較によって充満忠実性が得られる。

:::

:::definition "ha_1_3_1_18" (lean := "SerrePositivity.DifferentialGraded.DGFunctor")
*HA 定義 1.3.1.18*　dg 関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=85)）。対応表の状態：本体にある。

*主張*　体 $`k` 上の dg 関手は、対象の写像と各写像複体の鎖写像を備え、恒等射と合成を保つ。

仮定：同じ係数環を持つ二つの dg 圏（Lean が弱い：体の代わりに可換環でよい）。結論：対象関数と、単位および合成を保存する写像複体間の射を持つ豊穣関手（一致）。

写像複体の成分は $`k`-線形で微分と可換である。この関手を射として、$`k` 上の dg 圏の通常圏を作る。

:::

# 1.3.2 Derived ∞-Categories

%%%
number := false
tag := "ha-1-3-2"
%%%

*08-dgnerve-derived.html — 2. 導来 ∞ 圏 D(S) と Perf(S)*

\`\`\`text
abbrev Semifree := DGFullSubcategory (Complex S) (complexSemifree S)
def derivedInfinityCategory : SSet.\{u + 1\} := dgNerve S (Semifree S)
abbrev perfectInfinityCategory : SSet.\{u + 1\} := perfectInfinitySubcomplex S
\`\`\`

$`D(S)` は、semifree 複体（K-射影的な模型）の充満 dg 部分圏の dg nerve として定義する。semifree 複体どうしの Hom 複体はすでに「正しい」ので、局所化を取る必要がない。Perf(S) はその充満部分 ∞ 圏である。

- 内容　／　Lean　／　場所
- $`h\,D(S)\simeq H^0(\mathrm{Semifree}(S))`　／　\`derivedInfinityH0Equivalence\`　／　Derived/HomotopyCategoryComparison
- $`h\,D(S)\simeq` Mathlib の \`DerivedCategory (ModuleCat S)\`　／　\`derivedStableHomotopyEquivalence\`　／　Derived/StableHomotopyComparison
- D(S) は安定（任意の可換環上）　／　\`derivedInfinityCategory\_isStable\`　／　Derived/Stability
- 上の圏同値は三角同値（シフトと distinguished 三角形を保存・反映）　／　\`derivedStableHomotopyEquivalenceIsTriangulated\` など　／　Derived/StableTriangulatedEquivalence
- Perf(S) についても $`h\simeq H^0`　／　\`perfectInfinityH0Equivalence\`　／　Derived/PerfectHomotopy

これで「∞ 圏としての D(S)」と「Mathlib の三角圏としての導来圏」が、三角構造まで含めて一致する。第 7 章の三角構造（cofiber 由来）と Mathlib の導来圏の三角構造（写像錐由来）が同じものであることが、ここで確かめられている。

:::definition "ha_1_3_2_1" (lean := "CochainComplex.HomComplex, CochainComplex.HomComplex.Cochain.comp, CochainComplex.HomComplex.δ_comp")
*HA 定義 1.3.2.1*　鎖複体の dg 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=88)）。対応表の状態：Mathlib にある。

*主張*　加法圏の鎖複体全体は dg 圏をなし、次数 $`p` の写像は $`M_n\to N_{n+p}` の族、微分は $`d(f)=d_Nf-(-1)^pf d_M` である。

仮定：前加法圏の整数次数 cochain 複体（Lean が弱い：加法圏の有限双積は不要。次数を反転して HA の鎖複体と比較）。結論：次数 p の Hom の積、微分、次数付き合成と Leibniz 則を与える（一致）。

次数ごとの写像族全体を Hom 群の積として取る。写像族の合成の次数は和であり、微分との関係は Leibniz 則である。

:::

:::proposition "ha_1_3_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv, SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_complexEdge, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_homMk_arrow_eq_of_inclusion")
*HA 注意 1.3.2.2*　鎖複体の dg nerve の対象と射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=88)）。対応表の状態：一部（special）。

*主張*　鎖複体の dg nerve の対象は鎖複体、辺は鎖写像で、二つの辺がホモトピックであることは鎖ホモトピーの存在と同値である。

KB-W2型再照合：仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。

次数一の写像族 $`h_n:M_n\to N_{n+1}` の微分は $`d_Nh+hd_M` となる。その微分が二つの鎖写像の差であることが、dg nerve のホモトピー条件である。

:::

:::definition "ha_1_3_2_4" (lean := "CategoryTheory.Projective, CategoryTheory.EnoughProjectives")
*HA 定義 1.3.2.4*　射影対象と十分な射影対象（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=88)）。対応表の状態：Mathlib にある。

*主張*　アーベル圏の対象 $`P` は、すべてのエピ射に沿って $`\operatorname{Hom}(P,-)` が全射を与えるとき射影的である。

仮定：圏 C（Lean が弱い：アーベル性は不要）。結論：エピに対する射影対象の持ち上げ性と、各対象への射影対象からのエピの存在（一致）。

任意の対象が射影対象からのエピ射を受ける場合、射影対象が十分にあるという。この性質を繰り返し適用して射影分解を作れる。

:::

:::definition "ha_1_3_2_6" (lean := "CochainComplex.Plus")
*HA 記法 1.3.2.6*　有界性による鎖複体の部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=89)）。対応表の状態：一部（component）。

*主張*　$`\operatorname{Ch}^{-}(A)` は十分小さいホモロジー次数で零となる複体、$`\operatorname{Ch}^{+}(A)` は十分大きいホモロジー次数で零となる複体の充満部分圏である。

KB-W2型再照合：仮定：零射を持つ圏の整数次数 cochain 複体（Lean が弱い：有限双積と加法性は不要）。結論：項が十分低い cochain 次数で零となる複体の充満部分圏（Lean が弱い：HA の二方向のうち次数反転後の一方を与える）。

上付き符号をホモロジー次数の上下の有界性と直接同一視すると向きを取り違える。原典の $`\operatorname{Ch}^{-}` は下に有界、$`\operatorname{Ch}^{+}` は上に有界である。

:::

:::corollary "ha_1_3_2_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory_locallyKan")
*HA 系 1.3.2.12*　単体的アーベル群の Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=90)）。対応表の状態：一部（special）。

*主張*　単体的アーベル群の基礎単体集合は Kan 複体である。

KB-W2型再照合：仮定：可換環上の dg 圏から作る特定の単体加群（Lean が強い：任意の単体アーベル群を入力しない）。結論：対応する Hom 単体集合が Kan（一致する特別な場合）。

単体的アーベル群から終対象への写像に、鎖複体の正次数での全射性による Kan ファイブレーションの判定を適用できる。

:::

:::definition "ha_1_3_2_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanSimplicialCategory")
*HA 記法 1.3.2.13*　鎖複体の単体的豊穣圏の記法（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=90)）。対応表の状態：一部（special）。

*主張*　$`\operatorname{Ch}(A)_\Delta` は鎖複体の dg 圏の基礎単体的圏であり、鎖写像への前合成は単体的写像対象の射を誘導する。

Aを可換環R上の加群圏とし、その複体のdg圏を入力すると、doldKanSimplicialCategoryは原文の同じCh(A)∆という構成成分を直接与える。指定fの各Hom全射からのKan fibration性という後半は含まない。

$`f:M\to M'` の前合成で $`\operatorname{Hom}(M'_p,Q_q)\to\operatorname{Hom}(M_p,Q_q)` が全ての $`p<q` で全射なら、$`Q` への単体的写像対象に誘導される射は Kan ファイブレーションである。

:::

:::proposition "ha_1_3_2_15" (lean := "CategoryTheory.Injective.factorThru, CategoryTheory.Injective.comp_factorThru")
*HA 注意 1.3.2.15*　写像空間のファイブレーション判定を満たす場合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=90)）。対応表の状態：一部（component）。

*主張*　鎖写像への前合成の全射性は、各次数でその鎖写像が分裂単射であれば成り立ち、アーベル圏で各次数が単射かつ受け側の複体の各項が入射的でも成り立つ。

KB-W2型再照合：仮定：モノ f と入射対象 J（Lean が弱い：アーベル性は不要。HA の (b) を各次数に適用）。結論：任意の射から J への f に沿う延長と因数分解の等式（Lean が弱い：複体に対する全次数の記述と (a) の分裂の場合は型に含まれない）。

前者では各次数の左逆を使って射を延ばせる。後者は入射対象の延長性を各次数で使う。

:::

:::proposition "ha_1_3_2_17" (lean := "SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_isPushout")
*HA 注意 1.3.2.17*　鎖複体の写像円筒（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=91)）。対応表の状態：一部（special）。

*主張*　加法圏の鎖写像の写像錐は、鎖複体の dg nerve でその射の余ファイバーを表す。

Aを可換環上の加群圏としgを零写像に限ると、standardCofiberSquare\_isPushoutは同じmapping coneのdg nerve内のcofiber性を直接返す。E(1)テンソルによる通常押し出しとの同一視は含まない。

鎖複体のシリンダーによる押し出しで写像錐を作る。$`f:M\to M'` の錐の次数 $`n` は $`M'_n\oplus M_{n-1}` で、写像空間での比較によってこの押し出しが ∞ 圏での余ファイバーを与える。

:::

:::proposition "ha_1_3_2_24" (lean := "CategoryTheory.Idempotents.fullyFaithfulToKaroubi")
*HA 注意 1.3.2.24*　一般の加法圏での Dold–Kan による充満忠実埋め込み（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=97)）。対応表の状態：一部（component）。

*主張*　任意の加法圏の非負鎖複体の通常の nerve から単体的対象の通常の nerve への Dold–Kan 関手は充満忠実である。

KB-W2型再照合：仮定：圏 C（Lean が弱い：加法性は不要）。結論：冪等完備化への通常の充満忠実埋め込み（Lean が弱い：Dold–Kan から従う非負複体と単体対象の間の ∞ 圏の埋め込みはこの型にない）。

加法圏をその冪等完備化に充満忠実に埋め込み、そこで使える Dold–Kan の同値に比較する。原典の式に現れるのは通常の nerve である。

:::

# 1.3.3 The Universal Property of D\^-(A)

%%%
number := false
tag := "ha-1-3-3"
%%%

:::definition "ha_1_3_3_1" (lean := "CategoryTheory.Functor.LeftTExact, CategoryTheory.Functor.RightTExact, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor")
*HA 定義 1.3.3.1*　右・左 t 完全関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=97)）。対応表の状態：一部（component）。

*主張*　$`t` 構造を備えた安定 ∞ 圏の間の完全関手は、非負部分を保てば右 $`t` 完全、非正部分を保てば左 $`t` 完全である。

同じ∞完全関手Fが誘導するhC→hC′の関手にLeftTExact/RightTExactを適用すると、そのn=0のfieldは原文の同じt-structureの半分の頂点を送るという条件を直接返す。∞完全性の条件をこの通常関手のclassだけで得たとはしない。

左右はホモロジー次数の添字による。いずれの定義にも、安定圏の関手としての完全性が前提に入る。

:::

:::lemma_ "ha_1_3_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasSmallColimits_of_coproducts_geometricRealizations, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallColimits_of_coproducts_geometricRealizations")
*HA 補題 1.3.3.10*　有限余極限と幾何学的実現の関係（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=102)）。対応表の状態：一部（stronger-hyp）。

*主張*　有限余積と単体的対象の幾何学的実現から有限余極限が得られ、両方を保つ関手は右完全である。$`n` 圏ではそれぞれの逆も成り立つ。

KB-W2型再照合：仮定：小余積と幾何学的実現（Lean が強い：HA は有限余積で足りる）。結論：小余極限の存在と保存（Lean が強い：有限の場合を含む。Lean が弱い：n 圏での逆向きはこの型にない）。

有限図式の余極限を余積と実現で組み立てる。高次の射が切断されている $`n` 圏では、有限余極限の存在または保存から実現まで扱える。

:::

# 1.3.4 Inverting Quasi-Isomorphisms

%%%
number := false
tag := "ha-1-3-4"
%%%

*spectra-k-theory.html — 8. DG 圏の K 理論との比較 — 二つの定義*

- 　／　明示的な定義（Lurie が採用）　／　$`N^{hc}(\mathrm{DK}(\tau_{\ge0}\mathcal C))`
- 擬圏であること　／　直接計算（HA Prop. 1.3.1.10）　／　Kan 豊穣 ⇒ 擬圏（HTT §1.1.5）から自動
- 準備　／　鎖複体だけ　／　DK を Alexander–Whitney で monoidal に
- 単体　／　有限個の $`f_I`　／　$`\mathfrak C[\Delta^n]` からの単体的関手

内部ホーン $`\Lambda^n_k`（$`0\lt k\lt n`）で欠けるのは $`f_{[n]}` と $`f_{[n]\setminus\{k\}}` だけ。$`k` は内部の点なので $`df_{[n]}` の式に $`f_{[n]\setminus\{k\}}` が係数 $`\pm1` で現れる。$`f_{[n]}:=0` として解き、残りの関係は $`d^2=0` から従う。外側のホーンでは $`f_{[n]\setminus\{0\}}` が和に現れず解けない（擬圏だが Kan でない）。二つの定義は同型でなく圏同値（HA §1.3.1）。形式化には明示的な定義が向く。

*spectra-k-theory.html — 8. DG 圏の K 理論との比較 — 可換な三角形*

$$`K^{\mathrm{dg}}\simeq K\circ N_{\mathrm{dg}}\circ\mathrm{Perf}_{\mathrm{dg}}\colon\ \mathrm{dgCat}_k\to\mathrm{Sp}.`

- DG → ∞：$`\mathcal A\mapsto N_{\mathrm{dg}}(\mathrm{Perf}_{\mathrm{dg}}\mathcal A)`（$`\mathcal A` 自体は pretriangulated とは限らない）。Cohn：$`\mathrm{dgCat}_k[\mathrm{Mor}^{-1}]\simeq\mathrm{Cat}^{\mathrm{perf}}_k`（$`k` 線形な冪等完備安定 ∞ 圏）。

- DG 側の K：完全 dg 加群の Waldhausen 圏（Keller）。Tabuada の DG 版普遍不変量。モデル圏的。

- 対象ごとの比較：Toën–Vezzosi（Waldhausen K は Dwyer–Kan 局所化だけで決まる、仮定は原典確認）、Barwick・BGT。自然性まで込めた明示的な文献は未確認。

- 三角圏だけでは足りない：Schlichting の例（$`\mathbb Z/p^2` と $`\mathbb F_p[\varepsilon]/\varepsilon^2`）。

*spectra-k-theory.html — 8. DG 圏の K 理論との比較 — 普遍性による証明*

- 定義域の同一視：Cohn の同値 $`\Phi`。比べる相手は BGT の $`k` 線形版 $`\mathrm{Mot}^k_{\mathrm{add}}`。

- 加法的不変量の条件（$`E(0)=0`、フィルター余極限、分裂完全列）は両側で同じ形なので $`\mathrm{Mot}^{\mathrm{dg}}_{\mathrm{add}}\simeq\mathrm{Mot}^k_{\mathrm{add}}`、$`\mathcal U(k)\mapsto\mathcal U(\mathrm{Perf}\,k)`。

- $`\mathrm{map}(\mathcal U(\mathrm{Perf}\,k),\mathcal U(\mathcal B))\simeq K(\mathrm{Fun}^{\mathrm{ex}}_k(\mathrm{Perf}\,k,\mathcal B))=K(\mathcal B)`。

- $`K^{\mathrm{dg}}(\mathcal A)\simeq\mathrm{map}(\mathcal U(k),\mathcal U(\mathcal A))\simeq K(\mathrm{Perf}\,\mathcal A)`。余表現関手なので自然性は米田から自動。

限界：仕事は両側の余表現定理（加法性定理を使う）に移っただけ。Tabuada のモチーフ（モデル圏・derivator）が ∞ 圏の意味で普遍的な対象を表すことの確認が要り、明示的な文献は未確認。非連結 K・局所化不変量でも同じ論法が使える。

主な文献

- Lurie, Higher Algebra（§1.3.1 dg nerve、§1.4 安定化、§4.8 $`\mathrm{Pr}^L`）、HTT §1.1.5。

- Blumberg–Gepner–Tabuada, A universal characterization of higher algebraic K-theory。Barwick, On the algebraic K-theory of higher categories。

- Nikolaus–Scholze, On topological cyclic homology（Verdier 商は Thm I.3.3）。Gepner–Groth–Nikolaus, Universality of multiplicative infinite loop space machines。Robalo。

- Waldhausen, Algebraic K-theory of spaces。Thomason–Trobaugh。Schlichting。Toën–Vezzosi, A remark on K-theory and S-categories。Cohn。Tabuada, Higher K-theory via universal invariants。

:::definition "ha_1_3_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniversalConsequences.IsLocalization.precomposition_isFullyFaithful")
*HA 定義 1.3.4.1*　射を反転する ∞ 圏の普遍性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=108)）。対応表の状態：本体にある。

*主張*　$`W` を反転する $`C\to C[W^{-1}]` は、任意の終域への関手の前合成が充満忠実で、本質像が $`W` を同値に移す関手全体となることで特徴付けられる。

仮定：準圏の間の関手と反転する辺の集合（HA と一致。同一宇宙の標的での定義と宇宙変更用補題あり）。結論：W を反転し、前合成が W を反転する関手の充満部分圏との同値を与える（一致）。

普遍性は関手だけでなく自然変換も比較する。条件を満たす圏は同値まで定まり、通常圏の場合にはその nerve を使って同じ局所化を定義する。

:::

:::proposition "ha_1_3_4_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion_isLocalization, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.exists_small_inverting_factorization")
*HA 注意 1.3.4.2*　射の反転の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=108)）。対応表の状態：一部（special）。

*主張*　∞ 圏では任意の射の族を反転する局所化が存在し、指定射を印として加えた単体集合のファイブラント置換で得られる。

KB-W2型再照合：仮定：単体集合と全辺、又は W を反転する与えられた関手（Lean が強い：任意の W で仮定なしの存在ではない）。結論：全辺の局所化、及び任意の W の小さい反転因数分解（Lean が弱い：後者は普遍性を要求しない）。

退化辺も印を付けてよい。印付き単体集合のモデル構造においてこの置換を行うと、反転の普遍性を持つ ∞ 圏が得られる。

:::

:::proposition "ha_1_3_4_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization")
*HA 例 1.3.4.3*　反射的局所化と反転される射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=108)）。対応表の状態：本体にある。

*主張*　反射部分圏 $`C'\subseteq C` は、反射関手が同値に移す射を $`C` で反転した ∞ 圏と同値である。

仮定：充満部分準圏の包含が左随伴 reflector を持つ（HA と一致）。結論：reflector が自ら反転する辺の集合に関する局所化を与える（一致）。

比較関手は $`C'\hookrightarrow C\to C[W^{-1}]` の合成である。反射の単位も反転されるため、局所化後は対象をその反射像と同一視できる。

:::

:::definition "ha_1_3_4_15" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantRelativeCategory, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization")
*HA 定義 1.3.4.15*　モデル圏の基礎 ∞ 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=116)）。対応表の状態：本体にある。

*主張*　モデル圏の基礎 ∞ 圏を表示する関手とは、余ファイブラント対象の通常の nerve から出て、そこにある弱同値の反転後に同値となる関手である。

modelCofibrantRelativeCategoryは同じモデル圏のcofibrant対象と弱同値を与える。weakNerveEdgesとIsLocalizationを同じFへ適用すれば原文のunderlying ∞-categoryの定義全体になる。存在定理のための関手的分解・フレームをこの定義に追加する必要はない。

余ファイブラント対象の間の射を全て取る。局所化の普遍性で基礎 ∞ 圏が同値まで定まる。

:::

:::proposition "ha_1_3_4_16" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelCofibrantHammock_isLocalization, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammock_isLocalization")
*HA 注意 1.3.4.16*　余ファイブラント対象に制限する理由（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=116)）。対応表の状態：一部（component）。

*主張*　二通りの関手的因子分解があるモデル圏では、全対象、ファイブラント対象、余ファイブラント対象、または双方を満たす対象で弱同値を反転しても、同じ基礎 ∞ 圏が得られる。

KB-W2型再照合：仮定：モデル圏の関手的分解と指定フレーム（Lean が強い：明示的な hammock 模型とフレームを選ぶ）。結論：全圏・cofibrant 圏・cf 圏の局所化を、置換の比較を使って構成する（Lean が弱い：fibrant だけの部分圏はこの型に含まれない）。

関手的置換とその弱同値で各表示を比較する。モノイダルモデル圏に適用する場合、余ファイブラント対象を使うと、その間でテンソルが弱同値を保つ性質を利用できる。

:::

:::definition "ha_1_3_4_17" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCofibrantCategory")
*HA 記法 1.3.4.17*　余ファイブラント対象の通常圏としての扱い（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=116)）。対応表の状態：本体にある。

*主張*　余ファイブラント対象の圏 $`A^c` は、$`A` が単体的モデル圏の場合も、通常圏として扱う。

仮定：モデル圏（HA と一致）。結論：cofibrant 対象の通常の圏を用意し AsSmall で宇宙を調整する（一致）。

ここで使う $`N(A^c)` は通常の nerve である。単体的写像対象は、ファイブラントかつ余ファイブラントな対象から別に作るコヒーレント nerve の表示で用いる。

:::

# 1.3.5 Grothendieck Abelian Categories

%%%
number := false
tag := "ha-1-3-5"
%%%

:::corollary "ha_1_3_5_7" (lean := "CategoryTheory.IsGrothendieckAbelian.enoughInjectives")
*HA 系 1.3.5.7*　Grothendieck（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=124)）。対応表の状態：Mathlib にある。

*主張*　Grothendieck アーベル圏には十分な入射対象があり、任意の対象から入射対象への単射が存在する。

仮定：Grothendieck アーベル圏（HA と一致する標準的な 1 圏の公理化）。結論：各対象に入射対象へのモノが存在（一致）。

この単射を繰り返し使うと入射分解を作れる。結論の存在は Grothendieck アーベル圏の仮定による。

:::

:::lemma_ "ha_1_3_5_11" (lean := "CochainComplex.IsKInjective.eq_δ_of_cocycle, SerrePositivity.KST.DerivedGeometry.isKInjective_of_rlp_mono_quasiIso")
*HA 補題 1.3.5.11*　ホモロジーが消える複体からファイブラント複体への写像複体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=126)）。対応表の状態：一部（stronger-hyp）。

*主張*　Grothendieck アーベル圏の非輪状複体 $`M` とファイブラント複体 $`Q` の写像複体 $`\operatorname{Map}(M,Q)` は非輪状である。

同じfibrant複体QにK-injective性も追加すればeq\_δ\_of\_cocycleは同じHom(M,Q)の全次数のcycleがboundaryであると直接返し、原文のacyclic性を得る。無界のモデルinstanceやfibrantだけからの比較は含まない。

写像複体のサイクルは、移動した $`M` から $`Q` への鎖写像である。$`M` が非輪状なら錐への包含は自明余ファイブレーションとなり、ファイブラント性で写像が錐まで延びるのでサイクルは境界になる。

:::

:::proposition "ha_1_3_5_14" (lean := "CochainComplex.IsKInjective.quasiIso_iff")
*HA 命題 1.3.5.14*　擬同型がファイブラント複体への写像に誘導する同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=127)）。対応表の状態：一部（stronger-hyp）。

*主張*　Grothendieck アーベル圏の複体の擬同型は、ファイブラント複体への写像複体に前合成で擬同型を誘導する。

同じ二つのfibrant複体にK-injective性も追加するとquasiIso\_iffは、原文後半の同じ準同型fが鎖ホモトピー同値であるという結論を直接返す。前半の任意始域のHom前合成は含まない。

元の写像の錐の非輪状性を写像複体に移す。とくに両端がファイブラントな擬同型は鎖ホモトピー同値になり、導来 ∞ 圏でも同値を与える。

:::

:::definition "ha_1_3_5_20" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsKappaColimitClosed")
*HA 定義 1.3.5.20*　t 構造とフィルター付き余極限の両立性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=129)）。対応表の状態：本体にある。

*主張*　小さい濾過余極限を持つ安定 ∞ 圏で、$`t` 構造が濾過余極限と両立するとは、$`C_{\le0}` がこれらの余極限で閉じることである。

同じt-structureのC≤0の頂点述語PへIsKappaColimitClosed ℵ0を適用すると、同じC内の全小filtered余極限に対する閉性という原文の両立条件を直接表す。固定宇宙のsmall条件を保持し、通常圏のt切断で代用しない。

条件を課すのは非正部分を周囲の圏に入れたときの閉性である。逐次余極限との両立性も、この条件から従う。

:::

