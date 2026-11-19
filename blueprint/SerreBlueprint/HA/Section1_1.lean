import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.MappingExt
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.Stability
import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.StableHomotopyComparison
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Bicartesian
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronModel
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationSign
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationTriangle
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullStableClosure
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyBinaryBiproduct
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyFiniteBiproduct
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Loop
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceStability
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.DGPretriangulatedStability
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Shift
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoTriangulated
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Suspension
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalence
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionLoopAdjunctionOfEquivalence
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSwapSign
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionTranspose
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnconditionalStableCompactGeneration
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionStability
import SerrePositivity.KST.LocalizingInvariants.CofiberAdjunction
import SerrePositivity.KST.LocalizingInvariants.CofiberBottomLifting
import SerrePositivity.KST.LocalizingInvariants.CofiberRotationAdjunction
import SerrePositivity.KST.LocalizingInvariants.ExactFiniteLimitPreservation
import SerrePositivity.KST.LocalizingInvariants.FullStableClosure
import SerrePositivity.KST.LocalizingInvariants.PullbackStableCategory
import SerrePositivity.KST.LocalizingInvariants.StableFunctorMaps

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HA 1.1 Foundations" =>
%%%
number := false
tag := "ha-1-1"
%%%

HA 1.1 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/ha-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

:::proposition "ha_1_1_0_2" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated")
*HA 注意 1.1.0.2*　体上の dg 圏と安定 ∞ 圏の関係（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=17)）。対応表の状態：一部（component）。

*主張*　体 $`k` 上の前三角 dg 圏のデータは、$`k`-加群スペクトルのモノイダル ∞ 圏で豊穣化された安定 ∞ 圏のデータと対応する。

KB-W2型再照合：仮定：前三角 dg 圏（Lean が弱い：体に限らず可換環上でよい）。結論：その dg nerve が安定。体上の加群スペクトルで豊穣化した安定 ∞ 圏から dg 圏を復元する逆向きと豊穣化の比較は得られない（Lean が弱い）。

写像複体を使う dg 圏は、代数幾何の連接層の複体など代数的な安定 ∞ 圏の模型を与える。この説明で必要なのは $`k`-加群スペクトルによる豊穣化で、一般の安定ホモトピー論の例にはそのような豊穣化を仮定できない。

:::

# 1.1.1 Stability

%%%
number := false
tag := "ha-1-1-1"
%%%

*07-stable.html — 1. 定義 — 零対象と fiber/cofiber*

- 概念　／　Lean　／　中身
- 零対象　／　\`IsZeroVertex z\`、\`HasZeroVertex X\`　／　始対象かつ終対象である頂点（第 1 章の二つの境界充填条件）
- 零角の四角形　／　\`ZeroTriangle X\`　／　四角形 $`\Delta^1\times\Delta^1\to X` で、片方の角が零対象のもの
- fiber 列、cofiber 列　／　\`IsFiberSequence t\`、\`IsCofiberSequence t\`　／　零角の四角形が引き戻し／押し出し
- 射 $`f` の fiber、cofiber　／　\`FiberSquare f\`、\`CofiberSquare f\`　／　$`f` を辺に持つ fiber 列／cofiber 列の四角形

*07-stable.html — 1. 定義 — 判定と基本性質*

- 内容　／　Lean　／　場所
- 零対象・有限極限・有限余極限を持ち、引き戻し ⇔ 押し出しなら安定（HA Prop. 1.1.3.4 の十分性の向き）　／　\`isStable\_of\_finite\_limits\_colimits\`　／　Stable/Definition
- 安定なら、*任意の*四角形について引き戻し ⇔ 押し出し　／　\`IsStable.pullback\_iff\_pushout\_square\`　／　Stable/Bicartesian
- 貼り合わせ：左の四角形が押し出しなら、右が押し出し ⇔ 外側が押し出し（HTT Lemma 4.4.2.1）　／　\`isPushoutSquare\_pasting\_iff\`　／　Stable/Pasting
- 安定性の移送：trivial Kan fibration、宇宙の持ち上げ　／　\`isStable\_of\_trivialKanFibration\`、\`isStable\_of\_ulift\`　／　Stable/TrivialFibrationStability、Stable/UniverseStabilityDescent

*f-04-stable-verdier.html — 1. 安定 ∞ 圏の基本 — 1.1 定義*

quasicategory $`X` が*安定*であるとは、次の三つが成り立つことをいう（HA 1.1.1.9）。

- 零対象を持つ（始対象かつ終対象である対象）。

- すべての射が fiber と cofiber を持つ。

- 零対象を角に持つ四角形
$$`\begin{array}{ccc} x & \to & y \\ \downarrow & & \downarrow \\ 0 & \to & z \end{array}`
  について、「fiber 列（pullback）であること」と「cofiber 列（pushout）であること」が同値。

\`\`\`text
class IsStable (X : SSet.\{u\}) \[Quasicategory X\] : Prop extends HasZeroVertex X where
  fiber\_exists   (f : Edge x y) : Nonempty (FiberSquare f)
  cofiber\_exists (f : Edge x y) : Nonempty (CofiberSquare f)
  fiber\_iff\_cofiber (t : ZeroTriangle X) : IsFiberSequence t ↔ IsCofiberSequence t
\`\`\`

InfinityCategories/HA/StableInfinityCategories/Definition.lean:26。

関手 $`F : X \to Y` が*完全*であるとは、零対象を保ち、cofiber 列を cofiber 列に送ることをいう（\`IsExactFunctor\`、InfinityCategories/Kerodon/LimitsAndColimits/ExamplesOfLimitsAndColimits/ExactFunctor.lean:42）。
安定 ∞ 圏の間では、これは「有限極限を保つ」「有限余極限を保つ」とも同値である（HA 1.1.4.1）。

*f-04-stable-verdier.html — 1. 安定 ∞ 圏の基本 — 1.2 基本的な結果*

- 結果　／　宣言　／　状態
- ホモトピー圏は三角圏（Mathlib の \`Pretriangulated\`・\`IsTriangulated\`）　／　\`isTriangulated\_ho\`（InfinityCategories/HA/StableInfinityCategories/TriangulatedInstance.lean:21）　／　済
- 完全関手はホモトピー圏の三角関手を誘導する　／　\`exactFunctor\_isTriangulated\`　／　済
- 有限極限・有限余極限を持つ　／　\`IsStable.hasLimit\_cospan\` など（InfinityCategories/HA/StableInfinityCategories/StableFiniteLimitsColimits）　／　済
- 懸垂 $`\Sigma` とループ $`\Omega` は互いに逆の同値　／　InfinityCategories/HA/StableInfinityCategories/Suspension・Loop\*　／　済
- Ω による判定（HA 1.4.2.27：有限極限を持ち点付きで、Ω が同値なら安定）　／　なし　／　未着手（D-7）

:::definition "ha_1_1_1_1" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex")
*HA 定義 1.1.1.1*　零対象と点付き ∞ 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=17)）。対応表の状態：本体にある。

*主張*　∞ 圏の零対象は始対象かつ終対象となる対象であり、零対象を持つ圏を点付きといい、零対象全体は存在すれば可縮な Kan 複体をなす。

仮定：頂点 z を持つ単体集合（Lean が弱い：定義時点では準圏性を要求しない）。結論：零対象は始対象かつ終対象であり、点付き性はその存在を表す（一致）。

零対象と別の対象との写像空間を両方向で見ると、いずれも可縮である。これにより、零対象を選んだ後の同値とその高次の選択も一つの可縮な空間に入る。

:::

:::proposition "ha_1_1_1_2" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex")
*HA 注意 1.1.1.2*　点付き ∞ 圏の判定条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=17)）。対応表の状態：一部（direction）。

*主張*　∞ 圏が点付きであることは、始対象 $`\varnothing` と終対象 $`1` が存在し、さらに $`1\to\varnothing` があることと同値である。

HasZeroVertexのchosenZeroVertexは同じ準圏Cの始・終頂点を直接与え、その零頂点の恒等辺を終頂点→始頂点の証人にできる。pointed⇒原文(1)(2)(3)の向き。通常圏の零射の結果だけで逆向きを∞圏へ移したとはしない。

始対象の性質で逆向き $`\varnothing\to1` が得られる。二つの合成はそれぞれ始対象・終対象の自己写像空間で恒等射と同じ成分に属するので、両対象は同値になる。

:::

:::proposition "ha_1_1_1_3" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.hasZeroMorphisms_ho")
*HA 注意 1.1.1.3*　零射が定める写像空間の基点（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=18)）。対応表の状態：本体にある。

*主張*　点付き ∞ 圏のホモトピー圏の零射は、二対象の間を零対象経由で合成した射の類である。

仮定：零頂点を持つ準圏 X（HA と一致）。結論：hX に零射を与える。構成は選んだ零対象を通る一意の射の合成であり、HA の写像空間の合成を π₀ で評価した射（一致）。

零対象を経由する二本の射は、両方の写像空間が可縮なため類を変えない。したがって合成が写像空間のどの連結成分に入るかは、これらの選択から独立である。

:::

:::definition "ha_1_1_1_4" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence")
*HA 定義 1.1.1.4*　三角形とファイバー列・余ファイバー列（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=18)）。対応表の状態：本体にある。

*主張*　点付き ∞ 圏の三角とは左下が零対象の可換正方形で、それが引き戻しならファイバー列、押し出しなら余ファイバー列という。

仮定：単体集合 X と零頂点を持つ正方形（Lean が弱い：準圏性を前提に置かない）。結論：零角を持つ Δ¹×Δ¹ 図式と、その引き戻し・押し出しによるファイバー列・余ファイバー列の判定（一致）。

三角という呼称でもデータは正方形である。左下の零対象によって、正方形を可換にする高次のデータが、二辺の合成を零へ結ぶ情報になる。

:::

:::proposition "ha_1_1_1_5" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow")
*HA 注意 1.1.1.5*　三角形を指定するデータ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=18)）。対応表の状態：本体にある。

*主張*　点付き ∞ 圏の三角は、接続する二辺と、その合成を表す二単体、その合成を零へつなぐ二単体からなる。

仮定：点付き ∞ 圏の三角形（Lean が弱い：準圏性を仮定しない）。結論：零角の証明付きの Δ¹×Δ¹ 図式は二辺 f, g と零角を通る辺、共通の対角線に沿う二つの 2 単体を保持する。底辺と右辺が指定の f, g（一致）。

三角を二辺だけで描くとき、零との比較は図から省略されている。異なる零ホモトピーを選べるため、二辺の列そのものと指定された正方形は区別する。

:::

:::definition "ha_1_1_1_6" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare.fiber, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare.cofiber")
*HA 定義 1.1.1.6*　射のファイバーと余ファイバー（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=19)）。対応表の状態：本体にある。

*主張*　射 $`g:X\to Y` のファイバーは $`X\times_Y 0` を与える引き戻し正方形、余ファイバーは $`Y\amalg_X0` を与える押し出し正方形として定義される。

仮定：零角を持つ点付き単体集合と指定辺 f（Lean が弱い：準圏性を要求しない）。結論：右辺を f に固定した引き戻し、底辺を f に固定した押し出しを保持し、残る頂点がファイバー・余ファイバー（一致）。

零対象へ置き換える端点は二つの定義で逆である。略記の $`\operatorname{fib}(g)` や $`\operatorname{cofib}(g)` は頂点を示すが、普遍性を述べるときは元の図式の脚も含める。

:::

:::proposition "ha_1_1_1_7" (lean := "SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams.bottom_trivialKanFibration, SerrePositivity.KST.LocalizingInvariants.CofiberRotation.bottomSection")
*HA 注意 1.1.1.7*　余ファイバーの関手性と一意性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=19)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付き ∞ 圏で余ファイバー列を最初の射へ送る写像は Kan ファイブレーションで、各ファイバーは空または可縮であり、すべての射が余ファイバーを持つ場合は自明になる。

KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA は点付き性のみで射ごとの余ファイバーが存在する場合を含む）。結論：余ファイバー正方形から底辺への射は自明 Kan fibration で切断を持つ。安定な場合の結論と一致し、余ファイバーが一部しかない場合は扱わない。

余ファイバーの一意性を、一つの射の上にある選択の空間の可縮性として表せる。存在しない射の上ではファイバーが空になるので、全域で余ファイバーを選べる場合と区別する。

:::

:::proposition "ha_1_1_1_8" (lean := "SerrePositivity.KST.LocalizingInvariants.cofiberAdjunction") (uses := "htt_5_2_3_5")
*HA 注意 1.1.1.8*　余ファイバー関手の随伴と余極限保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=19)）。対応表の状態：一部（stronger-hyp）。

*主張*　余ファイバー関手は、対象 $`Z` を零射 $`0\to Z` へ送る端点の左 Kan 拡張に左随伴であり、存在する余極限を保つ。

KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA は点付きかつ余ファイバーを持てばよい）。結論：余ファイバー関手を左随伴とし、対象を零頂点からの射へ送る関手を右随伴とする（一致）。

$`\operatorname{cofib}(f)\to Z` を与えるには、$`f` の像を零にするように $`f` から $`0\to Z` へ写す。押し出しの普遍性がこの対応を写像空間の同値にする。

:::

:::definition "ha_1_1_1_9" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 定義 1.1.1.9*　安定 ∞ 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=19)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏とは、零対象を持ち、すべての射にファイバーと余ファイバーがあり、任意の三角がファイバー列であることと余ファイバー列であることが同値になる ∞ 圏である。

仮定：準圏 X（HA と一致）。結論：零対象が存在し、全辺についてファイバーと余ファイバーが存在し、零角を持つ任意の三角形について両列が同値という Prop（一致）。

零対象を一角に置いた正方形について、引き戻しと押し出しが同じ普遍性を表す。ファイバーと余ファイバーの任意の存在を仮定しているので、必要な正方形を各射から作ってこの双対性を使える。

*07-stable.html — 1. 定義 — 安定性（HA Def. 1.1.1.9）*

\`\`\`text
class IsStable (X : SSet.\{u\}) \[Quasicategory X\] : Prop extends HasZeroVertex X where
  fiber\_exists \{x y : X \_⦋0⦌\}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (FiberSquare f)
  cofiber\_exists \{x y : X \_⦋0⦌\}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) : Nonempty (CofiberSquare f)
  fiber\_iff\_cofiber (t : ZeroTriangle X) : IsFiberSequence t ↔ IsCofiberSequence t
\`\`\`

零対象を持ち、すべての射が fiber と cofiber を持ち、零角の四角形について fiber 列と cofiber 列が一致すること。三条件をそのまま書いている。三角圏の構造や $`\Sigma` の可逆性は定義に含めず、定理として導く（Stable/Definition）。

:::

:::proposition "ha_1_1_1_10" (lean := "CategoryTheory.Abelian.coimageIsoImage")
*HA 注意 1.1.1.10*　ファイバーと余ファイバーの対応とアーベル圏の類比（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=20)）。対応表の状態：Mathlib にある。

*主張*　安定性でファイバー列と余ファイバー列を一致させる条件は、アーベル圏で像と余像を一致させる公理に類比される。

仮定：アーベル圏の射 f（注記の比較対象と一致）。結論：余像から像への標準比較射が同型である。HA の類比で用いられるアーベル圏側の性質（一致）。

どちらの公理も、二つの逆向きの普遍構成のつながりを表す。ただしここで対象にしているのは、零対象を含む正方形の引き戻し・押し出しとしての性質である。

:::

:::proposition "ha_1_1_1_12" (lean := "SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory_isStable, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence")
*HA 例 1.1.1.12*　アーベル圏の導来 ∞ 圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=20)）。対応表の状態：一部（special）。

*主張*　適切な仮定の下で、アーベル圏 $`\mathcal A` の古典的導来圏は、安定な導来 ∞ 圏 $`\mathcal D(\mathcal A)` のホモトピー圏として得られる。

KB-W2型再照合：仮定：可換環 S と加群圏の導来圏の選択 HasDerivedCategory（Lean が強い：アーベル圏一般でなく加群圏の半自由複体模型）。結論：導来 ∞ 圏は安定で、ホモトピー圏と選んだ通常の導来圏が同値（一致）。

複体と準同型の情報を高次の圏に残すと、古典的導来圏で使う三角の背後にあるファイバーと余ファイバーの構成も扱える。具体的な構成は第1.3.2節に移る。

:::

:::proposition "ha_1_1_1_13" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_op")
*HA 注意 1.1.1.13*　反対 ∞ 圏の安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=20)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏の反対 ∞ 圏も安定である。

仮定：安定準圏 X（HA と一致）。結論：単体の順序を反転する反対準圏 X.op が IsStable（一致）。

反対化は零対象を保ち、ファイバーと余ファイバーを交換する。三角の二つの普遍性が同値である条件は、この交換の後も同じである。

:::

:::proposition "ha_1_1_1_14" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable")
*HA 注意 1.1.1.14*　性質としての安定性と加法性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=20)）。対応表の状態：一部（component）。

*主張*　安定性は ∞ 圏に対する性質で、別の構造の選択を要せず、安定な圏にはスペクトルによる標準的な豊穣化がある。

KB-W2型再照合：仮定：準圏 X（HA と一致）。結論：IsStable X は Prop であり構造の選択を追加しない。注記で予告する一般の安定 ∞ 圏の標準的なスペクトル豊穣化は型に含まれない（Lean が弱い）。

加法圏の Hom の群構造が圏自体から回復できることと並行して、安定 ∞ 圏でも後から与える構造を仮定する必要はない。スペクトル値の写像対象は、この内在的な構造の高次の形である。

:::

# 1.1.2 The Homotopy Category of a Stable ∞-Category

%%%
number := false
tag := "ha-1-1-2"
%%%

*07-stable.html — 2. ホモトピー圏の三角構造*

安定 ∞ 圏 $`X` のホモトピー圏 $`hX` に、Mathlib の三角圏の構造が instance として入っている。

- 構造　／　Lean　／　場所
- 加法圏　／　\`preadditive\_ho\`　／　Stable/HomotopyPreadditive
- suspension 関手 $`\Sigma\colon hX\to hX`　／　\`suspensionFunctor X\`　／　Stable/Suspension
- $`\mathbb Z` によるシフト　／　\`hasShift\_ho\`　／　Stable/Shift
- 前三角圏（distinguished = cofiber 三角形と同型なもの）　／　\`pretriangulated\_ho\`　／　Stable/PretriangulatedInstance
- 三角圏（八面体公理 TR4）　／　\`isTriangulated\_ho\`　／　Stable/TriangulatedInstance

*Σ の作り方*：零対象の間に $`x` を置いた四角形 $`x\to0`, $`0\to\Sigma x` を「suspension の四角形」とする。こうした四角形の ∞ 圏から始点を取り出す評価写像は、安定性から trivial Kan fibration になる。その逆（切断）を選び、反対の角を評価したものが $`\Sigma` である。逆の選び方の違いは可逆な 2-胞体で比較する（\`suspensionFunctorChoiceIso\`）。第 2 章で見た「性質を持ち上げ性に変えてから切断を選ぶ」型の構成である。

*distinguished な三角形*：cofiber の四角形から作った三角形 $`x\to y\to z\to\Sigma x` と同型な三角形の全体（\`cofiberDistinguishedTriangles\`）。八面体公理は、二つの cofiber 四角形を貼り合わせた図式（Stable/CofiberOctahedron\*）から導く。

*07-stable.html — 2. ホモトピー圏の三角構造 — 長完全列*

fiber 列 $`x\to y\to z` に $`\mathrm{Hom}_{hX}(w,-)` を適用すると、全整数次数の長完全列が得られる（\`fiberHomSequence\_exact\`、反変版も、Stable/LongExactSequence）。接続準同型は \`fiberHomConnecting\` で、評価式も公開されている。

:::definition "ha_1_1_2_1" (lean := "CategoryTheory.Preadditive, CategoryTheory.Limits.HasFiniteBiproducts")
*HA 定義 1.1.2.1*　加法圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=21)）。対応表の状態：Mathlib にある。

*主張*　加法圏は、零対象と有限双積を持ち、双積から定まる Hom の加法で各 Hom がアーベル群になる圏である。

仮定：通常圏 A（HA と一致）。結論：双線形なアーベル群 Hom と有限双積を組み合わせると HA の加法圏のデータになる。HA では Hom の加法を有限積・余積の比較から決定する。

有限積と有限余積の標準比較は、対角成分が恒等射、その他が零射の行列で与えられる。この比較を使うと、二射の和を対角射、二射の積、余対角射の合成で作れる。定義はこの加法に逆元があることも要求する。

:::

:::proposition "ha_1_1_2_2" (lean := "CategoryTheory.Abelian.ofCoimageImageComparisonIsIso, CategoryTheory.Abelian.coimageIsoImage")
*HA 注意 1.1.2.2*　アーベル圏の像と余像による特徴づけ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=21)）。対応表の状態：Mathlib にある。

*主張*　加法圏がアーベル圏であるとは、各射に核と余核があり、余像から像への標準射が同型であることである。

仮定：加法圏で核と余核を持つこと（HA と一致）。結論：余像から像への標準比較射がすべて同型なら Abelian を構成し、Abelian ではその比較射が同型（一致）。

射 $`f:X\to Y` に対し、余像は $`\ker(f)\to X` の余核、像は $`Y\to\operatorname{coker}(f)` の核として作る。この二つを結ぶ標準射によって条件を述べる。

:::

:::proposition "ha_1_1_2_3" (lean := "CategoryTheory.Preadditive")
*HA 注意 1.1.2.3*　加法圏の合成の双線形性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=22)）。対応表の状態：Mathlib にある。

*主張*　加法圏の合成は二変数で加法的であり、加法圏はアーベル群上の豊穣圏と見なせる。

仮定：前加法圏（Lean が弱い：有限双積の存在は不要）。結論：add\_comp と comp\_add がそれぞれ合成の左右の加法性を表す（一致）。

一方の射を固定すると、もう一方の Hom 群の和が保存される。したがって合成は二つの Hom 群のテンソル積を経由する。

:::

:::proposition "ha_1_1_2_4" (lean := "CategoryTheory.Limits.biprod.isoProd, CategoryTheory.Limits.biprod.isoCoprod")
*HA 注意 1.1.2.4*　加法圏の有限双積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=22)）。対応表の状態：Mathlib にある。

*主張*　加法圏の二対象の積と余積は標準同型で結ばれ、共通の対象を直和 $`X\oplus Y` と書く。

仮定：二対象の二項双積（HA の加法圏では存在。Lean はこの局所的な仮定でよい）。結論：双積と積、双積と余積の標準同型が得られ、合成で積と余積を同一視できる（一致）。

直和には積の射影と余積の包含の双方がある。互いに対応する成分を合成すると恒等射になり、異なる成分の間の合成は零となる。

:::

:::definition "ha_1_1_2_5" (lean := "CategoryTheory.Pretriangulated, CategoryTheory.IsTriangulated")
*HA 定義 1.1.2.5*　Verdier（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=22)）。対応表の状態：Mathlib にある。

*主張*　三角圏は、加法圏、移動の自己同値、指定三角形の類からなり、三角形への延長、回転、射の補完、八面体の公理を満たす。

仮定：加法的な整数シフトを持つ加法圏（HA の平行移動に対応）。結論：完全三角形の集合と同型・回転・延長の公理を Pretriangulated が、八面体公理を IsTriangulated が表す（一致）。

任意の射を三角形に延ばせ、恒等射の退化三角形も入り、同型で閉じる。回転の最後の矢印には移動した第一射の負号を付ける。二つの三角形の最初の可換四角形は三角形の射に補完でき、合成する二射とその合成の三つの余対象は八面体公理の第四の三角形をなす。

:::

:::proposition "ha_1_1_2_6" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopFunctor")
*HA 注意 1.1.2.6*　懸垂関手とループ関手の添字（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=24)）。対応表の状態：本体にある。

*主張*　基礎となる ∞ 圏を明示する場合、懸垂とループの自己関手を $`\Sigma_C,\Omega_C` と書く。

仮定：安定準圏 X（この箇所の文脈と一致）。結論：懸垂・ループの hX 上の関手を X を明示引数にして区別できる（一致）。

圏を変更する関手を扱う際、この添字で始域・終域のどちらの懸垂やループを使うか区別できる。

:::

:::definition "ha_1_1_2_7" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasShift_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftNegOneLoopIso")
*HA 記法 1.1.2.7*　整数によるシフト（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=24)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏では $`[n]` は $`n\ge 0` なら懸垂の $`n` 回反復、$`n\le 0` ならループの $`-n` 回反復を表す。

仮定：安定準圏 X（HA と一致）。結論：hX の整数シフトを備え、+1 が懸垂、−1 がループと自然同型である（一致）。

$`[0]` は恒等である。同じ記号を、安定 ∞ 圏上の関手にもホモトピー圏に誘導される関手にも使う。

:::

:::proposition "ha_1_1_2_8" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionLoopAdjunctionOfLoopEquivalence")
*HA 注意 1.1.2.8*　懸垂とループの随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=24)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付き ∞ 圏で懸垂とループが定義されれば $`\Sigma\dashv\Omega` となり、懸垂からの写像空間は零射を基点とするループ空間で表せる。

KB-W2型再照合：仮定：点付き準圏で指定のループ関手が準圏同値（Lean が強い：HA は両関手が定義されればよい）。結論：懸垂を左随伴、ループを右随伴とする QCatAdjunction（一致）。

$`\operatorname{Map}(\Sigma X,Y)\simeq\Omega\operatorname{Map}(X,Y)` によって、ホモトピー圏の懸垂からの Hom は群、二重懸垂からの Hom はアーベル群になる。懸垂が自己同値なら、任意の対象を二重懸垂としてこの構成を使える。

:::

:::lemma_ "ha_1_1_2_9" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteBiproducts_ho") (uses := "ha_1_1_1_1, ha_1_1_1_8, htt_1_1_2_4, htt_5_1_2_2")
*HA 補題 1.1.2.9*　懸垂が同値のときのホモトピー圏の加法性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=24)）。対応表の状態：一部（stronger-hyp）。

*主張*　余ファイバーを持つ点付き ∞ 圏で懸垂が自己同値なら、そのホモトピー圏は加法圏となる。

KB-W2型再照合：仮定：安定準圏 X（Lean は IsStable で仮定をまとめる。HA は点付き性・余ファイバー・懸垂同値で述べる）。結論：hX の前加法構造と有限双積（一致）。HA の仮定から IsStable への直接の比較宣言は採用した型にない。

二重懸垂からの射を二次ホモトピー群として表すと自然な加法が得られる。懸垂の可逆性でこの加法をすべての Hom に移し、零対象と有限双積に整合する加法になる。

:::

:::lemma_ "ha_1_1_2_10" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.swapIso_eq_neg_id, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.swapIso")
*HA 補題 1.1.2.10*　零対象を含む正方形の転置と懸垂からの射の符号（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=25)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付き ∞ 圏の懸垂からの射を表す零対象二つを含む四角形は、転置するとホモトピー圏で元の射の加法逆元を表す。

KB-W2型再照合：仮定：安定準圏の懸垂正方形（Lean が強い：HA は点付きで余ファイバーを持てばよい）。結論：二つの零角の交換が懸垂上の負の恒等射になり、そこからの射への前合成は符号を反転する（一致する安定な場合）。

二つの零対象を交換すると、零射を基点とする写像空間のループの向きが逆になる。$`\operatorname{Hom}_{hC}(X[1],Y)` の群演算における逆元がこれに対応する。

:::

:::definition "ha_1_1_2_11" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles") (uses := "ha_1_1_1_1, htt_1_1_2_4")
*HA 定義 1.1.2.11*　ホモトピー圏の完全三角形（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=26)）。対応表の状態：一部（stronger-hyp）。

*主張*　点付き ∞ 圏のホモトピー圏で、連結した二つの押し出しと両端の零対象で表示できる三角形を指定三角形とする。

KB-W2型再照合：仮定：安定準圏 X（Lean が強い：HA の定義は点付きで余ファイバーがあればよい）。結論：hX で余ファイバー正方形から得た三角形に同型なものの集合（一致）。

最初の押し出しで $`X\to Y` の余ファイバー $`Z` が現れる。外側の長方形の押し出しが最後の対象を $`X[1]` と同定し、そこへの射が三角形の接続射になる。

:::

:::lemma_ "ha_1_1_2_13" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle.connecting_eq_neg_suspension, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle.triangleIsoRotate")
*HA 補題 1.1.2.13*　二つの押し出しから得られる完全三角形（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=27)）。対応表の状態：本体にある。

*主張*　指定三角形を与える二連の押し出しを転置した形で読む場合、外側で同定した懸垂への接続射に負号を付ければ指定三角形となる。

仮定：安定準圏と余ファイバーの押し出し二つからなる回転長方形（HA と一致）。結論：外側の懸垂との比較を介して境界射が負号を持ち、得られた三角形が余ファイバー三角形の回転に同型（一致）。

転置は懸垂の同定に使う二つの零対象を交換する。接続射の符号の変更は、零射を基点とするループを逆向きにすることに由来する。

:::

:::theorem "ha_1_1_2_14" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasShift_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles") (uses := "ha_1_1_1_1, ha_1_1_2_7, ha_1_1_2_11, htt_1_1_2_4")
*HA 定理 1.1.2.14*　ホモトピー圏の三角圏構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=27)）。対応表の状態：一部（stronger-hyp）。

*主張*　余ファイバーを持つ点付き ∞ 圏で懸垂が自己同値なら、懸垂による移動と押し出しで定義した指定三角形がホモトピー圏を三角圏にする。

KB-W2型再照合：仮定：安定準圏 X（Lean は IsStable を要求。HA の表現は点付き性・余ファイバー・懸垂同値）。結論：余ファイバー三角形と整数シフトを使う hX の三角圏構造（一致）。HA の形で仮定を与える入口は型にない。

各射の余ファイバーから三角形を作れる。可換四角形の余ファイバーへの延長と、連続した押し出しの貼り合わせによって、三角形の射や八面体の図式を作る。

:::

:::proposition "ha_1_1_2_15" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence")
*HA 注意 1.1.2.15*　懸垂が同値であるという仮定と安定性の関係（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=27)）。対応表の状態：一部（direction）。

*主張*　点付きで余ファイバーを持ち、懸垂が自己同値であるという三角構造の構成条件は、安定性と同値である。

KB-W2型再照合：仮定：安定準圏、または点付き準圏と有限極限および指定ループ同値（逆向きは HA の懸垂・余ファイバー条件の双対）。結論：安定性から懸垂同値を得る。逆向きはループ版の安定性判定であり、懸垂版の入力から直接 IsStable を返す型は確認できない（Lean が弱い）。

安定性からこの条件が成り立つ。逆向きの判定は 1.4.2.27 による。従って安定 ∞ 圏のホモトピー圏には、前項の三角構造が付く。

:::

:::proposition "ha_1_1_2_16" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isTriangulated_ho, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronDiagram.octahedronModel")
*HA 注意 1.1.2.16*　安定 ∞ 圏から見た八面体公理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=30)）。対応表の状態：本体にある。

*主張*　三角圏の八面体公理は、安定 ∞ 圏における余ファイバーと押し出しの貼り合わせから従う。

仮定：安定準圏と合成可能な辺の余ファイバー図式（HA と一致）。結論：余ファイバーの貼り合わせから八面体を構成し、hX に八面体公理のインスタンスを与える（一致）。

合成する二射を一つの整合した図式に取り、その中で余ファイバーを比較してからホモトピー圏へ移す。三角圏上の八面体はこの図式の像として得られる。

:::

:::definition "ha_1_1_2_17" (lean := "SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityExt, SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityPiExtEquiv")
*HA 記法 1.1.2.17*　安定 ∞ 圏の Ext 群（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=30)）。対応表の状態：一部（special）。

*主張*　安定 ∞ 圏で $`\operatorname{Ext}_C^n(X,Y)=\operatorname{Hom}_{hC}(X[-n],Y)` とする。

KB-W2型再照合：仮定：加群の導来 ∞ 圏と二対象（Lean が強い：一般の安定 ∞ 圏でなく可換環上の導来 ∞ 圏）。結論：Ext をシフトしたホモトピー圏の Hom で定め、写像空間のホモトピー群と比較する。一般の写像スペクトルを使う比較は含まれない（Lean が弱い）。

負次数では零射を基点とする $`\operatorname{Map}_C(X,Y)` の $`(-n)` 次ホモトピー群になる。写像スペクトルを使えば、同じ式をすべての整数次数で読める。

:::

# 1.1.3 Closure Properties of Stable ∞-Categories

%%%
number := false
tag := "ha-1-1-3"
%%%

:::proposition "ha_1_1_3_1" (lean := "SerrePositivity.KST.LocalizingInvariants.stableFunctorCategory")
*HA 命題 1.1.3.1*　関手 ∞ 圏の安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=30)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏 $`C` と単体集合 $`K` に対し、関手圏 $`\operatorname{Fun}(K,C)` は安定である。

仮定：単体集合 K と安定準圏 A（HA と一致。同じ宇宙内の定式化）。結論：内部 Hom (ihom K).obj A.obj を安定準圏に束ね、任意の K の関手 ∞ 圏の安定性を与える（一致）。

零対象とファイバー・余ファイバーは各点で計算できる。各点で引き戻しと押し出しの条件が一致するので、図式圏でも一致する。

:::

:::definition "ha_1_1_3_2" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition, SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.isStable")
*HA 定義 1.1.3.2*　安定部分圏（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=30)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏の充満部分圏が零対象を含み、ファイバーと余ファイバーで閉じていれば、それ自身も安定であり、安定部分圏と呼ぶ。

仮定：安定準圏と零頂点・ファイバー・余ファイバーに閉じた頂点条件（HA の充満部分圏と一致）。結論：この頂点条件で作る充満部分複体は安定準圏（一致）。

充満性によって写像空間は周囲の圏から引き継がれる。閉性によって周囲で作ったファイバーと余ファイバーが部分圏に入り、そこでも普遍性を保つ。

:::

:::lemma_ "ha_1_1_3_3" (lean := "SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.isStable, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangulatedClosed_shift") (uses := "ha_1_1_1_9, ha_1_1_2_14, htt_1_1_2_4")
*HA 補題 1.1.3.3*　余ファイバーとシフトによる安定部分圏の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=30)）。対応表の状態：一部（stronger-hyp）。

*主張*　安定 ∞ 圏の充満部分圏の安定性は、余ファイバーと移動に関する閉性から従う。

KB-W2型再照合：仮定：安定準圏の充満部分圏でファイバーにも閉じる、または hX の三角閉性（Lean が強い：HA は余ファイバーとシフトのみ）。結論：前者は充満部分圏の安定性、後者はシフト閉性。余ファイバーの逆シフトからファイバー閉性を導く判定は得られない（Lean が弱い）。

ファイバーは対応する余ファイバーを逆懸垂したものなので、負の移動を含む閉性がファイバーを回収する。非空の場合は恒等射の余ファイバーから零対象も得られる。

:::

:::proposition "ha_1_1_3_4" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_finite_limits_colimits, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimitsColimits_of_isStable, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_iff_pushout_square")
*HA 命題 1.1.3.4*　有限極限・有限余極限による安定性の特徴づけ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=31)）。対応表の状態：本体にある。

*主張*　点付き ∞ 圏の安定性は、有限極限・有限余極限が存在し、任意の四角形で引き戻しと押し出しが同値であることで特徴付けられる。

仮定：点付き準圏（HA と一致）。結論：有限極限・有限余極限および全正方形での引き戻し⇔押し出しから安定性を得、安定性から同じ二条件が戻る（一致）。

零対象を含む特殊な四角形での条件から、任意の有限図式と任意の四角形に関する条件が従う。逆向きには四角形の条件をファイバーと余ファイバーのものに適用する。

:::

:::proposition "ha_1_1_3_5" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimitsColimits_of_isStable, SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushoutBinaryBiproduct")
*HA 注意 1.1.3.5*　安定 ∞ 圏の有限双積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=32)）。対応表の状態：一部（component）。

*主張*　安定 ∞ 圏の二対象の余積から積への、対角が恒等射で非対角が零射の比較は同値である。

KB-W2型再照合：仮定：安定準圏と二対象（HA と一致）。結論：有限積・余積の存在と、零始点の押し出しから hX の双積を作る。∞ 圏の正方形自体から余積→積の標準同値を比較する宣言は採用した型にない（Lean が弱い）。

有限積と有限余積の存在に加え、この標準比較によって二つの普遍性を同じ対象で扱える。零対象と組み合わせて有限双積を得る。

:::

:::proposition "ha_1_1_3_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_isStable_unconditional")
*HA 命題 1.1.3.6*　Ind 完備化の安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=32)）。対応表の状態：本体にある。

*主張*　小さい安定 ∞ 圏 $`C` と正則基数 $`\kappa` に対し、$`\operatorname{Ind}_\kappa(C)` は安定である。

仮定：正則基数 κ と小安定準圏 C（HA と一致）。結論：Ind κ C の IsStable を追加の極限保存の仮定なしで返す（一致）。

濾過余極限で加えた対象を含む有限の図式を小さい圏からの図式で近似し、有限極限と有限余極限の整合性を引き継ぐ。米田像の段階で安定性を使う。

:::

:::corollary "ha_1_1_3_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isStable, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idem_isStable")
*HA 系 1.1.3.7*　冪等完備化の安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=33)）。対応表の状態：本体にある。

*主張*　安定 ∞ 圏の冪等完備化は安定である。

仮定：安定準圏 C とその冪等完備化 f（HA と一致）。結論：任意の冪等完備化の標的が安定で、標準模型 Idem C も安定（一致）。

十分な Ind 完備化のコンパクト対象として、元の圏の対象のレトラクトを取り出せる。ここで必要な零対象、有限極限と余極限に関する閉性が保たれる。

:::

# 1.1.4 Exact Functors

%%%
number := false
tag := "ha-1-1-4"
%%%

原典照合の注記　Verdier 列と Karoubi 列の箇所は、原稿が記す別文献の説明。HA の同名の番号付き定理として扱わない。

*07-stable.html — 3. 完全関手*

\`\`\`text
class IsExactFunctor \{X Y : SSet.\{u\}\} (F : X ⟶ Y) : Prop
  -- 零対象と cofiber 列を保つ
\`\`\`

- 安定な $`X` からの完全関手は fiber 列も保つ（\`IsExactFunctor.preservesFiber\`）。逆に fiber 列を保てば完全（\`isExactFunctor\_of\_preservesFiber\`）。

- 一般の押し出し・引き戻しの四角形を保つ（\`preservesPushoutSquare\`、\`preservesPullbackSquare\`）。零角の長方形への貼り合わせで、零角の場合に帰着させる。

- ホモトピー圏の三角関手になる（\`exactFunctor\_isTriangulated\`。\`CommShift ℤ\` つき）。完全関手の間の自然変換はシフトと両立する。

このほか、部分集合の「安定閉包」（cofiber・fiber・シフトで閉じた充満部分圏、\`stableHoClosure\`、Stable/StableHoClosure）とその三角圏の構造がある。Verdier 列や局所化不変量（K 理論側）で使われる。

*08-dgnerve-derived.html — 3. Verdier 商（β3）*

dg 圏 $`D` と対象の集合 $`P` について、Drinfeld の dg 商 $`D/P`（$`P` の対象の恒等射を null-homotopic にする）を考える。

*定理*（Drinfeld 2004 Thm. 3.4 の ∞ 圏版、HA §1.1.4、Kerodon §6.3）. 平坦性の条件のもとで、$`N_{dg}(D)\to N_{dg}(D/P)` は $`P` を零にする局所化で、安定な Verdier 列を与える。

- \`resolvedDGQuotientFunctor\_isLocalization\`：平坦分解した後の商関手は局所化（第 4 章の \`IsLocalization\`）

- \`resolvedDGQuotient\_isStableVerdierSequence\`：安定 Verdier 列

- \`dgQuotient\_isStableVerdierSequence\`：局所 K-flat な場合は分解なしで成り立つ

注意：分解していない path 商がいつでも Verdier 商になるとは主張していない（計画文書の方針）。$`H^0` の Verdier 商との一致だけでは ∞ 関手圏の普遍性にならない点も明記されている。K 理論側では、Thomason の局所化 Perf(X)/Perf\<sub\>Z\</sub\>(X) ≃ Perf(U) や fibration 定理に使われる。

*f-04-stable-verdier.html — 1. 安定 ∞ 圏の基本 — 1.3 完全関手の ∞ 圏*

Verdier 列の普遍性を述べるために、関手 ∞ 圏の中の部分を用意しておく（InfinityCategories/HA/StableInfinityCategories/Exact/ExactFunctorCategory.lean）。

- \`exactFunctors X Y\`：完全関手のなす $`\mathrm{Fun}(X, Y)` の充満部分 ∞ 圏 $`\mathrm{Fun}^{\mathrm{ex}}(X, Y)`。

- \`zeroingExactFunctors X Y P\`：頂点の集合 $`P` を零に送る完全関手のなす部分。

- \`zeroingExactPrecomposition q P … Y\`：$`q : X \to Q` との前合成 $`\mathrm{Fun}^{\mathrm{ex}}(Q, Y) \to \mathrm{Fun}^{\mathrm{ex}}_{P \mapsto 0}(X, Y)`。

*f-04-stable-verdier.html — 2. 部分圏を零にすることと、cofiber 辺を可逆にすること*

安定 ∞ 圏 $`B` と頂点の集合 $`P`（部分圏 $`A` の対象）について、\*\*cofiber が $`P` に入る射\*\*の集合を考える。

$$`W_P \;=\; \{\, f : x \to y \mid \mathrm{cofib}(f) \in P \text{（同型を除いて）}\,\}`

（\`cofiberLocalizingEdges P\`、InfinityCategories/HA/StableInfinityCategories/CofiberLocalizingEdges.lean:21）。安定 ∞ 圏では、次の同値が基本になる。

命題

関手 $`F : B \to E`（$`B` は安定）について、次は同値（\`inverts\_cofiberLocalizingEdges\_iff\_kills\`、同 :58）。

- $`F` は $`W_P` の射をすべて可逆にする。

- $`F` は $`P` の対象をすべて零に送る。

理由：$`z \in P` について、$`0 \to z` の cofiber は $`z` なので、$`W_P` を可逆にするなら $`F(0) \to F(z)` が可逆になり、$`F(z)` は零になる。
逆に $`P` を零に送る完全関手なら、cofiber 列 $`x \to y \to z` が $`F(x) \to F(y) \to 0` に移るので、$`F(f)` は可逆になる。
したがって「$`A` で割る」とは、「cofiber が $`A` に入る射を可逆にする局所化」のことである。

*f-04-stable-verdier.html — 3. Verdier 列 — 3.1 定義（9 人論文による特徴づけ）*

安定 ∞ 圏と完全関手の列 $`A \xrightarrow{i} B \xrightarrow{q} C` が *Verdier 列*であるとは、次の三つが成り立つことをいう（Calmès ほか 9 名『Hermitian K-theory for stable ∞-categories』II、付録 A.1）。

- $`i` は充満忠実。

- $`q` の核（零に送られる対象）は、ちょうど $`i` の本質像。

- $`q` は、cofiber が $`i` の本質像に入る射での*局所化*（第 3 章の Dwyer–Kan 局所化）。

このとき $`C` を Verdier 商 $`B/A` と書く。条件 2 から、$`A` の像は「retract で閉じた安定部分圏」（厚い部分圏）でなければならない。

\`\`\`text
structure IsVerdierSequence \{A B C : StableCategory.\{u\}\} (i : ExactMap A B) (q : ExactMap B C) : Prop where
  fullyFaithful : IsFullyFaithful i.hom
  kernel (b : B.obj \_⦋0⦌) : IsZeroVertex (q.hom.app \_ b) ↔ b ∈ essentialImage i
  quotient : IsLocalization q.hom (cofiberLocalizingEdges (essentialImage i))
\`\`\`

InfinityCategories/HA/StableInfinityCategories/Verdier/VerdierSequence.lean:37。\`StableCategory\` は「単体的集合・quasicategory であること・安定性」を束ねた構造体、\`ExactMap\` は「射・完全性」を束ねた構造体（InfinityCategories/HA/StableInfinityCategories/Verdier/StableCategories.lean）。

定義から出る基本の補題：

- \`kills\_inclusion\`：$`q \circ i` は $`A` のすべての対象を零に送る。

- \`inverts\`：$`q` は cofiber が $`A` に入る射を可逆にする（§2 の命題から）。

- \`universal\`：どの quasicategory $`E` についても、前合成 $`\mathrm{Fun}(C, E) \to \mathrm{Fun}_{W}(B, E)` は同値。

*f-04-stable-verdier.html — 3. Verdier 列 — 3.2 もう一つの定義：完全関手として普遍的な商*

\`\`\`text
structure IsStableVerdierSequence (i : B ⟶ X) (q : X ⟶ Q) \[安定・quasicategory のインスタンス\] : Prop where
  fullyFaithful : IsFullyFaithful i
  inclusionExact : IsExactFunctor i
  quotientExact : IsExactFunctor q
  kills (z : B \_⦋0⦌) : IsZeroVertex ((i ≫ q).app \_ z)
  universal (Y) \[Quasicategory Y\] \[IsStable Y\] :
    IsQCatEquivalence (zeroingExactPrecomposition q (像) … Y)
\`\`\`

InfinityCategories/HA/StableInfinityCategories/Verdier/StableVerdierSequence.lean:15。

- 　／　\`IsVerdierSequence\`　／　\`IsStableVerdierSequence\`
- 形　／　束ねた形（\`StableCategory\`・\`ExactMap\`）　／　束ねない形（\`SSet\` とインスタンス）
- 核の条件　／　核 = 像（像は厚い）　／　像が零に行く（核 ⊇ 像）だけ
- 普遍性　／　すべての quasicategory への関手について（Dwyer–Kan 局所化）　／　安定 ∞ 圏への完全関手についてだけ
- 数学的な意味　／　Verdier 列（9 人論文 A.1）　／　$`\mathrm{Cat}^{\mathrm{ex}}_\infty` の中での cofiber（完全関手の世界での商）
- 使われ方　／　KST の Fibration・LI など約 277 本　／　Derived の dg 商・gluing と NonConnective の 7 本

*関係*：

- \`IsVerdierSequence\` ⇒ \`IsStableVerdierSequence\` は成り立つはずで、計画の M1。証明の筋は次のとおり。局所化の普遍性を、安定な行き先と完全関手に制限する。延長した関手が完全であることは、商の射を分数で表して確かめる（第 5 章）。

- 逆向きには、像が厚いこと（核 = 像）と、完全関手に限らない普遍性（局所化が安定で、Dwyer–Kan 局所化でもあること。M2）が必要である。

*f-04-stable-verdier.html — 3. Verdier 列 — 3.3 二つの形の関係*

束ねた定義の三つの条件は、どれも $`i` と $`q` の下の単体的集合の射（\`i.hom\`・\`q.hom\`）しか使わない。\`essentialImage i\` も「\`i.hom\` の像と同型な頂点」である。
つまり、束ねた形と束ねない形は、包み方が違うだけで中身は同じである。束ねない形の定義と、束ねた定義との同値補題は、まだコードにない（扱いは形式化の側）。

*f-04-stable-verdier.html — 4. 厚い部分圏*

安定 ∞ 圏 $`B` の充満部分圏 $`A` が*厚い*とは、零対象・fiber・cofiber で閉じていて（安定部分圏）、さらに retract で閉じていることをいう。

- 完全関手の核は、いつも厚い部分圏である。したがって Verdier 列の $`A`（の像）は厚い。

- 任意の部分圏 $`A` で割ると、核は $`A` の*厚い閉包*（$`A` を含む最小の厚い部分圏）になる。これが第 5 章の M7 の「一般の場合」である。

いまの状態：一般の述語はなく、dg 版 \`dgThickClosureProperty\`（InfinityCategories/Project/DerivedCategories/DGQuotientThickKernelCriterion.lean、triaRepresentable の retract 閉包）だけがある。
材料として、安定な閉包 \`StableVertexClosure\`（InfinityCategories/HA/StableInfinityCategories/StableVertexClosure、零・同型・fiber・cofiber で閉じた最小の集合）と retract 閉包 \`retractClosure\`（InfinityCategories/HTT/RetractsAndIdempotentCompletion/RetractClosure.lean:24）がある。

一般の安定 ∞ 圏での厚い部分圏・厚い閉包の定義は、まだコードにない。dg 版との一致は M9（第 5 章）。

*f-04-stable-verdier.html — 5. 随伴による判定と半直交分解*

定理（随伴による判定）

$`A \xrightarrow{i} B \xrightarrow{q} C` について、$`i` が充満忠実で、$`q` の核が $`i` の本質像で、$`q` が右随伴 $`j` を持ち、その余単位 $`q j \Rightarrow \mathrm{id}` が同型（$`j` が充満忠実）なら、Verdier 列である。

\`isVerdierSequence\_of\_adjoint\`（InfinityCategories/HA/StableInfinityCategories/Verdier/AdjointVerdier.lean）。条件 3（局所化）は、第 3 章 §5 の「反射による判定」（\`AdjointLocalization.isLocalization\`）から出る。

この状況は*半直交分解* $`B = \langle A, C \rangle` に対応する。$`C` は $`B` の中に $`j(C) = A^{\perp}` として実現され、商は Bousfield 型（第 3 章 §6）になる。
このリポジトリでは、次の形で使われている（InfinityCategories/HA/StableInfinityCategories/Semiorthogonal・Lax と KST/LocalizingInvariants）。

- \`SemiorthogonalDecomposition.isVerdier\`：半直交分解から Verdier 列を作る。

- lax pullback（Tamme）：二つの完全関手 $`f : X \to Z \leftarrow Y : g` の lax pullback は、$`X` と $`Y` の半直交分解を持つ。そこから Verdier 列が得られる（\`laxDifference\_isVerdier\`・\`tammeVerdierSequence\`）。これは Land–Tamme の定理の基礎で、K 理論の excision に使われる。

右随伴が存在しない一般の場合（小さい安定 ∞ 圏の商など）は、この判定は使えない。第 5 章の方法（局所化の存在と分数）が必要になる。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商*

- *普遍性*：安定な充満部分圏 $`\mathcal A\subset\mathcal C`（通常 thick）に対し、exact 関手 $`p\colon\mathcal C\to\mathcal C/\mathcal A` で $`\mathrm{Fun}^{\mathrm{ex}}(\mathcal C/\mathcal A,\mathcal D)\simeq\mathrm{Fun}^{\mathrm{ex}}_{\mathcal A\mapsto0}(\mathcal C,\mathcal D)`。$`\mathrm{Cat}^{\mathrm{ex}}_\infty` での cofiber $`\mathcal C\sqcup_{\mathcal A}0`。

- *構成*：$`W`＝cofiber が $`\mathcal A` に入る射。Dwyer–Kan 局所化 $`\mathcal C[W^{-1}]` は安定で $`p` は exact（Nikolaus–Scholze, On TC, Thm I.3.3）。写像空間 $`\mathrm{Map}_{\mathcal C/\mathcal A}(x,y)\simeq\operatorname{colim}_{y\to y',\,\mathrm{cofib}\in\mathcal A}\mathrm{Map}_{\mathcal C}(x,y')`（分数計算の ∞ 版）。ホモトピー圏は古典的な Verdier 商。

- *presentable 版*：$`\mathrm{Ind}\,\mathcal C/\mathrm{Ind}\,\mathcal A` は $`\mathcal A^\perp` への Bousfield 局所化。$`\mathrm{Idem}(\mathcal C/\mathcal A)\simeq(\mathrm{Ind}\,\mathcal C/\mathrm{Ind}\,\mathcal A)^\omega`（Thomason–Neeman）。冪等完備化の問題（§6 の $`K_0` の非全射性）の出どころ。

- *Verdier 列・Karoubi 列*：$`\mathcal A\to\mathcal C\to\mathcal C/\mathcal A` は fiber かつ cofiber 列。冪等完備化を許したものが Karoubi 列。$`\mathrm{Perf}_Z(X)\to\mathrm{Perf}(X)\to\mathrm{Perf}(U)` は Karoubi 列だが一般に Verdier 列でない。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記）*

定義の番号は 9 人論文 II（arXiv:2009.07224v5）の付録 A。付録 2 も参照。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — 前提*

小さい安定 ∞ 圏と完全関手の ∞ 圏 $`\mathrm{Cat}^{\mathrm{ex}}_\infty` で考える。冪等完備なものだけを集めたのが $`\mathrm{Cat}^{\mathrm{perf}}_\infty`。

- *冪等完備*：冪等な射（$`e^2\simeq e`）がすべて分裂する、つまりすべての retract（直和因子）が対象として存在すること。

- *冪等完備化* $`\mathcal C\mapsto\mathcal C^\natural=\mathrm{Idem}(\mathcal C)`：retract を形式的に付け足す操作。

- *Karoubi 同値*：冪等完備化した後で同値になる完全関手。言い換えると、充満忠実で、値域のすべての対象が像の retract になっている関手（dense な埋め込み）。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — Verdier 列*

*定義*（II.A.1.1）：列 $`\mathcal A\xrightarrow{i}\mathcal B\xrightarrow{p}\mathcal C`（合成は 0）が $`\mathrm{Cat}^{\mathrm{ex}}_\infty` で fiber 列かつ cofiber 列であること。具体的には次の二つ。

- \*\*$`i` は Verdier inclusion\*\*：充満忠実で、像が retract で閉じている（thick）（A.1.9）。

- \*\*$`p` は Verdier projection\*\*：$`\mathcal A` による局所化で、$`\mathcal C\simeq\mathcal B/\mathcal A`（A.1.7）。

Verdier 商 $`\mathcal B/\mathcal A` は「cofiber が $`\mathcal A` に入る射」を反転する Dwyer–Kan 局所化で、普遍性 $`\mathrm{Fun}^{\mathrm{ex}}(\mathcal B/\mathcal A,\mathcal D)\simeq\mathrm{Fun}^{\mathrm{ex}}_{\mathcal A\mapsto0}(\mathcal B,\mathcal D)` と分数表示を持つ（上の「構成」）。例：BGT の $`\mathcal A\to\mathrm{Ind}_\omega(\mathcal A)^\kappa\to\Sigma_\kappa\mathcal A`（Def. 9.1）。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — Karoubi 列*

*定義*（II.A.3.6）：三つの圏を冪等完備化したうえで、$`\mathrm{Cat}^{\mathrm{perf}}_\infty` で fiber 列かつ cofiber 列であること。言い直すと（A.3.8 iii)）、$`\mathcal A\to\mathcal B` が充満忠実で、誘導される $`\mathcal B/\mathcal A\to\mathcal C` が Karoubi 同値であること。Verdier 列では $`\mathcal B/\mathcal A\simeq\mathcal C` だったものを、retract を除いて一致すればよいと緩めた形で、Verdier 列は Karoubi 列だが逆は成り立たない。

*典型例*（Thomason–Trobaugh）：$`\mathrm{Perf}_Z(X)\to\mathrm{Perf}(X)\to\mathrm{Perf}(U)`。$`\mathrm{Perf}(X)/\mathrm{Perf}_Z(X)\to\mathrm{Perf}(U)` は充満忠実だが、$`\mathrm{Perf}(U)` の対象は retract を除いてしか X に持ち上がらない。論文の定理 3.1 の証明（§3.1）が使うのはこの列。

*spectra-k-theory.html — 7. ∞ 圏的な Verdier 商 — 補足：Verdier 列と Karoubi 列（2026-10-28 追記） — 違いが重要になる理由*

- *K\<sub\>0\</sub\> がずれる*：冪等完備化で変わる K 群は K\<sub\>0\</sub\> だけ（Lurie 281 L18 Prop. 1）。Karoubi 列が Verdier 列かどうかは K\<sub\>0\</sub\> の全射性で判定できる（9 人論文 A.3.10、背後は Thomason の分類 A.3.2）。

- *関手の分類*（II.2.7.1、1.6.5）：additive（分裂した Verdier 列を fiber 列に送る。例：連結 K）、Verdier-localising（Verdier 列）、Karoubi-localising（Karoubi 列。Verdier-localising かつ Karoubi 不変、と同値。例：*非連結 K*）。連結 K は Karoubi 列に対して π\<sub\>0\</sub\> で $`K_0(\mathcal C)/K_0(\mathcal C')` だけずれる（Barwick Th. 10.11）。非連結 K は Karoubi 不変なので、Thomason–Trobaugh の列もそのまま fiber 列に送る。論文が非連結 K を必要とする理由の一つ。

- *Ind による言い換え*（A.3.12、Thomason–Neeman）：$`\mathcal A\to\mathcal B\to\mathcal C` が Karoubi 列 ⇔ $`\mathrm{Ind}\,\mathcal A\to\mathrm{Ind}\,\mathcal B\to\mathrm{Ind}\,\mathcal C` が Verdier 列。このとき後者は分裂（Bousfield 局所化）し、$`\mathrm{Idem}(\mathcal B/\mathcal A)\simeq(\mathrm{Ind}\,\mathcal B/\mathrm{Ind}\,\mathcal A)^\omega`。

- *注意*（A.3.8 の警告）：冪等完備な圏の Verdier 商は冪等完備とは限らない。Cat\<sup\>perf\</sup\> で余ファイバーを取るときは商のあとでもう一度冪等完備化する（Efimov の $`\mathrm{Calk}_\kappa=(\mathrm{Ind}^\kappa/A)^{\mathrm{Kar}}`）。BGT の $`\Sigma_\kappa` は Cat\<sup\>ex\</sup\> の余ファイバーなので冪等完備化は付かない。

:::proposition "ha_1_1_4_1" (lean := "SerrePositivity.KST.LocalizingInvariants.exactMap_map_isLimit_finite, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare") (uses := "ha_1_1_1_9, ha_1_1_2_9, ha_1_1_3_4, htt_1_1_2_4, htt_4_4_3_2")
*HA 命題 1.1.4.1*　完全関手の特徴づけ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=33)）。対応表の状態：一部（direction）。

*主張*　安定 ∞ 圏の間の関手では、有限極限を保つこと、有限余極限を保つこと、完全であることが同値である。

KB-W2型再照合：仮定：安定準圏の間の完全関手（HA の完全⇒左・右完全の向きに一致）。結論：任意の有限極限および押し出しを保存する。右完全性を有限余極限全体で述べ、三条件の全方向をまとめた型は未確認（Lean が弱い）。

有限極限は終対象と引き戻しから、有限余極限は始対象と押し出しから作れる。安定圏では零対象と両方の普遍性を持つ四角形を共通に使える。

:::

:::proposition "ha_1_1_4_2" (lean := "SerrePositivity.KST.LocalizingInvariants.ordinaryPullback_isStable, SerrePositivity.KST.LocalizingInvariants.pullbackFst, SerrePositivity.KST.LocalizingInvariants.pullbackSnd")
*HA 命題 1.1.4.2*　完全関手のホモトピー引き戻しと安定性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HA.pdf#page=34)）。対応表の状態：一部（special）。

*主張*　安定 ∞ 圏と完全関手のホモトピー引き戻しは安定で、射影は完全である。安定圏から引き戻しへの関手の完全性は両射影で判定できる。

原文のhomotopy pullbackを現本体の標準catPullback模型として与える場合、ordinaryPullback\_isStableとpullbackFst/pullbackSndは同じ圏の安定性と射影の完全性(1)(2)を直接返す。任意の指定模型への輸送と判定(3)は含まない。

有限極限と有限余極限は対応する各成分で計算できる。成分の引き戻しで零対象を選べ、四角形の二つの普遍性も成分ごとに一致する。

:::

