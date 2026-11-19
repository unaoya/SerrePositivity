import Verso
import VersoManual
import VersoBlueprint
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.AlgebraicTopology.Reedy.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import SerrePositivity.HomotopicalAlgebra.Diagram.PostcompositionQuillen
import SerrePositivity.HomotopicalAlgebra.Diagram.Projective
import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveLeftProper
import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen
import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveSpan
import SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionData
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ModelCategory
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory
import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedAdjunction
import SerrePositivity.HomotopicalAlgebra.Quillen.Equivalence
import SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper
import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingMonomorphisms
import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClass
import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleRightClassInverseImage
import SerrePositivity.HomotopicalAlgebra.Smith.Existence
import SerrePositivity.HomotopicalAlgebra.Smith.WeakEquivalencesAccessible
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.BisimplicialCofibrancy

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT A.2 Model Categories" =>
%%%
number := false
tag := "htt-A-2"
%%%

HTT A.2 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# A.2.1 The Model Category Axioms

%%%
number := false
tag := "htt-A-2-1"
%%%

:::definition "htt_A_2_1_1" (lean := "HomotopicalAlgebra.ModelCategory, HomotopicalAlgebra.IsCofibrant, HomotopicalAlgebra.IsFibrant")
*HTT 定義 A.2.1.1*　モデル圏と fibrant な対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=828)）。対応表の状態：一部（component）。

*主張*　モデル圏は、小極限と小余極限を持つ圏に、持ち上げと因子分解を支配する余ファイブレーション・ファイブレーション・弱同値の三類を指定したものである。

KB-W2原文・型再照合：仮定：通常圏 C と三つの射の類（HTT と一致）。結論：CM2–CM5 と finite limits/colimits の部分、および初期射/終射による cofibrant/fibrant の定義は一致。Mathlib ModelCategory の CM1 は有限極限・有限余極限のみで、原典の全ての小極限・小余極限を内蔵しないため結論の一部。これは抽象的な構造の比較であり、SSet の instance を仮定していない。

三類はレトラクトで閉じ、弱同値は二つから三つの規則を満たす。どちらか一方が弱同値である余ファイブレーションとファイブレーションの組には持ち上げがあり、任意の射をその二通りに因子分解できる。

:::

# A.2.2 The Homotopy Category of a Model Category

%%%
number := false
tag := "htt-A-2-2"
%%%

:::proposition "htt_A_2_2_1" (lean := "HomotopicalAlgebra.leftHomotopyRel_iff_rightHomotopyRel, HomotopicalAlgebra.LeftHomotopyRel.leftHomotopy, HomotopicalAlgebra.RightHomotopyRel.rightHomotopy")
*HTT 命題 A.2.2.1*　筒と道によるホモトピーの四つの判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=829)）。対応表の状態：Mathlib にある。

*主張*　余ファイブラントな $`X` からファイブラントな $`Y` への二射がホモトピックかどうかは、シリンダーによっても道対象によっても同じように判定でき、選択に依らない。

仮定：抽象モデル圏 C、cofibrant X、fibrant Y、f,g:X→Y（HTT と一致）。結論：left/right homotopy relation の iff に加え、いずれも任意の good cylinder/path object に関する homotopy を与え、存在する場合と全ての場合の四条件が一致。good は元の coproduct cofibration/product fibration の条件。具体的な SSet instance は使わない。

シリンダーでは $`X\sqcup X\to Y` を延長し、道対象では $`X\to Y\times Y` を持ち上げる。いずれもある模型で可能ならすべての模型で可能である。両性質を持つ対象間の射をこの関係で割るとホモトピー圏が得られる。

:::

:::proposition "htt_A_2_2_2" (lean := "HomotopicalAlgebra.locallySmall_of_isLocalization")
*HTT 注意 A.2.2.2*　モデル圏の局所化の射集合の小ささ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=830)）。対応表の状態：Mathlib にある。

*主張*　モデル圏の弱同値を反転した圏は、ファイブラントかつ余ファイブラントな模型を使って記述できるので、射集合が小さい。

仮定：抽象モデル圏 C は locally small、L:C→H が元の weak equivalences の localization（HTT と一致）。結論：LocallySmall H、すなわち homotopy category と同値な任意の局所化の Hom も小さい（一致）。C の全小極限・小余極限は原典より不要。

局所化を生成射と関係で書くと小性は直ちには分からない。模型間の Hom 集合をホモトピー関係で割る表示なら集合の大きさを制御できる。

:::

# A.2.4 Left Properness and Homotopy Pushout Squares

%%%
number := false
tag := "htt-A-2-4"
%%%

:::definition "htt_A_2_4_1" (lean := "CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAgainst, CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst")
*HTT 定義 A.2.4.1*　左固有性と右固有性の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=832)）。対応表の状態：Mathlib にある。

*主張*　左固有なモデル圏では余ファイブレーションに沿う押し出しが弱同値を保ち、右固有なモデル圏ではファイブレーションに沿う引き戻しが弱同値を保つ。

仮定：抽象モデル圏 C の元の weakEquivalences/cofibrations/fibrations（HTT と一致）。結論：W.IsStableUnderCobaseChangeAgainst Cof は任意の cofibration に沿う W の pushout 保存、W.IsStableUnderBaseChangeAgainst Fib は fibration に沿う W の pullback 保存であり、原典の左右の固有性に一致。

比較するのは押し出しまたは引き戻しで弱同値の辺から得られる辺である。どの辺に余ファイブレーションまたはファイブレーションを課すかは双対になる。

:::

:::lemma_ "htt_A_2_4_3" (lean := "SerrePositivity.Quillen.weakEquivalence_of_pushout_along_cofibration")
*HTT 補題 A.2.4.3*　cofibrant な始点の弱同値の押出し（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=832)）。対応表の状態：一部（stronger-hyp）。

*主張*　余ファイブラントな二対象の間の弱同値を、始域から出る余ファイブレーションに沿って押し出すと、再び弱同値になる。

KB-W2原文・型再照合：仮定：抽象モデル圏 C、元の pushout、i cofibration、j weak equivalence に加え C が左固有（Lean が強い。A,A′ の cofibrant 性は不要）。結論：同じ pushout map j′ が弱同値（一致）。一般の C で cofibrant A,A′ だけからの型はない。

弱同値の始域だけでなく終域も余ファイブラントと仮定する。モデル圏全体の左固有性を仮定せず、この範囲で押し出しの弱同値保存が得られる。

:::

:::proposition "htt_A_2_4_4" (lean := "SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_span")
*HTT 命題 A.2.4.4*　押出しとホモトピー押出しの比較（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=834)）。対応表の状態：一部（stronger-hyp）。

*主張*　押し出しを作る二脚 $`A'\leftarrow A\to A_1` で $`A\to A'` が余ファイブレーションなら、$`A,A'` が余ファイブラントな場合、またはモデル圏が左固有な場合に、通常の押し出しはホモトピー押し出しでもある。

KB-W2原文・型再照合：仮定：左固有モデル圏 C、span の一辺が cofibration に加え IsLocallyPresentable と小さい cofibrant generators I,J（Lean が強い）。結論：実際の projective homotopy-colimit comparison が元の pushout への弱同値で、原典の (ii) の場合の homotopy pushout と一致。(i) の一般の cofibrant objects 版と非 combinatorial の C は含まない。

他方の脚やその終域に同種の仮定を加える必要はない。片側を余ファイブレーションとして扱い、置換に伴う弱同値を押し出しで比較する。

:::

# A.2.5 Quillen Adjunctions and Quillen Equivalences

%%%
number := false
tag := "htt-A-2-5"
%%%

:::proposition "htt_A_2_5_1" (lean := "SerrePositivity.Quillen.derivedAdjunction, SerrePositivity.Quillen.derived_isEquivalence_of_mate_weakEquivalences")
*HTT 命題 A.2.5.1*　キレン同値の導来関手による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=835)）。対応表の状態：一部（direction）。

*主張*　Quillen 随伴で、左導来関手が同値であること、右導来関手が同値であること、余ファイブラントな始域とファイブラントな終域の間で随伴する二射の弱同値性が一致することは同値である。

KB-W2原文・型再照合：仮定：抽象モデル圏 C,D の Quillen adjunction、元の weak-equivalence localizations と選んだ左右導来関手（HTT と一致）。結論：全 cofibrant X,fibrant Y の adjoint maps における weak equivalence の iff、すなわち条件 (3) から LF が equivalence、導来随伴により RF も equivalence となる方向は一致。導来同値から全 adjoint maps の判定へ戻す型はこの宣言にはなく、三条件全体の iff とは数えない。

最後の判定では $`F(c)\to d` と $`c\to G(d)` を比較する。導来随伴が同値かどうかを、適切な模型を選んだ元の圏の弱同値だけで検査できる。

:::

# A.2.6 Combinatorial Model Categories

%%%
number := false
tag := "htt-A-2-6"
%%%

:::definition "htt_A_2_6_1" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated, CategoryTheory.IsLocallyPresentable")
*HTT 定義 A.2.6.1*　組合せ的モデル圏の生成射（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=836)）。対応表の状態：一部（direction）。

*主張*　組合せ的モデル圏とは、基礎圏が可提示で、余ファイブレーションと自明余ファイブレーションの各類がそれぞれ小さい集合で弱飽和生成されるモデル圏である。

KB-W2原文・型再照合：仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と CofibrantlyGenerated I J（Lean の形式的な可呈示性が強い）。結論：cofibrations=I.rlp.llp、trivial cofibrations=J.rlp.llp、両生成類は small-object argument を持つ。A.1.2 の最小性と合わせ原典の二つの weak saturation generation の方向は一致。原典の四条件による presentable から Mathlib の定義への完全な比較は未供給。

二種類の生成射から、対応する右持ち上げ類を求められる。そのため生成射の選択からモデル構造の三類が決まる。

:::

:::definition "htt_A_2_6_2" (lean := "CategoryTheory.IsCardinalAccessibleCategory, CategoryTheory.Functor.IsCardinalAccessible")
*HTT 定義 A.2.6.2*　可到達な充満部分圏と包含関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=836)）。対応表の状態：一部（direction）。

*主張*　可提示な通常圏の充満部分圏が $`\kappa`-可到達部分圏であるとは、周囲の圏での $`\kappa`-濾過余極限で閉じ、その余極限による小さい生成集合を持つことである。

KB-W2原文・型再照合：仮定：full subcategory D⊆C に intrinsic κ-compact generating family と κ-filtered colimits があり、包含が κ-accessible（Lean が強い）。結論：小さい κ-filtered generating set と ambient C での κ-filtered colimit 閉性という HTT の二条件を満たす方向は一致。HTT は生成集合の各対象の intrinsic κ-compact 性を要求しないため、同じ κ の逆方向をこの定義だけからは得ない。

ある正則基数でこの性質を持てば可到達部分圏と呼ぶ。基数を単に大きくするだけでは、同じ生成表示が使えるとは限らない。

:::

:::corollary "htt_A_2_6_7" (lean := "SerrePositivity.Smith.exists_accessible_rightClass_inverseImage")
*HTT 系 A.2.6.7*　可到達部分圏の逆像の可到達性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=838)）。対応表の状態：一部（component）。

*主張*　可提示な通常圏の間の $`\kappa`-濾過余極限保存関手に沿う $`\kappa`-可到達部分圏の逆像は $`\kappa`-可到達部分圏である。

KB-W2原文・型再照合：仮定：C は Mathlib locally presentable、D=Arrow(E)、E も locally presentable、D0 は小さい生成射 I に対する right lifting class I.rlp、F:C→Arrow(E) は accessible（原典より特殊）。結論：F⁻¹D0 とその包含はある正則 ν で accessible。原典の固定した κ での κ-accessibility より弱く、一般の D0 も含まないが、この inverse-image category そのものの accessibility の部分は直接得られる。

逆像は、像が指定の充満部分圏に属する対象で張る。余極限保存で閉性が引き戻され、小さい濾過生成系も得られる。

:::

:::corollary "htt_A_2_6_8" (lean := "SerrePositivity.Smith.exists_accessible_weakEquivalences, SerrePositivity.Smith.exists_accessible_right_lifting_class, SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated")
*HTT 系 A.2.6.8*　組合せ的模型の三つの可到達な射類（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=838)）。対応表の状態：一部（stronger-hyp）。

*主張*　組合せ的モデル圏の矢印圏で、ファイブレーション、弱同値、自明ファイブレーションをそれぞれ対象とする充満部分圏は可到達部分圏である。

KB-W2原文・型再照合：仮定：抽象モデル圏 C、Mathlib IsLocallyPresentable C と小さい生成 I,J の CofibrantlyGenerated（Lean の形式的仮定が強い）。結論：元の W の full arrow subcategory と inclusion が accessible、F=J.rlp と F∩W=I.rlp も同じ right-lifting-class theorem により accessible となり、原典の三結論に一致。HTT の可呈示性と生成の定義から入力を得る完全な比較は未供給。

ファイブレーションと弱同値の両条件を満たす射も一つの可到達部分圏をなす。基礎の対象の可到達性ではなく、矢印圏内の射の類について述べている。

:::

:::lemma_ "htt_A_2_6_9" (lean := "SerrePositivity.Smith.smithGenerators, SerrePositivity.Smith.smithGenerators_left, SerrePositivity.Smith.smithGenerators_isSmall")
*HTT 補題 A.2.6.9*　自明 cofibration の小さい生成集合（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=839)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示な通常圏で、小生成の弱飽和類 $`C` と、二つから三つの規則を満たす可到達な射の類 $`W` を取り、$`C\cap W` が弱飽和なら、その共通部分も小生成である。

KB-W2原文・型再照合：仮定：Mathlib locally presentable C、Cof=I.rlp.llp、W は accessible な full arrow subcategory で包含も accessible、二対三と Cof∩W の pushout/transfinite/retract 閉性に加え I.rlp⊆W と W の retract 閉性（Lean が強い）。結論：小さい smithGenerators I W が Cof∩W を生成する（一致）。原典の四条件だけの型はない。

$`W` の可到達性は矢印圏内の充満部分圏として要求する。結論は指定の共通部分から小さい集合を選び、弱飽和閉包で共通部分全体を復元できることである。

:::

:::proposition "htt_A_2_6_10" (lean := "SerrePositivity.Smith.modelCategoryOfSmith, SerrePositivity.Smith.cofibrantlyGeneratedOfSmith")
*HTT 命題 A.2.6.10*　Smith の組合せ的模型の認識定理（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=841)）。対応表の状態：一部（stronger-hyp）。

*主張*　前項の条件に加え、$`C` に対する右持ち上げ類が $`W` に含まれるなら、余ファイブレーションが $`C`、弱同値が $`W` の組合せ的モデル構造が存在する。

KB-W2原文・型再照合：仮定：Mathlib locally presentable C、small I、Cof=I.rlp.llp、W の intrinsic accessibility と包含の accessibility、二対三、Cof∩W の pushout/transfinite 閉性、I.rlp⊆W に加え W の retract 閉性（Lean が強い）。結論：指定の三射類 Cof,W,(Cof∩W).rlp に ModelCategory を構成し、small J の CofibrantlyGenerated を得る（一致）。抽象的な構造を新たに構成するので具体的な SSet instance は仮定しない。

ファイブレーションは $`C\cap W` に対する右持ち上げ類である。二つの弱飽和類がともに小生成になるので、二種類の因子分解に小対象論法を適用できる。

:::

:::corollary "htt_A_2_6_11" (lean := "SerrePositivity.Smith.exists_accessible_weakEquivalences, SerrePositivity.Smith.cofibrantlyGeneratedOfSmith")
*HTT 系 A.2.6.11*　弱同値の可到達性と組合せ的模型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=843)）。対応表の状態：一部（stronger-hyp）。

*主張*　基礎圏が可提示で余ファイブレーションが小生成のモデル圏では、組合せ性は、弱同値が矢印圏の可到達部分圏をなすことと同値である。

KB-W2原文・型再照合：仮定：抽象モデル圏 C が Mathlib locally presentable、I は small cofibration generators、W の可到達性は intrinsic accessible category と accessible inclusion を持つ形式（Lean の形式的仮定が強い）。結論：既存の combinatorial generation から元の W の accessibility、逆にその W の入力から同じモデル圏の small trivial-cofibration generators を構成する二方向が一致。原典の可呈示性・accessible full subcategory の定義からの入力比較は未供給。

追加で必要なのは自明余ファイブレーションの小生成性である。逆向きには可到達な弱同値の類と余ファイブレーションの共通部分に小生成性の補題を適用する。

:::

:::proposition "htt_A_2_6_15" (lean := "SerrePositivity.Smith.modelCategoryOfSmith, SerrePositivity.Smith.cofibrantlyGeneratedOfSmith")
*HTT 命題 A.2.6.15*　左固有な組合せ的模型の認識（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=843)）。対応表の状態：一部（stronger-hyp）。

*主張*　可提示な通常圏で、完全な弱同値類と小さい余ファイブレーション生成集合が、指定の二重押し出し条件と右持ち上げ条件を満たせば、左固有な組合せ的モデル構造を定める。

KB-W2原文・型再照合：仮定：原典の W,I に加え Mathlib locally presentable と W の intrinsic/包含の accessibility、W の retract 閉性、Cof∩W の pushout/transfinite 閉性、さらに W の全 Cof=I.rlp.llp に沿う pushout 保存を明示（Lean が強い）。結論：元の Cof,W,(Cof∩W).rlp の combinatorial model を構成し、仮定した最後の閉性がその同じモデルの左固有性となる。この型は perfectness と生成 I の二段 pushout 条件のみから追加の閉性を導くものではない。

二つの押し出しを縦に並べ、上辺を生成余ファイブレーションとし、左下辺が弱同値なら右下辺にもそれを要求する。また生成射に対して右持ち上げ性を持つ射は弱同値と仮定する。余ファイブレーションは生成集合の弱飽和閉包、ファイブレーションはその中の弱同値に対する右持ち上げ類になる。

:::

# A.2.7 Simplicial Sets

%%%
number := false
tag := "htt-A-2-7"
%%%

:::proposition "htt_A_2_7_1" (lean := "SimplexCategory.skeletalEquivalence")
*HTT 注意 A.2.7.1*　単体圏と有限非空線形順序の同値（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=846)）。対応表の状態：Mathlib にある。

*主張*　単体圏 $`\Delta` は有限非空全順序集合すべての圏と同値である。

仮定：単体圏 SimplexCategory と全ての有限非空線形順序の圏 NonemptyFinLinOrd（HTT と一致）。結論：指定 functor による通常圏同値であり、\[n\] の骨格と大きい圏を同一視する記法の根拠に一致。

$`[n]` を代表として選んでも、各有限非空全順序集合を直接使っても、単体的対象を記述できる。

:::

:::definition "htt_A_2_7_2" (lean := "SSet.stdSimplex, SSet.yonedaEquiv, CategoryTheory.nerve")
*HTT 記法 A.2.7.2*　標準単体とその米田による評価（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=846)）。対応表の状態：Mathlib にある。

*主張*　全順序集合 $`J` に対して $`\Delta^J_n` は $`[n]\to J` の単調写像の集合であり、とくに $`\Delta^n=\Delta^{[n]}` から単体集合への写像は、その $`n` 単体に対応する。

仮定：単体集合 S、自然数 n、任意の線形順序 J（HTT と一致）。結論：SSet は単体的集合の圏、Δ\[n\] は uliftYoneda の \[n\] での値、SSet.yonedaEquiv は Hom(Δ\[n\],S)≃S\_n。一般の ΔJ は poset J の nerve（単体は単調列）で、同じ原典の記法に一致。

構造写像は単調写像による前合成で与える。標準単体の場合の自然な対応は米田の補題である。

:::

:::proposition "htt_A_2_7_3" (lean := "SSet.horn, SSet.mem_horn_iff")
*HTT 例 A.2.7.3*　標準単体のホーンの定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=846)）。対応表の状態：一部（special）。

*主張*　角 $`\Lambda_j^n` の $`m` 単体は、像に $`j` を加えても $`[n]` 全体を覆わない単調写像 $`[m]\to[n]` である。

KB-W2原文・型再照合：仮定：J=\[n\] と 0≤j≤n に固定（Lean が強い特殊形）。結論：各 m 単体で range(p)∪\{j\}≠univ という同じ horn の subcomplex の定義は一致。任意の finite ordered J への再添字化を含む horn の同型と、続く番号外の Kan model の存在・固有性の議論まではこの型に含まない。

頂点 $`j` 以外のどれか一つを飛ばすという条件である。幾何的には、$`j` と向かい合う面と全体の内部を除く。有限全順序集合で添字付けた標準単体にも同じ記述を使える。

:::

# A.2.8 Diagram Categories and Homotopy (Co)limits

%%%
number := false
tag := "htt-A-2-8"
%%%

:::definition "htt_A_2_8_1" (lean := "CategoryTheory.MorphismProperty.functorCategory, CategoryTheory.MorphismProperty.llp, CategoryTheory.MorphismProperty.rlp")
*HTT 定義 A.2.8.1*　図式の点ごとの射類と持上げ条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=847)）。対応表の状態：Mathlib にある。

*主張*　図式圏のモデル構造を定める際、弱同値は点ごと、入射的余ファイブレーションと射影的ファイブレーションはそれぞれ対応する点ごとの条件で定める。

仮定：抽象モデル圏 A と小さい通常圏 K（HTT と一致）。結論：P.functorCategory K は ∀k,P(α.app k) なので injective cofibration/projective fibration/weak equivalence の三つの定義に一致し、そのうち W∩Cof の rlp と W∩Fib の llp が残る二つの定義そのもの。model instance の存在とは別に五つの射類を定める。

入射的ファイブレーションは点ごとの自明余ファイブレーションに対する右持ち上げ類であり、射影的余ファイブレーションは点ごとの自明ファイブレーションに対する左持ち上げ類である。

:::

:::proposition "htt_A_2_8_2" (lean := "SerrePositivity.DiagramModel.Projective.modelCategory, SerrePositivity.DiagramModel.Projective.modelCategory_generated, SerrePositivity.DiagramModel.Projective.modelCategory_weakEquivalences, SerrePositivity.DiagramModel.Projective.modelCategory_fibrations")
*HTT 命題 A.2.8.2*　図式圏の射影的な組合せ的模型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=848)）。対応表の状態：一部（component）。

*主張*　組合せ的モデル圏の小さい図式の圏には、射影的モデル構造と入射的モデル構造がともに組合せ的モデル構造として存在する。

KB-W2原文・型再照合：仮定：K が小さい、抽象モデル圏 A が Mathlib locally presentable で小さい生成 I,J を持つ（形式的仮定の比較は A.2.6.1 参照）。結論：同じ Fun(K,A) に objectwise W,F と生成された projective cofibrations の ModelCategory を構成し、小さい generators も出力する。projective の結論は一致するが injective model の存在は含まない。

両構造で弱同値は同じ点ごとの弱同値である。射影的構造ではファイブレーション、入射的構造では余ファイブレーションを点ごとに指定する。

:::

:::proposition "htt_A_2_8_4" (lean := "SerrePositivity.DiagramModel.Projective.leftProper")
*HTT 注意 A.2.8.4*　図式模型の左固有性の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=850)）。対応表の状態：一部（component）。

*主張*　組合せ的モデル圏が左固有または右固有であれば、その小さい図式の射影的・入射的モデル構造もそれぞれ同じ固有性を持つ。

KB-W2原文・型再照合：仮定：K 小さい、A は Mathlib locally presentable かつ cofibrantly generated、左固有な抽象モデル圏（HTT の左固有部分と一致）。結論：実際に構成した projective model の W が projective cofibration に沿う pushout を保つ。原典の projective-left-proper の部分は一致、injective と right-proper の残る三つの部分は含まない。

図式の押し出しと引き戻しを各点で計算できる。射影的余ファイブレーションおよび入射的ファイブレーションもそれぞれ点ごとの条件を満たす。

:::

:::proposition "htt_A_2_8_5" (lean := "SerrePositivity.DiagramModel.Projective.cofibrations_le_objectwise, CategoryTheory.MorphismProperty.antitone_rlp")
*HTT 注意 A.2.8.5*　射影的 cofibration の各点での性質（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=850)）。対応表の状態：一部（stronger-hyp）。

*主張*　射影的余ファイブレーションは評価の左随伴で余ファイブレーションを移した射から弱飽和生成され、すべて入射的余ファイブレーションでもある。

KB-W2原文・型再照合：仮定：K 小さい、A は Mathlib locally presentable な cofibrantly generated 抽象モデル圏（Lean の形式的可呈示性の入力が強い）。結論：実際の projective cofibrations は objectwise cofibrations。W との交わりにも適用して rlp の反単調性を取ると、定義上の injective fibrations⊆projective fibrations も得られ、原典の二含意に一致。injective model の存在はこの二つの class inclusion には不要。

左随伴の値は添字圏の Hom 集合で添字付けた余積を使うので、生成に使う射は各点で余ファイブレーションになる。双対の包含として、入射的ファイブレーションは射影的ファイブレーションである。

:::

:::proposition "htt_A_2_8_6" (lean := "SerrePositivity.DiagramModel.Projective.postcompose_isLeftQuillen, SerrePositivity.DiagramModel.Projective.postcompose_isRightQuillen")
*HTT 注意 A.2.8.6*　キレン随伴の図式圏への作用（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=850)）。対応表の状態：一部（component）。

*主張*　組合せ的モデル圏の間の Quillen 随伴は、小さい図式に点ごとに適用すると、射影的モデル構造でも入射的モデル構造でも Quillen 随伴となる。

KB-W2原文・型再照合：仮定：通常の Quillen adjunction L⊣R と小さい K、両値域は Mathlib locally presentable な cofibrantly generated 模型（HTT の projective adjunction 部分と一致）。結論：実際の projective models の間の postcomposition は左右 Quillen であり、その ordinary adjunction は whiskering で与えられる。injective と Quillen equivalence の保存はこの型には含まない。

もとの随伴が Quillen 同値なら、点ごとの随伴も Quillen 同値になる。さらに同じ図式圏の射影的構造から入射的構造への恒等関手も左 Quillen 同値を与える。

:::

:::proposition "htt_A_2_8_7" (lean := "SerrePositivity.DiagramModel.Projective.colimit_isLeftQuillen, SerrePositivity.DiagramModel.Projective.constant_isRightQuillen")
*HTT 命題 A.2.8.7*　添字変換と射影的キレン随伴（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=851)）。対応表の状態：一部（special）。

*主張*　小さい添字圏の関手に沿う制限は、射影的構造では左 Kan 拡張の右 Quillen 随伴、入射的構造では右 Kan 拡張の左 Quillen 随伴になる。

KB-W2原文・型再照合：仮定：原典の f:K→K′ を K′=一点への唯一の functor に固定、値域は Mathlib locally presentable な cofibrantly generated 模型（Lean が強い特殊形）。結論：(f!,f\*)=(colim,const) は実際の projective models の Quillen adjunction。この (1) の特別な場合は一致するが、任意の f と injective の (2) は含まない。

射影的構造では制限が点ごとのファイブレーションを保つ。入射的構造では制限が点ごとの余ファイブレーションを保つ。いずれも点ごとの弱同値も保つため Quillen 随伴の条件がそろう。

:::

:::proposition "htt_A_2_8_11" (lean := "SerrePositivity.DiagramModel.Projective.hasPointwiseLeftDerivedColimit")
*HTT 注意 A.2.8.11*　導来余極限としてのホモトピー余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=852)）。対応表の状態：一部（component）。

*主張*　射影的モデル構造で左 Kan 拡張を左導来すると、入射的モデル構造によるホモトピー極限の双対としてホモトピー余極限が得られる。

KB-W2原文・型再照合：仮定：小さい K と Mathlib locally presentable な cofibrantly generated 抽象モデル圏 A、元の weak equivalences の任意の localization（HTT の homotopy-colimit の部分と一致）。結論：実際の colim は projective model に関して pointwise left derived functor を持ち、元の homotopy colimit の部分に一致。一般の f! の derived left Kan extension の各点判定を含む「全く双対な議論」までは含まない。

添字圏から一点への Kan 拡張を取るとき、左側では射影的余ファイブラント置換をして余極限を取る。

:::

:::proposition "htt_A_2_8_12" (lean := "SerrePositivity.DiagramModel.ProjectiveSpan.legs_cofibrations, SerrePositivity.DiagramModel.Projective.isCofibrant_obj")
*HTT 例 A.2.8.12*　射影的 cofibrant な span の必要条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=852)）。対応表の状態：一部（direction）。

*主張*　二脚図式 $`X'\leftarrow X\to X''` が射影的余ファイブラントであることは、中央が余ファイブラントで両脚が余ファイブレーションであることと同値である。

KB-W2原文・型再照合：仮定：walking span と同値な小さい K、Mathlib locally presentable な cofibrantly generated 抽象モデル圏（HTT の必要条件と一致）。結論：実際の projectively cofibrant diagram から root X の cofibrant 性と二つの legs の cofibration 性を得る。三条件から projective cofibrancy を構成する逆方向の型はない。

この形の図式に導来余極限を適用すると、二脚の余ファイブラント模型の通常の押し出しとしてホモトピー押し出しを得る。

:::

# A.2.9 Reedy Model Structures

%%%
number := false
tag := "htt-A-2-9"
%%%

:::definition "htt_A_2_9_1" (lean := "HomotopicalAlgebra.ReedyStructure")
*HTT 定義 A.2.9.1*　次数を指定した Reedy 圏の構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=853)）。対応表の状態：一部（component）。

*主張*　Reedy 圏は、同型が恒等射だけである小さい圏に、二種類の射による因子分解系を与え、それらが定める下降関係に無限降下がないものである。

KB-W2原文・型再照合：仮定：二つの乗法的射類と整列次数 deg を予め指定する（Lean が強い）。結論：非恒等逆射・直射での次数の厳密減少と一意な正規分解を ReedyStructure が要求する。原典の分解・降鎖禁止の成分は表すが、元の因子分解系とこのデータの同値、および任意の原典 Reedy 圏への次数の付与は含まない。

下降関係を作るには、右類の射の向きと左類の射の逆向きを合わせる。異なる対象を結ぶステップによる無限下降列を排除する。

:::

:::proposition "htt_A_2_9_4" (lean := "HomotopicalAlgebra.ReedyStructure.skeletal")
*HTT 警告 A.2.9.4*　Reedy 圏の骨格性という必要条件（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=853)）。対応表の状態：一部（direction）。

*主張*　Reedy 圏と同値な圏が原典の意味で Reedy 構造を持てるのは、各同型類の対象が一つだけの場合である。

KB-W2原文・型再照合：仮定：次数付き ReedyStructure を持つ圏（Lean が強い）。結論：同型な対象は等しいという Skeletal C を得るので、原典の「各同型類の代表が一つ」という必要条件は一致。圏同値の下でその条件から構造を移す十分性は含まない。

同値な圏でも同型な対象を重複して持ち得る。定義が恒等射以外の同型を排除するため、この重複があると定義をそのまま移せない。

:::

:::proposition "htt_A_2_9_5" (lean := "SerrePositivity.Reedy.simplex, SerrePositivity.Reedy.simplexInverse, SerrePositivity.Reedy.simplexDirect")
*HTT 例 A.2.9.5*　単体圏の Reedy 構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=853)）。対応表の状態：本体にある。

*主張*　単体圏 $`\Delta` は、全射を左類、単射を右類とする Reedy 圏である。

仮定：実際の SimplexCategory（HTT と一致）。結論：逆射が epi、直射が mono、次数が len の ReedyStructure を構成する。単体圏では epi/mono は単調写像の全射/単射なので原典に一致。

単調写像を像への全射と像の包含に分ける。非恒等な下降ステップで有限順序集合の大きさが減る。

:::

:::proposition "htt_A_2_9_6" (lean := "HomotopicalAlgebra.ReedyStructure.op")
*HTT 例 A.2.9.6*　Reedy 構造の反対圏への移行（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=853)）。対応表の状態：一部（stronger-hyp）。

*主張*　Reedy 圏の反対圏は、右類の反対を左類、左類の反対を右類にして Reedy 圏になる。

KB-W2原文・型再照合：仮定：元の Reedy 構造に整列次数を指定した場合（Lean が強い）。結論：同じ次数を保ち、逆射と直射を入れ替えた反対圏の実際の ReedyStructure を構成する（一致）。原典の次数なし定義との一般の同値は未供給。

射を反転すると因子分解の順序も反転する。対象に課す下降関係は二類を交換しても同じである。

:::

:::definition "htt_A_2_9_7" (lean := "SerrePositivity.Reedy.latchingEvaluation, SerrePositivity.Reedy.matchingEvaluation, SerrePositivity.Reedy.latchingComparison, SerrePositivity.Reedy.matchingComparison")
*HTT 記法 A.2.9.7*　latching と matching 対象の定義（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=854)）。対応表の状態：一部（stronger-hyp）。

*主張*　Reedy 図式の対象 $`j` でのラッチング対象は $`j` に入る非恒等の右類の射に沿う余極限、マッチング対象は $`j` から出る非恒等の左類の射に沿う極限である。

KB-W2原文・型再照合：仮定：整列次数付き Reedy 圏と必要な極限・余極限（次数データが Lean で追加）。結論：非恒等直射の over 圏による colimit と非恒等逆射の under 圏による limit、および X(j) との標準射を構成する。二つの定義と射は原典に一致。

二つはそれぞれ $`L_jX\to X(j)` と $`X(j)\to M_jX` を伴う。素朴に全スライスを使うと恒等射が含まれるため、ここでは該当する部分圏に制限する。

:::

:::proposition "htt_A_2_9_8" (lean := "SerrePositivity.SimplicialLatching.comparison_mono")
*HTT 例 A.2.9.8*　単体集合の latching 射の単射性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=854)）。対応表の状態：一部（component）。

*主張*　単体集合の $`[n]` でのラッチング対象は退化 $`n` 単体の集合であり、単体集合の射が単射であることは各次数の相対ラッチング射が単射であることで判定できる。

KB-W2原文・型再照合：仮定：任意の単体集合 X と n（HTT と一致）。結論：実際の latchingComparison simplexOp n の Mono 性を得る（原典の明記する成分と一致）。像と退化単体集合の指定同型、および任意の単射 f に対する相対 latching 射の iff は含まない。

相対ラッチング射は $`X_n\sqcup_{L_n X}L_n Y\to Y_n` である。もとの射が単射なら、像が退化している単体はもとから退化しているので、この比較射も単射になる。

:::

:::proposition "htt_A_2_9_13" (lean := "SerrePositivity.Reedy.lowerReedy, SerrePositivity.Reedy.upperReedy")
*HTT 注意 A.2.9.13*　次数で切った部分圏の Reedy 構造（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=855)）。対応表の状態：一部（special）。

*主張*　Reedy 圏の良いフィルトレーションの各段に、左右の類を制限した因子分解系が入る。

KB-W2原文・型再照合：仮定：整列次数を指定し、部分圏をその下方または閉切断に限定（Lean が強い特殊形）。結論：射類を制限した実際の ReedyStructure を構成する。この下方閉部分圏について原典の結論に一致するが、任意の good filtration に対する主張ではない。

段内の射の右因子が恒等であれば中間対象は終域そのものである。それ以外の場合も中間対象は終域より先に現れるので、この段に含まれる。

:::

:::corollary "htt_A_2_9_15" (lean := "SerrePositivity.Reedy.boundaryExtension, SerrePositivity.Reedy.BoundaryExtension.toFunctor, SerrePositivity.Reedy.BoundaryExtension.restrictionIso")
*HTT 系 A.2.9.15*　境界分解から一対象追加への図式拡張（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=855)）。対応表の状態：一部（direction）。

*主張*　良いフィルトレーションに沿い Reedy 図式を新しい対象 $`j` 一つへ延長するデータは、標準射 $`L_jX\to M_jX` を一つの対象を通して因子分解するデータと同値である。

KB-W2原文・型再照合：仮定：指定次数の低次部分圏に一つの対象を追加し、L→M の分解を与える（Lean が強い特殊形）。結論：同じ境界分解の中間対象を新しい頂点とする延長 functor を構成し、その元の下方図式への制限同型を得る。原典の (2) から (1) の方向に一致するが、任意 good filtration における二つのデータの同値は含まない。

因子分解の途中の対象が延長後の $`X(j)` になる。周辺の対象はすでに定義済みなので、ラッチング対象とマッチング対象はこの値を決める前に作れる。

:::

:::proposition "htt_A_2_9_19" (lean := "SerrePositivity.Reedy.modelCategory, SerrePositivity.Reedy.reedyLeft_trivialCofibrations_eq, SerrePositivity.Reedy.reedyRight_trivialFibrations_eq")
*HTT 命題 A.2.9.19*　自然数で一意に列挙された Reedy 模型（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=859)）。対応表の状態：一部（special）。

*主張*　Reedy 圏からモデル圏への図式には、点ごとの弱同値、相対ラッチング射で測る余ファイブレーション、相対マッチング射で測るファイブレーションからなるモデル構造が入る。

KB-W2原文・型再照合：仮定：抽象モデル圏 A、必要な境界極限と余極限、自然数次数が全単射（Lean が強い特殊形）。結論：実際の Fun(J,A) に objectwise W と相対 latching/matching によるモデル構造を構成し、trivial cofibration/fibration の二交差式も得る。原文の (C)(F)(W)(WC) にこの特殊形で一致する。任意の整礎次数は含まず、末尾の fibration iff (WF) は trivial fibration に読み替えず一致部分から除外する。

余ファイブレーションでは $`X(j)\sqcup_{L_jX}L_jY\to Y(j)`、ファイブレーションでは $`X(j)\to Y(j)\times_{M_jY}M_jX` を各対象で調べる。自明な場合は対応する比較射に弱同値も課す。原典が (WF) 直前で単に fibration と書く箇所は (F) との対比と双対性から trivial fibration と読む。

:::

:::lemma_ "htt_A_2_9_20" (lean := "SerrePositivity.Reedy.latchingEvaluation_mem_left")
*HTT 補題 A.2.9.20*　全 latching 境界における射類の保存（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=859)）。対応表の状態：一部（special）。

*主張*　Reedy 圏の右類のスライスの二つのふるい $`I'\subseteq I` で、$`I` 上の相対ラッチング射がすべて余ファイブレーションなら、二つのふるいの余極限からできる相対比較射も余ファイブレーションである。

KB-W2原文・型再照合：仮定：自然数次数付き Reedy 圏、I が一対象の latching index 全体、I′ が空（Lean が強い特殊形）。結論：各相対 latching 射が left に属すれば latching colimit 間の実際の射が left に属す。left を cofibration または trivial cofibration として (a)(b) のこの特殊形に一致。任意の二つの sieve の相対 pushout 射は扱わない。

比較射は $`\operatorname{colim}_I F\sqcup_{\operatorname{colim}_{I'}F}\operatorname{colim}_{I'}G\to\operatorname{colim}_I G` である。入力を自明余ファイブレーションとすれば、比較射にも同じ強い結論が成り立つ。

:::

:::proposition "htt_A_2_9_21" (lean := "SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.BisimplicialCofibrancy.reedyCofibrant")
*HTT 例 A.2.9.21*　二重単体集合の Reedy cofibrancy（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=862)）。対応表の状態：一部（special）。

*主張*　二重単体集合の Reedy 余ファイブレーションは単射であり、Reedy モデル構造は入射的モデル構造と一致する。

KB-W2原文・型再照合：仮定：単体集合の ModelCategory と cofibrations=monomorphisms を追加（証明済みの具体的 instance なし、HT-KQ は sorryAx を含む引用入力）。結論：f を空図式→任意の二重単体集合に特殊化した場合の Reedy cofibration 性に一致。任意の f の相対 latching 単射性 iff および injective model との一致は含まない。

外側の各次数でラッチング射の単射性を調べ、内側の次数ごとに単体集合の退化単体の記述を適用する。両モデル構造は弱同値についても点ごとに一致する。

:::

