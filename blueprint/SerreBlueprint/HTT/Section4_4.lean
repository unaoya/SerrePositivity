import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Yoneda
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pasting
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CovariantCosliceClassification
import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FiniteCoproductColimitGeneration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteColimitPreservationGeneration
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedColimitBasicShapes
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedColimitRestriction
import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContractibleConstantColimits
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShapeColimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LocalCanonicalConeOpposite
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Colimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentComparison
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FiniteColimitSpanGeneration
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.EffectiveSplittingRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemCofinality
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemConeRetraction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemWeakContractibility
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.MissingFaceInnerAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ShapeOppositeIso
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingCanonicalColimits
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingRestriction
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingLimitExistence
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakComparison
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakExtension
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakInnerAnodyne
import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "HTT 4.4 Examples of Colimits" =>
%%%
number := false
tag := "htt-4-4"
%%%

HTT 4.4 の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/htt-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。

# 4.4.1 Coproducts

%%%
number := false
tag := "htt-4-4-1"
%%%

:::proposition "htt_4_4_1_1" (lean := "CategoryTheory.Limits.isColimitCoconeFiberwiseColimitOfCocone, CategoryTheory.Limits.isColimitCoconeOfFiberwiseCocone, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_isColimit_iff")
*HTT 命題 4.4.1.1*　非交和図式の余極限と余積（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=312)）。対応表の状態：一部（special）。

*主張*　各図式 $`p_\alpha` に余極限 $`X_\alpha` があるなら、それらの非交和図式に余極限があることと $`X_\alpha` の余積があることは同値で、両者の値は一致する。

KB-W2原文・型再照合：仮定：各部分図式に余極限が存在する（Lean が強い：標的と各添字は通常の圏の神経。離散圏上の Grothendieck 構成を添字の非交和に取る）。結論：全図式の余極限余錐と部分余極限を頂点とする離散図式の余極限余錐を相互に移す（一致する場合。任意の準圏・単体集合形状は含まない）。

非交和図式からの余錐を与えることは、各成分から同じ頂点への余錐を与えることに分かれる。各成分の余極限を用いると、残る普遍性は余積のものになる。

:::

# 4.4.2 Pushouts

%%%
number := false
tag := "htt-4-4-2"
%%%

:::lemma_ "htt_4_4_2_1" (lean := "SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting_iff")
*HTT 補題 4.4.2.1*　押し出し四角形の貼り合わせ（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=313)）。対応表の状態：本体にある。

*主張*　横に並ぶ二つの正方形の左側が押し出しなら、右側が押し出しであることと外側の長方形が押し出しであることは同値である。

仮定：準圏の Δ²×Δ¹ 図式で左四角形が押し出し（HTT と一致）。結論：右四角形が押し出しであることと外周四角形が押し出しであることは同値（一致）。

左側の普遍性でその境界上の写像を置き換えると、外側への試験写像の条件が右側の条件と一致する。

:::

:::proposition "htt_4_4_2_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasColimit_pushout_shape_of_pointSpan") (uses := "htt_1_1_2_4")
*HTT 命題 4.4.2.2*　押し出し形状の余極限と部分余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=314)）。対応表の状態：一部（stronger-hyp）。

*主張*　図式の形が $`K=K'\amalg_{L'}L` で $`L'\to L` が単射なら、三つの制限図式の余極限 $`X,Y,Z` から全図式の余極限を押し出し $`X\amalg_Y Z` として計算できる。

KB-W2原文・型再照合：仮定：片側が単射な形状の押し出しと三つの制限図式の余極限（Lean が強い：標的のすべての三頂点 span に余極限を要求）。結論：元の図式の余極限が存在する（一致する向き。指定した span の押し出しと元の図式の余極限を同定する結論は含まない）。

全図式の余錐は二部分の余錐が共通部分で両立するもの。部分ごとの余極限を使うと、この両立条件を三つの余極限対象の押し出しで表せる。

:::

:::proposition "htt_4_4_2_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentComparison_restrict")
*HTT 注意 4.4.2.3*　部分余極限から誘導される辺の選択（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=314)）。対応表の状態：一部（component）。

*主張*　部分図式の余極限から作る押し出しの脚は可縮な選択まで決まり、有限余極限は始対象と押し出しを使って作れる。

KB-W2原文・型再照合：仮定：部分図式への包含と共通部分の余極限余錐、拡張図式の余極限余錐（Lean が弱い：後者には任意の余錐を許す）。結論：同じ制限余錐から誘導される、共通部分の頂点から拡張余錐の頂点への実際の辺を選ぶ（一致する成分。選択の空間の可縮性は含まない）。

共通部分の余極限から大きい部分の余極限への射は、制限した指定余錐から得られる。その射の選択を含めて図式を組むことが、貼り合わせの計算に必要である。

:::

:::corollary "htt_4_4_2_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts") (uses := "htt_1_1_2_4, htt_4_4_2_2")
*HTT 系 4.4.2.4*　始対象と押し出しからの有限余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=314)）。対応表の状態：一部（direction）。

*主張*　∞ 圏が有限余極限をすべて持つことは、始対象と押し出しを持つことと同値である。

KB-W2原文・型再照合：仮定：準圏に始対象とすべての span の余極限が存在する（HTT の十分方向と一致）。結論：任意の有限単体集合形状の図式に余極限が存在する（一致する方向。逆向きは同じ宣言に含まない）。

空の図式の余極限が始対象になる。他の有限図式は単体を有限回貼ることで作り、その過程で押し出しを使う。

:::

:::corollary "htt_4_4_2_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_finite_of_empty_pointSpan, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit.map_isColimit")
*HTT 系 4.4.2.5*　有限余極限を保つ関手の判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=314)）。対応表の状態：一部（direction）。

*主張*　始域が有限余極限を持つとき、関手が有限余極限を保つことは始対象と押し出しを保つことで判定できる。

KB-W2原文・型再照合：仮定：始対象と押し出しを保つ関手、始域の有限余極限（HTT の十分方向と一致。Lean では空図式と標準三頂点 span に保存される余極限を指定）。結論：任意の有限形状について余極限余錐の像は余極限（一致する方向。逆向きは含まない）。

存在の判定で用いる組み立てを、指定余錐の保存に適用する。各貼り合わせで関手が押し出しを保てば、有限回の後にも普遍性が残る。

:::

:::proposition "htt_4_4_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasPreservedColimit_of_coproducts_finite, SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts") (uses := "htt_1_1_2_4, htt_4_4_2_2, htt_4_4_2_4")
*HTT 命題 4.4.2.6*　小余積と押し出しからの小余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=314)）。対応表の状態：一部（stronger-hyp）。

*主張*　押し出しと $`\kappa`-小余積を持つ ∞ 圏は、すべての $`\kappa`-小図式の余極限を持つ。

KB-W2原文・型再照合：仮定：小余積と押し出しが存在する（Lean が強い：任意の正則濃度の切断ではなく固定宇宙内の全小余積。空余積と押し出しから有限余極限を得て恒等関手に適用）。結論：同じ元の小図式に余極限が存在する（一致する場合。任意の κ による切断は含まない）。

有限の貼り合わせだけでは足りない図式でも、指定された大きさまでの余積を使って部分をまとめられる。二種類の構成で任意の形を扱うための存在結果である。

:::

:::proposition "htt_4_4_2_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.preservesSmallColimits_of_coproducts_finite, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_finite_of_empty_pointSpan")
*HTT 命題 4.4.2.7*　小余積と押し出しによる保存性判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=315)）。対応表の状態：一部（stronger-hyp）。

*主張*　正則基数 $`\kappa` について、始域に $`\kappa`-小余極限があれば、関手がそれらを保つことは押し出しと $`\kappa`-小余積を保つことと同値である。

KB-W2原文・型再照合：仮定：始域の小余極限、押し出しと小余積の保存（Lean が強い：濃度 κ で切断せず固定宇宙で量化。空余積と押し出しの保存から全有限余極限の保存を得る）。結論：元の関手が固定宇宙内の全小余極限を保つ（一致する向きと範囲。任意の κ と逆向きは含まない）。

余極限の構成に使う二種類の普遍性を保つか調べればよい。押し出しの保存だけでは必要な大きさの離散図式の余極限を扱えない。

:::

:::proposition "htt_4_4_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_of_terminalShapeVertex, SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit.map_isColimit") (uses := "htt_1_1_2_4, htt_2_0_0_3, htt_2_1_3_4, htt_4_2_3_6")
*HTT 命題 4.4.2.9*　左ファイブレーションの弱可縮余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=316)）。対応表の状態：一部（special）。

*主張*　弱可縮な形の図式に対し、∞ 圏間の左ファイブレーションは指定余錐の余極限性を像で判定し、像の図式の指定余極限余錐を持ち上げられる。

KB-W2原文・型再照合：仮定：左ファイブレーションと弱可縮な図式形状（Lean が強い：形状に終頂点がある場合。関手には左ファイブレーション性を要求しない）。結論：同じ余極限余錐の像が余極限となる（(1) の保存方向が一致する場合。反映と底の指定余錐の持ち上げ (2) は含まない）。

ここでの持ち上げは、底で別の同値な余錐へ変えるのではなく、もとの底の余錐を像として得る。形の弱可縮性と左ファイブレーションの両方を使う。

:::

# 4.4.3 Coequalizers

%%%
number := false
tag := "htt-4-4-3"
%%%

:::proposition "htt_4_4_3_2" (lean := "CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_hasColimit_iff") (uses := "htt_1_1_2_4, htt_4_4_2_6")
*HTT 命題 4.4.3.2*　余等化子と小余積からの小余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=317)）。対応表の状態：一部（special）。

*主張*　正則基数 $`\kappa` について、∞ 圏がすべての $`\kappa`-小余極限を持つことは、余等化子と $`\kappa`-小余積を持つことと同値である。

KB-W2原文・型再照合：仮定：余等化子と小余積が存在する（Lean が強い：通常の圏の神経を標的に、添字も固定宇宙の通常の圏の神経に限る）。結論：通常の圏で全小余極限を得て、同じ図式の神経の余極限存在へ移せる（一致する向きと範囲。任意の単体集合形状、濃度 κ による切断と逆向きは含まない）。

押し出しも、余積を使って平行な二射を組んで余等化する形で扱える。このため始対象などを別に列挙する必要がない。

:::

# 4.4.4 Tensoring with Spaces

%%%
number := false
tag := "htt-4-4-4"
%%%

:::definition "htt_4_4_4_1" (lean := "CategoryTheory.Functor.RepresentableBy, CategoryTheory.Functor.RepresentableBy.homEquiv_eq")
*HTT 定義 4.4.4.1*　豊穣前層の表現可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=318)）。対応表の状態：一部（special）。

*主張*　閉モノイダル圏 $`\mathcal V` に豊穣化された反変関手 $`G` は、ある対象 $`C` と $`\mathbf1\to G(C)` がすべての $`X` で $`\operatorname{Map}(X,C)\cong G(X)` を誘導するとき表現可能である。

KB-W2原文・型再照合：仮定：閉モノイダル圏に豊穣な前層と表現対象（Lean が強い：豊穣基底は直積モノイダル圏 Type）。結論：恒等射の像 η が誘導する自然な Hom 写像が各対象で同型になるという表現データ（一致する場合）。

単位からの射は関手の値の普遍元に当たる。$`X\to C` の豊穣写像対象にその元を作用させることで、比較の同型が具体的に定まる。

:::

:::proposition "htt_4_4_4_2" (lean := "CategoryTheory.Functor.RepresentableBy, CategoryTheory.Functor.RepresentableBy.isRepresentable")
*HTT 注意 4.4.4.2*　指定した対象による前層の表現（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=318)）。対応表の状態：一部（special）。

*主張*　豊穣関手を表現するとき、普遍元と対象の組を略して、対象 $`C` が関手を表現するということがある。

KB-W2原文・型再照合：仮定：対 (C, η) が豊穣前層を表現する（Lean が強い：豊穣基底は Type）。結論：C を表現対象とするデータが前層の表現可能性を与える（一致する場合）。

この略称は普遍元が比較に使われることを省略して書くもの。同じ対象を指しても、実際の自然同型を使うときには普遍元を含めて読む。

:::

:::proposition "htt_4_4_4_3" (lean := "CategoryTheory.Functor.CorepresentableBy, CategoryTheory.Functor.CorepresentableBy.homEquiv_eq")
*HTT 注意 4.4.4.3*　豊穣共変関手の余表現可能性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=318)）。対応表の状態：一部（special）。

*主張*　豊穣関手の余表現可能性は、反対圏を用いて表現可能性を双対化した概念である。

KB-W2原文・型再照合：仮定：豊穣共変関手と余表現対象（Lean が強い：豊穣基底は Type）。結論：恒等射の像 η による自然な Hom 写像が各対象で同型になるという双対の表現データ（一致する場合）。

表現可能な反変関手では試験対象から表現対象へ射が向かう。余表現では固定対象から試験対象へ向かう写像対象を使う。

:::

:::proposition "htt_4_4_4_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverProjection_rightFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone")
*HTT 注意 4.4.4.6*　スライスの表現可能性と極限の存在（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=319)）。対応表の状態：本体にある。

*主張*　図式 $`p:K\to\mathcal C` の錐の右ファイブレーション $`\mathcal C_{/p}\to\mathcal C` が表現可能であることは、$`p` の極限が存在することと同値である。

仮定：準圏 C の任意の図式 p（HTT と一致）。結論：C/p→C は右ファイブレーションであり、HasLimit p は定義により C/p の終頂点の存在、すなわち右ファイブレーションの表現可能性である（一致）。

試験対象 $`Y` 上のファイバーが、$`Y` を頂点とする錐を集める。その右ファイブレーションを対象 $`L` が表現すれば、そこへの写像で錐が表されるので $`L` が極限になる。

:::

:::proposition "htt_4_4_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderProjection_leftFibration, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone")
*HTT 注意 4.4.4.7*　コスライスの余表現可能性と余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=319)）。対応表の状態：一部（component）。

*主張*　表現可能な右ファイブレーションの議論を反対化すると、余表現可能な左ファイブレーションの議論が得られる。

KB-W2原文・型再照合：仮定：準圏 C の任意の図式 p（HTT の双対の主張と一致）。結論：C の p 下のコスライスは左ファイブレーションであり、その全空間の始頂点の存在が HasColimit p である（一致する成分。一般の左ファイブレーションについて指定元による余表現と共変同値の双対判定は含まない）。

錐と右ファイブレーションを入れ替えて余錐と左ファイブレーションを使う。対象から出る写像の空間が、余錐ファイバーを余表現する。

:::

:::definition "htt_4_4_4_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram, SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantCosliceClassificationIso")
*HTT 記法 4.4.4.8*　コスライスを分類する共変関手（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=319)）。対応表の状態：一部（component）。

*主張*　$`F_p:h\mathcal C\to\mathcal H` は余錐の左ファイブレーションに対応する豊穣関手で、一点図式 $`X` なら $`\operatorname{Map}(X,-)`、定値 $`K`-図式 $`X` ならその値の $`[K]` による冪を与える。

KB-W2原文・型再照合：仮定：準圏上の図式とその下の左ファイブレーション（HTT と一致）。結論：直線化で分類関手を作り、単点図式の場合は元の共変 Hom 関手との同型を与える（一致する内容。指定の H 豊穣ホモトピー圏での表示は含まない）。

図式が定値の場合、各 $`Y` への余錐を、$`K` でパラメータづけた $`X\to Y` の族として読める。これが $`\mathcal H` における冪である。

:::

:::corollary "htt_4_4_4_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantJoinCocone_isColimit") (uses := "htt_1_1_2_4")
*HTT 系 4.4.4.10*　弱可縮な同値図式の余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=320)）。対応表の状態：一部（special）。

*主張*　弱可縮な形からの全辺同値な図式には余極限が存在し、指定余錐が余極限となることは、新たに加えた辺もすべて同値になることと同値である。

KB-W2原文・型再照合：仮定：準圏と弱可縮な単体集合、辺を同値に送る図式（Lean が強い：図式とその余錐を同じ頂点への定値写像とする）。結論：同じ定値余錐は余極限（一致する場合。任意の同値図式とその指定延長の判定は含まない）。

図式を点のように扱えるのは、形が弱可縮であり、しかも図式内で非可逆な輸送を含まない場合である。余錐の判定は、錐点も同じ同値の族に加わるかを見る。

:::

# 4.4.5 Retracts and Idempotents

%%%
number := false
tag := "htt-4-4-5"
%%%

:::definition "htt_4_4_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSplit_object_cases")
*HTT 定義 4.4.5.2*　冪等元と強弱の分裂図式の添字（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=322)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Idem}^+` は $`Y\xrightarrow{i}X\xrightarrow{r}Y` と $`ri=1_Y` を持つ指定二対象圏の nerve、$`\mathrm{Idem}` はその $`X` 上の充満部分、$`\mathrm{Ret}` は $`ri=1_Y` を表す二単体の像である。

仮定：二元冪等モノイドの一対象圏とその二対象の分裂圏（HTT と一致。Lean は後者を同じ二対象を持つ Karoubi 圏で構成）。結論：Idem と Idem⁺ は同じ圏の神経、Ret は同じ二単体の長辺を一点に潰す商であり、その標準包含を与える（一致）。

$`X` の自己射として恒等射と $`ir` が残る。$`\mathrm{Ret}` ではまず左逆を表す一つの面だけを採り、$`\mathrm{Idem}^+` の残りの単体は別の整合データになる。

:::

:::proposition "htt_4_4_5_3" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape")
*HTT 注意 4.4.5.3*　二元冪等モノイドの神経（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=322)）。対応表の状態：一部（component）。

*主張*　$`\mathrm{Idem}` は二元モノイド $`\{1,e\}`、$`e^2=e` の分類単体集合で、各次数に非退化単体をちょうど一つ持ち、それらの顔も非退化である。

KB-W2原文・型再照合：仮定：HTT の Idem（一致）。結論：恒等元と非恒等冪等元を持つ二元モノイドの一対象圏の神経として定義する（一致する成分。各次元の非退化単体の個数とこの性質による一意性は含まない）。

非退化な単体は自己射 $`e` の反復だけでできる。隣接する二つを合成しても $`e` になることが、顔で退化しない理由である。

:::

:::definition "htt_4_4_5_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting")
*HTT 定義 4.4.5.4*　冪等図式と弱い分裂と強い分裂（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=322)）。対応表の状態：本体にある。

*主張*　∞ 圏内の冪等子、弱レトラクション図式、強レトラクション図式は、それぞれ $`\mathrm{Idem}`、$`\mathrm{Ret}`、$`\mathrm{Idem}^+` からの写像であり、それらを内部 Hom に集める。

仮定：準圏 C（Lean が弱い：定義には任意の単体集合を許す）。結論：同じ Idem・Ret・Idem⁺ 上の全単体的写像として三種類の図式を定める。StrongSplitting は Idem への制限を固定した表示であり、元の Idem⁺ 上の写像とその同じ制限を回収する（一致）。

冪等という一つの等式を課すだけでなく、その等式の高次の整合性を、決まった単体的な形の像として指定する。弱図式ではこのうち二単体の部分を指定する。

:::

:::proposition "htt_4_4_5_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagramEquiv")
*HTT 注意 4.4.5.5*　弱い分裂図式と長辺が恒等の二単体（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=322)）。対応表の状態：本体にある。

*主張*　弱レトラクションは左逆の等式を示す二単体と同じデータで、$`\mathrm{Idem}` からの関手は冪等辺に加えて $`e^2\simeq e` とその全高次整合性を指定する。

仮定：準圏 C（Lean が弱い：任意の単体集合）。結論：Ret→C のデータは二単体と、長辺を潰した同じ頂点のデータに全単射で対応する（一致）。

ホモトピー圏では二単体を等式として忘れる。∞ 圏では、同じ等式に異なる整合データを与えられるため、形全体からの写像と区別する。

:::

:::proposition "htt_4_4_5_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_innerAnodyne")
*HTT 命題 4.4.5.6*　弱い分裂から強い分裂への包含（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=323)）。対応表の状態：本体にある。

*主張*　単体的包含 $`\mathrm{Ret}\hookrightarrow\mathrm{Idem}^+` は内アノダインである。

仮定：元の Ret から Idem⁺ への包含（HTT と一致）。結論：同じ写像が内アノダインである（一致）。

一つのレトラクション二単体から始めて、強いレトラクションの高次単体を補う。この比較が内アノダインであることが、任意の ∞ 圏を値域とする延長を保証する。

:::

:::corollary "htt_4_4_5_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_extension_exists")
*HTT 系 4.4.5.7*　弱い分裂図式の延長と制限の自明 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=323)）。対応表の状態：本体にある。

*主張*　∞ 圏 $`\mathcal C` への強レトラクション図式を弱図式へ制限する関手は自明ファイブレーションであり、任意の弱図式を強図式へ延長できる。

仮定：準圏 C（HTT と一致）。結論：同じ関手準圏間の制限は自明 Kan ファイブレーションで、任意の指定 Ret 図式を同じ制限で厳密に延長する（一致）。

弱図式を固定した延長についても、選択の空間が可縮である。これは対象ごとの延長だけでなく、図式の関手空間上の相対持ち上げから従う。

:::

:::lemma_ "htt_4_4_5_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex_innerAnodyne")
*HTT 補題 4.4.5.8*　指定面を含まない部分複体の内アノダイン性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=323)）。対応表の状態：本体にある。

*主張*　$`J\subseteq[ n ]` に含まれる二頂点の間に $`J` に属さない頂点があるとき、$`\Delta^J` を含まない単体で張る $`K\subseteq\Delta^n` の包含は内アノダインである。

仮定：J⊆\[n\] と i\<j\<k、i,k∈J、j∉J（HTT と一致）。結論：J 全体を含む単体を除いた同じ部分複体の包含は内アノダイン（一致）。

$`J` の間にある一つの飛ばした頂点を、欠けた単体を付け足すときの内側の頂点として使う。そのため外角の充填を要求せずに全体を得られる。

:::

:::lemma_ "htt_4_4_5_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemConeRetraction, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemConeRetraction_inl")
*HTT 補題 4.4.5.9*　冪等図式の添字の右錐からの収縮（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Idem}` の右錐 $`\mathrm{Idem}^{\triangleright}` への包含には、$`\mathrm{Idem}` を値域とする左逆がある。

仮定：Idem とその右錐（HTT と一致）。結論：元の包含への制限が恒等となる、同じ錐から Idem への射を与える（一致）。

錐点から元の一対象へ戻し、錐の新しい脚に冪等辺を使って整合性を作る。この選択が元の図式の上では恒等である。

:::

:::lemma_ "htt_4_4_5_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemShape_isWeaklyContractible")
*HTT 補題 4.4.5.10*　冪等図式の添字の弱可縮性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　$`\mathrm{Idem}` は弱可縮である。

仮定：Idem（HTT と一致）。結論：同じ単体集合は弱可縮（一致）。

錐の包含がレトラクションを持つことから、元の単体的集合の弱ホモトピー型は可縮な錐のレトラクトになる。

:::

:::lemma_ "htt_4_4_5_11" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion_isRightCofinal")
*HTT 補題 4.4.5.11*　冪等図式から強い分裂への包含の共終性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　包含 $`\mathrm{Idem}\hookrightarrow\mathrm{Idem}^+` は共終である。

仮定：Idem→Idem⁺ の同じ包含（HTT と一致）。結論：右共終、すなわち原典の共終写像である（一致）。

左側の一対象に制限して余極限を計算してよい。新しいレトラクション先についても、指定の比較のコンマ図式が共終性の条件を満たす。

:::

:::proposition "htt_4_4_5_12" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingCanonicalCocones_isColimit")
*HTT 命題 4.4.5.12*　強い分裂図式の左 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　強レトラクション図式 $`F:\mathrm{Idem}^+\to\mathcal C` は、$`\mathrm{Idem}` への制限の左 Kan 拡張である。

仮定：任意の準圏を値域とする Idem⁺ 上の全図式（HTT と一致）。結論：同じ Idem 包含に沿うすべての標準局所余錐が余極限となり、左 Kan 拡張である（一致）。

特に新しい対象の値は、冪等辺の指定する図式の余極限になる。その値を指定する射はレトラクションの射の一方である。

:::

:::proposition "htt_4_4_5_13" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingCanonicalCocones_isColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splitOppositeIso, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso_inclusion, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalConeOppositeIso_canonical, SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone")
*HTT 注意 4.4.5.13*　強い分裂図式の右 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　強レトラクション図式は $`\mathrm{Idem}` への制限の右 Kan 拡張でもある。

仮定：任意の準圏を値域とする Idem⁺ 上の全図式（HTT と一致）。結論：同じ二つの添字の反転同型は包含と可換し、標準左余錐の反転は標準右錐と等しい。反対準圏での左 Kan 判定から、元の全図式の全標準右錐の極限性を得る（一致）。

反対化でレトラクションの包含と射の役割を交換し、左 Kan 拡張の結果を使う。これにより同じ分裂対象が極限としても読める。

:::

:::corollary "htt_4_4_5_14" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasColimit, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasLimit")
*HTT 系 4.4.5.14*　冪等図式の分裂と極限と余極限（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=325)）。対応表の状態：本体にある。

*主張*　冪等子 $`F:\mathrm{Idem}\to\mathcal C` が強レトラクションへ延長できること、余極限を持つこと、極限を持つことは同値である。

仮定：準圏 C の指定 Idem 図式 F（HTT と一致）。結論：同じ F の厳密な強い分裂の存在、余極限の存在、極限の存在が互いに同値（一致）。

極限または余極限で得た対象には、冪等辺を分裂する普遍的な脚がある。逆に強レトラクション図式ならその追加対象を両方向の Kan 拡張として読める。

:::

:::corollary "htt_4_4_5_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasColimits, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasLimits")
*HTT 系 4.4.5.15*　冪等完備性の極限と余極限による判定（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=326)）。対応表の状態：本体にある。

*主張*　∞ 圏の冪等完備性は、すべての $`\mathrm{Idem}` 型図式が余極限を持つこと、またはすべてが極限を持つことと同値である。

仮定：準圏 C（HTT と一致）。結論：全 coherent 冪等図式の強い分裂の存在と、全 Idem 図式の余極限または極限の存在が互いに同値（一致）。

一つの冪等子についての分裂判定を全図式に適用する。ここで要求する極限・余極限の形は $`\mathrm{Idem}` に固定され、任意の小図式には及ばない。

:::

:::corollary "htt_4_4_5_16" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.effectiveSplittingRestriction_trivialKanFibration, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplittingRestriction_trivialKanFibration_of_complete, SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparisonRestriction_trivialKanFibration")
*HTT 系 4.4.5.16*　有効な冪等図式への制限の自明 Kan 性（[原典 PDF](https://www.math.ias.edu/~lurie/papers/HTT.pdf#page=326)）。対応表の状態：本体にある。

*主張*　強レトラクション図式の関手圏から有効な冪等子の充満部分圏への制限は自明 Kan ファイブレーションで、冪等完備な場合は弱図式および全冪等子への二つの制限がともに自明 Kan ファイブレーションになる。

仮定：準圏 C と、強い分裂を持つ有効な Idem 図式の充満部分圏（HTT と一致）。結論：Fun(Idem⁺,C) からその同じ部分圏への制限は自明 Kan。C が冪等完備なら Fun(Idem,C) への制限も自明 Kan で、Ret への制限と同じ二本を与える（一致）。

有効な冪等子は分裂を持つので、選択した分裂を忘れる写像のファイバーが可縮になる。冪等完備性があると、この制限の標的を冪等子全部に広げられる。

:::

