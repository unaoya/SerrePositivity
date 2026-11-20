-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Algebra.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import SerrePositivity.AlgebraicGeometry.AffineBaseVCoverRefinement
import SerrePositivity.AlgebraicGeometry.CompactMinimalPrimeVCoverRefinement
import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatteningNoetherian
import SerrePositivity.AlgebraicGeometry.GenericFlatness
import SerrePositivity.AlgebraicGeometry.NoetherianVCoverRefinement
import SerrePositivity.AlgebraicGeometry.SchemeBlowup
import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway
import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper
import SerrePositivity.AlgebraicGeometry.SchemeVCoverFlatSurjective
import SerrePositivity.AlgebraicGeometry.SchemeVCoverProper
import SerrePositivity.AlgebraicGeometry.SchemeVCoverSpecializations
import SerrePositivity.AlgebraicGeometry.StrictTransform
import SerrePositivity.AlgebraicGeometry.VCoverClosedRestrictionSpecializations
import SerrePositivity.AlgebraicGeometry.ValuativeFppfBlowupRefinement
import SerrePositivity.AlgebraicGeometry.ValuativeOpenImageGenerizations
import SerrePositivity.AlgebraicGeometry.ValuativeStrictTransformSurjective
import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "Rydh（Submersions and effective descent of étale morphisms, arXiv 0710.2488v3）" =>
%%%
number := false
tag := "vdescent-rydh"
%%%

Rydh の項目のうち、この経路で本体か Mathlib に対応があるもの。

# §1 Topologies

%%%
number := false
tag := "vdescent-rydh-1"
%%%

:::proposition "rydh_1_3" (lean := "PrimeSpectrum.le_iff_specializes")
*Rydh 注意 1.3*　素スペクトルの特殊化順序。対応表の状態：Mathlib にある。

*主張*　アフィンスキームの点を、特殊化した点が小さくなるように順序づけると、素イデアルの包含の逆順になる。このため極大点は極小素イデアルに対応する。

原典 PDF p.5, y=347.8。素イデアルの包含順序と specializes の同値。原典の点の ≤ は Lean の specializes の向きと逆で、極大な点は極小素イデアルになる。

:::

# §2 Subtrusive morphisms

%%%
number := false
tag := "vdescent-rydh-2"
%%%

:::proposition "rydh_2_1" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover.liftsSpecializations, SerrePositivity.AlgebraicGeometry.closure_subset_range_comp_of_vCover_closedRestriction") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1")
*Rydh 命題 2.1*　特殊化の持ち上げと同値な条件。対応表の状態：一部（component）。

*主張*　スキームの射 $`f\colon X\to Y` について、$`Y` のすべての特殊化の組が $`X` の特殊化の組に持ち上がる条件は、特殊化閉包 $`S` を用いた $`f(S(f^{-1}(Z)))=S(Z)` が一点集合について成り立つ条件とも、任意の部分集合 $`Z` について成り立つ条件とも同値である。また任意のプロ構成可能部分集合 $`Z` に対して $`f(\overline{f^{-1}(Z)})=Z` が成り立つこととも同値で、これらの条件の下では $`f` は特殊化位相で商写像となる。

原典 PDF p.7, y=480.6。付値持ち上げ条件のもとで (i) の点対の持ち上げと閉制限に対する閉包の包含を与える。(i)–(iv) の一般の同値は扱わない。

:::

:::definition "rydh_2_2" (lean := "SerrePositivity.AlgebraicGeometry.IsSchemeVCover.liftsSpecializations") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1")
*Rydh 定義 2.2*　S-subtrusive と subtrusive。対応表の状態：一部（component）。

*主張*　特殊化の組の持ち上げ条件を満たすスキームの射を $`S`-subtrusive と呼び、さらに構成可能位相で商写像となる射を subtrusive と呼ぶ。任意の底変換で subtrusive であれば普遍的 subtrusive である。

原典 PDF p.7, y=686.8。付値持ち上げの仮定から S-subtrusive の点対条件を与える。構成可能位相での商写像というもう一方の条件はこの型にない。

:::

:::proposition "rydh_2_5" (lean := "SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_proper_surjective, SerrePositivity.AlgebraicGeometry.isSchemeVCover_of_flat_surjective") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_2_6")
*Rydh 注意 2.5*　普遍 subtrusive 射の例。対応表の状態：一部（component）。

*主張*　スキームの全射は、任意の底変換で特殊化位相について閉写像、または任意の底変換で同位相について開写像で、かつ構成可能位相で普遍的な商写像となる場合に、普遍的 subtrusive である。前者の例は固有・整・本質的に固有な全射、後者の例は fpqc・fppf・普遍的開な全射である。

原典 PDF p.8, y=511.4。固有全射および平坦全射から付値による普遍 subtrusive の判定条件を得る。他の十分条件と反例は含まない。

外の文献：egaIV

:::

:::proposition "rydh_2_6" (lean := "IsBezout, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Module.isTorsionFree_iff_algebraMap_injective")
*Rydh 注意 2.6*　付値環での主イデアル性と平坦性。対応表の状態：Mathlib にある。

*主張*　付値環の有限生成イデアルは単項であり、その上の加群が平坦であることと無ねじれであることは同値である。特に整域である付値環上の代数は、構造射が単射であるとき、かつそのときに限り平坦である。

原典 PDF p.9, y=119.0。付値環には IsBezout のインスタンスがあり、有限生成イデアルは単項となる。平坦性は torsion 部分加群が零であることと同値で、整域への代数構造では構造射の単射性と同値になる。

外の文献：bourbaki\_alg\_comm\_5\_6

:::

# §3 Structure theorem for finitely presented subtrusions

%%%
number := false
tag := "vdescent-rydh-3"
%%%

:::lemma_ "rydh_3_2" (lean := "SerrePositivity.AlgebraicGeometry.surjective_openImage_of_vCover_affine_of_contains_minimalPrimes") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_1_3, rydh_2_1, rydh_2_2")
*Rydh 補題 3.2*　一般点を含む集合からの全射性。対応表の状態：一部（special）。

*主張*　$`S`-subtrusive 射 $`f\colon X\to Y` と、$`Y` のすべての極大点を含む部分集合 $`U` に対し、$`f^{-1}(U)` の Zariski 閉包に制限した $`f` は全射である。

原典 PDF p.12, y=216.6。アフィン基底のすべての極小素点を含む開集合の逆像の閉包からの全射性を得る。任意の部分集合や一般の S-subtrusive 射の範囲は含まない。

:::

:::definition "rydh_3_3" (lean := "SerrePositivity.AlgebraicGeometry.blowup, SerrePositivity.AlgebraicGeometry.blowupπ, SerrePositivity.AlgebraicGeometry.blowupπ_isProper, SerrePositivity.AlgebraicGeometry.blowupπ_restrict_complement_isIso, SerrePositivity.AlgebraicGeometry.strictTransform, SerrePositivity.AlgebraicGeometry.strictTransformπ")
*Rydh 定義 3.3*　爆発と狭義変換。対応表の状態：一部（component）。

*主張*　有限生成イデアル層で定まる閉部分スキームを中心にとった爆発は固有で、中心の補集合で同型である。この爆発に関する $`X\to S` の狭義変換は、中心の外にある $`X` の部分の底変換のスキーム論的閉包を取り、そこから爆発後の底へ射影して得る。

原典 PDF p.12, y=298.8。有限生成中心の爆発の固有性、中心の補集合上の同型、選んだ開の逆像のスキーム論的閉包による狭義変換を与える。原典は開を中心の補集合に固定し、その準コンパクト性も述べる。

外の文献：Stacks 081T

:::

:::proposition "rydh_3_4" (lean := "SerrePositivity.AlgebraicGeometry.strictTransformπ_surjective_of_vCover") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_2_1, rydh_2_2, rydh_3_3")
*Rydh 注意 3.4*　狭義変換の全射性。対応表の状態：一部（special）。

*主張*　普遍的 subtrusive な射 $`X\to Y` は、$`Y` の爆発に関する狭義変換をとると、爆発後の底に全射する。

原典 PDF p.12, y=403.4。Noether 基底・コンパクトな有限型の v 被覆・稠密開を入力とし、爆発の狭義変換が全射になる。一般の基底での結論は含まない。

外の文献：lazard\_autour、olivier\_sem\_samuel

:::

:::lemma_ "rydh_3_5" (lean := "SerrePositivity.AlgebraicGeometry.exists_dense_open_flat_restrict_of_compactSpace")
*Rydh 補題 3.5*　準コンパクト稠密開上の平坦性。対応表の状態：一部（special）。

*主張*　被約 qcqs スキーム $`Y` の極大点の集合が準コンパクトなら、任意の有限表示射 $`X\to Y` は $`Y` のある稠密な準コンパクト開集合上で平坦になる。

原典 PDF p.12, y=507.0。被約 Noether アフィン基底で準コンパクトな始域なら稠密平坦開を得る。Noether 基底では開は準コンパクト。原典の一般点集合の準コンパクト性だけを仮定する基底には拡張していない。

外の文献：egaIV

:::

:::proposition "rydh_3_6" (lean := "SerrePositivity.AlgebraicGeometry.exists_dense_open_flat_restrict_of_compactSpace, SerrePositivity.AlgebraicGeometry.exists_admissible_flat_strictTransformπ_of_finiteType, SerrePositivity.AlgebraicGeometry.strictTransformπ_surjective_of_vCover, SerrePositivity.AlgebraicGeometry.exists_fppf_blowup_refinement_of_flat_strictTransform_vCover") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_2_1, rydh_2_2, rydh_3_3")
*Rydh 命題 3.6*　爆発による狭義変換の平坦化。対応表の状態：一部（special）。

*主張*　$`Y` を極大点の集合が準コンパクトな被約 qcqs スキームとし、$`X\to Y` を有限表示な普遍的 subtrusive 射とする。$`Y` の全射な有限型爆発であって、この射の狭義変換が有限表示かつ忠実平坦になるものが存在する。

原典 PDF p.12, y=611.8。被約 Noether アフィン基底では、稠密平坦開上での平坦化からその補集合を中心とする全射な爆発を得る。狭義変換は平坦かつ全射であり、Noether 基底上の有限型性から有限表示。一般点集合の準コンパクト性だけを仮定する基底は含まない。

外の文献：RG71、Stacks 081T

:::

:::proposition "rydh_3_7" (lean := "SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineReduced_compact_minimalPrimes") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, rydh_2_1, rydh_3_3, rydh_3_6")
*Rydh 命題 3.7*　一般点集合が準コンパクトな基底での細分。対応表の状態：一部（special）。

*主張*　$`Y` がアフィンで極大点の集合が準コンパクトなら、有限表示な普遍的 subtrusive 射 $`X\to Y` は有限表示な忠実平坦射と有限表示な固有全射との合成へ細分できる。元の射が普遍的開なら、細分の源から $`X\times_Y Y'` への射を冪零閉埋め込みに選べる。ここで $`Y'\to Y` は固有全射の部分である。

原典 PDF p.13, y=119.0。被約アフィン基底で極小素点集合が準コンパクト、始域もアフィンのときに fppf–proper 細分を与える。一般の始域・非被約基底および普遍開の場合の nilimmersion の追加結論は含まない。

外の文献：RG71、egaIV

:::

:::theorem "rydh_3_10" (lean := "SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineBase, SerrePositivity.AlgebraicGeometry.exists_fppf_proper_refinement_vCover_affineNoetherian") (uses := "bm18_eq_1, bm18_1_1, bs17_2_1, bs17_2_3, rydh_1_3, rydh_2_1, rydh_3_3, rydh_3_5, rydh_3_6")
*Rydh 定理 3.10*　アフィンまたは Noether 基底の fppf–固有細分。対応表の状態：一部（special）。

*主張*　$`Y` がアフィンまたはネーターなら、有限表示な普遍的 subtrusive 射 $`X\to Y` は有限表示な忠実平坦射と有限表示な固有全射との合成へ細分できる。元の射が普遍的開なら、細分の源から $`X\times_Y Y'` への射を冪零閉埋め込みに選べる。ここで $`Y'\to Y` は固有全射の部分である。

原典 PDF p.14, y=428.8。任意のアフィン基底で、始域のアフィン性や基底の Noether 性を要求せず fppf–proper 細分を与える。一般の非アフィン Noether 基底と、元の射が普遍開の場合の nilimmersion の追加結論は含まない。

外の文献：egaIV

:::

# §A Étale morphisms and henselian pairs

%%%
number := false
tag := "vdescent-rydh-A"
%%%

:::proposition "rydh_A_2" (lean := "AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal")
*Rydh 命題 A.2*　対角・切断・普遍単射での開埋め込み。対応表の状態：一部（component）。

*主張*　代数空間のエタール射の対角射および任意の切断は開埋め込みである。その射が普遍的単射なら、射自体が開埋め込みである。

原典 PDF p.35, y=119.0。エタール射は局所有限型かつ形式的不分岐なので、スキームの場合には (i) の対角射が開埋め込みになり、底変換で (ii) の切断も開埋め込みになる。代数空間の一般性を含まない。

:::

# §B Absolute weak normalization

%%%
number := false
tag := "vdescent-rydh-B"
%%%

:::definition "rydh_B_1" (lean := "SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_bijective_of_perfect_reduced") (uses := "rydh_B_3")
*Rydh 定義 B.1*　絶対弱正規と絶対弱正規化。対応表の状態：一部（special）。

*主張*　スキームまたは代数空間 $`X` が絶対弱正規であるとは、$`X` が被約で、被約空間から $`X` への分離的な普遍的同相射がすべて同型であることをいう。絶対弱正規な空間から $`X` への分離的な普遍的同相射は、$`X` の絶対弱正規化と呼ばれる。

原典 PDF p.38, y=237.6。完全標数 p の環 A と被約環 B に対するアフィン普遍同相では環準同型が全単射になる。絶対弱正規性の判定のアフィン完全環の場合で、一般の被約スキーム・代数空間の定義や正規化の構成までは含まない。

:::

:::definition "rydh_B_3" (lean := "SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism")
*Rydh 定義 B.3*　弱 subintegral 拡大とその閉包。対応表の状態：一部（component）。

*主張*　環の包含 $`A\subseteq A'` でスペクトルの射が普遍的同相となるものを弱 subintegral 拡大と呼び、$`B` 内の $`A` の弱 subintegral 閉包をそのような最大の中間環と定める。環の絶対弱正規性と絶対弱正規化は、スペクトルに対する同じ概念で定める。

原典 PDF p.38, y=558.9。環射の整性・素点での全単射性・剰余体の純非分離性により Spec の普遍同相を表す。単射を入力にすれば weakly subintegral な拡大の条件に対応する。最大のそのような部分拡大の構成は含まない。

外の文献：egaIV

:::

