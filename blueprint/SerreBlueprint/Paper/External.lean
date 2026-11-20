-- audit2: 7d0968dad3e8672a6213dc0e508983c17f14eaaa inputs sha256 b3e2631992a041109ef8ab3a4836cc24453830556fb4a9c55f9a166f68e2cde1
-- audit2 baselines: 23cbebdfe9d75717f3f248bb0069ebd9dc9bbef6, cddf4d2dac6a409e64204686cf743e703350a6f6
import Verso
import VersoManual
import VersoBlueprint
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import SerrePositivity.AlgebraicGeometry.FiniteTypeFlatteningNoetherian
import SerrePositivity.AlgebraicGeometry.NoetherianFiniteModuleFlattening
import SerrePositivity.CategoryTheory.Karoubi.Triangulated
import SerrePositivity.CommutativeAlgebra.CohenGabber.Normalization
import SerrePositivity.CommutativeAlgebra.HenselianFinite
import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.FrobeniusGrowth
import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.General
import SerrePositivity.IntersectionMultiplicity.EqualCharZero.Positivity
import SerrePositivity.IntersectionMultiplicity.Vanishing
import SerrePositivity.LengthAlgebra.RootTowerLength.Additivity
import SerrePositivity.LengthAlgebra.RootTowerLength.Basic
import SerrePositivity.LengthAlgebra.RootTowerLength.Tower
import SerrePositivity.Paper.Section2.LengthAlgebra.EqualChar

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "引用した結果" =>
%%%
number := false
tag := "paper-external"
%%%

本論文が引用する外の文献の結果（`research/paper-coverage/external.csv`）。各本論文の項目から uses で張られる。CLMST の結果は CLMST の部のノード。BS19・K の文献の結果は、それぞれの対応表ができるまで状態を空にしてある。

:::proposition "ext_BGT_8_1"
*BGT 8.1*　小安定∞圏の局所化不変量を、Morita 同値・filtered colimit・完全列から余ファイバー列への保存によって定義する。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/bgt/items.csv; number=8.1（CSV行164）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_BGT_8_7"
*BGT 8.7*　局所化モチーフの安定表示可能∞圏と普遍局所化不変量 U\_loc を構成し、その普遍性を示す。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/bgt/items.csv; number=8.7（CSV行173）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_BGT_9_3"
*BGT 9.3*　§9.3 で Waldhausen 圏の非連結 K 理論と局所化を扱い、小安定∞圏の非連結 K 理論の局所化性を得る。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/bgt/items.csv; number=§9.3（CSV行202）。status・declarations はこの参照先から読む。本論文の 9.3 は節番号。式 (9.3) ではない。同表 number=§9.3 localization も局所化の証明段階として参照する。

:::

:::proposition "ext_BGT_9_8"
*BGT 9.8*　球スペクトルの完全加群圏の局所化モチーフからの写像スペクトルが非連結 K 理論を共表現する。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/bgt/items.csv; number=9.8（CSV行184）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_BS19_8_5"
*BS19 8.5*　perfectoidization を perfectoid 標的への写像の図式の導来極限で記述し、始域の π0 のみに依存することを示す。。状態はその文献の対応表を参照。

正本: research/bs-coverage/items.csv; number=8.5（CSV行128）。status・declarations はこの参照先から読む。本論文の版は arXiv:1905.08229v4、正本は著者版。正本の title\_ja・note と版の対応も読み、同番号だけを根拠に版を同一視しない。

:::

:::proposition "ext_BalmerSchlichting_1_10" (lean := "SerrePositivity.karoubiDistinguished")
*BalmerSchlichting 1.10*　三角圏 K の冪等完備化で、K の完全三角形の像の直和因子として得られる三角形を完全三角形と定義する。。対応表の状態：本体にある。

原典の direct factor を三角形の Retract で表した同じ定義。一般の三角圏を扱い、複体上の射影の lift を追加仮定しない。 原典・使用主張の確認: https://webhomes.maths.ed.ac.uk/\~v1ranick/papers/balmschl.pdf; Definition 1.10, printed p.823 (PDF p.5)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_BalmerSchlichting_1_12" (lean := "SerrePositivity.karoubiIsTriangulated")
*BalmerSchlichting 1.12*　Definition 1.10 の完全三角形の類により、三角圏の冪等完備化は三角圏となる。。対応表の状態：本体にある。

同じ Karoubi 完備化の前三角構造に八面体公理を供給する instance。一般の三角圏を扱う。この定理は関手延長の一意性まで要求しないので、その未実装を定理の不足とはしない。 原典・使用主張の確認: https://webhomes.maths.ed.ac.uk/\~v1ranick/papers/balmschl.pdf; Theorem 1.12, printed p.823 (PDF p.5)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Drinfeld_3_1"
*Drinfeld 3.1*　全 dg 部分圏の各対象の恒等射を微分にもつ次数 −1 の射を自由に付加して dg 商を構成する。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=§3.1; reference=Drinfeld（CSV行35）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_Drinfeld_3_4"
*Drinfeld 3.4*　Hom 複体についての適切な homotopical flatness の下で、dg 商の前三角包のホモトピー圏は元の前三角包の Verdier 商と同値になる。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=3.4; reference=Drinfeld（CSV行36）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_Faltings_Appendix_2" (lean := "SerrePositivity.Section2.towerLengthFun, SerrePositivity.Section2.towerLengthFun_tensor, SerrePositivity.Section2.towerLengthFun_add_of_exact_of_noetherian")
*Faltings Appendix 2*　根を付加する塔などの設定で、有限表示加群の段長さの正規化を一般加群へ拡張する正規化長さを構成し、短完全列の加法性・almost 同型に関する不変性などを示す。。対応表の状態：一部。

原典付録の toroidal な設定全般ではなく、本論文が CLMST の形で使う正則パラメータの根の塔で、三段階の長さ・有限段公式・加法性を確認。原典の一般 toroidal 基底と全 almost 不変性を含む付録全体の対応ではない。 原典・使用主張の確認: https://numdam.org/item/AST\_2002\_\_279\_\_185\_0.pdf; Appendix 2: opening p.200 and Lemma 7 (additivity), pp.202–203。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_GilletSoule" (lean := "SerrePositivity.intersectionVanishing_of_adams")
*GilletSoule*　本論文が用いる消滅：正則局所環 R と有限生成 M,N について、M⊗\_R N が有限長で dim M+dim N\<dim R なら χ\_R(M,N)=0。。対応表の状態：本体にある。

採用宣言は全剰余標数の正則局所環・有限加群について同じ次元条件と結論を持つ。二乗と三乗の巡回 Adams 作用素で証明する。文献全体の全 perfect complex・全 Adams 理論ではなく、本論文 (5.1) が引用する消滅主張に対する判定。 原著本文は購読画面までで未採取。使用主張は本論文 p.23 とソースの型で確認し、書誌は出版社ページで確認した。 原典・使用主張の確認: https://link.springer.com/article/10.1007/BF01388705; publisher metadata; Paper p.23 Equation (5.1)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Goodwillie_Main_Theorem"
*Goodwillie Main Theorem*　単体結合環の射 f が π0 で全射かつ冪零核を持つなら、相対群に有理同型 K\_n(f)⊗Q ≅ HC\_(n−1)(f)⊗Q がある。。対応表の状態：なし。

相対 K 理論と巡回ホモロジーを結ぶ Goodwillie–Jones 比較射と、この冪零核条件下での同値を確認できない。既存 others.csv の reference=Goodwillie, number=Introduction 0.1 も同じ対象だが、今回の単発文献の検索・型照合として判定を記録する。 原典・使用主張の確認: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/goodwillie-cyclic.pdf; Introduction 0.1, Main Theorem, printed p.348 (PDF p.3)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Jannsen_A_4_1"
*Jannsen A.4(1)*　整な正則 Noether スキーム X の、X と異なる整な正則閉部分スキーム Z でのブローアップは再び整・正則で dim X を保ち、例外因子も整・正則である。。対応表の状態：なし。

一般の正則スキームと正則中心に対するブローアップ全体および例外因子の正則性を述べる宣言は未確認。KST の regular sequence・チャートの同型や許容中心の構成だけではこの結論にならない。 原典・使用主張の確認: https://annals.math.princeton.edu/wp-content/uploads/annals-v172-n3-p03-p.pdf; Appendix A, Proposition A.4(1), printed p.1633 (PDF p.42)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_KuranoShimomoto" (lean := "SerrePositivity.exists_cohen_gabber_normalization")
*KuranoShimomoto*　等標数 p の完備局所環 A について、剰余写像を分裂する係数体とパラメータを選び、冪級数環から有限な正規化を得る。次元 d の各極小素イデアルで分数体拡大を分離的にできる。。対応表の状態：一部。

任意剰余体・次元零を含む完備 Noether 局所整域で、同じ剰余体の冪級数基底・有限性・単射性・分数体の分離性を返す。原典は非整域も許し、次元最大の各極小素イデアルを同時に扱うため、整域への特殊化として partial。 番号なしの文献引用と、参考文献欄が同定する Theorem 1.1 の辺を、それぞれ独立した辺先の行として残す。 原典・使用主張の確認: https://arxiv.org/pdf/1510.03573v2; Theorem 1.1, PDF p.1; Paper bibliography \[17\]。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_KuranoShimomoto_1_1" (lean := "SerrePositivity.exists_cohen_gabber_normalization")
*KuranoShimomoto 1.1*　等標数 p の完備局所環 A について、剰余写像を分裂する係数体とパラメータを選び、冪級数環から有限な正規化を得る。次元 d の各極小素イデアルで分数体拡大を分離的にできる。。対応表の状態：一部。

任意剰余体・次元零を含む完備 Noether 局所整域で、同じ剰余体の冪級数基底・有限性・単射性・分数体の分離性を返す。原典は非整域も許し、次元最大の各極小素イデアルを同時に扱うため、整域への特殊化として partial。 原典・使用主張の確認: https://arxiv.org/pdf/1510.03573v2; Theorem 1.1, PDF p.1。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_LT_3_10"
*LT 3.10*　Goodwillie の単体環についての比較を、連結な結合的環スペクトルへ移す帰着を説明する。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=3.10（CSV行101）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_3_12"
*LT 3.12*　任意の E 線形小安定∞圏 D に対し、相対テンソル積 −⊗\_E D は完全列を保存する。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=3.12（CSV行103）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_3_9"
*LT 3.9*　有理 Goodwillie–Jones Chern character のファイバーである有理無限小 K 理論は切除を満たす。証明ではこの不変量が truncating であることを示す。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=3.9（CSV行99）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_A_2"
*LT A.2*　truncating 局所化不変量は qcqs スキーム上で cdh 降下を満たし、抽象ブローアップ正方形を引き戻しへ送る。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=A.2（CSV行118）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_Appendix_B"
*LT Appendix B*　準連接な連結係数代数の層を持つ場合へ truncating 不変量の cdh 降下を拡張する付録。個別のテンソル表示と降下は B.2・B.3。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=§B（CSV行127）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_B_2"
*LT B.2*　qcqs 基底 S 上で、係数代数の引き戻し R\_X の QCoh と Perf は、それぞれ QCoh(S)・Perf(S) 上の相対テンソル積で表される。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=B.2（CSV行132）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_LT_B_3"
*LT B.3*　Perf(S) 線形∞圏の truncating 不変量 E と連結係数 R に対し、係数付き E(−;R) は cdh 降下を満たす。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/land-tamme/items.csv; number=B.3（CSV行133）。status・declarations はこの参照先から読む。

:::

:::proposition "ext_Ma17_2_2" (lean := "SerrePositivity.exists_complete_flat_local_extension_of_residueField")
*Ma17 2.2*　補題2.2は、平坦局所写像に対する Lech 型不等式を等次元・両環完備・基底が整域・拡大側の剰余体が代数閉の場合へ帰着する。別の引用箇所の §2.2 は Hilbert–Kunz 重複度と Frobenius 極限の解説。。対応表の状態：一部。

剰余体の任意拡大を、極大イデアルを保つ完備 Noether 平坦局所拡大で実現する部分を確認。補題全体の Lech 不等式の帰着と §2.2 の一般 Hilbert–Kunz 理論を一括で形式化したものではない。同じ辺先キーが Lemma 2.2（本論文 p.5）と Section 2.2（p.8）を兼ねるため、この一行で両方を明示する。 原典・使用主張の確認: https://arxiv.org/pdf/1609.00095v3; Lemma 2.2 and proof, PDF pp.3–4; Section 2.2。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Ma17_2_4" (lean := "SerrePositivity.tendsto_length_koszulHomologySelf_frobenius_pow")
*Ma17 2.4*　標数 p の完備局所環の、長さが環次元 d の有限自由複体で全ホモロジーが有限長なら、正次数 Frobenius ホモロジー長を p\^(ed) で割った値は零へ収束する。。対応表の状態：一部。

採用宣言は完全剰余体を持つ完備局所環のパラメータ Koszul 複体の場合。任意の有限自由複体・任意剰余体の一般定理には達していない。FrobeniusKoszulLimit の hRoberts は一般消滅を仮定して使う補助であり、一般定理の証明としては採用しない。 原典・使用主張の確認: https://arxiv.org/pdf/1609.00095v3; Theorem 2.4, PDF p.6。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Monsky" (lean := "SerrePositivity.Section2.normalized_frobenius_length_tendsto_perfection_quotient_of_primary")
*Monsky*　正標数 Noether 局所環、m 準素イデアル I と有限生成加群について、Frobenius 冪商の長さを p\^(ed) で正規化した Hilbert–Kunz 極限が存在する。。対応表の状態：一部。

完全剰余体と有限な正則正規化基底・生成的分離性を持つ正標数局所整域、正次元、加群 D 自身の場合に、m 準素 H の正規化 Frobenius 商長の極限を具体的な perfection 商長として示す。一般の局所環・有限加群の存在定理への一般化はしていない。原著は表紙・導入までの取得で、使用する存在主張は本論文 p.8 と Ma17 §2.2 で確認。 原典・使用主張の確認: https://gdz.sub.uni-goettingen.de/fulltext/PPN235181684\_0263/00000047?\_format=xml; 1983 paper introduction; Paper p.8; Ma17 Section 2.2。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Roberts85" (lean := "SerrePositivity.intersectionVanishing_of_adams")
*Roberts85*　本論文が用いる消滅：正則局所環 R と有限生成 M,N について、M⊗\_R N が有限長で dim M+dim N\<dim R なら χ\_R(M,N)=0。。対応表の状態：本体にある。

採用宣言は全剰余標数の正則局所環・有限加群について同じ次元条件と結論を持つ。二乗と三乗の巡回 Adams 作用素で証明する。文献全体の全 perfect complex・全 Adams 理論ではなく、本論文 (5.1) が引用する消滅主張に対する判定。 AMS 原著 PDF は取得時 403。使用主張は本論文 p.23 とソースの型で確認し、書誌は著者の刊行物一覧 no.11 で確認した。 原典・使用主張の確認: https://www2.math.utah.edu/\~roberts/publications.html; no.11; Paper p.23 Equation (5.1)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Roberts89" (lean := "SerrePositivity.tendsto_length_koszulHomologySelf_frobenius_pow")
*Roberts89*　標数 p の完備局所環の、長さが環次元 d の有限自由複体で全ホモロジーが有限長なら、正次数 Frobenius ホモロジー長を p\^(ed) で割った値は零へ収束する。。対応表の状態：一部。

採用宣言は完全剰余体を持つ完備局所環のパラメータ Koszul 複体の場合。任意の有限自由複体・任意剰余体の一般定理には達していない。FrobeniusKoszulLimit の hRoberts は一般消滅を仮定して使う補助であり、一般定理の証明としては採用しない。 原著章の本文は今回採取できず、同じ結果を再掲する Ma17 Theorem 2.4 と本論文 p.8 の引用で対象を同定した。章全体の対応を主張しない。 原典・使用主張の確認: https://www2.math.utah.edu/\~roberts/publications.html; author publication list no.19; statement restated in Ma17 Theorem 2.4。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Serre" (lean := "SerrePositivity.chi_pos_of_residueCharZero")
*Serre*　本論文が用いる等標数の正値性：正則局所環と有限生成 M,N でテンソルが有限長、dim M+dim N=dim R なら χ\_R(M,N)\>0。。対応表の状態：一部。

採用宣言は剰余標数零の場合で、完備化を仮定せず有限加群の正値性を示す。文献の等標数 p の場合を含めた等標数全体の対応ではない。本論文の主定理を戻して循環的にこの外部引用の証明とはしない。使用主張は本論文 p.23、書誌は Springer Local Algebra 2000。 原典・使用主張の確認: https://link.springer.com/book/10.1007/978-3-662-04203-8; Chapter V; Paper p.23 Lemma 5.1 proof。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Skalit15_3_10"
*Skalit15 3.10*　非分岐の設定で χ=e(A/P)e(A/Q) かつ π をさらに剰余した associated graded テンソルの次元が零なら、元のテンソルも次元零。本論文は証明中の有限支持の場合の局所交点数の総和表示も使う。。対応表の状態：なし。

命題の条件付き次元零の結論、および証明にある有限支持 Tor 層の大域 Euler 数と局所交点数の重み付き和の同定は未確認。本論文による証明部分の引用と命題本体を区別する。 原典・使用主張の確認: https://arxiv.org/pdf/1409.3616v2; Proposition 3.10 and proof, PDF p.21。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Skalit15_3_4"
*Skalit15 3.4*　正則局所環で余次元が補い合い閉点で交わる素閉部分スキームについて、χ\_A(A/P,A/Q)=e(A/P)e(A/Q)+χ\_\{Bl X\}(O\_\{Bl Y\},O\_\{Bl Z\}) というブローアップ公式。。対応表の状態：なし。

交点重複度と狭義変換上の大域 Tor コホモロジーの Euler 数を結ぶ同じ公式の宣言は未確認。一般のブローアップ・チャート・Euler 加法性だけを代用しない。 原典・使用主張の確認: https://arxiv.org/pdf/1409.3616v2; Theorem 3.4, PDF pp.18–19。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Skalit15_3_5"
*Skalit15 3.5*　閉点で交わる状況の閉部分スキーム Y,Z の狭義変換の交わりの被約化は Proj(gr(A/a)⊗\_\{gr A\}gr(A/b)) の被約化と同型で、空であることは後者の次数環の次元零に対応する。。対応表の状態：なし。

狭義変換と associated graded の Proj を結ぶ被約スキーム同型・空性の判定を同時に持つ宣言は未確認。 原典・使用主張の確認: https://arxiv.org/pdf/1409.3616v2; Lemma 3.5, PDF p.19。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Skalit15_3_8"
*Skalit15 3.8*　形式的等次元かつ普遍的鎖状な局所環 A の閉点でのブローアップでは、任意の閉点 x で dim O\_\{Bl X,x\}=dim A。。対応表の状態：なし。

指定された一般の局所環・ブローアップの閉点での次元等式を述べる宣言は未確認。射影チャートや有限型代数の一般次元補題はこの同定を供給しない。 原典・使用主張の確認: https://arxiv.org/pdf/1409.3616v2; Lemma 3.8, PDF p.20。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Stacks_03QH" (lean := "SerrePositivity.isLocalRing_finite_domain_of_complete")
*Stacks 03QH*　局所環の Hensel 性は、任意の有限代数が有限な局所代数の有限積に分かれることなどと同値である。。対応表の状態：一部。

本体では完備 Noether 局所環上の有限な整域が局所環であるという使用時の特殊な場合を証明。任意の Hensel 局所環・有限代数の積分解、および全条件の同値までの宣言ではない。 原典・使用主張の確認: https://stacks.math.columbia.edu/tag/03QH; Theorem 59.32.4, especially condition (3)。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Stacks_0815" (lean := "SerrePositivity.AlgebraicGeometry.exists_noetherian_finite_flattening_center, SerrePositivity.AlgebraicGeometry.exists_admissible_flat_strictTransformπ_of_finiteType")
*Stacks 0815*　qcqs 基底 S 上の準コンパクト・局所有限表示な X と有限型準連接加群 F が準コンパクト開 U 上で有限表示・平坦なら、U 許容ブローアップ後の狭義変換を有限表示・平坦にできる。。対応表の状態：一部。

Noether アフィン基底上の有限加群・正則主開境界での純変換の平坦化と、Noether 基底上の有限型射の構造層の平坦化を確認。原典の非 Noether qcqs 基底・任意の有限型準連接 F とその有限表示性全体は含まない。 原典・使用主張の確認: https://stacks.math.columbia.edu/tag/0815; Theorem 38.30.7。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Stacks_0BRI" (lean := "Algebra.IsInvariant.exists_smul_of_under_eq")
*Stacks 0BRI*　有限群 G が可換環 R に作用するとき、不変環 R\^G の同じ素イデアル上にある R の二つの素イデアルは G で共役である。。対応表の状態：Mathlib にある。

任意の有限群、可換環、同じ contraction を持つ素イデアルについて同じ推移性を持つ。Algebra.IsInvariant の基底 A に R\^G を選べば原典になる。有限な基底加群や分離性は追加しない。 原典・使用主張の確認: https://stacks.math.columbia.edu/tag/0BRI; Lemma 15.112.8。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_Stacks_0BRJ" (lean := "Ideal.IsFractionRing.normal, IsFractionRing.stabilizerHom_surjective")
*Stacks 0BRJ*　有限群作用の不変環の素イデアル p 上の q について、κ(q)/κ(p) は代数的正規拡大で、q の分解群からその自己同型群への写像は全射である。。対応表の状態：Mathlib にある。

κ(q),κ(p) を R/q と R\^G/p の分数体として扱う一般形の正規性・安定化群写像の全射性を確認。極大イデアルや剰余体拡大の分離性に狭めた版ではない。 原典・使用主張の確認: https://stacks.math.columbia.edu/tag/0BRJ; Lemma 15.112.9。ソースの静的照合のみで kernel 検査は再実行していない。

:::

:::proposition "ext_TT_5_2_2"
*TT 5.2.2*　開部分への完全複体の延長には K0 の障害があり、障害が消える対象は延長できる。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=5.1 \| 5.2.2 \| 5.2.3 \| 5.2.4; reference=Thomason–Trobaugh（CSV行15）。status・declarations はこの参照先から読む。同表のまとめ行 number=5.2.2 \| 5.2.3 \| 5.2.4 \| 7.4 も参照。

:::

:::proposition "ext_TT_5_2_3"
*TT 5.2.3*　開部分上の完全複体間の射を、源を開上で準同型同値な完全複体に置き換えて持ち上げる。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=5.1 \| 5.2.2 \| 5.2.3 \| 5.2.4; reference=Thomason–Trobaugh（CSV行15）。status・declarations はこの参照先から読む。同表のまとめ行 number=5.2.2 \| 5.2.3 \| 5.2.4 \| 7.4 も参照。

:::

:::proposition "ext_TT_5_2_4"
*TT 5.2.4*　開部分で零になる射を、開上の準同型同値を源へ前合成することによって零にできる。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=5.1 \| 5.2.2 \| 5.2.3 \| 5.2.4; reference=Thomason–Trobaugh（CSV行15）。status・declarations はこの参照先から読む。同表のまとめ行 number=5.2.2 \| 5.2.3 \| 5.2.4 \| 7.4 も参照。

:::

:::proposition "ext_TT_7_4"
*TT 7.4*　qcqs スキームとその準コンパクト開部分について、台付き非連結 K 理論は K(X)→K(U) のホモトピーファイバーを与える。。状態はその文献の対応表を参照。

正本: research/k-coverage/maps/others.csv; number=7.4; reference=Thomason–Trobaugh（CSV行16）。status・declarations はこの参照先から読む。同表のまとめ行 number=5.2.2 \| 5.2.3 \| 5.2.4 \| 7.4 も参照。

:::

