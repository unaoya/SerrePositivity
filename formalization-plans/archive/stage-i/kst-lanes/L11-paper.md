# K-L11：紙の検証と K0 の型草案

## 現在地

検証対象は KST 経路 §10 の 1〜14 と §13-5 の K0 界面。検証順は
1 → 3 → 2 → 4 → 7 → 8 → 9 → 10 → 5 → 6 → 11 → 12 → 13 → 14 → 型草案。
各項目は原典の版・番号・頁、証明再構成、Lean の必要補題、未確認点を区別する。
Lean ソースは変更しない。π_n は K-L9、H_* は K-L2、pro 形式は K-L6 の所有とする。

正本：[KST 経路](k-theory-kst-route.md)、[基盤計画](../infinity-lanes/foundations.md)。
完成判定は検証記録と型草案の完成であり、そこに列挙する数学的補題の Lean 実装完了ではない。

| 項目 | 現在の判定 | 主な未確認点／条件 |
| --- | --- | --- |
| 1 | 非可換行列計算と証明経路を確定 | Appendix A の鎖補題は L2 の証明義務 |
| 3 | 可換版の再構成完了 | 係数版では Koszul pro 消滅を明示 |
| 2 | dg 半自由置換を確定 | 単体模型との比較は5に分離 |
| 4 | BK 原文と simple 版の証明を確認 | R-completion 塔の補題を実装する |
| 7 | 正しい降下模型と MV 経路を確定 | 高次整合性を省略しない |
| 8 | 射影空間による代替証明を確定 | Thomason 全文の直接照合は未確認 |
| 9 | ℕ² の対角代替を確定 | 全 m の一様指数は不要 |
| 10 | F5 の平坦性の証明を確定 | Chase 原典の個別頁は未確認 |
| 5 | 原典と補正・実装義務を記載 | ∞版のセル比較は未確認 |
| 6 | dg 完全列と分裂の別義務を確定 | pairing と境界の整合が必要 |
| 11 | ∞加法性の原典と構成を確認 | coherent pushout の補題が必要 |
| 12 | 最小仕様と代替案を記載 | ∞ fibration の全証明は未確認 |
| 13 | 同値を確認、強い表現を修正 | literal な自明 fibration は別構成 |
| 14 | BGT の比較主張を確認 | Schlichting 全比較証明は未確認 |
| S1 | 型草案・自然性・利用表を記載済み | L1 と型を固定する入力として利用可能；未コンパイル |

## 1. Lemma 4.16 と Prop 4.14 の非可換版（L6・L2）

原典：[KST v4](https://arxiv.org/pdf/1611.08466v4) pp.25–26、Prop 4.14、Claim 4.15、Lemma 4.16；
同 pp.43–46、Appendix A。本文の仮定は可換環であり、以下は**非可換への拡張の再構成**である。

I は結合的非単位単体環、a ∈ I₀ は中心的で、その退化像による右乗法 x ↦ xa が各単体次数で単射、とする。
単位化は ℤ ⋉ I を用いる。aI = Ia は両側イデアルで、aI → I と x ↦ xa は別の射として扱う。
列ベクトルに左行列作用を入れ、φ(v) = ((1), (va,0))、ψ(v) = (1+N(v),0)、
u₀ = (0,…,0,a)ᵗ、u = (1,u₀) と置く。半直積の積を (g,x)(h,y)=(gh,x+gy) とすると
u⁻¹ψ(v)u = (1+N(v),N(v)u₀) = (1+N(v),(va,0)) = ψ(v)φ(v)。
N(v)N(w)=0、N(v)(wa,0)=0 なので ψ の加法性と φ・ψ の像の可換性は I の可換性を使わない。
左行列 b に対して (bv)a=b(va) であり、最後の座標は作用の外にあるため u は固定される。
これで Construction A.6 の共役ホモトピーは Mₙₙ(I) 同変になる。
Construction A.5 の shuffle による積ホモトピーと m−1 の帰納仮定を合成すると、
C(φ) は次数 ≤m で定数射と鎖ホモトピックになる。単体環ではこの自然な構成を各次数に適用し、
二重複体を全複体にする。積を交換した箇所は上の N(v) の計算だけである。

Prop 4.14 の拡張は「GL(ℤ) が im Hᵢ(BĜL(aI))→Hᵢ(BĜL(I)) に自明に作用する」。
Claim 4.15 の上三角ブロック群、安定化、Appendix A.4 の半直積比較を上記ホモトピーに適用する。
中心性は aI の両側性と (id,×a) の半直積射に必要。Lemma 4.16 の行列恒等式単独には中心性は不要。
非単位環の GL は単位化での合同部分とその単体的群状版で定義し、全行列が可逆とは仮定しない。

Lean 必要補題：単位化・両側イデアル、右乗法の左行列同変性、上三角平方零行列、
半直積共役公式、相対 bar 複体、自然な共役鎖ホモトピー、shuffle と truncated 鎖ホモトピー、
二重複体への自然変換の延長、有限ブロックから安定 GL への filtered colimit、Claim 4.15→4.14。
判定：行列段階は確認済み。Appendix A の鎖複体補題は L2 の実装義務であり、ここで公理化しない。

## 3. Corollary 4.12・4.13（L6）

原典：KST v4 pp.23–24（Lemma 4.9・4.10、Thm 4.11、Cor 4.12・4.13）。
Cor 4.12 の本文には独立した証明がない。以下は**証明の補完**。

I=(a₁,…,aᵣ)、J=φ(I) とする。Iⁿ→Jⁿ は同型で、
I^{r(n−1)+1} ⊆ (a₁ⁿ,…,aᵣⁿ) ⊆ Iⁿ より双方の塔は共終である。
従って {a(n)A}→{a(n)B} は pro 同型。ただし各 n のこの射が同型とは限らず、
Iⁿ≅Jⁿ を経由して逆向きのレベル射を取ることが必要である。
高次 π は離散環では零。Thm 4.11 で Koszul 商の相対 K の pro 同型を得る。
Lemma 4.10 により {Ko(A;a(n))}→{A/(a(n))} は π_* pro 同型、Prop 4.8 で K に移る。
B にも適用し、共終なイデアル冪と Lemma 4.6 の fiber 比較で結論。

Cor 4.13：各 i>0 の πᵢA は π₀A 上有限生成で、D(aⱼ) 上で零。
有限生成元ごとに局所化での消滅を使い、aⱼ の共通冪が πᵢA を殺す。
従って {a(n)πᵢA}=0（指数は i に依存してよい）。i=0 は恒等射なので
A→π₀A に Thm 4.11 を適用できる。ここで得る下側の商は Ko(π₀A;a(n))。
Lemma 4.10＋Prop 4.8 でこれを離散商 π₀A/(a(n)) に置き換える。
これは π₀Ko(A;a(n)) と等しいので、本文の tV_X(a(n)) と一致する。

係数版の条件：A 自身の Noether 性に代えて、可換 Noether 基底 B の有限生成ホモロジーに
平坦 H をテンソルして得る Koszul pro 消滅を要求する。B⊗H のホモロジーを有限生成と誤認しない。
非可換 Cor 4.12 は任意の非可換 Noether 環への無条件拡張ではなく、中心生成イデアルと
Lemma 4.10 の出力を持つ係数環に限定する。

Lean 必要補題：イデアル冪と生成元冪の二つの包含、共終塔の同型、
有限生成加群の局所化消滅→冪で消滅、Koszul SS の次数ごとの有限比較、
π₀Koszul の同定、平坦テンソルによるホモロジー・pro 零性保存、fiber 比較。
判定：可換版の再構成は完了。係数版は項目1・2と Koszul 補題を明示して移植する。

## 2. R[t] 上の半自由置換（L6）

原典：KST v4 p.27、Thm 4.11 の基底段階第2段落（非零因子への置換は説明なし）；
pp.28–29 の Claim 4.18・4.19 と r に関する帰納段階。
以下は**結合的 dg 代数による置換の補完**で、原典の単体可換環とは模型が異なる。

中心的 a を持つ connective R-dg 代数 A を、t↦a により R[t]-代数とみなす。
結合的 R[t]-代数としてセルを付加して Q→A を構成する。Q の基礎 graded 加群は
R[t] 上自由（単語の基底）なので t、従って tⁿ 倍が単射。
0→Q→Q→Q/tⁿ→0 の cofiber より Ko(Q;tⁿ)→Q/tⁿ は擬同型。
Q→A の擬同型は、その tⁿ 倍との可換正方形の cone により全ての n で Koszul 商の擬同型を与える。
置換は A→B と pro 遷移射を含む図式に関して関手的に取り、中心 t を共通にする。
これで Prop 4.14 は tⁿQ の合同部分に適用でき、Claim 4.19 の指数選択も保たれる。

r>1 では R[t₁,…,tᵣ] 上で同じ構成を使い、最後の変数で Koszul 商を取って帰納する。
中間 Koszul 代数自体が残りの変数に関して自由であるとは主張しない。
各帰納段階で関手的置換を取り直すか、Lemma 4.10 の出力を保持する。
πᵢQ≅πᵢA なので基底 Noether 性・有限生成性を要する条件はホモロジー側で保たれる。

Lean 必要補題：中心多項式環上の相対自由結合代数、関手的セル分解、
単語基底による t の単射性、cone の擬同型不変性、図式置換と冪の自然性、
中心 Koszul 商と derived quotient、Γ と ĜL の比較。
判定：dg の非零因子化は確認済み。**これだけで KST の単体環証明全体の移植完了にはならない**。
Γ の乗法・行列・bar の比較、Prop 2.15 の dg 版は項目5の別義務である。

## 4. simple 空間の pro-Whitehead（L6・L9・L2）

原典：KST v4 p.21、Prop 4.3。仮定は pointed connected nilpotent 空間の可算添字系。
[BK, LNM 304](https://doi.org/10.1007/978-3-540-38117-4) III.5.4(ii) p.83・III.6.6 pp.88–89。
原文は[大学公開スキャン](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/bk-yellow.pdf)
の PDF pp.88,93–94 で照合（印刷頁は5だけ小さい）。
III.5.4(ii)：各 X_s が R-nilpotent な fibration 塔について {X_s}→{R_sX_s} は weak pro-homotopy equivalence。
III.6.6：fibration 塔の射に対し {R_sX_s}→{R_sY_s} が weak pro-homotopy equivalence であることと
全正次数 Hᵢ(−;R) の pro 同型が同値。

必要な限定形：ℕ 塔 X,Y の各空間が連結 simple（π₁ は可換、全 πₙ への作用が自明）、
Hᵢ(X)→Hᵢ(Y) が全次数で pro 同型なら πᵢ も pro 同型。
KST の Prop 4.8 には連結 H 空間 BĜL⁺ を入れる。
ただし Claim 4.17 の相対 K の連結被覆 fiber については、**fiber は自動的に H 空間とは限らない**。
K の無限ループ写像として fiber・連結成分・被覆を比較し simple 性を証明する追加補題が要る。

再構成した証明：mapping-path による関手的置換で各塔の遷移を fibration にし、
各段階のホモトピー型を保つ。R=ℤ とする。simple 空間は nilpotent、従って ℤ-nilpotent。
5.4(ii) で X とその対角 completion 塔 ℤ_sX_s、Y と ℤ_sY_s をそれぞれ pro 同値で結ぶ。
6.6 により H_* pro 同型は中央の completion 塔の pro 同値を与える。
可換正方形と2-out-of-3で X→Y の π_* pro 同型が従う。nilpotence の長さに一様上界は不要。
単に「各レベルで Whitehead を適用」する証明ではない。

BK 補題自体を実装する経路：5.3 の principal Postnikov refinement と、
有限段の R-resolution の比較から5.4を示す。6.6 の順向きには自由単体 R 加群の
反復が pro 同値を保存すること（III.3.4）と cosimplicial partial Tot の有限段比較を使う。
逆向きは R-resolution の H_* における自然な左逆（I.5.4）を使う。
simple 版だけを直接 pro-Hurewicz で証明する道もあるが、それは原典からの別経路であり採用必須でない。

Lean 必要補題：simple の定義、連結 H 空間の simple 性、連結被覆と無限ループ空間の比較、
pro π₁=pro H₁、principal Postnikov refinement、自由単体 ℤ 加群と R-resolution、
partial Tot と二重塔対角、可算再添字、局所係数作用の自然性。
判定：BK の二命題とその合成による simple 版を原文で確認済み。これらの補題は L9・L2・L6 が証明する。

## 7. 係数つき降下データと D_qc（L4）

原典：KST v4 §2.2 pp.7–9（Perf と Zariski 降下）；LT v3 Appendix B、Lemma B.2、p.39；
TT Appendix B pp.409–418（O 加群と準連接加群の導来比較）。
LT は QCoh のテンソル積の経路であり、以下の有限 MV 帰納は**代替経路**。
ここで D4 は KST 経路 §4 の D4（係数つき Perf）で、既存 Derived/PullbackCriterion の D4 とは別。

X は qc separated、有限アフィン被覆 {Uᵢ}、H_X=O_X⊗_A H を準連接結合代数層とする。
降下模型は全ての重なり上の dg 加群を擬同型で局所化した Čech 図式の homotopy limit。
**鎖同型を strict な三重 cocycle で貼るだけのデータは採用しない**。
U∪V の場合、対象 M_U,M_V と重なり上の導来同値を、層複体の標準 fiber
fib(Rj_{U*}M_U ⊕ Rj_{V*}M_V → Rj_{U∩V*}M_{U∩V}) で貼る。
制限すると一方の項が恒等となり、元の複体を回収する。mapping 複体にも同じ fiber 式を適用し
完全忠実性を得る。全射性と合わせて導来圏同値。有限被覆について再帰し、
重なりの Čech 模型との Fubini・細分同値を入れて全高次整合性を回収する。
準連接性は qc 開埋め込みの Rj_* と有限 fiber で保存されることを証明する。
非可換 H に対しても O_X 上の中央作用と準連接基礎加群を使うのでこの構成は通る。

Perf の貼り合わせには別途「compact ⇔ 局所的 finite-cell の retract」が必要。
自由／忘却随伴から生成系 P⊗H_X を得るが、局所コンパクト性だけをもって
大域コンパクト性を無条件には推論しない。有限 MV と mapping の有限 fiber・filtered colimit の可換で証明する。
H の平坦性はこの導来降下自体には不要；非導来 H⊗O の底変更の計算には使う。

Lean 必要補題：係数加群層の導来制限・Rj_*、開底変更、QCoh の保存、
mapping の MV、homotopy coherent Čech limit の Fubini、有限被覆帰納、
アフィンで D_qc≃D(H⊗O(U))、コンパクト対象の局所判定と small Perf 模型。
判定：模型の仕様・再構成を確定。既存 D4 だけから層の降下は出ないため、この比較の実装を L4 に要求する。

## 8. Thomason Lemme 2.3 と KST Lemma 3.11（L5・L7）

原典：Thomason, *Les K-groupes d'un schéma éclaté et une formule d'intersection excédentaire*,
Invent. Math.112 (1993), pp.195–215、Lemme 2.3 p.200（公開検索抽出で本文の命題を確認；
[DOI](https://doi.org/10.1007/BF01232430)、PDF 全文の取得は失敗）。
2.3(a) は perfect F に対する F→Rp_*Lp*F、(b) は射影束での同じ単位同型と
1≤i≤d−1 の負の捻りの消滅。KST v4 Lemma 3.10・3.11 pp.15–16 がこの形で使用する。
原典の証明全体を確認済みとはせず、以下の**普遍 blowup の直接計算**を採用する。

普遍環 A′=ℤ[T₀,…,Tᵣ]、中心 (T) の blowup は ℙʳ_ℤ 上の O(−1) の全空間。
その構造層の射影直線側への押し出しは ⊕_{d≥0}O(d)。標準 r+1 アフィン被覆の
Čech 複体は有限長で、直和と可換。H^j(ℙʳ,O(d))=0 (j>0,d≥0)、
H⁰(O(d))=ℤ[T] の d 次部分より RΓ(O)=A′。よって O→Rp′_*O は擬同型。
perfect F は双対可能なので射影公式で F→Rp′_*Lp′*F を得る。
導来底変更後の p には同じ単位同型が移る（非導来底変更で代用しない）。

Lemma 3.11 は標準 Čech 複体の単項式分解で証明する。
O(−k)、1≤k≤r では総次数 −k の Laurent 単項式について、全 r+1 変数の指数が
負になることはない。一つの非負指数の変数を選べるため、その変数を加除する
Čech contracting homotopy がある。従って全コホモロジーが零。
任意の基底への導来テンソルで消滅が保存され、E=ℙʳ_Y 上でも
RHom(O_E,O_E(−k))=0。H 係数版は同じ O 線形複体をテンソルして得る。

Lean 必要補題：普遍 blowup≅Tot O(−1)、有限 Čech 複体と graded 直和、
単項式の次数分解・contracting homotopy、RΓ の比較、射影公式、導来底変更。
判定：必要な計算と原典との差分を確定；Thomason の全証明の直接照合は未確認。

## 9. Lemma 4.7 の対角代替（L6・L5・L7）

原典：KST v4 Lemma 4.7 pp.21–22、Lemma 5.5 pp.33–34、その二重添字使用 p.35；
[Isaksen, math/0106094v1](https://arxiv.org/pdf/math/0106094)、Thm 4.1 p.7
（刊行版は Fund. Math.175 (2002), pp.175–194；ここでは arXiv 頁）。
「Isaksen 4.7」ではなく、**KST Lemma 4.7 が Isaksen Thm 4.1 を使う**。

Ab 値の可換な二重塔 fₙₘ を固定。各 m で f_{-,m} が pro 同型とする。
Ab の pro 核・余核を levelwise に取れることから、任意の標的 (n,m) に対し
十分大きい n′ から ker(f_{n′,m})→ker(f_{n,m}) と coker の遷移が零。
一つの n′ にそろえる。k≥max(n′,m) とすると対角からの遷移
(k,k)→(n′,m)→(n,m) も零。従って全二重塔も pro 同型。
対角 ℕ→ℕ² は共終なので対角塔も pro 同型。πᵢ に各々適用すればスペクトル版を得る。
**全 m に一様な指数は不要**。必要なのは、二つの添字方向の遷移が交換することと
各固定 m での pro 零性である。m について関手的でない任意の選択では二重塔を作れない。

Lemma 5.5(ii) は有限個のチャートと有限長 Čech で次数ごとに有限個の指数を取る。
(iii) は各固定 m の普遍チャートの Lemma 4.10 と derived base change（4.1）から得る。
その後に上の核・余核の議論を適用する。有限集合の最大値は取るが無限 m の上限は取らない。
Lean 必要補題：Ab の levelwise kernel/cokernel、pro 零判定、対角共終性、
二重塔の可換性、有限長 SS の比較と有限被覆の自然性。
判定：ℕ² の π_* 版で代替可能。Isaksen の任意添字圏に関する一般定理は実装不要。

## 10. Chase と F5 の係数環（F5）

原典：Chase, *Direct Products of Modules*, Trans. AMS97 (1960), pp.457–473、Thm 2.1。
**定理の正確な頁は未確認**（AMS 原文取得は403）。
命題と以下の証明は [Stacks 05CZ, Prop 10.90.6](https://stacks.math.columbia.edu/tag/05CZ)
で照合できる。これは原典確認の代替資料であり、Chase 原文の読了とはしない。

A 可換 Noether ⇒ 有限生成イデアル I は有限表示。有限表示加群のテンソル積は積と可換なので
I⊗_A∏M_λ ≅ ∏(I⊗_AM_λ)。各 M_λ が平坦なら I⊗M_λ→M_λ は単射、
積も単射。有限生成イデアルによる平坦性判定から ∏M_λ は平坦。
F5 の M_λ=M_{s_λ}(A) は有限自由（行列成分による基底）であり、B_A=∏M_{s_λ}(A) は A 平坦。
有限サイズが λ によって非有界でもよい。B_A 自身の Noether 性は不要で、一般に主張しない。
Lean 必要補題：Noether→イデアル有限表示、有限表示テンソルと任意積、
積の単射性、イデアル平坦性判定、行列加群の有限自由性、積代数の中心 A 作用。
判定：F5 に必要な方向の証明を再構成済み；Chase の個別頁は未確認。

## 5. Waldhausen 2.3.2 の ∞-S• 版（L1・L2・L3）

原典：[Waldhausen LNM1126](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kspaces.pdf)
Thm 2.3.2 p.394、直後の Remark、Prop 2.3.3 pp.395–396、Prop 2.3.5 pp.396–397；
Lemma 2.3.4 p.395、Thm 1.7.1 pp.360–368。KST v4 Prop 2.15 p.10；BGT v4 Prop 9.31–9.32 pp.63–64、
Lemma 9.39・Prop 9.40 p.67。
重要な原文の区別：Thm 2.3.2 の有限自由版の π₀ は K′₀（自由加群が生成する部分群）。
**全 K₀ を得るのは直後の retract を許す変種**であり、自由版をそのまま Perf と同定しない。

再構成経路：connective dg 代数の有限半自由加群を球状セルの部分圏で近似し、
Thm 1.7.1 のセル濾過を作る。単一次数・rank q の対象の自己同値モノイドは ĜL_q と比較する。
直和による rank の安定化を群完備化し、完全正規部分群 E を殺す acyclic map を構成する。
群完備化のホモロジー局所化と simple 空間の Whitehead で BĜL⁺ を同定する。
最後に半自由の retract 完備化への cofinality を証明し、正の次数を保ち π₀ を K₀(π₀A) にする。
∞-S• との接続は BGT 7.12・9.32 の比較を再証明するか、同じセル・bar 構成を ∞-S• 内に作る。

原文 Lemma 2.3.4 は h_*M=π_*(M⊗ᴸ_Rπ₀R) とおき、既に Künneth SS
`Tor_p^{π_*R}(π_*M,π₀R)_q ⇒ h_{p+q}M` を使う。
πᵢM=0 (i<n) なら総次数 n の edge が πₙM≅hₙM を与える（自由模型で導来テンソルを計算）。
これを dg のセルテンソル濾過で再現するのが必要な移植である。
SS の式だけから Thm1.7.1 の全仮定が自動で出るとは判定しない。球状近似が必要な連結性を持つこと、
その近似が morphism・cofibration に関して相対的かつ関手的に取れることを証明する必要がある。
ΓA の乗法と半自由 dg 加群の自己同値の比較も必要で、Thm 2.3.2 はその dg 版を直接述べていない。
判定：原典の結論・π₀ の補正は確認済み。**∞版全体は未確認**、上記セル比較を証明する経路を代替仕様とする。
Lean 必要補題：球状セル濾過、相対近似の連結性、Künneth SS と収束、
ĜL 自己同値比較、Segal 群完備化、plus の局所係数 acyclicity、retract cofinality、S• 比較。

## 6. dg Bass 基本定理と自然分裂（L1・L3）

原典：KST v4 Thm 3.16–3.17 p.19；TT Thm 6.1 pp.351–354、Thm 6.6 p.361、
7.5 pp.365–366、8.1 p.367；
[Tabuada, *Eₙ-Regularity Implies Eₙ₋₁-Regularity*](https://ems.press/content/serial-article-files/26221),
Documenta Math.19 (2014), Thm 4.2 pp.128–130、Lemma 4.11・Notation 4.12 p.130；
[Weibel K-book III](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf) Def 4.1.1 pp.29–30、Thm 4.3 p.31
（Weibel は章別公開 PDF の頁）。

Tabuada 4.2 は任意 dg 圏・Morita 不変な局所化不変量について Bass の**完全列**を述べる。
その証明は ℙ¹ の [O],[O(−1)] による二成分分解と標準二開被覆の MV。
[O],[O]−[O(−1)] に基底変換すると制限写像は (Δ,0)。
eval(t=0) が Δ の片側逆を与えるので、LES は
0→Kₙ(D)→Kₙ(D[t])⊕Kₙ(D[t⁻¹])→Kₙ(D[t,t⁻¹])→Kₙ₋₁(D)→0 に分かれる。
これは dg 版への移植を原典で裏づける。ただし**完全列だけから最後の射の自然分裂は出ない**。

K 固有の自然分裂は、中央単位 t の automorphism と外積の組
s_t(x)=x∪[t] を作り、境界 ∂s_t=id となる向きで固定する。
TT 6.1(b) の「自然な自己同型まで」の符号を吸収し、∂ と s_t の定義を一緒に選ぶ。
必要なのは K 全体の対称モノイダル構造でなく Perf(D) の ℤ[t,t⁻¹] による作用と、
S• の biexact pairing の整合性。t は中心なので D 非可換でも可。
すると NKₙ(D)=ker(ev₀) を使って
Kₙ(D[t,t⁻¹])≅Kₙ(D)⊕NKₙ(D)⊕NKₙ(D)⊕Kₙ₋₁(D)。
負の次数はこの自然分裂で下降帰納できる。
Lean 必要補題：dg テンソルの商保存、ℙ¹ の半直交分解、局所化と MV、
基底変換、central-unit pairing、境界と外積の整合、eval の切断、NK の自然性。
判定：dg 完全列は原典確認済み。自然分裂には pairing の追加証明が必要；一般不変量の完全列からの推論では代用しない。

## 11. McCarthy 流加法性（L1）

原典：Waldhausen Thm 1.4.2 pp.336–337；
[Fiore–Pieper 著者公開版](https://www-personal.umd.umich.edu/~tmfiore/1/FiorePieperQCatAddNONHouse12.pdf)
Lemma 4.24 pp.56–57、Prop 4.27 pp.60–61、Thm 4.35 p.62；
pushout の関手的選択は Cor 3.35 pp.43–44（PDF に印刷された頁）。
これは McCarthy の発想を用いる ∞ 版の直接資料。Waldhausen の証明からは**経路変更**。

E(A,C,B) の cofiber 列を subobject と quotient に送る射について、
object simplices の二重単体集合の各 fiber を pushout を用いるホモトピーで縮める。
Quillen A の単体積版と realization lemma で対角の弱同値を得る（Lemma 4.24）。
object simplices→core を S• 後に比較する Prop 4.27(iv) を使い、
|core S•E|→|core S•A|×|core S•B| の同値を得る。
**E≃A×B を ∞圏レベルで主張するわけではない**。拡張類は S• と実現の後に処理される。
pushout を対象ごとに選ぶだけでは単体恒等式を満たさないため、
普遍的な cocartesian completion の制限自明ファイブレーションを使って関手的に選ぶ。
Lean 必要補題：cofiber 列の ∞圏、関手的 pushout、McCarthy 型単体ホモトピー、
単体積 Quillen A、二重実現と有限積、object/core の S• 後比較、反復 S• の自然性。
判定：∞版の主張と証明部品を原典確認済み；「そのまま」を strict な対象選択と解釈しない。

## 12. 最小 fibration 定理（L1・L3）

原典：Waldhausen Thm 1.6.4 pp.350–352（cylinder・saturation・extension を仮定）；
BGT v4 Thm 9.34 p.64（非連結 K の局所化）。
原典の古典的仮定を省略して ∞圏の定理に読み替えることはしない。

C 安定、D thick、W={f | cofib(f)∈D} とする。W は2-out-of-3、pushout、extension で閉じる。
∞-S• の W-同値を使う版と同値だけを使う版を比較し、
W-acyclic 対象の列が contractible なことと加法性で fiber を計算する。
局所化 C[W⁻¹] を dg 商の nerve と比較するには、三角圏 H⁰ の Verdier 普遍性だけでなく
mapping 空間の局所化の比較が必要。U15/U17 の H⁰ 同値だけをその代用にしない。

さらに quotient の冪等完備化は K₀ を変え得る。連結 K の fibration を
冪等完備 Verdier 列すべてに無条件で課すと、π₀ の全射性に誤りが生じる。
最終的に必要な型は **非連結 K の** K(D)→K(C)→K((C/D)^idem) の fiber 列。
連結構成で証明する中間定理は未完備商・必要な cofinality 条件を明示し、
Schlichting の suspension と比較して全次数 LES に昇格する。
Lean 必要補題：W の安定性、∞局所化と dg 商、W-S• の比較、acyclic 版の可縮性、
局所化定理の K₀ 条件、非連結化と fiber、境界射の自然性。
判定：最小最終仕様を確定；Waldhausen の論法の ∞版全体は未確認。代替は Schlichting の dg 局所化を証明して BGT と比較する。

## 13. gapped と第一行（L1）

原典：BGT v4 Def 7.1・Lemma 7.3 p.44、Remark 7.4 pp.44–45。
原文が述べるのは Gap([n],C)→Fun(Δ^{1,…,n},C) の **∞圏の同値**。
「自明 Kan ファイブレーション」という強い語は原文の結論そのものではない。

第一行 F(0,1)→…→F(0,n) から F(i,j)=cofib(F(0,i)→F(0,j)) を復元する。
対角は零、各四角は pushout であり、有限の順に left Kan extension を施せる。
各段の普遍錐の空間は可縮で、パラメータ付き図式にも同じ拡張を適用するので、
対象だけでなく mapping 空間も同値。n=0 は零対象の可縮空間として別処理する。
core を取れば Kan 複体間の弱同値を得る。これを literal な自明 Kan fibration にしたければ、
制限の相対境界持ち上げ性を証明するか、functorial な mapping-path fibration 置換を取る。
任意の同値 functor が literal な自明 Kan fibration とは限らない。
S• の定義は全 gapped 図式を保つ（商を選んだ第一行模型に置き換えると単体的整合性が必要）。
Lean 必要補題：Fun 上の相対 Kan extension、零対象空間、有限 cocartesian completion、
core の同値保存、パラメータ付き可縮 fiber、必要なら単体的 fibration 置換。
判定：原典の同値は確認済み；強い fibration 表現は別構成として仕様化する。

## 14. BGT (a) と Schlichting (b)（L3）

原典：BGT v4 §9.1 pp.57–58、Def 9.1、Lemma 9.4、Prop 9.5、Def 9.6 と直後の比較段落；
§9.3 Prop 9.32・Remark 9.33・Thm 9.34 pp.63–64。
BGT は Schlichting, *Negative K-theory of derived categories*, Math. Z.253 (2006), pp.97–134、
§2.2・§8・§12 をここで参照する。**刊行版の節ごとの頁と比較証明の全詳細は未確認**。
[公開原稿](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/schlneg.pdf) は表紙 June16,2003 の28頁版で、
刊行版と番号が異なる。直接照合できる対応物は setup1.3 p.4、Agreement §7 pp.14–15、
spectrum Def11.4 pp.20–21、Thm11.7 p.21、局所化 Thm11.10 pp.21–22、dg代数への適用11.14 p.22。
この版の「§2.2」は homotopy colimit、「§8」は負K₋₁の表示であり、BGT の引用番号を転記しない。

(a) は FκC=(Indω C)^κ、ΣκC=FκC/C、K^nc(C)=colim_r ΩʳK(ΣκʳC)。
κ は非可算正則で FκC に可算直和があり、id⊕T≃T の swindle で K(FκC)=0。
Fκ・Σκ の exactness と、dg suspension の対応物に同じ性質があることを示す。
共通の拡大圏へ二つの cone を写し、商を比較する自然な zigzag を作る。
連結 K の比較（9.32）と各 suspension の比較を r ごとに合わせて colimit を取る。
公開原稿11.4は flasque K の**関手的な contraction**から構造写像を作り、11.7は cofinality で
次数0の冪等完備化を補正して Ω-spectrum にする。11.10は suspension の exactness と
古典 fibration 定理で各段の cartesian square を作る。従って群だけの swindle でなく
contraction と構造写像の自然性を比較に含める必要がある。
π₀ の一致だけでは比較にならず、全整数・全 exact functor・境界射との整合が必要。
また Fκ 自体は κ-filtered colimit 保存までしか直接保証されない（Lemma 9.7 p.58）。
最終 K^nc の全 filtered colimit 保存を、これだけから形式的に導いてはいけない。

Lean 必要補題：宇宙を上げた Ind と κ-compact 小モデル、swindle、cone と quotient の exactness、
dg cone→∞ cone の比較、反復の coherent 自然性、Ωʳ と sequential colimit の π_* 計算、
負次数の比較、LES 境界の整合。判定：BGT の比較主張と Schlichting 公開原稿の構成を確認済み；
刊行版の番号対応と二模型間の全比較は未確認。代替は上記の共通 cone を構成し、比較を定理として実装する。

## S1. K0 界面の Lean 型草案

### S1.1 既存型への接続と宇宙

以下のコードは **Markdown 内の型草案**であり、コンパイル済み宣言でも追加公理でもない。
新しい構造の値は L1・L3 が具体的な K の構成と証明から組み立てる。
未定義の補助名はその直前・直後で仕様を示す。`sorry` でフィールドを埋めて利用しない。
原典の基礎は KST v4 §2 pp.7–11、BGT v4 §7 pp.44–49・§9 pp.57–70。

| 既存宣言 | 実際の型と使用箇所 |
| --- | --- |
| `DGCategory A D` | `EnrichedCategory (Complex A) D` の略記。`A : Type u [CommRing A]`、`D : Type v`。新しい dg 構造は導入しない |
| `DGFunctor A D E` | `EnrichedFunctor (Complex A) D E`。恒等・合成は `DGFunctor.id`、`DGFunctor.comp` |
| `modulePerfect A D` | `ObjectProperty (DerivedModuleCategory A D)`。型そのものではない |
| `PerfectModuleCategory A D` | `(modulePerfect A D).FullSubcategory`、既存の主 Perf |
| `SmallPerfectDGHomotopyCategoryOver A D Set.univ` | 小さい射影的 dg 代表系の H⁰。大きい主 Perf と三角同値 |
| `DGQuotient.localPerfectQuotientEquivalence A D S h` | `PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌ CompletedTriaQuotient A D S`、`h : localKFlat A D S` が必要 |
| `TriangulatedK0 C` | 対象の自由可換群を同型と完全三角の関係で割る `Type`。`AddCommGroup` 構造を持ち、Ab に包むには `AddCommGrp.of` |
| `TriangulatedK0.map F` | `[F.CommShift ℤ] [F.IsTriangulated]` の下で `TriangulatedK0 C →+ TriangulatedK0 E` |

参照ソース：`DifferentialGraded/Category/Basic.lean:21`、`Functor/Basic.lean:16`、
`Perfect/Basic.lean:21–30`、`Perfect/SmallEnhancementTriangulated.lean:18`、
`Quotient/DerivedComparisonPerfect.lean:69`、`CategoryTheory/TriangulatedK0.lean:37,110`
（いずれも `SerrePositivity/` 以下）。

最初は基底 A を固定し対象宇宙を u にそろえる。任意 v の既存 dg 圏には `[Small.{u} D]` を付け、
`Shrink` 等の代表系でこの宇宙に移してから評価する。大きい dg 加群圏を小さいと仮定しない。
Ab の値の宇宙は u、構成全体は u+1。別の基底への忘却・スカラー拡大を使う際は、
ℤ 線形版への忘却との自然な比較を追加する（異なる A の値を定義的等号で同一視しない）。

```lean
universe u
open CategoryTheory
open SerrePositivity SerrePositivity.DifferentialGraded

-- 豊穣構造の再定義でなく、既存構造を持つ対象の束ね。
structure SmallDG (A : Type u) [CommRing A] where
  Obj : Type u
  dg : DGCategory A Obj

-- instance と Category は既存 DGFunctor.id / comp から組み立てる。
-- Hom D E := DGFunctor A D.Obj E.Obj

structure KGroups (A : Type u) [CommRing A] where
  K : ℤ → (SmallDG A ⥤ AddCommGrp.{u})

-- K n の functor 法則に加え、dg 自然同値な射に同じ map を要求する。
-- dg nerve 上の coherent exact functor からの構成により証明する。
```

### S1.2 局所化・境界・Morita・余極限

単に各次数の完全列の存在だけでなく、**選んだ境界の自然性**を公開する。
`VerdierDGSequence` は dg 関手 i:C→D、q:D→E と零化の coherent データを持ち、
Perf(C)→Perf(D) は充満忠実、Perf(E) は Perf(D)/Perf(C) の冪等完備化であるという証明を含む。
任意の underlying 三角圏の同値を証明として代用しない。

```lean
-- AddExact は AddMonoidHom の range = ker の略記。
def AddExact {P Q R : Type*} [AddCommGroup P] [AddCommGroup Q]
    [AddCommGroup R] (f : P →+ Q) (g : Q →+ R) : Prop :=
  f.range = g.ker

-- 以下 KG : KGroups A、s : VerdierDGSequence A とする。
-- s.C, s.D, s.E : SmallDG A、s.i, s.q はそれらの Hom。
-- 要求するフィールド（KLocalizingLaws KG）:
boundary : ∀ (s : VerdierDGSequence A) (n : ℤ),
  (KG.K n).obj s.E ⟶ (KG.K (n-1)).obj s.C

exactD : ∀ s n,
  AddExact ((KG.K n).map s.i).hom ((KG.K n).map s.q).hom
exactE : ∀ s n,
  AddExact ((KG.K n).map s.q).hom (boundary s n).hom
exactC : ∀ s n,
  AddExact (boundary s n).hom ((KG.K (n-1)).map s.i).hom

-- s→t の coherent 可換図式 (a,b,c) に対して必須：
-- (KG.K n).map c ≫ boundary t n
--   = boundary s n ≫ (KG.K (n-1)).map a
-- さらに零 dg 圏への評価が零群であること。
```

U15 の具体的入力は `S : Set D`、`h : localKFlat A D S` から作る
`DGFullSubcategory D S → D → DGQuotient.QuotientObject D S`。
`localPerfectQuotientEquivalence` と小さい Perf 模型との三角同値を合成し、
S1.4 の次数0における商圏との比較を得る。h のない一般 dg 商には K-flat 置換を先行させる。
同値があることから境界を任意に選ぶのではなく、同じ dg 商の局所化列から選ぶ。

Morita 条件は `F : DGFunctor A D E` が導来拡張で Perf の同値を誘導する場合に
`IsIso ((KG.K n).map F)`。U16 の kernel 版では `kernelDerivedTensor` と
`perfectDerivedKernelAction` を使い、inverse kernel・unit/counit・三角整合性の
証明を入力する。kernel を単なる H⁰ functor に忘れてから K を定義しない。
dg 擬同値についての `quasiEquivalencePerfectEquivalence` はこの条件の既存供給源。

filtered 余極限については次の比較射を公開する：

```lean
-- J は小さい filtered な通常圏、F : J ⥤ SmallDG A。
-- c は F の「導来 filtered colimit」を実現する cocone とその証明。
filteredComparison : ∀ n F (c : DerivedFilteredDGCocone F),
  colimit (F ⋙ KG.K n) ⟶ (KG.K n).obj c.pt
filteredComparison_isIso : ∀ n F c, IsIso (filteredComparison n F c)
```

`DerivedFilteredDGCocone` は未定義の仕様名。cofibrant 図式の filtered colimit と dg nerve の
Morita 局所化後の colimit の比較を証明する証明書であり、単なる任意の cocone ではない。
後で F2 の Morita ∞圏に精密化した時は `Kₙ` の filtered-colimit-preservation に対応させる。
有限積・有限直和は加法性から導き、F5 の**無限積について K と積の可換性を要求しない**。

### S1.3 connective 代数の比較と Bass

`ConnectiveDGAlg A` は単位的結合 A-dg 代数、中央 A 作用、Hᵢ=0 (i<0) の証明を持つ仕様名。
`oneObj B : SmallDG A`、`discrete (π₀B)`、`truncate B : oneObj B ⟶ oneObj (discrete (π₀B))`
を用意する。cochain 規約なら同じ条件を H^i=0 (i>0) と読み替え、ゼロ次だけを共通にする。
一般の connective 性がホモロジーにしかない模型では truncation を strict dg 射として
直接選べないため、非正次数模型への関手的置換とその Morita 同型を挟む。

```lean
-- KComparisonLaws KG の欄（B は上の connective 模型に置換済み）:
truncation_isIso : ∀ B (n : ℤ), n ≤ 1 →
  IsIso ((KG.K n).map (truncate B))

-- PlusPi B r は L9 の基点付き Kan ホモトピー群に
-- plus H 空間の加法群構造を装備し Ab に束ねたもの（r>0）。
plusComparison : ∀ B (r : ℕ), 0 < r →
  (KG.K (r : ℤ)).obj (oneObj B) ≅ PlusPi B r
zeroDiscreteComparison : ∀ B,
  (KG.K 0).obj (oneObj B) ≅ ClassicalProjectiveK0 (piZero B)
```

全て B の射に関して自然な同型とする。plus 側は BĜL(B)⁺ の基点成分で、π₀ は零。
Ω∞K(B) の π₀ は別欄の K₀(π₀B)、r>0 だけが plus の πᵣ。
π₁ は一般 Kan 空間では非可換なので、L9 の π₁ に H 空間の可換性を証明してから Ab に包む。
「全 n の plus πₙ」を要求しない（負の次数はこの空間から得られない）。
この仕様は KST Prop 2.15・Thm 2.16 の π_* 形であり、連結性の仮定を外して一般 dg 圏に適用しない。

Bass の欄は中央多項式・Laurent 拡張 `D[t]`,`D[t⁻¹]`,`D[t,t⁻¹]` とその dg 射に対して持つ。
差写像の符号を固定し、以下の四つの準同型を自然に選ぶ：

```lean
diag : K_n D →+ (K_n D[t] × K_n D[t⁻¹])
diff : (K_n D[t] × K_n D[t⁻¹]) →+ K_n D[t,t⁻¹]
bassBoundary : K_n D[t,t⁻¹] →+ K_(n-1) D
bassSection : K_(n-1) D →+ K_n D[t,t⁻¹]
-- injective diag; AddExact diag diff; AddExact diff bassBoundary;
-- bassBoundary.comp bassSection = AddMonoidHom.id _
-- D の射について diag, diff, boundary, section の全てが自然。
```

このブロックの `K_n` と添字付き多項式記法は説明用で Lean 識別子ではない。
実際には `(KG.K n).obj D`、`(KG.K n).map polyInclusion` へ展開する。
NK の核と eval の切断から得る4項分解を公開系にする。
`truncation_isIso` の負次数はこの Bass の欄と n=0,1 の比較から証明するため、
実装の依存順は plus比較→0,1比較→Bass→全 n≤1。循環して要求しない。

### S1.4 π₀ と TriangulatedK0

任意 dg 圏 D の H⁰D は三角圏とは限らず、冪等完備とも限らない。
そのため正しい一般欄は次である：

```lean
-- D : Type v [DGCategory A D] [Small.{u} D]
zeroEquiv :
  K_0 D ≃+ TriangulatedK0
    (SmallPerfectDGHomotopyCategoryOver A D Set.univ)
```

`K_0 D` は束ね・縮小を経た `(KG.K 0).obj ...` の underlying group。
既存の `smallPerfectDGModuleHomotopyEquivalence` を通じて
`TriangulatedK0 (PerfectModuleCategory A D)` とも加法同値になる（必要な宇宙持ち上げを明記）。
自然性は Perf 拡張の三角関手 P_F について
`zeroEquiv_E.toAddMonoidHom.comp (Kmap F 0)` と
`(TriangulatedK0.map P_F).comp zeroEquiv_D.toAddMonoidHom` の等号で書く。

D 自身が pretriangulated かつ H⁰D が idempotent complete で Yoneda が Perf との三角同値を
与える場合に限り、`TriangulatedK0 (HomotopyCategory A D)` への特殊化を出す。
「π₀=TriangulatedK0(H⁰D)」を任意 dg 圏に課すと、一対象環の H⁰D に三角構造がなく型が合わない。

商については `zeroEquiv (QuotientObject D S)` と、既存の
`localPerfectQuotientEquivalence A D S h` の `TriangulatedK0.map` を合成し、
`K_0 (D/S) ≃+ TriangulatedK0 (CompletedTriaQuotient A D S)` を得る。
この同値は対象の Yoneda 類をその商対象の Grothendieck 類に送る式まで含める。
F5 はこの式と n=0,−1 の LES を使って既存の Euler 評価へ接続する。

### S1.5 利用表と界面の不足を隠さない条件

| 欄 | A（導来幾何） | B（pro切除） | C（KST §5） | D（実降下） | E（主論文 §3） | F5 |
| --- | --- | --- | --- | --- | --- | --- |
| Kₙ functor・零・加法性 | 生成系の分解 | 行列安定化 | 有限被覆 | 有理化・差の fiber | pullback | 分解と評価 |
| Verdier LES・自然境界 | blowup の逐次商 | 相対 K・二重 fiber | pro cartesian | 有理化後の五項補題 | 台つき比較 | n=0,−1 必須 |
| Morita・small Perf | 係数とチャート | 置換 | アフィン比較 | スキーム模型 | 基底変更 | U16 と商 |
| filtered colimit | 係数・局所化 | 安定 GL・冪局所化 | アフィン局所化 | E の評価 | central localization | 台判定 |
| connective truncation | 古典化 | 4.8・4.11・4.13 | 5.5 | 離散の負 K | 第2段の係数 | 第1段では直接不要 |
| plus πᵣ | — | 4.8・Claim4.17 | B 経由 | — | — | — |
| Bass 自然分裂 | ℙ¹・射影束から供給 | 低次数 pro切除 | 古典化の入力 | 冪零性の負次数 | — | K₋₁ の接続 |
| π₀=TriangulatedK0 Perf | 商の同定 | K₀ の古典比較 | — | 台つき K₀ | `theorem_3_1_K0` | `supportedRankK0_descent` |
| 下記の coherent 相対構成 | MV・商 | fiber の比較 | 二重塔 | E の fiber | Čech Tot・G作用 | 局所化列 |
| transfer・射影公式 | 有限平坦の構成 | — | — | — | Lemma3.2 | 必要なら E 経由 |

**Ab 値の Kₙ と LES だけで全工程が閉じるとはしない。**
一般のホモトピー可換四角形の二重 fiber、Čech Tot、群作用と transfer の恒等式には
chain-level／空間-level の整合性が要る。したがって S1 は次の追加供給口も固定する。

1. 相対 dg 圏（支持核・商）を構成できる場合は、その Kₙ を relative K とし、上の LES を使う。
   任意の射の fiber は kernel/cokernel から**標準群として復元できない**ので、L9 の Ω スペクトル模型の
   fiber を使うか、L1 が相対 S• 模型と自然 LES を提供する。E=fib(Kℚ→K[1/p]ℚ) もこれに含む。
2. 同じ構成から得る有限 MV と augmented Čech の降下証明を、L9 の π_* と L6 の pro 形式へ渡す。
   群ごとの同型を寄せ集めて homotopy coherent な降下を宣言しない。
3. E レーン用に有限平坦 f の restriction-of-scalars transfer と projection formula、
   `trf ∘ f* = [f_*O]` の作用式を加法性から証明する。可変 rank を最初から単一整数としない。
   有限自由 rank d の局所で d 倍にし、有理化と Zariski 降下で用いる。
4. 有理化は Ab で ℚ テンソルの完全性、空間側では L9 の telescope と比較。
   有限 G の有理 invariants の完全性・averaging と Shapiro は E/L9 の証明であり、
   任意群の固定点が完全であるという欄は設けない。

主論文との位置：`paper/paper.pdf` Thm3.1 pp.10–14、Lemma3.2–3.3 pp.12–13、
Lemma4.6 pp.21–22（本文の印刷頁）。第1段の離散平坦係数による E と F5 の経路は、
原典の LT truncating＋connective 商係数経路からの**明示的な変更**である。
S1 の成果は L1・L3 が満たすべき型・自然性・証明順と既存 U15/U16/K₀ への接続であり、
実装前に存在を仮定する新しい公理の提案ではない。

### S1.6 引き渡しの判定

14項目には原典の箇所、再構成または未確認の核心、必要補題を記載した。
未確認を含む項目の代替案は5・12・14、および8・10の原典アクセスに明記している。
これらを数学的に証明済み・Lean 実装済みとして扱わない。
S1 の型草案は任意 dg 圏と connective 代数の欄を分け、U15/U16・小さい Perf・既存 K₀ に
接続する。境界の自然性、Bass 分裂の自然性、次数0の対象類の式、相対構成の供給口を含む。
L1 との合流では補助名の実名、宇宙、相対 S•／L9 fiber の選択を固定する。
L11 の担当成果物はこの検証記録と型草案で完了し、Lean ファイルの変更は含まない。
