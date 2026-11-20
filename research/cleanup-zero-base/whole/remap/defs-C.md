# 概念の定義書：C 単体集合と ∞ 圏

小概念の名前は `remap-C.csv`・`remap-E.csv`・`remap-Z.csv` の new_subconcept と一致する（C・E・Z の三つの表から来るものを載せた。ほかの大分類の表から来るものは含まない）。［足場］は aux=1、［止めた経路］は stopped のあるもの。文献は入力の reference にあるものだけ。

## C 単体集合と ∞ 圏/Kan 複体とホモトピー群

**入るもの**：Kan 複体と Kan ファイブレーション、単体的ホモトピー、ホモトピー群 π_n と基本亜群、長完全列、弱ホモトピー同値と可縮性、Ex∞ による Kan 置換。

**入らないもの**：
- 点つき空間の loop・path・fiber・写像空間は「基点付き空間」へ
- anodyne 射の類・小対象の議論による関手的分解・Kan–Quillen モデル構造は「E/単体的モデルと anodyne」へ
- Kan 値の図式と 𝒮 への写像は「空間・Cat∞・前層・Ind」へ
- 準圏の中の同型・同値・core は「関手単体集合と同値」へ
- 左・右ファイブレーションは「ファイブレーションと straightening」へ（自明 Kan ファイブレーションはここ）
- 単体集合のホモトピー引き戻し・押し出しは「極限と余極限」へ

**小概念**：
- Ex∞ と Kan 置換
- Kan ファイブレーションの長完全列と lim¹
- ホモトピー群と基本亜群
- 単体的ホモトピーと prism
- 単体集合のホモトピー圏
- 弱ホモトピー同値と可縮 Kan 複体
- Kan 複体の中の合成三角形と四面体［足場］
- 単体的ホモトピーの Kan 比較三角形［足場・止めた経路］

**文献**：
- Ex∞ と Kan 置換：Kerodon §3.3、Moss 2020 §3
- Kan ファイブレーションの長完全列と lim¹：Kerodon §3.2.5–3.2.6、Goerss–Jardine I §7・VI §2
- ホモトピー群と基本亜群：Kerodon §3.2（Goerss–Jardine I §7）
- 単体的ホモトピーと prism：Kerodon §3.1.5
- 弱ホモトピー同値と可縮 Kan 複体：Kerodon §3.1.6・§3.2.7
- Kan 複体の中の合成三角形と四面体：BF 1978 の比較の足場
- 単体的ホモトピーと prism：Kerodon 3.1.5, 1.4.5
- 単体的ホモトピーの Kan 比較三角形：計画書 §396（ファイル冒頭）

## C 単体集合と ∞ 圏/dg 神経

**入るもの**：dg 圏の dg 神経：単体の定義と単体的構造、低次元の単体、ホーンの充填、dg 関手・dg 自然変換の作用、テンソルとの両立、coherent 神経との比較、写像空間の線形模型。

**入らないもの**：
- Dold–Kan 単体的加群の標準模型と Alexander–Whitney 合成は「B/単体的鎖・Dold–Kan・シャッフル」へ
- 複体の dg 神経での fiber 四角形・cofiber 四角形、複体の strict な図式の ∞ 局所化は「D/導来 ∞ 圏」へ
- dg 圏・dg 関手そのものは「B/dg 圏と dg 関手」へ
- dg 双加群の導来作用が dg 神経の間に誘導する関手は「B/双加群とテンソル」または「D/導来 ∞ 圏」へ

**小概念**：
- coherent 神経との比較
- dg 圏のテンソルと dg 神経
- dg 神経の単体と単体的構造
- dg 関手と dg 自然変換の作用
- ホーンの充填（dg 神経は ∞ 圏）
- 低次元の単体（頂点・辺・三角形）
- 単体の方程式の分解（線形部分と二次部分）［足場］
- coherent 神経との比較のための立方体の旗と Path の評価［足場］
- dg 神経の写像空間（線形模型）

**文献**：
- coherent 神経との比較：HA Proposition 1.3.1.17
- dg 神経の単体と単体的構造：HA Construction 1.3.1.6（Kerodon 2.5.3）
- dg 関手と dg 自然変換の作用：HA Construction 1.3.1.6・Proposition 1.3.1.20 周辺
- ホーンの充填（dg 神経は ∞ 圏）：HA Proposition 1.3.1.10
- 低次元の単体（頂点・辺・三角形）：HA Example 1.3.1.8
- 単体の方程式の分解（線形部分と二次部分）：HA Construction 1.3.1.6
- coherent 神経との比較のための立方体の旗と Path の評価：HA Proposition 1.3.1.17 の証明
- dg 神経の写像空間（線形模型）：HA Construction 1.3.1.6、Kerodon §4.6.5

## C 単体集合と ∞ 圏/∞ 層

**入るもの**：小さい通常の圏のサイトの上の（Čech）層：層条件が主語の宣言、層の充満部分 ∞ 圏、層化。

**入らないもの**：
- 集合値前層で重み付けた切断・ホモトピー極限は「極限と余極限」へ
- 集合値前層の離散埋め込み・空間値前層・米田は「空間・Cat∞・前層・Ind」へ
- 通常の圏の篩・Grothendieck 位相だけの補題は「Z/圏・関手・極限」へ
- スキームの降下（Zariski・Nisnevich など）は「H/降下」へ

**小概念**：
- サイト上の E 値前層
- 層化（層への反射）
- 層条件（篩の上の制限錐）

**文献**：
- サイト上の E 値前層：HTT 1.2.7.3
- 層条件（篩の上の制限錐）：HTT 6.2.2.6

## C 単体集合と ∞ 圏/ねじれ矢と edgewise subdivision

**入るもの**：edgewise subdivision とねじれ矢の単体集合 Tw(C)、両端への射影とそのファイバー、通常の圏のねじれ矢との比較。

**入らないもの**：
- ねじれ矢から作る Hom 二変数関手・米田埋め込みは「空間・Cat∞・前層・Ind」へ
- 固定した底の上の右ファイブレーションの ∞ 圏は「ファイブレーションと straightening」へ
- 写像空間の模型（pinched・区間）は「写像空間」へ

**小概念**：
- edgewise subdivision
- ねじれ矢の単体集合と両端への射影
- 通常の圏のねじれ矢（Hom 関手の元の圏）
- edgewise の重みの頂点と延長領域［足場］

**文献**：
- edgewise subdivision：Kerodon Construction 8.1.1.1、Remark 8.1.1.2（Tag 03JH）、Remark 8.1.1.4（Tag 00B3）、Notation 8.1.1.6（Tag 03JK）
- ねじれ矢の単体集合と両端への射影：Kerodon §8.1（Tag 03JB）
- 通常の圏のねじれ矢（Hom 関手の元の圏）：Kerodon Remark 8.1.0.3（Tag 03JC）、Proposition 8.1.1.10（Tag 03JN）
- edgewise の重みの頂点と延長領域：Kerodon Remark 8.1.1.2（Tag 03JH）、Corollary 8.1.1.13（Tag 048H）

## C 単体集合と ∞ 圏/サイズの条件

**入るもの**：単体集合・∞ 圏・射の小ささの条件：κ 小さい単体集合、局所小さい ∞ 圏、ファイバーが小さい射。

**入らないもの**：
- 通常の圏の Small・LocallySmall・宇宙の持ち上げは「Z/圏・関手・極限」へ
- κ-filtered・accessible・compact は「表示可能 ∞ 圏とフィルター」へ
- 基数・順序数そのものは「Z/組合せと順序」へ

**小概念**：
- κ 小さい単体集合
- ファイバーが小さい射
- 局所小さい ∞ 圏

**文献**：（reference の記載なし）

## C 単体集合と ∞ 圏/ファイブレーションと straightening

**入るもの**：左・右ファイブレーション、cartesian・cocartesian ファイブレーション、ファイバーと輸送、相対関手空間と切断、straightening・unstraightening（空間値、Cat∞ 値）、ファイブレーションの ∞ 圏。

**入らないもの**：
- Kan ファイブレーション・自明 Kan ファイブレーション・長完全列は「Kan 複体とホモトピー群」へ
- 内ファイブレーション・isofibration は「準圏（基本）」「関手単体集合と同値」へ
- 関手単体集合 Fun(X,Y) の一般の道具（辺・prism・評価）は「関手単体集合と同値」へ
- 空間値の図式の極限・切断空間が極限であることは「極限と余極限」へ
- Dwyer–Kan の両側 Grothendieck 構成は「局所化（Dwyer–Kan）」へ
- K 理論のファイブレーション定理は「H/S 構成と K スペクトル」へ
- 普遍左ファイブレーション 𝒮_* → 𝒮 は「空間・Cat∞・前層・Ind」へ

**小概念**：
- cartesian・cocartesian 辺とファイブレーション
- cocartesian ファイブレーションの分類（Cat∞ 値）
- straightening（空間値）
- strict な Kan 値図式の ∞ 圏
- unstraightening
- ファイバーと共変輸送
- 左ファイブレーションの ∞ 圏
- 左・右ファイブレーションと anodyne 射
- 相対関手空間（切断・延長・cocartesian 切断）
- 輸送表現（witness と prism）
- 通常の圏の上のファイブレーション（weighted nerve と strict transport）
- Grothendieck 構成と要素圏による係数の表示［足場］
- cocartesian 分類の Hom 比較［足場］
- 底の上の引き戻しとファイバーごとの関手空間［足場］

**文献**：
- cartesian・cocartesian 辺とファイブレーション：Kerodon §5.1.4（Tag 01U9）
- straightening（空間値）：Kerodon 5.6（Tag 027M）
- strict な Kan 値図式の ∞ 圏：Kerodon Corollary 5.6.0.6（Tag 028T）、§5.6（Tag 027M）
- unstraightening：Kerodon Corollary 5.6.0.6（Tag 028T）、Remark 5.6.2.18（Tag 0271）、Example 5.6.2.19
- ファイバーと共変輸送：Kerodon Definition 5.2.2.4、Theorem 5.2.4.1（Tag 024N）、5.2（Tag 019A）
- 左ファイブレーションの ∞ 圏：Kerodon Corollary 5.6.0.6（Tag 028T）
- 相対関手空間（切断・延長・cocartesian 切断）：Kerodon §5.3.1（Tag 035D）、§5.6.2（Tag 026H）
- 輸送表現（witness と prism）：Kerodon §5.6.8（Tag 02S9）、Lemma 5.6.8.10（Tag 02SK）
- 通常の圏の上のファイブレーション（weighted nerve と strict transport）：Kerodon Definition 5.3.3.1（Tag 025X）、§5.3.3（Tag 025W）、Construction 5.3.4.7、Theorem 5.3.5.7（Tag 037Q）、Remark 5.3.2.12（Tag 0252）、9.3（Tag 06FR）
- 底の上の引き戻しとファイバーごとの関手空間：Kerodon Proposition 5.2.4.5（Tag 024R）、Remark 5.6.2.18（Tag 0271）
- 相対関手空間（切断・延長・cocartesian 切断）：Kerodon §4.1.4・§4.5

## C 単体集合と ∞ 圏/写像空間

**入るもの**：∞ 圏の二対象の間の写像空間の模型（区間模型、左・右 pinched、coslice の fiber）、模型の比較、合成の空間。

**入らないもの**：
- coherent 神経の写像空間（豊穣 Hom との比較、necklace）は「単体的圏と coherent 神経」へ
- dg 神経の写像空間は「dg 神経」へ
- 錐・余錐の空間は「極限と余極限」へ
- 太い slice・fat join は「結とスライス」へ
- lax 引き戻しは「H/lax 引き戻しと局所化不変量」へ
- モデル圏のホモトピー関数複体は「E/ホモトピー関数複体と分解」へ
- 点つきの写像空間は「基点付き空間」へ
- 充満忠実性は「関手単体集合と同値」へ

**小概念**：
- 両端固定の区間模型
- 写像空間の模型の比較
- 右 pinched 写像空間
- 合成（合成三角形の空間）
- 左 pinched 写像空間と coslice の fiber
- 内部 Hom の交換と円柱上の四角形の空間［足場］
- 𝒮 の中の合成三角形の族の空間［足場］

分割で残るもの：矢印の空間 Fun(Δ¹,C) の両端評価と F(x)→y の矢印の空間（今の「矢印の空間と lax 引き戻し」の lax 引き戻し以外）。

**文献**：
- 両端固定の区間模型：Kerodon §4.6.1（Tag 01J3）
- 写像空間の模型の比較：Kerodon §4.6.5（Tag 01KW）
- 右 pinched 写像空間：Kerodon §4.6.5（Tag 01KW）、HTT §1.2.2
- 合成（合成三角形の空間）：Kerodon §4.6.9
- 左 pinched 写像空間と coslice の fiber：Kerodon §4.6.5
- 𝒮 の中の合成三角形の族の空間：Kerodon 7.1（Tag 02H1）、Kerodon Proposition 7.1.8.7（Tag 06A5）

## C 単体集合と ∞ 圏/冪等完備（∞ 圏）

**入るもの**：∞ 圏の retract、coherent な冪等（N(Idem) からの図式）とその分裂、冪等完備性と冪等完備化。

**入らないもの**：
- 通常の圏の Karoubi 包・レトラクトは「Z/冪等完備（通常の圏）」へ
- 自由随伴 Adj とモナドの組合せ論は「自由随伴（HA §4.7 の組合せ論）」へ
- Ind 完備化は「空間・Cat∞・前層・Ind」へ
- Perf の冪等完備・Cat^perf は「H/lax 引き戻しと局所化不変量」へ

**小概念**：
- retract
- 冪等元と分裂の添字（Idem・Split）と coherent な冪等
- 冪等完備と冪等完備化
- 分裂の添字 N(Split) の filtration（交互列の段階）［足場］

**文献**：（reference の記載なし）

## C 単体集合と ∞ 圏/単体的圏と coherent 神経

**入るもの**：単体的豊穣圏と coherent 神経：simplicial thickening（Path と立方体）、coherent 神経の単体、豊穣 Hom と写像空間の比較、necklace と coherent resolution による Hom の計算。

**入らないもの**：
- 立方体の頂点・正規形・cubical 集合・Serre 鎖の立方体は「立方体の組合せ論」へ
- Kan 複体の単体的圏の coherent 神経 𝒮、QCat の coherent 神経 Cat∞ は「空間・Cat∞・前層・Ind」へ
- dg 神経との比較は「dg 神経」へ
- 豊穣圏の一般論（任意のモノイダル圏で豊穣）は「Z/豊穣圏」へ
- SSet の内部 Hom そのものは「単体集合（基本）」へ
- hammock 局所化の単体的圏は「局所化（Dwyer–Kan）」へ
- 豊穣随伴から ∞ 圏の随伴を作る定理は「随伴（∞ 圏）」へ

**小概念**：
- 単体的豊穣圏の円柱［足場］
- necklace から立方体・cubical 集合へ
- necklace の形と圏
- necklace の連結（wedge）
- simplicial thickening の Path と立方体
- 単体集合の中の necklace
- 旗による単体の解像（coherent resolution）
- 豊穣 Hom と coherent 神経の写像空間の比較
- coherent 神経の頂点・辺と通常の神経からの射
- coherent 神経の低次元単体の読み戻し［足場］

**文献**：
- simplicial thickening の Path と立方体：HTT 1.1.5.10
- 旗による単体の解像（coherent resolution）：Kerodon Construction 4.6.7.22（Tag 01LV）、Proposition 4.6.7.23、Example・Corollary 4.6.7 の周辺
- 豊穣 Hom と coherent 神経の写像空間の比較：HA 1.3.1.17、Kerodon §4.6.7–4.6.8（Tag 01LW）
- coherent 神経の頂点・辺と通常の神経からの射：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）
- simplicial thickening の Path と立方体：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR）
- 豊穣 Hom と coherent 神経の写像空間の比較：Kerodon Construction 4.6.7.3（Tag 01LD）、Kerodon 2.4（Tag 00JN）
- coherent 神経の低次元単体の読み戻し：Kerodon 2.4.3、5.5.4

## C 単体集合と ∞ 圏/単体集合（基本）

**入るもの**：単体圏 Δ、単体集合の面・退化、標準単体・境界・ホーン、部分複体、積、内部 Hom、極限・余極限、非退化単体と骨格、細分、反対、単体的対象・余単体的対象。

**入らないもの**：
- 単体的ホモトピー・Kan 複体・Kan ファイブレーションは「Kan 複体とホモトピー群」へ
- anodyne 射・リフト性・Kan–Quillen モデル構造は「E/単体的モデルと anodyne」へ
- Moore 複体・正規化・Dold–Kan は「B/単体的鎖・Dold–Kan・シャッフル」へ
- 準圏の条件・辺の合成は「準圏（基本）」、圏の神経は「神経」へ
- SSet で豊穣した圏は「単体的圏と coherent 神経」へ
- 結・スライスは「結とスライス」へ
- Fin の単調写像だけの補題は「Z/組合せと順序」へ
- 余単体的可換環のコホモロジーは「A/Čech 複体と被覆」へ

**小概念**：
- 単体集合値図式の商・関数複体と底つきの内ホーン［足場］
- ホーン
- 単体圏 Δ と単体の面・退化
- 単体的対象・余単体的対象・Čech 神経
- 反対単体集合と宇宙の持ち上げ
- 極限・余極限・要素の圏
- 標準単体と米田
- 積・柱・pushout-product
- 部分複体と境界
- 関数複体（内部 Hom）
- 非退化単体・骨格・切り詰め・細分

**文献**：
- 単体集合値図式の商・関数複体と底つきの内ホーン：Goerss–Jardine I §7・VIII §2（関数複体）
- ホーン：Kerodon 1.2.4
- 単体圏 Δ と単体の面・退化：Kerodon 1.1.1
- 単体的対象・余単体的対象・Čech 神経：Kerodon 1.1.1; Mathlib SimplicialObject
- 反対単体集合と宇宙の持ち上げ：Kerodon 1.4.2（反対）
- 標準単体と米田：Kerodon 1.1.2
- 積・柱・pushout-product：Kerodon 3.1.2; HTT 2.3.2
- 部分複体と境界：Kerodon 1.1.4
- 関数複体（内部 Hom）：Kerodon 1.5.3（Fun）, 2.4
- 非退化単体・骨格・切り詰め・細分：Kerodon 1.1.3–1.1.4, 3.3

## C 単体集合と ∞ 圏/基点付き空間

**入るもの**：基点付き対象と基点付き単体集合：smash 積、基点付き内部 Hom、球面・懸垂・ループ、path 空間と mapping path、fiber・cofiber、点つきの写像空間・持ち上げの空間。

**入らないもの**：
- スペクトルの水準のもの（構造射、Ω スペクトル、スペクトルの逐次余極限）は「G/Ω スペクトル（Bousfield–Friedlander）」へ
- 球面の対称列は「G/対称列」へ
- ∞ 圏 𝒮_* と普遍左ファイブレーションは「空間・Cat∞・前層・Ind」へ
- 基点なしのホモトピー群・長完全列は「Kan 複体とホモトピー群」へ
- Eilenberg–MacLane 空間は G（スペクトル）へ

**小概念**：
- path 空間と mapping path
- 基点付き内部 Hom
- 基点付き対象と基点付き単体集合（基本）
- 球面・懸垂・ループ
- 直積と smash 積
- smash 積の pushout-product の角［足場］

**文献**：
- path 空間と mapping path：Goerss–Jardine I §7
- 基点付き内部 Hom：BF 1978 §2、HTT A.3.3（prePointed）
- 球面・懸垂・ループ：HA §1.4.2、BF 1978 §2

## C 単体集合と ∞ 圏/局所化（Dwyer–Kan）

**入るもの**：相対圏の単体的局所化：向き付き語と zigzag、hammock 局所化、自由解像による局所化、両側 Grothendieck 構成、亜群化、∞ 圏の局所化の普遍性、モデル圏の局所化との比較定理。

**入らないもの**：
- 通常の圏の局所化と射の類（MorphismProperty）は「Z/局所化と射の類」へ
- frame・余単体的分解・ホモトピー関数複体そのものは「E/ホモトピー関数複体と分解」へ
- 表示可能 ∞ 圏の局所対象と Bousfield 局所化は「表示可能 ∞ 圏とフィルター」へ
- 複体の strict な図式の ∞ 局所化は「D/導来 ∞ 圏」へ
- 余錐の貼り合わせ（部分余極限）は「極限と余極限」へ
- Verdier 商は「D/Verdier 列」へ

**小概念**：
- hammock 局所化（Hom 単体集合と単体的豊穣圏）
- zigzag の圏と関手性
- モデル圏の局所化との比較（三本矢と frame）
- 亜群化
- 向き付き語の圏
- 局所化の普遍性と反射的部分圏
- 自由解像による単体的局所化
- 二方向 Grothendieck 構成と zigzag の第一列の分解［足場］
- 自由圏の hammock の計算（生成矢での切断・木の縮約）［足場］

**文献**：
- hammock 局所化（Hom 単体集合と単体的豊穣圏）：Dwyer–Kan、Kerodon 6.3（Tag 01M4）
- zigzag の圏と関手性：Kerodon 6.3（Tag 01M4）
- モデル圏の局所化との比較（三本矢と frame）：Dwyer–Kan §7、Low 命題 3.7
- 亜群化：Kerodon 6.3.1
- 向き付き語の圏：Dwyer–Kan §4.2・§4.4、Kerodon 6.3（Tag 01M4）
- 自由解像による単体的局所化：Dwyer–Kan（命題 2.2）、HTT 1.1.5
- 二方向 Grothendieck 構成と zigzag の第一列の分解：Dwyer–Kan, Calculating simplicial localizations §9–10
- 自由圏の hammock の計算（生成矢での切断・木の縮約）：Dwyer–Kan 比較補題 2.3、Kerodon 6.3（Tag 01M4）
- モデル圏の局所化との比較（三本矢と frame）：Dwyer–Kan Function complexes §4；Thomason（Grothendieck 構成のホモトピー余極限）
- 自由解像による単体的局所化：Dwyer–Kan Simplicial localizations §2（自由単体的分解）

## C 単体集合と ∞ 圏/極限と余極限

**入るもの**：∞ 圏の錐・余錐、極限・余極限、始対象・終対象、引き戻し・押し出しの四角形、Kan 拡張、錐・余錐の空間、重み付き切断とホモトピー極限、空間値の図式の極限、単体集合のホモトピー引き戻し・押し出し。

**入らないもの**：
- 零対象・cofiber・安定性を使う四角形、完全関手は「D/安定 ∞ 圏」へ
- 複体の dg 神経での fiber 四角形・cofiber 四角形、複体の strict な図式の ∞ 局所化は「D/導来 ∞ 圏」へ
- 層条件が主語のものは「∞ 層」へ
- 相対関手空間は「ファイブレーションと straightening」へ
- filtered 余極限と有限極限の交換は「表示可能 ∞ 圏とフィルター」へ
- Cat∞ の中の引き戻しは「空間・Cat∞・前層・Ind」へ
- モデル圏のホモトピー余極限・重みつき実現は「E/図式のモデル構造とホモトピー余極限」へ
- 通常の圏の極限は「Z/圏・関手・極限」へ
- slice・coslice の構成は「結とスライス」へ
- coherent bar 構成は「D/coherent bar 構成」へ

**小概念**：
- 集合値前層で重み付けた切断
- 錐・余錐の空間
- Kan 拡張
- simplicial replacement と strict な自然変換の空間
- strict な図式・通常の圏の極限との比較
- ホモトピー引き戻し・押し出しと塔の極限（単体集合）
- 始対象・終対象と相対余極限
- 引き戻し・押し出しの四角形
- 空間値の図式の極限と切断空間
- 重み付き切断と Bousfield–Kan のホモトピー極限
- 錐・余錐と極限・余極限
- 錐・余錐の輸送と変換［足場］
- path 置換によるホモトピー引き戻しの模型［足場］

**文献**：
- 集合値前層で重み付けた切断：HTT 5.1.5.6、6.2.2.6、Kerodon §7.1（Tag 02H1）
- 錐・余錐の空間：Kerodon §4.6.4（Tag 01KW 付近）、HTT §4.2.1
- simplicial replacement と strict な自然変換の空間：Kerodon Construction 5.3.2.1（Tag 035V）
- strict な図式・通常の圏の極限との比較：Kerodon 7.5.4.6（Tag 03BB）、HTT 4.2.4.1
- 始対象・終対象と相対余極限：Kerodon 7.1（Tag 02H1）
- 引き戻し・押し出しの四角形：HTT §1.2.13、Kerodon §7.6.2
- 重み付き切断と Bousfield–Kan のホモトピー極限：Kerodon 7.5.3（Tag 03AP）、HA 1.2.4
- 錐・余錐の輸送と変換：Kerodon 7.1
- path 置換によるホモトピー引き戻しの模型：（ホモトピー引き戻しの具体模型）

## C 単体集合と ∞ 圏/準圏（基本）

**入るもの**：準圏の定義と基本：内ホーンの充填、辺と 2 単体による合成、内ファイブレーション、ホモトピー圏。

**入らないもの**：
- 同型・同値・core・関手単体集合は「関手単体集合と同値」へ
- 写像空間は「写像空間」へ
- 圏の神経は「神経」へ
- ホーン・標準単体そのものは「単体集合（基本）」へ

**小概念**：
- 辺・合成と準圏の条件

**文献**：
- 辺・合成と準圏の条件：Kerodon 1.3, 1.4

## C 単体集合と ∞ 圏/神経

**入るもの**：通常の圏の神経：単体、関手性、反対・宇宙の持ち上げとの両立、神経の単体の圏。

**入らないもの**：
- coherent 神経は「単体的圏と coherent 神経」、dg 神経は「dg 神経」へ
- 通常の圏のねじれ矢と神経のねじれ矢の比較は「ねじれ矢と edgewise subdivision」へ
- ComposableArrows・半順序の圏だけの補題は「Z/圏・関手・極限」へ
- 神経の上のファイブレーション（weighted nerve）は「ファイブレーションと straightening」へ

**小概念**：
- 神経の単体の圏の上の整合的な族［足場・止めた経路］

**文献**：
- 神経の単体の圏の上の整合的な族：計画書 §396（ファイル冒頭）

## C 単体集合と ∞ 圏/空間・Cat∞・前層・Ind

**入るもの**：空間の ∞ 圏 𝒮 と Cat∞（coherent 神経としての定義、Kan 値・準圏値の図式からの写像）、𝒮_*、前層の ∞ 圏、米田埋め込み、密度、Ind 完備化、P_Σ。

**入らないもの**：
- coherent 神経の一般論は「単体的圏と coherent 神経」へ
- straightening・unstraightening は「ファイブレーションと straightening」へ
- 層は「∞ 層」へ
- accessible・表示可能・Pr^L は「表示可能 ∞ 圏とフィルター」へ
- 𝒮 の中の極限の計算は「極限と余極限」へ
- dg 加群から 𝒮 への関手は「D/導来 ∞ 圏」へ
- 基点付き単体集合（模型の水準）は「基点付き空間」へ
- 冪等完備化 Idem(C) は「冪等完備（∞ 圏）」へ

**小概念**：
- Kan 値の図式と空間の ∞ 圏への写像
- 集合値前層の離散埋め込みと Yoneda
- 準圏値の豊穣関手とその図式［足場］
- Cat∞ と QCat
- Cat∞ の引き戻し
- Ind 完備化
- P_Σ（非アーベル導来圏）
- 前層の ∞ 圏
- 前層の密度（表現可能前層の余極限）
- 𝒮_*（基点付き空間の ∞ 圏）と普遍左ファイブレーション
- 空間の ∞ 圏 𝒮
- 米田埋め込み

**文献**：
- Kan 値の図式と空間の ∞ 圏への写像：Kerodon §5.5（𝒮 の定義）
- 集合値前層の離散埋め込みと Yoneda：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）
- Cat∞ と QCat：Kerodon 5.5.4
- Cat∞ の引き戻し：Kerodon 7.1、HTT 3.3.3
- Ind 完備化：HTT 5.3.5
- P_Σ（非アーベル導来圏）：HTT 5.5.8.8
- 前層の ∞ 圏：HTT 5.1.0.1、5.1.2
- 前層の密度（表現可能前層の余極限）：HTT 5.1.5.3
- 𝒮_*（基点付き空間の ∞ 圏）と普遍左ファイブレーション：Kerodon 5.5.3、5.6.3
- 空間の ∞ 圏 𝒮：Kerodon 5.5.1（Construction 5.5.1.1）
- 米田埋め込み：Kerodon 8.3.3、HTT 5.1.3

## C 単体集合と ∞ 圏/立方体の組合せ論

**入るもの**：立方体の組合せ論：立方体の頂点と頂点写像（面・退化・connection）、正規形、cubical 集合、Serre 鎖の立方体と cubical Λ。

**入らないもの**：
- coherent 神経の Hom としての立方体（Path の半順序の神経）と necklace は「単体的圏と coherent 神経」へ
- 単体集合の積 Δ¹×…×Δ¹ の一般の補題は「単体集合（基本）」へ
- 単体的鎖・シャッフルは「B/単体的鎖・Dold–Kan・シャッフル」へ
- S 構成そのものは「H/S 構成と K スペクトル」へ

**小概念**：
- 立方体の頂点写像と connection

（今ここへ来る小概念は「立方体の頂点写像と connection」と、読んで移された Serre 鎖の立方体の定義。cubical 集合と Serre 鎖の小概念は定義ごとの移し替えのときに立てる。）

**文献**：（reference の記載なし）

## C 単体集合と ∞ 圏/結とスライス

**入るもの**：単体集合の結（join）、fat join、relative join、スライスと余スライス、相対 coslice、太い slice。

**入らないもの**：
- 錐・余錐と極限の普遍性は「極限と余極限」へ
- 準圏の随伴（unit comma など）は「随伴（∞ 圏）」へ
- coslice の fiber としての写像空間は「写像空間」へ
- 通常の圏の Over・Under・comma は「Z/圏・関手・極限」へ
- 基点の追加（adjoin）は「基点付き空間」へ

**小概念**：
- fat join と結の比較
- relative join
- スライスと余スライス
- 相対 coslice と coslice の辺の族
- 結の構成
- 結の計算（標準単体・部分複体・結合・反転）
- 標準単体の頂点と始点を加える順序写像［足場］

**文献**：
- fat join と結の比較：Kerodon §4.6.2 (Tag 01HM), §4.6.6 (Tag 04HY)；HTT §4.2.1
- relative join：Kerodon §5.2.3–5.2.4 (Tag 0241 付近), Lemma 3.1.2.1
- スライスと余スライス：HTT §1.2.9, §2.1.2；Kerodon §4.3.5 (Tag 016Y)
- 相対 coslice と coslice の辺の族：HTT Prop 2.1.2.1；Kerodon §4.3.6, Prop 5.1.1.14 (Tag 01TF)
- 結の構成：HTT §1.2.8；Kerodon §4.3.3 (Tag 016K)
- 結の計算（標準単体・部分複体・結合・反転）：HTT §1.2.8, Lemma 2.1.2.3；Kerodon §4.3.3, §4.3.6
- 標準単体の頂点と始点を加える順序写像：HTT §1.2.8

## C 単体集合と ∞ 圏/自由随伴（HA §4.7 の組合せ論）

**入るもの**：自由随伴 Adj（二対象の 2 圏）の Hom 圏と水平合成、各次数の自由性、原子的な胞と充填条件（Riehl–Verity）、自己関手の空間。

**入らないもの**：
- 準圏の随伴の定義と判定は「随伴（∞ 圏）」へ
- 冪等と retract は「冪等完備（∞ 圏）」へ
- 有限順序の単調射だけの補題は「Z/組合せと順序」へ
- 通常の圏のモナド・随伴は「Z/圏・関手・極限」へ

**小概念**：
- Adj の原子的な胞の親と充填条件
- Adj の各次数の自由性（原子的な射・水平分解・切れ目）
- 自己関手の空間
- 自由随伴 Adj の Hom 圏と水平合成
- Adj の Hom の有限単調射による表示（順序和・区間双対・貼り合わせ）［足場］

**文献**：
- Adj の原子的な胞の親と充填条件：Riehl–Verity Definition 4.1.1、Lemma 4.1.4、§4.1、Proposition 4.2.15
- Adj の各次数の自由性（原子的な射・水平分解・切れ目）：Riehl–Verity Definition 2.1.4、Proposition 3.1.10、Example 3.1.11
- 自己関手の空間：HA §4.7.2–§4.7.3
- 自由随伴 Adj の Hom 圏と水平合成：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8
- Adj の Hom の有限単調射による表示（順序和・区間双対・貼り合わせ）：Riehl–Verity Remark 3.3.8、Proposition 4.2.15

## C 単体集合と ∞ 圏/表示可能 ∞ 圏とフィルター

**入るもの**：フィルター ∞ 圏、filtered 余極限と有限極限の交換、compact 対象、accessible・表示可能 ∞ 圏、Pr^L・Pr^R、局所対象と局所化。

**入らないもの**：
- Ind 完備化・P_Σ・前層は「空間・Cat∞・前層・Ind」へ
- 随伴の単位の空間は「随伴（∞ 圏）」へ
- κ 小さい単体集合などのサイズの条件は「サイズの条件」へ
- path 置換による引き戻しの模型は「極限と余極限」へ
- 安定表示可能 ∞ 圏は「D/安定 ∞ 圏」へ
- 通常の圏の局所表示可能・到達可能は「Z/圏・関手・極限」へ

**小概念**：
- Pr^L と Pr^R
- compact 対象による表示と濃度の取り替え
- フィルター ∞ 圏
- フィルター余極限と有限極限の交換
- 局所対象と局所化
- 表示可能 ∞ 圏の定義
- 分類図式・end・関手の射の読み替え［足場］
- ℕ の神経の spine と部分列［足場］

**文献**：
- Pr^L と Pr^R：HTT 5.5.3.1
- compact 対象による表示と濃度の取り替え：HTT 5.4.2、5.4.7
- フィルター ∞ 圏：HTT 5.3.1、Kerodon 9.1
- フィルター余極限と有限極限の交換：HTT 5.3.3.3
- 局所対象と局所化：HTT 5.5.4.1、5.5.4.15
- 表示可能 ∞ 圏の定義：HTT 5.5.0.1
- 分類図式・end・関手の射の読み替え：HTT 2.2、5.1
- ℕ の神経の spine と部分列：HTT 4.2.3（cofinality の道具）

## C 単体集合と ∞ 圏/関手単体集合と同値

**入るもの**：関手単体集合 Fun(X,Y) とそのホモトピー圏 h Fun（自然変換、可逆二胞体）、同型と ∞ 圏の同値、core、可逆 path と path 置換、充満忠実と本質的全射。

**入らないもの**：
- 相対関手空間 Fun_{/B} と切断は「ファイブレーションと straightening」へ
- SSet の内部 Hom の基本（ihom・curry）は「単体集合（基本）」へ
- 写像空間の模型は「写像空間」へ
- 随伴は「随伴（∞ 圏）」へ
- Cat∞ の中の引き戻しの錐は「空間・Cat∞・前層・Ind」へ
- dg 双加群が誘導する h Fun の射は「B/双加群とテンソル」へ
- Kan 置換は「Kan 複体とホモトピー群」へ

**小概念**：
- 関手空間の辺・同型・prism の表示［足場］
- core（最大部分 Kan 複体）
- fiber ごとの関手の全空間
- ∞ 圏のホモトピー引き戻し
- 充満忠実と本質的全射
- 可逆 path の空間と path 置換
- 可逆な区間と円柱
- 同型と ∞ 圏の同値
- 自然変換と可逆二胞体（h Fun）
- 関手単体集合の頂点・評価・転置

**文献**：
- 関手空間の辺・同型・prism の表示：Kerodon Corollary 5.6.0.6（Tag 028T）、Corollary 5.6.5.15（Tag 0296）
- core（最大部分 Kan 複体）：Kerodon §4.4.3
- ∞ 圏のホモトピー引き戻し：Kerodon §4.5.2
- 充満忠実と本質的全射：Kerodon §4.6.2
- 可逆 path の空間と path 置換：Kerodon §4.5.3
- 可逆な区間と円柱：Kerodon §4.5.3・§4.6.2
- 同型と ∞ 圏の同値：HTT §1.2.4、Kerodon §4.5.1（Tag 01DE）
- 自然変換と可逆二胞体（h Fun）：Kerodon §4.5.1
- 関手単体集合の頂点・評価・転置：Kerodon §1.5.3、§4.5

## C 単体集合と ∞ 圏/随伴（∞ 圏）

**入るもの**：準圏の随伴：h Fun の 2 圏での定義、単位・余単位、unit comma と普遍矢印、各点の単位条件と写像空間による判定、随伴の単位の空間（Pr^L と Pr^R の双対）、豊穣随伴からの随伴。

**入らないもの**：
- 自由随伴 Adj の組合せ論は「自由随伴（HA §4.7 の組合せ論）」へ
- 区間写像空間の操作（前合成・後合成）は「写像空間」へ
- Pr^L・Pr^R の定義は「表示可能 ∞ 圏とフィルター」へ
- Kan 拡張は「極限と余極限」へ
- 通常の圏の随伴は「Z/圏・関手・極限」、Quillen 随伴は「E/Quillen 関手と生成」へ

**小概念**：
- 随伴の単位の空間（Pr^L と Pr^R の双対）

**文献**：
- 随伴の単位の空間（Pr^L と Pr^R の双対）：HTT 5.5.3.4、5.2.6
