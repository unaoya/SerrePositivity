# K-L2（比較定理）

## 所有するもの・借りるもの

本レーンは単体集合の整数ホモロジー H_* を所有する。
正規化 chain 複体と alternating face map complex の比較も所有する。
単体的モノイドの群完備化と分類空間を所有する。
完全正規部分群に関する plus 構成を所有する。
Dold–Kan の環への延長と ĜL の比較への適用を所有する。
Waldhausen の古典的比較から ∞-S• への移植を所有する。
π_n の定義・群構造・長完全列は K-L9 から借りる。
π_n が届くまでは具体的な数学的データを明示的な引数とする。
pro 圏と pro 同型の実装は K-L6 から借りる。
∞-S• と連結 K の構成は K-L1 から借りる。
Bass 基本定理と負の次数への延長は K-L3 から借りる。
K0 界面の正確な Lean 型は S1 で確定する。
K0 界面の未供給の性質を本レーンの定理として公開しない。

## 1. 正本・配置・規約

作成日：2026-10-18。
チャットのレーン名：K-L2（比較定理）。
正本は [KST 経路](../k-theory-kst-route.md) と [基盤計画](../foundations.md)。
KST 経路の §2.5 P1、§4 D2、§5 K2、§10-5、§13 を参照する。
決定の衝突は foundations.md と KST 経路 §13 の優先順位で読む。
Lean の namespace は `SerrePositivity.KST.Comparison` とする。
Lean の所有ディレクトリは `SerrePositivity/KST/Comparison/` とする。
集約ファイルは `SerrePositivity/KST/Comparison.lean` とする。
監査ファイルは `scripts/audit_kst_comparison.lean` とする。
ルートへの変更は `public import SerrePositivity.KST.Comparison` の一行だけとする。
既存の KTheory、DifferentialGraded、Spectra は読み取り専用とする。
既存の InfinityCategories、HomotopicalAlgebra も読み取り専用とする。
他レーンの計画・監査ファイルは編集しない。
実施の経緯はコミットメッセージに書く。
本計画の現在地・宣言表は追記日誌ではなく現況に書き換える。
引用を説明に書くことと、引用を Lean の未証明入力にすることを区別する。
追加公理、sorry、原典の定理を仮定した存在証明は導入しない。
docstring は概要／方針／規約／使われ方を日本語で記す。

## 2. 目標と完成条件

最終目標は KST Proposition 2.15 の比較を完全に証明することである。
比較の形は Ω^∞ K(A) ≃ K₀(π₀A) × BĜL(A)⁺ である。
対象は connective な結合的単位的 dg 代数とする。
可換係数の場合だけに制限して非可換係数の必要性を隠さない。
KST Theorem 2.16 の次数 0 と 1 の比較を導く。
負の次数の比較は K-L3 の Bass 基本定理に接続する。
KST Lemma 2.13 の分類空間のホモトピー群を証明する。
この補題の π_n の基盤そのものは K-L9 の所有とする。
plus 構成の存在とその性質を区別して証明する。
群完備化の存在とホモロジー比較を区別して証明する。
ホモロジーを任意の関手として仮定して完成扱いにしない。
正規化複体と非正規化複体の準同型も証明対象に含める。
∞-S• の比較を古典的 Waldhausen 圏の比較で置換しない。
両者を接続する補題の仮定と出力を明記する。
標準三公理だけへの依存を保存単位ごとに確認する。
完成は全工程の実体と比較写像の自然性が供給された時点とする。

## 3. 原典対応

| 対象 | 原典 | 本レーンでの用途 |
| --- | --- | --- |
| Γ の環構造 | Schwede–Shipley 2003 §2.3、式 (2.8)–(2.9) | Alexander–Whitney 積 |
| Γ の忠実充満性 | 同 Proposition 2.13 | 正規化との整合 |
| ĜL_n | KST §2.2、式 (2.2) | π₀ の単元成分の逆像 |
| 安定 ĜL | KST 式 (2.3) | rank に関する安定化 |
| BĜL の π_n | KST Lemma 2.13 | 分類空間との比較 |
| 分類空間の群完備化 | Segal 1974 Proposition 1.5 | 群状モノイドへの適用 |
| plus と K₁ | KST Lemma 2.14 | π₁ の商 |
| K の比較 | KST Proposition 2.15 | 主比較定理 |
| 低次数の不変性 | KST Theorem 2.16 | 次数 0、1 |
| 球状対象 | Waldhausen LNM 1126 Theorem 1.7.1 | セル濾過と Hurewicz |
| 比較定理の部品 | Waldhausen §1.8、Theorem 1.8.1 | S• との比較 |
| strict cofinality | Waldhausen Proposition 1.5.9 | 自由対象からの比較 |
| GL と有限自由対象 | Waldhausen Proposition 2.3.5 | 分類空間の同定 |
| 主比較 | Waldhausen Theorem 2.3.2 | ∞-S• への移植 |
| 古典的 K₁ | Weibel K-book III | 離散環の比較先 |
| plus の原典番号 | Weibel K-book IV.1 | acyclic map の構成 |

KST は arXiv:1611.08466v4 を用いる。
KST §2.2 の該当箇所は本文頁 9–10 にある。
Schwede–Shipley は Equivalences of monoidal model categories を用いる。
掲載は Algebraic & Geometric Topology 3 (2003), 287–334 である。
その Proposition 2.13 は単体的環 ΓA を扱う。
同命題は ĜL が各次数で群であるとは述べない。
Segal 1974 Proposition 1.5、本文頁 296–297 を照合した。
A₀ の可縮性と Segal 写像 A_n → A₁^n のホモトピー同値が仮定。
結論は A₁ → Ω|A| がホモトピー同値となることと homotopy inverse の存在の同値。
証明は path-space PA と Proposition 1.6 の homotopy-cartesian な実現の比較による。
単体的模型では二重単体的 bar の対角を用い、この比較部分を別途証明する。
Waldhausen の原典本文の精査は §10-5 の記録に反映する。
Weibel III と IV.1 の用途を混同しない。

## 4. 次数と connective の読み替え

リポジトリの dg 代数は cochain 規約で読む。
connective は H^i(A) = 0 for i > 0 を意味する。
chain 側は C_n = A^(−n) とする。
したがって H_n(C) は H^(−n)(A) に対応する。
π₀A の比較先は H⁰(A) である。
H⁰ の消滅や空間の連結性を connective の定義に加えない。
単に connective な Z 次数 dg 代数は項ごとに非正とは限らない。
Γ の入力には非負 chain 複体が必要である。
一般の A には乗法を保つ good truncation τ≤0 を用いる。
truncation の零次項は Z⁰(A) とする。
負次数項は元の A の項とする。
truncation の包含が擬同型になることを connective 性から示す。
乗法と単位が truncation に制限することを証明する。
厳密に非正次数の入力と一般の connective 入力を区別する。
次数反転の differential の型と符号は個別に確認する。
cochain の Leibniz 則を chain の Leibniz 則へ輸送する。
Γ の乗法は AW に由来する結合的乗法である。
AW は対称でないので可換性を自動的に付けない。

## 5. L2a の採用済み設計：群と群状モノイド

状態：2026-10-18 にユーザーが変更を採用。正本 §13-10 に従って実装する。
依頼の「単体的群として定義する」は式 (2.2) と両立しない。
正しい対象は π₀ が群である単体的モノイドである。
英語の原典の用語は group-like simplicial monoid である。
各次数の乗法には必ずしも逆元がない。
原典 KST §4.3 も群と群状モノイドの違いを明記している。
この違いは単なる Lean の型クラスの選択ではない。
指定された乗法について群の公理が数学的に成立しない。
採用した設計は ĜL を単体的モノイドとし、π₀ に群構造を証明すること。
L2b の分類空間と群完備化もこの対象を受け取る。
各次数の単元群 GL_n((ΓA)_q) に置き換えない。
その置き換えは π₀ で可逆な全成分の逆像と一致しない。
別の単体的群模型を採るなら比較同値が新たな証明対象になる。
この設計は KST の式 (2.2) 自体を維持するものである。
正本ファイルの D2 を本レーンで無断修正しない。

### 5.1 具体的な反例

R = ℤ[t] とする。
A⁰ = R、A^(−1) = R e とする。
その他の次数は零とする。
e は t と可換で e² = 0 とする。
d(e) = t とし、R 上の differential は零とする。
Leibniz 則で d(e²) = te − et = 0 となる。
したがってこれは結合的単位的 dg 代数である。
正次数の項は零なので connective である。
H⁰(A) = R/(t) ≅ ℤ である。
SS03 の Γ では (ΓA)_0 = A⁰ = R である。
rank 1 の ĜL の零次単体は R → ℤ による単元の逆像である。
1+t は t = 0 で 1 になるのでこの逆像に属する。
一方 1+t は R で単元ではない。
もし (1+t)q = 1 なら t = −1 の評価で 0 = 1 が従う。
したがってこの逆像の乗法は群の乗法にならない。
この評価による反証は次数計算を必要としない。

### 5.2 Lean 検証の範囲

反例の代数部分を DoldKanGL.lean に置く。
環準同型による単元の逆像が部分モノイドになることを定義する。
ℤ[X] → ℤ の零点評価をその具体例とする。
1+X が逆像に属することを証明する。
1+X が ℤ[X] の単元でないことを証明する。
その逆像の 1+X に右逆元が存在しないことを証明する。
この段階では dg 代数 A と ΓA の実装を完了扱いにしない。
反例の dg 代数としての説明は紙上の検証として区別する。
代数部分の Lean 証明と原典の定義が変更提案の根拠である。

## 6. L2a の工程

第一に dg 代数を既存の DGCategory R PUnit（一対象 dg 圏）として入力する。
演算と法則を別構造に重複させない。Γ の積は通常順の dg 合成により定める。
第二に good truncation と次数反転を接続する。
第三に Dold–Kan Γ の加法的対象を選ぶ。
Mathlib の Γ と既存 γ1.5 の chain map 模型を比較する。
既存の γ1.5 ファイルは読み取り専用のまま利用する。
AW の chain map、単位、余結合性を用意する。
ΓA の積を SS03 式 (2.9) に従って定義する。
結合律と単位律を証明する。
単体作用と積の可換性を証明する。
π₀ の環と H⁰(A) の環との同型を証明する。
行列環から π₀ の行列環への写像を構成する。
GL_n(π₀A) の逆像を部分モノイドとして定義する。
face と degeneracy が逆像を保つことを証明する。
π₀ の群構造は K-L9 の界面に対して接続する。
rank の安定化を定義して ĜL(A) を作る。
式 (2.3) の引き戻しとの比較を証明する。
L2a の完了条件は ΓA、ĜL_n、安定 ĜL と自然性である。
代数的反例の検証だけでは L2a は完了しない。

## 7. L2b：群完備化

ファイルは GroupCompletion.lean とする。
入力は一般の単体的モノイドとする。
分類空間の bar 構成を明示する。
単体的作用の二重単体的 bar 構成を明示する。
対角と実現の比較で用いる補題を列挙する。
群状性の仮定が使われる箇所を分離する。
Segal–McDuff の群完備化写像を構成する。
必要な可換性・作用条件を定理の仮定に明示する。
任意のモノイドで無条件のホモロジー同型とは主張しない。
Segal Proposition 1.5 の適用条件を原文で確認する。
KST Lemma 2.13 への特殊化を証明する。
π_i(BĜL) と π_(i−1)(ĜL) の比較を接続する。
i = 1 と i > 1 の群の種類を区別する。
π₀(ĜL) と GL(π₀A) の同型を用いる。
高次では行列加法群との比較を用いる。
pro 系の自然性は K-L6 に渡せる形で公開する。
pro 圏そのものは本ファイルに再実装しない。

Segal Proposition 1.6（本文 pp.296–298）の移植は次の順序とする。
各単体作用の四角形の homotopy-cartesian 性を証明する。
正則 bar の行の積座標では、これは前置ラベルによる平行移動の比較となる。
この前段の補題では単体上の元の族を零頂点へ実収縮し、定数の平行移動へ比較する。
一般のパラメータへは共有 `CellularNaturalComparison` の骨格帰納を元の族付きに拡張する。
このセル降下の証明経路を原典の位相的な作用の議論から区別して記録する。
ここでも anodyne 局所化関手が余極限を保存するとは仮定しない。
原典は fat realization の骨格を double mapping cylinder で接合する。
その帰納の要は Lemma 1.7 のホモトピー引き戻しの貼り合わせである。
無限骨格への移行は Lemma 1.8 の telescope による。
本実装は二重単体集合の対角模型を使うので、対応する骨格・貼り合わせ・列極限の比較を証明する。
既存の `DiagonalLocalizedEquivalence.localized_diagonal_map` は行ごとの局所化同型の保存である。
これだけからホモトピー引き戻しの保存を結論しない。
基底付きの比較（右射を Kan fibration に置換した引き戻しへの標準射）を明示する。
Lemma 1.7・1.8 や Proposition 1.6 の結論そのものを入力構造体の仮定にしない。
全空間の収縮、厳密ファイバーの同型、標準ループ族との一致は既に実装済みである。

引き戻しと貼り合わせを接続する補助命題は、次の文言で確認する。
Kan fibration p:E→Δ[n] に沿う horn 包含の引き戻しは anodyne 局所化で同型となる。
この段階では strong anodyne 性までは主張しない。
組合せ的な証明方針：k を horn の添字とし、u(x)=min(x,k) とする。
u≤id と u≤const(k) による二つの単体的ホモトピーは、horn を保つ。
実際、新しく現れ得る頂点は k のみであり、元の単体が欠く j≠k は依然欠く。
区間端点の anodyne 性を使ってこれらを p に沿って持ち上げる。
基底のホモトピーが horn を保つため、その持ち上げは自動的に horn の逆像を保つ。
部分対象上の指定を別に保つ必要がある場合の pushout-product による相対延長も証明した。
終点は k 上のファイバーへ入り、そのファイバーは horn の逆像に含まれる。
全空間と逆像の双方で恒等写像とのホモトピーの zigzag を得て局所化同型を証明する。
一般の anodyne 射への拡張はスライスの積を取って忘れる左随伴を用いる。
スライスを前層圏と同値にして閉構造を移す。宇宙の整合には ULiftHom を使う。
局所化可逆な単射の既存の左持ち上げクラスによる特徴付けを借りる。
右随伴がその右テスト射をスライス内の Kan fibration に送ることを horn ごとに確認する。
その確認に上記の horn の逆像の局所化同型を使い、随伴で左持ち上げ性を移す。
これにより局所化関手の余極限保存を仮定せずに anodyne 射の比較へ進む。
Kan 基底に限れば、右随伴は Kan 複体を Kan な全空間に送る。
局所化可逆な単射は Kan 基底上の Kan fibration に左持ち上げ性を持つ。
全空間へ延長した後、基底への合成を相対ホモトピーで直して示す。
さらに単射・全単射的右持ち上げ性の分解を使い、Kan 基底上の任意の局所化同型の
Kan 引き戻しの可逆性を証明する。非 Kan 基底への拡張は別の未完了の項目である。
Kan 基底上で両方の構造射が Kan fibration の場合、左の任意の射による引き戻しも可逆となる。
左射を anodyne–Kan 分解し、二つの縦比較と可換四角形で一般の左射へ戻す。
これにより、固定した Kan 基底上のホモトピー引き戻し模型は左右両入力の局所化同型で不変となる。
これは Segal Proposition 1.6 の対角模型の補助であり、原典の fat realization の経路とは異なる。
非 Kan 基底の比較を進める補助として、有限極限と両立する Kan 置換 Ex∞ を構成する。
Mathlib の `SSet.sd`、`SSet.ex`、`sdExAdjunction` を使う。
最終頂点写像 sd(Δ[n])→Δ[n] を有限鎖の最大元で定め、自然変換 id→ex を得る。
その反復の順序余極限を Ex∞ とする。
有限極限保存は各 ex の右随伴性と型の filtered colimit の有限極限との交換から証明する。
Kan 性、単位の anodyne 性、fibration 保存は別々の未証明項目として管理する。
Moss Definition 23 の j_n^k は、有限鎖の最大元 m が k 以下なら元の集合を保ち、
m>k なら初期区間 [0,m] に置き換える単調写像として実装する。
これは原典の singleton 上の式を binary join で延長したものと一致する。
最大元を保つこと、j_n^n=id、j_n^0 が最終頂点と初期区間の合成であること、
k≤l のとき j_n^k∘j_n^l=j_n^k、冪等性を順に証明する。
Ex の単体の固定点による有限の複雑度フィルターを作り、regular pairing の前段とする。
Moss Definition 25 の r_n^k は、まず通常の codegeneracy σ^k による像を取り、
元の集合が頂点 k+1 を含む場合だけ初期区間 [0,k] を加える作用素として実装する。
これは原典の singleton 上の式の join による延長である。
Lemma 26 の式 (1) は、δ^{k+1} の像が k+1 を含まず、σ^k∘δ^{k+1}=id となることから示す。
他の面・退化との式、pairing の全単射・非退化性・正則性は別に証明する。
Lemma 26 (5) は、閾値を超える最大元の像を後の作用素が初期区間へ送る吸収則で示す。
Lemma 27 の一意性は、次の形で単体ごとの写像として証明する。
Ex(X)_n の単体 σ を、最小の複雑度 k で r_n^k に前合成した (n+1)-単体へ送る。
式 (4) からその像の複雑度は k 以下であり、式 (5) から任意の面の複雑度も k 以下となる。
指定した面は式 (1) で σ に戻るので、異なる表示の最小閾値は互いに以下で一致する。
同じ指定面を取って元の単体も一致し、この単体ごとの対応は単射となる。
この段階では対応先の非退化性と型 II の条件を主張しない。
Lemma 26 (7) では、先に未切断の強い式 r_n^k∘r_{n+1}^k=r_n^k∘sd(σ^{k+1}) を検証する。
singleton では頂点 k+1 と k+2 が初期区間 [0,k] に送られ、他の頂点では通常の
退化の恒等式に帰着する。和集合保存により任意の有限鎖へ拡張する。
原典の式 (7) はこの等式に j_n^k を後合成して得る。
証明後、最小閾値での拡張を二度行うと退化単体となることを示し、Lemma 28 へ接続する。
Lemma 26 (2) は、前側の面 δ^i（i≤k）の後に r_n^k と j_n^k を適用する作用素 F で示す。
入力集合の最大元 m≥k の場合、singleton {m} の像は初期区間 [0,m] であり、
F の単調性と最大元の保存から任意の入力集合の像も [0,m] に等しい。
前の j_n^{k-1} が入力を変える場合には m≥k であるため、双方の像が一致する。
この最大元による証明経路を、原典の singleton と join の直接計算から区別する。
原典の対応は Moss 2020 §3 Theorem 22、Corollary 30、Proposition 31・32 とする。
ここに原典を書いたことを、これらの Lean 証明が存在することとは扱わない。
Segal の位相的 fat realization の証明から、この組合せ的な補助構成を経る点を区別する。
既に定義した bar、標準群完備化写像、ホモトピー引き戻し模型の界面は変更しない。
Lemma 26 (8)・(9) は、j_n^k∘r_n^k の singleton の像を、頂点が k 以下なら singleton、
それより先なら σ^k の像までの初期区間と計算して示す。通常の退化の恒等式と、
全射な単調写像による初期区間の像を使い、和集合保存から全ての有限鎖に拡張する。
Lemma 29 の対応先の非退化性は、一般の単体集合の補題として示す。非退化な x が y の面として
一意に現れるとする。y=σ^h(t) なら、x を与える合成 δ^iσ^h は単射な同次元自己射なので恒等。
従って x=t となり、δ^h(y)=δ^{h+1}(y)=x が一意性に反する。原典の退化の計算を
Mathlib の mono_of_nonDegenerate と SimplexCategory.eq_id_of_mono で表す証明経路である。

Moss 2020 §5 Theorem 42 は strong anodyne 性を regular pairing で証明するが、
ここでは同命題を引用して済ませず、必要な局所化同型を上記の持ち上げで証明する。

## 8. L2c：H_* と plus

ホモロジーのファイルは Homology.lean とする。
plus のファイルは PlusConstruction.lean とする。
X の自由単体的アーベル群 ℤ[X] を構成する。
Mathlib の alternating face map complex を使う。
非正規化複体を正規化複体そのものと呼ばない。
退化部分複体を定義する。
退化部分複体の acyclic 性を証明する。
商模型または Moore 部分複体と正規化を同定する。
H_n(X; ℤ) を正規化複体のホモロジーとして定義する。
単体写像から誘導される写像を構成する。
恒等射・合成との整合を証明する。
ホモトピー不変性を証明する。
群完備化で必要な相対ホモロジーも区別して定義する。
plus の入力は Kan 複体と π₁ の完全正規部分群とする。
π₁ は K-L9 の定義に接続する。
未供給時の π₁ のデータは明示的な引数に留める。
plus の実際の存在証明を仮定の束で代用しない。
2-cell と 3-cell の添付による構成を検討する。
単体的 cell 添付と Kan 置換との関係を明示する。
acyclic は局所係数も含む性質として定義する。
整数係数のホモロジー同型だけから acyclic と呼ばない。
π₁ の完全正規部分群による商を証明する。
ホモロジー同型を acyclic 性の系として公開する。
自然性の意味は選択した構成とホモトピー類で区別する。

## 9. L2d：K₀・K₁

ファイルは K0K1.lean とする。
比較先の K₀ は離散環 π₀A の K₀ とする。
既存 KTheory の定義との比較が必要なら別の補題にする。
S1 以前に K0 界面の確定した型を捏造しない。
冪等元の持ち上げは導来圏での分裂と区別する。
任意の商環への strict な冪等元の持ち上げを主張しない。
有限射影加群と perfect 対象との対応を明記する。
K₀ の生成元・関係の比較を証明する。
K₁ は安定 GL の適切な商に接続する。
安定 elementary 部分群の完全性・正規性を証明する。
KST Lemma 2.14 を plus の π₁ の商から証明する。
Theorem 2.16 の次数 0 と 1 を導く。
負次数への帰納に必要な自然性を公開する。
負次数の主張は K-L3 から供給されるまでは完了扱いにしない。

## 10. L2e と正本 §10-5 の紙上確認

状態：確認項目と証明方針を記録済み、原典との照合と証明は未完了。
確認対象の文言は次のとおり。
「Waldhausen Theorem 2.3.2 の ∞-S• 版に必要な Theorem 1.7.1 の
Hurewicz の段階を、connective dg 代数の Künneth 型スペクトル系列で証明する。」
古典的な球状対象を有限セル dg 加群の模型に読み替える。
セルの次数と cochain の符号を §4 の規約で追跡する。
相対セル添付のホモロジーを濾過する。
Künneth 型スペクトル系列の E² 項を明示する。
底環、左右加群、Tor の変数、次数の総和を明示する。
connective 性から消滅域を得る。
セル濾過の有限性または有界性から収束を証明する。
edge map が必要な Hurewicz 写像であることを同定する。
必要な連結度で最初の非零次数の同型を証明する。
一般の Hurewicz 定理を未証明で持ち込まない。
Theorem 1.7.1 の他の仮定が ∞-S• 側で成立するか確認する。
Theorem 1.8.1 と Proposition 1.5.9 の適用条件を確認する。
Proposition 2.3.5 の有限自由対象の自己同値空間を ĜL と比較する。
K-L1 の K1a が届いた後に比較写像を組み立てる。
Perf への cofinality と K₀ の補正を区別する。
この方針の記録は紙上証明の完了を意味しない。
本項は L2a–d の後、K1a の供給状況と照合して進める。

## 11. 検証と保存

各保存単位で対象モジュールの lake build を実行する。
続いて scripts/audit_kst_comparison.lean を実行する。
公開宣言の完全な型と依存公理を表示する。
許される公理は propext、Classical.choice、Quot.sound のみとする。
許可リストは「三つ全てへの依存が必要」という意味ではない。
新規定義と定理の推移的な依存を確認する。
ビルドと監査の終了コードは set -o pipefail の下で確認する。
全体ビルドは工程の完了時に行う。
import 閉包が他レーンの作業で壊れたら回避策を実装しない。
所有ファイルの問題は自分で修正する。
git diff --check で空白の問題を確認する。
コミットは git commit --only と明示的なパスを用いる。
ルートには既存の他レーンの未コミット変更がある。
ルートを保存するときは一行だけを隔離した index を使用する。
既存の staged 状態を巻き込んだり破棄したりしない。
amend、rebase、reset は使用しない。

### Ex∞ の Kan 性へ向けた細分の比較

Moss Proposition 21 が用いる Kan 性を仮定として置かず、二重細分の horn の充填で示す。
最初に任意の部分順序集合 P について、nerve(P)→Ex(nerve(NonemptyFiniteChains P)) を作る。
各単体 [n]→P が、有限鎖の像を取る単調写像を与えることを使い、sd⊣Ex で転置する。
この段階では比較が同型であることは要求しない。これは Mathlib Subdivision.lean の未実装の
一般の B 関手を仮定せず、順序集合の nerve に必要な比較だけを直接構成する経路である。
次に二重細分の頂点である非空有限鎖 C から、horn に属する面 S の最大元を集める。
horn に属さない面が C にあれば horn の欠けた面の添字 k も加え、その最大元を取る。
この候補の単調性・像の horn への包含・horn 上での反復最終頂点写像との一致は、
それぞれ明示的に証明する項目であり、現時点では充填の成立を主張しない。

## 12. 現在地と主要宣言

現在地：L2a の有限 rank の構成を完了し、L2b の群状モノイドの bar 構成へ進む。
既存 γ1.5 の AW の閉性・結合律・単位律・自然性のビルドを確認した。
既存の標準成分模型から Γ の環構造を構成した。
ĜL_r の単体的モノイド、π₀ĜL_r ≃* GL_r(π₀A)、群構造、積と単位の代表上の整合を証明した。
一対象 dg 圏を入力とする ΓA と ĜL_r(A) の入口を構成した。
H⁰ の自己射環との環同型と、connective な入力の good truncation の擬同型を証明した。
L2a の有限 rank の要求は完了。安定 rank の余極限とその自然性は L2b の BĜL への接続で扱う。
L2b：一般のモノイドの二重単体的 bar、対角による分類空間、連結性と関手性を構成した。
一般の π₀ 誘導モノイドによる群状性を定義し、ĜL_r がそれを満たすことを証明した。
正則作用の分類圏、射影、準同型に関する関手と nerve の実際の収縮を構成した。
正則作用の二重単体的 nerve と対角の全空間も構成した。
標準写像の随伴側 M×Δ¹→BM と、両端が基点に一致する実単体的ホモトピーを構成した。
正則 bar の対角上の収縮を実単体的ホモトピーとして証明した。
正則 bar から BM への射影、M から全空間への写像と基点への三角形を構成した。
頂点による左平行移動、その辺に沿う実ホモトピーと π₀ への降下を構成した。
群状性から逆成分の平行移動で局所化後の左右逆を作り、anodyne 局所化での同型を証明した。
bar の各行と M の有限積の自然な厳密同型を構成し、Segal 条件を供給した。
正則 bar の基点上の厳密ファイバーと M の単体的同型、および標準四角形の引き戻し性を証明した。
ファイバーへ制限した全空間の収縮を射影すると標準ループ族に一致することを証明した。
K-L9 の単体的円からの点付き内部 Hom を借り、Kan 置換した BM のループ空間を構成した。
標準ループ族を円の商の普遍性へ降ろし、実際の射 M→ΩR(BM) と評価による復元を証明した。
正則 bar の各行の基底×M 座標と、任意の面・退化による始点の左平行移動の式を証明した。
右射を関手的な Kan fibration へ置換するホモトピー引き戻し模型と標準比較射を構成した。
模型の射影の fibration 性、左の対象が Kan の場合の模型の Kan 性、基底の可換な比較の射を証明した。
anodyne 包含と基底を固定する実ホモトピーを pushout-product の持ち上げから構成した。
基底上の収縮を任意の引き戻しへ移し、元の右射が Kan fibration なら厳密引き戻しの標準比較射が局所化同型となることを証明した。
標準単体の零頂点への実収縮、元の族の作用とそのホモトピーを構成した。
群状性から単体上の元の族による作用が anodyne 局所化同型となることを証明した。
単体上の作用の比較をセルと骨格の単射列で貼り合わせ、任意のパラメータで動く元の族の作用の局所化可逆性を証明した。
同じ右射の二つの anodyne–Kan 分解の比較が任意の基底変換後も可逆となること、別分解でもホモトピー引き戻し性を判定できることを証明した。
積射影の引き戻しは、因子の Kan 性を仮定せずホモトピー引き戻しとなることを証明した。
正則 bar の各構造写像が定める四角形のホモトピー引き戻し性を、群状性だけから証明した。
正次元 horn の包含の Kan fibration に沿う逆像が anodyne 局所化で同型となることを、実際の二段階の収縮で証明した。
スライスの閉構造と積・忘却の右随伴を実際に構成し、horn ごとの持ち上げ性を移すことで、一般の anodyne 射の Kan fibration に沿う引き戻しの局所化可逆性を証明した。
Kan 基底上では局所化可逆な単射の Kan fibration に対する左持ち上げ性、および任意の局所化同型の Kan 引き戻しの可逆性を証明した。
Kan 基底上の Kan fibration 同士の比較は左の任意の射で引き戻しても可逆となり、固定した Kan 基底上のホモトピー引き戻し模型の左右両入力に関する不変性まで証明した。
Mathlib の sd–Ex 随伴から、自然な最終頂点写像と各単体での切断、単射な X→Ex(X) を構成した。
Ex の反復と Ex∞ の実際の余極限関手、標準単位、有限極限保存を証明した。
Moss Definition 23 の作用素と合成則・冪等性・両端の式、Notation 24 の固定点フィルター、その零段階と単位の像の同定を証明した。
単体ごとの最小の複雑度と、その閾値の最小性を証明した。
Moss Definition 25 の r_n^k と、Lemma 26 (1) の指定した面との合成が恒等となる式を証明した。
和集合保存による singleton 上の比較原理、作用素の和集合保存と初期区間の像を証明した。
Lemma 26 (4) の拡張退化と複雑度の交換、(6) の小さい複雑度での通常の退化との一致を証明した。
Lemma 26 (5) の面と複雑度の吸収則を証明した。
最小の複雑度で次元を上げる exPairingStep と指定面による復元、単射性（Lemma 27）を証明した。
exPairingStep が最小の複雑度を保つこと、元の X の像に入る条件の同値も証明した。
Lemma 26 (7) より強い未切断の二重拡張退化の式と、原典の切断後の式を証明した。
exPairingStep の二重適用の通常の退化による表示と退化性を証明した。
対応先が非退化なら元は前段の exPairingStep の像ではないこと（Lemma 28 の部分）を証明した。
Lemma 26 (2) の前側の面の吸収則、(3) の後ろの面との交換則を証明した。
Lemma 26 (8)・(9) の切断した拡張退化と前後の通常の退化との交換則を証明した。
Lemma 26 の九つの式を全て証明した。
前側の面の複雑度の減少と、後ろの面が元の面の拡張になる式を Ex 上で証明した。
退化単体の複雑度に合った拡張は退化することを証明した。
対応先が非退化なら元も非退化であること（Lemma 28 の残りの部分）を証明した。
小さい複雑度の拡張の退化性、前後の面が元の型 II 単体に等しくないことを証明した。
型 II の集合 exTypeTwo を定義し、指定面の一意性・対応先の非退化性を証明した（Lemma 29）。
Mathlib の IsUniquelyCodimOneFace への接続も証明した。
型 I の集合 exTypeOne と、型 II の n 単体から型 I の n+1 単体への全単射を構成した。
全次元をまとめる exPairingCore と exPairing、その properness を構成した。
同次元の異なる型 II の面での最小複雑度の厳密な減少を証明した。
自然数値の弱 rank 関数 exPairingWeakRank から exPairing の正則性を証明した。
単位 X→Ex(X) の anodyne 性（Moss Theorem 22）を正則 pairing から証明した。
反復列を順序合成とし、X→Ex∞(X) の anodyne 性（Corollary 30）を証明した。
順序集合の nerve の細分から有限鎖の nerve への比較写像を構成した。
単調写像に関する自然性、最大元の写像を合成した際の Ex の単位との一致を証明した。
部分順序集合の非空有限鎖の最大元の存在・単調性・像との交換も証明した。
hornChainVertex を単調写像として定義し、全ての面が horn 内なら反復最大元と一致することを証明した。
各部分鎖の候補頂点が k 以外の共通の頂点を避けることを証明し、horn への写像を構成した。
doubleSubdivisionHornMap を二重細分された標準単体から horn への具体的な写像として構成した。
HornFacePoset とその nerve から horn への最終頂点写像を構成した。
hornChainToHorn_boundary により、horn 内の面の有限鎖上では候補と反復最大元が一致する。
実際の sd(horn) から HornFacePoset の nerve への比較を構成し、最終頂点との合成の一致を証明した。
全対象の subdivisionLastVertexMap と、その標準単体上の明示的な計算式を証明した。
二重細分の候補そのものの horn 上の境界条件の一致は未証明であり、まだ充填定理や Kan 性を主張しない。
Ex∞ の Kan 性・fibration 保存は未証明であり、現時点で Kan 置換と呼ばない。
非 Kan 基底への一般化、対角化後の bar 束の homotopy-cartesian 性、Segal 比較は未証明。
L2b、L2c、L2d、L2e は未完了である。
§10-5 は検証する文言と証明方針を記した段階である。
ĜL の対象は正本 §13-10 に従い群状単体的モノイドとする。
検証：`lake build SerrePositivity.KST.Comparison` は成功した。
検証：`lake env lean scripts/audit_kst_comparison.lean` は終了コード 0。
主要 493 宣言の型と公理を確認した。
さらに名前空間全体の 988 宣言（自動生成された公開補題・射影を含む）を許可リストで検査し、標準三公理のみを確認した。
L2a の工程の区切りで全体ビルドを実行した。
全体ビルドは比較レーンの import 閉包外の `KST/SchemeLemmas/Exceptional.lean:75` で失敗。
未解決の `CategoryTheory.Limits.pullback.map_fst` と関連する pullback の型不整合が原因。
比較レーンの対象ビルドは成功しており、他レーンのファイルは変更しない。

| 主要宣言 | 状態 | 意味 |
| --- | --- | --- |
| `unitsPreimage` | ビルド・監査済み | 環準同型による単元の逆像部分モノイド |
| `evalZeroUnits` | ビルド・監査済み | ℤ[X] → ℤ の単元の逆像 |
| `one_add_X_mem_evalZeroUnits` | ビルド・監査済み | 1+X は逆像に属する |
| `not_isUnit_one_add_X` | ビルド・監査済み | 多項式環では可逆でない |
| `one_add_X_no_right_inverse` | ビルド・監査済み | 逆像での右逆元の不存在 |
| `gammaEndRingObject`、`gammaEndDoldKanIso` | 実装済み | SS03 式 (2.9)、実際の Mathlib Γ との同型 |
| `SimplicialRing.componentsRing`、`simplexToComponents` | 実装済み | Mathlib π₀ の環と単体からの準同型 |
| `componentClassEquiv` | 実装済み | 成分全体を選んだ部分単体集合の π₀ |
| `hatGLMonoidObject` | 実装済み | KST 式 (2.2) |
| `hatGLComponentsMulEquiv`、`hatGL_mk_mul`、`hatGL_mk_one` | 実装済み | π₀ の群と誘導乗法の整合 |
| `dgAlgebraGamma`、`dgAlgebraHatGLComponents` | 実装済み | 一対象 dg 圏としての dg 代数への適用 |
| `gammaEndH0RingEquiv`、`dgAlgebraComponentsH0RingEquiv` | 実装済み | π₀Γ と既存 H⁰ 環の同型 |
| `gammaEndPiZeroHomologyEquiv` | 実装済み | 実際の Mathlib homology との全単射 |
| `quasiIso_connective_truncation` | 実装済み | H^i=0 (i>0) から good truncation の擬同型 |
| `monoidBar`、`monoidBarMap`、`monoidBarConnected` | 実装済み | bar 分類空間の対角模型と連結性 |
| `SimplicialMonoid.componentsMonoid`、`IsGrouplike` | 実装済み | 一般の群状性の界面 |
| `hatGL_isGrouplike` | 実装済み | ĜL の実際の群状性の供給 |
| `regularActionNerveContraction` | 実装済み | 正則作用の nerve の実ホモトピー |
| `monoidBarEdgeMap`、`monoidBarLoopFamily` | 実装済み | 各元が与える基点ループの自然な族 |
| `regularBar`、`regularBarContraction` | 実装済み | 正則作用の全空間の対角と実収縮 |
| `regularBarProjection`、`regularBarFiberMap_projection` | 実装済み | 分類空間への射影と標準ファイバー写像の三角形 |
| `monoidLeftTranslationHomotopy`、`grouplikeTranslationIso` | 実装済み | 実ホモトピーと逆成分による平行移動の可逆性 |
| `grouplikeTranslation_localized_isIso` | 実装済み | anodyne 局所化での具体的な適用 |
| `monoidWordEquiv`、`monoidBarRowIso` | 実装済み | 射列の隣接ラベルによる Segal 同型 |
| `regularBarFiberIso`、`regularBarFiber_isPullback` | 実装済み | 厳密ファイバーと標準引き戻し四角形 |
| `regularBarContraction_projection` | 実装済み | 収縮が与える標準ループ族との一致 |
| `monoidGroupCompletionSpace`、`monoidGroupCompletionSpace_kan` | 実装済み | K-L9 の ΩR(BM) とその Kan 性 |
| `monoidGroupCompletionMap`、`monoidGroupCompletionMap_evaluation` | 実装済み | 実際の標準射と標準ループ族への評価則 |
| `regularBarRowIso`、`regularActionCoordinate_whisker` | 実装済み | 各行の積座標と任意の単体作用の移送式 |
| `homotopyPullbackObject`、`homotopyPullbackComparison` | 実装済み | 右射の Kan 分解による比較模型と標準射 |
| `homotopyPullbackObject_kan`、`homotopyPullbackMap` | 実装済み | Kan 性と基底付き比較 |
| `anodyne_fiberwise_homotopy`、`anodyne_fibration_retraction` | 実装済み | 包含と基底を固定する実収縮 |
| `pullbackHomotopyOver` | 実装済み | 基底上のホモトピーの引き戻し |
| `isHomotopyPullback_of_fibration` | 実装済み | 右射が Kan fibration の厳密引き戻しの比較 |
| `simplexContraction`、`simplexMapContraction` | 実装済み | 標準単体と単体上の写像の実収縮 |
| `monoidActionFamilyHomotopy` | 実装済み | 元の族のホモトピーが誘導する作用のホモトピー |
| `monoidActionFamily_simplex_localized_isIso` | 実装済み | 単体上で動く元による作用の局所化可逆性 |
| `monoidActionFamily_localized_isIso` | 実装済み | 任意のパラメータで動く元の族の作用の局所化可逆性 |
| `replacementComparison_pullback_isIso` | 実装済み | 二つの Kan 分解の基底変換後の比較 |
| `isHomotopyPullback_iff_alternative` | 実装済み | 別の anodyne–Kan 分解による判定 |
| `productPullback_isHomotopyPullback` | 実装済み | 任意の因子を持つ積射影の基底変換 |
| `actionBarCoordinate_naturality` | 実装済み | 各構造写像と前置ラベルの作用の整合 |
| `actionBarSquare_isHomotopyPullback` | 実装済み | 群状性から Segal Proposition 1.6 の各行の仮定を供給 |
| `simplexMeetToIdentity`、`simplexMeetToVertex` | 実装済み | horn と両立する任意の頂点への二段階の収縮 |
| `relative_interval_lift`、`interval_lift` | 実装済み | Kan fibration に沿う両端点からの持ち上げ |
| `subcomplex_inclusion_localized_isIso` | 実装済み | 部分対象を保つ二段階の収縮による局所化可逆性 |
| `horn_preimage_localized_isIso` | 実装済み | Kan fibration に沿う正次元 horn の逆像の局所化可逆性 |
| `simplicialSliceClosed`、`sliceFiberFunctor_isLeftAdjoint` | 実装済み | 宇宙を揃えたスライスの閉構造と基底変換の右随伴 |
| `underlying_rlp_of_over_horns` | 実装済み | 基底付き horn の持ち上げ性による Kan 条件の判定 |
| `pullback_anodyne_localized_isIso` | 実装済み | 一般の anodyne 射の Kan 引き戻しの局所化可逆性 |
| `localizedMono_lifting_fibrantTarget` | 実装済み | Kan 基底上の fibration への局所化可逆な単射の持ち上げ |
| `sliceFiberRightAdjoint_kan` | 実装済み | Kan 基底上の右随伴の Kan 性 |
| `pullback_localized_isIso_of_kan_base` | 実装済み | Kan 基底上の任意の局所化同型の Kan 引き戻し |
| `pullbackMapBase_localized_isIso_of_kan_base` | 実装済み | Kan 基底上の Kan fibration の比較の任意の左射による引き戻し |
| `homotopyPullbackMap_localized_isIso_fixed_kan_base` | 実装済み | 固定した Kan 基底上のホモトピー引き戻しの両入力の不変性 |
| `subdivisionLastVertex`、`subdivisionVertexSectionAt_lastVertex` | 実装済み | 細分の自然な最終頂点写像と各単体での切断 |
| `exUnit`、`exUnitAt_mono` | 実装済み | Mathlib Ex への自然な単射 |
| `exSequence`、`exInfinity`、`exInfinityUnit` | 実装済み | Ex の反復と実際の順序余極限、標準単位 |
| `exInfinity_preservesFiniteLimits` | 実装済み | filtered colimit と有限極限の交換による保存性 |
| `subdivisionCutAt_comp`、`subdivisionCutAt_zero`、`subdivisionCutAt_last` | 実装済み | Moss Definition 23 の作用素の合成と両端の式 |
| `exComplexity_zero`、`exComplexity_last` | 実装済み | Moss Notation 24 のフィルターと単位の像・全単体の同定 |
| `exComplexityLevel_le_iff`、`exComplexityLevel_zero_iff` | 実装済み | 最小の複雑度とその零条件 |
| `subdivisionDegeneracyAt`、`subdivisionDegeneracyAt_face` | 実装済み | Moss Definition 25 と Lemma 26 (1) の拡張退化と指定面 |
| `finiteChainUnion_ext`、`finiteChainCut_preservesUnion`、`finiteChainDegeneracy_preservesUnion` | 実装済み | Moss Lemma 26 の singleton 上の比較原理とその前提 |
| `finiteChainDegeneracy_initialSegment` | 実装済み | 拡張退化の初期区間上の式 |
| `subdivisionDegeneracyAt_cut`、`subdivisionDegeneracyAt_cut_lt` | 実装済み | Moss Lemma 26 (4)・(6) の交換則 |
| `subdivisionCutAt_face_absorb` | 実装済み | Moss Lemma 26 (5) の面と複雑度の吸収則 |
| `exExpansion_face`、`exComplexity_face` | 実装済み | 指定した面の復元と面の複雑度の上界 |
| `exPairingStep_injective` | 実装済み | Moss Lemma 27 の対応先の一意性 |
| `exPairingStep_complexityLevel`、`exPairingStep_mem_image_iff` | 実装済み | 拡張前後の最小閾値と元の部分対象の制御 |
| `subdivisionDegeneracyAt_double`、`subdivisionDegeneracyAt_double_cut` | 実装済み | Moss Lemma 26 (7) の未切断の強い式と原典の式 |
| `exPairingStep_double_degenerate`、`exPairingStep_notMem_range_of_nonDegenerate` | 実装済み | 二重適用の退化性と Lemma 28 の像に関する部分 |
| `subdivisionDegeneracyAt_front_absorb`、`subdivisionDegeneracyAt_face_right` | 実装済み | Moss Lemma 26 (2)・(3) の前後の面との関係 |
| `finiteChainCutDegeneracy_singleton`、`subdivisionDegeneracyAt_front`、`subdivisionDegeneracyAt_rear` | 実装済み | Moss Lemma 26 (8)・(9) の通常の退化との交換則 |
| `exExpansion_front_complexity`、`exExpansion_rear_face` | 実装済み | Moss Lemma 29 の前後の面の計算 |
| `exExpansion_mem_degenerate`、`exPairingStep_nonDegenerate_source` | 実装済み | Moss Lemma 28 の退化性と非退化性を元へ戻す部分 |
| `exTypeTwo`、`exPairingStep_face_unique`、`exPairingStep_nonDegenerate_target` | 実装済み | 型 II の定義と Moss Lemma 29 の指定面・対応先の性質 |
| `nonDegenerate_of_unique_face`、`exPairingStep_isUniquelyCodimOneFace` | 実装済み | 一意な非退化面の一般補題と Mathlib の properness 述語への接続 |
| `exTypeOne`、`exPairingEquiv` | 実装済み | 型 I の定義と各次元の型 II との全単射 |
| `exPairingCore`、`exPairingCore_isProper`、`exPairing` | 実装済み | 全次元の proper pairing |
| `exPairingWeakRank`、`exPairingCore_isRegular`、`exPairing_isRegular` | 実装済み | 最小複雑度による先行関係の整礎性 |
| `exUnitAt_anodyne`、`exInfinityUnit_anodyne` | 実装済み | Moss Theorem 22、Corollary 30 の単位の anodyne 性 |
| `subdivisionNerveChains`、`subdivisionNerveChains_naturality`、`nerveChainsExUnit_lastVertex` | 実装済み | 順序集合の nerve の細分比較・自然性・最終頂点との整合 |
| `finiteChainGreatest`、`finiteChainGreatest_map` | 実装済み | 部分順序集合の非空有限鎖の最大元 |
| `hornChainVertex`、`hornChainVertex_common_missing` | 実装済み | 単調な候補頂点写像と共通に欠ける頂点 |
| `hornChainToHorn`、`doubleSubdivisionHornMap` | 実装済み | 二重細分から horn への写像、境界条件の一致は未証明 |
| `HornFacePoset`、`hornChainToHorn_boundary` | 実装済み | horn の面の nerve 上の境界条件 |
| `hornSubdivisionComparison`、`hornSubdivisionComparison_lastVertex` | 実装済み | 実際の horn の細分比較と最終頂点との一致 |
| `subdivisionLastVertexMap`、`subdivisionLastVertexMap_stdSimplex` | 実装済み | 全対象の最終頂点と標準単体上の計算 |
| Ex∞ の Kan 性 | 未証明 | Moss 2020 Proposition 21 |
| 群完備化・Segal 比較定理 | 未証明 | Segal Proposition 1.5、KST Lemma 2.13 |
| H_* | 未実装 | 正規化自由アーベル群複体 |
| plus 構成 | 未実装 | acyclic map と π₁ の商 |
| K₀・K₁ の比較 | 未実装 | KST Theorem 2.16、次数 0、1 |
| ∞-S• との比較 | K1a 接続前 | KST Proposition 2.15 |

## 13. 原典の所在

- [Moss 2020 原論文](https://link.springer.com/article/10.1007/s40062-019-00247-y)
- [Segal 1974 原論文 PDF](https://ncatlab.org/nlab/files/SegalCategoriesAndCohomologyTheories.pdf)
- [KST arXiv:1611.08466v4](https://arxiv.org/pdf/1611.08466v4)
- [Schwede–Shipley 2003 原論文 PDF](https://people.math.rochester.edu/faculty/doug/otherpapers/schwede-shipley2.pdf)

上の原典は設計の照合に用いる。
原典への参照だけを Lean の証明にすることはない。
