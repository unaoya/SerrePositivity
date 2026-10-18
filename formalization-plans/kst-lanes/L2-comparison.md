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
Kan 引き戻しの可逆性を証明する。非 Kan 基底への拡張は、構成した Ex∞ の有限極限・fibration 保存で証明済み。
Kan 基底上で両方の構造射が Kan fibration の場合、左の任意の射による引き戻しも可逆となる。
左射を anodyne–Kan 分解し、二つの縦比較と可換四角形で一般の左射へ戻す。
これにより、固定した Kan 基底上のホモトピー引き戻し模型は左右両入力の局所化同型で不変となる。
これは Segal Proposition 1.6 の対角模型の補助であり、原典の fat realization の経路とは異なる。
非 Kan 基底の比較を進める補助として、有限極限と両立する Kan 置換 Ex∞ を構成する。
Mathlib の `SSet.sd`、`SSet.ex`、`sdExAdjunction` を使う。
最終頂点写像 sd(Δ[n])→Δ[n] を有限鎖の最大元で定め、自然変換 id→ex を得る。
その反復の順序余極限を Ex∞ とする。
有限極限保存は各 ex の右随伴性と型の filtered colimit の有限極限との交換から証明する。
Kan 性、単位の anodyne 性、fibration 保存はそれぞれ独立に証明済み。
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

### Segal Lemma 1.7・1.8 の貼り合わせの文言と証明方針

原典 p.297 Lemma 1.7：span Y₁←Y₀→Y₂ から X₁←X₀→X₂ への射で、
二つの四角形が homotopy-cartesian なら、誘導される二重写像円筒 Y→X への各頂点の
四角形も homotopy-cartesian である。p.298 Lemma 1.8 は順序列の各四角形から telescope
の各段階の同じ性質を導く。原典は telescope を偶数・奇数の余積の二重写像円筒として扱う。
Lean では二重写像円筒を、X₀⊔X₀→X₀⊗Δ[1]（両端点）と
X₀⊔X₀→X₁⊔X₂（span の二射）との pushout として定義する。
span の射の誘導写像、各端点の包含、円筒の写像の式を先に証明する。
局所化可逆な各行の対角化の定理は模型の不変性だけに使い、homotopy-cartesian 性の
貼り合わせの代用にはしない。貼り合わせの本体はこの実際の pushout の比較について証明する。
現在の Ex∞ の有限極限保存、単位の anodyne 性、Kan 性と、slice の閉構造を用いて、
厳密な引き戻しの colimit との交換から homotopy 引き戻しの比較へ進める。
Lemma 1.7 本体を仮定とする構造体は導入せず、実際の円筒の比較について証明した。
Lemma 1.8 の telescope の貼り合わせも証明した。Proposition 1.6 の対角化の貼り合わせも証明済みである。

### 部分対象を保つ二段階の収縮と anodyne 性

確認する文言：単射 i:A→X に対し、X の恒等射と A に入る射を結ぶ二つの区間写像が
A を保つなら、i は anodyne である。単なる局所化可逆性より強い結論を証明する。
証明方針：任意の Kan fibration p に対する正方形を取り、A に入る終点から始める。
A 上で指定する写像を二つの制限ホモトピーで動かし、単射と区間端点の
pushout-product の持ち上げを二回使って恒等射側へ戻す。最終端点は元の A 上の射に厳密に一致する。
この補題を、既証の horn を保つ min(x,k) 経由の二段階の収縮の持ち上げへ適用する。
これにより Kan fibration に沿う horn の逆像は anodyne となる。
Moss 原論文 arXiv:1506.04887v2 §5 Theorem 5.1 の strong anodyne な pairing とは異なり、
ここでは相対ホモトピーの持ち上げから anodyne 性だけを示す経路を取る。
細分への応用は、細分した horn の像と安全な面の nerve の同定を別途証明してから行う。
Moss 同版 Proposition 2.19 の細分保存を引用による入力にはしない。
細分比較の単射性は、細分の元を余面で表示し、異なる二つの表示を共通の小さい面へ戻して証明する。
同型を得た後、細分された horn の anodyne 性を移し、sd⊣Ex の持ち上げ性の対応で
Ex の Kan fibration 保存を示す。Ex∞ の保存は、horn と標準単体の有限表示可能性により、
arrow 圏の filtered colimit が horn の右持ち上げ性を保つことから導く。
この経路で strong anodyne な pairing の保存そのものは主張しない。

### 厳密な引き戻しの覆いに沿う Kan 条件の局所性

確認する文言：p:E→B と覆い U_j→B に対し、全ての標準単体 Δ[n]→B が一片へ因子化し、
その片への厳密な引き戻しが Kan fibration なら、p も Kan fibration である。
証明方針：horn の持ち上げ問題の底の標準単体を一片へ移し、引き戻しの普遍性で上の horn も
その片へ移す。そこで充填し、全空間へ合成する。pushout では次数ごとの共同全射性が因子化を与える。
これは Mather 1976 §4 Theorem 18 と Lemmas 19–23 の WCHP の証明を引用するものではない。
厳密な引き戻しの場合だけを単体集合の持ち上げで示す補助であり、homotopy-cartesian な
span からこの状況へ移す論証は別途必要である。

### 縦射の関手的な Kan 分解への還元

確認する文言：span の射の各縦射を関手的に anodyne–Kan 分解すれば、中間対象も span をなし、
元の射は anodyne な三成分の単位と、Kan fibration の三成分の射の合成になる。
証明方針：図式の射を arrow 圏の図式にし、既存の関手的分解の中間対象・単位・射影を合成する。
二重写像円筒の既証の恒等・合成則を span の関手へまとめ、単位が誘導する円筒の射を
既証の模型の不変性で局所化同型とする。四つの頂点の置換の不変性で各四角形を比較する。
Mather 1976 Lemma 21 の fibration への還元に対応するが、元のホモトピー引き戻しを
厳密な引き戻しへ置換する論証まで完了したことは意味しない。

### 共通の trivial fibration 模型と単射に沿う延長による厳密化

確認する文言：同じ基底 C 上の Kan fibration E₁→C、E₂→C と、Y から両者への
局所化同型があるとき、Y→Z を anodyne、Z→E₁ と Z→E₂ を trivial fibration とする
可換な共通の模型を作る。ここで E₁ と E₂ の全空間は Kan とする。
証明方針：Y→E₁×_C E₂ を anodyne–Kan 分解し、その後半を二つの射影へ合成する。
射影の Kan 性と二対三から、Kan 全空間へ向かう局所化可逆な Kan fibration を得る。
既存の KanFibrationLocalizedLifting を適用し、全ての単射に対する右持ち上げ性を示す。

次に確認する文言：単射 j:A→B と trivial fibration q:Z→A に対し、
B 上の trivial fibration E→B と、Z≅A×_B E となる延長を構成する。
候補は j に沿う部分切断の対象である。既存の sliceFiberFunctor j とその右随伴 G を使い、
G(q):G(Z)→G(A) を恒等切断の転置 1_B→G(A) に沿って引き戻す。
全単射的右持ち上げ性は、積の単射保存と随伴で移す。j が単射なので、A へ制限した
部分切断は元の Z の元と一意に一致することを、随伴と引き戻しの普遍性で証明する。
この段階では延長や制限の同型を仮定した構造体は作らず、構成と普遍性を証明する。

一般の貼り合わせへの接続方針：Ex∞ と縦射の関手的分解で C を Kan にする。
水平の二つの基底射は既存の mono–全単射的右持ち上げ性の分解で単射に置換する。
その基底の比較を縦の Kan fibration で引き戻し、既証の right properness で模型を保つ。
元の中央の対象から二つの厳密ファイバーへの比較は、ホモトピー引き戻しの仮定から可逆になる。
共通の Z と、二つのファイバーの端点の全空間への単射に沿う延長を使い、
両面が厳密な引き戻しとなる span と、元の span に成分ごとの局所化同型で結ばれる中間 span を作る。
最後に円筒の関手の不変性と四頂点の置換で、証明済みの厳密な場合へ移す。
これは Mather 1976 Lemmas 19–23 の WCHP・numerable covering を移植する経路とは異なる。
上の共通模型・延長・中間 span の各構成と還元を組み合わせ、Lemma 1.7 を証明した。

### telescope の各段階の四角形への貼り合わせ

確認する文言：横に並ぶ二つの homotopy-cartesian な四角形で、中央の縦射が
Kan fibration なら、外周も homotopy-cartesian である。telescope では各成分の包含の
厳密な引き戻しと、余積から円筒への四角形に適用する。
証明方針：右端の縦射を anodyne–Kan 分解し、右の四角形を厳密ファイバーへの
局所化同型で表示する。中央の Kan fibration と新しいファイバーの Kan fibration の
比較を、左下の射に沿って引き戻す。既証の固定基底の引き戻しの不変性と
引き戻しの横の貼り合わせから、外周の別分解による比較も局所化同型とする。
各段階の対象を単に colimit と定義して telescope の結論を仮定することはしない。

### 骨格の単体・境界との積

確認する文言：任意の固定単体集合 K との直積はホモトピー引き戻しを保つ。
証明方針：右射の anodyne–Kan 分解を直積へ送り、厳密な引き戻しの保存と
局所化同型の直積保存で別分解の標準比較を可逆にする。
K の Kan 性や可縮性は使わず、標準単体とその境界の両方へ適用できる形にする。
これは Segal Proposition 1.6 の有限骨格の貼り付けの準備であり、有限骨格の帰納そのものを
完了したことにはしない。fat realization の骨格と対角模型の比較は個別に証明する。

### fat realization の具体的な模型と対角への比較

確認する文言：fat realization は、全ての n にわたる Xₙ⊗Δ[n] の余積を、
単射 θ:[m]→[n] について X(θ) と Δ(θ) が与える二射で同一視した余等化子とする。
この定義から各行の包含、面の関係式、dinatural な族からの desc と一意性を構成する。
既に構成した対角への行の評価は全ての θ に整合するので、実際の比較写像を与える。
この段階では比較写像の局所化可逆性や有限骨格のホモトピー引き戻し性を仮定しない。
骨格の付着の普遍性と、その後の比較の可逆性は独立の証明項目として残す。

### fat realization の各次数の標準形

確認する文言：各次数 d の元は、全射 σ:[d]→[k] と Xₖ の d 単体の組で一意に表せる。
証明方針：任意の t:[d]→[n] を Mathlib の epi–mono 分解 e≫i に分け、
行の元 x を X(i)(x) へ制限する。面との合成では image(t≫θ)=image(t) を示し、
image.ι と factorThruImage の輸送を照合して、余等化子の二射で標準形が等しいことを示す。
全射のときの像は終域であることを使い、全射の標準形から各行への包含が逆写像になることを証明する。
この標準形自体や比較の可逆性を、新しい仮定として導入しない。

### 標準形による fat realization の骨格

確認する文言：fat realization の n 骨格を、正規化した全射の終域の次元が n 以下の
元からなる部分単体集合とする。単体作用でその次元は増えない。
証明方針：全射 σ と単体作用 θ の合成 θ≫σ を epi–mono 分解し、
新しい像から元の終域への単射の次元の不等式を使う。
各行 Xₙ⊗Δ[n] の像は n 骨格に入り、次数 d の全ての元は d 次元までの骨格に入る。
この部分単体集合の定義から有限骨格の付着の pushout の普遍性を別途証明し、
ホモトピー引き戻しの骨格帰納を仮定にはしない。

### 有限骨格の一段階の付着の普遍性

確認する文言：n+1 行の境界との積を n 骨格へ送り、n+1 行の標準単体との積を
貼り付ける四角形は、n+1 骨格を頂点とする実際の pushout である。
証明方針：境界は非全射な単体写像なので、像の次元が n 以下であることと同値である。
これにより境界の積は n 骨格の厳密な逆像になる。n+1 骨格の元は旧骨格または
n+1 行の元から得られ、行の包含は境界の外で標準形の一意性により単射である。
型の圏の isPushout_of_isPullback_of_mono を各次数で適用して普遍性を示す。
この段階でもホモトピー引き戻しの貼り合わせを結論として仮定しない。

### 単射な脚を持つ pushout と二重写像円筒の比較

確認する文言：span の片方の脚が単射なら、二重写像円筒から通常の pushout への
円筒を潰す比較は局所化同型である。
証明方針：f:C→A の一端を貼る mapping cylinder を pushout(ι₀,f) として構成する。
A からの包含は端点の anodyne 性の pushout なので局所化同型であり、円筒を潰す射も
合成が恒等となる二対三から局所化同型である。
既存の二重写像円筒を、この mapping cylinder の残る端点と g:C→B の pushout として
普遍性で表示する。g が単射なら、g を共通の単射な脚とする pushout の比較の定理を使える。
有限骨格の付着では境界の積の包含がこの単射な脚になる。
これは通常の pushout がホモトピー pushout であることを新たに仮定するものではない。

### 境界の有限被覆でのホモトピー引き戻しの比較

確認する文言：右の脚が単射の二つの span とそれぞれの余極限に対し、
各頂点で同じ固定射 X→B への四角形がホモトピー引き戻しなら、余極限の四角形もそうなる。
証明方針：X→B を anodyne–Kan 分解し、各頂点から厳密ファイバーへの標準比較を作る。
基底 B のスライスに余錐を持ち上げ、左随伴である sliceFiberFunctor の余極限保存から
厳密ファイバーの余錐も余極限になることを示す。各頂点の比較の可逆性を、
単射な脚の span の余極限の比較へ適用して全体の比較を可逆にする。
有限個の面とその交叉への適用では、各片・交叉の四角形を別途確認する。
局所的な結論や境界全体の結論を入力の構造体へ隠さない。

### 有限個の面の和に関する帰納

確認する文言：分配束の性質 P が空対象を満たし、二対象とその交叉で P が成り立つときに
和でも成り立つなら、有限族の全ての非空な部分族の交叉で P が成り立つことから、全体の和で P が成り立つ。
証明方針：有限族の要素数で帰納する。新しい要素との交叉を、残りの族との交叉の有限和へ
分配し、その新しい族へ同じ帰納を適用する。交叉族の局所条件は元の族へ新しい要素を足した交叉から得る。
標準単体の境界の被覆への適用では、有限交叉が適切な頂点集合の面であることを別途計算する。

### 適切な非空な面の低次元標準単体表示

確認する文言：標準 n 単体の境界の非空な適切な頂点集合 S の面は、
m = |S| − 1 < n の標準単体と同型である。この同型と境界の包含の合成は、
S の頂点を昇順に並べた単射 [m]→[n] による標準単体の写像と一致する。
証明方針：面が境界以下であることを面の頂点集合の包含から示す。
部分対象の包含に沿った逆像を元の部分対象と明示的な次数ごとの同型で同定する。
Mathlib の faceRepresentableBy と有限順序集合の昇順列挙を合成し、
写像の一致を各単体の単調写像の成分で確認する。
これは Segal Proposition 1.6 の骨格帰納で、小さい行の条件を境界の各片へ移すために使う。

### 境界の付着の四角形への低い行の帰納仮定の適用

確認する文言：二重単体集合の射 α が各行で Kan fibration で、各単射の面の自然性の
四角形がホモトピー引き戻しであるとする。n 骨格への各 m ≤ n 行の四角形が
ホモトピー引き戻しなら、n + 1 行の境界の付着の四角形もそうである。
証明方針：境界の各非空な適切な面を低次元の標準単体として表示する。
単射の面の自然性の四角形と標準単体の積を取り、低い行から n 骨格への四角形と横に貼る。
中央の縦射は各行の Kan fibration と標準単体の積であり、既証の貼り合わせに適用できる。
面の表示の同型で境界の部分対象上へ移し、全ての適切な面から境界への有限被覆の定理を使う。
各行の Kan 性はこの段階の技術的仮定であり、一般の場合の Ex∞ による移送は別途行う。

### 有限骨格の付着から各行への比較を伸ばす帰納

確認する文言：前項の各行の Kan 性と面のホモトピー引き戻し性の下で、全ての n と
m ≤ n に対して、m 行と標準 m 単体の積から n 骨格への四角形はホモトピー引き戻しである。
証明方針：零骨格では第零行との実際の同型を標準形から証明する。
帰納段階では、境界の付着と境界の積の包含の実際の span を用いる。
左脚の比較は低い行から境界への前項、右脚の比較は二因子の積の厳密な引き戻しから得る。
単射な右脚と実際の付着の pushout に Lemma 1.7 を移す定理を適用し、
旧骨格と新しい行から次の骨格への四角形を得る。古い各行は旧骨格を経由して横に貼る。
この最後の貼り合わせの中央の骨格の射は Kan とは限らないため、
一般の二つのホモトピー引き戻しの貼り合わせ、または同じ固定射へのファイバー比較で処理する。
骨格の射の Kan 性を未証明のまま仮定しない。

### 中央の Kan 性を課さない四角形の横の貼り合わせ

確認する文言：任意の二つのホモトピー引き戻しの四角形を横に貼り合わせた外周も、
ホモトピー引き戻しである。中央の縦射や基底の Kan 性は不要である。
証明方針：三つの縦射に同じ関手的 anodyne–Kan 分解を適用する。
二つの四角形の上辺を arrow 圏の射として中間対象の関手へ送り、
単位の anodyne 性と四頂点の不変性から置換後の二つの四角形を得る。
中央の縦射が Kan な場合の既証の横の貼り合わせを適用し、
単位の自然性で外周の比較を元の外周へ戻す。
これは有限骨格の古い各行の比較を次の骨格へ進めるための補助である。

### 各行の局所化同型による有限骨格の比較

確認する文言：二重単体集合の射が各行で anodyne 局所化同型なら、
各有限骨格へ誘導される射も anodyne 局所化同型である。
証明方針：零骨格の実際の同型と行の自然性で初期段階を処理する。
次の骨格の付着の span の境界と新しい行では、固定対象との積の局所化同型保存を使う。
旧骨格には帰納仮定を使い、単射な脚の span の具体的な余極限の比較を適用する。
この不変性と四頂点の比較により、各行の Kan 性を仮定した有限骨格の比較を
一般の入力へ関手的な anodyne–Kan 分解で戻す。

### 無限骨格への順序余極限の四角形の比較

確認する文言：単体集合の自然数添字の四つの図式の可換四角形で、各段階が
ホモトピー引き戻し、上側二つの図式の遷移が単射なら、余極限の四角形も
ホモトピー引き戻しである。
証明方針：右の縦射の図式を関手的 anodyne–Kan 分解し、下辺との厳密な引き戻しを図式圏で作る。
各段階からこの引き戻しへの比較は局所化同型である。上左の遷移の単射性から、
既存の KanSequentialColimitComparison により比較の順序余極限も局所化同型となる。
上右の遷移の単射性から、分解の単位の順序余極限も局所化同型である。
horn の有限表示可能性により射影の余極限は Kan fibration のまま、
filtered colimit と有限極限の交換により厳密な引き戻しの余極限は引き戻しとなる。
一般の別分解の判定へこれらを代入して結論を得る。
Segal Proposition 1.6 の無限骨格の段階では、この有限表示可能性と実際の余極限の経路を用いる。
原典の Lemma 1.8 の telescope を経由する記述とは異なる証明経路であり、
既証の Lemma 1.8 は独立した比較補題として保持する。
fat realization と対角の比較の局所化可逆性は、この順序余極限の定理だけからは得られず、別の証明を要する。

### fat realization の各行の局所化同型に対する不変性

確認する文言：各行で anodyne 局所化同型である二重単体集合の射は、
fat realization 全体でも anodyne 局所化同型を誘導する。
証明方針：各有限骨格の不変性を骨格の順序列の自然変換へ適用する。
骨格の包含は単射であり、既存の KanSequentialColimitComparison の
具体的な余錐の比較を、実際の fat realization の包含の余錐へ適用する。
これは対角への自然な比較の可逆性とは別の主張である。

### fat realization と対角の自然比較の可逆性の補助模型

確認する文言：単体集合 X の各 Xₙ を定数単体集合とした二重単体集合の fat realization を D(X) とする。
各次数の標準形は全射 [d]→[k] と Xₖ の元の組であり、D(X)→X はその全射で元を引き戻す写像である。
D(Δ[n]) は頂点 0 を先頭に追加する余分な退化により可縮である。
証明方針：既存の fat realization と標準形を使って D と自然な augmentation を実際に構成する。
標準単体上では標準形の全射と頂点写像の双方に初期頂点を追加する操作を定義し、
面・退化との等式を証明して ExtraDegeneracyContraction に適用する。
D の余極限・単射保存を独立に示し、CellularNaturalComparison により任意の X の augmentation を局所化同型にする。
二重単体集合には各列で D を適用し、標準形による対角との同型と既存の対角の行ごとの局所化同型保存へ移す。
これは Segal 1974 Proposition 1.6 の fat realization と通常の realization の比較のための、
自由な退化の補助模型による証明経路である。可縮性や最終的な比較の可逆性を入力として仮定しない。
この補助模型、全次数の面・退化と整合する実際の余分な退化、標準単体上の augmentation の局所化可逆性は証明済み。
全射の形による評価関手の直和表示から余極限保存を証明し、一般の単体集合への移送も完了した。
各列の自由な退化の対角との実際の同型で、fat realization から対角への自然比較の可逆性を証明した。

### 正則 bar の収縮から標準ループ写像への接続

確認する文言：群状単体的モノイド M の既存の標準群完備化写像
M→ΩR(BM) は anodyne 局所化同型である。
証明方針：第零行の同型と評価の式で、Proposition 1.6 から正則 bar 束の
標準ファイバーの四角形のホモトピー引き戻し性を得る。
正則 bar の収縮を R(BM) へ射影して K-L9 の基点始点 path space へ curry し、
全空間から path space への射を作る。終点評価との可換性は収縮の終点の式から得る。
両方の全空間は実際の収縮により局所化後一点なので、この射は局所化同型となる。
K-L9 の loop と path 終点の厳密ファイバーの同型を使い、ファイバー間の比較を局所化同型にする。
最後に既存の regularBarContraction_projection と loop の評価の一意性で、
このファイバー比較が既存の monoidGroupCompletionMap と一致すると証明する。
π_n の同型を仮定して局所化可逆性を逆算せず、実際の写像と収縮で証明する。

### 安定 rank の単体的モノイドと成分の群状性

確認する文言：ĜL_r→ĜL_(r+1) は行列と単位のブロック和であり、係数環の射と可換する。
この順序列の実際の単体的モノイドの余極限を安定 ĜL とし、その π₀ は群状である。
証明方針：ブロック和と添字の付け替えから積と単位を保つ行列写像を構成する。
係数環の射との自然性を各行列成分で確認し、連結成分の行列の可逆性を単位群の写像で保つ。
単体的モノイドの図式圏で順序余極限を取り、各次数の underlying type の filtered colimit 保存を使う。
安定モノイドの零単体は有限段階の元で表され、その成分の二側逆を有限段階の群状性から選ぶ。
成分上の乗法と単位の自然性で安定モノイドの成分も可逆であると示す。
π_n の次数移動・行列の高次の積の比較は K-L9 の π_n を借りる界面として別途明示する。
群完備化写像の可逆性を、この π_n の界面の仮定として再導入しない。

### 単体的モノイドの成分関手と安定成分の同定

確認する文言：実際の π₀ の誘導乗法を使う成分モノイドの関手は、定数単体的モノイドの関手の左随伴である。
したがって成分は順序余極限を保存し、安定 ĜL の成分は GL_r(π₀A) の安定化の余極限と乗法を保って同型である。
証明方針：各単体の最初の頂点の成分から成分モノイドへの自然な射を作る。
定数モノイドへの自然変換は零次の写像を辺に関して等しくするので、π₀ の実際の商へ一意に降りる。
その写像が積と単位を保つことを零単体の代表で確認し、Hom 同値と随伴を構成する。
有限 rank の成分の同型と安定化の整合は、単元の値の行列とブロック和の等式で確認する。
この同型を順序余極限へ送り、成分関手の余極限保存と合成する。

### 群完備化比較と K-L9 のホモトピー類の接続

確認する文言：群状モノイドの標準群完備化写像は単位を定数ループへ送り、
Kan な模型を取ると K-L9 の全次数のホモトピー類の全単射を誘導する。
その零次数は GL(π₀A) と BĜL の基本群の同定へ、正次数は loop の次数移動へ接続する。
証明方針：単位が与える bar の辺は全次数で定数であることを nerve の射列で計算する。
区間での評価と円の商の全射性から標準群完備化写像の基点保存を得る。
Kan な対象間の局所化可逆な射は anodyne・Kan fibration 分解を使い、
K-L9 の二つの既証明のホモトピー不変性へ渡す。π_n 自体を再定義しない。
非 Kan の入力では Kan 置換を通し、置換単位の比較と標準写像の比較を合成する。
行列の正次数の積の公式は、未供給の K-L9 の性質を明示する界面として区別する。

### 基本群の積の向きと行列群の同型

確認する文言：Mathlib の SingleObj は f≫g=g*f の規約である。
K-L9 の π₁ の積の MulStruct は二単体の δ₂ を第一因子、δ₀ を第二因子とする。
したがって正向きの nerve の辺から π₁ への写像は反乗法的であり、
群からの比較では逆元を前合成して乗法的な同型を得る。
証明方針：一対象圏の nerve の辺を境界定数一次単体へ移す。
二つの辺の composable arrows の二単体を K-L9 の MulStruct と照合する。
標準群完備化写像の区間評価と、円の写像空間の成分の比較で代表の一致を示す。
成分上へ降ろして反乗法性を証明し、群状性による成分の群の逆元を前合成する。
標準写像の向きや既存の π₁ の定義を変更せず、群同型の方向の規約を明示する。

### 成分全体の部分単体集合と正次数のホモトピー類

確認する文言：Kan 複体 X の連結成分の一部を成分全体として選んだ部分単体集合は Kan である。
その包含は、選ばれた基点における全ての正次数のホモトピー群を保つ。
証明方針：ホーンを X で充填すると、その既に選ばれた一つの面と充填単体の成分が等しいので、
充填単体は部分単体集合に属する。正次数の境界定数単体の全頂点は基点の成分に属する。
関係を与える充填の一つの面も同じ成分にあるため、代表と関係の双方を一意に持ち上げる。
π_n の商と群演算には K-L9 の実際の定義を使い、成分選択の幾何だけを本レーンで証明する。
行列の可逆成分の包含へ適用し、高次の行列公式の有限 rank の段階へ接続する。

### 行列のホモトピー群の積分解と加法による基点移動

確認する文言：台単体集合が Kan である単体的環の全行列の正次数のホモトピー群は、
各係数の対応する基点でのホモトピー群の積と同型である。
零次の行列の全次数への退化を引く単体的同型によって、単位行列の基点を零行列へ移せる。
証明方針：係数評価が誘導する準同型を束ねる。全射性では係数ごとの境界定数単体の代表を選び、
それらの行列を作る。単射性では同じ添字零の RelStruct を係数ごとに選び、行列の充填へまとめる。
基点移動は零次の行列の退化を各次数で引く写像と足す写像を実際に構成する。
単体的加法群の Kan 性は低い面からと高い面からの退化による補正で別途供給する。
元のモノイドの次数ごとの乗法逆元は、この Kan 性の証明では用いない。

### 単体的環の台集合の Kan 性

確認する文言：任意の単体的環の台単体集合は Kan である。
証明方針：加法と退化を用い、ホーンの指定された面を逐次補正する。
まず i=0 から欠けた面 k の直前まで、y を y+s_i(x_i-d_i y) に置き換える。
続いて最高の面から k の直後まで、y を y+s_(i-1)(x_i-d_i y) に置き換える。
単体恒等式とホーンの互換性により、既に正した各面では補正項の面は零である。
低次のホーンの基底の場合を分離し、有限回の補正で全ての指定された面に一致する。
原典 KST Lemma 2.13 が暗黙に使う単体的加法群の Kan 性を、
本実装では horn の補正写像として直接証明する経路を取る。
次数ごとの行列の乗法逆元を使う経路へ戻さない。

### 整数ホモロジーの正規化と退化部分

確認する文言：自由単体的アーベル群 ℤ[X] の正規化 Moore 複体 Nℤ[X] を整数鎖複体とする。
Mathlib の alternating face map complex Kℤ[X] への自然な包含は実際の鎖ホモトピー同値である。
退化部分は Q∞=id-P∞ の像であり、その恒等射は零と鎖ホモトピックなので acyclic である。
証明方針：AddCommGrpCat.free を各単体次数へ施し、二つの既存の鎖複体関手を合成する。
正規化の比較には Mathlib の homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex を用いる。
H_n(X;ℤ) を Nℤ[X] の実際の homology として定義し、誘導写像と自然性を公開する。
単体的ホモトピーは自由関手を通して alternating face map complex の鎖ホモトピーへ渡し、
自然な正規化比較によって整数ホモロジーの写像の一致を得る。
退化部分の像の分解は Q∞ の冪等性から構成し、Mathlib の Q∞ の零ホモトピーを制限する。
退化像の生成する部分との一致は、Decomposition と Degeneracies の補題で別途確認する。
この経路は非正規化複体を正規化と呼び換える経路ではない。
原典は Weibel K-book IV.1.5–IV.1.6 の plus のホモロジー、Waldhausen LNM 1126 §1.7・§1.8・§2.3。

### 局所係数の単体的模型と acyclic 性

確認する文言：X.Elements の全ての射を同型へ送るアーベル群値関手を局所係数系とする。
Elements は Δᵒᵖ 上の共変の元の圏であり、通常の単体の圏と向きが逆である。
係数系を忘却 X.Elements→Δᵒᵖ に沿って左 Kan 拡張し、正規化 Moore 複体を取る。
この左 Kan 拡張の各次数は、その次数の単体の係数群の直和に一致することを別途証明する。
引き戻し係数は mapElements による前合成であり、鎖写像は Kan 拡張の普遍性から構成する。
acyclic 条件は標的上の全ての局所係数に対する、引き戻し係数からの実際のホモロジー写像の可逆性とする。
整数定数係数との比較は自由アーベル群模型との自然な同型を証明してから公開する。
原典番号の照合：Weibel K-book III は低次 K 群と完全群の代数的背景、
plus の存在は IV.1.5、acyclic map の局所係数による特徴付けは IV.1.6 である。
局所係数の圏論的模型は Cegarra–Garzón, Higher cohomologies of modules,
AGT 12 (2012), Remark 2.1 の全射の局所化による記述と整合させる。
原典 URL：<https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf>、
<https://msp.org/agt/2012/12-1/agt-v12-n1-p15-s.pdf>。
plus のセル添付の存在証明、π₁ の商、ホモトピーファイバーの acyclic 性との同値は未証明である。
これらを局所係数系の構造体のフィールドとして仮定しない。

### plus のセル添付で確かめる項目

確認する文言：連結な Kan 複体 X と完全正規部分群 P⊲π₁X に対し、
P のループを殺す 2-cell と、その相対ホモロジーの基底を殺す 3-cell を付ける。
Q=π₁X/P とする。2-cell を付けた Y の普遍 Q-cover への X の引き戻しは π₁=P を持つ。
P の完全性からこの cover の H₁ は零である。
相対鎖群 C₂(Ỹ,X̃) は添付したループを添字とする自由 ℤ[Q]-加群である。
相対長完全列により H₂(Ỹ)→H₂(Ỹ,X̃) は全射となる。
Ỹ は単連結なので、Hurewicz により相対基底の持ち上げを π₂ の代表として選べる。
それらを 3-cell で殺すと相対鎖複体の 3→2 微分は自由 ℤ[Q]-加群の恒等行列となる。
従って任意の Q-加群を係数にしても相対複体は収縮し、全局所係数でホモロジー同型を得る。
3-cell は π₁ を変えないため、最終の基本群は Q となる。
原典は Weibel K-book IV.1.5 および Ex. IV.1.4、IV.1.6。
Lean で必要な部品：単体的セル添付、cover と係数の比較、H₁ と基本群の可換化、
単連結 Hurewicz、2-cell・3-cell の基本群への効果、Kan 置換の局所係数ホモロジー保存。
π_n の定義や既存の次数移動は K-L9 から借りるが、未供給の部品を plus の存在と同値の仮定に束ねない。
先に既存の horn の二段階収縮を整数ホモロジーへ移し、その後局所係数・セル添付へ拡張する。
この論理の記録は、上記各部品の形式化完了を意味しない。

### filtered colimit とホモロジーの交換

確認する文言：アーベル群の filtered colimit は完全であり、鎖複体の filtered colimit のホモロジーは
各段階のホモロジーの filtered colimit と自然に同型である。
証明方針：関手圏の三項複体のホモロジーを評価関手のホモロジー保存で点ごとに記述する。
Mathlib の AB5 により余極限関手は有限極限・有限余極限を保存し、実際のホモロジーを保存する。
三項複体の次数ごとの余極限と複体の評価の余極限を照合して比較の自然性を得る。
これを自由整数鎖複体へ適用して、horn を順次添付する際の極限段階のホモロジーを計算する。
正規化は既に証明した自然なホモロジー比較で戻す。ホモロジー保存を新しい構造体の仮定にはしない。
Waldhausen LNM 1126 §1.7・§1.8 のセル濾過を単体的・アーベル圏の余極限で扱う証明経路である。

### horn 添付の pushout と相対余核

確認する文言：単射な鎖写像の擬同型性は、その余核複体が acyclic であることと同値である。
正方向は短完全列のホモロジー長完全列、逆方向は両隣の余核ホモロジーの消滅から従う。
非負鎖複体では H_n の左隣に H_(n+1) があるため、零次でも単射性の判定に適用できる。
アーベル圏の pushout で単射性は保存され、対応する二本の射の余核は実際に同型である。
従って単射な擬同型の pushout は擬同型である。
自由非正規化整数鎖複体の pushout 保存と、horn の単射性・ホモロジー同型を使って添付へ適用する。
原典のセル濾過による議論を、Mathlib の短完全列と余核の pushout 比較で証明する経路である。

## 12. 現在地と主要宣言

現在地：L2a と L2b の要求された群状モノイドの比較・KST Lemma 2.13 を完了し、L2c に進む。
L2c の正規化整数ホモロジー・自然な正規化比較・ホモトピー不変性・退化部分の収縮を証明した。
相対整数ホモロジーの余核模型、包含の鎖写像の単射性、連結射と三箇所の長完全性も完成した。
L2c の局所係数ホモロジーと plus、L2d の K₀・K₁、L2e の ∞-S• の比較は未完了である。
正本 §13-10 のとおり、ĜL は群状単体的モノイドであり、次数ごとの単体的群とはしない。
π_n とその既存の群演算・loop の次数移動・filtered colimit の定理は K-L9 の実装を借りた。
π_n の計算を追加仮定として導入せず、実際の Kan 模型に対する群同型を構成した。
pro 圏や pro 同型は本レーンには再実装しない。K-L6 との接続は所有する界面に従う。

### L2a の完成内容

SS03 式 (2.9) の Alexander–Whitney 積による Γ の環構造を構成した。
Mathlib の実際の Dold–Kan Γ との比較と、π₀Γ・H⁰・実際の homology の比較を証明した。
cochain 規約で H^i=0（i>0）の connective 性から good truncation の擬同型を証明した。
ĜL_r を π₀ で可逆な行列の単体的部分モノイドとして構成した。
零次の積から誘導した成分モノイドを GL_r(π₀A) と乗法的に同定し、群状性を証明した。
単位とのブロック和の安定化と実際の安定 ĜL の順序余極限を構成した。
成分モノイド関手の定数関手への左随伴性で π₀ と安定化の余極限を交換し、安定 GL(π₀A) と同定した。

### L2b の完成内容

一般の単体的モノイドの二重単体的 bar、対角による分類空間、連結性と関手性を構成した。
正則作用の bar の収縮を実際の単体的ホモトピーとして構成した。
群状性から元の族の作用の局所化可逆性を証明した。
Segal Proposition 1.6 の fat realization の有限骨格・順序余極限・対角との比較を証明した。
原典と異なる箇所は §11 の確認事項に記した。
無限骨格では telescope の引用によらず、有限 horn の表示可能性と filtered colimit の有限 pullback 保存を使った。
fat realization と対角との比較は自由な退化の標準単体上の実収縮と列ごとの局所化比較から導いた。
これを正則 bar に適用し、標準ファイバーのホモトピー引き戻し性を証明した。
K-L9 の実際の path・loop の模型で標準群完備化写像との一致を証明した。
群状モノイドの標準写像 M→ΩR(BM) が anodyne 局所化で可逆であることを追加仮定なしに証明した。
単位は定数ループへ送られることを全次数で証明した。
基本群では SingleObj の合成 f≫g=g*f と K-L9 の積の向きを二単体の MulStruct で照合した。
正向きの辺の反乗法性と標準比較との代表の一致から、逆元の辺による乗法的な群同型を構成した。
高次では成分全体の部分複体の Kan 性と、包含の正次数の群同型を代表・関係の持ち上げで証明した。
全行列の係数評価の群同型と、単位行列を引く実際の平行移動を構成した。
単体的環の Kan 性は低い面・高い面からの退化による有限回の補正で直接証明した。
これにより有限 rank の高次の群の係数表示から Kan 性の仮定を除いた。
零基点の係数評価は安定化に対し既存の係数を保ち、新しい係数を零へ送ることを証明した。
rank の図式の自然同型を構成し、K-L9 の群の filtered colimit の定理で実際の安定対象へ移した。
添字の宇宙の整合には AsSmall の圏同値を使った。
安定係数行列群は点ごとの群演算の有限行列に新しい単位の行・列を付ける実際の群の余極限である。
この単位は係数群を加法記法で書いた際の零に対応する。
KST Lemma 2.13 は次の三つの実際の宣言で供給される。

- `monoidBarKanConnected`：Kan 置換した安定分類空間の連結性。
- `lemma_2_13_pi_one`：GL(π₀A) と BĜL の基本群の乗法同値。
- `lemma_2_13_higher`：BĜL の次数 n+2 の群と、係数環の次数 n+1 の群の安定行列群の乗法同値。

### 残工程

L2c：正規化整数ホモロジー、非正規化との自然同型、ホモトピー不変性は完成。
退化射影 Q∞ の像の分裂と鎖収縮、全次数のホモロジー消滅、退化の消滅による普遍的特徴付けも証明した。
相対整数ホモロジーの余核模型と包含に対する長完全列は完成。
局所係数系・左 Kan 拡張による実際の正規化鎖複体・引き戻し係数と誘導鎖写像は構成した。
各次数の直和表示と Kan 拡張の単位の包含との一致を証明した。
定数整数係数の単体的群と自由単体的アーベル群の実際の同型、正規化複体とホモロジーの同型を構成した。
単体写像に対する比較の自然性を単体的群・正規化複体・ホモロジーで証明し、
全局所係数のホモロジー同型から整数係数のホモロジー同型を導いた。
二段階の対の収縮によるホモロジー同型と、正次元の全 horn 包含の整数ホモロジー同型を証明した。
自由非正規化整数鎖複体の余極限保存と、正規化・非正規化の擬同型による整数ホモロジー同型の判定も証明した。
AB5 による filtered colimit と整数ホモロジーの自然な交換、
各段階の整数ホモロジー同型の余極限への移送は完成した。
Kan 置換のホモロジー保存とセル添付の計算は未完了。
その後、局所係数を含む acyclic map、ホモロジー同型、基本群の完全正規部分群による商として plus を証明する。
L2d：確定した K0 界面、冪等元の持ち上げ、安定 elementary 部分群と K₁ の比較を証明する。
L2e：K-L1 の K1a の供給状況を確認し、§10-5 の Hurewicz の紙上確認と ∞-S• の比較へ進む。
§10-5 は文言と証明方針の記録の段階であり、紙上証明の完了とは扱わない。
負の次数は K-L3 の Bass 基本定理の界面に接続する。

### 検証

`lake build SerrePositivity.KST.Comparison`：成功、4478 jobs。
`lake env lean scripts/audit_kst_comparison.lean`：終了コード 0。
主要 1364 宣言の型と推移的依存公理を確認した。
名前空間全体の 2509 宣言（自動生成された公開補題・射影を含む）も許可リストで検査した。
許可した公理は propext、Classical.choice、Quot.sound の標準三公理のみ。
L2b の工程の区切りの全体ビルドはルート集約 `SerrePositivity.lean:1` で失敗した（12355 jobs の最終集約）。
`F1B.RelativeFunctorHomotopyComposition` の import が `F1.RelativeFunctorVertices` の
`SerrePositivity.InfinityCategories.relativeFunctorVertex` と重複するためである。
比較レーンの import 閉包の対象ビルドは成功しており、回避する import の変更はしない。
他レーンのファイルは編集していない。

### 主要宣言

| 主要宣言 | 状態 | 意味 |
| --- | --- | --- |
| `shortComplexPointwiseHomologyIso`、`shortComplexHomologyColimitIsColimit` | 監査済み | 関手圏のホモロジーと完全な余極限の実際の普遍性 |
| `integralHomologyFilteredColimitIso`、`integralHomologyIsomorphism_colimit` | 監査済み | filtered colimit との自然な比較同型と段階ごとの同型の保存 |
| `integralHomologyIsoOfPairContraction`、`hornIntegralHomologyIso` | 監査済み | 二段階の対の収縮と正次元 horn の整数ホモロジー同型 |
| `unnormalizedIntegralChains_preservesColimits` | 監査済み | 自由非正規化鎖複体の余極限保存 |
| `integralHomologyIsomorphism_iff_unnormalized_quasiIso` | 監査済み | 余極限を保存する複体での擬同型による判定 |
| `integralHomologyFunctor`、`normalizationHomologyNatIso` | 監査済み | 実際の正規化整数ホモロジーと非正規化との自然同型 |
| `coefficientFiberIsColimit`、`coefficientSimplicialObjIsoSigma` | 監査済み | 各次数の係数群の直和の普遍性と実際の比較同型 |
| `integerLocalCoefficientHomologyIso_naturality`、`integralHomologyIsomorphism_of_local` | 監査済み | 自然な比較と全局所係数から整数係数への帰結 |
| `integerCoefficientSimplicialIso`、`integerLocalCoefficientChainsIso`、`integerLocalCoefficientHomologyIso` | 監査済み | 定数整数局所係数と自由整数鎖複体の実際の同型 |
| `LocalCoefficientSystem`、`localCoefficientChains`、`localCoefficientHomologyMap` | 監査済み | 局所係数の実際の複体と誘導写像 |
| `LocalHomologyIsomorphism` | 監査済み | 全標的局所係数でのホモロジー同型条件。plus の存在は未証明 |
| `relativeIntegralChainsFunctor`、`normalizedIntegralChains_map_mono` | 監査済み | 相対鎖複体の関手と包含の単射性 |
| `relativeIntegralHomologyBoundary`、`relativeIntegralHomology_exact_at_source`、`relativeIntegralHomology_exact_at_target`、`relativeIntegralHomology_exact_at_relative` | 監査済み | 相対ホモロジー長完全列の連結射と完全性 |
| `integralHomologyMap_eq_of_homotopy` | 監査済み | 単体的ホモトピー不変性 |
| `degenerateIntegralChainsContraction`、`degenerateIntegralChains_homology_isZero` | 監査済み | 退化部分の実際の鎖収縮と消滅 |
| `integralDegenerateProjection_annihilates_iff` | 監査済み | 退化射影の像の普遍的特徴付け |
| `unitsPreimage`、`not_isUnit_one_add_X` | 監査済み | π₀ の単元の逆像が各次数の群とは限らない反例 |
| `gammaEndRingObject`、`gammaEndDoldKanIso` | 監査済み | SS03 式 (2.9) の実際の Γ の AW 環 |
| `SimplicialRing.componentsRing`、`simplexToComponents` | 監査済み | 成分環と各次数からの環準同型 |
| `dgAlgebraGamma`、`dgAlgebraHatGLComponents` | 監査済み | 一対象 dg 圏としての dg 代数への適用 |
| `gammaEndH0RingEquiv`、`dgAlgebraComponentsH0RingEquiv` | 監査済み | π₀Γ と既存の H⁰ 環の比較 |
| `gammaEndPiZeroHomologyEquiv`、`quasiIso_connective_truncation` | 監査済み | 実際の homology と connective truncation |
| `hatGLMonoidObject`、`hatGL_isGrouplike` | 監査済み | 群状単体的モノイドとしての ĜL |
| `hatGLInducedComponentsEquiv`、`hatGLRankComponentsIso` | 監査済み | 誘導乗法の有限比較と安定化の整合 |
| `SimplicialMonoid.componentsFunctor`、`componentsConstAdjunction` | 監査済み | 実際の成分モノイドと定数関手の随伴 |
| `stableHatGL`、`stableGeneralLinear`、`stableHatGLComponentsIso` | 監査済み | 実際の安定化の余極限と安定成分の同型 |
| `monoidBar`、`monoidBarMap`、`monoidBarConnected` | 監査済み | 実際の bar の対角模型・関手性・連結性 |
| `regularBarContraction`、`regularBarFiber_isPullback` | 監査済み | 正則作用の実収縮と厳密ファイバー |
| `grouplikeTranslation_localized_isIso` | 監査済み | 逆成分による作用の局所化可逆性 |
| `monoidActionFamily_localized_isIso` | 監査済み | 任意のパラメータの元の族による作用 |
| `homotopyPullbackObject`、`IsHomotopyPullback` | 監査済み | 実際の Kan 分解によるホモトピー引き戻し |
| `isHomotopyPullback_of_fibration`、`isHomotopyPullback_paste_horiz` | 監査済み | 厳密引き戻しからの比較と貼り合わせ |
| `sequential_homotopyPullback` | 監査済み | 有限 horn と余極限による無限骨格の比較 |
| `fatRealizationMap_localized_isIso` | 監査済み | fat realization の行ごとの局所化比較 |
| `freeDegeneraciesAugmentation` | 監査済み | 自由な退化と任意の対象の局所化比較 |
| `fatRealizationToDiagonal_localized_isIso` | 監査済み | fat realization と実際の対角の比較 |
| `segalRealization_homotopyPullback` | 監査済み | Segal Proposition 1.6 の対角版 |
| `regularBarFiber_homotopyPullback` | 監査済み | 群状モノイドの正則 bar の標準ファイバー |
| `monoidGroupCompletionSpace`、`monoidGroupCompletionMap` | 監査済み | 実際の ΩR(BM) と標準比較射 |
| `monoidGroupCompletionMap_path`、`monoidGroupCompletionMap_unit` | 監査済み | 標準ファイバー比較との一致と基点保存 |
| `monoidGroupCompletionMap_localized_isIso` | 監査済み | Segal Proposition 1.5 の群状モノイドの比較 |
| `hatGLGroupCompletionMap_localized_isIso` | 監査済み | 有限 rank の ĜL への特殊化 |
| `stableHatGLGroupCompletionMap_localized_isIso` | 監査済み | 実際の安定 ĜL への特殊化 |
| `kanPiIsomorphism_of_localized_isIso` | 監査済み | K-L9 の全基点・全次数の類への接続 |
| `monoidNerveLoopMulStruct`、`monoidNerveFundamentalClass_mul` | 監査済み | 二単体での基本群の積の向きの検査 |
| `groupCompletionVertex_eq_barLoop` | 監査済み | 標準群完備化の頂点と nerve の辺の代表の一致 |
| `monoidBarFundamentalMulEquiv` | 監査済み | 群状モノイドの成分群と BM の基本群の群同型 |
| `componentSubcomplex_kanComplex` | 監査済み | 成分全体の部分複体の Kan 性 |
| `componentPtSimplexLift`、`componentRelStructLift` | 監査済み | 正次数の代表と関係の実際の持ち上げ |
| `componentPositiveHomotopyMulEquiv` | 監査済み | 成分全体の包含の正次数の群同型 |
| `matrixRingObject`、`matrixPositiveHomotopyMulEquiv` | 監査済み | 全行列の単体的環と係数群の積分解 |
| `hatGLComponentIso`、`hatGLPositiveHomotopyMulEquiv` | 監査済み | 可逆成分の包含による正次数の比較 |
| `ringTranslationIso`、`matrixStabilization_sub_one` | 監査済み | 零基点への平行移動と安定化の整合 |
| `RingHornFaces.exists_lower_prefix`、`exists_filler` | 監査済み | 二方向の有限帰納によるホーン充填 |
| `ringSpace_kanComplex`、`stableHatGL_kanComplex` | 監査済み | 係数環と実際の安定 ĜL の Kan 性 |
| `simplicialRingHatGLCoefficientHomotopyMulEquiv` | 監査済み | 追加仮定のない有限 rank の高次の係数表示 |
| `hatGLCoefficientHomotopy_stabilization`、`hatGLRankCoefficientIso` | 監査済み | rank の安定化の可換性と群の図式の自然同型 |
| `coefficientMatrixRankSequence`、`stableCoefficientMatrices` | 監査済み | 係数群の行列と単位による安定化の実際の群の余極限 |
| `stableHatGLHomotopyIsColimit`、`stableHatGLHomotopyGroupColimitIso` | 監査済み | K-L9 の定理による実際の安定群の余極限 |
| `stableHatGLBarPositiveHomotopyMulEquiv` | 監査済み | 安定 ĜL と分類空間の正次数の群の delooping |
| `monoidBarKanConnected` | 監査済み | KST Lemma 2.13 の連結な Kan 模型 |
| `lemma_2_13_pi_one` | 監査済み | GL(π₀A) と基本群の乗法同値 |
| `lemma_2_13_higher` | 監査済み | 分類空間の全高次の群と安定係数行列群の乗法同値 |
| H_* | 基礎・相対長完全列・局所係数の鎖複体は監査済み | セル添付と Kan 置換の比較を継続 |
| plus 構成 | 未実装 | 局所係数の acyclic map と π₁ の商 |
| K₀・K₁ の比較 | 未実装 | KST Theorem 2.16 の次数 0、1 |
| ∞-S• との比較 | K1a の供給を確認予定 | KST Proposition 2.15 |

## 13. 原典の所在

- [Moss 2020 原論文](https://link.springer.com/article/10.1007/s40062-019-00247-y)
- [Segal 1974 原論文 PDF](https://ncatlab.org/nlab/files/SegalCategoriesAndCohomologyTheories.pdf)
- [KST arXiv:1611.08466v4](https://arxiv.org/pdf/1611.08466v4)
- [Schwede–Shipley 2003 原論文 PDF](https://people.math.rochester.edu/faculty/doug/otherpapers/schwede-shipley2.pdf)

上の原典は設計の照合に用いる。
原典への参照だけを Lean の証明にすることはない。
