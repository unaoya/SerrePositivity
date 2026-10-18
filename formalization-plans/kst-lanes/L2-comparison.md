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
Lemma 1.8 の telescope の貼り合わせも証明した。Proposition 1.6 の対角化の貼り合わせは残工程である。

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
fat realization と対角の比較の局所化可逆性は、この順序余極限の定理だけでは得られず別途残る。

### fat realization の各行の局所化同型に対する不変性

確認する文言：各行で anodyne 局所化同型である二重単体集合の射は、
fat realization 全体でも anodyne 局所化同型を誘導する。
証明方針：各有限骨格の不変性を骨格の順序列の自然変換へ適用する。
骨格の包含は単射であり、既存の KanSequentialColimitComparison の
具体的な余錐の比較を、実際の fat realization の包含の余錐へ適用する。
これは対角への自然な比較の可逆性とは別の主張である。

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
hornSubdivisionComparison_inclusion で包含との可換性を証明した。
doubleSubdivisionHornMap_boundary で二重細分の候補の horn 上の境界条件を証明した。
二回の随伴で転置し、任意の horn の写像が二回の Ex の後で充填できることを証明した。
有限単体集合から Ex∞ への写像の有限段階への因子化と遷移との整合を証明した。
exInfinity_kanComplex により Ex∞ の Kan 性（Moss Proposition 21）を証明した。
有限極限保存・anodyne な単位・Kan 性が揃い、Ex∞ は実際の Kan 置換となった。
Ex∞ の単射保存と局所化可逆な射の保存・反映を証明した。
Ex∞ の monoidal 構造と、内部モノイドの置換・単位を構成した。
既存の SimplicialObject MonCat と内部モノイドの移送を構成し、基礎単体集合の一致を証明した。
単体的モノイドの Ex∞ 置換と単位を構成し、基礎対象の Kan 性と単位の局所化可逆性を証明した。
π₀ のモノイド射の関手性、置換が π₀ のモノイド同型を誘導し群状性を保つことを証明した。
有限積座標の射の局所化可逆性と、bar の各行の Segal 座標の自然性を証明した。
既存の行ごとの局所化可逆性の対角化定理で、bar の模型の局所化不変性を証明した。
Ex∞ のモノイド置換への bar の比較射が局所化可逆であることを証明した。
Kan モノイドの有限積座標・bar の基底と全空間の各行の Kan 性を証明した。
正則 bar の各行の射影が Kan fibration であることを証明した。
二重写像円筒を実際の pushout として定義し、比較写像とその恒等・合成の保存を証明した。
スライスのファイバー関手の余極限・pushout 保存と、その標準比較同型を証明した。
円筒の端点の余積を C⊗∂Δ[1] と同定し、貼り付けの脚の単射性を証明した。
局所化可逆な二項余積の射、単射な脚を持つ pushout の比較の可逆性を証明した。
span の各成分の局所化可逆な比較が二重写像円筒で可逆となることを証明した。
円筒の端点の自然性の四角形と、二つの引き戻しの二項余積の引き戻し性を証明した。
adhesive 性による立方体の貼り合わせから、span の厳密な引き戻しについて、
二重写像円筒の中央の円筒・左右の頂点・中央の頂点の各四角形の引き戻し性を証明した。
部分対象を保つ二段階の収縮から、包含の anodyne 性を相対ホモトピーの持ち上げで証明した。
Kan fibration に沿う horn の逆像と、任意の anodyne 射の引き戻しの anodyne 性を証明した。
スライスの積の右随伴が、任意の Kan fibration を保つことも証明した。基底の Kan 性は不要。
二段階の収縮を任意の端点の向きへ一般化し、順序集合の nerve の部分対象にも適用した。
部分型の nerve と全頂点を指定した部分単体集合との同型を構成した。
horn の安全な面へ頂点 k を加える収縮から、面の部分順序集合の nerve の包含の anodyne 性を証明した。
余面の分裂による頂点集合の復元と、面の nerve の余面による被覆を証明した。
実際の正次元 horn の細分比較の各次数の全射性と epi 性を証明した。
細分の元の標準単体による表示を密度の余極限から証明し、horn の細分の元も余面で覆われることを証明した。
異なる余面表示の共通の小さい面への持ち上げから、実際の正次元 horn の細分比較の単射性・同型性を証明した。
この同型で細分された horn の anodyne 性を移し、sd の anodyne 保存と Ex の Kan fibration 保存を証明した。
horn と標準単体の有限表示可能性による arrow の順序余極限で、Ex∞ の Kan fibration 保存を証明した。
有限極限保存と局所化後の単位の同型を合わせ、任意の基底での Kan fibration に沿う局所化同型の引き戻しを証明した。
固定した任意の基底でのホモトピー引き戻し模型の左右の入力の不変性を証明した。
基底も動く Kan fibration の cospan の比較と、ホモトピー引き戻し模型の三入力の不変性を証明した。
標準比較射の自然性、四つの頂点の局所化同型によるホモトピー引き戻し性の保存・反映を証明した。
Ex∞ が四角形のホモトピー引き戻し性を保存・反映することを証明した。
厳密な引き戻しの pushout の覆いでの Kan fibration の局所性と、積・余積の Kan fibration 保存を証明した。
厳密な引き戻しの span の三縦射が Kan fibration なら、二重写像円筒の比較も Kan fibration と証明した。
ホモトピー引き戻し性の脚の交換の不変性と、三頂点のホモトピー引き戻し性の厳密な場合を証明した。
図式の射の関手的な成分ごとの anodyne–Kan 分解と、その自然性・因子化を構成した。
二重写像円筒を span の関手とし、左・右・中央の頂点の写像を自然変換にまとめた。
Kan 分解は span の二面と、円筒への三頂点の四角形のホモトピー引き戻し性を保存・反映すると証明した。
一般の homotopy-cartesian な二面から、縦射が Kan fibration の場合への還元は証明済み。
二つの Kan なファイバー模型へ向かう局所化同型を、共通の trivial fibration の模型で比較することを証明した。
部分切断の実際の対象と元の全空間からの包含を構成し、随伴表示による復元と一意性を証明した。
単射に沿う trivial fibration の延長と、元の射が厳密な引き戻しであることを証明した。
これらを span の模型の置換に組み合わせ、両面が厳密な引き戻しとなる span を構成した。
単射な基底への置換、任意の基底に沿う right properness、Ex∞ と縦射の Kan 分解で
追加の Kan 性・単射性の仮定を取り除き、Segal Lemma 1.7 の一般形を証明した。
添字付き余積を各次数の依存和として構成し、添字を写す成分ごとの厳密な引き戻しを余積へ移した。
成分ごとの Kan fibration・局所化同型の余積保存と、右縦射が Kan のホモトピー引き戻しの余積保存を証明した。
偶数・奇数の余積の span と二重写像円筒から、実際の telescope 関手を構成した。
中央の Kan fibration を用いる横の貼り合わせ、隣接段からの帰納、成分ごとの Kan 分解から、
各偶数・奇数段の telescope への四角形を追加仮定なしで証明した（Segal Lemma 1.8）。
任意の固定単体集合との直積がホモトピー引き戻しを保つことを証明した。
各行と標準単体の積から対角模型への評価、自然性、dinatural な関係式、恒等単体の計算を証明した。
dinatural な射の族を対角からの射へまとめる desc と、各行の復元・一意性を証明した。
単射の面の関係式の余等化子として fat realization の実対象を構成した。
各行の包含、面の関係式、desc の計算則と射の一意性、関手性を証明した。
対角への実際の比較を自然変換とし、各行の評価との一致を証明した。
単体圏の像分解の単射との後合成と全射の場合の輸送を証明した。
任意の epi–mono 分解による正規化の計算、面の関係式での不変性、全射の復元を証明した。
各次数の実際の余等化子へ正規化を降ろし、各行からの包含による両逆性を証明した。
fat realization の各次数と全射な標準形の型との同値を構成した。
標準形の自然性から、各行で単射の射の fat realization の単射性を証明した。
単体作用後の正規化の式と終域の次元の減少を証明した。
正規化した終域の次元による有限骨格の部分単体集合を構成した。
骨格の単調性、各次数での安定化、全骨格の和が全体となること、各行の像の包含を証明した。
各行の骨格への因子化、骨格の関手、全体への自然な包含を構成した。
骨格の順序列の実際の包含の余錐が fat realization を余極限とすることを証明した。
新しい行の旧骨格の逆像が境界であることと、境界外の単射性を標準形で証明した。
境界の付着の厳密な引き戻し、旧骨格と新しい行の共同全射性から、
一段階の骨格の付着の実際の pushout の普遍性を証明した。
mapping cylinder の実対象、底の anodyne な包含、底への収縮の局所化可逆性を証明した。
二重写像円筒の三部分の desc の普遍性から、一端ずつ貼る二段階の pushout 表示を証明した。
右の脚が単射なら、二重写像円筒を通常の pushout へ潰す比較が局所化同型であると証明した。
円筒から任意の具体的な span の余極限への比較と、各頂点・余錐の比較に関する自然性を証明した。
単射な右脚の通常の pushout の各頂点へ、Lemma 1.7 のホモトピー引き戻し性を移した。
任意の余錐の基底上への持ち上げと、固定した射の厳密ファイバーの余極限保存を証明した。
各頂点で同じ固定射へのホモトピー引き戻し性を、単射な脚の span の余極限へ貼り合わせる定理を証明した。
全ての非空な部分族の交叉から有限和へ進む分配束の帰納補題を証明した。
部分単体集合の分配束構造を既存の束演算のまま証明し、積と部分対象の有限被覆の比較を構成した。
境界の余面の有限被覆と頂点集合による交叉を計算し、適切な非空な面の比較から境界全体のホモトピー引き戻し性を証明した。
適切な非空な境界の面の低次元の標準単体表示と、包含の単射な単体圏の射との一致を証明した。
小さい行から指定した骨格への射、行・境界の付着の自然性、各面での因子化を証明した。
各行の Kan 性と低い行の比較から境界の付着のホモトピー引き戻し性を得た。
零骨格と第零行と標準零単体の積との実際の同型も証明した。
中央の Kan 性を課さないホモトピー引き戻しの横の貼り合わせを、三縦射の関手的 Kan 分解で証明した。
付着の実際の span とその余極限・自然性を構成し、旧骨格と新しい行から次の骨格への比較を証明した。
各行が Kan fibration の場合、全ての m ≤ n 行から n 骨格へのホモトピー引き戻し性の帰納を完了した。
各行の局所化同型による有限骨格の不変性を証明し、各行の Kan 性を仮定しない有限骨格の比較へ移した。
上側二つの図式の遷移が単射な順序余極限の四角形のホモトピー引き戻し保存を証明した。
各行を含む骨格の余終な尾と定数図式に適用し、各行から fat realization 全体への比較を証明した。
各行の局所化同型に対する fat realization 全体の不変性も証明した。
対角への比較の局所化可逆性は未証明。
Proposition 1.6 の対角化の貼り合わせは未証明。
対角化後の bar 束の homotopy-cartesian 性と、Segal 比較は未証明。
L2b、L2c、L2d、L2e は未完了である。
§10-5 は検証する文言と証明方針を記した段階である。
ĜL の対象は正本 §13-10 に従い群状単体的モノイドとする。
検証：`lake build SerrePositivity.KST.Comparison` は成功した。
検証：`lake env lean scripts/audit_kst_comparison.lean` は終了コード 0。
主要 988 宣言の型と公理を確認した。
さらに名前空間全体の 1805 宣言（自動生成された公開補題・射影を含む）を許可リストで検査し、標準三公理のみを確認した。
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
| `hornChainToHorn`、`doubleSubdivisionHornMap` | 実装済み | 二重細分から horn への具体的な写像 |
| `HornFacePoset`、`hornChainToHorn_boundary` | 実装済み | horn の面の nerve 上の境界条件 |
| `hornSubdivisionComparison`、`hornSubdivisionComparison_lastVertex` | 実装済み | 実際の horn の細分比較と最終頂点との一致 |
| `subdivisionLastVertexMap`、`subdivisionLastVertexMap_stdSimplex` | 実装済み | 全対象の最終頂点と標準単体上の計算 |
| `doubleSubdivisionHornMap_boundary`、`exDoubleHornFiller_boundary` | 実装済み | 二重細分の境界条件と二回の Ex の後の horn の充填 |
| `exInfinity_finite_factorization`、`exInfinityStage_succ` | 実装済み | 有限段階への因子化と反復列の遷移 |
| `exInfinity_hornFilling`、`exInfinity_kanComplex` | 実装済み | Moss 2020 Proposition 21 の Kan 性 |
| `exInfinity_map_localized_isIso_iff`、`exInfinity_preservesMonomorphisms` | 実装済み | 局所化可逆な射の保存・反映と単射保存 |
| `exInfinitySimplicialMonoidFunctor`、`exInfinitySimplicialMonoidUnit` | 実装済み | モノイド構造を保つ実際の Kan 置換 |
| `exInfinitySimplicialMonoid_componentsMulEquiv`、`exInfinitySimplicialMonoid_isGrouplike` | 実装済み | π₀ モノイドと群状性を保つ置換 |
| `monoidTupleMap_localized_isIso`、`monoidBarMap_localized_isIso` | 実装済み | 有限積座標と bar の局所化不変性 |
| `exInfinitySimplicialMonoid_bar_localized_isIso` | 実装済み | Kan モノイドへの置換が誘導する bar の可逆性 |
| `monoidBarRow_kanComplex`、`regularBarRow_kanComplex`、`actionBarProjection_row_rlp` | 実装済み | Kan モノイドの各行と射影の Kan 条件 |
| `doubleMappingCylinder`、`doubleMappingCylinderMap`、`doubleMappingCylinderMap_comp` | 実装済み | 実際の二重写像円筒と比較の関手性 |
| `sliceFiberPushoutIso`、`cylinderEndpoints_mono` | 実装済み | 厳密なファイバーと pushout の交換、貼り付けの単射性 |
| `pushoutMap_localized_isIso`、`doubleMappingCylinderMap_localized_isIso` | 実装済み | pushout と二重写像円筒の模型の局所化不変性 |
| `cylinderEndpoints_isPullback`、`coproductSquare_isPullback` | 実装済み | 円筒の境界と二項余積の厳密な引き戻し |
| `strictPushoutCube`、`doubleMappingCylinderMap_isPullback` | 実装済み | van Kampen 性による厳密な貼り合わせ |
| `doubleMappingCylinder_left_isPullback`、`doubleMappingCylinder_right_isPullback`、`doubleMappingCylinder_center_isPullback` | 実装済み | 三つの頂点の厳密な引き戻し |
| `subcomplex_inclusion_anodyne`、`horn_preimage_anodyne` | 実装済み | 二段階の収縮による相対持ち上げと horn の逆像の anodyne 性 |
| `sliceFiberRightAdjoint_rlp`、`pullback_anodyne` | 実装済み | 任意の基底での Kan fibration に沿う anodyne 射の基底変換 |
| `subcomplex_pairContraction_anodyne`、`orderNerveSubcomplex_anodyne` | 実装済み | 任意の向きの収縮と順序集合の nerve への適用 |
| `orderNerveSubcomplexIso`、`orderSubtypeNerve_anodyne` | 実装済み | 部分型の nerve と部分単体集合の比較 |
| `hornFaceInclusion_anodyne` | 実装済み | horn の安全な面の nerve の包含の anodyne 性 |
| `simplexFaceRetraction_chain`、`hornFaceNerve_faceCover` | 実装済み | 余面の分裂と面の nerve の余面による被覆 |
| `hornSubdivisionComparison_app_surjective`、`hornSubdivisionComparison_epi` | 実装済み | 実際の細分比較の全射性 |
| `subdivisionSimplexCover`、`hornSimplexFaceFactorization`、`hornSubdivisionFaceCover` | 実装済み | 密度による細分の表示と horn の余面表示 |
| `subdivisionCommonFace`、`hornSubdivisionComparison_isIso` | 実装済み | 共通の余面表示と実際の細分比較の同型性 |
| `subdivisionHorn_anodyne`、`subdivision_map_anodyne`、`ex_map_rlp` | 実装済み | 実際の sd の anodyne 保存と Ex の Kan fibration 保存 |
| `hornRight_sequentialColimit`、`exInfinity_map_rlp` | 実装済み | horn の有限表示可能性による Ex∞ の Kan fibration 保存 |
| `pullback_localized_isIso`、`sliceFiberFunctor_localized_isIso_anyBase` | 実装済み | 任意の基底での Kan fibration に沿う局所化同型の引き戻し |
| `pullbackMapBase_localized_isIso`、`homotopyPullbackMap_localized_isIso_fixed_base` | 実装済み | 任意の固定基底での左右の入力の比較 |
| `fibrantCospanMap_localized_isIso`、`homotopyPullbackMap_localized_isIso` | 実装済み | 基底も動かす三入力の比較 |
| `homotopyPullbackComparison_naturality`、`isHomotopyPullback_iff_of_localized_isIso` | 実装済み | 標準比較射の自然性と四つの頂点の置換 |
| `isHomotopyPullback_exInfinity_iff` | 実装済み | Ex∞ によるホモトピー引き戻しの保存・反映 |
| `lifting_of_pullbackFactorizations`、`kanFibration_of_pushoutCover` | 実装済み | 単体ごとの厳密な引き戻しの覆いによる Kan 条件の局所性 |
| `tensorRight_rlp`、`coproductMap_rlp`、`doubleMappingCylinderMap_rlp` | 実装済み | 厳密な引き戻しの span の円筒の比較の Kan 条件 |
| `isHomotopyPullback_flip_iff`、`isHomotopyPullback_of_left_fibration` | 実装済み | 脚の交換と左脚が Kan fibration の場合の判定 |
| `doubleMappingCylinder_homotopyPullbacks_of_strict` | 実装済み | 厳密な引き戻し・縦射が Kan fibration の場合の三頂点 |
| `diagramKanMiddle`、`diagramKanUnit`、`diagramKanProjection`、`diagramKan_fac` | 実装済み | 関手的な図式の成分ごとの anodyne–Kan 分解 |
| `spanCylinderFunctor`、`spanCylinderVertex` | 実装済み | span の円筒の関手と三頂点の自然性 |
| `diagramKan_arrowSquare_iff`、`spanCylinderKan_vertexSquare_iff` | 実装済み | 縦射が Kan fibration の場合への還元 |
| `commonTrivialFibrationRefinement` | 実装済み | 二つのファイバー模型の共通の trivial fibration の模型 |
| `partialSectionObject`、`partialSectionObject_allMono_rlp` | 実装済み | 部分切断の実対象と全体の trivial fibration 性 |
| `partialSectionAdjunct`、`partialSectionRestrictionLift_unique` | 実装済み | 随伴表示、復元、存在と一意性 |
| `partialSectionInclusion_isPullback`、`trivialFibrationExtension` | 実装済み | 単射に沿う延長と制限の厳密な引き戻し |
| `spanStrictification_of_mono` | 実装済み | 共通の trivial fibration の延長による厳密な span への置換 |
| `diagramPullback_arrowSquare_iff`、`diagramExInfinity_arrowSquare_iff` | 実装済み | 基底変換と Ex∞ による二面の比較 |
| `spanCylinder_vertexSquare_map_iff` | 実装済み | 成分ごとの局所化同型による円筒の頂点の四角形の比較 |
| `spanCylinder_vertex_homotopyPullback` | 実装済み | Segal Lemma 1.7、追加の Kan 性・単射性なし |
| `simplicialSum`、`simplicialSumIsCoproduct` | 実装済み | 次数ごとの依存和による実際の添字付き余積 |
| `simplicialSumReindex_isPullback`、`simplicialSumInclusion_isPullback` | 実装済み | 任意の添字の写像と成分の包含の引き戻し |
| `simplicialSumMap_rlp`、`simplicialSumMap_localized_isIso` | 実装済み | 成分ごとの Kan fibration と局所化同型の余積保存 |
| `simplicialSumReindex_homotopyPullback_of_fibrations` | 実装済み | Kan な右縦射を持つホモトピー引き戻しの余積 |
| `isHomotopyPullback_paste_horiz_of_middle_fibration` | 実装済み | 中央の Kan fibration を用いる横の貼り合わせ |
| `sequenceArrow_homotopyPullback_of_successors` | 実装済み | 隣接段から任意の遷移への帰納 |
| `telescopeSpan`、`telescopeSpanFunctor`、`telescopeFunctor` | 実装済み | 偶数・奇数段の余積による telescope の模型 |
| `telescopeEvenStage`、`telescopeOddStage` | 実装済み | 全ての偶数・奇数段の telescope への自然変換 |
| `telescopeFunctor_map_localized_isIso` | 実装済み | 成分ごとの局所化同型による telescope の不変性 |
| `telescopeStages_homotopyPullback` | 実装済み | Segal Lemma 1.8、隣接段の仮定のみ |
| `isHomotopyPullback_map_of_preserves_factorizations` | 実装済み | 分解・引き戻し・局所化同型を保つ関手による保存 |
| `tensorRight_isPullback`、`isHomotopyPullback_tensorRight` | 実装済み | 任意の固定単体集合との積の引き戻しの保存 |
| `diagonalRowEvaluation`、`diagonalRowEvaluation_dinaturality` | 実装済み | 各行と標準単体の積から実際の対角への整合する射 |
| `diagonalRowDesc`、`diagonalRowEvaluation_desc`、`diagonalRowDesc_unique` | 実装済み | 対角模型の行の余極限表示の普遍性 |
| `SimplexFace`、`fatRelationLeft`、`fatRelationRight`、`fatRealization` | 実装済み | 単射の面の関係式による余等化子の実対象 |
| `fatRealizationInclusion_face`、`fatRealizationDesc`、`fatRealization_hom_ext` | 実装済み | 面の関係式と余積・余等化子の普遍性 |
| `fatRealizationFunctor`、`fatRealizationToDiagonalNatTrans` | 実装済み | 実際の関手と対角への自然な比較（可逆性は未証明） |
| `simplexImage_comp_mono`、`simplexFactorThruImage_of_epi` | 実装済み | 単体圏の epi–mono 分解の対象・二因子の輸送 |
| `FatNormalForm`、`fatNormalize`、`fatNormalize_face` | 実装済み | 全射な標準形と面の関係式での不変性 |
| `fatDegreeCoforkIsColimit`、`fatDegreeNormalize` | 実装済み | 各次数の実際の余等化子へ降りる正規化 |
| `fatNormalFormRealize`、`fatNormalFormEquiv` | 実装済み | 各行の包含による逆写像と各次数の全射な標準形との同値 |
| `fatDegreeNormalize_map`、`fatRealizationMap_mono` | 実装済み | 標準形の自然性と各行の単射性の保存 |
| `fatDegreeNormalize_action`、`fatNormalDegree_action_le` | 実装済み | 単体作用後の正規化と終域の次元の減少 |
| `fatSkeleton`、`fatSkeleton_monotone`、`iSup_fatSkeleton_eq_top` | 実装済み | 標準形の次元による部分単体集合の濾過と全体の復元 |
| `fatSkeleton_obj_eq_univ`、`fatRealizationInclusion_mem_skeleton` | 実装済み | 各次数での安定化と各行の像の包含 |
| `fatSkeletonRow`、`fatSkeletonFunctor`、`fatSkeletonInclusion` | 実装済み | 各行の骨格への因子化と骨格の関手性 |
| `fatSkeletonSequence`、`fatSkeletonCoconeIsColimit` | 実装済み | 実際の有限骨格の順序余極限としての fat realization |
| `fatRealizationInclusion_mem_skeleton_iff_boundary` | 実装済み | 新しい行の旧骨格の逆像と境界の同定 |
| `fatRealizationInclusion_injective_off_boundary_range` | 実装済み | 境界の像の補集合での単射性 |
| `fatBoundaryAttachment`、`fatBoundaryAttachment_isPullback` | 実装済み | 境界の旧骨格への付着と厳密な引き戻し |
| `fatSkeletonStep_row_jointly_surjective`、`fatSkeleton_isPushout` | 実装済み | 一段階の付着の共同全射性と pushout の普遍性 |
| `mappingCylinder`、`mappingCylinderBase_anodyne`、`mappingCylinderRetraction_localized_isIso` | 実装済み | 片端を貼った円筒の底への収縮 |
| `doubleMappingCylinderDesc`、`doubleMappingCylinder_hom_ext` | 実装済み | 三部分の射による二重写像円筒の普遍性 |
| `mappingCylinderToDouble_isPushout` | 実装済み | 一端ずつ貼る二段階の pushout 表示 |
| `doubleMappingCylinderCollapse_localized_isIso` | 実装済み | 右の脚が単射の場合の通常の pushout への比較の可逆性 |
| `spanCylinderToColimit`、`spanCylinderToColimit_naturality` | 実装済み | 任意の具体的な余極限への円筒の自然な比較 |
| `spanPushout_vertex_homotopyPullback` | 実装済み | 単射な脚の通常の pushout の各頂点への貼り合わせ |
| `spanColimit_map_localized_isIso` | 実装済み | 具体的な span の余極限への成分ごとの可逆性の移送 |
| `coconeOverCoconeIsColimit`、`fiberCoconeIsColimit` | 実装済み | スライスへの持ち上げと厳密ファイバーの余極限保存 |
| `coconeBaseFiberComparison`、`coconeBase_homotopyPullback_of_span` | 実装済み | 同じ固定射への四角形の各頂点から余極限への貼り合わせ |
| `finiteSup_of_nonempty_intersections` | 実装済み | 有限交叉の条件を有限和へ移す束の帰納 |
| `subcomplexUnionCoconeIsColimit`、`tensorSubcomplexUnionCoconeIsColimit` | 実装済み | 部分対象の和とその積の実際の pushout |
| `tensorLeft_mono_of_mono`、`subcomplexDistribLattice` | 実装済み | 積の単射保存と部分対象の分配束構造 |
| `tensorSubcomplex_homotopyPullback_sup`、`tensorSubcomplex_homotopyPullback_bot` | 実装済み | 二つの部分対象の和と空対象の比較 |
| `tensorSubcomplex_homotopyPullback_top_iff`、`tensorSubcomplex_homotopyPullback_of_finset_cover` | 実装済み | 有限被覆から全体への比較 |
| `boundaryVertexFace_finset_inf`、`boundaryVertexFace_coface_cover` | 実装済み | 境界の余面の被覆と有限交叉 |
| `tensorBoundary_homotopyPullback_of_faces` | 実装済み | 適切な非空な面から境界への貼り合わせ |
| `subcomplexPreimageIsoOfLE` | 実装済み | 包含に沿う小さい部分対象の逆像の実際の同型 |
| `boundaryVertexFace_representation`、`boundaryVertexFaceIso_hom_ι` | 実装済み | 低次元の標準単体による面の表示と包含との一致 |
| `fatSkeletonRowOfLE_map`、`fatBoundaryAttachment_map` | 実装済み | 指定骨格への行と境界の付着の自然性 |
| `fatBoundaryAttachment_face` | 実装済み | 境界の面の低い行による因子化 |
| `tensorRestriction_homotopyPullback_iff` | 実装済み | 右因子の同型による比較の保存・反映 |
| `fatBoundaryAttachment_homotopyPullback` | 実装済み | 各行の Kan 性の下で低い行から境界の付着への比較 |
| `fatSkeletonRow_zero_isIso` | 実装済み | 零骨格と第零行の積の同型 |
| `kanReplacementSquare_homotopyPullback_iff` | 実装済み | 関手的な縦射の Kan 分解による四角形の比較 |
| `isHomotopyPullback_paste_horiz` | 実装済み | Kan 性を仮定しない二つの四角形の横の貼り合わせ |
| `fatAttachmentCoconeIsColimit`、`fatAttachmentSpanMap` | 実装済み | 骨格の実際の付着の span の余極限と比較 |
| `fatSkeleton_successor_homotopyPullback` | 実装済み | 境界から旧骨格・新しい行の次骨格への比較 |
| `fatSkeletonRow_homotopyPullback` | 実装済み | 各行の Kan 性の下で全ての有限骨格の行の比較 |
| `fatSkeletonMap_localized_isIso` | 実装済み | 各行の局所化同型に対する有限骨格の不変性 |
| `fatSkeletonRow_general_homotopyPullback` | 実装済み | Kan 性を仮定しない全ての有限骨格の行の比較 |
| `isHomotopyPullback_iff_alternative_fiber` | 実装済み | 任意の厳密なファイバーへの局所化同型による判定 |
| `sequentialColim_rlp`、`sequentialColim_preservesPullbacks` | 実装済み | 順序余極限の Kan fibration と厳密な引き戻しの保存 |
| `sequentialFiberComparison_app_localized_isIso` | 実装済み | 図式圏のファイバーへの各成分の比較 |
| `sequential_homotopyPullback`、`actual_sequential_homotopyPullback` | 実装済み | 単射な順序列のホモトピー引き戻しの実際の余極限への保存 |
| `fatSkeletonTailCoconeIsColimit`、`fatSkeletonTailRow_map` | 実装済み | 各行を含む骨格の余終な尾の普遍性と自然性 |
| `fatRealizationInclusion_homotopyPullback` | 実装済み | 各行から fat realization 全体への比較 |
| `fatRealizationMap_localized_isIso` | 実装済み | 各行の局所化同型に対する全体の不変性 |
| Segal Proposition 1.6 | 未証明 | 対角化の貼り合わせ |
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
