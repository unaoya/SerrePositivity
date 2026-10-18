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
対角化後の bar 束の homotopy-cartesian 性、Segal 比較は未証明。
L2b、L2c、L2d、L2e は未完了である。
§10-5 は検証する文言と証明方針を記した段階である。
ĜL の対象は正本 §13-10 に従い群状単体的モノイドとする。
検証：`lake build SerrePositivity.KST.Comparison` は成功した。
検証：`lake env lean scripts/audit_kst_comparison.lean` は終了コード 0。
主要 248 宣言の型と公理を確認した。
さらに名前空間全体の 619 宣言（自動生成された公開補題・射影を含む）を許可リストで検査し、標準三公理のみを確認した。
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
| 群完備化・Segal 比較定理 | 未証明 | Segal Proposition 1.5、KST Lemma 2.13 |
| H_* | 未実装 | 正規化自由アーベル群複体 |
| plus 構成 | 未実装 | acyclic map と π₁ の商 |
| K₀・K₁ の比較 | 未実装 | KST Theorem 2.16、次数 0、1 |
| ∞-S• との比較 | K1a 接続前 | KST Proposition 2.15 |

## 13. 原典の所在

- [Segal 1974 原論文 PDF](https://ncatlab.org/nlab/files/SegalCategoriesAndCohomologyTheories.pdf)
- [KST arXiv:1611.08466v4](https://arxiv.org/pdf/1611.08466v4)
- [Schwede–Shipley 2003 原論文 PDF](https://people.math.rochester.edu/faculty/doug/otherpapers/schwede-shipley2.pdf)

上の原典は設計の照合に用いる。
原典への参照だけを Lean の証明にすることはない。
