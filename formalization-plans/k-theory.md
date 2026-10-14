# K理論・スペクトル・dg 理論の形式化計画

作成日：2026-10-13。状態：M1・M2の基盤を実装中。球面対称列の可換モノイド構造まで完成。
基本構成、smashの交換・単位・結合同型、基点付き内部 Hom と随伴を実装済み。
smashのpentagon・triangle・二つのhexagonを証明し、閉対称モノイダル構造を登録済み。
対称列、各段の置換作用、直和の関手、左Kan拡張によるconvolutionと普遍性も構成済み。
添字圏の直和の対称モノイダル構造と、convolutionのモノイダル構造を登録済み。
convolutionの対称構造と、endによる内部 Hom・評価・余評価も構成済み。
内部 Hom との随伴を構成し、convolutionの閉対称モノイダル構造まで登録済み。
球面対称列の各段となる円の反復smash、次数の連結同型、最初の二因子の交換を構成済み。
全位置の隣接交換、対合性・遠隔可換性・braid関係も証明済み。
TypeAを共通群論へ移植し、一般の反復テンソルと円の反復smashの全次数の置換作用を実装済み。
各段の作用を全単射圏上の関手へまとめ、球面対称列まで構成済み。
連結の左右単位・結合の整合性と、左右ブロックの隣接交換との両立も証明済み。
全次数の任意の左右ブロック置換に関する、連結の同変性まで証明済み。
連結を自然変換へまとめ、convolution上の乗法とその因子化・一意性も構成済み。
単位射とその因子化・一意性、左右の標準射上での単位比較も構成済み。
二段のKan拡張の普遍性で、convolution全体の左右単位則まで証明済み。
乗法の結合則も証明し、一般の反復テンソルと球面対称列のモノイド構造まで登録済み。
可換性を各次数のブロック全体の交換へ帰着し、第0段を含む交換は証明済み。
先頭因子を末尾へ送る巡回置換の作用と、隣接交換の列・braidingによる射の一致も証明済み。
第1段と任意の段の左右のブロック交換と連結の両立も証明済み。
一般のブロック交換と乗法の可換性も証明し、球面対称列の可換モノイド構造まで登録済み。
球面モノイドの加群として対称スペクトルの対象・射・圏と、各次数・懸垂の構造射まで構成済み。
自由内部加群の一般論と、自由対称スペクトル・忘却関手の随伴も構成済み。
各段の評価の左随伴と、第n段を生成する自由スペクトルF_nも構成済み。
内部加群の極限・余極限と、対称スペクトルの各段の比較同型も構成済み。
自由スペクトルの各段の分解図式・生成元・ブロック作用の関係式と、n未満の段の零対象性も証明済み。
生成元の関係式を満たす射の族からの延長・一意性と、各段からの射とのHom同値も構成済み。
第二ブロックnの誘導図式の余極限と自由スペクトルの各段との比較同型も構成済み。
出力の全単射と入力の射に関する自然性、対称群作用付きの各段との自然同型も構成済み。
第一ブロックの対称群の関係式による余等化子を構成し、自由スペクトルの各段との比較同型も構成済み。
明示的な商上の出力の対称群作用と入力の同変射、各段・誘導表示との作用付き自然同型も構成済み。
n以上の段ではΣ_mで添字付けた誘導商と、自由スペクトルの各段との作用付き自然同型も構成済み。
球面上のテンソル積の基礎となる釣り合い商の対称列、釣り合い射の普遍性と二変数の関手性も構成済み。
商上へ球面作用を降ろし、対称スペクトルのテンソル積と二変数関手、線形な釣り合い射の降下も構成済み。
最新の実装範囲と検証は末尾の「実施記録」を参照する。

## 1. 目的と採用方針

最終目標は、原論文 *Positivity of Serre's Intersection Multiplicity* の定理3.1と補題4.6を
基盤から定式化し、現在保留している二つの降下入力を証明へ置き換えること。
完成済みの§3・§4・§5の比較や主定理への接続は利用し、その下のK理論の依存を解消する。

採用する方針は次のとおり。

1. K₀だけへ切り詰めず、非連結K理論スペクトルの水準で定理3.1を扱う。
2. 論文専用の固定点・totalizationを先に作らず、再利用できるホモトピー論とdg 理論を整備する。
3. 主モデルは、基点付き単体的集合上の対称スペクトルを第一選択とする。
4. 有理複体は、有理スペクトルの比較・計算モデルとして後から接続する。
5. 基礎理論の深い一般定理は、正確なステートメントを持つ名前付きの `sorry` 定理として引用できる。
6. 対象・射・演算・比較関手は具体的に定義し、何を引用しているかを追跡できるようにする。

以前検討した「K₀の帰結だけを引用して先へ進む」案は、現在の本文の完成に用いた方針である。
この新しい作業では、そこから一段下がり、スペクトル版の証明構造とdg 表示を扱う。
有理複体だけを主モデルとして始める仮案も、一般のスペクトルを基盤にする方針へ変更する。

## 2. 現在の入口と、完了の意味

2026-10-13時点のリポジトリで直接 `sorry` を含む対象は次の二つ。

| 現在の宣言 | 意味 | 置き換える証明 |
| --- | --- | --- |
| `SerrePositivity.theorem_3_1_K0` | 離散係数 H = A の支持つきK₀の有理降下 | 一般係数版の定理3.1を特殊化し、既存のK₀と比較する |
| `SerrePositivity.Section4.supportedRankK0_descent` | 補題4.6と一般係数版定理3.1をまとめた、ランク商の支持つきK₀の降下 | 実際のdg 表示、支持・群作用・係数変更の比較を介して定理3.1を適用する |

入口は [Inputs/Descent.lean](../SerrePositivity/Inputs/Descent.lean) と
[Section4/SupportedDescent.lean](../SerrePositivity/Paper/Section4/SupportedDescent.lean)。
後者の結論は、不変な類 y について正の整数 n とA側の類 x が存在し、n・y = baseChange(x)となること。

この計画の完了は、次の全てを満たすこととする。

- 定理3.1のスペクトル版と、補題4.6のdg 表示を、具体的な数学的対象について述べて証明する。
- 上の二つの宣言の直接の `sorry` を除き、一般定理からの導出に置き換える。
- スペクトルの π₀ と既存の二種類のK₀、各係数変更、群作用の対応を証明する。
- §3・§4とその利用先が引き続きビルドを通る。
- 残る未証明依存が、明示して精査した基礎定理・外部文献の引用だけであることを監査する。

「直接の `sorry` がなくなった」ことと「標準公理だけで証明した」ことは区別する。
引用として残す基礎定理の証明まで全て実装することは、この計画の初期の完了条件にはしない。
一方、定理3.1や補題4.6全体を別名の `sorry` へ移して完了とはしない。
作業途中には主要な補助定理を `sorry` で先に述べてもよいが、最終的な引用一覧には残さない。

旧会話で保留していた正則パラメータの正則性は、現在は証明済み。
この計画ではK理論の未証明入力に数えない。古い `notes/` は現在の構成にないため参照しない。
現状は [README](../README.md)、[解説](../exposition/ja/exposition-ja.tex)、
[監査](../scripts/audit_axioms.lean)を基準とする。

## 3. 最終的に述べる数学的主張

### 3.1 定理3.1：支持つき有理降下

Aを有限Krull次元の可換Noetherな ℤ_(p) 代数、Jをpを含むイデアルとする。
Hは中心的A作用を持つconnectiveな結合的導来A代数。
Tは有限可換A代数で、有限群GがA上作用する。
Spec(T) → Spec(A)は全射で、Gは各幾何ファイバーの点に推移的に作用すると仮定する。

目標は、引き戻しによる自然な同値

\[
K^J(H)_{\mathbb Q}
\simeq K^J(H\otimes_A^{\mathbf L}T)_{\mathbb Q}^{hG}.
\]

Kは非連結K理論、上付きJは中心局所化でV(J)の外で消えるperfect加群の支持を表す。
Hの可換性、A上の有限性、正のホモロジー次数の有界性、TのA平坦性、tame分岐は要求しない。
有理化するのはK理論の値であり、K(H)_ℚ と K(H ⊗ ℚ)を同一視しない。

一般のconnectiveな導来A代数をどの具体的モデルで扱うかは、スペクトル・dg 比較の段階で確定する。
dg A代数だけについて先に実装した場合、一般のHA代数との比較が終わるまでは定理3.1全体の完成としない。

### 3.2 補題4.6：connectiveな係数による表示

§4の自由列の圏から作った実際のランク商について、connectiveな結合的導来A代数Hを構成し、

\[
\mathcal P_A\simeq\operatorname{Perf}(H),\qquad
\mathcal P_T\simeq\operatorname{Perf}(H\otimes_A^{\mathbf L}T)
\]

を示す。二つの表示は、係数変更とAの元による中心局所化に関して両立する。
定理3.1へ適用するため、支持部分圏とGによるひねりの対応も証明する。
通常の自己準同型環だけでなく、選んだ生成元の自己準同型dg 代数を使う。
任意のシフトしたperfect対象の自己準同型代数がconnectiveであるとは主張しない。

### 3.3 既存のK₀への帰結

有限群の有理ホモトピー固定点の計算から、

\[
K_0^J(H)\otimes\mathbb Q\longrightarrow
\bigl(K_0^J(H\otimes_A^{\mathbf L}T)\otimes\mathbb Q\bigr)^G
\]

の全射性を得る。分母を払い、残るねじれをさらに整数倍で消し、現在の整数版へ移す。
離散係数の既存の `K0Supported` と、§4の `TriangulatedK0` は別々に比較する。
両者を定義上同じ群とは扱わない。

## 4. スペクトルのモデルの選定

| モデル | 利点 | 主な負担 | この計画での位置 |
| --- | --- | --- | --- |
| 逐次スペクトル | 列と構造写像の定義が簡潔 | 厳密な対称モノイダル構造と代数への展開 | 比較対象、必要なら基礎的な説明用 |
| 基点付き単体的集合上の対称スペクトル | smash積、結合的環、加群を同じ基盤で扱える | 対称列、球面対称列、安定モデル構造 | 主モデルの第一選択 |
| 直交スペクトル | 幾何的・同変ホモトピー論への展開 | 位相的豊穣構造、直交群、空間のモデル | 初期範囲には含めない |
| ∞圏の安定化 | 原論文の言語と直接対応 | ∞圏の極限・安定化・モノイダル構造 | 文献との比較先 |
| 非有界ℚ複体 | 有理固定点などの代数的計算 | 図式・群作用を含む比較 | 有理スペクトルの計算モデル |

対称スペクトルを採用する場合、対象を球面対称列𝕊の加群として記述する。
まず非正の通常の安定モデル構造を基準に検討し、正のモデル構造が必要な場合は用途を分ける。
結合的代数と加群を先に扱い、可換代数・E∞代数の追加条件を混同しない。

レベル同値と安定同値を区別する。対称スペクトルの安定ホモトピー群を、置換なしの各段の
ホモトピー群の素朴な極限だけで定義しない。semistabilityの問題を避けるため、
安定モデル構造・適切なfibrant replacementに基づく定義を選ぶ。
モデルの最終仕様はM0で固定し、その後は下位の具体的モデルと上位のAPIを分離する。

## 5. 現在利用できる基盤と不足

調査対象：Lean `v4.35.0-rc4`、mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
版は [lean-toolchain](../lean-toolchain) と [lake-manifest.json](../lake-manifest.json) による。
以下はこの固定版の調査であり、今後の更新時に再確認する。

| 分野 | 既存の部品 | そのまま完成済みとは扱えない範囲 |
| --- | --- | --- |
| モデル圏 | `AlgebraicTopology/ModelCategory/` | 今回のスペクトルの具体的モデル構造と図式の置換 |
| 単体的集合 | `SimplicialSet/Basic`、境界・角・Kan複体 | Kan–Quillenモデル構造の全体の接続 |
| 基点 | `CategoryTheory/Category/Pointed` | 基点付き単体的集合のsmash積と閉対称モノイダル構造 |
| 対称列 | 群作用、関手圏、Day convolutionの部品 | 有限集合の全単射圏上の対称列に対する完成したモノイダル構造 |
| 豊穣圏 | `CategoryTheory/Enriched/`、`SimplicialCategory/` | 必要なtensor・cotensor・モデル構造との接続 |
| 複体 | 非有界複体、Hom複体、導来圏、K-injective/K-projective | dg 圏・dg 商・導来tensor・perfect圏の一式 |
| 全複体 | `Algebra/Homology/TotalComplex` | 非有界cosimplicial図式の積による導来totalization |
| 群作用 | Maschke、群コホモロジー、Shapiro | 整合的な作用と非有界有理スペクトルのhGとの比較 |
| 降下 | Čech nerve、サイト、層、Čech複体 | スペクトル値の導来降下、cdh降下の接続 |
| 代数幾何 | スキーム、有限・平坦・proper射など | flatteningと必要な抽象blowupの降下を一式で使う接続 |

`SpectralObject` と `SpectralSequence` はスペクトル系列の理論であり、安定スペクトルではない。
既存の単体的集合のモノイダル構造は直積であり、smash積ではない。
既存の `TotalComplex` は対角線の余積を使う。非有界な導来極限で必要な積と区別する。
確認した複体の具体的モデル構造は有界下の場合であり、非有界の場合にそのまま流用しない。

リポジトリ内では、[自由列の生成元](../SerrePositivity/Asymptotic/FreeSequenceGenerator.lean)、
[三角圏のK₀](../SerrePositivity/CategoryTheory/TriangulatedK0.lean)、
[§4の集約](../SerrePositivity/Paper/Section4/Foundations.lean)を再利用する。
§4の三角圏・支持・群作用・評価は、スペクトルやdg 表示そのものを既に与えているわけではない。

## 6. 定義・引用・証明のルール

- 対象・射・演算を定義した後、その定義について一般定理を述べる。
- 数学的構造の法則を持つ型やクラスは使える。未証明入力をまとめた設定クラスは作らない。
- 引用の各宣言に、文献・定理番号・版・仮定・結論・自然性・使用箇所を記録する。
- 圏同値、モデル圏のQuillen同値、∞圏の同値を区別する。
- 単なる三角圏の同値から、図式のホモトピー極限や整合的群作用の対応を自動的に主張しない。
- 置換は関手として扱い、自然な比較を用意する。各対象での存在だけでは図式へ適用しない。
- K₀の帰結を証明するために、K理論スペクトルの π₀ を既存K₀と定義して済ませない。
  K理論の構成または独立した特徴づけを与え、その比較定理を述べる。
- 中間の `sorry` は許容するが、引用・作業中の未証明補題・本文の保留定理を区別して管理する。
- 最終到達点では、本文の定理3.1・補題4.6に相当する結論を含む丸ごとの引用は残さない。

## 7. マイルストーンと完了条件

各段階は、定義の形式化、一般定理の正確な定式化、接続の証明、依存監査を一組として進める。
日数やトークン数での見積もりはせず、次の成果物で進捗を判断する。

### M0：基盤仕様と引用台帳

**成果物**：主モデル、宇宙、次数、左右加群、引用範囲、予定API、依存方向の仕様。
単体的集合から対称スペクトル、dg 係数から環スペクトル、K理論までの具体的な経路を固定する。
左右加群と逆環、係数拡大の順序を選び、EndとMorita表示の向きを確認する。
全ての源・標的を実際に定義できるか確認し、名称だけの抽象 `Spectrum` で仕様を代用しない。

**完了条件**：各主要引用を型として書くために必要な対象が一覧になり、
安定同値とπₙの定義が循環しない。比較先に必要な∞圏基盤の範囲も固定する。

### M1：基点付き単体的集合

**定義**：基点付き対象・基点を保つ射、零対象、wedge、smash積、円S¹。
smash積は直積をwedgeで潰す構成とし、標準的な商またはpushoutで定義する。
閉対称モノイダル構造、suspension・loopの随伴、必要な単体的豊穣構造を整備する。
Kan–Quillenの弱同値・ファイバー化・余ファイバー化を定義し、モデル構造の存在は引用できる。

**完了条件**：単位・結合・対称性の構造と、円とのsmashを用いた構造写像を記述できる。
引用が対象の定義の代用品になっていない。

### M2：対称列と対称スペクトル

**定義**：有限集合と全単射の圏、その直和、対称列、convolution、球面対称列𝕊。
𝕊は可換モノイド、対称スペクトルは𝕊加群として構成する。
各段のΣₙ作用と反復構造写像の整合性を、この加群構造から取り出す。
評価関手、自由スペクトルとの随伴、極限・余極限、smash積を構成する。

**完了条件**：具体的なスペクトル、射、球面、suspension spectrumが存在し、
環・加群と安定モデル構造の一般定理を正確に述べられる。

### M3：安定モデル構造と安定ホモトピー論

**定義・主張**：レベルモデル構造、Ωスペクトル、安定同値、安定モデル構造、
関手的なcofibrant/fibrant replacement、導来smash、πₙ、ホモトピー圏の安定性。
安定モデル構造とモノイダル公理の適合性は、Hovey–Shipley–Smith等の一般定理として引用できる。
πₙは全整数次数で定義し、同値判定・ファイバー列の長完全列・シフトとの対応を述べる。

**完了条件**：導来ファイバー、余ファイバー、tensorと自然な比較を使える。
必要な上位定理は置換の選択から独立し、semistabilityの制限を誤って全対象へ広げていない。

### M4：図式、ホモトピー極限、群作用、有理化

**構成**：図式のprojective/injective/Reedyモデル構造の必要範囲、導来極限・余極限、
cosimplicial図式のtotalization、切断に由来するextra degeneracy。
G作用はBG上の図式として扱い、hGはそのホモトピー極限として定義する。
整合的な作用と厳密な図式を結ぶ比較も、適用範囲を明示して述べる。
有理化を一般スペクトルの局所化として構成し、非有界ℚ複体との比較を導入する。

**証明する接続**：ホモトピー極限どうしの交換、降下比較のretractへの保存、split Čech降下。
有理・有限Gについて、不変部分の完全性と全次数のホモトピー群との対応を示す。
置換作用の固定点を計算し、無界性を保持したまま原論文の(3.8)を扱う。

**完了条件**：hG、totalization、ファイバーを通常の極限で代用していない。
有界性やスペクトル系列の収束を追加仮定せず、導来極限の一般論で必要な接続を述べられる。

### M5：dg 圏、dg 加群、perfect圏、Morita理論

**構成**：Homが非有界A複体であるdg 圏、閉次数零の単位、次数つき合成とLeibniz則、
dg 関手、準同値、dg 加群、加群の導来圏、導来tensor、perfect加群。
複体の豊穣化はmathlibのHom複体・合成・微分との両立を再利用する。
perfect加群は有限cell加群のretractによる生成とコンパクト性との対応を精査する。
生成元による表示、dg 商、モデル圏・∞圏との比較は一般定理として引用できる。

**完了条件**：dg 商とそのperfect hullを既存のVerdier商・Karoubi包絡へ比較できる。
圏同値だけでなく、中心作用・scalar extensionの自然な比較を記述できる。

### M6：環・加群スペクトルと非連結K理論

**構成**：結合的環スペクトル、加群、導来tensor、コンパクト・perfect加群、
小さい冪等完備な安定圏または対応するdg モデルを入力とする非連結K理論。
K理論の源の圏、射、同値、exact sequenceの意味を先に固定する。
必要な構成定理または独立した普遍的特徴づけを正確に述べ、引用範囲を明示する。

**必要な一般定理**：Morita不変性、局所化、加法性、π₀と三角圏K₀の比較、
有限projective係数変更のtransfer、基底変更、射影公式。
Goodwillieの比較をそのまま述べる範囲では負巡回ホモロジーとcharacter mapも定義する。
この構成を引用する場合にも、自然な変換とファイバーの型を省略しない。

**完了条件**：深いK理論の証明を引用しても、本文が必要とする図式と自然性を全て述べられる。
既存のK₀への比較を単なる名称の一致として扱わない。

### M7：支持とtruncating invariantの降下

**構成**：中心局所化、支持つきperfect圏、係数のスキーム上の引き戻し。
モデルから得られるホモトピー論を使って、スキーム上の係数付きK理論のpresheafを定式化する。

原論文の証明を次の比較に分ける。

1. E(U) = fib(K(U)_ℚ → K(U[1/p])_ℚ)を定義する。
2. Goodwillieのcharacter mapの自然性から、Eをinfinitesimal K理論のファイバーへ比較する。
3. Eのlocalizing・truncatingな性質とconnectiveな係数への適用を得る。
4. Land–Tammeから係数付きcdh降下を得る。
5. p ∈ Jとperfect localizationにより、支持つきファイバーL(Y)を実際の支持つき有理K理論と同定する。
6. nilinvariance、支持、中心局所化の自然性を整理する。

**完了条件**：K理論をcdh sheafificationで置き換えて結論を変えていない。
Hのconnectiveness、p ∈ J、係数の中心性が使われる箇所を個別に追跡できる。

### M8：有限全射の降下と定理3.1

**補題3.2**：有限忠実平坦射についてtransferを構成・引用する。
局所的に階数aの自由なvector bundleの場合、引き戻しとtransferの合成がa倍になる自然な同一性を得る。
有理化によるretract、切断を持つČech図式の降下、Zariski貼り合わせを証明する。
対象ごとの数値等式だけでなくpresheafの図式全体の自然性が必要。

**補題3.3**：cdh被覆と有限忠実平坦被覆が生成する位相を扱う。
reduction、閉成分への帰着、flattening by blowup、次元帰納法により、
有限全射が被覆になることと通常のČech降下を導く。
flattening等の深い幾何定理は引用できるが、補題3.3そのものを最終的な丸ごとの引用にはしない。

**軌道の議論**：Čech項上の切断に帰着し、切断のG移動を使う。
切断の一致軌跡の外での有限コピーの分解、G同変な抽象blowup、
有理置換作用の固定点、閉部分への次元帰納法、nilinvarianceを接続する。

**完了条件**：全スペクトル次数について定理3.1を証明する。
G不変部分を得るための有理化、非平坦有限射、非有界な係数に関する仮定を取り違えない。

### M9：補題4.6の具体的な表示

1. E_S = (S^(s_n))が加法的生成元であることを既存のretractの結果から得る。
2. B_S = ∏_n M_(s_n)(S)による、商の前のperfect圏の表示を構成する。
3. A上の射加群の平坦性と、有限表示性による無限積・tensorの比較を証明する。
   有限添字の `TensorProduct.piRight` を無限積の定理として使わない。
4. 次数零の自由列のdg 圏に、小さいランクの対象の恒等射を潰すcontracting homotopyを加える。
   Drinfeldのpath表示でdg 商を構成する。
5. コチェイン規約で新しいhomotopyの次数は−1。Hom複体は非正次数に集中する。
   原論文のホモロジー規約では非負次数であり、これによりHのconnectivenessを示す。
6. Homの平坦性と次数の範囲からK-flat性を供給し、H ⊗_A Tと導来tensorを比較する。
7. path表示が係数変更でT側のdg 商へ移ることを証明する。
   T自体のA平坦性は仮定しない。T側に必要な平坦性はT上で確認する。
8. perfect hullと冪等完備化が既存の𝒫_Sを与えることを、dg 商・Moritaの一般定理から示す。
9. 中心局所化、compactnessによるパラメータの冪の零作用、支持部分圏の対応を証明する。
10. GによるひねりがT因子の自己同型に対応し、既存の群作用と係数変更の写像が一致すると示す。

**完了条件**：具体的なHと同じ𝒫_A・𝒫_Tの表示を得る。
一般のT側について一様支持代表元を追加仮定せず、商の後の支持と直和因子を扱う。

### M10：二つの保留入力の解消と統合

定理3.1からπ₀の降下を得て、整数倍の帰結へ移す。
既存の局所環の設定では、有限Krull次元、ℤ_(p)代数構造、pを含む支持イデアルを供給する。
パラメータイデアルの根基しか極大イデアルと一致しない場合、pを加えて同じ支持を持つことを示す。
補題4.6の表示と支持・作用の対応を使い、§4の降下を証明する。

`theorem_3_1_K0` と `supportedRankK0_descent` の公開インターフェースをできるだけ保ち、
現在の利用先へ接続する。二種類の既存K₀への比較の向きと自然性を確認する。

**完了条件**：§3・§4・§5と主定理がビルドを通り、
二つの保留入力の直接の `sorry` が消え、残る引用と各利用先の依存が説明できる。

## 8. 依存関係と着手順

```text
M0 仕様
 ├─ M1 基点付き単体的集合 → M2 対称スペクトル → M3 安定モデル
 │                                            ├─ M4 図式・hG・有理化
 │                                            └─ M6 環・加群・K理論
 └─ M5 dg 圏・加群・Morita ─────────────────────→ M6

M4 + M6 + 支持・スキームの基盤 → M7 支持つきcdh降下 → M8 定理3.1
M5 + M6の比較 + 既存の自由列   → M9 補題4.6
M8 + M9 + K₀比較・整数倍化     → M10 二つの保留入力の解消
```

まずM0 → M1 → M2 → M3を主系列とする。
M5のdg 定義はこの主系列と独立に設計できるが、比較とK理論の入力モデルを先にM0で合わせる。
M4の有限群の固定点、split Čech図式、有限homotopy pullbackを、基盤の検証例として使う。
検証例に合うだけの専用定義へ一般論を縮めない。

## 9. 初期の引用候補

これは採用済みのLean宣言の一覧ではなく、ステートメントを精査する候補一覧。
引用ごとに、版・番号、具体的なモデル、仮定、結論、自然性、使用箇所、証明を後回しにする理由を記録する。

| 引用候補 | 初期に残せる範囲 | 自分たちで確認・証明する接続 |
| --- | --- | --- |
| Kan–Quillen | 明示した射のクラスに対するモデル構造 | 基点付き対象、smash、豊穣構造への適用 |
| Hovey–Shipley–Smith | 対称スペクトルの安定モデル構造、monoidal axiom | 採用した定義、置換、導来演算、πₙへの接続 |
| モデル・∞圏の比較 | モデルが表すホモトピー論と必要な図式の比較 | 原論文の引用定理を適用する型の対応 |
| Shipley等 | 環スペクトル・dg 代数、加群、有理モデルの比較 | 係数変更、支持、群作用を含む両立 |
| Drinfeld・dg Morita | dg 商とVerdier商、生成元の自己準同型による表示 | ランク商の具体的平坦性、connectiveness、基底変更 |
| 非連結K理論の一般論 | 構成または独立した特徴づけ、局所化、加法性 | π₀の既存K₀比較、transfer図式への適用 |
| Thomason–Trobaugh等 | perfect localizationと係数付きの必要な比較 | 中心支持の定義、pを反転した支持の消滅 |
| Goodwillie | relative K理論・負巡回ホモロジーの比較 | character squareからEへのファイバーの比較 |
| Land–Tamme | truncating invariantの係数付きcdh降下 | EとLへの適用、実際の支持つきK理論との同定 |
| flatteningなどの幾何 | 精密に述べた平坦化・スキームの一般定理 | 補題3.3と軌道の議論の帰納法・被覆の構成 |

引用を増やす場合は、対象の定義を避けるための追加ではないことを確認する。
基礎定理を後で証明する作業は別のマイルストーンとして足せるが、
既に接続した本文を毎回書き換える必要がないよう、一般定理のインターフェースを保つ。

## 10. モジュール配置の案

以下は全体の配置案。`Spectra/` の基点付き対象の基盤を実装し始めた。
それ以外の新しいK理論の層が既に実装されていることを意味しない。

```text
SerrePositivity/
  HomotopicalAlgebra/      図式、置換、導来演算の一般論
  Spectra/                基点付き単体的集合、対称列、スペクトル、環・加群
  DifferentialGraded/     dg 圏、加群、perfect圏、商、Morita
  AlgebraicKTheory/       非連結K理論、支持、比較、transfer
  Descent/                スペクトル値の降下、有限被覆、群による軌道の議論
  Inputs/                 正確な出典を持つ基礎理論の引用
  Paper/Section3/         一般係数版定理3.1の論文上の入口（配置は要確定）
  Paper/Section4/         補題4.6と既存の降下への接続
```

`CategoryTheory/` は現在の環に依存しない一般論の方向を保つ。
基礎のモジュールから論文や長さ代数の具体的構成をimportしない。
モジュール名・namespaceはM0で確定し、実装後は対応する宣言と検証結果を各段階へ追記する。

## 11. 検証、引用監査、並行作業

- 各段階で、具体的な定義と引用定理の型がLeanで通ることを確認する。
- 引用からの接続は証明し、`#print axioms` と `#print sorries` で依存を追う。
- `sorryAx` の有無だけでなく、到達する引用定理の名前と意味を確認する。
- 移行前後で、同じ対象・係数変更・支持・群作用を扱っていることを比較定理で検証する。
- 同値の自然性、図式の置換の関手性、宇宙、次数と左右加群の向きを監査対象にする。
- ドキュメントだけを変更する段階ではリンクと記述の整合性を検証し、不要な全体ビルドはしない。
- 実装を統合するときは、[監査スクリプト](../scripts/audit_axioms.lean)と解説の引用一覧も更新する。
- 並行作業のある共有ファイルを変更する前に最新の実装を確認する。
  新しい基盤は専用モジュールから始め、既存の二つの入口の置換はM10で行う。
- §2の具体的な長さ代数の構成はこの計画の入力ではない。
  §2からの適用、§5の有限近似・正値性は別作業として扱う。

## 12. 次の具体的な作業

最初の実装に入る前に、M0として次を確定する。

1. 基点付き単体的集合の主モデルは `Under (𝟙_ SSet)` に確定した。
   単体的な基点付き集合との圏同値は証明済み。
2. smash積、円、豊穣構造、convolutionの具体的な構成と既存APIの再利用範囲。
3. 対称スペクトルの加群による定義と、安定モデル構造の引用の正確な型。
4. 安定同値の独立した定義と、πₙ・置換への接続。
5. モデル圏の図式と文献の∞圏の図式を結ぶために必要な比較の範囲。
6. 基盤からK理論までの宇宙・次数・加群の規約と引用台帳。

M1の対象・射・通常のsmash積の普遍性、交換同型、左右単位の自然同型、内部 Hom と随伴、
結合同型と三変数での自然性を実装した。
smashのpentagon・triangle・二つのhexagonと閉対称モノイダル構造の登録まで完了した。
有限集合の全単射亜群、対称列、各段の置換作用、直和の関手とconvolutionの基盤を実装した。
直和の対称モノイダル構造とconvolutionの結合・単位の登録まで実装した。
convolutionの交換と対称性、内部 Hom のendと評価・余評価まで実装した。
内部 Hom との随伴と閉構造の登録まで実装した。
円の反復smashによる各段の対象と、次数の連結・最初の二因子の交換を実装した。
全ての位置の隣接交換とその関係式まで実装した。
TypeAの再利用と全次数の置換作用までproductionへ接続した（§27）。
全単射圏上の球面対称列まで構成した。
連結の左右単位・結合の整合性と、右ブロックの隣接交換との両立まで証明した（§29）。
左ブロックの全位置の隣接交換との両立も証明した（§30）。
任意の左右ブロック置換へ拡張し、第0段も含む連結の同変性を証明した（§31）。
全単射圏上で連結を自然変換へまとめ、convolutionの乗法と因子化・一意性を構成した（§32）。
単位射と因子化・一意性、左右の標準射上での単位比較を構成した（§33）。
その比較をconvolution全体の左右単位則へ持ち上げた（§34）。
乗法の結合則を証明し、反復テンソルと球面対称列のモノイド構造を登録した（§35）。
可換性の必要十分条件を各次数のブロック全体の交換へ帰着し、第0段の場合を証明した（§36）。
先頭因子を末尾へ送る巡回置換の作用とbraidingを比較した（§37）。
その比較を、第1段と任意の段の左右のブロック交換へ接続した（§38）。
モノイダル関手のbraidingの保存を帰納で証明し、一般の二ブロックの交換へ拡張した（§39）。
乗法の可換性を導き、球面対称列の可換モノイド構造を登録した。
球面モノイド上の内部加群として対称スペクトルの対象・射・圏を構成した（§40）。
各次数の構造射の同変性・単位・結合、懸垂構造射と射との両立も証明した。
自由内部加群の一般論と、自由対称スペクトル・忘却関手の随伴を構成した（§41）。
各段の評価の左随伴を自由球面加群と合成し、自由スペクトルF_nを構成した（§42）。
内部加群の極限・余極限の一般論と、対称スペクトルの各段の比較を構成した（§43）。
自由スペクトルの各段の分解図式と生成元の関係式、n未満の段の零対象性まで構成した（§44）。
次はn以上の段を一つのブロックの対称群に沿う誘導表示へまとめ、球面上のテンソル積の構成へ進める。
一般の直積と有限余極限だけから閉対称モノイダル構造を主張せず、
必要な余極限の保存と単体的集合の性質を明示して証明する。
M0全体、とくに安定同値・図式のモデル・文献の∞圏との比較の仕様は引き続き詰める。

## 13. 参照資料

- [原論文](../paper/paper.pdf) §3.1–3.3、補題4.6。出典は [SOURCE.md](../paper/SOURCE.md)。
- [日本語解説](../exposition/ja/exposition-ja.tex)の定理3.1、補題4.6、付録A。
- Hovey–Shipley–Smith, [Symmetric spectra](https://arxiv.org/abs/math/9801077)。
- Mandell–May–Schwede–Shipley,
  [Model categories of diagram spectra](https://math.uchicago.edu/~may/PAPERS/mmssLMSDec30.pdf)。
- Schwede, [On the homotopy groups of symmetric spectra](https://arxiv.org/abs/math/0608059)。
- Shipley, [HZ-algebra spectra are differential graded algebras](https://arxiv.org/abs/math/0209215)、
  [関連する訂正・説明](https://arxiv.org/abs/0708.1299)。採用時には参照する版と番号を固定する。
- Drinfeld, [DG quotients of DG categories, v7](https://arxiv.org/pdf/math/0210114v7)、§3.1・定理3.4。
- Land–Tamme, [On the K-theory of pullbacks](https://arxiv.org/abs/1808.05559)、
  原論文の指定するv3、Appendix A・B。
- Lurie, [Higher Algebra](https://www.math.ias.edu/~lurie/papers/HA.pdf)。
- Goodwillie、Thomason–Trobaugh、非連結K理論の一般論の版・番号は、原論文の参考文献から
  引用台帳へ移す際に該当箇所と適用仮定を改めて確認する。

参考文献があることだけでLeanに既存実装があるとは判断しない。
この文書は会話で採用した方針と固定版の調査をまとめた計画であり、
ここに挙げたスペクトル・dg 理論・K理論の新しい成果が既に実装済みであることを意味しない。

## 14. 実施記録：基点付き対象の基盤（2026-10-13）

### 採用した定義

一般の直積モノイダル圏Cについて `PointedObject C := Under (𝟙_ C)` と定義した。
対象と射にはMathlibのunder圏を使い、主モデルを単体的集合に特殊化する。
基点付き対象の零射は具体的な一つの点を経由する射として選ぶ。
一般論の対象・射の宇宙はそれぞれ `Type u`、`Category.{v}` とし、
単体的集合への特殊化では対象の宇宙が `u + 1`、射の宇宙が `u` となる。

### 証明・構成したもの

| モジュール | 内容 |
| --- | --- |
| [Pointed/Basic](../SerrePositivity/Spectra/Pointed/Basic.lean) | 基点付き対象、忘却、一つの点の零対象性、零射の具体的な表示 |
| [Pointed/Products](../SerrePositivity/Spectra/Pointed/Products.lean) | 直積、射影、普遍性、射の写像、二つの軸とその自然性 |
| [Pointed/AdjoinBasepoint](../SerrePositivity/Spectra/Pointed/AdjoinBasepoint.lean) | 自由な基点の追加、忘却との随伴、零次球面の候補 |
| [Pointed/Smash](../SerrePositivity/Spectra/Pointed/Smash.lean) | wedge、二つの軸を潰すpushout、Homの普遍性、標準射のエピ性、smashの二変数関手 |
| [Pointed/Cofiber](../SerrePositivity/Spectra/Pointed/Cofiber.lean) | 基礎圏の射の像を基点へ潰す通常の商と、そのHomの普遍性 |
| [PointedSimplicialSet/Basic](../SerrePositivity/Spectra/PointedSimplicialSet/Basic.lean) | 各次数の基点、単体写像との両立、`SimplicialObject Pointed`との圏同値 |
| [PointedSimplicialSet/Spheres](../SerrePositivity/Spectra/PointedSimplicialSet/Spheres.lean) | 境界を潰す単体的球面と円の定義 |
| [Spectra/Foundations](../SerrePositivity/Spectra/Foundations.lean) | 独立にビルド・検証するための集約入口 |

smash積の普遍性は、「直積から出る基点付き射で、二つの軸を零にするもの」とのHom同値。
基点へ潰す商にも普遍性を証明しており、球面は名前だけの未証明対象ではない。
自由な基点の追加による零次球面と、境界を潰す零次球面の比較はまだ行っていない。

### 境界と検証

この範囲に `sorry` はない。モデル構造、ホモトピー不変性、閉対称モノイダル構造、
導来smash、対称スペクトル本体を構成済みとはしない。M1全体の完了ではなく、その最初の実装単位である。

実行する検証は次のとおり。

```sh
lake build SerrePositivity.Spectra.Foundations
lake env lean scripts/audit_spectra.lean
```

集約ビルドは1261ジョブで成功。専用の[公理監査](../scripts/audit_spectra.lean)は、
この集約が読み込む `Spectra/` の公開宣言を全て調べ、標準公理以外の依存を拒否する。
実行結果は、宣言を持つ7モジュール・86宣言について標準公理のみで、`sorry` 依存なし。
8個のLeanモジュールと監査スクリプトの行長・空白、計画書のリンクも確認した。
将来引用を導入するときは、引用の台帳と監査の許容範囲を明示的に更新する。
リポジトリの既存のルートimport、§3・§4の降下入力、他の作業のファイルは変更していない。

## 15. 実施記録：smash の交換と単位（2026-10-13）

### 一般論としての追加

- [SmashSymmetry](../SerrePositivity/Spectra/Pointed/SmashSymmetry.lean)：
  直積の交換をsmashへ降ろし、交換同型、二回の交換が恒等射となること、二変数での自然性を証明した。
  直積と有限余極限だけを使い、閉構造は仮定しない。
- [TensorCoproduct](../SerrePositivity/Spectra/Pointed/TensorCoproduct.lean)：
  閉直積圏では直積が左随伴となるため、二項余積を保存する。
  余積との直積から出る射の構成と、二成分による等式判定を証明した。
- [SmashUnit](../SerrePositivity/Spectra/Pointed/SmashUnit.lean)：
  閉直積圏と有限余極限の下で、自由な基点を持つ零次球面をsmashの単位として構成した。
  左単位射と逆射の両合成、自然性、左右単位の自然同型を証明した。
  零次球面の非基点側への包含は、そのままでは基点付き射ではない。
  smashへ合成して初めて基点を保つことを、軸の零化から証明している。
- [MonoidalPrerequisites](../SerrePositivity/Spectra/PointedSimplicialSet/MonoidalPrerequisites.lean)：
  Mathlibの型への関手圏の閉構造を単体的集合へ適用し、直積の余極限保存とsmashの単位へ接続した。

### 境界

今回の自然同型はモノイダル構造のデータの一部である。
結合子、pentagon・triangle・hexagon、smashの内部 Hom をまだ構成していないため、
基点付き単体的集合に `MonoidalCategory` や `MonoidalClosed` の完成したsmash構造を登録していない。
基礎圏SSetの直積の閉構造と、基点付き対象のsmashの閉構造を区別する。

次は、閉直積圏の余極限保存と、軸を零にする射の普遍性を使って、
結合子と内部 Hom の構成を進める。モノイダル構造の登録は整合性の公理を確認してから行う。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1273ジョブで成功した。
追加した一般論と接続に新しい `sorry` はない。
公理監査は引き続き `scripts/audit_spectra.lean` で全公開宣言を対象にする。
実行結果は11モジュール・141宣言について標準公理のみで、`sorry` 依存なし。
ソースの行長・空白、計画書のローカルリンクも検査を通った。
並行作業の§2・CLMST、共有ルートimportと既存の降下入力は編集していない。

## 16. 実施記録：内部 Hom と smash の随伴（2026-10-13）

### 定義と仮定

閉直積モノイダル圏Cと等化子の存在を仮定する。
基礎圏の内部 Hom から、定義域の基点への制限と、行き先の基点で定数となる射の等化子を取る。
その等化子に定数射を基点として付けたものが、基点付き内部 Hom `basedHom X Y`。
対象の基点を保つ射の条件を定義に組み込み、各次数の関数空間で代用していない。

有限余極限も仮定した上で、既存の通常のsmash積とのHom同値と随伴を構成した。
基点付き対象にsmashのモノイダル構造を先に仮定する循環はない。

### 証明した接続

| モジュール | 内容 |
| --- | --- |
| [InternalHom](../SerrePositivity/Spectra/Pointed/InternalHom.lean) | 等化子による内部 Hom、定数射の基点、包含、行き先に関する関手 |
| [ReducedPair](../SerrePositivity/Spectra/Pointed/ReducedPair.lean) | 一方の変数が基点なら定数となる射、軸の零化との同値、smashからの射とのHom同値 |
| [SmashCurrying](../SerrePositivity/Spectra/Pointed/SmashCurrying.lean) | reducedな射のcurry・uncurryとその往復、smashと内部 Hom のHom同値 |
| [SmashAdjunction](../SerrePositivity/Spectra/Pointed/SmashAdjunction.lean) | Hom同値の自然性、随伴、評価・余評価、三角恒等式、左右のsmashの余極限保存 |
| [単体的集合への特殊化](../SerrePositivity/Spectra/PointedSimplicialSet/InternalHom.lean) | Mathlibの単体的集合の閉構造と等化子から、内部 Hom・随伴・余極限保存の仮定を供給 |

二つのreduced条件の役割は別である。
第一変数を基点へ制限したときの定数性は、curryが内部 Hom の等化子に入る条件。
第二変数での定数性は、その等化子へ送る射が基点を保つ条件となる。
この二条件を明示して、基礎圏の閉構造のcurry・uncurryから証明している。

### 到達点と残る範囲

左右のsmashが左随伴であり、通常の余極限を保存することを得た。
これにより、次の結合子や対称列に用いる保存結果を一般論として再利用できる。
今回の三角恒等式は随伴のものであり、モノイダル構造のtriangle公理の証明とは区別する。

結合子、pentagon・triangle・hexagonの確認、閉対称モノイダル構造の登録は引き続き残る。
内部 Hom の行き先に関する関手と各Xについての右随伴は構成済みだが、
定義域に関する反変性もまとめた二変数関手は、今後のモノイダル構造と合わせて整理する。
モデル構造、導来smash、対称スペクトル、K理論の保留入力はまだ変更していない。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1278ジョブで成功した。
追加した一般論に新しい `sorry` はない。全公開宣言の公理監査は
`lake env lean scripts/audit_spectra.lean` で実行する。
監査結果は16モジュール・204宣言について標準公理のみで、`sorry` 依存なし。
17個のLeanソースの行長・空白、計画書のリンクとコードブロックも確認した。
今回も既存の共有ルートimport、§2・CLMSTの並行作業、二つの降下入力は編集していない。

## 17. 実施記録：smash の結合子と三変数の普遍性（2026-10-13）

### 一般論としての構成

閉直積圏Cと有限余極限を仮定し、基点付き対象のsmashの結合同型を構成した。
結合子を入力として仮定せず、三変数の直積から商へ降りる射として定義している。
この構成には内部 Hom の等化子の存在を仮定する必要はない。

| モジュール | 内容 |
| --- | --- |
| [ProductColimits](../SerrePositivity/Spectra/Pointed/ProductColimits.lean) | 基点付き直積の左右関手、pushout保存、余積の二成分による射の等式判定、直積写像のエピ性 |
| [ProductAssociator](../SerrePositivity/Spectra/Pointed/ProductAssociator.lean) | 基点付き直積の結合同型、逆射、軸との両立、自然性、直積のpentagon |
| [TripleSmash](../SerrePositivity/Spectra/Pointed/TripleSmash.lean) | 三変数で各基点において零となる射、左右の括弧への降下、標準射のエピ性、左右のHom同値 |
| [SmashAssociator](../SerrePositivity/Spectra/Pointed/SmashAssociator.lean) | smashの結合射と逆射、両合成の恒等性、結合同型、三変数での自然性 |
| [単体的集合への特殊化](../SerrePositivity/Spectra/PointedSimplicialSet/MonoidalPrerequisites.lean) | 単体的集合の閉構造と有限余極限から結合同型の仮定を供給 |

基点付き直積が基点付き余積を保存するとは主張していない。
必要なのはpushoutの保存と、余積の成分に制限することで射を判定できることである。
忘却関手の連結余極限の保存・反映と、基礎圏の閉直積構造を利用している。

三変数の標準射は、三つの基点軸を零にする。
直積の結合射はその軸を保つため、左右の括弧で取ったsmashの間に射が降りる。
二つの標準射のエピ性から逆射の恒等式を確認し、自然性も標準射へ引き戻して証明した。
Hom同値はこの降下の存在と一意性を、次の多変数の議論でも再利用できる形にまとめている。

### 残る整合性と次の順序

今回証明したpentagonは直積のものであり、smashのpentagonはまだ残る。
次は四変数の標準射とそのエピ性を整備し、smashのpentagonを直積のpentagonへ帰着する。
続いて単位とのtriangle、交換とのhexagonを証明し、閉対称モノイダル構造を登録する。
これらが終わるまでは、基点付き単体的集合のsmashに完成したモノイダル構造を登録しない。
対称列・対称スペクトル、モデル構造、導来演算、定理3.1・補題4.6の保留入力は引き続き残る。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1282ジョブで成功した。
`lake env lean scripts/audit_spectra.lean` は20モジュール・291宣言を監査し、
標準公理のみで `sorry` 依存がないことを確認した。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimport、§2・CLMSTなどの並行作業、既存の二つの降下入力は編集していない。

## 18. 実施記録：smash の pentagon と hexagon（2026-10-13）

### 四変数の結合の整合性

[SmashPentagon](../SerrePositivity/Spectra/Pointed/SmashPentagon.lean)で、
四変数の五通りの括弧に対応する直積からsmashへの標準射を定義した。
左括弧の標準射は、三変数の標準射との直積と、最後のsmashの商射の合成であり、エピ射となる。
五角形の各辺で、smashの結合射が直積の結合射と両立することを証明した。
左右の経路を左括弧の標準射に沿って引き戻すと、直積のpentagonに右括弧の標準射を合成した
等式になる。標準射のエピ性から `smashAssoc_pentagon` を得た。

四変数の新しい降下公理や引用は追加していない。
三変数の普遍性、直積の写像の合成則、直積の結合射の自然性を再利用した。

### 三変数の結合と交換の整合性

[SmashHexagon](../SerrePositivity/Spectra/Pointed/SmashHexagon.lean)で、
直積の二つのhexagonを射影への合成で証明した。
三変数の標準射が、内側の交換と外側の交換の双方で直積の交換射と両立することを確認し、
同じ引き戻しの方法で `smashAssoc_hexagon_forward` と `smashAssoc_hexagon_reverse` を証明した。
この二つの等式はMathlibの `BraidedCategory` の二つのhexagonと同じ向き・括弧で述べている。
標準射と交換との比較には、基礎圏の閉構造の仮定は不要である。

単体的集合への接続と集約モジュールにも両モジュールを追加した。
結合・交換の整合性は証明済みだが、単位とのtriangleは引き続き残る。
次は零次球面の非基点側・基点側の二成分でtriangleを確認し、
単位・結合・交換をまとめて閉対称モノイダル構造を登録する。
対称列・対称スペクトル、モデル構造、導来演算、定理3.1・補題4.6の保留入力は未変更。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1284ジョブで成功した。
全公開宣言の公理監査は22モジュール・320宣言について標準公理のみで、`sorry` 依存なし。
新規二モジュールに `sorry` や診断用の `trace_state` は残していない。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
今回も共有ルートimportや他作業のファイルは編集していない。

## 19. 実施記録：triangle と閉対称モノイダル構造の登録（2026-10-13）

### 単位と結合の整合性

[SmashTriangle](../SerrePositivity/Spectra/Pointed/SmashTriangle.lean)で
`smashAssoc_triangle` を証明した。
三変数の標準射で引き戻し、零次球面を中央へ挿入する基礎圏の射を使って二成分で比較した。
非基点側では左右の単位のraw mapが恒等的に作用し、両経路は通常のsmashの商射となる。
基点側では左右の経路はそれぞれ二つの軸を通るため、商へ合成すると零となる。

零次球面の成分を選ぶ射は基点付き射ではないので、
成分の比較を基礎圏Cで行い、その二項余積と直積の保存を使用している。
非基点側・基点側に任意の射を入れたときの単位raw mapの動作も補題として残した。

### 型クラスへの接続

[SmashMonoidal](../SerrePositivity/Spectra/Pointed/SmashMonoidal.lean)で、
閉直積圏Cと有限余極限の下で `PointedObject C` に通常のsmashのモノイダル構造を登録した。
テンソル積は `smash`、射のテンソル積は `smashMap`、単位は `sphereZero`。
構成済みの結合・単位同型と、それぞれの自然性・pentagon・triangleを
Mathlibの `MonoidalCategory.ofTensorHom` へ渡している。
交換同型、二つのhexagon、交換の対合性により `SymmetricCategory` も登録した。

さらに等化子の存在を仮定し、既存の `basedHomFunctor` と `smashHomAdjunction` を
`MonoidalClosed` の右随伴と随伴として登録した。
閉構造を新たな入力として仮定したり、内部 Hom を別の対象で置き換えたりしていない。

[単体的集合への接続](../SerrePositivity/Spectra/PointedSimplicialSet/Monoidal.lean)では、
三つの型クラスが推論できることを確認した。
テンソル積・単位・内部 Hom・評価射が、既存の具体的な構成と定義上同じであることも証明した。
これにより、以後の対称列の構成でMathlibの一般的な閉対称モノイダル圏APIを利用できる。

### 次の範囲と検証

通常のsmashの閉対称モノイダル基盤は揃った。
次は有限集合と全単射の圏を用いる対称列、そのconvolutionと球面の対称列を整備する。
この登録はモデル構造・導来smash・対称スペクトルの構成を意味しない。
定理3.1・補題4.6の二つの保留入力も引き続き未変更である。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1287ジョブで成功した。
全公開宣言の公理監査は25モジュール・338宣言について標準公理のみで、`sorry` 依存なし。
新規三モジュールに `sorry` や診断用の `trace_state` は残していない。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimport・§2・CLMSTなどの並行作業のファイルは編集していない。

## 20. 実施記録：対称列と convolution の基盤（2026-10-13）

### 添字圏と置換作用

[FiniteBijection](../SerrePositivity/Spectra/SymmetricSequence/FiniteBijection.lean)で、
Mathlibの `FintypeCat.Skeleton.{0}` のcoreを `FiniteBijection` として採用した。
対象は標準有限集合の濃度であり、射は全単射だけを含む。
添字圏は宇宙0で小さいため、その上のKan拡張には小さい余極限の存在を使用できる。
射と `Fin n` の同値との対応、射が存在する場合の濃度の等式を証明した。
全ての有限集合の全単射圏への標準包含もMathlibのcore関手から構成した。

[Basic](../SerrePositivity/Spectra/SymmetricSequence/Basic.lean)で、
この亜群上の共変関手を対称列と定義した。各段の対称群作用と、作用の圏への評価関手を構成した。
置換の積σ・τは圏の合成ではτの後にσとなることを明示し、
`Action` の乗法則と自然変換の同変性を証明した。対称列の射の各段による等式判定も得た。

対称列は関手圏の略記ではなく独立した型の同義語とし、圏構造だけを登録した。
元の関手圏への恒等的なfull・faithful関手を備える。
これにより、関手圏の点ごとのテンソル積を、以後登録するconvolutionの構造へ混入させない。

### 直和と convolution

[DisjointUnion](../SerrePositivity/Spectra/SymmetricSequence/DisjointUnion.lean)で、
濃度の加法と `finSumFinEquiv` によるブロックの全単射を使い、直和の二変数関手を構成した。
恒等射と合成の保存は証明済み。直和の結合・単位・交換の同型の登録は次の段階に残す。

[Convolution](../SerrePositivity/Spectra/SymmetricSequence/Convolution.lean)で、
外部テンソル積を直和に沿って左Kan拡張し、convolutionの二変数関手を構成した。
MathlibのKan拡張の存在、随伴・普遍性と各段の余極限表示を利用している。
各段の分解図式の対象は、二つの有限集合と、その直和から当該段への全単射。
射がブロックの置換を同一視するため、単に次数の組を列挙した余積ではない。
第n段に現れる分解の二つの濃度の和はnに等しいことを証明した。

`convolutionUnit` は外部テンソル積から左Kan拡張への自然変換であり、
convolutionのモノイダル単位対象を意味しない。
添字圏のモノイダル構造を仮定せずに、演算・関手性・普遍性を先に具体的に得ている。

[Pointed](../SerrePositivity/Spectra/SymmetricSequence/Pointed.lean)で、
基点付き単体的集合の対称列とsmash convolutionへ特殊化した。
第p段と第q段のsmashを第p+q段へ送る構造射と、そのブロック置換に関する同変性を証明した。

### 次の範囲と検証

次は直和の対称モノイダル構造を整え、MathlibのDay convolution APIを使って
このconvolutionの結合・単位・交換を登録する。その後、球面対称列とその可換モノイド構造、
球面対称列の加群としての対称スペクトルへ進む。
今回、convolutionのモノイダル構造や球面対称列の乗法・加群はまだ構成していない。
モデル構造・導来演算、定理3.1・補題4.6の二つの保留入力も未変更である。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1306ジョブで成功した。
全公開宣言の公理監査は30モジュール・390宣言について標準公理のみで、`sorry` 依存なし。
対称列に点ごとのモノイダル構造が自動推論されないことも、別のLean検査で確認した。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimportと他作業のファイルは編集していない。

## 21. 実施記録：直和の対称構造と convolution のモノイダル構造（2026-10-13）

### 添字圏の直和

[SumCoherence](../SerrePositivity/Spectra/SymmetricSequence/SumCoherence.lean)で、
標準有限集合を二項和へ展開してから戻す全単射として、直和の結合・単位・交換を構成した。
三つのブロックでの結合射の動作、二つのブロックでの交換と直和写像の動作を補題にした。
これらの式で自然性、pentagon、triangle、二つのhexagon、交換の対合性を証明した。
有限集合の濃度の等式だけで射の等式を代用せず、各ブロックの元で全単射を比較している。

[SumMonoidal](../SerrePositivity/Spectra/SymmetricSequence/SumMonoidal.lean)で、
`FiniteBijection` にこの直和の `MonoidalCategory` と `SymmetricCategory` を登録した。
登録したテンソル関手は、前段階のconvolutionに使った `sumFunctor` と定義上同じである。
これは全単射圏の直和のモノイダル構造であり、その圏の二項余積の普遍性を主張するものではない。

### 具体的な convolution の Day 構造

[DayStructure](../SerrePositivity/Spectra/SymmetricSequence/DayStructure.lean)で、
既存のconvolutionとそのKan拡張の自然変換をMathlibの `DayConvolution` へ接続した。
空集合の包含に沿って基礎圏のテンソル単位を左Kan拡張し、convolutionの単位候補を構成した。
その候補が `DayConvolutionUnit` の普遍性を持つことも証明した。

具体的なテンソル対象を維持するため、
`InducedLawfulDayConvolutionMonoidalCategoryStructCore` に既存のconvolutionを明示的に指定した。
Day構造やその構成用の補助クラスを大域的なinstanceにせず、誘導構造の構成へ渡している。

[DayMonoidal](../SerrePositivity/Spectra/SymmetricSequence/DayMonoidal.lean)で、
基礎圏のbraiding・閉構造・小さい余極限を仮定して、
対称列のconvolutionに `MonoidalCategory` とlawfulなDay構造を登録した。
左右テンソルの余極限保存を閉構造から供給し、MathlibのDay convolutionの一般論により
結合子・左右単位・自然性・pentagon・triangleを得ている。
テンソル対象が既存のconvolutionであり、単位対象が空集合からのKan拡張であることを
定義上の等式として確認した。

基点付き単体的集合の対称列でもモノイダル構造の型クラス推論が通ることを確認した。
この段階ではconvolutionの `SymmetricCategory` や `MonoidalClosed` はまだ登録していない。
次はDay convolutionの交換と閉構造のAPIへ接続し、球面対称列の可換モノイド構造へ進む。
球面対称列の加群・対称スペクトル、モデル構造、導来演算、二つの降下入力は未変更である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1312ジョブで成功した。
全公開宣言の公理監査は34モジュール・436宣言について標準公理のみで、`sorry` 依存なし。
追加した四モジュールに未証明入力はなく、診断用のコードも残していない。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimportと並行作業のファイルは編集していない。

## 22. 実施記録：convolution の対称性と内部 Hom の end（2026-10-13）

### 交換構造の登録

[DaySymmetry](../SerrePositivity/Spectra/SymmetricSequence/DaySymmetry.lean)で、
MathlibのDay braidingを関手圏へのfull・faithfulな包含に沿って対称列へ引き戻した。
包含した交換射が元のDay braidingとなること、包含した結合射の逆が
Day associatorの逆となることも補題にした。
lawfulなDay構造の写像・結合子の比較式を使い、交換の自然性、二つのhexagon、対称性を証明した。

基礎圏Cが対称・閉モノイダルで小さい余極限を持つとき、
対称列のconvolutionに `SymmetricCategory` を登録した。
基点付き単体的集合の対称列でも、この型クラス推論が通ることを確認した。
比較に用いるDay構造の補助instanceはモジュール内で局所的に有効にしている。

### end による内部 Hom

[DayInternalHom](../SerrePositivity/Spectra/SymmetricSequence/DayInternalHom.lean)で、
基礎圏Cの閉構造と小さい極限から内部 Hom の候補を構成した。
第x段はjに関する `[F(j), G(j ⊕ x)]` のendであり、
Mathlibの `dayConvolutionInternalHomDiagramFunctor` と `endFunctor` を組み合わせている。
添字xと行き先Gに関する関手性もこの構成に含めた。

endから各内部 Hom への射影、全単射の引き戻しと行き先への作用の整合性、
射影が普遍的なwedgeを作ることを証明した。
これを `DayConvolutionInternalHom` のデータへまとめ、
convolutionの普遍性による評価射と、構造射のcurryによる余評価射を定義した。
新しいendの普遍性や閉構造を未証明入力として仮定していない。

基点付き単体的集合の対称列へは、内部 Hom の関手を特殊化した。
評価・余評価の専用略記はカーネルの正規化で時間制限に達したため追加していない。
一般のCについての構成は検証済みであり、専用APIの整理は随伴の接続と合わせて行う。
この制約を新しい `sorry` や検査の省略で回避していない。

### 次の範囲と検証

convolutionの対称モノイダル構造は揃った。
内部 Hom の対象・射・普遍性・評価・余評価は構成済みだが、
自然性と三角恒等式を随伴のデータとしてまとめること、および `MonoidalClosed` の登録は残る。
MathlibのDay内部 Hom の自然性・三角恒等式の定理を利用し、
endの誘導射と構成した内部 Hom 関手の写像との一致を確認して接続する。
その後、球面対称列と可換モノイド構造、球面対称列の加群へ進む。
対称スペクトル・モデル構造・導来演算と、定理3.1・補題4.6の二つの降下入力は未変更。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1317ジョブで成功した。
全公開宣言の公理監査は36モジュール・452宣言について標準公理のみで、`sorry` 依存なし。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimportや他作業のファイルは編集していない。

## 23. 実施記録：convolution と内部 Hom の随伴・閉構造（2026-10-13）

### end の写像と Day 内部 Hom の写像

[DayAdjunction](../SerrePositivity/Spectra/SymmetricSequence/DayAdjunction.lean)で、
endの誘導射として定義した内部 Hom 関手の写像が、
`DayConvolutionInternalHom.map` の普遍性による誘導射と一致することを証明した。
endの普遍的なwedgeの射影に合成して判定し、Mathlibの `end_.map_π` と
Day内部 Hom の射影の比較式を使っている。

登録したテンソル積と同じDay構造を明示する補助定義を用意し、局所的なinstanceとして使った。
一般の具体的なconvolutionの構成用データと、登録されたテンソル積のlawfulなDay構造を区別し、
後者に沿った `convolutionEvaluation` と `convolutionCoevaluation` を定義した。
これらは既存のendの対象・射影をそのまま使用する。

### 自然性、三角恒等式、随伴

関手圏への忠実な包含を通してテンソル写像をDayの写像へ移し、
内部 Hom 関手の写像との一致を使って評価・余評価の自然性を証明した。
二つの三角恒等式もMathlibのDay内部 Hom の定理から接続した。
包含による恒等射の保存と、Day convolution の対象が登録したテンソル対象であることを
明示的に簡約し、型の比較が不要に構成の内部へ展開されることを避けている。

これらを `Adjunction.mkOfUnitCounit` にまとめ、
`tensorLeft F ⊣ internalHomFunctor F` を構成した。
基礎圏Cが対称・閉モノイダルで小さい極限・余極限を持つとき、
対称列のconvolutionに `MonoidalClosed` を登録した。
この登録の右随伴は、前段階で構成したendの内部 Hom 関手そのものである。

Mathlibの `ihom` の各段が指定したendとなること、
`ihom.ev`・`ihom.coev` の成分が今回の評価・余評価となることを定義上の等式で確認した。
基点付き単体的集合の対称列でも `MonoidalClosed` の型クラス推論が通る。
以前時間制限に達した専用略記の追加に依存せず、登録した標準の内部 Hom APIを利用できる。
時間制限の引き上げや未証明入力の追加は行っていない。

### 次の範囲と検証

対称列のconvolutionの閉対称モノイダル基盤が揃った。
次は、円 `S¹` の反復smashを第n段とする球面対称列を構成し、
置換作用と和次数への乗法を整えて可換モノイド構造を得る。
第0段はsmashの単位 `sphereZero` とする。
既存の境界商による単体的球面と、円の反復smashは別の具体的モデルなので、
それらを定義上同じものとは扱わず、必要な比較は後で行う。
球面対称列の加群・対称スペクトル、モデル構造、導来演算、二つの降下入力はまだ未変更である。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1318ジョブで成功した。
全公開宣言の公理監査は37モジュール・468宣言について標準公理のみで、`sorry` 依存なし。
追加したモジュールに未証明入力や診断用コードは残していない。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
共有ルートimportと並行作業のファイルは編集していない。
## 24. 実施記録：反復テンソルと球面対称列の各段（2026-10-13）

### 再利用する反復テンソルの基盤

[TensorPowers](../SerrePositivity/Spectra/SymmetricSequence/TensorPowers.lean)で、
一般のモノイダル圏の対象Xについて、右に括った反復テンソル `power X n` を定義した。
第0段はテンソル単位、第n+1段はXと第n段のテンソル積である。
対象の射から各段の射を構成し、恒等射・合成の保存を証明して各段の自己関手へまとめた。

単位・結合子から `power X m ⊗ power X n ≅ power X (m + n)` を再帰的に構成し、
対象の射に関する自然性を証明した。
次数の加法の等式は、対象の等式による `eqToIso` として明示的に移送している。
この移送が反復テンソルの写像と両立することも補題として残した。
第1段と元の対象の比較、および第1段の関手と恒等関手の自然同型も構成した。

[TensorPermutations](../SerrePositivity/Spectra/SymmetricSequence/TensorPermutations.lean)で、
対称モノイダル圏において最初の二因子を交換する同型を構成した。
結合子で二因子を括り、braidingを残りの因子とのテンソル積へ延長してから括弧を戻す。
二回の交換が恒等射となることと、対象の射に関する自然性を証明した。
この段階では任意の置換の作用を主張していない。

### 円の反復 smash への特殊化

[SpherePowers](../SerrePositivity/Spectra/SymmetricSequence/SpherePowers.lean)で、
球面対称列の各段に使う `spherePower n` を円の反復smashとして定義した。
宇宙は基点付き単体的集合の宇宙uを明示して固定し、宇宙0へ暗黙に特殊化しない。
第0段は `sphereZero`、第1段は円と同型、第2段は円二つのsmashと同型である。
和次数への連結同型と、最初の二因子の交換・対合性も一般論から接続した。
境界商によるn次の単体的球面との同一視や比較はまだ行っていない。

### 次の範囲と検証

現時点の `spherePower` は各段の対象の族であり、全単射圏上の対称列としては未完成である。
現在のMathlibには、今回調べた範囲で一般の対称モノイダル圏の反復テンソルに
全置換を作用させる完成したAPIは見つからなかった。通常のfree monoidal categoryの
APIは存在するが、これだけで対称群作用を供給できるとは扱わない。

次は各位置の隣接交換を構成し、対合性・離れた交換の可換性・braid関係を確認する。
任意の置換への拡張では分解の選択によらないことと乗法則を証明し、
既存の有限集合の全単射圏へ関手としてまとめる。
その上で、次数の連結のブロック置換との両立、結合・単位・交換との整合性を確認し、
convolutionの普遍性を使って球面対称列の可換モノイド構造を作る。
置換作用が未完成の段階で、自明な作用を代入して球面対称列と呼ぶことはしない。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1321ジョブで成功した。
全公開宣言の公理監査は40モジュール・494宣言について標準公理のみで、`sorry` 依存なし。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
対称スペクトル・モデル構造・導来演算、二つの降下入力は未変更である。
共有ルートimportと並行作業のファイルは編集していない。

## 25. 実施記録：各位置の隣接交換と Coxeter 関係（2026-10-13）

### 全位置の交換と遠隔可換性

[AdjacentTranspositions](../SerrePositivity/Spectra/SymmetricSequence/AdjacentTranspositions.lean)で、
n+1個の因子に対して、`Fin n` を添字とするn個の隣接交換 `adjacentIso` を構成した。
先頭の交換は既存の `swapFirstIso`、それ以外は先頭の因子を保って尾の交換へ再帰する。
全位置の対合性と対象の射に関する自然性を、この再帰から証明した。

先頭の交換が尾の任意の自己射と両立することを、結合子の自然性とwhiskerの交換則で証明した。
これを使い、二つの位置i・jが `i + 1 < j` を満たすときの隣接交換の可換性を得た。
逆順の位置については、この等式の対称性で同じ可換性を利用できる。

### braid 関係

[AdjacentBraid](../SerrePositivity/Spectra/SymmetricSequence/AdjacentBraid.lean)で、
三因子の二つの隣接交換と、三因子を一つのブロックとして尾へテンソルする括弧付けを構成した。
この括弧付けの同型が、先頭の二つの隣接交換と両立することを
Mathlibのモノイダル整合性タクティックで確認した。
これは結合・単位の整合性であり、braid関係そのものを同タクティックに仮定させてはいない。

Mathlibの `BraidedCategory.yang_baxter` を尾とのテンソル積へ延長し、
上の同型へ合成して、先頭での `s₀ s₁ s₀ = s₁ s₀ s₁` を証明した。
さらに先頭の因子を保つ再帰により、任意の隣接した二位置のbraid関係を証明した。
これで対合性・遠隔可換性・braid関係の三種類が全位置について揃った。

球面の各段へも、任意の位置の隣接交換とこれら三種類の関係式を特殊化した。
宇宙uを明示した円の反復smashを引き続き使用している。

### 任意の置換への拡張に向けた境界

今回証明したのは反復テンソル上の生成元と関係式であり、
`Equiv.Perm (Fin n)` の任意の元の作用や乗法則はまだ定義していない。
次は群の提示の普遍性を使って自己同型群への準同型を構成し、
その提示と通常の対称群との同定を確認する。
Mathlibには `PresentedGroup` と `CoxeterSystem.lift` のAPIがあり、
隣接交換による生成についての結果もあるが、生成だけで提示の完全性を代用しない。
有限集合の全単射圏の合成と群の乗法の順序も、既存の規約に合わせて接続する。

この接続の後で、全置換の分解に依存しないこと、ブロック置換と次数の連結の両立、
連結の結合・単位・交換との整合性を確認し、球面対称列の可換モノイド構造へ進む。
全置換作用と球面対称列の可換モノイド構造は、現段階では未完成である。

集約 `SerrePositivity.Spectra.Foundations` のビルドは1323ジョブで成功した。
全公開宣言の公理監査は42モジュール・512宣言について標準公理のみで、`sorry` 依存なし。
追加した二モジュールに未証明入力や診断用コードは残していない。
Leanソースの行長・空白、計画書のローカルリンク、`git diff --check` も確認した。
対称スペクトル・モデル構造・導来演算、二つの降下入力は未変更。
共有ルートimportと並行作業のファイルは編集していない。

## 26. 再利用調査：ArxivFormalization の TypeA（2026-10-13）

### 再利用する範囲

ArxivFormalizationの `ArxivFormalization/Coxeter/TypeA.lean` に、
型A Coxeter群と `Equiv.Perm (Fin (n + 1))` の乗法同型 `typeAEquivPerm` がある。
単純反射が標準の隣接互換へ送られる計算則 `typeAEquivPerm_simple` もある。
全射性だけでなく、挿入ソートの正規形による単射性を証明しているため、
今回必要な「関係式による提示が通常の対称群を与える」という接続に利用できる。

再利用元はコミット `761bc6bc1b8f18764afa9f2d439264e79da14a31`。
確認したTypeAファイルに未コミット変更はなく、ソースのSHA256は
`16a2c3c77f0dec26ca5bb5ea6f5380c4fa599db962bedb6935d94f9fc72da188`。
数学部分のimportはMathlibのCoxeter・有限置換・符号のモジュールに限られる。
管理用の `Meta.Blueprint` とblueprint属性は、再利用する数学の依存から外せる。

FreeRibbonの普遍liftも調べたが、`RightRigidCategory`・`RibbonCategory` と
生成元の完全pairingを要求する。今回の通常のsmashの閉対称モノイダル基盤だけから
これらの追加データを供給する方針は採用していないため、FreeRibbon全体は直接の取り込み対象にしない。
既存のMathlibのモノイダル整合性とYang–Baxterの接続を引き続き利用する。

### 固定版への移植の試験

元リポジトリのground-truth監査スクリプトを実行したが、Mathlibの配置先が存在せず、
ビルド前に終了した。元の環境やソースは修復・変更していない。
そのため、元環境のビルド結果を再利用可能性の根拠にはしていない。

代わりに `/tmp/serre-typea-reuse-probe/TypeA.lean` に検証版を作成し、
本リポジトリのLean `v4.35.0-rc4` と固定版Mathlibで直接コンパイルした。
blueprintの管理属性9個と管理モジュールのimportを外し、
非推奨の書き換え補題名3箇所を現行名へ更新した。
`castSucc_isLiftable` では、現行の簡約で既に閉じるゴールの後にあった5行を削除した。
定義・定理の数学的なステートメント、正規形の構成、単射性の証明方針は変更していない。
これによりTypeAの証明全体がコンパイルでき、二つの中心宣言の公理依存は標準3公理のみとなった。

### 今回の反復テンソルとの接続の試作

同じ検証ファイルで、既存の `adjacentIso` を反復テンソルの自己同型群の元へ送った。
証明済みの対合性・遠隔可換性・braid関係から、型Aの `CoxeterMatrix.IsLiftable` を証明した。
`CoxeterSystem.lift` で抽象Coxeter群から自己同型群への準同型を作り、
再利用した `typeAEquivPerm` の逆と合成して
`Equiv.Perm (Fin (n + 1)) →* Aut (power X (n + 1))` を構成した。
標準の隣接互換が既存の隣接交換へ送られることも証明した。
自己同型群の乗法と圏の合成の順序の違いは、比較時に明示している。

最終の検証コマンドは
`lake env lean /tmp/serre-typea-reuse-probe/TypeA.lean`、終了コードは0。
ログは `/tmp/serre-typea-reuse-probe/connection.log`。
再利用したTypeAと接続の試作について73宣言を監査し、標準公理のみで `sorry` 依存なしを確認した。
この73宣言は試作の監査対象であり、productionのスペクトル基盤の512宣言にはまだ加えていない。

### 採用する次の順序

1. TypeAの数学部分を独立した群論モジュールとして取り込む。出典・元コミット・版差の修正を記録する。
2. 反復テンソルの自己同型への接続は別モジュールに置き、既存の隣接交換の証明を再利用する。
3. 第0段の自明な置換群も扱い、全単射圏上の関手として全次数をまとめる。
4. ブロック置換と次数の連結を比較し、連結の整合性を証明して球面対称列の可換モノイドを構成する。

元リポジトリ全体をLake依存に追加する方針ではなく、数学的に独立したTypeAの範囲を再利用する。
将来両リポジトリで共有する場合も、この群論部分を独立した共通基盤にするのが適切。
今回の調査ではproductionのLeanファイル、依存設定、共有ルートimportは変更していない。


## 27. 実施記録：共通基盤への移植と全次数の置換作用（2026-10-13）

### 将来の統合を見据えた配置

ユーザーの方針に従い、リポジトリ統合や新パッケージの作成を今は行わず、
共通数学として再利用する内容と球面への特殊化を分けてproductionへ取り込んだ。

- [群論のTypeA](../SerrePositivity/GroupTheory/Coxeter/TypeA.lean)に、ArxivFormalizationの証明を移植した。
- [対合の一般関係](../SerrePositivity/GroupTheory/Coxeter/InvolutionRelations.lean)を群論側へ置いた。
- 反復テンソル・隣接交換・braid関係の四モジュールを `CategoryTheory/Monoidal` へ移した。
  namespaceと宣言名は維持し、以前の `Spectra/SymmetricSequence` のimport経路は互換入口として残した。
- [一般の置換作用](../SerrePositivity/CategoryTheory/Monoidal/PermutationAction.lean)を共通圏論側へ置いた。
- [円への特殊化](../SerrePositivity/Spectra/SymmetricSequence/SpherePermutationAction.lean)だけをスペクトル側へ置いた。

共通群論・共通モノイダル圏論には、スペクトル側やArxivFormalization側へのimport依存を置いていない。
[群論の出典管理](../SerrePositivity/GroupTheory/Coxeter/README.md)に、元コミット・ソースhash・移植差分・
修正時の同期方針を記録した。[圏論の配置方針](../SerrePositivity/CategoryTheory/Monoidal/README.md)も記録した。
今後の数学的修正と版差の調整を区別し、将来統合するときにTypeAの証明を一本化できる構成とする。

### 取り込んだ作用とその範囲

型Aの普遍性による正次数の作用に、第0段の自明な作用を加え、
`Equiv.Perm (Fin n) →* Aut (power X n)` を全次数について構成した。
標準の隣接互換が既存の隣接交換へ送られること、恒等置換の値、
群の積と圏の合成が逆順で両立することを証明した。
円の反復smashにも、全次数の作用と隣接互換の値・乗法則を接続した。
この作用は準同型として構成したため、置換を語へ分解する選択に依存しない。

この段階で完成したのは各段の対称群作用である。
全単射圏上の一つの関手として球面対称列をまとめること、ブロック置換と連結の比較、
連結の結合・単位・交換の整合性と可換モノイド構造は次に行う。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1892ジョブで成功した。
移動前の四つのimport経路も、互換入口の対象ビルド693ジョブで検証した。
公理監査を共通圏論・共通群論の公開宣言まで拡張し、
46モジュール・595宣言について標準公理のみで `sorry` 依存なしを確認した。
ソースの行長・空白、共通層からスペクトル層への逆importがないこと、
ドキュメントのローカルリンク、`git diff --check` も確認した。

元リポジトリのソース、Lake依存設定、共有ルートimport、並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力、対称スペクトル・モデル構造・導来演算は未変更である。

## 28. 実施記録：各段の作用から球面対称列へ（2026-10-13）

### 共通の有限全単射圏と作用の関手化

[有限全単射圏](../SerrePositivity/CategoryTheory/FiniteBijection.lean)を共通の圏論層へ移し、
旧スペクトル側のimport経路は互換入口として残した。
既存のnamespaceと宣言名は維持し、恒等射・合成の全単射としての計算則も共通層へまとめた。
射が存在すれば濃度だけでなく骨格の対象そのものが等しいことを証明した。

[FiniteBijectionAction](../SerrePositivity/CategoryTheory/FiniteBijectionAction.lean)で、
任意の対象の族Aと各段の対称群作用から、全単射圏上の関手 `familyFunctor` を構成した。
全単射の濃度の等式を使って置換を同じ段の自己同型へ戻し、
その作用の後で行き先の段へ移送する `familyMap` を定義した。
恒等射・合成の保存と、標準の置換の像が元の作用に一致することを証明した。
この一般構成は基礎圏の圏構造だけを仮定し、モノイダル構造やスペクトルに依存しない。

### 反復テンソルと球面への接続

[PowerBijectionFunctor](../SerrePositivity/CategoryTheory/Monoidal/PowerBijectionFunctor.lean)で、
上の一般構成を反復テンソルと既存の置換作用に適用した。
各段の対象と置換の像が既存の構成と同じであることを確認した。
これも共通の圏論層に置き、スペクトル側への逆importはない。

[TensorPowerSequence](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerSequence.lean)で、
この関手をconvolutionを備える対称列の型へ接続した。
[SphereSequence](../SerrePositivity/Spectra/SymmetricSequence/SphereSequence.lean)で、
円へ特殊化して `sphereSequence` を定義した。
各段の対象は既存の `spherePower` であり、置換の像と対称列から取り出す各段の作用は
既存の `spherePermutationAction` に一致する。第0段も含めて関手の恒等射・合成の保存を備える。

この段階で球面対称列は全単射圏上の一つの関手として完成した。
convolutionの可換モノイド構造はまだ追加していない。
次はブロック置換と次数の連結の両立、連結の結合・単位・交換の整合性を確認し、
convolutionの普遍性から乗法を構成する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1897ジョブで成功した。
有限全単射圏の旧import経路と直和の入口も、対象ビルド837ジョブで確認した。
公理監査を共通の有限全単射圏と作用の関手化のモジュールまで拡張し、
50モジュール・612宣言について標準公理のみで `sorry` 依存なしを確認した。
ソースの行長・空白、共通層からスペクトル層への逆importがないこと、
ドキュメントのローカルリンク、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
二つの降下入力、対称スペクトル・モデル構造・導来演算は未変更である。


## 29. 実施記録：次数の連結の整合性と右ブロックの生成元（2026-10-13）

### 共通のモノイダル圏論

[TensorPowerCoherence](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerCoherence.lean)で、
一般のモノイダル圏における反復テンソルの連結同型について、左右単位と結合の整合性を証明した。
三次数l・m・nの連結では、先にlとmを連結する射と、先にmとnを連結する射を、
圏の結合子と自然数の結合則による次数の移送を介して比較する。
左・右の次数の移送と連結の両立も補助結果として整備した。
これらの結果は対称構造や球面を仮定しない。

[TensorPowerBlockGenerators](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerBlockGenerators.lean)で、
右ブロック内の隣接交換が、連結後の対応する位置の隣接交換へ送られることを証明した。
位置iを左ブロックの長さmだけずらす `Fin.natAdd` と、次数の等式による位置の移送を明示した。
既存の置換作用の生成元である隣接交換と比較しており、別の作用を連結から移送して定義してはいない。
このモジュールは対称モノイダル構造を仮定する共通圏論で、スペクトルには依存しない。

### 円への特殊化と残りの範囲

[SpherePowerCoherence](../SerrePositivity/Spectra/SymmetricSequence/SpherePowerCoherence.lean)で、
右単位・三次数の結合・右ブロックの隣接交換の結果を円の反復smashへ接続した。
左右単位の一般論は共通モジュールにあり、球面側では既存の連結同型をそのまま利用する。

今回完成したブロック比較は右ブロックの隣接交換に限る。
左ブロックの隣接交換、全置換への拡張、左右ブロックの交換と連結の両立は未実装である。
次にこれらを証明し、convolutionの普遍性から球面対称列の乗法と可換モノイド構造を構成する。
可換モノイド、対称スペクトル、安定モデル構造、導来演算は今回の到達点には含めない。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1900ジョブで成功した。
集約をビルドした後の公理監査で、共通基盤を含む53モジュール・630宣言について、
標準公理のみで `sorry` 依存なしを確認した。
ソースの行長・空白、共通層からスペクトル層への逆importがないこと、
ドキュメントのローカルリンク、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 30. 実施記録：左ブロックの全位置の隣接交換（2026-10-13）

### 先頭二因子の比較と位置についての帰納

[TensorPowerLeftBlock](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerLeftBlock.lean)で、
左ブロックの全位置の隣接交換と連結の両立を証明した。
先頭二因子を保った尾の連結を、先頭二因子を一つのブロックとする括り方へ比較し、
結合子の自然性とwhiskerの交換則から先頭二因子の交換との両立を導いた。
この比較は尾の連結を任意の射として扱える一般補題である。
その後、先頭を保つ再帰的な隣接交換について交換位置の帰納を行った。

左ブロックの次数m+1と右ブロックの次数nの連結後は、
`(m+1)+n = (m+n)+1` の移送を明示する。
左ブロックの位置iは `Fin.castAdd n i` に送られ、位置の値は変わらない。
先頭位置と後続位置のどちらも、この次数の移送と既存の `adjacentIso` を比較している。
単位・結合の一般論に続き、球面に依存しない共通のモノイダル圏論として配置した。

[SpherePowerCoherence](../SerrePositivity/Spectra/SymmetricSequence/SpherePowerCoherence.lean)に、
この左ブロックの結果を円の反復smashへ特殊化する宣言を追加した。
左右ブロックの隣接交換の比較が揃ったが、全ブロック置換の同変性をまだ主張していない。
次に、対称群がこれらの生成元で生成されることと既存の作用の乗法則を用いて、
任意の左右ブロックの置換へ拡張する。
ブロック全体の交換と連結の両立、convolutionの乗法・可換モノイド構造はその後に行う。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1901ジョブで成功した。
最新の集約の公理監査で、共通基盤を含む54モジュール・640宣言について、
標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 31. 実施記録：任意の左右ブロック置換と連結の同変性（2026-10-13）

### 再利用した群論と有限集合の一般論

[PermutationInduction](../SerrePositivity/GroupTheory/Coxeter/PermutationInduction.lean)で、
型Aと対称群の同型を介して、Coxeter系の単純生成元による帰納を有限対称群へ移した。
恒等置換で成立し、右から隣接互換を掛ける段階で保存される性質は、全置換で成立する。
これは移植済みのTypeAの証明の帰結であり、新しい正規形の証明は追加していない。

[FiniteBlockEquiv](../SerrePositivity/CategoryTheory/FiniteBlockEquiv.lean)に、
標準有限集合のブロック全単射 `blockEquiv` と恒等・合成の比較を移した。
既存のnamespaceと宣言名は維持し、`Spectra/SymmetricSequence/DisjointUnion` はこれをimportする。
左右の二点の交換の像と、左右の置換の乗法を保つことも証明した。
この有限集合の一般論はスペクトルや全単射圏の定義に依存しない。

### 任意のブロック置換への拡張

[TensorPowerBlockPermutations](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerBlockPermutations.lean)で、
置換作用と次数の移送の両立を証明した。
左ブロックの隣接交換の結果を、移送を含まない全次数の作用の主張へ接続した。
その後、左右それぞれの任意の置換について、隣接互換による帰納と作用の乗法則を用いて
連結の同変性を証明し、二つを組み合わせた。

最終の一般定理 `appendIso_block_permutation` は、次数m・nの任意の置換σ・τについて、
各ブロックに作用してから連結する射が、連結してから `blockEquiv σ τ` に作用する射に
等しいことを述べる。第0段も含む。
作用の積と圏の合成の順序が逆であることを既存の乗法則で扱い、
連結から新しい作用を定義する代わりに、既存の `permutationAction` との一致を証明している。

[SpherePowerCoherence](../SerrePositivity/Spectra/SymmetricSequence/SpherePowerCoherence.lean)で、
この一般定理を円の反復smashと既存の `spherePermutationAction` へ特殊化した。
今回のブロック置換は左右それぞれの内部の置換であり、ブロック全体の入れ替えはまだ扱っていない。
次に連結を全単射圏上の自然変換へまとめ、ブロック全体の交換との整合性を証明する。
convolutionの普遍性からの乗法と可換モノイド構造はその後に構成する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1904ジョブで成功した。
移した有限集合の一般論も公理監査の対象へ加え、最新の集約の57モジュール・652宣言について、
標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 32. 実施記録：連結の自然変換と convolution の乗法（2026-10-13）

### 共通層の直和と連結

[FiniteBijectionSum](../SerrePositivity/CategoryTheory/FiniteBijectionSum.lean)に、
有限全単射圏の直和の対象・射・二変数関手を移した。
既存のnamespaceと宣言名を維持し、`Spectra/SymmetricSequence/DisjointUnion` は互換入口とした。
直和のモノイダル構造やDay convolutionへの登録は、引き続き既存のスペクトル側のモジュールで行う。

[PowerBijectionAppend](../SerrePositivity/CategoryTheory/Monoidal/PowerBijectionAppend.lean)で、
反復テンソルの連結同型を、全単射圏の二変数に関する自然変換 `appendNatTrans` へまとめた。
外部テンソル積から、直和関手と反復テンソル関手の合成への射である。
自然性の証明では、骨格の対象が射により等しくなることを用いて、
任意の全単射を各段の置換として読み、§31のブロック置換の同変性を適用した。
この共通の圏論は余極限やconvolutionの存在を仮定しない。

### 左 Kan 拡張からの乗法

[TensorPowerMultiplication](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerMultiplication.lean)で、
上の自然変換を対称列の外部テンソル積からの射 `tensorPowerAppend` として読んだ。
既存のconvolutionのHom同値の逆写像を用いて、
convolutionから反復テンソルの対称列への乗法 `tensorPowerMultiplication` を構成した。

convolutionの標準射との合成が元の連結の自然変換に等しいことを証明した。
標準のm元集合・n元集合での成分では、合成が既存の連結同型の射に一致する。
同じ因子化条件を満たす乗法が一意であることも、Hom同値の単射性から証明した。
[SphereMultiplication](../SerrePositivity/Spectra/SymmetricSequence/SphereMultiplication.lean)で、
自然変換・乗法・因子化・各次数の比較を円の反復smashの球面対称列へ特殊化した。

今回構成したのは乗法の射であり、モノイド構造の登録ではない。
単位射、convolutionの結合子・左右単位子に対する乗法の法則、可換性は未実装である。
ブロック全体の交換との比較も未実装であり、次にこれらを整えて可換モノイド構造へ進む。
各次数の連結について既に証明した結合・単位の整合性と、
今回の乗法の因子化を、convolutionの普遍性を介して利用する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1908ジョブで成功した。
移した直和の一般論も監査の対象へ加え、最新の集約の60モジュール・663宣言について、
標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 33. 実施記録：単位射と標準射上の左右単位比較（2026-10-13）

### 単位対象の普遍性からの射

[TensorPowerUnit](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerUnit.lean)で、
第0段の恒等射を一点圏からの自然変換 `tensorPowerUnitData` として定義した。
単位対象を定める空集合からの左Kan拡張の標準射 `convolutionUnitCan` を明示し、
その普遍性を用いて `tensorPowerUnit : convolutionTensorUnit ⟶ tensorPowerSequence X` を構成した。

標準射との合成が第0段の恒等射に等しいことを、自然変換の等式と第0段の成分の両方で証明した。
同じ因子化条件を満たす単位射は一意であることも証明した。
基礎圏に閉構造がある場合、登録済みの対称列のモノイダル単位からの射
`tensorPowerUnitHom` として読む定義も追加し、二つの表示が同じ射であることを確認した。

### 乗法との比較

単位対象の標準射と単位射を左側に置き、convolutionの標準射と乗法を合成する場合、
合成は基礎圏の左単位子と次数の移送に等しいことを証明した。
右側に置く場合の合成は、基礎圏の右単位子に等しいことも証明した。
この二つの比較は、単位射の第0段の因子化と、§32の乗法の各次数での因子化を用い、
既存の連結同型の左右単位の整合性へ帰着した。

[SphereUnit](../SerrePositivity/Spectra/SymmetricSequence/SphereUnit.lean)で、
単位射、登録済みのモノイダル単位からの表示、第0段の因子化を球面対称列へ特殊化した。
一般の左右比較も集約のimportから利用できる。

今回証明した左右比較は、単位対象とconvolutionを定める標準射上の比較である。
`η ⊗ 𝟙 ≫ μ = λ.hom` と `𝟙 ⊗ η ≫ μ = ρ.hom` という、
登録済みのconvolution全体の左右単位則はまだ証明していない。
次に左Kan拡張の普遍性でこの比較を持ち上げる。
乗法の結合則、ブロック全体の交換と可換性、可換モノイド構造の登録も未実装である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1910ジョブで成功した。
最新の集約の62モジュール・678宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 34. 実施記録：convolution 全体の左右単位則（2026-10-13）

### 二段の普遍性と登録済み Day 構造との比較

[DayUnitComparisons](../SerrePositivity/Spectra/SymmetricSequence/DayUnitComparisons.lean)で、
単位対象と対称列のconvolutionからの射は、二段の標準射上の値で決まることを証明した。
まずconvolutionの左Kan拡張の普遍性を使い、次に単位対象の左Kan拡張を
外部テンソル積へ延長した図式の普遍性を使う。
右側・左側の両方について、二段の標準射上の比較から射の等式を得る一般補題を整備した。

登録済みDay構造の埋め込み、convolutionの標準射、単位対象の標準射を、
既存の具体的な構成と比較する補題も追加した。
登録済みの標準射に含まれる恒等同型を介した合成は、射の等式として取り除いた。
この比較を用いて、convolutionの標準射と左右whiskerの両立、
登録済み左右単位子の標準射上での計算を利用できるようにした。

一般の単位の標準射 `convolutionUnitCan` とその左Kan拡張のinstanceは、
反復テンソル固有の `TensorPowerUnit` から [DayStructure](../SerrePositivity/Spectra/SymmetricSequence/DayStructure.lean)
へ移した。既存のnamespaceと宣言名は維持した。

### 反復テンソルと球面対称列の左右単位則

[TensorPowerUnitLaws](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerUnitLaws.lean)で、
直和の左右単位同型の逆射の像を、次数の移送および恒等射と比較した。
標準射上のwhiskerの計算と§33の左右比較を、上の二段の普遍性で持ち上げて、
登録済みconvolutionの左右単位則を証明した。

具体的には、単位射ηと乗法μについて
`(η ▷ F) ≫ μ = (λ_ F).hom` と `(F ◁ η) ≫ μ = (ρ_ F).hom` を
対称列の自然変換の等式として証明した。標準射上だけの比較ではない。
[SphereUnit](../SerrePositivity/Spectra/SymmetricSequence/SphereUnit.lean)で、この二つの法則を
円の反復smashの球面対称列へ特殊化した。

乗法・単位射・左右単位則が揃った。次は乗法の結合則をconvolution全体で証明する。
ブロック全体の交換との整合性、乗法の可換性、可換モノイド構造の登録も未実装である。
各次数の連結の結合の整合性は証明済みであり、Day構造の結合子との比較を介して利用する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1912ジョブで成功した。
最新の集約の64モジュール・699宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 35. 実施記録：乗法の結合則とモノイド構造（2026-10-13）

### 三重 convolution の比較

[DayAssociativityComparisons](../SerrePositivity/Spectra/SymmetricSequence/DayAssociativityComparisons.lean)で、
三重convolutionからの射が、二段の標準射上の値で決まる一般補題を証明した。
外側のconvolutionの左Kan拡張の普遍性に続き、内側のconvolutionを
外部テンソル積へ延長した図式の普遍性を使った。
登録済みDay構造の結合子の標準射上の計算も、既存の具体的なconvolutionへ接続した。

[SumCoherence](../SerrePositivity/Spectra/SymmetricSequence/SumCoherence.lean)で、
添字圏の括弧を変更する全単射 `assocEquiv` が、自然数の結合則による `finCongr` に
一致することを証明した。各ブロックの点を追跡し、因子の順序が変わらないことを確認した。
この全単射の反復テンソルへの像を、次数の結合則による移送へ比較した。

### convolution 全体の乗法の結合則

[TensorPowerAssociativity](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerAssociativity.lean)で、
三重convolutionの二段の標準射上で、乗法の二つの合成を比較した。
whiskerと標準射の両立、乗法の因子化、結合子の計算、自然性を用いて、
両辺を各次数の連結同型の式に帰着した。
最後に、既に証明した連結の結合の整合性を次数の逆移送と合成し、
convolution全体の自然変換の等式として乗法の結合則を証明した。

[TensorPowerMonoid](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerMonoid.lean)で、
構成済みの乗法・単位射と結合則・左右単位則を `MonObj (tensorPowerSequence X)` として登録した。
登録された乗法と単位射が、既存の構成と同じであることも確認した。

[SphereMonoid](../SerrePositivity/Spectra/SymmetricSequence/SphereMonoid.lean)で、
円へ特殊化した結合則と `MonObj sphereSequence` を接続し、
球面対称列を束ねたモノイド対象 `sphereMonoid` を構成した。
型の略記を重ねた球面対称列に対しては、一般のモノイド構造への接続を明示して登録した。
underlying object、乗法、単位射はいずれも既存の球面対称列・乗法・単位射と同じである。

今回完成したのはモノイド構造であり、可換性はまだ証明していない。
次はブロック全体の交換との整合性を証明し、Day convolutionの交換と比較して
乗法の可換性を得る。その法則を加えて可換モノイド構造を登録する。
対称スペクトルを球面対称列上の加群として構成する段階は、その後に行う。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1917ジョブで成功した。
最新の集約の68モジュール・715宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 36. 実施記録：可換性の帰着と第0段のブロック交換（2026-10-13）

### Day braiding と標準射の比較

[DayBraidingComparisons](../SerrePositivity/Spectra/SymmetricSequence/DayBraidingComparisons.lean)で、
登録済みconvolutionのbraidingを、各段のbraiding、convolutionの標準射、
添字圏の二ブロック全体の交換による誘導射へ展開する比較を証明した。
関手圏への埋め込みと既存のDay braidingの比較を用い、
交換後の和次数から元の和次数へ戻す添字圏の射も明示して扱った。

一般の対称列Fと乗法μについて、`(β_ F F).hom ≫ μ = μ` が、
全ての二つの添字での標準射上の交換の等式と同値であることを証明した。
一方の方向は可換性の等式へ標準射を合成することで得る。
逆方向はconvolutionの左Kan拡張の普遍性を使って自然変換の等式へ持ち上げる。

### 反復テンソルと第0段の比較

[TensorPowerCommutativity](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerCommutativity.lean)で、
乗法の因子化と骨格の標準対象による表示を用い、上の条件を各次数の連結同型へ帰着した。
乗法の可換性は、m・nについて、基礎圏のbraidingの後でn・mの順に連結し、
添字圏のブロック交換の像でm+n段へ戻す射が、m・nの順の連結に等しいことと同値である。
ここでの作用は既存の対称列の射の像であり、交換から新たな作用を定義してはいない。

[SumCoherence](../SerrePositivity/Spectra/SymmetricSequence/SumCoherence.lean)で、
片側が空の場合のブロック交換が、次数の可換則による移送に一致することを証明した。
その交換の反復テンソルへの像を次数の移送として計算し、braidingと左右単位子の一般則を用いて、
m=0およびn=0の場合の連結と交換の両立を証明した。
これにより、可換性の必要十分条件を正次数どうしの場合だけへ絞る定理も証明した。

[SphereCommutativity](../SerrePositivity/Spectra/SymmetricSequence/SphereCommutativity.lean)で、
全次数の条件、第0段を含む左右の比較、正次数だけへの帰着を球面対称列へ特殊化した。

今回完成したのは可換性への帰着と第0段の比較であり、可換性全体ではない。
正次数どうしのブロック全体の交換と連結の両立は未証明である。
次は一因子をブロックの向こうへ移す隣接互換の列を既存の置換作用で計算し、
braidingのhexagon・連結の結合の整合性・左右ブロック内の同変性を用いて一般のブロック交換へ拡張する。
この証明が得られたら、今回の必要十分条件から可換性を導き、`IsCommMonObj` を登録する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1920ジョブで成功した。
最新の集約の71モジュール・731宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 37. 実施記録：先頭因子の移動と巡回置換の作用（2026-10-13）

### 共通の有限置換

[FirstToLast](../SerrePositivity/GroupTheory/Coxeter/FirstToLast.lean)で、
先頭を固定し尾の置換を一つ後ろへずらす `shiftPerm` を構成した。
第0位置を固定すること、尾での作用、恒等・乗法の保存、
隣接互換を一つ後ろの隣接互換へ送ることを証明した。

この操作と先頭の隣接互換を用いて、先頭を末尾へ送る `firstToLastPerm` を再帰で構成した。
第0位置が末尾へ、その他の位置が一つ前へ送られることを証明し、
Mathlibの `(finRotate (n+1)).symm` に一致することを確認した。
群論の一般論として配置し、圏論・スペクトルには依存しない。

### 反復テンソルの隣接交換と braiding

[TensorPowerFirstCrossing](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossing.lean)で、
先頭因子を末尾へ移す同型 `moveFirstIso` を、既存の先頭の隣接交換と尾への左whiskerの再帰で構成した。
この射が、Xと残りn因子とのbraiding、右単位子の逆射による第1段への表示、
次数nと1の連結同型の合成に一致することを証明した。
帰納の基底ではbraidingと単位子の一般則、帰納段階ではhexagonと結合子の自然性を用いた。
この比較は置換作用を仮定しない一般の対称モノイダル圏の結果である。

[TensorPowerFirstCrossingAction](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossingAction.lean)で、
尾の置換をずらした既存の `permutationAction` が、一因子を固定した左whiskerに一致することを
隣接互換による帰納で証明した。
その結果、`firstToLastPerm` の既存の作用が `moveFirstIso` に一致し、
Mathlibの逆向きの巡回置換の作用も、上のbraidingと連結による射に一致することを証明した。
置換作用をbraidingから再定義するのではなく、構成済みの作用との一致を確認している。

[SphereFirstCrossing](../SerrePositivity/Spectra/SymmetricSequence/SphereFirstCrossing.lean)で、
移動の同型、有限置換の作用との比較、braidingとの比較を円の反復smashへ特殊化した。

今回完成したのは、先頭の一因子Xを末尾へ移す巡回置換の作用の比較である。
§36の正次数のブロック交換の条件には、Xの第1段 `power X 1 = X ⊗ 𝟙` という表示と
添字圏のブロック交換が現れるため、まず右単位子と次数の移送を介してこの比較へ接続する。
その後、hexagon・連結の結合の整合性・ブロック内の同変性により、
二つの一般の正次数のブロック全体の交換へ拡張する。
一般のブロック交換、乗法の可換性、`IsCommMonObj` の登録はまだ未実装である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1924ジョブで成功した。
最新の集約の75モジュール・752宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 38. 実施記録：第1段と任意の段の左右ブロック交換（2026-10-13）

### 巡回置換から添字の交換へ

[SumCoherence](../SerrePositivity/Spectra/SymmetricSequence/SumCoherence.lean)で、
右側の一因子とのブロック交換 `swapEquiv n 1` が、
順向きの `finRotate (n+1)` と `n+1 = 1+n` の次数の移送の合成に一致することを証明した。
末尾位置とそれ以外の位置を追跡して比較した。

[TensorPowerFirstCrossingAction](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossingAction.lean)で、
順向きの巡回置換の既存の作用が、先頭を末尾へ移す `moveFirstIso` の逆射に一致することを証明した。
§37の逆向きの巡回置換の比較から、作用の逆元保存と同型の逆射を用いて導いた。

### 第1段の表示と braiding

[TensorPowerCoherence](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerCoherence.lean)で、
第1段を左側に置く連結同型が、右単位子と次数の移送の合成に等しいことを証明した。
これは対称構造を仮定しないモノイダル圏の結果である。

[TensorPowerFirstCrossing](../SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossing.lean)で、
第1段 `power X 1 = X ⊗ 𝟙` と尾のbraidingの後に連結する射を、
右単位子でXへ戻してから `moveFirstIso` を適用する射と比較した。
braidingの自然性、§37の巡回移動の計算、単位子の逆射の打ち消しを用いた。

### 実際のブロック交換の等式

[TensorPowerSingleBlockSwap](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerSingleBlockSwap.lean)で、
添字圏の右側の一因子とのブロック交換の像を、巡回置換の作用と次数の移送として計算した。
上の第1段の比較と巡回移動の逆射を合成し、
第1段を左に置くブロック全体の交換と連結の両立を証明した。
第1段を右に置く場合も、基礎圏のbraidingの対称性と、
添字圏の二度のブロック交換が恒等射になることから証明した。

[SphereSingleBlockSwap](../SerrePositivity/Spectra/SymmetricSequence/SphereSingleBlockSwap.lean)で、
第1段と任意の段の左右の比較を球面対称列へ特殊化した。
これらは実際の対称列の射の像を含む§36の可換性の条件そのものである。
因子Xの移動だけの比較から、第1段の表示と次数の移送を介した接続が完了した。

第0段・第1段を含む場合は証明済みである。
一般の二つの正次数のブロック全体の交換は、まだ未証明である。
次に、一方のブロックを第1段と残りの連結として分け、hexagonと連結の結合の整合性を使って、
今回の比較と帰納仮定を合成する。添字圏のhexagonによる射の合成の比較も用いる。
この一般の交換が得られたら、§36の必要十分条件から乗法の可換性を導き、`IsCommMonObj` を登録する。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1926ジョブで成功した。
最新の集約の77モジュール・762宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力と、対称スペクトル以降の構成は未変更である。


## 39. 実施記録：一般のブロック交換と球面対称列の可換モノイド（2026-10-13）

### 共通のモノイダル関手の一般論

[BraidingPreservation](../SerrePositivity/CategoryTheory/Monoidal/BraidingPreservation.lean)で、
モノイダル関手がXとZ、YとZのbraidingを保存するなら、X⊗YとZのbraidingも保存することを証明した。
定義域と値域のhexagon、結合子・whiskerの像の計算、tensoratorと逆tensoratorの打ち消し、
braidingの自然性を用いた。この結果は対称構造を仮定せず、braidedな圏とモノイダル関手の一般論である。
スペクトルや反復テンソルに依存しない共通の圏論層に置いた。

[PowerBijectionMonoidal](../SerrePositivity/Spectra/SymmetricSequence/PowerBijectionMonoidal.lean)で、
既存の全単射圏上の反復テンソル関手に、モノイダル関手の構造を登録した。
単位比較は第0段の恒等同型、tensoratorは既存の連結同型である。
自然性は連結の自然変換から、結合・単位の整合性は証明済みの連結の比較と添字の射の像の計算から得た。
登録されたtensoratorと逆tensoratorが、既存の連結同型の射・逆射に等しいことも確認した。
このモジュールは円には依存しないが、添字圏の直和のモノイダル構造が現在スペクトル側にあるため、
その構造への接続としてスペクトル側に置いた。

### 帰納による一般のブロック交換

[TensorPowerBraiding](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerBraiding.lean)で、
反復テンソル関手のbraidingの保存を、添字の一方の濃度についての帰納で証明した。
第0段との交換を基底とし、第1段との交換と帰納仮定に上のモノイダル関手の一般補題を適用した。
`of 1 ⊗ of m = of (m+1)` の対象の等式を明示して、帰納段階の添字を揃えた。

その保存則を `Functor.Braided` として登録し、全次数m・nについて、
braiding、n・mの順の連結、添字のブロック交換の像の合成が、m・nの順の連結に等しいことを導いた。
既存の全置換作用と全単射圏上の関手をそのまま使い、braidingから作用を再定義してはいない。
第0段、第1段だけに限らない、一般の二ブロック全体の交換の証明が完了した。

### convolution の可換性と球面への登録

[TensorPowerCommMonoid](../SerrePositivity/Spectra/SymmetricSequence/TensorPowerCommMonoid.lean)で、
§36の可換性の必要十分条件に上の一般の交換を適用し、convolution全体の乗法の可換性を証明した。
既存の反復テンソルのモノイド構造に `IsCommMonObj` を登録した。

[SphereCommMonoid](../SerrePositivity/Spectra/SymmetricSequence/SphereCommMonoid.lean)で、
全次数のブロック交換と乗法の可換性を円へ特殊化し、`IsCommMonObj sphereSequence` を登録した。
可換モノイド対象 `sphereCommMonoid` を構成し、underlying object、乗法、単位射が
既存の球面対称列・乗法・単位射と同じであることを確認した。
可換性を忘れて得るモノイド対象も、既存の `sphereMonoid` と同じである。

球面対称列の可換モノイド構造が完成した。
次はこの球面モノイド上の加群として、対称スペクトルの対象・射・圏を構成する。
Mathlibの `Mathlib.CategoryTheory.Monoidal.Mod` にある内部加群の対象・射の一般論を入口として確認した。
採用済みのconvolutionと球面モノイドに適用し、各次数の構造射との対応を整える。
対称スペクトル、安定モデル構造、導来演算、K理論の降下入力は今回まだ構成・変更していない。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1932ジョブで成功した。
最新の集約の82モジュール・787宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 40. 実施記録：対称スペクトルの対象・射・圏と構造射（2026-10-13）

### Mathlib の内部加群を使った定義

[Basic](../SerrePositivity/Spectra/SymmetricSpectrum/Basic.lean)で、
`SymmetricSpectrum := CategoryTheory.Mod PointedSymmetricSequence sphereSequence` として
球面モノイド上の内部加群を対称スペクトルの主モデルへ採用した。
構成済みの対称列のconvolutionと球面のモノイド構造を用い、
Mathlibの加群の対象・作用を保つ射・圏の一般論を再利用した。

作用を忘れる関手とその忠実性、各次数の対象と射の成分を構成した。
加群作用の単位・結合則と、射が作用と両立する等式を既存の球面の乗法・単位で読める形に接続した。
対称列・作用・二つの法則から対象を作る構成子と、作用と両立する対称列の射から射を作る構成子も追加した。
射の各次数の成分が恒等・合成を保つこと、各次数の成分でスペクトルの射が決まることを証明した。

### 各次数の構造射と整合性

[StructureMaps](../SerrePositivity/Spectra/SymmetricSpectrum/StructureMaps.lean)で、
convolutionの標準射と加群作用を合成して
`spherePower p ∧ E_q → E_(p+q)` という各次数の構造射を構成した。
球面側とスペクトル側の二ブロックの置換に関する同変性、スペクトルの射の成分との両立を証明した。

第0段の構造射が基礎圏の単位子と添字の左単位同型の逆射の像に一致することも証明した。
二段の球面の連結を先に行う場合と、二回の作用を順に行う場合の等式は、
加群作用の結合則へ二段の標準射を合成し、Day結合子の計算・自然性・乗法の因子化から導いた。
基礎圏の結合子と添字圏の結合子の逆射の像を明示した各次数の等式である。
この証明では既存の三重convolutionの比較を再利用し、具体的な引数を明示して適用した。

[Suspension](../SerrePositivity/Spectra/SymmetricSpectrum/Suspension.lean)で、
第1段の構造射から標準の `S¹ ∧ E_n → E_(n+1)` を取り出した。
円と第1段の比較同型、`1+n = n+1` の次数の移送を明示した。
スペクトルの射の成分がこの懸垂構造射と両立することも証明した。

[Sphere](../SerrePositivity/Spectra/SymmetricSpectrum/Sphere.lean)で、
球面モノイド自身の正則加群を球面スペクトルとして構成した。
underlying対称列と加群作用は既存の球面対称列とその乗法であり、
各次数の構造射は既存の円の反復smashの連結同型に一致する。

### 到達点と次の範囲

対称スペクトルの対象・射・圏と、各次数の構造射・懸垂構造射・球面スペクトルが構成できた。
各次数の構造射の同変性・単位・結合の整合性と、射との両立も証明済みである。
次は自由球面加群と忘却関手の随伴、および各段の評価との接続を整える。
対称スペクトルの極限・余極限や球面上のテンソル積、弱同値・モデル構造・導来演算はまだ未実装である。
安定同値や安定ホモトピー群の仕様も、M0・M3の範囲として引き続き扱う。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1938ジョブで成功した。
最新の集約の86モジュール・815宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 41. 実施記録：自由内部加群と自由対称スペクトルの随伴（2026-10-13）

### 共通の圏論層の自由内部加群

[FreeModule](../SerrePositivity/CategoryTheory/Monoidal/FreeModule.lean)で、
一般のモノイダル圏とモノイド対象Mについて、M⊗Xを自由M加群にする構成を整備した。
作用は結合子の逆射とMの乗法の右whiskerの合成である。
単位則・結合則を、モノイドの法則、結合子の自然性、pentagonと単位の整合性から証明した。
Mathlibの内部加群の対象・射を再利用し、対称構造・閉構造・余極限は仮定しない共通の一般論とした。

生成元の射は、左単位子の逆射とMの単位の右whiskerの合成で定義した。
Xから加群Eへの射fは、Mによる左whiskerの後にEの作用を合成して自由加群の射へ延長した。
延長を生成元へ制限するとfになることと、自由加群の射がその生成元での値からの延長に等しいことを証明した。
これらからHom同値を構成し、左右の自然性を確認して、自由加群関手と忘却関手の随伴を得た。
随伴の単位が生成元の射、余単位のunderlying射が加群作用であることも証明した。

### 球面モノイドへの特殊化

[Free](../SerrePositivity/Spectra/SymmetricSpectrum/Free.lean)で、
上の一般論を球面対称列へ適用し、対称列を生成元とする自由対称スペクトルを構成した。
underlying対称列は球面とのconvolution `𝕊 ⊗ F` であり、
作用は既存の球面の乗法から得る射に一致する。
自由関手の後に作用を忘れる合成関手も、球面との左convolution関手に等しい。

対称列からの射と自由対称スペクトルからの射のHom同値、生成元からの延長、
延長の因子化と一意性をスペクトルのAPIとして公開した。
`freeFunctor ⊣ forget` を構成し、単位・余単位の具体的な射との比較も接続した。

今回の自由構成の入力は対称列である。
各段の基点付き単体的集合から作る自由スペクトル、すなわち各段の評価の左随伴はまだ構成していない。
次に対称列の各段の評価とその左随伴を整え、今回の自由球面加群関手と合成して接続する。
対称スペクトルの極限・余極限、球面上のテンソル積、弱同値・モデル構造・導来演算も引き続き未実装である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1940ジョブで成功した。
最新の集約の88モジュール・842宣言について、標準公理のみで `sorry` 依存なしを確認した。
行長・空白、未完了の証明用マーカー、共通層からスペクトル層への逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 42. 実施記録：各段の評価と自由対称スペクトルF_n（2026-10-13）

### 対称列の自由生成

[SymmetricSequence/Evaluation](../SerrePositivity/Spectra/SymmetricSequence/Evaluation.lean)で、
対称列の第n段の評価とその左随伴を構成した。
Mathlibの `evaluationLeftAdjoint` と `evaluationAdjunctionRight` を再利用し、
点ごとのテンソル積を登録しない対称列の型へ随伴を移した。
仮定は、全単射のHomで添字付けた余積の存在だけである。

自由対称列の第m段は、nからmへの全単射で添字付けたXの余積として定義される。
生成元の射は恒等全単射に対応する余積への包含である。
第n段への射fの延長は、各全単射hについてfとF(h)を合成し、余積の普遍性でまとめる。
成分の具体的な式、生成元への制限、延長の因子化・一意性、随伴の単位との一致を証明した。
入力Xには対称群の作用を要求しない。作用を保持する評価への左随伴とは区別する。

### 球面の自由加群との合成

[SymmetricSpectrum/Evaluation](../SerrePositivity/Spectra/SymmetricSpectrum/Evaluation.lean)で、
対称列の自由生成と自由球面加群を合成してF_nを構成した。
随伴の合成により、`F_n ⊣ evaluation n` と
`Hom(F_n X, E) ≃ Hom(X, E_n)` を得た。
生成元の射からの延長、生成元上での一致、延長の一意性も証明した。

underlying対称列は球面と自由対称列のconvolutionである。
生成元の射が二つの自由構成の生成元の射の合成であることと、
延長が自由対称列への延長・自由球面加群への延長を順に行う構成に一致することも証明した。
基点付き単体的集合に対して、余積の存在は既存の基盤のインスタンスから供給される。

### 到達点と次の範囲

対称列を入力とする自由スペクトルに加え、基点付き単体的集合を入力として
第n段を生成する自由スペクトルとその普遍性が利用できる。
各段を対称群に沿って誘導されたsmashとして表す比較同型は、今回の範囲には含めない。
次は対称スペクトルの極限・余極限を整え、この具体的な表示にも接続する。
球面上のテンソル積、弱同値・モデル構造・導来演算・安定ホモトピー群も引き続き未実装である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1943ジョブで成功した。
最新の集約の90モジュール・866宣言について、標準公理のみで `sorry` 依存なしを確認した。
97個のLeanソースの行長・空白・未完了の証明用マーカー、共通層からの逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 43. 実施記録：内部加群と対称スペクトルの極限・余極限（2026-10-13）

### 内部加群の共通構成

[ModuleLimits](../SerrePositivity/CategoryTheory/Monoidal/ModuleLimits.lean)で、
一般のモノイダル圏Cとモノイド対象Mについて、内部加群の極限を構成した。
基礎圏の任意の極限錐cに対して、`M ⊗ c.pt → c.pt` を極限の普遍性で定義する。
各射影への合成は、Mを射影に作用させた後、図式の各加群の作用を合成した射である。
単位則・結合則を各射影上で確認し、加群の極限錐とその普遍性を証明した。
テンソル積の極限保存を仮定しない。

underlying射の逆射も作用と両立することから、忘却関手の同型の反映を登録した。
極限錐の持ち上げとMathlibの創出の一般論を組み合わせ、忘却関手が極限を創出することを証明した。
基礎圏の極限の存在から加群圏の極限の存在を供給するインスタンスも登録した。

[ModuleColimits](../SerrePositivity/CategoryTheory/Monoidal/ModuleColimits.lean)で、
同様に基礎圏の任意の余極限余錐に加群作用を誘導し、余極限の普遍性と創出を証明した。
こちらの仮定は、全ての左テンソル関手が対象とする図式の形の余極限を保存することである。
Mとのテンソルの余極限から作用を定義し、単位と二つのMのテンソルの保存を使って作用の法則を確認した。
閉構造を共通定理の仮定に直接含めず、保存の条件を明示する形とした。
二つの共通モジュールはスペクトルの構成に依存しない。

### 対称列と対称スペクトルへの接続

[SymmetricSequence/Limits](../SerrePositivity/Spectra/SymmetricSequence/Limits.lean)で、
関手圏の点ごとの極限・余極限を対称列の型へ移した。
関手圏への恒等的な包含の保存と、各段の評価による保存を登録した。
既存のDay convolutionのモノイダル構造は維持する。

[SymmetricSpectrum/Limits](../SerrePositivity/Spectra/SymmetricSpectrum/Limits.lean)で、
共通の内部加群の一般論を球面モノイドへ適用した。
余極限側の左テンソルの保存は、既に構成した対称列の閉構造と随伴から得られる。
対称スペクトルに宇宙uの小さい極限・余極限の存在、忘却関手の創出・保存、
各段の評価による極限・余極限の保存を登録した。
一般の図式の形については、基点付き単体的集合側の存在を仮定するAPIも公開した。

極限スペクトルの第n段と第n段の図式の極限との標準同型、
および余極限の対応する標準同型を構成した。
各同型と逆同型について、射影・包含との両立も証明した。
対称列を入力とする自由関手と、第n段を生成するF_nの余極限保存も随伴から登録した。

### 到達点と次の範囲

通常の極限・余極限を対称スペクトルの各段で計算する基盤が利用できる。
積・引き戻し・余積・押し出しなどの構成を、既存の圏論APIから扱えるようになった。
次は自由スペクトルの各段の具体的な表示へ接続し、球面上のテンソル積の構成を進める。
ホモトピー極限・余極限、弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1947ジョブで成功した。
最新の集約の94モジュール・931宣言について、標準公理のみで `sorry` 依存なしを確認した。
101個のLeanソースの行長・空白・未完了の証明用マーカー、共通層からの逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 44. 実施記録：自由スペクトルの各段の生成元・関係式と零になる範囲（2026-10-13）

### 自由対称列の集中する次数と置換作用

[FreeSupport](../SerrePositivity/Spectra/SymmetricSequence/FreeSupport.lean)で、
自由対称列の全ての余積成分への包含を公開した。
全単射の作用が余積の添字への後合成であること、入力の射が全ての成分に同じ射を作用させること、
各段からの射が余積成分上の値で決まることを証明した。
全ての成分は、恒等全単射の生成元を全単射で移送して得られる。

生成する次数n以外では全単射の添字が空となるため、各段が始対象となることを証明した。
第n段では、置換σに対応する生成元へ置換τを作用させると、τ・σに対応する生成元になる。
この順序は既存の群の積と圏の合成の規約に一致する。

### convolutionの各段の生成元と関係式

[FreeConvolution](../SerrePositivity/Spectra/SymmetricSequence/FreeConvolution.lean)で、
自由対称列とのconvolutionの分解図式を公開した。
各項は、第一の対称列の段と、nから第二ブロックへの全単射で添字付けたXの余積とのテンソル積である。
既存の点ごとの左Kan拡張から、その図式の余極限との比較同型を得た。

第一ブロックaとnの直和からmへの全単射hについて、
`F(a) ⊗ X → (F ⊗ freeAt_n X)_m` の生成元の射を定義した。
任意の分解項の余積成分からの射が、この生成元の一つに等しいことを証明した。
左テンソルの余積保存と点ごとのKan拡張の普遍性から、
第m段からの射が全ての生成元上の値で決まることも証明した。

出力の全単射による作用は、生成元の添字hへの後合成となる。
第一ブロックの全単射kによるFの作用は、hへkと恒等射の直和を前合成する関係式に一致する。
この比較は、次に対称群に沿う誘導商を構成する際の関係式になる。
生成元上の射の決定は証明済みだが、その関係式を満たす任意の族からの延長は今後整備する。

### n未満の段の零対象性と球面への特殊化

分解の濃度はp+q=mを満たす。m<nの場合はqがnと異なるため、
自由対称列のq段は始対象であり、左テンソルの始対象保存から各分解項も始対象となる。
[InitialColimits](../SerrePositivity/CategoryTheory/Limits/InitialColimits.lean)に、
始対象の図式の余極限も始対象となる一般論を置き、各段の始対象性へ接続した。
この補助結果はモノイダル構造やスペクトルに依存しない。
公理監査の対象も共通の `CategoryTheory.Limits` 層へ拡張した。

[FreeLevels](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevels.lean)で、
上の構成を球面対称列へ特殊化した。
F_n Xの各段の余極限表示、球面とXからの生成元、その生成元による射の決定、
出力と球面側のブロックの作用の関係式を公開した。
n未満の段の始対象性と、基点付き単体的集合の零対象との比較による零対象性も証明した。

### 到達点と次の範囲

F_n Xの各段について、分解図式・生成元・ブロックの関係式と、n未満の段の零対象性が利用できる。
n以上の段を一つの第一ブロックp=m−nへまとめ、
対称群に沿う誘導商として表す比較同型は引き続き構成する。
その際は生成元の関係式を満たす族からの延長を整え、比較同型の両方向を証明する。
球面上のテンソル積、モデル構造・導来演算・安定ホモトピー群も今後の範囲である。

### 検証

集約 `SerrePositivity.Spectra.Foundations` のビルドは1951ジョブで成功した。
最新の集約の98モジュール・970宣言について、標準公理のみで `sorry` 依存なしを確認した。
105個のLeanソースの行長・空白・未完了の証明用マーカー、共通層からの逆import、
ドキュメントのローカルリンクと章番号、`git diff --check` も確認した。

共有ルートimport・依存設定・元リポジトリ・並行作業のファイルは編集していない。
定理3.1・補題4.6の二つの降下入力は未変更である。


## 45. 実施記録：生成元からの降下と自由スペクトルの誘導図式表示（2026-10-14）

### 引き継ぎと保存

共通の圏論・群論基盤、スペクトル本体と計画・監査、誘導表示の作業途中の保存を
三つのコミットに分けた。作業途中の保存時点ではFreeConvolutionDescはビルド済みだが、
FreeInductionの余錐の自然性証明が失敗していた。後者は集約のimportには含まれていなかった。
共有ルートimportと並行作業の可換環・CLMST関連の変更はコミット対象から除外した。

### 関係式を満たす射の族からの降下

[FreeConvolutionDesc](../SerrePositivity/Spectra/SymmetricSequence/FreeConvolutionDesc.lean)で、
第一ブロックの全単射の関係式を満たす生成元上の射の族を定義した。
左テンソルの余積保存によって分解図式の各項への射を作り、自然性を証明して余錐を構成した。
各段全体への延長、生成元上の因子化、一意性とHom同値を得た。

### 誘導図式との比較

[FiniteBijectionShift](../SerrePositivity/CategoryTheory/FiniteBijectionShift.lean)で、
固定したn元の有限集合を右に加える関手を構成した。
[FreeInduction](../SerrePositivity/Spectra/SymmetricSequence/FreeInduction.lean)では、
この関手のcostructured arrow圏上の誘導図式を構成した。
第一ブロックの濃度はm−nであり、各項はFのm−n段とXのテンソル積に等しい。

余錐の自然性では、添字圏の関手の射とブロックの直和射を明示的に比較することで、
引き継ぎ時の書き換えの失敗を解消した。
生成元からの降下の普遍性を使い、自由convolutionの第m段がこの図式の余極限になることを証明した。
比較同型の両方向は、生成元と標準包含を互いに送る。
射の決定には第一ブロックを標準のm−n元の有限集合に固定した生成元だけで十分である。

[FreeLevelInduction](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelInduction.lean)で、
上の一般論を球面対称列へ特殊化した。
自由スペクトルF_n Xの第m段と誘導図式の余極限との比較同型を構成し、
各項がm−n次球面とXのsmashであること、比較同型の両方向と生成元の両立を証明した。
集約Foundationsからこれらを公開した。

### 到達点と次の範囲

各段の誘導図式による余極限表示が利用できる。
対称群の明示的な商表示との比較、出力の置換作用と入力の射に関する自然性は今後整備する。
球面上のテンソル積、弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1955ジョブで成功した。
監査対象へFiniteBijectionShiftを追加し、102モジュール・1018宣言について、
標準公理のみでsorry依存なしを確認した。
変更したLeanソースの行長・末尾空白・未完了の証明用マーカーとgit diff --checkも確認した。


## 46. 実施記録：自由スペクトルの誘導表示の自然性と対称群作用（2026-10-14）

### 余極限上の出力と入力の射

[FreeInductionNaturality](../SerrePositivity/Spectra/SymmetricSequence/FreeInductionNaturality.lean)で、
出力の全単射を誘導図式の全単射の添字への後合成として定義した。
標準包含の移送から余錐を作り、余極限の普遍性で出力の射へ延長した。
入力の射は各項の第二因子へ作用する自然変換を作り、その余極限の射として定義した。

両者について恒等射・合成の法則と、入力の射と出力の全単射の可換性を証明した。
自由convolutionの生成元に関する入力の自然性は、自由対称列の生成元の自然性と、
外部テンソル積・左Kan拡張の関手性から証明した。
既存の各段の比較同型は、出力の全単射と入力の射の両方に関して自然である。

### 作用付きの比較

[FreeInductionAction](../SerrePositivity/Spectra/SymmetricSequence/FreeInductionAction.lean)で、
余極限上の出力の対称群作用を構成した。
置換の積と圏の合成の規約を既存のFiniteBijection.permutationに合わせ、
作用の単位・乗法則を出力の射の関手性から証明した。
標準包含に対する作用は、全単射の添字への後合成である。
入力の射を同変射へ持ち上げ、固定した出力次数で作用付きの誘導表示の関手を構成した。
自由convolutionの各段との比較を、対称群作用を備えた同型へ持ち上げた。

[FreeLevelAction](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelAction.lean)で、
上の一般論を球面対称列へ特殊化した。
自由スペクトルの入力の射と、具体的な自由convolutionの入力の射の一致は、
左Kan拡張の普遍性と登録済みのDay convolutionの標準射上での比較から証明した。
自由スペクトルの各段と誘導表示との、入力Xに自然な対称群作用付き同型を構成した。
自由スペクトルの各段の生成元についても、入力の射がXの因子へ作用することを証明した。

### 到達点と次の範囲

各段の誘導図式による表示を、出力の対称群作用と入力の射を含めて利用できる。
次は誘導図式と対称群の明示的な商表示との比較を整備する。
球面上のテンソル積、弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1958ジョブで成功した。
スペクトルの85個のLeanソースの行長・末尾空白・未完了の証明用マーカーと、
ドキュメントのローカルリンク、git diff --checkを確認した。
公理監査は105モジュール・1057宣言で成功し、標準公理のみでsorry依存なしを確認した。


## 47. 実施記録：自由スペクトルの各段の明示的なブロック商（2026-10-14）

### 生成元と対称群の関係式

[FreeBlockQuotient](../SerrePositivity/Spectra/SymmetricSequence/FreeBlockQuotient.lean)で、
第一ブロックをp=m−n、第二ブロックをnに固定した。
全単射h:p+n→mで添字付けたF_p⊗Xの余積を生成元の対象とし、
第一ブロックの置換σとhで添字付けた同じ対象の余積から二つの射を構成した。
一方の射はF_pへのσの作用を使い、もう一方はσと恒等射のブロック直和をhへ前合成する。
この二つの射の余等化子を、明示的なブロック商として定義した。

n≤mの場合はp+n=mであるため、全単射の添字の型とΣ_mとの同値も構成した。
関係式の添字はΣ_pと全単射の添字の積であり、
通常の誘導表示に現れるΣ_mとΣ_pの関係を明示する構成である。
現段階では余積の添字をΣ_mそのものへ置き換えた別の商対象は登録していない。

### 商の普遍性と比較同型

固定次数の生成元から自由convolutionの各段への射は、ブロックの関係式を同一視する。
任意の商の余錐から全ての第一ブロックの生成元上の射の族を復元し、
既存の生成元からの降下の普遍性に接続した。
これにより、各段を頂点とする余錐が余等化子の普遍性を持つことを証明した。

自由convolutionの各段と明示的なブロック商との比較同型を構成した。
比較同型の両方向は、固定次数の生成元と商の生成元を互いに送る。
商の生成元の関係式と、生成元上の値による商からの射の決定も証明した。
既存の誘導図式の余極限との比較同型を構成し、生成元をその標準包含へ送ることを証明した。

[FreeLevelQuotient](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelQuotient.lean)で、
これらを球面対称列へ特殊化した。
球面側の置換作用と全単射の添字のブロック置換を同一視する関係式を公開し、
自由スペクトルF_n Xの第m段と余等化子との比較同型を構成した。
各項はS^{m−n}とXのsmashであり、n未満では商も零対象になる。

### 到達点と次の範囲

自由スペクトルの各段を、具体的な生成元の余積と対称群の関係式の余等化子として利用できる。
次はこの商上の出力の対称群作用と入力の自然性を構成し、既存の作用付き誘導表示と比較する。
全単射の添字をΣ_mへ置き換えた表示や、球面上のテンソル積への接続も今後整備する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1960ジョブで成功した。
スペクトルの87個のLeanソースの行長・末尾空白・未完了の証明用マーカーと、
ドキュメントのローカルリンク、git diff --checkを確認した。
公理監査は107モジュール・1092宣言で成功し、標準公理のみでsorry依存なしを確認した。


## 48. 実施記録：明示的な商表示の自然性と対称群作用（2026-10-14）

### 商の普遍性から構成する射

[FreeBlockQuotientMaps](../SerrePositivity/Spectra/SymmetricSequence/FreeBlockQuotientMaps.lean)で、
第一ブロックの関係式を満たす生成元上の射の族を商全体の射へ降ろす構成を公開した。
出力の自己全単射は全単射の添字への後合成、入力の射は各生成元の第二因子への作用として定義した。
いずれも関係式を保つことを証明し、余等化子の普遍性から商上の射へ降ろした。
既存の比較同型による作用の移送を定義に使わず、商の普遍性から直接構成した。

生成元上の因子化、恒等射・合成の法則と入力の射・出力の全単射の可換性を証明した。
自由convolutionの各段と商との比較同型は、出力の自己全単射と入力の射の両方に関して自然である。
出力の射のAPIは固定したmの自己全単射を対象とする。
異なる次数mとm'の全単射に関する一般化は、この商のAPIにはまだ登録していない。

### 対称群作用と比較の自然同型

[FreeBlockQuotientAction](../SerrePositivity/Spectra/SymmetricSequence/FreeBlockQuotientAction.lean)で、
商上の出力の射を対称群作用へまとめた。
作用は生成元の全単射の添字への後合成であり、積と圏の合成の規約は既存の構成に一致する。
入力の射を同変射とし、固定した出力次数で作用付きの商表示の関手を構成した。

自由convolutionの各段と商との比較を対称群作用付きの同型へ持ち上げた。
商と既存の誘導図式の作用付き比較は入力に関して自然であり、自然同型として構成した。
各段から商を経由して誘導表示へ送る比較は、元の誘導表示への比較と一致することも証明した。

[FreeLevelQuotientAction](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelQuotientAction.lean)で、
これらを球面対称列へ特殊化した。
自由スペクトルの作用付き各段と商表示との自然同型、
商表示と既存の作用付き誘導表示との自然同型を構成した。
生成元への置換作用と入力の射の公式、自然同型の合成が元の比較に一致することも公開した。

### 到達点と次の範囲

自由スペクトルの各段の明示的な商表示は、出力の対称群作用と入力の射を含めて利用できる。
次は全単射の添字をΣ_mそのものへ移送した商表示と、球面上のテンソル積への接続を整備する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1963ジョブで成功した。
スペクトルの90個のLeanソースの行長・末尾空白・未完了の証明用マーカーと、
ドキュメントのローカルリンク、git diff --checkを確認した。
公理監査は110モジュール・1135宣言で成功し、標準公理のみでsorry依存なしを確認した。


## 49. 実施記録：対称群そのもので添字付けた自由スペクトルの誘導商（2026-10-14）

### 全単射の添字と対称群の乗法の規約

[FreePermutationIndex](../SerrePositivity/Spectra/SymmetricSequence/FreePermutationIndex.lean)で、
n≤mの場合の標準のブロック直和p+nと出力mの同型を構成した。ここでp=m−nである。
この同型を使い、全単射h:p+n→mの添字とΣ_mとの同値を明示した。
第一ブロックのΣ_pからΣ_mへの置換の移送が群の積を保つことも証明し、準同型として公開した。

ブロック置換をhへ前合成すると、対応するΣ_mの置換へブロック置換を右から掛ける。
出力の置換をhへ後合成すると、対応するΣ_mの置換へ左から掛ける。
この二つの公式を、群の積と圏の合成の規約に合わせて証明した。

### 対称群で添字付けた余等化子

[FreePermutationQuotient](../SerrePositivity/Spectra/SymmetricSequence/FreePermutationQuotient.lean)で、
Σ_mで添字付けたF_p⊗Xの余積と、Σ_p×Σ_mで添字付けた関係式の余積を構成した。
関係式の左辺はF_pへの置換σの作用を使い、右辺は添字τをτ・b(σ)へ送る。
bは第一ブロックの置換をΣ_mへ移す準同型である。
この二つの射の余等化子を、対称群そのもので添字付けた誘導商として定義した。

生成元の関係式、生成元上の値による射の決定と、関係式を満たす族からの降下を公開した。
全単射の商との比較の両方向を生成元上で構成し、互いに逆であることを証明した。
余積の添字の同値だけでなく、関係式を含む余等化子の比較同型を構成した。

### 出力の左乗法と入力の同変射

[FreePermutationAction](../SerrePositivity/Spectra/SymmetricSequence/FreePermutationAction.lean)で、
出力の置換κを添字τへの左乗法κ・τとして商へ降ろした。
関係式を保つことは群の結合則から証明し、出力の対称群作用へまとめた。
入力の射は各生成元の第二因子へ作用し、出力の対称群に関する同変射となる。
これらを固定した出力次数の関手へまとめ、全単射の商との作用付き自然同型を構成した。

[FreeLevelPermutation](../SerrePositivity/Spectra/SymmetricSpectrum/FreeLevelPermutation.lean)で、
上の構成を球面対称列へ特殊化した。
自由スペクトルF_n Xの第m段を、Σ_mで添字付けたS^{m−n}とXのsmashの余積から作る誘導商と比較した。
生成元の関係式、出力の左乗法、入力の射の公式と、作用付き各段との自然同型を公開した。

### 到達点と次の範囲

n以上の段の、対称群そのもので添字付けた誘導表示が入力の自然性と出力の作用を含めて利用できる。
n未満の段の零対象性は既存のFreeLevelsとFreeLevelQuotientで扱う。
次は球面モノイド上のテンソル積へ進み、加群の作用を用いた二つの射の余等化子を構成する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1967ジョブで成功した。
スペクトルの94個のLeanソースの行長・末尾空白・未完了の証明用マーカーと、
ドキュメントのローカルリンク、git diff --checkを確認した。
公理監査は114モジュール・1193宣言で成功し、標準公理のみでsorry依存なしを確認した。


## 50. 実施記録：球面上のテンソル積の基礎となる釣り合い商（2026-10-14）

### 共通の内部加群の商と普遍性

[BalancedTensor](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensor.lean)で、
内部加群EとFについて、(E⊗M)⊗FからE⊗Fへの二つの射を構成した。
第一の射はEの左作用をbraidingで右側へ移した射を使い、
第二の射は結合子とFの左作用を使う。
これらの余等化子を釣り合いテンソル積の基礎対象として定義した。

標準射が二つの作用を同一視することと、標準射のエピ性を証明した。
釣り合い条件を満たす射の型、商への降下、因子化、一意性とHom同値を構成した。
二つの関係式が加群の射に関して自然であることを証明し、
二つの加群の射を商の射へ降ろした。
標準射との両立、恒等射・合成の法則から二変数関手まで構成した。

この層の仮定はbraidingと余等化子の存在であり、テンソル積の余極限保存を仮定しない。
ここで構成するのは基礎圏の対象であり、この商上の加群作用はまだ登録していない。
左作用を右側へ移した射の加群射に関する自然性は証明したが、
一般のbraided圏での右加群の法則を別の構造として登録することは、この段階の範囲に含めない。

### 球面への特殊化と各段の計算

[TensorQuotient](../SerrePositivity/Spectra/SymmetricSpectrum/TensorQuotient.lean)で、
上の一般論を球面モノイドと対称スペクトルへ特殊化した。
球面上のテンソル積の基礎となる対称列tensorSequenceを構成した。
二つの関係式は既存のbraiding・結合子・球面作用から得られる射であることも明示した。

通常のconvolutionから商への標準射はエピである。
釣り合い条件を満たす対称列の射の降下と一意性、Hom同値、
二つのスペクトルの射に関する関手性を公開した。
対称列の評価の余等化子保存を使い、tensorSequenceの第n段と
二つの関係式の第n段の余等化子との比較同型を構成した。
この比較は標準射を各段の余等化子の標準射へ送る。

### 到達点と次の範囲

球面上のテンソル積の基礎となる対称列の商と、その普遍性・関手性が利用できる。
次は球面の可換性とconvolutionの余等化子保存を使い、この商上へ球面作用を降ろす。
作用の単位・結合則を証明して対称スペクトルへ持ち上げ、その射と二変数関手へ接続する。
その後にスペクトル圏のテンソル単位・結合子・対称性と自由スペクトルの比較を整備する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1969ジョブで成功した。
スペクトルの95個と新しい共通層の1個のLeanソースについて、
行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンクとgit diff --checkも確認した。
公理監査は116モジュール・1243宣言で成功し、標準公理のみでsorry依存なしを確認した。


## 51. 実施記録：釣り合い商上の球面作用と対称スペクトルのテンソル積（2026-10-14）

### 右テンソルの加群作用と左右の作用の整合性

[TensorRightModule](../SerrePositivity/CategoryTheory/Monoidal/TensorRightModule.lean)で、
加群Eの作用からE⊗Xの加群作用を構成した。
作用は結合子の逆とEの作用の右テンソルであり、単位・結合の法則を証明した。
第一因子の加群の射と第二因子の射が誘導する加群の射と、右テンソルの結合子も構成した。

係数モノイドが可換な場合、Eの左作用とbraidingで右側へ移した作用の整合性を証明した。
証明にはbraidingの自然性・hexagon、Eの作用の結合則と係数の可換性を使った。
右側へ移した作用はE⊗MからEへの加群の射となる。

### 商への作用の降下

[BalancedTensorModule](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorModule.lean)で、
釣り合い関係式の二つの射を加群の射へ持ち上げた。
第一の射には左右の作用の整合性、第二の射には右テンソルの結合子と第二因子の射を使う。
この平行射の図式の忘却像を、既存の基礎対象の釣り合い関係式の図式と比較した。

左テンソルが余等化子を保存する場合、既存の加群の余極限の一般論で
釣り合い商へ作用を降ろし、単位・結合の作用則を持つ内部加群を構成した。
その基礎対象は前回の商そのものであり、別の基礎対象への置き換えは行わない。
標準射を介した作用の公式と、既存の商の射の作用との両立を証明し、
加群圏に値を取るテンソル積の二変数関手へまとめた。

第一因子の作用と両立する釣り合い射は、加群の射として降下できる。
その基礎対象の射は既存の釣り合い射の降下に一致する。
商の作用の比較と射の同変性には、左テンソルによる標準射のエピ性を用いた。
共通層では全ての左テンソルの平行射図式の余極限保存だけを明示的に仮定する。

### 球面上の対称スペクトルのテンソル積

[Tensor](../SerrePositivity/Spectra/SymmetricSpectrum/Tensor.lean)で、
球面の可換性とconvolutionの閉構造から上の構成へ接続した。
対称スペクトルsphereTensor E Fを構成し、
その基礎対称列が既存のtensorSequence E Fであることを証明した。
球面作用は標準射を介して第一のスペクトルの作用と両立する。

二つのスペクトルの射から得るテンソル積の射と、スペクトル圏の二変数関手を構成した。
球面作用を忘れると、前回の釣り合い商の対称列の二変数関手そのものである。
球面作用と両立する釣り合い射のスペクトルとしての降下、
標準射上の因子化と一意性も公開した。

### 到達点と次の範囲

球面上のテンソル積は、対称スペクトルとその射・二変数関手として利用できる。
次は球面スペクトルをテンソル単位とする比較と、自由スペクトルとのテンソル積の比較へ進む。
結合子・対称性・整合性を証明し、スペクトル圏のモノイダル構造を登録する作業も残る。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1972ジョブで成功した。
スペクトルの96個と新しい共通層の2個のLeanソースについて、
行長・末尾空白・未完了の証明用マーカーと共通層からのimport方向を確認した。
ドキュメントのローカルリンクとgit diff --checkも確認した。
公理監査は119モジュール・1279宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 52. 実施記録：球面上のテンソル積の右単位自然同型（2026-10-14）

### 正則加群との右単位比較

[BalancedTensorRightUnit](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorRightUnit.lean)で、
可換モノイドM上の加群Eについて、釣り合いテンソル積E⊗_M MとEの同型を構成した。
braidingで右側へ移した作用の単位則・結合則を証明し、
この作用を釣り合い商からEへの射として降ろした。
逆射は右単位同型の逆、Mの単位の挿入、商への標準射の合成である。
作用の単位則と商の関係式から、両方向の合成が恒等射となることを証明した。

順方向がMの作用と両立することを左右の作用の整合性から証明し、
同型を基礎対象だけでなく加群の同型として構成した。
逆射の線形性には、線形な同型の逆射に関する既存の一般論を用いた。
Eの射に関する自然性を証明し、正則加群を右側に固定したテンソル積の関手と
恒等関手との自然同型へまとめた。

### 対称スペクトルへの特殊化

[TensorRightUnit](../SerrePositivity/Spectra/SymmetricSpectrum/TensorRightUnit.lean)で、
球面の可換モノイドと正則加群としての球面スペクトルへ上の比較を特殊化した。
sphereTensor E sphereからEへのスペクトルの同型と自然同型を構成した。
標準射上の順方向を右側へ移した球面作用、逆方向を球面の単位の挿入と比較した。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

球面スペクトルとの右テンソル積の単位比較は、スペクトルの自然同型として利用できる。
左単位比較、自由スペクトルとのテンソル積の比較、結合子・対称性・整合性の証明と
スペクトル圏のモノイダル構造の登録は今後進める。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1974ジョブで成功した。
新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
公理監査は121モジュール・1306宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 53. 実施記録：球面上のテンソル積の左単位自然同型（2026-10-14）

### 正則加群との左単位比較

[BalancedTensorLeftUnit](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorLeftUnit.lean)で、
可換モノイドM上の加群Eについて、釣り合いテンソル積M⊗_M EとEの同型を構成した。
正則加群の右側へ移した作用がMの乗法に一致することを可換性から証明した。
Eの左作用は作用の結合則により釣り合い条件を満たし、商からの射へ降下する。
逆射は左単位同型の逆、Mの単位の挿入、商への標準射の合成である。
作用の単位則と商の関係式から、両方向の合成が恒等射となることを証明した。

降下する作用の線形性を作用の結合則から証明し、加群の同型へ持ち上げた。
逆射の線形性には線形な同型の逆射に関する既存の一般論を用いた。
加群の射に関する自然性を証明し、正則加群を左側に固定したテンソル積の関手と
恒等関手との自然同型へまとめた。順逆の基礎射の公式も公開した。

### 対称スペクトルへの特殊化と左右の一致

[TensorLeftUnit](../SerrePositivity/Spectra/SymmetricSpectrum/TensorLeftUnit.lean)で、
球面の可換モノイドと正則加群としての球面スペクトルへ上の比較を特殊化した。
sphereTensor sphere EからEへのスペクトルの単位同型と自然同型を構成した。
標準射上の順方向を球面作用、逆方向を球面の単位の挿入と比較した。

球面スペクトル自身では、左右の単位同型が一致することも証明した。
商の標準射で射を決定し、球面の乗法の可換性から左右の作用を比較する。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

球面スペクトルは左右ともテンソル単位の自然同型を備える。
自由スペクトルとのテンソル積の比較、結合子・対称性・整合性の証明と
スペクトル圏のモノイダル構造の登録は今後進める。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1976ジョブで成功した。
新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
公理監査は123モジュール・1331宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 54. 実施記録：自由球面加群との右テンソル積の自然比較（2026-10-14）

### 自由加群との釣り合いテンソル積

[BalancedTensorFreeRight](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreeRight.lean)で、
可換モノイドM上の加群Eと対象Xについて、E⊗_M Free_M(X)とE⊗Xの比較を構成した。
順方向は結合子の逆を介して自由加群の係数をEの右作用へ移す射である。
右作用の結合則とモノイダル整合性から釣り合い条件を証明し、商からの射へ降ろした。
逆方向はXから自由加群への生成元をEの右にテンソルし、標準射で商へ送る。

順方向と逆方向の合成は右作用の単位則から恒等射になる。
商上の合成は、釣り合い関係式と「生成元に係数を作用させると自由加群の恒等射になる」
という既存の公式から恒等射になる。これにより基礎対象の比較同型を構成した。

結合子の加群作用との両立と、Eの右作用の線形性を組み合わせ、
比較をE⊗Xに第一因子から作用を与えた加群との同型へ持ち上げた。
加群の射と生成対象の射の両方に関する自然性を証明した。
通常の右テンソルの二変数関手と、第二因子を自由加群にした釣り合いテンソル積の関手を構成し、
比較を二変数の自然同型へまとめた。順逆の基礎射の公式も公開した。

### 対称スペクトルとF_nへの特殊化

[TensorFreeRight](../SerrePositivity/Spectra/SymmetricSpectrum/TensorFreeRight.lean)で、
球面の可換モノイドへ上の比較を特殊化した。
スペクトルEと対称列Xのconvolution E.X⊗Xに、Eから球面作用を与えたスペクトルを構成した。
sphereTensor E (freeObj X)とのスペクトルの同型を得て、順方向を係数の右作用、
逆方向を自由球面加群の生成元の挿入と比較した。
両方の入力の射に関する自然性と二変数の自然同型も公開した。

Xに第n段を自由生成する対称列を取ることで、sphereTensor E (F_n X)にも比較を特殊化した。
この比較もスペクトルと基点付き単体的集合の両方の射に関して自然である。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

自由球面加群を右因子とするテンソル積は、生成対称列とのconvolutionへ作用を与えた
スペクトルと自然同型である。F_nを右因子とする場合にも利用できる。
自由加群を左因子とする比較、自由スペクトル同士の積の比較、結合子・対称性・整合性の証明と
スペクトル圏のモノイダル構造の登録は今後進める。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

集約SerrePositivity.Spectra.Foundationsのビルドは1978ジョブで成功した。
新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
公理監査は125モジュール・1362宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 55. 実施記録：二つの自由スペクトルのテンソル積の自然比較（2026-10-14）

### 自由加群の右テンソルと二つの自由加群の積

[BalancedTensorFreePair](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreePair.lean)で、
自由M加群Free_M(X)の右にYをテンソルした加群とFree_M(X⊗Y)との同型を構成した。
基礎射は結合子の順逆であり、前回の右テンソルの結合子の線形性から加群の同型へ持ち上げた。
この部分はbraiding・係数の可換性・余等化子を仮定しない。
両方の生成対象の射に関する自然性と、生成元を結合子の逆で送る公式も証明した。

可換係数・余等化子とその左テンソルによる保存の仮定の下で、前回の自由右因子の比較と
上の結合子による比較を合成した。
これによりFree_M(X)⊗_M Free_M(Y)とFree_M(X⊗Y)の加群同型を構成した。
両方の生成対象の射に関する自然性を証明し、二変数関手間の自然同型へまとめた。
逆比較は積から作る自由加群の生成元を、二つの生成元のテンソルと標準射の合成へ送る。
順比較は二つの生成元のテンソルを積の生成元へ送る。両方向の公式を公開した。

### 対称スペクトルへの特殊化

[TensorFreePair](../SerrePositivity/Spectra/SymmetricSpectrum/TensorFreePair.lean)で、
二つの自由球面加群の球面上のテンソル積を、生成対称列のconvolutionから作る
自由球面加群と比較するスペクトルの同型を構成した。
右因子の比較と結合子の比較との合成、両方の射に関する自然性、
生成元上の順逆の公式、二変数の自然同型も公開した。

第m段・第n段を自由生成する対称列を代入し、F_m XとF_n Yの積にも特殊化した。
比較先は二つの生成対称列のconvolutionから作る自由球面加群である。
両方の基点付き単体的集合の射に関する自然性も証明した。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

二つの自由球面加群の積と、生成対称列の積の自由球面加群との自然同型を利用できる。
F_m・F_nの生成対称列の積をm+n次での自由生成表示へ整理する比較は残る。
自由加群を左因子とする一般の比較、結合子・対称性・整合性の証明と
スペクトル圏のモノイダル構造の登録も今後進める。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
集約SerrePositivity.Spectra.Foundationsのビルドは1980ジョブで成功した。
公理監査は127モジュール・1390宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 56. 実施記録：F_mとF_nのテンソル積の和次数の自由生成表示（2026-10-14）

### 二つの自由対称列のconvolution

[FreePairConvolution](../SerrePositivity/Spectra/SymmetricSequence/FreePairConvolution.lean)で、
第m段からXを生成する自由対称列と、第n段からYを生成する自由対称列のconvolutionを、
第m+n段からX⊗Yを生成する自由対称列と比較した。
基礎圏は閉対称モノイダル圏で小さい余極限を持つと仮定する。

二つの自由対称列の各項は全単射で添字付けた余積である。
左右のテンソルの余積保存を使い、二つの余積成分の積から指定された射を延長する構成と、
その成分上の公式・射の決定性を証明した。
和次数の射から直和の全単射で移送した射をこの構成でまとめ、外部積の自然変換を構成した。
convolutionの左Kan拡張の普遍性から、対称列全体の射へ延長した。

和次数の生成元は、二つの自由対称列の生成元をテンソルしてconvolutionの標準射で送る射である。
延長がこの生成元上で元の射に一致することを証明した。
全ての余積成分は和次数の生成元から全単射で移送して得られるため、
convolutionからの射も和次数の生成元上の値で決まる。
この決定性と自由対称列の随伴を使い、比較の順逆が互いに逆であることを証明した。
両方向の生成元の公式も公開した。

登録済みのDay構造の標準射とテンソル射の両立を使い、
convolutionの生成元の両方の入力の射に関する自然性を証明した。
比較同型が両方の入力に関して自然であることも生成元による決定性から証明した。

### 自由スペクトルの和次数表示

[TensorFreeAtSum](../SerrePositivity/Spectra/SymmetricSpectrum/TensorFreeAtSum.lean)で、
前回のF_m・F_nの積の比較に、自由球面加群関手で移した上の自由対称列の比較を合成した。
F_m XのF_n Yとの球面上のテンソル積とF_(m+n)(X⊗Y)とのスペクトルの同型を構成した。
ここでX⊗Yは基点付き単体的集合の通常のsmashである。
両方の入力の射に関する自然性を証明し、二変数関手間の自然同型へまとめた。
m・nには正の条件を要求せず、零次も同じ構成で扱う。
集約FoundationsとスペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

自由スペクトルF_m XとF_n Yの積の和次数表示を、スペクトルの自然同型として利用できる。
自由加群を左因子とする一般の比較、結合子・対称性・整合性の証明と
スペクトル圏のモノイダル構造の登録は今後進める。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンクとgit diff --checkも確認した。
集約SerrePositivity.Spectra.Foundationsのビルドは1982ジョブで成功した。
公理監査は129モジュール・1418宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 57. 実施記録：球面上のテンソル積の交換自然同型（2026-10-14）

### 釣り合い商の交換と関係式

[BalancedTensorSymmetry](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorSymmetry.lean)で、
対称モノイダル圏におけるE⊗_M FとF⊗_M Eの交換同型を構成した。
三因子E・M・Fを逆順へ移す射を定義し、braidingの自然性とhexagonによって別の表示と比較した。
この射を使い、基礎圏の交換が釣り合い関係式の左辺を右辺へ、右辺を左辺へ移すことを証明した。
係数の可換性は基礎対象の商とその交換の構成では要求しない。

基礎圏の交換と反対順の標準射の合成は釣り合い条件を満たすため、商からの射へ降ろせる。
標準射上の交換の公式を証明し、基礎圏の対称性と商からの射の決定性を使って
二回の交換が恒等射になることを証明した。
これにより基礎対象の交換同型を得た。

### 加群作用と単位比較との両立

可換係数と左テンソルの余等化子保存の仮定の下で、商上の交換射が加群作用と両立することを証明した。
反対順の釣り合い関係式を介して第一因子の作用を第二因子へ移し、
braidingのhexagonと二回の交換の恒等性を使って商の作用と比較した。
順逆の交換射を加群の射へ持ち上げ、加群としての交換同型を構成した。

両方の加群の射に関する自然性を基礎圏のbraidingの自然性から証明し、
二変数関手と入力を交換した関手との自然同型へまとめた。
正則加群との交換を左単位同型へ続けると右単位同型になることも証明した。

### 対称スペクトルへの特殊化

[TensorSymmetry](../SerrePositivity/Spectra/SymmetricSpectrum/TensorSymmetry.lean)で、
sphereTensor E FとsphereTensor F Eのスペクトルの交換同型へ特殊化した。
標準射上のbraidingの公式、逆射が反対順の交換射であること、両方の射に関する自然性、
二回の交換の恒等性と二変数の自然同型を公開した。
球面との交換を左単位比較へ続けると右単位比較になることも特殊化した。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

球面上のテンソル積は左右の単位自然同型と交換自然同型を備える。
結合同型の構成とpentagon・triangle・hexagonの整合性を証明し、
スペクトル圏の対称モノイダル構造を登録する作業が残る。
自由加群を左因子とする一般の比較も今後公開する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

新しい二つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
集約SerrePositivity.Spectra.Foundationsのビルドは1984ジョブで成功した。
公理監査は131モジュール・1444宣言で成功し、標準公理のみでsorry依存なしを確認した。

## 58. 実施記録：球面上のテンソル積の結合自然同型（2026-10-14）

### テンソル後の商への降下と三因子の標準射

[BalancedTensorIterated](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorIterated.lean)で、
釣り合い商を左または右にテンソルした対象からの射を、対応する関係式を満たす射から構成した。
対応するテンソル関手の余等化子保存を仮定し、保存比較の同型と余等化子の降下射を用いる。
左右の標準射との因子化の公式と、標準射のエピ性を証明した。

可換係数と左テンソルの余等化子保存の下で、標準射を加群の射として構成した。
商の右側へ移した作用を、第二因子の右作用と標準射で計算する公式も証明した。
左結合・右結合の三重釣り合いテンソル積への標準射を構成し、三つの加群の射との両立を証明した。
右結合の標準射は左テンソルの保存から、左結合の標準射は右テンソルの保存も使ってエピ射となる。

### 二段の商への結合子の降下

[BalancedTensorAssociator](../SerrePositivity/CategoryTheory/Monoidal/BalancedTensorAssociator.lean)で、
左結合・右結合の反復釣り合いテンソル積の基礎対象の比較を構成した。
右結合の標準射の前に基礎圏の結合子を付け、左側の二因子の関係式を満たすことを証明した。
第一段階の降下は残る二因子の関係式も満たすため、二段目の商へ降ろせる。
結合子の逆と左結合の標準射から、逆方向も二段の商へ降ろした。

関係式の確認には、商の左右の作用と標準射の両立、および基礎圏のモノイダル整合性を使った。
順逆の比較は三因子の標準射上で結合子とその逆に一致する。
標準射のエピ性から両方向の合成が恒等射となることを証明し、基礎対象の結合同型を構成した。

三因子の標準射と結合子を加群の射として構成し、結合比較の順方向の作用との両立を証明した。
この際も左テンソルした三因子の標準射のエピ性を使う。
線形な同型の逆射の一般論から加群の結合同型へ持ち上げた。
三つの加群の射に関する自然性を標準射上で証明し、三変数の関手間の自然同型へまとめた。

### 対称スペクトルへの特殊化

[TensorAssociator](../SerrePositivity/Spectra/SymmetricSpectrum/TensorAssociator.lean)で、
球面上のテンソル積の結合同型へ特殊化した。
基礎対称列のconvolutionの閉構造から左右の余等化子保存を供給する。
左右の三因子の標準射とエピ性、標準射上の結合子の順逆の公式、
三つのスペクトルの射に関する自然性と三変数の自然同型を公開した。
集約Foundationsと共通層・スペクトルのREADMEに新しい入口を追加した。

### 到達点と次の範囲

球面上のテンソル積は左右の単位・交換・結合の自然同型を備える。
pentagon・triangle・hexagonの整合性を証明して対称モノイダル構造を登録する作業が残る。
自由加群を左因子とする一般の比較も今後公開する。
弱同値・モデル構造・導来演算・安定ホモトピー群は引き続き未実装である。
共有ルートimport・依存設定・並行作業の可換環・CLMST関連ファイルは変更していない。
定理3.1・補題4.6の二つの降下入力は未変更である。

### 検証

新しい三つのLeanソースの行長・末尾空白・未完了の証明用マーカーを確認した。
ドキュメントのローカルリンク、共通層からのimport方向とgit diff --checkも確認した。
集約SerrePositivity.Spectra.Foundationsのビルドは1987ジョブで成功した。
公理監査は134モジュール・1510宣言で成功し、標準公理のみでsorry依存なしを確認した。
