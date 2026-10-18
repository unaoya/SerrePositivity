# dg nerve の規約と計算

## 概要と参照先

任意の `A : Type u`、`[CommRing A]`、`D : Type v`、`[DGCategory A D]` を扱う。
追加の有界性・平坦性・標数の仮定は置かない。
正本は [計画](../../formalization-plans/dg-nerve.md)。この文書の N0 は紙の計算であり、
Lean での dg nerve の存在やホーン充填の証明を意味しない。
N0〜N6 の必須項目は完了。任意の dg 圏の dg nerve と quasicategory instance、
ホモトピー圏と H⁰ の圏同値、右 pinched Hom の単体的 A 加群・直接の線形 Kan 充填・π₀ 比較、
dg 関手と厳密自然変換によるホモトピー、具体例と最終公理監査を公開済み。
以下の途中段階の記録は保存時点の履歴を表す。最新の検証は末尾の N6 を参照。

原典は [Higher Algebra](https://www.math.ias.edu/~lurie/papers/HA.pdf)
Construction 1.3.1.6、Proposition 1.3.1.10、Remark 1.3.1.12 と、
[Kerodon §2.5.3](https://kerodon.net/tag/00PK)、
[§4.6.5](https://kerodon.net/tag/01KW)。以下の展開計算は本リポジトリの規約で行う。

## 規約：次数・順序・符号

`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`、微分 `δ` は次数 +1。
`compose A g f h` は通常順の `g ∘ f` で、`h` は次数の和の等式。
`differential_compose` は

```
δ(g ∘ f) = δg ∘ f + (-1)^deg(g) g ∘ δf
```

を与える。HA の chain 次数を負に読み替え、HA の `f_I` は符号を変えずに用いる。
Kerodon Construction 2.5.3.1 は括弧の順序が逆である。
同じ Hom 複体の微分で比較する場合、Kerodon の成分は
`f_I^K = (-1)^(|I|-2) f_I^HA` とする。この再符号化は辺と単位を固定し、
三角形の成分を負にする。原典間の式をそのまま混在させない。

## N0.1：単体の方程式

`I = {i₀ < ⋯ < iᵣ}`、`r ≥ 1` と置く。`f_I` の次数は `1-r = 2-|I|`。
`a=min I`、`b=max I`、`ε(I,j)=(-1)^#{k∈I | j<k}` と書く。
`I≤j={k∈I | k≤j}`、`I≥j={k∈I | j≤k}` として

```
F_I = Σ_{j∈I, a<j<b} ε(I,j) (f_{I\{j}} - f_{I≥j} ∘ f_{I≤j}),
δ f_I = F_I.
```

右辺の各項は次数 `3-|I|`。内部点を消すので両端は変わらない。
合成項も `(2-|I≥j|)+(2-|I≤j|)=3-|I|` である。
辺では和が空で `δ f_ab=0`。Lean では符号を
`((I.filter (fun k => j < k)).card : ℤ).negOnePow` で表す。

2 単体では内部点 1 の符号が −1 なので

```
δ f₀₁₂ = f₁₂ ∘ f₀₁ - f₀₂.
```

3 単体では内部点 1, 2 の符号がそれぞれ +1, −1 なので

```
δ f₀₁₂₃ = -f₀₁₃ + f₂₃ ∘ f₀₁₂ + f₀₂₃ - f₁₂₃ ∘ f₀₁.
```

この右辺の微分を展開すると、辺が閉じていることから

```
-(f₁₃∘f₀₁-f₀₃) + f₂₃∘(f₁₂∘f₀₁-f₀₂)
+ (f₂₃∘f₀₂-f₀₃) - (f₂₃∘f₁₂-f₁₃)∘f₀₁ = 0.
```

最後は結合律と加法群の相殺。ここでは後から作用する辺の次数が 0 なので Leibniz の符号は +1。
負次数の符号も検査するため、4 単体では

```
F₀₁₂₃₄ = -f₀₂₃₄ + f₁₂₃₄∘f₀₁ + f₀₁₃₄
          -f₂₃₄∘f₀₁₂ - f₀₁₂₄ + f₃₄∘f₀₁₂₃.
δ(-f₂₃₄∘f₀₁₂) = -(f₃₄∘f₂₃-f₂₄)∘f₀₁₂
                      + f₂₃₄∘(f₁₂∘f₀₁-f₀₂).
```

他の五項も上の 3 単体の式で微分すると全項が相殺する。
特に最後の + は `deg(f₂₃₄)=-1` から生じ、微分 +1 の規約と整合する。
計画 §1.1 の符号の訂正は不要。

## N0.2：内部ホーンの解と整合性

`V={0,…,n}`、`0<i<n`、`M=V\{i}` とする。ホーンから未指定なのは `f_V,f_M` のみ。
`f_V=0` と置き、頂点全体の式を解くと

```
f_M = Σ_{0<j<n} (-1)^(j-i) f_{V≥j}∘f_{V≤j}
      - Σ_{0<j<n, j≠i} (-1)^(j-i) f_{V\{j}}.
```

`ε(V,i)ε(V,j)=(-1)^(j-i)` を使った。負の指数も整数の符号として解釈する。
両端が残るので `f_M` と右辺はすべて `Hom^(2-n)(X₀,Xₙ)` に属する。
切断 `V≤j,V≥j` は M にならないため、右辺には既知データしか現れない。
`n=2` では `f₀₂=f₁₂∘f₀₁` となる。

欠けた面自身の式を確かめるため、任意の成分族に対し残差 `R_I=δf_I-F_I` を置く。
必要な有限代数恒等式は

```
δF_I = Σ_{a<j<b} ε(I,j) R_{I\{j}}
       - Σ_{a<j<b} ε(I,j)
           (R_{I≥j}∘f_{I≤j} + (-1)^(2-|I≥j|) f_{I≥j}∘R_{I≤j}).
```

導出では各微分を `δf_K=F_K+R_K` に置き換える。残差のない項は次の三種類に分ける。

1. 二つの内部点を消す項。異なる j,k の削除順を交換すると
   `ε(I,j)ε(I\{j},k)=-ε(I,k)ε(I\{k},j)` なので相殺する。
2. 一点の削除と一度の切断を行う項。削除点が切断点の左右のどちらにあるかで組を作る。
   右側の因子を通る微分の符号 `(-1)^(2-|I≥j|)` を含めると係数は互いに逆になる。
3. 二度切断する項。同じ三部分への分割の二通りを組にし、結合律で同じ射に直す。
   Leibniz の符号と切断の符号の積は互いに逆になる。

これで表示した残差の項だけが残る。I=V では全ての真部分集合の残差が既知の式により 0 で、
例外は削除項の `R_M` だけ。既に `F_V=0` としたので
`0=δF_V=ε(V,i)R_M`、符号は可逆だから `R_M=0`。
`δR_V=-δF_V` は `δ²=0` による同じ議論である。
これはホーンのデータ回収・貼合せの組合せ論とは別に Lean で証明すべき恒等式である。

## N0.3：右 pinched 写像空間

右 pinched Hom の n 単体は `σ:Δ[n+1]→X` で、先頭の **n+1 個の頂点が張る面**
`Δ[{0,…,n}]` 全体が x に定値、最終頂点 n+1 が y となるもの。
「先頭の面が退化」とはこの面全体の条件を意味する。
複数の余次元 1 の面をすべて x に定値にする条件ではない。

dg nerve では最終頂点を ∞ と書き、空でない `J⊆{0,…,n}` に対し
`f_J := f_{J∪{∞}} ∈ Hom^(1-|J|)(x,y)`。
先頭の面に入る辺は id、高次成分は 0 なので、非線形項は次のように線形化する。
`J={j₀<⋯<jᵣ}` とすると

```
|J|=1 : δf_J=0,
|J|≥2 : δf_J = Σ_{a=0}^r (-1)^(r-a+1) f_{J\{j_a}}.
```

a≥1 の項は通常の削除項で、∞ の一個分を符号の指数に加える。
a=0 の項は j₁ での切断の合成項から現れる。
左因子が先頭の退化辺 id で、`f_{J\{j₀}}∘id=f_{J\{j₀}}`。
他の切断では先頭の高次成分が 0 なので寄与しない。
例えば `δf₀₁=f₀-f₁`、`δf₀₁₂=-f₁₂+f₀₂-f₀₁`。

この線形作用素を L とすると `L²=0` は二重削除の順序交換による符号相殺。
右辺に微分を適用し、真部分集合の式を代入すると 0 になる。
全 n 次ホーン（n≥1、0≤i≤n）について `V={0,…,n}`、`M=V\{i}`、
`e_a=(-1)^(n-a+1)` とし、

```
f_V=0,
f_M = - Σ_{a≠i} e_i e_a f_{V\{a}}
```

と置く。`f_M` の次数は `1-n`。頂点全体の式はこの定義で成り立つ。
その微分と二重削除の相殺から `δf_M=Lf_M` も従う。
n=1 では欠けた頂点を既知の頂点と同じ閉元に取り、次数 −1 の辺を 0 とする。
特に i=0 の外部ホーンでも `f_{V\{min V}}` を同様に解ける。
これは dg nerve 本体の外部ホーンが埋まるという主張ではない。

## 実装の使われ方と現在の範囲

N1 はこの方程式を満たす単体とその引き戻しを、N2 は残差恒等式とホーン貼合せを形式化する。
N4 は最後の線形方程式と全ホーンの充填を形式化する。
N0 時点の公開 Lean 宣言はなく、公理監査は既存の合成・単位・結合則の再検査のみ。
N1〜N6 の定義・定理は未完了である。

## N1 の途中の実装（2026-10-17）

`DGNerve/Simplex.lean` に単体データと HA の方程式、零単体と対象の同値を置く。
`DGNerve/LowDimensional.lean` は一単体と閉次数零元の同値、既存閉零圏への辺の写像、
二単体の微分の式を証明する。`DGNerve/Index.lean` は端点・濃度と像の補題。
`DGNerve/Reindex.lean` は**データ部分**の引き戻しと恒等・合成の法則を与える。

引き戻しが方程式を保存することと `dgNerve : SSet` は未構成。
二単体の特徴づけも逆構成はまだない。N1 完了とは数えない。
全 46 件の明示的公開宣言を `scripts/audit_dg_nerve.lean` で監査し、標準 3 公理のみ。
公開宣言の全ての型・前提・検証記録は計画 §5 の N1a 保存に記録した。

`DGNerve/PullbackEquation.lean` は J 上単射の場合の成分・内部点の項・有限和の移送と
方程式の保存を証明する。全域単射な単調写像に沿う単体は `Simplex.pullbackOfInjective`。
二点集合では任意の単調写像について方程式が保存される。
非単射で三点以上の集合については相殺が未証明で、一般の退化写像はまだ構成していない。
N1b までの明示的公開宣言は累計 56 件、全て標準 3 公理のみ。型と前提は計画 §5 を参照。

## N1c：単体的集合の構成（2026-10-17）

現在は `dgNerve A D : SSet.{max u v}` を `DGNerve/Basic.lean` に構成済み。
前述の N1a・N1b の「一般の退化写像は未構成」は、それぞれの保存時点の記録である。

`DegeneracyIndex.lean` と `DegeneracyEquation.lean` は基本退化について、内部の二項の相殺と
端点での単位則を検証する。`Pullback.lean` は非単射写像の基本退化経由の分解と次元の帰納法で
任意の単調写像の方程式の保存を証明する。データ部分は最初に指定した三分岐に定義上一致する。
`Algebra.lean` は零の合成と、次数・対象の等式で移送した単位則の補題を提供する。

集約入口は `SerrePositivity.InfinityCategories.DGNerve`。
零・一単体の同値と面・退化の頂点の計算を公開した。
二単体の逆構成、面・退化の斉次成分の計算補題、共有ルートの import は引き続き未完了。
quasicategory 性と N2〜N6 も未完了で、N1 全体の完了とは数えない。
累計 93 件の明示的公開宣言は全て標準 3 公理のみ。全ての型と前提は計画 §5 の N1c に記録した。

## N1 完了（2026-10-17）

`Triangle.lean` は三つの閉零射と `δh=f₁₂∘f₀₁-f₀₂` を満たす次数 −1 の射から二単体を構成し、
`dgNerve.triangleEquiv` で逆向きの評価と合わせた同値を与える。
`Computations.lean` は面の成分と、退化の単射・潰れた辺の単位・高次の零の全分岐を公開する。
集約入口と共有ルートの import を含め、N1 の要求を満たした。
N1a〜N1c に記録した未完了項目はそれぞれの保存時点のもので、N1d で解消した。
対象入口とルートはビルド成功。累計 110 件の明示的公開宣言は全て標準 3 公理のみ。
N2〜N6 は未完了で、quasicategory 性や写像空間の Kan 性はまだ証明していない。

## N2a：ホーンの既知成分と符号計算（2026-10-17、N2 は未完了）

`HornIndex.lean` は、全体集合 V と欠けた面 V\\{i} 以外の I が利用可能な面に含まれることを示す。
`HornFaces.lean` は同じホーン単体の制限をどの利用可能な面から読んでも一致することを示す。
`HornData.lean` は共通の対象族 `vertexObj` と、その面を選んで値を回収する `recoverHom` を構成する。
成分の回収結果が選択によらず各面と一致することは、まだ証明していない。

`Signs.lean` は ε(I,j)=(-1)^{#{k∈I:j<k}} として
`ε(I,j)ε(I\\{j},k)=-ε(I,k)ε(I\\{k},j)` を証明し、二重削除の和を対合で相殺する。
二重切断の係数についても、右側成分の次数による Leibniz の符号を含めて反転することを証明した。
`Algebra.lean` に合成の加法・差・符号スカラーの補題を追加した。

`Residual.lean` は R_I=δf_I-F_I、`R_I=0 ↔ δf_I=F_I`、`δR_I=-δF_I` を証明する。
ここで F_I は単体の方程式の右辺。残差を真部分集合の残差で表す主恒等式は未証明。
`HornEquation.lean` は内部点集合 K と i∈K に対して

```
missingComponent = composed(i) - ε(I,i) Σ_{j∈K\\{i}} ε(I,j)(deleted(j)-composed(j))
```

が最上位方程式の右辺を零にすることと、N0 の解の式との一致を証明する。
これは任意の加法可換群の有限和の定理であり、まだ実際の単体データへの組込みはない。
欠けた面自身の方程式、ホーンの貼合せ、`Quasicategory` instance は未構成。
公開宣言の型・前提・検証結果は計画 §5 の N2a に記録する。N3〜N6 も引き続き未完了。

## N2b：回収成分の整合性と既知方程式（2026-10-17、N2 は未完了）

`HornComponents.lean` の `HornData.face_hom_heq` は、二つの利用可能な面の部分集合が大域で
同じ像を持つとき、その成分が異種等号で一致することを示す。
`HornData.recoverHom_heq_face` により、回収した値は任意の利用可能な面の対応成分と一致する。
補助的な有限順序による列挙は比較の証明にのみ用い、単体の表現と添字は変更していない。

`HornPartial.lean` の `knownData` は既知成分を回収し、未知の全体集合と欠けた面の成分には
仮に零を入れたデータ。`knownData_pullback_face` は全ての利用可能な面への制限が元の面の
データに等しいことを示す。`knownData_equation` は `I ≠ univ` と `I ≠ univ.erase i` の下で
`δf_I=F_I` を示す。これにより、N2a に残っていた回収の整合性と既知方程式の保存は解消した。

このデータはまだ充填単体ではない。欠けた面の成分を最上位方程式の解へ置き換えること、
その変更後も既知方程式が保たれること、主残差恒等式による欠けた面自身の方程式、
貼合せと `Quasicategory` instance が残る。N2 と N3〜N6 は引き続き未完了。

## N2c：欠けた成分の補正と最上位方程式（2026-10-17、N2 は未完了）

`Replace.lean` は一集合 M の成分だけを置き換える `SimplexData.replace` を与える。
M を含まない像への制限と、M 自身の方程式の右辺は置換で変わらない。
`EquationTransfer.lean` は各既知の面に一致する任意のデータが既知方程式を満たすことを証明し、
欠けた面の成分を任意に置き換えた場合にも適用する。

`TopCorrection.lean` は、I の内部点 i に対して M=I\\{i} の成分を f'_M に置き換えると

```
F'_I - F_I = ε(I,i) (f'_M - f_M)
```

となることを、有限和のうち i の削除項だけが変わることから示す。ここで F_I は方程式の右辺。
`correctingHom` は `f'_M=f_M-ε(I,i)F_I` とし、`rhs_solveTop` は `F'_I=0` を証明する。
既知データでは f_M=0 なので、これは N0 の最上位方程式の解と同じ補正である。

`HornFilling.lean` の `HornData.fillerData` はこの補正を内部ホーンの既知データに適用する。
既知の面との一致、既知の全方程式、最上位成分の零、最上位方程式を証明済み。
残るのは欠けた面 M 自身の方程式である。

`fillerOfMissingEquation` と `extensionOfMissingEquation` は、**その欠けた面の方程式を
明示的な前提として**単体とホーン写像の延長を構成する。貼合せの証明には `horn.hom_ext` を用いる。
この前提を満たす証明と主残差恒等式は未構成であり、無条件の内部ホーン充填と
`Quasicategory` instance は未完了。N2 の完成とは数えず、N3〜N6 も未完了。

## N2d：残差展開と有限和の相殺（2026-10-17、N2 は未完了）

`LinearBoundary.lean` は内部点集合 K と、適切な端点・次数・濃度の場合に元の `hom` を評価し、
それ以外を零とする補助評価 `homOrZero` を定義する。単体の表現は変更していない。
線形な削除部分 L_I=Σ_{j∈K} ε(I,j) f_{I\\{j}} について、
`linearBoundary_squared` が実際の成分を使う二重削除和の零を証明する。

`BoundaryDecomposition.lean` は、切断合成部分 Q_I と元の右辺について `F_I=L_I-Q_I` を示し、
F_I の微分と切断合成の Leibniz 展開を証明する。
`CompositionCancellation.lean` は、共通の値にそろえた削除・切断の混合二重和の相殺、
二重切断の係数の二重和の相殺、通常順合成の結合律を用いた三重合成の二項の相殺を証明する。
実際の入れ子の切断集合と次数を、この共通の値へそろえる接続はまだ完了していない。

`ResidualExpansion.lean` は R_I=δf_I-F_I とし、各内部点 j で、削除を E、左右切断を L,R、
右側成分の次数を q と書くと

```
residualContribution_j = ε(I,j) (R_E - R_R∘f_L - (-1)^q f_R∘R_L)
rhsContribution_j      = ε(I,j) (F_E - F_R∘f_L - (-1)^q f_R∘F_L)
δF_I = Σ_j residualContribution_j + Σ_j rhsContribution_j
```

を証明する。主残差恒等式には、実際の `Σ_j rhsContribution_j=0` の証明がまだ必要。
その接続、欠けた面自身の方程式、無条件の内部ホーン充填と `Quasicategory` instance が残る。
N2 および N3〜N6 は引き続き未完了。

## N2 完了（2026-10-17）

`CutErasure.lean` と `CutBoundary.lean` は、削除後の切断と切断後の削除の集合・次数・合成値を
そろえる。`MixedBoundary.lean` は実際の混合項全体の零を証明する。
`NestedCut.lean` は二重切断の中間の集合と次数を同定し、通常順合成の結合律を適用する。
`CubicBoundary.lean` は実際の三重合成項の総和の零を証明する。

これらと二重削除の零から、`Bianchi.lean` は実際の `Σ rhsContribution=0` を証明し、
主残差恒等式 `δF_I=Σ residualContribution` を得る。
`HornResidual.lean` はこれを充填候補の全体集合に適用する。左辺は `δ²f_V=0`、
既知の削除面と左右切断の残差は零なので `ε(V,i)R_{V\\{i}}=0` が残り、欠けた面の方程式が従う。
これで N2d までの未証明部分は解消した。

`Quasicategory.lean` の `dgNerve.filler` は追加の方程式の前提なしに充填単体を構成する。
`filler_face` は全ての既知の面との一致、`hornFilling` はホーン写像の延長を証明する。
`dgNerve.instQuasicategory` は `Quasicategory (dgNerve A D)` を公開する。
前提は任意の可換環 A と dg 圏 D のみ。ホーンの充填では内部点の二不等式を要求する。
有界性・平坦性・体・標数の追加仮定はない。

N2 の全体が完了し、N3（H⁰ との比較）・N5（関手性）・N4（右 pinched 写像空間）・N6 は未完了。
公開宣言の正確な型・前提・ビルドと公理監査の記録は計画 §5 の N2e を参照。

## N3a：端点付きの辺と境界関係（2026-10-18、N3 は未完了）

`TruncatedEdges.lean` は `twoTruncation=(SSet.truncation 2).obj (dgNerve A D)` を使い、
固定した零単体 x,y の間の辺と、その対象 x.obj 0,y.obj 0 間の閉零元の同値を構成する。
端点の面の等式による対象の移送と、両向きの逆則も検証済み。
Mathlib の `Quasicategory₂` instance がこの切断に自動推論されることを監査で確認する。

`TruncatedTriangles.lean` は二単体の三つの面を計算し、端点付きの合成構造について

```
Nonempty (CompStruct f g h) ↔ ∃ t : Hom^{-1}(x,z), δt = g∘f-h
```

を証明する。ここで辺はその閉零成分として読んでいる。
`EdgeHomotopy.lean` は退化した恒等辺を dg 単位に同定し、
`HomotopicL f g` と `HomotopicR f g` を、いずれも `δt=f-g` の原始元の存在で特徴づける。
さらに既存の閉零圏の射との同値 `edgeClosedEquiv` を構成し、
両ホモトピーが `boundaryRelation A D (edgeClosed f) (edgeClosed g)` と同値であることを証明した。

既存の H⁰ を変更せずに辺のホモトピー関係まで比較した段階であり、圏同値は未構成。
合成の対応、明示的な零ホモトピーの合成構造、商上の両向きの関手と逆同型が残る。
N3 全体および N4〜N6 は未完了。

## N3 完了（2026-10-18）

`ClosedComposition.lean` は既存の閉零圏の恒等・合成の評価を dg 単位・通常順合成と同定する。
`strictComp` は実際の閉零合成から作る対角辺、`strictCompStruct` はその辺を対角に持つ
**零ホモトピー**の三角形。`comp_homotopic_strictComp` は `CompStruct.comp_unique` を使い、
Mathlib が選ぶ辺の合成が実際の合成とホモトピックであることを示す。

`HomotopyCategory.lean` の namespace は `DGNerve.HomotopyComparison`。
`toH0` は二次切断のホモトピー圏から既存の H⁰ への関手で、辺の類をその閉零射の境界類に送る。
恒等射・合成の保存を証明し、境界関係の比較から忠実性、閉零代表元から充満性、
任意の dg 対象の定値零単体から本質的全射性を証明した。

`equivalence` は

```
SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (dgNerve A D))
  ≌ DifferentialGraded.HomotopyCategory A D
```

を与える。`fromH0` は逆関手、`unitIso` と `counitIso` は両方向の往復の自然同型。
逆関手と自然同型は、充満・忠実・本質的全射な関手からの Mathlib の圏同値の構成を使う。
任意の可換環 A と任意の dg 圏 D のみを前提とし、追加の方程式や有界性は仮定しない。
これで N3a の未完了項目は解消した。N4〜N6 は未完了。

## N5a：dg 関手の写像と充満部分圏（2026-10-18、N5 は未完了）

`FunctorMapping.lean` は dg 関手で全対象と全斉次成分を写し、微分・通常順合成・単位と
符号付き有限和の保存から単体の方程式を保つことを示す。
`Functor.lean` は任意の単調写像による引き戻しとの可換性を、単射・潰れた辺の単位・
それ以外の零の三分岐で証明する。

`dgNerve.map (F : DGFunctor A D E) : dgNerve A D ⟶ dgNerve A E`、
`dgNerve.map_id`、`dgNerve.map_comp` を公開した。
単体データの写像は D,E の対象宇宙を別々に扱う。
単体的写像は Mathlib の `nerve` の写像と同様に、D,E を共通の対象宇宙に置いている。

`FullSubcategory.lean` は、全頂点の対象が P を満たす単体による部分複体 `fullOnObjects` を定義する。
各 Hom 複体を変えずに単体を充満 dg 部分圏へ持ち上げる `liftToFull` と往復の計算を構成し、
`range_inclusion` で包含の dg nerve の像が `fullOnObjects` に等しいことを証明した。

厳密 dg 自然変換から単体的ホモトピーを作る部分は未構成。
N5 全体の完了とは数えない。N4 と N6 も未完了。

## N5 完了：厳密 dg 自然変換のホモトピー（2026-10-18）

`DGNerve.StrictNatTrans F G` は各対象での閉次数零成分 η と、全斉次射に対する
`η_y ∘ F(f) = G(f) ∘ η_x` の厳密自然性を持つ。成分の可逆性は要求しない。
`StrictNatTrans.lean` の二相間の写像は F 内・G 内ではその関手の斉次写像、
F から G をまたぐ場合は `η_y ∘ F(f)` を取り、微分・合成・単位・符号付き有限和を保つ。

`NatTransSimplex.lean` は任意の単体と単調写像 β : Fin(n+1) →o Fin 2 を使い、
各頂点を相に従って F/G へ送り、全有限部分集合の成分を二相間の写像で送る。
全単体方程式と、任意の引き戻しとの可換性を証明した。
`NatTrans.lean` の `StrictNatTrans.homotopyMap` はこれを

```
dgNerve A D ⊗ Δ[1] ⟶ dgNerve A E
```

にまとめ、`homotopyMap_zero` と `homotopyMap_one` が端点をそれぞれ
`dgNerve.map F` と `dgNerve.map G` に同定する。
`StrictNatTrans.homotopy` はこの二写像の Mathlib の `SSet.Homotopy`。

任意の可換環 A と dg 圏 D,E に対する構成であり、方程式の追加仮定はない。
これで N5a の未完了項目が解消し N5 は完了。N4 と N6 は未完了。
公開宣言 335 件と既存 5 則の公理監査は標準三公理の範囲内である。

## N4a：一般の右 pinched Hom（2026-10-18、N4 は未完了）

`PinchedHom/Basic.lean` の `InfinityCategories.pinchedHom x y` は任意の単体的集合 X に対して定義する。
n 単体は X の (n+1) 単体で、先頭の n+1 頂点が張る面全体が x に定値、最終頂点が y となるもの。
`PinchedHom/Index.lean` は [m] → [n] を最終頂点を固定して [m+1] → [n+1] へ延長する。
先頭の面と最終点の可換性および延長の恒等・合成則から、全ての面・退化を持つ SSet を構成した。
quasicategory や Kan 性はこの一般の定義に仮定していない。

`PinchedHom/Edges.lean` の `vertexEquiv` は、この空間の零単体と X の端点付き辺の同値。
`DGNerve/PinchedHom.lean` の `DGNerve.pinchedHom A D x y` は dg 圏の二対象間への適用で、
`DGNerve.PinchedHom.vertexCycleEquiv` はその零単体を `zeroCycles (homObject A D x y)` に同定する。
任意の可換環と dg 圏で成立し、宇宙は `max u v`。

全次数の線形族との比較、各次数の A 加群構造と単体的写像の線形性、
直接の線形ホーン充填による Kan 性、π₀ と H⁰ の射の同定は未完了。
N4 全体の完了とは数えない。N6 も未完了。
今回までの公開宣言 361 件と既存 5 則は標準三公理の範囲で監査済み。

## N4b：線形模型と実際の単体からの成分回収（2026-10-18、N4 は未完了）

`DGNerve/PinchedLinear.lean` の `PinchedHom.LinearData A x y n` は、全ての非空 J に
次数 `1−|J|` の射を割り当てる。集合・次数・その条件を一つの添字にまとめ、
`component` で J と指定次数から評価する。元の `Simplex.hom` の設計は変えていない。
右辺 `LinearData.rhs` は N0.3 通り、二点以上で
`Σ j:J, (#{t∈J:j<t}+1).negOnePow • f_(J.erase j)`、一点では零。

この右辺の零・加法・A スカラー倍の保存から、全ての `δf_J=rhs f J` の解を部分加群
`linearSubmodule A x y n` にまとめた。その台型 `LinearSimplex` は各 n で A 加群となり、
全単体方程式の取り出しと一点成分の閉性を証明した。
`PinchedLinearReindex.lean` は単射なら像、非単射なら零という成分族の引き戻しを A 線形写像とし、
両分岐の計算と恒等・合成の法則を証明する。解への制限はまだ未構成。

`PinchedIndex.lean` は J に最終点を加える `withLast` の濃度・端点を計算する。
`PinchedComponents.lean` は実際の右 pinched 単体の先頭対象が全て x、最終対象が y と証明し、
`toLinearData` で最終点を含む全成分を回収する。対象の移送と元の成分の一致も異種等号で証明済み。

回収した族の線形方程式、線形解からの単体の再構成、両逆則、全次数の実際の写像空間の加群構造、
面・退化の線形性、直接の線形ホーン充填と Kan 性、π₀ 比較は未完了。
線形模型の定義だけで N4 全体を完了とは数えない。N6 も未完了。
全公開宣言 387 件と既存 5 則の監査は標準三公理の範囲内。

## N4c：先頭面と切断の線形化の計算（2026-10-18、N4 は未完了）

`PinchedFront.lean` は、実際の右 pinched 単体の先頭面の辺が dg 単位、三点以上の成分が零であることを、
定値面の条件から証明する。`front_hom_heq` は元の先頭埋め込みの像の成分と定値単体の成分を比較し、
`front_hom_unit` と `front_hom_zero` が全成分を評価する。
`compose_front_hom_unit` と `compose_front_hom_zero` は、その成分を先に作用させる合成を計算する。

`PinchedCuts.lean` は `withLast J` の削除・左右切断を J の式に戻し、
符号の指数が `#{t∈J:j<t}+1` であると示す。
`PinchedSecond.lean` は二番目の点での左切断が最初の二点、右切断が最小点の削除となること、
二点の左切断が起こる内部点は二番目の点だけであることを証明する。
さらに二番目と最小点の削除係数が逆符号となるため、合成項の負号が最初の削除係数になる。

これらは任意の可換環と dg 圏で成立する有限集合・単位・零の計算であり、追加の単体方程式は仮定しない。
全有限和の同定による線形方程式の導出、逆構成、全次数の同値と実際の加群構造、
直接の線形ホーン充填・Kan 性・π₀ 比較は未完了。N6 も未完了。
全公開宣言 409 件と既存 5 則は標準三公理の範囲で監査済み。

## N4d：各内部点の項の線形化（2026-10-18、N4 は未完了）

`PinchedFront.lean` の像の集合に対する成分比較は、依存する証明引数を保持したまま先頭面の単位・零を適用する。
`PinchedTerms.lean` は左右切断・切断合成・一点削除の成分を元の term の式から取り出す。
二番目以外の内部点で切断合成が零、二番目では右切断成分に一致し、
その右切断成分は `toLinearData s` の最小点を消した成分になると証明した。
各内部点の削除成分も回収した族の対応する成分に一致する。

`PinchedTermLinear.lean` の `term_heq_linear` は、実際の右 pinched 単体 s からの回収族 f に対して、
二点以上の J と min J<j、j∈J の全ての項を

```
(#{t∈J:j<t}+1).negOnePow • (f_(J.erase j) - if j=second J then f_(J.erase (min J)) else 0)
```

に同定する。対象の移送は異種等号で記述し、次数は全て k+1、k=1−|J|。
任意の可換環と dg 圏で成立し、追加の高次方程式は仮定しない。

全有限和の同定と線形方程式、逆構成、全次数の同値と実際の加群構造、
直接の線形ホーン充填・Kan 性・π₀ 比較、N6 は未完了。
全公開宣言 425 件と既存 5 則は標準三公理の範囲で監査済み。

## N4e：全右辺の線形化と解の模型への順写像（2026-10-18、N4 は未完了）

`PinchedSum.lean` は `Option J ≃ withLast J` によって和を最終点の項と先頭集合の和に分ける。
`PinchedSumLinear.lean` の `sum_linear_terms` は二番目の点の補正項を最小点の項へ戻し、
内部点の線形表示の和が全削除和に一致すると示す。任意の加法可換群で成立する有限の計算である。

`PinchedRhs.lean` の `rhs_heq_linear` は元の単体の右辺を、回収族の `LinearData.rhs` に同定する。
`toLinearData_equation` は元の単体方程式から回収族の全線形方程式を導く。
二点以上の J には全右辺の同定を、一点の J には元の辺の閉性と零の線形右辺を使う。
したがって n=0 を含む全次数、全非空 J を扱い、線形方程式を仮定に追加していない。

`PinchedHom.toLinearSimplex` は任意の可換環 A、dg 圏 D、対象 x,y に対して

```
(DGNerve.pinchedHom A D x y) _⦋n⦌ → PinchedHom.LinearSimplex A x y n
```

を与える。N4b のデータ回収が解の部分加群へ持ち上がった。
逆構成・両逆則、全次数の同値と実際の加群構造、面・退化の線形性、
直接の線形ホーン充填・Kan 性・π₀ 比較、N6 は未完了。
全公開宣言 435 件と既存 5 則は標準三公理の範囲で監査済み。

## N4f：線形族からのデータの再構成（2026-10-18、N4 は未完了）

`PinchedRecoverIndex.lean` の `withoutLast I` は最終点を除いた先頭集合を一段小さい添字で読む。
`withLast` との往復、濃度、最小点を計算した。
`PinchedReadData.lean` は全先頭対象と最終対象を固定した任意のデータの終端成分を回収する。
実際の単体からの既存の `toLinearData` はこの共通操作を使うよう整理し、全方程式を再検証した。

`PinchedReconstructData.lean` の `LinearData.toSimplexData` は、先頭対象を x、最終対象を y とし、
終点が最終点なら元の線形成分、先頭面の二点なら単位、高次なら零というデータを構成する。
三分岐の計算と、再構成データの終端成分を回収すると元の族に戻ることを証明した。
`PinchedReconstructFaces.lean` は先頭面全体が x の定値データ、最終頂点が y の零単体データと示す。
任意の線形族と全 n に対するデータの結果であり、追加の方程式を仮定していない。

線形解から全単体方程式を導くこと、実際の逆写像と両逆則、実際の加群構造、
単体的な線形性、直接の線形ホーン充填・Kan 性・π₀ 比較、N6 は未完了。
全公開宣言 456 件と既存 5 則は標準三公理の範囲で監査済み。`reconstructObj` は公理に依存しない。

## N4g：全次数の線形表示の同値（2026-10-18、N4 は未完了）

`PinchedData.lean` は先頭面と終端だけを固定したデータを共通の補助対象とする。
`PinchedDataFront.lean`・`PinchedDataTerms.lean`・`PinchedDataRhs.lean` は、単体方程式を仮定せずに
先頭面の単位・零と全右辺の線形化を証明する。
`PinchedDataEquation.lean` の `Data.equation_of_linear` は、回収族の線形方程式から
元の全単体方程式を導く。終端を含む集合は線形化、含まない集合は定値先頭面の方程式による。

`PinchedReconstruct.lean` は線形解から実際の単体と右 pinched 単体を構成する。
`PinchedLinearEquiv.lean` は全終端成分の回収が単射であることを示し、両逆則を得る。
`PinchedHom.linearEquiv x y n` は任意の可換環 A、dg 圏 D、二対象 x,y、全 n に対して

```
(DGNerve.pinchedHom A D x y) _⦋n⦌ ≃ PinchedHom.LinearSimplex A x y n
```

を与える。入力の線形解の方程式から実際の単体方程式を証明しており、追加の方程式は仮定しない。
これでデータだけの比較から、全次数の実際の単体の線形表示の同値へ進んだ。

実際の写像空間への A 加群構造と単体的な線形性、直接の線形ホーン充填・Kan 性、
π₀ 比較、N6 は未完了。N4 全体の完了とは数えない。
全公開宣言 491 件と既存 5 則は標準三公理の範囲で監査済み。

## N4h：実際の写像空間の単体的 A 加群（2026-10-18、N4 は未完了）

`PinchedReindexIndex.lean` と `PinchedNaturality.lean` は、最終点固定延長の像・単射性・零分岐を比較し、
成分回収が任意の単体圏の射による引き戻しと可換であることを示す。
`PinchedLinearPullback.lean` は線形成分族の引き戻しを解の部分加群へ制限した A 線形写像とし、
恒等・合成の法則と全次数の同値の自然性を証明する。全ての退化も含む結果である。

`PinchedModule.lean` は各次数の実際の右 pinched 単体に加法可換群と A 加群を移す。
`moduleEquiv` は元の回収の同値を A 線形同値とし、`pullbackLinear` の値は元の引き戻しに一致する。
`pullback_add` と `pullback_smul` が元の面・退化の加法・A スカラー倍の保存を示す。
`PinchedModuleObject.lean` の `moduleObject x y` はこれを `SimplicialObject (ModuleCat.{max u v} A)` にまとめ、
各写像が元の単体的集合の写像であることも `moduleObject_map_apply` で確認する。

任意の可換環 A、dg 圏 D、二対象 x,y、全次数・全単体的射に対する構成で追加仮定はない。
これで N4 の各次数の加群構造と単体的な線形性は証明済み。
直接の線形ホーン充填・Kan 性、π₀ 比較、N6 は未完了。
全公開宣言 513 件と既存 5 則は標準三公理の範囲で監査済み。

## N4i：直接の線形充填の代数補題（2026-10-18、N4 は未完了）

`PinchedDeletion.lean` の `deleteSum_squared` は、右 pinched 方程式の全頂点削除和の二乗が零であることを示す。
`deletionSolution` は指定点以外の寄与の和に指定係数の逆元を掛けて負にした値で、
`sum_eq_zero_of_deletionSolution` がその値による削除和の相殺を証明する。端点でも同じ式を使う。

`PinchedLinearResidual.lean` は線形右辺を全域化した削除和に同定し、その微分を削除面の残差の和で表す。
`LinearData.missing_equation` は、最上位右辺が零で他の全削除面の残差が零なら欠けた面の方程式を導く。
`LinearData.rhs_eq_zero_of_deletionSolution` は明示解から最上位右辺が零であることを示す。
これらは条件付きの代数補題。実際のホーンからの成分回収と全方程式・面の一致はまだ構成していない。

対象・集約ビルドと公理監査は終了コード 0。全公開宣言530件と既存5則は標準三公理の範囲内。
直接の線形ホーン充填と Kan 性、π₀ 比較、N6 は未完了。

## N4j：直接の線形ホーン充填と Kan 性（2026-10-18、π₀ 比較は未完了）

`PinchedHornData.lean` は実際のホーンの二面から回収する同じ成分の一致を示し、
全体集合と欠けた面以外の既知成分を回収する。利用可能な面への制限は元の面と一致する。
`PinchedLinearEquationTransfer.lean` は単射な引き戻しで線形右辺を移送する。

`PinchedHornFilling.lean` は最上位成分を零、欠けた面を削除和の明示解とする。
既知方程式は面から回収し、最上位右辺は明示解で相殺する。
欠けた面自身の方程式は残差恒等式から証明し、全方程式を満たす線形解を構成した。

`PinchedKan.lean` はこれを実際の単体に戻し、面の一致からホーンを延長する。
任意の可換環 A、dg 圏 D、二対象 x,y に対して
`PinchedHom.instKanComplex : SSet.KanComplex (DGNerve.pinchedHom A D x y)` を公開する。
全 `n : ℕ` と全 `i : Fin (n+2)` のホーンを扱い、両端と次元一も含む。
追加の方程式の前提も、一般の単体的群による Kan 性も使っていない。

対象・集約ビルドと公理監査は終了コード 0。全公開宣言553件と既存5則は標準三公理の範囲内。
N4 の直接の線形充填と Kan 性は完了。π₀ と H⁰ の Hom の比較、N6 は未完了。

## N4k：π₀ と H⁰ の Hom の同値（2026-10-18、N4 必須項目完了）

`PinchedHom/Paths.lean` は一般の単体的集合で、右 pinched Hom の道を
`CompStruct (id x) (vertexEquiv t) (vertexEquiv s)` として両方向に読む。
`PinchedPiZero.lean` はこれを N3 の右辺ホモトピーと境界関係の比較につなぐ。
`path_iff_boundary` は道の存在と閉零射の境界関係の同値、
`piZero_mk_eq_iff_boundary` は Mathlib の連結成分の等しさと境界関係の同値。

`PinchedHom.piZeroEquiv x y` は任意の可換環 A と dg 圏 D に対して、
Mathlib の `SSet.π₀ (DGNerve.pinchedHom A D x y)` と既存の `HomotopyCategory A D` の
x,y の像の間の Hom を同定する。追加仮定はない。

対象・集約ビルドと公理監査は終了コード 0。全公開宣言568件と既存5則は標準三公理の範囲内。
これで N4 の必須項目は完了。N6 の具体例と最終監査が残る。
正規化 Moore 複体の比較は任意項目として見送る。

## N6：具体例と最終検査（2026-10-18、N0〜N6 必須範囲完了）

`DGNerve/Checks.lean` は、既存の一点 dg 圏の instance `ringEnrichment` と
非有界複体 dg 圏の instance `complexEnrichment` で二単体の微分方程式を具体化する。
`ring_triangle_equation` は `δh = f₁₂ ∘ f₀₁ − f₀₂`、
`complex_compose` は通常順 dg 合成と Mathlib の cochain 合成の一致、
`complex_triangle_equation` は `HomComplex.δ (-1) 0 h = f₀₁.comp f₁₂ − f₀₂` を証明する。
任意の可換環に対して成立し、複体の有界性や平坦性の仮定はない。
両具体例の quasicategory instance と写像空間の Kan instance も型検査した。

対象 `Checks` と集約 `DGNerve` のビルドは終了コード 0（3505 jobs）。
全公開宣言571件の型検査と、既存5則を含む計576件の公理監査を照合し、全て標準三公理の範囲内。
全宣言の docstring 規約と担当ソースに新しい穴・公理がないことも確認した。
受入基準ごとの実装・型・検証の対応表と正確な新規公開型は計画 §5 の N6 に記録した。

N0〜N6 の必須項目は全て完了。正規化 Moore 複体と τ≤0 Hom の比較は任意項目として見送った。
この文書の各途中記録にある未完了の記述は、その保存時点の履歴である。

## N7.1：dg fiber 錐と slice の終対象条件（2026-10-18、紙の検証）

参照は HA Construction 1.3.1.6、Proposition 1.3.1.10、HTT Definition 1.2.13.4、
Kerodon §4.6.5・§7.1。Core の `JoinCone p` は `Δ[0] ⋆ K → X`、
`IsLimitCone c` は `IsTerminalVertex (sliceOver p) c` である。
以下は N7a の紙の計算であり、N7b〜N7e の Lean の定理の完成はまだ主張しない。
係数環は従来どおり任意の可換環。ここでは錐の頂点を A、係数環を R と書き分ける。

### 境界延長で未知になる六成分

`K = Λ[2,2]` の三頂点を B,C,D、二辺を `g:B→D`, `h:C→D` とする。
固定した錐 c は頂点 A、閉次数零の辺 `p:A→B`, `q:A→C`, `t:A→D` と、
次数 −1 の二成分 u,v を持ち、

```
δu = g p − t,     δv = h q − t.
```

slice での正次元境界 `∂Δ[m] → sliceOver p`（m≥1）の最後の頂点が c であるとする。
`sliceOverEquiv` の普遍性で、これは `∂Δ[m] ⋆ K` からの dg nerve のデータであり、
最後の頂点に対応する `{m} ⋆ K` 上では c と一致する。
可変頂点全体を `V={X₀,…,Xₘ₋₁,A}`（|V|=m+1）と書く。
`Δ[m] ⋆ K` へ延ばす際、真の可変部分集合の成分は境界から全て既知。
K の非退化単体には BC や BCD がないため、未知は正確に次の六つとなる。

| 支持集合 | 未知成分 | 値と次数 |
| --- | --- | --- |
| V | a | Hom(X₀,A) の 1−m 次 |
| V∪{B} | b | Hom(X₀,B) の −m 次 |
| V∪{C} | c′ | Hom(X₀,C) の −m 次 |
| V∪{D} | d | Hom(X₀,D) の −m 次 |
| V∪{B,D} | e | Hom(X₀,D) の −m−1 次 |
| V∪{C,D} | f | Hom(X₀,D) の −m−1 次 |

HA の成分方程式を展開し、既知の項を r にまとめると、正確な符号は

```
δa = r₀,
δb = p a + rB,          δc′ = q a + rC,          δd = t a + rD,
δe = g b − d − u a + rBD,
δf = h c′ − d − v a + rCD.
```

`r₀` の次数は 2−m、`rB,rC,rD` は 1−m、`rBD,rCD` は −m。
例えば V∪{B,D} の切断 A の係数は +1 なので合成項は `−u a`、
切断 B の係数は −1 なので `−d+g b`。V∪{B} の切断 A は −1 なので `+p a`。
それ以外の削除・切断は可変頂点の真部分集合だけを使い、既知である。
特に `I=V` の式 `δa=r₀` は残る。N2 のように a を無条件に零と置いてはならない。

### Hom の fiber と比較写像の錐

`H=Hom(X₀,A)`、`E=Hom(X₀,B)⊕Hom(X₀,C)`、`G=Hom(X₀,D)` とし、
`μ:E→G`, `μ(b,c′)=g b−h c′` と置く。
fiber の座標規約を

```
F^k = E^k ⊕ G^(k−1),
δF(b,c′,z) = (δb,δc′, μ(b,c′)−δz)
```

とする。これは `mappingCone μ⟦−1⟧` の G 座標を負にして得る表示。
Mathlib の `δ_inl = ofHom (μ ≫ inr)`、`δ_snd = −fst.comp (ofHom μ)` と整合する。
この符号変更は N0 の dg nerve の成分の符号を変更するものではない。
`w=u−v` は `δw=g p−h q` を満たすので

```
Φ:H→F,       Φ(a)=(p a,q a,w a)
```

は複体の射。第三成分では `δ(w a)=(δw)a−w δa` を用いるため、
`δF Φ(a)=(p δa,q δa,w δa)=Φ(δa)` となる。

六式のうち f の式を `d=h c′−v a+rCD−δf` として解き、
`z=e−f`, `U=(b,c′,z)`, `R=(rB,rC,rCD−rBD)` とすると、残りの独立な式は

```
δa=r₀,             δF U−Φ(a)=R.
```

既知部分集合の方程式と N2 の主残差恒等式により、右辺は次を満たす。

```
δr₀=0,                      δR=−Φ(r₀),
rD=h rC+v r₀+δrCD.
```

後二式の各座標は
`δrB=−p r₀`, `δrC=−q r₀`,
`δrBD=rD−g rB−u r₀`, `δrCD=rD−h rC−v r₀`。
したがって `C^k=H^(k+1)⊕F^k`, `δC(a,U)=(−δa,δF U−Φa)` とした比較写像の錐で、
求める方程式は `δC(a,U)=(−r₀,R)`、右辺は閉元という一つの線形問題である。

### 厳密 dg fiber の次数ごとの明示解

A が標準の dg fiber であるとき、Hom(X₀,A) と上の F の比較 Φ は複体の厳密同型となる。
複体 dg 圏では有限直和と shift、mappingCone の `inl/fst/snd` による座標表示を使い、
Hom の複体の同型を全次数で構成する。擬同型だけをここで代用しない。
この同型により次の値を直接選べる。

```
b=0, c′=0, e=0, f=0,     a=−Φ⁻¹(R),     d=−v a+rCD.
```

実際、`δa=−Φ⁻¹(δR)=r₀`、`Φa+R=0` より b,c′ と e−f の式が成立する。
f の式は d の定義で成立し、e の式は e−f の式から従う。
最後に `δd=−(h q−t)a+v r₀+δrCD=t a+rD`。
これで `I=V` の制約も含めて六つの方程式を解いた。
m=1 では r₀=0（V は辺）、a は閉零射、残りの式が二つの錐の間の比較のホモトピーを与える。

N7c ではこの代数計算だけでなく、join の成分回収の選択独立性、全次数の符号移送、
既知境界との一致、`JoinCone` と正方形の比較まで Lean で検証する必要がある。
N7b〜N7e は未完了であり、本紙の明示解を無条件の ∞ 引き戻し定理とは数えない。

## N7.2：複体 dg nerve の零対象（2026-10-18）

任意の可換環 A と任意の零対象 `Z : Complex A` に対し、
`DGNerve.isTerminalVertex_of_isZero Z hZ` と `DGNerve.isInitialVertex_of_isZero Z hZ` を証明した。
`isTerminalVertex_zero A` と `isInitialVertex_zero A` は零複体そのものへの適用。
追加の有界性・平坦性の仮定はない。

零定値 dg 関手と両方向の零自然変換から、`appendZero`・`prependZero` は任意の単体に零頂点を加える。
終端へ向かう成分、始域から出る成分は全次数で零なので、単体は残りの面で一意に決まる。
指定された任意の境界にこの拡張を適用し、共通面と端点を比較して全ての境界面との一致を証明した。
Core の境界充填による `IsTerminalVertex` と `IsInitialVertex` を直接満たし、次元一も含む。

対象 `ZeroObject` と集約 `DGNerve` のビルドは終了コード 0（3585 jobs）。
全公開宣言604件の型検査、既存5則を含む609件の公理監査は標準三公理の範囲内。
正確な新規公開型と前提は計画 §5 の N7b に記録した。
N7b の複体版は完了。充満部分圏への制限は N7d、fiber の錐と引き戻しは N7c 以降の未完了範囲。

## N7.3：標準 fiber の錐と Hom 座標（2026-10-18、極限性は未証明）

`fiberDifference g h` を `biprod.desc g (-h)`、`pullbackFiber g h` をその mappingCone の −1 シフトとする。
標準射影から二脚を作り、`fiberNullHomotopy` の微分が二つの脚の合成の差になることを証明した。
B を通る標準ホモトピーの三角形と C を通る零ホモトピーの三角形を貼って
`standardFiberSquare g h` を構成し、その右辺・上辺が g,h であることを確認した。
`standardFiberCone` は Core の JoinCone で、その頂点は標準 fiber の頂点そのもの。

`pullbackHomCoordinates g h n` は全 n:ℤ に対し、Hom(X,P) の次数 n+1 の成分を
Hom(X,B)、Hom(X,C) の同次数成分と Hom(X,D) の次数 n 成分へ A 線形に同定する。
微分は `(δb,δc,gb−hc−δz)` であり、三座標が標準の脚・ホモトピーへの後合成と一致することも証明した。
`pullbackHomBoundaryLift` はこの座標の逆の負による明示解。
`pullbackHomBoundaryLift_differential` は整合条件 δR=−Φr₀ のもとで δa=r₀ を証明する。

対象・集約ビルドは終了コード 0（3643 jobs）、公開宣言656件の型検査と既存5則を含む661件の
公理監査は標準三公理の範囲内。正確な公開型・前提は計画 §5 の N7c1 に記録した。
まだ実際の slice 境界から右辺の整合条件を導いておらず、境界全体との一致も未検証。
`IsLimitCone`・`IsPullbackSquare` の証明と N7d・N7e は未完了。


## N7.4：cospan のセルと部分境界の成分回収（2026-10-18）

任意の `n : ℕ` について、`join Δ[n] Λ[2,2]` を二つの `Δ[n+2]` で表示する
`cospanJoin_isPushout` を証明した。共通面は `δ ((Fin.last (n+1)).castSucc)`、
先頭の面 `j` の包含は大きい単体の `δ (j.castAdd 2)` と可換。
`joinStdSimplexIso_inl`・`joinStdSimplexIso_inr` は左右の頂点の番号を明示する。

`SelectedFaces.region S` は「選んだ頂点 `j ∈ S` のいずれかを避ける単体」の部分複体。
`SelectedFaces.desc` は全ての共通の制限で一致する面の族を貼り合わせ、`desc_face` は元の面を復元する。
`CoversVertices S := ∀ k, ∃ j ∈ S, j ≠ k` の下で対象族を回収し、
`recoverHom` は `hknown : ∃ j ∈ S, j ∉ I` を満たす部分集合の斉次成分を取り出す。
`recoverHom_heq_face` により、この値は I を含む任意の選んだ面の成分と異種等号で一致する。
N2 の順序付き列挙と面による分解の証明を、ホーン以外の部分境界でも使える形にした。

この保存単位は成分回収の準備まで。実際の slice 境界の面の族の整合性、
未知六成分の残差恒等式、充填単体の方程式と境界一致、`IsPullbackSquare` は未証明。
N7c〜N7e は未完了。公開型・前提・監査結果は計画 §5 の N7c2 に記録する。


## N7.5：実際の join 境界から既知方程式へ（2026-10-18）

`cospanPrefixFaces n` は `Fin (n+4)` の最初の `n+2` 点。全頂点を覆い、
既知集合の条件は `¬ cospanPrefixFaces n ⊆ I` と同値。
`cospanUnknown_cases` は残りの集合を、先頭だけ、先頭と B/C、先頭と D、全体の四種類に分類する。
左右のセルを合わせたときの共通の先頭・D 成分の同定は次の工程で行う。

任意の `F : join (boundary (n+1)) Λ[2,2] ⟶ X` から、追加の整合性仮定なしに
`cospanBoundaryLeft F`・`cospanBoundaryRight F` を構成した。
境界包含の join は単射なので、その持ち上げである各面の整合性が従い、貼り合わせられる。
実際の slice 境界 `b : boundary (n+1) ⟶ sliceOver p` には `F := sliceOverUncurry b` を使う。

dg nerve を標的とすると、`cospanBoundaryLeftData F unknown`・`cospanBoundaryRightData F unknown`
は各々 `SimplexData A D (n+3)`。未知の射族 `unknown` をどの値にしても、
全ての既知面で元の F の制限と一致し、先頭の一点でも欠く I の `Equation I` を満たす。
未知成分の方程式はまだ証明していないので、これらのデータを `Simplex` とはしていない。

次は共通成分の比較、標準 fiber への対象の移送、未知六成分の残差恒等式と解を実装する。
`IsPullbackSquare` および N7d・N7e は未完了。正確な公開型と前提は計画 §5 の N7c3 に記録する。


## N7.6：先頭と脚の残差整合条件（2026-10-18）

`cospanApex n` は先頭集合の最後の点で、その集合の濃度は `n+2`。
先頭の一点を削除した集合、錐頂点より前で終わる左切断、零より後で始まる右切断は既知集合。
これらの事実で Bianchi の有限和の既知残差を消去した。

`SimplexData.differential_rhs_zero_of_proper_equations` は全真部分集合の方程式から右辺の閉性を導く。
先頭集合に適用すると `cospanPrefixRhs_closed`、すなわち `δr₀=0` を得る。
末尾一点を加えた集合では、錐頂点の Bianchi の寄与だけが残る。
その点の符号は負一、右切断の次数は零なので、
`cospanOneTailRhs_differential` は右辺の微分を脚と先頭残差の合成に同定する。
先頭の未知成分を零とすれば、`cospanOneTailRhs_differential_of_prefix_zero` により
`δr_B=−p r₀`・`δr_C=−q r₀`・`δr_D=−t r₀` に対応する式になる。

`cospanBoundaryLeftZeroData F`・`cospanBoundaryRightZeroData F` は実際の join 境界写像の
全未知成分を零としたデータ。両者の先頭成分の零、先頭右辺の閉性、脚側微分の式を証明した。
ここで脚は回収した `edgeHom` であり、標準 fiber の射との同定はまだ行っていない。
次数は先頭成分が `−n`、先頭右辺が `−n+1`、脚側右辺が `−n−1+1`。
後者は `−n` と等しいが、定義では微分の出力次数をそのまま保持する。

残る三角形成分の微分恒等式、左右の共通成分と錐の対象・射の同定、fiber 座標による未知成分の解、
全方程式と境界の一致、`IsPullbackSquare` は未完了。公開型と前提は計画 §5 の N7c4 に記録する。


## N7.7：三角形側の残差整合条件（2026-10-18）

全体集合の錐頂点と最初の末尾頂点での削除・切断を計算し、Bianchi の寄与がこの二点に限られることを
`differential_rhs_cospan_twoTail_pair` で証明した。前者の符号は正一、後者は負一。
`SimplexData.tripleHom` は任意の増加する三頂点の次数 −1 の成分。
二つの寄与は、それぞれ `u e₀` と `−e_D + g e_B` になる（e は各未知集合の残差）。

`differential_rhs_cospan_twoTail_of_unknown_zero` は未知成分が全て零である場合に
`δr_BD = −(u r₀ + (−r_D + g r_B))`、すなわち `r_D − g r_B − u r₀` を与える。
`cospanBoundaryLeftZeroData_unknownHom`・右版で実際の境界データの全未知成分の零を確認し、
左右の `...ZeroData_twoTail_differential` により、この整合式を追加仮定なしに証明した。
右のセルでは同じ式の g,u,r_B,r_BD を h,v,r_C,r_CD と読む。

この時点の射・三角形は、各セルから回収した `edgeHom`・`tripleHom`。
左右に共通の先頭・D 成分の同定と、標準 fiber の錐の p,q,t,u,v,g,h との比較はまだ未完了。
従って、二セルをまとめた fiber の座標の適用、未知六成分の解、全方程式と貼り合わせ、
`IsPullbackSquare` の完成とは数えない。公開型・前提・次数は計画 §5 の N7c5 に記録する。


## N7.8：左右の共通面の一致（2026-10-18）

`cospanCommonOrderHom n : Fin (n+3) →o Fin (n+4)` は最初の末尾頂点 B/C を飛ばす面。
共通面の先頭 `n+2` 点の像は `cospanPrefixFaces n` に等しい。
小さい二セルの pushout の可換性と面の合成恒等式から、
左右の零未知データの共通面への制限が全ての既知面で一致することを示した。
共通面の未知集合の像も元の未知集合なので、その成分は左右とも零。

`SimplexData.ext_of_selected_faces_zero_unknown` は、頂点を覆う選んだ面で一致し、
残りの成分がともに零である二データを同定する。単体の方程式は仮定しない。
これを適用した `cospanBoundaryZeroData_common F` は追加仮定なしに
`(cospanBoundaryLeftZeroData F).pullback (cospanCommonOrderHom n) =
(cospanBoundaryRightZeroData F).pullback (cospanCommonOrderHom n)` を与える。

`cospanBoundaryZeroData_common_obj` は共通面上の全対象の等式、
`cospanBoundaryZeroData_common_rhs_heq` はその任意の部分集合の像での右辺の異種等号を与える。
N2 の単射の像の比較を方程式前の `SimplexData` と `rhs` に拡張して使った。

次は最後の頂点に指定された錐を境界から回収し、標準 fiber の対象・脚・三角形成分と比較する。
その後の fiber 座標による六成分の解と最終充填、`IsPullbackSquare`、N7d・N7e は未完了。
公開型・前提は計画 §5 の N7c6 に記録する。


## N7.9：最後の頂点の標準 fiber 錐の回収（2026-10-18）

`sliceOverUncurry_yoneda` と `sliceBoundary_last_cone` により、slice 境界 b の最後の頂点が錐 c なら、
`joinMap (boundaryVertex n (Fin.last (n+1))) (𝟙 K) ≫ sliceOverUncurry b = c.val` を得る。
`lastTriangleOrderHom n` は標準セルの最後の三頂点を選び、その三角形は零番目の既知面に含まれる。
標準 join 同型と最後の左頂点の可換性を使い、左右の零未知データの最後の三角形が c の対応する三角形に
等しいことを `sliceBoundaryLeftData_last_triangle`・右版で証明した。

c を `standardFiberCone g h` とすると、`fiberSliceBoundary_left_triangle`・右版により、
最後の三角形のデータは `fiberLowerTriangle g h`・`fiberUpperTriangle g h` に等しい。
六つの対象の等式（両側の頂点 P、左の B・D、右の C・D）、六辺の cochain の異種等号
（p,g,t と q,h,t）、三点成分の異種等号（u と零）を全て取り出した。
`ComplexTriangleComponents` は chain map とホモトピーからの三角形の対象・三辺・三点成分を評価する。

最後の頂点の条件 hb は終対象性の境界テストそのものの入力であり、別の極限性の仮定は使っていない。
回収した射はまず異種等号で保持し、次に端点と次数の等式に沿って Hom 座標へ移す。
未知六成分の解、未知方程式と最終充填、`IsPullbackSquare` と N7d・N7e は未完了。
公開型と全前提は計画 §5 の N7c7 に記録する。


## N7.10：型付き残差と未知成分の逆座標による候補（2026-10-18）

`gradedHomTransport` は端点と次数の等式に沿う線形同型で、微分・合成を保つ。
`fiberBoundarySource` を左の零番目の対象 X に取り、`q := fiberBoundaryDegree n = −n−1` と置く。
先頭右辺 r₀ は `Cochain X P (q+2)`、r_B,r_C,r_D は次数 q+1、r_BD,r_CD は次数 q の
標準の対象への cochain として `FiberBoundaryResiduals` に定義した。
先頭と D 側の共通値は左側から一度だけ移送し、右の生のデータとは
`fiberBoundaryRhs0_heq_right`・`fiberBoundaryRhsD_heq_right` の異種等号で同定する。
`fiberBoundaryRhs0_closed` により型付きの δr₀=0 も証明した。

`pullbackResidual_matrix` は四つの微分整合式を前提として、Hom-fiber の三座標の行列条件を与える。
`PullbackBoundaryEquations` はその条件から先頭の明示解の微分方程式を証明し、射影・ホモトピー・
対角射の式、d=r_CD の微分式と左三角形の式を証明する。これらの一般補題の整合式は明示的な前提。
実際の境界の r_B,r_C,r_BD,r_CD が移送後もその整合式を満たす証明は次に行う。

実際の境界から `fiberBoundaryUnknownA` を `−φ⁻¹(r_B,r_C,r_CD−r_BD)`、
`fiberBoundaryUnknownD` を r_CD として定義し、その射影・ホモトピー・対角射・左三角形の式を確認した。
ただし実際の候補の δa=r₀ と δd=t a+r_D は未証明。
未知成分を入れた単体データ・全方程式・境界の一致・`IsPullbackSquare`、N7d・N7e は未完了。
公開型・全前提は計画 §5 の N7c8 に記録する。


## N7.11：実際の境界の微分整合式と明示解の微分（2026-10-18）

`FiberBoundaryLegCompatibility` と `FiberBoundaryTriangleCompatibility` により、
実際の slice 境界 b（次元 n+1）の最後の頂点が標準錐であるという条件 hb だけから、
型付き残差について δr_B=−p r₀、δr_C=−q r₀、
δr_BD=r_D−g r_B−u r₀、δr_CD=r_D−h r_C を証明した。
`CospanOneTailTransport`・`CospanTwoTailTransport` は一般 dg 圏の Bianchi を
対象と次数の等式と成分の異種等号に沿って移す。
`cospanTwoTailLastRhs` は三角形の計算と同じ次数で D 側右辺を評価し、
`cospanTwoTailLastRhs_heq` が既存の脚側右辺と比較する。

`fiberBoundaryUnknownA_differential` は実際の候補 a=−φ⁻¹(r_B,r_C,r_CD−r_BD) に対し
δa=r₀ を、`fiberBoundaryUnknownD_differential` は d=r_CD に対し δd=t a+r_D を与える。
これらの定理には微分整合式や極限性の追加仮定はない。環 A は任意の可換環、複体は非有界。
N7.10 の射影・ホモトピー・対角射・左三角形の式と合わせて明示候補の有限線形系を検証した。

右側の r_C,r_CD は、移送した cochain と生の右辺との異種等号を同時に記録する
`fiberBoundaryRhsCWithHEq`・`fiberBoundaryRhsCDWithHEq` の値として定義した。
この二つは本体を検査した `opaque` 定義であり、移送の大きな項を比較時に再展開しないためのもの。
公理は追加していない。`gradedHomTransportWithHEq` がその一般的な構成を与える。

未完了：明示解を入れた単体データの構成、未知四集合の方程式との一致、全境界の一致と貼合せ、
標準四角形の `IsPullbackSquare`、N7d と N7e。候補の微分式を最終的な充填定理とは数えない。
新規公開宣言 33 個の正確な型と前提は計画 §5 の N7c9 に記録する。


## N7.12：明示解を挿入した候補データと先頭方程式（2026-10-18）

`fixedHomFamily` は有効な固定端点・次数の一射を成分置換の全ての引数指定へ拡張し、
`replaceFixed` がその一射を一集合に挿入する。
`ReplacementLocality` は置換集合 M を含まない I で寄与・右辺・方程式を保存する。
`equation_of_fixed` と `equation_of_fixed_heq` により、固定した端点・次数または型付き Hom の式から
一集合の全ての端点・次数での `Equation` を検証できる。

`fiberBoundaryLeftNative` と右版は、共通の a,d を左右の生の対象へ移した値と異種等号を保持する。
本体を検査した `opaque` 定義を使い、比較時の大きな移送項の再展開を防ぐ。
`fiberBoundaryLeftCandidate`・右版は零未知基底の V=`cospanPrefixFaces n` と
V∪{D} の二成分をそれぞれ a,d に置き換えた `SimplexData`。
まだ `Simplex` ではなく、全未知方程式の検証は含まない。

候補の対象族、全ての既知面、全既知集合の方程式を保存することを証明した。
V と V∪{D} 以外の全成分は基底と一致し、そのうち未知成分は零。
`fiberBoundaryLeftCandidate_prefix_equation`・右版は V の方程式を証明する。
先頭右辺は二回の置換で変わらず、挿入した成分の微分は N7.11 の δa=r₀ に一致する。
環・複体・境界・最後の頂点の条件は N7.11 と同じで、追加の整合式・極限性の仮定はない。

未完了：V∪{B}（右では C）、V∪{D}、全体集合の三つの未知方程式、
左右の共通面と貼合せ、全境界の一致、標準四角形の `IsPullbackSquare`、N7d・N7e。
新規公開宣言 34 個の正確な型・前提は計画 §5 の N7c10 に記録する。


## N7.13：先頭置換による右辺の変化と脚・D 側方程式（2026-10-18）

`LeftCutReplacement` は内部点 i の左切断成分を置き換えると i だけの寄与が変わることを証明する。
削除集合と右切断は最大頂点を含み、左切断は含まないので他の項は保存される。
`eqRec_proofFamily_apply` は端点・次数・濃度の証明だけを引数とする族の評価から依存型の移送を除く。

`cospanOneTailRhs_replace_prefix` は、先頭成分の変化を Δa とすると脚側右辺の変化が p Δa であることを
証明する。錐頂点の符号 −1 と合成項の負が相殺する。
`CospanPrefixReplacementTransport` はこの式を型付き Hom へ移し、
先頭の零未知基底から置換した右辺を r+p a と比較する。
`fiberBoundaryLeftPrefixCandidate`・右版は先頭だけを置換した中間データ。

`fiberBoundaryLeftCandidate_first_equation`・右版は、B 側・C 側成分を零とした方程式を証明した。
`fiberBoundaryLeftCandidate_last_equation`・右版は、D 側成分 d の方程式を証明した。
D 側成分の置換は最初の脚側右辺を変えず、自分の集合の右辺も変えない。
その右辺は型付きの r_D+t a に一致し、既に証明した δd=t a+r_D を適用する。
これらは任意の可換環と非有界複体の境界に対し、最後の頂点の条件 hb だけで成り立つ。

未完了：全体集合の三角形方程式（二つのセルそれぞれ）、左右の共通面での一致・貼合せ、
全境界での一致と標準四角形の `IsPullbackSquare`、N7d・N7e。
新規公開宣言 22 個の正確な型・全前提は計画 §5 の N7c11 に記録する。


## N7.14：三角形方程式と左右の実際の単体（2026-10-18）

`cospanTwoTailRhs_replace_prefix` は先頭成分の変化 Δa が三角形側右辺を −u Δa だけ変えることを証明する。
`rhs_replace_of_erase_eq` は内部削除集合と別表示の集合を同定した置換公式。
`cospanTwoTailRhs_replace_D` は D 側成分の変化が右辺をその負だけ変えることを与える。
`cospanTwoTailRhs_replace_zero_of_heq` は二置換の変化を型付き Hom へ移し、
r−u a−d=0 から置換後の全体右辺が零になることを証明する。

`fiberBoundaryLeftCandidate_full_rhs_zero`・右版と `...full_equation` により、
左右の候補の最後の未知方程式を証明した。
左側は明示解の −d−u a+r_BD=0、右側は u=0 と d=r_CD を使う。
全体成分は零のままなので、右辺の零性がそのまま微分方程式になる。

`fiberBoundary{Left,Right}Candidate_all_equations` は任意の部分集合 I の Equation を与える。
既知集合と四種類の未知集合を分類し、これまでの全検証を合わせた。
`fiberBoundaryLeftSimplex`・`fiberBoundaryRightSimplex` はこれらの方程式を付けた
`Simplex A (Complex A) (n+3)` であり、実際の dg nerve の単体である。
環 A は任意の可換環、複体は非有界。実際の境界と最後の頂点の条件 hb 以外の前提はない。

未完了：左右の共通面の一致、貼合せ、全境界と cospan 上の一致、slice への curry、
標準四角形の `IsPullbackSquare`、N7d・N7e。
全方程式を満たす二単体の構成は完了したが、slice の充填と終対象性はまだ完了していない。
新規公開 15 宣言の正確な型と前提は計画 §5 の N7c12 に記録する。


## N7.15：標準 fiber の ∞ 引き戻し性（N7c 完了、2026-10-18）

`standardFiberCone_isLimit (g : B ⟶ D) (h : C ⟶ D) : IsLimitCone (standardFiberCone g h)` と
`standardFiberSquare_isPullback (g : B ⟶ D) (h : C ⟶ D) :
IsPullbackSquare (standardFiberSquare g h)` を証明した。
A は任意の可換環、B,C,D は非有界の `Complex A`。閉性・整合式・擬同型性などの追加仮定はない。
標準 fiber は既存の `pullbackFiber g h`、すなわち B⊕C→D の mapping cone の −1 シフト。

左右の候補の挿入成分を共通の型付き a,d と比較し、それ以外は零未知基底の共通面へ戻して
`fiberBoundaryCandidate_common`・`fiberBoundarySimplex_common` を証明した。
`fiberBoundaryJoinFiller` は二セルの押し出しで実際の二単体を貼る。
`fiberBoundaryJoinFiller_faces` は元の境界の全ての自由因子の面との一致。
`joinBoundaryFaces_fixed` が右因子の固定条件を一つの面から回収し、
`sliceOverCurry_boundary_of_joinFaces` が curry した写像の全境界との一致を示す。
これにより標準錐を最後の頂点とする任意の正次元 slice 境界を直接充填した。
モデル構造・Joyal の定理・coherent nerve は使用していない。

N7a、N7b、N7c は完了。未完了は N7d（充満 dg 部分圏への制限）と N7e（任意の引き戻しの頂点の比較）。
N7f の双対は任意項目。新規公開 17 宣言の正確な型と前提は計画 §5 の N7c13 に記録する。


## N7.16：充満部分圏への制限と Semifree の零・標準引き戻し（N7d 完了、2026-10-18）

`fullInclusion_mono` により充満 dg 部分圏の包含の dg nerve は単射。
`range_le_fullOnObjects_of_vertices` は写像の全頂点の対象が P を持てばその全像が
`fullOnObjects A D P` に含まれることを示す。
`fullInclusionLift` は N5 の `range_inclusion` と像への同型を使い、その写像を部分圏へ持ち上げる。
全頂点を覆う写像に沿う延長を扱う `fullInclusion_extension` を、正次元境界の join に適用した。
これにより `isLimitCone_of_fullInclusion` と `isPullbackSquare_of_fullInclusion` は、
部分圏内の錐・四角形の周囲での極限性・引き戻し性を部分圏へ反映する。閉性の仮定はこの反映自体には不要。

`fullFiberSquare P g h hB hC hD hP` は B,C,D と標準 fiber が P に属するときの部分圏内の四角形。
`fullFiberSquare_inclusion` は包含像が周囲の標準四角形に等しいこと、
`fullFiberSquare_isPullback` はその ∞ 引き戻し性を証明する。
したがって錐・シフト・有限直和などの閉性により fiber の所属 hP を得る任意の充満部分圏へ適用できる。
零複体の所属だけから、`isTerminalVertex_full_zero`・`isInitialVertex_full_zero` が零対象を与える。

Semifree への適用前に、`formalization-plans/derived-infinity-category.md` の
D2h 完了（§5、2026-10-18）と D2h′ 完了の記録を確認した。
`Derived/SemifreeClosure.lean` の `complexSemifree_zero` と
`complexSemifree_biprodFiber`（二項直和と fiber の無条件の閉性）を使用する。
`semifreeFiberSquare` と `semifreeFiberSquare_isPullback` は任意の Semifree B,C,D の標準引き戻しを構成し、
`semifreeFiberSquare_inclusion` は周囲の標準四角形との一致を与える。
`isTerminalVertex_semifree_zero`・`isInitialVertex_semifree_zero` も証明済み。
これらの標的 `dgNerve A (Semifree A)` は定義上 `derivedInfinityCategory A` と同じ単体集合。
集約の循環 import を避けるため Derived/InfinityCategory 自体は import しない。

N7a–N7d は完了。残る必須項目は N7e（任意の引き戻しの頂点と標準 fiber の比較・擬同型性）。
N7f は任意項目。新規公開 28 宣言の正確な型と前提は計画 §5 の N7d に記録する。


## N7.17：任意の引き戻しの頂点から標準 fiber への誘導射（N7e・N7 必須項目完了、2026-10-18）

任意の `F : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ dgNerve A (Complex A)` に対し、
`presentComplexCospan (pullbackCospan F)` が右上二辺から三複体・二射を抽出する。
共通終域の等式はホーンの二辺の共通頂点から導出し、
その二射の標準 fiber 四角形の cospan が元の cospan と厳密に等しいことも証明した。
図式の一致を外部の追加仮定として要求しない。

`squareStandardFiber F` はこの二射の差の mapping cone の −1 シフト。
`squareFiberComparisonEdge F` は元の錐から標準 fiber 錐への slice の比較辺を射影し、
終点を実際の標準 fiber に同定した辺である。
`squareFiberComparison F : (pullbackCone F).vertex.obj 0 ⟶ squareStandardFiber F` はその辺の chain map。
比較辺は標準錐の終対象性から選択するので、比較元の極限性は構成には不要。
これは極限の普遍性による誘導射の選択であり、孤立した二対象間の任意の射を選んでいるのではない。

前提が `hF : IsPullbackSquare F` のとき、
`squareFiberComparison_nerve_isIso` は同じ比較辺の類が nerveHomotopyCategory で同型であること、
`squareFiberComparison_H0_isIso` はその閉零射の H⁰ の類が同型であること、
`squareFiberComparison_homotopyEquivalence` は同じ chain map がホモトピー同値であること、
`squareFiberComparison_quasiIso` はその擬同型性を与える。
A は任意の可換環で複体は非有界。整合式・閉性・図式一致などの追加前提はない。

証明は、終対象間の指定された辺に A2 の片側逆射を二回与えて同型にし、
N3 の H⁰ 比較と既存の complexHomotopyComparison、Mathlib のホモトピー商の同型の特徴づけを通す。
標準 cospan 上の任意の極限錐に対する同じ比較も `FiberConeComparison` に公開した。

N7a–N7e は完了。N7f の cofiber の双対は任意項目として未実装。
新規公開 37 宣言の正確な型と全前提は計画の実施記録（分割後は archive/dg-nerve-log.md）に記録する。


## γ1：局所 Kan な単体的圏の coherent nerve（着手前の照合）

目標は任意の `C : Type u`、`[Category.{v} C]`、`[SimplicialCategory C]` に対する
`(∀ X Y : C, SSet.KanComplex (SimplicialCategory.sHom X Y)) →
SSet.Quasicategory (CategoryTheory.SimplicialNerve C)`。
局所 Kan 性以外に充填の選択・整合性・モデル構造を仮定しない。
原典は HTT 1.1.5.10 と [Kerodon 2.4.5.1](https://kerodon.net/tag/00LH)。
配置は `InfinityCategories/Coherent/`。着手前の照合に基づく以下の方針で γ1 を証明した。

### Path[n] と順序の向き

Mathlib `AlgebraicTopology/SimplicialNerve.lean` の `SimplicialThickening J` は、
対象が線形順序 J、a から b への path が端点を含む区間 [a,b] の部分集合。
Hom 単体集合はこの path の圏の通常 nerve、合成は和集合、単位は singleton。
Mathlib の path 間の射は **包含**。したがって m 単体は増大列
`I₀ ⊆ ⋯ ⊆ Iₘ` である。`SimplicialNerve C` の n 単体は
`EnrichedFunctor SSet (SimplicialThickening (ULift (Fin (n+1)))) C`。
ULift は宇宙の調整であり、対象や path の数学を変更しない。

[Kerodon 2.4.3.1・2.4.3.5](https://kerodon.net/tag/00KM) は path を逆包含で順序付ける。
よって同じ記号をそのまま同一視しない。Mathlib の 2 単体の Hom 内の辺は
直接辺 f₀₂ から合成 f₁₂∘f₀₁ へ向かい、Kerodon 2.4.3.10 は逆向きである。
以下の証明は Mathlib の包含規約を直接使い、Kerodon の空洞立方体の上下を交換する。
これは `SimplicialNerve` の再定義や設計変更を必要としない。

### 内部ホーンを一つの Hom の延長問題へ戻す

[Kerodon §2.4.4](https://kerodon.net/tag/00L0) は Path[S] を単体の Path[n] の余極限で構成し、
Path[-] と coherent nerve の随伴を得る。γ1 では任意の S に対するこの左随伴を先に作らず、
ホーンを構成する面の豊穣関手を貼り合わせる局所的な普遍性を証明する。

a<b の path を内部点の部分集合へ送ると、その Hom は (b−a−1) 次元立方体の nerve。
Mathlib では座標 xⱼ=1 が j を含むことを表し、合成は切断点の座標 xⱼ=1 の面に入る。
内部ホーン Λ[n,i]（0<i<n）から既知となるデータは、(a,b)≠(0,n) の Hom 全体と、
(0,n) の Hom 立方体の次の部分単体集合である：

- すべての内部点 j に対する xⱼ=1 の面（合成から既知）。
- j≠i に対する xⱼ=0 の面（ホーンに含まれる面から既知）。

増大列 I₀⊆⋯⊆Iₘ では「I₀ が内部点を含む、または Iₘ が i 以外の内部点を欠く」
がこの部分単体集合への所属条件になる。欠ける面は xᵢ=0 だけ。
これは [Kerodon 2.4.5.8](https://kerodon.net/tag/00LR) の包含規約での翻訳である。
ホーンが与える元の面上で一致することと、合成面との一致を証明してから貼る。

### Kan 性による延長と豊穣関手の復元

内部点 i の座標を Δ[1] として分離し、残りの立方体を Q、その境界を ∂Q とする。
既知部分は `(∂Q × Δ[1]) ∪ (Q × {1})`。
包含は `∂Q ↪ Q` と `{1} ↪ Δ[1]` の pushout-product なので anodyne。
Mathlib `AnodyneExtensions/PushoutProduct.lean` の
`anodyneExtensions_unionProd_ι` と `anodyneExtensions.horn_ι` を利用できる。
従って Kan な `sHom X₀ Xₙ` への写像は全立方体へ延長する。
[Kerodon 2.4.5.12](https://kerodon.net/tag/00LV) の空洞立方体の充填に対応する。
n=2 では Q は一点、既知部分は合成を表す {1} で、同じ議論が適用される。

延長は合成面を固定するため、全 Hom の写像は単位・合成を保つ豊穣関手になる。
端点以外の Hom は既知のまま。これを `SimplicialNerve C` の n 単体とし、
`horn.hom_ext` により元のホーンへの制限を確認する。
[Kerodon 2.4.5.9–2.4.5.10](https://kerodon.net/tag/00LT) の方法を用いる。
Mathlib の `Quasicategory` が求める n+2 次元の全内部ホーンをこの方法で充填する。

現在地：Path の内部点座標の Hom 同型、一座標分離、空洞部分の anodyne 性と
`pathHollow_extension` を証明済み。ホーンから共通対象・Hom を回収し、全制限との整合性、
零座標面の同定、共通単体と零座標面の交わりでの厳密な一致まで証明した。
native な合成面への同型 `pathThroughIso` と、零座標面・他の合成面との逆像を計算済み。
閉区間内の Hom は周囲の Hom と単位・合成に整合して同型である。
真部分区間の回収 `hornProperIntervalHom` は区間外の任意の既知面の候補に一致し、
大きい区間内での回収とも一致する。外側も真部分区間なら、標準回収は単位・合成を保つ。
全区間の各内部切断点上の実際の写像 `hornInnerCompositionHom` を構成した。
一般の `hornCompositionHom` は、外側も真部分区間なら標準回収の合成面への制限に等しい。
真部分区間の回収を既知面に制限すると元のホーンの Hom に一致する。
零座標面と合成面の交わりは面内 Hom の直積と同型であり、この交わり上で
`hornCompositionHom_zero_overlap` が両方の回収写像の厳密な一致を与える。
同じ座標に関する零座標面と合成面の交わりは空で、その上の写像は一意である。
二つの合成面の交わりは三つの native Hom の合成で全射に覆われる
（`pathTripleToIntersection_epi`、切断点 b≤c を仮定）。
この全射と真部分区間の合成則、C の結合律から、
`hornCompositionHom_composition_overlap` を証明した。
特に `hornInnerCompositionHom_overlap` は全区間の任意の内部切断点 b,c に対し、
`homOfLE inf_le_left ≫ hornInnerCompositionHom b =
 homOfLE inf_le_right ≫ hornInnerCompositionHom c` を与える。
前提は元の内部ホーン、0<i<last、0<b,c<last のみで、Kan 性や全区間の Hom の存在は不要。
全区間の零座標面・合成面の添字を統一し、`iSup_pathHollowFace` により面族の和が
`pathHollow` と厳密に等しいことを証明した。部分単体集合の多重余等化子を使い、
`hornHollowFaceHom_compatible` の全ての交わりでの一致から、追加の整合性仮定なしに
`hornHollowHom` を構成した。`hornHollowHom_on_face` は各面への制限を回収する。
`hornHollowHom_extension` の型は、内部ホーン σ、0<i<last と端点 Hom の Kan 性から、
`∃ g : nerve (Path (ULift.up 0) (ULift.up last)) ⟶ sHom (hornObj σ 0) (hornObj σ last),
 ∀ j, (pathHollowFace (hornHollowPoint i h0 hn) j).ι ≫ g = hornHollowFaceHom σ h0 hn j`。
他の Hom の Kan 性や全区間の Hom 写像の存在は前提にしていない。
延長と真部分区間の回収から `hornFillHom` を全ての頂点対に定義した。
逆向き区間の空性、同じ端点の単位則、真部分区間の合成則と内部合成面の制限を使い、
`hornFillHom_id`・`hornFillHom_comp` を証明し、`hornFilledFunctor` を復元した。
`hornFillHom_on_zero`・`hornFillHom_on_face`・`hornFilledFunctor_face` により
全ての既知面が元のホーンに一致する。これを Mathlib の面ごとのホーン充填判定に渡した。

γ1 は完了。namespace `SerrePositivity.InfinityCategories.Coherent` の最終公開 instance は

```lean
simplicialNerve_quasicategory (C : Type u)
    [Category.{v} C] [SimplicialCategory C]
    [∀ X Y : C, SSet.KanComplex (SimplicialCategory.sHom X Y)] :
    SSet.Quasicategory (SimplicialNerve C)
```

前提は Mathlib の単体的圏と各 Hom の Kan 性だけで、充填や整合性を仮定していない。
型は対象・Hom の両宇宙を保持する。明示的な公開 234 宣言を公理監査済みで標準三公理のみ。
対象と集約のビルド、公理監査は終了コード 0。N7 と計画分割の完了も再検証した。
γ2・γ3 と N7f の任意の双対は今回の範囲外。
各段の実施記録はコミットメッセージへ置き、計画本文には現在地と残工程を短く残す。

## γ1.5：Dold–Kan 豊穣化と dg nerve の比較

γ1.5a〜d は完了。任意の `[CommRing R] [DGCategory R D]` に対して、構成済みの比較射を
順方向とする `coherentComparisonEquivalence` を得た。以下は設計・規約・数学の正本。
原典は [HA 1.3.1.12–1.3.1.17](https://www.math.ias.edu/~lurie/papers/HA.pdf)、
[Kerodon 2.5.7](https://kerodon.net/tag/00RF)、
[2.5.8](https://kerodon.net/tag/00S0)、[2.5.9](https://kerodon.net/tag/00SC)。
配置は `InfinityCategories/DoldKanComparison/`。既存の dg 層と Core は編集しない。

### 複体と単体的 Hom の模型

可換環 R、`D : Type v`、`[DGCategory R D]` とし、H=Hom^•(x,y) と書く。
HA の homological 次数を反転し、非負 chain 複体 L(H) を
`L(H)₀=Z⁰H`、`L(H)ₖ=H^(−k)`（k>0）、微分は δ とする。
次数1から0へは δ を閉元へ因子分解する。これは τ^{≤0}H の反転であり、
次数0を H⁰ の項そのものにする切断ではない。H⁰ のコホモロジーへの商も取らない。

DK(L(H)) の具体的模型には、標準単体の正規化 chain 複体から L(H) への chain map を使う。
その成分は、非空 J={j₀<…<jₖ}⊆[n] ごとの `t_J∈H^(−k)` で、
`δt_J=Σ_{r=0}^k (−1)^r t_{J\{j_r}}` を満たす（k=0 では閉元）。
単調写像で単射な J は像の成分へ送り、潰れる正次数成分は零とする。
Mathlib の `Abelian.DoldKan.Γ` と同一の定義だとは仮定せず、正規化・逆関手との
自然同型は別途構成する。既存 DK の同値は `AlgebraicTopology/DoldKan/Equivalence.lean` にある。

N4 の `LinearSimplex` の成分 f_J は、k=|J|−1 として
`δf_J=(−1)^(k+1) Σ_r (−1)^r f_{J\{j_r}}` を満たす。
したがって `ε_k=(−1)^(k(k−1)/2)`、`t_J=ε_k f_J` が上の DK 方程式へ移す。
実際 `ε_k (−1)^(k+1)=ε_{k−1}`、`ε_k²=1`。k=0,1 では ε=1、k=2,3 では ε=−1。
濃度を保つ像では同じ ε が現れ、非単射成分は零なので、変換は全ての面・退化と可換である。
Hom の実装にはこの線形模型を再利用し、標準 chain map 模型との比較を明示する。
`LinearSimplex` は係数環の宇宙 u に収まり、ClosedCategory の Hom の宇宙と一致する。
coherent nerve と dg nerve の単体集合はともに `SSet.{max u v}` となる。

### C_Δ の合成と局所 Kan 性

対象は D の対象、通常の圏には `ClosedCategory R D`（閉次数零射の圏）を使う。
単体的 Hom は DK(L(H))。次数0の単体と閉次数零射の同値を豊穣と通常の圏の比較に使う。
`DGCategory` に任意の通常の `Category D` が既に付いているとは仮定しない。

原典の lax monoidal 構造は Alexander–Whitney の対角写像による。
後の射を g、前の射を f と書くと、成分での合成は

```
(g ⋆ f)_{j₀…jₖ} = Σ_{r=0}^k compose g_{j₀…jᵣ} f_{jᵣ…jₖ}.
```

AW の最初の因子が後の射、二番目が前の射である点を固定する。
N4 の f 座標では各項に `(−1)^(r(k−r))` が付く。
リポジトリの `eComp : Hom(x,y)⊗Hom(y,z) → Hom(x,z)` と通常順 compose の間の
Koszul 交換も追跡し、AW の因子を符号なしに入れ替えない。
chain map 性は Leibniz 則と隣接する切れ目の相殺、結合律は二つの切れ目での和の交換、
単位則は正次数の単位成分が零であることによる。
shuffle は正規化から積の正規化への逆向きの写像であり、AW と混同しない。
AW∘shuffle=id と chain homotopy は比較に使うが、新しい引用・公理にはしない。

N4 の線形模型との単体的な同型により、全ホーンの直接の線形充填を移して局所 Kan 性を得る。
一般の「単体的アーベル群は Kan」を未証明の仮定としては使わない。
その後 γ1 の instance を適用して `SimplicialNerve C_Δ` の quasicategory 性を得る。

### 比較写像の向きと符号

比較は HA Construction 1.3.1.16 と同じ向き
`Θ : SimplicialNerve C_Δ ⟶ dgNerve R D` とする。
逆向きの厳密な単体的射や全次数の同型は先に要求しない。
Mathlib の Path は包含方向で、内部座標1は点を含む合成面、座標0は点を欠く削除面である。
内部点の順序は降順に取る。I の内部点が m 個なら、その順序に対する立方体の基本 chain は
全 m! 個の最大増大列を置換符号で足したものである。
Θ の I 成分は、豊穣関手の Hom 写像でこの基本 chain を送った値とする。
N4 座標を直接評価する実装では各 m 単体の評価に ε_m を掛ける。

内部点 j より大きい内部点の個数を q とすると、基本 chain の境界の j 項は
`(−1)^q (合成面 − 削除面)`。I の j より大きい点は末尾を含めて q+1 個なので、
N0 の `(−1)^{#{k∈I:k>j}} (f_{I\{j}} − compose …)` と厳密に一致する。
合成面の基本 chain は右区間、左区間の順の shuffle で表し、AW の因子の順と合わせる。
退化では最大列の正規化 chain が潰れることを使って単体的自然性を示す。

頂点では対象を保ち、辺では同じ閉零射を取る。2単体では唯一の一次元 Path Hom の像 h が
`δh=compose f₁₂ f₀₁−f₀₂` を満たし、N1 の三角形のデータに一致する。
ε₁=1 なのでここに追加の符号はない。高次では一般に全単体の同型にはならない。

### 写像空間の比較と A3e への接続

標的の右 pinched Hom は N4 により上の DK(L(H)) と同型になる。
始域の右 pinched Hom については、coherent nerve の余単体的立方体模型 Q^• を使う。
`Q^• → Δ^•` が誘導する `ψ : DK(L(H)) → Sing_Q DK(L(H))` と Θ の写像空間への作用を比較し、
その合成を上の符号変換による同型に同定する。ψ が Kan 複体上でホモトピー同値となることを
局所的に証明し、Θ の写像空間への作用のホモトピー同値を得る。
始域の pinched Hom が単体的 Hom そのものと同型だとは仮定しない。

Core の現行 `IsFullyFaithful` は各 pinched Hom の射に実際の単体的ホモトピー逆を要求する。
弱同値や π₀ の全単射だけでこれを満たしたとは数えず、ホモトピー逆まで作って接続する。
Θ は頂点上で恒等なので本質的全射性が得られる。
A3e の `qCatEquivalenceOfFullyFaithfulEssentiallySurjective` は Core に実装済みである。
比較写像と各 pinched Hom の実際のホモトピー同値を完成させた後、
この判定に充満忠実性と頂点上恒等による本質的全射性を渡して `QCatEquivalence` を構成する。
比較写像・写像空間の比較・同値判定への接続が全て済むまでは、∞ 圏の同値の完成とは数えない。

現在地：γ1.5a の設計、γ1.5b の単体的圏と局所 Kan 性、γ1.5c の比較写像、
γ1.5d の写像空間の実際のホモトピー逆と quasicategory の同値が完了。
namespace `DoldKanComparison` の `homModule x y : SimplicialObject (ModuleCat.{u} R)` と
`homSpace x y : SSet.{u}` は N4 の線形解を全ての単調写像に関してまとめたもの。
`homSpaceLiftIso x y` は `SSet.uliftFunctor.{v,u}.obj (homSpace x y)` と
`DGNerve.pinchedHom R D x y` の自然同型であり、次数ごとの同値だけではない。
`homSpaceKan x y : SSet.KanComplex (homSpace x y)` は N4 の直接の線形充填から従う。
宇宙の持ち上げが Kan 性を反映する一般補題 `kanComplex_of_ulift` も証明した。
`degreeSign` は ε_k を二項係数で実装し、`degreeSign_differential` が微分の符号の変換、
`degreeSign_cut` が AW 合成での交差符号を与える。符号による作用は二度で恒等になる。
`homSpaceVertexCycleEquiv` は零単体と閉次数零元の同値、`closedHomVertexEquiv` は
`ClosedCategory R D` の射と零単体の同値である。合成との整合は
`closedStandardVertexEquiv_comp` によって単体的圏の構成へ接続する。
`standardSubmodule` は標準境界の独立な方程式を課した部分加群である。
`standardSimplexEquiv` は N4 の解とこの標準方程式の解との全次数の R 線形同値。
`standardPullback_val` は標準座標の引き戻しが有限集合の像による通常の作用と一致することを示す。
`standardModuleIso` は小さい N4 の単体的加群から `standardModule` への自然同型であり、
台単体集合の `homSpaceStandardIso` と `standardHomSpaceKan` も得られる。
標準方程式との符号変換と全ての退化との可換性は Lean で証明済み。
`connectiveHomComplex` は Mathlib の n↦−n の埋め込みに沿う smart truncation であり、
零次数と `zeroCycles` の同型、正次数と H^(−n) の同型を持つ。
`connectiveHomComplex_d_positive`・`connectiveHomComplex_d_zero` は、微分が符号を変えず
元の δ および閉元への因子分解に一致することを示す。
`doldKanHomModule` はこの複体に Mathlib の `Abelian.DoldKan.Γ` を適用した対象そのもの。
`doldKanHomNormalizationIso` はその正規化 Moore 複体と切断 Hom 複体の同型である。
`mooreNormalizedModuleIso` は Mathlib の正規化の各項を正の面の核の共通部分と同定する。
`standardMooreTermIso` により標準模型へ適用し、`standardMooreTopMap_mono` は正次数の
正規化から H^(−n) への最上位成分による評価が単射であることを示す。正規化された成分は
全体集合と零番目の面以外では零で、後者は前者の δ に等しい。
`normalizedLiftData` は最上位に z、零番目の面に δz を置く具体的な逆構成であり、
標準方程式と全ての正の面の消滅を満たす。`normalizedTopEval_surjective` により
最上位評価は全射でもあり、`normalizedTopEquiv` は線形同値となる。
`standardMoorePositiveIso x y n` は実際の Mathlib Moore 正規化の次数 n+1 の項と
H^(−(n+1)) との同型で、追加の閉性・充填の仮定はない。
`standardZeroEquiv` は標準零単体と閉次数零の元の R 線形同値であり、
`standardMooreZeroIso` は実際の Moore 正規化の零項と切断 Hom の零項との同型である。
`standardMoorePositiveIso_d` と `standardMooreZeroIso_d` により、各項の同型は微分と可換。
`standardNormalizationIso` は標準模型の実際の Moore 正規化と切断 Hom の複体の同型である。
`standardDoldKanModuleIso` は Dold–Kan 同値の unit と Γ の作用でこれを戻した自然同型、
`homModuleDoldKanIso` は N4 の線形単体的加群と実際の Mathlib Γ の自然同型である。
`homSpaceDoldKanIso` はその台単体集合の同型であり、全ての面・退化と可換である。
`doldKanHomSpaceKan` は N4 の線形充填をこの同型で移した Kan instance。
`doldKanHomPinchedIso` は宇宙を持ち上げた DK Hom と dg nerve の右 pinched Hom の同型である。
coherent nerve の写像空間との比較は、後述の `resolutionHomIso` と
`coherentPinchedStandardComparison_homotopyEquivalence` によって完成する。
対象・集約ビルドは3916件で成功し、公開524宣言の型と公理監査は標準三公理のみ。
正確な型・前提・公理監査は `scripts/audit_dold_kan_comparison.lean` に記録する。

`awData` は後の射の接頭部分と前の射の接尾部分を合成して全切断点で足す成分族の演算。
`awDataBilinear x y z n` はこの演算を
`LinearData R y z n →ₗ[R] LinearData R x y n →ₗ[R] LinearData R x z n` にまとめる。
`standardConstant` は閉零射の全ての退化をまとめた標準単体であり、一点成分はその閉零射、
二点以上の成分は零となる。`awData_unit_left`・`awData_unit_right` は、dg 単位の
定数単体が任意の成分族に対する両側単位であることを証明する。最小・最大切断点だけが残る。
`standardUnitMap x : 𝟙_ SSet.{u} ⟶ standardHomSpace x x` は、全ての面・退化との
可換性も持つ単位写像。これらは AW の標準方程式の保存を仮定せずに証明している。
`awData_assoc` は任意の三つの成分族についての結合律。二切断の依存対の同値
`AWIndex.cutPairEquiv` で二重和を移し、反復切断の集合の同定と dg 結合則を使う。
`awData_pullback` は全ての単調写像による引き戻しとの可換性であり、退化も含む。
集合上単射なら左右の切断の像を同定し、非単射なら各切断の少なくとも片側の
引き戻し成分が零となることを使う。ここに新しい標準方程式の仮定はない。

γ1.5b は完了。Hom の Mathlib Γ との同定と Kan 性、成分族上の AW の双線形性と
単位則・結合律・単体的自然性に加え、標準方程式の保存も証明済み。
`differential_awData_eq_standardRhs` は標準単体の AW 成分の微分が標準境界に等しいことを示す。
Leibniz 則から得る左右の削除和を `AWIndex.boundaryPairEquiv` で、削除後の切断と
二種類の対角に分ける。非対角は削除後の AW 項に一致し、対角は
`awDiagonal_sum_eq_zero` によって隣接切断どうしで符号を反転して相殺する。
`awData_mem_standard` は閉性の証明、`standardAW g f : StandardSimplex R x z n` は
追加仮定なしの標準単体の合成である。
`standardEnrichedCategory` は単位・合成・全豊穣則を備える構造である。
`closedStandardVertexEquiv` は閉零射と標準零単体の同値で、恒等射と合成を保つ。
`doldKanSimplicialCategory : SimplicialCategory (ClosedCategory R D)` が通常の圏との
整合性も備えた C_Δ の instance。豊穣 Hom は標準成分模型で実装し、
`doldKanSimplicialHomIso` により実際の Mathlib Γ の Hom と全単調写像について自然同型となる。
`doldKanSimplicialCategory_locallyKan` は全ての Hom の Kan instance。
`doldKanCoherentNerve : SSet.{max u v}` はこの C_Δ の coherent nerve であり、
`doldKanCoherentNerve_quasicategory` は γ1 の一般定理から従う。
前提は `[CommRing R] [DGCategory R D]` のみで、任意の通常の Category D は要求しない。
γ1.5c の比較写像と低次の一致、γ1.5d の写像空間の比較と同値の証明も完了。

γ1.5c は完了。`cubeFlag e` は任意の番号付け `e : Fin m ≃ T` に対して、
空集合から先頭 t 座標へ進む立方体の m 単体を作る。
`standardTopEval x y m` は標準 m 単体の全体集合の次数 −m の成分を取る線形写像。
`cubeEvaluation e φ` は全ての置換 σ の旗を φ で送り、最上位評価を置換符号で足した値である。
`descendingEnumeration` と `pathCubeMap` は有限内部点の降順の向きと native Path への包含を与え、
`coherentCubeComponent` は enriched functor の Hom 写像を通じて次数 −|S| の値を得る。
ここでは標準 DK 座標を使うため、N4 からの次数符号の変換は Hom の模型に含まれている。

`cubeFlag_face_swap` は隣接二座標の交換で同じ内部面が得られることを示す。
`cubeFlag_internal_sum_eq_zero` はその交換を固定点のない対合として、任意の可換加法群への
評価で内部面の符号付き和が零となることを証明する。二倍の消去や 2 の可逆性は使わない。
`cubeEvaluation_zero`・`cubeEvaluation_one` は零次・一次の旗の一意性による評価の計算。
`cubeFaceMap e i ε` は一つの座標を固定する面の包含。残りの座標は
`ULift (Fin n)` で番号付けし、元と同じ宇宙の単体集合を保つ。
`cubeFlag_boundary_sum` は任意の可換加法群で、全最大旗の交代境界を
座標1面−座標0面の交代和へ変換する。内部面の対合による相殺と、
先頭・末尾の座標を指定する置換の分解を使い、整数の係数のまま証明した。

`standardTopEval_d` は最上位評価の微分を面の最上位評価の交代和に送る。
`cubeEvaluation_succ_d` は `[CommRing R] [DGCategory R D]` の下で、
任意の `e : Fin (n+1) ≃ T` と
`φ : Coherent.cube T ⟶ standardHomSpace x y` に対し、次の等式を与える。
ここで `e₀ : Fin n ≃ ULift.{u} (Fin n)` は `Equiv.ulift.symm`。

```text
δ(cubeEvaluation e φ)
  = Σ i : Fin (n+1), (−1)^i •
      (cubeEvaluation e₀ (cubeFaceMap e i true ≫ φ)
       − cubeEvaluation e₀ (cubeFaceMap e i false ≫ φ)).
```

型は Hom の微分 `d (−↑(n+1)) (−↑n)` の等式であり、全ての正次元を含む。
`cubeEvaluation_zero_closed e φ : differential R (cubeEvaluation e φ) = 0`
が零次元の閉性を与える。

`cubeImageMap f` は座標の像による立方体の写像で、座標同値の移送と評価の可換性も証明した。
`erasedEnumeration e i : Fin m ≃ S.erase (e i).val` は一座標を飛ばした番号付け。
`pathCubeMap_face_zero` は座標0面の Path への写像が、この番号付けを通じて
一点削除した内部点集合の `pathCubeMap` を通ることを示す。
`cubeEvaluation_pathFace_zero` は同じ因子分解を立方体評価へ移す。
`erasedEnumeration_eq_descending` は元が降順なら削除後も標準の降順番号付けに等しいと示す。
`strictAnti_enumeration_card_filter` は降順の番号 i がその点より大きい点数に等しいことを示し、
座標境界の係数と dg nerve の係数の照合に使う。

`pathCubeMap_face_one` は座標1面の Path が、その点の左右の区間に制限した Path の
合成を通ることを示す。`coherentCube_face_one_apply` は任意の単体で、その像が
後半の像を第一引数、前半の像を第二引数とする `standardAW` に等しいことを示す。
前提は `[LinearOrder J] [CommRing R] [DGCategory R D]` と実際の豊穣関手
`s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D)`。

`standardTopEval_map_degenerate_zero` は標準 Hom への任意の射で退化単体の最上位評価が
零となることを示す。`standardComponent_nerve_zero_of_not_injOn` は順序 nerve の選んだ
頂点集合で頂点写像が非単射なら、その像の該当成分が零となることを示す。
`cubeEvaluation_restriction_zero` は座標を一つでも忘れた正次元の立方体の評価を零にする。
これらは標準 Hom への射の線形性を要求しない。

`standardTopEval_AW_restriction_zero_of_inversion` は座標の分割 `P : T → Prop` に対し、
番号付け `e : Fin (n+1) ≃ T` に `r < s`、`¬P (e r)`、`P (e s)` があれば、
P 座標への像を後の射、¬P 座標への像を前の射とする AW の最上位評価が零になることを示す。
`standardTopEval_AW_restriction_eq_term` は `P (e r) ↔ r.val < c.val` が全ての r で成立すれば、
AW の和には切断点 c の一項だけが残ることを示す。c が最初または最後の場合も含む。
前提は `[CommRing R] [DGCategory R D]` と各座標立方体からの実際の標準 Hom 写像。

`cubeSumEnumeration e f : Fin (p+q) ≃ A ⊕ B` は
`e : Fin p ≃ A`、`f : Fin q ≃ B` を順に連結する番号付け。
`cubeSumLeftMap`・`cubeSumRightMap` は和の座標集合から各因子への射影である。
`standardTopEval_AW_cubeSum e f ψ φ` は `[CommRing R] [DGCategory R D]` の下で、
`ψ : Coherent.cube A ⟶ standardHomSpace y z` と
`φ : Coherent.cube B ⟶ standardHomSpace x y` に対し、次を与える。

```text
topEval (p+q) (AW (ψ (projA (flag (e⊕f)))) (φ (projB (flag (e⊕f)))))
  = compose R (cubeFlagEvaluation e ψ) (cubeFlagEvaluation f φ).
```

両辺は次数 `−↑(p+q)` にあり、`p=0`・`q=0` も含む。
`awTerm_cubeSum_eq_comp` が境目の一項の評価、`awTerm_cubeSum_zero_of_bad_cut` が
他の切断点の消滅を与える。接頭・接尾の濃度と次数は `CubeBlockIndices` で明示する。
`cubeBlockPermutation σ τ` は各区間を保つ置換で、その符号は `sign σ * sign τ`。
`standardTopEval_AW_cubeSum_signed_sum` はこの二つの置換に関する AW 評価の符号付き二重和が
`compose R (cubeEvaluation e ψ) (cubeEvaluation f φ)` に等しいことを示す。

`cubeBlockPermutation_inversion_of_not_range` は区間を保たない全置換から逆転の組を取り出し、
`cubeBlockPermutation_sum` は像の外で零となる和を区間内置換の二重和へ再添字付けする。
`standardTopEval_AW_cubeSum_all_permutations` は、これを AW 評価の全置換の和に適用する。
`cubeAWCompositionMap ψ φ : Coherent.cube (A ⊕ B) ⟶ standardHomSpace x z` は
前の射・後の射の座標射影を Cartesian な積に組み、標準合成へ送る実際の単体集合の射。
`cubeEvaluation_AW_comp e f ψ φ` は次の等式を与える。

```text
cubeEvaluation (cubeSumEnumeration e f) (cubeAWCompositionMap ψ φ)
  = compose R (cubeEvaluation e ψ) (cubeEvaluation f φ).
```

前提は同じく `[CommRing R] [DGCategory R D]`、次数は `−↑(p+q)`、零次元も含む。
これで全最大旗の AW 評価の合成公式を得た。

`pathIntervalSet S c d` は元の有限内部点集合を新しい開区間へ制限した有限集合。
`pathIntervalCoordinateIso` は区間内の元の座標とこの有限集合の順序同型である。
`pathSplitCoordinateEquiv S j` は `S.erase j.val` を、後半の `pathIntervalSet S j.val.val b` と
前半の `pathIntervalSet S a j.val.val` の和へ分ける。元の点の値を保ち、濃度も加法的になる。
`pathSplitEnumeration_eq_descending` は左右の降順番号付けを後半、前半の順に連結した番号付けが
削除後の標準の降順番号付けに等しいことを示す。

`coherentCube_split_face` は、この座標同値を通して Path の実際の合成面の Hom 写像が
左右の `coherentCubeHom` の `cubeAWCompositionMap` に等しいと示す。
`cubeEvaluation_pathSplitFace` は任意の左右の番号付けで、合成面の評価が二つの評価の dg 合成に等しいと示す。
`cubeEvaluation_coherent_face_one_comp` は `[LinearOrder J] [CommRing R] [DGCategory R D]` と
実際の豊穣関手 s、`e : Fin (m+1) ≃ S`、`StrictAnti e`、座標 i の下で、
番号付き1面の評価と、後半・前半の `coherentCubeComponent` の通常順合成を `HEq` で同定する。
`S.erase (e i).val` の濃度と左右の内部点数の和を同定して向きを移すため、追加の符号はない。
`coherentCubeComponentAt s hab S k hk` は `hk : k = −↑S.card` により次数を指定した標準成分。
`coherentCubeCompositionAt s hab S j l hl` は `hl : l = 1−↑S.card` により終次数を指定した合成項。
`cubeEvaluation_coherent_face_zero_at`・`cubeEvaluation_coherent_face_one_at` は、それぞれの面の評価を
同じ次数の削除成分・合成項に通常の等号で同定する。

`coherentCubeComponentAt_d s hab S k l hk hl` は任意の有限内部点集合 S と
`hk : k = −↑S.card`、`hl : l = k+1` に対し次の式を与える。

```text
Hom.d k l (coherentCubeComponentAt s hab S k hk)
  = Σ j : S, (−1)^(#{t∈S : j<t}) •
      (coherentCubeCompositionAt s hab S j l _
       − coherentCubeComponentAt s hab (S.erase j) l _).
```

空の S も含み、この場合は閉零射の条件となる。
`coherentInteriorSet I a b` は有限頂点集合 I の開区間内の内部点集合で、
`card_coherentInteriorSet` が最小・最大の両端の下で内部点数+2=全頂点数を示す。
`coherentInterior_term_sign` は全頂点の右側の点数が内部点の右側の点数+1であることから、
dg nerve の符号付きの削除−合成を上の符号付きの合成−削除へ同定する。

`coherentSimplexData (s : doldKanCoherentNerve _⦋n⦌) : DGNerve.SimplexData R D n`
は各 coherent 単体の頂点と全斉次成分を持つ実際の台データ。
`coherentSimplexData_obj` は対象成分の一致、`coherentSimplexData_hom_heq` は各成分と
内部点の標準立方体評価との一致を示す。前提は `[CommRing R] [DGCategory R D]`。
`coherentVertexSet`・`coherentVertexInterior` は Fin の頂点集合を native な ULift の座標へ移し、
削除・左右切断・符号の点数を保つ。`coherentInteriorVertex_sum` は内部座標の和を元の有限頂点番号の和にし、
`coherentSimplexData_term_eq_interior` は既存 rhs の各項を内部点表示の微分項へ同定する。
`coherentSimplexData_equation s I a b k hI ha hb hk` が全ての有限頂点集合について、
既存の `DGNerve.Simplex.equation` と同じ微分方程式を証明する。追加の整合性・充填の仮定はない。

```lean
coherentSimplex {n : ℕ} (s : doldKanCoherentNerve _⦋n⦌) : DGNerve.Simplex R D n
```

各 coherent 単体から同次元の実際の dg 単体を得て、以下の自然性により
比較写像 `N^hc(C_Δ) ⟶ N_dg(C)` を構成した。頂点・辺・三角形での一致も証明済み。

有限頂点集合上で単射な場合の自然性は証明済み。
`pathCubeImageSet` と `pathCubeImageIso` は、選んだ有限内部点上で厳密単調な順序写像の
有限像と順序同型を作る。`pathCubeMap_image` は実際の native Path の像がこの座標同型を
通ることを示す。`coherentCubeHom_image` と `coherentCubeComponent_image_heq` は、
豊穣関手の引き戻しと降順の立方体評価にこの分解を移す。
`coherentInteriorSet_image` は、元の有限頂点集合上で単射な順序写像について、
内部点の像が像の頂点集合の内部点集合に等しいことを示す。

`coherentSimplexData_pullback_hom_of_inj` の前提は `[CommRing R] [DGCategory R D]`、
`s : doldKanCoherentNerve _⦋n⦌`、`α : Fin (m+1) →o Fin (n+1)`、有限頂点集合 I と
既存の hom の端点・次数の証明 `hI,ha,hb,hk`、および `hi : Set.InjOn α (I : Set _)`。
結論は次の等式である。

```lean
(coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s)).hom
  I a b k hI ha hb hk =
    ((coherentSimplexData s).pullback α).hom I a b k hI ha hb hk
```

単射性は I 上だけでよく、α が他の頂点を潰していても適用できる。
次数零・内部点のない場合も含む。

非単射な高次成分の自然性も証明済み。
`coherentInterior_collision_of_not_inj` は、最小・最大の端点を持つ三点以上の有限頂点集合で
順序写像が非単射なら、内部点の像が端点または別の内部点の像と重なることを示す。
`pathImageFlag_repeat` は、各旗で重複する点のうち後から加わるものの前後の頂点が
等しいことを示す。`standardTopEval_thin_nerve_repeat_zero` は薄い圏の nerve でこの反復を
退化と判定する。Path の既存の圏構造を使い、部分順序の instance を追加しない。
`cubeEvaluation_coherentImage_zero_of_endpoint`・
`cubeEvaluation_coherentImage_zero_of_collision` が全ての置換の旗の評価を零にする。

`coherentSimplexData_pullback_hom_of_not_inj` は上の `of_inj` と同じ
`s,α,I,a,b,k,hI,ha,hb,hk` に対して、前提を
`hi : ¬ Set.InjOn α (I : Set _)`、`hc : I.card ≠ 2` とした同じ hom の等式である。
`2 ≤ I.card` と hc から三点以上が従い、両側が零になる。任意の dg 圏に適用でき、
像の両端が一致する場合も含む。

`standardTopEval_collapsed_path` は端点が一致する Path の零単体を豊穣単位に同定し、
豊穣関手の単位保存と `standardZeroEval_unit` から dg 単位を得る。
`coherentSimplexData_pullback_hom_of_collapsed_pair` は非単射な二点集合についても
上と同じ hom の等式を証明する。これで既存の dg 引き戻しの三分岐が全てそろった。
`coherentSimplexData_pullback` と `coherentSimplex_pullback` は全単調写像での等式である。
前提は `[CommRing R] [DGCategory R D]` のみ。

```lean
coherentComparison : doldKanCoherentNerve (R := R) (D := D) ⟶ dgNerve R D

coherentSimplex_pullback {m n : ℕ} (s : doldKanCoherentNerve _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
  coherentSimplex ((SimplicialThickening.functor α.uliftMap).comp SSet s) =
    (coherentSimplex s).pullback α
```

`coherentComparison_obj` は全次元で頂点 a の対象を `s.obj (.mk (ULift.up a))` に同定する。
`coherentComparison_edgeHom` は全次元の異なる二頂点 a < b で、比較した辺の次数零成分が
`s.map` による二端点だけの定数 Path の零成分に等しいことを示す。
`singletonPathFlag hab t` は唯一の内部点 t を加える一次の旗で、その両端は
`singletonPathFlag_obj_zero`・`singletonPathFlag_obj_one` によって
`pathOfInterior hab ∅` と `pathOfInterior hab {t}` に等しい。
`coherentComparison_triangleHom` は実際の二単体の `triangleHom` がこの旗の像の
次数 −1 の最上位成分に等しいことを示す。三角形では t は一番の頂点であり、
旗は `{0,2} → {0,1,2}`、追加の負号はない。既存の `differential_triangleHom` により
`δh = f₁₂ ∘ f₀₁ − f₀₂` となる。これで γ1.5c の頂点・辺・二単体の検査を満たす。
γ1.5d の pinched Hom の実際の単体的ホモトピー同値と ∞ 圏の同値は、
後述の `ComparisonEquivalence.lean` で完成している。

### γ1.5d：比較射と端点の同定（完了）

`coherentConstant x n` は全ての対象を x、全ての Hom を dg 単位の定数単体に送る
実際の豊穣関手である。`coherentVertex x` はその零単体で、
`coherentComparison_vertex x` が比較像を `DGNerve.Simplex.vertex x` に等号で同定する。
`coherentVertex_reconstruct` は任意の coherent 零単体を唯一の対象から再構成し、
Hom の写像まで単位保存から一致させる。従って `coherentVertexEquiv` は全零単体と D の同値。
`coherentComparison_surjective_vertices` と `coherentComparison_essentiallySurjective` により、
A3e の本質的全射側は追加仮定なしに完了している。

```lean
coherentVertexEquiv : doldKanCoherentNerve (R := R) (D := D) _⦋0⦌ ≃ D
coherentComparison_essentiallySurjective : IsEssentiallySurjective
  (coherentComparison (R := R) (D := D))
coherentPinchedComparison (x y : D) :
  coherentPinchedHom (R := R) x y ⟶ DGNerve.pinchedHom R D x y
standardHomPinchedIso (x y : D) :
  SSet.uliftFunctor.{v,u}.obj (standardHomSpace (R := R) x y) ≅ DGNerve.pinchedHom R D x y
coherentPinchedStandardComparison (x y : D) :
  coherentPinchedHom (R := R) x y ⟶
    SSet.uliftFunctor.{v,u}.obj (standardHomSpace (R := R) x y)
```

前提は `[CommRing R] [DGCategory R D]` のみ。
`coherentPinchedHom` の端点は `coherentVertex x` と `coherentVertex y`。
`coherentPinchedSimplex` は端点の同一視の cast を台の単体に残さず、
比較写像の値そのものに pinched 条件を添える。比較射は全ての面・退化と可換である。
`coherentPinchedComparison_component_heq` は任意の非空有限集合 J について、N4 の回収成分を
`withLast J` の内部座標の降順立方体評価に同定する。
`coherentPinchedStandardComparison_component` はこれを標準 DK 座標で表し、
回収成分に `degreeSign (J.card−1)` を掛けたものに等しいと示す。
`coherentPinchedStandardComparison_comp` はこの射を `standardHomPinchedIso.hom` で戻すと
元の `coherentPinchedComparison` に等しいという、実際の単体集合の射の等式である。

逆向きの射は F1 の確定済みの最大頂点の構成を再利用する。
`standardHomToCoherentPinched x y` は、閉零射の圏の対象 x,y に対して
持ち上げた `standardHomSpace x y` から `coherentPinchedHom x y` への実際の単体集合の射。
台の単体は F1 の `coherentHomComparisonSimplex` そのものであり、
`coherentNerveVertex_eq_vertex` で端点を同定する。
`coherentHomComparisonSimplex_naturality` を使い、全ての面・退化との可換性も持つ。
この射の定義だけではホモトピー逆であることを主張しない。

```lean
standardHomToCoherentPinched (x y : ClosedCategory R D) :
  SSet.uliftFunctor.{v,u}.obj (standardHomSpace (R := R) (D := D) x y) ⟶
    coherentPinchedHom (R := R) (D := D) x y
```

`maximumFlagOrder a S e` は、a から追加した最終点への Path の旗の各頂点から、
最終点以外の最大の頂点を取る単調写像。`pathLastMaximumMap_cubeFlag` は F1 の実際の
`pathLastMaximumMap` の値をこの添字写像に同定する。
`maximumFlagOrder_le_iff` は最大値の上界を始点と既知の全内部点の上界で特徴づける。
後から加える点が先行する点以下なら最大頂点は繰り返し、
`cubeFlagEvaluation_maximum_zero_of_inversion` により最上位評価は零になる。
昇順で加える場合は、最大頂点が始点、各内部点を順に通り、厳密単調となる。

`cubeEvaluation_maximum` は全ての座標数 m、降順の番号付け `e : Fin m ≃ S`、
標準 n 単体 σ に対して、次の等式を証明する。前提は `[CommRing R] [DGCategory R D]` のみ。

```text
cubeEvaluation e (pathCubeMap ≫ pathLastMaximumMap a ≫ yonedaEquiv.symm σ)
  = degreeSign m • standardTopEval m
      (standardPullback (maximumFlagOrder a S (Fin.revPerm.trans e)) σ).
```

昇順でない全ての旗が零となり、唯一の昇順の旗だけが残る。
`revPerm_sign m` は反転の整数の置換符号が `degreeSign m = (−1)^(m choose 2)` に等しいことを
二要素の組の個数から証明する。零次元も同じ式に含み、二の可逆性は使わない。
`maximumFlagOrder_image` と `withLast_interior_source_image` により、昇順の旗の像は
選んだ元の頂点集合 J に等しい。`cubeEvaluation_withLast_maximum` はその像の同定を使い、
立方体評価を `degreeSign (J.card−1)` と元の標準単体の J 成分の積に同定する。
`cubeEvaluation_object_transport` と `coherentHomComparison_cubeEvaluation_heq` は
F1 の豊穣関手の端点の型の移送を通じて、この一般式を実際の比較単体の評価に移す。

`standardCoherentPinchedSimplex_linear_component` は、実際の逆向きの射と比較射を合成した
N4 回収成分が元の標準成分の次数符号倍であることを示す。標準座標へ戻すときに
同じ次数符号をもう一度掛けるため、二重作用が相殺する。
前提は `[CommRing R] [DGCategory R D]` のみで、全ての非空有限集合と零次元を含む。

```lean
standardHomToCoherentPinched_comp (x y : ClosedCategory R D) :
  standardHomToCoherentPinched (R := R) x y ≫
    coherentPinchedStandardComparison (R := R) (D := D) x y = 𝟙 _
```

これは全次数・全成分の等式から得た単体集合の射の厳密な等式であり、π₀ の計算に限らない。
片側の逆の性質は完了したが、これだけで二射をホモトピー同値とは数えない。
`coherentPinchedComparison_eq_pinchedHomMap` は固定端点の比較射を、Core の
`pinchedHomMap coherentComparison (coherentVertex x) (coherentVertex y)` の後に
`coherentComparison_vertex` による端点の等式の同型を合成した射に同定する。
`pinchedEndpointIso_hom_val` はこの移送が台の単体を変えないことを全次数で示す。
従って、定義の異なる二つの射を単に同じ働きをする射として扱うのでなく、射の等式で接続している。

`coherentComparison_fullyFaithful_iff` は任意の coherent 頂点を `coherentVertexEquiv` で戻し、
全 dg 対象間の固定端点の比較射が実際のホモトピー逆を持つことと Core の充満忠実性を同値にする。
さらに `standardHomPinchedIso` に沿う移送を使い、標準座標での判定を得る。
具体的な判定の前提は `[CommRing R] [DGCategory R D]` のみで、必要な三つの写像空間の Kan 性は
既存の局所 Kan 性と自然同型から導く。

```lean
coherentComparison_fullyFaithful_iff_standard :
  IsFullyFaithful (coherentComparison (R := R) (D := D)) ↔
    ∀ x y : D,
      IsSimplicialHomotopyEquivalence (coherentPinchedStandardComparison (R := R) x y)
```

これは充満忠実性の判定への移送である。右辺の実際のホモトピー逆は、
最後の解像の随伴による転置の証明で構成する。
反対側の合成のホモトピーの構成には、F1 の確定済みの `CoherentResolutionFlag n d` を使う。
`resolutionFlagPath F t` は各段の有限集合の持ち上げた像に追加した最終点を加えた native Path。
始点は F.start であり、`resolutionFlagPathFunctor F` はその包含による d 単体である。
`resolutionFlagPath_maximum` は、その最後以外の最大頂点が `F.maxAt t` に等しいことを示す。
`resolutionFlagPath_pullback` は、任意の添字写像 α での旗の正規化した引き戻しが、
選んだ元の Path の `F.maxAt (α 0)` からの末尾に等しいという式である。退化も含む。

`coherentPinched_source_obj`・`coherentPinched_target_obj` は実際の pinched 条件から
各端点の対象を固定する。これを使って各旗での標準 Hom の値を定義する。

```lean
resolutionHomValue {x y : ClosedCategory R D} {n d : ℕ}
    (s : coherentPinchedHom (R := R) (D := D) x y _⦋n⦌)
    (F : CoherentResolutionFlag n d) : StandardSimplex R (D := D) x y d

resolutionHomValue_standard (σ : StandardSimplex R (D := D) x y n)
    (F : CoherentResolutionFlag n d) :
  resolutionHomValue (standardCoherentPinchedSimplex σ) F =
    standardPullback ⟨F.maxAt, F.maxAt_monotone⟩ σ
```

前提は `[CommRing R] [DGCategory R D]` のみ。
最後の式は全次数・全旗での等式であり、標準 Hom からの射が補助解像の最大元への射影を
通じた値を取ることを示す。`resolutionHomValue_pullback` は任意の pinched 単体 s を固定し、
旗の次数を変える全ての単調写像 α について
`standardPullback α (resolutionHomValue s F) = resolutionHomValue s (F.pullback α)` を証明する。
α が先頭頂点を変える場合も、Path を先頭部分と末尾に分解し、pinched 条件によって
先頭部分の値を単位に同定する。豊穣関手の合成保存と AW の右単位則で先頭部分を消す。
これにより、固定した s に対して実際の単体集合の射が得られる。

```lean
resolutionHomMap {x y : ClosedCategory R D} {n : ℕ}
    (s : coherentPinchedHom (R := R) (D := D) x y _⦋n⦌) :
  coherentResolutionSimplex.{u} n ⟶ standardHomSpace (R := R) (D := D) x y

resolutionHomMap_standard (σ : StandardSimplex R (D := D) x y n) :
  resolutionHomMap (standardCoherentPinchedSimplex σ) =
    coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ
```

ここでも前提は `[CommRing R] [DGCategory R D]` のみ。最後の式は単体集合の射の等式である。
`resolutionFlagPath_pushforward` は旗の押し出しが最終点固定延長による Path の像に等しいことを
証明する。単射でない写像による頂点の重複も含む。`resolutionHomValue_reindex` は
豊穣関手の前合成と端点の移送をこの一致へ接続し、pinched 単体の次数変更との整合を与える。

```lean
resolutionHomMap_reindex {x y : ClosedCategory R D} {m n : ℕ}
    (s : coherentPinchedHom (R := R) (D := D) x y _⦋n⦌) (β : ⦋m⦌ ⟶ ⦋n⦌) :
  resolutionHomMap ((coherentPinchedHom (R := R) (D := D) x y).map β.op s) =
    coherentResolutionMap β.toOrderHom ≫ resolutionHomMap s
```

前提は同じく `[CommRing R] [DGCategory R D]` のみ。これで旗の次数と pinched 単体の次数の
両方について自然性が揃った。

`resolutionEndpointEquiv` は台の coherent 単体を変えず、F1 と本比較の端点の表示を合わせる。
`resolutionFlagPathFunctor_eq_pathFlag` は native Path の二つの集合表示を等式で同定する。
これらを使う `resolutionHomMap_eq_flagMap` により、実際の評価を F1 の確定済みの
`coherentPinchedFlagMap` に厳密に同定する。F1 の両側の逆を持つ構成を適用すると、
解像上の射からの逆構成が得られる。

```lean
resolutionHomEquiv (x y : ClosedCategory R D) (n : ℕ) :
  coherentPinchedHom (R := R) (D := D) x y _⦋n⦌ ≃
    (coherentResolutionSimplex.{u} n ⟶ standardHomSpace (R := R) (D := D) x y)
```

前提は `[CommRing R] [DGCategory R D]` のみ。
`resolutionHomEquiv_apply` は順方向が `resolutionHomMap` そのものであることを示す。
`resolutionHomMap_equiv_symm` と `resolutionHomEquiv_symm_map` は実際の評価の両側の回収則、
`resolutionHomEquiv_symm_reindex` は逆構成の面・退化との整合である。
この固定次数の同値と自然性だけでは、標準 Hom との比較射のホモトピー同値とは数えない。
`resolutionHomIso` はこの同値と自然性を実際の単体集合の同型にまとめる。
F1 の確定済みの解像の右随伴を使い、二段の ULift で Hom と coherent nerve の宇宙を合わせる。

```lean
resolutionHomIso (x y : ClosedCategory R D) :
  coherentPinchedHom (R := R) (D := D) x y ≅
    SSet.uliftFunctor.{v, u}.obj
      (coherentResolutionRightAdjoint.obj (standardHomSpace (R := R) (D := D) x y))

standardHomToCoherentPinched_resolutionHomIso (x y : ClosedCategory R D) :
  standardHomToCoherentPinched (R := R) (D := D) x y ≫ (resolutionHomIso x y).hom =
    SSet.uliftFunctor.{v, u}.map
      (coherentResolutionComparison (standardHomSpace (R := R) (D := D) x y))
```

前提は引き続き `[CommRing R] [DGCategory R D]` のみ。
可換式は全次数の旗での評価から証明した射の等式である。
`simplicialHomotopyEquivalence_split_iff` は Kan 複体間の二射 f、g が `f ≫ g = 𝟙 _` を
満たすとき、一方の実際のホモトピー同値性が他方の同値性と同値であることを示す。
この判定と解像の同型により、元の dg 比較射について次を得る。

```lean
coherentComparison_fullyFaithful_iff_resolution :
  IsFullyFaithful (coherentComparison (R := R) (D := D)) ↔
    ∀ x y : D, IsSimplicialHomotopyEquivalence (SSet.uliftFunctor.{v, u}.map
      (coherentResolutionComparison (standardHomSpace (R := R) (D := D) x y)))
```

右随伴側の必要な Kan 性は `resolutionHomIso` の逆射によって実際の pinched Hom から導く。
この判定の右辺は、最後の `resolutionComparison_homotopyEquivalence` によって証明済み。
充満忠実性・本質的全射性を合わせた A3e による ∞ 圏の同値も構成済み。
標準単体ごとの解像の変形だけでは次数間の自然性を持つホモトピーとみなさない。
一般の解像の射影については、F1 の確定済みの境界の貼り合わせとセル帰納法の定理を使う。

低次の基底は厳密な同型まで証明済み。
`resolutionFlag_sets_eq_interval_of_le_one` は `n ≤ 1` のとき、任意次数の旗 F について
`F.sets t = Finset.Icc F.start (F.maxAt t)` を示す。頂点が高々二つなので区間内の点は
いずれかの端点であり、旗に必ず含まれる。
`resolutionProjection_section_of_le_one` はこの式を使い、射影の後に区間の切断を取る合成が
厳密に恒等となることを示す。従って次の同型を得る。

```lean
resolutionProjectionIsoOfLeOne {n : ℕ} (hn : n ≤ 1) :
  coherentResolutionSimplex.{u} n ≅ (Δ[n] : SSet.{u})

standardCoherentPinchedEquivOfLeOne (x y : ClosedCategory R D) {n : ℕ} (hn : n ≤ 1) :
  StandardSimplex R (D := D) x y n ≃
    coherentPinchedHom (R := R) (D := D) x y _⦋n⦌
```

二つ目の同値の順方向は `standardCoherentPinchedSimplex`、逆方向は
`coherentPinchedStandardComparison` の実際の n 単体上の作用から ULift を戻したもの。
前提は `[CommRing R] [DGCategory R D]` と `n ≤ 1` のみである。
`coherentPinchedStandardComparison_section_of_le_one` は反対側の合成も n 単体上で恒等となる
等式であり、π₀ の計算だけではない。一般次数での片側の回収則は
`standardCoherentPinchedSimplex_comparison` で公開する。
一般次数のホモトピー逆には、最後の解像の随伴による転置の証明を使う。

高次の解像の相対的な変形のため、`normalizeResolutionFlag S hS h0` を構成した。
増大する非空な有限集合族 S の最初の集合の最大元 c を始点とし、各段を c 以上に制限する。
`normalizeResolutionFlag_maxAt` は各段の最大元が変わらないこと、
`normalizeResolutionFlag_pullback` は正規化が全ての添字の引き戻しと可換であることを示す。
既存の旗の集合族を正規化すると元の旗に戻る。

選んだ頂点 i と単位区間の単体 t に対し、`resolutionInsertVertex F i t` は
`S r := if t r = 0 then F.sets r else insert i (F.sets r)` を正規化した旗である。
始点は `if t 0 = 0 then F.start else max i F.start`、各段の最大元は
`if t r = 0 then F.maxAt r else max i (F.maxAt r)`。
`resolutionInsertVertex_pullback` は F と t の同時の引き戻しに対する自然性を証明する。
新しい切断点が、元の変形の始点と元の旗の引き戻しの始点の両方以上であることが要点となる。
これにより、面で切り落とされた点を変形が後から戻すことを防ぐ。

```lean
resolutionInsertHomotopy {n : ℕ} (i : Fin (n + 1)) :
  SSet.Homotopy (𝟙 (coherentResolutionSimplex.{u} n))
    (coherentResolutionMap (resolutionUpperVertexMap i))
```

ここで `resolutionUpperVertexMap i` は `k ↦ max i k`。
零端点は既存の旗の正規化の回収、一端点は追加・切断後の集合とこの頂点写像の直接像の一致から得る。
`resolutionInsertVertex_no_new_vertices` は変形後の各集合の元が元の元か i に限られることを示す。
従って i 以外の欠落頂点を補わず、区間全体を追加する変形とは異なる相対的な構成に使える。
ホーンの部分複体への制限は以下の通り。これらの局所的な補題は独立の補助 API であり、
γ1.5d の完成には最後の一般の解像の射影と随伴の転置を使う。
これは補助解像上のホモトピーであり、比較射の反対側の合成のホモトピーそのものではない。

`resolutionHorn i` は `∃ j, j ≠ i ∧ j ∉ F.support` を満たす旗の部分複体。
旗の引き戻しは台を増やさないため、同じ欠落頂点を証人として面・退化を保つ。
この定義は Λ[n,i] に対応する台による明示模型であり、左 Kan 拡張をホーンに適用した値との
同定はまだ含まない。`resolutionInsertVertex_mem_horn` は i 以外の欠落頂点が追加されないことを
使って変形中の全単体の所属を保つ。全体の変形を持ち上げ、次を構成した。

```lean
resolutionHornInsertHomotopy {n : ℕ} (i : Fin (n + 1)) :
  SSet.Homotopy (𝟙 (resolutionHorn.{u} i).toSSet) (resolutionHornUpperMap i)
```

`resolutionHornUpperMap_ι` と `resolutionHornInsertHomotopyMap_ι` は、制限した射とホモトピーが
包含後に全体の構成と厳密に一致することを示す。両端の計算も同じホーン内で行っている。

i ≠ 0 なら `resolutionPositiveFace n := coherentResolutionFace (Finset.univ.erase 0)` は
欠落頂点0を証人として `resolutionHorn i` に含まれる。
最大値の直接像の点は i 以上なので、`resolutionHornUpperMap i` の値もこの面に入る。
`resolutionHornToPositiveFace i hi` がこの持ち上げであり、射の因子分解を得る。

```lean
resolutionHornUpperMap_factor_positiveFace {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
  resolutionHornToPositiveFace.{u} i hi ≫
      SSet.Subcomplex.homOfLE (resolutionPositiveFace_le_horn i hi) =
    resolutionHornUpperMap i
```

これはホーン内の恒等射を面を通る射まで変形した構成である。
この局所的な縮約の方法自体を i = 0 へ延長する補題は実装していない。

Kan 標的での位相的な比較には、次の既存のホモトピー同値性による条件を使う。

```lean
IsKanPrecompositionEquivalence (f : A ⟶ B) : Prop :=
  ∀ (K : SSet.{u}) [SSet.KanComplex K],
    IsSimplicialHomotopyEquivalence ((MonoidalClosed.pre f).app K)
```

`functorIsoPrecompositionOfHomotopyKan` は任意の `SSet.Homotopy f g` が、Kan 標的 K への
前合成の二射の可逆な二胞体を与えることを示す。内部 Hom が Kan であることを使うため、
元の A・B の Kan 性やホモトピーの頂点の固定性は要求しない。
従ってこの条件はホモトピー不変で、合成と二対六則を満たす。
これはモデル構造の存在の引用を追加せずに補助解像を比較するための条件であり、
最終的な dg 比較射に要求する実際のホモトピー逆は変更しない。

i ≠ 0 のとき同じ一頂点の追加は零頂点を除く旗の面も保つ。
`resolutionPositiveFaceInsertHomotopy` はその面の恒等射から最大値の自己写像へのホモトピー。
ホーンから面へ移して包含で戻る合成と、その逆順の合成はそれぞれの最大値の自己写像に等しい。
両方とも恒等射から変形されるので二対六則により次を得る。

```lean
resolutionPositiveFace_inclusion_isKanPrecompositionEquivalence {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
  IsKanPrecompositionEquivalence
    (SSet.Subcomplex.homOfLE (resolutionPositiveFace_le_horn.{u} i hi))
```

この主張は任意の Kan 標的への写像空間の実際のホモトピー同値性である。
標準単体側にも `standardUpperVertexHomotopy i` を構成した。
その台の射は解像の区間の切断、変形、最大元の射影の合成で、各単体の各頂点での値は
`if t r = 0 then σ r else max i (σ r)`。
`StandardUpperStable A i` は標準単体の部分複体 A が変形全体の像を含む条件である。
`standardSubcomplexUpperHomotopy` はこの条件のもとで同じ部分複体内のホモトピーを与える。
`standardHorn_upper_stable` は i 以外の欠落頂点の保存でホーンの安定性を証明し、
`standardPositiveFace_upper_stable` は i ≠ 0 の場合の零頂点を除く面の安定性を証明する。
両側の変形と面を通る因子分解により、標準ホーン側の面の包含も Kan 標的の比較を満たす。

`resolutionHornProjection i` は旗の各段の最大元の列を取る射を標準ホーンへ制限したもの。
旗の台で欠ける頂点は最大元の列でも欠けるので、全ての i で定義できる。
`resolutionHornProjection_positiveFace_square` は零頂点を除く面の F1 の射影と
ホーンの射影が両側の包含で可換するという厳密な射の等式である。
確定済みの面の射影の同値性、標準側の面の包含の同値性を合成し、解像側の包含を消去すると次を得る。

```lean
resolutionHornProjection_isKanPrecompositionEquivalence_of_ne_zero {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
  IsKanPrecompositionEquivalence (resolutionHornProjection.{u} i)
```

これは任意の Kan 標的 K に対して、標準ホーンから K への内部 Hom から、旗で定義した
ホーンの模型から K への内部 Hom への前合成が実際の単体的ホモトピー逆を持つことを意味する。
標的 K の Kan 性と i ≠ 0 以外の充填・比較の仮定を追加していない。
この局所ホーンの証明の i = 0 への延長と左 Kan 拡張との直接の同定は未実装。
γ1.5d の完成には、次の F1 の一般の射影の定理を使うため、これらを追加の仮定にはしない。


### γ1.5d の完成：解像の随伴によるホモトピー逆

F を `coherentResolution`、G をその右随伴、p_A を自然な射影 F(A) → A、
η_K を `coherentResolutionComparison K` と書く。F1 の確定済みの
`coherentResolutionProjectionAll_isPrecompositionEquivalence A` により、全ての A について
p_A による前合成は任意の quasicategory への内部 Hom の同値である。
これは境界での比較、単射と余極限の保存、セル帰納法から証明された定理を使う。

`resolutionCylinderMap A : F(A ⊗ Δ[1]) → F(A) ⊗ Δ[1]` は、第一射影の F による像と、
p の後の第二射影を組にした射である。p の自然性により両方の端点を厳密に保つ。
従って `resolutionHomotopyTranspose` は F(A) → K の二射の実際のホモトピーを、
随伴による A → G(K) の二射の実際のホモトピーへ移す。積と F の厳密な可換性は仮定しない。

K が Kan のとき、余単位 ε_K : F(G(K)) → K を p_G(K) に沿って降下し、
g : G(K) → K と `p_G(K) ≫ g ~ ε_K` を選ぶ。
このホモトピーを転置すると、自然性と随伴の計算則により `g ≫ η_K ~ 𝟙 _` となる。
一方、F(η_K) で前合成すると `p_K ≫ η_K ≫ g ~ p_K`。
p_K による前合成の同値は Kan 標的 K へのホモトピーを反映するため、
`η_K ≫ g ~ 𝟙 _` も得る。降下と反映には内部 Hom の同値の本質的全射性と
逆同値の単位の成分を使い、最後は実際の単体的ホモトピーへ戻す。

```lean
resolutionComparison_homotopyEquivalence (K : SSet.{u}) [SSet.KanComplex K] :
  IsSimplicialHomotopyEquivalence (coherentResolutionComparison K)
```

右随伴 G(K) の Kan 性はこの定理の前提ではない。
`uliftHomotopy` と `ulift_homotopyEquivalence` により、この実際のホモトピー逆を
coherent nerve の宇宙 max(u,v) へ移せる。標準 Hom の Kan 性と既存の可換式を合わせて
元の比較射の写像空間の同値性と充満忠実性を得る。

```lean
coherentPinchedStandardComparison_homotopyEquivalence (x y : ClosedCategory R D) :
  IsSimplicialHomotopyEquivalence
    (coherentPinchedStandardComparison (R := R) (D := D) x y)

coherentPinchedComparison_homotopyEquivalence (x y : D) :
  IsSimplicialHomotopyEquivalence (coherentPinchedComparison (R := R) (D := D) x y)

coherentComparison_fullyFaithful :
  IsFullyFaithful (coherentComparison (R := R) (D := D))

coherentComparisonEquivalence :
  QCatEquivalence (doldKanCoherentNerve (R := R) (D := D)) (dgNerve R D)

coherentComparisonEquivalence_hom :
  (coherentComparisonEquivalence (R := R) (D := D)).hom =
    coherentComparison (R := R) (D := D)

coherentComparison_isQCatEquivalence :
  IsQCatEquivalence (coherentComparison (R := R) (D := D))
```

これらの前提は `[CommRing R] [DGCategory R D]` のみ。
A3e に実際の比較射の充満忠実性と既存の本質的全射性を渡したもので、
選択した同値の順方向は頂点・辺・三角形で計算済みの比較射そのものである。
`coherentPinchedStandardComparison_oppositeHomotopy x y` は、既存の標準比較射の後に
既存の `standardHomToCoherentPinched` を合成した射と恒等射の実際のホモトピーを与える。
逆順の合成の厳密な恒等式も保持しており、同値の存在だけに置き換えていない。

γ1.5a〜d の要求には未完了項目はない。E2b 自体の Alg_E の豊穣化・忘却 ∞ 関手の構成と
γ3 の極限・余極限の比較は後続の別工程であり、この同値だけで完成したとは数えない。


## γ3：homotopy 極限・余極限と ∞ 極限・余極限

担当は N。正本は `formalization-plans/e-infinity-algebras.md` §3 と
`formalization-plans/foundations.md` §1。γ1.5 の完了後に続けて担当し、
𝒮（F2）・Sp（L9）・E2b の三者が共有する比較を作る。

担当と着手順（foundations.md §1 の決定）：γ1.5 の後に N が γ3 を担当する。
目標は homotopy 極限・余極限と ∞ 極限・余極限の比較（HTT 4.2.4.1 型）であり、
まず Kan 複体の単体的モデル圏の cofibrant-fibrant 部分圏を対象とする。
初段は通常の小圏の strict な図式について、有限積・fibration 引き戻し・塔の極限を扱う。
豊穣 Hom の標準比較 q_x と coherent な錐の比較を証明し、𝒮（F2）、Sp（L9）、
E2b が再利用できる形で公開する。余極限側は後続工程とし、極限側の部分成果で完了とはしない。
E2b の具体的適用は E2a の完了後に行う。

現在は γ3a と、γ3b の検出・比較ファイバー・重み付き end・表現可能な標準比較射、
strict な図式・錐の coherent nerve での表示、fibration の塔の重み付き end の Kan 性、
塔と一脚が fibration の cospan の実際の標準比較 κ・q_x のホモトピー同値性まで実装。
離散図式の比較、𝒮 の空積、Kan 値図式の end の一般の Kan 性も実装済み。
Kan 値図式の end の同値不変性も証明済み。一般の coherent な錐との比較、
𝒮 の残りの極限と Sp への適用は未実装。
当面は通常の小圏で添字付けた strict な図式の極限側を扱い、余極限と一般の図式の比較は後続に保持する。

### γ3a：原典と今回の限定形

[HTT Theorem 4.2.4.1](https://arxiv.org/pdf/math/0608040) は局所 Kan な単体的圏の
homotopy 余極限と coherent nerve の余極限の対応である。今回はその双対である極限形を使う。
単体的モデル圏 A に適用するときは cofibrant-fibrant 対象の充満単体的部分圏 A° を用いる。
モデル構造の存在を新しい引用・公理として導入せず、第一段階は必要な充填と比較を直接証明する。

原典の対応は次の通り。

| 役割 | 原典 |
| --- | --- |
| 局所 Kan な C の coherent nerve が ∞ 圏 | [Kerodon Theorem 2.4.5.1](https://kerodon.net/tag/00LH)（γ1） |
| 単体的 Hom と coherent nerve の写像空間 | [Kerodon Theorem 4.6.7.5、Remark 4.6.7.9](https://kerodon.net/tag/01LA)。リポジトリの右 pinched の向きとの移送を含む |
| 表現可能な空間値関手による極限の検出 | [Kerodon Proposition 7.4.1.22](https://kerodon.net/tag/039L) |
| 空間の極限と切断空間 | [Kerodon Proposition 7.4.1.6](https://kerodon.net/tag/05QS)、[Construction 7.5.1.1](https://kerodon.net/tag/03A0) |
| strict 極限から homotopy 極限への比較 | [Kerodon Proposition 7.5.3.12](https://kerodon.net/tag/03B1)。isofibrant 図式の場合 |
| Kan 図式の homotopy 極限錐 | [Kerodon Definition 7.5.4.1](https://kerodon.net/tag/03B6) |
| 今回の局所 Kan な単体的圏への限定形 | [Kerodon Corollary 7.5.4.6](https://kerodon.net/tag/03BB) |

§2.4.5 は quasicategory 性の入力であり、写像空間の比較そのものは §4.6.7 を使う。
通常の strict 極限だけでは homotopy 極限錐になるとは限らない点は
[Kerodon Warning 7.5.4.3](https://kerodon.net/tag/03B8) に対応する。

**限定した主張。** C を各 sHom が Kan である単体的圏、I を小さい通常の圏とする。
F : I → C を strict な図式、λ を頂点 L から F への strict な錐とする。
ここで必要な strict 極限は単体的豊穣を含む極限であり、全ての x : C について

```
θ_x : sHom_C(x,L) ≅ lim_{i ∈ I} sHom_C(x,F(i))
```

が SSet の自然な同型で、λ の成分による射に一致することを要求する。
台の通常の圏での極限であるという条件だけでは、この同型を省略しない。
H_x(i) := sHom_C(x,F(i)) と置き、さらに strict な極限から homotopy 極限への
標準の比較が全ての x について同値であると仮定する。

```
κ_x : lim_I H_x → holim_I H_x
q_x := κ_x ∘ θ_x : sHom_C(x,L) → holim_I H_x
```

このとき λ が定める図式
`N(I)◁ → N^hc(C)` は極限図式、すなわちリポジトリの `IsLimitCone` を満たす。
より一般に、豊穣 strict 極限を前提にせずとも、この錐から得られる q_x が全ての x で
Kan 複体のホモトピー同値なら同じ結論を得る。strict 極限の限定形はこれを θ_x と κ_x で検証する。

錐の左頂点の向きは `Δ[0] ⋆ N(I)` とする。I に始対象を付加した圏の nerve との同定を
明示して strict な錐から `JoinCone` を構成し、二つを定義的に等しいとは扱わない。
局所 Kan 性だけから全ての strict 極限の保存を結論しない。

### γ3b：pinched 写像空間による証明の界面

Z := N^hc(C)、p := N^hc(F)、λ̂ : JoinCone p とする。
Core の定義では `IsLimitCone λ̂ = IsTerminalVertex (X := sliceOver p) λ̂`。
A3d の `isTerminalVertex_iff_pinchedHom_isContractibleKan` によって、
全ての錐 c : JoinCone p について、錐の ∞ 圏の `pinchedHom c λ̂` が可縮であることへ帰着する。

c の頂点を x とすると、c は homotopy coherent な錐の点 b_c を `holim_I H_x` に与える。
γ3b で構成する本体は、端点と錐のデータに整合する比較

```
pinchedHom_{sliceOver p}(c,λ̂) ≃ hofib_{b_c}(q_x)
```

である。q_x が同値なら右辺は可縮であり、A3d から λ̂ の極限性を得る。
可縮性を要求する対象はこのファイバーである。`lim_I H_x` 自体の可縮性を要求すると、
例えば一点図式の一般の Hom まで可縮にするため、極限の主張を変えてしまう。
また任意の c は coherent な錐であり、strict な錐の点だけに制限しない。

実装では holim の Kan 模型を選び、q_x を Kan fibration で置き換えた後の strict fiber を使える。
q_x 自体の fibration 性を証明した場合だけ、置き換え前の strict fiber と同一視する。
可縮性は `IsContractibleKan`（零次元を含む全境界の充填）で証明し、π₀ の全単射で代用しない。
各 i での sHom と pinched Hom の同値だけを並べても図式全体の比較にはならないので、
錐の成分・添字圏の射・高次の整合性を含む比較を証明する。

holim の候補は通常の図式の同値に不変な Kan 模型とする。
Bousfield–Kan 型なら `∫_i Fun(N(I/i), H_x(i))` という重み付き end を使い、
`N(I/i)` の i に関する作用も含めて定義する。
strict limit をこの重み付き end に写す比較 κ_x と、coherent な錐の点 b_c の対応が証明対象である。
既存の F1 の空間・写像空間の API を再利用するが、原典の定理を Lean の仮定に追加しない。

### γ3b の実装済み界面（本体の比較は未完了）

`HomotopyLimits/Detection.lean` と `ComparisonFiber.lean` に検出と最後の推論を置く。
namespace は `SerrePositivity.InfinityCategories.HomotopyLimits`。

| 公開 API | 型と役割 |
| --- | --- |
| `isLimitCone_iff_conePinchedHom_isContractibleKan c` | `[Quasicategory X]` の下で `IsLimitCone c ↔ ∀ d : JoinCone p, IsContractibleKan (pinchedHom (X := sliceOver p) d c)` |
| `comparisonFiber q b` | `vertexFiber (equivalencePathReplacementMap q) b`。置換前の strict fiber とは区別する |
| `comparisonFiber_isContractibleKan_of_homotopyEquivalence q hq b` | A・B が Kan、q : A → B が実際のホモトピー同値なら `IsContractibleKan (comparisonFiber q b)` |
| `isLimitCone_of_comparisonFiber_homotopyEquivalence` | 全ての coherent な錐 d で、同値な比較射 q_d の fiber と錐の pinched Hom の実際のホモトピー同値を与えれば `IsLimitCone c` |

最後の API は比較射とその同値の**構成を入力として要求する**。
これだけを HTT 4.2.4.1 の双対の証明完成とは数えない。

`WeightedSections.lean`・`WeightedFunctor.lean` では一般の共変な重み W と図式 H に対して
`weightedSections W H := ∫_i Fun(W(i),H(i))` を Mathlib の豊穣 end で構成した。
次の普遍性は Kan 性なしで成立する。

```lean
weightedSectionsHomEquiv (W H : I ⥤ SSet.{u}) (A : SSet.{u}) :
  (A ⟶ weightedSections W H) ≃ (W ⊗ (Functor.const I).obj A ⟶ H)

weightedSectionsAdjunction (W : I ⥤ SSet.{u}) :
  weightedParameterFunctor W ⊣ weightedSectionsFunctor W
```

ここで `weightedParameterFunctor W` は `A ↦ (i ↦ W(i) × A)`。
`weightedSectionsFunctor_preservesLimits` は通常の単体集合の極限の保存であり、
一般の図式の strict 極限が Kan であることや ∞ 極限性の証明ではない。

`BousfieldKan.lean` の `bousfieldKanWeight I := Over.mapFunctor I ⋙ nerveFunctor` は
共変な i ↦ N(I/i) を実際に定義する。`bousfieldKanHolim H` はこの重みの end。
`bousfieldKanLimitComparison H : limit H → bousfieldKanHolim H` は重みを忘れる標準射であり、
`bousfieldKanLimitComparison_evaluation H i` により恒等射 `i → i` での評価は極限射影になる。
`bousfieldKanLimitComparison_naturality η` は図式に関する厳密な自然性。
一般の添字圏における Kan 値図式の end の Kan 性と対象ごとの同値に対する不変性は
後節で証明済み。coherent な錐の頂点 fiber との比較は未証明。
離散図式の比較の同型性は下記で証明済み。

`RepresentableComparison.lean` は strict な錐から実際の射 q_x を作る。
前提は `I : Type u`、`[SmallCategory I]`、`C : Type v`、`[Category.{u} C]`、
`[SimplicialCategory C]`。以下の構成に局所 Kan 性は不要。

```lean
representableHomotopyLimitComparison (c : Cone F) (x : C) :
  SimplicialCategory.sHom x c.pt ⟶ bousfieldKanHolim (simplicialHomDiagram F x)

representableHomotopyLimitComparison_factorization (c : Cone F) (x : C)
    (h : IsLimit (simplicialHomCone c x)) :
  representableHomotopyLimitComparison c x =
    (enrichedLimitHomIso c x h).hom ≫
      bousfieldKanLimitComparison (simplicialHomDiagram F x)
```

`representableHomotopyLimitComparison_naturality c f` は始対象の射 f に関する反変な自然性。
局所 Kan 性を仮定すれば `simplicialHomDiagram_obj_kanComplex` が各成分の Kan 性を与える。
ただし具体的な coherent な錐 c から end の点 b_c を作ることと、
錐の pinched Hom を `comparisonFiber q_x b_c` と比較することは未完了。
strict な錐から q_x を構成できたことを、その比較まで証明したとは数えない。
公開747宣言の正確な型・全前提・依存公理は `scripts/audit_homotopy_limits.lean` が正本。

### strict な図式・錐の coherent 表示

`StrictNerveMaps.lean` は、Hom の宇宙 u と対象の宇宙 v が異なる場合も、
図式の始域を `SSet.uliftFunctor.{v,u}.obj (nerve I)` に統一する。
対象と射を持ち上げた圏 `AsSmall.{v} I` の nerve との **SSet の同型** `nerveAsSmallIso I` を構成し、
元の図式を後合成して F1 の既存の `nerveToCoherent C` に渡す。
圏同値だけを持ち上げた nerve の同型として扱う構成ではない。

```lean
strictCoherentDiagram (F : I ⥤ C) :
  (SSet.uliftFunctor.{v,u}).obj (nerve I) ⟶ SimplicialNerve C

strictCoherentCone (c : Cone F) : JoinCone (strictCoherentDiagram F)

strictCoherentCone_vertex (c : Cone F) :
  (strictCoherentCone c).vertex = coherentNerveVertex c.pt
```

前提は `I : Type u`、`[SmallCategory I]`、`C : Type v`、`[Category.{u} C]`、
`[SimplicialCategory C]` のみ。局所 Kan 性や錐の極限性は構成に不要。
`StrictCones.lean` は `WithInitial (AsSmall.{v} I)` から C への実際の通常の関手を作り、
その始対象の nerve の錐を元の添字圏上へ制限する。
`strictCoherentConeMap_inr` は元の図式上での厳密な固定条件、
`strictCoherentConeMap_inl` は左頂点の厳密な表示である。

`StrictConeLegs.lean` の `strictCoherentConeLeg c i` は、右因子の頂点 i で制限した後、
`pointJoinStdSimplexIso 0` の逆射で Δ[1] からの射に正規化した脚。
`strictCoherentConeLeg_eq` は次の **実際の辺の等式** を証明する。

```lean
strictCoherentConeLeg c i = SSet.yonedaEquiv.symm
  ((nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (c.π.app i)))
```

`strictCoherentDiagram_precomp G F` は通常の添字圏の関手による図式の制限への自然性。
これは strict な錐の表示とその成分を確定したものであり、一般の coherent な錐を strict に
直せることや `IsLimitCone (strictCoherentCone c)` を示したものではない。
γ3b ではこの具体的な λ̂ を、既存の q_x と全ての coherent な錐の写像空間の比較へ接続する。

### 離散図式の比較と三つの strict 極限の Kan 性

`TerminalWeight.lean` は、図式の圏の終対象である重み W に対して、任意の strict 極限錐の
`weightedConeComparison W c` が同型であることを証明する。重みの変数を忘れる直積の射影の
同型、極限の普遍性、重み付き end の普遍性を合成し、実際の比較射に一致することを検証した。

`DiscreteComparison.lean` は離散圏の over 圏の対象・射と nerve の全次数の単体の一意性から、
重み `bousfieldKanWeight (Discrete J)` の厳密な終対象性を証明する。
したがって任意の `H : Discrete J ⥤ SSet.{u}` で、成分の Kan 性や添字の有限性なしに

```lean
bousfieldKanLimitComparison_discrete_isIso H : IsIso (bousfieldKanLimitComparison H)
bousfieldKanLimitComparison_discrete_homotopyEquivalence H :
  IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H)
```

が成り立つ。`RepresentableProducts.lean` の
`representableHomotopyLimitComparison_discrete_isIso c x h` と
`representableHomotopyLimitComparison_discrete_homotopyEquivalence c x h` は、
離散添字の錐と `h : IsLimit (simplicialHomCone c x)` から、実際の q_x の同型性と
ホモトピー同値性を与える。この計算だけで非空の積の ∞ 極限性を証明したとは数えない。

`TowerExtension.lean` の `exists_tower_extension` は、任意の射 j に対して、
各遷移が j の持ち上げ性を持つとき零段の指定された延長を全段に整合的に延長する。
`hasLiftingProperty_towerLimitπ_zero` は極限の零段への射影にも同じ持ち上げ性を移す。
各段で独立な延長を選んで塔の整合性を省略する構成ではない。

`KanLimits.lean` の公開結果は次の通り。モデル構造の存在や弱同値を仮定しない。
Fibration は Mathlib の単体集合の全ホーンの持ち上げ性による既存クラス。

| 宣言 | 正確な対象と前提 |
| --- | --- |
| `discreteLimit_kanComplex H` | `H : Discrete J ⥤ SSet.{u}`、全ての H(i) が Kan なら `KanComplex (limit H)`。空積を含む |
| `bousfieldKanHolim_discrete_kanComplex H` | 同じ前提で `KanComplex (bousfieldKanHolim H)` |
| `pullback_kanComplex_of_fibration p q` | `p : E → B` が Fibration、`q : D → B`、D が Kan なら `KanComplex (pullback p q)` |
| `towerLimit_kanComplex H` | `H : ℕᵒᵖ ⥤ SSet.{u}`、H(0) が Kan、全ての隣接遷移が Fibration なら `KanComplex (limit H)` |
| `towerLimitπ_zero_fibration H` | 隣接遷移の Fibration 性だけから `Fibration (limit.π H (Opposite.op 0))` |

### fibration の塔の重み付き end（実装済み）

通常の小圏で添字付けた end の規約では添字と係数の単体のサイズを u にそろえるため、
可算塔の添字には `AsSmall.{u} ℕᵒᵖ` を使う。
`TowerDiagramExtension.lean` は、始域も変化する図式の射 j : A → B に対して、
零段の指定された延長を保ちながら、各後続段の j と標的の遷移の間の持ち上げ性で自然変換を延長する。
`exists_resized_tower_diagram_extension` はこの構成を持ち上げた添字へ移す。

`WeightedTowerKan.lean` は任意の重み `W : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}` と図式 H に対して
次を証明する。重み W の Kan 性・可縮性は要求しない。

| 宣言 | 前提と結論 |
| --- | --- |
| `weightedSections_tower_projection_fibration W H` | H の全隣接遷移が Fibration なら、`weightedSectionsπ W H (AsSmall.up.obj (Opposite.op 0))` が Fibration。H(0) の Kan 性は不要 |
| `weightedSections_tower_kanComplex W H` | 加えて H(0) が Kan なら `KanComplex (weightedSections W H)` |
| `bousfieldKanHolim_tower_kanComplex H` | `H : ℕᵒᵖ ⥤ SSet.{u}`、H(0) が Kan、全隣接遷移が Fibration なら `KanComplex (bousfieldKanHolim ((AsSmall.down : AsSmall.{u} ℕᵒᵖ ⥤ ℕᵒᵖ) ⋙ H))` |

証明は end のホーンをパラメーター付き自然変換として表示し、
重みとホーン包含の直積の anodyne 性を各段の相対的な持ち上げに渡す。
塔の標準比較 κ_x の同値性は後述の重みの比較で別に証明する。
一般の図式の end の Kan 性は未完了。

`WeightedRestriction.lean` は重みの射 j : W → W' に対して実際の前合成
`weightedSectionsPre j H : weightedSections W' H → weightedSections W H` を定義する。
その内部 Hom への成分、任意のパラメーターでの uncurry との整合性、恒等・合成則、
`weightedConeComparison W' c ≫ weightedSectionsPre j H = weightedConeComparison W c`
を証明する。

`exists_resized_tower_extension_of_anodyne j hj a` は、H(0) の Kan 性と隣接遷移の Fibration 性の下で、
成分ごとに anodyne な j に沿って a : A → H を自然変換として延長する。
`WeightedTowerRestriction.lean` の `weightedSectionsPre_tower_exists_section` は、
制限先の end 自体をパラメーターにして、この延長から次の厳密な切断を構成する。

```lean
∃ s : weightedSections W H ⟶ weightedSections W' H,
  s ≫ weightedSectionsPre j H = 𝟙 (weightedSections W H)
```

前提は j の全成分の anodyne 性、H(0) の Kan 性と隣接遷移の Fibration 性。
`WeightedCorner.lean` は j とパラメーターの単射の pushout-product を図式の圏で作り、
評価関手による pushout の保存から各成分の anodyne 性を証明する。
`WeightedTowerTrivialFibration.lean` はこの相対的な延長を全境界に適用し、
制限の trivial Kan fibration 性と実際の単体的ホモトピー同値性を証明する。

```lean
weightedSectionsPre_tower_trivialKanFibration
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    TrivialKanFibration (weightedSectionsPre j H)
weightedSectionsPre_tower_homotopyEquivalence
    {W W' H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre j H)
```

この結果は任意の二つの重みの成分ごとに anodyne な比較を扱う。
塔の標準比較 κ_x に適用する具体的な重みの比較は次節に記す。
coherent な錐の写像空間の導来 fiber 比較は未完了。

### 塔の標準比較（κ と q_x は実装済み）

`ConeWeight.lean` は W(i) = N(I/i)、U(i) = Δ[0] に対して
V(i) = N(WithInitial(I/i)) を厳密な関手 `bousfieldKanConeWeight I` として構成する。
`initialExtensionFunctor` の恒等・合成則も等式として証明し、擬関手の同型で代用しない。
`bousfieldKanConeWeightInclusion : W → V` は元の over 圏の包含、
`bousfieldKanConeWeightPoint : U → V` は新しい始対象の頂点の包含である。
後者の全成分は `nervePoint_leftAnodyne` により anodyne。

```lean
bousfieldKanConeWeightPoint_tower_trivialKanFibration
    (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    TrivialKanFibration (weightedSectionsPre bousfieldKanConeWeightPoint H)
```

`ConeWeightComparison.lean` は任意の strict な錐 c について二つの厳密な合成式を証明する。
V の比較射の後で W に制限すると `bousfieldKanConeComparison c`、
U に制限すると `weightedConeComparison U c` に一致する。
前者は `bousfieldKanConeComparison_factorization`、
後者は `bousfieldKanConeWeightComparison_point` である。

```lean
bousfieldKanConeWeightComparison_tower_homotopyEquivalence
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c)
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence
      (weightedConeComparison (bousfieldKanConeWeight (AsSmall.{u} ℕᵒᵖ)) c)
```

U は図式の圏の終対象であるため、その比較射は同型である。
V → U の end の制限のホモトピー同値性と二対三則で上の定理を得る。
c.pt の Kan 性は U の end との同型から導き、前提に追加しない。
`NerveOpposite.lean` は `(nerve C).op ≅ nerve Cᵒᵖ` を射列の反転と逆反転から構成し、
頂点包含と通常の関手に関する自然性を証明する。
終対象の頂点包含の right anodyne 性も、反対圏の始対象の定理から導く。
`NerveInitialComparison.lean` は始対象を保つ関手の nerve が単射なら left anodyne であることを、
始対象からの錐による矢の retract として証明する。反転同型で終対象側の right anodyne 性を得る。

`ConeWeightAnodyne.lean` では W → V の単射性と共通の終対象を確認する。
I/i の恒等射の対象は始対象の付加後も終対象であるため、この包含は各成分で right anodyne、
従って anodyne となる。I 自体の始対象・終対象は要求しない。
`bousfieldKanConeWeightInclusion_tower_trivialKanFibration` はこの包含による end の制限の
trivial Kan fibration 性を証明する。二つの同値を合成して実際の κ の同値性が得られる。

```lean
bousfieldKanLimitComparison_tower_homotopyEquivalence
    (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H)
```

`bousfieldKanConeComparison_tower_homotopyEquivalence c hc` は同じ仮定で任意の極限錐 c を扱う。
c.pt の Kan 性は一点重みの end との同型から導出する。
豊穣極限の Hom 図式へ適用した実際の q_x についても、次を公開する。

```lean
representableHomotopyLimitComparison_tower_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)
```

この型では x の Hom 図式に必要な Kan 性と fibration 性を直接要求し、
C 全体の局所 Kan 性で省略しない。通常の圏の極限性だけでは Hom 図式の極限性を代用できない。
一般の coherent な錐の写像空間との比較は引き続き未完了であり、
これらの κ と q_x の同値性だけでは `IsLimitCone (strictCoherentCone c)` の証明にはならない。

### cospan の標準比較と一脚の fibration 性への準備

`CospanDiagramExtension.lean` の `exists_cospan_diagram_extension` は中央の延長を固定し、
左右の持ち上げ問題を解いて自然変換を作る。`exists_resized_cospan_diagram_extension` は
添字を AsSmall.{u} WalkingCospan に持ち上げた版である。
`exists_resized_cospan_extension_of_anodyne` は中央の Kan 性と両脚の Fibration 性から、
成分ごとに anodyne な全ての自然変換に沿う延長を構成する。

`WeightedExtensions.lean` は次の延長性 hH を入力に、任意の重みの end の Kan 性、
成分ごとの anodyne な重みの制限の trivial Kan fibration 性とホモトピー同値性を証明する。

```lean
∀ {A B : I ⥤ SSet.{u}} (j : A ⟶ B),
  (∀ i, anodyneExtensions (j.app i)) → ∀ a : A ⟶ H, ∃ b : B ⟶ H, j ≫ b = a
```

`BousfieldKanComparison.lean` はこの明示的な延長性の下で、任意の極限錐の比較と
選択された極限の実際の κ のホモトピー同値性を証明する。
この hH は定理の入力であり、任意の Kan 図式について証明済みとはしない。
`CospanComparison.lean` は hH を上の相対的な持ち上げから実際に構成して次を公開する。

```lean
bousfieldKanLimitComparison_cospan_homotopyEquivalence
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inr))] :
    IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H)
representableHomotopyLimitComparison_cospan_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))]
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inr))] :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)
```

`weightedSections_cospan_kanComplex` と `weightedSectionsPre_cospan_trivialKanFibration` も
同じ H の前提で任意の重みを扱う。`bousfieldKanConeComparison_cospan_homotopyEquivalence`
は選択された極限に限らず任意の極限錐 c を扱い、c.pt の Kan 性は前提に追加しない。

一脚だけの fibration 性には、成分ごとの anodyne 性だけを同じ証明へ渡すことはできない。
`CospanRightCorner.lean` は j : A → B の右成分を先に延長するための中央の境界射

```
cospanRightCornerMap j : A(one) ⨿_{A(right)} B(right) → B(one)
```

を構成する。`exists_cospan_extension_of_rightCorner` は、この境界射と右成分の
終対象射に対する持ち上げ性、および左成分の左脚に対する持ち上げ性から延長する。
係数の宇宙へ持ち上げた具体的な版は次である。

```lean
exists_resized_cospan_extension_of_rightCorner
    {A B H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : A ⟶ B)
    (hl : anodyneExtensions (j.app (AsSmall.up.obj .left)))
    (hr : anodyneExtensions (j.app (AsSmall.up.obj .right)))
    (h₀ : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (a : A ⟶ H) : ∃ b : B ⟶ H, j ≫ b = a
```

右脚の fibration 性は不要だが、中央の相対境界の anodyne 性 h₀ を入力に要求する。
ホーンの直積に対する h₀ は次の定理で検証する。重みの制限と境界を同時に固定する
pushout-product の h₀ は後述の交換同型で元の重みの相対境界へ帰着する。
元の重みの相対境界と一脚での κ の同値性は後述の実際の比較で証明した。
coherent な錐の pinched Hom との比較と 𝒮・Sp の ∞ 引き戻しへの適用は未完了。
両脚が fibration の比較だけで、要求された引き戻しの ∞ 普遍性を完成とは数えない。

### 一脚だけが fibration の cospan の end の Kan 性（実装済み）

`WeightMapMono.lean` は、対象上で単射な忠実関手の nerve の単射性を証明する。
添字の射 f が Mono なら `Over.map f` は対象上で単射で、射の左成分を保つため忠実である。
従って `bousfieldKanWeight_map_mono f` は重みの遷移の Mono 性を与える。

`CospanTensorCorner.lean` は重み W の右脚が単射のとき、
`cospanRightCornerMap (W ◁ const.map f)` を W の右脚と f の pushout-product と同定する。
f が anodyne ならこの相対境界も anodyne であり、前節の一脚の相対延長が使える。
この定理は通常の cospan と AsSmall による持ち上げの両方で公開する。

```lean
weightedSections_cospan_leftFibration_kanComplex
    (W H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [Mono (W.map (AsSmall.up.map WalkingCospan.Hom.inr))]
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    KanComplex (weightedSections W H)
bousfieldKanHolim_cospan_leftFibration_kanComplex
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    KanComplex (bousfieldKanHolim H)
```

証明は W とホーン包含の直積に沿ってパラメーター付き自然変換を延長する。
Bousfield–Kan 重みでは添字の右脚が単射なので、必要な重みの右脚の単射性も実際に証明済み。
右脚の fibration 性や追加の比較仮定は不要。
これは比較先の Kan 性の定理である。標準比較 κ の同値性は後述の
`CospanSingleFibrationComparison.lean` で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の ∞ 引き戻しへの適用も未完了。

### 相対境界と pushout-product の交換（実装済み）

`CospanCornerTensor.lean` は重みの射 j : W → W' とパラメーターの射 f : A → B について、
中央の相対境界を取る操作と pushout-product を作る操作の間の交換同型を構成する。

```
K := W(one) ⨿_{W(right)} W'(right)
k := cospanRightCornerMap (AsSmall.up ◁ j) : K → W'(one)
P := weightedCorner j f
Q := cornerTensorProduct j f  -- k と f の pushout-product
cornerTensorIso j f : Q.pt ≅ domain(cospanRightCornerMap (AsSmall.up ◁ P.ι))
```

`tensorRightCornerPushout` は K の pushout の直積による保存。
`cornerTensorMap` は K×B を P の中央と右成分の相対 pushout へ写す射である。
`cornerTensorComparison` と `cornerTensorReverse` は二通りの pushout の間の射で、
両合成が恒等であることを全ての生成成分で証明して `cornerTensorIso` を得る。
`cornerTensorComparison_fac` は同型の順射の後で相対境界射を適用すると Q.ι に等しい式。
交換同型とこの可換性自体には、f の単射性も j の anodyne 性も要求しない。

```lean
rightCorner_weightedCorner_anodyne
    {W W' : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    anodyneExtensions (cospanRightCornerMap
      (Functor.whiskerLeft AsSmall.up (weightedCorner j f).ι))
```

`CospanSingleFibrationRestriction.lean` はこの交換を全ての境界に適用する。
重みの左右の成分と中央の相対境界を一脚の相対延長に渡すことで、次を証明する。

```lean
weightedSectionsPre_cospan_leftFibration_trivialKanFibration
    {W W' H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (j : W ⟶ W')
    (hj : ∀ i, anodyneExtensions (j.app i))
    (hk : anodyneExtensions (cospanRightCornerMap (Functor.whiskerLeft AsSmall.up j)))
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    TrivialKanFibration (weightedSectionsPre j H)
```

`weightedSectionsPre_cospan_leftFibration_homotopyEquivalence` は同じ前提に加え、
W と W' の右脚の Mono 性を要求して両 end の Kan 性を証明し、実際のホモトピー同値性を得る。
入力 hk は具体的な標準重みで検証すべき元の相対境界の anodyne 性であり、
境界付きの pushout-product に対する条件を別途仮定する必要はなくなった。
元の重みでの hk と一脚での κ の同値性は後述の実際の比較で証明した。
coherent な錐の写像空間との比較と 𝒮・Sp の ∞ 引き戻しへの適用は未完了。

### 一脚の fibration 性での一点側の比較（実装済み）

`ConeWeightPointCorner.lean` は対象上で単射な忠実関手 F について、
`nerveMap (WithInitial.map F)` の Mono 性を証明する。
従って添字の単射 f に対して補助重みの遷移 `bousfieldKanConeWeight I` は Mono であり、
新しい始対象を保つ単射なので left anodyne、従って anodyne でもある。
`bousfieldKanConeWeight_map_mono` と `bousfieldKanConeWeight_map_anodyne` がこの主張である。

`cospanRightCorner_anodyne_of_sourceRightIso j hB` は始域の右脚が同型なら、
pushout の右包含の同型性を使って相対境界を終域の右脚と同型の合成で表す。
定値一点 U と補助重み V の包含に適用すると、
`bousfieldKanConeWeightPoint_cospan_corner_anodyne` は元の相対境界の anodyne 性を証明する。
これは追加入力ではなく、実際の標準重みについて検証した定理である。

`CospanSingleFibrationPointComparison.lean` は次を公開する。

```lean
bousfieldKanConeWeightPoint_cospan_leftFibration_trivialKanFibration
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    TrivialKanFibration (weightedSectionsPre bousfieldKanConeWeightPoint H)
bousfieldKanConeWeightComparison_cospan_leftFibration_homotopyEquivalence
    (H : AsSmall.{u} WalkingCospan ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj .one))]
    [KanComplex (H.obj (AsSmall.up.obj .right))]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (c : Cone H) (hc : IsLimit c) :
    IsSimplicialHomotopyEquivalence
      (weightedConeComparison (bousfieldKanConeWeight (AsSmall.{u} WalkingCospan)) c)
```

`bousfieldKanConeWeight_cospan_leftFibration_kanComplex` は同じ H の前提で補助 end の Kan 性。
一点側の制限の後で比較射を合成すると終対象重み U の比較同型になるので、二対三則で同値性を得る。
c.pt の Kan 性は一点重みの end との同型から導く。
図式の右脚の fibration 性と、未証明の重みの比較仮定は要求しない。
元の重み W → V の相対境界とその制限、一脚の場合の κ 全体も後述の実際の比較で証明した。
coherent な錐の写像空間との比較、𝒮・Sp の適用は継続中。

### 元の重みの右脚と相対錐の anodyne 性（接続は未完了）

`NerveTerminalExtension.lean` は対象上で単射な忠実関手 F : C → D について、
C に始対象、D に終対象 t があり、t が F の対象の像にないとき、nerveMap F の anodyne 性を証明する。
C に新しい終対象を付加すると、元の包含は始対象を保ち、D への拡張は終対象を保つ。
両方の nerve の単射性を確認し、left と right の anodyne 性を合成する。
この証明はモデル構造や弱同値の判定を新しい引用として要求しない。

`CospanOverRight.lean` では、walking cospan の右端に入る射が可逆であることを確認する。
一般に全ての構造射が可逆な over 圏では恒等射の対象は始対象になる。
非可逆な単射 f への後合成は、終域の恒等射の対象を像に含まないので上の分解が使える。
AsSmall への持ち上げと右脚の単射性・非可逆性を確認して、実際の重みの遷移に適用する。

```lean
bousfieldKanWeight_cospan_inr_anodyne :
  anodyneExtensions ((bousfieldKanWeight (AsSmall.{u} WalkingCospan)).map
    (AsSmall.up.map WalkingCospan.Hom.inr))
```

`RelativeConeAnodyne.lean` は点の境界と全ての正次元ホーンの pushout-join を、
標準単体の join の同型で一つ高いホーンに移す。最後の外側ホーンも許す。
`relativePointSliceUnderMap_fibration` は元の射の Kan fibration 性から相対 coslice の
Kan fibration 性を得る。始域・終域の Kan 性は要求しない。
これを anodyne な部分複体の包含に適用し、相対的な錐の anodyne 性を証明する。

```lean
joinUnion_pointBoundary_anodyne {B : SSet.{u}} (B₀ : B.Subcomplex)
    (hB : anodyneExtensions B₀.ι) :
    anodyneExtensions (joinUnion (boundary.{u} 0) B₀).ι
bousfieldKanWeight_cospan_inr_relativeCone_anodyne :
  anodyneExtensions (joinUnion (boundary.{u} 0)
    (Subcomplex.range ((bousfieldKanWeight (AsSmall.{u} WalkingCospan)).map
      (AsSmall.up.map WalkingCospan.Hom.inr)))).ι
```

後者は実際の重みの遷移を像の包含と始域の同型で同定した結果である。
この相対錐の単体集合と `cospanRightCornerMap` で作った元の重み W → V の相対境界との
同型による同定は後述の `PointJoinCorner`・`InitialNerveCorner` で実装した。
coherent な錐の写像空間との比較、𝒮・Sp の残りの ∞ 極限は未完了。

### WithInitial の nerve の切断と元の圏の部分（次数ごとの構成）

以下では `C : Type u` と `[SmallCategory C]` を前提とする。関手の標的 D も同じ宇宙の小圏とする。

`InitialNerveCut.lean` は新しい始対象を 0、元の対象を 1 に送るタグを定義する。
WithInitial の射はタグを増加させるので、射列 F のタグは単調写像になる。
その零の初区間の逆像に既存の `Join.pullCut` を使い、新しい始対象の頂点数を定める。

```lean
initialNerveCut {n : ℕ} (F : ComposableArrows (WithInitial C) n) : ℕ
initialNerveCut_le F : initialNerveCut F ≤ n + 1
initialNerve_lt_cut_iff F (i : Fin (n + 1)) :
  i.val < initialNerveCut F ↔ F.obj i = WithInitial.star
initialNerveCut_precomp {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (F : (nerve (WithInitial C)) _⦋n⦌) :
  initialNerveCut ((nerve (WithInitial C)).map α.op F) =
    Join.pullCut α.toOrderHom (initialNerveCut F)
```

`initialNerveCut_map` は元の圏の任意の関手の WithInitial への拡張が切断を保つ式。
元の圏の包含後の射列の切断は零、新しい始対象で一定の射列の切断は n+1 である。
対象の等号判定や元の圏の非空性は使わない。

`InitialNerveOldPart.lean` は新しい始対象でない対象と、それらの間の射を元の圏へ戻す。
`initialNerveOldMap_id` と `initialNerveOldMap_comp` により、この操作は関手になる。

```lean
initialNerveOldFunctor {J : Type v} [Category.{w} J]
    (F : J ⥤ WithInitial C) (h : ∀ i, F.obj i ≠ .star) : J ⥤ C
```

対象と射の包含後の等式は `initialNerveOldFunctor_obj` と `initialNerveOldFunctor_map`。
端点の等式による移送を eqToHom で明示する。

`InitialNerveTail.lean` は切断以後の区間を制限し、元の圏の後半の射列を構成する。

```lean
initialNerveTail {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : initialNerveCut F ≤ n) : ComposableArrows C (n - initialNerveCut F)
initialNerveJoinSimplex {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n
```

後半が非空なら `initialNerveTail`、空なら補った空単体を使い、元の圏の対象を選ばない。
`initialNerveTail_obj`・`initialNerveTail_map` は復元した後半の対象と射を元の射列と同定し、
`initialNerveJoinSimplex_cut` は構成したデータの切断を元の切断と同定する。
これらの次数ごとの構成の単体的自然性と逆関係は、後述の `InitialJoinIso.lean` で証明した。
相対錐と WithInitial の標準境界の同定と一脚での κ は、以下の実際の比較で証明した。
既存の始対象の錐の射との一致、coherent な錐の写像空間との比較、𝒮・Sp の適用は継続中。

`AugmentedNerve.lean` は補った空単体を含む nerve の評価を提供する。
C : Type u、[SmallCategory C] の下で、

```lean
augNerveObj {r : ℕ} (τ : Join.augObj (nerve C) r) (i : Fin r) : C
augNerveMap {r : ℕ} (τ : Join.augObj (nerve C) r)
    {i j : Fin r} (h : i ≤ j) : augNerveObj τ i ⟶ augNerveObj τ j
```

を定義し、恒等射・合成の保存と任意の順序写像に沿う再添字付けを証明した。
`augNerveObj_augMap` は対象の等式、`augNerveMap_augMap` はその等式による
端点の移送を含む射の等式。頂点数が零なら Fin 0 の添字で処理し、対象を選ばない。

`InitialJoinChain.lean` は逆向きの次数ごとの構成を提供する。

```lean
initialJoinChain {n : ℕ} (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    ComposableArrows (WithInitial C) n
initialJoinChain_star_iff {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (n + 1)) :
    (initialJoinChain s).obj i = WithInitial.star ↔ i.val < s.1.val
initialNerveCut_initialJoinChain {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    initialNerveCut (initialJoinChain s) = s.1.val
```

前半の頂点を新しい始対象、後半を元の射列の対象にし、始対象からの射の一意性と
`augNerveMap_comp` から関手法則を証明する。`initialJoinObj_star`・`initialJoinObj_of` で
端点の移送を明示する。切断が元に戻ることまで検証済みである。
この次数ごとの構成から単体集合の同型への拡張は、以下の三ファイルで証明した。
相対錐と標準境界の同定、一脚の場合の κ 全体は以下で実装した。
γ3b の主比較、𝒮・Sp の適用は継続中。

`InitialJoinNaturality.lean` は任意の順序写像に対する後半の添字の可換性を証明し、
対象の等式と射の HEq を介して射列の厳密な自然性を得る。

```lean
initialJoinChain_simplexMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    initialJoinChain (Join.simplexMap Δ[0] (nerve C) α.toOrderHom s) =
      (nerve (WithInitial C)).map α.op (initialJoinChain s)
initialJoinNerveMap (C : Type u) [SmallCategory C] :
    join (Δ[0] : SSet.{u}) (nerve C) ⟶ nerve (WithInitial C)
```

`InitialJoinRetraction.lean` は復元した後半の対象・射と元の射列の式を使う。
空の後半も含め、分解して戻す向きの厳密な逆関係を証明した。
`InitialJoinIso.lean` は比較後の射列から切断と後半の全対象・全射を読み戻して単射性を証明し、
もう一方の逆関係と分解の自然性を導く。

```lean
initialJoinChain_initialNerveJoinSimplex {n : ℕ}
    (F : ComposableArrows (WithInitial C) n) :
    initialJoinChain (initialNerveJoinSimplex F) = F
initialNerveJoinSimplex_initialJoinChain {n : ℕ}
    (s : Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    initialNerveJoinSimplex (initialJoinChain s) = s
initialJoinNerveIso (C : Type u) [SmallCategory C] :
    join (Δ[0] : SSet.{u}) (nerve C) ≅ nerve (WithInitial C)
```

前提は小さい圏であることだけであり、C の非空性・Kan 性や関手の忠実性は要求しない。
同型の順方向は `initialJoinNerveMap`、逆方向は `initialNerveJoinMap`。
この同型と両端の包含・元の圏の関手との可換性は以下で証明した。
既存の始対象の錐の射との一致はこの定理群では使わず、未完了として残す。
相対錐と標準境界の同定、一脚の場合の κ 全体は以下で実装した。
γ3b の主比較、𝒮・Sp の適用は継続中。

### 一脚だけが fibration の cospan の実際の比較（実装済み）

`InitialJoinFaces.lean` と `InitialJoinFunctor.lean` は自然な同型の順方向について、
点側の包含を `nervePoint .star`、底面の包含を `nerveMap WithInitial.incl` と同定する。
任意の G : C ⥤ D に対して次の厳密な自然性を証明した。

```lean
initialJoinNerveMap_naturality (G : C ⥤ D) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap G) ≫ initialJoinNerveMap D =
      initialJoinNerveMap C ≫ nerveMap (WithInitial.map G)
```

`PointJoinCorner.lean` は f : A ⟶ B に対して
`pointJoinCorner f : pushout f (joinInr Δ[0] A) ⟶ join Δ[0] B` を定義する。
単射の像への同型と空 join の同型で `joinUnion_isPushout` を移送し、
`pointJoinCorner_anodyne f [Mono f] hf` を証明した。hf は f の anodyne 性である。
`InitialNerveCorner.lean` はこの結果を始対象の付加の正方形へ移す。

```lean
initialNerveCorner (G : C ⥤ D) :
    pushout (nerveMap G) (nerveMap (WithInitial.incl : C ⥤ WithInitial C)) ⟶
      nerve (WithInitial D)
initialNerveCorner_anodyne (G : C ⥤ D) [Mono (nerveMap G)]
    (hG : anodyneExtensions (nerveMap G)) : anodyneExtensions (initialNerveCorner G)
```

C と D は Type u の小さい圏。対象の非空性、Kan 性や追加の境界の持ち上げ性は不要。
`CospanSingleFibrationComparison.lean` の
`bousfieldKanConeWeightInclusion_cospan_corner_anodyne` は、実際の W → V の相対境界を
この形で表示し、既に証明した右遷移の anodyne 性を適用する。追加の境界仮定は残らない。

以下の H の条件は中央・右端の Kan 性と左脚の Fibration 性。
右脚の Fibration 性も、極限頂点の Kan 性の別の仮定も要求しない。

```lean
H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}
[KanComplex (H.obj (AsSmall.up.obj .one))]
[KanComplex (H.obj (AsSmall.up.obj .right))]
[Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]

bousfieldKanConeWeightInclusion_cospan_leftFibration_trivialKanFibration H :
    TrivialKanFibration (weightedSectionsPre bousfieldKanConeWeightInclusion H)
bousfieldKanConeWeightInclusion_cospan_leftFibration_homotopyEquivalence H :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre bousfieldKanConeWeightInclusion H)
bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence H
    (c : Cone H) (hc : IsLimit c) :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c)
bousfieldKanLimitComparison_cospan_leftFibration_homotopyEquivalence H :
    IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H)
```

一点側で既に証明した同値と、元の重みへの実際の制限の同値を合成して κ を得る。
豊穣圏 C : Type v、[Category.{u} C]、[SimplicialCategory C] について、
`representableHomotopyLimitComparison_cospan_leftFibration_homotopyEquivalence c x hc` は
実際の `representableHomotopyLimitComparison c x` の単体的ホモトピー同値性を証明する。
ここで F : AsSmall.{u} WalkingCospan ⥤ C、c : Cone F、x : C、
hc : IsLimit (simplicialHomCone c x) であり、上記の H の条件を
`H := simplicialHomDiagram F x` に要求する。正確な全型は公開747宣言の監査に記録。
錐の pinched Hom と比較射の導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了である。

### 重み付き end と weighted nerve の切断の族（全単射を実装）

γ3b の主比較へ向け、Bousfield–Kan 重み付き end と weighted nerve の切断空間の対応を作る。
切断の族から自然変換へ戻す構成と両逆関係まで以下で証明した。
単体集合の切断模型との同型と一般の Kan 値図式での Kan 性も以下で証明した。
coherent な錐の pinched Hom と導来ファイバーの比較は未完了なので、γ3b の完成とは数えない。

`PrefixOverWeight.lean` は各射列 σ の初区間を、その終点の over 圏へ持ち上げる。
I : Type u、[SmallCategory I] の下で、次を構成した。

```lean
prefixOverChain {n : ℕ} (σ : ComposableArrows I n) (i : Fin (n + 1)) :
    ComposableArrows (Over (σ.obj i)) i.val
prefixOverWeight {n : ℕ} (σ : ComposableArrows I n) :
    simplexPrefixWeight n ⟶ σ ⋙ bousfieldKanWeight I
```

`prefixOverChain_inclusion` は i ≤ j に沿う後合成と初区間の包含の可換性、
`prefixOverChain_restriction` は任意の面・退化の制限との可換性。
Yoneda による単体集合の射の式と `prefixOverWeight_restriction` も公開した。

`WeightedNerveCoefficients.lean` はパラメータ a : Δ[n] ⟶ A を各初区間へ制限し、
over 圏の単体と直積にまとめて自然変換 η で評価する。
`prefixOverParameter_restriction` と `weightedNerveCoefficients_restriction` により、
全ての面・退化に整合する係数を作る。
`WeightedNerveSections.lean` はこれを底の nerve 上の射へ束ねる。

```lean
weightedNerveSectionFromTransform {A : SSet.{u}} {H : I ⥤ SSet.{u}}
    (η : bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    nerve I ⊗ A ⟶ weightedNerve H
weightedNerveSectionFromTransform_projection η :
    weightedNerveSectionFromTransform η ≫ weightedNerveProjection H = fst (nerve I) A
bousfieldKanWeightedNerveEvaluation (H : I ⥤ SSet.{u}) :
    nerve I ⊗ bousfieldKanHolim H ⟶ weightedNerve H
bousfieldKanWeightedNerveEvaluation_projection (H : I ⥤ SSet.{u}) :
    bousfieldKanWeightedNerveEvaluation H ≫ weightedNerveProjection H =
      fst (nerve I) (bousfieldKanHolim H)
```

普遍的な族は重み付き end の恒等射を uncurry して得る。
ここでは係数やパラメータの Kan 性を要求しない。F1 の既存の `weightedNerve` を使い、
重複した nerve の定義は導入しない。逆対応は以下で証明した。

`WeightedSectionCoefficients.lean` は切断の射影条件で底を正規化した係数を取り出す。
`weightedSectionCoefficients_restriction` は切断の全ての面・退化との可換性を係数の等式に移す。
`WeightedSectionOverEvaluation.lean` は over 圏の射列の底を忘れた後、最後の係数を取り出し、
最後の構造射で後合成する。最後の頂点を保たない作用素には係数の自然性と over の三角形を使う。
`WeightedSectionTransform.lean` はこの評価を全次数と全添字で束ねる。

```lean
weightedSectionTransform {A : SSet.{u}} {H : I ⥤ SSet.{u}}
    (s : nerve I ⊗ A ⟶ weightedNerve H)
    (hs : s ≫ weightedNerveProjection H = fst (nerve I) A) :
    bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H
```

`WeightedSectionTransformRetraction.lean` は over 圏の射列を最後の構造射で復元し、
`weightedSectionTransform_fromTransform η` により自然変換側の逆関係を証明する。
`WeightedSectionRoundtrip.lean` は初区間の最後での評価から元の係数を回収し、
`weightedNerveSectionFromTransform_fromSection s hs` により切断側の逆関係を証明する。
いずれもホモトピーだけでなく、実際の射・自然変換の厳密な等式である。

```lean
weightedNerveSectionEquiv (H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) ≃
      {s : nerve I ⊗ A ⟶ weightedNerve H //
        s ≫ weightedNerveProjection H = fst (nerve I) A}
bousfieldKanSectionHomEquiv (H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (A ⟶ bousfieldKanHolim H) ≃
      {s : nerve I ⊗ A ⟶ weightedNerve H //
        s ≫ weightedNerveProjection H = fst (nerve I) A}
```

後者は重み付き end の普遍性との合成であり、I : Type u、[SmallCategory I] だけを仮定する。
パラメータ A と係数図式 H の Kan 性は不要。
この全単射のパラメータ自然性と単体集合としての切断模型との同型は以下で証明した。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は継続中。

### 切断模型との同型と一般の Kan 性（実装済み）

`WeightedSectionParameter.lean` は係数と切断のパラメータの前合成に関する自然性を証明する。
`bousfieldKanSectionHomEquiv_apply H f` は全単射の順方向を
`(nerve I ◁ f) ≫ bousfieldKanWeightedNerveEvaluation H` と同定する。
`bousfieldKanSectionHomEquiv_parameter f g` は任意のパラメータの射に対する自然性である。

`SimplicialSections.lean` は任意の p : E ⟶ K に対し、切断の単体集合を
内部 Hom の後合成の射の恒等写像の点上の引き戻しとして構成する。

```lean
simplicialSections (p : E ⟶ K) : SSet.{u} :=
  pullback ((ihom K).map p) (curry (fst K (𝟙_ SSet.{u})))
simplicialSectionsEvaluation (p : E ⟶ K) : K ⊗ simplicialSections p ⟶ E
simplicialSectionsHomEquiv (p : E ⟶ K) (A : SSet.{u}) :
    (A ⟶ simplicialSections p) ≃ {s : K ⊗ A ⟶ E // s ≫ p = fst K A}
```

評価は底への合成が第一射影に一致する。`simplicialSectionsLift` は任意の切断の族を持ち上げ、
`simplicialSectionsLift_evaluation` と `simplicialSections_hom_ext` が存在と一意性を与える。
`BousfieldKanSectionsIso.lean` は二つの模型の普遍的な族から両向きの射を作り、評価の一意性を使う。

```lean
bousfieldKanSectionsMap (H : I ⥤ SSet.{u}) :
    bousfieldKanHolim H ⟶ simplicialSections (weightedNerveProjection H)
sectionsBousfieldKanMap (H : I ⥤ SSet.{u}) :
    simplicialSections (weightedNerveProjection H) ⟶ bousfieldKanHolim H
bousfieldKanSectionsIso (H : I ⥤ SSet.{u}) :
    bousfieldKanHolim H ≅ simplicialSections (weightedNerveProjection H)
```

両射の評価の等式と両向きの厳密な逆関係を公開した。
ここまでの同型には Kan 性、fibration 性、添字圏の有限性は不要である。

`SectionsKan.lean` は F1 の既存の `relativeFunctorSpace` とも同定する。

```lean
simplicialSectionsRelativeIso {K E : SSet.{u}} (p : E ⟶ K) :
    simplicialSections p ≅ relativeFunctorSpace p (𝟙 K)
simplicialSections_kanComplex {K E : SSet.{u}} (p : E ⟶ K) [LeftFibration p] :
    KanComplex (simplicialSections p)
bousfieldKanHolim_kanComplex {I : Type u} [SmallCategory I] (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (bousfieldKanHolim H)
```

F1 の `weightedNerveProjection_leftFibration` と相対関手空間の Kan 性を使い、同型で移す。
底や全空間の quasicategory 性は要求しない。
これは比較先の一般の Kan 性であり、strict 極限の比較が任意の Kan 図式で同値になるとは主張しない。
coherent な錐の pinched Hom と導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限は未完了。

### 切断模型の図式自然性と相対持ち上げ（実装済み）

`SectionsFunctor.lean` は底 K を保つ写像に関する切断空間の関手性を提供する。

```lean
simplicialSectionsMap {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) : simplicialSections p ⟶ simplicialSections q
simplicialSectionsFunctor (K : SSet.{u}) : Over K ⥤ SSet.{u}
```

普遍的な族の後合成を切断空間へ持ち上げて定義し、評価の公式と恒等・合成の法則を証明した。
`SectionsDiagramNaturality.lean` は `weightedSectionsUncurry_postcomp`、係数と切断の族の
後合成の式を使い、Bousfield–Kan の普遍的な切断の図式自然性を証明する。

```lean
bousfieldKanSectionsMap_naturality {H H' : I ⥤ SSet.{u}} (η : H ⟶ H') :
    bousfieldKanSectionsMap H ≫
        simplicialSectionsMap (weightedNerveMap η) (weightedNerveMap_projection η) =
      weightedSectionsMap (bousfieldKanWeight I) η ≫ bousfieldKanSectionsMap H'
bousfieldKanSectionsNatIso (I : Type u) [SmallCategory I] :
    bousfieldKanHolimFunctor I ≅ weightedNerveFunctor I ⋙ simplicialSectionsFunctor (nerve I)
```

同型が各図式で存在するだけでなく、F1 の実際の `weightedNerveMap η` と可換な自然同型となる。
この自然性は図式や写像の Kan 性・同値性を要求しない。

`SectionsLifting.lean` は全空間の写像の相対持ち上げ性を切断空間の写像へ移す。
K、E、E'、A、B は全て SSet.{u}。

```lean
simplicialSectionsMap_hasLiftingProperty {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) (i : A ⟶ B) [HasLiftingProperty (K ◁ i) f] :
    HasLiftingProperty i (simplicialSectionsMap f hf)
simplicialSectionsMap_fibration {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) [Fibration f] : Fibration (simplicialSectionsMap f hf)
simplicialSectionsMap_trivialKanFibration {p : E ⟶ K} {q : E' ⟶ K}
    (f : E ⟶ E') (hf : f ≫ q = p) [TrivialKanFibration f] :
    TrivialKanFibration (simplicialSectionsMap f hf)
```

ホーンでは底との直積の anodyne 性、境界では直積の単射性を使う。
前提は全空間間の写像 f の性質であり、p と q が left fibration であることだけでは代用しない。
coherent な錐の切断模型との比較射の構成とその同値性、pinched Hom と導来ファイバーの主比較、
𝒮・Sp の残りの ∞ 極限への適用は引き続き未完了である。

### coherent な錐の具体的な切断データ（実装済み）

`CoherentConeSections.lean` は任意の JoinCone p をその頂点の coslice へ curry する。
strict な通常の錐に制限せず、左端の固定条件は `coherentCone_inl_vertex c` で証明する。

```lean
coherentConeCosliceSection {p : K ⟶ X} (c : JoinCone p) :
    K ⟶ sliceUnder (SSet.yonedaEquiv.symm c.vertex)
coherentConeCosliceSection_projection c :
    coherentConeCosliceSection c ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) = p
```

`cosliceSectionCone` は逆構成であり、頂点の保存と錐側の厳密な逆関係を公開した。
`fixedVertexConeSectionEquiv p x` は左端を x に固定した全ての錐と、coslice への持ち上げの全単射。
`CoherentConeSectionSpace.lean` はこの持ち上げを F1 の相対関手空間の具体的な点にする。

```lean
coherentConeSectionSpace (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  relativeFunctorSpace (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p
coherentConeSectionPoint {p : K ⟶ X} (c : JoinCone p) :
    (coherentConeSectionSpace p c.vertex) _⦋0⦌
```

`fixedVertexConeSpaceEquiv p x` は頂点を固定した錐とこの模型の零単体の全単射である。
X が quasicategory ならこの模型は Kan。K の quasicategory 性は不要。

`PullbackSections.lean` は任意の p : E ⟶ B と a : K ⟶ B について、
`pullbackSectionsRelativeIso p a : simplicialSections (pullback.snd p a) ≅ relativeFunctorSpace p a`
を証明した。ここには充填性の仮定はない。
`CoherentConeLeftFibration.lean` は coslice 射影を実際に図式に沿って引き戻す。

```lean
coherentConeProjection (p : K ⟶ X) (x : X _⦋0⦌) : coherentConeTotal p x ⟶ K
coherentConeSectionsIso (p : K ⟶ X) (x : X _⦋0⦌) :
    simplicialSections (coherentConeProjection p x) ≅ coherentConeSectionSpace p x
coherentConeSectionVertex {p : K ⟶ X} (c : JoinCone p) :
    (simplicialSections (coherentConeProjection p c.vertex)) _⦋0⦌
```

X が quasicategory なら射影は left fibration。
`coherentConeProjectionFiberIso` は各 fiber を x の coslice の対応する fiber と同定し、
`coherentConeProjectionMappingEquivalence` は右 pinched Hom への F1 の同値を合成する。
局所 Kan な単体的圏 C : Type v、[Category.{u} C]、[SimplicialCategory C] に対し、
`strictCoherentConeFiberHomEquivalence F x i` は実際の strict な図式 F : J ⥤ C に適用した次の同値。

```lean
QCatEquivalence (vertexFiber
  (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (ULift.up (ComposableArrows.mk₀ i)))
  ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)))
```

J : Type u、[SmallCategory J] と全ての sHom の Kan 性を要求する。持ち上げの宇宙を省略しない。
ここまでで任意の coherent な錐に具体的な切断の点と、fiber ごとの実際の Hom の比較を与えた。
fiber の比較を図式全体の比較へ束ねること、その切断空間と Bousfield–Kan end の同値性、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限への適用は未完了。

### 切断空間と strict transport の通常の極限（実装済み）

`TransportConeAssembly.lean` は通常の錐 c から `nerve I ⊗ c.pt` を
simplicial replacement へ写す。各射列の始点で錐の成分を添え、始点が移る自然性は c.w を使う。
strict transport の錐では F1 の `universalScaffold p` を後合成し、元の全空間への切断の族を得る。

```lean
strictTransportConeAssembly {E : SSet.{u}} (p : E ⟶ nerve I)
    (c : Cone (leftStrictTransportDiagram p)) : nerve I ⊗ c.pt ⟶ E
strictTransportConeAssembly_projection p c :
    strictTransportConeAssembly p c ≫ p = fst (nerve I) c.pt
strictTransportConeSections p c : c.pt ⟶ simplicialSections p
```

`TransportSectionsCone.lean` は普遍的な切断の族を各 under 圏の忘却で制限し、
`transportSectionsRestriction p i : simplicialSections p ⟶ leftStrictTransport p i` を作る。
これらは strict transport の全ての構造射と厳密に可換である。
`TransportSectionsRetraction.lean` と `TransportSectionsLimit.lean` は両向きの回収を証明する。
under 圏の射列は、底の標準の under 射列を最初の構造射で前合成して復元できる。
この式と通常の錐の可換性で任意の互換な族の全成分を回収する。

```lean
transportSectionsCone (p : E ⟶ nerve I) : Cone (leftStrictTransportDiagram p)
transportSectionsConeIsLimit (p : E ⟶ nerve I) : IsLimit (transportSectionsCone p)
transportLimitSectionsIso (p : E ⟶ nerve I) :
    limit (leftStrictTransportDiagram p) ≅ simplicialSections p
```

I : Type u、[SmallCategory I]、E : SSet.{u}。この通常の極限の同定に left fibration 性は不要。

`TransportSectionsComparison.lean` は切断空間が担う極限錐に実際の標準比較を適用する。

```lean
strictTransportSectionsComparison {I : Type u} [SmallCategory I] {E : SSet.{u}}
    (p : E ⟶ nerve I) :
    simplicialSections p ⟶ bousfieldKanHolim (leftStrictTransportDiagram p)
strictTransportSectionsComparison_cospan_homotopyEquivalence {E : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} WalkingCospan)) [LeftFibration p] :
    IsSimplicialHomotopyEquivalence (strictTransportSectionsComparison p)
strictTransportSectionsComparison_tower_homotopyEquivalence {E : SSet.{u}}
    (p : E ⟶ nerve (AsSmall.{u} ℕᵒᵖ)) [LeftFibration p] :
    IsSimplicialHomotopyEquivalence (strictTransportSectionsComparison p)
strictTransportSectionsComparison_discrete_isIso {J : Type u} {E : SSet.{u}}
    (p : E ⟶ nerve (Discrete J)) : IsIso (strictTransportSectionsComparison p)
```

cospan と塔では F1 の `leftStrictTransportMap_fibration_of_thin` を使う。
strict transport の Kan 値性と、各構造射の fibration 性は p の left fibration 性から導出する。
離散の場合は left fibration 性も有限性も不要。
これは切断空間と strict transport 図式の大域的な比較である。
元の豊穣 Hom 図式 `simplicialHomDiagram F x` との自然な比較は別途必要であり未完了。
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの ∞ 極限も継続中。

### weighted nerve の strict transport への自然な単位比較（実装済み）

`WeightedTransportCoefficients` は H(i) の単体を under 圏の各構造射で輸送する。
`WeightedTransportUnit` はこの族を相対関手空間へ curry し、自然変換にまとめる。
任意の `I : Type u`・`[SmallCategory I]` と `H : I ⥤ SSet.{u}` に対して、

```lean
weightedTransportUnit H : H ⟶ leftStrictTransportDiagram (weightedNerveProjection H)
weightedTransportUnitComponent_evaluate H i :
    weightedTransportUnitComponent H i ≫
      leftStrictTransportEvaluate (weightedNerveProjection H) i = weightedNerveFiberMap H i
```

を構成した。前者の自然性は全ての構造射について厳密な等式であり、Kan 性は不要。
後者は恒等射での評価との合成が weighted nerve の既存の fiber 同型に一致することを述べる。
`WeightedTransportUnitEquivalence` は `[∀ i, KanComplex (H.obj i)]` の下で

```lean
weightedTransportUnitComponent_isQCatEquivalence H i :
    IsQCatEquivalence (weightedTransportUnitComponent H i)
weightedTransportUnitComponent_homotopyEquivalence H i :
    IsSimplicialHomotopyEquivalence (weightedTransportUnitComponent H i)
```

を証明した。恒等射での評価は自明 Kan fibration なので、その同値性と合成の fiber 同型を使う。
これは元の図式 H とその weighted nerve の strict transport の自然な比較である。
成分のホモトピー逆の自然性は要求しない。end 上の誘導射の同値性は次節で証明した。
coherent cone の射影の strict transport と元の sHom 図式との自然な比較、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は未完了。

### Bousfield–Kan end の成分ごとの同値不変性（実装済み）

`WeightedCoefficientPostcomp` は最後の係数評価の係数図式に関する自然性を証明する。
`WeightedBoundaryReconstruction` と `WeightedBoundaryLifting` は、正次元の境界を最後の面と
最後の係数から復元する。零次元では係数の自明 Kan fibration の切断を使う。
`WeightedNerveTrivialFibration` により、任意の `C : Type u`・`[Category.{u} C]`、
`F G : C ⥤ SSet.{u}`、`η : F ⟶ G` について次が成立する。

```lean
weightedNerveMap_trivialKanFibration η [∀ c, TrivialKanFibration (η.app c)] :
    TrivialKanFibration (weightedNerveMap η)
```

`BousfieldKanCoefficientFibration` は切断空間との自然同型でこの持ち上げ性を end に移す。
ここからは `I : Type u`・`[SmallCategory I]`、`F G : I ⥤ SSet.{u}` とする。

```lean
bousfieldKanMap_trivialKanFibration (η : F ⟶ G)
    [∀ i, TrivialKanFibration (η.app i)] :
    TrivialKanFibration (weightedSectionsMap (bousfieldKanWeight I) η)
```

ここまでは値の Kan 性も遷移の fibration 性も不要。
`DiagramPathReplacement` と `DiagramPathSpan` は自然変換の成分の既存の可逆 path 置換を束ね、
`diagramPathReplacement η` と自然変換 `diagramPathProjection η`・`diagramPathEndpoint η`・
`diagramPathSection η` を作る。切断との合成は厳密に恒等変換と η に等しい。
Kan 値図式の成分ごとの同値なら二つの射影がともに成分ごとの自明 Kan fibration になる。
`BousfieldKanHomotopyInvariance` はこの span により、次を証明した。

```lean
bousfieldKanMap_isQCatEquivalence
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, IsQCatEquivalence (η.app i)) :
    IsQCatEquivalence (weightedSectionsMap (bousfieldKanWeight I) η)
bousfieldKanMap_homotopyEquivalence
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, IsSimplicialHomotopyEquivalence (η.app i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap (bousfieldKanWeight I) η)
weightedTransportUnit_end_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (weightedTransportUnit H))
```

添字の有限性、遷移の fibration 性、成分の逆の自然性は要求しない。
`bousfieldKanWeightedSections_kanComplex` は同値判定で使う end 表示の Kan 性の instance。
単位が誘導する end の射を、切断の通常の極限錐から作る `strictTransportSectionsComparison` と
厳密に等しいとは主張しない。この段階で自然に比較したものは H とその weighted nerve の transport。
coherent cone の射影の transport と元の sHom 図式との自然な比較、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は未完了。

### 全空間の比較から transport・切断空間への比較（実装済み）

`RelativeFunctorPostcomposition` は、同じ底への射影 p・q と `f ≫ q = p` を満たす実際の射 f に対し、
相対関手の後合成 `relativeFunctorPost p q f hf a` を構成した。
定義域の前合成・頂点での評価・uncurry と可換で、充填性は定義に不要。
`TransportPostcomparison` は各 under 圏でこの後合成を使い、
任意の `I : Type u`・`[SmallCategory I]`、`p : E ⟶ nerve I`、`q : E' ⟶ nerve I` に対して

```lean
strictTransportPost p q (f : E ⟶ E') (hf : f ≫ q = p) :
    leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram q
strictTransportPost_evaluate p q f hf i :
    (strictTransportPost p q f hf).app i ≫ leftStrictTransportEvaluate q i =
      leftStrictTransportEvaluate p i ≫
        vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i)
```

を証明した。p・q が left fibration なら、右辺の各 fiber の誘導射が圏同値であることから
`strictTransportPost_component_isQCatEquivalence` が各成分の同値性を検出する。
`strictTransportPost_end_homotopyEquivalence` は同じ全 fiber の条件の下で、
`weightedSectionsMap (bousfieldKanWeight I) (strictTransportPost p q f hf)` の
実際の単体的ホモトピー同値性を証明する。添字の形や遷移の fibration 性は不要。

`TransportSectionsNaturality` は under 圏への制限と全空間の後合成の可換性を示し、
次の標準比較射の厳密な可換四角形を証明した。

```lean
strictTransportSectionsComparison_naturality p q f hf :
    simplicialSectionsMap f hf ≫ strictTransportSectionsComparison q =
      strictTransportSectionsComparison p ≫
        weightedSectionsMap (bousfieldKanWeight I) (strictTransportPost p q f hf)
```

`SectionsFiberwiseComparison` はこの四角形と既存の標準比較の同値性を使い、
`IsSimplicialHomotopyEquivalence (simplicialSectionsMap f hf)` を次の三つの名前で公開した。

- `simplicialSectionsMap_cospan_homotopyEquivalence`：底は `nerve (AsSmall.{u} WalkingCospan)`。
- `simplicialSectionsMap_tower_homotopyEquivalence`：底は `nerve (AsSmall.{u} ℕᵒᵖ)`。
- `simplicialSectionsMap_discrete_homotopyEquivalence`：底は `nerve (Discrete J)`、J の有限性は不要。

各定理の前提は `[LeftFibration p]`・`[LeftFibration q]`、`hf : f ≫ q = p` と
`∀ i, IsQCatEquivalence (vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i))`。
f 自身の fibration 性や自明 Kan fibration 性は要求しない。
一般の判定 `simplicialSectionsMap_homotopyEquivalence_of_transportComparisons` では、
二つの標準比較のホモトピー同値性を入力とするが、上記三つの定理ではそれを既存の証明から供給する。
この結果は実際の全空間の射 f からの比較であり、fiber ごとに選んだ同値の族から f の存在は結論しない。
coherent cone の射影と元の sHom 図式の模型の間の実際の比較の構成、
錐の pinched Hom と q_x の導来ファイバーの主比較、𝒮・Sp の残りの適用は未完了。

### 錐の pinched Hom を回収する right fibration の比較 span（実装済み）

`RightConeBoundary` は境界と右の一点の join を最後のホーンと同定し、
right fibration r による点上の slice の後合成が自明 Kan fibration であることを証明した。
`VertexFiberMapLifting` は全空間の射の持ち上げ性を同じ底の頂点 fiber の誘導射へ移す。

`RightFibrationMappingSpan` と `RightFibrationHomComparison` は、`r : E ⟶ B`、
`c : E _⦋0⦌`、`x : B _⦋0⦌` に対して次の実際の span を構成する。

```lean
rightFibrationMappingTotal r c x =
    vertexFiber (sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) x
rightFibrationMappingHomProjection r c x :
    rightFibrationMappingTotal r c x ⟶ pinchedHom x (r.app (Opposite.op ⦋0⦌) c)
rightFibrationMappingEvaluation r c x :
    rightFibrationMappingTotal r c x ⟶ vertexFiber r x
```

`[RightFibration r]` の下で前者の射影は自明 Kan fibration。
`[Quasicategory B]` も仮定すると中間空間は Kan で、後者の始点評価は Kan fibration になる。
E の quasicategory 性は r の inner fibration 性から導出し、r 自身の Kan fibration 性は要求しない。
`rightFibrationMappingSection` は前者の切断を選び、
`rightFibrationMappingSection_projection` は切断と射影の合成が厳密に恒等射であることを示す。
`rightFibrationHomComparison r c x` はこの切断に始点評価を続けた射。
この切断の選択に関する自然性は主張しない。

`VertexFiberMapFiber` は任意の同じ底上の射の二重 fiber を元の射の fiber と同型にする。
これと点上の slice fiber の同型により、

```lean
rightFibrationMappingEvaluationFiberIso r c x
    (d : (vertexFiber r x) _⦋0⦌) :
    vertexFiber (rightFibrationMappingEvaluation r c x) d ≅ pinchedHom d.val c
```

を証明した。この同型自体には right fibration 性も quasicategory 性も不要。
`ConeMappingSpan` は r を実際の錐の slice の頂点射影 `sliceOverProjection p` に特殊化する。
任意の `p : K ⟶ X` と全ての coherent な錐 d・c に対して、

```lean
coneVertexFiberPoint d : (vertexFiber (sliceOverProjection p) d.vertex) _⦋0⦌
conePinchedHom_mappingEvaluationFiberIso (d c : JoinCone p) :
    pinchedHom (X := sliceOver p) d c ≅
      vertexFiber (rightFibrationMappingEvaluation (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d)
```

を得る。X が quasicategory なら、この表示に使う始点評価は上記の実際の Kan fibration である。
これは主比較の pinched Hom 側を strict fiber として回収した結果であり、
選択を含む `rightFibrationHomComparison` と既存の sHom からの `q_x` をまだ同定していない。
始点評価の strict fiber と導来ファイバーの比較は次節で証明した。
錐の頂点 fiber と end の切断模型の比較、𝒮・Sp の残りの ∞ 極限への適用は継続中。

### 錐の pinched Hom と始点評価の導来ファイバー（実装済み）

`KanEquivalencePaths` は Kan 複体の全ての path が可逆で、
`equivalencePathι X` が通常の区間関手空間への厳密な同型になることを示す。
`PointEndpointEvaluation` と `KanRelativePathLifting` は一点の関手空間の同型と二変数随伴を使い、
Kan 複体間の Kan fibration p について任意の端点 j の
`relativeEquivalencePathMapAt p j` が自明 Kan fibration になることを証明した。
区間の端点の anodyne 性は、追跡済みの既存の `AnodyneIntervalEndpoints.delta_anodyne` を使う。

`FibrationDerivedFiberSpan` は始域の可逆 path の終点の像を b に固定し、
strict fiber と path 置換の fiber への二つの自明 Kan fibration を構成する。
`[KanComplex E]`・`[KanComplex B]`・`p : E ⟶ B`・`[Fibration p]` の下で

```lean
fibrationStrictDerivedFiberEquivalence p (b : B _⦋0⦌) :
    QCatEquivalence (vertexFiber p b) (comparisonFiber p b)
```

を得た。置換前の射 p に fibration 性がない場合へは拡張していない。
`ConeDerivedFiberComparison` はこの同値に前節の strict fiber の同型を接続する。
任意の `p : K ⟶ X`、`[Quasicategory X]` と全ての coherent な錐 d・c に対して、

```lean
conePinchedHom_mappingEvaluationDerivedFiberEquivalence (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (rightFibrationMappingEvaluation (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d))
```

を証明した。添字 K の quasicategory 性や、図式 p の strict な通常の圏からの表示は不要。
`ConeSpanLimitCriterion` は極限錐なら始点評価が全ての x で自明 Kan fibration となること、
逆に始点評価が全ての x で同値なら、実際の導来ファイバーの可縮性と A3d から極限錐となることを示す。

さらに `ConeRepresentableCriterion` は span の射影の切断の同値性を二対三で使い、
前節で構成した実際の表現可能な比較射による次の判定を証明した。

```lean
isLimitCone_iff_rightFibrationHomComparison_homotopyEquivalence (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence
        (rightFibrationHomComparison (sliceOverProjection p) c x)
```

比較射の始域は `pinchedHom x c.vertex`、終域は `vertexFiber (sliceOverProjection p) x`。
両者は Kan で、全ての x を量化する。この射は span の自明 Kan fibration の切断の選択を含む。
この ∞ 圏内の極限判定を、豊穣 Hom からの既存の `representableHomotopyLimitComparison c x`
とまだ同定していない。錐の頂点 fiber と end の切断模型の比較、および元の q_x との接続、
𝒮・Sp の残りの ∞ 極限への適用は未完了であり、γ3b・γ3c の完成とは数えない。

### 固定頂点の内部 Hom の錐への二つの比較射（構成済み）

`ConeFamilyApex` は内部 Hom による錐の模型から頂点への射影を作る。
`SectionConeFamily` は coslice の切断の普遍族を join と直積の比較で展開する。
任意の `K X : SSet.{u}`、`p : K ⟶ X`、`x : X _⦋0⦌` に対して次を構成した。
X の quasicategory 性や図式の通常の圏からの表示は不要。

```lean
coneFamilyApex p : coneFamily p ⟶ X
fixedApexConeFamily p x : SSet.{u} := vertexFiber (coneFamilyApex p) x

sliceConeFamilyMap_apex p :
  sliceConeFamilyMap p ≫ coneFamilyApex p = sliceOverProjection p
coneVertexFiberFamilyMap p x :
  vertexFiber (sliceOverProjection p) x ⟶ fixedApexConeFamily p x

sectionConeFamilyUncurry p x :
  join (Δ[0] : SSet.{u}) K ⊗ coherentConeSectionSpace p x ⟶ X
sectionConeFamilyMap p x : coherentConeSectionSpace p x ⟶ coneFamily p
sectionConeFamilyMap_apex p x :
  sectionConeFamilyMap p x ≫ coneFamilyApex p = SSet.const x
sectionFixedApexConeFamilyMap p x :
  coherentConeSectionSpace p x ⟶ fixedApexConeFamily p x
```

`sectionConeFamilyUncurry_fixed` と `sectionConeFamilyUncurry_curry_fixed` は
右端が全次数で p に固定されることを示す。二つの apex の補題も射の厳密な等式であり、
零単体だけの対応ではない。このため slice 側と切断側から同じ固定頂点の模型への
実際の単体集合の射が得られた。slice 側の同値性は後節で証明した。
切断空間側の同値性も後節で証明した。
大域的な `isQCatEquivalence_sliceConeFamilyMap p` から strict fiber の同値性を
そのまま結論せず、固定頂点を保つ比較を別途証明する。
既存の豊穣 q_x との接続と 𝒮・Sp の残りの適用も未完了。

### 両端固定の fat join 模型への同値（実装済み）

`FixedEndpointConeSpace` と `FixedEndpointConeIso` は、二重 fiber としての
`fixedApexConeFamily p x` を両端固定の単一 fiber で表示する。
任意の `K X : SSet.{u}`、`p : K ⟶ X`、`x : X _⦋0⦌` に対して

```lean
fixedEndpointConeSpace p x :=
  vertexFiber ((pre (joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
fixedApexEndpointConeSpaceIso p x :
  fixedApexConeFamily p x ≅ fixedEndpointConeSpace p x
```

を構成した。同型には充填性の仮定が不要。左右の制限を `fixedApexConeFamilyEvaluation_inl`・
`fixedApexConeFamilyEvaluation_inr` で計算し、逆射は両端の条件を回収して二回 fiber へ持ち上げる。

`FixedEndpointFatComparison` は次の模型と実際の射を追加した。

```lean
fixedEndpointFatConeSpace p x :=
  vertexFiber ((pre (fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) p))
fixedEndpointConeFatComparison p x :
  fixedEndpointConeSpace p x ⟶ fixedEndpointFatConeSpace p x
fixedApexFatConeComparison p x :
  fixedApexConeFamily p x ⟶ fixedEndpointFatConeSpace p x
```

`[Quasicategory X]` の下で `fixedEndpointConeFatComparison_isQCatEquivalence p x` と
`fixedApexFatConeComparison_isQCatEquivalence p x` を証明した。
前者は既存の F1 の `isQCatEquivalence_fatJoinComparison_fixedEndpoints` の適用であり、
後者は厳密な同型との合成である。固定条件を外した大域的な同値だけには依存しない。
`joinEndpointInclusion_vertex_surjective` は両端包含が全頂点を含むことを示し、
同じ前提の下で `fixedEndpointConeSpace_kanComplex`・`fixedApexConeFamily_kanComplex` を得る。
K の quasicategory 性や非空性、p の fibration 性は不要。

前節の slice 側の射の同値性は後節で証明した。切断空間側の射の同値性も後節で証明した。
豊穣 q_x との整合性および 𝒮・Sp の残りの適用も引き続き証明が必要である。

### 両端固定の普遍性と slice 比較の厳密な左逆（実装済み）

`FixedFatConeUniversal`・`FixedFatConeCurry` は太い slice の既存の普遍性を、
頂点も固定する fiber に制限した。任意の `K X A : SSet.{u}`、
`p : K ⟶ X`、`x : X _⦋0⦌` に対して、充填性の仮定なしで

```lean
fixedFatConeHomEquiv p x A :
  (A ⟶ fixedEndpointFatConeSpace p x) ≃
    {F : fatJoin A K ⟶ X //
      fatJoinInl A K ≫ F = SSet.const x ∧ fatJoinInr A K ≫ F = p}
```

を構成した。順方向は `fixedFatConeUncurry`、逆方向は `fixedFatConeCurry`。
左右の固定条件、パラメータの前合成との可換性、単射性と両方の往復則を証明した。
`fixedEndpointFatConeSpace_kanComplex p x` は `[Quasicategory X]` の下で成立する。
これは前節の圏同値をホモトピー圏の同値へ移し、亜群性から導く。

`FixedSliceFatComparison` は、前節までの二つの実際の射の合成をそのまま使う。

```lean
fixedSliceFatConeComparison p x :
  vertexFiber (sliceOverProjection p) x ⟶ fixedEndpointFatConeSpace p x :=
    coneVertexFiberFamilyMap p x ≫ fixedApexFatConeComparison p x
```

`fixedSliceFatConeComparison_toLaxSlice` は頂点の固定を忘れた合成が
`vertexFiberι (sliceOverProjection p) x ≫ sliceLaxMap p` に厳密に一致することを示す。
`sliceLaxMap_mono` は fat join 比較のエピ性と uncurry の単射性から従い、
`fixedSliceFatConeComparison_mono` も充填性の仮定なしで得られる。
`fixedSliceFatConeComparison_uncurry x f` は任意パラメータの族を展開した射を
`fatJoinComparison A K ≫ sliceOverUncurry (f ≫ vertexFiberι _ x)` と同定する。

`[Quasicategory X]` の下で、既存の F1 の `exists_joinDiagram_relative_extension` を
この比較の像を固定した部分族として使い、次を証明した。

```lean
fixedSliceFatConeComparison_exists_retraction p x :
  ∃ r : fixedEndpointFatConeSpace p x ⟶ vertexFiber (sliceOverProjection p) x,
    fixedSliceFatConeComparison p x ≫ r = 𝟙 _
```

逆射は頂点と図式を保つ。K の quasicategory 性や非空性は不要である。
この厳密な左逆に加え、次節でホモトピー右逆を構成して圏同値性を証明した。
切断空間側の同値、豊穣 q_x との接続と 𝒮・Sp の残りの適用は未完了。

### slice の頂点 fiber と固定頂点の内部 Hom の錐の同値（実装済み）

`FatJoinTimeInput` は join の区間とホモトピーの時間を区別して円柱の成分を交換する。
`FixedFatConeHomotopy` は両端を全時間で固定する図式のホモトピーから、
固定頂点の錐の族の実際のホモトピー `fixedFatConeHomotopyOfDiagram` を構成する。
この構成には充填性を要求しない。

`FixedSliceConeEquivalence` は任意のパラメータ A について、
両端固定の fat join の図式を通常の join の図式とホモトピーまで比較する既存の F1 の
`exists_joinDiagram_of_fatJoinDiagram` を適用した。
回収した図式を頂点を保って slice へ curry し、上のホモトピーの移送を使うことで、
`fixedSliceFatConeComparison_exists_homotopy a` が任意の族 a のホモトピーまでの逆像を与える。
恒等族に適用し、前節の厳密な左逆と合わせて圏同値性を証明した。

任意の `K X : SSet.{u}`、`[Quasicategory X]`、`p : K ⟶ X`、`x : X _⦋0⦌` について、

```lean
fixedSliceFatConeComparison_isQCatEquivalence p x :
  IsQCatEquivalence (fixedSliceFatConeComparison p x)
coneVertexFiberFamilyMap_isQCatEquivalence p x :
  IsQCatEquivalence (coneVertexFiberFamilyMap p x)
coneVertexFiberFamilyMap_homotopyEquivalence p x :
  IsSimplicialHomotopyEquivalence (coneVertexFiberFamilyMap p x)
```

を得た。後二者は実際の `vertexFiber (sliceOverProjection p) x ⟶ fixedApexConeFamily p x`
についての主張である。図式の添字 K の quasicategory 性・非空性や p の fibration 性は不要。
固定頂点の比較を、大域的な slice の同値から無条件に導いたのではない。

`FixedApexLimitCriterion` はこの同値を既存の native な表現可能な極限判定へ接続する。
任意の `c : JoinCone p` について

```lean
fixedApexConeHomComparison c x : pinchedHom x c.vertex ⟶ fixedApexConeFamily p x
isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence c :
  IsLimitCone c ↔ ∀ x : X _⦋0⦌,
    IsSimplicialHomotopyEquivalence (fixedApexConeHomComparison c x)
```

を公開した。比較射は既存の `rightFibrationHomComparison` に実際の模型の同値を後合成したもので、
元の span の自明 Kan fibration の切断の選択を保持する。その自然性は主張しない。
切断空間側の `sectionFixedApexConeFamilyMap` の同値性は後節で証明した。
豊穣 q_x との一致、𝒮・Sp の残りの適用は未完了であり、γ3b・γ3c の完成とは数えない。

### 切断の右パラメータ表示と標準比較の厳密な左逆（実装済み）

`SectionConeUniversal` は切断空間の任意パラメータ A に対する普遍性を公開した。
任意の `K X A : SSet.{u}`、`p : K ⟶ X`、`x : X _⦋0⦌` に対して、充填性の仮定なしで

```lean
sectionConeHomEquiv p x A :
  (A ⟶ coherentConeSectionSpace p x) ≃
    {F : join (Δ[0] : SSet.{u}) (K ⊗ A) ⟶ X //
      joinInl Δ[0] (K ⊗ A) ≫ F = SSet.yonedaEquiv.symm x ∧
        joinInr Δ[0] (K ⊗ A) ≫ F = fst K A ≫ p}
```

を証明した。`sectionConeUncurry`・`sectionConeCurry` の両端条件、自然性、単射性と往復則を含む。

`FatJoinTensorRight` と `FatJoinTensorRightComparison` は右パラメータを fat join の右因子へ移す射
`fatJoinTensorRight A B P : fatJoin A B ⊗ P ⟶ fatJoin A (B ⊗ P)` を構成した。
左右の包含と円柱上の計算、パラメータへの自然性に加え、次の厳密な可換性を証明した。

```lean
fatJoinTensorRight_comparison A B P :
  fatJoinTensorRight A B P ≫ fatJoinComparison A (B ⊗ P) =
    (fatJoinComparison A B ▷ P) ≫ joinTensorRight A B P
```

`RightFatConeDiagram`・`RightFatConeNaturality` は任意の族
`f : A ⟶ fixedEndpointFatConeSpace p x` を
`rightFatConeDiagram f : fatJoin Δ[0] (K ⊗ A) ⟶ X` へ展開した。
左端は x、右端は `fst K A ≫ p`。右直積比較で引き戻すと元の普遍族になること、
パラメータへの自然性と単射性を証明した。左端と引き戻しによる射の一意性を使うため、
空の A も扱え、右直積比較自体のエピ性を要求しない。

`SectionFatConeComparison` は既存の二つの射の合成をそのまま比較として使う。

```lean
sectionFatConeComparison p x :
  coherentConeSectionSpace p x ⟶ fixedEndpointFatConeSpace p x :=
    sectionFixedApexConeFamilyMap p x ≫ fixedApexFatConeComparison p x
sectionFatConeComparison_diagram f :
  rightFatConeDiagram (f ≫ sectionFatConeComparison p x) =
    fatJoinComparison Δ[0] (K ⊗ A) ≫ sectionConeUncurry f
```

この任意パラメータの同定から `sectionFatConeComparison_mono p x` を充填性なしで得た。
さらに `[Quasicategory X]` の下で、F1 の `exists_joinDiagram_right_relative_extension` により
比較の像の部分族を固定して延長し、次を証明した。

```lean
sectionFatConeComparison_exists_retraction p x :
  ∃ r : fixedEndpointFatConeSpace p x ⟶ coherentConeSectionSpace p x,
    sectionFatConeComparison p x ≫ r = 𝟙 _
```

K の quasicategory 性や非空性、p の fibration 性は不要。逆射は図式と頂点を保つ。
次節ではこの左逆とホモトピー右逆を合わせて圏同値性を証明した。
豊穣 q_x との接続、𝒮・Sp の残りの適用は引き続き未完了。

### 錐の頂点 fiber と切断空間の同値・切断による極限判定（実装済み）

`RightFatConeHomotopy` は右パラメータの fat join 図式の両端固定のホモトピーを、
固定頂点の共通模型の族のホモトピーへ戻す。右直積比較で引き戻した普遍族を curry し、
左右の固定条件を全ホモトピー時間で確認する。この構成は充填性の仮定なしで成立する。

`SectionConeEquivalence` は F1 の両端固定の join 比較で任意の族の逆像をホモトピーまで回収した。
前節の厳密な左逆と合わせ、任意の `K X : SSet.{u}`、`[Quasicategory X]`、
`p : K ⟶ X`、`x : X _⦋0⦌` に対して次を証明した。

```lean
sectionFatConeComparison_isQCatEquivalence p x :
  IsQCatEquivalence (sectionFatConeComparison p x)
sectionFixedApexConeFamilyMap_isQCatEquivalence p x :
  IsQCatEquivalence (sectionFixedApexConeFamilyMap p x)
sectionFixedApexConeFamilyMap_homotopyEquivalence p x :
  IsSimplicialHomotopyEquivalence (sectionFixedApexConeFamilyMap p x)
coneVertexFiberSectionEquivalence p x :
  QCatEquivalence (vertexFiber (sliceOverProjection p) x) (coherentConeSectionSpace p x)
```

前三者は既存の標準射そのものの性質である。最後の同値は共通模型への二つの標準比較を使い、
切断側の逆の選択を含む。K の quasicategory 性・非空性や p の fibration 性は不要。

`ConeSectionLimitCriterion` は表現可能な比較の終域を切断空間へ移す。
任意の coherent な錐 `c : JoinCone p` に対し

```lean
coneSectionHomComparison c x : pinchedHom x c.vertex ⟶ coherentConeSectionSpace p x
isLimitCone_iff_coneSectionHomComparison_homotopyEquivalence c :
  IsLimitCone c ↔ ∀ x : X _⦋0⦌,
    IsSimplicialHomotopyEquivalence (coneSectionHomComparison c x)
```

を得た。比較には span の切断と切断側の同値の逆の選択を含み、その自然性は主張しない。

### 表現可能な transport の Bousfield–Kan end による三形状の極限判定（実装済み）

`ConeTransportLimitCriterion` は通常の小圏 I、`p : nerve I ⟶ X` に対し、
錐の left fibration `coherentConeProjection p x` の strict transport の end への射を定義する。

```lean
coneTransportHomComparison c x : pinchedHom x c.vertex ⟶
  bousfieldKanHolim (leftStrictTransportDiagram (coherentConeProjection p x))
```

これは `coneSectionHomComparison c x` に、引き戻しの切断の厳密な同型の逆と
`strictTransportSectionsComparison` を合成した実際の射である。
`coneTransportHolim_kanComplex p x` は任意の I でこの end が Kan であることを示す。
一般の I の極限判定では、全ての x での標準比較のホモトピー同値性を
`isLimitCone_iff_coneTransportHomComparison_of_transport` の仮定として明示する。
次の三つの添字では既存の実際の標準比較の同値性を適用し、その追加仮定を除いた。

| 公開名 | 添字 I |
| --- | --- |
| `isLimitCone_iff_coneTransportHomComparison_cospan` | `AsSmall.{u} WalkingCospan` |
| `isLimitCone_iff_coneTransportHomComparison_tower` | `AsSmall.{u} ℕᵒᵖ` |
| `isLimitCone_iff_coneTransportHomComparison_discrete` | `Discrete J`、任意の `J : Type u` |

いずれも型は `IsLimitCone c ↔ ∀ x, IsSimplicialHomotopyEquivalence
(coneTransportHomComparison c x)`。前提は `[Quasicategory X]` と指定された添字の図式・錐だけで、
p の fibration 性、離散添字の有限性・非空性を要求しない。
この end の係数は錐の left fibration の transport である。
元の `simplicialHomDiagram F x` との自然な比較と、豊穣 Hom からの実際の q_x との整合性は未完了。
したがって 𝒮・Sp の残りの適用を含む γ3b・γ3c はまだ完了と数えない。

### 反対の coherent nerve への自然な標準射（構成済み）

豊穣 Hom の右 pinched 比較を左 coslice の係数模型へ接続する準備として、
path の包含方向と単体の頂点の反転を区別して形式化した。
`CoherentPathDual` は線形順序 J の path の部分集合を変えずに二端点と上下界を交換する。
恒等 path・二回の双対・逆順の合成との整合性を証明し、

```lean
coherentThickeningDual J : EnrichedFunctor SSet
  (SimplicialThickening J) (SimplicialThickening Jᵒᵈ)ᵒᵖ
```

を構成した。J は任意の `Type u` と `[LinearOrder J]`。
`CoherentEnrichedOpposite` は豊穣関手 F の反対 `coherentEnrichedFunctorOp F`、
合成との可換性、thickening の双対の単調写像への自然性を証明する。
豊穣圏の反対の構造は Mathlib の `Enriched.Opposite` を使う。

`CoherentReverseThickening` は `ULift.{u} (Fin (n+1))` の頂点を `Fin.rev` で反転し、
標準 thickening からその反対への豊穣関手を作る。
`coherentReverseThickening_naturality α` は添字の反転 `SimplexCategory.rev.map α` と
前合成が可換であることを全ての面・退化について証明する。

`CoherentOppositeMap` は任意の `C : Type v`、`[Category.{u} C]`、`[SimplicialCategory C]` に対し、

```lean
coherentNerveOppositeMap C : (SimplicialNerve C).op ⟶ SimplicialNerve Cᵒᵖ
coherentNerveOppositeMap_vertex x :
  (coherentNerveOppositeMap C).app (Opposite.op ⦋0⦌)
    (SSet.opObjEquiv.symm (coherentNerveVertex x)) = coherentNerveVertex (Opposite.op x)
```

を構成した。Kan 性・quasicategory 性は不要で、頂点の像は厳密な等式である。
`CoherentNervePost` は対象の宇宙が共通の `C D : Type v` と豊穣関手 F に対し
`coherentNervePost F : SimplicialNerve C ⟶ SimplicialNerve D` を後合成で定義し、

```lean
coherentNerveOppositeMap_post F :
  SSet.opFunctor.map (coherentNervePost F) ≫ coherentNerveOppositeMap D =
    coherentNerveOppositeMap C ≫ coherentNervePost (coherentEnrichedFunctorOp F)
```

を証明した。これは豊穣関手への実際の自然性であり、点ごとの同値の選択ではない。
反対の標準射の逆射・往復則は次節で証明した。左 coslice の係数図式への接続は未完了。
元の豊穣 Hom の図式・q_x との比較、および 𝒮・Sp の残りの適用は引き続き未完了。

### 反対の coherent nerve の厳密な同型と逆射の自然性（実装済み）

`CoherentDoubleOpposite` は二重反対の豊穣圏から元の圏への標準関手
`coherentEnrichedDoubleUnop C : EnrichedFunctor SSet Cᵒᵖᵒᵖ C` を構成した。
対象を二回 unop し、Hom は恒等射とする。二つの対称性が合成で打ち消し合うことと、
豊穣関手への自然性を証明している。

`CoherentReverseInvolution` は標準 thickening の二回の頂点と path の反転の往復則を証明した。
対象では `Fin.rev_rev`、Hom では端点の等式による移送を明示し、部分集合の二回の像を計算する。

`CoherentOppositeIso` は任意の `C : Type v`、`[Category.{u} C]`、`[SimplicialCategory C]` に対し、

```lean
coherentNerveOppositeInverse C : SimplicialNerve Cᵒᵖ ⟶ (SimplicialNerve C).op
coherentNerveOppositeIso C : (SimplicialNerve C).op ≅ SimplicialNerve Cᵒᵖ
coherentNerveOppositeMap_isIso C : IsIso (coherentNerveOppositeMap C)
coherentNerveOppositeInverse_vertex x :
  (coherentNerveOppositeInverse C).app (Opposite.op ⦋0⦌)
    (coherentNerveVertex (Opposite.op x)) = SSet.opObjEquiv.symm (coherentNerveVertex x)
```

を公開した。同型の順方向は既存の `coherentNerveOppositeMap C` である。
逆射は同じ反転をもう一度行い、二重反対を忘れる構成から得る。
`coherentOppositeSimplex_involution`・`coherentOppositeInverseSimplex_opposite`・
`coherentOppositeSimplex_inverse` が各 simplex の両方の往復を厳密な等式で与え、
`coherentOppositeInverseSimplex_naturality` が面・退化との可換性を与える。
Kan 性・quasicategory 性・逆の選択の追加仮定は不要。

さらに対象の宇宙が共通の C・D と豊穣関手 F に対し、

```lean
coherentNerveOppositeInverse_post F :
  coherentNervePost (coherentEnrichedFunctorOp F) ≫ coherentNerveOppositeInverse D =
    coherentNerveOppositeInverse C ≫ SSet.opFunctor.map (coherentNervePost F)
```

を証明した。順方向の自然性の両側に逆射を合成し、往復則で消去する。
これで反対への移送を両方向で自然に使える。
左 coslice の係数図式、元の豊穣 Hom の図式・q_x との比較、𝒮・Sp の残りの適用は未完了。

### 反転による Kan ホモトピー同値の保存（実装済み）

`OppositeKanHomotopy` は以下を公開する。全ての単体集合は同じ宇宙 u に置き、
`uliftOppositeIso` の追加宇宙 v は任意とする。

```lean
oppositeTensorIso (X Y : SSet.{u}) : (X ⊗ Y).op ≅ X.op ⊗ Y.op
oppositeSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) :
  SSet.Homotopy (SSet.opFunctor.map g) (SSet.opFunctor.map f)
oppositeKanHomotopyEquivalence {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : IsSimplicialHomotopyEquivalence f) :
  IsSimplicialHomotopyEquivalence (SSet.opFunctor.map f)
uliftOppositeIso (X : SSet.{u}) :
  (SSet.uliftFunctor.{v, u}).obj X.op ≅ ((SSet.uliftFunctor.{v, u}).obj X).op
```

直積と宇宙の持ち上げの同型は成分ごとの恒等対応である。
ホモトピーを反転すると区間の端点が交換されるため、その向きも交換する。
Kan 性の下では可逆な二胞体の逆を使い、反転した逆射の両合成を恒等射と比較する。
これは Kerodon §4.6.7 の左右の Hom の移送の補助段階であり、
左 coslice の係数図式への実際の自然比較と元の q_x への接続は引き続き未完了。

### 反転した豊穣 Hom から左 coslice fiber への比較（実装済み）

`CoherentLeftHomComparison` は `C : Type v`、`[Category.{u} C]`、
`[SimplicialCategory C]`、`x y : C` に対して次の実際の射を構成する。

```lean
coherentOppositeRightHomComparison (x y : C) :
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y) ⟶
    pinchedHom (X := (SimplicialNerve C).op)
      (SSet.opObjEquiv.symm (coherentNerveVertex y))
      (SSet.opObjEquiv.symm (coherentNerveVertex x))
coherentLeftHomComparison (x y : C) :
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
    pinchedHomLeft (coherentNerveVertex x) (coherentNerveVertex y)
coherentCosliceFiberComparison (x y : C) :
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (coherentNerveVertex y)
```

まず Cᵒᵖ の対象 op(y), op(x) に標準の `coherentHomComparison` を適用する。
その後 `coherentNerveOppositeInverse C` が誘導する右 Hom の射を合成し、
`coherentOppositeHomEndpointIso x y` で二端点を厳密に移す。
この射全体を反転し、`uliftOppositeIso` と `pinchedLeftCosliceFiberIso` で
始域と終域を同定する。射の定義には Kan 性もホモトピー逆の選択も必要ない。

`[∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]` の下で、三つの射はそれぞれ

```lean
coherentOppositeRightHomComparison_homotopyEquivalence (x y : C) :
  IsSimplicialHomotopyEquivalence (coherentOppositeRightHomComparison x y)
coherentLeftHomComparison_homotopyEquivalence (x y : C) :
  IsSimplicialHomotopyEquivalence (coherentLeftHomComparison x y)
coherentCosliceFiberComparison_homotopyEquivalence (x y : C) :
  IsSimplicialHomotopyEquivalence (coherentCosliceFiberComparison x y)
```

を満たす。反対 nerve の逆射は同型なので、その右 Hom の射は trivial Kan fibration。
F1 の標準比較の同値性とこれを合成し、Kan ホモトピー同値の反転による保存を使う。
左 coslice fiber の Kan 性も左 Hom との厳密な同型から移す。

これは Kerodon §4.6.7 と HTT 4.2.4.1 の係数比較の各値の段階である。
始域の反転は明示的で、元の sHom と同じ図式とは扱わない。
添字圏の射・高次整合性を含む係数図式全体への自然比較と、元の q_x との接続は未完了。
したがって γ3b と 𝒮・Sp の残りの適用は引き続き未完了である。

### 標準 Hom 比較の豊穣関手による後合成への自然性（実装済み）

`CoherentHomPost` は共通の対象宇宙 `C D : Type v`、`[Category.{u} C]`、
`[Category.{u} D]`、`[SimplicialCategory C]`、`[SimplicialCategory D]` と
`F : EnrichedFunctor SSet C D` に対し、Kan 性を仮定せず次を証明する。

```lean
coherentHomComparisonObj_post F (x y : C) {n : ℕ} (i : Fin (n + 2)) :
  F.obj (coherentHomComparisonObj x y i) =
    coherentHomComparisonObj (F.obj x) (F.obj y) i
coherentHomComparisonSimplex_post F {x y : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom x y) _⦋n⦌) :
  (coherentHomComparisonSimplex σ).comp SSet F =
    coherentHomComparisonSimplex ((F.map x y).app (Opposite.op ⦋n⦌) σ)
coherentNervePost_vertex F (x : C) :
  (coherentNervePost F).app (Opposite.op ⦋0⦌) (coherentNerveVertex x) =
    coherentNerveVertex (F.obj x)
```

Hom の比較の各分岐で、両端点を標準対象へ移して豊穣関手の単位則と
`yonedaEquiv_symm_comp` を用いる。最後の頂点から前の頂点への Hom は空である。
`pinchedHom_endpointTransport_val` は端点を等号で移しても元の simplex の値が変わらない式。
`coherentHomPostEndpointIso F x y` は後合成で写した端点から標準頂点への厳密な同型である。
これらから単体集合の射として

```lean
coherentHomComparison_post F (x y : C) :
  (SSet.uliftFunctor.{v, u}).map (F.map x y) ≫ coherentHomComparison (F.obj x) (F.obj y) =
    coherentHomComparison x y ≫
      pinchedHomMap (coherentNervePost F) (coherentNerveVertex x) (coherentNerveVertex y) ≫
      (coherentHomPostEndpointIso F x y).hom
```

を証明した。これは任意の次数での厳密な後合成の自然性であり、点ごとの同値の選択ではない。
原典上の位置は Kerodon §4.6.7、HTT 4.2.4.1 の係数比較の自然性である。
添字圏の射が誘導する Hom の合成作用と高次整合性への接続、および左 coslice 側への移送、
元の q_x との一致は未完了。𝒮・Sp の残りの適用も引き続き未完了である。

### 左 coslice の係数を評価する最小点の座標（実装済み）

`CoherentPathMinimum` は `j : Fin (n+1)` と
`P : Path (ULift.up 0 : ULift.{u} (Fin (n+2))) (ULift.up j.succ)` に対して、
零以外の path の頂点を Fin(n+1) の添字で集めた `pathAfterFirst P` を定義する。
この集合は終点を含むので空でない。`pathFirstMinimum P` はその最小元である。
所属、各正頂点以下、終点以下の式を公開した。

```lean
pathFirstMinimum_antitone (h : P.I ⊆ Q.I) :
  pathFirstMinimum Q ≤ pathFirstMinimum P
```

正の切断点 i.succ で合成すると、後半の全点は切断点以上であり、前半の最小点は
切断点以下である。`pathFirstMinimum_comp P Q` はそのため最小点が前半の値に等しいことを示す。
これは HTT 4.2.4.1 の重み付き nerve から左 coslice への比較で必要な豊穣合成の座標則である。

終点までの初区間に値を置いた `pathFirstMinimumIndex P : Fin (j.val+1)` を用い、
その値を反転する単調関手 `pathFirstMinimumReverseFunctor j` と

```lean
pathFirstMinimumMap (j : Fin (n + 1)) :
  nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
    (Δ[j.val] : SSet.{u}).op
```

を構成した。`pathFirstMinimumMap_apply j F k` の値は
`pathFirstMinimumIndex (F.obj k.rev)` に一致する。
Mathlib の path は包含順序なので最小点は反単調であり、この値域の反転を省略しない。

初点固定の拡張は既存 Core の `prependOrderHom` を用いる。
`pathFirstReindex α P` はその拡張で path の部分集合の像を取り、
`pathFirstMinimum_reindex α P` は最小点が α と可換になることを示す。
α は非単射でもよい。さらに初区間内の添字と単体集合の射について

```lean
pathFirstMinimumMap_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (j : Fin (m + 1)) :
  nerveMap (pathFirstReindexFunctor α.toOrderHom j) ≫
    pathFirstMinimumMap (α.toOrderHom j) =
  pathFirstMinimumMap j ≫
    SSet.opFunctor.map (stdSimplex.map (simplexPrefixRestriction α j))
```

を証明した。全ての面・退化を含み、Kan 性・図式の極限性は要求しない。
原典上の位置は Kerodon §4.6.7 と HTT 4.2.4.1 の係数評価である。
これらの座標則を重み付き nerve の実際の左 coslice 射へ組み立てる工程、
元の q_x との一致、および 𝒮・Sp の残りの適用は未完了。

### weighted nerve の係数の実際の評価と合成・添字変換（実装済み）

`WeightedCoherentCoefficients` は `I : Type u`、`[SmallCategory I]`、
`H : I ⥤ SSet.{u}`、`σ : ComposableArrows I n` と反転した係数
`τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor` を扱う。
`reflectedSimplexMap τ_j` は Δ[j] → H(σj).op を反転し、二重反転の標準同型を合成して
Δ[j].op → H(σj) にする。前合成と後合成との厳密な可換性も証明している。

```lean
weightedCoherentCoefficient τ (j : Fin (n + 1)) :
  nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶ H.obj (σ.obj j)
```

は最小点の座標射にこの係数を合成した実際の射である。
`pathFirstMinimumMap_comp i j h` は座標射の合成則を、反転した初区間の包含を明示して与える。
`reflectedWeightedCoefficient_naturality τ i j h` は τ の自然性を反転を戻して計算する。
この二式から、`i j : Fin (n+1)` と `h : i ≤ j` に対して

```lean
weightedCoherentCoefficient_comp τ i j h :
  eComp SSet
    (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
    ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ weightedCoherentCoefficient τ j =
  fst _ _ ≫ weightedCoherentCoefficient τ i ≫ H.map (σ.map (homOfLE h))
```

を証明した。後半の path を無視した係数の評価に、図式の射の作用を合成する式である。
さらに任意の `α : ⦋m⦌ ⟶ ⦋n⦌` に対し、
`weightedCoherentCoefficient_reindex α τ j` は係数を初区間へ制限する操作が
path の `prependOrderHom` による添字変換と厳密に可換となることを示す。
退化を含む全ての単体圏の射を扱い、Kan 性は要求しない。

`WeightedRepresentableCoefficients` は `H := simplicialHomDiagram F x` へ適用する。
`[Category.{u} C] [SimplicialCategory C]`、`x : C`、`f : y ⟶ z` に対し

```lean
simplicialHomWhiskerLeft_app x f d a :
  (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map f).app d a =
    (eComp SSet x y z).app d
      (a, PinchedHom.constant (SimplicialCategory.homEquiv' y z f) d.unop.len)
```

を証明し、表現可能な係数の図式作用を通常の射の定値 simplex との豊穣合成と同定した。
`weightedRepresentableCoefficient_comp F x τ i j h d P Q` は係数の合成則を
この豊穣合成の式で表す。前提は strict な図式、反転した係数の自然変換、順序 i≤j のみ。
P・Q はそれぞれ初点→i.succ、i.succ→j.succ の path nerve の d 単体である。
C の対象の宇宙 v は Hom・I の宇宙 u と異なってよい。

これは HTT 4.2.4.1、Kerodon §7.5.4 の cone の豊穣関手を作る非定値 Hom の合成則である。
cone の全ての頂点と Hom を一つの豊穣関手に組み立て、実際の左 coslice への射とする工程、
元の q_x との一致、および 𝒮・Sp の残りの適用は引き続き未完了。

### 𝒮 の空積（実装済み）

`CoherentTerminal.lean` の `coherentNerve_isTerminalVertex_of_enrichedTerminal t h` は、
局所 Kan な単体的圏において全ての `sHom(x,t)` が単体集合の終対象なら、
`IsTerminalVertex (coherentNerveVertex t)` を証明する。全ての nerve の頂点を元の対象で表示し、
F1 の実際の写像空間比較で可縮性を移して A3d を使う。追加の比較仮定はない。

`SpaceTerminal.lean` は、F1 の既存の `KanObject`・`SpaceInfinity`・`pointSpaceVertex` に対して
次を公開する。`EmptyCone.lean` で空図式の slice 射影の厳密な同型を構成したので、
空積を `IsLimitCone` として公開できる。

```lean
pointSpaceVertex_isTerminalVertex : IsTerminalVertex pointSpaceVertex.{u}
spaceEmptyProductCone : JoinCone (⊥ : SpaceInfinity.{u}.Subcomplex).ι
spaceEmptyProductCone_isLimitCone : IsLimitCone spaceEmptyProductCone.{u}
```

ここでは一般の重み付き end の比較を前提としていない。𝒮 の非空の有限積・引き戻し・塔と、
Sp の空積を含む全ての適用は未完了。

### γ3c：最初に検証する三つの極限

下表は H_x の Kan 図式での条件である。C の射が「fibration」と呼ばれることだけでは代用せず、
全ての x で sHom_C(x,−) が必要な Kan fibration を与えることを検証する。

| 形 | strict な計算と追加条件 |
| --- | --- |
| 有限積（空積を含む） | 各 H_x(i) が Kan。豊穣積の θ_x と、Kan 複体の積が homotopy 積を計算することを証明する |
| 引き戻し A → B ← D | 三つの写像空間が Kan で、少なくとも一方の脚が全ての x で Kan fibration。strict pullback が homotopy pullback を計算することを証明する |
| 塔 … → X₂ → X₁ → X₀ | 各段が Kan で、全ての遷移が全ての x で Kan fibration。逆極限の Kan 性と homotopy 極限との比較を証明する |

𝒮 には F1 の `KanObject` と `SpaceInfinity := SimplicialNerve KanObject` を使う。
写像空間は内部 Hom `Fun(X,Y)`。SSet の全対象が cofibrant であることに対応する直接の
内部 Hom のホーン充填を使い、Kan fibration の引き戻しと塔、有限積を適用例として公開する。
一般の Kan 図式の strict 極限を無条件に ∞ 極限とはしない。

Sp の接続先は L9 の `KST/Spectra/CoherentNerve.lean` にある
`SerrePositivity.KST.Spectra.Sp := SimplicialNerve OmegaSpectrum`。
`OmegaSpectrum` は `sigma_mono` と全基点での `KanPiIsomorphism` の Ω 条件を保持し、
`OmegaSpectrum.simplicialCategory` と `OmegaSpectrum.mappingSpace_kanComplex` は構成済みである。
この模型の局所 Kan 性を利用し、levelwise の極限が対象の条件を満たすことを別途検証する。
単体的モデル圏から raw sHom を使うときは cofibrant な始対象と fibrant な終対象が必要なので、
単に「全対象が Ω スペクトル」という条件だけで局所 Kan 性を主張しない。
cofibrant かつ fibrant な Ω スペクトルの充満部分圏を使うか、同じ導来写像空間を与える模型を選ぶ。
levelwise に strict 極限を作った後も、Ω 条件・fibrant 性・豊穣 Hom の保存を個別に確認する。
その極限が cofibrant でない場合は cofibrant-fibrant 置換 L° → L を取り、
L° から元の図式への錐が同じ homotopy 普遍性を持つことを比較してから Sp の極限として公開する。
A° が strict 極限で閉じていることを暗黙に仮定しない。
E2b（Alg_E）への適用は E2a 完了後に行う。

### 宇宙・配置・完了条件

Hom の宇宙を u、C の対象の宇宙を v とし、まず I : Type u と Hom も u の小圏を扱う。
H_x とその極限は SSet.{u}、coherent nerve は SSet.{max u v} に置き、
N(I) と錐の shape の ULift を明示する。𝒮 は対象型のため SSet.{u+1} となる。
異なる図式の宇宙への一般化は、そのサイズの極限の存在と持ち上げの同型を前提として明示する。

実装は `InfinityCategories/HomotopyLimits/` と専用の集約・公理監査に置き、Core・F1・Sp の
他レーンのソースは編集しない。新しい sorry・axiom・未証明の引用を導入せず、公開宣言の
正確な型・全前提・依存公理を検査する。モデル構造を使う範囲は古典的対象の ∞ 圏化に限る。
γ3b の完了には錐の pinched Hom と導来ファイバーの比較および極限錐の定理、
γ3c の完了には 𝒮 と Sp の三つの適用の公開と対象ビルド・標準三公理の監査が必要。
この紙の記録と原典の照合だけを γ3b・γ3c の完成とは数えない。
