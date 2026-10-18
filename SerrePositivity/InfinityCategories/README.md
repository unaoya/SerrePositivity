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

γ1.5a（紙の設計）は完了。以下は γ1.5b 以降の実装で用いる設計と規約の正本。
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

現在地：γ1.5a の設計記録と γ1.5b の単体的圏 C_Δ の構成・局所 Kan 性が完了。
namespace `DoldKanComparison` の `homModule x y : SimplicialObject (ModuleCat.{u} R)` と
`homSpace x y : SSet.{u}` は N4 の線形解を全ての単調写像に関してまとめたもの。
`homSpaceLiftIso x y` は `SSet.uliftFunctor.{v,u}.obj (homSpace x y)` と
`DGNerve.pinchedHom R D x y` の自然同型であり、次数ごとの同値だけではない。
`homSpaceKan x y : SSet.KanComplex (homSpace x y)` は N4 の直接の線形充填から従う。
宇宙の持ち上げが Kan 性を反映する一般補題 `kanComplex_of_ulift` も証明した。
`degreeSign` は ε_k を二項係数で実装し、`degreeSign_differential` が微分の符号の変換、
`degreeSign_cut` が AW 合成での交差符号を与える。符号による作用は二度で恒等になる。
`homSpaceVertexCycleEquiv` は零単体と閉次数零元の同値、`closedHomVertexEquiv` は
`ClosedCategory R D` の射と零単体の同値である。まだ合成の保存を主張していない。
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
この同型はまだ coherent nerve の写像空間との比較ではない。
対象・集約ビルドは3717件で成功し、公開332宣言の型と公理監査は標準三公理のみ。
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
残りは γ1.5c の dg nerve への比較写像と低次の一致、γ1.5d の写像空間の比較および同値の証明。

γ1.5c は進行中。`cubeFlag e` は任意の番号付け `e : Fin m ≃ T` に対して、
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

まだ dg nerve への単体集合の射は得ていない。全置換の和から区間を保つ置換の組への再添字付け、
その和と Path の合成面の対応、dg 単体の方程式、退化も含む自然性、
および比較写像の頂点・辺・三角形での一致が残る。


## γ3：homotopy 極限・余極限と ∞ 極限・余極限（γ1.5 の後）

担当と順序は `formalization-plans/foundations.md` §1・§4 と
`formalization-plans/e-infinity-algebras.md` §3 に従う。γ1.5 の完了後に着手し、
𝒮（F2）・Sp（L9）・E2b が共用する比較を作る。第一段階は単体集合の Quillen モデル構造と、
その cofibrant-fibrant 対象である Kan 複体の単体的圏を扱う。
原典は [HTT §4.2.4、特に Theorem 4.2.4.1](https://www.math.ias.edu/~lurie/papers/HTT.pdf)。
coherent nerve の写像空間の比較には
[Kerodon §4.6.7](https://kerodon.net/tag/01LA) を使う。

方針は、局所 Kan な単体的圏の homotopy coherent な錐の写像空間を、coherent nerve の
錐の写像空間へ比較し、モデル側の homotopy 極限・余極限の普遍性を Core の ∞ 圏の
極限・余極限の普遍性へ送ることである。まず 𝒮 := N^hc(Kan) で証明し、
余極限の値には必要な Kan 置換を施す。通常の極限・余極限との無条件な同一視や
π₀ の普遍性だけを完成とは数えない。小さい図式の宇宙と対象の宇宙を区別し、
厳密な図式と homotopy coherent な図式の比較も証明すべき工程に含める。

後続では同じ写像空間による判定を単体的モデル圏の cofibrant-fibrant 部分へ一般化し、
Sp の ∞ 極限、E2b の右 Quillen 関手による ∞ 極限保存へ接続する。
Quillen 随伴から ∞ 随伴への比較（HTT 5.2.4.6 型）も §3 の後続項目として保持する。
モデル構造を使う範囲はこの古典的モデルの ∞ 圏化に限り、F0 の一般論の前提を変更しない。
新しい sorry・axiom・未証明の引用は導入しない。現在は着手前の設計記録であり、γ3 の成果は未実装。
