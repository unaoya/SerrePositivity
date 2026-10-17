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
