# infinity-categories-readme の記録（2026-10-19 に本文から移動）

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

Semifree への適用前に、`formalization-plans/archive/stage-i/infinity-lanes/derived-infinity-category.md` の
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

担当は N。正本は `formalization-plans/archive/stage-i/infinity-lanes/e-infinity-algebras.md` §3 と
`formalization-plans/archive/stage-i/infinity-lanes/foundations.md` §1。γ1.5 の完了後に続けて担当し、
𝒮（F2）・Sp（L9）・E2b の三者が共有する比較を作る。

担当と着手順（foundations.md §1 の決定）：γ1.5 の後に N が γ3 を担当する。
目標は homotopy 極限・余極限と ∞ 極限・余極限の比較（HTT 4.2.4.1 型）であり、
まず Kan 複体の単体的モデル圏の cofibrant-fibrant 部分圏を対象とする。
初段は通常の小圏の strict な図式について、有限積・fibration 引き戻し・塔の極限を扱う。
豊穣 Hom の標準比較 q_x と coherent な錐の比較を証明し、𝒮（F2）、Sp（L9）、
E2b が再利用できる形で公開する。余極限側は後続工程とし、極限側の部分成果で完了とはしない。
E2b の具体的適用は E2a の完了後に行う。

現在は γ3a の限定形の記録と、γ3b の任意の小圏での両向きの可縮性判定・直接比較まで実装済み。
局所 Kan な単体的圏の通常の錐について、添字の形状や Hom の遷移の fibration 性を仮定せず、
実際の coherent nerve の錐が ∞ 極限錐であることは、
全ての x と元の Bousfield–Kan end の全頂点 b で
`comparisonFiber (representableHomotopyLimitComparison c x) b` が可縮 Kan であることと同値。
元の q_x の fibration 性や Hom 錐の厳密極限性は、この判定の前提に要求しない。
反転比較との照合、ULift の同値検出、A3d に基づく native な切断判定を介して証明する。
反転・ULift 後の切断比較の導来 fiber から native な制限の導来 fiber への実際の比較射も、
任意の添字圏と通常の錐で構成し、局所 Kan 性の下で同値性を証明している。
任意の coherent な錐 d・c の pinched Hom と標準の切断制限の実際の導来 fiber の同値も
構成済み。底の固定点は元の d の標準の切断の点そのもので、共通模型で厳密に照合している。
さらに三形状では、反転豊穣比較 q′ の ULift 後の導来 fiber までの同値を公開済み。
標準切断点は end の比較同値の逆で回収し、その像とのずれは底の path で移送する。
導来 fiber と ULift の厳密な交換同型により、三形状の比較は元の宇宙の q′ の fiber 全体を
持ち上げた模型まで移送済み。三形状では、元の非反転 q_x の fiber と pinched Hom の
反転なしの直接の同値まで公開した。Kan な fiber の反転を実際の同値で外している。

γ3c の指定三形状は 𝒮・Sp の双方で実際の対象と ∞ 極限錐を公開済み。
𝒮 は小さな積、一脚 Kan fibration の引き戻し、Kan fibration の可算塔の極限。
Sp は空積を含む有限積、一脚が全段で fibration の引き戻し、全隣接遷移が全段で fibration の塔。
Sp の極限対象の段は置換せず、Kan 性・構造射の単射性・全基点全次数の Ω 条件を証明している。

余極限側は着手済み。通常の余錐を元の標準図式上の native な余錐として構成し、頂点と
反対の極限性による双対判定を検証した。離散添字では全反変 Hom の極限性から余極限性を導き、
Kan 複体の余錐では台の余極限性からこの Hom 条件を検証する。
𝒮 の実際の小さい余積を、空余積を含めて Kan 性・台の普遍性とともに公開した。
通常の余錐の各脚と元の射の厳密な一致、および余積の成分包含との一致も検証した。
単射な遷移を持つ Kan 複体列の実際の逐次余極限は、対象・余錐・各脚とともに公開した。
左脚の台が単射な span の通常の押し出しを Kan 置換した実際の ∞ 押し出しも公開した。
任意の span は左脚を単射と trivial Kan fibration に分解して置換し、成分ごとの同値で
元の図式へ余極限余錐を輸送した。元の両脚に条件なく、実際の ∞ 押し出しと頂点を公開した。
一般の遷移を持つ列も、各段の境界分解で単射な列へ置換し、元の図式へ輸送することで
実際の homotopy 逐次余極限・native な余極限余錐・頂点の等号を構成した。
任意の小圏上の反転係数の end と切断の比較、およびその極限・余極限判定も公開した。
この一般形状では q′ の全導来 fiber の可縮性による両向き判定も証明済み。
任意の coherent な錐から strict な錐への pinched Hom は、標準点から回収した反転 end の
点における q′ の導来 fiber 全体の ULift と、追加の比較仮定なしで直接同値である。
さらに任意の小圏で、edgewise 共通解像に沿って反転比較を元の q_x へ移し、元の q_x の
同値性・全導来 fiber の可縮性と native な極限・余極限性の両向き判定を証明した。
任意の coherent な d からの pinched Hom も、回収した元の end の点での非反転 q_x の
導来 fiber 全体の ULift と直接同値にした。追加の比較仮定は不要で、fiber の反転も残らない。
E2a 完了後の E2b 適用と一般の小さい余極限の構成・Quillen 随伴への適用等は残る。
この一般形状の可縮性判定と直接比較を、γ3 全体の完成とは数えない。
以下に限定形と工程ごとの型・検証の記録を置く。

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
公開844宣言の正確な型・全前提・依存公理は `scripts/audit_homotopy_limits.lean` が正本。

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
`H := simplicialHomDiagram F x` に要求する。正確な全型は公開844宣言の監査に記録。
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

### weighted nerve から coherent な錐の全空間への実際の射（実装済み）

`WeightedConeSimplex` は `I : Type u`、`[SmallCategory I]`、`C : Type v`、
`[Category.{u} C]`、`[SimplicialCategory C]` と `F : I ⥤ C`、`x : C` に対し、
反転した表現可能な係数の simplex を coherent な cone simplex にする。

```lean
weightedConeSimplex F x {n : ℕ} {σ : ComposableArrows I n}
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor) :
  (SimplicialNerve C) _⦋n + 1⦌
weightedConeSimplex_apex F x τ :
  (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
    (weightedConeSimplex F x τ) = coherentNerveVertex x
weightedConeSimplex_tail F x τ :
  (SimplicialNerve C).δ 0 (weightedConeSimplex F x τ) =
    (strictCoherentDiagram F).app (Opposite.op ⦋n⦌) (ULift.up σ)
```

`weightedConeObj` は初点を x、正頂点 j.succ を F(σj) に写す。
`weightedConeHom` は初点の自己 Hom を恒等、初点からの Hom を係数評価、
正頂点から初点への空の Hom を `weightedConeEmptyMap`、
正頂点間を `weightedConeTailHom` の通常の射の定値 simplex にする。
単位則と合成則の八分岐を検証し、非定値部分には
`weightedRepresentableCoefficient_comp` を用いた。
`weightedConeSimplex_reindex F x α τ` は初点固定の `prependOrderHom` による
thickening の前合成と全ての面・退化の作用の可換性を与える。

`WeightedCosliceComparison` は join の同型でこの simplex を左 coslice に写す。
`weightedCosliceSimplex`、`weightedCosliceSimplex_naturality`、
`weightedCosliceSimplex_projection` が各次数の構成・自然性・底の計算である。

```lean
weightedCosliceComparison F x :
  (SSet.uliftFunctor.{v, u}).obj
    (weightedNerve (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ⟶
  sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x))
weightedCoherentConeComparison F x :
  (SSet.uliftFunctor.{v, u}).obj
    (weightedNerve (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ⟶
  coherentConeTotal (strictCoherentDiagram F) (coherentNerveVertex x)
weightedCoherentConeComparison_over F x :
  weightedCoherentConeComparison F x ≫
    coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x) =
  (SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))
```

`weightedCosliceComparison_over` は左 coslice の射影との可換性を与え、
引き戻しへの持ち上げで `weightedCoherentConeComparison` を定義する。
これで添字圏の作用と高次 simplex の整合性を持つ実際の底上の射ができた。
Kan 性・図式の極限性・Hom のホモトピー逆の選択は一切要求しない。
原典は HTT 4.2.4.1、Kerodon §7.5.4。

この射の各 fiber の同値性はまだ未証明であり、点ごとの既存の Hom の同値だけで
射全体の同値性を結論しない。始域には係数の反転があるので、その切断空間の移送と
元の q_x との一致も証明対象である。𝒮・Sp の残りの適用を含む γ3b・γ3c は未完了。

### 一定の底での fiber 比較と左右の座標の照合（実装済み）

`ReflectedPathCoordinates` は `j : Fin (n+1)` と初点零から j.succ への path P を扱う。
`reflectedFirstPath P` は頂点を全て Fin.rev で反転した path であり、
始点は j.rev.castSucc、終点は最後の頂点となる。
`reflectedFirstPath_mem` と `reflectedFirstPath_maximum` は

```lean
ULift.up k.castSucc ∈ (reflectedFirstPath P).I ↔ ULift.up k.rev.succ ∈ P.I
pathLastMaximum (reflectedFirstPath P) = (pathFirstMinimum P).rev
```

を与える。包含圏の関手 `reflectedFirstPathFunctor` と、その最大点の射の評価も公開した。
`reflectedFirstPathMaximumMap` は最小点の射に反転した初区間の包含と
標準単体の反転を合成すると、反転 path の最大点の射になることを示す。
`reflectedYonedaMap` は反転した空間の simplex の Yoneda 射を反転して戻す式。
これらから任意の `X : SSet.{u}` と `s : X.op _⦋n⦌` に対し

```lean
reflectedConstantCoefficient s j :
  pathFirstMinimumMap j ≫ reflectedSimplexMap
    (stdSimplex.map (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
      SSet.yonedaEquiv.symm s) =
  nerveMap (reflectedFirstPathFunctor j) ≫ pathLastMaximumMap j.rev ≫
    SSet.yonedaEquiv.symm (SSet.opObjEquiv s)
```

を証明した。全ての次数での厳密な式で、Kan 性を要求しない。

`WeightedConstantFiber` は `F : I ⥤ C`、`x : C`、`i : I` に対して
一定の底の包含と構成済みの比較射を合成し、
`weightedConstantCosliceMap_projection` で終点が F(i) に定値であることを証明する。

```lean
weightedConstantCosliceFiberMap F x i :
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
  vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex (F.obj i))
```

はその実際の fiber への持ち上げである。
`weightedConstantCosliceFiberMap_simplex F x i s` は元の simplex が
`weightedConeSimplex F x (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙
SSet.opFunctor) i s)` に一致することを示す。
`weightedConstantConeHom_zero_succ F x i s j` はその非定値 Hom の作用を
反転した path の右最大点による評価として計算する。

一方、`coherentLeftHomComparison_simplex x y s` は既存の左 Hom 比較の元の simplex が

```lean
coherentOppositeInverseSimplex
  (coherentHomComparisonSimplex (X := Opposite.op y) (Y := Opposite.op x)
    (SSet.opObjEquiv s))
```

であることを示す。pinched Hom の端点の等号による移送は元の simplex を変えない。
原典は Kerodon §4.6.7、HTT 4.2.4.1。

これで二つの射の座標を比較できる形になったが、coherent simplex 全体の一致と
実際の fiber 射の同値性はまだ未証明である。元の q_x と切断空間への接続、
𝒮・Sp の残りの適用も未完了であり、この座標の照合だけで γ3b の完成とはしない。

### 一定の底の fiber 射と標準左 Hom 比較の厳密な一致（実装済み）

`WeightedConstantSimplex` は `I : Type u`、`[SmallCategory I]`、`C : Type v`、
`[Category.{u} C]`、`[SimplicialCategory C]`、`F : I ⥤ C`、`x : C`、`i : I` に対して、
一定の底で作った coherent simplex 全体を反対圏の右 Hom の標準 simplex と比較する。

```lean
weightedConstantConeSimplex_eq F x i {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) :
  weightedConeSimplex F x
    (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) =
  coherentOppositeInverseSimplex
    (coherentHomComparisonSimplex (X := Opposite.op (F.obj i)) (Y := Opposite.op x)
      (SSet.opObjEquiv s))
```

頂点は Fin.rev の初点・正頂点での場合分けにより対応する。
Hom では反転後の二端点を標準の端点へ移送してから、既存の右 Hom の移送の式を使う。
非定値 Hom は最小点と反転 path の最大点の射の等式、
同じ対象間は豊穣恒等、正頂点から初点への Hom は空であることに帰着する。
反転 thickening の Hom の端点を移送しても path の部分集合は変わらないことを明示する。

coslice の座標の単射性を使い、実際の射として

```lean
weightedConstantCosliceFiberMap_eq F x i :
  weightedConstantCosliceFiberMap F x i = coherentCosliceFiberComparison x (F.obj i)
```

を証明した。二つの構成の射そのものの厳密な一致で、Hom の逆射を選び直さない。
したがって局所 Kan 性だけで

```lean
weightedConstantCosliceFiberMap_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) (i : I) :
  IsSimplicialHomotopyEquivalence (weightedConstantCosliceFiberMap F x i)
```

を得る。追加の比較同値の仮定はない。原典は Kerodon §4.6.7、HTT 4.2.4.1。

残るのは、この一定の底での射を weighted nerve の持ち上げた fiber と
coherent cone の引き戻しの fiber の標準同型に沿って移し、
`weightedCoherentConeComparison` が誘導する各 fiber の射に同定する工程である。
その後の切断空間の移送、元の q_x との一致、𝒮・Sp の残りの適用は未完了。
γ3b・γ3c の完成とはまだ数えない。

### 全体の比較射の各 fiber の同値性（実装済み）

`UniverseVertexFiber` は任意の射 p : E→B と頂点 b に対し、

```lean
uliftVertexFiberIso (p : E ⟶ B) (b : B _⦋0⦌) :
  (SSet.uliftFunctor.{v, u}).obj (vertexFiber p b) ≅
  vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)
```

を各次数で ULift と部分型を交換して構成した。包含との厳密な可換性と、
固定頂点を等号で移した fiber の包含が変わらない式も証明している。

`WeightedConeFiberEquivalence` は `F : I ⥤ C`、`x : C`、`i : I` に対し
`weightedConeSourceFiberIso` で持ち上げた weighted nerve の fiber を
反転した sHom(x,F(i)) の ULift と同定する。
`weightedConeTargetFiberIso` は coherent cone の引き戻しの fiber を
始点 x・終点 F(i) の左 coslice fiber と同定する。
どちらも包含後の式を明示し、以下の実際の fiber 射との因子分解を証明した。

```lean
weightedCoherentConeFiberMap F x
    (b : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
  vertexFiber ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))) b ⟶
  vertexFiber (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x)) b
weightedCoherentConeFiberMap_factorization F x i :
  (weightedConeSourceFiberIso F x i).hom ≫
    weightedCoherentConeFiberMap F x (ULift.up (nerveVertex i)) ≫
    (weightedConeTargetFiberIso F x i).hom = weightedConstantCosliceFiberMap F x i
```

この射の定義は `weightedCoherentConeComparison F x` とその底上の可換性に
`vertexFiberMap` を適用したものである。別に選んだ点ごとの同値には置き換えない。
局所 Kan 性の下で、両端の同型から fiber の Kan 性を移し、
一定の底で証明した実際の射の同値性から同型を消去することで

```lean
weightedCoherentConeFiberMap_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    (F : I ⥤ C) (x : C) (b : ((SSet.uliftFunctor.{v, u}).obj (nerve I)) _⦋0⦌) :
  IsSimplicialHomotopyEquivalence (weightedCoherentConeFiberMap F x b)
```

を証明した。`weightedCoherentConeFiberMap_homotopyEquivalence_at F x i` は
標準頂点の場合。任意の底の零単体は元の圏の対象で表示できるため、上の全頂点版に追加仮定はない。
C の対象の宇宙 v と Hom・I の宇宙 u は異なってよい。
原典は HTT 4.2.4.1、Kerodon §7.5.4。

残るのは反転した係数の weighted nerve と coherent cone の全空間の切断空間の比較、
反転・ULift・底の nerve の同型に沿う移送、元の q_x との一致である。
𝒮・Sp の残りの適用を含む γ3b・γ3c は未完了。

### left fibration の宇宙の持ち上げと切断比較の実際の射（実装済み）

`UniverseLeftFibration` は元の射 p : E→B に指定した一つのホーンの相対持ち上げ性だけを仮定して、
その宇宙の持ち上げで同じ持ち上げ性が成り立つことを証明する。

```lean
ulift_hasLiftingProperty_horn {E B : SSet.{u}} (p : E ⟶ B)
    (n : ℕ) (i : Fin (n + 2)) [HasLiftingProperty (horn.{u} (n + 1) i).ι p] :
  HasLiftingProperty (horn.{max u v} (n + 1) i).ι ((SSet.uliftFunctor.{v, u}).map p)
leftFibration_uliftFunctor_map {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
  LeftFibration ((SSet.uliftFunctor.{v, u}).map p)
```

各ホーン面と底の simplex を `uliftSimplexHomDown` で元の宇宙へ戻す。
`uliftSimplexHomDown_post` と既存の面への制限の式で相対可換条件を移し、
互換な面を貼り合わせて元の射の相対充填を使う。
その充填 simplex を Yoneda の同値で持ち上げ、全ての面と底の条件を確認する。
異なる宇宙の単体集合間の射や、p の Kan fibration 性は仮定しない。
最後以外のホーンへ適用して上の left fibration 性の保存を得る。

`WeightedConeSections` は `F : I ⥤ C` と局所 Kan な C に対して
`weightedConeSource_leftFibration` により反転豊穣係数の持ち上げた weighted nerve の射影が
left fibration であることを証明する。図式の各射の fibration 性は不要。
`weightedConeSourceSections_kanComplex F x` はその切断空間の Kan 性である。

```lean
weightedCoherentConeSectionsComparison F x :
  simplicialSections ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))) ⟶
  coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)
```

は構成済みの全体の底上の射で切断を後合成し、coherent cone の切断模型との厳密な同型を
合成した実際の射である。射の定義には Kan 性・極限性を要求しない。
C の対象の宇宙 v と Hom・I の宇宙 u は異なってよい。
原典は HTT 4.2.4.1、Kerodon §7.5.4。

切断比較の同値性、底の nerve の同型と反転・ULift を通じた重み付き end への移送、
元の q_x との一致、および 𝒮・Sp の残りの適用は未完了。

### 底の厳密な同型による移送と三形状の切断比較の同値性（実装済み）

`SectionsBaseIso` は任意の `p : E ⟶ K` と `e : K ≅ L` に対し、

```lean
simplicialSectionsBaseIso p e : simplicialSections p ≅ simplicialSections (p ≫ e.hom)
```

を構成した。順方向は普遍的な切断の族を e.inv で前合成し、逆方向は e.hom で前合成する。
評価の一意性と二因子の交換則で両方の往復則を示す。fibration 性・Kan 性は不要。
`simplicialSectionsBaseMap_naturality`は全体の底上の射が誘導する切断写像との厳密な自然性である。

`FibersBaseIso` は left fibration の射影の同型による後合成での保存、
`vertexFiberBaseIso p e b` と包含の式、実際の fiber 射との自然性を証明する。
全頂点上の fiber 射の同値性を新しい底の全頂点へ移す式と、
切断写像の同値性が底の同型の前後で同値となる判定も公開した。
`SectionsShapeBaseIso` はこれを既存の離散・cospan・塔の切断比較へ適用する。

`LiftedShapeNerveIso` は厳密な逆関手から nerve の厳密な同型を作り、

```lean
liftedDiscreteNerveIso (J : Type u) :
  (SSet.uliftFunctor.{v, u}).obj (nerve (Discrete J)) ≅ nerve (Discrete (ULift.{v, u} J))
liftedAsSmallNerveIso (J : Type) [SmallCategory J] :
  (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} J)) ≅ nerve (AsSmall.{max u v} J)
```

を構成する。後者は WalkingCospan と ℕᵒᵖ の双方へ適用する。
単なる圏同値ではなく厳密な逆関手を使うため、底の変更に上の同型の結果をそのまま使える。

`WeightedConeSectionEquivalence` は `C : Type v`、`[Category.{u} C]`、
`[SimplicialCategory C]`、`[∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]` の下で

```lean
weightedCoherentConeSectionsComparison_discrete_homotopyEquivalence
    {J : Type u} (F : Discrete J ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x)
weightedCoherentConeSectionsComparison_cospan_homotopyEquivalence
    (F : AsSmall.{u} WalkingCospan ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x)
weightedCoherentConeSectionsComparison_tower_homotopyEquivalence
    (F : AsSmall.{u} ℕᵒᵖ ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x)
```

を証明した。比較射は構成済みの全体の射による後合成のままで、
全頂点の実際の fiber 射の同値性を底の標準同型を通じて三形状の判定に渡す。
C の対象と Hom の宇宙は異なってよい。図式の射に fibration 性を仮定せず、
離散図式には有限性も要求しない。原典は HTT 4.2.4.1、Kerodon §7.5.4。

始域は反転した豊穣係数の weighted nerve の射影の ULift の切断空間である。
その反転と ULift を元の `sHom(x,F−)` の Bousfield–Kan end へ移す比較、
元の q_x と cone の写像空間の射との一致、𝒮・Sp の残りの適用は未完了。
したがってこの三形状の切断比較の同値性だけで γ3b・γ3c の完成とはしない。

### 切断空間の ULift 同型と反転豊穣 Hom の end からの実際の比較（実装済み）

`UniverseSSetMaps` は型の ULift の完全忠実性を関手圏へ移して
単体集合の ULift 関手の充満性・忠実性を構成した。
`uliftTensorIso X Y` は ULift された対と ULift の対を交換する直積の同型、
`uliftStdSimplexIso n` は標準単体の二段の ULift を大きい宇宙の一段の ULift にする同型。
直積の同型の第二因子の自然性と、同型を通じた Yoneda 射の式も公開した。

`UniverseSections` は任意の `p : E ⟶ K` に対し

```lean
uliftSectionsComparison p :
  (SSet.uliftFunctor.{v, u}).obj (simplicialSections p) ⟶
  simplicialSections ((SSet.uliftFunctor.{v, u}).map p)
uliftSectionsIso p :
  (SSet.uliftFunctor.{v, u}).obj (simplicialSections p) ≅
  simplicialSections ((SSet.uliftFunctor.{v, u}).map p)
```

を構成し、同型の順方向が上の標準比較射であることを保持する。
標準比較は普遍的な評価を持ち上げ、直積の同型を前合成して作る。
小さいパラメータ A からの切断と ULift(A) からの持ち上げた切断の全単射を、
ULift の完全忠実性と普遍的な評価で構成した。
逆対応は直積の同型を前合成した評価の族の原像を取り、底を固定することを忠実性で検出する。
標準単体へ適用して各次数の全単射を得て、実際の標準比較が同型であることを示す。
Kan 性・fibration 性・極限性の仮定はない。

`ReflectedHomHolimComparison` はこの同型と既存の `bousfieldKanSectionsIso` を使い、

```lean
reflectedHomHolimConeComparison (F : I ⥤ C) (x : C) :
  (SSet.uliftFunctor.{v, u}).obj
    (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ⟶
  coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)
```

を定義した。射の定義は任意の小圏 I と単体的圏 C に対し、局所 Kan 性なしで成立する。
全ての豊穣 Hom が Kan のとき、以下を証明した。

```lean
reflectedHomHolimConeComparison_discrete_homotopyEquivalence
    {J : Type u} (F : Discrete J ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x)
reflectedHomHolimConeComparison_cospan_homotopyEquivalence
    (F : AsSmall.{u} WalkingCospan ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x)
reflectedHomHolimConeComparison_tower_homotopyEquivalence
    (F : AsSmall.{u} ℕᵒᵖ ⥤ C) (x : C) :
  IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x)
```

持ち上げた二つの厳密な同型と三形状の実際の切断比較の同値性を合成する。
離散対象に有限性を要求せず、図式の射の fibration 性もこの比較には不要。
C の対象の宇宙 v と Hom・I の宇宙 u は異なってよい。
原典は HTT 4.2.4.1、Kerodon §7.5.4。

これで始域の ULift を切断空間の外へ移したが、係数は依然として反転した sHom である。
元の sHom の end や q_x と同一視せず、その反転の移送と strict な錐の比較射との整合性を
次の証明対象として残す。𝒮・Sp の残りの適用を含む γ3b・γ3c は未完了。

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


### 反転した strict Hom 錐の標準比較と切断模型への合成

`OppositeFibration` は全ホーンの相対充填を反転同型で移し、Kan fibration の反転を証明する。
`ReflectedRepresentableComparison` は反転した Hom 錐の極限性、実際の標準比較 q′、
Hom の始対象に関する反変自然性を構成する。DoldKanComparison の既存の
`ulift_homotopyEquivalence` を再利用し、三形状で coherent な錐の切断模型への実際の合成が
ホモトピー同値であることまで証明した。原典上の位置は HTT 4.2.4.1 の双対、
Kerodon 7.5.3.12、7.5.4.6 の strict な錐との比較である。

以下の共通変数は `I : Type u`、`[SmallCategory I]`、`C : Type v`、
`[Category.{u} C]`、`[SimplicialCategory C]`、`F : I ⥤ C`、`c : Cone F`、`x : C`。
新規公開宣言の型は次の通り（全暗黙引数・宇宙・前提は監査スクリプトの `#check @` にも記録）。

```lean
fibration_opFunctor_map {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p] :
  Fibration (SSet.opFunctor.map p)
reflectedSimplicialHomCone (c : Cone F) (x : C) :
  Cone (simplicialHomDiagram F x ⋙ SSet.opFunctor)
reflectedSimplicialHomCone_isLimit (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) :
  IsLimit (reflectedSimplicialHomCone c x)
reflectedRepresentableComparison (c : Cone F) (x : C) :
  (SimplicialCategory.sHom x c.pt).op ⟶
    bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)
reflectedRepresentableComparison_naturality (c : Cone F) {x y : C} (f : x ⟶ y) :
  SSet.opFunctor.map (((SimplicialCategory.sHomFunctor C).map f.op).app c.pt) ≫
      reflectedRepresentableComparison c x =
    reflectedRepresentableComparison c y ≫ (bousfieldKanHolimFunctor I).map
      (Functor.whiskerRight (simplicialHomDiagramPre F f) SSet.opFunctor)
reflectedStrictConeSectionsComparison (c : Cone F) (x : C) :
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
    coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)
```

反転した錐の脚は元の Hom 錐の脚を反転関手で写したもの。q′ はこの錐から直接作る
`bousfieldKanConeComparison` であり、同値の存在から選んだ別の射ではない。
最後の切断比較は `uliftFunctor.map q′ ≫ reflectedHomHolimConeComparison F x` と定義する。
反転の極限保存にも元の通常の錐の極限性ではなく `IsLimit (simplicialHomCone c x)` を使う。

残る六宣言の正確な型・前提は次の通り。

```lean
reflectedRepresentableComparison_discrete_isIso {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) :
  IsIso (reflectedRepresentableComparison c x)
reflectedRepresentableComparison_cospan_homotopyEquivalence
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .one))]
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj .right))]
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
  IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)
reflectedRepresentableComparison_tower_homotopyEquivalence
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [KanComplex ((simplicialHomDiagram F x).obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
  IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)
reflectedStrictConeSectionsComparison_discrete_homotopyEquivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : Discrete J ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x)) :
  IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)
reflectedStrictConeSectionsComparison_cospan_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
  IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)
reflectedStrictConeSectionsComparison_tower_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    (hc : IsLimit (simplicialHomCone c x))
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
  IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)
```

離散図式の q′ の同型性には Kan 性や添字の有限性は不要。cospan の q′ には中央と右端の
Kan 性と左脚の fibration 性のみを要求し、右脚の条件を加えない。塔の q′ には零段の Kan 性と
全隣接遷移の fibration 性を要求する。切断模型への三つの合成には局所 Kan 性を使う。

係数の反転を元の Hom 図式の end へ自然に移す比較、元の q_x との整合性、
`reflectedStrictConeSectionsComparison` と native な strict 錐の Hom 比較との一致は未完了。
したがって、この合成の同値性だけから strict な錐の `IsLimitCone` は結論していない。
𝒮・Sp の残りの適用と余極限の比較も未完了のまま保持する。

検証：`lake build SerrePositivity.InfinityCategories.HomotopyLimits` 成功（4434 jobs）、
`scripts/audit_homotopy_limits.lean` の公開856宣言の `#check @` と公理監査が成功。
標準3公理のみ。新規ファイルに警告・sorry・追加公理はない。
集約から再帰的に辿る他担当の700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-reflected-strict-aggregate.log` と
`/tmp/gamma3-reflected-strict-audit.log`。


### strict な錐の全パラメータでの評価と各脚との整合性

`StrictConeWeightedEvaluation` は任意の `H : I ⥤ SSet.{u}` と `c : Cone H` に対し、
標準比較を weighted nerve の族へ評価すると、第二射影と c の脚から直接作る族に一致することを
証明する。各初区間の係数は `stdSimplex.map prefix ≫ a ≫ c.π.app (σ.obj j)`。
底を対象 i に固定したときは `c.π.app i ≫ weightedNerveConstantLift H i` に一致する。
これらは Kan 性・極限性なしで全次数・全パラメータについて厳密に成立する。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の strict な錐の主比較の整合性。

以下は `universe u`、`{I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}` の下の正確な型。

```lean
lemma bousfieldKanConeComparison_weightedNerveEvaluation (c : Cone H) :
    (nerve I ◁ bousfieldKanConeComparison c) ≫ bousfieldKanWeightedNerveEvaluation H =
      weightedNerveSectionFromTransform
        (snd (bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π)
lemma weightedNerveCoefficients_cone_app (c : Cone H) {n : ℕ}
    (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ c.pt) (j : Fin (n + 1)) :
    (weightedNerveCoefficients
      (snd (bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) σ a).app j =
    stdSimplex.map (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
      a ≫ c.π.app (σ.obj j)
lemma bousfieldKanConeComparison_sections_evaluation (c : Cone H) :
    (nerve I ◁ (bousfieldKanConeComparison c ≫ bousfieldKanSectionsMap H)) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
    weightedNerveSectionFromTransform
      (snd (bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π)
lemma weightedNerveSectionFromCone_constant (c : Cone H) (i : I) :
    lift (SSet.const (nerveVertex i)) (𝟙 c.pt) ≫ weightedNerveSectionFromTransform
      (snd (bousfieldKanWeight I) ((Functor.const I).obj c.pt) ≫ c.π) =
    c.π.app i ≫ weightedNerveConstantLift H i
```

`ReflectedStrictConeEvaluation` は切断空間・引き戻し・ULift・重み付き end の評価を順に戻し、
`reflectedStrictConeSectionsComparison` の相対関手としての普遍的な族を同定する。
終域の coslice への族は、反転した Hom 錐の脚から作る weighted nerve の族を ULift で写して
`weightedCosliceComparison F x` に合成した射と厳密に一致する。
非定値 Hom の係数も、初区間の最小点の座標、反転したパラメータ a、実際の錐の脚による
sHom の後合成という式へ分解した。

さらに `reflectedStrictConeSectionsComparison_evaluate` は任意の i で底を固定すると、
錐の脚 `c.π.app i` による sHom の後合成を反転・ULift した射と
`coherentCosliceFiberComparison x (F.obj i)` の合成（包含後）に一致することを示す。
これは既存の canonical な左 Hom 比較そのものへの等式であり、各点で選んだ逆射を使わない。
対象 i を固定しても Hom のパラメータは全次数で自由である。

共通変数は `universe u v`、`{I : Type u} [SmallCategory I]`、
`{C : Type v} [Category.{u} C] [SimplicialCategory C]`。
新規公開宣言の正確な型・全前提は以下と監査スクリプトの `#check @` に記録。

```lean
lemma pullbackSectionsRelativeIso_hom_uncurry {K E B : SSet.{u}}
    (p : E ⟶ B) (a : K ⟶ B) :
    relativeFunctorUncurry (pullbackSectionsRelativeIso p a).hom =
      simplicialSectionsEvaluation (pullback.snd p a) ≫ pullback.fst p a
lemma weightedCoherentConeSectionsComparison_uncurry (F : I ⥤ C) (x : C) :
    relativeFunctorUncurry (weightedCoherentConeSectionsComparison F x) =
      simplicialSectionsEvaluation ((SSet.uliftFunctor.{v, u}).map
        (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))) ≫
      weightedCosliceComparison F x
lemma reflectedHomHolimConeComparison_uncurry (F : I ⥤ C) (x : C) :
    relativeFunctorUncurry (reflectedHomHolimConeComparison F x) =
      (uliftTensorIso (nerve I)
        (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor))).inv ≫
      (SSet.uliftFunctor.{v, u}).map
        (bousfieldKanWeightedNerveEvaluation (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      weightedCosliceComparison F x
lemma reflectedStrictConeSectionsComparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    relativeFunctorUncurry (reflectedStrictConeSectionsComparison c x) =
      (uliftTensorIso (nerve I) (SimplicialCategory.sHom x c.pt).op).inv ≫
      (SSet.uliftFunctor.{v, u}).map (weightedNerveSectionFromTransform
        (snd (bousfieldKanWeight I) ((Functor.const I).obj
          (reflectedSimplicialHomCone c x).pt) ≫ (reflectedSimplicialHomCone c x).π)) ≫
      weightedCosliceComparison F x
lemma weightedCoherentCoefficient_strictCone {F : I ⥤ C} (c : Cone F) (x : C)
    {n : ℕ} (σ : ComposableArrows I n)
    (a : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom x c.pt).op)
    (j : Fin (n + 1)) :
    weightedCoherentCoefficient (weightedNerveCoefficients
      (snd (bousfieldKanWeight I) ((Functor.const I).obj
        (reflectedSimplicialHomCone c x).pt) ≫ (reflectedSimplicialHomCone c x).π) σ a) j =
      pathFirstMinimumMap j ≫
        SSet.opFunctor.map (SSet.stdSimplex.map
          (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt))) ≫
        reflectedSimplexMap a ≫
        ((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app (σ.obj j))
lemma reflectedStrictConeSectionsComparison_evaluate {F : I ⥤ C}
    (c : Cone F) (x : C) (i : I) :
    lift (SSet.const (ULift.up (nerveVertex i)))
        (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op)) ≫
      relativeFunctorUncurry (reflectedStrictConeSectionsComparison c x) =
    (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map
        (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map (c.π.app i))) ≫
      coherentCosliceFiberComparison x (F.obj i) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex (F.obj i))
```

以上の整合性は極限性・局所 Kan 性を追加せず、定義済みの実際の比較射について証明した。
選択付きの `coneSectionHomComparison (strictCoherentCone c)` とこの合成との全体の比較は
まだ未完了であり、各脚の等式だけで錐の ∞ 圏での普遍性を結論しない。
元の q_x と係数の反転との整合性、𝒮・Sp の残りの適用、余極限の比較も継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4436 jobs）、公開866宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-strict-cone-evaluation-aggregate.log` と
`/tmp/gamma3-strict-cone-evaluation-audit.log`。


### native な比較に向けた反復 slice と join の再結合の準備

残る比較の一つは、錐 `c.val : Δ[0]⋆K → X` の図式上の coslice の切断から
元の K 上の切断への制限を、既存の `rightFibrationMappingEvaluation` と比較すること。
反復 slice の図式では `(Δ[n]⋆Δ[0])⋆K` と `Δ[n]⋆(Δ[0]⋆K)` が現れるため、
まず join の再結合を担当ディレクトリ内で構成する。Core の定義は変更しない。
原典上の位置は HTT §1.2.8、4.2.4.1 の双対、Kerodon §4.3.5、7.4.1.6。

`AssociativeJoinSimplex` は補った空単体を含め、join の単体を左右の頂点数と各単体、
頂点数の和の条件で表示する。三つの区間への展開と両方の逆関係を示し、
`joinAssociatorSimplexEquiv A B C n` を構成した。これは次数ごとの全単射であり、
単体集合の結合同型としてはまだ公開しない。

長さの和の等式は、各区間の単体を持つ依存和に対する部分型の条件に置く。
証明の移送を単体のデータから分けるため、逆関係は部分型の値の外延性と
全単射の往復則に対する型を明示した `congrArg` で証明する。
元の join の Fin による切断の定義は維持する。

`JoinAssociativityCuts` では切断の引き戻しの単調性、左区間に制限した切断の一致、
右区間で原点を移した切断が二つの引き戻した切断の差になる式を証明した。
`JoinSumNaturality` は長さの和表示へ単体作用を明示的に移し、二因子の
`augmentedJoinSumEquiv` と元の補った join の単体作用が全順序写像について可換であること、
移した作用の恒等則・合成則を証明する。頂点数零のケースも含む。

新規14宣言の正確な型は以下。共通の宇宙は `universe u`、`A B C : SSet.{u}`。
全暗黙引数と宇宙は監査スクリプトの `#check @` にも記録する。

```lean
abbrev joinSumSimplex (A B : SSet.{u}) (n : ℕ) : Type u
instance joinSumSimplex_zero_subsingleton (A B : SSet.{u}) :
    Subsingleton (joinSumSimplex A B 0)
def augmentedJoinSumEquiv (A B : SSet.{u}) (n : ℕ) :
    Join.augObj (join A B) n ≃ joinSumSimplex A B n
abbrev joinTripleSimplex (A B C : SSet.{u}) (n : ℕ) : Type u
def leftJoinSumTripleEquiv (A B C : SSet.{u}) (n : ℕ) :
    joinSumSimplex (join A B) C n ≃ joinTripleSimplex A B C n
def rightJoinSumTripleEquiv (A B C : SSet.{u}) (n : ℕ) :
    joinSumSimplex A (join B C) n ≃ joinTripleSimplex A B C n
def joinAssociatorSimplexEquiv (A B C : SSet.{u}) (n : ℕ) :
    (join (join A B) C) _⦋n⦌ ≃ (join A (join B C)) _⦋n⦌
lemma joinPullCut_mono {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    Join.pullCut α a ≤ Join.pullCut α b
lemma joinPullCut_leftMap {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    Join.pullCut (Join.leftMap α b) a = Join.pullCut α a
lemma joinPullCut_rightMap {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    Join.pullCut (Join.rightMap α a) (b - a) = Join.pullCut α b - Join.pullCut α a
def joinSumSimplexMap (A B : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) :
    joinSumSimplex A B n → joinSumSimplex A B m
lemma augmentedJoinSumEquiv_map (A B : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n)
    (s : Join.augObj (join A B) n) :
    augmentedJoinSumEquiv A B m (Join.augMap (join A B) α s) =
      joinSumSimplexMap A B α (augmentedJoinSumEquiv A B n s)
lemma joinSumSimplexMap_id (A B : SSet.{u}) (n : ℕ) (s : joinSumSimplex A B n) :
    joinSumSimplexMap A B (OrderHom.id : Fin n →o Fin n) s = s
lemma joinSumSimplexMap_comp (A B : SSet.{u}) {l m n : ℕ}
    (α : Fin m →o Fin n) (β : Fin l →o Fin m) (s : joinSumSimplex A B n) :
    joinSumSimplexMap A B (α.comp β) s =
      joinSumSimplexMap A B β (joinSumSimplexMap A B α s)
```

三因子の再結合 `joinAssociatorSimplexEquiv` の面・退化との可換性、単体集合の結合同型、
三因子の射についての自然性は下節で実装済み。その同型を使う反復 slice の比較、
native な錐の全体の比較、元の q_x と反転した係数の整合性、𝒮・Sp の残りの適用は
引き続き未完了。

検証：対象集約 `HomotopyLimits` のビルド成功（4439 jobs）、公開880宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-join-assoc-preparation-aggregate.log` と
`/tmp/gamma3-join-assoc-preparation-audit.log`。


### join の結合同型と三因子の射についての自然性

`JoinTripleCoordinates` は二つの切断の間の `joinMiddleMap α a b` を直接定義し、
左区間の左右の制限、右区間の左右の制限を、直接の三つの区間の制限と HEq で同定する。
空区間も含み、頂点数の等式による移送を省略しない。
`JoinTripleMaps` は三つの区間の共通表示への単体作用を構成し、左括弧・右括弧の両方から
移した作用が同じ実際の作用になることを証明する。

`JoinAssociator` はこれを用いて既存の各次数の `joinAssociatorSimplexEquiv` の
全ての面・退化への自然性を証明し、任意の `A B C : SSet.{u}` に対して

```lean
joinAssociator A B C : join (join A B) C ≅ join A (join B C)
```

を構成した。Kan 性・quasicategory 性・非空性の仮定はない。
順方向は構成済みの次数ごとの全単射であり、同値な別の射へ置き換えない。

`JoinAssociatorMaps` は両括弧付けの共通表示が各因子の射に自然であることを証明し、
任意の `f : A ⟶ A'`、`g : B ⟶ B'`、`h : C ⟶ C'` に対し

```lean
joinMap (joinMap f g) h ≫ (joinAssociator A' B' C').hom =
  (joinAssociator A B C).hom ≫ joinMap f (joinMap g h)
```

を得た。因子の射に単射性や同値性は不要。この可換式を反復 slice のパラメータ変更に使う。
原典上の位置は HTT §1.2.8、4.2.4.1 の双対、Kerodon §4.3.5、7.4.1.6。

新規27宣言の正確な型・全前提は以下と公開宣言の監査に記録する。
共通の宇宙は `universe u`。`joinSumSimplex` と `joinTripleSimplex` は前節の和表示を用いる。

```lean
def joinMiddleMap {m n : ℕ} (α : Fin m →o Fin n) (a b : ℕ) :
    Fin (Join.pullCut α (a + b) - Join.pullCut α a) →o Fin b
lemma joinAugMap_heq (X : SSet.{u}) {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (α : Fin m →o Fin n) (β : Fin m' →o Fin n')
    (hα : ∀ (i : Fin m) (j : Fin m'), i.val = j.val → (α i).val = (β j).val)
    (x : Join.augObj X n) (y : Join.augObj X n') (hxy : HEq x y) :
    HEq (Join.augMap X α x) (Join.augMap X β y)
lemma joinTripleSimplex_ext {A B C : SSet.{u}} {n : ℕ}
    (s t : joinTripleSimplex A B C n)
    (ha : s.val.1 = t.val.1) (hb : s.val.2.1 = t.val.2.1)
    (hc : s.val.2.2.1 = t.val.2.2.1)
    (hx : HEq s.val.2.2.2.1 t.val.2.2.2.1)
    (hy : HEq s.val.2.2.2.2.1 t.val.2.2.2.2.1)
    (hz : HEq s.val.2.2.2.2.2 t.val.2.2.2.2.2) : s = t
lemma joinAugMap_left_left (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : Join.augObj X a) :
    HEq (Join.augMap X (Join.leftMap (Join.leftMap α (a + b)) a) x)
      (Join.augMap X (Join.leftMap α a) x)
lemma joinAugMap_right_left (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : Join.augObj X b) :
    HEq (Join.augMap X (Join.rightMap (Join.leftMap α (a + b)) a)
      (cast (congrArg (Join.augObj X) (by omega : b = a + b - a)) x))
      (Join.augMap X (joinMiddleMap α a b) x)
lemma joinAugMap_left_right (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : Join.augObj X b) :
    HEq (Join.augMap X (Join.leftMap (Join.rightMap α a) b) x)
      (Join.augMap X (joinMiddleMap α a b) x)
lemma joinAugMap_right_right (X : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (a b : ℕ) (x : Join.augObj X (n - (a + b))) :
    HEq (Join.augMap X (Join.rightMap (Join.rightMap α a) b)
      (cast (congrArg (Join.augObj X) (by omega : n - (a + b) = n - a - b)) x))
      (Join.augMap X (Join.rightMap α (a + b)) x)
lemma joinSumSimplex_left_heq {A B : SSet.{u}} {n : ℕ}
    {s t : joinSumSimplex A B n} (h : s = t) : HEq s.val.2.2.1 t.val.2.2.1
lemma joinSumSimplex_right_heq {A B : SSet.{u}} {n : ℕ}
    {s t : joinSumSimplex A B n} (h : s = t) : HEq s.val.2.2.2 t.val.2.2.2
lemma augmentedJoinSumEquiv_cast_val (A B : SSet.{u}) {n n' : ℕ} (h : n = n')
    (s : Join.augObj (join A B) n) :
    (augmentedJoinSumEquiv A B n'
      (cast (congrArg (Join.augObj (join A B)) h) s)).val =
    (augmentedJoinSumEquiv A B n s).val
def joinTripleSimplexMap (A B C : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n) :
    joinTripleSimplex A B C n → joinTripleSimplex A B C m
lemma joinTripleSimplexMap_left (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (t : joinTripleSimplex A B C n) :
    leftJoinSumTripleEquiv A B C m
        (joinSumSimplexMap (join A B) C α ((leftJoinSumTripleEquiv A B C n).symm t)) =
      joinTripleSimplexMap A B C α t
lemma joinTripleSimplexMap_right (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (t : joinTripleSimplex A B C n) :
    rightJoinSumTripleEquiv A B C m
        (joinSumSimplexMap A (join B C) α ((rightJoinSumTripleEquiv A B C n).symm t)) =
      joinTripleSimplexMap A B C α t
def leftJoinTripleEncoding (A B C : SSet.{u}) (n : ℕ) :
    Join.augObj (join (join A B) C) n ≃ joinTripleSimplex A B C n
def rightJoinTripleEncoding (A B C : SSet.{u}) (n : ℕ) :
    Join.augObj (join A (join B C)) n ≃ joinTripleSimplex A B C n
lemma leftJoinTripleEncoding_map (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join (join A B) C) n) :
    leftJoinTripleEncoding A B C m (Join.augMap (join (join A B) C) α s) =
      joinTripleSimplexMap A B C α (leftJoinTripleEncoding A B C n s)
lemma rightJoinTripleEncoding_map (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join A (join B C)) n) :
    rightJoinTripleEncoding A B C m (Join.augMap (join A (join B C)) α s) =
      joinTripleSimplexMap A B C α (rightJoinTripleEncoding A B C n s)
lemma joinAssociatorSimplexEquiv_naturality (A B C : SSet.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (s : (join (join A B) C) _⦋n⦌) :
    joinAssociatorSimplexEquiv A B C m ((join (join A B) C).map α.op s) =
      (join A (join B C)).map α.op (joinAssociatorSimplexEquiv A B C n s)
def joinAssociator (A B C : SSet.{u}) : join (join A B) C ≅ join A (join B C)
def joinSumSimplexHom {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) :
    joinSumSimplex A B n → joinSumSimplex A' B' n
  | ⟨⟨a, b, x, y⟩, h⟩ => ⟨⟨a, b, Join.augHom f a x, Join.augHom g b y⟩, h⟩

/-- 概要：join の和表示への全単射は両因子の射の作用と可換。
方針：空の場合を分け、非空では joinMap の各次数の定義を読む。
規約：因子の射に追加の仮定は不要。
使われ方：HTT §1.2.8 の結合同型の自然性の準備。 -/
lemma augmentedJoinSumEquiv_hom {A A' B B' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) (s : Join.augObj (join A B) n) :
    augmentedJoinSumEquiv A' B' n (Join.augHom (joinMap f g) n s) =
      joinSumSimplexHom f g n (augmentedJoinSumEquiv A B n s)
def joinTripleSimplexHom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ) :
    joinTripleSimplex A B C n → joinTripleSimplex A' B' C' n
  | ⟨⟨a, b, c, x, y, z⟩, hn⟩ =>
    ⟨⟨a, b, c, Join.augHom f a x, Join.augHom g b y, Join.augHom h c z⟩, hn⟩

/-- 概要：左括弧の和表示の展開は各因子の射と可換。
方針：内側の二因子の自然性を、三つの区間への値の写像へ渡す。
規約：部分型の和の証明は外延性で分離する。
使われ方：HTT §1.2.8 の左括弧の自然性。 -/
lemma leftJoinSumTripleEquiv_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : joinSumSimplex (join A B) C n) :
    leftJoinSumTripleEquiv A' B' C' n (joinSumSimplexHom (joinMap f g) h n s) =
      joinTripleSimplexHom f g h n (leftJoinSumTripleEquiv A B C n s)
lemma rightJoinSumTripleEquiv_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : joinSumSimplex A (join B C) n) :
    rightJoinSumTripleEquiv A' B' C' n (joinSumSimplexHom f (joinMap g h) n s) =
      joinTripleSimplexHom f g h n (rightJoinSumTripleEquiv A B C n s)
lemma leftJoinTripleEncoding_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : Join.augObj (join (join A B) C) n) :
    leftJoinTripleEncoding A' B' C' n (Join.augHom (joinMap (joinMap f g) h) n s) =
      joinTripleSimplexHom f g h n (leftJoinTripleEncoding A B C n s)
lemma rightJoinTripleEncoding_hom {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') (n : ℕ)
    (s : Join.augObj (join A (join B C)) n) :
    rightJoinTripleEncoding A' B' C' n (Join.augHom (joinMap f (joinMap g h)) n s) =
      joinTripleSimplexHom f g h n (rightJoinTripleEncoding A B C n s)
lemma joinAssociator_naturality {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    joinMap (joinMap f g) h ≫ (joinAssociator A' B' C').hom =
      (joinAssociator A B C).hom ≫ joinMap f (joinMap g h)
```

join の単体集合としての結合同型と三因子の射に関する自然性は完成。
固定面の包含の式、反復 slice の同定、native な比較 span の評価と slice の制限の対応も
下節で実装済み。coslice の切断の制限への移送、元の q_x と係数の反転の整合性、
𝒮・Sp の残りの適用は未完了であり、γ3b・γ3c の完成とはしない。

検証：対象集約 `HomotopyLimits` のビルド成功（4443 jobs）、公開907宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-join-associator-aggregate.log` と
`/tmp/gamma3-join-associator-audit.log`。


### 反復 slice の同型と native な極限判定の slice の制限への移送

`JoinAssociatorInclusions` に前二因子・後二因子・外側二因子の固定面、最初・最後の因子の
包含と結合同型の可換式、および逆方向の自然性を証明した。
`IteratedSliceOverFamilies` は `p : K ⟶ X`、`q : L ⟶ sliceOver p` と任意の
パラメータ A について、二度の uncurry と join の再結合、二度の curry による両方向の族を
構成し、全パラメータでの厳密な往復則と前合成の自然性を証明する。
`IteratedSliceOverIso` により

```lean
iteratedSliceOverIso q : sliceOver q ≅ sliceOver (sliceOverUncurry q)
```

を得た。元の X への二重の射影を保つだけでなく、`IteratedSliceOverRestriction` により
元の図式 p への slice の制限を `sliceOverProjection q` に対応させる。
K・L・X・p・q に充填性は一切要求しない。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon §4.3.5、7.4.1.6。

`ConeIteratedSliceIso` は任意の coherent な錐 `c : JoinCone p` の Yoneda 表示に特殊化する。
固定図式の等式による移送を明示し、底 X の上の同型と実際の制限の対応を得る。
同じ底上の同型による頂点 fiber の同型も構成し、任意の x について

```lean
coneMappingTotalIso c x :
  rightFibrationMappingTotal (sliceOverProjection p) c x ≅
    vertexFiber (sliceOverProjection c.val) x
```

を得た。この同型の順方向の後に、錐の図式から元の図式への slice の制限の fiber 射を
合成すると、既存の `rightFibrationMappingEvaluation (sliceOverProjection p) c x` に
厳密に一致する。中間空間の同値の存在だけを述べるものではない。
この段階の同型・可換式には Kan 性や極限性を要求しない。

`ConeSliceRestrictionCriterion` は、この可換図式で A3d に基づく既存の native な判定を移す。
任意の `[Quasicategory X]`、任意の単体集合 K、任意の `p : K ⟶ X` と coherent な錐 c に対し

```lean
isLimitCone_iff_coneSliceRestrictionFiberMap_homotopyEquivalence (c : JoinCone p) :
  IsLimitCone c ↔ ∀ x : X _⦋0⦌,
    IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x)
```

を証明した。strict な錐、有限の添字、追加の fibration 性、選択した Hom の逆の自然性は
仮定しない。極限の条件を変えず、実際の slice の制限で検出する一般の判定である。

新規53宣言の正確な型・全前提は以下と公開宣言の監査に記録する。
共通の宇宙は `universe u`。各族の宣言の共通変数は
`{K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceOver p)`。

```lean
lemma augmentedJoinSumEquiv_inr (A B : SSet.{u}) (n : ℕ) (b : Join.augObj B n) :
    augmentedJoinSumEquiv A B n (Join.augHom (joinInr A B) n b) =
      (⟨⟨0, n, PUnit.unit, b⟩, by simp⟩ : joinSumSimplex A B n)
lemma augmentedJoinSumEquiv_inl (A B : SSet.{u}) (n : ℕ) (a : Join.augObj A n) :
    augmentedJoinSumEquiv A B n (Join.augHom (joinInl A B) n a) =
      (⟨⟨n, 0, a, PUnit.unit⟩, by simp⟩ : joinSumSimplex A B n)
lemma joinAssociator_hom_encoding (A B C : SSet.{u}) (n : ℕ)
    (s : (join (join A B) C) _⦋n⦌) :
    rightJoinTripleEncoding A B C (n + 1) ((joinAssociator A B C).hom.app _ s) =
      leftJoinTripleEncoding A B C (n + 1) s
lemma joinAssociator_rightPair (A B C : SSet.{u}) :
    joinMap (joinInr A B) (𝟙 C) ≫ (joinAssociator A B C).hom =
      joinInr A (join B C)
lemma joinAssociator_leftPair (A B C : SSet.{u}) :
    joinInl (join A B) C ≫ (joinAssociator A B C).hom =
      joinMap (𝟙 A) (joinInl B C)
lemma joinAssociator_inv_rightPair (A B C : SSet.{u}) :
    joinInr A (join B C) ≫ (joinAssociator A B C).inv = joinMap (joinInr A B) (𝟙 C)
lemma joinAssociator_inv_leftPair (A B C : SSet.{u}) :
    joinMap (𝟙 A) (joinInl B C) ≫ (joinAssociator A B C).inv = joinInl (join A B) C
lemma joinAssociator_last (A B C : SSet.{u}) :
    joinInr (join A B) C ≫ (joinAssociator A B C).hom =
      joinInr B C ≫ joinInr A (join B C)
lemma joinAssociator_inv_first (A B C : SSet.{u}) :
    joinInl A (join B C) ≫ (joinAssociator A B C).inv =
      joinInl A B ≫ joinInl (join A B) C
lemma joinAssociator_inv_naturality {A A' B B' C C' : SSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    joinMap f (joinMap g h) ≫ (joinAssociator A' B' C').inv =
      (joinAssociator A B C).inv ≫ joinMap (joinMap f g) h
lemma joinAssociator_outerPair (A B C : SSet.{u}) :
    joinMap (joinInl A B) (𝟙 C) ≫ (joinAssociator A B C).hom =
      joinMap (𝟙 A) (joinInr B C)
lemma joinAssociator_inv_outerPair (A B C : SSet.{u}) :
    joinMap (𝟙 A) (joinInr B C) ≫ (joinAssociator A B C).inv =
      joinMap (joinInl A B) (𝟙 C)
def iteratedSliceOverForwardFamily (s : A ⟶ sliceOver q) :
    A ⟶ sliceOver (sliceOverUncurry q)
lemma iteratedSliceOverForwardFamily_uncurry (s : A ⟶ sliceOver q) :
    sliceOverUncurry (iteratedSliceOverForwardFamily q s) =
      (joinAssociator A L K).inv ≫ sliceOverUncurry (sliceOverUncurry s)
def iteratedSliceOverInnerFamily (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    join A L ⟶ sliceOver p
lemma iteratedSliceOverInnerFamily_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (iteratedSliceOverInnerFamily q s) =
      (joinAssociator A L K).hom ≫ sliceOverUncurry s
lemma iteratedSliceOverInnerFamily_fixed (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    joinInr A L ≫ iteratedSliceOverInnerFamily q s = q
def iteratedSliceOverBackwardFamily (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    A ⟶ sliceOver q
lemma iteratedSliceOverBackwardFamily_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (iteratedSliceOverBackwardFamily q s) = iteratedSliceOverInnerFamily q s
lemma iteratedSliceOverFamily_backward_forward (s : A ⟶ sliceOver q) :
    iteratedSliceOverBackwardFamily q (iteratedSliceOverForwardFamily q s) = s
lemma iteratedSliceOverFamily_forward_backward (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    iteratedSliceOverForwardFamily q (iteratedSliceOverBackwardFamily q s) = s
lemma iteratedSliceOverForwardFamily_naturality (f : A' ⟶ A) (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q (f ≫ s) = f ≫ iteratedSliceOverForwardFamily q s
lemma iteratedSliceOverBackwardFamily_naturality (f : A' ⟶ A)
    (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    iteratedSliceOverBackwardFamily q (f ≫ s) = f ≫ iteratedSliceOverBackwardFamily q s
def iteratedSliceOverHomEquiv (A : SSet.{u}) :
    (A ⟶ sliceOver q) ≃ (A ⟶ sliceOver (sliceOverUncurry q))
def iteratedSliceOverMap : sliceOver q ⟶ sliceOver (sliceOverUncurry q)
lemma iteratedSliceOverForwardFamily_eq (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q s = s ≫ iteratedSliceOverMap q
def iteratedSliceOverInv : sliceOver (sliceOverUncurry q) ⟶ sliceOver q
lemma iteratedSliceOverBackwardFamily_eq (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    iteratedSliceOverBackwardFamily q s = s ≫ iteratedSliceOverInv q
def iteratedSliceOverIso : sliceOver q ≅ sliceOver (sliceOverUncurry q)
lemma iteratedSliceOverForwardFamily_projection (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q s ≫ sliceOverProjection (sliceOverUncurry q) =
      s ≫ sliceOverProjection q ≫ sliceOverProjection p
lemma iteratedSliceOverIso_projection :
    (iteratedSliceOverIso q).hom ≫ sliceOverProjection (sliceOverUncurry q) =
      sliceOverProjection q ≫ sliceOverProjection p
lemma sliceOverUncurry_eqToHom {K X A : SSet.{u}} {p r : K ⟶ X}
    (h : p = r) (s : A ⟶ sliceOver p) :
    sliceOverUncurry (s ≫ eqToHom (congrArg (fun f : K ⟶ X ↦ sliceOver f) h)) =
      sliceOverUncurry s
def uncurriedSliceOverRestriction : sliceOver (sliceOverUncurry q) ⟶ sliceOver p
lemma uncurriedSliceOverRestriction_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (s ≫ uncurriedSliceOverRestriction q) =
      joinMap (𝟙 A) (joinInr L K) ≫ sliceOverUncurry s
lemma iteratedSliceOverForwardFamily_restriction (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q s ≫ uncurriedSliceOverRestriction q =
      s ≫ sliceOverProjection q
lemma iteratedSliceOverIso_restriction :
    (iteratedSliceOverIso q).hom ≫ uncurriedSliceOverRestriction q = sliceOverProjection q
lemma uncurriedSliceOverRestriction_projection :
    uncurriedSliceOverRestriction q ≫ sliceOverProjection p =
      sliceOverProjection (sliceOverUncurry q)
def vertexFiberIsoOfOverIso {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) : vertexFiber p b ≅ vertexFiber q b
lemma vertexFiberIsoOfOverIso_hom_ι {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (e : E ≅ F) (he : e.hom ≫ q = p) (b : B _⦋0⦌) :
    (vertexFiberIsoOfOverIso p q e he b).hom ≫ vertexFiberι q b = vertexFiberι p b ≫ e.hom
lemma sliceOver_eqToHom_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    eqToHom (congrArg (fun f : K ⟶ X ↦ sliceOver f) h) ≫ sliceOverProjection q =
      sliceOverProjection p
abbrev coneYonedaPoint (c : JoinCone p) : (Δ[0] : SSet.{u}) ⟶ sliceOver p
def coneSliceOverDiagramIso (c : JoinCone p) :
    sliceOver (sliceOverUncurry (coneYonedaPoint c)) ≅ sliceOver c.val
lemma coneSliceOverDiagramIso_projection (c : JoinCone p) :
    (coneSliceOverDiagramIso c).hom ≫ sliceOverProjection c.val =
      sliceOverProjection (sliceOverUncurry (coneYonedaPoint c))
def coneIteratedSliceIso (c : JoinCone p) :
    sliceOver (coneYonedaPoint c) ≅ sliceOver c.val
lemma coneIteratedSliceIso_projection (c : JoinCone p) :
    (coneIteratedSliceIso c).hom ≫ sliceOverProjection c.val =
      sliceOverProjection (coneYonedaPoint c) ≫ sliceOverProjection p
def coneSliceOverRestriction (c : JoinCone p) : sliceOver c.val ⟶ sliceOver p
lemma coneIteratedSliceIso_restriction (c : JoinCone p) :
    (coneIteratedSliceIso c).hom ≫ coneSliceOverRestriction c =
      sliceOverProjection (coneYonedaPoint c)
lemma coneSliceOverRestriction_projection (c : JoinCone p) :
    coneSliceOverRestriction c ≫ sliceOverProjection p = sliceOverProjection c.val
def coneMappingTotalIso (c : JoinCone p) (x : X _⦋0⦌) :
    rightFibrationMappingTotal (sliceOverProjection p) c x ≅
      vertexFiber (sliceOverProjection c.val) x
lemma coneMappingTotalIso_evaluation (c : JoinCone p) (x : X _⦋0⦌) :
    (coneMappingTotalIso c x).hom ≫
        vertexFiberMap (sliceOverProjection c.val) (sliceOverProjection p)
          (coneSliceOverRestriction c) (coneSliceOverRestriction_projection c) x =
      rightFibrationMappingEvaluation (sliceOverProjection p) c x
def coneSliceRestrictionFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    vertexFiber (sliceOverProjection c.val) x ⟶ vertexFiber (sliceOverProjection p) x
lemma coneSliceRestrictionFiberMap_homotopyEquivalence_iff {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
        (rightFibrationMappingEvaluation (sliceOverProjection p) c x) ↔
      IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x)
lemma isLimitCone_iff_coneSliceRestrictionFiberMap_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x)
```

slice の制限の頂点 fiber の判定を coslice の切断空間の制限へ移す比較、
strict な豊穣錐についてその制限と構成済みの q′ の可換式、元の q_x と反転した係数の
整合性、𝒮・Sp の残りの適用は未完了。今回は native な任意の錐の判定の制限側への移送までであり、
γ3b・γ3c の完成とはしない。余極限の比較も後続に保持する。

検証：対象集約 `HomotopyLimits` のビルド成功（4449 jobs）、公開960宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
集約の他担当の依存700ソースはすべて追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-slice-restriction-aggregate.log` と
`/tmp/gamma3-cone-slice-restriction-audit.log`。


### 図式の制限と切断から両端固定の錐への標準比較の自然性

`ConeDiagramRestriction` に任意の `p : J ⟶ X`、`f : K ⟶ J`、頂点 x について
`endpointConeRestrict p x f` を構成した。これは両端固定の内部 Hom の錐を
`joinMap (𝟙 Δ[0]) f` で前合成する実際の射である。射の構成と固定条件には
quasicategory 性・Kan 性・f の単射性は不要。
`ConeDiagramTensor` は、この図式因子の変更と左右の join・直積の標準比較の可換式を与える。

`ConeRestrictionComparison` は coslice の切断から両端固定の錐への標準比較について
次の厳密な可換式を証明した。

```lean
relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
    sectionEndpointConeComparison (f ≫ p) x =
  sectionEndpointConeComparison p x ≫ endpointConeRestrict p x f
```

この式は任意の図式に成立する。X が quasicategory なら両方の標準比較は
単体的ホモトピー同値であり、二対三則により
`sectionRestriction_homotopyEquivalence_iff_endpoint` を得る。
選択した逆同値の自然性は仮定せず、全パラメータでの uncurry の式から証明した。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon 4.6.6.8、7.4.1.6。

新規13宣言の正確な型は以下。別記の `[Quasicategory X]` 以外の充填性の前提はない。

```lean
abbrev endpointConeEvaluation {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌)

lemma endpointConeEvaluation_restrict_fixed {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    endpointConeEvaluation p x ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X ≫
      (pre (joinEndpointInclusion Δ[0] K)).app X =
        SSet.const (functorVertex (joinEndpointDesc (SSet.yonedaEquiv.symm x) (f ≫ p)))

def endpointConeRestrict {K J X : SSet.{u}} (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    fixedEndpointConeSpace p x ⟶ fixedEndpointConeSpace (f ≫ p) x

lemma endpointConeRestrict_evaluation {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    endpointConeRestrict p x f ≫ endpointConeEvaluation (f ≫ p) x =
      endpointConeEvaluation p x ≫ (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X

lemma sectionConeUncurry_restrict {A K J X : SSet.{u}} {p : J ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ coherentConeSectionSpace p x) (f : K ⟶ J) :
    sectionConeUncurry (s ≫ relativeFunctorPre
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (f ▷ A) ≫ sectionConeUncurry s

lemma augTensorEquiv_symm_homLeft {B D : SSet.{u}} (f : B ⟶ D) (A : SSet.{u})
    (r : ℕ) (b : Join.augObj B r) (a : Join.augObj A r) :
    Join.augHom (f ▷ A) r ((Join.augTensorEquiv B A r).symm (b, a)) =
      (Join.augTensorEquiv D A r).symm (Join.augHom f r b, a)

lemma joinTensorRight_diagram {B D : SSet.{u}} (f : B ⟶ D) (C A : SSet.{u}) :
    (joinMap (𝟙 C) f ▷ A) ≫ joinTensorRight C D A =
      joinTensorRight C B A ≫ joinMap (𝟙 C) (f ▷ A)

lemma joinTensorLeft_diagram {B D : SSet.{u}} (f : B ⟶ D) (A C : SSet.{u}) :
    (A ◁ joinMap (𝟙 C) f) ≫ joinTensorLeft A C D =
      joinTensorLeft A C B ≫ joinMap (𝟙 (A ⊗ C)) f

noncomputable def sectionEndpointConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : coherentConeSectionSpace p x ⟶ fixedEndpointConeSpace p x

lemma sectionEndpointConeComparison_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ coherentConeSectionSpace p x) :
    uncurry (s ≫ sectionEndpointConeComparison p x ≫ endpointConeEvaluation p x) =
      joinTensorRight Δ[0] K A ≫ sectionConeUncurry s

lemma sectionEndpointConeComparison_restrict {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
        sectionEndpointConeComparison (f ≫ p) x =
      sectionEndpointConeComparison p x ≫ endpointConeRestrict p x f

lemma sectionEndpointConeComparison_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (sectionEndpointConeComparison p x)

lemma sectionRestriction_homotopyEquivalence_iff_endpoint {K J X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f) ↔
      IsSimplicialHomotopyEquivalence (endpointConeRestrict p x f)
```

slice の頂点 fiber の制限と両端固定の錐の制限の可換式は、次の証明対象として残る。
従って native な極限判定の切断の制限への移送はまだ完了していない。
豊穣 q′ の制限との可換式、元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、
余極限の比較も未完了。γ3b・γ3c は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4452 jobs）、公開973宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-diagram-restriction-aggregate.log` と
`/tmp/gamma3-cone-diagram-restriction-audit.log`。


### native な極限判定の coslice の切断の制限への移送

`SliceEndpointConeComparison` は、slice の頂点 fiber から両端固定の錐への実際の
標準比較 `sliceEndpointConeComparison p x` を追跡し、任意の図式の射 f について
次の厳密な可換式を証明した。

```lean
sliceRestrictionFiberMap p x f ≫ sliceEndpointConeComparison (f ≫ p) x =
  sliceEndpointConeComparison p x ≫ endpointConeRestrict p x f
```

全パラメータでの uncurry の値、slice の制限と可変頂点の射影の可換性も証明した。
X が quasicategory なら、この比較は単体的ホモトピー同値である。前回の切断側の
可換式と合わせ、`sliceRestriction_homotopyEquivalence_iff_sections` は
slice の頂点 fiber の制限と coslice の切断の制限のホモトピー同値性を同値にする。

`ConeSectionRestrictionCriterion` は任意の coherent な錐 c に特殊化する。
`coneSliceOverRestriction_eq` は従来の native な制限を通常の図式の制限へ厳密に同定し、
錐の固定条件による終域の移送を含めて `coneSectionRestriction c x` を定義した。
主定理 `isLimitCone_iff_coneSectionRestriction_homotopyEquivalence` は

```lean
IsLimitCone c ↔ ∀ x : X _⦋0⦌,
  IsSimplicialHomotopyEquivalence (coneSectionRestriction c x)
```

を与える。前提は `[Quasicategory X]` のみ。K は任意の単体集合、c は任意の錐であり、
strict な錐、通常の圏の nerve、有限の添字、fibration の図式に制限しない。
追加の比較同値の仮定もない。A3d の native な極限判定から、実際の標準比較と
その可換四角形の二対三則により導いた。選択した逆同値の自然性は使わない。
`coneSectionRestriction_uncurry` は、この実際の制限の全パラメータの値も与える。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6。

新規16宣言の正確な型と全前提は以下。

```lean
noncomputable def sliceEndpointConeComparison {K X : SSet.{u}} (p : K ⟶ X)
    (x : X _⦋0⦌) : vertexFiber (sliceOverProjection p) x ⟶ fixedEndpointConeSpace p x

lemma sliceConeFamilyUncurry_parameter {A K X : SSet.{u}} {p : K ⟶ X}
    (s : A ⟶ sliceOver p) :
    (join (Δ[0] : SSet.{u}) K ◁ s) ≫ sliceConeFamilyUncurry p =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫ joinTensorLeft A Δ[0] K ≫
        joinMap (fst A Δ[0]) (𝟙 K) ≫ sliceOverUncurry s

lemma sliceEndpointConeComparison_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ vertexFiber (sliceOverProjection p) x) :
    uncurry (s ≫ sliceEndpointConeComparison p x ≫ endpointConeEvaluation p x) =
      (β_ (join (Δ[0] : SSet.{u}) K) A).hom ≫ joinTensorLeft A Δ[0] K ≫
        joinMap (fst A Δ[0]) (𝟙 K) ≫
          sliceOverUncurry (s ≫ vertexFiberι (sliceOverProjection p) x)

lemma sliceOverRestrict_projection {K J X : SSet.{u}} (p : J ⟶ X) (f : K ⟶ J) :
    sliceOverRestrict p f ≫ sliceOverProjection (f ≫ p) = sliceOverProjection p

def sliceRestrictionFiberMap {K J X : SSet.{u}} (p : J ⟶ X) (x : X _⦋0⦌)
    (f : K ⟶ J) :
    vertexFiber (sliceOverProjection p) x ⟶ vertexFiber (sliceOverProjection (f ≫ p)) x

lemma sliceEndpointConeComparison_restrict {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    sliceRestrictionFiberMap p x f ≫ sliceEndpointConeComparison (f ≫ p) x =
      sliceEndpointConeComparison p x ≫ endpointConeRestrict p x f

lemma sliceEndpointConeComparison_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (sliceEndpointConeComparison p x)

lemma sliceRestriction_homotopyEquivalence_iff_sections {K J X : SSet.{u}}
    [Quasicategory X] (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    IsSimplicialHomotopyEquivalence (sliceRestrictionFiberMap p x f) ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f)

lemma coneSliceOverRestriction_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (s : A ⟶ sliceOver c.val) :
    sliceOverUncurry (s ≫ coneSliceOverRestriction c) =
      joinMap (𝟙 A) (joinInr (Δ[0] : SSet.{u}) K) ≫ sliceOverUncurry s

lemma coneSliceOverRestriction_eq {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    coneSliceOverRestriction c =
      sliceOverRestrict c.val (joinInr (Δ[0] : SSet.{u}) K) ≫
        eqToHom (congrArg (fun f : K ⟶ X ↦ sliceOver f) c.property)

def coneSectionRestriction {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p)
    (x : X _⦋0⦌) : coherentConeSectionSpace c.val x ⟶ coherentConeSectionSpace p x

lemma sectionConeUncurry_eqToHom {A K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (x : X _⦋0⦌) (s : A ⟶ coherentConeSectionSpace p x) :
    sectionConeUncurry (s ≫
      eqToHom (congrArg (fun f : K ⟶ X ↦ coherentConeSectionSpace f x) h)) =
      sectionConeUncurry s

lemma coneSectionRestriction_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (s : A ⟶ coherentConeSectionSpace c.val x) :
    sectionConeUncurry (s ≫ coneSectionRestriction c x) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (joinInr (Δ[0] : SSet.{u}) K ▷ A) ≫
        sectionConeUncurry s

lemma normalizedSliceRestriction_iff_sections {K J X : SSet.{u}} [Quasicategory X]
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q)
    (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (vertexFiberMap (sliceOverProjection p) (sliceOverProjection q)
        (sliceOverRestrict p f ≫ eqToHom (congrArg (fun r : K ⟶ X ↦ sliceOver r) h))
        (by rw [Category.assoc, sliceOver_eqToHom_projection h, sliceOverRestrict_projection])
        x) ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
          eqToHom (congrArg (fun r : K ⟶ X ↦ coherentConeSectionSpace r x) h))

lemma coneSliceRestriction_homotopyEquivalence_iff_sections {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSliceRestrictionFiberMap c x) ↔
      IsSimplicialHomotopyEquivalence (coneSectionRestriction c x)

lemma isLimitCone_iff_coneSectionRestriction_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneSectionRestriction c x)
```

これで native な極限判定の切断の制限への移送は証明済み。
strict な豊穣錐について、この制限と構成済みの q′ の可換式、
元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、余極限の比較は未完了。
従って γ3b・γ3c の完成とはしない。

検証：対象集約 `HomotopyLimits` のビルド成功（4454 jobs）、公開989宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-cone-section-restriction-aggregate.log` と
`/tmp/gamma3-cone-section-restriction-audit.log`。


### 錐の頂点評価と、反転した豊穣 Hom を始域とする native な比較

`ConeApexEvaluation` は任意の単体集合 K について、左頂点の包含
`joinInl Δ[0] K` が left anodyne であることを証明した。
任意の quasicategory X の任意の coherent な錐 c と頂点 x について、錐の図式 c.val 上の
coslice の切断を c.vertex で評価する実際の射 `coneApexSectionEvaluation c x` は
trivial Kan fibration、従って単体的ホモトピー同値である。
包含後の値も内部 Hom の頂点評価に厳密に一致する。

`StrictConeNativeComparison` は strict な錐 c に特殊化し、終域を c.pt の標準頂点へ
正規化した `strictConeApexEvaluation c x` の厳密な切断 `strictConeApexSection c x` を選ぶ。
反転した豊穣 Hom からの既存の `coherentCosliceFiberComparison x c.pt` をこの切断と合成して
`reflectedStrictConeFamilyComparison c x` を構成した。
頂点評価との合成は元の coslice fiber 比較に厳密に一致し、局所 Kan 性の下で
この族の比較は単体的ホモトピー同値となる。元の図式への `coneSectionRestriction` を合成した
`reflectedNativeConeComparison c x` に対し、主定理は次の通り。

```lean
IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
  IsSimplicialHomotopyEquivalence (reflectedNativeConeComparison c x)
```

I は任意の小圏、C は単体的圏で、追加の前提は
`[∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]` のみ。
通常の錐 c の極限性、Hom 錐の極限性、図式の fibration 性や比較同値の仮定は置かない。
この比較の始域は `ULift (sHom(x,c.pt).op)`、終域は元の strict な図式上の
coslice の切断空間である。選んだ切断を含む実際の native な射であり、構成済みの
`reflectedStrictConeSectionsComparison`（q′ と weighted 比較の合成）とはまだ同定していない。
切断の選択に関する図式の自然性も主張しない。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6。

新規16宣言の正確な型と全前提は以下。

```lean
lemma joinApexInclusion_leftAnodyne (K : SSet.{u}) :
    leftAnodyneExtensions (joinInl (Δ[0] : SSet.{u}) K)

def joinApexVertex (K : SSet.{u}) : (join (Δ[0] : SSet.{u}) K) _⦋0⦌

lemma coneDiagram_apex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    c.val.app (Opposite.op ⦋0⦌) (joinApexVertex K) = c.vertex

def coneApexSectionEvaluation {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) : coherentConeSectionSpace c.val x ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex

lemma coneApexSectionEvaluation_ι {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    coneApexSectionEvaluation c x ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex =
      vertexFiberι ((ihom (join (Δ[0] : SSet.{u}) K)).map
        (sliceUnderProjection (SSet.yonedaEquiv.symm x))) (functorVertex c.val) ≫
          evaluateFunctorAt (joinApexVertex K)

lemma coneApexSectionEvaluation_trivialKanFibration {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    TrivialKanFibration (coneApexSectionEvaluation c x)

lemma coneApexSectionEvaluation_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneApexSectionEvaluation c x)

noncomputable def strictConeApexEvaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x) ⟶
      vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex c.pt)

lemma strictConeApexEvaluation_trivialKanFibration {F : I ⥤ C} (c : Cone F) (x : C) :
    TrivialKanFibration (strictConeApexEvaluation c x)

noncomputable def strictConeApexSection {F : I ⥤ C} (c : Cone F) (x : C) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex c.pt) ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x)

lemma strictConeApexSection_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    strictConeApexSection c x ≫ strictConeApexEvaluation c x = 𝟙 _

noncomputable def reflectedStrictConeFamilyComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x)

lemma reflectedStrictConeFamilyComparison_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    reflectedStrictConeFamilyComparison c x ≫ strictConeApexEvaluation c x =
      coherentCosliceFiberComparison x c.pt

lemma reflectedStrictConeFamilyComparison_homotopyEquivalence {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeFamilyComparison c x)

noncomputable def reflectedNativeConeComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)

lemma strictCoherentCone_isLimit_iff_reflectedNativeConeComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (reflectedNativeConeComparison c x)
```

次は q′ の切断比較とこの native な制限の比較を接続する。
方針は、strict な錐を通常の添字圏に始対象を加えた図式で表し、その図式の Hom 錐から
weighted な切断比較を作り、元の図式への制限と頂点での評価を同時に追跡すること。
今回の定理だけでは Hom の strict 極限から ∞ 極限はまだ得られない。
q′ との整合性、元の q_x と反転係数の整合性、𝒮・Sp の残りの適用、余極限の比較は未完了。
従って γ3b・γ3c の完成とはしない。

検証：対象集約 `HomotopyLimits` のビルド成功（4456 jobs）、公開1005宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-native-enriched-apex-aggregate.log` と
`/tmp/gamma3-native-enriched-apex-audit.log`。


### q′ と native な制限の主可換式、三形状の homotopy 極限の移送

`SmallStrictConeParameter` は、通常の小圏 I に始対象を加えた `WithInitial I` 上の
`smallStrictConeFunctor c` と、錐の形 `Δ[0] ⋆ ULift N(I)` から `ULift N(WithInitial I)`
への標準射 `smallStrictConeParameter I` を構成した。この標準射による図式の引き戻しは、
既存の `strictCoherentCone c` の図式そのもの。右因子上では元の添字の包含、左頂点では
新しい始対象に厳密に一致する。既存の錐の定義は変更していない。

`WeightedStrictConeFamily` は、始対象付き図式の始対象からの標準錐
`smallStrictConeExtension c` に既存の q′ の切断比較を適用し、標準射で引き戻して
錐全体上の族 `weightedStrictConeFamilyComparison c x` を構成した。
頂点評価との合成は `coherentCosliceFiberComparison x c.pt` に厳密に一致する。
局所 Kan 性の下でこの族の比較は単体的ホモトピー同値となる。
始対象付き図式全体の Bousfield–Kan 比較の同値性は仮定しない。
頂点評価の切断を選ぶ前回の族とは異なり、この族は q′ の実際の構成から得ている。

`WeightedConeRestriction` は全パラメータの展開式から、主可換式

```lean
weightedStrictConeFamilyComparison c x ≫
    coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x) =
  reflectedStrictConeSectionsComparison c x
```

を証明した。この射の等式には局所 Kan 性や極限性は不要。
局所 Kan 性の下で `strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison` は

```lean
IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
  IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)
```

を与える。通常の小圏 I と錐 c は任意で、比較同値の追加仮定は置かない。
これにより、q′ と native な制限の接続は証明済みとなった。

`StrictHomotopyLimits` の三つの公開定理は、局所 Kan な単体的圏 C において、
全 x で `IsLimit (simplicialHomCone c x)` ならば次の `IsLimitCone (strictCoherentCone c)` を与える。

- `strictCoherentCone_isLimit_of_discrete_homLimit`：任意の離散図式。添字の有限性は不要。
- `strictCoherentCone_isLimit_of_cospan_homLimit`：一脚が Hom 上で fibration の cospan。
  全 x で左脚の fibration 性を要求し、右脚の fibration 性は要求しない。
- `strictCoherentCone_isLimit_of_tower_homLimit`：Hom 上の全隣接遷移が fibration の塔。

これらは任意の追加の比較同値を仮定する界面ではなく、構成済みの q′ の比較と
主可換式による ∞ 極限錐の定理である。ただし 𝒮・Sp の実際の錐と Hom 条件の検証は別途必要。
原典上の位置は HTT 4.2.4.1 の双対の限定形、Kerodon 7.5.3.12、7.5.4.6。

新規27宣言の型は以下。共通の C は `[Category.{u} C] [SimplicialCategory C]` を持つ。
`weightedStrictConeFamilyComparison_homotopyEquivalence`、上の極限判定、および三つの
移送定理には `[∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]` を付ける。
他の宣言には局所 Kan 性は不要。その他の前提は各型に明記した。

```lean
def smallStrictConeFunctor {F : I ⥤ C} (c : Cone F) : WithInitial I ⥤ C

lemma smallStrictConeFunctor_restriction {F : I ⥤ C} (c : Cone F) :
    WithInitial.incl ⋙ smallStrictConeFunctor c = F

def coneIndexResize (I : Type u) [SmallCategory I] :
    WithInitial (AsSmall.{v} I) ⥤ AsSmall.{v} (WithInitial I)

lemma coneIndexResize_functor {F : I ⥤ C} (c : Cone F) :
    coneIndexResize I ⋙ AsSmall.down ⋙ smallStrictConeFunctor c = strictConeFunctor c

noncomputable def smallStrictConeParameter (I : Type u) [SmallCategory I] :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      (SSet.uliftFunctor.{v, u}).obj (nerve (WithInitial I))

lemma smallStrictConeParameter_inr (I : Type u) [SmallCategory I] :
    joinInr (Δ[0] : SSet.{max u v}) _ ≫ smallStrictConeParameter.{u, v} I =
      (SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C

lemma smallStrictConeParameter_inl (I : Type u) [SmallCategory I] :
    joinInl (Δ[0] : SSet.{max u v}) _ ≫ smallStrictConeParameter.{u, v} I =
      SSet.yonedaEquiv.symm (ULift.up (nerveVertex (WithInitial.star : WithInitial I)))

lemma smallStrictConeParameter_diagram {F : I ⥤ C} (c : Cone F) :
    smallStrictConeParameter I ≫ strictCoherentDiagram (smallStrictConeFunctor c) =
      (strictCoherentCone c).val

def smallStrictConeExtension {F : I ⥤ C} (c : Cone F) : Cone (smallStrictConeFunctor c) where
  pt

lemma smallStrictConeExtension_app_of {F : I ⥤ C} (c : Cone F) (i : I) :
    (smallStrictConeExtension c).π.app (WithInitial.of i) = c.π.app i

lemma smallStrictConeExtension_app_star {F : I ⥤ C} (c : Cone F) :
    (smallStrictConeExtension c).π.app WithInitial.star = 𝟙 c.pt

lemma smallStrictConeExtension_whisker {F : I ⥤ C} (c : Cone F) :
    (smallStrictConeExtension c).whisker WithInitial.incl = c

lemma smallStrictConeParameter_apex (I : Type u) [SmallCategory I] :
    (smallStrictConeParameter.{u, v} I).app (Opposite.op ⦋0⦌)
        (joinApexVertex ((SSet.uliftFunctor.{v, u}).obj (nerve I))) =
      ULift.up (nerveVertex (WithInitial.star : WithInitial I))

lemma relativeFunctorUncurry_eqToHom {A K E B : SSet.{u}} (q : E ⟶ B)
    {p r : K ⟶ B} (h : p = r) (s : A ⟶ relativeFunctorSpace q p) :
    relativeFunctorUncurry (s ≫
      eqToHom (congrArg (fun f : K ⟶ B ↦ relativeFunctorSpace q f) h)) =
      relativeFunctorUncurry s

noncomputable def weightedStrictConeFamilyComparison {F : I ⥤ C} (c : Cone F) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op ⟶
      coherentConeSectionSpace (strictCoherentCone c).val (coherentNerveVertex x)

lemma weightedStrictConeFamilyComparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    relativeFunctorUncurry (weightedStrictConeFamilyComparison c x) =
      (smallStrictConeParameter I ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x c.pt).op) ≫
          relativeFunctorUncurry
            (reflectedStrictConeSectionsComparison (smallStrictConeExtension c) x)

lemma strictConeApexEvaluation_ι {F : I ⥤ C} (c : Cone F) (x : C) :
    strictConeApexEvaluation c x ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex c.pt) =
      vertexFiberι ((ihom (join (Δ[0] : SSet.{max u v})
        ((SSet.uliftFunctor.{v, u}).obj (nerve I)))).map
          (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x))))
        (functorVertex (strictCoherentCone c).val) ≫
          evaluateFunctorAt (joinApexVertex ((SSet.uliftFunctor.{v, u}).obj (nerve I)))

lemma relativeFunctorUncurry_at_vertex {A K E B : SSet.{u}} (q : E ⟶ B)
    (p : K ⟶ B) (s : A ⟶ relativeFunctorSpace q p) (v : K _⦋0⦌) :
    s ≫ vertexFiberι ((ihom K).map q) (functorVertex p) ≫ evaluateFunctorAt v =
      lift (SSet.const v) (𝟙 A) ≫ relativeFunctorUncurry s

lemma weightedStrictConeFamilyComparison_evaluation {F : I ⥤ C} (c : Cone F) (x : C) :
    weightedStrictConeFamilyComparison c x ≫ strictConeApexEvaluation c x =
      coherentCosliceFiberComparison x c.pt

lemma weightedStrictConeFamilyComparison_homotopyEquivalence {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedStrictConeFamilyComparison c x)

lemma smallStrictConeDiagram_restriction {F : I ⥤ C} (c : Cone F) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C

lemma smallStrictConeExtension_comparison_uncurry {F : I ⥤ C} (c : Cone F) (x : C) :
    ((SSet.uliftFunctor.{v, u}).map (nerveMap (WithInitial.incl (C

lemma weightedStrictConeFamilyComparison_restriction {F : I ⥤ C} (c : Cone F) (x : C) :
    weightedStrictConeFamilyComparison c x ≫
        coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x) =
      reflectedStrictConeSectionsComparison c x

lemma strictCoherentCone_isLimit_iff_reflectedStrictConeSectionsComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x)

lemma strictCoherentCone_isLimit_of_discrete_homLimit {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (hc : ∀ x : C, IsLimit (simplicialHomCone c x)) :
    IsLimitCone (strictCoherentCone c)

lemma strictCoherentCone_isLimit_of_cospan_homLimit
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    (hc : ∀ x : C, IsLimit (simplicialHomCone c x))
    [∀ x : C, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsLimitCone (strictCoherentCone c)

lemma strictCoherentCone_isLimit_of_tower_homLimit
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    (hc : ∀ x : C, IsLimit (simplicialHomCone c x))
    [∀ (x : C) (n : ℕ), Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsLimitCone (strictCoherentCone c)
```

未完了範囲：元の非反転の end・q_x と反転係数の直接比較、𝒮・Sp での実際の積・
引き戻し・塔の錐とその Hom 条件の検証、余極限の比較を残す。
𝒮 の空積以外の具体的な適用は、この一般定理だけでは完了と数えない。
γ3 全体は継続中であり、E2b の具体的な適用は E2a 完了後に扱う。

検証：対象集約 `HomotopyLimits` のビルド成功（4460 jobs）、公開1032宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存700ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-strict-homotopy-limits-aggregate.log` と
`/tmp/gamma3-strict-homotopy-limits-audit.log`。


### γ3c：𝒮 の実際の積・一脚 fibration の引き戻し・塔の極限

`KanConeLimits` は F1 の既存の `KanObject` と `kanObjectForget` を使い、
豊穣 Hom 関手が忘却後の内部 Hom 関手に厳密に一致することを証明した。
右随伴である内部 Hom の極限保存により、台で極限となる Kan 複体の錐は全ての豊穣 Hom でも
極限となる。通常の Kan 複体の圏の極限性も台の普遍性から戻せる。
任意の台の錐の頂点が Kan なら、その頂点と射影を Kan 複体の錐へ束縛する構成も公開した。
fibration の内部 Hom による保存を検証し、`strictCoherentDiagram F` と F1 の既存の
`kanDiagramCoherentNerve F` の厳密な一致も証明した。

`SpaceProducts` は任意の小さい離散図式 `F : Discrete J ⥤ KanObject` について、
台の `limit (F ⋙ kanObjectForget)` を `kanProductObject F` に束縛し、実際の射影から
`kanProductCone F` を構成した。忘却後と Kan 複体の通常の圏での極限性を証明。
F1 の図式上の `spaceProductCone F` は追加の仮定なしで `IsLimitCone` を満たす。
頂点は `spaceInfinityVertex (kanProductObject F)` に厳密に一致する。
J に有限性や非空性は不要なので、γ3c の有限積も含む。

`SpacePullbacks` は Kan 複体の射 `p : E ⟶ B`、`q : D ⟶ B` について、
台の p が Kan fibration なら、実際の単体集合の `pullback p q` を頂点とする
`kanPullbackCone p q` を束縛した。右脚 q の fibration 性は要求しない。
通常の引き戻しの普遍性を AsSmall の添字へ移し、忘却後と Kan 複体の圏の極限性を証明。
Hom の左脚の fibration 性は内部 Hom による保存で検証し、
`spacePullbackCone_isLimitCone` は既存の空間値図式上の実際の ∞ 引き戻し錐を与える。

`SpaceTowers` は `F : AsSmall ℕᵒᵖ ⥤ KanObject` の台の全隣接遷移が Kan fibration なら、
元の可算塔の `limit (AsSmall.up ⋙ F ⋙ kanObjectForget)` を頂点とする `kanTowerCone F`
を構成した。頂点の Kan 性、忘却後と Kan 複体の圏の極限性を証明。
全 Hom の極限性と全隣接遷移の fibration 性を検証して、
`spaceTowerCone_isLimitCone` は既存の空間値図式上の実際の ∞ 極限錐を与える。

三つの結論はいずれも `IsLimitCone` であり、未証明の Hom 条件や比較同値を前提とする界面ではない。
原典上の位置は HTT 4.2.4.1 の双対、Kerodon 7.5.3.12、7.5.4.6。
γ3c の 𝒮 の指定された三形状の極限はこれで公開済みとなった。

新規31宣言の型は以下。共通の宇宙は u。
`SpaceProducts` の J は任意の `Type u`。
`SpacePullbacks` の E、B、D は `KanObject.{u}`、p と q は上記の射であり、
`kanPullbackCone` 以降の宣言には `[Fibration (show E.obj ⟶ B.obj from p)]` を付ける。
`SpaceTowers` の F は上記の塔。`kanTowerUnderlyingCone` 以外には全 n について
`[Fibration (show (F.obj (AsSmall.up.obj (Opposite.op (n+1)))).obj ⟶
(F.obj (AsSmall.up.obj (Opposite.op n))).obj from
F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]` を付ける。
これ以外の前提は各型に明記した。

```lean
lemma kanObjectHomFunctor_eq (X : KanObject.{u}) :
    (SimplicialCategory.sHomFunctor KanObject.{u}).obj (Opposite.op X) =
      kanObjectForget ⋙ ihom X.obj

noncomputable def kanObjectCone_isLimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ KanObject.{u}} (c : Cone F) (hc : IsLimit (kanObjectForget.mapCone c)) :
    IsLimit c where
  lift s

noncomputable def kanObjectHomCone_isLimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ KanObject.{u}} (c : Cone F) (hc : IsLimit (kanObjectForget.mapCone c))
    (X : KanObject.{u}) : IsLimit (simplicialHomCone c X)

def kanObjectConeOfUnderlying {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u})
    (c : Cone (F ⋙ kanObjectForget)) (h : KanComplex c.pt) : Cone F where
  pt

lemma kanObjectConeOfUnderlying_forget {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) (c : Cone (F ⋙ kanObjectForget)) (h : KanComplex c.pt) :
    kanObjectForget.mapCone (kanObjectConeOfUnderlying F c h) = c

noncomputable def kanObjectConeOfUnderlying_forget_isLimit {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) (c : Cone (F ⋙ kanObjectForget)) (h : KanComplex c.pt)
    (hc : IsLimit c) : IsLimit (kanObjectForget.mapCone (kanObjectConeOfUnderlying F c h))

lemma kanObjectHom_map_fibration (X : KanObject.{u}) {Y Z : KanObject.{u}} (f : Y ⟶ Z)
    [Fibration (show Y.obj ⟶ Z.obj from f)] :
    Fibration (((SimplicialCategory.sHomFunctor KanObject.{u}).obj (Opposite.op X)).map f)

lemma strictCoherentDiagram_eq_kanDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) : strictCoherentDiagram F = kanDiagramCoherentNerve F

noncomputable def kanProductObject (F : Discrete J ⥤ KanObject.{u}) : KanObject.{u}

noncomputable def kanProductCone (F : Discrete J ⥤ KanObject.{u}) : Cone F where
  pt

noncomputable def kanProductCone_forget_isLimit (F : Discrete J ⥤ KanObject.{u}) :
    IsLimit (kanObjectForget.mapCone (kanProductCone F))

noncomputable def kanProductCone_isLimit (F : Discrete J ⥤ KanObject.{u}) :
    IsLimit (kanProductCone F)

noncomputable def spaceProductCone (F : Discrete J ⥤ KanObject.{u}) :
    JoinCone (kanDiagramCoherentNerve F)

lemma spaceProductCone_vertex (F : Discrete J ⥤ KanObject.{u}) :
    (spaceProductCone F).vertex = spaceInfinityVertex (kanProductObject F)

lemma spaceProductCone_isLimitCone (F : Discrete J ⥤ KanObject.{u}) :
    IsLimitCone (spaceProductCone F)

def kanPullbackDiagram : AsSmall.{u} WalkingCospan ⥤ KanObject.{u}

noncomputable def kanPullbackUnderlyingCone : Cone (kanPullbackDiagram p q ⋙ kanObjectForget)

noncomputable def kanPullbackCone : Cone (kanPullbackDiagram p q)

lemma kanPullbackCone_obj : (kanPullbackCone p q).pt.obj =
    pullback (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q)

noncomputable def kanPullbackCone_forget_isLimit :
    IsLimit (kanObjectForget.mapCone (kanPullbackCone p q))

noncomputable def kanPullbackCone_isLimit : IsLimit (kanPullbackCone p q)

noncomputable def spacePullbackCone : JoinCone (kanDiagramCoherentNerve (kanPullbackDiagram p q))

lemma spacePullbackCone_isLimitCone : IsLimitCone (spacePullbackCone p q)

noncomputable def kanTowerUnderlyingCone : Cone (F ⋙ kanObjectForget)

lemma kanTowerUnderlyingCone_kanComplex : KanComplex (kanTowerUnderlyingCone F).pt

noncomputable def kanTowerCone : Cone F

lemma kanTowerCone_obj : (kanTowerCone F).pt.obj =
    limit (AsSmall.up ⋙ F ⋙ kanObjectForget)

noncomputable def kanTowerCone_forget_isLimit :
    IsLimit (kanObjectForget.mapCone (kanTowerCone F))

noncomputable def kanTowerCone_isLimit : IsLimit (kanTowerCone F)

noncomputable def spaceTowerCone : JoinCone (kanDiagramCoherentNerve F)

lemma spaceTowerCone_isLimitCone : IsLimitCone (spaceTowerCone F)
```

Sp の Ω スペクトルの実際の三形状の極限、元の非反転の end・q_x と反転係数の直接比較、
余極限の比較は未完了。𝒮 の今回の極限の適用だけで γ3 全体を完了とは数えない。
E2b の具体的な適用は E2a 完了後に扱う。

検証：対象集約 `HomotopyLimits` のビルド成功（4467 jobs）、公開1063宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存703ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-space-limits-aggregate.log` と `/tmp/gamma3-space-limits-audit.log`。


### γ3c：Sp の段評価と、段ごとの極限から豊穣 Hom の極限への移送

L9 の正本の模型を確認した。`KST.Spectra.OmegaSpectrum` は各段の点つき Kan 複体に加え、
懸垂の構造射の単射性と、随伴構造射の全基点の π_* 同型を条件に持つ。
`KST.Spectra.Sp` は L9 の既存の単体的圏の coherent nerve。
𝒮 の極限を各段で取るだけで、この Ω 条件と構造射の単射性が得られたとは扱わない。
既存の Sp、対象、射、豊穣構造の定義は変更していない。

`SpectrumMappingDiagram` は L9 の実際の写像空間の後合成と各段評価の可換式
`spectrumHomMap_evaluation` を証明し、`spectrumMappingEvaluation` として自然変換へ束ねた。
点つき内部 Hom と忘却の二つの右随伴の極限保存、前合成と後合成の可換性、
懸垂の写像空間の自然性、構造射による境界比較の後合成に関する自然性も証明した。
この段階で通常の射の零単体だけに制限せず、写像単体集合全体の自然性を扱う。

`SpectrumHomLimitFamilies` は、任意の小圏 I の L9 のスペクトルの錐 c が各段で極限なら、
全ての豊穣 Hom の錐も実際に極限となることを証明した。主定理は

```lean
spectrumHomCone_isLimit_of_levelwise (c : Cone F)
    (hc : ∀ n, IsLimit (spectrumLevelCone c n)) (X : OmegaSpectrum.{u}) :
  IsLimit (simplicialHomCone c X)
```

共通の前提は `I : Type u`、`[SmallCategory I]`、`F : I ⥤ OmegaSpectrum.{u}`。
`spectrumLevelCone c n` は c の n 段への評価で、極限性は点つき単体集合の圏で指定する。
SimplicialCategory の実体には `OmegaSpectrum.simplicialCategory` を用いる。

証明では Hom 図式上の任意の錐 s について、各段の普遍射 `spectrumHomLimitFamily` を作る。
次段の境界 Hom の射影で検査し、前合成・後合成・懸垂の自然性からスペクトルの構造射との
整合性 `spectrumHomLimitFamily_condition` を導いた。L9 の既存の
`TruncatedMapping.familyLift` で実際の全写像空間への普遍射を構成し、全ての段と
全単体的パラメータでの射影則と一意性まで証明した。
別の写像空間の模型や、追加の Hom の比較同値は導入していない。
原典上の位置は BF 1978 §2、HTT 4.2.4.1、Kerodon 7.5.4.6。

新規21宣言の正確な型は以下。Ω スペクトルと点つき単体集合の単体的豊穣構造は
それぞれ L9 の `OmegaSpectrum.simplicialCategory` と `PointedEnrichment.simplicialCategory`。
I、F には上記の共通の前提を付ける。その他の前提は各型に明記した。

```lean
def spectrumLevelFunctor (n : ℕ) : OmegaSpectrum.{u} ⥤ PointedSimplicialSet.{u}

noncomputable def pointedMappingFunctor (A : PointedSimplicialSet.{u}) :
    PointedSimplicialSet.{u} ⥤ SSet.{u}

noncomputable instance pointedMappingFunctor_preservesLimits (A : PointedSimplicialSet.{u}) :
    PreservesLimits (pointedMappingFunctor A)

lemma spectrumHomMap_evaluation (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (f : Y ⟶ Z) (n : ℕ) :
    ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map f ≫
        OmegaSpectrum.evaluation X Z n =
      OmegaSpectrum.evaluation X Y n ≫
        (PointedObject.basedHomMap (X.level n).space (f.app n)).right

noncomputable def spectrumStageHomFunctor (X : OmegaSpectrum.{u}) (n : ℕ) :
    OmegaSpectrum.{u} ⥤ SSet.{u}

noncomputable def spectrumMappingEvaluation (X : OmegaSpectrum.{u}) (n : ℕ) :
    (SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X) ⟶
      spectrumStageHomFunctor X n

lemma pointedMapping_pre_post {A B Y Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (f : Y ⟶ Z) :
    PointedMapping.pre i Y ≫ (pointedMappingFunctor A).map f =
      (pointedMappingFunctor B).map f ≫ PointedMapping.pre i Z

lemma suspensionHom_post (A : PointedSimplicialSet.{u}) {B D : PointedSimplicialSet.{u}}
    (f : B ⟶ D) :
    (pointedMappingFunctor A).map f ≫ (suspensionHom A D).right =
      (suspensionHom A B).right ≫ (pointedMappingFunctor (suspension A)).map
        (PointedSimplicialSet.circle.{u} ◁ f)

lemma spectrumMappingStep_post (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (f : Y ⟶ Z) (n : ℕ) :
    OmegaSpectrum.mappingStep X Y n ≫
        (pointedMappingFunctor (suspension (X.level n).space)).map (f.app (n + 1)) =
      (pointedMappingFunctor (X.level n).space).map (f.app n) ≫
        OmegaSpectrum.mappingStep X Z n

def spectrumLevelCone (c : Cone F) (n : ℕ) : Cone (F ⋙ spectrumLevelFunctor n)

def spectrumStageHomCone (c : Cone F) (X : OmegaSpectrum.{u}) (n : ℕ) :
    Cone (F ⋙ spectrumStageHomFunctor X n)

def spectrumStageHomCone_isLimit (c : Cone F) (X : OmegaSpectrum.{u}) (n : ℕ)
    (hc : IsLimit (spectrumLevelCone c n)) : IsLimit (spectrumStageHomCone c X n)

def spectrumHomParameterCone (X : OmegaSpectrum.{u}) (n : ℕ)
    (s : Cone (simplicialHomDiagram F X)) : Cone (F ⋙ spectrumStageHomFunctor X n)

def spectrumHomLimitFamily (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) (n : ℕ) :
    s.pt ⟶ (PointedObject.basedHom (X.level n).space (c.pt.level n).space).right

lemma spectrumHomLimitFamily_fac (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) (n : ℕ) (i : I) :
    spectrumHomLimitFamily c hc X s n ≫
        (pointedMappingFunctor (X.level n).space).map ((c.π.app i).app n) =
      s.π.app i ≫ OmegaSpectrum.evaluation X (F.obj i) n

lemma spectrumHomLimitFamily_condition (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) (n : ℕ) :
    spectrumHomLimitFamily c hc X s (n + 1) ≫
        PointedMapping.pre (X.sigma n) (c.pt.level (n + 1)).space =
      spectrumHomLimitFamily c hc X s n ≫ OmegaSpectrum.mappingStep X c.pt n

def spectrumHomConeLift (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) :
    s.pt ⟶ OmegaSpectrum.mappingSpace X c.pt

lemma spectrumHomConeLift_evaluation (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) (n : ℕ) :
    spectrumHomConeLift c hc X s ≫ OmegaSpectrum.evaluation X c.pt n =
      spectrumHomLimitFamily c hc X s n

lemma spectrumHomConeLift_fac (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X)) (i : I) :
    spectrumHomConeLift c hc X s ≫ (simplicialHomCone c X).π.app i = s.π.app i

lemma spectrumHomConeLift_uniq (c : Cone F) (hc : ∀ n, IsLimit (spectrumLevelCone c n))
    (X : OmegaSpectrum.{u}) (s : Cone (simplicialHomDiagram F X))
    (m : s.pt ⟶ OmegaSpectrum.mappingSpace X c.pt)
    (hm : ∀ i, m ≫ (simplicialHomCone c X).π.app i = s.π.app i) :
    m = spectrumHomConeLift c hc X s

def spectrumHomCone_isLimit_of_levelwise (c : Cone F)
    (hc : ∀ n, IsLimit (spectrumLevelCone c n)) (X : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone c X)
```

これは Sp の実際の Hom 条件を段ごとの普遍性から検証する証明であり、
Sp の積・引き戻し・塔の極限対象を構成した定理ではない。
具体的な対象の Ω 条件と構造射の単射性、必要な Hom の fibration 条件を検証し、
三形状の ∞ 極限錐を公開する工程は未完了。元の非反転の end・q_x と反転係数の直接比較、
余極限側も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4528 jobs）、公開1084宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存758ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-hom-limits-aggregate.log` と
`/tmp/gamma3-spectrum-hom-limits-audit.log`。


### γ3c：Sp の二項積に向けた全基点 π_* 同型と Kan Ω 列の積

`KanPiProducts` は L9 の実際の `KanHomotopy` について、積の二つの射影による
`kanHomotopyProdMap n x y` が全単射であることを証明した。
全ての基点 (x,y) と全自然数次数 n を扱い、零次数を除外しない。
単射性は二つの充填関係を積へ組み合わせ、全射性は境界定数単体の代表を積へ組む。
積の射に関する自然性を証明し、`kanPiIsomorphism_tensor` として、全基点の π_* 同型の
二項積も全基点の π_* 同型であることを公開した。
指定した基点の正次数の群だけへ条件を弱めていない。

`SpectrumBinaryProductSequence` は loop の右随伴性から点つき二項積の標準同型
`loopProductIso A B : loopSpace (PointedObject.prod A B) ≅
PointedObject.prod (loopSpace A) (loopSpace B)` を構成し、射影との厳密な可換式を証明した。
二つの構造射から `binaryProductSigma s t` を作り、その随伴がこの同型の下で
二つの随伴構造射の積に厳密に一致することを `binaryProductSigma_adjoint` で証明。

L9 の二つの `KanSequence` の段ごとの二項積 `binaryProductKanSequence X Y` を構成した。
射影二本、任意の厳密な列の射 f、g を組にする普遍射、その射影則と一意性も公開した。
各段の Kan 性は点つき積の成分ごとの充填から得る。
主定理 `binaryProductKanSequence_omega` は

```lean
binaryProductKanSequence_omega (X Y : KanSequence.{u})
    (hX : X.OmegaCondition) (hY : Y.OmegaCondition) :
  (binaryProductKanSequence X Y).OmegaCondition
```

を与える。loop と積の厳密な同型、随伴構造射の計算、全基点 π_* 同型の二項積の保存から
Ω 条件を検証した。各段の構造射の単射性はこの証明の前提には置かない。
原典上の位置は BF 1978 §2、HA §1.4.2、Kerodon §3.2.2、HTT 4.2.4.1。

新規23宣言の正確な型・前提は以下。宇宙は u、KanHomotopy・KanPiIsomorphism・
KanSequence は L9 の既存のものを使う。

```lean
def prodPointedSimplex {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) : (X ⊗ Y).PtSimplex n (x, y)

lemma prodPointedSimplex_fst {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) :
    mapSimplex (fst X Y) rfl (prodPointedSimplex f g) = f

lemma prodPointedSimplex_snd {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f : X.PtSimplex n x) (g : Y.PtSimplex n y) :
    mapSimplex (snd X Y) rfl (prodPointedSimplex f g) = g

def kanHomotopyProdMap {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    KanHomotopy (X ⊗ Y) n (x, y) → KanHomotopy X n x × KanHomotopy Y n y

lemma kanHomotopyProdMap_bijective {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) : Function.Bijective (kanHomotopyProdMap n x y)

def kanHomotopyProdEquiv {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    KanHomotopy (X ⊗ Y) n (x, y) ≃ KanHomotopy X n x × KanHomotopy Y n y

lemma kanHomotopyProdMap_naturality {X Y X' Y' : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex X'] [KanComplex Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (a : KanHomotopy (X ⊗ Y) n (x, y)) :
    kanHomotopyProdMap n (f.app _ x) (g.app _ y)
        (KanHomotopy.map n (f ⊗ₘ g) rfl a) =
      Prod.map (KanHomotopy.map n f rfl) (KanHomotopy.map n g rfl)
        (kanHomotopyProdMap n x y a)

lemma kanPiIsomorphism_tensor {X Y X' Y' : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex X'] [KanComplex Y']
    {f : X ⟶ X'} {g : Y ⟶ Y'} (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g) :
    KanPiIsomorphism (f ⊗ₘ g)

def loopProductCone_isLimit (A B : PointedSimplicialSet.{u}) :
    IsLimit (BinaryFan.mk (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedObject.prodFst A B)) (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (PointedObject.prodSnd A B)))

def loopProductIso (A B : PointedSimplicialSet.{u}) :
    loopSpace (PointedObject.prod A B) ≅ PointedObject.prod (loopSpace A) (loopSpace B)

lemma loopProductIso_hom_fst (A B : PointedSimplicialSet.{u}) :
    (loopProductIso A B).hom ≫ PointedObject.prodFst (loopSpace A) (loopSpace B) =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (PointedObject.prodFst A B)

lemma loopProductIso_hom_snd (A B : PointedSimplicialSet.{u}) :
    (loopProductIso A B).hom ≫ PointedObject.prodSnd (loopSpace A) (loopSpace B) =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (PointedObject.prodSnd A B)

def binaryProductSigma {A B A' B' : PointedSimplicialSet.{u}}
    (s : suspension A ⟶ A') (t : suspension B ⟶ B') :
    suspension (PointedObject.prod A B) ⟶ PointedObject.prod A' B'

lemma binaryProductSigma_adjoint {A B A' B' : PointedSimplicialSet.{u}}
    (s : suspension A ⟶ A') (t : suspension B ⟶ B') :
    suspensionLoopEquiv _ _ (binaryProductSigma s t) ≫ (loopProductIso A' B').hom =
      PointedObject.prodMap (suspensionLoopEquiv _ _ s) (suspensionLoopEquiv _ _ t)

def binaryProductKanSequence (X Y : KanSequence.{u}) : KanSequence.{u}

def binaryProductKanSequenceFst (X Y : KanSequence.{u}) :
    KanSequence.Hom (binaryProductKanSequence X Y) X

def binaryProductKanSequenceSnd (X Y : KanSequence.{u}) :
    KanSequence.Hom (binaryProductKanSequence X Y) Y

lemma kanSequenceHom_ext {X Y : KanSequence.{u}} {f g : KanSequence.Hom X Y}
    (h : ∀ n, f.app n = g.app n) : f = g

def binaryProductKanSequenceLift {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    KanSequence.Hom Z (binaryProductKanSequence X Y)

lemma binaryProductKanSequenceLift_fst {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    (binaryProductKanSequenceLift f g).comp (binaryProductKanSequenceFst X Y) = f

lemma binaryProductKanSequenceLift_snd {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y) :
    (binaryProductKanSequenceLift f g).comp (binaryProductKanSequenceSnd X Y) = g

lemma binaryProductKanSequenceLift_uniq {X Y Z : KanSequence.{u}}
    (f : KanSequence.Hom Z X) (g : KanSequence.Hom Z Y)
    (m : KanSequence.Hom Z (binaryProductKanSequence X Y))
    (hf : m.comp (binaryProductKanSequenceFst X Y) = f)
    (hg : m.comp (binaryProductKanSequenceSnd X Y) = g) :
    m = binaryProductKanSequenceLift f g

lemma binaryProductKanSequence_omega (X Y : KanSequence.{u})
    (hX : X.OmegaCondition) (hY : Y.OmegaCondition) :
    (binaryProductKanSequence X Y).OmegaCondition
```

今回の対象は構造射の単射性をまだ要求しない Kan Ω 列の二項積。
L9 の `OmegaSpectrum` として束縛する構造射の単射性の検証、Sp の二項積の錐と極限性、
空積と一般の有限積、引き戻しと塔の実際の Sp の極限の公開は未完了。
この中間の列の Ω 条件と普遍性だけで Sp の有限積を完了とは数えない。
元の非反転の end・q_x と反転係数の直接比較、余極限側も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4587 jobs）、公開1107宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-binary-product-sequence-aggregate.log` と
`/tmp/gamma3-spectrum-binary-product-sequence-audit.log`。


### γ3c：smash の単体表示と Sp の実際の二項積

`SmashSimplex` は各次数の smash を「両成分が非基点の組、または基点」として表す
集合の計算を与える。組を潰す標準写像の全射性・核の等式と、二つの射影による
`A ∧ (B × C) → (A ∧ B) × (A ∧ C)` の単射性を証明した。
`SmashSimplexModel` は面・退化作用を入れ、両軸の零化と pushout の普遍性から
既存の smash との標準同型 `smashSimplexModelIso` を構成した。
既存の smash や L9 の対象の定義は変更していない。

`SmashProductMono` はこの同型から既存の標準射の各次数の全射性を得て、
二つの射影を使う標準比較 `smashProductComparison` の基礎単体写像のモノ射性を証明した。
ここには Kan 性の仮定はない。`binaryProductSigma_factor` で積の構造射を
この比較と二構造射の積に分解し、元の二構造射がモノ射なら積の構造射もモノ射とした。

`SpectrumBinaryProduct` は前回の Kan Ω 列の積の全基点の Ω 条件とこの単射性を合わせ、
L9 の実際の `OmegaSpectrum` の対象 `spectrumBinaryProduct X Y` を構成した。
各段は点つき通常積、構造射は `binaryProductSigma`。
二つの厳密な射影、持ち上げた離散二対象の図式、その錐、各段の極限性を公開した。
既存の `spectrumHomCone_isLimit_of_levelwise` を適用して全ての実際の豊穣 Hom の
極限性を得て、離散図式の比較定理から coherent nerve の実際の極限錐性を得る。
主定理は `spectrumBinaryProductInfinityCone_isLimit (X Y : OmegaSpectrum.{u})`。
追加の条件付き入力はなく、L9 の OmegaSpectrum の定義に含まれる Kan 性・単射な構造射・
全基点の Ω 条件だけを使う。Sp の二項積については実際の対象と ∞ 極限錐まで完成した。
原典上の位置は BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の双対、Kerodon 7.5.4.6。

新規44宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
`SpectrumBinaryProduct` の最後の三宣言では L9 の
`OmegaSpectrum.simplicialCategory` を局所 instance として使う。
公開宣言の公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`SmashSimplex`：

```lean
abbrev SmashSimplex {A B : Type u} (a₀ : A) (b₀ : B)

def smashSimplexPack {A B : Type u} (a₀ : A) (b₀ : B) (a : A) (b : B) :
    SmashSimplex a₀ b₀

lemma smashSimplexPack_eq_none {A B : Type u} (a₀ : A) (b₀ : B) (a : A) (b : B) :
    smashSimplexPack a₀ b₀ a b = none ↔ a = a₀ ∨ b = b₀

lemma smashSimplexPack_surjective {A B : Type u} (a₀ : A) (b₀ : B) :
    ∀ s : SmashSimplex a₀ b₀, ∃ a b, smashSimplexPack a₀ b₀ a b = s

lemma smashSimplexPack_eq_iff {A B : Type u} (a₀ : A) (b₀ : B)
    (a a' : A) (b b' : B) :
    smashSimplexPack a₀ b₀ a b = smashSimplexPack a₀ b₀ a' b' ↔
      (a = a' ∧ b = b') ∨ ((a = a₀ ∨ b = b₀) ∧ (a' = a₀ ∨ b' = b₀))

def smashSimplexMap {A B C D : Type u} {a₀ : A} {b₀ : B} (c₀ : C) (d₀ : D)
    (f : A → C) (g : B → D) : SmashSimplex a₀ b₀ → SmashSimplex c₀ d₀

lemma smashSimplexMap_pack {A B C D : Type u} {a₀ : A} {b₀ : B} {c₀ : C} {d₀ : D}
    (f : A → C) (g : B → D) (hf : f a₀ = c₀) (hg : g b₀ = d₀) (a : A) (b : B) :
    smashSimplexMap c₀ d₀ f g (smashSimplexPack a₀ b₀ a b) =
      smashSimplexPack c₀ d₀ (f a) (g b)

def smashSimplexProductComparison {A B C : Type u} (a₀ : A) (b₀ : B) (c₀ : C) :
    SmashSimplex a₀ (b₀, c₀) → SmashSimplex a₀ b₀ × SmashSimplex a₀ c₀

lemma smashSimplexProductComparison_pack {A B C : Type u}
    (a₀ : A) (b₀ : B) (c₀ : C) (a : A) (b : B) (c : C) :
    smashSimplexProductComparison a₀ b₀ c₀ (smashSimplexPack a₀ (b₀, c₀) a (b, c)) =
      (smashSimplexPack a₀ b₀ a b, smashSimplexPack a₀ c₀ a c)

lemma smashSimplexProductComparison_injective {A B C : Type u} (a₀ : A) (b₀ : B) (c₀ : C) :
    Function.Injective (smashSimplexProductComparison a₀ b₀ c₀)
```

`SmashSimplexModel`：

```lean
def smashSimplexModelSSet (A B : PointedSimplicialSet.{u}) : SSet.{u}

def smashSimplexModel (A B : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u}

lemma smashSimplexModel_basepoint (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    PointedSimplicialSet.basepointAt (smashSimplexModel A B) d = none

def smashSimplexModelQuotient (A B : PointedSimplicialSet.{u}) :
    PointedObject.prod A B ⟶ smashSimplexModel A B

lemma pointedZero_app (A B : PointedSimplicialSet.{u}) (d : SimplexCategoryᵒᵖ)
    (a : A.right.obj d) : (0 : A ⟶ B).right.app d a =
      PointedSimplicialSet.basepointAt B d

lemma smashSimplexModelQuotient_axisLeft (A B : PointedSimplicialSet.{u}) :
    PointedObject.axisLeft A B ≫ smashSimplexModelQuotient A B = 0

lemma smashSimplexModelQuotient_axisRight (A B : PointedSimplicialSet.{u}) :
    PointedObject.axisRight A B ≫ smashSimplexModelQuotient A B = 0

def smashToSimplexModel (A B : PointedSimplicialSet.{u}) :
    PointedObject.smash A B ⟶ smashSimplexModel A B

lemma smashToSimplexModel_quotient (A B : PointedSimplicialSet.{u}) :
    PointedObject.smashQuotient A B ≫ smashToSimplexModel A B =
      smashSimplexModelQuotient A B

lemma smashQuotient_axisLeft_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) :
    (PointedObject.smashQuotient A B).right.app d
        (a, PointedSimplicialSet.basepointAt B d) =
      PointedSimplicialSet.basepointAt (PointedObject.smash A B) d

lemma smashQuotient_axisRight_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (b : B.right.obj d) :
    (PointedObject.smashQuotient A B).right.app d
        (PointedSimplicialSet.basepointAt A d, b) =
      PointedSimplicialSet.basepointAt (PointedObject.smash A B) d

def simplexModelToSmashApp (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) : (smashSimplexModelSSet A B).obj d →
      (PointedObject.smash A B).right.obj d

lemma simplexModelToSmashApp_pack (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) (b : B.right.obj d) :
    simplexModelToSmashApp A B d
        (smashSimplexPack (PointedSimplicialSet.basepointAt A d)
          (PointedSimplicialSet.basepointAt B d) a b) =
      (PointedObject.smashQuotient A B).right.app d (a, b)

def simplexModelToSmash (A B : PointedSimplicialSet.{u}) :
    smashSimplexModel A B ⟶ PointedObject.smash A B

lemma simplexModelToSmash_quotient (A B : PointedSimplicialSet.{u}) :
    smashSimplexModelQuotient A B ≫ simplexModelToSmash A B =
      PointedObject.smashQuotient A B

def smashSimplexModelIso (A B : PointedSimplicialSet.{u}) :
    PointedObject.smash A B ≅ smashSimplexModel A B
```

`SmashProductMono`：

```lean
lemma pointedProduct_basepointAt (B C : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    PointedSimplicialSet.basepointAt (PointedObject.prod B C) d =
      (PointedSimplicialSet.basepointAt B d, PointedSimplicialSet.basepointAt C d)

lemma smashQuotient_app_surjective (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.Surjective ((PointedObject.smashQuotient A B).right.app d)

lemma smashToSimplexModel_quotient_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) (b : B.right.obj d) :
    (smashToSimplexModel A B).right.app d
        ((PointedObject.smashQuotient A B).right.app d (a, b)) =
      smashSimplexPack (PointedSimplicialSet.basepointAt A d)
        (PointedSimplicialSet.basepointAt B d) a b

lemma smashMap_quotient_app {A B A' B' : PointedSimplicialSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (d : SimplexCategoryᵒᵖ)
    (a : A.right.obj d) (b : B.right.obj d) :
    (PointedObject.smashMap f g).right.app d
        ((PointedObject.smashQuotient A B).right.app d (a, b)) =
      (PointedObject.smashQuotient A' B').right.app d (f.right.app d a, g.right.app d b)

def smashProductComparison (A B C : PointedSimplicialSet.{u}) :
    PointedObject.smash A (PointedObject.prod B C) ⟶
      PointedObject.prod (PointedObject.smash A B) (PointedObject.smash A C)

lemma smashProductComparison_app_injective (A B C : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((smashProductComparison A B C).right.app d)

instance smashProductComparison_mono (A B C : PointedSimplicialSet.{u}) :
    Mono (smashProductComparison A B C).right
```

`SpectrumBinaryProduct`：

```lean
lemma binaryProductSigma_factor {A B A' B' : PointedSimplicialSet.{u}}
    (s : suspension A ⟶ A') (t : suspension B ⟶ B') :
    binaryProductSigma s t =
      smashProductComparison PointedSimplicialSet.circle.{u} A B ≫ PointedObject.prodMap s t

instance binaryProductSigma_mono {A B A' B' : PointedSimplicialSet.{u}}
    (s : suspension A ⟶ A') (t : suspension B ⟶ B') [Mono s.right] [Mono t.right] :
    Mono (binaryProductSigma s t).right

def spectrumBinaryProduct (X Y : OmegaSpectrum.{u}) : OmegaSpectrum.{u}

def spectrumBinaryProductFst (X Y : OmegaSpectrum.{u}) : spectrumBinaryProduct X Y ⟶ X

def spectrumBinaryProductSnd (X Y : OmegaSpectrum.{u}) : spectrumBinaryProduct X Y ⟶ Y

def spectrumBinaryProductDiagram (X Y : OmegaSpectrum.{u}) :
    Discrete (ULift.{u} WalkingPair) ⥤ OmegaSpectrum.{u}

def spectrumBinaryProductCone (X Y : OmegaSpectrum.{u}) :
    Cone (spectrumBinaryProductDiagram X Y)

def spectrumBinaryProductCone_level_isLimit (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumBinaryProductCone X Y) n)

def spectrumBinaryProductCone_hom_isLimit (X Y Z : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone (spectrumBinaryProductCone X Y) Z)

def spectrumBinaryProductInfinityCone (X Y : OmegaSpectrum.{u}) :
    JoinCone (strictCoherentDiagram (spectrumBinaryProductDiagram X Y))

lemma spectrumBinaryProductInfinityCone_isLimit (X Y : OmegaSpectrum.{u}) :
    IsLimitCone (spectrumBinaryProductInfinityCone X Y)
```

Sp の空積と一般の有限積への束ね直し、一脚 fibration の引き戻し、fibration の塔は未完了。
元の非反転の end・q_x と反転係数の直接比較、余極限側、E2a 完了後の E2b 適用も未完了。
二項積だけを γ3 全体の完了とは数えず、作業を継続する。

検証：対象集約 `HomotopyLimits` のビルド成功（4591 jobs）、公開1151宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-binary-product-aggregate.log` と
`/tmp/gamma3-spectrum-binary-product-audit.log`。


### γ3c：Sp の空積を含む全ての有限積

`SpectrumPoint` は各段が `PointedObject.point` の実際の `spectrumPoint` を構成した。
一点の Kan 性は終対象へのホーン充填で証明した。
`suspensionPoint_isZero` と `loopPoint_isZero` は懸垂・loop の随伴を使い、
一点から出る射・一点へ入る射の一意性をそれぞれ移して得る。
構造射は一点への射で、零対象間の同型なので基礎単体写像もモノ射。
その随伴も零対象間の同型なので、全基点・零次数を含む Ω 条件を満たす。
Kan 列の中間対象に止めず、L9 の `OmegaSpectrum` に束ねた。

`SpectrumFiniteProducts` は `spectrumPoint_isTerminal` で通常のスペクトルの圏の終対象性を、
`spectrumBinaryProductLift` と `spectrumBinaryFan_isLimit` で前回の実際の二項積の
通常の普遍性を証明した。その終対象と二項積を入力に、Mathlib の有限帰納の構成で
`spectrumHasFiniteProducts` を得た。添字は任意の有限型でよく、空の型も含む。
これらの存在・保存のクラスの補題はこのモジュール内だけで instance として使う。
外部で型クラスとして使う場合は対応する公開補題を局所 instance にできる。

各段の評価 `spectrumLevelFunctor n` について終対象と二項積の保存を直接確認し、
`spectrumLevel_preservesFiniteProducts` を証明した。
任意の `J : Type u`、`[Finite J]`、`F : Discrete J ⥤ OmegaSpectrum.{u}` に対し、
`spectrumFiniteProductCone F` はこの構成から選んだ実際の通常の極限錐。
`spectrumFiniteProductCone_level_isLimit` はその全ての段が点つき単体的集合の極限錐で
あることを与える。L9 の実際の写像空間の全パラメータの普遍性を使って
全ての豊穣 Hom の極限性へ移し、既存の離散図式の比較定理を適用した。

主定理は `spectrumFiniteProductInfinityCone_isLimit`。
底は元の有限離散図式の nerve、標的は L9 の `Sp` と同じ coherent nerve。
追加仮定は添字 J の有限性だけで、空積・一点積・全ての有限積を含む。
構造射の単射性、全基点の Ω 条件、各段と実際の豊穣 Hom の普遍性は検証済みの構成から得る。
Sp の有限積の工程はこれで実際の対象と ∞ 極限錐まで完成した。
原典上の位置は BF 1978 §2、HA §1.4.2、HTT 4.2.4.1 の双対、Kerodon 7.5.4.6。

新規19宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
最後の三宣言では L9 の `OmegaSpectrum.simplicialCategory` を局所 instance として使う。
公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`SpectrumPoint`：

```lean
instance pointedPoint_kanComplex :
    KanComplex (PointedObject.point : PointedSimplicialSet.{u}).right

lemma suspensionPoint_isZero :
    IsZero (suspension (PointedObject.point : PointedSimplicialSet.{u}))

lemma loopPoint_isZero :
    IsZero (loopSpace (PointedObject.point : PointedSimplicialSet.{u}))

def spectrumPoint : OmegaSpectrum.{u}
```

`SpectrumFiniteProducts`：

```lean
def spectrumPoint_isTerminal : IsTerminal spectrumPoint.{u}

def spectrumBinaryProductLift {X Y Z : OmegaSpectrum.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ spectrumBinaryProduct X Y

def spectrumBinaryFan_isLimit (X Y : OmegaSpectrum.{u}) :
    IsLimit (BinaryFan.mk (spectrumBinaryProductFst X Y) (spectrumBinaryProductSnd X Y))

lemma spectrumHasTerminal : HasTerminal OmegaSpectrum.{u}

lemma spectrumHasBinaryProducts : HasBinaryProducts OmegaSpectrum.{u}

lemma spectrumHasFiniteProducts : HasFiniteProducts OmegaSpectrum.{u}

lemma spectrumLevel_preservesTerminal (n : ℕ) :
    PreservesLimit (Functor.empty.{0} OmegaSpectrum.{u}) (spectrumLevelFunctor n)

lemma spectrumLevel_preservesBinaryProducts (n : ℕ) :
    PreservesLimitsOfShape (Discrete WalkingPair) (spectrumLevelFunctor n)

lemma spectrumLevel_preservesFiniteProducts (n : ℕ) :
    PreservesFiniteProducts (spectrumLevelFunctor n)

def spectrumFiniteProductCone {J : Type u} [Finite J] (F : Discrete J ⥤ OmegaSpectrum.{u}) :
    Cone F

def spectrumFiniteProductCone_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : IsLimit (spectrumFiniteProductCone F)

def spectrumFiniteProductCone_level_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumFiniteProductCone F) n)

def spectrumFiniteProductCone_hom_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) (X : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone (spectrumFiniteProductCone F) X)

def spectrumFiniteProductInfinityCone {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : JoinCone (strictCoherentDiagram F)

lemma spectrumFiniteProductInfinityCone_isLimit {J : Type u} [Finite J]
    (F : Discrete J ⥤ OmegaSpectrum.{u}) : IsLimitCone (spectrumFiniteProductInfinityCone F)
```

Sp の一脚 fibration の引き戻しと fibration の塔の実際の極限錐は未完了。
元の非反転の end・q_x と反転係数の直接比較、余極限側、E2a 完了後の E2b 適用も未完了。
γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4593 jobs）、公開1170宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルの警告・sorry・追加公理はない。
他担当の依存812ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-finite-products-aggregate.log` と
`/tmp/gamma3-spectrum-finite-products-audit.log`。


### γ3c：Sp の引き戻し構造射の単射性と実際の随伴比較

`SmashMonomorphisms` は基点を保つ二つの単射について、各次数の smash の具体的表示への
作用が単射であることを証明した。既存の smash の標準射の各次数の全射性と表示の同型を使い、
`smashMap_app_injective`・`smashMap_mono` として基礎単体写像のモノ射性へ戻した。
`pointedWhiskerLeft_mono` は任意の左因子との smash が基礎モノ射を保つことを与える。
ここには Kan 性やモデル構造の仮定はない。

`SpectrumPullbackMonomorphisms` は、点つき引き戻しの二つの射影を組にする
`pointedPullbackToProduct` の基礎単体写像がモノ射であることを、既存の台の引き戻しの
普遍性で証明した。L9 の既存の `KanSequence.pullbackSigma f g n` について、
次段の積への包含との合成は、現在段の包含の懸垂と二項積の構造射の合成に一致する。
この可換式 `pullbackSigma_product_factor` と前回の積の構造射の単射性を使い、
`pullbackSigma_mono` を得た。要求するのは二つの全空間列 E、X の構造射の単射性だけで、
底の列 B の構造射や二つの射 f、g の fibration 性は使わない。
L9 の二つの OmegaSpectrum からの cospan に対しては、元の sigma_mono がこの前提を満たす。
引き戻しの構造射を単射へ置換する工程は、この段ごとの構成には不要となった。

`SpectrumPullbackAdjoints` は loop が右随伴であることから、通常の点つき引き戻しとの
標準同型 `loopPullbackIso` を構成した。二つの射影との厳密な可換式も公開した。
`pullbackAdjointMap f g n` は元の二つの随伴構造射を各射影と合成し、
列の射の随伴可換式で貼り合わせた実際の引き戻し間の射。
`pullbackSigma_adjoint` は引き戻し構造射の随伴を loop–引き戻し同型と合成すると
この比較射へ厳密に一致することを証明した。これらの代数的な等式には fibration 性は不要。

一脚 f が各段で Kan fibration のとき、`pullbackSequence_omega_iff` は
L9 の実際の引き戻し Kan 列の Ω 条件と、全 n に対する
`KanPiIsomorphism (pullbackAdjointMap f g n).right` の同値を与える。
全基点・零次数を含む元の Ω 条件を保持し、指定基点の正次数だけへ弱めていない。
ただし、元の三つの列の Ω 条件からこの比較射の π_* 同型性を導く保存定理は未証明。
この同値だけを Sp の引き戻し対象の完成とは数えない。
原典上の位置は BF 1978 §2、HA §1.4.2、Goerss–Jardine I §§7–8、HTT 4.2.4.1。

新規14宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`SmashMonomorphisms`：

```lean
lemma smashSimplexMap_injective {A B C D : Type u} {a₀ : A} {b₀ : B} {c₀ : C} {d₀ : D}
    (f : A → C) (g : B → D) (hf : f a₀ = c₀) (hg : g b₀ = d₀)
    (hi : Function.Injective f) (hj : Function.Injective g) :
    Function.Injective (smashSimplexMap (a₀

lemma smashMap_app_injective {A B C D : PointedSimplicialSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) [Mono f.right] [Mono g.right] (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((PointedObject.smashMap f g).right.app d)

instance smashMap_mono {A B C D : PointedSimplicialSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) [Mono f.right] [Mono g.right] :
    Mono (PointedObject.smashMap f g).right

instance pointedWhiskerLeft_mono (A : PointedSimplicialSet.{u})
    {B C : PointedSimplicialSet.{u}} (f : B ⟶ C) [Mono f.right] : Mono (A ◁ f).right
```

`SpectrumPullbackMonomorphisms`：

```lean
def pointedPullbackToProduct {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    pullback f g ⟶ PointedObject.prod E X

instance pointedPullbackToProduct_mono {E X B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (g : X ⟶ B) : Mono (pointedPullbackToProduct f g).right

lemma pullbackSigma_product_factor {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    KanSequence.pullbackSigma f g n ≫
        pointedPullbackToProduct (f.app (n + 1)) (g.app (n + 1)) =
      PointedSimplicialSet.circle.{u} ◁ pointedPullbackToProduct (f.app n) (g.app n) ≫
        binaryProductSigma (E.sigma n) (X.sigma n)

lemma pullbackSigma_mono {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    (hE : ∀ n, Mono (E.sigma n).right) (hX : ∀ n, Mono (X.sigma n).right) (n : ℕ) :
    Mono (KanSequence.pullbackSigma f g n).right
```

`SpectrumPullbackAdjoints`：

```lean
def loopPullbackIso {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    loopSpace (pullback f g) ≅
      pullback (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} f)
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} g)

lemma loopPullbackIso_hom_fst {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    (loopPullbackIso f g).hom ≫ pullback.fst _ _ =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pullback.fst f g)

lemma loopPullbackIso_hom_snd {E X B : PointedSimplicialSet.{u}} (f : E ⟶ B) (g : X ⟶ B) :
    (loopPullbackIso f g).hom ≫ pullback.snd _ _ =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pullback.snd f g)

def pullbackAdjointMap {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    pullback (f.app n) (g.app n) ⟶
      pullback (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (f.app (n + 1)))
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (g.app (n + 1)))

lemma pullbackSigma_adjoint {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B) (n : ℕ) :
    suspensionLoopEquiv _ _ (KanSequence.pullbackSigma f g n) ≫
        (loopPullbackIso (f.app (n + 1)) (g.app (n + 1))).hom =
      pullbackAdjointMap f g n

lemma pullbackSequence_omega_iff {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right] :
    (KanSequence.pullbackSequence f g).OmegaCondition ↔
      ∀ n, KanPiIsomorphism (pullbackAdjointMap f g n).right
```

Sp の引き戻しで残る工程は、元の Ω 条件から実際の比較射の全基点 π_* 同型性を証明すること、
実際の Ω スペクトルの錐を束ねること、豊穣 Hom の fibration 条件を検証して ∞ 極限錐を公開すること。
Sp の塔、元の非反転の end・q_x と反転係数の直接比較、余極限側、E2a 完了後の E2b 適用も未完了。
γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4605 jobs）、公開1184宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存821ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-structure-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-structure-audit.log`。


### γ3c：fibration の fiber・底から全空間の全次数を比較する補題

Sp の引き戻しの Ω 条件で必要な比較に向け、全空間の π_* 同型の判定を整えた。
`GroupPointedFiveLemma` の `group_pointed_five_lemma` は、最初の四項だけが群で、
最後の項が任意の基点付き集合でよい五項補題。最後の写像に準同型性は要求せず、
最後の縦写像は基点保存と単射性だけを使う。
`FibrationTotalPositive` はこれを Kan fibration の自然な長完全列の
底・fiber・全空間・底・fiber の五項へ適用した。
`fibrationTotal_positive_bijective` は底と指定 fiber の全基点 π_* 同型性から、
全空間の指定基点の全ての正次数の全単射性を与える。
基本群 π₁ の次の fiber の π₀ を群として扱わず、n=0 も同じ証明で含める。

零次数の比較では、空の fiber に対する `KanPiIsomorphism` の全基点条件は自動的に成立し、
それだけから成分の全射性を導けないことに注意して前提を分けた。
`FibrationComponentTransport` の `fibration_vertex_in_component` は、底の連結成分の
等号を一本の辺へ戻し、指定始点から Kan fibration に沿って持ち上げる。
`fibration_componentFiber_exists` と `fibration_componentFiber_exact` は、
**任意の底の頂点 b** について、その頂点に写る全空間の成分が fiber の成分から来ることを与える。
既存の参照頂点 e の像 p(e) 上だけの完全性を使う界面とは別に、
fiber の参照頂点や非空性を先に仮定しない界面を公開した。

`FibrationTotalComponents` は任意の b 上の射 `fibrationFiberMapBase` を定義した。
全空間の π₀ の単射性は、底の π_* 同型性と各全空間頂点の像の上の fiber の成分の単射性から得る。
全射性は、底の成分の全射性と **全ての b 上の fiber の成分の全射性** から得る。
`fibrationTotal_piIsomorphism` は、底の π_* 同型、各全空間頂点の像の上の fiber の
全基点 π_* 同型、およびこの全 b の成分の全射性を入力に、全空間の全基点・全自然数次数の
π_* 同型を証明する。零次数と正次数をそれぞれの正確な条件で検証した。

`FibrationAllFibers` の `fibrationFiberMapBase_piIsomorphism_of_vertex` は、
指定 fiber に頂点がある場合、元の全空間と底の π_* 同型からその fiber の π_* 同型を得る。
`fibrationFiberMapBase_piZero_surjective` は、元の全空間の参照頂点 e₀ と
全空間・底の π_* 同型性から、**任意の b 上の成分の全射性** を証明した。
標的 fiber の成分を全空間で戻し、底の成分の単射性から源の fiber へ移して頂点を得て、
その頂点で既存の fiber 比較を使う。源の fiber が空の可能性もこの手順で検査する。
参照頂点 e₀ は、全基点の条件から全空間の π₀ の全射性を得るために明示している。
L9 の点つき各段を使うときには、その基点を e₀ として渡せる。
原典上の位置は Goerss–Jardine I §§7–8、Kerodon 3.2.6、BF 1978 §2、HTT 4.2.4.1。

新規12宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`GroupPointedFiveLemma`：

```lean
lemma group_pointed_five_lemma
    {A B C D E A' B' C' D' E' : Type u}
    [Group A] [Group B] [Group C] [Group D]
    [Group A'] [Group B'] [Group C'] [Group D']
    (e : E) (e' : E')
    (d₁ : A →* B) (d₂ : B →* C) (d₃ : C →* D) (d₄ : D → E)
    (d₁' : A' →* B') (d₂' : B' →* C') (d₃' : C' →* D') (d₄' : D' → E')
    (f₁ : A →* A') (f₂ : B →* B') (f₃ : C →* C') (f₄ : D →* D') (f₅ : E → E')
    (h₁ : ∀ a, f₂ (d₁ a) = d₁' (f₁ a))
    (h₂ : ∀ b, f₃ (d₂ b) = d₂' (f₂ b))
    (h₃ : ∀ c, f₄ (d₃ c) = d₃' (f₃ c))
    (h₄ : ∀ d, f₅ (d₄ d) = d₄' (f₄ d)) (h₅ : f₅ e = e')
    (ex₁ : ∀ b, d₂ b = 1 ↔ ∃ a, d₁ a = b)
    (ex₂ : ∀ c, d₃ c = 1 ↔ ∃ b, d₂ b = c)
    (ex₃ : ∀ d, d₄ d = e ↔ ∃ c, d₃ c = d)
    (ex₁' : ∀ b, d₂' b = 1 ↔ ∃ a, d₁' a = b)
    (ex₂' : ∀ c, d₃' c = 1 ↔ ∃ b, d₂' b = c)
    (ex₃' : ∀ d, d₄' d = e' ↔ ∃ c, d₃' c = d)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Bijective f₂)
    (hf₄ : Function.Bijective f₄) (hf₅ : Function.Injective f₅) :
    Function.Bijective f₃
```

`FibrationTotalPositive`：

```lean
lemma fibrationTotal_positive_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : KanPiIsomorphism g) (e : E _⦋0⦌)
    (hF : KanPiIsomorphism (fiberMap p p' f g comm e)) (n : ℕ) :
    Function.Bijective (KanHomotopyGroup.map (n
```

`FibrationComponentTransport`：

```lean
lemma fibration_vertex_in_component {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e : E _⦋0⦌) (b : B _⦋0⦌)
    (hb : π₀.mk (p.app _ e) = π₀.mk b) :
    ∃ e' : E _⦋0⦌, p.app _ e' = b ∧ π₀.mk e' = π₀.mk e

lemma fibration_componentFiber_exists {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (b : B _⦋0⦌) (a : π₀ E)
    (ha : mapπ₀ p a = π₀.mk b) :
    ∃ c : π₀ (KanFiber p b), mapπ₀ (fiberι p b) c = a

lemma fibration_componentFiber_exact {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (b : B _⦋0⦌) (a : π₀ E) :
    mapπ₀ p a = π₀.mk b ↔
      ∃ c : π₀ (KanFiber p b), mapπ₀ (fiberι p b) c = a
```

`FibrationTotalComponents`：

```lean
def fibrationFiberMapBase {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) : KanFiber p b ⟶ KanFiber p' (g.app _ b)

lemma fibrationFiberMapBase_ι {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    fibrationFiberMapBase p p' f g comm b ≫ fiberι p' (g.app _ b) = fiberι p b ≫ f

lemma fibrationTotal_piZero_injective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : KanPiIsomorphism g)
    (hF : ∀ e : E _⦋0⦌, Function.Injective (mapπ₀ (fiberMap p p' f g comm e))) :
    Function.Injective (mapπ₀ f)

lemma fibrationTotal_piZero_surjective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : Function.Surjective (mapπ₀ g))
    (hF : ∀ b : B _⦋0⦌, Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))) :
    Function.Surjective (mapπ₀ f)

lemma fibrationTotal_piIsomorphism {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : KanPiIsomorphism g)
    (hF : ∀ e : E _⦋0⦌, KanPiIsomorphism (fiberMap p p' f g comm e))
    (hF₀ : ∀ b : B _⦋0⦌,
      Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))) :
    KanPiIsomorphism f
```

`FibrationAllFibers`：

```lean
lemma fibrationFiberMapBase_piIsomorphism_of_vertex {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g)
    (b : B _⦋0⦌) (v : (KanFiber p b) _⦋0⦌) :
    KanPiIsomorphism (fibrationFiberMapBase p p' f g comm b)

lemma fibrationFiberMapBase_piZero_surjective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : KanPiIsomorphism f) (hg : KanPiIsomorphism g) (e₀ : E _⦋0⦌) (b : B _⦋0⦌) :
    Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))
```

これらは全空間の比較に必要な補題であり、Sp の引き戻しの Ω 条件そのものの証明ではない。
次に、引き戻し射影の fiber と元の fibration の fiber の標準同型を構成し、
実際の `pullbackAdjointMap` へこれらの比較を適用する。
引き戻しの Ω スペクトルと錐の束ね直し、豊穣 Hom の fibration 条件と ∞ 極限性、Sp の塔、
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4627 jobs）、公開1196宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-fibration-total-comparison-aggregate.log` と
`/tmp/gamma3-fibration-total-comparison-audit.log`。


### γ3c：Sp の実際の引き戻し対象の Ω 条件と全豊穣 Hom の普遍性

`PullbackFiberIso` は、任意の単体集合の引き戻し正方形
`P → E, P → X, E → B, X → B` について、第二射影の x 上の fiber と
元の第一脚の b 上の fiber の標準同型 `pullbackFiberIso` を構成した。
q(x)=b の等号を明示し、二つの引き戻しの普遍性だけで順射と逆射を検証した。
Kan 性・fibration 性・非空性は不要で、空の fiber も同じ同型で扱う。
`PullbackFiberNaturality` は二つの引き戻しの比較に対する同型の自然性を包含後で証明し、
同型による可換な表示の変更の下で π_* 同型性と π₀ 全射性を移す補題を公開した。
零次数の全射性の移送には Kan 性や非空性を仮定しない。

`FiberBaseComparison` は等しい底の頂点上の fiber の同型 `fiberBaseIso` を与え、
任意の底上の `fibrationFiberMapBase` を L9 の参照頂点の像上の `fiberMap` に同定した。
これを前回の全空間比較へ渡す `fibrationTotal_piIsomorphism_of_base` を証明した。
`PullbackPiComparison` の `pullbackComparison_piIsomorphism` は、
二つの一脚 Kan fibration の引き戻しを比較する三つの射が全基点 π_* 同型なら、
引き戻し間の実際の射も全基点 π_* 同型であることを証明する。
零次数の全射性の検査に元の全空間 E の頂点 e₀ を明示し、空の fiber を省略しない。
各引き戻しの第一射影の可換条件、第二射影の可換条件、元の二脚の可換条件を全て要求する。

`SpectrumPullbackOmega` はこの比較定理を実際の `pullbackAdjointMap f g n` に適用した。
三つの Kan 列 E、X、B が Ω 条件を満たし、f が各段で Kan fibration であれば、
`pullbackAdjointMap_piIsomorphism` はその射の全基点・零次数を含む π_* 同型性を与える。
元の点つき各段の基点を比較定理の e₀ として渡す。
`pullbackSequence_omega` は前回の厳密な随伴比較により、L9 の元の段ごとの引き戻し列が
実際に Ω 条件を満たすことを証明した。
元の二つの構造射が単射なら引き戻し構造射も単射である前回の結果と合わせ、

```lean
def spectrumPullback {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : OmegaSpectrum.{u}
```

を構成した。各段は元の点つき通常引き戻しそのもので、単射置換や別の Sp の模型を使わない。
二つの厳密なスペクトルの射影と底への合成の一致も公開した。

`SpectrumPullbackCones` は持ち上げた cospan の実際の図式・錐を構成した。
各段の点つき引き戻しの普遍性と添字の圏同値から、
`spectrumPullbackCone_level_isLimit` で全ての段の極限性を証明した。
L9 の実際の写像空間の族の普遍性を適用して、
`spectrumPullbackCone_hom_isLimit` は全ての豊穣 Hom の極限性を与える。
coherent nerve の実際の錐 `spectrumPullbackInfinityCone` も構成した。
ただし Hom の左脚の fibration 性はまだ未証明なので、
この錐を `IsLimitCone` とする Sp の ∞ 引き戻しの工程全体は未完了。
原典上の位置は Goerss–Jardine I §§7–8、Kerodon 3.2.5–3.2.6、BF 1978 §2、
HA §1.4.2、HTT 4.2.4.1 の双対。

新規27宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
`SpectrumPullbackCones` の最後の二宣言では L9 の `OmegaSpectrum.simplicialCategory` を
固有名を持つ局所 instance として使う。公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`PullbackFiberIso`：

```lean
def pullbackFiberToOriginal
    {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : KanFiber j x ⟶ KanFiber p b

def originalFiberToPullback
    {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : KanFiber p b ⟶ KanFiber j x

lemma pullbackFiberToOriginal_ι
    {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) :
    pullbackFiberToOriginal hP x b hxb ≫ fiberι p b = fiberι j x ≫ i

lemma originalFiberToPullback_ι
    {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) :
    originalFiberToPullback hP x b hxb ≫ fiberι j x =
      hP.lift (fiberι p b) (SSet.const x) (by rw [fiberι_comp, const_comp, hxb])

def pullbackFiberIso
    {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : KanFiber j x ≅ KanFiber p b
```

`PullbackFiberNaturality`：

```lean
lemma pullbackFiberIso_naturality
    {P E X B P' E' X' B' : SSet.{u}}
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    {i' : P' ⟶ E'} {j' : P' ⟶ X'} {p' : E' ⟶ B'} {q' : X' ⟶ B'}
    (hP : IsPullback i j p q) (hP' : IsPullback i' j' p' q')
    (aP : P ⟶ P') (aE : E ⟶ E') (aX : X ⟶ X') (aB : B ⟶ B')
    (hi : i ≫ aE = aP ≫ i') (hj : j ≫ aX = aP ≫ j')
    (hp : p ≫ aB = aE ≫ p') (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) (hxb' : q'.app _ (aX.app _ x) = aB.app _ b) :
    fibrationFiberMapBase j j' aP aX hj x ≫
        (pullbackFiberIso hP' (aX.app _ x) (aB.app _ b) hxb').hom =
      (pullbackFiberIso hP x b hxb).hom ≫ fibrationFiberMapBase p p' aE aB hp b

lemma kanPiIsomorphism_of_iso_square {A B C D : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex C] [KanComplex D]
    (e : A ≅ B) (e' : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ e'.hom = e.hom ≫ g) (hg : KanPiIsomorphism g) : KanPiIsomorphism f

lemma piZero_surjective_of_iso_square {A B C D : SSet.{u}}
    (e : A ≅ B) (e' : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f ≫ e'.hom = e.hom ≫ g) (hg : Function.Surjective (mapπ₀ g)) :
    Function.Surjective (mapπ₀ f)
```

`FiberBaseComparison`：

```lean
def fiberBaseIso {E B : SSet.{u}} (p : E ⟶ B) (b b' : B _⦋0⦌) (h : b = b') :
    KanFiber p b ≅ KanFiber p b'

lemma fiberBaseIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b b' : B _⦋0⦌) (h : b = b') :
    (fiberBaseIso p b b' h).hom ≫ fiberι p b' = fiberι p b

lemma fibrationFiberMapBase_to_fiberMap {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (e : E _⦋0⦌) :
    fibrationFiberMapBase p p' f g comm (p.app _ e) ≫
        (fiberBaseIso p' _ _ (base_eq p p' f g comm e)).hom = fiberMap p p' f g comm e

lemma fibrationTotal_piIsomorphism_of_base {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hg : KanPiIsomorphism g)
    (hF : ∀ b, KanPiIsomorphism (fibrationFiberMapBase p p' f g comm b))
    (hF₀ : ∀ b, Function.Surjective (mapπ₀ (fibrationFiberMapBase p p' f g comm b))) :
    KanPiIsomorphism f
```

`PullbackPiComparison`：

```lean
lemma pullbackSecond_fibration {P E X B : SSet.{u}}
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) [Fibration p] : Fibration j

lemma pullbackComparison_piIsomorphism
    {P E X B P' E' X' B' : SSet.{u}}
    [KanComplex P] [KanComplex E] [KanComplex X] [KanComplex B]
    [KanComplex P'] [KanComplex E'] [KanComplex X'] [KanComplex B']
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    {i' : P' ⟶ E'} {j' : P' ⟶ X'} {p' : E' ⟶ B'} {q' : X' ⟶ B'}
    (hP : IsPullback i j p q) (hP' : IsPullback i' j' p' q') [Fibration p] [Fibration p']
    (aP : P ⟶ P') (aE : E ⟶ E') (aX : X ⟶ X') (aB : B ⟶ B')
    (hi : i ≫ aE = aP ≫ i') (hj : j ≫ aX = aP ≫ j')
    (hp : p ≫ aB = aE ≫ p') (hq : q ≫ aB = aX ≫ q')
    (hE : KanPiIsomorphism aE) (hX : KanPiIsomorphism aX) (hB : KanPiIsomorphism aB)
    (e₀ : E _⦋0⦌) : KanPiIsomorphism aP
```

`SpectrumPullbackOmega`：

```lean
lemma pullbackAdjointMap_piIsomorphism {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right]
    (hE : E.OmegaCondition) (hX : X.OmegaCondition) (hB : B.OmegaCondition) (n : ℕ) :
    KanPiIsomorphism (pullbackAdjointMap f g n).right

lemma pullbackSequence_omega {E X B : KanSequence.{u}}
    (f : KanSequence.Hom E B) (g : KanSequence.Hom X B)
    [∀ n, Fibration (f.app n).right]
    (hE : E.OmegaCondition) (hX : X.OmegaCondition) (hB : B.OmegaCondition) :
    (KanSequence.pullbackSequence f g).OmegaCondition

def spectrumPullback {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : OmegaSpectrum.{u}

def spectrumPullbackFst {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : spectrumPullback f g ⟶ E

def spectrumPullbackSnd {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : spectrumPullback f g ⟶ X

lemma spectrumPullback_condition {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] :
    spectrumPullbackFst f g ≫ f = spectrumPullbackSnd f g ≫ g
```

`SpectrumPullbackCones`：

```lean
def spectrumPullbackDiagram
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B) : AsSmall.{u} WalkingCospan ⥤ OmegaSpectrum.{u}

def spectrumPullbackOrdinaryCone
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : PullbackCone f g

def spectrumPullbackCone
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : Cone (spectrumPullbackDiagram f g)

def spectrumPullbackOrdinaryCone_level_isLimit
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] (n : ℕ) :
    IsLimit ((spectrumLevelFunctor n).mapCone (spectrumPullbackOrdinaryCone f g))

def spectrumPullbackCone_level_isLimit
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] (n : ℕ) :
    IsLimit (spectrumLevelCone (spectrumPullbackCone f g) n)

def spectrumPullbackCone_hom_isLimit
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] (Z : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone (spectrumPullbackCone f g) Z)

def spectrumPullbackInfinityCone
    {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
    [∀ n, Fibration (f.app n).right] : JoinCone (strictCoherentDiagram (spectrumPullbackDiagram f g))
```

残る引き戻しの工程は、左脚が各段で fibration のスペクトル射の実際の豊穣 Hom 写像の
fibration 性を検証し、上記の錐を Sp の `IsLimitCone` として公開すること。
Sp の塔、非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4633 jobs）、公開1223宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規6ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-objects-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-objects-audit.log`。


### γ3c：Sp の実際の一脚 fibration の引き戻しの ∞ 極限性

`RelativePointedHomLifting` は、単射 i とパラメータのホーン j の pushout-product に沿う
持ち上げを `relativeTensorLift` として構成した。
`relativePointedHom_hornLift` はこれを点つき Hom の族へ適用し、
既存パラメータ上の族、i に沿って指定された族、標的の fibration への合成を同時に保つ。
uncurry して二つの部分を pushout へ貼り合わせ、充填した族の基点条件は
指定部分の基点が源の基点に一致することから得る。
源の単射性と標的の fibration 性だけを使い、パラメータや源の Kan 性は不要。

`SpectrumHomHornFamilies` の `spectrumHom_hornFamily` は、L9 のスペクトル射
p : Y → Z が各段で fibration のとき、Hom のホーンを各段で整合する族へ持ち上げる。
零段は点つき Hom の後合成の fibration 性を使う。
次段では源スペクトル X の構造射の単射性を用いて上の相対充填を適用する。
ホーン上の既存の族との一致、底への合成、前段からの構造整合条件を全て保持して帰納する。
境界比較の後合成に関する厳密な可換式 `spectrumMappingStep_post` を使って
相対充填の基底との整合性を検証した。

`SpectrumHomFibrations` の `spectrumHom_hornLift` はその整合族を、
L9 の全切断写像空間の実際の `TruncatedMapping.familyLift` へ束ねる。
各段の評価の普遍性からホーン上と底への二つの等式を確認した。
`spectrumHomMap_fibration` は任意の X について

```lean
instance spectrumHomMap_fibration (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right] :
    Fibration (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p)
```

を与える。対象・豊穣構造・写像空間は L9 の実際のものを使う。
各段の fibration 性以外の安定 fibration 条件や Hom の比較同値を仮定しない。

これを前回の引き戻し錐の全豊穣 Hom の極限性へ適用し、
`spectrumPullbackInfinityCone_isLimit` を証明した。
左脚 f が各段で Kan fibration であれば、右脚 g は任意でよい。
各段が点つき通常引き戻しである実際の OmegaSpectrum、二つの厳密な射影、
各段の普遍性、全豊穣 Hom の普遍性と左脚の fibration 性を全て検証した上で、
coherent nerve の既存の `IsLimitCone` を結論する。
Sp の指定された一脚 fibration の引き戻しの工程は、実際の対象と ∞ 極限錐まで完成した。
原典上の位置は BF 1978 §2、HTT A.3.3、HA §1.4.2、HTT 4.2.4.1 の双対、
Kerodon 7.5.3.12・7.5.4.6。

新規6宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
スペクトルの二モジュールでは L9 の `OmegaSpectrum.simplicialCategory` を固有名の局所 instance
として使い、最後の定理では局所 Kan 性も元の写像空間の Kan 性から与える。
公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`RelativePointedHomLifting`：

```lean
lemma relativeTensorLift {A X E B T U : SSet.{u}} (p : E ⟶ B) (i : A ⟶ X) (j : T ⟶ U)
    (h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (curriedTensor SSet.{u}) i j).ι p)
    (earlier : X ⊗ T ⟶ E) (prescribed : A ⊗ U ⟶ E) (base : X ⊗ U ⟶ B)
    (hc : i ▷ T ≫ earlier = A ◁ j ≫ prescribed)
    (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ U ≫ base) :
    ∃ l : X ⊗ U ⟶ E, X ◁ j ≫ l = earlier ∧ i ▷ U ≫ l = prescribed ∧ l ≫ p = base

lemma relativePointedHom_hornLift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) [Mono i.right] (p : E ⟶ B) [Fibration p.right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c
```

`SpectrumHomHornFamilies`：

```lean
lemma spectrumHom_hornFamily (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ OmegaSpectrum.mappingSpace X Y) (b : U ⟶ OmegaSpectrum.mappingSpace X Z)
    (h : a ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p =
      j ≫ b) :
    ∃ l : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right,
      (∀ n, j ≫ l n = a ≫ OmegaSpectrum.evaluation X Y n) ∧
      (∀ n, l n ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ OmegaSpectrum.evaluation X Z n) ∧
      (∀ n, l (n + 1) ≫ PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        l n ≫ OmegaSpectrum.mappingStep X Y n)
```

`SpectrumHomFibrations`：

```lean
lemma spectrumHom_hornLift (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ OmegaSpectrum.mappingSpace X Y) (b : U ⟶ OmegaSpectrum.mappingSpace X Z)
    (h : a ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p =
      j ≫ b) :
    ∃ l : U ⟶ OmegaSpectrum.mappingSpace X Y, j ≫ l = a ∧
      l ≫ ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p = b

instance spectrumHomMap_fibration (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}}
    (p : Y ⟶ Z) [∀ n, Fibration (p.app n).right] :
    Fibration (((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map p)

lemma spectrumPullbackInfinityCone_isLimit {E X B : OmegaSpectrum.{u}}
    (f : E ⟶ B) (g : X ⟶ B) [∀ n, Fibration (f.app n).right] :
    IsLimitCone (spectrumPullbackInfinityCone f g)
```

Sp の fibration の塔の実際の極限錐は未完了。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4636 jobs）、公開1229宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-pullback-infinity-aggregate.log` と
`/tmp/gamma3-spectrum-pullback-infinity-audit.log`。


### γ3c：塔の相対比較の持ち上げ性を極限へ移す準備

Sp の fibration の塔に向け、L9 の実際の `FibrationTower.limit` 上の比較を構成した。
`TowerMaps` の `towerMap f hf` は、遷移 dX、dY と厳密に可換な各段の射 f から、
整合族の極限の射を与える。各段への射影の式、恒等射と合成の保存を証明した。
`towerMatchingMap f hf n` は、次の源の段 X(n+1) から
`pullback (dY n) (f n)` への射で、成分は f(n+1) と dX(n)。
この標的は「次の標的の成分」と「既に選んだ源の前段の成分」の同時指定を表す。

`TowerMatchingLifting` の `towerRelative_liftFamily` は、任意の左射 j に対し、
初段 f(0) と全ての `towerMatchingMap f hf n` が j に対する持ち上げ性を持つなら、
塔の極限の射の可換正方形を各段の整合する持ち上げへ解く。
初段を充填した後、次の標的成分と前段の充填を上の引き戻しに組み、相対比較を充填する。
ホーン上の一致、底への合成、隣接段の遷移との一致を全て保持する。
`towerMap_hasLiftingProperty` はその族を実際の整合族の極限へ束ねる。
`towerMap_rlp` は任意の射のクラス W への RLP を同じ条件で極限の射へ移す。
W の閉性は要求しない。

`towerMap_fibration` は初段と相対比較が Kan fibration の場合に極限の射も fibration とする。
各段の f の fibration 性だけを前提とする主張ではなく、相対比較の fibration 性を明示している。
`towerMap_piIsomorphism_of_matching_rlp` は、両極限が Kan で、初段と相対比較が全ての単射に
RLP を持つとき、極限の射が全基点・全自然数次数の π_* 同型であることを与える。
段ごとの π_* 同型だけから相対比較の RLP を推論する工程は未証明。

その次工程で使う相対充填を `RelativePointedHomLifting` で拡張した。
`relativePointedHom_lift` は、必要な一つの pushout-product の持ち上げ性を明示し、
点つき Hom の既存族・指定部分・底への合成を同時に保つ充填を構成する。
既存の `relativePointedHom_hornLift` は同じ公開型を保ち、この一般の補題へ渡す形へ整理した。
新規 `relativePointedHom_anodyneLift` は、源の射が anodyne、標的の射が Kan fibration、
パラメータの射が任意の単射の場合の相対充填を証明する。
この補題を塔の mapping path の相対比較の全単射 RLP に用いる予定。
原典上の位置は Goerss–Jardine I §§7–8、HTT A.3.3、BF 1978 §2、HTT 4.2.4.1。

新規12宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
既存のホーン充填を含む全公開宣言の公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`TowerMaps`：

```lean
def towerMap {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    FibrationTower.limit X dX ⟶ FibrationTower.limit Y dY

lemma towerMap_projection {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    towerMap f hf ≫ FibrationTower.projection Y dY n =
      FibrationTower.projection X dX n ≫ f n

lemma towerMap_id (X : ℕ → SSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n) :
    towerMap (fun n ↦ 𝟙 (X n)) (fun n ↦ by simp) = 𝟙 (FibrationTower.limit X d)

lemma towerMap_comp {X Y Z : ℕ → SSet.{u}}
    {dX : ∀ n, X (n + 1) ⟶ X n} {dY : ∀ n, Y (n + 1) ⟶ Y n}
    {dZ : ∀ n, Z (n + 1) ⟶ Z n}
    (f : ∀ n, X n ⟶ Y n) (g : ∀ n, Y n ⟶ Z n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    (hg : ∀ n, dY n ≫ g n = g (n + 1) ≫ dZ n) :
    towerMap f hf ≫ towerMap g hg =
      towerMap (fun n ↦ f n ≫ g n) (fun n ↦ by
        rw [← Category.assoc, hf n, Category.assoc, hg n, ← Category.assoc])

def towerMatchingMap {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    X (n + 1) ⟶ pullback (dY n) (f n)
```

`TowerMatchingLifting`：

```lean
lemma towerRelative_liftFamily {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    {T U : SSet.{u}} (j : T ⟶ U) [HasLiftingProperty j (f 0)]
    [∀ n, HasLiftingProperty j (towerMatchingMap f hf n)]
    (a : T ⟶ FibrationTower.limit X dX) (b : U ⟶ FibrationTower.limit Y dY)
    (h : a ≫ towerMap f hf = j ≫ b) :
    ∃ l : ∀ n, U ⟶ X n,
      (∀ n, j ≫ l n = a ≫ FibrationTower.projection X dX n) ∧
      (∀ n, l n ≫ f n = b ≫ FibrationTower.projection Y dY n) ∧
      (∀ n, l (n + 1) ≫ dX n = l n)

lemma towerMap_hasLiftingProperty {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    {T U : SSet.{u}} (j : T ⟶ U) [HasLiftingProperty j (f 0)]
    [∀ n, HasLiftingProperty j (towerMatchingMap f hf n)] :
    HasLiftingProperty j (towerMap f hf)

lemma towerMap_rlp {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (W : MorphismProperty SSet.{u})
    (h0 : W.rlp (f 0)) (hm : ∀ n, W.rlp (towerMatchingMap f hf n)) : W.rlp (towerMap f hf)

lemma towerMap_fibration {X Y : ℕ → SSet.{u}} {dX : ∀ n, X (n + 1) ⟶ X n}
    {dY : ∀ n, Y (n + 1) ⟶ Y n} (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [Fibration (f 0)] [∀ n, Fibration (towerMatchingMap f hf n)] :
    Fibration (towerMap f hf)

lemma towerMap_piIsomorphism_of_matching_rlp {X Y : ℕ → SSet.{u}}
    {dX : ∀ n, X (n + 1) ⟶ X n} {dY : ∀ n, Y (n + 1) ⟶ Y n}
    [KanComplex (FibrationTower.limit X dX)] [KanComplex (FibrationTower.limit Y dY)]
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    (h0 : (MorphismProperty.monomorphisms SSet.{u}).rlp (f 0))
    (hm : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (towerMatchingMap f hf n)) :
    KanPiIsomorphism (towerMap f hf)
```

`RelativePointedHomLifting`：

```lean
lemma relativePointedHom_lift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) (p : E ⟶ B)
    {T U : SSet.{u}} (j : T ⟶ U)
    (hpp : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (curriedTensor SSet.{u}) i.right j).ι p.right)
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c

lemma relativePointedHom_anodyneLift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) (hi : anodyneExtensions i.right) (p : E ⟶ B) [Fibration p.right]
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c
```

次に mapping path による塔の比較の因子分解を構成し、段ごとの π_* 同型と塔の fibration 性から
初段と相対比較の全単射 RLP を証明する必要がある。
Sp の塔の実際の対象の Ω 条件・構造射の単射性・錐とその ∞ 極限性は未完了。
今回の相対 RLP の条件付き判定だけを塔の工程の完成とは数えない。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4638 jobs）、公開1241宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルと変更した相対充填ファイルの警告・sorry・追加公理はない。
他担当の依存838ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-tower-relative-lifting-aggregate.log` と
`/tmp/gamma3-tower-relative-lifting-audit.log`。


### γ3c：mapping path の塔の因子分解と源側の全ての単射への RLP

`MappingPathNaturality` は任意の点つき射の可換正方形について、
自由 path の端点評価と定数 path の自然性を、閉構造の pre と単位の自然同型から証明した。
`mappingPathMap f f' a b h` は path の後合成と元の源の射を引き戻しに貼り合わせた射。
path 成分、源射影、標的の終点射、定数 path の比較射の四つとの厳密な可換式を得た。
ここには Kan 性や fibration 性の仮定はない。

`MappingPathTowers` はこれを隣接する段の正方形に適用し、
`mappingPathTowerStep` を遷移とする実際の中間の塔を構成した。
源・標的への射影と定数 path の比較を L9 の整合族の極限へ束ね、
`mappingPathTowerLimitSource`、`mappingPathTowerLimitTarget`、`mappingPathTowerLimitUnit` を与える。
Unit と Source の合成が元の源の極限の恒等射であること、Unit と Target の合成が
元の `towerMap` に等しいことを、全ての段の射影の後で証明した。
極限の射としての等式を保持し、ホモトピー可換な因子分解に止めていない。

`RelativeFreePathLifting` の `relativeFreePath_lift` は、p が Kan fibration であるとき、
自由 path の単射パラメータ上の族を、指定した端点の値と底の path を保って拡張する。
端点の包含の anodyne 性を前回の点つき Hom の相対充填へ渡し、
単位からの内部 Hom の同型で端点を表示した。端点は零・一のどちらも選べる。

`MappingPathSourceLifting` の `mappingPathSourceMatchingMap` は、
mapping path の源射影について、次の源成分と前段の mapping path 成分を同時指定する
基礎単体集合の引き戻しへの実際の比較射。
`mappingPathSourceMatchingMap_rlp` は、標的側の縦射 b が Kan fibration なら、
この相対比較が全ての単射への RLP を持つことを証明する。
指定端点を保つ自由 path の相対充填を使い、二つの引き戻しの普遍性で対角射を構成した。
源側の縦射 a の fibration 性と横射 f の π_* 同型性は、この RLP の証明には不要。

`mappingPathTowerLimitSource_rlp` は、標的の各段が Kan で、標的の全遷移が fibration のとき、
中間の塔の極限から源の塔の極限への射が全ての単射への RLP を持つことを与える。
初段は既存の mapping path の源射影の RLP、次段は上の相対比較の RLP を使う。
さらに両方の縦射が fibration なら `mappingPathMap_fibration` により中間の遷移も fibration。
両方の各段が Kan なら `mappingPathTowerLimit_kanComplex` により中間の極限は Kan となる。

これらを合わせ、両方の塔が各段で Kan・全遷移が fibration のとき、
`mappingPathTowerLimitSource_piIsomorphism` と `mappingPathTowerLimitUnit_piIsomorphism` は
源側の極限の射と定数 path の比較射の全基点・全自然数次数の π_* 同型性を与える。
元の各段の射 f の π_* 同型性にはまだ依存しない。
元の f が各段で π_* 同型である場合の標的側の相対比較と Target の極限の射の RLP は未証明。
原典上の位置は Goerss–Jardine I §7、HTT A.3.3、BF 1978 §2、HTT 4.2.4.1。

新規24宣言の正確な型・全前提は以下。namespace は
`SerrePositivity.InfinityCategories.HomotopyLimits`、宇宙は u。
最後の二つの π_* 比較の型では、中間の極限の Kan 性を上の公開補題から局所 instance として使う。
公理依存の正本は `scripts/audit_homotopy_limits.lean`。

`MappingPathNaturality`：

```lean
lemma freePathEndpoint_naturality {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) (k : Fin 2) :
    PointedObject.basedHomMap freeInterval.{u} f ≫ freePathEndpoint Z k =
      freePathEndpoint Y k ≫ f

lemma freeConstantPath_naturality {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) :
    freeConstantPath Y ≫ PointedObject.basedHomMap freeInterval.{u} f =
      f ≫ freeConstantPath Z

def mappingPathMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') : mappingPath f ⟶ mappingPath f'

lemma mappingPathMap_path {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ pullback.fst (freePathEndpoint Y' 1) f' =
      pullback.fst (freePathEndpoint Y 1) f ≫ PointedObject.basedHomMap freeInterval.{u} b

lemma mappingPathMap_source {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ mappingPathRetraction f' = mappingPathRetraction f ≫ a

lemma mappingPathMap_target {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ mappingPathProjection f' = mappingPathProjection f ≫ b

lemma mappingPathMap_unit {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathUnit f ≫ mappingPathMap f f' a b h = a ≫ mappingPathUnit f'
```

`MappingPathTowers`：

```lean
def mappingPathTowerStep
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) : mappingPath (f (n + 1)) ⟶ mappingPath (f n)

lemma mappingPathTower_source_comm
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    mappingPathTowerStep X Y dX dY f hf n ≫ mappingPathRetraction (f n) =
      mappingPathRetraction (f (n + 1)) ≫ dX n

lemma mappingPathTower_target_comm
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    mappingPathTowerStep X Y dX dY f hf n ≫ mappingPathProjection (f n) =
      mappingPathProjection (f (n + 1)) ≫ dY n

lemma mappingPathTower_unit_comm
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) (n : ℕ) :
    dX n ≫ mappingPathUnit (f n) =
      mappingPathUnit (f (n + 1)) ≫ mappingPathTowerStep X Y dX dY f hf n

def mappingPathTowerLimitSource
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    FibrationTower.limit (fun n ↦ (mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right) ⟶
      FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right)

def mappingPathTowerLimitTarget
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    FibrationTower.limit (fun n ↦ (mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right) ⟶
      FibrationTower.limit (fun n ↦ (Y n).right) (fun n ↦ (dY n).right)

def mappingPathTowerLimitUnit
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right) ⟶
      FibrationTower.limit (fun n ↦ (mappingPath (f n)).right)
        (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right)

lemma mappingPathTowerLimitUnit_source
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    mappingPathTowerLimitUnit X Y dX dY f hf ≫ mappingPathTowerLimitSource X Y dX dY f hf =
      𝟙 (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (dX n).right))

lemma mappingPathTowerLimitUnit_target
    (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n) :
    mappingPathTowerLimitUnit X Y dX dY f hf ≫ mappingPathTowerLimitTarget X Y dX dY f hf =
      towerMap (fun n ↦ (f n).right) (by
        intro n
        simpa only [Under.comp_right] using congrArg Under.Hom.right (hf n))
```

`RelativeFreePathLifting`：

```lean
lemma relativeFreePath_lift {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) [Fibration p.right] (k : Fin 2)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (freePathSpace Y).right) (b : U ⟶ Y.right)
    (c : U ⟶ (freePathSpace Z).right)
    (hc : j ≫ b = a ≫ (freePathEndpoint Y k).right)
    (he : a ≫ (PointedObject.basedHomMap freeInterval.{u} p).right = j ≫ c)
    (ha : b ≫ p.right = c ≫ (freePathEndpoint Z k).right) :
    ∃ l : U ⟶ (freePathSpace Y).right, j ≫ l = a ∧
      l ≫ (freePathEndpoint Y k).right = b ∧
      l ≫ (PointedObject.basedHomMap freeInterval.{u} p).right = c
```

`MappingPathSourceLifting`：

```lean
def mappingPathSourceMatchingMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    (mappingPath f).right ⟶ pullback a.right (mappingPathRetraction f').right

lemma mappingPathSourceMatchingMap_rlp {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration b.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathSourceMatchingMap f f' a b h)

lemma mappingPathTowerLimitSource_rlp (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (Y n).right] [∀ n, Fibration (dY n).right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathTowerLimitSource X Y dX dY f hf)

lemma mappingPathMap_fibration {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right] :
    Fibration (mappingPathMap f f' a b h).right

lemma mappingPathTowerLimit_kanComplex (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    KanComplex (FibrationTower.limit (fun n ↦ (mappingPath (f n)).right)
      (fun n ↦ (mappingPathTowerStep X Y dX dY f hf n).right))

lemma mappingPathTowerLimitSource_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    KanPiIsomorphism (mappingPathTowerLimitSource X Y dX dY f hf)

lemma mappingPathTowerLimitUnit_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right] :
    KanPiIsomorphism (mappingPathTowerLimitUnit X Y dX dY f hf)
```

残る工程は、標的側の相対比較の fibration 性と、元の各段の π_* 同型性からの全ての単射への RLP、
Target の極限の射の比較、および元の塔の極限の射の π_* 同型性を導くこと。
その後、Sp の塔の対象の構造射の単射性・Ω 条件と実際の錐の ∞ 極限性を検証する。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 全体は継続中。

検証：対象集約 `HomotopyLimits` のビルド成功（4648 jobs）、公開1265宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルの警告・sorry・追加公理はない。
他担当の依存844ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-mapping-path-tower-source-aggregate.log` と
`/tmp/gamma3-mapping-path-tower-source-audit.log`。


### γ3c：mapping path の標的側の相対比較と塔の極限の π_* 同型

`RelativeFreePathBoundary` の `relativeFreePath_boundaryHornLift` は、自由 path の
両端点・底への合成・既存のホーン上の族を同時に保つ充填を構成する。
前提は底の点つき射の fibration 性とパラメータがホーンであることだけであり、
対象の Kan 性は要求しない。境界の Hom の積表示と相対 Hom 充填を用いる。

`MappingPathTargetLifting` で、可換正方形の両縦射が fibration なら
`mappingPathTargetMatchingMap` も fibration となることを証明した。
さらに四対象が Kan で両横射が全基点 π_* 同型なら、この相対比較は全ての単射への RLP を持つ。
前段の標的射影の RLP を引き戻し、次段の標的射影と二対三で比較し、
源の基点を明示して相対 Whitehead を適用する。

`TowerPiComparison` では、この相対比較の RLP を実際の極限の射
`mappingPathTowerLimitTarget` へ移した。前回の定数 path の比較と合成して、
`pointedTowerMap_piIsomorphism` を得た。正確な前提は、両塔の全段が点つき Kan 複体、
全遷移が fibration、比較が厳密可換で、各段の比較が全基点・全自然数次数の π_* 同型であること。
結論も実際の `FibrationTower.limit` 間の射の全基点・全次数の π_* 同型である。
比較射自身の fibration 性や matching map の RLP を追加の前提には置かない。

この定理は Sp の塔の Ω 条件を検証するための入力であり、
Sp の塔の実際の対象・構造射の単射性・Ω 条件・∞ 極限錐への適用は引き続き未完了。
非反転の比較、余極限側、E2a 完了後の E2b 適用も未完了で、γ3 は継続中。
原典：Goerss–Jardine I §§7–8、BF 1978 §2、HTT A.3.3、HTT 4.2.4.1。

新規7公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`）：

```lean
lemma relativeFreePath_boundaryHornLift {Y Z : PointedSimplicialSet.{u}}
    (p : Y ⟶ Z) [Fibration p.right] {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ (freePathSpace Y).right) (b₀ b₁ : U ⟶ Y.right)
    (c : U ⟶ (freePathSpace Z).right)
    (hc₀ : j ≫ b₀ = a ≫ (freePathEndpoint Y 0).right)
    (hc₁ : j ≫ b₁ = a ≫ (freePathEndpoint Y 1).right)
    (he : a ≫ (PointedObject.basedHomMap freeInterval.{u} p).right = j ≫ c)
    (ha₀ : b₀ ≫ p.right = c ≫ (freePathEndpoint Z 0).right)
    (ha₁ : b₁ ≫ p.right = c ≫ (freePathEndpoint Z 1).right) :
    ∃ l : U ⟶ (freePathSpace Y).right,
      j ≫ l = a ∧ l ≫ (freePathEndpoint Y 0).right = b₀ ∧
        l ≫ (freePathEndpoint Y 1).right = b₁ ∧
          l ≫ (PointedObject.basedHomMap freeInterval.{u} p).right = c

def mappingPathTargetMatchingMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    (mappingPath f).right ⟶ pullback b.right (mappingPathProjection f').right

lemma mappingPathTargetMatchingMap_fibration {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right] :
    Fibration (mappingPathTargetMatchingMap f f' a b h)

lemma mappingPathTargetMatchingMap_rlp {X Y X' Y' : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] [KanComplex X'.right] [KanComplex Y'.right]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right]
    (hf : KanPiIsomorphism f.right) (hf' : KanPiIsomorphism f'.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathTargetMatchingMap f f' a b h)

lemma mappingPathTowerLimitTarget_rlp (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, KanPiIsomorphism (f n).right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathTowerLimitTarget X Y dX dY f hf)

lemma mappingPathTowerLimitTarget_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, KanPiIsomorphism (f n).right) :
    KanPiIsomorphism (mappingPathTowerLimitTarget X Y dX dY f hf)

lemma pointedTowerMap_piIsomorphism (X Y : ℕ → PointedSimplicialSet.{u})
    (dX : ∀ n, X (n + 1) ⟶ X n) (dY : ∀ n, Y (n + 1) ⟶ Y n)
    (f : ∀ n, X n ⟶ Y n) (hf : ∀ n, dX n ≫ f n = f (n + 1) ≫ dY n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (dX n).right] [∀ n, Fibration (dY n).right]
    (hπ : ∀ n, KanPiIsomorphism (f n).right) :
    KanPiIsomorphism (towerMap (fun n ↦ (f n).right)
      (fun n ↦ congrArg Under.Hom.right (hf n)))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4653 jobs）、公開1272宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-tower-pi-aggregate.log` と `/tmp/gamma3-tower-pi-audit.log`。


### γ3c：Sp の段ごとに fibration の塔の実際の ∞ 極限錐

`PointedTowers` は `FibrationTower.limit` の整合族の極限に基点を加え、射影・持ち上げ・
外延性と通常の極限錐 `pointedTowerCone_isLimit` を構成する。初段が Kan、遷移が fibration
なら点つき極限も Kan。`LoopTowers` は loop の右随伴性を用いて、極限の loop と loop の塔の
極限の厳密同型 `loopTowerIso` を構成し、各射影との可換式を証明する。

`SpectrumTowerSequence` は元の Kan 列の塔の段ごとの極限へ懸垂構造射を組み立てる。
随伴構造射と `loopTowerIso` の合成は各段の随伴構造射が誘導する実際の塔の極限の射に
厳密に一致する。`SpectrumTowerOmega` は前回の `pointedTowerMap_piIsomorphism` を適用し、
各元の列の Ω 条件から極限の列の全基点・全自然数次数の Ω 条件を証明した。

構造射の単射性には `SmashJointProjections` を使う。右因子の単体を識別する基点保存射の族は、
smash の単体も識別する。非基点の組と基点の具体的表示で基点へ潰れる場合も検査する。
`SpectrumTowerMonomorphisms` は元の全構造射が単射なら極限の構造射も単射であることを証明。
この単射性の証明自体には、遷移の fibration 性や Ω 条件を使わない。

`SpectrumTowers` の `spectrumTower X d` は、各段を置換せず、上の Kan 性・単射性・Ω 条件で
L9 の Ω スペクトルに束ねた実際の極限対象である。射影を通常の錐にまとめ、各スペクトル段で
点つき極限の普遍性を検証し、既存の全切断の族の定理で全ての実際の豊穣 Hom の極限性を得る。
隣接遷移の Hom の fibration 性には既存の `spectrumHomMap_fibration` を適用した。

主要定理 `spectrumTowerInfinityCone_isLimit` の前提は、
`X : ℕ → OmegaSpectrum`、`d : ∀ n, X (n+1) ⟶ X n` と
`[∀ n k, Fibration ((d n).app k).right]` のみ。
結論は `IsLimitCone (spectrumTowerInfinityCone X d)`。
添字は `AsSmall ℕᵒᵖ`、通常図式は `AsSmall.down ⋙ Functor.ofOpSequence d`、
錐の頂点は実際の `spectrumTower X d` である。
Hom の極限性や追加の比較同値・Ω 条件を前提に置かない。

これにより、γ3c で指定された 𝒮 と Sp の有限積・一脚 fibration の引き戻し・fibration の塔は、
いずれも実際の対象と錐について ∞ 極限錐であることが揃った。
γ3 全体は継続中。非反転の元の比較射の導来 fiber と反転比較との直接の橋渡し、
余極限側、E2a 完了後の E2b 適用は引き続き未完了。
原典：Goerss–Jardine I §§7–8、BF 1978 §2、HA §1.4.2、HTT A.3.3、HTT 4.2.4.1 の双対。

新規35公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`）：

```lean
def pointedTowerLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : PointedSimplicialSet.{u}

instance pointedTowerLimit_kanComplex (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n, Fibration (d n).right] [KanComplex (X 0).right] :
    KanComplex (pointedTowerLimit X d).right

def pointedTowerProjection (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) : pointedTowerLimit X d ⟶ X n

lemma pointedTowerProjection_comp (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) :
    pointedTowerProjection X d (n + 1) ≫ d n = pointedTowerProjection X d n

def pointedTowerLift {A : PointedSimplicialSet.{u}} (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (f : ∀ n, A ⟶ X n)
    (hf : ∀ n, f (n + 1) ≫ d n = f n) : A ⟶ pointedTowerLimit X d

lemma pointedTowerLift_projection {A : PointedSimplicialSet.{u}}
    (X : ℕ → PointedSimplicialSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    (f : ∀ n, A ⟶ X n) (hf : ∀ n, f (n + 1) ≫ d n = f n) (n : ℕ) :
    pointedTowerLift X d f hf ≫ pointedTowerProjection X d n = f n

lemma pointedTowerLimit_hom_ext {A : PointedSimplicialSet.{u}}
    (X : ℕ → PointedSimplicialSet.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    {f g : A ⟶ pointedTowerLimit X d}
    (h : ∀ n, f ≫ pointedTowerProjection X d n = g ≫ pointedTowerProjection X d n) : f = g

def pointedTowerCone (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : Cone (Functor.ofOpSequence d)

def pointedTowerCone_isLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : IsLimit (pointedTowerCone X d)

def loopTowerCone (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) :
    Cone (Functor.ofOpSequence d ⋙
      PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})

def loopTowerCone_isLimit (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) : IsLimit (loopTowerCone X d)

def loopTowerIso (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) :
    loopSpace (pointedTowerLimit X d) ≅
      pointedTowerLimit (fun n ↦ loopSpace (X n))
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (d n))

lemma loopTowerIso_hom_projection (X : ℕ → PointedSimplicialSet.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) (n : ℕ) :
    (loopTowerIso X d).hom ≫ pointedTowerProjection _ _ n =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedTowerProjection X d n)

def towerSequenceSigma (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    suspension (pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k)) ⟶
      pointedTowerLimit (fun n ↦ ((X n).level (k + 1)).space) (fun n ↦ (d n).app (k + 1))

def towerKanSequence (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right] : KanSequence.{u}

def towerKanSequenceProjection (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) :
    KanSequence.Hom (towerKanSequence X d) (X n)

def towerSequenceAdjointMap (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    pointedTowerLimit (fun n ↦ ((X n).level k).space) (fun n ↦ (d n).app k) ⟶
      pointedTowerLimit (fun n ↦ loopSpace ((X n).level (k + 1)).space)
        (fun n ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u} ((d n).app (k + 1)))

lemma towerSequenceSigma_adjoint (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n)) (k : ℕ) :
    suspensionLoopEquiv _ _ (towerSequenceSigma X d k) ≫
        (loopTowerIso (fun n ↦ ((X n).level (k + 1)).space)
          (fun n ↦ (d n).app (k + 1))).hom = towerSequenceAdjointMap X d k

lemma towerSequenceAdjointMap_piIsomorphism (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right]
    (hX : ∀ n, (X n).OmegaCondition) (k : ℕ) :
    KanPiIsomorphism (towerSequenceAdjointMap X d k).right

lemma towerKanSequence_omega (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    [∀ n k, Fibration ((d n).app k).right]
    (hX : ∀ n, (X n).OmegaCondition) : (towerKanSequence X d).OmegaCondition

lemma smashSimplexPack_eq_of_family {A B : Type u} {J : Type v} {C : J → Type u}
    (a₀ : A) (b₀ : B) (c₀ : ∀ i, C i) (f : ∀ i, B → C i)
    (hf : ∀ i, f i b₀ = c₀ i) (hinj : Function.Injective (fun b ↦ fun i ↦ f i b))
    (a a' : A) (b b' : B)
    (h : ∀ i, smashSimplexPack a₀ (c₀ i) a (f i b) =
      smashSimplexPack a₀ (c₀ i) a' (f i b')) :
    smashSimplexPack a₀ b₀ a b = smashSimplexPack a₀ b₀ a' b'

lemma smashMap_jointlyInjective {J : Type v} (A B : PointedSimplicialSet.{u})
    (C : J → PointedSimplicialSet.{u}) (f : ∀ i, B ⟶ C i) (m : SimplexCategoryᵒᵖ)
    (hf : Function.Injective (fun b ↦ fun i ↦ (f i).right.app m b))
    (s t : (PointedObject.smash A B).right.obj m)
    (h : ∀ i, (PointedObject.smashMap (𝟙 A) (f i)).right.app m s =
      (PointedObject.smashMap (𝟙 A) (f i)).right.app m t) : s = t

lemma towerSequenceSigma_app_injective (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    (hmono : ∀ n k, Mono ((X n).sigma k).right) (k : ℕ) (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((towerSequenceSigma X d k).right.app m)

lemma towerSequenceSigma_mono (X : ℕ → KanSequence.{u})
    (d : ∀ n, KanSequence.Hom (X (n + 1)) (X n))
    (hmono : ∀ n k, Mono ((X n).sigma k).right) (k : ℕ) :
    Mono (towerSequenceSigma X d k).right

def spectrumTower (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : OmegaSpectrum.{u}

def spectrumTowerProjection (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) : spectrumTower X d ⟶ X n

lemma spectrumTowerProjection_comp (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] (n : ℕ) :
    spectrumTowerProjection X d (n + 1) ≫ d n = spectrumTowerProjection X d n

def spectrumTowerOrdinaryCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : Cone (Functor.ofOpSequence d)

def spectrumTowerOrdinaryCone_level_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (k : ℕ) :
    IsLimit ((spectrumLevelFunctor k).mapCone (spectrumTowerOrdinaryCone X d))

def spectrumTowerDiagram (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n) :
    AsSmall.{u} ℕᵒᵖ ⥤ OmegaSpectrum.{u}

def spectrumTowerCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : Cone (spectrumTowerDiagram X d)

def spectrumTowerCone_level_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (k : ℕ) :
    IsLimit (spectrumLevelCone (spectrumTowerCone X d) k)

def spectrumTowerCone_hom_isLimit (X : ℕ → OmegaSpectrum.{u})
    (d : ∀ n, X (n + 1) ⟶ X n) [∀ n k, Fibration ((d n).app k).right] (Z : OmegaSpectrum.{u}) :
    IsLimit (simplicialHomCone (spectrumTowerCone X d) Z)

def spectrumTowerInfinityCone (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] :
    JoinCone (strictCoherentDiagram (spectrumTowerDiagram X d))

lemma spectrumTowerInfinityCone_isLimit (X : ℕ → OmegaSpectrum.{u}) (d : ∀ n, X (n + 1) ⟶ X n)
    [∀ n k, Fibration ((d n).app k).right] : IsLimitCone (spectrumTowerInfinityCone X d)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4660 jobs）、公開1307宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規7ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-spectrum-towers-aggregate.log` と `/tmp/gamma3-spectrum-towers-audit.log`。


### γ3b：元の q_x と反転比較 q′ の同値判定、および元の比較からの極限性

`ReflectedConeLimitLift` で Kan 複体間のホモトピー同値性が反転で検出されることと、
任意の錐の厳密極限への射が反転の極限保存同型と可換であることを証明した。
錐の厳密極限性は要求しない。二重反転の自然同型で元の射へ戻す。

`ConeComparisonReflection` は任意の錐の比較を
`bousfieldKanConeComparison c = limit.lift H c ≫ bousfieldKanLimitComparison H`
と厳密に分解する。元と反転後の標準比較 κ の同値性を消去し、両極限への射を比較する。
離散 Kan 図式、一脚 fibration の Kan cospan、Kan fibration の塔について、
必要な κ の同値性と厳密極限の Kan 性を検証して、比較の同値性の一致を得た。
反転した end と元の end を同一視することはなく、中間の厳密極限の保存同型を使う。

`RepresentableReflection` の三つの `representableComparison_reflection_*_iff` は、
局所 Kan な単体的圏の実際の Hom 錐にこの判定を適用し、元の
`representableHomotopyLimitComparison c x` が同値であることと、
`reflectedRepresentableComparison c x` が同値であることの同値を証明した。
cospan には Hom の左脚の fibration 性、塔には全隣接遷移の Hom の fibration 性を要求する。
Hom 錐そのものが厳密極限であることは、三形状のいずれの定理にも要求しない。

`RepresentableLimitCriterion` の三つの
`strictCoherentCone_isLimit_of_*_representableComparison` は、元の q_x の同値性を全 x で
仮定して `IsLimitCone (strictCoherentCone c)` を導く共有定理である。
反転比較を ULift し、反転 end から実際の coherent 錐の切断模型への比較と合成して、
既存の native な極限判定へ渡す。局所 Kan 性と形状に応じた Hom の fibration 性は明示する。

これは三形状で元の q_x を入力とする十分条件を証明したもの。
元の q_x の同値性と native な極限性の逆向き、元の比較射の導来 fiber と錐の pinched Hom
との直接比較、一般形状の元と反転 end の直接比較は、引き続き未完了。
余極限側と E2a 完了後の E2b 適用も未完了で、γ3 は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 7.5.3.12・7.5.4.6、2.4.5、4.6.7。

新規15公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`、節変数を展開）：

```lean
lemma oppositeKanHomotopyEquivalence_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence (SSet.opFunctor.map f) ↔
      IsSimplicialHomotopyEquivalence f

lemma reflectedConeLimitLift {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}
    (c : Cone H) :
    SSet.opFunctor.map (limit.lift H c) ≫ (preservesLimitIso SSet.opFunctor H).hom =
      limit.lift (H ⋙ SSet.opFunctor) (SSet.opFunctor.mapCone c)

lemma reflectedConeLimitLift_homotopyEquivalence_iff
    {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [KanComplex (limit H)] :
    IsSimplicialHomotopyEquivalence
      (limit.lift (H ⋙ SSet.opFunctor) (SSet.opFunctor.mapCone c)) ↔
      IsSimplicialHomotopyEquivalence (limit.lift H c)

lemma bousfieldKanConeComparison_limitLift {I : Type u} [SmallCategory I]
    {H : I ⥤ SSet.{u}} (c : Cone H) :
    bousfieldKanConeComparison c = limit.lift H c ≫ bousfieldKanLimitComparison H

lemma strictLimit_kanComplex_of_terminalWeight {I : Type u} [SmallCategory I]
    (W H : I ⥤ SSet.{u}) (hW : IsTerminal W) [KanComplex (weightedSections W H)] :
    KanComplex (limit H)

lemma bousfieldKanConeComparison_reflection_iff
    {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] [KanComplex (limit H)]
    (hκ : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H))
    (hκ' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison (H ⋙ SSet.opFunctor))) :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) ↔
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison (SSet.opFunctor.mapCone c))

lemma bousfieldKanConeComparison_reflection_discrete_iff {J : Type u}
    {H : Discrete J ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) ↔
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison (SSet.opFunctor.mapCone c))

lemma bousfieldKanConeComparison_reflection_cospan_iff
    {H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) ↔
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison (SSet.opFunctor.mapCone c))

lemma bousfieldKanConeComparison_reflection_tower_iff
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) ↔
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison (SSet.opFunctor.mapCone c))

lemma representableComparison_reflection_discrete_iff {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) ↔
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)

lemma representableComparison_reflection_cospan_iff {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F) (x : C)
    [Fibration ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) ↔
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)

lemma representableComparison_reflection_tower_iff {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F) (x : C)
    [∀ n : ℕ, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) ↔
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)

lemma strictCoherentCone_isLimit_of_discrete_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F)
    (hc : ∀ x : C, IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)) :
    IsLimitCone (strictCoherentCone c)

lemma strictCoherentCone_isLimit_of_cospan_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (hc : ∀ x : C, IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)) :
    IsLimitCone (strictCoherentCone c)

lemma strictCoherentCone_isLimit_of_tower_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (hc : ∀ x : C, IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)) :
    IsLimitCone (strictCoherentCone c)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4664 jobs）、公開1322宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-limit-criterion-aggregate.log` と
`/tmp/gamma3-representable-limit-criterion-audit.log`。


### γ3b：元の q_x の同値性と native な ∞ 極限性の両向きの判定

`UniverseHomotopyReflection` は、持ち上げた二射の実際の単体的ホモトピーを元の宇宙へ戻す
`uliftHomotopyDown` と、持ち上げた射のホモトピー逆を充満性で戻す
`homotopyEquivalence_of_ulift` を構成した。これにより
`ulift_homotopyEquivalence_iff` で、宇宙の持ち上げの前後のホモトピー同値性が同値となる。
この宇宙の移送自体には、元・持ち上げ後のいずれの単体集合にも Kan 性を要求しない。

`RepresentableLimitEquivalence` は、反転 end からの切断比較の後合成を消去し、
ULift の同値検出で反転比較 q′ の同値性へ戻す中間判定を構成した。
一般の添字圏では、反転 end から切断空間への比較の同値性を明示した前提に置く。
三形状では、この前提を既存の実際の比較定理で検証した。

主要定理は `strictCoherentCone_isLimit_iff_discrete_representableComparison`、
`strictCoherentCone_isLimit_iff_cospan_representableComparison`、
`strictCoherentCone_isLimit_iff_tower_representableComparison`。
結論はそれぞれ
`IsLimitCone (strictCoherentCone c) ↔ ∀ x, IsSimplicialHomotopyEquivalence
  (representableHomotopyLimitComparison c x)`。
離散図式では局所 Kan 性のみで、添字の有限性・非空性は要求しない。
cospan では全 x で Hom の左脚が fibration、塔では全 x・全隣接遷移で Hom が fibration
であることを追加する。Hom 錐の厳密極限性、元の q_x の fibration 性、追加の比較同値は
三つの主要定理の前提に置かない。

これで指定三形状について、前回の十分条件の逆向きも証明された。
元の q_x の導来 fiber と錐の pinched Hom の直接比較、および可縮性による判定への
元の q_x を使った直接の接続は引き続き未完了。一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用も未完了で、γ3 全体は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 7.5.3.12・7.5.4.6、2.4.5、4.6.7。

新規7公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`、節変数を展開）：

```lean
def uliftHomotopyDown {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g)) : SSet.Homotopy f g

lemma homotopyEquivalence_of_ulift {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f)) :
    IsSimplicialHomotopyEquivalence f

lemma ulift_homotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) ↔
      IsSimplicialHomotopyEquivalence f

lemma reflectedStrictConeSectionsComparison_homotopyEquivalence_iff {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {F : I ⥤ C}
    (c : Cone F) (x : C)
    (hE : IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x)) :
    IsSimplicialHomotopyEquivalence (reflectedStrictConeSectionsComparison c x) ↔
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)

lemma strictCoherentCone_isLimit_iff_discrete_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)

lemma strictCoherentCone_isLimit_iff_cospan_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)

lemma strictCoherentCone_isLimit_iff_tower_representableComparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4666 jobs）、公開1329宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-limit-equivalence-aggregate.log` と
`/tmp/gamma3-representable-limit-equivalence-audit.log`。


### γ3b：元の q_x の全導来 fiber の可縮性による三形状の両向きの極限判定

`IntervalHomBoundary` は、二つの単位の余積からの内部 Hom の積表示を構成し、
単射な二端点包含への制限が fibration であることから、通常の区間の両端点の同時評価
`intervalHomEndpoints` の Kan fibration 性を証明した。
第一成分は終点一、第二成分は始点零。既存の可逆 path の包含の同型を利用している。

`KanComparisonFibers` の `kanEquivalencePathReplacementMap_fibration` は、
Kan 複体間の任意の射 q の可逆 path 置換の終点射が Kan fibration であることを証明する。
元の始域のホーンを先に充填し、標的の両端点を同時指定して path を充填する。
元の q の fibration 性は不要。既存の `comparisonFiber q b` はその終点射の頂点 fiber
そのものであり、任意の q と b について Kan 性を得た。

`homotopyEquivalence_iff_comparisonFiber_isContractibleKan` は、Kan 複体間の任意の射で
`IsSimplicialHomotopyEquivalence q ↔ ∀ b, IsContractibleKan (comparisonFiber q b)` を証明。
逆向きは path 置換の終点射を右ファイブレーションとして扱い、全頂点 fiber の可縮性から
trivial Kan fibration 性を得て、その同値性を元の射へ戻す。空の始域・標的も除外しない。

`RepresentableFiberCriterion` は任意の通常の小圏について、元の q_x の同値性をその
全導来 fiber の可縮性と同値にした。指定三形状では前回の実際の錐の極限判定と接続し、
`strictCoherentCone_isLimit_iff_discrete_comparisonFiber`、
`strictCoherentCone_isLimit_iff_cospan_comparisonFiber`、
`strictCoherentCone_isLimit_iff_tower_comparisonFiber` を公開した。

三定理の結論は
`IsLimitCone (strictCoherentCone c) ↔ ∀ x b,
  IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)`。
b は元の `bousfieldKanHolim (simplicialHomDiagram F x)` の全頂点を走る。
局所 Kan 性に加え、cospan では Hom の左脚の fibration 性、塔では Hom の全隣接遷移の
fibration 性を要求する。離散図式には添字の有限性・非空性を要求しない。
元の q_x の fibration 性、Hom 錐の厳密極限性、追加の比較同値は三定理の前提に置かない。

これにより γ3b の指定三形状について、A3d に基づく native な極限性を元の q_x の導来 fiber
の可縮性へ両向きに帰着できた。ただし、錐の pinched Hom と元の導来 fiber の実際の比較射を
直接構成したわけではない。この直接比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了で、γ3 全体は継続中。
原典：HTT 4.2.4.1 の限定形、Kerodon 4.5.3.24・7.5.3.12・7.5.4.6、Goerss–Jardine I §7。

新規17公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`、節変数を展開）：

```lean
lemma homPre_const_unitIsoSelf {K Y : SSet.{u}} (v : K _⦋0⦌) :
    (MonoidalClosed.pre (SSet.const (X

def intervalHomBoundaryIsLimit (Y : SSet.{u}) :
    IsLimit (BinaryFan.mk
      ((MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y)
      ((MonoidalClosed.pre (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y))

def intervalHomBoundaryEvaluationIsLimit (Y : SSet.{u}) :
    IsLimit (BinaryFan.mk
      ((MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X

def intervalHomBoundaryEvaluationIso (Y : SSet.{u}) :
    (ihom ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).obj Y ≅ Y ⨯ Y

lemma intervalHomBoundaryEvaluationIso_hom_fst (Y : SSet.{u}) :
    (intervalHomBoundaryEvaluationIso Y).hom ≫ prod.fst =
      (MonoidalClosed.pre (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X

lemma intervalHomBoundaryEvaluationIso_hom_snd (Y : SSet.{u}) :
    (intervalHomBoundaryEvaluationIso Y).hom ≫ prod.snd =
      (MonoidalClosed.pre (coprod.inr : 𝟙_ SSet.{u} ⟶ (𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u}))).app Y ≫
        (unitIsoSelf (X

def intervalHomEndpoints (Y : SSet.{u}) : (ihom (Δ[1] : SSet.{u})).obj Y ⟶ Y ⨯ Y

instance intervalHomEndpoints_fibration (Y : SSet.{u}) [KanComplex Y] :
    Fibration (intervalHomEndpoints Y)

lemma intervalHomEndpoints_fst (Y : SSet.{u}) :
    intervalHomEndpoints Y ≫ prod.fst = evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)

lemma intervalHomEndpoints_snd (Y : SSet.{u}) :
    intervalHomEndpoints Y ≫ prod.snd = evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)

instance kanEquivalencePathReplacementMap_fibration {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) :
    Fibration (equivalencePathReplacementMap q)

instance kanComparisonFiber_kanComplex {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) (b : B _⦋0⦌) :
    KanComplex (comparisonFiber q b)

lemma homotopyEquivalence_iff_comparisonFiber_isContractibleKan {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) :
    IsSimplicialHomotopyEquivalence q ↔ ∀ b : B _⦋0⦌,
      IsContractibleKan (comparisonFiber q b)

lemma representableComparison_iff_comparisonFiber_isContractibleKan {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) ↔
      ∀ b : (bousfieldKanHolim (simplicialHomDiagram F x)) _⦋0⦌,
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)

lemma strictCoherentCone_isLimit_iff_discrete_comparisonFiber {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] {J : Type u}
    {F : Discrete J ⥤ C} (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ (x : C)
      (b : (bousfieldKanHolim (simplicialHomDiagram F x)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)

lemma strictCoherentCone_isLimit_iff_cospan_comparisonFiber {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} WalkingCospan ⥤ C} (c : Cone F)
    [∀ x : C, Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    IsLimitCone (strictCoherentCone c) ↔ ∀ (x : C)
      (b : (bousfieldKanHolim (simplicialHomDiagram F x)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)

lemma strictCoherentCone_isLimit_iff_tower_comparisonFiber {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : AsSmall.{u} ℕᵒᵖ ⥤ C} (c : Cone F)
    [∀ (x : C) (n : ℕ), Fibration
      ((simplicialHomDiagram F x).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    IsLimitCone (strictCoherentCone c) ↔ ∀ (x : C)
      (b : (bousfieldKanHolim (simplicialHomDiagram F x)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4669 jobs）、公開1346宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-representable-fiber-criterion-aggregate.log` と
`/tmp/gamma3-representable-fiber-criterion-audit.log`。


### γ3b：同じ底上の源の比較が誘導する導来 fiber の実際の射と weighted な錐への適用

`ComparisonFiberSource` は、既存の `comparisonFiber p b` の path 成分と源成分を取り出し、
整合する二成分からの持ち上げと外延性を構成した。標的 B が Kan のとき、
`comparisonFiberSource p b : comparisonFiber p b ⟶ E` が Kan fibration であることを証明。
元の p の fibration 性も、E の Kan 性もこの射影の fibration 性には要求しない。
両端点を指定する区間の内部 Hom の充填を使い、源成分をそのまま保持する。

`ComparisonFiberFunctor` の `comparisonFiberMap p q f hf b` は、同じ底上の可換図式
`f ≫ q = p` が誘導する実際の射。path 成分と固定頂点 b を保持し、源成分にだけ f を適用する。
その源射影との可換正方形は厳密な引き戻しであり、Kan 性なしで普遍性を構成した。
E・D・B が Kan、f がホモトピー同値なら、この実際の fiber 比較射もホモトピー同値。
導来 fiber の源射影の fibration 性に、可逆 path の相対持ち上げを使う既存の同値の
引き戻し定理を適用した。元の p・q の fibration 性は要求しない。

`WeightedConeDerivedFiberComparison` は主可換式
`weightedStrictConeFamilyComparison c x ≫ coneSectionRestriction ... =
  reflectedStrictConeSectionsComparison c x`
へこの構成を適用する。
`weightedStrictConeFamilyFiberComparison c x b` は、反転・ULift 後の切断比較の導来 fiber から、
native な切断の制限の同じ頂点 b 上の導来 fiber への実際の射である。
源成分で weighted な錐全体の比較と厳密に可換であることを記録した。
局所 Kan 性の下で、この実際の射がホモトピー同値であることも証明した。
添字圏 I と通常の錐 c は任意であり、Hom の fibration 性や厳密極限性は要求しない。

この工程の fiber は `reflectedStrictConeSectionsComparison` の fiber である。
元の非反転 q_x の fiber との直接比較、および native な制限の導来 fiber と錐の pinched Hom
の直接比較をすべて閉じたわけではない。これらの残る比較 span、一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用は引き続き未完了で、γ3 は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

新規17公開宣言の正確な型・全前提（名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits`、節変数を展開）：

```lean
def comparisonFiberPath {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiber p b ⟶ equivalencePath B

def comparisonFiberSource {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiber p b ⟶ E

lemma comparisonFiberPath_source {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiberPath p b ≫ equivalencePathEndpoint B 0 = comparisonFiberSource p b ≫ p

lemma comparisonFiberPath_target {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiberPath p b ≫ equivalencePathEndpoint B 1 = SSet.const b

def comparisonFiberLift {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ equivalencePathEndpoint B 1 = SSet.const b) : T ⟶ comparisonFiber p b

lemma comparisonFiberLift_path {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ equivalencePathEndpoint B 1 = SSet.const b) :
    comparisonFiberLift p b a s h₀ h₁ ≫ comparisonFiberPath p b = a

lemma comparisonFiberLift_source {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ equivalencePathEndpoint B 1 = SSet.const b) :
    comparisonFiberLift p b a s h₀ h₁ ≫ comparisonFiberSource p b = s

lemma comparisonFiber_hom_ext {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {f g : T ⟶ comparisonFiber p b}
    (hp : f ≫ comparisonFiberPath p b = g ≫ comparisonFiberPath p b)
    (hs : f ≫ comparisonFiberSource p b = g ≫ comparisonFiberSource p b) : f = g

instance comparisonFiberSource_fibration {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) (b : B _⦋0⦌) : Fibration (comparisonFiberSource p b)

def comparisonFiberMap {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiber p b ⟶ comparisonFiber q b

lemma comparisonFiberMap_path {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiberMap p q f hf b ≫ comparisonFiberPath q b = comparisonFiberPath p b

lemma comparisonFiberMap_source {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    comparisonFiberMap p q f hf b ≫ comparisonFiberSource q b = comparisonFiberSource p b ≫ f

lemma comparisonFiberMap_isPullback {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (f : E ⟶ D) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    IsPullback (comparisonFiberMap p q f hf b) (comparisonFiberSource p b)
      (comparisonFiberSource q b) f

lemma comparisonFiberMap_homotopyEquivalence {E D B : SSet.{u}}
    [KanComplex E] [KanComplex D] [KanComplex B]
    (p : E ⟶ B) (q : D ⟶ B) (f : E ⟶ D) (hf : f ≫ q = p)
    (he : IsSimplicialHomotopyEquivalence f) (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (comparisonFiberMap p q f hf b)

noncomputable def weightedStrictConeFamilyFiberComparison {I : Type u} [SmallCategory I] {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C}
    (c : Cone F) (x : C)
    (b : (coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)) _⦋0⦌) :
    comparisonFiber (reflectedStrictConeSectionsComparison c x) b ⟶
      comparisonFiber (coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x)) b

lemma weightedStrictConeFamilyFiberComparison_source {I : Type u} [SmallCategory I] {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C}
    (c : Cone F) (x : C)
    (b : (coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)) _⦋0⦌) :
    weightedStrictConeFamilyFiberComparison c x b ≫
        comparisonFiberSource
          (coneSectionRestriction (strictCoherentCone c) (coherentNerveVertex x)) b =
      comparisonFiberSource (reflectedStrictConeSectionsComparison c x) b ≫
        weightedStrictConeFamilyComparison c x

lemma weightedStrictConeFamilyFiberComparison_homotopyEquivalence {I : Type u} [SmallCategory I] {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (x : C)
    (b : (coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (weightedStrictConeFamilyFiberComparison c x b)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4672 jobs）、公開1363宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
検証ログは `/tmp/gamma3-weighted-cone-derived-fiber-aggregate.log` と
`/tmp/gamma3-weighted-cone-derived-fiber-audit.log`。

### γ3b：標的の同値が誘導する実際の導来 fiber の比較


Kan 複体間の `p : E ⟶ B` と `g : B ⟶ D`、頂点 `b : B _⦋0⦌` に対して、
実際の射
`comparisonFiberPost p g b : comparisonFiber p b ⟶ comparisonFiber (p ≫ g) (g.app _ b)`
を構成した。可逆 path を g で後合成し、元の源成分を保持する。
`comparisonFiberPost_source` と `comparisonFiberPost_path` はこの二成分の厳密な等式。

`comparisonFiberPost_homotopyEquivalence` の前提は E・B・D の Kan 性と g の単体的
ホモトピー同値性であり、p の fibration 性や E・fiber の非空性は要求しない。
path 置換の全空間の比較は、元の源への二つの自明 Kan fibration との可換式から、
g の同値性なしでも同値となる。全空間と底が同値な Kan fibration の正方形から
各 fiber の実際の比較の同値性を得て、部分型の頂点 fiber の模型へ厳密な同型で戻した。

空の fiber を含めるため、全基点・全次数の `KanPiIsomorphism` だけで結論せず、
fiber の π₀ の全射性を別に証明する。全空間の π₀ の全射性、底の π₀ の単射性と
fibration の成分持ち上げからこれを得る。源に頂点がある場合は点つき Whitehead を使い、
頂点がない場合は π₀ の全射性から標的も全次数で空であることを確認する。

既存の同じ底上の源の比較 `comparisonFiberMap` と合わせ、導来 fiber の源と標的の
同値による実際の比較が使える。元の非反転 q_x と錐の pinched Hom の直接比較、
一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用は引き続き未完了。
この補助比較を γ3 全体の完成とは数えない。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、Goerss–Jardine I §§7–8。

公開21宣言の正確な型と前提（namespace `HomotopyLimits`）：

```lean
instance kanEquivalencePathReplacement_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) : KanComplex (equivalencePathReplacement f)

lemma kanPiIsomorphism_of_homotopyEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (he : IsSimplicialHomotopyEquivalence f) :
    KanPiIsomorphism f

lemma homotopyEquivalence_of_kanPiIsomorphism_of_vertex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (hf : KanPiIsomorphism f) (x : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence f

lemma homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (hf : KanPiIsomorphism f)
    (h₀ : Function.Surjective (mapπ₀ f)) : IsSimplicialHomotopyEquivalence f

lemma fibrationFiberMapBase_homotopyEquivalence {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : IsSimplicialHomotopyEquivalence f) (hg : IsSimplicialHomotopyEquivalence g)
    (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (fibrationFiberMapBase p p' f g comm b)

def vertexFiberKanFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiber p b ≅ KanFiber p b

lemma vertexFiberKanFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (vertexFiberKanFiberIso p b).hom ≫ fiberι p b = vertexFiberι p b

lemma vertexFiberKanFiberIso_inv_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (vertexFiberKanFiberIso p b).inv ≫ vertexFiberι p b = fiberι p b

def vertexFiberSquareMap {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    vertexFiber p b ⟶ vertexFiber p' (g.app _ b)

lemma vertexFiberSquareMap_ι {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (p' : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (comm : p ≫ g = f ≫ p') (b : B _⦋0⦌) :
    vertexFiberSquareMap p p' f g comm b ≫ vertexFiberι p' (g.app _ b) =
      vertexFiberι p b ≫ f

lemma vertexFiberSquareMap_homotopyEquivalence {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : IsSimplicialHomotopyEquivalence f) (hg : IsSimplicialHomotopyEquivalence g)
    (b : B _⦋0⦌) : IsSimplicialHomotopyEquivalence (vertexFiberSquareMap p p' f g comm b)

def comparisonPathReplacementPost {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    equivalencePathReplacement p ⟶ equivalencePathReplacement (p ≫ g)

lemma comparisonPathReplacementPost_path {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ pullback.fst (equivalencePathEndpoint D 0) (p ≫ g) =
      pullback.fst (equivalencePathEndpoint B 0) p ≫ equivalencePathMap g

lemma comparisonPathReplacementPost_source {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ equivalencePathReplacementProjection (p ≫ g) =
      equivalencePathReplacementProjection p

lemma comparisonPathReplacementPost_target {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ equivalencePathReplacementMap (p ≫ g) =
      equivalencePathReplacementMap p ≫ g

lemma comparisonPathReplacementPost_homotopyEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (g : B ⟶ D) :
    IsSimplicialHomotopyEquivalence (comparisonPathReplacementPost p g)

def comparisonFiberPost {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiber p b ⟶ comparisonFiber (p ≫ g) (g.app _ b)

lemma comparisonFiberPost_ι {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ vertexFiberι (equivalencePathReplacementMap (p ≫ g)) (g.app _ b) =
      vertexFiberι (equivalencePathReplacementMap p) b ≫ comparisonPathReplacementPost p g

lemma comparisonFiberPost_source {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ comparisonFiberSource (p ≫ g) (g.app _ b) =
      comparisonFiberSource p b

lemma comparisonFiberPost_path {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ comparisonFiberPath (p ≫ g) (g.app _ b) =
      comparisonFiberPath p b ≫ equivalencePathMap g

lemma comparisonFiberPost_homotopyEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (g : B ⟶ D)
    (hg : IsSimplicialHomotopyEquivalence g) (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (comparisonFiberPost p g b)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4677 jobs）、公開1384宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルの警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-comparison-fiber-post-aggregate.log`、
`/tmp/gamma3-comparison-fiber-post-audit.log`。

### γ3b：任意の coherent な錐の pinched Hom と選んだ切断比較の導来 fiber


`rightFibrationHomDerivedFiberMap r c x d` は、選んだ表現可能な比較
`rightFibrationHomComparison r c x` の導来 fiber から、比較 span の始点評価
`rightFibrationMappingEvaluation r c x` の同じ頂点 d 上の導来 fiber への実際の射である。
span の切断による源成分の作用と、底の可逆 path が保持されることを厳密な等式で記録した。
底 B が quasicategory なら、この実際の射はホモトピー同値である。
r 自体の Kan fibration 性、比較射の同値性、fiber の可縮性・非空性は要求しない。

既存の始点評価の fiber と全空間の pinched Hom の同値と合わせ、
`rightFibrationPinchedHomComparisonDerivedFiberEquivalence r c x d` を得た。
これは `pinchedHom d.val c` と選んだ比較の実際の導来 fiber の圏同値である。
E・B の quasicategory 性と r の right fibration 性を前提とする。

さらに錐の slice 射影へ適用し、頂点 fiber と切断空間の既存の同値で標的を移す。
`coneSectionDerivedFiberMap d c` はこの後合成による実際の fiber の射であり、
源成分を保持し、path は選んだ同値で後合成する。この射もホモトピー同値となる。
最終的に `conePinchedHom_sectionComparisonDerivedFiberEquivalence d c` は

```lean
QCatEquivalence (pinchedHom (X := sliceOver p) d c)
  (comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d))
```

を与える。K、p、d、c は任意で、X の quasicategory 性だけを要求する。
strict な通常の錐、極限錐、可縮な fiber に制限しない。
`coneSectionDerivedFiberPoint d` は d の頂点 fiber の点を
`coneVertexFiberSectionEquivalence p d.vertex` の順射で写した点である。
この同値の逆には選択があるため、標準の切断制限の点との厳密な一致は主張しない。

未完了は、選んだ比較と標準の切断制限の fiber の照合、元の非反転 q_x の fiber への
直接比較、一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用。
既存の三形状の可縮性判定と、この任意の錐の fiber 比較は区別して保持し、γ3 は継続中。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6。

公開12宣言の正確な型と前提（namespace `HomotopyLimits`）：

```lean
lemma rightFibrationMappingSection_homotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] (r : E ⟶ B) [RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (rightFibrationMappingSection r c x)

def rightFibrationHomDerivedFiberMap {E B : SSet.{u}} (r : E ⟶ B) [RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (vertexFiber r x) _⦋0⦌) :
    comparisonFiber (rightFibrationHomComparison r c x) d ⟶
      comparisonFiber (rightFibrationMappingEvaluation r c x) d

lemma rightFibrationHomDerivedFiberMap_source {E B : SSet.{u}}
    (r : E ⟶ B) [RightFibration r] (c : E _⦋0⦌) (x : B _⦋0⦌)
    (d : (vertexFiber r x) _⦋0⦌) :
    rightFibrationHomDerivedFiberMap r c x d ≫
        comparisonFiberSource (rightFibrationMappingEvaluation r c x) d =
      comparisonFiberSource (rightFibrationHomComparison r c x) d ≫
        rightFibrationMappingSection r c x

lemma rightFibrationHomDerivedFiberMap_path {E B : SSet.{u}}
    (r : E ⟶ B) [RightFibration r] (c : E _⦋0⦌) (x : B _⦋0⦌)
    (d : (vertexFiber r x) _⦋0⦌) :
    rightFibrationHomDerivedFiberMap r c x d ≫
        comparisonFiberPath (rightFibrationMappingEvaluation r c x) d =
      comparisonFiberPath (rightFibrationHomComparison r c x) d

lemma rightFibrationHomDerivedFiberMap_homotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] (r : E ⟶ B) [RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (vertexFiber r x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (rightFibrationHomDerivedFiberMap r c x d)

def rightFibrationPinchedHomComparisonDerivedFiberEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (r : E ⟶ B) [RightFibration r]
    (c : E _⦋0⦌) (x : B _⦋0⦌) (d : (vertexFiber r x) _⦋0⦌) :
    QCatEquivalence (pinchedHom d.val c)
      (comparisonFiber (rightFibrationHomComparison r c x) d)

def coneSectionDerivedFiberPoint {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d : JoinCone p) : (coherentConeSectionSpace p d.vertex) _⦋0⦌

def coneSectionDerivedFiberMap {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    comparisonFiber (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) ⟶
      comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d)

lemma coneSectionDerivedFiberMap_source {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    coneSectionDerivedFiberMap d c ≫ comparisonFiberSource (coneSectionHomComparison c d.vertex)
        (coneSectionDerivedFiberPoint d) =
      comparisonFiberSource (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d)

lemma coneSectionDerivedFiberMap_path {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    coneSectionDerivedFiberMap d c ≫ comparisonFiberPath (coneSectionHomComparison c d.vertex)
        (coneSectionDerivedFiberPoint d) =
      comparisonFiberPath (rightFibrationHomComparison (sliceOverProjection p) c d.vertex)
        (coneVertexFiberPoint d) ≫
          equivalencePathMap (coneVertexFiberSectionEquivalence p d.vertex).hom

lemma coneSectionDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (d c : JoinCone p) :
    IsSimplicialHomotopyEquivalence (coneSectionDerivedFiberMap d c)

def conePinchedHom_sectionComparisonDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSectionHomComparison c d.vertex) (coneSectionDerivedFiberPoint d))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4679 jobs）、公開1396宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-cone-section-derived-aggregate.log`、
`/tmp/gamma3-cone-section-derived-audit.log`。

### γ3b：標準の錐の点を保持する native な切断制限の導来 fiber と pinched Hom


`conePinchedHom_sectionRestrictionDerivedFiberEquivalence d c` を構成した。
X が quasicategory、`p : K ⟶ X`、`d c : JoinCone p` に対し、型は

```lean
QCatEquivalence (pinchedHom (X := sliceOver p) d c)
  (comparisonFiber (coneSectionRestriction c d.vertex) (coherentConeSectionPoint d))
```

である。K・p・d・c は任意。strict な通常の錐への制限、極限性、比較射の同値性、
fiber の可縮性や非空性は前提に要求しない。底の点は選んだ切断比較の像ではなく、
元の d を coslice へ curry した標準の `coherentConeSectionPoint d` そのもの。

証明の第一段では `coneMappingTotalIso c x` が始点評価と native な slice 制限を厳密に
対応させる式から、同じ底上の実際の fiber 射 `coneSliceDerivedFiberMap c x b` を作る。
これは源の厳密な同型から誘導される同値であり、元の点 b を変更しない。
その結果 `conePinchedHom_sliceRestrictionDerivedFiberEquivalence d c` を得る。

第二段では、slice・切断の標準比較を共通の `fixedEndpointConeSpace` へ移す。
図式の固定条件 c.property による移送を正規化した自然性を証明し、
`coneSliceEndpointComparison_restrict` と `coneSectionEndpointComparison_restrict` により、
両制限が同じ `coneEndpointRestriction c x` と厳密に可換であることを確認した。
それぞれから共通模型の導来 fiber への実際の射
`coneSliceEndpointDerivedFiberMap` と `coneSectionEndpointDerivedFiberMap` を構成し、
源と標的の標準比較の同値性から、両方がホモトピー同値であることを証明した。

最後に `coneEndpointComparison_point_eq d` で固定点を厳密に照合する。
標準の slice の点と標準の切断の点の共通模型での像は等しい。
零単体の普遍族を uncurry すると両方とも
`fst (join Δ[0] K) Δ[0] ≫ d.val` となるためである。
この照合自体には X の quasicategory 性や同値の逆の選択は不要。
共通模型上で同じ底の点を持つ二つの fiber の同値を合成して主定理を得た。

これで、任意の coherent な錐の pinched Hom と標準の切断制限の実際の導来 fiber の
直接比較は完了した。反転・ULift 後の切断比較からこの標準制限の fiber への実際の同値は
既存の `weightedStrictConeFamilyFiberComparison_homotopyEquivalence` にある。
元の非反転 q_x の fiber までの直接比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6。

公開19宣言の正確な型と前提（namespace `HomotopyLimits`）：

```lean
def coneSliceDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    comparisonFiber (rightFibrationMappingEvaluation (sliceOverProjection p) c x) b ⟶
      comparisonFiber (coneSliceRestrictionFiberMap c x) b

lemma coneSliceDerivedFiberMap_source {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    coneSliceDerivedFiberMap c x b ≫ comparisonFiberSource (coneSliceRestrictionFiberMap c x) b =
      comparisonFiberSource (rightFibrationMappingEvaluation (sliceOverProjection p) c x) b ≫
        (coneMappingTotalIso c x).hom

lemma coneSliceDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSliceDerivedFiberMap c x b)

def conePinchedHom_sliceRestrictionDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSliceRestrictionFiberMap c d.vertex) (coneVertexFiberPoint d))

lemma sectionConeUncurry_sectionPoint {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCone p) :
    sectionConeUncurry (SSet.yonedaEquiv.symm (coherentConeSectionPoint d)) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (fst K (Δ[0] : SSet.{u})) ≫ d.val

lemma sliceEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (coneVertexFiberPoint d) ≫
        sliceEndpointConeComparison p d.vertex ≫ endpointConeEvaluation p d.vertex) =
      fst (join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val

lemma sectionEndpointConeComparison_point_uncurry {K X : SSet.{u}} {p : K ⟶ X}
    (d : JoinCone p) :
    uncurry (SSet.yonedaEquiv.symm (coherentConeSectionPoint d) ≫
        sectionEndpointConeComparison p d.vertex ≫ endpointConeEvaluation p d.vertex) =
      fst (join (Δ[0] : SSet.{u}) K) (Δ[0] : SSet.{u}) ≫ d.val

lemma coneEndpointComparison_point_eq {K X : SSet.{u}} {p : K ⟶ X} (d : JoinCone p) :
    (sliceEndpointConeComparison p d.vertex).app _ (coneVertexFiberPoint d) =
      (sectionEndpointConeComparison p d.vertex).app _ (coherentConeSectionPoint d)

def normalizedEndpointConeRestriction {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    fixedEndpointConeSpace p x ⟶ fixedEndpointConeSpace q x

lemma normalizedSliceEndpointComparison_restrict {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    vertexFiberMap (sliceOverProjection p) (sliceOverProjection q)
        (sliceOverRestrict p f ≫ eqToHom (congrArg (fun r : K ⟶ X ↦ sliceOver r) h))
        (by rw [Category.assoc, sliceOver_eqToHom_projection h, sliceOverRestrict_projection]) x ≫
      sliceEndpointConeComparison q x =
        sliceEndpointConeComparison p x ≫ normalizedEndpointConeRestriction p q f h x

lemma normalizedSectionEndpointComparison_restrict {K J X : SSet.{u}}
    (p : J ⟶ X) (q : K ⟶ X) (f : K ⟶ J) (h : f ≫ p = q) (x : X _⦋0⦌) :
    (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f ≫
        eqToHom (congrArg (fun r : K ⟶ X ↦ coherentConeSectionSpace r x) h)) ≫
      sectionEndpointConeComparison q x =
        sectionEndpointConeComparison p x ≫ normalizedEndpointConeRestriction p q f h x

def coneEndpointRestriction {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    fixedEndpointConeSpace c.val x ⟶ fixedEndpointConeSpace p x

lemma coneSliceEndpointComparison_restrict {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    coneSliceRestrictionFiberMap c x ≫ sliceEndpointConeComparison p x =
      sliceEndpointConeComparison c.val x ≫ coneEndpointRestriction c x

lemma coneSectionEndpointComparison_restrict {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) :
    coneSectionRestriction c x ≫ sectionEndpointConeComparison p x =
      sectionEndpointConeComparison c.val x ≫ coneEndpointRestriction c x

def coneSliceEndpointDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    comparisonFiber (coneSliceRestrictionFiberMap c x) b ⟶
      comparisonFiber (coneEndpointRestriction c x) ((sliceEndpointConeComparison p x).app _ b)

lemma coneSliceEndpointDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (vertexFiber (sliceOverProjection p) x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSliceEndpointDerivedFiberMap c x b)

def coneSectionEndpointDerivedFiberMap {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (x : X _⦋0⦌) (b : (coherentConeSectionSpace p x) _⦋0⦌) :
    comparisonFiber (coneSectionRestriction c x) b ⟶
      comparisonFiber (coneEndpointRestriction c x)
        ((sectionEndpointConeComparison p x).app _ b)

lemma coneSectionEndpointDerivedFiberMap_homotopyEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (b : (coherentConeSectionSpace p x) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coneSectionEndpointDerivedFiberMap c x b)

def conePinchedHom_sectionRestrictionDerivedFiberEquivalence {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (d c : JoinCone p) :
    QCatEquivalence (pinchedHom (X := sliceOver p) d c)
      (comparisonFiber (coneSectionRestriction c d.vertex) (coherentConeSectionPoint d))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4683 jobs）、公開1415宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-native-restriction-derived-aggregate.log`、
`/tmp/gamma3-native-restriction-derived-audit.log`。

### γ3b：底の path による固定点の移送と反転・ULift 後の豊穣比較の導来 fiber


任意の添字圏 I と局所 Kan な単体的圏 C、通常の錐 c、同じ strict な図式上の任意の coherent
な錐 d に対して、`strictConePinched_reflectedDerivedFiberEquivalence c d` を構成した。
pinched Hom と `reflectedStrictConeSectionsComparison c (coherentNerveObject d.vertex)` の
導来 fiber の同値であり、点は元の d の標準切断点を頂点の表示の等式で移送した
`strictConeDerivedFiberPoint d` である。厳密極限性や Hom の fibration 性は要求しない。
既存の native な制限の fiber の同値と weighted な錐の実際の fiber 比較を合成する。

さらに end から切断への比較を除き、三形状では ULift 後の反転豊穣比較 q′ 自体の
導来 fiber まで同定した。公開定理は
`strictConePinched_reflectedEnd_discrete_equivalence`、
`strictConePinched_reflectedEnd_cospan_equivalence`、
`strictConePinched_reflectedEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、いずれも pinched Hom と

```lean
comparisonFiber ((SSet.uliftFunctor.{v, u}).map (reflectedRepresentableComparison c x))
  (strictConeReflectedEndPoint d hκ)
```

の圏同値を返す。hκ はこの形状の既存の end・切断比較の同値性の証明であり、
利用者に追加の同値性の前提を要求しない。三定理の前提は局所 Kan 性だけで、
離散図式の有限性、Hom の fibration 性、錐 c の厳密極限性は不要。
一般の I で同じ結論を使う補助定理は
`strictConePinched_reflectedEndDerivedFiberEquivalence c d hκ` であり、こちらは hκ を明示する。

固定点を回収するため、底の path に沿う実際の fiber の比較を追加した。
`kanFiberPathEndpointMap p e j` は、p の path の持ち上げ空間から端点 j 上の fiber への射。
全空間と底が Kan、p が fibration なら、両端点の射は実際のホモトピー同値になる。
これを元の射 p の path 置換へ適用した `comparisonFiberPathEquivalence p e` は、
元の p に fibration 性を要求せず、底の指定した可逆 path の両端の導来 fiber を同値にする。
Kan な底の辺から同じ移送を行う `comparisonFiberEdgeEquivalence p e` も公開した。

`comparisonFiberPostInverseEquivalence p g hg b` は、標的の同値 g の任意の点 b に対し、
選んだ逆による点 g⁻¹(b) 上の p の導来 fiber と、b 上の p≫g の導来 fiber の同値を返す。
b が g の厳密な像であることを要求しない。後合成の実際の fiber 射と、
g⁻¹≫g から恒等射へのホモトピーを b で評価した辺による移送を合成する。
三形状の `strictConeReflectedEndPoint` はこの選んだ逆で標準切断点を回収した点である。
等式による固定点の移送と path による移送を区別し、元の点のデータを保持する。

未完了は ULift を外す移送、反転した係数の q′ と元の非反転 q_x の fiber の直接比較、
一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

公開15宣言の正確な型と前提（namespace `HomotopyLimits`）：

```lean
universe u v
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

noncomputable def comparisonFiberIndexIso {T : Type v} (E B : T → SSet.{u}) (p : ∀ t, E t ⟶ B t)
    {s t : T} (h : s = t) (b : (B s) _⦋0⦌) :
    comparisonFiber (p s) b ≅ comparisonFiber (p t) (h ▸ b)

def strictConeDerivedFiberPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F)) :
    (coherentConeSectionSpace (strictCoherentDiagram F)
      (coherentNerveVertex (coherentNerveObject d.vertex))) _⦋0⦌

def strictConePinched_reflectedDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber (reflectedStrictConeSectionsComparison c (coherentNerveObject d.vertex))
        (strictConeDerivedFiberPoint d))

instance kanEquivalencePathMap_fibration {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] : Fibration (equivalencePathMap p)

def kanFiberPathEndpointMap {E B : SSet.{u}} (p : E ⟶ B)
    (e : (equivalencePath B) _⦋0⦌) (j : Fin 2) :
    vertexFiber (equivalencePathMap p) e ⟶
      vertexFiber p ((equivalencePathEndpoint B j).app _ e)

lemma kanFiberPathEndpointMap_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : (equivalencePath B) _⦋0⦌) (j : Fin 2) :
    IsSimplicialHomotopyEquivalence (kanFiberPathEndpointMap p e j)

def kanFiberPathEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e : (equivalencePath B) _⦋0⦌) :
    QCatEquivalence (vertexFiber p ((equivalencePathEndpoint B 0).app _ e))
      (vertexFiber p ((equivalencePathEndpoint B 1).app _ e))

def comparisonFiberPathEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) (e : (equivalencePath B) _⦋0⦌) :
    QCatEquivalence (comparisonFiber p ((equivalencePathEndpoint B 0).app _ e))
      (comparisonFiber p ((equivalencePathEndpoint B 1).app _ e))

def comparisonFiberEdgeEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) {b₀ b₁ : B _⦋0⦌} (e : SSet.Edge b₀ b₁) :
    QCatEquivalence (comparisonFiber p b₀) (comparisonFiber p b₁)

def comparisonFiberPostInverseEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D]
    (p : E ⟶ B) (g : B ⟶ D) (hg : IsSimplicialHomotopyEquivalence g) (b : D _⦋0⦌) :
    QCatEquivalence (comparisonFiber p ((Classical.choose hg).app _ b))
      (comparisonFiber (p ≫ g) b)

def strictConeReflectedEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    ((SSet.uliftFunctor.{v, u}).obj (bousfieldKanHolim
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) _⦋0⦌

def strictConePinched_reflectedEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (reflectedRepresentableComparison c (coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d hκ))

def strictConePinched_reflectedEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (reflectedRepresentableComparison c (coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (coherentNerveObject d.vertex))))

def strictConePinched_reflectedEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (reflectedRepresentableComparison c (coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
            (coherentNerveObject d.vertex))))

def strictConePinched_reflectedEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (reflectedRepresentableComparison c (coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (coherentNerveObject d.vertex))))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4688 jobs）、公開1430宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-reflected-end-derived-aggregate.log`、
`/tmp/gamma3-reflected-end-derived-audit.log`。

### γ3b：導来 fiber と ULift の厳密な交換、および元の宇宙の反転比較への移送


`uliftComparisonFiberIso p b` を構成した。型は

```lean
(SSet.uliftFunctor.{v, u}).obj (comparisonFiber p b) ≅
  comparisonFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)
```

であり、`p : E ⟶ B`、`b : B _⦋0⦌` と B の Kan 性だけを前提に取る。
E の Kan 性、p の fibration 性、fiber の非空性・可縮性は要求しない。
ホモトピー型の存在だけでなく、既存の path 置換で定義した実際の導来 fiber の厳密な同型。

まず `uliftInternalHomComparison` を評価の ULift から curry して定義し、ULift の完全忠実性
でパラメータごとの逆を作る。各標準単体の全単射が実際の比較の成分であることを確認して
`uliftInternalHomIso` を得た。標準区間の宇宙の同型で始域を移した `uliftIntervalHomIso` は、
両端評価と標的への後合成に厳密に可換。Kan 複体の path は全て可逆であることを使い、
`uliftEquivalencePathIso` と、その包含・両端評価・後合成の可換式を得た。

ULift の引き戻し保存を型の極限保存と単体対象の後合成から証明した。
これと可逆 path の始点評価の可換式により `uliftPathReplacementIso p` を作った。
その同型は元の源への射影と終点評価を厳密に保持する。
最後に頂点 fiber と ULift の交換同型を合成して、元の p と b の導来 fiber を復元した。

三形状への適用は `strictConePinched_smallReflectedEnd_discrete_equivalence`、
`strictConePinched_smallReflectedEnd_cospan_equivalence`、
`strictConePinched_smallReflectedEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、pinched Hom と

```lean
(SSet.uliftFunctor.{v, u}).obj
  (comparisonFiber (reflectedRepresentableComparison c x)
    (strictConeSmallReflectedEndPoint d hκ))
```

の圏同値である。hκ は各形状の既存の end・切断比較の同値性の証明で、三定理の利用者に
追加の比較仮定は要求しない。局所 Kan 性のみを要求し、c の厳密極限性、Hom の fibration 性、
離散図式の有限性は不要。元の宇宙の点は既存の回収した点の ULift.down で定義する。
一般の添字圏で使う補助定理は `strictConePinched_smallReflectedEndDerivedFiberEquivalence` で、
この一般形には hκ を明示する。

ULift は比較射の内部から fiber 全体の外へ移した。pinched Hom の宇宙が max u v なので、
比較対象の宇宙を揃える ULift 自体は fiber 全体に残す。
係数の反転 q′ と元の非反転 q_x の fiber の直接比較、一般形状の end の直接比較、
余極限側、E2a 完了後の E2b 適用は未完了。γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

公開30宣言の正確な型と前提（namespace `HomotopyLimits`）：

```lean
universe u v
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

def uliftInternalHomComparison (K B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B) ⟶
      (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B)

lemma uliftInternalHomComparison_map_uncurry {K B A : SSet.{u}}
    (f : A ⟶ (ihom K).obj B) :
    uncurry ((SSet.uliftFunctor.{v, u}).map f ≫ uliftInternalHomComparison K B) =
      (uliftTensorIso K A).inv ≫ (SSet.uliftFunctor.{v, u}).map (uncurry f)

def uliftInternalHomHomEquiv (K B A : SSet.{u}) :
    (A ⟶ (ihom K).obj B) ≃
      ((SSet.uliftFunctor.{v, u}).obj A ⟶
        (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B))

def uliftInternalHomSimplexEquiv (K B : SSet.{u}) (n : ℕ) :
    ((SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B)) _⦋n⦌ ≃
      ((ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj
        ((SSet.uliftFunctor.{v, u}).obj B)) _⦋n⦌

lemma uliftInternalHomSimplexEquiv_apply (K B : SSet.{u}) {n : ℕ}
    (s : ((SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B)) _⦋n⦌) :
    uliftInternalHomSimplexEquiv K B n s =
      (uliftInternalHomComparison K B).app (Opposite.op ⦋n⦌) s

instance uliftInternalHomComparison_isIso (K B : SSet.{u}) :
    IsIso (uliftInternalHomComparison.{u, v} K B)

def uliftInternalHomIso (K B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom K).obj B) ≅
      (ihom ((SSet.uliftFunctor.{v, u}).obj K)).obj ((SSet.uliftFunctor.{v, u}).obj B)

lemma uliftInternalHomComparison_evaluate (K B : SSet.{u}) (k : K _⦋0⦌) :
    uliftInternalHomComparison.{u, v} K B ≫ evaluateFunctorAt (Y :=
        (SSet.uliftFunctor.{v, u}).obj B) (ULift.up k) =
      (SSet.uliftFunctor.{v, u}).map (evaluateFunctorAt (Y := B) k)

def uliftIntervalHomIso (B : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom (Δ[1] : SSet.{u})).obj B) ≅
      (ihom (Δ[1] : SSet.{max u v})).obj ((SSet.uliftFunctor.{v, u}).obj B)

lemma uliftIntervalHomIso_hom_evaluate (B : SSet.{u}) (j : Fin 2) :
    (uliftIntervalHomIso.{u, v} B).hom ≫
        evaluateFunctorAt (Y := (SSet.uliftFunctor.{v, u}).obj B) (stdSimplex.obj₀Equiv.symm j) =
      (SSet.uliftFunctor.{v, u}).map
        (evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm j))

lemma uliftIntervalHomIso_hom_naturality {E B : SSet.{u}} (p : E ⟶ B) :
    (uliftIntervalHomIso.{u, v} E).hom ≫
        (ihom (Δ[1] : SSet.{max u v})).map ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map ((ihom (Δ[1] : SSet.{u})).map p) ≫
        (uliftIntervalHomIso.{u, v} B).hom

def uliftEquivalencePathIso (B : SSet.{u}) [KanComplex B] :
    (SSet.uliftFunctor.{v, u}).obj (equivalencePath B) ≅
      equivalencePath ((SSet.uliftFunctor.{v, u}).obj B)

lemma uliftEquivalencePathIso_hom_ι (B : SSet.{u}) [KanComplex B] :
    (uliftEquivalencePathIso.{u, v} B).hom ≫
        equivalencePathι ((SSet.uliftFunctor.{v, u}).obj B) =
      (SSet.uliftFunctor.{v, u}).map (equivalencePathι B) ≫
        (uliftIntervalHomIso.{u, v} B).hom

lemma uliftEquivalencePathIso_hom_endpoint (B : SSet.{u}) [KanComplex B] (j : Fin 2) :
    (uliftEquivalencePathIso.{u, v} B).hom ≫
        equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) j =
      (SSet.uliftFunctor.{v, u}).map (equivalencePathEndpoint B j)

lemma uliftEquivalencePathIso_hom_naturality {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) :
    (uliftEquivalencePathIso.{u, v} E).hom ≫
        equivalencePathMap ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (equivalencePathMap p) ≫
        (uliftEquivalencePathIso.{u, v} B).hom

instance uliftSSetFunctor_preservesPullback {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    PreservesLimit (cospan f g) (SSet.uliftFunctor.{v, u})

def uliftPullbackIso {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (pullback f g) ≅
      pullback ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)

lemma uliftPullbackIso_hom_fst {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (uliftPullbackIso.{u, v} f g).hom ≫ pullback.fst _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst f g)

lemma uliftPullbackIso_hom_snd {A B C : SSet.{u}} (f : A ⟶ B) (g : C ⟶ B) :
    (uliftPullbackIso.{u, v} f g).hom ≫ pullback.snd _ _ =
      (SSet.uliftFunctor.{v, u}).map (pullback.snd f g)

lemma uliftPathReplacement_isPullback {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    IsPullback
      ((SSet.uliftFunctor.{v, u}).map (pullback.fst (equivalencePathEndpoint B 0) p) ≫
        (uliftEquivalencePathIso.{u, v} B).hom)
      ((SSet.uliftFunctor.{v, u}).map (equivalencePathReplacementProjection p))
      (equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) 0)
      ((SSet.uliftFunctor.{v, u}).map p)

def uliftPathReplacementIso {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (SSet.uliftFunctor.{v, u}).obj (equivalencePathReplacement p) ≅
      equivalencePathReplacement ((SSet.uliftFunctor.{v, u}).map p)

lemma uliftPathReplacementIso_hom_path {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫ pullback.fst
        (equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) 0)
        ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst (equivalencePathEndpoint B 0) p) ≫
        (uliftEquivalencePathIso.{u, v} B).hom

lemma uliftPathReplacementIso_hom_source {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫
        equivalencePathReplacementProjection ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (equivalencePathReplacementProjection p)

lemma uliftPathReplacementIso_hom_target {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) :
    (uliftPathReplacementIso.{u, v} p).hom ≫
        equivalencePathReplacementMap ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (equivalencePathReplacementMap p)

def uliftComparisonFiberIso {E B : SSet.{u}} [KanComplex B] (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (comparisonFiber p b) ≅
      comparisonFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b)

def strictConeSmallReflectedEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    (bousfieldKanHolim
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)) _⦋0⦌

def strictConePinched_smallReflectedEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d hκ)))

def strictConePinched_smallReflectedEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
              (coherentNerveObject d.vertex)))))

def strictConePinched_smallReflectedEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
              (coherentNerveObject d.vertex)))))

def strictConePinched_smallReflectedEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
              (coherentNerveObject d.vertex)))))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4694 jobs）、公開1460宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規6ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-ulift-comparison-fiber-aggregate.log`、
`/tmp/gamma3-ulift-comparison-fiber-audit.log`。

### γ3b：反転した係数から元の非反転 q_x の導来 fiber の反転への直接比較


任意の Kan 複体間の射 p と底の点 b について `oppositeComparisonFiberEquivalence p b` を構成した。

```lean
QCatEquivalence (comparisonFiber p b).op
  (comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b))
```

p の fibration 性や fiber の非空性・可縮性は要求しない。
頂点 fiber と反転の厳密な同型 `oppositeVertexFiberIso` を作り、元の path 置換の終点射を
反転して共通の fibration 模型とした。元の path 置換への切断はホモトピー同値であり、
反転しても同値となる。この切断が同じ底上で誘導する実際の fiber 射
`oppositeComparisonFiberSectionMap` の同値性を、strict・導来 fiber の比較と合成した。

係数図式 H の錐 c の元の標準比較 q と反転した比較 q′ は、それぞれ厳密極限への射と
極限標準比較 κ・κ′ の合成に分解する。`reflectedConeLimitLift` の厳密な可換式、
標的の同型による `comparisonFiberPostIsoEquivalence`、標的の同値と底の path による移送を
合わせ、反転した比較の fiber を元の比較の fiber の反転へ直接移した。
`bousfieldKanConeFiberReflection_{discrete,cospan,tower}_equivalence` は二つの κ の同値性を
指定形状で検証し、利用者に追加の比較同値の仮定を要求しない。
一般形 `bousfieldKanConeFiberReflectionEquivalence` は κ・κ′ の同値性と極限の Kan 性を明示する。
固定点 `bousfieldKanReflectedFiberPoint H hκ' b` は、κ′ の選んだ逆、反転の極限保存同型の逆、
元の κ の反転の順で回収し、最後に零次の反転の全単射で元の end の点に戻す。

strict な錐への適用は `strictConePinched_originalEnd_discrete_equivalence`、
`strictConePinched_originalEnd_cospan_equivalence`、`strictConePinched_originalEnd_tower_equivalence`。
x = `coherentNerveObject d.vertex` とすると、任意の coherent な錐 d について

```lean
QCatEquivalence (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
  ((SSet.uliftFunctor.{v, u}).obj
    (comparisonFiber (representableHomotopyLimitComparison c x)
      (strictConeOriginalEndPoint d hκ hL')).op)
```

を与える。比較射は元の非反転 q_x そのもの。反転は fiber 全体に作用し、ULift は
pinched Hom の宇宙に揃えるため fiber 全体の外に置く。
離散図式は局所 Kan 性だけを要求し、有限性は不要。cospan は d の頂点が表す x に対する
Hom 図式の左脚の fibration 性、塔は同じ x に対する全隣接遷移の fibration 性を要求する。
錐 c 自体の厳密極限性・∞ 極限性はどの定理の前提にもしない。
一般形 `strictConePinched_originalEndDerivedFiberEquivalence` の追加の比較入力は三形状で検証した。

この結果は fiber 全体の反転を明示した直接比較であり、γ3b 冒頭の反転なしの模型の同定とは
区別する。fiber 全体の反転を外す実際の比較、一般形状の end の直接比較、余極限側、
E2a 完了後の E2b 適用は引き続き未完了。指定三形状の既存の全 fiber の可縮性判定は保持し、
γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.5.3.24・7.4.1.6・7.5.4.6。

公開19宣言の正確な型と前提（namespace `HomotopyLimits`、この節の追加分）：

```lean
universe u v
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

lemma opposite_pinchedConstant {B : SSet.{u}} (b : B _⦋0⦌) (n : ℕ) :
    PinchedHom.constant (SSet.opObjEquiv.symm b : B.op _⦋0⦌) n =
      SSet.opObjEquiv.symm (PinchedHom.constant b n)

def oppositeVertexFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (vertexFiber p b).op ≅ vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b)

lemma oppositeVertexFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (oppositeVertexFiberIso p b).hom ≫
        vertexFiberι (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) =
      SSet.opFunctor.map (vertexFiberι p b)

lemma kanEquivalencePathReplacementSection_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) :
    IsSimplicialHomotopyEquivalence (equivalencePathReplacementSection p)

def oppositeComparisonFiberSectionMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ⟶
      comparisonFiber (SSet.opFunctor.map (equivalencePathReplacementMap p))
        (SSet.opObjEquiv.symm b)

lemma oppositeComparisonFiberSectionMap_source {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    oppositeComparisonFiberSectionMap p b ≫
        comparisonFiberSource (SSet.opFunctor.map (equivalencePathReplacementMap p))
          (SSet.opObjEquiv.symm b) =
      comparisonFiberSource (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b) ≫
        SSet.opFunctor.map (equivalencePathReplacementSection p)

lemma oppositeComparisonFiberSectionMap_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) (b : B _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (oppositeComparisonFiberSectionMap p b)

def oppositeComparisonFiberEquivalence {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) (b : B _⦋0⦌) :
    QCatEquivalence (comparisonFiber p b).op
      (comparisonFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm b))

def comparisonFiberPostIsoEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (e : B ≅ D) (b : D _⦋0⦌) :
    QCatEquivalence (comparisonFiber p (e.inv.app _ b)) (comparisonFiber (p ≫ e.hom) b)

def bousfieldKanReflectedFiberPoint {I : Type u} [SmallCategory I] (H : I ⥤ SSet.{u})
    (hκ' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison (H ⋙ SSet.opFunctor)))
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) : (bousfieldKanHolim H) _⦋0⦌

def bousfieldKanConeFiberReflectionEquivalence {I : Type u} [SmallCategory I]
    {H : I ⥤ SSet.{u}} (c : Cone H) [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [KanComplex (limit H)]
    (hκ : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison H))
    (hκ' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison (H ⋙ SSet.opFunctor)))
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c) (bousfieldKanReflectedFiberPoint H hκ' b)).op

def bousfieldKanConeFiberReflection_discrete_equivalence {J : Type u}
    {H : (Discrete J) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H (bousfieldKanLimitComparison_discrete_homotopyEquivalence
          (H ⋙ SSet.opFunctor)) b)).op

def bousfieldKanConeFiberReflection_cospan_equivalence
    {H : (AsSmall.{u} WalkingCospan) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H
          (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
        (H ⋙ SSet.opFunctor) (limit.cone _) (limit.isLimit _)) b)).op

def bousfieldKanConeFiberReflection_tower_equivalence
    {H : (AsSmall.{u} ℕᵒᵖ) ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c)
        (bousfieldKanReflectedFiberPoint H (bousfieldKanLimitComparison_tower_homotopyEquivalence (H
          ⋙ SSet.opFunctor)) b)).op

def strictConeOriginalEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex)))
    (hL' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    (bousfieldKanHolim (simplicialHomDiagram F (coherentNerveObject d.vertex))) _⦋0⦌

def strictConePinched_originalEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [KanComplex (limit (simplicialHomDiagram F (coherentNerveObject d.vertex)))]
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex)))
    (hL : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex))))
    (hL' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d hκ hL')).op)

def strictConePinched_originalEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d
            (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_discrete_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))).op)

def strictConePinched_originalEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map WalkingCospan.Hom.inl))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_cospan_homotopyEquivalence
            F
            (coherentNerveObject d.vertex))
            (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor) (limit.cone _)
              (limit.isLimit _)))).op)

def strictConePinched_originalEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [∀ n : ℕ, Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_tower_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))).op)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4699 jobs）、公開1479宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-original-end-fiber-aggregate.log`、
`/tmp/gamma3-original-end-fiber-audit.log`。

### γ3b：Kan な fiber の反転の除去と元の非反転 q_x の反転なしの直接比較


`kanOppositeComparison K : K.op ⟶ K` とそのホモトピー同値性を、任意の Kan 複体 K に対して
構成した。空の Kan 複体も含み、非空性・可縮性は要求しない。
まず局所 Kan な単体的圏で、反転した豊穣 Hom の ULift を左 pinched Hom へ移し、
左右の pinched 模型の同値を経由して右 pinched Hom へ移し、coherent Hom 比較の逆で
元の豊穣 Hom の ULift に戻す。この実際の射 `coherentHomOppositeComparison x y` は同値。

次に C を KanObject、一点空間から K への Hom として任意の K を実現する。
`pointKanObjectHomIso` の同型で左右を挟み、ULift の充満性で元の宇宙の射 K.op ⟶ K を取る。
ULift 後に逆を持つことをホモトピーの降下で元へ戻し、構成済みの実際の射の同値性を得た。
`kanOppositeEquivalence K` と、任意の宇宙の持ち上げに対する
`uliftKanOppositeEquivalence K` も公開した。
これらは既存の左右の比較の選んだ逆を含む。射についての厳密な自然性や二重反転の厳密な
往復則をこの構成の結論には含めない。

これを元の q_x の導来 fiber に適用し、fiber 全体の反転を外した。
三形状の公開定理は `strictConePinched_originalFiber_discrete_equivalence`、
`strictConePinched_originalFiber_cospan_equivalence`、
`strictConePinched_originalFiber_tower_equivalence`。x = `coherentNerveObject d.vertex` とすると、
型は

```lean
QCatEquivalence (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
  ((SSet.uliftFunctor.{v, u}).obj
    (comparisonFiber (representableHomotopyLimitComparison c x)
      (strictConeOriginalEndPoint d hκ hL')))
```

であり、比較射・fiber のどちらにも反転を残さない。ULift は対象と Hom の宇宙を揃えるため
fiber 全体の外に置く。点 b_d は前工程と同じ `strictConeOriginalEndPoint` であり、元の coherent
な錐 d の標準切断点から、比較同値の逆・極限保存同型で回収した点を保持する。

離散図式は局所 Kan 性だけを要求し、有限性は不要。cospan は x に対する Hom 図式の左脚の
fibration 性、塔は同じ x に対する全隣接遷移の fibration 性を要求する。
通常の錐 c と coherent な錐 d は任意であり、c の厳密極限性・∞ 極限性を前提にしない。
一般形 `strictConePinched_originalFiberEquivalence` の追加の比較入力は三形状で検証している。

これで指定三形状の γ3b の元の q_x と pinched Hom の反転なしの直接比較まで実装済み。
既存の全 x・全 end の頂点 b に対する可縮性の両向きの判定と、𝒮・Sp の指定三形状の適用も
保持する。一般形状の end の直接比較、余極限側、E2a 完了後の E2b 適用は引き続き未完了で、
γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 4.6.5–4.6.7・7.4.1.6・7.5.4.6。

公開10宣言の正確な型と前提（namespace `HomotopyLimits`、この節の追加分）：

```lean
universe u v
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

def coherentHomOppositeComparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y).op ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x y)

lemma coherentHomOppositeComparison_homotopyEquivalence
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (x y : C) :
    IsSimplicialHomotopyEquivalence (coherentHomOppositeComparison x y)

def kanOppositeComparison (K : SSet.{u}) [KanComplex K] : K.op ⟶ K

lemma kanOppositeComparison_homotopyEquivalence (K : SSet.{u}) [KanComplex K] :
    IsSimplicialHomotopyEquivalence (kanOppositeComparison K)

def kanOppositeEquivalence (K : SSet.{u}) [KanComplex K] : QCatEquivalence K.op K

def uliftKanOppositeEquivalence (K : SSet.{u}) [KanComplex K] :
    QCatEquivalence ((SSet.uliftFunctor.{v, u}).obj K.op)
      ((SSet.uliftFunctor.{v, u}).obj K)

def strictConePinched_originalFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [KanComplex (limit (simplicialHomDiagram F (coherentNerveObject d.vertex)))]
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex)))
    (hL : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex))))
    (hL' : IsSimplicialHomotopyEquivalence (bousfieldKanLimitComparison
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d hκ hL')))

def strictConePinched_originalFiber_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d
            (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_discrete_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))))

def strictConePinched_originalFiber_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map WalkingCospan.Hom.inl))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_cospan_homotopyEquivalence
            F
            (coherentNerveObject d.vertex))
            (bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor) (limit.cone _)
              (limit.isLimit _)))))

def strictConePinched_originalFiber_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    [∀ n : ℕ, Fibration ((simplicialHomDiagram F (coherentNerveObject d.vertex)).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (strictConeOriginalEndPoint d (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (coherentNerveObject d.vertex))
            (bousfieldKanLimitComparison_tower_homotopyEquivalence
            (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)))))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4701 jobs）、公開1489宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルに警告・sorry・追加公理はない。
他担当の依存846ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-direct-original-fiber-aggregate.log`、
`/tmp/gamma3-direct-original-fiber-audit.log`。

### γ3 余極限側：着手時の文言と方針

極限側の指定三形状と元の q_x の導来 fiber の直接比較を保持したまま、余極限側へ進む。
既存の `Stable/Cocone.lean` の `JoinCocone`・`IsColimitCone` を native な定義として使い、
新しい余極限性の定義を作らない。通常の余錐 c を反対圏の通常の錐 c.op にし、局所 Kan な
反対の単体的圏の coherent nerve 上で既存の極限定理を適用する。
その錐を `reverseCocone` で反転し、coherent nerve の反対の標準同型と二重反転で元の値域へ戻す。
添字は nerve の反対の標準同型と ULift の反転の同型で元の通常の添字へ戻す。

初段は離散図式の Hom 条件による余極限判定を扱い、空余積を含む 𝒮 の余積へ接続する。
余錐の native な構成、標準の図式との一致、頂点・脚の元の通常の余錐との一致、余極限性の
証明を区別して検証する。双対化した図式上の条件付きの定理だけで 𝒮 の適用の完成とは数えない。
押し出し・逐次 homotopy 余極限では実際の模型と必要な cofibration 条件・Kan 置換も検証する。
一般形状の end の直接比較と、E2a 完了後の E2b 適用も後続に保持する。

再利用候補 `Stable/ConeOpposite.lean`・`ColimitReindex.lean`・`SquareDuality.lean` の依存閉包は
着手時点で他担当307ソース、全て追跡済み・コミット済み・変更なしであることを確認した。
原典：HTT 4.2.4.1、Kerodon 7.1・7.4–7.5、coherent nerve の反対の同型は Kerodon 4.6.7。

### γ3 余極限側：標準図式上の通常の余錐の native な表示と双対化


`strictNativeCocone c : JoinCocone (strictCoherentDiagram F)` を、任意の通常の小圏 I、
単体的圏 C、`F : I ⥤ C`、`c : Cocone F` に対して構成した。
固定図式は既存の `strictCoherentDiagram F` そのものであり、元の C の coherent nerve 内の
既存の native な余錐である。
`strictNativeCocone_vertex c` は頂点が元の c.pt の標準頂点に等しいことを証明する。

手順は次の通り。c.op の strict な錐を `reverseCocone` で反転し、添字を
`strictCoconeIndexIso I : U N(I) ≅ (U N(Iᵒᵖ)).op` で元の I へ戻す。
反対の単体的圏の coherent nerve の反転を `coherentOppositeReturnIso C` で元の値域へ戻す。
この時点の図式 `strictCoherentCoconeDiagram F` が元の標準図式に厳密に等しいことを、
`strictCoherentDiagram_opposite` と `strictCoherentCoconeDiagram_eq` で全単体について検証した。
通常の射列の反転と定値な豊穣 Hom の反対の一致、二重反転の自然性による。
頂点や辺だけの一致ではなく SSet の射の等式として照合している。

最後に固定図式の等式で余錐を正規化する。
`coherentCoconeOfDiagramEq` はこの移送で余錐の射・頂点・余極限性を保持する。
値域の同型による `coherentCoconePost` も native な余極限性を保存し反映する。
これらを既存の極限・余極限の反転の同値へ接続し、

```lean
strictNativeCocone_isColimit_iff (c : Cocone F) :
  IsColimitCone (strictNativeCocone c) ↔ IsLimitCone (strictCoherentCone c.op)
```

を公開した。この形式的な双対化は局所 Kan 性、c の通常の余極限性、図式の特別な形を
要求しない。後続の homotopy 余極限への適用では、局所 Kan 性と Hom 条件を具体的に検証する。
余錐の脚の元の通常の成分との照合、離散 Hom 条件からの余極限性、𝒮 の実際の余積・空余積、
homotopy 押し出し・逐次 homotopy 余極限の模型への適用は、この構成だけでは完成と数えない。
一般形状の end の直接比較と、E2a 完了後の E2b 適用も引き続き後続工程。
原典：HTT 4.2.4.1、Kerodon 4.6.7・7.1・7.4–7.5。

公開24宣言の正確な型と前提（namespace `HomotopyLimits`、この節の追加分）：

```lean
universe u v
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

def coherentCoconePost {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) : JoinCocone (p ≫ q)

lemma coherentCoconePost_val {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) : (coherentCoconePost c q).val = c.val ≫ q

lemma coherentCoconePost_vertex {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) : (coherentCoconePost c q).vertex = q.app _ c.vertex

lemma coherentCoconePost_isColimit_iff {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) [IsIso q] :
    IsColimitCone c ↔ IsColimitCone (coherentCoconePost c q)

def coherentCoconeOfDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCocone p) : JoinCocone q

lemma coherentCoconeOfDiagramEq_val {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCocone p) : (coherentCoconeOfDiagramEq h c).val = c.val

lemma coherentCoconeOfDiagramEq_vertex {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCocone p) : (coherentCoconeOfDiagramEq h c).vertex = c.vertex

lemma coherentCoconeOfDiagramEq_isColimit_iff {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCocone p) :
    IsColimitCone c ↔ IsColimitCone (coherentCoconeOfDiagramEq h c)

def coherentOppositeReturnIso (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    (SimplicialNerve Cᵒᵖ).op ≅ SimplicialNerve C

lemma coherentOppositeReturnIso_hom_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (x : C) : (coherentOppositeReturnIso C).hom.app _
        (SSet.opObjEquiv.symm (coherentNerveVertex (Opposite.op x))) = coherentNerveVertex x

def strictCoconeIndexIso (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ≅
      ((SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ)).op

lemma strictCoconeIndexIso_hom_vertex {I : Type u} [SmallCategory I] (i : I) :
    (strictCoconeIndexIso.{u, v} I).hom.app _ (ULift.up (nerveVertex i)) =
      SSet.opObjEquiv.symm (ULift.up (nerveVertex (Opposite.op i)))

lemma strictCoconeIndexIso_hom_factorization (I : Type u) [SmallCategory I] :
    (strictCoconeIndexIso.{u, v} I).hom =
      (SSet.opFunctorCompOpFunctorIso.app ((SSet.uliftFunctor.{v, u}).obj (nerve I))).inv ≫
        SSet.opFunctor.map ((uliftOppositeIso (nerve I)).inv ≫
          (SSet.uliftFunctor.{v, u}).map (nerveOppositeIso (C := I)).hom)

def strictCoherentCoconeDiagram (F : I ⥤ C) :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C

lemma strictCoherentCoconeDiagram_vertex (F : I ⥤ C) (i : I) :
    (strictCoherentCoconeDiagram F).app _ (ULift.up (nerveVertex i)) =
      coherentNerveVertex (F.obj i)

def strictCoherentCocone {F : I ⥤ C} (c : Cocone F) :
    JoinCocone (strictCoherentCoconeDiagram F)

lemma strictCoherentCocone_vertex {F : I ⥤ C} (c : Cocone F) :
    (strictCoherentCocone c).vertex = coherentNerveVertex c.pt

lemma strictCoherentCocone_isColimit_iff {F : I ⥤ C} (c : Cocone F) :
    IsColimitCone (strictCoherentCocone c) ↔ IsLimitCone (strictCoherentCone c.op)

lemma strictCoherentDiagram_opposite {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) :
    SSet.opFunctor.map (strictCoherentDiagram F) ≫ (coherentNerveOppositeIso C).hom =
      (uliftOppositeIso (nerve I)).inv ≫
        (SSet.uliftFunctor.{v, u}).map (nerveOppositeIso (C := I)).hom ≫
          strictCoherentDiagram F.op

lemma strictCoherentCoconeDiagram_eq {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C) :
    strictCoherentCoconeDiagram F = strictCoherentDiagram F

def strictNativeCocone {F : I ⥤ C} (c : Cocone F) : JoinCocone (strictCoherentDiagram F)

lemma strictNativeCocone_val {F : I ⥤ C} (c : Cocone F) :
    (strictNativeCocone c).val = (strictCoherentCocone c).val

lemma strictNativeCocone_vertex {F : I ⥤ C} (c : Cocone F) :
    (strictNativeCocone c).vertex = coherentNerveVertex c.pt

lemma strictNativeCocone_isColimit_iff {F : I ⥤ C} (c : Cocone F) :
    IsColimitCone (strictNativeCocone c) ↔ IsLimitCone (strictCoherentCone c.op)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4776 jobs）、公開1513宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規5ファイルに警告・sorry・追加公理はない。
既存の Stable 側の双対化 API の再利用で、他担当の依存は916ソースとなり、
全て追跡済み・コミット済み・変更なしを確認した。
ログ：`/tmp/gamma3-native-cocones-aggregate.log`、`/tmp/gamma3-native-cocones-audit.log`。

### γ3：任意の小圏での切断比較と反転豊穣 end による極限・余極限の判定

quasicategory K 上の二つの left fibration p・q と底を保つ実際の射 f について、
全ての頂点の fiber で f が同値なら、f の後合成による切断空間の射はホモトピー同値である。
F1 の fiber ごとの前合成同値の判定と底上の逆射による相対後合成を使い、切断模型との
同型の自然性で移す。f 自身の fibration 性と添字の三形状への制限は不要。

これを構成済みの weightedCoherentConeComparison に適用した。任意の小圏 I、局所 Kan な
単体的圏 C、通常の図式 F : I → C、対象 x について、実際の
reflectedHomHolimConeComparison F x はホモトピー同値となる。
反転係数 sHom(x,F−).op の end を使う点は維持し、元の非反転 end と同一視しない。

したがって通常の錐 c の strictCoherentCone が native な ∞ 極限錐であることは、
全ての x で reflectedRepresentableComparison c x がホモトピー同値であることと同値。
通常の余錐 c では、元の標準図式上の strictNativeCocone c の ∞ 余極限性を、
反対圏の全対象 x で reflectedRepresentableComparison c.op x が同値であることで判定できる。
Hom の厳密極限性や射の fibration 性をこの二つの判定の前提に付けない。

一般形状の元の非反転 q_x への移送、余錐の各脚の同定、𝒮 の実際の余積・homotopy 押し出し・
逐次余極限への適用、E2a 完了後の E2b は未完了。γ3 全体は引き続き進行中。
原典：HTT 4.2.4.1、Kerodon 5.6.0.6・7.4.1.6・7.5.4.6。

公開する六宣言の正確な型は以下。`I : Type u [SmallCategory I]`、`C : Type v`、
`[Category.{u} C] [SimplicialCategory C]`、C の全 sHom の Kan 性を共通前提とする。
最初の二宣言は宣言内の前提のみを使い、C・I は不要。

`SectionsFiberwiseEquivalence.lean`：

```lean
lemma simplicialSectionsRelativeIso_naturality {K E E' : SSet.{u}}
    (p : E ⟶ K) (q : E' ⟶ K) (f : E ⟶ E') (hf : f ≫ q = p) :
    simplicialSectionsMap f hf ≫ (simplicialSectionsRelativeIso q).hom =
      (simplicialSectionsRelativeIso p).hom ≫ relativeFunctorPost p q f hf (𝟙 K)
```

`SectionsFiberwiseEquivalence.lean`：

```lean
lemma simplicialSectionsMap_homotopyEquivalence_of_fibers
    {K E E' : SSet.{u}} [Quasicategory K]
    (p : E ⟶ K) (q : E' ⟶ K) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ b, IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsSimplicialHomotopyEquivalence (simplicialSectionsMap f hf)
```

`GeneralHomHolimComparison.lean`：

```lean
lemma weightedCoherentConeSectionsComparison_homotopyEquivalence (F : I ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x)
```

`GeneralHomHolimComparison.lean`：

```lean
lemma reflectedHomHolimConeComparison_homotopyEquivalence (F : I ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x)
```

`GeneralReflectedCriterion.lean`：

```lean
lemma strictCoherentCone_isLimit_iff_reflectedRepresentableComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)
```

`GeneralReflectedCriterion.lean`：

```lean
lemma strictNativeCocone_isColimit_iff_reflectedRepresentableComparison {F : I ⥤ C}
    (c : Cocone F) :
    IsColimitCone (strictNativeCocone c) ↔ ∀ x : Cᵒᵖ,
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c.op x)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4984 jobs）、公開1519宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルに警告・sorry・追加公理はない。
他担当の依存1114ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-general-aggregate.log`、`/tmp/gamma3-general-audit.log`。

### γ3：離散な添字上の Hom 条件による余極限性と Kan 複体の台での検証

離散添字は `Discrete J` という表示に限らず、任意の小圏 I に `[IsDiscrete I]` を
要求する形で扱える。各 Over i は対象・射とも一意で、その nerve は厳密な終対象である。
したがって Bousfield–Kan 重みも終対象で、strict な極限から end への標準比較は同型。
これは反対の離散圏 Iᵒᵖ にも追加の再添字なしに適用でき、空の添字も含む。

局所 Kan な単体的圏 C の通常の余錐 c について、全ての x : Cᵒᵖ で
`IsLimit (simplicialHomCone c.op x)` なら、元の図式上の `strictNativeCocone c` は
`IsColimitCone` を満たす。反転した Hom 錐の厳密な極限性、終対象の重みとの比較、
前節の一般形状の native な極限判定を使って証明する。
通常の圏での余極限性だけを豊穣 Hom の極限性の代わりに仮定しない。

𝒮 の入力となる Kan 複体の余錐 c では、その台が単体集合の余極限であれば、
全ての反変豊穣 Hom の極限性を直接検証できる。反対圏の豊穣 Hom 関手は、忘却後の
内部 Hom の反変変数の関手と厳密に一致する。braiding と豊穣合成を展開して前合成の式に戻し、
この内部 Hom 関手の極限保存を使う。離散添字では台の余極限性から native な余極限性を得る。

これらは実際に与えた Kan な頂点を保持する移送定理であり、任意の Kan 複体の族の余積対象の
構成やその Kan 性をまだ含まない。余積対象・余錐の各脚・homotopy 押し出し・逐次余極限、
一般形状の非反転 q_x への移送、E2a 後の E2b の範囲は継続する。
原典：HTT 4.2.4.1、Kerodon 7.5.4.1・7.5.4.6。

公開する十三宣言の正確な型を次に置く。`DiscreteShapeComparison` は
`I : Type u [SmallCategory I] [IsDiscrete I]` を共通前提とする。
`DiscreteHomColimits` にはさらに `C : Type v [Category.{u} C] [SimplicialCategory C]` を置き、
最後の二宣言には C の全 sHom の Kan 性を要求する。
`KanCoconeColimits` は宣言内の前提だけで、対象は既存の `KanObject.{u}` を使う。

`DiscreteShapeComparison.lean`：

```lean
instance isDiscreteOver_subsingleton (i : I) : Subsingleton (Over i)
```

`DiscreteShapeComparison.lean`：

```lean
instance isDiscreteOver_isThin (i : I) : Quiver.IsThin (Over i)
```

`DiscreteShapeComparison.lean`：

```lean
instance isDiscreteOverNerve_obj_subsingleton (i : I) (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((nerve (Over i)).obj n)
```

`DiscreteShapeComparison.lean`：

```lean
def isDiscreteOverNerve_isTerminal (i : I) : IsTerminal (nerve (Over i))
```

`DiscreteShapeComparison.lean`：

```lean
def isDiscreteBousfieldKanWeight_isTerminal : IsTerminal (bousfieldKanWeight I)
```

`DiscreteShapeComparison.lean`：

```lean
instance bousfieldKanLimitComparison_isDiscrete_isIso (H : I ⥤ SSet.{u}) :
    IsIso (bousfieldKanLimitComparison H)
```

`DiscreteHomColimits.lean`：

```lean
lemma reflectedRepresentableComparison_isDiscrete_isIso {F : I ⥤ C}
    (c : Cone F) (x : C) (hc : IsLimit (simplicialHomCone c x)) :
    IsIso (reflectedRepresentableComparison c x)
```

`DiscreteHomColimits.lean`：

```lean
lemma strictCoherentCone_isLimit_of_isDiscrete_homLimit {F : I ⥤ C}
    (c : Cone F) (hc : ∀ x : C, IsLimit (simplicialHomCone c x)) :
    IsLimitCone (strictCoherentCone c)
```

`DiscreteHomColimits.lean`：

```lean
lemma strictNativeCocone_isColimit_of_isDiscrete_homLimit {F : I ⥤ C}
    (c : Cocone F) (hc : ∀ x : Cᵒᵖ, IsLimit (simplicialHomCone c.op x)) :
    IsColimitCone (strictNativeCocone c)
```

`KanCoconeColimits.lean`：

```lean
lemma kanObjectOppositeHomFunctor_eq (X : KanObject.{u}) :
    (SimplicialCategory.sHomFunctor KanObject.{u}ᵒᵖ).obj (Opposite.op (Opposite.op X)) =
      kanObjectForget.op ⋙ (internalHom (C := SSet.{u})).flip.obj X.obj
```

`KanCoconeColimits.lean`：

```lean
noncomputable def kanObjectCocone_isColimit_of_forget {I : Type u} [SmallCategory I]
    {F : I ⥤ KanObject.{u}} (c : Cocone F)
    (hc : IsColimit (kanObjectForget.mapCocone c)) : IsColimit c
```

`KanCoconeColimits.lean`：

```lean
noncomputable def kanObjectOppositeHomCone_isLimit_of_forget
    {I : Type u} [SmallCategory I] {F : I ⥤ KanObject.{u}} (c : Cocone F)
    (hc : IsColimit (kanObjectForget.mapCocone c)) (X : KanObject.{u}ᵒᵖ) :
    IsLimit (simplicialHomCone c.op X)
```

`KanCoconeColimits.lean`：

```lean
lemma strictNativeCocone_isColimit_of_kanDiscrete_forget
    {I : Type u} [SmallCategory I] [IsDiscrete I] {F : I ⥤ KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c)) :
    IsColimitCone (strictNativeCocone c)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4987 jobs）、公開1532宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルに警告・sorry・追加公理はない。
他担当の依存1114ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-discrete-colimit-aggregate.log`、`/tmp/gamma3-discrete-colimit-audit.log`。

### γ3：𝒮 の実際の小さい余積と空余積

単体集合の族 F : J → SSet の余積を、次数 n で `Σ j, (F j).obj n` となる直和として
構成した。面・退化は成分添字 j を保持し、標準包含と成分ごとの降下射が余積の普遍性を満たす。
全成分が Kan ならこの実際の直和も Kan。ホーンの指定された面を Yoneda で単体に戻し、
二次元以上では面の交わりから全ての成分添字が等しいと示す。一次元のホーンには唯一の面を使う。
同じ成分への因子分解の後、包含の単射性で整合性を検証し、その成分の Kan 充填を直和へ戻す。
有限性・添字の非空性・モデル構造の新たな仮定は不要。

F : Discrete J → KanObject に対して、台がこの直和である `kanCoproductObject F` と
その標準包含の通常の余錐 `kanCoproductCocone F` を構成した。
台の単体集合の圏と通常の Kan 複体の圏でそれぞれ余積の普遍性を証明している。
前節の反変 Hom の極限性の検証から、F1 の既存の図式 `kanDiagramCoherentNerve F` 上の
`spaceCoproductCocone F` が native な `IsColimitCone` を満たすと証明した。
頂点は実際の直和の標準頂点で、Kan 置換や同値類による対象の置き換えを行わない。
J は任意の小さい型であり、空余積と有限余積もこの同じ構成に含まれる。

これで 𝒮 の小さい余積の対象・余錐・余極限性は公開済み。
余錐の native な各脚と包含射の照合、homotopy 押し出し・逐次余極限、
一般形状の非反転 q_x への移送、E2a 完了後の E2b は継続する。
原典：HTT 4.2.4.1、Kerodon 7.5.4.1・7.5.4.6。

公開する十八宣言の正確な型は以下。共通前提は `J : Type u`。
対象・Hom の宇宙は既存の `KanObject.{u}` に従い、空間の coherent nerve の宇宙は u+1。

`SimplicialCoproducts.lean`：

```lean
def simplicialCoproduct (F : J → SSet.{u}) : SSet.{u}
```

`SimplicialCoproducts.lean`：

```lean
def simplicialCoproductι (F : J → SSet.{u}) (j : J) : F j ⟶ simplicialCoproduct F
```

`SimplicialCoproducts.lean`：

```lean
def simplicialCoproductDesc (F : J → SSet.{u}) {X : SSet.{u}}
    (f : ∀ j, F j ⟶ X) : simplicialCoproduct F ⟶ X
```

`SimplicialCoproducts.lean`：

```lean
lemma simplicialCoproductι_desc (F : J → SSet.{u}) {X : SSet.{u}}
    (f : ∀ j, F j ⟶ X) (j : J) :
    simplicialCoproductι F j ≫ simplicialCoproductDesc F f = f j
```

`SimplicialCoproducts.lean`：

```lean
lemma simplicialCoproduct_hom_ext (F : J → SSet.{u}) {X : SSet.{u}}
    {f g : simplicialCoproduct F ⟶ X}
    (h : ∀ j, simplicialCoproductι F j ≫ f = simplicialCoproductι F j ≫ g) : f = g
```

`SimplicialCoproducts.lean`：

```lean
lemma simplicialCoproductι_cancel (F : J → SSet.{u}) (j : J) {X : SSet.{u}}
    {f g : X ⟶ F j} (h : f ≫ simplicialCoproductι F j = g ≫ simplicialCoproductι F j) :
    f = g
```

`SimplicialCoproducts.lean`：

```lean
def simplicialCoproduct_isColimit (F : J → SSet.{u}) :
    IsColimit (Cofan.mk (simplicialCoproduct F) (simplicialCoproductι F))
```

`SimplicialCoproducts.lean`：

```lean
lemma simplicialCoproduct_simplexLabel_face (F : J → SSet.{u}) {n : ℕ}
    (f : (Δ[n + 1] : SSet.{u}) ⟶ simplicialCoproduct F) (j : Fin (n + 2)) :
    (SSet.yonedaEquiv (stdSimplex.δ j ≫ f)).1 = (SSet.yonedaEquiv f).1
```

`SimplicialCoproducts.lean`：

```lean
lemma simplicialCoproduct_simplex_factorization (F : J → SSet.{u}) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ simplicialCoproduct F) (j : J)
    (h : (SSet.yonedaEquiv f).1 = j) :
    ∃ g : (Δ[n] : SSet.{u}) ⟶ F j, g ≫ simplicialCoproductι F j = f
```

`KanCoproducts.lean`：

```lean
lemma simplicialCoproduct_horn_simplexLabel_eq (F : J → SSet.{u}) {n : ℕ}
    {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ simplicialCoproduct F)
    (hf : horn.IsCompatible f) (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i) :
    (SSet.yonedaEquiv (f j hj)).1 = (SSet.yonedaEquiv (f k hk)).1
```

`KanCoproducts.lean`：

```lean
instance simplicialCoproduct_kanComplex (F : J → SSet.{u}) [∀ j, KanComplex (F j)] :
    KanComplex (simplicialCoproduct F)
```

`SpaceCoproducts.lean`：

```lean
def kanCoproductObject (F : Discrete J ⥤ KanObject.{u}) : KanObject.{u}
```

`SpaceCoproducts.lean`：

```lean
def kanCoproductCocone (F : Discrete J ⥤ KanObject.{u}) : Cocone F
```

`SpaceCoproducts.lean`：

```lean
def kanCoproductCocone_forget_isColimit (F : Discrete J ⥤ KanObject.{u}) :
    IsColimit (kanObjectForget.mapCocone (kanCoproductCocone F))
```

`SpaceCoproducts.lean`：

```lean
noncomputable def kanCoproductCocone_isColimit (F : Discrete J ⥤ KanObject.{u}) :
    IsColimit (kanCoproductCocone F)
```

`SpaceCoproducts.lean`：

```lean
noncomputable def spaceCoproductCocone (F : Discrete J ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F)
```

`SpaceCoproducts.lean`：

```lean
lemma spaceCoproductCocone_vertex (F : Discrete J ⥤ KanObject.{u}) :
    (spaceCoproductCocone F).vertex = spaceInfinityVertex (kanCoproductObject F)
```

`SpaceCoproducts.lean`：

```lean
lemma spaceCoproductCocone_isColimitCone (F : Discrete J ⥤ KanObject.{u}) :
    IsColimitCone (spaceCoproductCocone F)
```

検証：対象集約 `HomotopyLimits` のビルド成功（4990 jobs）、公開1550宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルに警告・sorry・追加公理はない。
他担当の依存1114ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-space-coproduct-aggregate.log`、`/tmp/gamma3-space-coproduct-audit.log`。

### γ3：native な余錐の各脚と元の通常の射・余積の成分包含の厳密な一致

native な余錐を指定した頂点と余錐頂点の二点の join に制限し、標準区間へ戻す実際の射を
`coherentCoconeLegMap` とした。この脚は、値域の後合成、添字の再表示、図式の等式による
余錐の移送と厳密に可換である。錐を反転して得た余錐の脚は、元の錐の脚を区間ごと反転した
射に等しい。二点の join の反転を標準区間の反転と照合して証明した。

通常の余錐 c の `strictNativeCocone c` について、任意の i の脚は、元の射 c.ι.app i の
通常の nerve から coherent nerve への標準表示に厳密に一致する。
添字の反転の同型を零単体で計算し、反対の錐の脚の既存の等式を使ってから値域を元へ戻す。
値域の帰還については一次の coherent simplex の対象と Hom を比較する。
逆向きの Path が存在しない場合も空の始域の射の一意性で処理し、省略しない。
局所 Kan 性、余極限性、添字の形状の仮定は不要。

𝒮 の実際の余積では、`spaceCoproductCoconeLeg F j` が直和の標準包含
`simplicialCoproductι (fun k ↦ (F.obj ⟨k⟩).obj) j` の coherent 表示に一致する。
元の F1 の図式上への移送は脚を変えず、余積対象も実際の直和のまま保持される。
これで小さい余積について、対象・native な余錐・余極限性に加えて各成分包含の照合も完了した。

homotopy 押し出し・逐次余極限、一般形状の非反転 q_x への移送、E2a 後の E2b は未完了。
原典：HTT 4.2.4.1、Kerodon 4.6.7・7.5.4.6。

公開する十一宣言の正確な型は以下。最初の六宣言は宣言内の前提のみを使う。
`StrictCoconeLegs` の共通前提は `I : Type u [SmallCategory I]`、
`C : Type v [Category.{u} C] [SimplicialCategory C]`。値域の帰還の辺の補題には I は不要。
`SpaceCoproductLegs` は `J : Type u` を共通前提とする。

`CoherentCoconeLegs.lean`：

```lean
def coherentCoconeLegMap {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p)
    (i : (Δ[0] : SSet.{u}) ⟶ K) : (Δ[1] : SSet.{u}) ⟶ X
```

`CoherentCoconeLegs.lean`：

```lean
lemma coherentCoconeLegMap_post {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap (coherentCoconePost c q) i = coherentCoconeLegMap c i ≫ q
```

`CoherentCoconeLegs.lean`：

```lean
lemma coherentCoconeLegMap_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (r : L ⟶ K) (i : (Δ[0] : SSet.{u}) ⟶ L) :
    coherentCoconeLegMap (c.restrict r) i = coherentCoconeLegMap c (i ≫ r)
```

`CoherentCoconeLegs.lean`：

```lean
lemma coherentCoconeLegMap_ofDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : JoinCocone p) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap (coherentCoconeOfDiagramEq h c) i = coherentCoconeLegMap c i
```

`CoherentCoconeLegs.lean`：

```lean
lemma pointJoinStdSimplexIso_reverse :
    (pointJoinStdSimplexIso.{u} 0).inv ≫
        joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
        (stableJoinReverseIso Δ[0] Δ[0]).inv =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map (pointJoinStdSimplexIso 0).inv
```

`CoherentCoconeLegs.lean`：

```lean
lemma coherentCoconeLegMap_reverse {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap c.reverseCocone
        ((stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map i) =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map
        ((pointJoinStdSimplexIso 0).inv ≫ joinMap (𝟙 Δ[0]) i ≫ c.val)
```

`StrictCoconeLegs.lean`：

```lean
lemma coherentOppositeReturnIso_hom_edge {x y : C} (f : x ⟶ y) :
    (coherentOppositeReturnIso C).hom.app (Opposite.op ⦋1⦌)
        (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ f.op))) =
      (nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
```

`StrictCoconeLegs.lean`：

```lean
def strictNativeCoconeLeg {F : I ⥤ C} (c : Cocone F) (i : I) :
    (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C
```

`StrictCoconeLegs.lean`：

```lean
lemma strictNativeCoconeLeg_eq {F : I ⥤ C} (c : Cocone F) (i : I) :
    strictNativeCoconeLeg c i = SSet.yonedaEquiv.symm
      ((nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (c.ι.app i)))
```

`SpaceCoproductLegs.lean`：

```lean
noncomputable def spaceCoproductCoconeLeg (F : Discrete J ⥤ KanObject.{u}) (j : J) :
    (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}
```

`SpaceCoproductLegs.lean`：

```lean
lemma spaceCoproductCoconeLeg_eq (F : Discrete J ⥤ KanObject.{u}) (j : J) :
    spaceCoproductCoconeLeg F j = SSet.yonedaEquiv.symm
      ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj ⟨j⟩ ⟶ kanCoproductObject F from
          simplicialCoproductι (fun k : J ↦ (F.obj ⟨k⟩).obj) j)))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4993 jobs）、公開1561宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルに警告・sorry・追加公理はない。
他担当の依存1114ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-coproduct-leg-aggregate.log`、`/tmp/gamma3-coproduct-leg-audit.log`。

### γ3b：任意の小圏上の反転比較の全導来 fiber と pinched Hom の直接模型

反転比較 q′ について、任意の小圏 I、局所 Kan な単体的圏 C、通常の錐 c に対し、
`strictCoherentCone c` の native な極限性が、全ての x と反転 end の全頂点 b における
`comparisonFiber (reflectedRepresentableComparison c x) b` の可縮 Kan 性と同値である。
通常の余錐についても、元の標準図式上の余錐の native な余極限性を反対圏の同じ全導来 fiber
の可縮性で判定する。元の比較射の fibration 性、Hom の厳密極限性、添字の形状は要求しない。

さらに任意の coherent な錐 d の標準切断点を、一般の end と切断の比較同値の逆で戻し、
元の宇宙の反転 end の点 `generalStrictConeReflectedEndPoint d` を定める。
この点での q′ の導来 fiber 全体を ULift した模型は、d から strictCoherentCone c への
pinched Hom と実際に同値である。逆の選択の像と元の標準点のずれは既存の底の path の
移送で照合している。追加の比較同値の仮定はなく、c の極限性も前提としない。

A3d の全写像空間の可縮性による終対象判定から、任意の c の極限性は全ての coherent な錐 d
に対するこの具体的な fiber 模型の可縮性とも同値となる。d の量化を strict な錐だけへ
制限しない。可縮性は零次元を含む全境界の充填であり、非空性も含む。

今回の一般形状の模型は反転係数の q′ の fiber である。指定三形状で既に証明した元の非反転
q_x の直接模型と同一視しない。一般形状の非反転 q_x への移送、homotopy 押し出し・
逐次余極限の実際の構成、E2a 完了後の E2b は引き続き未完了。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、A3d の終対象の写像空間判定。

公開する七宣言の正確な型は以下。共通前提は `I : Type u [SmallCategory I]`、
`C : Type v [Category.{u} C] [SimplicialCategory C]` と C の全 sHom の Kan 性。

`GeneralReflectedFibers.lean`：

```lean
lemma reflectedRepresentableComparison_iff_comparisonFiber_isContractibleKan {F : I ⥤ C}
    (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x) ↔
      ∀ b : (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)) _⦋0⦌,
        IsContractibleKan (comparisonFiber (reflectedRepresentableComparison c x) b)
```

`GeneralReflectedFibers.lean`：

```lean
lemma strictCoherentCone_isLimit_iff_reflectedComparisonFiber {F : I ⥤ C} (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ (x : C)
      (b : (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (reflectedRepresentableComparison c x) b)
```

`GeneralReflectedFibers.lean`：

```lean
lemma strictNativeCocone_isColimit_iff_reflectedComparisonFiber {F : I ⥤ C} (c : Cocone F) :
    IsColimitCone (strictNativeCocone c) ↔ ∀ (x : Cᵒᵖ)
      (b : (bousfieldKanHolim (simplicialHomDiagram F.op x ⋙ SSet.opFunctor)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (reflectedRepresentableComparison c.op x) b)
```

`GeneralConeFiberModel.lean`：

```lean
def generalStrictConeReflectedEndPoint {F : I ⥤ C}
    (d : JoinCone (strictCoherentDiagram F)) :
    (bousfieldKanHolim
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)) _⦋0⦌
```

`GeneralConeFiberModel.lean`：

```lean
def strictConePinched_generalReflectedEnd_equivalence {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (generalStrictConeReflectedEndPoint d)))
```

`GeneralConeFiberModel.lean`：

```lean
lemma strictConePinched_isContractibleKan_iff_generalReflectedEnd {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    IsContractibleKan
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c)) ↔
    IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
      (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
        (generalStrictConeReflectedEndPoint d)))
```

`GeneralConeFiberModel.lean`：

```lean
lemma strictCoherentCone_isLimit_iff_generalReflectedEndPointFibers {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ d : JoinCone (strictCoherentDiagram F),
      IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (generalStrictConeReflectedEndPoint d)))
```

検証：対象集約 `HomotopyLimits` のビルド成功（4995 jobs）、公開1568宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルに警告・sorry・追加公理はない。
他担当の依存1114ソースは全て追跡済み・コミット済み・変更なし。
ログ：`/tmp/gamma3-general-fiber-model-aggregate.log`、`/tmp/gamma3-general-fiber-model-audit.log`。

### γ3：strict な錐の再添字と単射な Kan 複体列の実際の逐次余極限

strict な coherent 錐を添字の任意の標準単体に制限した式を、元の射列の先頭へ錐の脚を
前置した通常の nerve の表示として計算した。これにより、任意の通常の関手 G に対し、
`strictCoherentConeMap (c.whisker G)` は元の錐の射への `joinMap id (ULift.map (nerveMap G))`
の前合成に厳密に等しい。固定図式も既存の自然性の等式で移す。
添字の nerve の持ち上げが同型なら、この再添字は native な極限性を保ち反映する。
この部分には局所 Kan 性を要求しない。

標準の塔の添字 AsSmall ℕᵒᵖ と列の反対の添字 (AsSmall ℕ)ᵒᵖ を、通常の圏同値に加え
nerve の厳密な同型として比較した。反対の錐を既存の塔の極限定理に適用できる。

F : AsSmall.{u} ℕ → KanObject.{u} の台の通常の余極限を、L9 の確定済みの filtered colimit
の Kan 性により `kanSequentialColimitObject F` として束縛する。この Kan 性には遷移の
単射性は不要。通常の余錐、台と Kan 複体の圏の余極限の普遍性、全反変 Hom の塔の極限性を
証明した。隣接遷移が台の単体集合で単射なら、その前合成による各 Hom の遷移は Kan
fibration である。これは全ての Kan 対象 X と全ての隣接遷移について検証する。

したがって、全隣接遷移の台の単射性を前提に、F1 の元の図式 kanDiagramCoherentNerve F 上の
実際の余錐 `spaceSequentialColimitCocone F` は native な `IsColimitCone` を満たす。
頂点は通常の台の colimit のままで、Kan 置換を挟まない。余錐の各脚も、台の通常の余極限の
包含射の coherent 表示と厳密に一致する。追加の Hom 極限条件や比較同値の仮定は不要。

単射性は通常の Kan 複体の圏の Mono ではなく、`F ⋙ kanObjectForget` の隣接射の Mono として
指定する。任意の遷移の列からの cofibrant な列への置換と比較、homotopy 押し出し、
一般形状の非反転 q_x への移送、E2a 後の E2b は未完了。
原典：HTT 4.2.4.1、Kerodon 7.5.3.12・7.5.4.6、Goerss–Jardine I §7。

公開する二十二宣言の正確な型は以下。`StrictConeSimplex` の後半と `StrictConeReindex` の
後半は `I J : Type u [SmallCategory I] [SmallCategory J]`、
`C : Type v [Category.{u} C] [SimplicialCategory C]` を共通前提とする。
その他は各宣言内の前提のみ。`OppositeSequenceIndex` の持ち上げの宇宙は u。

`StrictConeSimplex.lean`：

```lean
lemma nerveInitialCone_simplex {J : Type u} [SmallCategory J] {j : J}
    (h : IsInitial j) {n : ℕ} (a : (Δ[n] : SSet.{u}) ⟶ nerve J) :
    joinMap (𝟙 Δ[0]) a ≫ nerveInitialCone h =
      (pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (initialChain h
        (SSet.yonedaEquiv a))
```

`StrictConeSimplex.lean`：

```lean
lemma strictCoherentConeMap_simplex {F : I ⥤ C} (c : Cone F) {n : ℕ}
    (a : (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I)) :
    joinMap (𝟙 Δ[0]) a ≫ strictCoherentConeMap c =
      (pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        ((nerveToCoherent C).app (Opposite.op ⦋n + 1⦌)
          (ComposableArrows.precomp ((SSet.yonedaEquiv a).down ⋙ F)
            (c.π.app ((SSet.yonedaEquiv a).down.obj 0))))
```

`StrictConeReindex.lean`：

```lean
def coherentConeRestrict {K L X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (f : L ⟶ K) :
    JoinCone (f ≫ p)
```

`StrictConeReindex.lean`：

```lean
lemma coherentConeRestrict_isLimit_iff {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : L ⟶ K) [IsIso f] :
    IsLimitCone c ↔ IsLimitCone (coherentConeRestrict c f)
```

`StrictConeReindex.lean`：

```lean
lemma coherentConeCast_isLimit_iff {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCone p) (h : p = q) : IsLimitCone (c.cast h) ↔ IsLimitCone c
```

`StrictConeReindex.lean`：

```lean
lemma strictCoherentConeMap_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    joinMap (𝟙 (Δ[0] : SSet.{max u v}))
        ((SSet.uliftFunctor.{v, u}).map (nerveMap G)) ≫ strictCoherentConeMap c =
      strictCoherentConeMap (c.whisker G)
```

`StrictConeReindex.lean`：

```lean
lemma strictCoherentCone_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I) :
    strictCoherentCone (c.whisker G) =
      (coherentConeRestrict (strictCoherentCone c)
        ((SSet.uliftFunctor.{v, u}).map (nerveMap G))).cast
          (strictCoherentDiagram_precomp G F)
```

`StrictConeReindex.lean`：

```lean
lemma strictCoherentCone_isLimit_iff_whisker {F : I ⥤ C} (c : Cone F) (G : J ⥤ I)
    [IsIso ((SSet.uliftFunctor.{v, u}).map (nerveMap G))] :
    IsLimitCone (strictCoherentCone c) ↔ IsLimitCone (strictCoherentCone (c.whisker G))
```

`OppositeSequenceIndex.lean`：

```lean
def oppositeSequenceIndex : AsSmall.{u} ℕᵒᵖ ⥤ (AsSmall.{u} ℕ)ᵒᵖ
```

`OppositeSequenceIndex.lean`：

```lean
def oppositeSequenceIndexEquivalence : AsSmall.{u} ℕᵒᵖ ≌ (AsSmall.{u} ℕ)ᵒᵖ
```

`OppositeSequenceIndex.lean`：

```lean
instance nerveMap_oppositeSequenceIndex_isIso : IsIso (nerveMap oppositeSequenceIndex.{u})
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def kanSequentialColimitObject (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    KanObject.{u}
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def kanSequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) : Cocone F
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def kanSequentialColimitCocone_forget_isColimit
    (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    IsColimit (kanObjectForget.mapCocone (kanSequentialColimitCocone F))
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def kanSequentialColimitCocone_isColimit (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    IsColimit (kanSequentialColimitCocone F)
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def kanSequentialColimitCocone_homTower_isLimit
    (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (X : KanObject.{u}ᵒᵖ) :
    IsLimit (simplicialHomCone
      ((kanSequentialColimitCocone F).op.whisker oppositeSequenceIndex) X)
```

`SpaceSequentialColimits.lean`：

```lean
instance kanSequenceHomTower_map_fibration (F : AsSmall.{u} ℕ ⥤ KanObject.{u})
    [∀ n : ℕ, Mono ((F ⋙ kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n))))]
    (X : KanObject.{u}ᵒᵖ) (n : ℕ) :
    Fibration ((simplicialHomDiagram (oppositeSequenceIndex ⋙ F.op) X).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def spaceSequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F)
```

`SpaceSequentialColimits.lean`：

```lean
lemma spaceSequentialColimitCocone_vertex (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    (spaceSequentialColimitCocone F).vertex =
      spaceInfinityVertex (kanSequentialColimitObject F)
```

`SpaceSequentialColimits.lean`：

```lean
noncomputable def spaceSequentialColimitCoconeLeg (F : AsSmall.{u} ℕ ⥤ KanObject.{u})
    (n : ℕ) : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}
```

`SpaceSequentialColimits.lean`：

```lean
lemma spaceSequentialColimitCoconeLeg_eq (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (n : ℕ) :
    spaceSequentialColimitCoconeLeg F n = SSet.yonedaEquiv.symm
      ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj (AsSmall.up.obj n) ⟶ kanSequentialColimitObject F from
          colimit.ι (F ⋙ kanObjectForget) (AsSmall.up.obj n))))
```

`SpaceSequentialColimits.lean`：

```lean
lemma spaceSequentialColimitCocone_isColimitCone (F : AsSmall.{u} ℕ ⥤ KanObject.{u})
    [∀ n : ℕ, Mono ((F ⋙ kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n))))] :
    IsColimitCone (spaceSequentialColimitCocone F)
```

検証：対象集約 `HomotopyLimits` のビルド成功（5000 jobs）、公開1590宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルに警告・sorry・追加公理はない。
L9 の確定済みの filtered colimit の Kan 性を再利用し、他担当の依存は1115ソース。
全て追跡済み・コミット済み・変更なしを確認した。
ログ：`/tmp/gamma3-space-sequential-colimit-aggregate.log`、
`/tmp/gamma3-space-sequential-colimit-audit.log`。

### γ3：非 Kan な台の anodyne 置換と一脚が単射な span の実際の homotopy 押し出し

任意の anodyne 射 i : A → B と Kan 対象 X に対して、内部 Hom の前合成
`(pre i).app X` は trivial Kan fibration、したがって単体的ホモトピー同値である。
全境界との pushout-product の anodyne 性を内部 Hom の二変数随伴で移して証明した。
A と B の Kan 性は不要。既存のホーンの小対象論法の関手と単位から、任意の単体集合 P の
実際の Kan 置換対象 `anodyneKanObject P` と anodyne な単位射を構成した。
新しいモデル構造や弱同値の一致を仮定しない。

Kan 複体の図式 F の台の余錐 c の頂点をこの置換に替え、各脚を単位で後合成することで、
元の F からの Kan な余錐 `anodyneKanCocone c` を構成する。
その反変 Hom 錐から置換前の内部 Hom 錐への実際の射はホモトピー同値。
反転した Bousfield–Kan 比較 q′ はこの同値の反転と置換前の比較の合成に厳密に分解する。
添字の nerve の持ち上げが同型な再表示を許し、native な余極限性を置換前の比較で判定できる。
台の通常の余極限の場合には、置換前の全反変内部 Hom の錐の厳密な極限性も検証した。

F : AsSmall.{u} WalkingSpan → KanObject.{u} の通常の台の押し出し P を取り、
`kanHomotopyPushoutObject F := anodyneKanObject P` を頂点とする余錐を作った。
標準 span の反対の添字を標準 cospan の添字に、圏同値と nerve の厳密な同型で移す。
左脚の台が単射なら、その前合成による各反変 Hom の左脚は Kan fibration。
通常の押し出しの Hom の普遍性と一脚 fibration の cospan の end 比較から、置換前の比較が
同値になる。単位による Hom の同値を消去し、F1 の元の図式上の実際の余錐
`spaceHomotopyPushoutCocone F` が native な `IsColimitCone` を満たすと証明した。

要求する条件は `Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))`。
右脚の単射性も P 自体の Kan 性も追加の比較同値も要求しない。
頂点は使用した Kan 置換対象に厳密に一致し、三つの脚はいずれも元の colimit の包含と
anodyne な単位の合成の coherent 表示に厳密に一致する。

単射性を仮定しない span の置換と元の図式への比較、一般の遷移の列の cofibrant 置換と比較、
一般形状の非反転 q_x への移送、E2a 後の E2b は未完了。
原典：HTT 4.2.4.1、Kerodon 7.5.3.12・7.5.4.6、Goerss–Jardine I §7。

公開する二十五宣言の正確な型は以下。`AnodyneKanCocones` は
`I J : Type u [SmallCategory I] [SmallCategory J]`、`F : I → KanObject.{u}` を共通前提とする。
その他は各宣言内の前提のみで、既存の Kan 複体の宇宙に従う。

`KanSourceReplacement.lean`：

```lean
lemma trivialKanFibration_pre_of_anodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (X : SSet.{u}) [KanComplex X] :
    TrivialKanFibration ((pre i).app X)
```

`KanSourceReplacement.lean`：

```lean
lemma homotopyEquivalence_pre_of_anodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) (X : SSet.{u}) [KanComplex X] :
    IsSimplicialHomotopyEquivalence ((pre i).app X)
```

`KanSourceReplacement.lean`：

```lean
def anodyneKanObject (A : SSet.{u}) : KanObject.{u}
```

`KanSourceReplacement.lean`：

```lean
def anodyneKanObjectUnit (A : SSet.{u}) : A ⟶ (anodyneKanObject A).obj
```

`KanSourceReplacement.lean`：

```lean
lemma anodyneKanObjectUnit_anodyne (A : SSet.{u}) :
    SSet.anodyneExtensions (anodyneKanObjectUnit A)
```

`KanSourceReplacement.lean`：

```lean
instance anodyneKanObjectUnit_pre_trivialKanFibration (A : SSet.{u})
    (X : SSet.{u}) [KanComplex X] :
    TrivialKanFibration ((pre (anodyneKanObjectUnit A)).app X)
```

`AnodyneKanCocones.lean`：

```lean
def underlyingKanCoconeHomCone (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    Cone (simplicialHomDiagram F.op X)
```

`AnodyneKanCocones.lean`：

```lean
def underlyingKanCoconeHomCone_isLimit (c : Cocone (F ⋙ kanObjectForget))
    (hc : IsColimit c) (X : KanObject.{u}ᵒᵖ) : IsLimit (underlyingKanCoconeHomCone c X)
```

`AnodyneKanCocones.lean`：

```lean
def anodyneKanCocone (c : Cocone (F ⋙ kanObjectForget)) : Cocone F
```

`AnodyneKanCocones.lean`：

```lean
def anodyneKanCoconeHomComparison (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    simplicialHomCone (anodyneKanCocone c).op X ⟶ underlyingKanCoconeHomCone c X
```

`AnodyneKanCocones.lean`：

```lean
lemma anodyneKanCoconeHomComparison_homotopyEquivalence
    (c : Cocone (F ⋙ kanObjectForget)) (X : KanObject.{u}ᵒᵖ) :
    IsSimplicialHomotopyEquivalence (anodyneKanCoconeHomComparison c X).hom
```

`AnodyneKanCocones.lean`：

```lean
lemma anodyneKanCocone_reflectedComparison_factorization
    (c : Cocone (F ⋙ kanObjectForget)) (G : J ⥤ Iᵒᵖ) (X : KanObject.{u}ᵒᵖ) :
    reflectedRepresentableComparison ((anodyneKanCocone c).op.whisker G) X =
      SSet.opFunctor.map (anodyneKanCoconeHomComparison c X).hom ≫
        bousfieldKanConeComparison
          (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G))
```

`AnodyneKanCocones.lean`：

```lean
lemma anodyneKanCocone_isColimit_iff_reflectedHomComparison
    (c : Cocone (F ⋙ kanObjectForget)) (G : J ⥤ Iᵒᵖ)
    [IsIso ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap G))] :
    IsColimitCone (strictNativeCocone (anodyneKanCocone c)) ↔ ∀ X : KanObject.{u}ᵒᵖ,
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison
        (SSet.opFunctor.mapCone ((underlyingKanCoconeHomCone c X).whisker G)))
```

`OppositeSpanIndex.lean`：

```lean
def oppositeSpanIndex : AsSmall.{u} WalkingCospan ⥤ (AsSmall.{u} WalkingSpan)ᵒᵖ
```

`OppositeSpanIndex.lean`：

```lean
def oppositeSpanIndexEquivalence :
    AsSmall.{u} WalkingCospan ≌ (AsSmall.{u} WalkingSpan)ᵒᵖ
```

`OppositeSpanIndex.lean`：

```lean
instance nerveMap_oppositeSpanIndex_isIso : IsIso (nerveMap oppositeSpanIndex.{u})
```

`SpaceHomotopyPushouts.lean`：

```lean
def kanHomotopyPushoutObject (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) : KanObject.{u}
```

`SpaceHomotopyPushouts.lean`：

```lean
def kanHomotopyPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) : Cocone F
```

`SpaceHomotopyPushouts.lean`：

```lean
def underlyingPushoutHomCospan_isLimit
    (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) (X : KanObject.{u}ᵒᵖ) :
    IsLimit ((underlyingKanCoconeHomCone (colimit.cocone (F ⋙ kanObjectForget)) X).whisker
      oppositeSpanIndex)
```

`SpaceHomotopyPushouts.lean`：

```lean
lemma underlyingPushoutHomCospanComparison_homotopyEquivalence
    (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u})
    [Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))]
    (X : KanObject.{u}ᵒᵖ) :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison
      (SSet.opFunctor.mapCone
        ((underlyingKanCoconeHomCone (colimit.cocone (F ⋙ kanObjectForget)) X).whisker
          oppositeSpanIndex)))
```

`SpaceHomotopyPushouts.lean`：

```lean
def spaceHomotopyPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F)
```

`SpaceHomotopyPushouts.lean`：

```lean
lemma spaceHomotopyPushoutCocone_vertex (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    (spaceHomotopyPushoutCocone F).vertex = spaceInfinityVertex (kanHomotopyPushoutObject F)
```

`SpaceHomotopyPushouts.lean`：

```lean
def spaceHomotopyPushoutCoconeLeg (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u})
    (i : WalkingSpan) : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}
```

`SpaceHomotopyPushouts.lean`：

```lean
lemma spaceHomotopyPushoutCoconeLeg_eq (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u})
    (i : WalkingSpan) :
    spaceHomotopyPushoutCoconeLeg F i = SSet.yonedaEquiv.symm
      ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj (AsSmall.up.obj i) ⟶ kanHomotopyPushoutObject F from
          (show (F.obj (AsSmall.up.obj i)).obj ⟶ (kanHomotopyPushoutObject F).obj from
            colimit.ι (F ⋙ kanObjectForget) (AsSmall.up.obj i) ≫
              anodyneKanObjectUnit (colimit (F ⋙ kanObjectForget))))))
```

`SpaceHomotopyPushouts.lean`：

```lean
lemma spaceHomotopyPushoutCocone_isColimitCone (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u})
    [Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))] :
    IsColimitCone (spaceHomotopyPushoutCocone F)
```

検証：対象集約 `HomotopyLimits` のビルド成功（5005 jobs）、公開1615宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルに警告・sorry・追加公理はない。
ホーンの小対象論法の確定済みの関手的 anodyne 置換を再利用し、他担当の依存は1116ソース。
全て追跡済み・コミット済み・変更なしを確認した。
ログ：`/tmp/gamma3-space-homotopy-pushout-aggregate.log`、
`/tmp/gamma3-space-homotopy-pushout-audit.log`。

### γ3：任意の Kan 値 span の実際の ∞ 押し出しと頂点を保持する図式の輸送

Kan 複体間の任意の射 f を、境界の小対象論法による単射 i と trivial Kan fibration p に
分解した。p の終域の Kan 性から中間対象も Kan となる。`kanMonoArrow_fac` は i ≫ p = f
という厳密な等号で、p の単体的ホモトピー同値性も証明した。

任意の Kan 値 span F の中心と右端を保持し、左端をこの中間対象に替えた
`kanSpanMonoReplacement F` を構成した。元の図式への比較は中心と右端で恒等、左端で p。
厳密な自然性と全成分の同値性を証明した。元の両脚の単射性は仮定しない。

別途、任意の quasicategory の同型な図式の間で、余極限余錐を頂点の等号を保持して
輸送する一般補題を証明した。図式の同型を可逆円柱へ延長し、一端から余錐を延長して
他端へ制限する。Kan 値図式では、成分ごとの同値な厳密自然変換から F1 の関手同型を作り、
この輸送に渡す。添字は任意の小圏で、strict 自然変換空間の Kan 性は仮定しない。

単射に替えた span の台の通常の押し出しを anodyne に Kan 置換した対象を
`spaceArbitraryPushoutObject F` とした。その余極限余錐を上記の比較に沿って輸送し、
**元の `kanDiagramCoherentNerve F` 上の** `spaceArbitraryPushoutCocone F` と
その native な `IsColimitCone` を構成した。頂点はこの Kan 置換対象の標準頂点に厳密に一致する。
脚の単射性、追加の Hom 条件、比較同値は前提にない。

この一般の span の余錐は coherent な輸送で得る。置換前の通常の押し出しの脚を使った
厳密な式は主張しておらず、輸送された各脚の詳細な比較式はここには含めない。
一般の遷移を持つ列の置換と比較、一般形状の非反転 q_x への移送、E2a 後の E2b 適用は残る。
γ3 全体は継続中。原典：HTT 4.2.4.1、Kerodon 7.5.4.6、境界の小対象論法。

公開二十四宣言の正確な型は以下。全て名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits` 内。
`KanMonoArrowFactorization` の後半七宣言は `{A B : KanObject.{u}}` を共通前提とする。
他の前提は各型に明記した。

`KanMonoArrowFactorization.lean`：

```lean
lemma kanComplex_of_trivialKanFibration_target {A B : SSet.{u}} [KanComplex B]
    (p : A ⟶ B) [TrivialKanFibration p] : KanComplex A
```

```lean
def kanMonoArrowObject (f : A ⟶ B) : KanObject.{u}
```

```lean
def kanMonoArrowLeft (f : A ⟶ B) : A ⟶ kanMonoArrowObject f
```

```lean
def kanMonoArrowRight (f : A ⟶ B) : kanMonoArrowObject f ⟶ B
```

```lean
instance kanMonoArrowLeft_mono (f : A ⟶ B) : Mono (kanObjectForget.map (kanMonoArrowLeft f))
```

```lean
instance kanMonoArrowRight_trivialKanFibration (f : A ⟶ B) :
    TrivialKanFibration (kanObjectForget.map (kanMonoArrowRight f))
```

```lean
lemma kanMonoArrow_fac (f : A ⟶ B) : kanMonoArrowLeft f ≫ kanMonoArrowRight f = f
```

```lean
lemma kanMonoArrowRight_homotopyEquivalence (f : A ⟶ B) :
    IsSimplicialHomotopyEquivalence (kanObjectForget.map (kanMonoArrowRight f))
```

`KanDiagramColimitTransport.lean`：

```lean
lemma exists_colimitCocone_functorIso_sameVertex {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) (c : JoinCocone p) (hc : IsColimitCone c) :
    ∃ d : JoinCocone q, IsColimitCone d ∧ d.vertex = c.vertex
```

```lean
def colimitCoconeOfFunctorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) (c : JoinCocone p) (hc : IsColimitCone c) : JoinCocone q
```

```lean
lemma colimitCoconeOfFunctorIso_isColimit {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (colimitCoconeOfFunctorIso e c hc)
```

```lean
lemma colimitCoconeOfFunctorIso_vertex {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (e : FunctorIso p q) (c : JoinCocone p) (hc : IsColimitCone c) :
    (colimitCoconeOfFunctorIso e c hc).vertex = c.vertex
```

```lean
def kanDiagramColimitTransport {I : Type u} [SmallCategory I]
    {F G : I ⥤ KanObject.{u}} (η : F ⋙ kanObjectForget ⟶ G ⋙ kanObjectForget)
    (hη : ∀ i, IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : JoinCocone (kanDiagramCoherentNerve F)) (hc : IsColimitCone c) :
    JoinCocone (kanDiagramCoherentNerve G)
```

```lean
lemma kanDiagramColimitTransport_isColimit {I : Type u} [SmallCategory I]
    {F G : I ⥤ KanObject.{u}} (η : F ⋙ kanObjectForget ⟶ G ⋙ kanObjectForget)
    (hη : ∀ i, IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : JoinCocone (kanDiagramCoherentNerve F)) (hc : IsColimitCone c) :
    IsColimitCone (kanDiagramColimitTransport η hη c hc)
```

```lean
lemma kanDiagramColimitTransport_vertex {I : Type u} [SmallCategory I]
    {F G : I ⥤ KanObject.{u}} (η : F ⋙ kanObjectForget ⟶ G ⋙ kanObjectForget)
    (hη : ∀ i, IsQCatEquivalence (X := (F.obj i).obj) (Y := (G.obj i).obj) (η.app i))
    (c : JoinCocone (kanDiagramCoherentNerve F)) (hc : IsColimitCone c) :
    (kanDiagramColimitTransport η hη c hc).vertex = c.vertex
```

`SpaceArbitraryPushouts.lean`：

```lean
def kanSpanMonoReplacement (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    AsSmall.{u} WalkingSpan ⥤ KanObject.{u}
```

```lean
def kanSpanMonoReplacementComparison (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    kanSpanMonoReplacement F ⋙ kanObjectForget ⟶ F ⋙ kanObjectForget
```

```lean
instance kanSpanMonoReplacement_left_mono (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    Mono ((kanSpanMonoReplacement F ⋙ kanObjectForget).map
      (AsSmall.up.map WalkingSpan.Hom.fst))
```

```lean
lemma kanSpanMonoReplacementComparison_isQCatEquivalence
    (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) (i : AsSmall.{u} WalkingSpan) :
    IsQCatEquivalence (X := ((kanSpanMonoReplacement F).obj i).obj) (Y := (F.obj i).obj)
      ((kanSpanMonoReplacementComparison F).app i)
```

```lean
def spaceArbitraryPushoutObject (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) : KanObject.{u}
```

```lean
def spaceArbitraryPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F)
```

```lean
lemma spaceArbitraryPushoutCocone_vertex (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    (spaceArbitraryPushoutCocone F).vertex =
      spaceInfinityVertex (spaceArbitraryPushoutObject F)
```

```lean
lemma spaceArbitraryPushoutCocone_isColimitCone
    (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    IsColimitCone (spaceArbitraryPushoutCocone F)
```

```lean
lemma spaceInfinity_hasColimit_span (F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}) :
    SerrePositivity.InfinityCategories.HasColimit (kanDiagramCoherentNerve F)
```

検証：対象集約 `HomotopyLimits` のビルド成功（5121 jobs）、公開1639宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規3ファイルの24宣言を監査に追加した。
新規ファイルに警告・sorry・追加公理はない。再帰的な他担当の依存1229ソースは全て
追跡済み・コミット済み・変更なしを確認した。
ログ：`/tmp/gamma3-arbitrary-pushout-aggregate.log`、
`/tmp/gamma3-arbitrary-pushout-audit.log`。

### γ3：一般の遷移を持つ Kan 複体列の実際の homotopy 逐次余極限

任意の F : AsSmall.{u} ℕ → KanObject.{u} に対し、全隣接遷移が台で単射な
`kanSequenceMonoReplacement F` と、元の台の図式への厳密自然変換
`kanSequenceMonoComparison F` を構成した。
零段を元の F₀ として比較を恒等にし、置換済みの Rₙ から Fₙ₊₁ への合成
pₙ ≫ F(n → n+1) を、Kan な中間対象 Rₙ₊₁ への単射 iₙ と trivial Kan fibration
pₙ₊₁ に境界分解する。iₙ ≫ pₙ₊₁ = pₙ ≫ F(n → n+1) は厳密な等号。
隣接射の列を ℕ 上の関手に延長し、この可換性から全ての射に対する自然性を得る。
比較成分は零段で恒等、後続段で trivial Kan fibration なので、全て同値である。
元の列の遷移の単射性・fibration 性は仮定しない。

この置換した列 R の台の通常の逐次余極限は既存の定理で Kan。
それを `spaceArbitrarySequentialColimitObject F` として取った。
R の実際の ∞ 余極限余錐を、成分ごとの同値な自然変換に沿う図式の同型によって輸送し、
**元の `kanDiagramCoherentNerve F` 上の** `spaceArbitrarySequentialColimitCocone F` を構成した。
この余錐の native な `IsColimitCone` と、頂点が構成した対象の標準頂点に厳密に一致することを
証明した。`spaceInfinity_hasColimit_sequence` が元の図式の ∞ 余極限の存在を公開する。
脚の単射性、追加の Hom 条件、比較同値は前提にない。

元の F の通常の余極限自体が homotopy 余極限であるとは主張しない。
輸送した各脚の詳細な比較式も今回の型には含めない。
一般形状の非反転 q_x への移送、E2a 完了後の E2b 適用は未完了で、γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 7.5.3.12・7.5.4.6、境界の小対象論法。

公開十二宣言の正確な型は以下。全て名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits` 内。宇宙は u、前提は各型に明記した。

`KanSequenceMonoReplacement.lean`：

```lean
def kanSequenceMonoStage (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    (n : ℕ) → Σ X : KanObject.{u}, X ⟶ F.obj (AsSmall.up.obj n)
```

```lean
def kanSequenceMonoStep (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (n : ℕ) :
    (kanSequenceMonoStage F n).1 ⟶ (kanSequenceMonoStage F (n + 1)).1
```

```lean
lemma kanSequenceMonoStep_comparison (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (n : ℕ) :
    kanSequenceMonoStep F n ≫ (kanSequenceMonoStage F (n + 1)).2 =
      (kanSequenceMonoStage F n).2 ≫ F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)))
```

```lean
def kanSequenceMonoReplacement (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    AsSmall.{u} ℕ ⥤ KanObject.{u}
```

```lean
def kanSequenceMonoComparison (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    kanSequenceMonoReplacement F ⋙ kanObjectForget ⟶ F ⋙ kanObjectForget
```

```lean
instance kanSequenceMonoReplacement_step_mono (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (n : ℕ) :
    Mono ((kanSequenceMonoReplacement F ⋙ kanObjectForget).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n))))
```

```lean
lemma kanSequenceMonoComparison_isQCatEquivalence
    (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) (i : AsSmall.{u} ℕ) :
    IsQCatEquivalence (X := ((kanSequenceMonoReplacement F).obj i).obj) (Y := (F.obj i).obj)
      ((kanSequenceMonoComparison F).app i)
```

`SpaceArbitrarySequentialColimits.lean`：

```lean
def spaceArbitrarySequentialColimitObject (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    KanObject.{u}
```

```lean
def spaceArbitrarySequentialColimitCocone (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F)
```

```lean
lemma spaceArbitrarySequentialColimitCocone_vertex (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    (spaceArbitrarySequentialColimitCocone F).vertex =
      spaceInfinityVertex (spaceArbitrarySequentialColimitObject F)
```

```lean
lemma spaceArbitrarySequentialColimitCocone_isColimitCone
    (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    IsColimitCone (spaceArbitrarySequentialColimitCocone F)
```

```lean
lemma spaceInfinity_hasColimit_sequence (F : AsSmall.{u} ℕ ⥤ KanObject.{u}) :
    SerrePositivity.InfinityCategories.HasColimit (kanDiagramCoherentNerve F)
```

検証：対象集約 `HomotopyLimits` のビルド成功（5123 jobs）、公開1651宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規2ファイルの12宣言を監査に追加した。
新規ファイルに警告・sorry・追加公理はない。他担当の再帰的な依存1229ソースは全て
追跡済み・コミット済み・変更なしを再確認した。
ログ：`/tmp/gamma3-arbitrary-sequence-aggregate.log`、
`/tmp/gamma3-arbitrary-sequence-audit.log`。

### γ3b：一般形状の非反転比較への移送の方針

任意の小圏上の Kan 値図式 H と Kan な頂点の錐 c に対し、F1 の確定済みの
edgewiseSubdivisionFunctor を係数と錐へ同時に適用する。
共通の edgewise 係数から H と H ⋙ opFunctor への左右の自然変換は、各成分が
trivial Kan fibration。Bousfield–Kan end の同値不変性と錐の比較の自然性を用い、
共通始域の頂点の左右の射影と end の左右の誘導射が作る二つの可換正方形を得る。
四辺の同値性の消去によって元の q と反転係数の q′ の同値性を照合する。
厳密極限の Kan 性や κ の同値性、遷移の fibration 性は要求しない方針。
これを局所 Kan な単体的圏の豊穣 Hom の錐へ適用し、native な極限・余極限と
元の非反転 q_x の全導来 fiber の可縮性との一般の両向き判定へ進む。
反転 end と元の end の実際の比較および pinched Hom の元の fiber 模型への直接移送は、
この判定と区別して検証する。原典：HTT 4.2.4.1、Kerodon 7.5.4.6、8.1.1。

### γ3b：任意の小圏上の元の非反転 q_x による判定と pinched Hom の直接 fiber 模型

局所 Kan な単体的圏 C、任意の小圏 I、F : I → C と通常の錐 c に対し、実際の
`strictCoherentCone c` が ∞ 極限錐であることと、全ての x に対する元の非反転比較
`representableHomotopyLimitComparison c x` が同値であることの両向きの判定を証明した。
さらに、元の end の全ての点 b でこの q_x の導来 fiber が可縮 Kan であることとも同値。
添字の形状・Hom 錐の厳密極限性・遷移や q_x の fibration 性の仮定を付けない。
通常の余錐でも、元の図式上の `strictNativeCocone c` に対して反対圏の非反転比較による
余極限性と全導来 fiber の可縮性の両向き判定を公開した。

まず一般の Kan 値図式 H の錐 c に edgewise 解像を適用した。
左右の自然変換 `diagramEdgewiseRight H` と `diagramEdgewiseLeft H` の全成分は
trivial Kan fibration。それが誘導する Bousfield–Kan end の二つの実際の射も同値になる。
錐の比較の自然性から、edgewise な頂点の左右の射影と end の左右の誘導射の二つの
厳密な可換正方形を構成した。四つの同値の消去により q と反転比較 q′ を照合した。
厳密極限を経由しないので、その Kan 性や極限標準比較 κ の同値性は不要である。

判定だけでなく、反転比較の導来 fiber と元の比較の導来 fiber の実際の同値
`bousfieldKanConeFiber_generalReflection_equivalence` も構成した。
反転 end の指定点 b を左 end 射影の逆で共通 end に戻し、右 end 射影で元の end の点に移す。
左の頂点射影による源の移送、左の end 射影の後合成の逆の fiber 比較、右の end 射影による
後合成、右の頂点射影による源の移送を順に合成する。
左の end 射影の逆像の像と b のずれは path による固定点の移送で照合する。
この同値は fiber 全体の反転を残さず、元の宇宙の実際の比較射 q を用いる。

任意の coherent な錐 d の標準切断点から回収した反転 end の点を同じ手順で移し、
`generalStrictConeOriginalEndPoint d` を定めた。既存の反転 fiber 模型と上述の同値の ULift を
合成することで、全 coherent な d について
`pinchedHom d (strictCoherentCone c)` と、この点上の元の非反転 q_x の導来 fiber 全体の
ULift の直接の同値 `strictConePinched_generalOriginalEnd_equivalence c d` を証明した。
反転した fiber、Hom の厳密極限性、追加の比較同値の入力はいずれも残らない。
A3d により、その全 d における模型の可縮性と native な極限性の同値も得た。

これにより、指定三形状での元の q_x の判定・直接模型を任意の小圏へ拡張した。
E2a 後の E2b への具体的適用、一般の空間値図式の実際の小さい余極限の構成と
Quillen 随伴への適用等はこの保存単位に含めず、γ3 全体は継続中。
原典：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6・8.1.1。

公開十八宣言の正確な型は以下。全て名前空間
`SerrePositivity.InfinityCategories.HomotopyLimits` 内で、
`I : Type u [SmallCategory I]` を共通前提とする。
`GeneralOriginalCriterion` と `GeneralOriginalConeFiberModel` はさらに
`C : Type v [Category.{u} C] [SimplicialCategory C]` と
`[∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]` を共通前提とする。
それ以外の全前提は各型に明記した。

`GeneralConeComparisonReflection.lean`：

```lean
def diagramEdgewiseRight (H : I ⥤ SSet.{u}) : H ⋙ edgewiseSubdivisionFunctor ⟶ H
```

```lean
def diagramEdgewiseLeft (H : I ⥤ SSet.{u}) :
    H ⋙ edgewiseSubdivisionFunctor ⟶ H ⋙ SSet.opFunctor
```

```lean
lemma bousfieldKanConeComparison_edgewiseRight {H : I ⥤ SSet.{u}} (c : Cone H) :
    edgewiseRight c.pt ≫ bousfieldKanConeComparison c =
      bousfieldKanConeComparison (edgewiseSubdivisionFunctor.mapCone c) ≫
        weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H)
```

```lean
lemma bousfieldKanConeComparison_edgewiseLeft {H : I ⥤ SSet.{u}} (c : Cone H) :
    edgewiseLeft c.pt ≫ bousfieldKanConeComparison (SSet.opFunctor.mapCone c) =
      bousfieldKanConeComparison (edgewiseSubdivisionFunctor.mapCone c) ≫
        weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseLeft H)
```

```lean
lemma bousfieldKanEdgewiseRight_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H))
```

```lean
lemma bousfieldKanEdgewiseLeft_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseLeft H))
```

```lean
lemma bousfieldKanConeComparison_reflection_general_iff
    {H : I ⥤ SSet.{u}} (c : Cone H) [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison c) ↔
      IsSimplicialHomotopyEquivalence (bousfieldKanConeComparison (SSet.opFunctor.mapCone c))
```

`GeneralOriginalCriterion.lean`：

```lean
lemma representableComparison_reflection_general_iff {F : I ⥤ C} (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x) ↔
      IsSimplicialHomotopyEquivalence (reflectedRepresentableComparison c x)
```

```lean
lemma strictCoherentCone_isLimit_iff_general_representableComparison {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ x : C,
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c x)
```

```lean
lemma strictNativeCocone_isColimit_iff_general_representableComparison {F : I ⥤ C}
    (c : Cocone F) :
    IsColimitCone (strictNativeCocone c) ↔ ∀ x : Cᵒᵖ,
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c.op x)
```

```lean
lemma strictCoherentCone_isLimit_iff_general_comparisonFiber {F : I ⥤ C} (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ (x : C)
      (b : (bousfieldKanHolim (simplicialHomDiagram F x)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c x) b)
```

```lean
lemma strictNativeCocone_isColimit_iff_general_comparisonFiber {F : I ⥤ C} (c : Cocone F) :
    IsColimitCone (strictNativeCocone c) ↔ ∀ (x : Cᵒᵖ)
      (b : (bousfieldKanHolim (simplicialHomDiagram F.op x)) _⦋0⦌),
        IsContractibleKan (comparisonFiber (representableHomotopyLimitComparison c.op x) b)
```

`GeneralConeFiberReflection.lean`：

```lean
def bousfieldKanGeneralReflectedFiberPoint (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    (bousfieldKanHolim H) _⦋0⦌
```

```lean
def bousfieldKanConeFiber_generalReflection_equivalence {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    (b : (bousfieldKanHolim (H ⋙ SSet.opFunctor)) _⦋0⦌) :
    QCatEquivalence (comparisonFiber (bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) b)
      (comparisonFiber (bousfieldKanConeComparison c)
        (bousfieldKanGeneralReflectedFiberPoint H b))
```

`GeneralOriginalConeFiberModel.lean`：

```lean
def generalStrictConeOriginalEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F)) :
    (bousfieldKanHolim (simplicialHomDiagram F (coherentNerveObject d.vertex))) _⦋0⦌
```

```lean
def strictConePinched_generalOriginalEnd_equivalence {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (generalStrictConeOriginalEndPoint d)))
```

```lean
lemma strictConePinched_isContractibleKan_iff_generalOriginalEnd {F : I ⥤ C}
    (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    IsContractibleKan
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c)) ↔
    IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
      (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
        (generalStrictConeOriginalEndPoint d)))
```

```lean
lemma strictCoherentCone_isLimit_iff_generalOriginalEndPointFibers {F : I ⥤ C}
    (c : Cone F) :
    IsLimitCone (strictCoherentCone c) ↔ ∀ d : JoinCone (strictCoherentDiagram F),
      IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (representableHomotopyLimitComparison c (coherentNerveObject d.vertex))
          (generalStrictConeOriginalEndPoint d)))
```

検証：対象集約 `HomotopyLimits` のビルド成功（5127 jobs）、公開1669宣言の `#check @` と
公理監査成功（標準3公理のみ）。新規4ファイルの18宣言を監査に追加した。
新規ファイルに警告・sorry・追加公理はない。edgewise 解像を含む他担当の再帰的な依存
1229ソースは全て追跡済み・コミット済み・変更なしを再確認した。
ログ：`/tmp/gamma3-general-original-aggregate.log`、`/tmp/gamma3-general-original-audit.log`。

### γ3：自然な単体的 Hom 随伴同型と coherent nerve による極限錐の像

`SimplicialAdjunctionHomIso adj` は、通常の随伴 adj : L ⊣ R に対する
sHom_D(Lx,y) ≅ sHom_C(x,Ry) の y に自然な同型と、零単体で adj.homEquiv に一致する条件。
x に関する追加の高次の豊穣自然性は型に含めない。
この同型は任意の図式 F の表現可能な係数図式の自然同型を誘導し、錐の頂点の Hom 同型と
元の Bousfield–Kan 比較 q の厳密な可換正方形を作る。
両圏の局所 Kan 性の下で、同型な二辺の消去によって、左像 Lx で測る元の q の同値性と
右像の錐の q の同値性が一致する。全 x の判定により、任意の小圏上の strict な表示の
∞ 極限錐を通常の右随伴 R の mapCone が保つ。

R が豊穣関手の場合、通常の作用には F1 の `coherentEnrichedUnderlyingFunctor R` を使う。
`nerveToCoherent_postcomp`、`strictCoherentDiagram_postcomp`、
`strictCoherentConeMap_postcomp` は、通常の像の coherent 表示が実際の
`coherentNerveMap R` による後合成と厳密に一致することを述べる。
錐の固定図式の等式による移送まで含めて `strictCoherentCone_postcomp` で照合し、
`strictCoherentCone_postcomp_isLimit_of_adjunctionHomIso` は像の native な極限性を与える。

一般に、同じ図式の二つの極限錐は h(slice) で同型である。その同型を後合成の slice 写像で
移せば、一つの極限錐の保存から全ての極限錐の保存が従う。
`strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso` はこの事実を用い、
標準となる通常の錐 c が一つ存在する strict な図式の上の、任意の coherent な極限錐 d の
保存を述べる。d 自体が通常の strict な錐から来るとは仮定しない。

必要な入力は通常の随伴・自然な単体的 Hom 同型・局所 Kan 性であり、Hom の厳密極限性や
遷移の fibration 性は追加しない。通常の Quillen 条件だけから Hom 同型の存在を導いたり、
任意の coherent な図式に対する導来随伴を構成したりする段階は含めない。
モデル圏の cofibrant-fibrant 置換・frame との接続と E2b の具体的適用は後続の課題。
原典：HTT 4.2.4.1・5.2.4.6、Kerodon 7.5.4.6。

公開十四宣言の正確な型は以下。名前空間は
`SerrePositivity.InfinityCategories.HomotopyLimits`。
`AdjunctionHomLimits` の共通前提は `C : Type v`、`D : Type w`、
`[Category.{u} C] [Category.{u} D] [SimplicialCategory C] [SimplicialCategory D]`、
`L : C → D` と `R : D → C` は通常の関手。図式の添字は `I : Type u [SmallCategory I]`。
`StrictConeFunctorImage` は対象の宇宙を共有する `C D : Type v` と同じ Hom の前提を使う。
ただし `composableArrows_precomp_postcomp` は通常の Category だけで、SimplicialCategory は不要。
`PostcompLimitTransport` の全前提は型内に明記した。

`AdjunctionHomLimits.lean`：

```lean
def SimplicialAdjunctionHomIso (adj : L ⊣ R)
```

```lean
lemma simplicialAdjunctionHomIso_zero {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj)
    (x : C) (y : D) (f : L.obj x ⟶ y) :
    ((e.val x).hom.app y).app (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _ f) =
      SimplicialCategory.homEquiv' _ _ (adj.homEquiv x y f)
```

```lean
def simplicialAdjunctionHomDiagramIso {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj)
    (F : I ⥤ D) (x : C) :
    simplicialHomDiagram F (L.obj x) ≅ simplicialHomDiagram (F ⋙ R) x
```

```lean
lemma representableComparison_adjunction_square {adj : L ⊣ R}
    (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F) (x : C) :
    ((e.val x).app c.pt).hom ≫ representableHomotopyLimitComparison (R.mapCone c) x =
      representableHomotopyLimitComparison c (L.obj x) ≫
        weightedSectionsMap (bousfieldKanWeight I)
          (simplicialAdjunctionHomDiagramIso e F x).hom
```

```lean
lemma representableComparison_adjunction_homotopyEquivalence_iff
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F) (x : C) :
    IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison c (L.obj x)) ↔
      IsSimplicialHomotopyEquivalence (representableHomotopyLimitComparison (R.mapCone c) x)
```

```lean
lemma strictCoherentCone_map_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    {adj : L ⊣ R} (e : SimplicialAdjunctionHomIso adj) {F : I ⥤ D} (c : Cone F)
    (hc : IsLimitCone (strictCoherentCone c)) : IsLimitCone (strictCoherentCone (R.mapCone c))
```

`PostcompLimitTransport.lean`：

```lean
lemma isLimitCone_postcomp_of_one_limitCone {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : K ⟶ X} (f : X ⟶ Y)
    (c : JoinCone p) (hc : IsLimitCone c) (hfc : IsLimitCone (c.postcomp f))
    (d : JoinCone p) (hd : IsLimitCone d) : IsLimitCone (d.postcomp f)
```

`StrictConeFunctorImage.lean`：

```lean
lemma nerveToCoherent_postcomp (R : EnrichedFunctor SSet.{u} D C) :
    nerveToCoherent D ≫ coherentNerveMap R =
      nerveMap (coherentEnrichedUnderlyingFunctor R) ≫ nerveToCoherent C
```

```lean
lemma strictCoherentDiagram_postcomp (F : I ⥤ D) (R : EnrichedFunctor SSet.{u} D C) :
    strictCoherentDiagram F ≫ coherentNerveMap R =
      strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R)
```

```lean
lemma composableArrows_precomp_postcomp {n : ℕ} (A : ComposableArrows D n)
    {d : D} (f : d ⟶ A.obj 0) (G : D ⥤ C) :
    ComposableArrows.precomp A f ⋙ G = ComposableArrows.precomp (A ⋙ G) (G.map f)
```

```lean
lemma strictCoherentConeMap_postcomp {F : I ⥤ D} (c : Cone F)
    (R : EnrichedFunctor SSet.{u} D C) :
    strictCoherentConeMap c ≫ coherentNerveMap R =
      strictCoherentConeMap ((coherentEnrichedUnderlyingFunctor R).mapCone c)
```

```lean
lemma strictCoherentCone_postcomp {F : I ⥤ D} (c : Cone F)
    (R : EnrichedFunctor SSet.{u} D C) :
    ((strictCoherentCone c).postcomp (coherentNerveMap R)).cast
        (strictCoherentDiagram_postcomp F R) =
      strictCoherentCone ((coherentEnrichedUnderlyingFunctor R).mapCone c)
```

```lean
lemma strictCoherentCone_postcomp_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
    {adj : L ⊣ coherentEnrichedUnderlyingFunctor R} (e : SimplicialAdjunctionHomIso adj)
    {F : I ⥤ D} (c : Cone F) (hc : IsLimitCone (strictCoherentCone c)) :
    IsLimitCone ((strictCoherentCone c).postcomp (coherentNerveMap R))
```

```lean
lemma strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
    {adj : L ⊣ coherentEnrichedUnderlyingFunctor R} (e : SimplicialAdjunctionHomIso adj)
    {F : I ⥤ D} (c : Cone F) (hc : IsLimitCone (strictCoherentCone c))
    (d : JoinCone (strictCoherentDiagram F)) (hd : IsLimitCone d) :
    IsLimitCone (d.postcomp (coherentNerveMap R))
```

