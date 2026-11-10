# 第2章の交差抜き取り検査（-c）

- 対象表は main の `e3c1c6c0e`。抽出後の `abe0628ab` からの差分には章別 CSV・検査証拠の変更がない。
- 乱数の種は `0xabe0628a`。Python 3.14.7 の `random.Random(seed).sample` を使用。章を 1→2→3、区分を own・both・mathlib の合算→partial→none の順に取り、各母集団は番号の数値順に整列してから重複なしで抽出した。
- 独立照合では抽出に元表の区分を使い、引用の宣言名を段1・段1′および章別 kernel evidence の型の取得に使った。元表の理由は独立判定を固定した後に読んだ。Kerodon 本文と型・定義本体を照らし、必要な候補の型を追加確認した。
- §8.1 の直接対応を partial の基準とした。差は対応区分で数え、同じ区分を支える引用の補足は別記した。§8.4 の停止基準は own・both・mathlib 群の比較後の差に適用する。

| 元の区分 | 母集団 | 抽出 | 独立照合の差 | 比較後の差 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 59 | 20 | 0/20（0%） | 0/20（0%） |
| partial | 80 | 10 | 0/10（0%） | 0/10（0%） |
| none | 74 | 10 | 1/10（10%） | 1/10（10%） |

比較後の own・both・mathlib の差は1割以下。partial・none の差は §8.2 の一括見直し用に記録した。

## own・both・mathlib

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [2.1.2.13](https://kerodon.net/tag/00CF) | mathlib | mathlib | mathlib | — | モノイダル圏を入力。tensorUnit が 𝟙_ C の値で、圏 C を明示できるため本文の単位対象の記法に一致。 `CategoryTheory.MonoidalCategoryStruct.tensorUnit` (`Mathlib/CategoryTheory/Monoidal/Category.lean:98`) |
| [2.1.2.19](https://kerodon.net/tag/00CK) | mathlib | mathlib | mathlib | — | モノイダル圏の任意の X,Y。MonoidalCategory.triangle は X⊗(1⊗Y) からの左単位子経由と結合子の逆・右単位子経由の一致。本文の向きは結合子を反対に書いた同じ等式。 `CategoryTheory.MonoidalCategory.triangle` (`Mathlib/CategoryTheory/Monoidal/Category.lean:207`) |
| [2.1.5.8](https://kerodon.net/tag/00DL) | mathlib | mathlib | mathlib | — | モノイダル圏間の F。LaxMonoidal の μ と自然性・結合性は非単位的構造を表し、ε と二つの unitality は本文が要求する単位を指定する。 `CategoryTheory.Functor.LaxMonoidal` (`Mathlib/CategoryTheory/Monoidal/Functor.lean:65`) |
| [2.2.0.1](https://kerodon.net/tag/007L) | mathlib | mathlib | mathlib | — | 双圏を入力として Bicategory.Strict の三つの 1-射の等式と各 coherence が eqToIso という条件を課す。基礎の Hom 圏と合成は Bicategory のデータで、本文の厳密性に一致。 `CategoryTheory.Bicategory.Strict` (`Mathlib/CategoryTheory/Bicategory/Strict/Basic.lean:40`) |
| [2.2.1.1](https://kerodon.net/tag/007Q) | mathlib | mathlib | mathlib | — | 対象型を指定。Bicategory の homCategory と whiskering、associator、unitors および coherence が本文のデータを与える。横合成は左右 whiskering から得る。 `CategoryTheory.Bicategory` (`Mathlib/CategoryTheory/Bicategory/Basic.lean:61`) |
| [2.2.2.2](https://kerodon.net/tag/03J5) | mathlib | mathlib | mathlib | — | 引戻しを持つ普通圏。SpanBicat で左右の射のクラスを全射に広げると任意の span を取れる。2-射は頂点間の可換写像、合成は引戻し。 `CategoryTheory.Span` (`Mathlib/CategoryTheory/Bicategory/Span/Basic.lean:42`), `CategoryTheory.Span.SpanBicat` (`Mathlib/CategoryTheory/Bicategory/Span/Basic.lean:151`), `CategoryTheory.Span.SpanBicat.instBicategory` (`Mathlib/CategoryTheory/Bicategory/Span/Basic.lean:364`) |
| [2.2.3.1](https://kerodon.net/tag/008B) | mathlib | mathlib | mathlib | — | 任意の双圏。Opposite.bicategory は 1-射を反転し、各 Hom 圏の 2-射の向きを保持する。逆順の合成と入れ替えた単位子が一致。 `Bicategory.Opposite.bicategory` (`Mathlib/CategoryTheory/Bicategory/Opposites.lean:157`) |
| [2.2.4.1](https://kerodon.net/tag/008H) | mathlib | mathlib | mathlib | — | 双圏 B,C。StrictPseudofunctor は対象と Hom の作用に加え、1-射の単位・合成を等式で保存し、対応する構造 2-射を eqToIso とする。Core は両 unitor と associator の保存を明示する。 `CategoryTheory.StrictPseudofunctor` (`Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean:43`) |
| [2.4.1.11](https://kerodon.net/tag/00K1) | mathlib | mathlib | mathlib | — | 豊穣基底を SSet に取る。EnrichedFunctor は対象写像と単体集合の Hom 写像を持ち、map_id と map_comp が本文の両可換条件。 `CategoryTheory.EnrichedFunctor` (`Mathlib/CategoryTheory/Enriched/Basic.lean:293`) |
| [2.4.7.3](https://kerodon.net/tag/00N2) | mathlib | mathlib | mathlib | — | CoxeterSystem の W と指定の生成元。length は simple reflection のリストの積が w になるものの最小の長さを取る。生成性により空の候補集合の分岐は不要。 `CoxeterSystem.length` (`Mathlib/GroupTheory/Coxeter/Length.lean:74`) |
| [2.5.0.2](https://kerodon.net/tag/00NF) | mathlib | mathlib | mathlib | — | ChainComplex の添字を ℤ に取る。HomologicalComplex は隣接次数の微分と d≫d=0 を持ち、それ以外の成分は形によりゼロ。仮定の加法性は Lean のゼロ射仮定より強い。 `ChainComplex` (`Mathlib/Algebra/Homology/HomologicalComplex.lean:151`) |
| [2.5.0.3](https://kerodon.net/tag/00NG) | mathlib | mathlib | mathlib | — | 同じ添字形の二鎖複体。Hom は各次数の f と微分との可換式を持ち、本文の chain map。 `HomologicalComplex.Hom` (`Mathlib/Algebra/Homology/HomologicalComplex.lean:217`) |
| [2.5.0.4](https://kerodon.net/tag/00NH) | mathlib | mathlib | mathlib | — | 可換環 k について ModuleCat k を値圏に、ℤ を添字にした ChainComplex の既存 Category instance が本文の Ch(k)。 `ChainComplex` (`Mathlib/Algebra/Homology/HomologicalComplex.lean:151`) |
| [2.5.1.5](https://kerodon.net/tag/00NV) | mathlib | mathlib | mathlib | — | アーベル圏の鎖写像。QuasiIso は全次数の QuasiIsoAt、後者は homologyMap の IsIso。整数添字に特殊化すると本文の条件。 `QuasiIso` (`Mathlib/Algebra/Homology/QuasiIso.lean:138`), `QuasiIsoAt` (`Mathlib/Algebra/Homology/QuasiIso.lean:34`) |
| [2.5.2.1](https://kerodon.net/tag/00PA) | own | own | own | — | 対象型 D と可換係数環。A=ℤ の DGCategory は非有界鎖複体による豊穣で、Hom 複体・閉単位・鎖写像の合成および圏法則を持つ。 `SerrePositivity.DifferentialGraded.DGCategory` (`SerrePositivity/DifferentialGraded/Category/Basic.lean:58`) |
| [2.5.2.4](https://kerodon.net/tag/00PD) | own | own | own | — | dg 圏を入力。ClosedCategory の ForgetEnrichment の Hom は単位複体からの鎖写像なので零次サイクル、合成と恒等射は豊穣構造から誘導される。 `SerrePositivity.DifferentialGraded.ClosedCategory` (`SerrePositivity/DifferentialGraded/Category/Basic.lean:63`) |
| [2.5.3.10](https://kerodon.net/tag/00PW) | own | own | own | — | 任意の DGCategory で dgNerve.instQuasicategory。hornFilling が同じ dgNerve の内ホーンを全て埋める。 `SerrePositivity.InfinityCategories.dgNerve.instQuasicategory` (`SerrePositivity/InfinityCategories/DGNerve/Quasicategory.lean:54`), `SerrePositivity.InfinityCategories.dgNerve.hornFilling` (`SerrePositivity/InfinityCategories/DGNerve/Quasicategory.lean:45`) |
| [2.5.4.6](https://kerodon.net/tag/00Q4) | own | own | own | — | dg 圏を入力。HomotopyCategory は閉零次射を境界で割った圏で、homotopyHomologyEquiv が Hom 複体の H₀ と同定する。恒等射・合成は元の閉零次射の像。 `SerrePositivity.DifferentialGraded.HomotopyCategory` (`SerrePositivity/DifferentialGraded/Category/Basic.lean:242`), `SerrePositivity.DifferentialGraded.homotopyHomologyEquiv` (`SerrePositivity/DifferentialGraded/Category/Basic.lean:356`) |
| [2.5.7.3](https://kerodon.net/tag/00RJ) | own | own | own | — | 整数加群の二つの単体対象と bidegree p,q。shuffleBidegree と shuffleApp の成分は各 (p,q)-shuffle に対する退化写像のテンソルを permutation の符号で加えたもの。 `SerrePositivity.KST.ProExcision.shuffleApp` (`SerrePositivity/KST/ProExcision/Shuffle.lean:34`), `SerrePositivity.KST.ProExcision.shuffleBidegree` (`SerrePositivity/KST/ProExcision/Shuffle.lean:23`) |
| [2.5.8.1](https://kerodon.net/tag/00S1) | own | own | own | — | n,p と p≤n。awFront と awBack は Fin の順序写像 i↦i、j↦p+j。単体アーベル群の反変作用で本文の二つの準同型を得る。 `SerrePositivity.KST.ProExcision.awFront` (`SerrePositivity/KST/ProExcision/AlexanderWhitney.lean:24`), `SerrePositivity.KST.ProExcision.awBack` (`SerrePositivity/KST/ProExcision/AlexanderWhitney.lean:33`) |

## partial

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [2.1.4.17](https://kerodon.net/tag/00DB) | partial | partial | partial | special | LaxMonoidal.comp の μ は本文と同じ G の tensorator の後に G.map μ を合成する。単位付き C,D,E と単位まで保つ構造に限る。 `CategoryTheory.Functor.LaxMonoidal.comp` (`Mathlib/CategoryTheory/Monoidal/Functor.lean:231`) |
| [2.2.5.5](https://kerodon.net/tag/0090) | partial | partial | partial | component | LaxFunctor・Pseudofunctor・StrictPseudofunctor の id,comp は指定の対象間の恒等・合成を与える。StrictlyUnitaryLaxFunctor にも同じ二演算と法則がある。四つの普通圏を一括して持つ包含図式は確認できなかった。 `CategoryTheory.LaxFunctor.id` (`Mathlib/CategoryTheory/Bicategory/Functor/Lax.lean:145`), `CategoryTheory.LaxFunctor.comp` (`Mathlib/CategoryTheory/Bicategory/Functor/Lax.lean:178`), `CategoryTheory.Pseudofunctor.id` (`Mathlib/CategoryTheory/Bicategory/Functor/Pseudofunctor.lean:146`), `CategoryTheory.Pseudofunctor.comp` (`Mathlib/CategoryTheory/Bicategory/Functor/Pseudofunctor.lean:158`), `CategoryTheory.StrictPseudofunctor.id` (`Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean:128`), `CategoryTheory.StrictPseudofunctor.comp` (`Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean:134`) |
| [2.3.5.1](https://kerodon.net/tag/00BA) | partial | partial | partial | component | SimplicialThickening.Path と compFunctor は有限線形順序の場合の端点を持つ部分集合と和による 1-射の合成を与える。一方 path_hom_iff の 2-射は包含で、Kerodon の逆包含とは逆。任意の半順序で指定の逆包含を使う厳密双圏は確認できなかった。 `CategoryTheory.SimplicialThickening.Path` (`Mathlib/AlgebraicTopology/SimplicialNerve.lean:63`), `CategoryTheory.SimplicialThickening.compFunctor` (`Mathlib/AlgebraicTopology/SimplicialNerve.lean:113`)。追加確認 `SerrePositivity/InfinityCategories/Coherent/Path.lean:30` |
| [2.4.3.5](https://kerodon.net/tag/00KS) | partial | partial | partial | component | SimplicialNerve は添字 [n] 上の豊穣関手を取るが、Mathlib の compFunctor と path_hom_iff は包含、Kerodon 2.4.3.1 は逆包含。包含方向の違いが現れない 0・1 次の成分は coherentNerveVertexEquiv と coherentNerveEdgeEquiv で一致。一般の n で指定の逆包含を使う nerve は確認できなかった。 `CategoryTheory.SimplicialNerve` (`Mathlib/AlgebraicTopology/SimplicialNerve.lean:190`)。追加確認 `SerrePositivity/InfinityCategories/Coherent/Path.lean:30`, `SerrePositivity/InfinityCategories/F1/Coherent/Vertices.lean:101`, `SerrePositivity/InfinityCategories/F1/Coherent/EdgeEquiv.lean:93` |
| [2.5.4.10](https://kerodon.net/tag/00Q8) | partial | partial | partial | component | HomotopyComparison.equivalence は指定の toH0 による圏同値。Kerodon が指定する普通圏の厳密な同型の逆関手と等式を返す型は確認できなかった。 `SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.equivalence` (`SerrePositivity/InfinityCategories/DGNerve/HomotopyCategory.lean:98`), `SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0` (`SerrePositivity/InfinityCategories/DGNerve/HomotopyCategory.lean:34`) |
| [2.5.6.11](https://kerodon.net/tag/00R2) | partial | partial | partial | special | M が非負次数のとき Abelian.DoldKan.equivalence と Adjunction.homAddEquiv の逆写像が、F.map の後に counit を合成する指定の θ を加法同型にする。一般の整数添字 M の右随伴の値は零延長の右随伴で smart 切断した後の Γ となる。任意の M について本文の指定 counit による加法同型までを返す型は確認できなかった。 `CategoryTheory.Abelian.DoldKan.equivalence` (`Mathlib/AlgebraicTopology/DoldKan/Equivalence.lean:167`)。追加確認 `Mathlib/CategoryTheory/Adjunction/Additive.lean:53` |
| [2.5.7.10](https://kerodon.net/tag/00RR) | partial | partial | partial | component | shuffleBilinear_left_unit は自由化した標準零単体を左因子とする単位式の模型。projectedRingShuffleProduct の法則は同じ環上の積に限る。任意の A,B の左右単位と符号付き対称性の三条件をすべて与える型は確認できなかった。 `SerrePositivity.InfinityCategories.projectedRingShuffleProduct_assoc` (`SerrePositivity/InfinityCategories/Derived/DGSimplicialRingProjectedLaws.lean:36`), `SerrePositivity.InfinityCategories.projectedRingShuffleProduct_left_unit` (`SerrePositivity/InfinityCategories/Derived/DGSimplicialRingProjectedLaws.lean:59`), `SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_left_unit` (`SerrePositivity/EInfinity/BarrattEccles/ShuffleLeftUnit.lean:72`) |
| [2.5.8.11](https://kerodon.net/tag/00SB) | partial | partial | partial | component | normalizedEZHomotopy は同じ normalizedAlexanderWhitney の後に shuffle を合成した射と恒等を鎖ホモトピーで結ぶ。従ってホモロジー上の AW の単射性は直接出る。逆合成のホモトピーまたは全射性までの型は確認できなかった。 `SerrePositivity.KST.ProExcision.normalizedEZHomotopy` (`SerrePositivity/KST/ProExcision/NormalizedEZHomotopy.lean:64`), `SerrePositivity.KST.ProExcision.ezHomotopy` (`SerrePositivity/KST/ProExcision/EZHomotopy.lean:62`) |
| [2.5.9.10](https://kerodon.net/tag/00SN) | partial | partial | partial | component | coherentComparison と coherentComparison_obj が所定の source・target の比較射と対象上の恒等を与える。app は coherentSimplex を指定するが、本文の評価式による比較の一意性を述べる型は確認できなかった。 `SerrePositivity.InfinityCategories.DoldKanComparison.coherentComparison` (`SerrePositivity/InfinityCategories/DoldKanComparison/CoherentComparison.lean:59`), `SerrePositivity.InfinityCategories.DoldKanComparison.coherentComparison_obj` (`SerrePositivity/InfinityCategories/DoldKanComparison/CoherentComparison.lean:78`) |
| [2.5.9.13](https://kerodon.net/tag/00SQ) | partial | partial | partial | special | cubeFlag_boundary_sum は 2 以上の次元で最大旗の符号付き境界を座標面の符号付き和に同定する。零始まりの添字と 1 面−0 面の組は一始まりの添字と 0 面−1 面に対応する。正規化鎖の式として全次元を量化する宣言は確認できなかった。 `SerrePositivity.InfinityCategories.DoldKanComparison.cubeFlag_boundary_sum` (`SerrePositivity/InfinityCategories/DoldKanComparison/CubeBoundary.lean:84`), `SerrePositivity.InfinityCategories.DoldKanComparison.cubeFlag_boundary_eq_outer_sum` (`SerrePositivity/InfinityCategories/DoldKanComparison/CubeBoundary.lean:49`) |

## none

| Kerodon | -a2 | 独立 | 比較後 | partial_kind | 照合内容と元表の型 |
|---|---|---|---|---|---|
| [2.1.2.4](https://kerodon.net/tag/00C6) | none | none | none | — | IsIdempotentElem と Semigroup の左右消去を探索。単位元を持たない半群で指定元の冪等性と両側作用の単射性を単位元条件と同値にする型は確認できなかった。 — |
| [2.1.4.1](https://kerodon.net/tag/00CW) | none | none | none | — | Functor.Monoidal と CoreMonoidal の tensorator は自然同型。非単位的モノイダル圏間で tensor と associator を厳密に保存する条件を定義した型は確認できなかった。 — |
| [2.2.6.1](https://kerodon.net/tag/0098) | none | none | none | — | Pseudofunctor.comp・id と Bicategory.Equivalence を確認。後者は双圏内の対象間の同値であり、双圏間の擬関手の両側の厳密な逆を定義するものではない。 — |
| [2.3.1.1](https://kerodon.net/tag/009U) | none | none | none | — | StrictlyUnitaryLaxFunctor と LocallyDiscrete、SimplicialNerve を探索。前二者は候補の n 成分の入力、後者は SSet 豊穣を入力とする別の nerve。全次元を単体集合に束ねた Duskin nerve は確認できなかった。 — |
| [2.3.2.1](https://kerodon.net/tag/00AC) | none | none | none | — | 普通の nerve の準圏性と局所 Kan 豊穣圏の coherent nerve を探索。一般の Duskin nerve の準圏性と全 2-射可逆性の iff は確認できなかった。 — |
| [2.3.3.1](https://kerodon.net/tag/00AR) | none | none | none | — | StrictlyUnitaryLaxFunctor と coherent / dg nerve の hornFilling を探索。指定した 2-胞体 γ の可逆性による Duskin nerve の内ホーンの延長を扱う型は確認できなかった。 — |
| [2.3.4.5](https://kerodon.net/tag/00AX) | none | none | none | — | StrictlyUnitaryPseudofunctor と SimplicialNerve の写像を探索。thin 2-単体を保存する Duskin nerve 間の写像と指定関手の全単射は確認できなかった。 — |
| [2.3.5.7](https://kerodon.net/tag/00BF) | none | none | none | — | SimplicialThickening.Path と SimplicialNerve は関連する道のモデルだが豊穣圏への関手を表す。厳密双圏への厳密関手と Duskin nerve の T_[n] による指定同型は確認できなかった。 — |
| [2.4.4.9](https://kerodon.net/tag/00L9) | none | none | none | — | Coherent.cube、SimplicialThickening.Path と necklace を探索。任意の S の非退化単体と指定両端を持つ旗の族を、この箇所の対応にまとめる宣言は確認できなかった。 — |
| [2.5.6.13](https://kerodon.net/tag/00R4) | none | own | own | — | 本体の normalizedChainsHomEquiv は任意の非有界 Complex A に対して正規化鎖からの Hom を Γ(truncLE' H) への単体加群の Hom に移す。A=ℤ と homological grading への読み替えで適用し、ModuleCat.adj の次数ごとの随伴を合成する。左の自然性は normalizedChainsHomEquiv_precomp。標準単体に適用し Yoneda で右随伴の n 成分を読むと本文の K(M)_n。 —。追加確認 `SerrePositivity/EInfinity/ComplexLimits/NormalizedChainsHom.lean:57`, `SerrePositivity/EInfinity/ComplexLimits/NormalizedChainsHomNaturality.lean:32`, `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean:92`, `Mathlib/CategoryTheory/Adjunction/Whiskering.lean:32` |

## 差があった行の比較

### [2.5.6.13](https://kerodon.net/tag/00R4)（-a2 `none`、独立 `own`、比較後 `own`）

- -a2 の理由を照合した記録。確認済み・なし。単体集合の正規化鎖複体と Dold–Kan の部品はあるが、ℤ 次数の K を右随伴として組んだ宣言は未発見。
- 今回の判定。-a2 が探した一つの随伴名は見つからなかったが、normalizedChainsHomEquiv は非有界 H を既に量化し、normalizedChainsHomEquiv_precomp が左の自然性を返す。自由加群・忘却随伴を次数ごとに適用した Hom 同値と合成し、Adjunction.adjunctionOfEquivRight を適用できる。標準単体の式から右随伴の各次数が本文の K(H) と一致する。

## 追加の kernel 型

追加の `#check` は既存モジュールの import だけを使い、章別3回と補足2回に分けて共有鍵を取得した。各回の上限は500秒、実測の最長は約15秒。

```lean
CategoryTheory.SimplicialNerve : (C : Type u_2) →
  [inst : CategoryTheory.Category.{u_1, u_2} C] → [CategoryTheory.SimplicialCategory C] → SSet
@CategoryTheory.Adjunction.homAddEquiv : {C : Type u_1} →
  {D : Type u_2} →
    [inst : CategoryTheory.Category.{u_3, u_1} C] →
      [inst_1 : CategoryTheory.Category.{u_4, u_2} D] →
        [inst_2 : CategoryTheory.Preadditive C] →
          [inst_3 : CategoryTheory.Preadditive D] →
            {F : CategoryTheory.Functor C D} →
              {G : CategoryTheory.Functor D C} →
                (F ⊣ G) → [F.Additive] → (X : C) → (Y : D) → (F.obj X ⟶ Y) ≃+ (X ⟶ G.obj Y)
CategoryTheory.Adjunction.whiskerRight : (C : Type u_2) →
  {D : Type u_4} →
    {E : Type u_6} →
      [inst : CategoryTheory.Category.{u_1, u_2} C] →
        [inst_1 : CategoryTheory.Category.{u_3, u_4} D] →
          [inst_2 : CategoryTheory.Category.{u_5, u_6} E] →
            {F : CategoryTheory.Functor D E} →
              {G : CategoryTheory.Functor E D} →
                (F ⊣ G) →
                  ((CategoryTheory.Functor.whiskeringRight C D E).obj F ⊣
                    (CategoryTheory.Functor.whiskeringRight C E D).obj G)
ModuleCat.adj : (R : Type u_1) → [inst : Ring R] → ModuleCat.free R ⊣ CategoryTheory.forget (ModuleCat R)
@CategoryTheory.Abelian.DoldKan.equivalence : {A : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} A] →
    [inst_1 : CategoryTheory.Abelian A] → CategoryTheory.SimplicialObject A ≌ ChainComplex A ℕ
@CategoryTheory.StrictlyUnitaryLaxFunctor.comp_assoc : ∀ {B : Type u_9} [inst : CategoryTheory.Bicategory B]
  {C : Type u_10} [inst_1 : CategoryTheory.Bicategory C] {D : Type u_11} [inst_2 : CategoryTheory.Bicategory D]
  {E : Type u_12} [inst_3 : CategoryTheory.Bicategory E] (F : CategoryTheory.StrictlyUnitaryLaxFunctor B C)
  (G : CategoryTheory.StrictlyUnitaryLaxFunctor C D) (H : CategoryTheory.StrictlyUnitaryLaxFunctor D E),
  (F.comp G).comp H = F.comp (G.comp H)
SerrePositivity.KST.ProExcision.normalizedEZHomotopy : (C D : CategoryTheory.SimplicialObject (ModuleCat ℤ)) →
  Homotopy
    (CategoryTheory.CategoryStruct.id
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat ℤ)).obj
        (SerrePositivity.KST.ProExcision.simplicialIntegerTensor C D)))
    (CategoryTheory.CategoryStruct.comp (SerrePositivity.KST.ProExcision.normalizedAlexanderWhitney C D)
      (SerrePositivity.KST.ProExcision.normalizedShuffle C D))
@SerrePositivity.InfinityCategories.Coherent.path_hom_iff : ∀ {J : Type u_1} [inst : LinearOrder J] {a b : J}
  (p q : CategoryTheory.SimplicialThickening.Path a b), Nonempty (p ⟶ q) ↔ p.I ⊆ q.I
SerrePositivity.InfinityCategories.coherentNerveVertexEquiv : (C : Type u_2) →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    [inst_1 : CategoryTheory.SimplicialCategory C] →
      C ≃ (CategoryTheory.SimplicialNerve C).obj (Opposite.op { len := 0 })
@SerrePositivity.InfinityCategories.coherentNerveEdgeEquiv : {C : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} C] →
    [inst_1 : CategoryTheory.SimplicialCategory C] →
      (X Y : C) →
        SSet.Edge (SerrePositivity.InfinityCategories.coherentNerveVertex X)
            (SerrePositivity.InfinityCategories.coherentNerveVertex Y) ≃
          (X ⟶ Y)
SerrePositivity.EInfinity.ComplexLimits.normalizedChainsHomEquiv : (A : Type u_1) →
  [inst : CommRing A] →
    (S : SSet) →
      (H : SerrePositivity.DifferentialGraded.Complex A) →
        ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj S ⟶ H) ≃
          ((SerrePositivity.EInfinity.BarrattEccles.linearization A).obj S ⟶
            CategoryTheory.Abelian.DoldKan.Γ.obj (HomologicalComplex.truncLE' H (ComplexShape.embeddingUpIntLE 0)))
SerrePositivity.EInfinity.ComplexLimits.normalizedChainsHomEquiv_precomp : ∀ (A : Type u_1) [inst : CommRing A]
  {S T : SSet} (f : S ⟶ T) (H : SerrePositivity.DifferentialGraded.Complex A)
  (g : (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj T ⟶ H),
  (SerrePositivity.EInfinity.ComplexLimits.normalizedChainsHomEquiv A S H)
      (CategoryTheory.CategoryStruct.comp ((SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) g) =
    CategoryTheory.CategoryStruct.comp ((SerrePositivity.EInfinity.BarrattEccles.linearization A).map f)
      ((SerrePositivity.EInfinity.ComplexLimits.normalizedChainsHomEquiv A T H) g)
```

## 元の kernel evidence から照合した型

`ch2-kernel-evidence.json`、段1、段1′から own・both・mathlib 群の型を取得した。表示用に空白を整えた。

### 2.1.2.13

```lean
CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} : (C : Type u_2) → {𝒞 : CategoryTheory.Category.{u_1, u_2} C} → [self : CategoryTheory.MonoidalCategoryStruct.{u_1, u_2} C] → C
```

### 2.1.2.19

```lean
@CategoryTheory.MonoidalCategory.triangle.{u_1, u_2} : ∀ {C : Type u_2} {𝒞 : CategoryTheory.Category.{u_1, u_2} C} [self : @CategoryTheory.MonoidalCategory.{u_1, u_2} C 𝒞] (X Y : C), @Eq.{u_1 + 1} (@Quiver.Hom.{u_1, u_2} C (@CategoryTheory.CategoryStruct.toQuiver.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C 𝒞)) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self))) Y) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X Y)) (@CategoryTheory.CategoryStruct.comp.{u_1, u_2} C (@CategoryTheory.Category.toCategoryStruct.{u_1, u_2} C 𝒞) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self))) Y) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self)) Y)) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X Y) (@CategoryTheory.Iso.hom.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self))) Y) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self)) Y)) (@CategoryTheory.MonoidalCategoryStruct.associator.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self)) Y)) (@CategoryTheory.MonoidalCategoryStruct.whiskerLeft.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self)) Y) Y (@CategoryTheory.Iso.hom.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self)) Y) Y (@CategoryTheory.MonoidalCategoryStruct.leftUnitor.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) Y)))) (@CategoryTheory.MonoidalCategoryStruct.whiskerRight.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self))) X (@CategoryTheory.Iso.hom.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategoryStruct.tensorObj.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X (@CategoryTheory.MonoidalCategoryStruct.tensorUnit.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self))) X (@CategoryTheory.MonoidalCategoryStruct.rightUnitor.{u_1, u_2} C 𝒞 (@CategoryTheory.MonoidalCategory.toMonoidalCategoryStruct.{u_1, u_2} C 𝒞 self) X)) Y)
```

### 2.1.5.8

```lean
@CategoryTheory.Functor.LaxMonoidal.{u_1, u_2, u_3, u_4} : {C : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} C] → [@CategoryTheory.MonoidalCategory.{u_1, u_3} C inst] → {D : Type u_4} → [inst_2 : CategoryTheory.Category.{u_2, u_4} D] → [@CategoryTheory.MonoidalCategory.{u_2, u_4} D inst_2] → @CategoryTheory.Functor.{u_1, u_2, u_3, u_4} C inst D inst_2 → Type (max u_3 u_2)
```

### 2.2.0.1

```lean
CategoryTheory.Bicategory.Strict.{u_1, u_2, u_3} : (B : Type u_3) → [CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → Prop
```

### 2.2.1.1

```lean
CategoryTheory.Bicategory.{u_1, u_2, u_3} : Type u_3 → Type (max (max u_3 (u_2 + 1)) (u_1 + 1))
```

### 2.2.2.2

```lean
@CategoryTheory.Span.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.MorphismProperty.{u_1, u_2} C → CategoryTheory.MorphismProperty.{u_1, u_2} C → C → C → Type (max u_2 u_1)
CategoryTheory.Span.SpanBicat.{u_1, u_2} : (C : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} C] → CategoryTheory.MorphismProperty.{u_1, u_2} C → CategoryTheory.MorphismProperty.{u_1, u_2} C → Type u_2
@CategoryTheory.Span.SpanBicat.instBicategory.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → {Wₗ Wᵣ : CategoryTheory.MorphismProperty.{u_1, u_2} C} → [CategoryTheory.MorphismProperty.ContainsIdentities.{u_1, u_2} Wₗ] → [CategoryTheory.MorphismProperty.ContainsIdentities.{u_1, u_2} Wᵣ] → [CategoryTheory.MorphismProperty.HasPullbacksAgainst.{u_1, u_2} Wₗ Wᵣ] → [CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst.{u_1, u_2} Wₗ Wᵣ] → [CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst.{u_1, u_2} Wᵣ Wₗ] → [CategoryTheory.MorphismProperty.IsStableUnderComposition.{u_1, u_2} Wₗ] → [CategoryTheory.MorphismProperty.IsStableUnderComposition.{u_1, u_2} Wᵣ] → CategoryTheory.Bicategory.{u_1, max u_2 u_1, u_2} (CategoryTheory.Span.SpanBicat.{u_1, u_2} C Wₗ Wᵣ)
```

### 2.2.3.1

```lean
@Bicategory.Opposite.bicategory.{u_1, u_2, u_3} : {B : Type u_3} → [CategoryTheory.Bicategory.{u_1, u_2, u_3} B] → CategoryTheory.Bicategory.{u_1, u_2, u_3} (Opposite.{u_3 + 1} B)
```

### 2.2.4.1

```lean
CategoryTheory.StrictPseudofunctor.{u_1, u_2, u_3, u_4, u_5, u_6} : (B : Type u_5) → [CategoryTheory.Bicategory.{u_1, u_3, u_5} B] → (C : Type u_6) → [CategoryTheory.Bicategory.{u_2, u_4, u_6} C] → Type (max (max (max (max (max u_5 u_6) u_3) u_4) u_1) u_2)
```

### 2.4.1.11

```lean
CategoryTheory.EnrichedFunctor.{u_1, u_2, u_3, u_4} : (V : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} V] → [inst_1 : @CategoryTheory.MonoidalCategory.{u_1, u_2} V inst] → (C : Type u_3) → [@CategoryTheory.EnrichedCategory.{u_1, u_2, u_3} V inst inst_1 C] → (D : Type u_4) → [@CategoryTheory.EnrichedCategory.{u_1, u_2, u_4} V inst inst_1 D] → Type (max (max u_3 u_4) u_1)
```

### 2.4.7.3

```lean
@CoxeterSystem.length.{u_1, u_2} : {B : Type u_1} → {W : Type u_2} → [inst : Group.{u_2} W] → {M : CoxeterMatrix.{u_1} B} → @CoxeterSystem.{u_1, u_2} B M W inst → W → Nat
```

### 2.5.0.2

```lean
ChainComplex.{u_1, u_2, u_3} : (V : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} V] → [@CategoryTheory.Limits.HasZeroMorphisms.{u_1, u_2} V inst] → (α : Type u_3) → [AddRightCancelSemigroup.{u_3} α] → [One.{u_3} α] → Type (max (max u_3 u_2) u_1)
```

### 2.5.0.3

```lean
@HomologicalComplex.Hom.{u_1, u_2, u_3} : {ι : Type u_3} → {V : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} V] → [inst_1 : @CategoryTheory.Limits.HasZeroMorphisms.{u_1, u_2} V inst] → {c : ComplexShape.{u_3} ι} → @HomologicalComplex.{u_1, u_2, u_3} ι V inst inst_1 c → @HomologicalComplex.{u_1, u_2, u_3} ι V inst inst_1 c → Type (max u_3 u_1)
```

### 2.5.0.4

```lean
ChainComplex.{u_1, u_2, u_3} : (V : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} V] → [@CategoryTheory.Limits.HasZeroMorphisms.{u_1, u_2} V inst] → (α : Type u_3) → [AddRightCancelSemigroup.{u_3} α] → [One.{u_3} α] → Type (max (max u_3 u_2) u_1)
```

### 2.5.1.5

```lean
@QuasiIso.{u_1, u_2, u_3} : {ι : Type u_3} → {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → [inst_1 : @CategoryTheory.Limits.HasZeroMorphisms.{u_1, u_2} C inst] → {c : ComplexShape.{u_3} ι} → {K L : @HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c} → @Quiver.Hom.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@CategoryTheory.CategoryStruct.toQuiver.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@CategoryTheory.Category.toCategoryStruct.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@HomologicalComplex.instCategory.{u_1, u_2, u_3} ι C inst inst_1 c))) K L → [∀ (i : ι), @HomologicalComplex.HasHomology.{u_1, u_2, u_3} C inst inst_1 ι c K i] → [∀ (i : ι), @HomologicalComplex.HasHomology.{u_1, u_2, u_3} C inst inst_1 ι c L i] → Prop
@QuasiIsoAt.{u_1, u_2, u_3} : {ι : Type u_3} → {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → [inst_1 : @CategoryTheory.Limits.HasZeroMorphisms.{u_1, u_2} C inst] → {c : ComplexShape.{u_3} ι} → {K L : @HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c} → @Quiver.Hom.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@CategoryTheory.CategoryStruct.toQuiver.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@CategoryTheory.Category.toCategoryStruct.{max u_3 u_1, max (max u_2 u_3) u_1} (@HomologicalComplex.{u_1, u_2, u_3} ι C inst inst_1 c) (@HomologicalComplex.instCategory.{u_1, u_2, u_3} ι C inst inst_1 c))) K L → (i : ι) → [@HomologicalComplex.HasHomology.{u_1, u_2, u_3} C inst inst_1 ι c K i] → [@HomologicalComplex.HasHomology.{u_1, u_2, u_3} C inst inst_1 ι c L i] → Prop
```

### 2.5.2.1

```lean
SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} : (A : Type u_1) → [CommRing.{u_1} A] → Type u_2 → Type (max (max u_2 (u_1 + 1)) u_1)
```

### 2.5.2.4

```lean
SerrePositivity.DifferentialGraded.ClosedCategory.{u_1, u_2} : (A : Type u_1) → [inst : CommRing.{u_1} A] → (D : Type u_2) → [@SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} A inst D] → Type u_2
```

### 2.5.3.10

```lean
SerrePositivity.InfinityCategories.dgNerve.instQuasicategory.{u_1, u_2} : ∀ (A : Type u_1) [inst : CommRing.{u_1} A] (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} A D], SSet.Quasicategory.{max u_2 u_1} (SerrePositivity.InfinityCategories.dgNerve.{u_1, u_2} A D)
SerrePositivity.InfinityCategories.dgNerve.hornFilling.{u_1, u_2} : ∀ (A : Type u_1) [inst : CommRing.{u_1} A] (D : Type u_2) [inst_1 : SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} A D] {n : ℕ} {i : Fin (HAdd.hAdd.{0, 0, 0} n 3)} (σ : Quiver.Hom.{max u_1 u_2, max (u_1 + 1) (u_2 + 1)} (SSet.Subcomplex.toSSet.{max u_1 u_2} (SSet.horn.{max u_1 u_2} (HAdd.hAdd.{0, 0, 0} n 2) i)) (SerrePositivity.InfinityCategories.dgNerve.{u_1, u_2} A D)), LT.lt.{0} 0 i → LT.lt.{0} i (Fin.last (HAdd.hAdd.{0, 0, 0} n 2)) → ∃ τ, Eq.{max (u_1 + 1) (u_2 + 1)} σ (CategoryTheory.CategoryStruct.comp.{max u_1 u_2, (max u_1 u_2) + 1} (SSet.Subcomplex.ι.{max u_1 u_2} (SSet.horn.{max u_1 u_2} (HAdd.hAdd.{0, 0, 0} n 2) i)) τ)
```

### 2.5.4.6

```lean
SerrePositivity.DifferentialGraded.HomotopyCategory.{u_1, u_2} : (A : Type u_1) → [inst : CommRing.{u_1} A] → (D : Type u_2) → [@SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} A inst D] → Type u_2
SerrePositivity.DifferentialGraded.homotopyHomologyEquiv.{u_1, u_2} : (A : Type u_1) → [inst : CommRing.{u_1} A] → (D : Type u_2) → [inst_1 : SerrePositivity.DifferentialGraded.DGCategory.{u_1, u_2} A D] → (x y : SerrePositivity.DifferentialGraded.ClosedCategory.{u_1, u_2} A D) → Equiv.{u_1 + 1, u_1 + 1} (Quiver.Hom.{u_1, u_2} (CategoryTheory.Functor.obj.{u_1, u_1, u_2, u_2} (SerrePositivity.DifferentialGraded.toHomotopy.{u_1, u_2} A D) x) (CategoryTheory.Functor.obj.{u_1, u_1, u_2, u_2} (SerrePositivity.DifferentialGraded.toHomotopy.{u_1, u_2} A D) y)) ↑(HomologicalComplex.homology.{u_1, u_1 + 1, 0} (SerrePositivity.DifferentialGraded.homObject.{u_1, u_2} A D x y) 0)
```

### 2.5.7.3

```lean
SerrePositivity.KST.ProExcision.shuffleApp.{u_1} : (C D : CategoryTheory.SimplicialObject.{u_1, u_1 + 1} (ModuleCat.{u_1, 0} ℤ)) → (n : ℕ) → Quiver.Hom.{u_1, u_1 + 1} (HomologicalComplex.X.{u_1, u_1 + 1, 0} (SerrePositivity.KST.ProExcision.chainIntegerTensor.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} (AlgebraicTopology.alternatingFaceMapComplex.{u_1, u_1 + 1} (ModuleCat.{u_1, 0} ℤ)) C) (CategoryTheory.Functor.obj.{u_1, u_1, u_1 + 1, u_1 + 1} (AlgebraicTopology.alternatingFaceMapComplex.{u_1, u_1 + 1} (ModuleCat.{u_1, 0} ℤ)) D)) n) (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.KST.ProExcision.simplicialIntegerTensor.{u_1} C D) (Opposite.op.{1} { len := n }))
SerrePositivity.KST.ProExcision.shuffleBidegree.{u_1} : (C D : CategoryTheory.SimplicialObject.{u_1, u_1 + 1} (ModuleCat.{u_1, 0} ℤ)) → (p q n : ℕ) → Eq.{1} (HAdd.hAdd.{0, 0, 0} p q) n → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.KST.ProExcision.integerTensor.{u_1} (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} C (Opposite.op.{1} { len := p })) (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} D (Opposite.op.{1} { len := q }))) (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.KST.ProExcision.simplicialIntegerTensor.{u_1} C D) (Opposite.op.{1} { len := n }))
```

### 2.5.8.1

```lean
SerrePositivity.KST.ProExcision.awFront : (n : ℕ) → (i : Fin (HAdd.hAdd.{0, 0, 0} n 1)) → Quiver.Hom.{0, 0} { len := ↑i } { len := n }
SerrePositivity.KST.ProExcision.awBack : (n : ℕ) → (i : Fin (HAdd.hAdd.{0, 0, 0} n 1)) → Quiver.Hom.{0, 0} { len := HSub.hSub.{0, 0, 0} n ↑i } { len := n }
```
